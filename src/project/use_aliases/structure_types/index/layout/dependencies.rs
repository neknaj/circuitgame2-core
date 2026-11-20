//! 解決した型参照を、循環検査でたどる添字へ変換する。

mod order;

#[cfg(verus_only)]
use order::{dependencies_in_order, dependency_cycle, dependency_edge, dependency_graph_valid};

use super::{ResolvedStructureEntry, ResolvedStructures, StructureFieldType, UseAliases};
use super::{StructureLayoutError, StructureLayouts, StructurePosition};
use crate::project::{DeclaredFieldType, LocatedName};
#[cfg(verus_only)]
use crate::project::location_in_source;
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence};
use order::{DependencyEdge, check_dependency_order};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 循環を構成する一つのフィールド型参照。
#[derive(Debug)]
pub struct StructureTypeReference<'p, 'a> {
    /// 参照を書いた構造体の宣言位置。
    pub from: StructurePosition,
    /// 参照を書いたフィールドの宣言順の添字。
    pub field: usize,
    /// 参照が指す構造体の宣言位置。
    pub to: StructurePosition,
    /// 参照を書いた型名の元ソース位置。
    pub location: LocatedName<'p, 'a>,
}

/// 構造体の型、配置、または循環に関する診断。
#[derive(Debug)]
pub enum StructureTypeError<'p, 'a> {
    /// 数値、型参照、または配置の検査で検出した診断。
    Layout(StructureLayoutError<'p, 'a>),
    /// フィールド型をたどると同じ構造体に戻る。
    Cycle {
        /// 参照先が次の参照元につながる順に並ぶ閉路。自己参照では1件になる。
        references: Vec<StructureTypeReference<'p, 'a>>,
    },
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn dependency_target(
        &self, index: &ResolvedStructures, ty: StructureFieldType, target: Option<usize>,
    ) -> bool {
        match ty {
            StructureFieldType::Bits(_) => target.is_none(),
            StructureFieldType::Struct(position) => target matches Some(i)
                && i < index.entries_model().len() && index.entries_model()[i as int].position == position,
        }
    }

    spec fn dependency_row_matches(
        &self, index: &ResolvedStructures, declaration: ResolvedStructureEntry, edges: Seq<Option<usize>>,
    ) -> bool {
        let fields = declaration.declaration.fields@;
        &&& edges.len() <= fields.len()
        &&& forall|i: int| 0 <= i < edges.len() ==>
            self.dependency_target(index, fields[i].ty, #[trigger] edges[i])
    }

    fn structure_dependencies(
        &self, index: &ResolvedStructures, _limit: u64, row: &ResolvedStructureEntry,
    ) -> (edges: Vec<Option<usize>>)
        requires
            self.can_resolve(),
            self.targets.project_model().has_parsed_sources(),
            self.structure_index_matches(_limit, Ok(*index)),
            index.entries_model().contains(*row),
        ensures
            edges@.len() == row.declaration.fields@.len(),
            self.dependency_row_matches(index, *row, edges@),
    {
        let declarations = row.declaration.fields.as_slice();
        let mut edges = Vec::new();
        let mut i = 0;
        while i < declarations.len()
            invariant
                self.can_resolve(),
                self.targets.project_model().has_parsed_sources(),
                self.structure_index_matches(_limit, Ok(*index)),
                index.entries_model().contains(*row),
                declarations@ == row.declaration.fields@,
                i == edges@.len() <= declarations@.len(),
                self.dependency_row_matches(index, *row, edges@),
            decreases declarations@.len() - i,
        {
            let field = &declarations[i];
            let target = match field.ty {
                StructureFieldType::Bits(_) => None,
                StructureFieldType::Struct(position) => {
                    proof { self.structure_row_evidence(index, _limit, *row); }
                    let Some(target) = index.find_entry(position) else { unreachable!() };
                    Some(target)
                },
            };
            assert(self.dependency_target(index, field.ty, target));
            edges.push(target);
            i += 1;
        }
        edges
    }

    spec fn dependency_rows_match(&self, index: &ResolvedStructures, graph: Seq<Vec<Option<usize>>>) -> bool {
        &&& graph.len() <= index.entries_model().len()
        &&& forall|i: int| 0 <= i < graph.len() ==> {
            let row = index.entries_model()[i];
            &&& (#[trigger] graph[i])@.len() == row.declaration.fields@.len()
            &&& self.dependency_row_matches(index, row, graph[i]@)
        }
    }

    fn structure_dependency_graph(
        &self, index: &ResolvedStructures, limit: u64,
    ) -> (graph: Vec<Vec<Option<usize>>>)
        requires
            self.can_resolve(),
            self.targets.project_model().has_parsed_sources(),
            self.structure_index_matches(limit, Ok(*index)),
        ensures
            graph@.len() == index.entries_model().len(),
            self.dependency_rows_match(index, graph@),
            dependency_graph_valid(graph@),
    {
        let rows = index.entries();
        let mut graph = Vec::new();
        let mut i = 0;
        while i < rows.len()
            invariant
                self.can_resolve(),
                self.targets.project_model().has_parsed_sources(),
                self.structure_index_matches(limit, Ok(*index)),
                rows@ == index.entries_model(),
                i == graph@.len() <= rows@.len(),
                self.dependency_rows_match(index, graph@),
            decreases rows@.len() - i,
        {
            let row = &rows[i];
            assert(rows@.contains(*row));
            let edges = self.structure_dependencies(index, limit, row);
            graph.push(edges);
            i += 1;
        }
        graph
    }
    spec fn reference_matches(
        &self, index: &ResolvedStructures, edge: DependencyEdge, reference: StructureTypeReference,
    ) -> bool {
        let row = index.entries_model()[edge.from as int];
        let file = row.position.file as int;
        let project = self.targets.project_model();
        &&& reference.from == row.position
        &&& reference.field == edge.field
        &&& reference.to == index.entries_model()[edge.to as int].position
        &&& row.declaration.fields@[edge.field as int].declared.ty matches DeclaredFieldType::Named { form }
        &&& is_form_location(&project.sources_model()[file],
            project.circuits_model()[file].syntax.forms@[form as int], reference.location)
    }

    fn dependency_reference(
        &self, index: &ResolvedStructures, _limit: u64, _graph: &[Vec<Option<usize>>], edge: DependencyEdge,
    ) -> (reference: StructureTypeReference<'p, 'a>)
        requires
            self.can_resolve(),
            self.structure_index_matches(_limit, Ok(*index)),
            _graph@.len() == index.entries_model().len(),
            self.dependency_rows_match(index, _graph@),
            dependency_edge(_graph@, edge),
        ensures self.reference_matches(index, edge, reference),
    {
        let project = self.targets.project();
        let rows = index.entries();
        let row = &rows[edge.from];
        let field = row.declaration.fields[edge.field];
        proof {
            assert(rows@.contains(*row));
            self.structure_row_evidence(index, _limit, *row);
            assert(self.dependency_target(index, field.ty, Some(edge.to)));
        }
        let DeclaredFieldType::Named { form: type_atom } = field.declared.ty else { unreachable!() };
        let source = &project.sources()[row.position.file];
        let parsed = &project.circuits()[row.position.file];
        proof {
            assert(parsed_circuit_matches(*source, *parsed));
            parsed_index_evidence(*source, *parsed);
        }
        let location = form_location(source, parsed.syntax.forms.as_slice(), type_atom);
        StructureTypeReference { from: row.position, field: edge.field, to: rows[edge.to].position, location }
    }

    fn structure_cycle_references(
        &self, index: &ResolvedStructures, limit: u64, graph: &[Vec<Option<usize>>], cycle: &[DependencyEdge],
    ) -> (references: Vec<StructureTypeReference<'p, 'a>>)
        requires
            self.can_resolve(),
            self.structure_index_matches(limit, Ok(*index)),
            graph@.len() == index.entries_model().len(),
            self.dependency_rows_match(index, graph@),
            dependency_cycle(graph@, cycle@),
        ensures
            references@.len() == cycle@.len(),
            references@.len() > 0,
            forall|i: int| 0 <= i < references@.len() ==> location_in_source((#[trigger] references@[i]).location),
            forall|i: int, j: int| 0 <= i && j == i + 1 && j < references@.len() ==>
                (#[trigger] references@[i]).to == (#[trigger] references@[j]).from,
            references@.last().to == references@[0].from,
            forall|i: int| 0 <= i < cycle@.len() ==>
                self.reference_matches(index, cycle@[i], #[trigger] references@[i]),
    {
        let mut references = Vec::new();
        let mut i = 0;
        while i < cycle.len()
            invariant
                self.can_resolve(),
                self.structure_index_matches(limit, Ok(*index)),
                graph@.len() == index.entries_model().len(),
                self.dependency_rows_match(index, graph@),
                dependency_cycle(graph@, cycle@),
                i == references@.len() <= cycle@.len(),
                forall|j: int| 0 <= j < i ==> self.reference_matches(index, cycle@[j], #[trigger] references@[j]),
            decreases cycle@.len() - i,
        {
            let reference = self.dependency_reference(index, limit, graph, cycle[i]);
            references.push(reference);
            i += 1;
        }
        references
    }

    /// 構造体の型検査結果を配置と参照グラフに結び付ける。
    pub closed spec fn structure_types_match(
        &self, limit: u64, result: Result<StructureLayouts, StructureTypeError>,
    ) -> bool {
        match result {
            Err(StructureTypeError::Layout(error)) => self.structure_layouts_match(limit, Err(error)),
            _ => exists|index: ResolvedStructures, graph: Seq<Vec<Option<usize>>>|
                #[trigger] self.structure_index_matches(limit, Ok(index))
                    && #[trigger] self.dependency_rows_match(&index, graph)
                    && graph.len() == index.entries_model().len()
                    && match result {
                        Ok(layouts) => self.layouts_for_index(&index, Ok(layouts))
                            && exists|rank: Seq<nat>| #[trigger] dependencies_in_order(graph, rank),
                        Err(StructureTypeError::Cycle { references }) =>
                            (exists|layouts: StructureLayouts| #[trigger] self.layouts_for_index(&index, Ok(layouts)))
                            && (exists|cycle: Seq<DependencyEdge>| #[trigger] dependency_cycle(graph, cycle)
                                && cycle.len() == references@.len()
                                && forall|i: int| 0 <= i < cycle.len() ==>
                                    self.reference_matches(&index, cycle[i], #[trigger] references@[i])),
                        _ => false,
                    },
        }
    }

    /// 型検査を通過した配置表には、このプロジェクトの各構造体の配置がある。
    pub(in crate::project::use_aliases) proof fn checked_layout_contains(
        &self, limit: u64, layouts: StructureLayouts, position: StructurePosition,
    )
        requires
            self.structure_types_match(limit, Ok(layouts)),
            self.is_structure_position(position),
        ensures exists|i: int| 0 <= i < layouts.entries_model().len()
            && (#[trigger] layouts.entries_model()[i]).position == position,
    {
        reveal(UseAliases::structure_index_matches);
        let (index, graph) = choose|index: ResolvedStructures, graph: Seq<Vec<Option<usize>>>|
            #[trigger] self.structure_index_matches(limit, Ok(index))
                && #[trigger] self.dependency_rows_match(&index, graph)
                && graph.len() == index.entries_model().len()
                && self.layouts_for_index(&index, Ok(layouts))
                && exists|rank: Seq<nat>| #[trigger] dependencies_in_order(graph, rank);
        let rows = index.entries_model();
        self.targets.project_model().circuit_count_fits();
        let stop = StructurePosition {
            file: self.targets.project_model().circuits_model().len() as usize, entry: 0,
        };
        assert(self.structure_index_matches(limit, Ok(index)));
        assert(self.structure_prefix(limit, stop, rows));
        assert(super::structure_before(position, stop));
        assert(self.is_structure_position(position));
        assert(self.layouts_for_index(&index, Ok(layouts)));
        assert(self.layouts_before(&index, layouts.entries_model()));
        let i = choose|i: int| 0 <= i < rows.len() && (#[trigger] rows[i]).position == position;
        assert(self.layout_row_result(&index, rows[i], Ok(layouts.entries_model()[i])));
    }

    pub(in crate::project::use_aliases) proof fn checked_layout_positions_are_declared(&self, limit: u64, layouts: StructureLayouts)
        requires self.structure_types_match(limit, Ok(layouts)),
        ensures forall|i: int| 0 <= i < layouts.entries_model().len()
            ==> self.is_structure_position((#[trigger] layouts.entries_model()[i]).position),
    {
        reveal(UseAliases::structure_index_matches);
        let (index, graph) = choose|index: ResolvedStructures, graph: Seq<Vec<Option<usize>>>|
            #[trigger] self.structure_index_matches(limit, Ok(index))
                && #[trigger] self.dependency_rows_match(&index, graph)
                && graph.len() == index.entries_model().len()
                && self.layouts_for_index(&index, Ok(layouts))
                && exists|rank: Seq<nat>| #[trigger] dependencies_in_order(graph, rank);
        assert(self.structure_index_matches(limit, Ok(index)));
        assert(self.layouts_for_index(&index, Ok(layouts)));
        assert(self.layouts_before(&index, layouts.entries_model()));
        assert forall|i: int| 0 <= i < layouts.entries_model().len()
            implies self.is_structure_position((#[trigger] layouts.entries_model()[i]).position) by {
            let row = index.entries_model()[i];
            assert(self.layout_row_result(&index, row, Ok(layouts.entries_model()[i])));
        };
    }

    /// 構造体の型参照を解決し、配置と循環を検査する。
    ///
    /// `limit` は各構造体とビット列フィールドの宣言幅の上限。
    ///
    /// # Examples
    ///
    /// ファイルをまたぐ循環では、各型名が書かれたファイルと範囲を確認できる。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     SourceSnapshot, StructureTypeError, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    /// let project = parse_circuit_project(&[
    ///     SourceSnapshot { path: "left.ncg2", revision: 1,
    ///         text: "(struct Left (width 1) (next Right (at 0)))" },
    ///     SourceSnapshot { path: "right.ncg2", revision: 2,
    ///         text: "(struct Right (width 1) (next Left (at 0)))" },
    /// ]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let Err(StructureTypeError::Cycle { references }) = aliases.check_structure_types(1) else {
    ///     panic!("expected a cycle");
    /// };
    /// assert_eq!(references.len(), 2);
    /// assert_eq!(references[0].to, references[1].from);
    /// assert_eq!(references[1].to, references[0].from);
    /// let site = &references[0].location;
    /// assert_eq!(site.source.revision, 1);
    /// assert_eq!(&site.source.text[site.span.clone()], "Right");
    /// ```
    ///
    /// # Errors
    ///
    /// 数値、名前解決、配置の診断を優先する。型参照が循環するときは、
    /// 実際に閉路を構成する型名字句の位置を返す。
    pub fn check_structure_types(&self, limit: u64)
        -> (result: Result<StructureLayouts<'p, 'a>, StructureTypeError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            self.structure_types_match(limit, result),
            result matches Err(StructureTypeError::Cycle { references }) ==> {
                &&& references@.len() > 0
                &&& forall|i: int| 0 <= i < references@.len() ==> location_in_source((#[trigger] references@[i]).location)
                &&& forall|i: int, j: int| 0 <= i && j == i + 1 && j < references@.len() ==>
                    (#[trigger] references@[i]).to == (#[trigger] references@[j]).from
                &&& references@.last().to == references@[0].from
            },
    {
        let _project = self.targets.project();
        let index = match self.index_resolved_structures(limit) {
            Ok(index) => index,
            Err(error) => return Err(StructureTypeError::Layout(StructureLayoutError::Resolution(error))),
        };
        let layouts = match self.place_resolved_structures(&index, limit) {
            Ok(layouts) => layouts,
            Err(error) => return Err(StructureTypeError::Layout(error)),
        };
        let graph = self.structure_dependency_graph(&index, limit);
        match check_dependency_order(graph.as_slice()) {
            Ok(()) => Ok(layouts),
            Err(cycle) => {
                let references = self.structure_cycle_references(&index, limit, graph.as_slice(), cycle.as_slice());
                Err(StructureTypeError::Cycle { references })
            },
        }
    }
}

} // verus!
