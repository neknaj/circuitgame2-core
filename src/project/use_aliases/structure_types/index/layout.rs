//! 解決済みの構造体フィールドを、宣言に従ってビット区間へ配置する。

mod dependencies;
mod fields;
mod operations;
pub use operations::{StructureOperation, StructureOperationError, TypedStructureOperation};
pub use dependencies::{StructureTypeError, StructureTypeReference};

use super::{ResolvedStructureEntry, ResolvedStructures, StructureIndexError, StructurePosition, UseAliases};
use super::super::StructureFieldType;
use crate::project::LocatedName;
use crate::project::circuits::{form_location, read_indexed_atom};
use alloc::vec::Vec;
use core::ops::Range;
use fields::{FieldConflict, check_field_placement};
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::project::circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::project::declarations::located_name_evidence;
#[cfg(verus_only)]
use crate::project::structure_declarations::checked_structure_fields;
#[cfg(verus_only)]
use crate::project::{DeclaredFieldType, StructureDeclaration, structure_declaration_result};
#[cfg(verus_only)]
use fields::{field_range_matches, overlaps, placement_matches};
#[cfg(verus_only)]
use super::structure_before;
#[cfg(verus_only)]
use crate::syntax::form_span;
#[cfg(verus_only)]
use crate::syntax::circuit::reference_atom;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 構造体のフィールド名、型、ビット区間。
#[derive(Debug)]
pub struct StructureLayoutField<'p, 'a> {
    /// フィールド名の綴り。
    pub name: &'a str,
    /// フィールド名の元ソース位置。
    pub location: LocatedName<'p, 'a>,
    /// 解決済みのフィールド型。
    pub ty: StructureFieldType,
    /// 最下位ビットを0とする半開区間。
    pub range: Range<u64>,
}

/// 一つの構造体宣言のフィールド配置。
#[derive(Debug)]
pub struct StructureLayout<'p, 'a> {
    /// 構造体型の同一性を識別する宣言位置。
    pub position: StructurePosition,
    /// 空きビットを含む総幅。
    pub width: u64,
    /// 元の宣言順のフィールド。
    pub fields: Vec<StructureLayoutField<'p, 'a>>,
}

/// プロジェクト内の構造体の配置。フィールド型の循環は別途検査する。
#[derive(Debug)]
pub struct StructureLayouts<'p, 'a> {
    entries: Vec<StructureLayout<'p, 'a>>,
}

spec fn representation_width(layouts: Seq<StructureLayout>, ty: StructureFieldType, width: int) -> bool {
    match ty {
        StructureFieldType::Bits(bits) => width == bits,
        StructureFieldType::Struct(position) => exists|i: int| 0 <= i < layouts.len()
            && (#[trigger] layouts[i]).position == position && layouts[i].width == width,
    }
}

impl<'p, 'a> StructureLayouts<'p, 'a> {
    #[verifier::type_invariant]
    spec fn layout_entries_valid(&self) -> bool {
        &&& forall|i: int, j: int| 0 <= i < j < self.entries@.len() ==>
            structure_before((#[trigger] self.entries@[i]).position, (#[trigger] self.entries@[j]).position)
        &&& forall|i: int| 0 <= i < self.entries@.len() ==> {
            let entry = #[trigger] self.entries@[i];
            &&& entry.width > 0
            &&& forall|j: int| 0 <= j < entry.fields@.len() ==> {
                let field = #[trigger] entry.fields@[j];
                &&& field.range.start < field.range.end <= entry.width
                &&& representation_width(self.entries@, field.ty, field.range.end - field.range.start)
            }
        }
    }
    /// 構造体の配置をファイル順と厳格索引順で返す。
    pub fn entries(&self) -> (entries: &[StructureLayout<'p, 'a>])
        ensures entries@ == self.entries_model(),
    {
        self.entries.as_slice()
    }

    /// 配置済み宣言の列を表す。
    pub closed spec fn entries_model(&self) -> Seq<StructureLayout<'p, 'a>> { self.entries@ }
}

/// フィールドを配置できない理由。
#[derive(Debug)]
pub enum StructurePlacementError<'p, 'a> {
    /// 同じ名前のフィールドを二度宣言した。
    DuplicateName {
        /// 後のフィールド名。
        later: LocatedName<'p, 'a>,
        /// 先のフィールド名。
        prior: LocatedName<'p, 'a>,
    },
    /// 選んだビット区間が構造体の範囲に収まらない。
    Outside {
        /// 範囲外の指定をしたオフセットの字句。
        offset: LocatedName<'p, 'a>,
        /// フィールドの開始ビット。
        start: u64,
        /// フィールド型のビット幅。
        field_width: u64,
        /// 構造体の総幅。
        structure_width: u64,
    },
    /// 二つのフィールドのビット区間が交わる。
    Overlap {
        /// 後のフィールド名。
        later: LocatedName<'p, 'a>,
        /// 先のフィールド名。
        prior: LocatedName<'p, 'a>,
        /// 後のフィールドのビット区間。
        later_range: Range<u64>,
        /// 先のフィールドのビット区間。
        prior_range: Range<u64>,
    },
}

/// 構造体の型解決または配置に関する診断。
#[derive(Debug)]
pub enum StructureLayoutError<'p, 'a> {
    /// 宣言の数値検査または型解決で検出した違反。
    Resolution(StructureIndexError<'p, 'a>),
    /// 解決したフィールドを配置するときに検出した違反。
    Placement {
        /// 診断対象の構造体宣言。
        position: StructurePosition,
        /// フィールドを配置できない理由と関連箇所。
        error: StructurePlacementError<'p, 'a>,
    },
}

struct FieldPlacement<'p, 'a> {
    name: &'a str,
    location: LocatedName<'p, 'a>,
    offset_location: LocatedName<'p, 'a>,
    ty: StructureFieldType,
    offset: u64,
    width: u64,
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    proof fn structure_row_evidence(
        &self, index: &ResolvedStructures, limit: u64, row: ResolvedStructureEntry,
    )
        requires
            self.targets.project_model().has_parsed_sources(),
            self.structure_index_matches(limit, Ok(*index)),
            index.entries_model().contains(row),
        ensures
            self.is_structure_position(row.position),
            self.structure_resolution_matches(row.position.file, row.position.entry, limit, Ok(Some(row.declaration))),
            0 < row.declaration.width <= limit,
            forall|i: int| 0 <= i < row.declaration.fields@.len() ==> {
                let f = #[trigger] row.declaration.fields@[i];
                let forms = self.targets.project_model().circuits_model()[row.position.file as int].syntax.forms@;
                &&& f.declared.site.name < forms.len()
                &&& forms[f.declared.site.name as int] is Atom
                &&& f.declared.site.offset < forms.len()
                &&& match f.ty {
                    StructureFieldType::Bits(width) => 0 < width <= limit,
                    StructureFieldType::Struct(target) =>
                        f.declared.ty matches DeclaredFieldType::Named { form } && form < forms.len()
                        && forms[form as int] is Atom && reference_atom(forms[form as int]->Atom_kind)
                        && self.is_structure_position(target)
                        && exists|j: int| 0 <= j < index.entries_model().len()
                            && (#[trigger] index.entries_model()[j]).position == target,
                }
            },
    {
        let entries = index.entries_model();
        let project = &self.targets.project_model();
        let at = choose|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]) == row;
        let file = row.position.file;
        let entry = row.position.entry;
        project.circuit_count_fits();
        let stop = StructurePosition { file: project.circuits_model().len() as usize, entry: 0 };
        reveal(UseAliases::structure_index_matches);
        assert(self.structure_prefix(limit, stop, entries));
        assert(self.structure_resolution_matches(file, entry, limit, Ok(Some(row.declaration))));
        reveal(UseAliases::structure_resolution_matches);
        let (scope, declaration) = choose|scope, declaration: StructureDeclaration|
            #[trigger] self.structure_scope_matches(file, entry, &scope)
            && #[trigger] structure_declaration_result(project, file as int, entry as int, limit, Ok(Some(declaration)))
            && self.structure_after_numbers(&scope, declaration, Ok(Some(row.declaration)));
        checked_structure_fields(project, file, entry, limit, declaration);
        let forms = project.circuits_model()[file as int].syntax.forms@;
        assert forall|i: int| 0 <= i < row.declaration.fields@.len() implies {
            let f = #[trigger] row.declaration.fields@[i];
            &&& f.declared.site.name < forms.len()
            &&& forms[f.declared.site.name as int] is Atom
            &&& f.declared.site.offset < forms.len()
            &&& match f.ty {
                StructureFieldType::Bits(width) => 0 < width <= limit,
                StructureFieldType::Struct(target) =>
                    f.declared.ty matches DeclaredFieldType::Named { form } && form < forms.len()
                    && forms[form as int] is Atom && reference_atom(forms[form as int]->Atom_kind)
                    && self.is_structure_position(target) && exists|j: int| 0 <= j < entries.len()
                        && (#[trigger] entries[j]).position == target,
            }
        } by {
            let f = row.declaration.fields@[i];
            assert(self.structure_field_matches(&scope, declaration.fields@[i], f));
            if let StructureFieldType::Struct(target) = f.ty {
                let binding = choose|binding| #[trigger] self.structure_type_binding(&scope,
                    f.declared.ty->Named_form, Ok(binding)) && self.structure_position_matches(target, binding);
                assert(self.is_structure_position(target));
                assert(structure_before(target, stop));
                assert(exists|j: int| 0 <= j < entries.len() && (#[trigger] entries[j]).position == target);
            }
        };
    }

    spec fn field_width_matches(
        &self, index: &ResolvedStructures, ty: StructureFieldType, width: u64,
    ) -> bool {
        match ty {
            StructureFieldType::Bits(bits) => width == bits,
            StructureFieldType::Struct(target) => exists|j: int| 0 <= j < index.entries_model().len()
                && (#[trigger] index.entries_model()[j]).position == target
                && index.entries_model()[j].declaration.width == width,
        }
    }

    spec fn field_placement_input(
        &self, index: &ResolvedStructures, row: ResolvedStructureEntry, i: int, field: FieldPlacement,
    ) -> bool {
        let project = self.targets.project_model();
        let file = row.position.file as int;
        let forms = project.circuits_model()[file].syntax.forms@;
        let source = &project.sources_model()[file];
        let f = row.declaration.fields@[i];
        let name_span = form_span(forms[f.declared.site.name as int]);
        &&& 0 <= i < row.declaration.fields@.len()
        &&& field.ty == f.ty && field.offset == f.declared.offset
        &&& is_form_location(source, forms[f.declared.site.name as int], field.location)
        &&& is_form_location(source, forms[f.declared.site.offset as int], field.offset_location)
        &&& field.name.spec_bytes() == source.text.spec_bytes()[name_span.start as int..name_span.end as int]
        &&& 0 < field.width
        &&& self.field_width_matches(index, field.ty, field.width)
    }

    fn field_for_placement(
        &self, index: &ResolvedStructures, _limit: u64, row: &ResolvedStructureEntry, i: usize,
    ) -> (field: FieldPlacement<'p, 'a>)
        requires
            self.can_resolve(),
            self.structure_index_matches(_limit, Ok(*index)),
            index.entries_model().contains(*row),
            i < row.declaration.fields@.len(),
        ensures self.field_placement_input(index, *row, i as int, field),
    {
        let project = self.targets.project();
        proof { self.structure_row_evidence(index, _limit, *row); }
        let source = &project.sources()[row.position.file];
        let circuit = &project.circuits()[row.position.file];
        proof {
            assert(parsed_circuit_matches(*source, *circuit));
            parsed_index_evidence(*source, *circuit);
        }
        let forms = circuit.syntax.forms.as_slice();
        let f = row.declaration.fields[i];
        let (name, span) = read_indexed_atom(source.text, forms, f.declared.site.name);
        let location = LocatedName { source, span };
        proof { located_name_evidence(location); }
        let offset_location = form_location(source, forms, f.declared.site.offset);
        let width = match f.ty {
            StructureFieldType::Bits(width) => width,
            StructureFieldType::Struct(target) => {
                let Some(declaration) = index.get(target) else { unreachable!() };
                proof {
                    reveal(ResolvedStructures::lookup_matches);
                    let j = choose|j: int| 0 <= j < index.entries_model().len()
                        && (#[trigger] index.entries_model()[j]).position == target
                        && index.entries_model()[j].declaration == *declaration;
                    assert(index.entries_model().contains(index.entries_model()[j]));
                    self.structure_row_evidence(index, _limit, index.entries_model()[j]);
                }
                declaration.width
            },
        };
        FieldPlacement { name, location, offset_location, ty: f.ty, offset: f.declared.offset, width }
    }

    spec fn layout_field_at(
        &self, index: &ResolvedStructures, row: ResolvedStructureEntry, i: int, output: StructureLayoutField,
    ) -> bool {
        exists|field: FieldPlacement| #[trigger] self.field_placement_input(index, row, i, field)
            && output.name == field.name && output.location == field.location && output.ty == field.ty
            && field_range_matches(field.offset, field.width, output.range)
            && output.range.end <= row.declaration.width
    }

    spec fn fields_disjoint(earlier: StructureLayoutField, later: StructureLayoutField) -> bool {
        earlier.name.spec_bytes() != later.name.spec_bytes() && !overlaps(earlier.range, later.range)
    }

    #[verifier::opaque]
    spec fn structure_layout_prefix(
        &self, index: &ResolvedStructures, row: ResolvedStructureEntry, fields: Seq<StructureLayoutField>,
    ) -> bool {
        &&& fields.len() <= row.declaration.fields@.len()
        &&& forall|i: int| 0 <= i < fields.len() ==> self.layout_field_at(index, row, i, #[trigger] fields[i])
        &&& forall|i: int, j: int| 0 <= i < j < fields.len() ==>
            Self::fields_disjoint(#[trigger] fields[i], #[trigger] fields[j])
    }

    spec fn placement_diagnostic_matches(
        &self, total: u64, field: FieldPlacement, prior: Seq<StructureLayoutField>,
        conflict: FieldConflict, error: StructurePlacementError,
    ) -> bool {
        &&& placement_matches(total, prior, field.name, field.offset, field.width, Err(conflict))
        &&& match (conflict, error) {
            (FieldConflict::Name(i), StructurePlacementError::DuplicateName { later, prior: earlier }) =>
                later == field.location && earlier == prior[i as int].location,
            (FieldConflict::Outside, StructurePlacementError::Outside { offset, start, field_width, structure_width }) =>
                offset == field.offset_location && start == field.offset && field_width == field.width
                    && structure_width == total,
            (FieldConflict::Overlap(i), StructurePlacementError::Overlap { later, prior: earlier, later_range, prior_range }) =>
                later == field.location && earlier == prior[i as int].location
                    && field_range_matches(field.offset, field.width, later_range)
                    && prior_range == prior[i as int].range,
            _ => false,
        }
    }

    spec fn layout_row_result(
        &self, index: &ResolvedStructures, row: ResolvedStructureEntry,
        result: Result<StructureLayout, StructurePlacementError>,
    ) -> bool {
        match result {
            Ok(layout) => layout.position == row.position && layout.width == row.declaration.width
                && layout.width > 0
                && layout.fields@.len() == row.declaration.fields@.len()
                && self.structure_layout_prefix(index, row, layout.fields@),
            Err(error) => exists|prior: Seq<StructureLayoutField>, field: FieldPlacement, conflict: FieldConflict|
                #[trigger] self.structure_layout_prefix(index, row, prior)
                && self.field_placement_input(index, row, prior.len() as int, field)
                && #[trigger] self.placement_diagnostic_matches(row.declaration.width, field, prior, conflict, error),
        }
    }

    proof fn append_layout_field(
        &self, index: &ResolvedStructures, row: ResolvedStructureEntry,
        prior: Seq<StructureLayoutField>, input: FieldPlacement, output: StructureLayoutField,
    )
        requires
            self.structure_layout_prefix(index, row, prior),
            self.field_placement_input(index, row, prior.len() as int, input),
            output.name == input.name && output.location == input.location && output.ty == input.ty,
            placement_matches(row.declaration.width, prior, input.name, input.offset, input.width, Ok(output.range)),
            output.range.end <= row.declaration.width,
        ensures self.structure_layout_prefix(index, row, prior.push(output)),
    {
        reveal(UseAliases::structure_layout_prefix);
        let all = prior.push(output);
        assert(self.layout_field_at(index, row, prior.len() as int, output));
        assert forall|i: int| 0 <= i < all.len() implies self.layout_field_at(index, row, i, #[trigger] all[i]) by {
            if i < prior.len() {
                assert(all[i] == prior[i]);
            } else {
                assert(all[i] == output);
            }
        };
        assert forall|i: int, j: int| 0 <= i < j < all.len() implies
            Self::fields_disjoint(#[trigger] all[i], #[trigger] all[j]) by {
            assert(all[i] == prior[i]);
            if j < prior.len() {
                assert(all[j] == prior[j]);
            } else {
                assert(all[j] == output);
                assert(!fields::conflicts(prior[i], input.name, output.range));
            }
        };
        assert(self.structure_layout_prefix(index, row, all));
    }

    fn place_structure(
        &self, index: &ResolvedStructures, limit: u64, row: &ResolvedStructureEntry,
    ) -> (result: Result<StructureLayout<'p, 'a>, StructurePlacementError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.structure_index_matches(limit, Ok(*index)),
            index.entries_model().contains(*row),
        ensures self.layout_row_result(index, *row, result),
    {
        let _project = self.targets.project();
        proof { self.structure_row_evidence(index, limit, *row); }
        let total = row.declaration.width;
        let mut fields: Vec<StructureLayoutField> = Vec::new();
        assert(self.structure_layout_prefix(index, *row, fields@)) by {
            reveal(UseAliases::structure_layout_prefix);
        };
        let mut i = 0;
        while i < row.declaration.fields.len()
            invariant
                self.can_resolve(),
                self.structure_index_matches(limit, Ok(*index)),
                index.entries_model().contains(*row),
                0 < total == row.declaration.width,
                i == fields@.len() <= row.declaration.fields@.len(),
                self.structure_layout_prefix(index, *row, fields@),
            decreases row.declaration.fields@.len() - i,
        {
            let field = self.field_for_placement(index, limit, row, i);
            let ghost input = field;
            let range = match check_field_placement(total, fields.as_slice(), field.name, field.offset, field.width) {
                Ok(range) => range,
                Err(conflict) => {
                    let ghost why = conflict;
                    let error = match conflict {
                        FieldConflict::Name(j) => {
                            let other = &fields[j].location;
                            StructurePlacementError::DuplicateName {
                                later: field.location, prior: LocatedName { source: other.source, span: other.span.start..other.span.end },
                            }
                        },
                        FieldConflict::Outside => StructurePlacementError::Outside {
                            offset: field.offset_location, start: field.offset, field_width: field.width, structure_width: total,
                        },
                        FieldConflict::Overlap(j) => {
                            let earlier = &fields[j];
                            StructurePlacementError::Overlap {
                                later: field.location,
                                prior: LocatedName { source: earlier.location.source, span: earlier.location.span.start..earlier.location.span.end },
                                later_range: field.offset..field.offset + field.width,
                                prior_range: earlier.range.start..earlier.range.end,
                            }
                        },
                    };
                    assert(self.placement_diagnostic_matches(total, input, fields@, why, error));
                    return Err(error);
                },
            };
            let output = StructureLayoutField { name: field.name, location: field.location, ty: field.ty, range };
            proof { self.append_layout_field(index, *row, fields@, input, output); }
            fields.push(output);
            i += 1;
        }
        Ok(StructureLayout { position: row.position, width: total, fields })
    }

    spec fn layouts_before(
        &self, index: &ResolvedStructures, layouts: Seq<StructureLayout>,
    ) -> bool {
        &&& layouts.len() <= index.entries_model().len()
        &&& forall|i: int| 0 <= i < layouts.len() ==>
            self.layout_row_result(index, index.entries_model()[i], Ok(#[trigger] layouts[i]))
    }

    /// 配置結果が宣言と解決済みの型に対応し、診断が最初の違反を指すことを表す。
    pub closed spec fn structure_layouts_match(
        &self, limit: u64, result: Result<StructureLayouts, StructureLayoutError>,
    ) -> bool {
        match result {
            Err(StructureLayoutError::Resolution(error)) => self.structure_index_matches(limit, Err(error)),
            _ => exists|index: ResolvedStructures| #[trigger] self.structure_index_matches(limit, Ok(index))
                && self.layouts_for_index(&index, result),
        }
    }

    spec fn layouts_for_index(
        &self, index: &ResolvedStructures, result: Result<StructureLayouts, StructureLayoutError>,
    ) -> bool {
        match result {
            Ok(layouts) => layouts.entries@.len() == index.entries_model().len()
                && self.layouts_before(index, layouts.entries@),
            Err(StructureLayoutError::Placement { position, error }) => exists|prior: Seq<StructureLayout>|
                #[trigger] self.layouts_before(index, prior)
                    && prior.len() < index.entries_model().len()
                    && index.entries_model()[prior.len() as int].position == position
                    && self.layout_row_result(index, index.entries_model()[prior.len() as int], Err(error)),
            _ => false,
        }
    }

    proof fn layout_entries_agree_at(
        &self, limit: u64, left_index: &ResolvedStructures, right_index: &ResolvedStructures,
        left: StructureLayouts, right: StructureLayouts, a: int, b: int,
    )
        requires
            self.can_resolve(),
            self.structure_index_matches(limit, Ok(*left_index)),
            self.structure_index_matches(limit, Ok(*right_index)),
            self.layouts_for_index(left_index, Ok(left)),
            self.layouts_for_index(right_index, Ok(right)),
            0 <= a < left.entries_model().len(),
            0 <= b < right.entries_model().len(),
            left.entries_model()[a].position == right.entries_model()[b].position,
        ensures ({
            let l = left.entries_model()[a];
            let r = right.entries_model()[b];
            &&& l.width == r.width
            &&& l.fields@.len() == r.fields@.len()
            &&& forall|i: int| 0 <= i < l.fields@.len() ==> {
                let x = #[trigger] l.fields@[i];
                let y = #[trigger] r.fields@[i];
                &&& x.name.spec_bytes() == y.name.spec_bytes()
                &&& x.location == y.location
                &&& x.ty == y.ty
                &&& x.range == y.range
            }
        }),
    {
        self.targets.parsed_project_model();
        let lx = left_index.entries_model()[a];
        let rx = right_index.entries_model()[b];
        let l = left.entries_model()[a];
        let r = right.entries_model()[b];
        assert(self.layout_row_result(left_index, lx, Ok(l)));
        assert(self.layout_row_result(right_index, rx, Ok(r)));
        self.structure_row_evidence(left_index, limit, lx);
        self.structure_row_evidence(right_index, limit, rx);
        self.resolved_structures_agree(l.position, limit, lx.declaration, rx.declaration);
        reveal(UseAliases::structure_layout_prefix);
        assert forall|i: int| 0 <= i < l.fields@.len() implies {
            let x = #[trigger] l.fields@[i];
            let y = #[trigger] r.fields@[i];
            &&& x.name.spec_bytes() == y.name.spec_bytes()
            &&& x.location == y.location
            &&& x.ty == y.ty
            &&& x.range == y.range
        } by {
            self.layout_fields_agree_at(limit, left_index, right_index, lx, rx, i, l.fields@[i], r.fields@[i]);
        };
    }

    proof fn layout_fields_agree_at(
        &self, limit: u64, left_index: &ResolvedStructures, right_index: &ResolvedStructures,
        left_row: ResolvedStructureEntry, right_row: ResolvedStructureEntry, i: int,
        left: StructureLayoutField, right: StructureLayoutField,
    )
        requires
            self.can_resolve(),
            self.structure_index_matches(limit, Ok(*left_index)),
            self.structure_index_matches(limit, Ok(*right_index)),
            left_row.position == right_row.position,
            left_row.declaration.fields@ == right_row.declaration.fields@,
            self.layout_field_at(left_index, left_row, i, left),
            self.layout_field_at(right_index, right_row, i, right),
        ensures
            left.name.spec_bytes() == right.name.spec_bytes(),
            left.location == right.location,
            left.ty == right.ty,
            left.range == right.range,
    {
        let a = choose|field: FieldPlacement| #[trigger] self.field_placement_input(left_index, left_row, i, field)
            && left.name == field.name && left.location == field.location && left.ty == field.ty
            && field_range_matches(field.offset, field.width, left.range)
            && left.range.end <= left_row.declaration.width;
        let b = choose|field: FieldPlacement| #[trigger] self.field_placement_input(right_index, right_row, i, field)
            && right.name == field.name && right.location == field.location && right.ty == field.ty
            && field_range_matches(field.offset, field.width, right.range)
            && right.range.end <= right_row.declaration.width;
        if let StructureFieldType::Struct(position) = a.ty {
            let ls = left_index.entries_model();
            let rs = right_index.entries_model();
            let x = choose|j: int| 0 <= j < ls.len() && (#[trigger] ls[j]).position == position
                && ls[j].declaration.width == a.width;
            let y = choose|j: int| 0 <= j < rs.len() && (#[trigger] rs[j]).position == position
                && rs[j].declaration.width == b.width;
            self.targets.parsed_project_model();
            self.structure_row_evidence(left_index, limit, ls[x]);
            self.structure_row_evidence(right_index, limit, rs[y]);
            self.resolved_structures_agree(position, limit, ls[x].declaration, rs[y].declaration);
        }
    }

    /// ビット列と構造体型のフィールドを半開区間に配置する。
    ///
    /// 構造体型のフィールド幅には、参照先が宣言した総幅を使う。
    /// 宣言順を保持し、空きビットの区間を詰めない。型参照の循環は別途検査する。
    ///
    /// # Examples
    ///
    /// 宣言順がビット位置の順と異なる場合も、区間は各フィールドの `at` に従う。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "layout.ncg2", revision: 1,
    ///     text: "(struct Word (width 8))
    ///         (struct Packet (width 16) (data Word (at 8)) (flag (bits 1) (at 0)))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let layouts = aliases.check_structure_layouts(16).unwrap();
    /// let packet = &layouts.entries()[1];
    /// assert_eq!(packet.width, 16);
    /// assert_eq!(packet.fields[0].range, 8..16);
    /// assert_eq!(packet.fields[1].range, 0..1);
    /// ```
    ///
    /// # Errors
    ///
    /// プロジェクト全体の数値と型名を検査してから、宣言順に各フィールドを配置する。
    /// 各フィールドは先に範囲を検査し、その後に衝突する最初の先行フィールドを探す。
    /// 同じ先行フィールドと名前も区間も衝突したときは、名前の重複を返す。
    pub fn check_structure_layouts(&self, limit: u64)
        -> (result: Result<StructureLayouts<'p, 'a>, StructureLayoutError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.structure_layouts_match(limit, result),
    {
        let index = match self.index_resolved_structures(limit) {
            Ok(index) => index,
            Err(error) => return Err(StructureLayoutError::Resolution(error)),
        };
        self.place_resolved_structures(&index, limit)
    }

    proof fn layouts_preserve_order_and_ranges(
        &self, index: &ResolvedStructures, limit: u64, layouts: Seq<StructureLayout>,
    )
        requires
            self.structure_index_matches(limit, Ok(*index)),
            self.layouts_before(index, layouts),
            layouts.len() == index.entries_model().len(),
        ensures
            forall|i: int, j: int| 0 <= i < j < layouts.len() ==>
                structure_before((#[trigger] layouts[i]).position, (#[trigger] layouts[j]).position),
            forall|i: int| 0 <= i < layouts.len() ==> {
                let entry = #[trigger] layouts[i];
                &&& entry.width > 0
                &&& forall|j: int| 0 <= j < entry.fields@.len() ==> {
                    let field = #[trigger] entry.fields@[j];
                    &&& field.range.start < field.range.end <= entry.width
                    &&& representation_width(layouts, field.ty, field.range.end - field.range.start)
                }
            },
    {
        reveal(UseAliases::structure_index_matches);
        let rows = index.entries_model();
        assert(super::entries_in_order(rows));
        assert forall|i: int, j: int| 0 <= i < j < layouts.len() implies
            structure_before((#[trigger] layouts[i]).position, (#[trigger] layouts[j]).position) by {
            assert(self.layout_row_result(index, rows[i], Ok(layouts[i])));
            assert(self.layout_row_result(index, rows[j], Ok(layouts[j])));
            assert(structure_before(rows[i].position, rows[j].position));
        };
        reveal(UseAliases::structure_layout_prefix);
        assert forall|i: int| 0 <= i < layouts.len() implies {
            let entry = #[trigger] layouts[i];
            &&& entry.width > 0
            &&& forall|j: int| 0 <= j < entry.fields@.len() ==> {
                let field = #[trigger] entry.fields@[j];
                &&& field.range.start < field.range.end <= entry.width
                &&& representation_width(layouts, field.ty, field.range.end - field.range.start)
            }
        } by {
            assert(self.layout_row_result(index, rows[i], Ok(layouts[i])));
            assert forall|j: int| 0 <= j < layouts[i].fields@.len() implies {
                let field = #[trigger] layouts[i].fields@[j];
                &&& field.range.start < field.range.end <= layouts[i].width
                &&& representation_width(layouts, field.ty, field.range.end - field.range.start)
            } by {
                let output = layouts[i].fields@[j];
                assert(self.layout_field_at(index, rows[i], j, output));
                let field = choose|field: FieldPlacement| #[trigger] self.field_placement_input(index, rows[i], j, field)
                    && output.name == field.name && output.location == field.location && output.ty == field.ty
                    && field_range_matches(field.offset, field.width, output.range)
                    && output.range.end <= rows[i].declaration.width;
                if let StructureFieldType::Struct(position) = field.ty {
                    let target = choose|target: int| 0 <= target < rows.len()
                        && (#[trigger] rows[target]).position == position && rows[target].declaration.width == field.width;
                    assert(self.layout_row_result(index, rows[target], Ok(layouts[target])));
                    assert(representation_width(layouts, output.ty, output.range.end - output.range.start));
                }
            };
        };
    }

    fn place_resolved_structures(&self, index: &ResolvedStructures, limit: u64)
        -> (result: Result<StructureLayouts<'p, 'a>, StructureLayoutError<'p, 'a>>)
        requires self.can_resolve(), self.structure_index_matches(limit, Ok(*index)),
        ensures self.layouts_for_index(index, result),
    {
        let rows = index.entries();
        let mut layouts = Vec::new();
        let mut i = 0;
        while i < rows.len()
            invariant
                self.can_resolve(),
                self.structure_index_matches(limit, Ok(*index)),
                rows@ == index.entries_model(),
                i == layouts@.len() <= rows@.len(),
                self.layouts_before(index, layouts@),
            decreases rows@.len() - i,
        {
            let row = &rows[i];
            assert(rows@.contains(*row));
            let layout = match self.place_structure(index, limit, row) {
                Ok(layout) => layout,
                Err(error) => return Err(StructureLayoutError::Placement { position: row.position, error }),
            };
            layouts.push(layout);
            i += 1;
        }
        proof { self.layouts_preserve_order_and_ranges(index, limit, layouts@); }
        Ok(StructureLayouts { entries: layouts })
    }
}

} // verus!
