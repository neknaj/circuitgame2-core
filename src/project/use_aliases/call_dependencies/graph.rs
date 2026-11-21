//! 関数の依存グラフを検査し、閉路の各辺を元の呼び出しに戻す。

use super::super::dependency_order::{DependencyEdge, check_dependency_order};
#[cfg(verus_only)]
use super::super::dependency_order::{
    complete_dependency_order, dependency_cycle, dependency_edge,
    dependency_graph_valid, graph_has_cycle,
};
use super::super::function_atoms::copy_location;
use super::super::{DefinitionBatchError, DefinitionBinding, DefinitionPosition, IndexedDefinitionBinding, UseAliases};
use crate::syntax::circuit::{ExpressionReferenceKind, Head};
use super::vertices::FunctionVertices;
#[cfg(verus_only)]
use super::vertices::function_position;
#[cfg(verus_only)]
use super::CallDependency;
use crate::project::{CircuitProject, LocatedName};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 閉路を構成する一つの呼び出しと、解決した関数宣言。
#[derive(Debug)]
pub struct FunctionCallSite<'p, 'a> {
    /// 呼び出し元のファイル、索引項目、定義、参照の添字。
    pub position: DefinitionPosition,
    /// 呼び出し先のファイルと索引項目の添字。
    pub target: (usize, usize),
    /// 呼び出し先名が現れた元ソースの範囲。
    pub location: LocatedName<'p, 'a>,
}

/// 関数を展開する前の参照解決または循環検査で見つかった違反。
#[derive(Debug)]
pub enum FunctionExpansionError<'p, 'a> {
    /// 元ソース順に調べて最初に解決できなかった定義参照。
    Reference(DefinitionBatchError<'p, 'a>),
    /// 先頭の呼び出し元へ戻る一つ以上の呼び出し。
    Cycle(Vec<FunctionCallSite<'p, 'a>>),
}

/// 依存辺と、同じ参照を指す解決結果の添字。
pub(in crate::project::use_aliases) struct IndexedFunctionCallSite<'p, 'a> {
    pub(in crate::project::use_aliases) _binding: Ghost<usize>,
    pub(in crate::project::use_aliases) site: FunctionCallSite<'p, 'a>,
}

/// 同じ頂点順を使う隣接リストと呼び出し位置。
struct FunctionGraph<'p, 'a> {
    graph: Vec<Vec<Option<usize>>>,
    sites: Vec<Vec<usize>>,
    flat: Vec<IndexedFunctionCallSite<'p, 'a>>,
}

/// 呼び出し先を呼び出し元より先に並べた、プロジェクト内の関数の展開順。
#[derive(Debug)]
pub struct FunctionExpansionOrder<'p, 'a> {
    project: &'p CircuitProject<'a>,
    vertices: FunctionVertices,
    order: Vec<usize>,
}

impl<'p, 'a> FunctionExpansionOrder<'p, 'a> {
    /// 宣言位置が参照する、構文解析済みのプロジェクト。
    pub fn project(&self) -> (project: &'p CircuitProject<'a>)
        ensures *project == self.project_model(),
    { self.project }

    /// 宣言位置が参照するプロジェクトを表す。
    pub closed spec fn project_model(&self) -> CircuitProject<'a> { *self.project }

    /// 展開順に並ぶ関数の個数。
    pub fn len(&self) -> (count: usize)
        ensures count == self.order_model().len(),
    { self.order.len() }

    /// プロジェクト内に展開対象の関数がないかを返す。
    pub fn is_empty(&self) -> (empty: bool)
        ensures empty <==> self.order_model().len() == 0,
    { self.order.len() == 0 }

    /// 展開順の添字から、宣言のファイルと厳格索引項目の添字を得る。
    /// 範囲外では `None` を返す。
    pub fn get(&self, index: usize) -> (position: Option<(usize, usize)>)
        ensures position == self.position_model(index as int),
    {
        if index >= self.order.len() { return None; }
        let vertex = self.order[index];
        let positions = self.vertices.positions();
        if vertex >= positions.len() { return None; }
        Some(positions[vertex])
    }

    /// 展開順を内部の頂点番号列で表す。
    pub closed spec fn order_model(&self) -> Seq<usize> { self.order@ }

    /// 展開順の添字に対応するソース上の宣言位置。
    pub closed spec fn position_model(&self, index: int) -> Option<(usize, usize)> {
        let vertices = self.vertices.positions_model();
        if 0 <= index < self.order@.len() && self.order@[index] < vertices.len() {
            Some(vertices[self.order@[index] as int])
        } else {
            None
        }
    }

    /// 展開する宣言を頂点番号で引き、展開済み回路を格納する位置を求める。
    pub(in crate::project::use_aliases) fn template_vertex(&self, position: (usize, usize))
        -> (vertex: Option<usize>)
        ensures self.template_vertex_matches(position, vertex),
    {
        self.vertices.get(position)
    }

    /// 展開順の位置から、同じ関数の格納先となる頂点番号を返す。
    pub(in crate::project::use_aliases) fn template_at(&self, index: usize) -> (vertex: Option<usize>)
        ensures vertex == if index < self.order_model().len() { Some(self.order_model()[index as int]) } else { None },
    {
        if index < self.order.len() { Some(self.order[index]) } else { None }
    }

    pub(in crate::project::use_aliases) closed spec fn template_vertex_matches(
        &self, position: (usize, usize), vertex: Option<usize>,
    ) -> bool {
        self.vertices.vertex_at(position, vertex)
    }

    pub(in crate::project::use_aliases) proof fn template_vertex_at_position(
        &self, position: (usize, usize), at: int, vertex: Option<usize>,
    )
        requires self.position_model(at) == Some(position), self.template_vertex_matches(position, vertex),
        ensures 0 <= at < self.order_model().len(), vertex == Some(self.order_model()[at]),
    {
        assert(self.vertices.positions_model()[self.order@[at] as int] == position);
    }

    /// 展開順が全関数の宣言位置を重複なく含むことを表す。
    pub closed spec fn source_positions_complete(&self) -> bool {
        let circuits = self.project_model().circuits_model();
        &&& forall|i: int| 0 <= i < self.order_model().len()
            ==> ((#[trigger] self.position_model(i)) matches Some(position) && function_position(circuits, position))
        &&& forall|position: (usize, usize)| #[trigger] function_position(circuits, position)
            ==> exists|i: int| 0 <= i < self.order_model().len() && #[trigger] self.position_model(i) == Some(position)
        &&& forall|i: int, j: int| 0 <= i < j < self.order_model().len()
            ==> (#[trigger] self.position_model(i)) != (#[trigger] self.position_model(j))
    }

    proof fn complete_order_covers_source(&self, graph: Seq<Vec<Option<usize>>>)
        requires
            self.vertices.matches(&self.project_model()),
            self.vertices.positions_model().len() == graph.len(),
            complete_dependency_order(graph, self.order_model()),
        ensures self.source_positions_complete(),
    {
        self.vertices.project_evidence(&self.project_model());
        let vertices = self.vertices.positions_model();
        let order = self.order_model();
        let circuits = self.project_model().circuits_model();
        let rank = choose|rank: Seq<nat>| #[trigger] super::super::dependency_order::dependencies_in_order(graph, rank)
            && order.len() == graph.len() && super::super::dependency_order::completion_order_matches(order, rank)
            && (forall|node: int| #![trigger rank[node]] 0 <= node < graph.len()
                ==> rank[node] < order.len() && order[rank[node] as int] == node);
        assert forall|i: int| 0 <= i < order.len()
            implies ((#[trigger] self.position_model(i)) matches Some(position)
                && function_position(circuits, position)) by {
            assert(order[i] < vertices.len());
        };
        assert forall|position: (usize, usize)| #[trigger] function_position(circuits, position)
            implies exists|i: int| 0 <= i < order.len() && #[trigger] self.position_model(i) == Some(position) by {
            let vertex = choose|v: int| 0 <= v < vertices.len() && (#[trigger] vertices[v]) == position;
            let i = rank[vertex] as int;
            assert(order[i] == vertex);
            assert(self.position_model(i) == Some(position));
        };
        assert forall|i: int, j: int| 0 <= i < j < order.len()
            implies (#[trigger] self.position_model(i)) != (#[trigger] self.position_model(j)) by {
            assert(rank[order[i] as int] == i);
            assert(rank[order[j] as int] == j);
            let a = order[i] as int;
            let b = order[j] as int;
            assert(self.position_model(i) == Some(vertices[a]));
            assert(self.position_model(j) == Some(vertices[b]));
            if a < b { assert(vertices[a] != vertices[b]); }
            if b < a { assert(vertices[b] != vertices[a]); }
        };
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    spec fn is_function_dependency(&self, item: IndexedDefinitionBinding) -> bool {
        &&& item.resolved.site.owner is Func
        &&& item.resolved.site.role is Callee
        &&& item.resolved.binding is Declaration
    }

    #[verifier::opaque]
    pub(in crate::project::use_aliases) open spec fn function_call_site_matches(
        &self, site: FunctionCallSite,
    ) -> bool {
        let at = site.position;
        &&& self.func_call_at(at.file, at.entry, at.definition, at.reference)
        &&& self.call_dependency_matches((at.file, at.entry, at.definition, at.reference),
            Ok(Some(CallDependency { target: site.target, reference: site.location })))
        &&& crate::project::location_in_source(site.location)
    }

    proof fn function_call_endpoints(&self, site: FunctionCallSite)
        requires self.function_call_site_matches(site),
        ensures ({
            let circuits = self.targets.project_model().circuits_model();
            &&& function_position(circuits, (site.position.file, site.position.entry))
            &&& function_position(circuits, site.target)
        }),
    {
        reveal(UseAliases::function_call_site_matches);
        let at = site.position;
        let edge = CallDependency { target: site.target, reference: site.location };
        let resolved = choose|resolved: super::ResolvedDefinitionReference|
            #[trigger] self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, Ok(resolved))
            && self.resolved_call_dependency_matches(resolved, Some(edge));
        assert(self.func_position_matches(resolved.binding, Some(site.target)));
    }

    #[verifier::opaque]
    pub(in crate::project::use_aliases) closed spec fn function_call_sites_match(
        &self, found: Seq<IndexedDefinitionBinding>, processed: int, sites: Seq<IndexedFunctionCallSite>,
    ) -> bool {
        &&& 0 <= processed <= found.len()
        &&& forall|i: int| 0 <= i < sites.len() ==> {
            let row = #[trigger] sites[i];
            &&& row._binding@ < processed
            &&& self.is_function_dependency(found[row._binding@ as int])
            &&& row.site.position == found[row._binding@ as int].position
            &&& self.function_call_site_matches(row.site)
        }
        &&& forall|i: int, j: int| 0 <= i < j < sites.len()
            ==> (#[trigger] sites[i])._binding@ < (#[trigger] sites[j])._binding@
        &&& forall|at: int| 0 <= at < processed && #[trigger] self.is_function_dependency(found[at])
            ==> exists|i: int| 0 <= i < sites.len() && (#[trigger] sites[i])._binding@ == at
    }

    proof fn extend_function_call_sites(
        &self, found: Seq<IndexedDefinitionBinding>, at: int, before: Seq<IndexedFunctionCallSite>,
        added: Option<IndexedFunctionCallSite>,
    )
        requires
            self.function_call_sites_match(found, at, before),
            at < found.len(),
            added.is_some() <==> self.is_function_dependency(found[at]),
            added matches Some(row) ==> row._binding@ == at && row.site.position == found[at].position
                && self.function_call_site_matches(row.site),
        ensures self.function_call_sites_match(found, at + 1,
            if let Some(row) = added { before.push(row) } else { before }),
    {
        reveal(UseAliases::function_call_sites_match);
        let after = if let Some(row) = added { before.push(row) } else { before };
        assert forall|i: int| 0 <= i < after.len() implies {
            let row = #[trigger] after[i];
            &&& row._binding@ < at + 1
            &&& self.is_function_dependency(found[row._binding@ as int])
            &&& row.site.position == found[row._binding@ as int].position
            &&& self.function_call_site_matches(row.site)
        } by {
            if i < before.len() { assert(after[i] == before[i]); }
        };
        assert forall|i: int, j: int| 0 <= i < j < after.len()
            implies (#[trigger] after[i])._binding@ < (#[trigger] after[j])._binding@ by {
            assert(after[i] == before[i]);
            if j < before.len() { assert(after[j] == before[j]); }
        };
        assert forall|i: int| 0 <= i < at + 1 && #[trigger] self.is_function_dependency(found[i])
            implies exists|j: int| 0 <= j < after.len() && (#[trigger] after[j])._binding@ == i by {
            if i < at {
                let j = choose|j: int| 0 <= j < before.len() && (#[trigger] before[j])._binding@ == i;
                assert(after[j] == before[j]);
            } else {
                assert(after[before.len() as int] == added->Some_0);
            }
        };
    }

    /// 解決済み参照を元の順序で走査し、関数宣言に解決した呼び出しだけを集める。
    pub(in crate::project::use_aliases) fn collect_function_call_sites(
        &self, found: &[IndexedDefinitionBinding<'p, 'a>],
    ) -> (sites: Vec<IndexedFunctionCallSite<'p, 'a>>)
        requires self.can_resolve(), self.definition_bindings_match(found@),
        ensures self.function_call_sites_match(found@, found@.len() as int, sites@),
    {
        let mut sites = Vec::new();
        assert(self.function_call_sites_match(found@, 0, sites@)) by {
            reveal(UseAliases::function_call_sites_match);
        };
        let mut i = 0;
        while i < found.len()
            invariant
                self.can_resolve(), self.definition_bindings_match(found@),
                i <= found@.len(), self.function_call_sites_match(found@, i as int, sites@),
            decreases found@.len() - i,
        {
            let item = &found[i];
            let at = item.position;
            if matches!(item.resolved.site.owner, Head::Func) && matches!(item.resolved.site.role, ExpressionReferenceKind::Callee)
                && matches!(item.resolved.binding, DefinitionBinding::Declaration { .. })
            {
                proof {
                    assert(self.is_function_dependency(*item)) by { reveal(UseAliases::is_function_dependency); }
                    self.definition_binding_at(found@, i as int);
                    self.resolved_reference_is_func_call(at, item.resolved);
                }
                let edge = self.call_dependency_from_binding(
                    Ghost((at.file, at.entry, at.definition, at.reference)), &item.resolved);
                let Some(edge) = edge else {
                    proof { assert(false); }
                    unreachable!()
                };
                let row = IndexedFunctionCallSite {
                    _binding: Ghost(i), site: FunctionCallSite { position: at, target: edge.target, location: edge.reference },
                };
                proof {
                    assert(self.function_call_site_matches(row.site)) by { reveal(UseAliases::function_call_site_matches); }
                    self.extend_function_call_sites(found@, i as int, sites@, Some(row));
                }
                sites.push(row);
            } else {
                proof {
                    assert(!self.is_function_dependency(*item)) by { reveal(UseAliases::is_function_dependency); }
                    self.extend_function_call_sites(found@, i as int, sites@, None);
                }
            }
            i += 1;
        }
        sites
    }

    pub(in crate::project::use_aliases) open spec fn function_graph_sites_match(
        &self, vertices: Seq<(usize, usize)>, graph: Seq<Vec<Option<usize>>>,
        flat: Seq<IndexedFunctionCallSite>, sites: Seq<Vec<usize>>,
    ) -> bool {
        &&& graph.len() == vertices.len() == sites.len()
        &&& forall|from: int| 0 <= from < graph.len() ==> (#[trigger] graph[from])@.len() == sites[from]@.len()
        &&& forall|from: int, i: int| 0 <= from < graph.len() && 0 <= i < graph[from]@.len() ==> {
            let index = sites[from]@[i];
            let site = flat[index as int].site;
            &&& (#[trigger] graph[from]@[i]) matches Some(to)
            &&& index < flat.len()
            &&& to < vertices.len()
            &&& vertices[from] == (site.position.file, site.position.entry)
            &&& vertices[to as int] == site.target
            &&& self.function_call_site_matches(site)
        }
    }

    #[verifier::opaque]
    spec fn has_call_index(rows: Seq<Vec<usize>>, index: int) -> bool {
        exists|r: int, j: int| 0 <= r < rows.len() && 0 <= j < rows[r]@.len()
            && (#[trigger] rows[r]@[j]) == index
    }

    spec fn call_site_prefix_matches(
        &self, processed: int, rows: Seq<Vec<usize>>,
    ) -> bool {
        &&& 0 <= processed
        &&& forall|r: int, j: int| 0 <= r < rows.len() && 0 <= j < rows[r]@.len()
            ==> (#[trigger] rows[r]@[j]) < processed
        &&& forall|r: int, j: int, k: int| 0 <= r < rows.len() && 0 <= j < k < rows[r]@.len()
            ==> (#[trigger] rows[r]@[j]) < (#[trigger] rows[r]@[k])
        &&& forall|i: int| 0 <= i < processed ==> #[trigger] Self::has_call_index(rows, i)
    }

    proof fn append_call_site(
        &self, processed: usize, rows: Seq<Vec<usize>>, after: Seq<Vec<usize>>, from: int,
    )
        requires
            self.call_site_prefix_matches(processed as int, rows),
            0 <= from < rows.len(), after.len() == rows.len(),
            after[from]@ == rows[from]@.push(processed),
            forall|r: int| 0 <= r < rows.len() && r != from ==> (#[trigger] after[r]) == rows[r],
        ensures self.call_site_prefix_matches(processed + 1, after),
    {
        assert forall|r: int, j: int| 0 <= r < after.len() && 0 <= j < after[r]@.len()
            implies (#[trigger] after[r]@[j]) < processed + 1 by {
            if r == from && j == rows[r]@.len() {
                assert(after[r]@[j] == processed);
            } else {
                assert(after[r]@[j] == rows[r]@[j]);
            }
        };
        assert forall|r: int, j: int, k: int| 0 <= r < after.len() && 0 <= j < k < after[r]@.len()
            implies (#[trigger] after[r]@[j]) < (#[trigger] after[r]@[k]) by {
            assert(after[r]@[j] == rows[r]@[j]);
            if r != from || k < rows[r]@.len() { assert(after[r]@[k] == rows[r]@[k]); }
        };
        assert forall|i: int| 0 <= i < processed + 1 implies #[trigger] Self::has_call_index(after, i) by {
            reveal(UseAliases::has_call_index);
            if i < processed {
                assert(Self::has_call_index(rows, i));
                let r_j = choose|r: int, j: int| 0 <= r < rows.len() && 0 <= j < rows[r]@.len()
                    && (#[trigger] rows[r]@[j]) == i;
                assert(after[r_j.0]@[r_j.1] == rows[r_j.0]@[r_j.1]);
            } else {
                assert(after[from]@[rows[from]@.len() as int] == i);
            }
        };
    }

    fn materialize_function_graph(
        &self, vertices: &FunctionVertices, flat: Vec<IndexedFunctionCallSite<'p, 'a>>,
    ) -> (result: FunctionGraph<'p, 'a>)
        requires
            vertices.matches(&self.targets.project_model()),
            forall|i: int| 0 <= i < flat@.len() ==> self.function_call_site_matches((#[trigger] flat@[i]).site),
        ensures
            result.flat@ == flat@,
            self.function_graph_sites_match(vertices.positions_model(), result.graph@, flat@, result.sites@),
            self.call_site_prefix_matches(flat@.len() as int, result.sites@),
    {
        let positions = vertices.positions();
        let mut graph: Vec<Vec<Option<usize>>> = Vec::new();
        let mut sites: Vec<Vec<usize>> = Vec::new();
        let mut vertex = 0;
        while vertex < positions.len()
            invariant
                vertex <= positions@.len(), graph@.len() == vertex, sites@.len() == vertex,
                forall|r: int| 0 <= r < vertex ==> (#[trigger] graph@[r])@.len() == 0,
                forall|r: int| 0 <= r < vertex ==> (#[trigger] sites@[r])@.len() == 0,
            decreases positions@.len() - vertex,
        {
            graph.push(Vec::new());
            sites.push(Vec::new());
            vertex += 1;
        }
        let mut i = 0;
        while i < flat.len()
            invariant
                i <= flat@.len(), positions@ == vertices.positions_model(),
                vertices.matches(&self.targets.project_model()),
                forall|j: int| 0 <= j < flat@.len() ==> self.function_call_site_matches((#[trigger] flat@[j]).site),
                self.function_graph_sites_match(positions@, graph@, flat@, sites@),
                self.call_site_prefix_matches(i as int, sites@),
            decreases flat@.len() - i,
        {
            let site = &flat[i].site;
            let caller = (site.position.file, site.position.entry);
            proof {
                self.function_call_endpoints(*site);
                vertices.project_evidence(&self.targets.project_model());
            }
            let Some(from) = vertices.get(caller) else {
                proof { assert(false); }
                unreachable!()
            };
            let Some(to) = vertices.get(site.target) else {
                proof { assert(false); }
                unreachable!()
            };
            let ghost before_graph = graph@;
            let ghost before_sites = sites@;
            graph[from].push(Some(to));
            sites[from].push(i);
            proof {
                assert forall|r: int| 0 <= r < sites@.len() && r != from
                    implies (#[trigger] sites@[r]) == before_sites[r] by {};
                self.append_call_site(i, before_sites, sites@, from as int);
                assert forall|r: int, j: int| 0 <= r < graph@.len() && 0 <= j < graph@[r]@.len() implies {
                    let index = sites@[r]@[j];
                    let added = flat@[index as int].site;
                    &&& (#[trigger] graph@[r]@[j]) matches Some(next)
                    &&& index < flat@.len()
                    &&& next < positions@.len()
                    &&& positions@[r] == (added.position.file, added.position.entry)
                    &&& positions@[next as int] == added.target
                    &&& self.function_call_site_matches(added)
                } by {
                    if r != from || j < before_graph[r]@.len() {
                        assert(graph@[r]@[j] == before_graph[r]@[j]);
                        assert(sites@[r]@[j] == before_sites[r]@[j]);
                    }
                };
            }
            i += 1;
        }
        FunctionGraph { graph, sites, flat }
    }

    #[verifier::opaque]
    pub(in crate::project::use_aliases) open spec fn function_cycle_matches(
        &self, vertices: Seq<(usize, usize)>, graph: Seq<Vec<Option<usize>>>,
        flat: Seq<IndexedFunctionCallSite>, sites: Seq<Vec<usize>>, cycle: Seq<DependencyEdge>,
        references: Seq<FunctionCallSite>,
    ) -> bool {
        &&& dependency_cycle(graph, cycle)
        &&& references.len() == cycle.len()
        &&& forall|i: int| 0 <= i < references.len() ==> {
            let edge = cycle[i];
            let reference = #[trigger] references[i];
            &&& reference == flat[sites[edge.from as int]@[edge.field as int] as int].site
            &&& self.function_call_site_matches(reference)
            &&& (reference.position.file, reference.position.entry) == vertices[edge.from as int]
            &&& reference.target == vertices[edge.to as int]
        }
        &&& forall|i: int, j: int| 0 <= i && j == i + 1 && j < references.len() ==> {
            let next = (#[trigger] references[j]).position;
            (#[trigger] references[i]).target == (next.file, next.entry)
        }
        &&& references.last().target == (references[0].position.file, references[0].position.entry)
    }

    fn function_cycle_sites(
        &self, Ghost(vertices): Ghost<Seq<(usize, usize)>>,
        Ghost(graph): Ghost<Seq<Vec<Option<usize>>>>, flat: &[IndexedFunctionCallSite<'p, 'a>], sites: &[Vec<usize>],
        cycle: &[DependencyEdge],
    ) -> (references: Vec<FunctionCallSite<'p, 'a>>)
        requires self.function_graph_sites_match(vertices, graph, flat@, sites@), dependency_cycle(graph, cycle@),
        ensures self.function_cycle_matches(vertices, graph, flat@, sites@, cycle@, references@),
    {
        let mut references = Vec::new();
        let mut index = 0;
        while index < cycle.len()
            invariant
                self.function_graph_sites_match(vertices, graph, flat@, sites@), dependency_cycle(graph, cycle@),
                index == references@.len() <= cycle@.len(),
                forall|i: int| 0 <= i < index ==> {
                    let edge = cycle@[i];
                    (#[trigger] references@[i]) == flat@[sites@[edge.from as int]@[edge.field as int] as int].site
                },
            decreases cycle@.len() - index,
        {
            let edge = cycle[index];
            assert(dependency_edge(graph, edge));
            assert(graph[edge.from as int]@[edge.field as int] == Some(edge.to));
            let index_at_site = sites[edge.from][edge.field];
            let site = &flat[index_at_site].site;
            references.push(FunctionCallSite {
                position: site.position,
                target: site.target,
                location: copy_location(&site.location),
            });
            index += 1;
        }
        proof {
            reveal(UseAliases::function_cycle_matches);
            assert forall|i: int| 0 <= i < references@.len() implies {
                let edge = cycle@[i];
                let reference = #[trigger] references@[i];
                &&& reference == flat@[sites@[edge.from as int]@[edge.field as int] as int].site
                &&& self.function_call_site_matches(reference)
                &&& (reference.position.file, reference.position.entry) == vertices[edge.from as int]
                &&& reference.target == vertices[edge.to as int]
            } by {
                let edge = cycle@[i];
                assert(dependency_edge(graph, edge));
                assert(graph[edge.from as int]@[edge.field as int] == Some(edge.to));
            };
        }
        references
    }

    #[verifier::opaque]
    pub(in crate::project::use_aliases) open spec fn located_function_cycle(
        &self, vertices: Seq<(usize, usize)>, graph: Seq<Vec<Option<usize>>>,
        flat: Seq<IndexedFunctionCallSite>, sites: Seq<Vec<usize>>, references: Seq<FunctionCallSite>,
    ) -> bool {
        exists|cycle: Seq<DependencyEdge>|
            #[trigger] self.function_cycle_matches(vertices, graph, flat, sites, cycle, references)
    }

    /// 依存先が先に並ぶ順序を返す。循環があれば、閉路を構成する呼び出しを返す。
    pub(in crate::project::use_aliases) fn order_function_graph(
        &self, Ghost(vertices): Ghost<Seq<(usize, usize)>>, graph: &[Vec<Option<usize>>],
        flat: &[IndexedFunctionCallSite<'p, 'a>], sites: &[Vec<usize>],
    ) -> (result: Result<Vec<usize>, Vec<FunctionCallSite<'p, 'a>>>)
        requires self.function_graph_sites_match(vertices, graph@, flat@, sites@),
        ensures
            result.is_err() <==> graph_has_cycle(graph@),
            match result {
                Ok(order) => complete_dependency_order(graph@, order@),
                Err(references) => self.located_function_cycle(vertices, graph@, flat@, sites@, references@),
            },
    {
        assert(dependency_graph_valid(graph@)) by {
            assert forall|row: int, i: int| 0 <= row < graph@.len() && 0 <= i < graph@[row]@.len()
                implies ((#[trigger] graph@[row]@[i]) matches Some(target) ==> target < graph@.len()) by {};
        };
        match check_dependency_order(graph, true) {
            Ok(order) => {
                assert(complete_dependency_order(graph@, order@));
                return Ok(order);
            },
            Err(cycle) => {
                let references = self.function_cycle_sites(Ghost(vertices), Ghost(graph@), flat, sites, cycle.as_slice());
                assert(self.located_function_cycle(vertices, graph@, flat@, sites@, references@)) by {
                    reveal(UseAliases::located_function_cycle);
                    assert(self.function_cycle_matches(vertices, graph@, flat@, sites@, cycle@, references@));
                };
                return Err(references);
            },
        }
    }

    pub(in crate::project::use_aliases) closed spec fn function_expansion_order_matches(
        &self, found: Seq<IndexedDefinitionBinding>, result: Result<FunctionExpansionOrder, Vec<FunctionCallSite>>,
    ) -> bool {
        exists|flat: Seq<IndexedFunctionCallSite>, graph: Seq<Vec<Option<usize>>>,
            sites: Seq<Vec<usize>>, vertices: FunctionVertices|
            #![trigger self.function_call_sites_match(found, found.len() as int, flat),
                self.function_graph_sites_match(vertices.positions_model(), graph, flat, sites)]
            self.function_call_sites_match(found, found.len() as int, flat)
            && vertices.matches(&self.targets.project_model())
            && self.function_graph_sites_match(vertices.positions_model(), graph, flat, sites)
            && self.call_site_prefix_matches(flat.len() as int, sites)
            && match result {
                Ok(plan) => plan.project_model() == self.targets.project_model()
                    && plan.vertices == vertices && complete_dependency_order(graph, plan.order@)
                    && plan.source_positions_complete(),
                Err(references) => self.located_function_cycle(vertices.positions_model(), graph, flat, sites, references@),
            }
    }

    /// 解決済みのプロジェクトから、関数の展開順または再帰を構成する呼び出し列を得る。
    pub(in crate::project::use_aliases) fn function_expansion_order(
        &self, found: &[IndexedDefinitionBinding<'p, 'a>],
    ) -> (result: Result<FunctionExpansionOrder<'p, 'a>, Vec<FunctionCallSite<'p, 'a>>>)
        requires self.can_resolve(), self.definition_bindings_match(found@),
        ensures self.function_expansion_order_matches(found@, result),
    {
        let project = self.targets.project();
        let vertices = FunctionVertices::from_project(project);
        let flat = self.collect_function_call_sites(found);
        proof {
            assert forall|i: int| 0 <= i < flat@.len() implies self.function_call_site_matches((#[trigger] flat@[i]).site) by {
                reveal(UseAliases::function_call_sites_match);
            };
        }
        let graph = self.materialize_function_graph(&vertices, flat);
        let ghost positions = vertices.positions_model();
        let ghost index = vertices;
        let ordered = self.order_function_graph(Ghost(positions), graph.graph.as_slice(), graph.flat.as_slice(), graph.sites.as_slice());
        let result = match ordered {
            Ok(order) => {
                let plan = FunctionExpansionOrder { project, vertices, order };
                proof { plan.complete_order_covers_source(graph.graph@); }
                Ok(plan)
            },
            Err(references) => Err(references),
        };
        assert(self.function_expansion_order_matches(found@, result)) by {
            assert(index.matches(&self.targets.project_model()));
            assert(self.function_call_sites_match(found@, found@.len() as int, graph.flat@));
            assert(self.function_graph_sites_match(positions, graph.graph@, graph.flat@, graph.sites@));
            assert(self.call_site_prefix_matches(graph.flat@.len() as int, graph.sites@));
            assert(match result {
                Ok(plan) => plan.project_model() == self.targets.project_model()
                    && plan.vertices == index && complete_dependency_order(graph.graph@, plan.order@)
                    && plan.source_positions_complete(),
                Err(references) => self.located_function_cycle(positions, graph.graph@, graph.flat@, graph.sites@, references@),
            });
        };
        result
    }

    /// 展開準備の結果を、解決済み参照から得られる依存順または閉路に結び付ける。
    pub closed spec fn function_expansion_evidence(
        &self, result: Result<FunctionExpansionOrder, FunctionExpansionError>,
    ) -> bool {
        match result {
            Err(FunctionExpansionError::Reference(error)) => self.definition_batch_error_evidence(error),
            Ok(plan) => plan.source_positions_complete()
                && (exists|found: Seq<IndexedDefinitionBinding>| #[trigger] self.definition_bindings_match(found)
                    && self.function_expansion_order_matches(found, Ok(plan))),
            Err(FunctionExpansionError::Cycle(references)) => exists|found: Seq<IndexedDefinitionBinding>|
                #[trigger] self.definition_bindings_match(found)
                && self.function_expansion_order_matches(found, Err(references)),
        }
    }

    /// 展開順の各頂点を重複のない格納先として使えることを示す。
    pub(in crate::project::use_aliases) proof fn template_index_evidence(&self, plan: FunctionExpansionOrder)
        requires self.function_expansion_evidence(Ok(plan)),
        ensures
            plan.project_model() == self.targets.project_model(),
            forall|rank: int| 0 <= rank < plan.order_model().len() ==>
                (#[trigger] plan.order_model()[rank]) < plan.order_model().len()
                    && plan.position_model(rank).is_some(),
            forall|a: int, b: int| 0 <= a < b < plan.order_model().len() ==>
                (#[trigger] plan.order_model()[a]) != (#[trigger] plan.order_model()[b]),
    {
        let found = choose|found: Seq<IndexedDefinitionBinding>| #[trigger] self.definition_bindings_match(found)
            && self.function_expansion_order_matches(found, Ok(plan));
        let (flat, graph, sites, vertices) = choose|flat: Seq<IndexedFunctionCallSite>, graph: Seq<Vec<Option<usize>>>,
            sites: Seq<Vec<usize>>, vertices: FunctionVertices|
            #![trigger self.function_call_sites_match(found, found.len() as int, flat),
                self.function_graph_sites_match(vertices.positions_model(), graph, flat, sites)]
            self.function_call_sites_match(found, found.len() as int, flat)
            && vertices.matches(&self.targets.project_model())
            && self.function_graph_sites_match(vertices.positions_model(), graph, flat, sites)
            && self.call_site_prefix_matches(flat.len() as int, sites)
            && plan.project_model() == self.targets.project_model() && plan.vertices == vertices
            && complete_dependency_order(graph, plan.order@) && plan.source_positions_complete();
        let order = plan.order_model();
        let rank = choose|rank: Seq<nat>| #[trigger] super::super::dependency_order::dependencies_in_order(graph, rank)
            && order.len() == graph.len() && super::super::dependency_order::completion_order_matches(order, rank)
            && (forall|node: int| #![trigger rank[node]] 0 <= node < graph.len()
                ==> rank[node] < order.len() && order[rank[node] as int] == node);
        assert(rank.len() == graph.len());
        assert forall|a: int, b: int| 0 <= a < b < order.len()
            implies (#[trigger] order[a]) != (#[trigger] order[b]) by {
            assert(rank[order[a] as int] == a);
            assert(rank[order[b] as int] == b);
        };
        assert forall|i: int| 0 <= i < order.len() implies
            (#[trigger] order[i]) < order.len() && plan.position_model(i).is_some() by {
            assert(order[i] < rank.len());
            assert(plan.position_model(i).is_some()) by { reveal(FunctionExpansionOrder::source_positions_complete); };
        };
    }

    pub(in crate::project::use_aliases) proof fn template_rank_from_position(
        &self, plan: FunctionExpansionOrder, position: (usize, usize), first: int, other: int,
    )
        requires
            self.function_expansion_evidence(Ok(plan)),
            plan.position_model(first) == Some(position),
            plan.position_model(other) == Some(position),
        ensures first == other,
    {
        reveal(FunctionExpansionOrder::source_positions_complete);
        assert(0 <= first < plan.order_model().len());
        assert(0 <= other < plan.order_model().len());
        if first < other {
            assert(plan.position_model(first) != plan.position_model(other));
        } else if other < first {
            assert(plan.position_model(other) != plan.position_model(first));
        }
    }

    /// 循環診断の呼び出しが、元の関数参照と一致することを表す。
    pub closed spec fn expansion_call_in_source(&self, site: FunctionCallSite) -> bool {
        self.function_call_site_matches(site)
    }

    pub(in crate::project::use_aliases) proof fn expansion_site_for_binding(
        &self, at: DefinitionPosition, target: (usize, usize), binding: super::ResolvedDefinitionReference,
    ) -> (site: FunctionCallSite<'p, 'a>)
        requires
            self.func_call_at(at.file, at.entry, at.definition, at.reference),
            self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, Ok(binding)),
            self.func_position_matches(binding.binding, Some(target)),
        ensures site.position == at, site.target == target, self.expansion_call_in_source(site),
    {
        let location = LocatedName { source: binding.site.source, span: binding.site.name.span };
        self.resolved_reference_location(at.file, at.entry, at.definition, at.reference, binding);
        crate::project::declarations::located_name_evidence(location);
        let edge = CallDependency { target, reference: location };
        assert(self.resolved_call_dependency_matches(binding, Some(edge)));
        self.record_call_dependency((at.file, at.entry, at.definition, at.reference), binding, Some(edge));
        reveal(UseAliases::function_call_site_matches);
        FunctionCallSite { position: at, target, location }
    }

    /// 循環診断の各辺が、同じプロジェクトの呼び出しをつないで閉じることを示す。
    pub proof fn function_expansion_cycle_in_source(&self, references: Vec<FunctionCallSite>)
        requires self.function_expansion_evidence(Err(FunctionExpansionError::Cycle(references))),
        ensures
            references@.len() > 0,
            forall|i: int| 0 <= i < references@.len() ==> {
                let site = #[trigger] references@[i];
                self.expansion_call_in_source(site) && crate::project::location_in_source(site.location)
            },
            forall|i: int, j: int| 0 <= i && j == i + 1 && j < references@.len() ==> {
                let next = (#[trigger] references@[j]).position;
                (#[trigger] references@[i]).target == (next.file, next.entry)
            },
            references@.last().target == (references@[0].position.file, references@[0].position.entry),
    {
        let found = choose|found: Seq<IndexedDefinitionBinding>| #[trigger] self.definition_bindings_match(found)
            && self.function_expansion_order_matches(found, Err(references));
        let (flat, graph, sites, vertices) = choose|flat: Seq<IndexedFunctionCallSite>, graph: Seq<Vec<Option<usize>>>,
            sites: Seq<Vec<usize>>, vertices: FunctionVertices|
            #![trigger self.function_call_sites_match(found, found.len() as int, flat),
                self.function_graph_sites_match(vertices.positions_model(), graph, flat, sites)]
            self.function_call_sites_match(found, found.len() as int, flat)
            && vertices.matches(&self.targets.project_model())
            && self.function_graph_sites_match(vertices.positions_model(), graph, flat, sites)
            && self.call_site_prefix_matches(flat.len() as int, sites)
            && self.located_function_cycle(vertices.positions_model(), graph, flat, sites, references@);
        reveal(UseAliases::located_function_cycle);
        let cycle = choose|cycle: Seq<DependencyEdge>|
            #[trigger] self.function_cycle_matches(vertices.positions_model(), graph, flat, sites, cycle, references@);
        reveal(UseAliases::function_cycle_matches);
        reveal(UseAliases::function_call_site_matches);
        assert(self.function_cycle_matches(vertices.positions_model(), graph, flat, sites, cycle, references@));
    }

    /// 元の呼び出しに対し、展開順の添字を呼び出し先、呼び出し元の順に返す。
    pub proof fn function_expansion_callee_precedes(
        &self, plan: FunctionExpansionOrder, site: FunctionCallSite,
    ) -> (order: (int, int))
        requires
            self.can_resolve(),
            self.function_expansion_evidence(Ok(plan)),
            self.expansion_call_in_source(site),
        ensures
            0 <= order.0 < order.1 < plan.order_model().len(),
            plan.position_model(order.0) == Some(site.target),
            plan.position_model(order.1) == Some((site.position.file, site.position.entry)),
    {
        let found = choose|found: Seq<IndexedDefinitionBinding>| #[trigger] self.definition_bindings_match(found)
            && self.function_expansion_order_matches(found, Ok(plan));
        let (flat, graph, rows, vertices) = choose|flat: Seq<IndexedFunctionCallSite>, graph: Seq<Vec<Option<usize>>>,
            rows: Seq<Vec<usize>>, vertices: FunctionVertices|
            #![trigger self.function_call_sites_match(found, found.len() as int, flat),
                self.function_graph_sites_match(vertices.positions_model(), graph, flat, rows)]
            self.function_call_sites_match(found, found.len() as int, flat)
            && vertices.matches(&self.targets.project_model())
            && self.function_graph_sites_match(vertices.positions_model(), graph, flat, rows)
            && self.call_site_prefix_matches(flat.len() as int, rows)
            && plan.project_model() == self.targets.project_model() && plan.vertices == vertices
            && complete_dependency_order(graph, plan.order@) && plan.source_positions_complete();
        reveal(UseAliases::function_call_site_matches);
        let at = site.position;
        let caller = (at.file, at.entry, at.definition, at.reference);
        let i = self.definition_binding_index(found, at);
        self.definition_binding_at(found, i);
        let original = found[i];
        self.resolved_reference_is_func_call(at, original.resolved);
        let expected = CallDependency { target: site.target, reference: site.location };
        if original.resolved.binding is Nor {
            assert(self.call_dependency_matches(caller, Ok(None))) by {
                reveal(UseAliases::call_dependency_matches);
                assert(self.resolved_call_dependency_matches(original.resolved, None));
            };
            self.call_dependencies_agree(caller, Some(expected), None);
        }
        assert(self.is_function_dependency(original)) by { reveal(UseAliases::is_function_dependency); }
        reveal(UseAliases::function_call_sites_match);
        let slot = choose|j: int| 0 <= j < flat.len() && (#[trigger] flat[j])._binding@ == i;
        let selected = flat[slot].site;
        assert(selected.position == at);
        assert(self.function_call_site_matches(selected));
        self.call_dependencies_agree(caller, Some(expected),
            Some(CallDependency { target: selected.target, reference: selected.location }));
        assert(Self::has_call_index(rows, slot));
        reveal(UseAliases::has_call_index);
        let (from, column) = choose|r: int, j: int| 0 <= r < rows.len() && 0 <= j < rows[r]@.len()
            && (#[trigger] rows[r]@[j]) == slot;
        let targets = vertices.positions_model();
        vertices.project_evidence(&self.targets.project_model());
        vstd::std_specs::vec::axiom_spec_len(&graph[from]);
        assert(0 <= from < graph.len() <= usize::MAX && 0 <= column < graph[from]@.len() <= usize::MAX);
        let to = graph[from]@[column]->Some_0;
        assert(graph[from]@[column] is Some);
        assert(targets[from] == (site.position.file, site.position.entry));
        assert(targets[to as int] == site.target);
        assert(dependency_edge(graph, DependencyEdge { from: from as usize, field: column as usize, to }));
        let ordered = plan.order@;
        let rank = choose|rank: Seq<nat>| #[trigger] super::super::dependency_order::dependencies_in_order(graph, rank)
            && ordered.len() == graph.len() && super::super::dependency_order::completion_order_matches(ordered, rank)
            && (forall|node: int| #![trigger rank[node]] 0 <= node < graph.len()
                ==> rank[node] < ordered.len() && ordered[rank[node] as int] == node);
        (rank[to as int] as int, rank[from] as int)
    }

    /// プロジェクトの `func` を呼び出し先から展開できる順に並べる。
    ///
    /// すべての `def` の参照を先に解決する。関数の依存関係には入れ子の呼び出しを含め、
    /// 基底 NOR は除く。結果は `check_use_aliases` に渡したプロジェクトを参照する。
    /// 基底宣言の検査には `validate_circuit_basis` を使う。
    ///
    /// # Errors
    ///
    /// 定義参照を解決できない場合は最初の違反を、関数呼び出しが循環する場合は
    /// 閉路を構成する呼び出し先名のソース範囲を返す。
    pub fn prepare_function_expansion(&self)
        -> (result: Result<FunctionExpansionOrder<'p, 'a>, FunctionExpansionError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.function_expansion_evidence(result),
    {
        let found = match self.resolve_definitions() {
            Ok(found) => found,
            Err(error) => return Err(FunctionExpansionError::Reference(error)),
        };
        let ordered = self.function_expansion_order(found.as_slice());
        let ghost model = ordered;
        let result = match ordered {
            Ok(plan) => Ok(plan),
            Err(references) => Err(FunctionExpansionError::Cycle(references)),
        };
        assert(self.function_expansion_evidence(result)) by {
            if let Ok(plan) = model {
                assert(plan.source_positions_complete());
            }
        };
        result
    }
}

} // verus!
