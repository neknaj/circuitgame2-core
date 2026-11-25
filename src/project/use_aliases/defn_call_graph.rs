//! NCG2M の補助関数の呼び出しを並べ、循環があれば元の呼び出しを返す。

use alloc::vec::Vec;
use vstd::prelude::*;
use crate::ncg2m::{
    call_evaluation::{CallArguments, DefnEvaluationBody}, expression_types::DefnBodyCallError,
};
use crate::project::ParsedProjectSources;
use super::{DefnCallEdge, DefnCallSite, DefnPosition, MixedUseAliases};
use super::dependency_order::{DependencyEdge, check_dependency_order};
#[cfg(verus_only)]
use super::dependency_order::{complete_dependency_order, completion_order_matches, dependencies_in_order,
    dependency_cycle, dependency_edge, dependency_graph_valid};
#[cfg(verus_only)]
use super::super::declarations::{defn_position_before, defn_vertices_valid};
#[cfg(verus_only)]
use super::super::exports::mixed_exports_use_project_declarations;
#[cfg(verus_only)]
use super::super::mixed_use_targets_match;
#[cfg(verus_only)]
use super::call_site::{named_body_check_belongs_to_project, named_body_matches_project, project_named_defn_body_matches};
#[cfg(verus_only)]
use crate::ncg2m::data_types::DefnSignature;
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use crate::ncg2m::expression_types::named_call::{defn_body_calls_cover_slots, defn_call_arguments, defn_call_edge_matches, defn_call_is_expression_slot};

verus! {

/// 補助関数の呼び出し順を求められなかった理由。
#[derive(Debug)]
pub enum DefnCallGraphError<'p, 'a> {
    /// 補助関数の本体で診断または段階の確定待ちが生じた。
    Body {
        /// 本体を検査した補助関数。
        from: DefnPosition,
        /// 呼び出しまたは式の診断。
        error: DefnBodyCallError<'p, 'a>,
    },
    /// 型検査の記録から漏れた、本体内の補助関数の呼び出し。
    ///
    /// 構文上の式の位置と型検査の記録が食い違ったことを示す。
    UnvisitedCall(DefnCallEdge<'p, 'a>),
    /// 元の呼び出しを順につないだ閉路。最後の呼び出し先は先頭の呼び出し元に戻る。
    Cycle(Vec<DefnCallEdge<'p, 'a>>),
}

/// 検査した補助関数と、呼び出し先を先に並べた順序。
pub struct DefnCallPlan<'p, 'a> {
    project: &'p ParsedProjectSources<'a>,
    vertices: Vec<DefnPosition>,
    edges: Vec<Vec<DefnCallEdge<'p, 'a>>>,
    order: Vec<usize>,
    ranks: Vec<usize>,
}

spec fn reverse_order_matches(order: Seq<usize>, ranks: Seq<usize>) -> bool {
    &&& order.len() == ranks.len()
    &&& forall|i: int| 0 <= i < order.len() ==> {
        let node = #[trigger] order[i];
        node < ranks.len() && ranks[node as int] == i
    }
    &&& forall|node: int| 0 <= node < ranks.len() ==> {
        let rank = #[trigger] ranks[node];
        rank < order.len() && order[rank as int] == node
    }
}

fn invert_call_order(order: &[usize], Ghost(expected): Ghost<Seq<nat>>) -> (ranks: Vec<usize>)
    requires
        order@.len() == expected.len(),
        completion_order_matches(order@, expected),
        forall|node: int| 0 <= node < expected.len() ==> {
            let rank = #[trigger] expected[node];
            rank < order@.len() && order@[rank as int] == node
        },
    ensures reverse_order_matches(order@, ranks@),
{
    let mut ranks = Vec::new();
    while ranks.len() < order.len()
        invariant ranks@.len() <= order@.len(),
        decreases order@.len() - ranks@.len(),
    {
        ranks.push(0usize);
    }
    let mut i = 0;
    while i < order.len()
        invariant
            i <= order@.len() == ranks@.len() == expected.len(),
            completion_order_matches(order@, expected),
            forall|node: int| 0 <= node < expected.len() ==> {
                let rank = #[trigger] expected[node];
                rank < order@.len() && order@[rank as int] == node
            },
            forall|j: int| 0 <= j < i ==> {
                let node = #[trigger] order@[j];
                node < ranks@.len() && ranks@[node as int] == j
            },
        decreases order@.len() - i,
    {
        let node = order[i];
        let ghost previous = ranks@;
        ranks.set(node, i);
        proof {
            assert forall|j: int| 0 <= j < i implies {
                let older = #[trigger] order@[j];
                older < ranks@.len() && ranks@[older as int] == j
            } by {
                assert(expected[order@[j] as int] == j);
                assert(expected[node as int] == i);
                assert(order@[j] != node);
                assert(ranks@[order@[j] as int] == previous[order@[j] as int]);
            };
        }
        i += 1;
    }
    proof {
        assert forall|node: int| 0 <= node < ranks@.len() implies {
            let rank = #[trigger] ranks@[node];
            rank < order@.len() && order@[rank as int] == node
        } by {
            assert(order@[expected[node] as int] == node);
            assert(ranks@[node] == expected[node]);
        };
    }
    ranks
}

#[verifier::opaque]
spec fn anchored_arguments(project: &ParsedProjectSources, vertices: Seq<DefnPosition>, rows: Seq<Vec<DefnCallEdge>>) -> bool {
    &&& rows.len() == vertices.len()
    &&& forall|row: int, site: int| 0 <= row < rows.len() && 0 <= site < rows[row]@.len() ==> {
        let edge = #[trigger] rows[row]@[site];
        &&& edge.from == vertices[row]
        &&& edge.from.file < project.sources_model().len()
        &&& *edge.call.source == project.sources_model()[edge.from.file as int]
        &&& project.functional_forms_model(edge.from.file) matches Some(forms)
            && defn_call_arguments(forms, edge.at, edge.arguments@)
        &&& project.indexed_defn(edge.to.file, edge.to.item) matches Some(header)
            && edge.arguments@.len() == header.parameters@.len()
    }
}

#[verifier::opaque]
spec fn ordered_edges(
    project: &ParsedProjectSources, vertices: Seq<DefnPosition>, edges: Seq<Vec<DefnCallEdge>>,
    order: Seq<usize>, ranks: Seq<usize>,
) -> bool {
    &&& forall|row: int| 0 <= row < vertices.len() ==> {
        let pos = #[trigger] vertices[row];
        project.indexed_defn(pos.file, pos.item).is_some()
    }
    &&& forall|row: int, site: int| 0 <= row < edges.len() && 0 <= site < edges[row]@.len() ==> {
        let edge = #[trigger] edges[row]@[site];
        let ranked = order.map_values(|node: usize| vertices[node as int]);
        &&& ranked.contains(edge.to)
        &&& ranked.index_of(edge.to) < ranks[row]
    }
}

impl<'p, 'a> DefnCallPlan<'p, 'a> {
    #[verifier::type_invariant]
    spec fn indexes_are_valid(&self) -> bool {
        &&& anchored_arguments(self.project, self.vertices@, self.edges@)
        &&& ordered_edges(self.project, self.vertices@, self.edges@, self.order@, self.ranks@)
        &&& self.ranks@.len() == self.vertices@.len()
        &&& reverse_order_matches(self.order@, self.ranks@)
        &&& forall|a: int, b: int| 0 <= a < b < self.vertices@.len()
            ==> defn_position_before(#[trigger] self.vertices@[a], #[trigger] self.vertices@[b])
    }

    /// 宣言の位置から評価順の順位を得る。計画に含まれなければ `None` を返す。
    pub fn rank_of(&self, position: DefnPosition) -> (rank: Option<usize>)
        ensures
            rank.is_some() == self.order_model().contains(position),
            rank matches Some(i) ==> i < self.order_model().len()
                && i == self.order_model().index_of(position),
    {
        proof { use_type_invariant(self); }
        let Some(node) = vertex_index(self.vertices.as_slice(), position) else {
            assert(!self.order_model().contains(position)) by {
                if self.order_model().contains(position) {
                    let ranked = self.order_model();
                    let i = choose|i: int| 0 <= i < ranked.len() && (#[trigger] ranked[i]) == position;
                    assert(self.vertices@.contains(position));
                }
            };
            return None;
        };
        let rank = self.ranks[node];
        proof {
            let ranked = self.order_model();
            assert(self.order@[rank as int] == node);
            assert(ranked[rank as int] == position);
            assert(ranked.contains(position));
            let first = ranked.index_of(position);
            let first_node = self.order@[first];
            assert(self.vertices@[first_node as int] == position);
            if first_node < node {
                assert(defn_position_before(self.vertices@[first_node as int], self.vertices@[node as int]));
            } else if node < first_node {
                assert(defn_position_before(self.vertices@[node as int], self.vertices@[first_node as int]));
            }
            assert(first_node == node);
            assert(self.ranks@[first_node as int] == first);
        }
        Some(rank)
    }

    /// 計画が参照する、解析済みのソース集合を表す。
    pub closed spec fn project_model(&self) -> ParsedProjectSources<'a> {
        *self.project
    }

    /// 本体の構文木と署名が、計画の順位に対応する同じソースにあることを表す。
    pub open spec fn body_matches_at_rank(&self, rank: usize, body: DefnEvaluationBody<'p, 'a>) -> bool {
        let project = self.project_model();
        let order = self.order_model();
        let defn = order[rank as int];
        &&& rank < order.len()
        &&& defn.file < project.sources_model().len()
        &&& *body.source == project.sources_model()[defn.file as int]
        &&& project.functional_forms_model(defn.file) == Some(body.forms@)
        &&& crate::ncg2m::file::retained_forms_in_source_order(body.forms@)
        &&& body.at < body.forms@.len()
        &&& form_spans_valid(body.source.text_model(), body.forms@,
            body.source.text_model().spec_bytes().len() as int)
        &&& form_span(body.forms@[body.at as int]) == body.signature.body_span
        &&& project.defn_signature_matches_index(defn.file, defn.item, Some(body.signature))
    }

    /// 同じ順位から得た本体は、元文書、構文木上の位置と署名が一致する。
    pub proof fn bodies_at_rank_agree(&self, rank: usize, first: DefnEvaluationBody<'p, 'a>, second: DefnEvaluationBody<'p, 'a>)
        requires self.body_matches_at_rank(rank, first), self.body_matches_at_rank(rank, second),
        ensures
            *first.source == *second.source,
            first.forms@ == second.forms@,
            first.at == second.at,
            crate::ncg2m::data_types::same_defn_signature(first.signature, second.signature),
    {
        let project = self.project_model();
        let defn = self.order_model()[rank as int];
        project.indexed_defn_signature_origin(defn.file, defn.item, Some(first.signature));
        project.indexed_defn_signature_origin(defn.file, defn.item, Some(second.signature));
        let header = project.indexed_defn(defn.file, defn.item)->Some_0;
        let source = project.sources_model()[defn.file as int].text_model();
        crate::ncg2m::data_types::signatures_from_header_agree(source, header, first.signature, second.signature);
        crate::ncg2m::data_types::signature_result_origin(source, header, first.signature);
        crate::ncg2m::data_types::signature_result_origin(source, header, second.signature);
        let forms = first.forms@;
        reveal(crate::ncg2m::file::retained_forms_in_source_order);
        assert(crate::syntax::strict_preorder_ranges(forms));
        crate::ncg2m::file::meta_ast_unique_start(forms, first.at, second.at);
    }

    /// 指定した順位の本体を、計画に対応する元の文書版から返す。
    pub fn body_at_rank(&self, rank: usize) -> (body: Option<DefnEvaluationBody<'p, 'a>>)
        ensures self.order_nodes_valid(),
            body.is_some() == (rank < self.order_model().len()),
            body matches Some(body) ==> self.body_matches_at_rank(rank, body),
    {
        proof { use_type_invariant(self); }
        let defn = self.at_rank(rank)?;
        proof {
            reveal(ordered_edges);
            let node = self.order@[rank as int];
            assert(self.vertices@[node as int] == defn);
        }
        self.project.defn_evaluation_body(defn.file, defn.item)
    }

    /// 呼び出し先から呼び出し元の順に並べた補助関数。
    pub closed spec fn order_model(&self) -> Seq<DefnPosition> {
        self.order@.map_values(|node: usize| self.vertices@[node as int])
    }

    /// 呼び出し元ごとの呼び出し列。
    pub closed spec fn edges_model(&self) -> Seq<Vec<DefnCallEdge<'p, 'a>>> {
        self.edges@
    }

    /// 並びに含まれる補助関数の件数。
    pub fn len(&self) -> (count: usize)
        ensures count == self.order_model().len(),
    {
        self.order.len()
    }

    /// 指定した順位の補助関数を返す。範囲外なら `None` を返す。
    pub fn at_rank(&self, rank: usize) -> (position: Option<DefnPosition>)
        ensures match position {
            Some(position) => rank < self.order_model().len() && position == self.order_model()[rank as int],
            None => rank >= self.order_model().len() || !self.order_nodes_valid(),
        },
    {
        let node = *self.order.get(rank)?;
        self.vertices.get(node).copied()
    }

    /// 順位で指定した補助関数の呼び出し列を表す。
    pub closed spec fn calls_model_at_rank(&self, rank: usize) -> Option<Seq<DefnCallEdge<'p, 'a>>> {
        if rank < self.order@.len() && self.order@[rank as int] < self.edges@.len() {
            Some(self.edges@[self.order@[rank as int] as int]@)
        } else {
            None
        }
    }

    /// 指定した順位の補助関数が呼び出す補助関数と、元の呼び出し位置を返す。
    pub fn calls_at_rank(&self, rank: usize) -> (calls: Option<&[DefnCallEdge<'p, 'a>]>)
        ensures self.calls_model_at_rank(rank) == match calls {
            Some(sites) => Some(sites@),
            None => None,
        },
    {
        let node = *self.order.get(rank)?;
        let sites = self.edges.get(node)?;
        Some(sites.as_slice())
    }

    /// 計画に含まれる呼び出しの引数評価を始める。
    ///
    /// 呼び出し元の順位または呼び出し列の添字が範囲外なら `None` を返す。
    pub fn call_arguments<'call, Value>(&'call self, rank: usize, site: usize)
        -> (waiting: Option<CallArguments<'call, 'p, 'a, Value>>)
        ensures
            waiting.is_some() <==> (self.calls_model_at_rank(rank) matches Some(edges) && site < edges.len()),
            waiting matches Some(args) ==> {
                let edges = self.calls_model_at_rank(rank)->Some_0;
                let edge = *args.model().0;
                let project = self.project_model();
                &&& edge == edges[site as int]
                &&& args.model().1 == Seq::<Value>::empty()
                &&& self.order_model().contains(edge.to)
                &&& self.order_model().index_of(edge.to) < rank
                &&& rank < self.order_model().len() && edge.from == self.order_model()[rank as int]
                &&& edge.from.file < project.sources_model().len()
                &&& *edge.call.source == project.sources_model()[edge.from.file as int]
                &&& project.functional_forms_model(edge.from.file) matches Some(forms)
                    && defn_call_arguments(forms, edge.at, edge.arguments@)
                &&& project.indexed_defn(edge.to.file, edge.to.item) matches Some(header)
                    && edge.arguments@.len() == header.parameters@.len()
            },
    {
        proof { use_type_invariant(self); }
        let edge = self.calls_at_rank(rank)?.get(site)?;
        proof {
            reveal(anchored_arguments);
            reveal(ordered_edges);
            let node = self.order@[rank as int] as int;
            assert(self.ranks@[node] == rank);
            assert(*edge == self.edges@[node]@[site as int]);
        }
        Some(CallArguments::start(edge))
    }

    /// 順序のすべての添字から補助関数の位置を取り出せることを表す。
    pub closed spec fn order_nodes_valid(&self) -> bool {
        forall|i: int| 0 <= i < self.order@.len() ==> (#[trigger] self.order@[i]) < self.vertices@.len()
    }
}

spec fn contains_vertex(positions: Seq<DefnPosition>, pos: DefnPosition) -> bool {
    positions.contains(pos)
}

fn vertex_index(positions: &[DefnPosition], pos: DefnPosition) -> (index: Option<usize>)
    requires forall|a: int, b: int| 0 <= a < b < positions@.len()
        ==> defn_position_before(#[trigger] positions@[a], #[trigger] positions@[b]),
    ensures index.is_some() == contains_vertex(positions@, pos),
        index matches Some(i) ==> i < positions@.len() && positions@[i as int] == pos,
{
    let mut lo = 0;
    let mut hi = positions.len();
    while lo < hi
        invariant
            lo <= hi <= positions@.len(),
            forall|i: int| 0 <= i < lo ==> defn_position_before(#[trigger] positions@[i], pos),
            forall|i: int| hi <= i < positions@.len() ==> defn_position_before(pos, #[trigger] positions@[i]),
            forall|a: int, b: int| 0 <= a < b < positions@.len()
                ==> defn_position_before(#[trigger] positions@[a], #[trigger] positions@[b]),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let found = positions[mid];
        if found.file < pos.file || (found.file == pos.file && found.item < pos.item) {
            lo = mid + 1;
        } else if pos.file < found.file || (pos.file == found.file && pos.item < found.item) {
            hi = mid;
        } else {
            return Some(mid);
        }
    }
    None
}

spec fn graph_row_matches(
    aliases: &MixedUseAliases, vertices: Seq<DefnPosition>, from: usize,
    edges: Seq<DefnCallEdge>, row: Seq<Option<usize>>,
) -> bool {
    &&& from < vertices.len()
    &&& edges.len() == row.len() <= usize::MAX
    &&& forall|i: int| 0 <= i < row.len() ==> {
        let edge = #[trigger] edges[i];
        &&& edge.from == vertices[from as int]
        &&& defn_call_edge_matches(aliases, edge)
        &&& row[i] matches Some(to) && to < vertices.len() && edge.to == vertices[to as int]
    }
}

fn link_graph_row(
    _aliases: &MixedUseAliases, vertices: &[DefnPosition], _from: usize, edges: &[DefnCallEdge],
) -> (row: Vec<Option<usize>>)
    requires
        defn_vertices_valid(&_aliases.targets_model().project_model(), vertices@),
        _from < vertices@.len(),
        forall|i: int| 0 <= i < edges@.len() ==> {
            let edge = #[trigger] edges@[i];
            edge.from == vertices@[_from as int] && defn_call_edge_matches(_aliases, edge)
        },
    ensures graph_row_matches(_aliases, vertices@, _from, edges@, row@),
{
    let _count = edges.len();
    let mut row = Vec::<Option<usize>>::new();
    let mut i = 0;
    while i < edges.len()
        invariant
            i <= edges@.len() == _count,
            defn_vertices_valid(&_aliases.targets_model().project_model(), vertices@),
            _from < vertices@.len(),
            forall|j: int| 0 <= j < edges@.len() ==> {
                let edge = #[trigger] edges@[j];
                edge.from == vertices@[_from as int] && defn_call_edge_matches(_aliases, edge)
            },
            graph_row_matches(_aliases, vertices@, _from, edges@.take(i as int), row@),
        decreases edges@.len() - i,
    {
        let edge = &edges[i];
        assert(defn_call_edge_matches(_aliases, *edge));
        assert(contains_vertex(vertices@, edge.to)) by {
            reveal(defn_call_edge_matches);
        };
        let Some(to) = vertex_index(vertices, edge.to) else { unreachable!() };
        row.push(Some(to));
        assert(edges@.take(i as int + 1) =~= edges@.take(i as int).push(*edge));
        i += 1;
    }
    assert(edges@.take(i as int) =~= edges@);
    row
}

spec fn checked_body(aliases: &MixedUseAliases, pos: DefnPosition) -> bool {
    exists|signature: DefnSignature|
        #[trigger] project_named_defn_body_matches(aliases, pos.file, pos.item, Some(Ok(signature)))
}

spec fn graph_matches(
    aliases: &MixedUseAliases, vertices: Seq<DefnPosition>,
    rows: Seq<Vec<DefnCallEdge>>, graph: Seq<Vec<Option<usize>>>,
) -> bool {
    &&& rows.len() == graph.len() <= vertices.len() <= usize::MAX
    &&& forall|i: int| 0 <= i < rows.len() ==> {
        &&& graph_row_matches(aliases, vertices, i as usize, (#[trigger] rows[i])@, graph[i]@)
        &&& checked_body(aliases, vertices[i])
        &&& defn_body_calls_cover_slots(aliases, vertices[i], rows[i]@)
    }
}

fn graph_rows<'t, 'p, 'a>(
    aliases: &MixedUseAliases<'t, 'p, 'a>, vertices: &[DefnPosition],
) -> (result: Result<(Vec<Vec<DefnCallEdge<'p, 'a>>>, Vec<Vec<Option<usize>>>), DefnCallGraphError<'p, 'a>>)
    requires
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
        defn_vertices_valid(&aliases.targets_model().project_model(), vertices@),
    ensures
        match result {
            Ok((rows, graph)) => graph@.len() == vertices@.len() && graph_matches(aliases, vertices@, rows@, graph@)
                && dependency_graph_valid(graph@),
            Err(DefnCallGraphError::Body { from, error }) =>
                project_named_defn_body_matches(aliases, from.file, from.item, Some(Err(error))),
            Err(DefnCallGraphError::UnvisitedCall(edge)) => defn_call_is_expression_slot(aliases, edge),
            Err(DefnCallGraphError::Cycle(_)) => false,
        },
{
    let project = aliases.targets().project();
    let mut rows = Vec::<Vec<DefnCallEdge>>::new();
    let mut graph = Vec::<Vec<Option<usize>>>::new();
    let mut node = 0;
    while node < vertices.len()
        invariant
            node == rows@.len() <= vertices@.len(),
            *project == aliases.targets_model().project_model(),
            mixed_use_targets_match(project, aliases.targets_model()),
            defn_vertices_valid(project, vertices@),
            graph_matches(aliases, vertices@, rows@, graph@),
        decreases vertices@.len() - node,
    {
        let from = vertices[node];
        let Some((body, capture)) = project.check_named_defn_body(aliases, from.file, from.item, true) else { unreachable!() };
        match body {
            Err(error) => {
                proof { named_body_matches_project(aliases, from.file, from.item, Some(Err(error))); }
                return Err(DefnCallGraphError::Body { from, error });
            }
            Ok(signature) => {
                proof {
                    named_body_matches_project(aliases, from.file, from.item, Some(Ok(signature)));
                    assert(checked_body(aliases, from));
                }
            }
        }
        let edges = match capture {
            Ok(edges) => edges,
            Err(edge) => return Err(DefnCallGraphError::UnvisitedCall(edge)),
        };
        let linked = link_graph_row(aliases, vertices, node, edges.as_slice());
        rows.push(edges);
        graph.push(linked);
        node += 1;
    }
    proof {
        assert forall|node: int, field: int| 0 <= node < graph@.len() && 0 <= field < graph@[node]@.len()
            implies ((#[trigger] graph@[node]@[field]) matches Some(target) ==> target < graph@.len()) by {
            assert(graph_row_matches(aliases, vertices@, node as usize, rows@[node]@, graph@[node]@));
            assert(defn_call_edge_matches(aliases, rows@[node]@[field]));
        };
    }
    Ok((rows, graph))
}

fn copy_edge<'p, 'a>(
    _aliases: &MixedUseAliases<'_, 'p, 'a>, edge: &DefnCallEdge<'p, 'a>,
) -> (copy: DefnCallEdge<'p, 'a>)
    requires defn_call_edge_matches(_aliases, *edge),
    ensures copy.from == edge.from, copy.to == edge.to, copy.at == edge.at,
        copy.call == edge.call, copy.arguments@ == edge.arguments@,
        defn_call_edge_matches(_aliases, copy),
{
    let site = &edge.call;
    let mut arguments = Vec::new();
    let mut i = 0;
    while i < edge.arguments.len()
        invariant
            i <= edge.arguments@.len(),
            arguments@ == edge.arguments@.take(i as int),
        decreases edge.arguments@.len() - i,
    {
        arguments.push(edge.arguments[i]);
        assert(arguments@ =~= edge.arguments@.take(i as int + 1));
        i += 1;
    }
    assert(arguments@ =~= edge.arguments@);
    proof { reveal(defn_call_edge_matches); }
    DefnCallEdge { from: edge.from, to: edge.to, at: edge.at, arguments, call: DefnCallSite {
        source: site.source, span: site.span.start..site.span.end, head: site.head.start..site.head.end,
    } }
}

/// 循環を構成するすべての呼び出しが元のソースを指し、順につながることを表す。
pub open spec fn defn_call_cycle(aliases: &MixedUseAliases, cycle: Seq<DefnCallEdge>) -> bool {
    &&& cycle.len() > 0
    &&& forall|i: int| 0 <= i < cycle.len() ==> defn_call_edge_matches(aliases, #[trigger] cycle[i])
    &&& forall|i: int, j: int| 0 <= i && j == i + 1 && j < cycle.len()
        ==> (#[trigger] cycle[i]).to == (#[trigger] cycle[j]).from
    &&& cycle.last().to == cycle[0].from
}

fn graph_cycle_sites<'p, 'a>(
    _aliases: &MixedUseAliases<'_, 'p, 'a>, _vertices: &[DefnPosition], rows: &[Vec<DefnCallEdge<'p, 'a>>],
    _graph: &[Vec<Option<usize>>], cycle: &[DependencyEdge],
) -> (sites: Vec<DefnCallEdge<'p, 'a>>)
    requires
        dependency_cycle(_graph@, cycle@),
        graph_matches(_aliases, _vertices@, rows@, _graph@),
    ensures defn_call_cycle(_aliases, sites@),
{
    let mut sites = Vec::<DefnCallEdge>::new();
    let mut i = 0;
    while i < cycle.len()
        invariant
            i == sites@.len() <= cycle@.len(),
            dependency_cycle(_graph@, cycle@),
            graph_matches(_aliases, _vertices@, rows@, _graph@),
            forall|j: int| 0 <= j < sites@.len() ==> {
                let step = #[trigger] cycle@[j];
                &&& sites@[j].at == rows@[step.from as int]@[step.field as int].at
                &&& sites@[j].call == rows@[step.from as int]@[step.field as int].call
                &&& sites@[j].arguments@ == rows@[step.from as int]@[step.field as int].arguments@
                &&& sites@[j].from == _vertices@[step.from as int]
                &&& sites@[j].to == _vertices@[step.to as int]
                &&& defn_call_edge_matches(_aliases, sites@[j])
            },
        decreases cycle@.len() - i,
    {
        let step = &cycle[i];
        assert(dependency_edge(_graph@, *step));
        assert(graph_row_matches(_aliases, _vertices@, step.from, rows@[step.from as int]@, _graph@[step.from as int]@));
        let edge = &rows[step.from][step.field];
        sites.push(copy_edge(_aliases, edge));
        i += 1;
    }
    proof {
        assert forall|j: int| 0 <= j < sites@.len()
            implies defn_call_edge_matches(_aliases, #[trigger] sites@[j]) by {
            assert(dependency_edge(_graph@, cycle@[j]));
        };
        assert forall|a: int, b: int| 0 <= a && b == a + 1 && b < sites@.len()
            implies (#[trigger] sites@[a]).to == (#[trigger] sites@[b]).from by {
            assert(cycle@[a].to == cycle@[b].from);
        };
        let last = sites@.len() - 1;
        assert(cycle@[last].to == cycle@[0].from);
        assert(sites@[last].to == sites@[0].from);
    }
    sites
}

/// 成功した計画の順序が全補助関数を含み、すべての呼び出しで順位が下がることを表す。
pub closed spec fn defn_call_plan_matches(aliases: &MixedUseAliases, plan: &DefnCallPlan) -> bool {
    let order = plan.order_model();
    &&& plan.project_model() == aliases.targets_model().project_model()
    &&& defn_vertices_valid(&aliases.targets_model().project_model(), plan.vertices@)
    &&& plan.order_nodes_valid()
    &&& plan.edges_model().len() == plan.vertices@.len()
    &&& order.no_duplicates()
    &&& forall|pos: DefnPosition| #[trigger] plan.vertices@.contains(pos) ==> order.contains(pos)
    &&& forall|pos: DefnPosition| #[trigger] plan.vertices@.contains(pos) ==> checked_body(aliases, pos)
    &&& forall|row: int| 0 <= row < plan.edges_model().len()
        ==> defn_body_calls_cover_slots(aliases, plan.vertices@[row], (#[trigger] plan.edges_model()[row])@)
    &&& forall|row: int, slot: int| 0 <= row < plan.edges_model().len()
        && 0 <= slot < plan.edges_model()[row]@.len() ==> {
            let edge = #[trigger] plan.edges_model()[row]@[slot];
            &&& defn_call_edge_matches(aliases, edge)
            &&& edge.from == plan.vertices@[row]
            &&& order.contains(edge.from) && order.contains(edge.to)
            &&& order.index_of(edge.to) < order.index_of(edge.from)
        }
}

/// 指定した補助関数の本体が型検査を通り、計画の順序に含まれることを示す。
pub proof fn defn_call_plan_contains(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, pos: DefnPosition,
)
    requires defn_call_plan_matches(aliases, plan),
        aliases.targets_model().project_model().indexed_defn(pos.file, pos.item).is_some(),
    ensures
        plan.order_model().contains(pos),
        exists|signature: DefnSignature|
            #[trigger] project_named_defn_body_matches(aliases, pos.file, pos.item, Some(Ok(signature))),
{}

/// 呼び出しを含まない局所スカラー本体について、計画の型検査結果を評価器が使う型判断に結び付ける。
pub proof fn defn_call_plan_local_scalar_body<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, plan: &DefnCallPlan<'p, 'a>,
    rank: usize, body: DefnEvaluationBody<'p, 'a>,
)
    requires
        defn_call_plan_matches(aliases, plan), plan.body_matches_at_rank(rank, body),
        body.signature.result_type.ty.list_depth == 0,
        body.signature.result_type.ty.atom matches crate::ncg2m::data_types::DataTypeAtom::Builtin(
            crate::ncg2m::data_types::BuiltinDataType::Bool | crate::ncg2m::data_types::BuiltinDataType::Integer(_)
        ),
        crate::ncg2m::expression_types::local_scalar_fragment(body.source.text_model(), body.forms@, body.at),
    ensures crate::ncg2m::expression_types::local_scalar_site_is_typed(
        body.source.text_model(), body.forms@, body.signature.parameters@, body.at, body.signature.result_type.ty,
    ),
{
    let defn = plan.order_model()[rank as int];
    let project = aliases.targets_model().project_model();
    assert(plan.order_nodes_valid());
    defn_call_plan_contains(aliases, plan, defn);
    let signature = choose|signature: DefnSignature|
        #[trigger] project_named_defn_body_matches(aliases, defn.file, defn.item, Some(Ok(signature)));
    named_body_check_belongs_to_project(aliases, defn.file, defn.item, Some(Ok(signature)));
    project.named_defn_local_scalar_type(aliases, defn.file, defn.item, signature, body);
}

/// 計画で補助関数に割り当てられた順位と、指定した呼び出しでの順位減少を取り出す。
pub proof fn defn_call_plan_edge_order(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize,
)
    requires defn_call_plan_matches(aliases, plan), rank < plan.order_model().len(),
    ensures plan.calls_model_at_rank(rank) matches Some(sites) && {
        &&& defn_body_calls_cover_slots(aliases, plan.order_model()[rank as int], sites)
        &&& forall|j: int| 0 <= j < sites.len() ==> {
            let edge = #[trigger] sites[j];
            let order = plan.order_model();
            &&& defn_call_edge_matches(aliases, edge)
            &&& edge.from == order[rank as int]
            &&& order.contains(edge.to)
            &&& order.index_of(edge.to) < rank
        }
    },
{
    let order = plan.order_model();
    let node = plan.order@[rank as int] as int;
    let sites = plan.edges@[node]@;
    assert(plan.calls_model_at_rank(rank) == Some(sites));
    assert(defn_body_calls_cover_slots(aliases, plan.vertices@[node], plan.edges_model()[node]@));
    assert forall|j: int| 0 <= j < sites.len() implies {
        let edge = #[trigger] sites[j];
        &&& defn_call_edge_matches(aliases, edge)
        &&& edge.from == order[rank as int]
        &&& order.contains(edge.to)
        &&& order.index_of(edge.to) < rank
    } by {
        let edge = plan.edges_model()[node]@[j];
        assert(edge.from == plan.vertices@[node] && edge.from == order[rank as int]);
        assert(order.index_of(edge.from) == rank);
    };
}

/// 順位ごとの呼び出し列から、元の構文木の位置と呼び出し先の順位を取り出す。
pub proof fn defn_call_plan_site_at_rank(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, site: usize,
) -> (at: usize)
    requires
        defn_call_plan_matches(aliases, plan),
        rank < plan.order_model().len(),
        plan.calls_model_at_rank(rank) matches Some(sites) && site < sites.len(),
    ensures {
        let sites = plan.calls_model_at_rank(rank)->Some_0;
        let edge = sites[site as int];
        let order = plan.order_model();
        let project = aliases.targets_model().project_model();
        &&& at == edge.at
        &&& edge.from == order[rank as int]
        &&& order.contains(edge.to)
        &&& order.index_of(edge.to) < rank
        &&& project.indexed_defn(edge.to.file, edge.to.item) matches Some(target)
            && edge.arguments@.len() == target.parameters@.len()
        &&& edge.from.file < project.sources_model().len()
        &&& *edge.call.source == project.sources_model()[edge.from.file as int]
        &&& project.functional_forms_model(edge.from.file) matches Some(forms) && {
            &&& at + 1 < forms.len()
            &&& forms[at as int] is List
            &&& forms[at + 1] is Atom
            &&& edge.call.span == form_span(forms[at as int])
            &&& edge.call.head == form_span(forms[at + 1])
            &&& defn_call_arguments(forms, at, edge.arguments@)
        }
    },
{
    defn_call_plan_edge_order(aliases, plan, rank);
    let edge = plan.calls_model_at_rank(rank)->Some_0[site as int];
    assert(defn_call_edge_matches(aliases, edge));
    reveal(defn_call_edge_matches);
    edge.at
}

proof fn checked_rows_anchor_arguments(
    aliases: &MixedUseAliases, project: &ParsedProjectSources, vertices: Seq<DefnPosition>,
    rows: Seq<Vec<DefnCallEdge>>, graph: Seq<Vec<Option<usize>>>,
)
    requires
        *project == aliases.targets_model().project_model(),
        graph_matches(aliases, vertices, rows, graph), rows.len() == vertices.len(),
    ensures anchored_arguments(project, vertices, rows),
{
    reveal(anchored_arguments);
    assert forall|row: int, site: int| 0 <= row < rows.len() && 0 <= site < rows[row]@.len() implies {
        let edge = #[trigger] rows[row]@[site];
        &&& edge.from == vertices[row]
        &&& edge.from.file < project.sources_model().len()
        &&& *edge.call.source == project.sources_model()[edge.from.file as int]
        &&& project.functional_forms_model(edge.from.file) matches Some(forms)
            && defn_call_arguments(forms, edge.at, edge.arguments@)
        &&& project.indexed_defn(edge.to.file, edge.to.item) matches Some(header)
            && edge.arguments@.len() == header.parameters@.len()
    } by {
        let edge = rows[row]@[site];
        assert(graph_row_matches(aliases, vertices, row as usize, rows[row]@, graph[row]@));
        assert(defn_call_edge_matches(aliases, edge));
        reveal(defn_call_edge_matches);
    };
}

proof fn checked_edges_have_order(
    aliases: &MixedUseAliases, project: &ParsedProjectSources, vertices: Seq<DefnPosition>,
    edges: Seq<Vec<DefnCallEdge>>, graph: Seq<Vec<Option<usize>>>, order: Seq<usize>,
    ranks: Seq<usize>, expected: Seq<nat>,
)
    requires *project == aliases.targets_model().project_model(),
        defn_vertices_valid(project, vertices), graph.len() == vertices.len(),
        graph_matches(aliases, vertices, edges, graph), edges.len() == vertices.len(),
        order.len() == vertices.len(), reverse_order_matches(order, ranks),
        dependencies_in_order(graph, expected), completion_order_matches(order, expected),
    ensures ordered_edges(project, vertices, edges, order, ranks),
{
    reveal(ordered_edges);
    let ranked = order.map_values(|node: usize| vertices[node as int]);
    assert forall|row: int| 0 <= row < vertices.len() implies {
        let pos = #[trigger] vertices[row];
        project.indexed_defn(pos.file, pos.item).is_some()
    } by {
        let pos = vertices[row];
        assert(vertices.contains(pos));
    };
    assert forall|row: int, site: int| 0 <= row < edges.len() && 0 <= site < edges[row]@.len() implies {
        let edge = #[trigger] edges[row]@[site];
        ranked.contains(edge.to) && ranked.index_of(edge.to) < ranks[row]
    } by {
        let to = graph[row]@[site]->Some_0;
        assert(graph_row_matches(aliases, vertices, row as usize, edges[row]@, graph[row]@));
        assert(dependency_edge(graph, DependencyEdge { from: row as usize, field: site as usize, to }));
        assert(ranks[row] == expected[row] && ranks[to as int] == expected[to as int]);
        assert(ranked[ranks[to as int] as int] == edges[row]@[site].to);
    };
}

proof fn checked_dependency_order_is_call_plan(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, graph: Seq<Vec<Option<usize>>>,
)
    requires
        plan.project_model() == aliases.targets_model().project_model(),
        defn_vertices_valid(&aliases.targets_model().project_model(), plan.vertices@),
        graph.len() == plan.vertices@.len(),
        graph_matches(aliases, plan.vertices@, plan.edges@, graph),
        complete_dependency_order(graph, plan.order@),
    ensures defn_call_plan_matches(aliases, plan),
{
    let nodes = plan.vertices@;
    let order = plan.order@;
    let ranked = plan.order_model();
    let ranks = choose|rank: Seq<nat>| #[trigger] dependencies_in_order(graph, rank)
        && order.len() == graph.len() && completion_order_matches(order, rank)
        && (forall|node: int| #![trigger rank[node]] 0 <= node < graph.len()
            ==> rank[node] < order.len() && order[rank[node] as int] == node);
    assert forall|pos: DefnPosition| #[trigger] nodes.contains(pos) implies ranked.contains(pos) by {
        let i = choose|i: int| 0 <= i < nodes.len() && (#[trigger] nodes[i]) == pos;
        assert(ranked[ranks[i] as int] == pos);
    };
    assert forall|pos: DefnPosition| #[trigger] nodes.contains(pos) implies checked_body(aliases, pos) by {
        let i = choose|i: int| 0 <= i < nodes.len() && (#[trigger] nodes[i]) == pos;
        assert(graph_row_matches(aliases, nodes, i as usize, plan.edges@[i]@, graph[i]@));
        assert(checked_body(aliases, nodes[i]));
    };
    assert forall|a: int, b: int| 0 <= a < b < ranked.len() implies (#[trigger] ranked[a]) != (#[trigger] ranked[b]) by {
        let left = order[a] as int;
        let right = order[b] as int;
        assert(ranks[left] == a && ranks[right] == b && left != right);
        if left < right { assert(defn_position_before(nodes[left], nodes[right])); }
        else { assert(defn_position_before(nodes[right], nodes[left])); }
    };
    assert forall|row: int, slot: int| 0 <= row < plan.edges@.len() && 0 <= slot < plan.edges@[row]@.len()
        implies {
            let edge = #[trigger] plan.edges@[row]@[slot];
            defn_call_edge_matches(aliases, edge) && edge.from == nodes[row]
                && ranked.contains(edge.from) && ranked.contains(edge.to)
                && ranked.index_of(edge.to) < ranked.index_of(edge.from)
        } by {
        let to = graph[row]@[slot]->Some_0;
        let edge = plan.edges@[row]@[slot];
        assert(graph_row_matches(aliases, nodes, row as usize, plan.edges@[row]@, graph[row]@));
        assert(dependency_edge(graph, DependencyEdge { from: row as usize, field: slot as usize, to }));
        assert(ranked[ranks[row] as int] == edge.from && ranked[ranks[to as int] as int] == edge.to);
        assert(ranked.index_of(edge.from) == ranks[row] && ranked.index_of(edge.to) == ranks[to as int]);
    };
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// プロジェクト内の補助関数を検査し、呼び出し先を先に並べる。
    ///
    /// 反復回数にかかわらず、反復本体で訪れた補助関数の呼び出しを含める。
    ///
    /// # Errors
    ///
    /// 型検査を完了できない本体、訪問記録に漏れた呼び出し、または循環を返す。組み込みやテンプレートの検査に
    /// 実行段階が必要な場合は、その本体の保留を返す。
    pub fn plan_defn_calls(&self) -> (result: Result<DefnCallPlan<'p, 'a>, DefnCallGraphError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures match result {
            Ok(plan) => defn_call_plan_matches(self, &plan),
            Err(DefnCallGraphError::Body { from, error }) =>
                project_named_defn_body_matches(self, from.file, from.item, Some(Err(error))),
            Err(DefnCallGraphError::UnvisitedCall(edge)) => defn_call_is_expression_slot(self, edge),
            Err(DefnCallGraphError::Cycle(sites)) => defn_call_cycle(self, sites@),
        },
    {
        let targets = self.targets();
        let project = targets.project();
        let exports = targets.exports();
        let declarations = exports.declarations();
        proof {
            targets.mixed_use_exports_match(project);
            mixed_exports_use_project_declarations(project, exports);
        }
        let vertices = declarations.defn_positions(project);
        let (edges, graph) = graph_rows(self, &vertices)?;
        match check_dependency_order(graph.as_slice(), true) {
            Err(cycle) => Err(DefnCallGraphError::Cycle(graph_cycle_sites(self, &vertices, &edges, &graph, &cycle))),
            Ok(order) => {
                let ghost expected = choose|rank: Seq<nat>| #[trigger] dependencies_in_order(graph@, rank)
                    && order@.len() == graph@.len() && completion_order_matches(order@, rank)
                    && (forall|node: int| #![trigger rank[node]] 0 <= node < graph@.len()
                        ==> rank[node] < order@.len() && order@[rank[node] as int] == node);
                let ranks = invert_call_order(order.as_slice(), Ghost(expected));
                proof {
                    checked_rows_anchor_arguments(self, project, vertices@, edges@, graph@);
                    checked_edges_have_order(self, project, vertices@, edges@, graph@, order@, ranks@, expected);
                }
                let plan = DefnCallPlan { project, vertices, edges, order, ranks };
                proof { checked_dependency_order_is_call_plan(self, &plan, graph@); }
                Ok(plan)
            }
        }
    }
}

}
