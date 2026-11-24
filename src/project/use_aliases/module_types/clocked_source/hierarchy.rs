//! ルートから到達するモジュールを調べ、子の展開結果を親の呼び出しで共有する。

use super::{ClockedModuleError, ClockedNor, FunctionTemplates, LocatedName, ModuleBodyPosition, ModuleCallTarget, ModuleCalls, UseAliases, builtin_instance};
use crate::project::{CircuitProject, use_aliases::dependency_order::{DependencyEdge, check_dependency_order}};
use crate::syntax::circuit::Head;
#[cfg(verus_only)]
use crate::syntax::circuit::NamedBuildCircuit;
use alloc::{collections::BTreeMap, vec::Vec};
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::project::use_aliases::dependency_order::{
    completion_order_matches, dependencies_in_order, dependency_cycle, dependency_edge, dependency_graph_valid,
};
#[cfg(verus_only)]
use vstd::laws_cmp::obeys_cmp;
#[cfg(verus_only)]
use super::{builtin_nor_template, edge_templates_ready, function_templates::function_target};
#[cfg(verus_only)]
use crate::project::use_aliases::call_dependencies::function_position;
#[cfg(verus_only)]
use super::semantics::{ModuleSourceLayout, call_layout_is_ready, prior_layout_at};
#[cfg(verus_only)]
mod source_models;

verus! {

type Position = (usize, usize);

spec fn key(position: ModuleBodyPosition) -> Position {
    (position.file, position.entry)
}

spec fn module_key(circuits: Seq<NamedBuildCircuit>, at: Position) -> bool {
    &&& at.0 < circuits.len()
    &&& at.1 < circuits[at.0 as int].syntax.entries@.len()
    &&& circuits[at.0 as int].syntax.entries@[at.1 as int].head is Module
}

spec fn before(at: Position, stop: Position) -> bool {
    at.0 < stop.0 || (at.0 == stop.0 && at.1 < stop.1)
}

spec fn vertex_index_matches(positions: Seq<ModuleBodyPosition>, vertices: Map<Position, usize>) -> bool {
    &&& forall|at: Position| #[trigger] vertices.contains_key(at) ==> {
        let vertex = vertices[at];
        vertex < positions.len() && key(positions[vertex as int]) == at
    }
    &&& forall|i: int| 0 <= i < positions.len() ==> {
        let at = key(#[trigger] positions[i]);
        vertices.contains_key(at) && vertices[at] == i
    }
}

spec fn scanned_modules(circuits: Seq<NamedBuildCircuit>, root: ModuleBodyPosition, vertices: Map<Position, usize>,
    stop: Position) -> bool
{
    forall|at: Position| #[trigger] vertices.contains_key(at)
        == (at == key(root) || (module_key(circuits, at) && before(at, stop)))
}

proof fn add_module_vertex(positions: Seq<ModuleBodyPosition>, vertices: Map<Position, usize>,
    position: ModuleBodyPosition, vertex: usize)
    requires vertex_index_matches(positions, vertices), !vertices.contains_key(key(position)), vertex == positions.len(),
    ensures vertex_index_matches(positions.push(position), vertices.insert(key(position), vertex)),
{
    let next_positions = positions.push(position);
    let next_vertices = vertices.insert(key(position), vertex);
    assert forall|i: int| 0 <= i < next_positions.len() implies {
        let at = key(#[trigger] next_positions[i]);
        next_vertices.contains_key(at) && next_vertices[at] == i
    } by {
        if i < positions.len() { assert(next_positions[i] == positions[i]); }
    };
}

fn indexed_modules(project: &CircuitProject, root: ModuleBodyPosition)
    -> (index: (Vec<ModuleBodyPosition>, BTreeMap<Position, usize>))
    ensures index.0@.len() > 0 && index.0@[0] == root, obeys_cmp::<Position>(),
        vertex_index_matches(index.0@, index.1@),
        forall|at: Position| #[trigger] index.1@.contains_key(at)
            == (at == key(root) || module_key(project.circuits_model(), at)),
{
    let circuits = project.circuits();
    let mut positions = Vec::new();
    positions.push(root);
    let mut vertices = BTreeMap::new();
    proof {
        broadcast use vstd::laws_cmp::group_laws_cmp;
        assert(obeys_cmp::<Position>());
    }
    vertices.insert((root.file, root.entry), 0);
    let mut file = 0;
    while file < circuits.len()
        invariant file <= circuits@.len(), circuits@ == project.circuits_model(),
            positions@.len() > 0 && positions@[0] == root, obeys_cmp::<Position>(),
            vertex_index_matches(positions@, vertices@), scanned_modules(circuits@, root, vertices@, (file, 0)),
        decreases circuits@.len() - file,
    {
        let entries = circuits[file].syntax.entries.as_slice();
        let mut entry = 0;
        while entry < entries.len()
            invariant file < circuits@.len(), entries@ == circuits@[file as int].syntax.entries@,
                entry <= entries@.len(), positions@.len() > 0 && positions@[0] == root, obeys_cmp::<Position>(),
                vertex_index_matches(positions@, vertices@), scanned_modules(circuits@, root, vertices@, (file, entry)),
            decreases entries@.len() - entry,
        {
            let ghost prior = vertices@;
            if matches!(entries[entry].head, Head::Module) && (file != root.file || entry != root.entry) {
                let position = ModuleBodyPosition { file, entry };
                let vertex = positions.len();
                proof { add_module_vertex(positions@, prior, position, vertex); }
                vertices.insert((file, entry), vertex);
                positions.push(position);
            }
            assert forall|at: Position| #[trigger] vertices@.contains_key(at)
                == (at == key(root) || (module_key(circuits@, at) && before(at, (file, (entry + 1) as usize)))) by {
                if at != (file, entry) { assert(before(at, (file, entry)) == before(at, (file, (entry + 1) as usize))); }
                assert(prior.contains_key(at) == (at == key(root) || (module_key(circuits@, at) && before(at, (file, entry)))));
            };
            entry += 1;
        }
        assert forall|at: Position| #[trigger] vertices@.contains_key(at)
            == (at == key(root) || (module_key(circuits@, at) && before(at, ((file + 1) as usize, 0)))) by {
            assert(vertices@.contains_key(at)
                == (at == key(root) || (module_key(circuits@, at) && before(at, (file, entry)))));
        };
        file += 1;
    }
    assert forall|at: Position| #[trigger] vertices@.contains_key(at)
        == (at == key(root) || module_key(circuits@, at)) by {
        assert(vertices@.contains_key(at)
            == (at == key(root) || (module_key(circuits@, at) && before(at, (file, 0)))));
    };
    (positions, vertices)
}

struct Work<'p, 'a> {
    node: usize,
    call: Option<LocatedName<'p, 'a>>,
}

struct CheckedModules<'p, 'a> {
    modules: Vec<Option<ModuleCalls<'p, 'a>>>,
    graph: Vec<Vec<Option<usize>>>,
}

spec fn pending_matches(pending: Seq<Work>, size: nat) -> bool {
    forall|i: int| 0 <= i < pending.len() ==> {
        let item = #[trigger] pending[i];
        item.node < size && (item.call.is_none() ==> item.node == 0)
    }
}

spec fn is_pending(pending: Seq<Work>, node: usize) -> bool {
    exists|i: int| 0 <= i < pending.len() && (#[trigger] pending[i]).node == node
}

spec fn discovered_accounted_for(seen: Seq<bool>, modules: Seq<Option<ModuleCalls>>, pending: Seq<Work>,
    active: Option<usize>) -> bool
{
    forall|i: usize| i < seen.len() && #[trigger] seen[i as int] ==>
        modules[i as int].is_some() || is_pending(pending, i) || active == Some(i)
}

spec fn graph_targets_discovered(graph: Seq<Vec<Option<usize>>>, seen: Seq<bool>) -> bool {
    forall|i: int, c: int| 0 <= i < graph.len() && 0 <= c < graph[i]@.len() ==>
        ((#[trigger] graph[i]@[c]) matches Some(to) ==> to < seen.len() && seen[to as int])
}

spec fn graph_targets_loaded(graph: Seq<Vec<Option<usize>>>, modules: Seq<Option<ModuleCalls>>) -> bool {
    forall|i: int, c: int| 0 <= i < graph.len() && 0 <= c < graph[i]@.len() ==>
        ((#[trigger] graph[i]@[c]) matches Some(to) ==> to < modules.len() && modules[to as int].is_some())
}

spec fn completed_templates(modules: Seq<Option<ModuleCalls>>, rank: Seq<nat>, templates: Seq<Option<ClockedNor>>,
    layouts: Seq<Option<ModuleSourceLayout>>, positions: Seq<ModuleBodyPosition>, stop: int) -> bool
{
    &&& layouts.len() == templates.len() == positions.len() == modules.len()
    &&& forall|node: int| 0 <= node < modules.len() && rank[node] < stop && modules[node].is_some()
        ==> #[trigger] prior_layout_at(templates, layouts, node, positions[node])
}

spec fn unseen_matches(seen: Seq<bool>, unseen: Set<usize>) -> bool {
    &&& forall|i: usize| i < seen.len() ==> #[trigger] unseen.contains(i) == !seen[i as int]
    &&& forall|i: usize| #[trigger] unseen.contains(i) ==> i < seen.len()
}

spec fn slots_match(modules: Seq<Option<ModuleCalls>>, graph: Seq<Vec<Option<usize>>>) -> bool {
    &&& graph.len() == modules.len()
    &&& forall|i: int| 0 <= i < modules.len() ==> {
        let row = #[trigger] graph[i];
        row@.len() == match modules[i] { Some(loaded) => loaded.calls@.len(), None => 0 }
    }
}

spec fn call_vertex(call: &crate::project::CheckedModuleCall, vertices: Map<Position, usize>) -> Option<usize> {
    match call.inputs.ports.signature.target {
        ModuleCallTarget::Routine { position, .. } if vertices.contains_key(key(position)) => Some(vertices[key(position)]),
        _ => None,
    }
}

proof fn call_vertex_position(call: &crate::project::CheckedModuleCall, vertices: Map<Position, usize>,
    positions: Seq<ModuleBodyPosition>, child: usize)
    requires vertex_index_matches(positions, vertices), call_vertex(call, vertices) == Some(child),
    ensures child < positions.len(),
        call.inputs.ports.signature.target matches ModuleCallTarget::Routine { position, .. }
            && positions[child as int] == position,
{
    let target = call.inputs.ports.signature.target;
    assert(target is Routine);
    assert(key(positions[child as int]) == key(target->Routine_position));
}

spec fn edges_match(modules: Seq<Option<ModuleCalls>>, graph: Seq<Vec<Option<usize>>>,
    vertices: Map<Position, usize>) -> bool
{
    forall|i: int, c: int| 0 <= i < modules.len() && 0 <= c < graph[i]@.len() ==>
        (#[trigger] graph[i]@[c]) == call_vertex(&modules[i]->Some_0.calls@[c], vertices)
}

fn call_location<'p, 'a>(call: &crate::project::CheckedModuleCall<'p, 'a>) -> (site: LocatedName<'p, 'a>)
    ensures *site.source == *call.inputs.ports.signature.source && site.span == call.inputs.ports.signature.call.span,
{
    let signature = &call.inputs.ports.signature;
    LocatedName { source: signature.source, span: signature.call.span.start..signature.call.span.end }
}

fn module_cycle_sites<'p, 'a>(checked: &CheckedModules<'p, 'a>, edges: &[DependencyEdge])
    -> (path: Vec<LocatedName<'p, 'a>>)
    requires slots_match(checked.modules@, checked.graph@), dependency_cycle(checked.graph@, edges@),
    ensures path@.len() == edges@.len(),
        forall|i: int| 0 <= i < path@.len() ==> {
            let site = #[trigger] path@[i];
            let edge = edges@[i];
            let signature = checked.modules@[edge.from as int]->Some_0.calls@[edge.field as int].inputs.ports.signature;
            *site.source == *signature.source && site.span == signature.call.span
        },
{
    let mut path: Vec<LocatedName<'p, 'a>> = Vec::with_capacity(edges.len());
    let mut i = 0;
    while i < edges.len()
        invariant i == path@.len() <= edges@.len(),
            slots_match(checked.modules@, checked.graph@), dependency_cycle(checked.graph@, edges@),
            forall|j: int| 0 <= j < i ==> {
                let site = #[trigger] path@[j];
                let edge = edges@[j];
                let signature = checked.modules@[edge.from as int]->Some_0.calls@[edge.field as int].inputs.ports.signature;
                *site.source == *signature.source && site.span == signature.call.span
            },
        decreases edges@.len() - i,
    {
        let edge = edges[i];
        assert(dependency_edge(checked.graph@, edge));
        let Some(loaded) = &checked.modules[edge.from] else {
            proof { assert(false); }
            unreachable!()
        };
        let site = call_location(&loaded.calls[edge.field]);
        let ghost before = path@;
        path.push(site);
        assert forall|j: int| 0 <= j < path@.len() implies {
            let site = #[trigger] path@[j];
            let edge = edges@[j];
            let signature = checked.modules@[edge.from as int]->Some_0.calls@[edge.field as int].inputs.ports.signature;
            *site.source == *signature.source && site.span == signature.call.span
        } by { if j < i { assert(path@[j] == before[j]); } };
        i += 1;
    }
    path
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn loaded_modules_match(&self, positions: Seq<ModuleBodyPosition>, width: u64, modules: Seq<Option<ModuleCalls>>) -> bool {
        &&& modules.len() == positions.len()
        &&& forall|i: int| 0 <= i < modules.len() ==> ((#[trigger] modules[i]) matches Some(loaded)
            ==> self.module_calls_result(positions[i], width, Ok(Some(loaded))))
    }

    fn reachable_modules(&self, root: ModuleBodyPosition, positions: &[ModuleBodyPosition], vertices: &BTreeMap<Position, usize>, width: u64)
        -> (result: Result<Option<CheckedModules<'p, 'a>>, ClockedModuleError<'p, 'a>>)
        requires self.can_resolve(), positions@.len() > 0 && positions@[0] == root, obeys_cmp::<Position>(),
            vertex_index_matches(positions@, vertices@),
        ensures match result {
            Ok(Some(loaded)) => self.loaded_modules_match(positions@, width, loaded.modules@)
                && slots_match(loaded.modules@, loaded.graph@) && dependency_graph_valid(loaded.graph@)
                && edges_match(loaded.modules@, loaded.graph@, vertices@)
                && graph_targets_loaded(loaded.graph@, loaded.modules@)
                && loaded.modules@[0].is_some(),
            Ok(None) => self.module_calls_result(root, width, Ok(None)),
            Err(ClockedModuleError::Parent(error)) => self.module_calls_result(root, width, Err(error)),
            Err(ClockedModuleError::Function { .. } | ClockedModuleError::PortLayout { .. }) => false,
            Err(_) => true,
        },
    {
        let size = positions.len();
        let mut modules: Vec<Option<ModuleCalls>> = Vec::with_capacity(size);
        let mut graph: Vec<Vec<Option<usize>>> = Vec::with_capacity(size);
        let mut seen: Vec<bool> = Vec::with_capacity(size);
        let ghost mut unseen = Set::<usize>::empty();
        let mut i = 0;
        while i < size
            invariant i <= size, i == modules@.len() == graph@.len() == seen@.len(),
                unseen_matches(seen@, unseen), slots_match(modules@, graph@), dependency_graph_valid(graph@),
                forall|j: int| 0 <= j < i ==> (#[trigger] modules@[j]).is_none(),
                forall|j: int| 0 <= j < i ==> !(#[trigger] seen@[j]),
            decreases size - i,
        {
            let ghost prior_modules = modules@;
            let ghost prior_graph = graph@;
            let ghost prior_seen = seen@;
            modules.push(None);
            graph.push(Vec::new());
            seen.push(false);
            proof {
                unseen = unseen.insert(i);
                assert forall|j: int| 0 <= j < modules@.len() implies {
                    (#[trigger] modules@[j]).is_none() && graph@[j]@.len() == 0
                } by {
                    if j < i {
                        assert(modules@[j] == prior_modules[j] && graph@[j] == prior_graph[j]);
                    }
                };
                assert forall|j: usize| j < seen@.len() implies #[trigger] unseen.contains(j) == !seen@[j as int] by {
                    if j < i { assert(seen@[j as int] == prior_seen[j as int]); }
                };
                assert forall|j: int| 0 <= j < seen@.len() implies !(#[trigger] seen@[j]) by {
                    if j < i { assert(seen@[j] == prior_seen[j]); }
                };
            }
            i += 1;
        }
        let mut pending = Vec::new();
        pending.push(Work { node: 0, call: None });
        let ghost initially_seen = seen@;
        seen.set(0, true);
        proof {
            unseen = unseen.remove(0);
            assert forall|j: usize| j < size && #[trigger] seen@[j as int] implies is_pending(pending@, j) by {
                if j != 0 { assert(seen@[j as int] == initially_seen[j as int]); }
                assert(pending@[0].node == j);
            };
        }
        let ghost mut root_loaded = false;
        while pending.len() > 0
            invariant
                self.can_resolve(), obeys_cmp::<Position>(), positions@[0] == root, vertex_index_matches(positions@, vertices@),
                size == positions@.len() == modules@.len() == graph@.len() == seen@.len(), size > 0,
                pending_matches(pending@, size as nat), unseen_matches(seen@, unseen),
                discovered_accounted_for(seen@, modules@, pending@, None),
                graph_targets_discovered(graph@, seen@),
                self.loaded_modules_match(positions@, width, modules@),
                slots_match(modules@, graph@), dependency_graph_valid(graph@),
                edges_match(modules@, graph@, vertices@),
                root_loaded ==> modules@[0].is_some(),
                !root_loaded ==> pending@.len() == 1 && pending@[0].node == 0 && pending@[0].call.is_none(),
            decreases unseen.len() + pending@.len(),
        {
            let ghost before_pop = pending@;
            let next = pending.pop().unwrap();
            let node = next.node;
            assert forall|j: usize| j < size && #[trigger] seen@[j as int]
                implies modules@[j as int].is_some() || is_pending(pending@, j) || Some(node) == Some(j) by {
                if !modules@[j as int].is_some() && j != node {
                    assert(is_pending(before_pop, j));
                    let k = choose|k: int| 0 <= k < before_pop.len() && (#[trigger] before_pop[k]).node == j;
                    assert(k < pending@.len() && pending@[k] == before_pop[k]);
                }
            };
            let position = positions[node];
            let checked = match self.check_module_calls(position, width) {
                Ok(Some(checked)) => checked,
                Ok(None) => match next.call {
                    Some(site) => return Err(ClockedModuleError::Unsupported(site)),
                    None => return Ok(None),
                },
                Err(reason) => match next.call {
                    Some(call) => return Err(ClockedModuleError::Child { call, reason: super::PrimitiveModuleError::Module(reason) }),
                    None => return Err(ClockedModuleError::Parent(reason)),
                },
            };
            let ghost remaining = unseen.len() + pending@.len();
            let mut row: Vec<Option<usize>> = Vec::new();
            let mut c = 0;
            while c < checked.calls.len()
                invariant
                    obeys_cmp::<Position>(), vertex_index_matches(positions@, vertices@),
                    size == positions@.len() == seen@.len() == modules@.len() == graph@.len(),
                    c == row@.len() <= checked.calls@.len(),
                    pending_matches(pending@, size as nat), unseen_matches(seen@, unseen),
                    discovered_accounted_for(seen@, modules@, pending@, Some(node)),
                    graph_targets_discovered(graph@, seen@),
                    unseen.len() + pending@.len() == remaining,
                    forall|j: int| 0 <= j < row@.len() ==>
                        ((#[trigger] row@[j]) matches Some(target) ==> target < size && seen@[target as int]),
                    forall|j: int| 0 <= j < row@.len() ==>
                        (#[trigger] row@[j]) == call_vertex(&checked.calls@[j], vertices@),
                decreases checked.calls@.len() - c,
            {
                let call = &checked.calls[c];
                let target = match call.inputs.ports.signature.target {
                    ModuleCallTarget::Routine { position, .. } =>
                        match vertices.get(&(position.file, position.entry)) {
                            Some(target) => Some(*target),
                            _ => None,
                        },
                    _ => None,
                };
                assert(target == call_vertex(call, vertices@));
                if let Some(to) = target {
                    if !seen[to] {
                        let ghost old_seen = seen@;
                        let ghost old_pending = pending@;
                        seen.set(to, true);
                        pending.push(Work { node: to, call: Some(call_location(call)) });
                        proof {
                            vstd::set::lemma_set_remove_len(unseen, to);
                            unseen = unseen.remove(to);
                            assert forall|j: usize| j < size implies #[trigger] unseen.contains(j) == !seen@[j as int] by {
                                if j != to { assert(seen@[j as int] == old_seen[j as int]); }
                            };
                            assert forall|j: int| 0 <= j < pending@.len() implies {
                                let item = #[trigger] pending@[j];
                                item.node < size && (item.call.is_none() ==> item.node == 0)
                            } by {
                                if j < old_pending.len() { assert(pending@[j] == old_pending[j]); }
                            };
                            assert forall|j: usize| j < size && #[trigger] seen@[j as int]
                                implies modules@[j as int].is_some() || is_pending(pending@, j) || Some(node) == Some(j) by {
                                if j == to {
                                    assert(pending@[old_pending.len() as int].node == j);
                                } else if !modules@[j as int].is_some() && j != node {
                                    assert(is_pending(old_pending, j));
                                    let k = choose|k: int| 0 <= k < old_pending.len() && (#[trigger] old_pending[k]).node == j;
                                    assert(pending@[k] == old_pending[k]);
                                }
                            };
                            assert forall|j: int, field: int| 0 <= j < graph@.len() && 0 <= field < graph@[j]@.len() implies
                                ((#[trigger] graph@[j]@[field]) matches Some(child) ==> child < size && seen@[child as int]) by {
                                if let Some(child) = graph@[j]@[field] { assert(old_seen[child as int]); }
                            };
                            assert forall|j: int| 0 <= j < row@.len() implies
                                ((#[trigger] row@[j]) matches Some(child) ==> child < size && seen@[child as int]) by {
                                if let Some(child) = row@[j] { assert(old_seen[child as int]); }
                            };
                        }
                    }
                }
                let ghost before = row@;
                row.push(target);
                assert forall|j: int| 0 <= j < row@.len() implies
                    ((#[trigger] row@[j]) matches Some(target) ==> target < size && seen@[target as int])
                    && row@[j] == call_vertex(&checked.calls@[j], vertices@) by {
                    if j < c { assert(row@[j] == before[j]); }
                };
                c += 1;
            }
            let ghost old_modules = modules@;
            let ghost old_graph = graph@;
            modules.set(node, Some(checked));
            graph.set(node, row);
            assert forall|j: usize| j < size && #[trigger] seen@[j as int]
                implies modules@[j as int].is_some() || is_pending(pending@, j) by {
                if j != node { assert(modules@[j as int] == old_modules[j as int]); }
            };
            assert forall|j: int| 0 <= j < modules@.len() implies (#[trigger] modules@[j]) matches Some(loaded)
                ==> self.module_calls_result(positions@[j], width, Ok(Some(loaded))) by {
                if j != node { assert(modules@[j] == old_modules[j]); }
            };
            assert forall|j: int| 0 <= j < graph@.len() implies {
                let row = #[trigger] graph@[j];
                row@.len() == match modules@[j] { Some(loaded) => loaded.calls@.len(), None => 0 }
            } by {
                if j != node { assert(modules@[j] == old_modules[j] && graph@[j] == old_graph[j]); }
            };
            assert forall|j: int, field: int| 0 <= j < graph@.len() && 0 <= field < graph@[j]@.len() implies
                ((#[trigger] graph@[j]@[field]) matches Some(target) ==> target < size && seen@[target as int])
                && graph@[j]@[field] == call_vertex(&modules@[j]->Some_0.calls@[field], vertices@) by {
                if j != node { assert(graph@[j] == old_graph[j] && modules@[j] == old_modules[j]); }
            };
            proof { root_loaded = true; }
        }
        assert forall|j: int, field: int| 0 <= j < graph@.len() && 0 <= field < graph@[j]@.len() implies
            ((#[trigger] graph@[j]@[field]) matches Some(target) ==> target < size && modules@[target as int].is_some()) by {
            if let Some(target) = graph@[j]@[field] {
                assert(seen@[target as int]);
                assert(!is_pending(pending@, target));
            }
        };
        Ok(Some(CheckedModules { modules, graph }))
    }

    /// ルートから到達するモジュールを子から順に展開する。
    ///
    /// 平坦なビット配列の上限には `usize::MAX` を使う。
    ///
    /// # Errors
    ///
    /// [Self::lower_clocked_module_with_limits] と同じ順に違反を診断する。
    pub fn lower_clocked_module(&self, owner: ModuleBodyPosition, width_limit: u64, gate_limit: usize)
        -> (result: Result<Option<ClockedNor>, ClockedModuleError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            result == Ok(None) ==> self.module_calls_result(owner, width_limit, Ok(None)),
            result matches Err(ClockedModuleError::Parent(error)) ==>
                self.module_calls_result(owner, width_limit, Err(error)),
            result matches Err(ClockedModuleError::Function { call, expansion }) ==>
                self.clocked_module_function_error(width_limit, usize::MAX, gate_limit, call, expansion),
            result matches Ok(Some(circuit)) ==> circuit.netlist_model().gates@.len() <= gate_limit
                && crate::netlist::clocked_wiring_valid(&circuit.netlist_model())
                && self.clocked_module_ports_match(owner, width_limit, &circuit.netlist_model())
                && self.clocked_module_source_layout(owner, width_limit, &circuit.netlist_model()),
    {
        self.lower_clocked_module_with_limits(owner, width_limit, usize::MAX, gate_limit)
    }

    /// ルートから到達するモジュールを子から順に展開する。
    ///
    /// 入出力は単一ビットで、各右辺は信号名か定数を直接渡すモジュール、関数、基底 NOR のいずれかの呼び出しとする。
    /// `bit_limit` はモジュールの入力と出力、および関数の入力・定義・出力の各ビット配列に適用する。
    /// モジュールと、モジュールから直接呼ぶ関数の展開結果は宣言ごとに共有する。
    /// ゲート番号は呼び出しごとに割り当てる。
    /// 返した回路をソースの参照回路と同じ入力列で実行すると、reset 直後と各 tick の公開出力が一致する。
    /// 指定位置がモジュールを指さなければ `None` を返す。
    ///
    /// # Errors
    ///
    /// 到達する宣言の型と呼び出しを検査する。同じ宣言から新たに見つけた呼び出し先は後ろから調べる。
    /// 宣言間の再帰は、その閉路を構成する呼び出しの位置で報告する。
    /// 各モジュールの入出力の型を確かめてから、直接呼ぶ関数を呼び出し順に展開する。
    /// 関数の展開に失敗した場合は、モジュールの呼び出し位置と関数側の診断を返す。
    /// 配線の組み立てでは、対応外の式や型、ゲート数の上限、遅延のない配線の循環を診断する。
    pub fn lower_clocked_module_with_limits(&self, owner: ModuleBodyPosition, width_limit: u64, bit_limit: usize, gate_limit: usize)
        -> (result: Result<Option<ClockedNor>, ClockedModuleError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            result == Ok(None) ==> self.module_calls_result(owner, width_limit, Ok(None)),
            result matches Err(ClockedModuleError::Parent(error)) ==>
                self.module_calls_result(owner, width_limit, Err(error)),
            result matches Err(ClockedModuleError::Function { call, expansion }) ==>
                self.clocked_module_function_error(width_limit, bit_limit, gate_limit, call, expansion),
            result matches Err(ClockedModuleError::PortLayout { direction, site, layout }) ==>
                self.clocked_module_port_error(width_limit, bit_limit, direction, site, layout),
            result matches Ok(Some(circuit)) ==> circuit.netlist_model().gates@.len() <= gate_limit
                && circuit.netlist_model().input_count <= bit_limit && circuit.netlist_model().outputs@.len() <= bit_limit
                && crate::netlist::clocked_wiring_valid(&circuit.netlist_model())
                && self.clocked_module_ports_match(owner, width_limit, &circuit.netlist_model())
                && self.clocked_module_source_layout(owner, width_limit, &circuit.netlist_model()),
    {
        let (positions, vertices) = indexed_modules(self.targets.project(), owner);
        let Some(checked) = self.reachable_modules(owner, &positions, &vertices, width_limit)? else { return Ok(None); };
        let order = match check_dependency_order(&checked.graph, true) {
            Ok(order) => order,
            Err(cycle) => return Err(ClockedModuleError::Recursion(module_cycle_sites(&checked, &cycle))),
        };
        let builtin = match builtin_instance() {
            Ok(circuit) => circuit,
            Err(error) => return Err(ClockedModuleError::Netlist(error)),
        };
        let size = positions.len();
        let mut functions = FunctionTemplates::new();
        let mut templates: Vec<Option<ClockedNor>> = Vec::with_capacity(size);
        let mut i = 0;
        while i < size
            invariant i == templates@.len() <= size,
            decreases size - i,
        {
            templates.push(None);
            i += 1;
        }
        let ghost rank = choose|rank: Seq<nat>|
            #[trigger] dependencies_in_order(checked.graph@, rank)
            && completion_order_matches(order@, rank)
            && (forall|node: int| #![trigger rank[node]] 0 <= node < checked.graph@.len()
                ==> rank[node] < order@.len() && order@[rank[node] as int] == node);
        let ghost mut layouts = Seq::new(size as nat, |_: int| None::<ModuleSourceLayout>);
        proof { self.empty_source_table(positions@, width_limit, checked.modules@, rank, layouts); }
        let mut i = 0;
        while i < order.len()
            invariant
                self.can_resolve(), size == positions@.len() == templates@.len(), positions@[0] == owner,
                obeys_cmp::<Position>(), self.clocked_functions_match(functions@, width_limit, bit_limit, gate_limit),
                forall|at: Position| #[trigger] vertices@.contains_key(at)
                    == (at == key(owner) || module_key(self.targets.project_model().circuits_model(), at)),
                self.loaded_modules_match(positions@, width_limit, checked.modules@),
                slots_match(checked.modules@, checked.graph@), checked.modules@[0].is_some(),
                completion_order_matches(order@, rank), rank.len() == size,
                forall|vertex: int| #![trigger rank[vertex]] 0 <= vertex < size
                    ==> rank[vertex] < order@.len() && order@[rank[vertex] as int] == vertex,
                dependencies_in_order(checked.graph@, rank), graph_targets_loaded(checked.graph@, checked.modules@),
                completed_templates(checked.modules@, rank, templates@, layouts, positions@, i as int),
                vertex_index_matches(positions@, vertices@), edges_match(checked.modules@, checked.graph@, vertices@),
                self.source_model_table(positions@, width_limit, checked.modules@, rank, layouts),
                forall|j: int| 0 <= j < layouts.len() && (#[trigger] layouts[j]).is_some() ==> rank[j] < i,
                builtin_nor_template(&builtin.netlist_model()),
                i <= rank[0] < order@.len(), order@[rank[0] as int] == 0usize,
            decreases order@.len() - i,
        {
            let node = order[i];
            assert(node < size && checked.graph@.len() == size);
            if let Some(loaded) = &checked.modules[node] {
                let edges = &checked.graph[node];
                proof { vstd::std_specs::vec::axiom_spec_len(edges); }
                assert forall|field: int| 0 <= field < edges@.len() implies #[trigger]
                    call_layout_is_ready(&loaded.calls@[field], edges@[field], templates@, layouts) by {
                    if let Some(child) = edges@[field] {
                        assert(field as usize as int == field);
                        let call = &loaded.calls@[field];
                        assert(edges@[field] == checked.graph@[node as int]@[field]);
                        assert(call_vertex(call, vertices@) == Some(child));
                        call_vertex_position(call, vertices@, positions@, child);
                        let position = call.inputs.ports.signature.target->Routine_position;
                        let edge = DependencyEdge { from: node, to: child, field: field as usize };
                        assert(dependency_edge(checked.graph@, edge));
                        assert(rank[child as int] < rank[node as int]);
                        assert(prior_layout_at(templates@, layouts, child as int, position));
                    }
                };
                assert(edge_templates_ready(edges@, templates@)) by {
                    assert forall|field: int| 0 <= field < edges@.len() implies
                        ((#[trigger] edges@[field]) matches Some(child) ==> child < size && templates@[child as int].is_some()) by {
                        assert(call_layout_is_ready(&loaded.calls@[field], edges@[field], templates@, layouts));
                    };
                };
                proof {
                    assert forall|field: int| 0 <= field < loaded.calls@.len() implies {
                        (#[trigger] function_target(loaded, edges@, field)) matches Some(target)
                            ==> function_position(self.targets.project_model().circuits_model(), target)
                    } by {
                        if let Some(target) = function_target(loaded, edges@, field) {
                            let call = &loaded.calls@[field];
                            self.module_calls_item_evidence(positions@[node as int], width_limit, loaded, field);
                            self.module_call_ports_evidence(call.at, width_limit, call.inputs.ports);
                            self.module_call_site_evidence(call.at, width_limit, call.inputs.ports.signature);
                            assert(edges@[field] == checked.graph@[node as int]@[field]);
                            assert(call_vertex(call, vertices@).is_none());
                            assert(!vertices@.contains_key(target));
                            assert(!module_key(self.targets.project_model().circuits_model(), target));
                        }
                    };
                }
                let circuit = self.lower_checked_module(positions[node], width_limit, bit_limit, gate_limit, loaded, edges,
                    &templates, &mut functions, &builtin)?;
                let ghost layout = self.source_layout_from_compiled(positions@[node as int], width_limit, loaded,
                    edges@, templates@, layouts, functions@, bit_limit, gate_limit, &builtin, &circuit.netlist_model());
                proof {
                    assert(layouts[node as int].is_none());
                    assert forall|field: int| 0 <= field < loaded.calls@.len() implies #[trigger]
                        self.source_call_in_table(loaded, width_limit, layout, positions@, rank, layouts, node as int, field) by {
                        let call = loaded.calls@[field];
                        self.source_layer_call_supported(loaded, &layout.circuit, &layout.layer, field);
                        if let ModuleCallTarget::Routine { position, .. } = call.inputs.ports.signature.target {
                            if edges@[field].is_none() {
                                assert(self.source_function_in_layer(width_limit, position, layout, field));
                            } else {
                                let child = edges@[field]->Some_0;
                                assert(edges@[field] == checked.graph@[node as int]@[field]);
                                assert(call_vertex(&call, vertices@) == Some(child));
                                call_vertex_position(&call, vertices@, positions@, child);
                                assert(call_layout_is_ready(&call, edges@[field], templates@, layouts));
                                let edge = DependencyEdge { from: node, to: child, field: field as usize };
                                assert(dependency_edge(checked.graph@, edge));
                                assert(rank[child as int] < rank[node as int]);
                                self.source_call_for_child(loaded, width_limit, layout, positions@, rank, layouts, node as int, field, child as int);
                            }
                        }
                    };
                    self.extend_source_table(positions@, width_limit, checked.modules@, rank, layouts, node as int, layout);
                }
                if node == 0 {
                    proof {
                        assert forall|a: int, b: int| 0 <= a < b < positions@.len() implies
                            #[trigger] positions@[a] != #[trigger] positions@[b] by {
                            let first = key(positions@[a]);
                            let second = key(positions@[b]);
                            assert(vertices@[first] == a && vertices@[second] == b);
                        };
                        self.source_model_for_root(owner, width_limit, positions@, checked.modules@, rank,
                            layouts.update(0, Some(layout)), &circuit.netlist_model());
                    }
                    return Ok(Some(circuit));
                }
                let ghost previous = templates@;
                let ghost previous_layouts = layouts;
                templates.set(node, Some(circuit));
                proof { layouts = layouts.update(node as int, Some(layout)); }
                assert forall|j: int| 0 <= j < layouts.len() && (#[trigger] layouts[j]).is_some() implies rank[j] < i + 1 by {
                    if j != node { assert(layouts[j] == previous_layouts[j]); }
                };
                assert forall|child: int| 0 <= child < checked.modules@.len() && rank[child] < i + 1
                    && checked.modules@[child].is_some() implies #[trigger]
                    prior_layout_at(templates@, layouts, child, positions@[child]) by {
                    if child != node {
                        assert(child == order@[rank[child] as int]);
                        assert(rank[child] < i);
                        assert(templates@[child] == previous[child]);
                        assert(layouts[child] == previous_layouts[child]);
                        assert(prior_layout_at(previous, previous_layouts, child, positions@[child]));
                    }
                };
            } else {
                assert forall|child: int| 0 <= child < checked.modules@.len() && rank[child] < i + 1
                    && checked.modules@[child].is_some() implies #[trigger]
                    prior_layout_at(templates@, layouts, child, positions@[child]) by {
                    assert(child == order@[rank[child] as int] && child != node);
                    assert(rank[child] < i);
                };
            }
            assert(i < rank[0]);
            i += 1;
        }
        proof { assert(false); }
        unreachable!()
    }
}

} // verus!
