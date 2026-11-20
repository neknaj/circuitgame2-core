//! 依存先が先に並ぶ順序を求め、循環があれば元の辺をたどる閉路を返す。

use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, Debug)]
pub(super) struct DependencyEdge {
    pub(super) from: usize,
    pub(super) field: usize,
    pub(super) to: usize,
}

pub(super) open spec fn dependency_graph_valid(graph: Seq<Vec<Option<usize>>>) -> bool {
    forall|row: int, field: int| 0 <= row < graph.len() && 0 <= field < graph[row]@.len() ==>
        ((#[trigger] graph[row]@[field]) matches Some(target) ==> target < graph.len())
}

pub(super) open spec fn dependency_edge(graph: Seq<Vec<Option<usize>>>, edge: DependencyEdge) -> bool {
    &&& edge.from < graph.len()
    &&& edge.to < graph.len()
    &&& edge.field < graph[edge.from as int]@.len()
    &&& graph[edge.from as int]@[edge.field as int] == Some(edge.to)
}

pub(super) open spec fn dependencies_in_order(graph: Seq<Vec<Option<usize>>>, rank: Seq<nat>) -> bool {
    &&& rank.len() == graph.len()
    &&& forall|edge: DependencyEdge| #[trigger] dependency_edge(graph, edge) ==>
        rank[edge.to as int] < rank[edge.from as int]
}

pub(super) open spec fn dependency_cycle(graph: Seq<Vec<Option<usize>>>, path: Seq<DependencyEdge>) -> bool {
    &&& 0 < path.len()
    &&& forall|i: int| 0 <= i < path.len() ==> dependency_edge(graph, #[trigger] path[i])
    &&& forall|a: int, b: int| 0 <= a && b == a + 1 && b < path.len() ==>
        (#[trigger] path[a]).to == (#[trigger] path[b]).from
    &&& path[path.len() - 1].to == path[0].from
}

proof fn rank_decreases_along_path(
    graph: Seq<Vec<Option<usize>>>, rank: Seq<nat>, path: Seq<DependencyEdge>, at: int,
)
    requires
        dependencies_in_order(graph, rank),
        dependency_cycle(graph, path),
        0 <= at < path.len(),
    ensures rank[path[at].to as int] < rank[path[0].from as int],
    decreases at,
{
    assert(dependency_edge(graph, path[at]));
    if at > 0 {
        rank_decreases_along_path(graph, rank, path, at - 1);
        assert(path[at - 1].to == path[at].from);
    }
}

/// すべての依存辺で順位が下がるとき、同じ頂点に戻る閉路は存在しない。
pub(super) proof fn rank_excludes_cycle(
    graph: Seq<Vec<Option<usize>>>, rank: Seq<nat>, path: Seq<DependencyEdge>,
)
    requires dependencies_in_order(graph, rank),
    ensures !dependency_cycle(graph, path),
{
    if dependency_cycle(graph, path) {
        rank_decreases_along_path(graph, rank, path, path.len() - 1);
    }
}

#[derive(Clone, Copy)]
enum Visit {
    New,
    Active(usize),
    Done,
}

#[derive(Clone, Copy)]
struct Frame {
    node: usize,
    next: usize,
}

spec fn visited_prefix(graph: Seq<Vec<Option<usize>>>, states: Seq<Visit>, frame: Frame) -> bool {
    forall|field: int| 0 <= field < frame.next ==>
        ((#[trigger] graph[frame.node as int]@[field]) matches Some(child) ==> states[child as int] is Done)
}

spec fn stack_links(graph: Seq<Vec<Option<usize>>>, stack: Seq<Frame>) -> bool {
    forall|a: int, b: int| 0 <= a && b == a + 1 && b < stack.len() ==> {
        let parent = #[trigger] stack[a];
        let child = #[trigger] stack[b];
        dependency_edge(graph, DependencyEdge { from: parent.node, field: parent.next, to: child.node })
    }
}

spec fn stack_matches(graph: Seq<Vec<Option<usize>>>, states: Seq<Visit>, stack: Seq<Frame>) -> bool {
    &&& forall|depth: int| 0 <= depth < stack.len() ==> {
        let frame = #[trigger] stack[depth];
        &&& frame.node < graph.len()
        &&& states[frame.node as int] == Visit::Active(depth as usize)
        &&& frame.next <= graph[frame.node as int]@.len()
        &&& visited_prefix(graph, states, frame)
    }
    &&& stack_links(graph, stack)
    &&& forall|node: int| 0 <= node < states.len() && (#[trigger] states[node]) is Active ==> {
        let depth = states[node]->Active_0 as int;
        &&& depth < stack.len()
        &&& stack[depth].node == node
    }
}

spec fn completed_matches(
    graph: Seq<Vec<Option<usize>>>, states: Seq<Visit>, ranks: Seq<nat>, completed: nat,
) -> bool {
    &&& states.len() == ranks.len()
    &&& forall|node: int| 0 <= node < states.len() && (#[trigger] states[node]) is Done ==>
        ranks[node] < completed
    &&& forall|edge: DependencyEdge| #[trigger] dependency_edge(graph, edge)
        && states[edge.from as int] is Done ==> {
        states[edge.to as int] is Done && ranks[edge.to as int] < ranks[edge.from as int]
    }
}

spec fn unvisited_matches(states: Seq<Visit>, unvisited: Set<usize>) -> bool {
    forall|node: usize| node < states.len() ==> (#[trigger] unvisited.contains(node)) == (states[node as int] is New)
}

spec fn fields_left_at_top(graph: Seq<Vec<Option<usize>>>, stack: Seq<Frame>) -> nat {
    if stack.len() == 0 {
        0
    } else {
        let top = stack.last();
        (graph[top.node as int]@.len() - top.next) as nat
    }
}

fn close_cycle(
    _graph: &[Vec<Option<usize>>], stack: &[Frame], first: usize, edge: DependencyEdge,
) -> (cycle: Vec<DependencyEdge>)
    requires
        0 < stack@.len(), first < stack@.len(),
        dependency_edge(_graph@, edge),
        edge.from == stack@.last().node, edge.to == stack@[first as int].node,
        stack_links(_graph@, stack@),
    ensures dependency_cycle(_graph@, cycle@),
{
    let mut cycle: Vec<DependencyEdge> = Vec::new();
    let mut depth = first;
    while depth < stack.len() - 1
        invariant
            first <= depth < stack@.len(),
            cycle@.len() == depth - first,
            forall|i: int| 0 <= i < cycle@.len() ==> {
                let parent = stack@[first + i];
                &&& (#[trigger] cycle@[i]).from == parent.node
                &&& cycle@[i].field == parent.next
                &&& cycle@[i].to == stack@[first + i + 1].node
            },
            stack_links(_graph@, stack@),
        decreases stack@.len() - depth,
    {
        let parent = stack[depth];
        let child = stack[depth + 1];
        cycle.push(DependencyEdge { from: parent.node, field: parent.next, to: child.node });
        depth += 1;
    }
    let ghost prefix = cycle@;
    cycle.push(edge);
    assert forall|i: int| 0 <= i < cycle@.len() implies dependency_edge(_graph@, #[trigger] cycle@[i]) by {
        if i < prefix.len() {
            assert(cycle@[i] == prefix[i]);
            let depth = first + i;
            let parent = stack@[depth];
            assert(dependency_edge(_graph@, DependencyEdge {
                from: parent.node, field: parent.next, to: stack@[depth + 1].node,
            }));
        }
    };
    assert forall|a: int, b: int| 0 <= a && b == a + 1 && b < cycle@.len() implies
        (#[trigger] cycle@[a]).to == (#[trigger] cycle@[b]).from by {
        assert(cycle@[a] == prefix[a]);
        if b < prefix.len() { assert(cycle@[b] == prefix[b]); }
    };
    cycle
}

fn begin_visit(
    _graph: &[Vec<Option<usize>>], states: &mut Vec<Visit>, stack: &mut Vec<Frame>,
    _ranks: Ghost<Seq<nat>>, _completed: Ghost<nat>, node: usize,
)
    requires
        old(states)@.len() == _graph@.len(),
        stack_matches(_graph@, old(states)@, old(stack)@),
        completed_matches(_graph@, old(states)@, _ranks@, _completed@),
        node < old(states)@.len(),
        old(states)@[node as int] is New,
        old(stack)@.len() > 0 ==> {
            let parent = old(stack)@.last();
            dependency_edge(_graph@, DependencyEdge { from: parent.node, field: parent.next, to: node })
        },
    ensures
        final(states)@ == old(states)@.update(node as int, Visit::Active(old(stack)@.len() as usize)),
        final(stack)@ == old(stack)@.push(Frame { node, next: 0 }),
        stack_matches(_graph@, final(states)@, final(stack)@),
        completed_matches(_graph@, final(states)@, _ranks@, _completed@),
{
    let depth = stack.len();
    states.set(node, Visit::Active(depth));
    stack.push(Frame { node, next: 0 });
}

fn finish_visit(
    _graph: &[Vec<Option<usize>>], states: &mut Vec<Visit>, stack: &mut Vec<Frame>,
    _ranks: Ghost<Seq<nat>>, _completed: Ghost<nat>,
)
    requires
        old(states)@.len() == _graph@.len(),
        stack_matches(_graph@, old(states)@, old(stack)@),
        completed_matches(_graph@, old(states)@, _ranks@, _completed@),
        0 < old(stack)@.len(),
        old(stack)@.last().next == _graph@[old(stack)@.last().node as int]@.len(),
    ensures
        final(states)@ == old(states)@.update(old(stack)@.last().node as int, Visit::Done),
        final(stack)@ == old(stack)@.take(old(stack)@.len() - 1),
        stack_matches(_graph@, final(states)@, final(stack)@),
        completed_matches(_graph@, final(states)@,
            _ranks@.update(old(stack)@.last().node as int, _completed@), _completed@ + 1),
{
    let top = stack.len() - 1;
    let node = stack[top].node;
    states.set(node, Visit::Done);
    stack.pop();
}

fn advance_field(
    _graph: &[Vec<Option<usize>>], _states: &[Visit], stack: &mut Vec<Frame>,
)
    requires
        _states@.len() == _graph@.len(),
        stack_matches(_graph@, _states@, old(stack)@),
        0 < old(stack)@.len(),
        ({
            let frame = old(stack)@.last();
            &&& frame.next < _graph@[frame.node as int]@.len()
            &&& _graph@[frame.node as int]@[frame.next as int] matches Some(child) ==>
                child < _states@.len() && _states@[child as int] is Done
        }),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        fields_left_at_top(_graph@, final(stack)@) < fields_left_at_top(_graph@, old(stack)@),
        stack_matches(_graph@, _states@, final(stack)@),
{
    let top = stack.len() - 1;
    let frame = stack[top];
    proof { vstd::std_specs::vec::axiom_spec_len(&_graph@[frame.node as int]); }
    stack.set(top, Frame { node: frame.node, next: frame.next + 1 });
}

pub(super) open spec fn graph_has_cycle(graph: Seq<Vec<Option<usize>>>) -> bool {
    exists|path: Seq<DependencyEdge>| #[trigger] dependency_cycle(graph, path)
}

pub(super) open spec fn completion_order_matches(order: Seq<usize>, ranks: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < order.len() ==> {
        let node = #[trigger] order[i];
        node < ranks.len() && ranks[node as int] == i
    }
}

pub(super) open spec fn complete_dependency_order(graph: Seq<Vec<Option<usize>>>, order: Seq<usize>) -> bool {
    exists|rank: Seq<nat>| #[trigger] dependencies_in_order(graph, rank)
        && order.len() == graph.len() && completion_order_matches(order, rank)
        && (forall|node: int| #![trigger rank[node]] 0 <= node < graph.len()
            ==> rank[node] < order.len() && order[rank[node] as int] == node)
}

pub(super) fn check_dependency_order(graph: &[Vec<Option<usize>>], retain_order: bool)
    -> (result: Result<Vec<usize>, Vec<DependencyEdge>>)
    requires dependency_graph_valid(graph@),
    ensures
        result.is_err() <==> graph_has_cycle(graph@),
        match result {
            Ok(order) => if retain_order {
                complete_dependency_order(graph@, order@)
            } else { order@.len() == 0 && (exists|rank: Seq<nat>| #[trigger] dependencies_in_order(graph@, rank)) },
            Err(cycle) => dependency_cycle(graph@, cycle@),
        },
{
    let mut states = Vec::new();
    let ghost mut unvisited = Set::<usize>::empty();
    let mut i = 0;
    while i < graph.len()
        invariant
            i == states@.len() <= graph@.len(),
            forall|node: int| 0 <= node < i ==> (#[trigger] states@[node]) is New,
            unvisited_matches(states@, unvisited),
            unvisited.len() == i,
            forall|node: usize| #[trigger] unvisited.contains(node) ==> node < i,
        decreases graph@.len() - i,
    {
        states.push(Visit::New);
        proof {
            vstd::set::lemma_set_insert_len(unvisited, i);
            unvisited = unvisited.insert(i);
        }
        i += 1;
    }

    let ghost mut completed = 0nat;
    let ghost mut ranks = Seq::new(states@.len(), |_: int| 0nat);
    let mut order = Vec::new();
    let mut stack: Vec<Frame> = Vec::new();
    let mut root = 0;
    while root < graph.len() || !stack.is_empty()
        invariant
            dependency_graph_valid(graph@),
            states@.len() == graph@.len(),
            root <= graph@.len(),
            unvisited_matches(states@, unvisited),
            stack_matches(graph@, states@, stack@),
            completed_matches(graph@, states@, ranks, completed),
            completed + unvisited.len() + stack@.len() == graph@.len(),
            forall|node: usize| #[trigger] unvisited.contains(node) ==> node < graph@.len(),
            !retain_order ==> order@.len() == 0,
            retain_order ==> order@.len() == completed && completion_order_matches(order@, ranks)
                && (forall|node: int| 0 <= node < states@.len() && (#[trigger] states@[node]) is Done
                    ==> ranks[node] < order@.len() && order@[ranks[node] as int] == node)
                && (forall|i: int| 0 <= i < order@.len() ==> states@[(#[trigger] order@[i]) as int] is Done),
            forall|node: int| 0 <= node < root ==> !((#[trigger] states@[node]) is New),
        decreases graph@.len() - root, unvisited.len(), stack@.len(), fields_left_at_top(graph@, stack@),
    {
        if stack.is_empty() {
            if matches!(states[root], Visit::New) {
                proof {
                    vstd::set::lemma_set_remove_len(unvisited, root);
                    unvisited = unvisited.remove(root);
                }
                begin_visit(graph, &mut states, &mut stack, Ghost(ranks), Ghost(completed), root);
            }
            root += 1;
            continue;
        }

        let top = stack.len() - 1;
        let frame = stack[top];
        if frame.next == graph[frame.node].len() {
            let ghost old_order = order@;
            let ghost old_ranks = ranks;
            let ghost old_states = states@;
            finish_visit(graph, &mut states, &mut stack, Ghost(ranks), Ghost(completed));
            if retain_order {
                order.push(frame.node);
            }
            proof {
                ranks = ranks.update(frame.node as int, completed);
                completed = completed + 1;
                if retain_order {
                    assert forall|i: int| 0 <= i < order@.len() implies {
                        let node = #[trigger] order@[i];
                        node < ranks.len() && ranks[node as int] == i && states@[node as int] is Done
                    } by {
                        if i < old_order.len() {
                            let node = old_order[i];
                            assert(old_states[node as int] is Done);
                            assert(old_states[frame.node as int] is Active);
                            assert(node != frame.node);
                            assert(ranks[node as int] == old_ranks[node as int]);
                        }
                    };
                    assert(completion_order_matches(order@, ranks));
                    assert forall|i: int| 0 <= i < order@.len()
                        implies states@[(#[trigger] order@[i]) as int] is Done by {};
                    assert forall|node: int| 0 <= node < states@.len() && (#[trigger] states@[node]) is Done
                        implies ranks[node] < order@.len() && order@[ranks[node] as int] == node by {
                        if node != frame.node {
                            assert(old_states[node] is Done);
                        }
                    };
                }
            }
            continue;
        }

        let field = frame.next;
        if let Some(child) = graph[frame.node][field] {
            match states[child] {
                Visit::Active(first) => {
                    let edge = DependencyEdge { from: frame.node, field, to: child };
                    let cycle = close_cycle(graph, stack.as_slice(), first, edge);
                    assert(graph_has_cycle(graph@));
                    return Err(cycle);
                },
                Visit::New => {
                    proof {
                        vstd::set::lemma_set_remove_len(unvisited, child);
                        unvisited = unvisited.remove(child);
                    }
                    // 親のカーソルは、子の順位が確定するまで参照辺に置く。
                    begin_visit(graph, &mut states, &mut stack, Ghost(ranks), Ghost(completed), child);
                    continue;
                },
                Visit::Done => {},
            }
        }
        advance_field(graph, states.as_slice(), &mut stack);
    }

    proof {
        assert(unvisited =~= Set::<usize>::empty());
        assert forall|node: int| 0 <= node < graph@.len() implies (#[trigger] states@[node]) is Done by {};
        assert forall|edge: DependencyEdge| #[trigger] dependency_edge(graph@, edge) implies
            ranks[edge.to as int] < ranks[edge.from as int] by {};
        assert(dependencies_in_order(graph@, ranks));
        if retain_order {
            assert(order@.len() == graph@.len() && completion_order_matches(order@, ranks));
            assert forall|node: int| #![trigger ranks[node]] 0 <= node < graph@.len()
                implies ranks[node] < order@.len() && order@[ranks[node] as int] == node by {
                assert(states@[node] is Done);
            };
        }
        assert forall|path: Seq<DependencyEdge>| !#[trigger] dependency_cycle(graph@, path) by {
            rank_excludes_cycle(graph@, ranks, path);
        };
    }
    Ok(order)
}

} // verus!
