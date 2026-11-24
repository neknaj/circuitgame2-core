//! 展開後の NOR 回路について、定常化の上界をゲートの深さから求める。

use super::dependency_order::check_dependency_order;
#[cfg(verus_only)]
use super::dependency_order::{DependencyEdge, complete_dependency_order, completion_order_matches,
    dependencies_in_order, dependency_cycle, dependency_edge, dependency_graph_valid, rank_excludes_cycle};
use crate::netlist::{ClockedNor, Wire};
#[cfg(verus_only)]
use crate::netlist::{NorGate, NorNetlist, clocked_gate_updates, clocked_wiring_valid, wire_available, wire_value};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

spec fn gate_dependency(wire: Wire) -> Option<usize> {
    if let Wire::Gate(gate) = wire { Some(gate) } else { None }
}

fn dependency_from_wire(wire: Wire) -> (target: Option<usize>)
    ensures target == gate_dependency(wire),
{
    if let Wire::Gate(gate) = wire { Some(gate) } else { None }
}

spec fn gate_dependencies(gates: Seq<NorGate>, graph: Seq<Vec<Option<usize>>>) -> bool {
    &&& gates.len() == graph.len()
    &&& forall|i: int| 0 <= i < gates.len() ==> {
        let row = #[trigger] graph[i];
        row@ =~= seq![gate_dependency(gates[i].left), gate_dependency(gates[i].right)]
    }
}

spec fn gate_edge(gates: Seq<NorGate>, edge: DependencyEdge) -> bool {
    &&& edge.from < gates.len() && edge.to < gates.len() && edge.field < 2
    &&& gate_dependency(if edge.field == 0 { gates[edge.from as int].left } else { gates[edge.from as int].right })
        == Some(edge.to)
}

spec fn gate_cycle(gates: Seq<NorGate>, path: Seq<DependencyEdge>) -> bool {
    &&& 0 < path.len()
    &&& forall|i: int| 0 <= i < path.len() ==> gate_edge(gates, #[trigger] path[i])
    &&& forall|i: int, j: int| 0 <= i && j == i + 1 && j < path.len() ==>
        (#[trigger] path[i]).to == (#[trigger] path[j]).from
    &&& path.last().to == path[0].from
}

/// 回路内にゲートへの参照だけで閉じる経路があることを表す。
pub closed spec fn clocked_nor_has_cycle(netlist: &NorNetlist) -> bool {
    exists|path: Seq<DependencyEdge>| #[trigger] gate_cycle(netlist.gates@, path)
}

proof fn gate_cycle_uses_dependencies(gates: Seq<NorGate>, graph: Seq<Vec<Option<usize>>>, path: Seq<DependencyEdge>)
    requires gate_dependencies(gates, graph),
    ensures gate_cycle(gates, path) == dependency_cycle(graph, path),
{
    assert forall|i: int| 0 <= i < path.len() implies
        gate_edge(gates, #[trigger] path[i]) == dependency_edge(graph, path[i]) by {
        let edge = path[i];
        if edge.from < graph.len() {
            let row = graph[edge.from as int];
            assert(row@ =~= seq![gate_dependency(gates[edge.from as int].left), gate_dependency(gates[edge.from as int].right)]);
        }
    };
    if path.len() > 0 {
        assert(path.last() == path[path.len() - 1]);
    }
}

spec fn wire_depth(depths: Seq<usize>, wire: Wire) -> nat {
    if let Wire::Gate(gate) = wire { depths[gate as int] as nat } else { 0 }
}

spec fn gate_depth(depths: Seq<usize>, gate: NorGate) -> nat {
    let left = wire_depth(depths, gate.left);
    let right = wire_depth(depths, gate.right);
    1 + if left >= right { left } else { right }
}

/// 各ゲートが入力の最大深さより1深く、上界が回路全体の最大深さになることを表す。
pub closed spec fn clocked_nor_depths(netlist: &NorNetlist, depths: Seq<usize>, bound: usize) -> bool {
    &&& clocked_wiring_valid(netlist)
    &&& depths.len() == netlist.gates@.len()
    &&& forall|i: int| 0 <= i < depths.len() ==> (#[trigger] depths[i]) == gate_depth(depths, netlist.gates@[i])
        && depths[i] <= bound
    &&& (bound == 0 || exists|i: int| 0 <= i < depths.len() && (#[trigger] depths[i]) == bound)
}

fn computed_gate_depth(wire: Wire, depths: &[usize]) -> (depth: usize)
    requires wire matches Wire::Gate(gate) ==> gate < depths@.len(),
    ensures depth == wire_depth(depths@, wire),
{
    match wire {
        Wire::Gate(gate) => depths[gate],
        Wire::Input(_) | Wire::Constant(_) => 0,
    }
}

proof fn earlier_gate_depth(wire: Wire, field: usize, node: usize, graph: Seq<Vec<Option<usize>>>, rank: Seq<nat>)
    requires
        node < graph.len(), field < graph[node as int]@.len(),
        graph[node as int]@[field as int] == gate_dependency(wire),
        dependencies_in_order(graph, rank), dependency_graph_valid(graph),
    ensures wire matches Wire::Gate(gate) ==> gate < graph.len() && rank[gate as int] < rank[node as int],
{
    if let Wire::Gate(gate) = wire {
        assert(dependency_edge(graph, DependencyEdge { from: node, field, to: gate }));
    }
}

spec fn clocked_nor_has_depth_bound(netlist: &NorNetlist, bound: usize) -> bool {
    exists|depths: Seq<usize>| #[trigger] clocked_nor_depths(netlist, depths, bound)
}

/// 閉路の有無と、各ゲートの深さから定常化上界の結果を定める。
pub closed spec fn clocked_nor_bound_matches(netlist: &NorNetlist, result: Option<usize>) -> bool {
    if let Some(bound) = result {
        !clocked_nor_has_cycle(netlist) && clocked_nor_has_depth_bound(netlist, bound)
    } else {
        clocked_nor_has_cycle(netlist)
    }
}

/// 深さ表と依存順位を、解析結果の契約へ結び付ける。
#[verifier::spinoff_prover]
proof fn completed_depths_give_bound(netlist: &NorNetlist, depths: Seq<usize>, bound: usize,
    graph: Seq<Vec<Option<usize>>>, rank: Seq<nat>,
)
    requires
        clocked_nor_depths(netlist, depths, bound),
        gate_dependencies(netlist.gates@, graph),
        dependencies_in_order(graph, rank),
    ensures clocked_nor_bound_matches(netlist, Some(bound)),
{
    assert(!clocked_nor_has_cycle(netlist)) by {
        if clocked_nor_has_cycle(netlist) {
            let path = choose|path: Seq<DependencyEdge>| #[trigger] gate_cycle(netlist.gates@, path);
            gate_cycle_uses_dependencies(netlist.gates@, graph, path);
            assert(dependency_cycle(graph, path));
            rank_excludes_cycle(graph, rank, path);
            assert(false);
        }
    };
    assert(clocked_nor_has_depth_bound(netlist, bound)) by {
        assert(clocked_nor_depths(netlist, depths, bound));
    };
    assert(clocked_nor_bound_matches(netlist, Some(bound))) by {
        reveal(clocked_nor_bound_matches);
    };
}

/// ゲート専用回路が固定入力で定常化するまでの tick 数の上界を返す。
///
/// 到達する公開出力の有無にかかわらず全ゲートを調べる。ゲートを含まなければ0を、
/// フィードバックがあれば未推定を表す `None` を返す。
pub fn clocked_nor_settling_bound(circuit: &ClockedNor) -> (result: Option<usize>)
    ensures clocked_nor_bound_matches(&circuit.netlist_model(), result),
{
    let netlist = circuit.checked_netlist();
    proof { crate::netlist::clocked_wiring_endpoints(netlist); }
    let mut graph: Vec<Vec<Option<usize>>> = Vec::new();
    let mut i = 0;
    while i < netlist.gates.len()
        invariant
            i == graph@.len() <= netlist.gates@.len(),
            gate_dependencies(netlist.gates@.take(i as int), graph@),
            forall|j: int| 0 <= j < netlist.gates@.len() ==> {
                let gate = #[trigger] netlist.gates@[j];
                wire_available(gate.left, netlist.input_count as nat, netlist.gates@.len())
                    && wire_available(gate.right, netlist.input_count as nat, netlist.gates@.len())
            },
            forall|j: int, side: int| 0 <= j < i && 0 <= side < 2 ==>
                ((#[trigger] graph@[j]@[side]) matches Some(target) ==> target < netlist.gates@.len()),
        decreases netlist.gates@.len() - i,
    {
        let gate = netlist.gates[i];
        let mut row = Vec::new();
        row.push(dependency_from_wire(gate.left));
        row.push(dependency_from_wire(gate.right));
        assert(row@ =~= seq![gate_dependency(gate.left), gate_dependency(gate.right)]);
        let ghost earlier = graph@;
        graph.push(row);
        assert forall|j: int| 0 <= j <= i implies (#[trigger] graph@[j])@ =~=
            seq![gate_dependency(netlist.gates@[j].left), gate_dependency(netlist.gates@[j].right)] by {
            if j < i { assert(graph@[j] == earlier[j]); }
        };
        assert forall|j: int, side: int| 0 <= j <= i && 0 <= side < 2 implies
            ((#[trigger] graph@[j]@[side]) matches Some(target) ==> target < netlist.gates@.len()) by {
            if j < i {
                assert(graph@[j] == earlier[j]);
            } else {
                assert(wire_available(gate.left, netlist.input_count as nat, netlist.gates@.len()));
                assert(wire_available(gate.right, netlist.input_count as nat, netlist.gates@.len()));
                assert(graph@[j]@ =~= seq![gate_dependency(gate.left), gate_dependency(gate.right)]);
            }
        };
        i += 1;
    }
    assert(netlist.gates@.take(i as int) =~= netlist.gates@);
    let order = match check_dependency_order(graph.as_slice(), true) {
        Ok(order) => order,
        Err(path) => {
            proof { gate_cycle_uses_dependencies(netlist.gates@, graph@, path@); }
            assert(clocked_nor_has_cycle(netlist));
            assert(clocked_nor_bound_matches(&circuit.netlist_model(), None));
            return None;
        },
    };
    let ghost rank = choose|rank: Seq<nat>| #[trigger] dependencies_in_order(graph@, rank)
        && order@.len() == graph@.len() && completion_order_matches(order@, rank)
        && (forall|node: int| #![trigger rank[node]] 0 <= node < graph@.len()
            ==> rank[node] < order@.len() && order@[rank[node] as int] == node);
    assert(complete_dependency_order(graph@, order@));
    let mut depths = alloc::vec![0usize; netlist.gates.len()];
    let mut bound = 0;
    let mut i = 0;
    while i < order.len()
        invariant
            i <= order@.len() == depths@.len() == graph@.len() == netlist.gates@.len(),
            dependencies_in_order(graph@, rank), completion_order_matches(order@, rank),
            gate_dependencies(netlist.gates@, graph@), dependency_graph_valid(graph@),
            *netlist == circuit.netlist_model(), clocked_wiring_valid(netlist),
            forall|node: int| #![trigger rank[node]] 0 <= node < depths@.len() ==>
                rank[node] < order@.len() && order@[rank[node] as int] == node,
            forall|node: int| 0 <= node < depths@.len() && rank[node] < i ==>
                (#[trigger] depths@[node]) == gate_depth(depths@, netlist.gates@[node])
                    && depths@[node] <= rank[node] + 1 && depths@[node] <= bound,
            bound == 0 || exists|node: int| 0 <= node < depths@.len() && rank[node] < i && (#[trigger] depths@[node]) == bound,
        decreases order@.len() - i,
    {
        let node = order[i];
        let gate = netlist.gates[node];
        proof {
            assert(rank[node as int] == i);
            earlier_gate_depth(gate.left, 0, node, graph@, rank);
            earlier_gate_depth(gate.right, 1, node, graph@, rank);
        }
        let left = computed_gate_depth(gate.left, depths.as_slice());
        let right = computed_gate_depth(gate.right, depths.as_slice());
        assert(left <= i && right <= i) by {
            if let Wire::Gate(from) = gate.left { assert(depths@[from as int] <= rank[from as int] + 1); }
            if let Wire::Gate(from) = gate.right { assert(depths@[from as int] <= rank[from as int] + 1); }
        };
        let depth = if left >= right { left + 1 } else { right + 1 };
        let ghost earlier = depths@;
        let ghost prior_bound = bound;
        depths.set(node, depth);
        if depth > bound { bound = depth; }
        assert forall|j: int| 0 <= j < depths@.len() && rank[j] < i + 1 implies
            (#[trigger] depths@[j]) == gate_depth(depths@, netlist.gates@[j])
                && depths@[j] <= rank[j] + 1 && depths@[j] <= bound by {
            let other = netlist.gates@[j];
            earlier_gate_depth(other.left, 0, j as usize, graph@, rank);
            earlier_gate_depth(other.right, 1, j as usize, graph@, rank);
            assert(wire_depth(depths@, other.left) == wire_depth(earlier, other.left));
            assert(wire_depth(depths@, other.right) == wire_depth(earlier, other.right));
            if j != node {
                assert(rank[j] < i);
                assert(depths@[j] == earlier[j]);
            }
        };
        proof {
            if bound == depth {
                assert(depths@[node as int] == bound);
                assert(rank[node as int] == i);
                assert(exists|j: int| 0 <= j < depths@.len() && rank[j] < i + 1 && (#[trigger] depths@[j]) == bound);
            } else {
                assert(bound == prior_bound && bound > 0);
                let earlier_max = choose|j: int| 0 <= j < earlier.len() && rank[j] < i && (#[trigger] earlier[j]) == prior_bound;
                assert(earlier_max != node && depths@[earlier_max] == bound);
                assert(exists|j: int| 0 <= j < depths@.len() && rank[j] < i + 1 && (#[trigger] depths@[j]) == bound);
            }
        }
        i += 1;
    }
    proof {
        let model = &circuit.netlist_model();
        assert(*model == *netlist);
        assert(clocked_nor_depths(model, depths@, bound));
        completed_depths_give_bound(model, depths@, bound, graph@, rank);
    }
    Some(bound)
}

/// 全 tick に同じ入力を与えたときの内部状態列。最初の状態は任意のゲート値を取れる。
pub open spec fn fixed_nor_states(netlist: &NorNetlist, input: Seq<bool>, states: Seq<Seq<bool>>) -> bool {
    &&& input.len() == netlist.input_count
    &&& forall|i: int| 0 <= i < states.len() ==> (#[trigger] states[i]).len() == netlist.gates@.len()
    &&& forall|i: int| 0 < i < states.len() ==>
        #[trigger] clocked_gate_updates(netlist.gates@, input, states[i - 1], states[i])
}

/// 二つの履歴がそのゲートの深さまで進めば、同じ固定入力から同じ値を得る。
proof fn gate_settles_by_depth(netlist: &NorNetlist, depths: Seq<usize>, bound: usize, gate: int,
    input: Seq<bool>, first: Seq<Seq<bool>>, second: Seq<Seq<bool>>, a: int, b: int,
)
    requires
        clocked_nor_depths(netlist, depths, bound),
        fixed_nor_states(netlist, input, first), fixed_nor_states(netlist, input, second),
        0 <= gate < depths.len(), depths[gate] <= a < first.len(), depths[gate] <= b < second.len(),
    ensures first[a][gate] == second[b][gate],
    decreases depths[gate],
{
    let current = netlist.gates@[gate];
    crate::netlist::clocked_wiring_endpoints(netlist);
    assert(depths[gate] == gate_depth(depths, current) && depths[gate] > 0);
    if let Wire::Gate(left) = current.left {
        assert(wire_depth(depths, current.left) < depths[gate]);
        gate_settles_by_depth(netlist, depths, bound, left as int, input, first, second, a - 1, b - 1);
    }
    if let Wire::Gate(right) = current.right {
        assert(wire_depth(depths, current.right) < depths[gate]);
        gate_settles_by_depth(netlist, depths, bound, right as int, input, first, second, a - 1, b - 1);
    }
    assert(wire_value(current.left, input, first[a - 1]) == wire_value(current.left, input, second[b - 1]));
    assert(wire_value(current.right, input, first[a - 1]) == wire_value(current.right, input, second[b - 1]));
    assert(clocked_gate_updates(netlist.gates@, input, first[a - 1], first[a]));
    assert(clocked_gate_updates(netlist.gates@, input, second[b - 1], second[b]));
}

/// 上界以降の全ゲートの値は、初期状態や経過 tick にかかわらず固定入力だけで決まる。
pub proof fn clocked_nor_states_settle(netlist: &NorNetlist, bound: usize, input: Seq<bool>,
    first: Seq<Seq<bool>>, second: Seq<Seq<bool>>, a: int, b: int,
)
    requires
        clocked_nor_bound_matches(netlist, Some(bound)),
        fixed_nor_states(netlist, input, first), fixed_nor_states(netlist, input, second),
        bound <= a < first.len(), bound <= b < second.len(),
    ensures first[a] == second[b],
{
    let depths = choose|depths: Seq<usize>| #[trigger] clocked_nor_depths(netlist, depths, bound);
    assert forall|gate: int| 0 <= gate < netlist.gates@.len() implies (#[trigger] first[a][gate]) == second[b][gate] by {
        gate_settles_by_depth(netlist, depths, bound, gate, input, first, second, a, b);
    };
    assert(first[a] =~= second[b]);
}

} // verus!
