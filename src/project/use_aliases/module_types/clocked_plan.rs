//! 親回路のゲート番号を予約し、遅延を持たない出力の接続先を確定する。

use crate::netlist::{Wire, wire_within};
use crate::project::use_aliases::dependency_order::{DependencyEdge, check_dependency_order};
#[cfg(verus_only)]
use crate::{netlist::wire_available, project::use_aliases::dependency_order::{
    complete_dependency_order, completion_order_matches, dependencies_in_order, dependency_cycle, dependency_edge,
    dependency_graph_valid,
}};
use alloc::{vec, vec::Vec};
use core::ops::Range;
use vstd::prelude::*;

verus! {

/// 親回路の一つのビットの駆動元。実引数への直結は `Alias` で表す。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedWireDriver {
    /// 親回路の入力、定数、または番号を予約済みのゲート出力。
    Terminal(Wire),
    /// その位置にある別のビットの駆動元を参照する。参照先は後ろにあってもよい。
    Alias(usize),
}

/// 子回路の配置先と、直結をたどった後の配線。
#[derive(Debug)]
pub struct ClockedLinkPlan {
    /// 子回路の順に割り当てた連続区間。ゲートを持たない回路の区間は空。
    pub regions: Vec<Range<usize>>,
    /// 親回路に配置する全ゲートの件数。
    pub gate_count: usize,
    /// 駆動元の指定順に並ぶ配線。
    pub wires: Vec<Wire>,
}

/// ゲート番号の予約や直結の解決で見つかった違反。
#[derive(Debug, Eq, PartialEq)]
pub enum ClockedPlanError {
    /// ゲート数の上限を初めて超える子回路の位置。
    GateCapacity(usize),
    /// 最初に見つかった範囲外の駆動元の位置。
    Wire(usize),
    /// 直結だけで閉じる循環。各要素は駆動元の位置で、末尾は先頭を参照する。
    AliasCycle(Vec<usize>),
}

#[verifier::opaque]
spec fn preceding_gates(counts: Seq<usize>, end: int) -> nat
    decreases end,
{
    if end <= 0 { 0 } else { preceding_gates(counts, end - 1) + counts[end - 1] as nat }
}

#[verifier::opaque]
spec fn region_prefix(counts: Seq<usize>, regions: Seq<Range<usize>>, limit: usize) -> bool {
    &&& regions.len() <= counts.len()
    &&& forall|i: int| 0 <= i < regions.len() ==> {
        let region = #[trigger] regions[i];
        &&& region.start == preceding_gates(counts, i)
        &&& region.end == preceding_gates(counts, i + 1)
        &&& region.end <= limit
    }
}

spec fn gate_capacity_at(counts: Seq<usize>, limit: usize, i: usize) -> bool {
    &&& i < counts.len()
    &&& forall|j: int| 0 <= j <= i ==> #[trigger] preceding_gates(counts, j) <= limit
    &&& preceding_gates(counts, i + 1) > limit
}

/// 各区間の長さが子回路のゲート数と一致し、親回路のゲート番号を漏れや重複なく割り当てることを表す。
pub open spec fn clocked_regions_cover(counts: Seq<usize>, regions: Seq<Range<usize>>, total: usize) -> bool {
    &&& regions.len() == counts.len()
    &&& (regions.len() == 0 ==> total == 0)
    &&& forall|i: int| 0 <= i < regions.len() ==> {
        let region = #[trigger] regions[i];
        &&& region.start <= region.end <= total
        &&& region.end - region.start == counts[i]
        &&& region.start == if i == 0 { 0 } else { regions[i - 1].end }
        &&& (i + 1 == regions.len() ==> region.end == total)
    }
}

proof fn reserved_regions_cover(counts: Seq<usize>, regions: Seq<Range<usize>>, limit: usize, total: usize)
    requires regions.len() == counts.len(), region_prefix(counts, regions, limit),
        total == preceding_gates(counts, counts.len() as int),
    ensures clocked_regions_cover(counts, regions, total),
{
    reveal(region_prefix);
    reveal(preceding_gates);
    assert forall|i: int| 0 <= i < regions.len() implies {
        let region = #[trigger] regions[i];
        &&& region.start <= region.end <= total
        &&& region.end - region.start == counts[i]
        &&& region.start == if i == 0 { 0 } else { regions[i - 1].end }
        &&& (i + 1 == regions.len() ==> region.end == total)
    } by {
        assert(preceding_gates(counts, i + 1) == preceding_gates(counts, i) + counts[i]);
        if i > 0 { assert(regions[i - 1].end == preceding_gates(counts, i)); }
        gate_prefix_grows(counts, i + 1, counts.len() as int);
    };
}

proof fn gate_prefix_grows(counts: Seq<usize>, before: int, after: int)
    requires 0 <= before <= after <= counts.len(),
    ensures preceding_gates(counts, before) <= preceding_gates(counts, after),
    decreases after - before,
{
    if before < after {
        reveal(preceding_gates);
        gate_prefix_grows(counts, before, after - 1);
    }
}

fn reserve_regions(counts: &[usize], limit: usize) -> (result: Result<(Vec<Range<usize>>, usize), usize>)
    ensures match result {
        Ok((regions, total)) => regions@.len() == counts@.len() && region_prefix(counts@, regions@, limit)
            && total == preceding_gates(counts@, counts@.len() as int) && total <= limit,
        Err(i) => gate_capacity_at(counts@, limit, i),
    },
{
    let mut regions = Vec::with_capacity(counts.len());
    let mut end = 0;
    let mut i = 0;
    assert(region_prefix(counts@, regions@, limit)) by { reveal(region_prefix); };
    assert(end == preceding_gates(counts@, 0)) by { reveal(preceding_gates); };
    while i < counts.len()
        invariant
            i == regions@.len() <= counts@.len(), region_prefix(counts@, regions@, limit),
            end == preceding_gates(counts@, i as int), end <= limit,
        decreases counts@.len() - i,
    {
        let count = counts[i];
        assert(preceding_gates(counts@, i + 1) == end + count) by { reveal(preceding_gates); };
        if count > limit - end {
            proof {
                reveal(region_prefix);
                assert forall|j: int| 0 <= j <= i implies #[trigger] preceding_gates(counts@, j) <= limit by {
                    if j > 0 {
                        assert(regions@[j - 1].end == preceding_gates(counts@, j));
                    } else { reveal(preceding_gates); }
                };
            }
            return Err(i);
        }
        let start = end;
        end += count;
        let ghost prior = regions@;
        regions.push(start..end);
        assert(region_prefix(counts@, regions@, limit)) by {
            reveal(region_prefix);
            assert forall|j: int| 0 <= j < regions@.len() implies {
                let region = #[trigger] regions@[j];
                region.start == preceding_gates(counts@, j) && region.end == preceding_gates(counts@, j + 1)
                    && region.end <= limit
            } by {
                if j < i { assert(regions@[j] == prior[j]); }
            };
        };
        i += 1;
    }
    Ok((regions, end))
}

spec fn wire_valid(driver: ClockedWireDriver, inputs: usize, gates: usize, size: nat) -> bool {
    match driver {
        ClockedWireDriver::Terminal(wire) => wire_available(wire, inputs as nat, gates as nat),
        ClockedWireDriver::Alias(target) => target < size,
    }
}

spec fn alias_target(driver: ClockedWireDriver) -> Option<usize> {
    match driver {
        ClockedWireDriver::Terminal(_) => None,
        ClockedWireDriver::Alias(target) => Some(target),
    }
}

#[verifier::opaque]
spec fn driver_graph_prefix(drivers: Seq<ClockedWireDriver>, graph: Seq<Vec<Option<usize>>>) -> bool {
    &&& graph.len() <= drivers.len()
    &&& forall|i: int| 0 <= i < graph.len() ==>
        (#[trigger] graph[i])@ == seq![alias_target(drivers[i])]
}

spec fn valid_drivers_prefix(drivers: Seq<ClockedWireDriver>, inputs: usize, gates: usize, end: int) -> bool {
    forall|i: int| 0 <= i < end ==> wire_valid(#[trigger] drivers[i], inputs, gates, drivers.len())
}

fn build_driver_graph(drivers: &[ClockedWireDriver], inputs: usize, gates: usize)
    -> (result: Result<Vec<Vec<Option<usize>>>, usize>)
    ensures match result {
        Ok(graph) => graph@.len() == drivers@.len() && driver_graph_prefix(drivers@, graph@)
            && dependency_graph_valid(graph@) && valid_drivers_prefix(drivers@, inputs, gates, drivers@.len() as int),
        Err(i) => i < drivers@.len() && valid_drivers_prefix(drivers@, inputs, gates, i as int)
            && !wire_valid(drivers@[i as int], inputs, gates, drivers@.len()),
    },
{
    let mut graph = Vec::with_capacity(drivers.len());
    let mut i = 0;
    assert(driver_graph_prefix(drivers@, graph@)) by { reveal(driver_graph_prefix); };
    while i < drivers.len()
        invariant i == graph@.len() <= drivers@.len(), driver_graph_prefix(drivers@, graph@),
            valid_drivers_prefix(drivers@, inputs, gates, i as int),
        decreases drivers@.len() - i,
    {
        let target = match drivers[i] {
            ClockedWireDriver::Alias(target) => {
                if target >= drivers.len() { return Err(i); }
                Some(target)
            },
            ClockedWireDriver::Terminal(wire) => {
                if !wire_within(wire, inputs, gates) { return Err(i); }
                None
            },
        };
        let mut row = Vec::new();
        row.push(target);
        assert(row@ =~= seq![alias_target(drivers@[i as int])]);
        let ghost prior = graph@;
        graph.push(row);
        assert(driver_graph_prefix(drivers@, graph@)) by {
            reveal(driver_graph_prefix);
            assert forall|j: int| 0 <= j < graph@.len() implies
                (#[trigger] graph@[j])@ == seq![alias_target(drivers@[j])] by {
                if j < i { assert(graph@[j] == prior[j]); }
            };
        };
        i += 1;
    }
    reveal(driver_graph_prefix);
    assert forall|row: int, field: int| 0 <= row < graph@.len() && 0 <= field < graph@[row]@.len()
        implies ((#[trigger] graph@[row]@[field]) matches Some(target) ==> target < graph@.len()) by {
        assert(field == 0 && graph@[row]@[field] == alias_target(drivers@[row]));
    };
    Ok(graph)
}

spec fn driven_wire(driver: ClockedWireDriver, wires: Seq<Wire>) -> Wire {
    match driver {
        ClockedWireDriver::Terminal(wire) => wire,
        ClockedWireDriver::Alias(target) => wires[target as int],
    }
}

spec fn wire_rank(drivers: Seq<ClockedWireDriver>, rank: Seq<nat>) -> bool {
    &&& rank.len() == drivers.len()
    &&& forall|i: int| 0 <= i < drivers.len() ==>
        (alias_target(#[trigger] drivers[i]) matches Some(target) ==> target < drivers.len() && rank[target as int] < rank[i])
}

spec fn resolved_prefix(drivers: Seq<ClockedWireDriver>, rank: Seq<nat>, wires: Seq<Wire>, stop: int) -> bool {
    &&& wires.len() == drivers.len()
    &&& forall|i: int| 0 <= i < wires.len() && rank[i] < stop ==> #[trigger] wires[i] == driven_wire(drivers[i], wires)
}

/// 各終点の配線と、直結が指す配線が解決結果に保存されることを表す。
pub closed spec fn clocked_wires_match(drivers: Seq<ClockedWireDriver>, wires: Seq<Wire>) -> bool {
    &&& exists|rank: Seq<nat>| #[trigger] wire_rank(drivers, rank)
    &&& wires.len() == drivers.len()
    &&& forall|i: int| 0 <= i < wires.len() ==> #[trigger] wires[i] == driven_wire(drivers[i], wires)
}

/// 解決済みの一つの配線が、指定した終点か直結先の配線と一致することを示す。
pub proof fn clocked_wire_at(drivers: Seq<ClockedWireDriver>, wires: Seq<Wire>, i: int)
    requires clocked_wires_match(drivers, wires), 0 <= i < drivers.len(),
    ensures wires.len() == drivers.len(),
        match drivers[i] {
            ClockedWireDriver::Terminal(wire) => wires[i] == wire,
            ClockedWireDriver::Alias(target) => target < wires.len() && wires[i] == wires[target as int],
        },
{
    let rank = choose|rank: Seq<nat>| #[trigger] wire_rank(drivers, rank);
    assert(wire_rank(drivers, rank));
}

proof fn graph_gives_wire_rank(drivers: Seq<ClockedWireDriver>, graph: Seq<Vec<Option<usize>>>, rank: Seq<nat>)
    requires driver_graph_prefix(drivers, graph), graph.len() == drivers.len(), dependencies_in_order(graph, rank),
        dependency_graph_valid(graph), drivers.len() <= usize::MAX,
    ensures wire_rank(drivers, rank),
{
    reveal(driver_graph_prefix);
    assert forall|i: int| 0 <= i < drivers.len() implies
        (alias_target(#[trigger] drivers[i]) matches Some(target) ==> target < drivers.len() && rank[target as int] < rank[i]) by {
        if let Some(target) = alias_target(drivers[i]) {
            assert(graph[i]@.len() == 1);
            assert(graph[i]@[0] == Some(target));
            assert(target < graph.len());
            let node = i as usize;
            assert(node as int == i);
            assert(dependency_edge(graph, DependencyEdge { from: node, field: 0, to: target }));
        }
    };
}

fn resolve_driver_wires(drivers: &[ClockedWireDriver], _graph: &[Vec<Option<usize>>], order: &[usize], _inputs: usize, _gates: usize)
    -> (wires: Vec<Wire>)
    requires driver_graph_prefix(drivers@, _graph@), _graph@.len() == drivers@.len(), dependency_graph_valid(_graph@),
        complete_dependency_order(_graph@, order@), valid_drivers_prefix(drivers@, _inputs, _gates, drivers@.len() as int),
    ensures clocked_wires_match(drivers@, wires@),
        forall|i: int| 0 <= i < wires@.len() ==> wire_available(#[trigger] wires@[i], _inputs as nat, _gates as nat),
{
    let count = drivers.len();
    let ghost rank = choose|rank: Seq<nat>| #[trigger] dependencies_in_order(_graph@, rank)
        && completion_order_matches(order@, rank)
        && (forall|node: int| #![trigger rank[node]] 0 <= node < _graph@.len()
            ==> rank[node] < order@.len() && order@[rank[node] as int] == node);
    proof { graph_gives_wire_rank(drivers@, _graph@, rank); }
    let mut wires = vec![Wire::Constant(false); count];
    let mut i = 0;
    while i < order.len()
        invariant
            i <= order@.len() == drivers@.len() == wires@.len(),
            completion_order_matches(order@, rank), wire_rank(drivers@, rank),
            forall|node: int| #![trigger rank[node]] 0 <= node < drivers@.len()
                ==> rank[node] < order@.len() && order@[rank[node] as int] == node,
            valid_drivers_prefix(drivers@, _inputs, _gates, drivers@.len() as int),
            resolved_prefix(drivers@, rank, wires@, i as int),
            forall|j: int| 0 <= j < wires@.len() ==> wire_available(#[trigger] wires@[j], _inputs as nat, _gates as nat),
        decreases order@.len() - i,
    {
        let node = order[i];
        let wire = match drivers[node] {
            ClockedWireDriver::Terminal(wire) => wire,
            ClockedWireDriver::Alias(target) => wires[target],
        };
        assert(wire == driven_wire(drivers@[node as int], wires@));
        let ghost prior = wires@;
        wires.set(node, wire);
        assert forall|j: int| 0 <= j < wires@.len() implies
            wire_available(#[trigger] wires@[j], _inputs as nat, _gates as nat) by {
            if j != node { assert(wires@[j] == prior[j]); }
        };
        assert forall|j: int| 0 <= j < wires@.len() && rank[j] <= i implies
            #[trigger] wires@[j] == driven_wire(drivers@[j], wires@) by {
            if let ClockedWireDriver::Alias(target) = drivers@[j] {
                assert(rank[target as int] < rank[j]);
                assert(target != node && wires@[target as int] == prior[target as int]);
            }
            if j != node {
                assert(rank[j] != i && wires@[j] == prior[j]);
            }
        };
        i += 1;
    }
    assert(clocked_wires_match(drivers@, wires@));
    wires
}

/// 診断列の各位置が次の駆動元を参照し、最後の位置が先頭へ戻ることを表す。
pub closed spec fn clocked_wire_cycle(drivers: Seq<ClockedWireDriver>, cycle: Seq<usize>) -> bool {
    &&& cycle.len() > 0
    &&& forall|i: int| 0 <= i < cycle.len() ==> {
        let current = #[trigger] cycle[i];
        let next = if i + 1 == cycle.len() { cycle[0] } else { cycle[i + 1] };
        current < drivers.len() && drivers[current as int] == ClockedWireDriver::Alias(next)
    }
}

fn cycle_driver_positions(_drivers: &[ClockedWireDriver], _graph: &[Vec<Option<usize>>], edges: &[DependencyEdge])
    -> (positions: Vec<usize>)
    requires driver_graph_prefix(_drivers@, _graph@), _graph@.len() == _drivers@.len(), dependency_cycle(_graph@, edges@),
    ensures clocked_wire_cycle(_drivers@, positions@),
{
    let mut positions = Vec::with_capacity(edges.len());
    let mut i = 0;
    while i < edges.len()
        invariant i == positions@.len() <= edges@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] positions@[j]) == edges@[j].from,
        decreases edges@.len() - i,
    {
        let ghost prior = positions@;
        positions.push(edges[i].from);
        assert forall|j: int| 0 <= j < positions@.len() implies
            (#[trigger] positions@[j]) == edges@[j].from by {
            if j < i { assert(positions@[j] == prior[j]); }
        };
        i += 1;
    }
    reveal(driver_graph_prefix);
    assert forall|j: int| 0 <= j < positions@.len() implies {
        let current = #[trigger] positions@[j];
        let next = if j + 1 == positions@.len() { positions@[0] } else { positions@[j + 1] };
        current < _drivers@.len() && _drivers@[current as int] == ClockedWireDriver::Alias(next)
    } by {
        let edge = edges@[j];
        assert(dependency_edge(_graph@, edge));
        assert(_graph@[edge.from as int]@ == seq![alias_target(_drivers@[edge.from as int])]);
        assert(edge.field == 0);
        if j + 1 < edges@.len() { assert(edge.to == edges@[j + 1].from); }
    };
    positions
}

/// 予約区間と配線、または先に見つかった範囲外参照や直結の閉路を定める。
pub closed spec fn clocked_link_plan_result(
    counts: Seq<usize>, drivers: Seq<ClockedWireDriver>, inputs: usize, limit: usize,
    result: Result<ClockedLinkPlan, ClockedPlanError>,
) -> bool {
    let count = preceding_gates(counts, counts.len() as int);
    match result {
        Ok(plan) => plan.regions@.len() == counts.len() && region_prefix(counts, plan.regions@, limit)
            && plan.gate_count == count && count <= limit
            && clocked_wires_match(drivers, plan.wires@)
            && (forall|i: int| 0 <= i < plan.wires@.len() ==>
                wire_available(#[trigger] plan.wires@[i], inputs as nat, count)),
        Err(ClockedPlanError::GateCapacity(i)) => gate_capacity_at(counts, limit, i),
        Err(ClockedPlanError::Wire(i)) => count <= limit && i < drivers.len()
            && valid_drivers_prefix(drivers, inputs, count as usize, i as int)
            && !wire_valid(drivers[i as int], inputs, count as usize, drivers.len()),
        Err(ClockedPlanError::AliasCycle(cycle)) => count <= limit
            && valid_drivers_prefix(drivers, inputs, count as usize, drivers.len() as int)
            && clocked_wire_cycle(drivers, cycle@),
    }
}

/// 子回路の位置を予約し、指定した各ビットの駆動元を求める。
///
/// `counts` は子回路ごとのゲート数、`inputs` は親回路の入力ビット数、`limit` はゲート数の上限。
/// ゲート出力は予約後の番号で指定する。直結だけをたどるため、ゲートを経由するフィードバックを許す。
///
/// # Errors
///
/// 最初にゲートの上限、次に駆動元の範囲、最後に直結だけで閉じる循環を検査する。
pub fn plan_clocked_links(counts: &[usize], drivers: &[ClockedWireDriver], inputs: usize, limit: usize)
    -> (result: Result<ClockedLinkPlan, ClockedPlanError>)
    ensures
        clocked_link_plan_result(counts@, drivers@, inputs, limit, result),
        result matches Ok(plan) ==> clocked_regions_cover(counts@, plan.regions@, plan.gate_count)
            && plan.gate_count <= limit && plan.wires@.len() == drivers@.len()
            && clocked_wires_match(drivers@, plan.wires@)
            && (forall|i: int| 0 <= i < plan.wires@.len() ==>
                wire_available(#[trigger] plan.wires@[i], inputs as nat, plan.gate_count as nat)),
{
    let (regions, gate_count) = match reserve_regions(counts, limit) {
        Ok(plan) => plan,
        Err(i) => return Err(ClockedPlanError::GateCapacity(i)),
    };
    let graph = match build_driver_graph(drivers, inputs, gate_count) {
        Ok(graph) => graph,
        Err(i) => return Err(ClockedPlanError::Wire(i)),
    };
    let order = match check_dependency_order(graph.as_slice(), true) {
        Ok(order) => order,
        Err(edges) => return Err(ClockedPlanError::AliasCycle(cycle_driver_positions(drivers, graph.as_slice(), edges.as_slice()))),
    };
    let wires = resolve_driver_wires(drivers, graph.as_slice(), order.as_slice(), inputs, gate_count);
    proof { reserved_regions_cover(counts@, regions@, limit, gate_count); }
    Ok(ClockedLinkPlan { regions, gate_count, wires })
}

proof fn finite_wire_resolutions_agree(
    drivers: Seq<ClockedWireDriver>, rank: Seq<nat>, first: Seq<Wire>, second: Seq<Wire>, i: int,
)
    requires clocked_wires_match(drivers, first), clocked_wires_match(drivers, second),
        wire_rank(drivers, rank), 0 <= i < drivers.len(),
    ensures first[i] == second[i],
    decreases rank[i],
{
    assert(first[i] == driven_wire(drivers[i], first));
    assert(second[i] == driven_wire(drivers[i], second));
    if let ClockedWireDriver::Alias(target) = drivers[i] {
        finite_wire_resolutions_agree(drivers, rank, first, second, target as int);
    }
}

/// 直結が循環しないとき、どの順に解決しても同じ配線を得ることを示す。
pub proof fn clocked_wire_solutions_agree(drivers: Seq<ClockedWireDriver>, first: Seq<Wire>, second: Seq<Wire>)
    requires clocked_wires_match(drivers, first), clocked_wires_match(drivers, second),
    ensures first == second,
{
    let rank = choose|rank: Seq<nat>| #[trigger] wire_rank(drivers, rank);
    assert forall|i: int| 0 <= i < drivers.len() implies (#[trigger] first[i]) == second[i] by {
        finite_wire_resolutions_agree(drivers, rank, first, second, i);
    };
    assert(first =~= second);
}

} // verus!
