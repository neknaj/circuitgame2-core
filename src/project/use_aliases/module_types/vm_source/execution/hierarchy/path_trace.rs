//! 名前解決で得た呼び出し経路に沿って、有限トレースを射影する。

use super::{ClockedHierarchy, ClockedFunctionTemplate, ClockedModuleNetwork, ClockedModuleVm, ClockedModuleVmLimits,
    ModuleBodyPosition, UseAliases, routine_placed};
use super::placement_model::{RoutineWiring, placed_routine_evidence, sibling_routines_order};
use super::placement_model::trace::{RoutineFrame, frame_observed_from, frame_state_slice, join_frame_state_slices,
    join_vm_state_slices, nested_state_slice, nested_trace_projects, project_nested_trace, project_routine_trace,
    routine_trace, trace_frame_lengths, trace_projection_ready, update_input_read_from, vm_state_slice};
use crate::netlist::{ClockedVm, clocked_vm_trace};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 呼び出し番号を順にたどった先のモジュール。番号は各親のソース順である。
spec fn path_target(graph: Seq<Vec<Option<usize>>>, node: usize, path: Seq<usize>) -> Option<usize>
    decreases path.len(),
{
    if node >= graph.len() { None }
    else if path.len() == 0 { Some(node) }
    else if path[0] < graph[node as int]@.len() {
        match graph[node as int]@[path[0] as int] {
            Some(child) => path_target(graph, child, path.skip(1)),
            None => None,
        }
    } else { None }
}

/// 各段の配置を足し、経路末尾の位置を開始点からの添字で表す。
spec fn path_offsets(
    graph: Seq<Vec<Option<usize>>>, networks: Seq<Option<ClockedModuleNetwork>>, node: usize, path: Seq<usize>,
) -> (nat, nat)
    decreases path.len(),
{
    if path.len() == 0 || node >= graph.len() || node >= networks.len()
        || path[0] >= graph[node as int]@.len() { (0, 0) }
    else {
        let call = path[0] as int;
        match (graph[node as int]@[call], networks[node as int]) {
            (Some(child), Some(parent)) if parent._hierarchy_wiring@.is_some()
                && call < parent._hierarchy_wiring@->Some_0.routines.len()
                && parent._hierarchy_wiring@->Some_0.routines[call].is_some() => {
                let wiring = parent._hierarchy_wiring@->Some_0;
                let routine = wiring.routines[call]->Some_0;
                let tail = path_offsets(graph, networks, child, path.skip(1));
                ((routine.gates.start + tail.0) as nat,
                    (wiring.direct_devices + routine.storage.start + tail.1) as nat)
            },
            _ => (0, 0),
        }
    }
}

/// 経路が分岐する最初の位置で、先の呼び出しを選ぶ。
/// 一方が他方の接頭列である場合は、同じインスタンスの内外を指す。
spec fn paths_diverge_in_order(first: Seq<usize>, second: Seq<usize>) -> bool
    decreases first.len(),
{
    &&& first.len() > 0 && second.len() > 0
    &&& (first[0] < second[0]
        || (first[0] == second[0] && paths_diverge_in_order(first.skip(1), second.skip(1))))
}

/// 選ばれたインスタンスの状態は、開始モジュールのゲート列と状態素子列の部分列にある。
struct PathTrace {
    frames: Seq<RoutineFrame>,
    updates: Seq<Seq<bool>>,
    gates: nat,
    storage: nat,
    hops: Seq<TraceHop>,
}

struct TraceHop {
    node: usize,
    frames: Seq<RoutineFrame>,
    updates: Seq<Seq<bool>>,
}

spec fn edge_placement(parent: ClockedModuleNetwork, call: usize, routine: RoutineWiring) -> bool {
    let circuit = parent.circuit.netlist_model();
    &&& parent._hierarchy_wiring@ matches Some(wiring)
    &&& call < wiring.routines.len()
    &&& wiring.routines[call as int] == Some(routine)
    &&& wiring.direct_devices <= parent.storage@.len()
    &&& trace_projection_ready(&circuit, parent.inputs.total_bits_model(), parent.storage@,
        wiring.routines, wiring.direct_devices, wiring.first_child_input, call as int)
    &&& routine_placed(routine, circuit.gates@, parent.storage@.skip(wiring.direct_devices as int), circuit.input_count)
}

spec fn hop_projects(
    graph: Seq<Vec<Option<usize>>>, networks: Seq<Option<ClockedModuleNetwork>>, from: TraceHop, to: TraceHop, call: usize,
) -> bool {
    &&& from.node < graph.len() && from.node < networks.len()
    &&& call < graph[from.node as int]@.len()
    &&& graph[from.node as int]@[call as int] == Some(to.node)
    &&& networks[from.node as int] matches Some(parent)
    &&& parent._hierarchy_wiring@ matches Some(wiring)
    &&& call < wiring.routines.len()
    &&& wiring.routines[call as int] matches Some(routine)
    &&& nested_trace_projects(routine, wiring.direct_devices, from.frames, from.updates, to.frames, to.updates)
}

spec fn trace_follows_path(
    graph: Seq<Vec<Option<usize>>>, networks: Seq<Option<ClockedModuleNetwork>>, path: Seq<usize>,
    first: TraceHop, target: usize, result: PathTrace,
) -> bool {
    &&& result.hops.len() == path.len() + 1
    &&& result.hops[0] == first
    &&& result.hops.last().node == target
    &&& result.hops.last().frames == result.frames && result.hops.last().updates == result.updates
    &&& forall|i: int| 0 <= i < path.len() ==> hop_projects(graph, networks, #[trigger] result.hops[i],
        result.hops[i + 1], path[i])
}

spec fn trace_starts_in_vm(
    inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, routine: RoutineWiring, direct: usize,
    frames: Seq<RoutineFrame>, updates: Seq<Seq<bool>>,
) -> bool {
    &&& updates.len() == inputs.len()
    &&& frames.len() == inputs.len() + 1
    &&& frame_observed_from(&states[0], routine, direct,
        Seq::new(states[0].external_count() as nat, |_: int| false), frames[0])
    &&& forall|i: int| 0 < i < frames.len() ==> frame_observed_from(&states[i], routine, direct,
        inputs[i - 1], #[trigger] frames[i])
    &&& forall|i: int| 0 <= i < updates.len() ==> update_input_read_from(&states[i], routine,
        inputs[i], #[trigger] updates[i])
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    proof fn selected_trace_edge(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        end: int, networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
        node: usize, call: usize, child: usize,
    ) -> (routine: RoutineWiring)
        requires
            self.clocked_hierarchy_matches(root, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, end, networks, functions),
            node < networks.len(), node < hierarchy.rank@.len(), node < hierarchy.modules@.len(),
            hierarchy.rank@[node as int] < end,
            hierarchy.modules@[node as int].is_some(),
            call < hierarchy.graph@[node as int]@.len(),
            hierarchy.graph@[node as int]@[call as int] == Some(child),
        ensures
            child < networks.len(), hierarchy.rank@[child as int] < end,
            hierarchy.modules@[child as int].is_some(),
            networks[node as int].is_some() && networks[child as int].is_some(),
            edge_placement(networks[node as int]->Some_0, call, routine),
            ({
                let target = networks[child as int]->Some_0;
                &&& routine.callee == target.circuit.netlist_model()
                &&& routine.devices == target.storage@
                &&& routine.external.len() == target.inputs.total_bits_model()
            }),
    {
        reveal(UseAliases::hierarchy_templates_through);
        reveal(UseAliases::network_uses_selected_templates);
        reveal(UseAliases::hierarchy_public_wiring);
        self.clocked_hierarchy_evidence(root, limits.width, hierarchy);
        self.clocked_hierarchy_edge(root, limits.width, hierarchy, node as int, call as int);
        let parent = networks[node as int]->Some_0;
        let checked = hierarchy.modules@[node as int]->Some_0;
        let edges = hierarchy.graph@[node as int]@;
        let wiring = parent._hierarchy_wiring@->Some_0;
        assert(Self::network_uses_selected_templates(&checked, edges, networks, functions, &parent));
        let rank = hierarchy.rank@[node as int] as int;
        let child_rank = hierarchy.rank@[child as int] as int;
        assert(hierarchy.order@[rank] == node);
        assert(hierarchy.order@[child_rank] == child);
        assert(self.hierarchy_network_wiring(&checked, limits, &parent));
        assert(wiring.routines[call as int].is_some());
        let routine = wiring.routines[call as int]->Some_0;
        placed_routine_evidence(wiring.routines, parent.circuit.netlist_model().gates@,
            parent.storage@.skip(wiring.direct_devices as int), wiring.first_child_input,
            parent.circuit.netlist_model().input_count, call as int);
        assert(Self::routine_uses_selected_template(&checked, edges, networks, functions, call as int,
            routine.callee, routine.inputs, routine.layout, routine.devices));
        let target = networks[child as int]->Some_0;
        assert(self.hierarchy_network_wiring(&hierarchy.modules@[child as int]->Some_0, limits, &target));
        assert(edge_placement(parent, call, routine));
        routine
    }

    /// 各段で選ばれた子を証明に使い、末尾のインスタンスの区間を開始点からの添字に直す。
    proof fn project_resolved_path(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        end: int, networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
        node: usize, path: Seq<usize>, target: usize, frames: Seq<RoutineFrame>, updates: Seq<Seq<bool>>,
    ) -> (result: PathTrace)
        requires
            self.clocked_hierarchy_matches(root, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, end, networks, functions),
            node < networks.len(), node < hierarchy.rank@.len(), node < hierarchy.modules@.len(),
            hierarchy.rank@[node as int] < end,
            hierarchy.modules@[node as int].is_some(), networks[node as int].is_some(),
            path_target(hierarchy.graph@, node, path) == Some(target),
            ({
                let parent = networks[node as int]->Some_0;
                routine_trace(&parent.circuit.netlist_model(), parent.storage@, parent.inputs.total_bits_model() as nat,
                    frames, updates)
            }),
        ensures
            target < networks.len(), networks[target as int].is_some(),
            trace_follows_path(hierarchy.graph@, networks, path, TraceHop { node, frames, updates }, target, result),
            (result.gates, result.storage) == path_offsets(hierarchy.graph@, networks, node, path),
            result.frames.len() == frames.len(), result.updates.len() == updates.len(),
            ({
                let parent = networks[node as int]->Some_0;
                let leaf = networks[target as int]->Some_0;
                &&& routine_trace(&leaf.circuit.netlist_model(), leaf.storage@, leaf.inputs.total_bits_model() as nat,
                    result.frames, result.updates)
                &&& result.gates + leaf.circuit.netlist_model().gates@.len() <= parent.circuit.netlist_model().gates@.len()
                &&& result.storage + leaf.storage@.len() <= parent.storage@.len()
                &&& forall|i: int| 0 <= i < frames.len() ==> frame_state_slice(frames[i], #[trigger] result.frames[i],
                    result.gates, leaf.circuit.netlist_model().gates@.len(), result.storage, leaf.storage@.len())
            }),
        decreases path.len(),
    {
        self.clocked_hierarchy_evidence(root, limits.width, hierarchy);
        let first = TraceHop { node, frames, updates };
        let parent = networks[node as int]->Some_0;
        if path.len() == 0 {
            assert forall|i: int| 0 <= i < frames.len() implies frame_state_slice(
                #[trigger] frames[i], frames[i], 0, parent.circuit.netlist_model().gates@.len(), 0, parent.storage@.len()) by {
                trace_frame_lengths(&parent.circuit.netlist_model(), parent.storage@, parent.inputs.total_bits_model() as nat,
                    frames, updates, i);
                super::placement_model::trace::frame_identity_slice(frames[i]);
            };
            PathTrace { frames, updates, gates: 0, storage: 0, hops: seq![first] }
        } else {
            let call = path[0];
            let child = hierarchy.graph@[node as int]@[call as int]->Some_0;
            let routine = self.selected_trace_edge(root, limits, hierarchy, end, networks, functions, node, call, child);
            let wiring = parent._hierarchy_wiring@->Some_0;
            let (local, local_updates) = project_nested_trace(&parent.circuit.netlist_model(), parent.inputs.total_bits_model(),
                parent.storage@, wiring.routines, wiring.direct_devices, wiring.first_child_input, call as int, frames, updates);
            let suffix = self.project_resolved_path(root, limits, hierarchy, end, networks, functions, child, path.skip(1),
                target, local, local_updates);
            let hops = seq![first] + suffix.hops;
            let result = PathTrace {
                frames: suffix.frames, updates: suffix.updates, gates: (routine.gates.start + suffix.gates) as nat,
                storage: (wiring.direct_devices + routine.storage.start + suffix.storage) as nat,
                hops,
            };
            let child_network = networks[child as int]->Some_0;
            assert((result.gates, result.storage) == path_offsets(hierarchy.graph@, networks, node, path));
            assert(routine.gates.start + child_network.circuit.netlist_model().gates@.len() <= parent.circuit.netlist_model().gates@.len());
            assert(wiring.direct_devices + routine.storage.start + child_network.storage@.len() <= parent.storage@.len());
            let leaf = networks[target as int]->Some_0;
            assert forall|i: int| 0 <= i < frames.len() implies frame_state_slice(frames[i], #[trigger] result.frames[i],
                result.gates, leaf.circuit.netlist_model().gates@.len(), result.storage, leaf.storage@.len()) by {
                let netlist = parent.circuit.netlist_model();
                trace_frame_lengths(&netlist, parent.storage@, parent.inputs.total_bits_model() as nat, frames, updates, i);
                nested_state_slice(routine, wiring.direct_devices, frames, updates, local, local_updates, i,
                    netlist.gates@.len(), parent.storage@.len());
                join_frame_state_slices(frames[i], local[i], result.frames[i],
                    (routine.gates.start as nat, routine.callee.gates@.len(),
                        (wiring.direct_devices + routine.storage.start) as nat, routine.devices.len()),
                    (suffix.gates, leaf.circuit.netlist_model().gates@.len(), suffix.storage, leaf.storage@.len()));
            };
            assert forall|i: int| 0 <= i < path.len() implies hop_projects(hierarchy.graph@, networks,
                #[trigger] hops[i], hops[i + 1], path[i]) by {
                if i == 0 {
                    assert(hops[0] == first);
                    assert(hops[1] == suffix.hops[0]);
                    assert(suffix.hops[0] == (TraceHop { node: child, frames: local, updates: local_updates }));
                } else {
                    assert(hops[i] == suffix.hops[i - 1]);
                    assert(hops[i + 1] == suffix.hops[i]);
                    assert(path[i] == path.skip(1)[i - 1]);
                }
            };
            result
        }
    }

    /// 展開済みのルート VM から、ソースで指定した呼び出し経路の有限トレースを得る。
    proof fn project_resolved_vm_path(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        end: int, networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
        compiled: &ClockedModuleVm, path: Seq<usize>, target: usize,
        inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    ) -> (result: PathTrace)
        requires
            self.clocked_hierarchy_matches(root, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, end, networks, functions),
            0 < end, hierarchy.order@[end - 1] == 0,
            networks.len() > 0, networks[0].is_some(),
            hierarchy.modules@.len() > 0, hierarchy.modules@[0].is_some(),
            self.network_vm_on_reset(&networks[0]->Some_0, limits.state_bits, compiled),
            0 < path.len(), path_target(hierarchy.graph@, 0, path) == Some(target),
            clocked_vm_trace(inputs, states, outputs), states[0].same_layout(&compiled.vm),
        ensures
            target < networks.len(), networks[target as int].is_some(),
            result.frames.len() == states.len(), result.updates.len() == inputs.len(),
            (result.gates, result.storage) == path_offsets(hierarchy.graph@, networks, 0, path),
            ({
                let parent = networks[0]->Some_0;
                let leaf = networks[target as int]->Some_0;
                let first = hierarchy.graph@[0]@[path[0] as int]->Some_0;
                let wiring = parent._hierarchy_wiring@->Some_0;
                let routine = wiring.routines[path[0] as int]->Some_0;
                &&& routine_trace(&leaf.circuit.netlist_model(), leaf.storage@, leaf.inputs.total_bits_model() as nat,
                    result.frames, result.updates)
                &&& result.gates + leaf.circuit.netlist_model().gates@.len() <= parent.circuit.netlist_model().gates@.len()
                &&& result.storage + leaf.storage@.len() <= parent.storage@.len()
                &&& forall|i: int| 0 <= i < states.len() ==> vm_state_slice(&states[i], #[trigger] result.frames[i],
                    result.gates, leaf.circuit.netlist_model().gates@.len(), result.storage, leaf.storage@.len())
                &&& routine.gates.start <= result.gates
                &&& result.gates + leaf.circuit.netlist_model().gates@.len() <= routine.gates.end
                &&& wiring.direct_devices + routine.storage.start <= result.storage
                &&& result.storage + leaf.storage@.len() <= wiring.direct_devices + routine.storage.end
                &&& exists|first_frames: Seq<RoutineFrame>, first_updates: Seq<Seq<bool>>, suffix: PathTrace| {
                    &&& #[trigger] trace_starts_in_vm(inputs, states, routine, wiring.direct_devices, first_frames, first_updates)
                    &&& #[trigger] trace_follows_path(hierarchy.graph@, networks, path.skip(1),
                        TraceHop { node: first, frames: first_frames, updates: first_updates }, target, suffix)
                    &&& result.frames == suffix.frames && result.updates == suffix.updates
                    &&& result.gates == routine.gates.start + suffix.gates
                    &&& result.storage == wiring.direct_devices + routine.storage.start + suffix.storage
                    &&& result.hops == suffix.hops
                }
            }),
    {
        self.clocked_hierarchy_evidence(root, limits.width, hierarchy);
        let call = path[0];
        let child = hierarchy.graph@[0]@[call as int]->Some_0;
        let routine = self.selected_trace_edge(root, limits, hierarchy, end, networks, functions, 0, call, child);
        let parent = networks[0]->Some_0;
        let wiring = parent._hierarchy_wiring@->Some_0;
        let vm = states[0];
        vm.reset_snapshot(outputs[0]);
        vm.preserve_layout_evidence(&compiled.vm, parent.circuit.netlist_model(), parent.inputs.total_bits_model(), parent.storage@);
        let (frames, updates) = project_routine_trace(inputs, states, outputs, parent.storage@,
            wiring.routines, wiring.direct_devices, wiring.first_child_input, call as int, inputs.len());
        assert(trace_starts_in_vm(inputs, states, routine, wiring.direct_devices, frames, updates));
        let suffix = self.project_resolved_path(root, limits, hierarchy, end, networks, functions, child, path.skip(1),
            target, frames, updates);
        let result = PathTrace {
            frames: suffix.frames, updates: suffix.updates, gates: (routine.gates.start + suffix.gates) as nat,
            storage: (wiring.direct_devices + routine.storage.start + suffix.storage) as nat,
            hops: suffix.hops,
        };
        let child_network = networks[child as int]->Some_0;
        assert(routine.gates.start + child_network.circuit.netlist_model().gates@.len() <= parent.circuit.netlist_model().gates@.len());
        assert(wiring.direct_devices + routine.storage.start + child_network.storage@.len() <= parent.storage@.len());
        assert(trace_follows_path(hierarchy.graph@, networks, path.skip(1),
            TraceHop { node: child, frames, updates }, target, suffix));
        let leaf = networks[target as int]->Some_0;
        assert forall|i: int| 0 <= i < states.len() implies vm_state_slice(&states[i], #[trigger] result.frames[i],
            result.gates, leaf.circuit.netlist_model().gates@.len(), result.storage, leaf.storage@.len()) by {
            join_vm_state_slices(&states[i], frames[i], result.frames[i],
                (routine.gates.start as nat, routine.callee.gates@.len(),
                    (wiring.direct_devices + routine.storage.start) as nat, routine.devices.len()),
                (suffix.gates, leaf.circuit.netlist_model().gates@.len(), suffix.storage, leaf.storage@.len()));
        };
        result
    }

    /// 経路末尾の配置が、開始インスタンスと最初の子の区間内に収まる。
    proof fn resolved_path_bounds(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        end: int, networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
        node: usize, path: Seq<usize>, target: usize,
    )
        requires
            self.clocked_hierarchy_matches(root, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, end, networks, functions),
            node < networks.len(), node < hierarchy.rank@.len(), node < hierarchy.modules@.len(),
            hierarchy.rank@[node as int] < end,
            hierarchy.modules@[node as int].is_some(), networks[node as int].is_some(),
            path_target(hierarchy.graph@, node, path) == Some(target),
        ensures
            target < networks.len(), networks[target as int].is_some(),
            ({
                let parent = networks[node as int]->Some_0;
                let leaf = networks[target as int]->Some_0;
                let offset = path_offsets(hierarchy.graph@, networks, node, path);
                &&& offset.0 + leaf.circuit.netlist_model().gates@.len() <= parent.circuit.netlist_model().gates@.len()
                &&& offset.1 + leaf.storage@.len() <= parent.storage@.len()
                &&& path.len() > 0 ==> {
                    let wiring = parent._hierarchy_wiring@->Some_0;
                    let routine = wiring.routines[path[0] as int]->Some_0;
                    &&& routine.gates.start <= offset.0
                    &&& offset.0 + leaf.circuit.netlist_model().gates@.len() <= routine.gates.end
                    &&& wiring.direct_devices + routine.storage.start <= offset.1
                    &&& offset.1 + leaf.storage@.len() <= wiring.direct_devices + routine.storage.end
                }
            }),
        decreases path.len(),
    {
        self.clocked_hierarchy_evidence(root, limits.width, hierarchy);
        if path.len() > 0 {
            let call = path[0];
            let child = hierarchy.graph@[node as int]@[call as int]->Some_0;
            let routine = self.selected_trace_edge(root, limits, hierarchy, end, networks, functions, node, call, child);
            self.resolved_path_bounds(root, limits, hierarchy, end, networks, functions, child, path.skip(1), target);
            let parent = networks[node as int]->Some_0;
            let direct = parent._hierarchy_wiring@->Some_0.direct_devices;
            assert(direct + routine.storage.end <= parent.storage@.len());
        }
    }

    /// 分岐した二つの経路は、分岐までの共通の配置を足しても状態区間が重ならない。
    proof fn resolved_paths_separate(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        end: int, networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
        node: usize, first: Seq<usize>, second: Seq<usize>, first_target: usize, second_target: usize,
    )
        requires
            self.clocked_hierarchy_matches(root, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, end, networks, functions),
            node < networks.len(), node < hierarchy.rank@.len(), node < hierarchy.modules@.len(),
            hierarchy.rank@[node as int] < end,
            hierarchy.modules@[node as int].is_some(), networks[node as int].is_some(),
            paths_diverge_in_order(first, second),
            path_target(hierarchy.graph@, node, first) == Some(first_target),
            path_target(hierarchy.graph@, node, second) == Some(second_target),
        ensures
            first_target < networks.len(), networks[first_target as int].is_some(),
            second_target < networks.len(), networks[second_target as int].is_some(),
            ({
                let leaf = networks[first_target as int]->Some_0;
                let left = path_offsets(hierarchy.graph@, networks, node, first);
                let right = path_offsets(hierarchy.graph@, networks, node, second);
                &&& left.0 + leaf.circuit.netlist_model().gates@.len() <= right.0
                &&& left.1 + leaf.storage@.len() <= right.1
            }),
        decreases first.len(),
    {
        self.clocked_hierarchy_evidence(root, limits.width, hierarchy);
        let edges = hierarchy.graph@[node as int]@;
        let earlier = edges[first[0] as int]->Some_0;
        self.selected_trace_edge(root, limits, hierarchy, end, networks, functions, node, first[0], earlier);
        if first[0] == second[0] {
            self.resolved_paths_separate(root, limits, hierarchy, end, networks, functions, earlier,
                first.skip(1), second.skip(1), first_target, second_target);
        } else {
            let later = edges[second[0] as int]->Some_0;
            self.selected_trace_edge(root, limits, hierarchy, end, networks, functions, node, second[0], later);
            self.resolved_path_bounds(root, limits, hierarchy, end, networks, functions, node, first, first_target);
            self.resolved_path_bounds(root, limits, hierarchy, end, networks, functions, node, second, second_target);
            let parent = networks[node as int]->Some_0;
            let wiring = parent._hierarchy_wiring@->Some_0;
            let netlist = parent.circuit.netlist_model();
            sibling_routines_order(wiring.routines, netlist.gates@, parent.storage@.skip(wiring.direct_devices as int),
                wiring.first_child_input, netlist.input_count, first[0] as int, second[0] as int);
        }
    }

    /// 二つの経路の末尾は、同じ宣言を指す場合も分岐先ごとに別の状態区間を使う。
    proof fn project_separate_vm_paths(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        end: int, networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
        compiled: &ClockedModuleVm, first: Seq<usize>, second: Seq<usize>, first_target: usize, second_target: usize,
        inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    ) -> (result: (PathTrace, PathTrace))
        requires
            self.clocked_hierarchy_matches(root, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, end, networks, functions),
            0 < end, hierarchy.order@[end - 1] == 0,
            networks.len() > 0, networks[0].is_some(),
            hierarchy.modules@.len() > 0, hierarchy.modules@[0].is_some(),
            self.network_vm_on_reset(&networks[0]->Some_0, limits.state_bits, compiled),
            paths_diverge_in_order(first, second),
            path_target(hierarchy.graph@, 0, first) == Some(first_target),
            path_target(hierarchy.graph@, 0, second) == Some(second_target),
            clocked_vm_trace(inputs, states, outputs), states[0].same_layout(&compiled.vm),
        ensures
            ({
                let first_leaf = networks[first_target as int]->Some_0;
                let second_leaf = networks[second_target as int]->Some_0;
                &&& first_target < networks.len() && networks[first_target as int].is_some()
                &&& second_target < networks.len() && networks[second_target as int].is_some()
                &&& (result.0.gates, result.0.storage) == path_offsets(hierarchy.graph@, networks, 0, first)
                &&& (result.1.gates, result.1.storage) == path_offsets(hierarchy.graph@, networks, 0, second)
                &&& result.0.gates + first_leaf.circuit.netlist_model().gates@.len() <= result.1.gates
                &&& result.0.storage + first_leaf.storage@.len() <= result.1.storage
                &&& result.0.frames.len() == result.1.frames.len() == states.len()
                &&& forall|i: int| 0 <= i < states.len() ==> {
                    &&& vm_state_slice(&states[i], #[trigger] result.0.frames[i], result.0.gates,
                        first_leaf.circuit.netlist_model().gates@.len(), result.0.storage, first_leaf.storage@.len())
                    &&& vm_state_slice(&states[i], #[trigger] result.1.frames[i], result.1.gates,
                        second_leaf.circuit.netlist_model().gates@.len(), result.1.storage, second_leaf.storage@.len())
                }
            }),
    {
        let earlier = self.project_resolved_vm_path(root, limits, hierarchy, end, networks, functions, compiled,
            first, first_target, inputs, states, outputs);
        let later = self.project_resolved_vm_path(root, limits, hierarchy, end, networks, functions, compiled,
            second, second_target, inputs, states, outputs);
        self.clocked_hierarchy_evidence(root, limits.width, hierarchy);
        self.resolved_paths_separate(root, limits, hierarchy, end, networks, functions, 0, first, second,
            first_target, second_target);
        (earlier, later)
    }
}

} // verus!
