//! 名前解決で得た呼び出し経路に沿って、有限トレースを射影する。

use super::{ClockedHierarchy, ClockedFunctionTemplate, ClockedModuleNetwork, ClockedModuleVm, ClockedModuleVmLimits,
    ModuleBodyPosition, UseAliases, routine_placed};
use super::placement_model::{RoutineWiring, placed_routine_evidence, sibling_routines_order};
use super::placement_model::trace::{RoutineFrame, frame_observed_from, frame_output_count, frame_outputs, frame_state_slice, join_frame_state_slices,
    join_vm_state_slices, nested_state_slice, nested_trace_projects, project_nested_trace, project_routine_trace,
    routine_trace, trace_frame_lengths, trace_projection_ready, update_input_read_from, vm_state_slice, vm_state_slice_bounds};
use crate::netlist::{ClockedVm, clocked_vm_trace};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

verus! {

/// 名前解決済みの呼び出し一件の観測を表す。
pub struct ClockedModuleObservation {
    /// 呼び出し先モジュールの宣言位置。
    pub declaration: ModuleBodyPosition,
    /// ルート VM におけるゲートの半開区間。
    pub gates: Range<usize>,
    /// ルート VM におけるラッチと RAM の半開区間。
    pub storage: Range<usize>,
    /// reset 直後と各 tick 後の公開出力。先頭は reset の観測。
    pub outputs: Seq<Seq<bool>>,
}

impl ClockedModuleObservation {
    /// 観測件数が状態列と一致し、すべての状態で各区間が範囲内にある。
    pub open spec fn fits_trace(&self, states: Seq<ClockedVm>) -> bool {
        &&& self.outputs.len() == states.len()
        &&& forall|i: int| 0 <= i < states.len() ==> {
            let state = #[trigger] states[i];
            &&& self.gates.start <= self.gates.end <= state.gate_values_model().len()
            &&& self.storage.start <= self.storage.end <= state.storage_model().len()
        }
    }
}

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

spec fn vm_path_projection(
    graph: Seq<Vec<Option<usize>>>, networks: Seq<Option<ClockedModuleNetwork>>, path: Seq<usize>, target: usize,
    inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, result: PathTrace,
) -> bool {
    let parent = networks[0]->Some_0;
    let leaf = networks[target as int]->Some_0;
    let first = graph[0]@[path[0] as int]->Some_0;
    let wiring = parent._hierarchy_wiring@->Some_0;
    let routine = wiring.routines[path[0] as int]->Some_0;
    &&& result.frames.len() == states.len() && result.updates.len() == inputs.len()
    &&& (result.gates, result.storage) == path_offsets(graph, networks, 0, path)
    &&& routine_trace(&leaf.circuit.netlist_model(), leaf.storage@, leaf.inputs.total_bits_model() as nat,
        result.frames, result.updates)
    &&& result.gates + leaf.circuit.netlist_model().gates@.len() <= parent.circuit.netlist_model().gates@.len()
    &&& result.storage + leaf.storage@.len() <= parent.storage@.len()
    &&& forall|i: int| 0 <= i < states.len() ==> vm_state_slice(&states[i], #[trigger] result.frames[i],
        result.gates, leaf.circuit.netlist_model().gates@.len(), result.storage, leaf.storage@.len())
    &&& exists|frames: Seq<RoutineFrame>, updates: Seq<Seq<bool>>, suffix: PathTrace| {
        &&& #[trigger] trace_starts_in_vm(inputs, states, routine, wiring.direct_devices, frames, updates)
        &&& #[trigger] trace_follows_path(graph, networks, path.skip(1), TraceHop { node: first, frames, updates },
            target, suffix)
        &&& result.frames == suffix.frames && result.updates == suffix.updates && result.hops == suffix.hops
        &&& result.gates == routine.gates.start + suffix.gates
        &&& result.storage == wiring.direct_devices + routine.storage.start + suffix.storage
    }
}

spec fn public_observation_matches(
    hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>, path: Seq<usize>,
    inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, result: Option<ClockedModuleObservation>,
) -> bool {
    match result {
        None => path.len() == 0 || path_target(hierarchy.graph@, 0, path).is_none(),
        Some(observed) => {
            &&& path.len() > 0
            &&& path_target(hierarchy.graph@, 0, path) matches Some(target)
            &&& target < hierarchy.positions@.len() && target < networks.len()
            &&& networks[target as int] matches Some(network)
            &&& observed.declaration == hierarchy.positions@[target as int]
            &&& observed.gates.start + network.circuit.netlist_model().gates@.len() == observed.gates.end
            &&& observed.storage.start + network.storage@.len() == observed.storage.end
            &&& observed.outputs.len() == states.len()
            &&& exists|trace: PathTrace| #[trigger]
                vm_path_projection(hierarchy.graph@, networks, path, target, inputs, states, trace)
                && observed.gates.start == trace.gates && observed.storage.start == trace.storage
                && observed.outputs == frame_outputs(trace.frames)
        },
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 二つの経路が分岐し、最初に異なる呼び出しでは `first` がソース順で先にある。
    ///
    /// 一方が他方の接頭列である場合は、同じインスタンスの内外を指すため成立しない。
    pub open spec fn clocked_module_paths_in_order(first: Seq<usize>, second: Seq<usize>) -> bool
        decreases first.len(),
    {
        &&& first.len() > 0 && second.len() > 0
        &&& (first[0] < second[0]
            || (first[0] == second[0] && Self::clocked_module_paths_in_order(first.skip(1), second.skip(1))))
    }

    /// 同じコンパイル結果と VM 実行に対する二つの呼び出しの観測を表す。
    pub closed spec fn clocked_module_observations_match(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        first: Seq<usize>, second: Seq<usize>, inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>,
        result: (Option<ClockedModuleObservation>, Option<ClockedModuleObservation>),
    ) -> bool {
        exists|hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
            functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int|
            #[trigger] self.hierarchy_compilation_snapshot(root, limits, compiled, hierarchy, networks, functions, end)
            && public_observation_matches(hierarchy, networks, first, inputs, states, result.0)
            && public_observation_matches(hierarchy, networks, second, inputs, states, result.1)
    }

    /// reset と有限個の入力から、二つのモジュール呼び出しの公開出力と状態区間を得る。
    ///
    /// 経路の各番号は、その親にある検査済みの呼び出し一覧の添字。空の経路や、途中でモジュールの
    /// 呼び出しをたどれない経路には `None` を返す。結果が二つあり、経路が分岐順なら区間は重ならない。
    pub proof fn observe_clocked_module_paths(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        first: Seq<usize>, second: Seq<usize>, inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    ) -> (result: (Option<ClockedModuleObservation>, Option<ClockedModuleObservation>))
        requires self.clocked_module_hierarchy_vm(root, limits, compiled),
            clocked_vm_trace(inputs, states, outputs), states[0].same_layout(&compiled.vm),
        ensures self.clocked_module_observations_match(root, limits, compiled, first, second, inputs, states, result),
            first.len() == 0 ==> result.0.is_none(),
            second.len() == 0 ==> result.1.is_none(),
            result.0 matches Some(left) ==> left.fits_trace(states),
            result.1 matches Some(right) ==> right.fits_trace(states),
            result matches (Some(left), Some(right)) ==> Self::clocked_module_paths_in_order(first, second) ==>
                left.gates.end <= right.gates.start && left.storage.end <= right.storage.start,
    {
        let (hierarchy, networks, functions, end) = choose|hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
            functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int|
                #[trigger] self.hierarchy_compilation_snapshot(root, limits, compiled, hierarchy, networks, functions, end);
        let left = self.observe_compiled_path(root, limits, compiled, hierarchy, networks, functions, end,
            first, inputs, states, outputs);
        let right = self.observe_compiled_path(root, limits, compiled, hierarchy, networks, functions, end,
            second, inputs, states, outputs);
        if Self::clocked_module_paths_in_order(first, second) && left.is_some() && right.is_some() {
            self.clocked_hierarchy_evidence(root, limits.width, &hierarchy);
            let earlier = path_target(hierarchy.graph@, 0, first)->Some_0;
            let later = path_target(hierarchy.graph@, 0, second)->Some_0;
            self.resolved_paths_separate(root, limits, &hierarchy, end, networks, functions, 0, first, second, earlier, later);
        }
        (left, right)
    }

    proof fn observe_compiled_path(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
        functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int,
        path: Seq<usize>, inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    ) -> (result: Option<ClockedModuleObservation>)
        requires self.hierarchy_compilation_snapshot(root, limits, compiled, hierarchy, networks, functions, end),
            clocked_vm_trace(inputs, states, outputs), states[0].same_layout(&compiled.vm),
        ensures public_observation_matches(hierarchy, networks, path, inputs, states, result),
            path.len() == 0 ==> result.is_none(),
            result matches Some(observed) ==> {
                &&& observed.fits_trace(states)
                &&& path_target(hierarchy.graph@, 0, path) matches Some(target)
                &&& networks[target as int] matches Some(network)
                &&& observed.gates.start + network.circuit.netlist_model().gates@.len() == observed.gates.end
                &&& observed.storage.start + network.storage@.len() == observed.storage.end
                &&& observed.gates.start == path_offsets(hierarchy.graph@, networks, 0, path).0
                &&& observed.storage.start == path_offsets(hierarchy.graph@, networks, 0, path).1
            },
    {
        if path.len() == 0 { return None; }
        let resolved = path_target(hierarchy.graph@, 0, path);
        if resolved.is_none() { return None; }
        let target = resolved->Some_0;
        let trace = self.project_resolved_vm_path(root, limits, &hierarchy, end, networks, functions, compiled,
            path, target, inputs, states, outputs);
        self.clocked_hierarchy_evidence(root, limits.width, &hierarchy);
        reveal(UseAliases::hierarchy_templates_through);
        assert(target < hierarchy.positions@.len());
        frame_output_count(trace.frames);
        let parent = networks[0]->Some_0;
        let leaf = networks[target as int]->Some_0;
        let parent_netlist = parent.circuit.netlist_model();
        vstd::std_specs::vec::axiom_spec_len(&parent_netlist.gates);
        vstd::std_specs::vec::axiom_spec_len(&parent.storage);
        let observed = ClockedModuleObservation {
            declaration: hierarchy.positions@[target as int],
            gates: Range { start: trace.gates as usize, end: (trace.gates + leaf.circuit.netlist_model().gates@.len()) as usize },
            storage: Range { start: trace.storage as usize, end: (trace.storage + leaf.storage@.len()) as usize },
            outputs: frame_outputs(trace.frames),
        };
        assert(observed.fits_trace(states)) by {
            assert forall|i: int| 0 <= i < states.len() implies {
                let state = #[trigger] states[i];
                &&& observed.gates.start <= observed.gates.end <= state.gate_values_model().len()
                &&& observed.storage.start <= observed.storage.end <= state.storage_model().len()
            } by {
                vm_state_slice_bounds(&states[i], trace.frames[i], trace.gates, leaf.circuit.netlist_model().gates@.len(),
                    trace.storage, leaf.storage@.len());
            };
        };
        assert(public_observation_matches(hierarchy, networks, path, inputs, states, Some(observed))) by {
            assert(vm_path_projection(hierarchy.graph@, networks, path, target, inputs, states, trace));
        };
        Some(observed)
    }

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
            vm_path_projection(hierarchy.graph@, networks, path, target, inputs, states, result),
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
            Self::clocked_module_paths_in_order(first, second),
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


}

} // verus!
