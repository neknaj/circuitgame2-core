//! 子を先に展開し、各呼び出しに独立したゲートと状態出力の区間を割り当てる。

mod placement_model;
#[cfg(verus_only)]
mod path_trace;
#[cfg(verus_only)]
mod source_ids;
#[cfg(verus_only)]
mod source_placement;
#[cfg(verus_only)]
pub use path_trace::ClockedModuleObservation;

use placement_model::RoutineWiring;
#[cfg(verus_only)]
use placement_model::{empty_routine_pins, empty_routines, extend_routine_pins, extend_routines,
    join_routine_input_offsets, routine_pins_valid, routine_placed, routine_vm_input_offsets,
    routines_output_width, routines_pins_valid, routines_placed};
use super::super::super::{ClockedModuleOutputs, ClockedStorageLayout, ClockedStorageLayoutError, ClockedStoragePlacement,
    ClockedWireDriver, copy_location};
#[cfg(verus_only)]
use super::super::super::clocked_source::ClockedHierarchy;
use super::super::super::clocked_source::function_templates::FunctionTemplates;
#[cfg(verus_only)]
use super::super::super::clocked_source::function_templates::{function_cache_extends, function_target, function_templates_cover};
#[cfg(verus_only)]
use crate::project::use_aliases::bit_func::ClockedFunctionTemplate;
use super::super::{ClockedEndpointError, ClockedPlanError, clocked_resolve};
use super::{ClockedModuleNetwork, ClockedModuleVm, ClockedModuleVmError, ClockedModuleVmLimits,
    ModuleBodyPosition, ModuleCalls, ResolveRowError, ResolveRowsError, UseAliases, append_row, resolve_rows};
#[cfg(verus_only)]
use super::row_model;
#[cfg(verus_only)]
use super::child_outputs::{child_port_drivers_match, child_port_resolves_to_instance};
#[cfg(verus_only)]
use super::resolved_bits;
#[cfg(verus_only)]
use super::super::super::clocked_source::resolved_driver;
#[cfg(verus_only)]
use super::super::super::clocked_plan::{clocked_cycle_edge, clocked_wire_at, clocked_wire_cycle, clocked_wires_match};
use crate::netlist::{ClockedNor, ClockedStatefulInstanceError, ClockedStorageInputs, NorGate, NorNetlist, PortBitLayout, Wire};
#[cfg(verus_only)]
use crate::netlist::{clocked_stateful_arguments, clocked_storage_output_width, clocked_storage_width_concat,
    instance_outputs_match};
use crate::project::{LocatedName, ModuleCallTarget};
use alloc::{boxed::Box, vec::Vec};
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::laws_cmp::obeys_cmp;

verus! {

/// 呼び出しごとの配置と、親の定義を組み立てる前に求めた実引数。
struct CallPlacement<'s, 'p, 'a> {
    circuit: &'s ClockedNor,
    inputs: &'s PortBitLayout,
    outputs: &'s PortBitLayout,
    storage: &'s [ClockedStorageInputs],
    storage_sites: &'s [ClockedStoragePlacement<'p, 'a>],
    gates: Range<usize>,
    states: Range<usize>,
    arguments: Vec<ClockedWireDriver>,
    _argument_rows: Ghost<Vec<Vec<ClockedWireDriver>>>,
}

/// 記号配線を作った局所式か呼び出しを示す、証明用の根拠。
enum HierarchyRowOrigin {
    Local(Vec<ClockedWireDriver>),
    Call(usize),
}

/// ビット順の記号配線と、定義ごとの配線の出所。
struct HierarchyRows {
    bits: Vec<ClockedWireDriver>,
    _origins: Ghost<Seq<HierarchyRowOrigin>>,
}

/// 直接呼び出した素子が占めるゲート番号または状態素子の添字。
enum PrimitivePlacement {
    Nor(usize),
    Storage(usize),
}

/// 型検査済みの実引数と、親回路でその値を受け取る配線。
struct PrimitiveWiring {
    placement: PrimitivePlacement,
    rows: Vec<Vec<ClockedWireDriver>>,
    arguments: Seq<Wire>,
    outputs: Seq<Wire>,
}

/// 呼び出し境界までに配置したゲート、直接素子、子回路内の状態素子の数。
struct CallBoundary {
    gates: nat,
    direct: nat,
    child: nat,
}

/// 所有する呼び出しを探す配列。子の状態素子番号は直接素子の直後を起点とする。
enum PartitionArea {
    Gate,
    DirectStorage,
    ChildStorage,
}

spec fn boundary_position(boundary: CallBoundary, area: PartitionArea) -> nat {
    match area {
        PartitionArea::Gate => boundary.gates,
        PartitionArea::DirectStorage => boundary.direct,
        PartitionArea::ChildStorage => boundary.child,
    }
}

spec fn call_interval_matches(
    first: CallBoundary, last: CallBoundary, routine: Option<RoutineWiring>, primitive: Option<PrimitiveWiring>,
) -> bool {
    match (routine, primitive) {
        (Some(item), None) => {
            &&& item.gates.start == first.gates && item.gates.end == last.gates
            &&& first.gates <= last.gates
            &&& item.storage.start == first.child && item.storage.end == last.child
            &&& first.child <= last.child
            &&& first.direct == last.direct
        },
        (None, Some(item)) => match item.placement {
            PrimitivePlacement::Nor(gate) => gate == first.gates && last.gates == first.gates + 1
                && last.direct == first.direct && last.child == first.child,
            PrimitivePlacement::Storage(index) => index == first.direct && last.direct == first.direct + 1
                && last.gates == first.gates && last.child == first.child,
        },
        _ => false,
    }
}

/// 各配列を、先頭から末尾までソース上の呼び出し順に区切る。
#[verifier::opaque]
spec fn call_partition_matches(
    boundaries: Seq<CallBoundary>, routines: Seq<Option<RoutineWiring>>,
    primitives: Seq<Option<PrimitiveWiring>>, end: CallBoundary,
) -> bool {
    &&& boundaries.len() == routines.len() + 1
    &&& routines.len() == primitives.len()
    &&& boundaries[0] == (CallBoundary { gates: 0, direct: 0, child: 0 })
    &&& boundaries.last() == end
    &&& forall|i: int| 0 <= i < routines.len() ==>
        call_interval_matches(boundaries[i], boundaries[i + 1], #[trigger] routines[i], primitives[i])
}

proof fn extend_call_partition(
    boundaries: Seq<CallBoundary>, routines: Seq<Option<RoutineWiring>>,
    primitives: Seq<Option<PrimitiveWiring>>, before: CallBoundary, after: CallBoundary,
    routine: Option<RoutineWiring>, primitive: Option<PrimitiveWiring>,
)
    requires
        call_partition_matches(boundaries, routines, primitives, before),
        call_interval_matches(before, after, routine, primitive),
    ensures call_partition_matches(boundaries.push(after), routines.push(routine), primitives.push(primitive), after),
{
    reveal(call_partition_matches);
    let following = boundaries.push(after);
    let new_routines = routines.push(routine);
    let new_primitives = primitives.push(primitive);
    assert forall|i: int| 0 <= i < new_routines.len() implies
        call_interval_matches(following[i], following[i + 1], #[trigger] new_routines[i], new_primitives[i]) by {
        if i < routines.len() {
            assert(new_routines[i] == routines[i] && new_primitives[i] == primitives[i]);
            assert(following[i] == boundaries[i] && following[i + 1] == boundaries[i + 1]);
        } else {
            assert(following[i] == before);
        }
    };
}

proof fn partition_boundary_order(
    boundaries: Seq<CallBoundary>, routines: Seq<Option<RoutineWiring>>,
    primitives: Seq<Option<PrimitiveWiring>>, area: PartitionArea, start: int, end: int,
)
    requires 0 <= start <= end < boundaries.len(),
        call_partition_matches(boundaries, routines, primitives, boundaries.last()),
    ensures boundary_position(boundaries[start], area) <= boundary_position(boundaries[end], area),
    decreases end - start,
{
    reveal(call_partition_matches);
    if start < end {
        let previous = end - 1;
        assert(previous < routines.len());
        assert(call_interval_matches(boundaries[previous], boundaries[previous + 1], routines[previous], primitives[previous]));
        assert(boundary_position(boundaries[previous], area) <= boundary_position(boundaries[end], area));
        partition_boundary_order(boundaries, routines, primitives, area, start, previous);
    }
}

/// 実配列の添字は、空でないただ一つの呼び出し区間に属する。
proof fn partition_owner(
    boundaries: Seq<CallBoundary>, routines: Seq<Option<RoutineWiring>>,
    primitives: Seq<Option<PrimitiveWiring>>, area: PartitionArea, index: nat, end: int,
) -> (call: int)
    requires 0 <= end < boundaries.len(),
        call_partition_matches(boundaries, routines, primitives, boundaries.last()),
        index < boundary_position(boundaries[end], area),
    ensures 0 <= call < end,
        boundary_position(boundaries[call], area) <= index < boundary_position(boundaries[call + 1], area),
        forall|i: int| 0 <= i < routines.len() && i != call ==>
            #[trigger] boundary_position(boundaries[i + 1], area) <= index
                || index < #[trigger] boundary_position(boundaries[i], area),
        call_interval_matches(boundaries[call], boundaries[call + 1], routines[call], primitives[call]),
    decreases end,
{
    reveal(call_partition_matches);
    assert(end > 0);
    if index < boundary_position(boundaries[end - 1], area) {
        partition_owner(boundaries, routines, primitives, area, index, end - 1)
    } else {
        let call = end - 1;
        assert forall|i: int| 0 <= i < routines.len() && i != call implies
            #[trigger] boundary_position(boundaries[i + 1], area) <= index
                || index < #[trigger] boundary_position(boundaries[i], area) by {
            if i < call {
                partition_boundary_order(boundaries, routines, primitives, area, i + 1, call);
            } else {
                partition_boundary_order(boundaries, routines, primitives, area, call + 1, i);
            }
        };
        call
    }
}

/// 親の定義と公開ポートが参照する配線、および各呼び出しの移設済み出力。
pub(super) struct HierarchyWiring {
    definitions: Seq<Wire>,
    origins: Seq<HierarchyRowOrigin>,
    routines: Seq<Option<RoutineWiring>>,
    primitives: Seq<Option<PrimitiveWiring>>,
    boundaries: Seq<CallBoundary>,
    direct_devices: usize,
    first_child_input: usize,
}

fn call_site<'p, 'a>(checked: &ModuleCalls<'p, 'a>, call: usize) -> (site: LocatedName<'p, 'a>)
    requires call < checked.calls@.len(),
    ensures site.source == checked.calls@[call as int].inputs.ports.signature.source
        && site.span == checked.calls@[call as int].inputs.ports.signature.call.span,
{
    let signature = &checked.calls[call].inputs.ports.signature;
    LocatedName { source: signature.source, span: signature.call.span.start..signature.call.span.end }
}

/// 呼び出しの手前までに配置するゲートの数。
#[verifier::opaque]
spec fn gate_cursor(checked: &ModuleCalls, calls: Seq<Option<CallPlacement>>, count: nat) -> nat
    decreases count,
{
    if count == 0 || count > calls.len() { 0 } else {
        let i = (count - 1) as int;
        if let Some(child) = calls[i] { child.gates.end as nat }
        else if checked.calls@[i].inputs.ports.signature.target is Nor { gate_cursor(checked, calls, i as nat) + 1 }
        else { gate_cursor(checked, calls, i as nat) }
    }
}

spec fn storage_outputs(range: Range<usize>) -> Seq<Wire> {
    Seq::new((range.end - range.start) as nat, |i: int| Wire::Input((range.start + i) as usize))
}

proof fn gate_cursor_zero(checked: &ModuleCalls, calls: Seq<Option<CallPlacement>>)
    ensures gate_cursor(checked, calls, 0) == 0,
{
    reveal(gate_cursor);
}

proof fn gate_cursor_next(checked: &ModuleCalls, calls: Seq<Option<CallPlacement>>, call: nat)
    requires call < calls.len() == checked.calls@.len(),
    ensures gate_cursor(checked, calls, call + 1) == if let Some(child) = calls[call as int] { child.gates.end as nat }
        else if checked.calls@[call as int].inputs.ports.signature.target is Nor { gate_cursor(checked, calls, call) + 1 }
        else { gate_cursor(checked, calls, call) },
{
    reveal(gate_cursor);
}

spec fn primitive_symbolic_row(
    checked: &ModuleCalls, ports: &ClockedModuleOutputs, calls: Seq<Option<CallPlacement>>,
    direct: &ClockedStorageLayout, bits: Seq<ClockedWireDriver>, slot: int, origin: HierarchyRowOrigin,
) -> bool {
    match origin {
        HierarchyRowOrigin::Call(call) if calls[call as int].is_none() => {
            let range = ports.definitions.ranges_model()[slot];
            let row = bits.subrange(range.start as int, range.end as int);
            if checked.calls@[call as int].inputs.ports.signature.target is Nor {
                row == seq![ClockedWireDriver::Terminal(Wire::Gate(gate_cursor(checked, calls, call as nat) as usize))]
            } else {
                &&& direct.by_call@[call as int] matches Some(index)
                &&& index < direct.instances@.len()
                &&& row == storage_outputs(direct.instances@[index as int].outputs)
                    .map_values(|wire: Wire| ClockedWireDriver::Terminal(wire))
            }
        },
        _ => true,
    }
}

spec fn primitive_follows_plan(
    checked: &ModuleCalls, calls: Seq<Option<CallPlacement>>, direct: &ClockedStorageLayout,
    call: int, primitive: Option<PrimitiveWiring>,
) -> bool {
    match primitive {
        None => calls[call].is_some(),
        Some(item) => calls[call].is_none() && match item.placement {
            PrimitivePlacement::Nor(gate) => gate == gate_cursor(checked, calls, call as nat),
            PrimitivePlacement::Storage(index) => direct.by_call@[call] == Some(index),
        },
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) fn has_clocked_routine_call(&self, checked: &ModuleCalls<'p, 'a>) -> (found: bool)
        ensures found == (exists|i: int| 0 <= i < checked.calls@.len()
            && (#[trigger] checked.calls@[i]).inputs.ports.signature.target is Routine),
    {
        let mut i = 0;
        while i < checked.calls.len()
            invariant i <= checked.calls@.len(), forall|j: int| 0 <= j < i ==>
                !((#[trigger] checked.calls@[j]).inputs.ports.signature.target is Routine),
            decreases checked.calls@.len() - i,
        {
            if matches!(checked.calls[i].inputs.ports.signature.target, ModuleCallTarget::Routine { .. }) {
                return true;
            }
            i += 1;
        }
        false
    }

    spec fn hierarchy_network_wiring(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
    ) -> bool {
        exists|ports: ClockedModuleOutputs|
            #[trigger] self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(ports))
            && network.inputs == ports.inputs && network.outputs == ports.outputs
            && network.inputs.total_bits_model() + clocked_storage_output_width(network.storage@)
                == network.circuit.netlist_model().input_count
            && (network._hierarchy_wiring@ matches Some(wiring)
                && self.hierarchy_public_wiring(checked, limits.width, &ports, &wiring, network.circuit.netlist_model().outputs@)
                && self.hierarchy_primitives_bound(checked, limits.width, &ports, wiring.definitions,
                    wiring.primitives, network.circuit.netlist_model().gates@,
                    network.storage@.take(wiring.direct_devices as int), network.storage_sites@.take(wiring.direct_devices as int))
                && wiring.primitives.len() == checked.calls@.len()
                && wiring.direct_devices <= network.storage@.len()
                && routines_pins_valid(wiring.routines, network.circuit.netlist_model().input_count,
                    network.circuit.netlist_model().gates@.len())
                && call_partition_matches(wiring.boundaries, wiring.routines, wiring.primitives, CallBoundary {
                    gates: network.circuit.netlist_model().gates@.len(),
                    direct: wiring.direct_devices as nat,
                    child: (network.storage@.len() - wiring.direct_devices) as nat,
                })
                && routine_vm_input_offsets(wiring.routines, network.storage@, wiring.direct_devices,
                    network.inputs.total_bits_model())
                && routines_placed(wiring.routines, network.circuit.netlist_model().gates@,
                    network.storage@.skip(wiring.direct_devices as int), wiring.first_child_input,
                    network.circuit.netlist_model().input_count))
    }

    spec fn hierarchy_primitive_bound(
        &self, checked: &ModuleCalls, width: u64, ports: &ClockedModuleOutputs, definitions: Seq<Wire>,
        call: int, primitive: Option<PrimitiveWiring>, gates: Seq<NorGate>,
        storage: Seq<ClockedStorageInputs>, sites: Seq<ClockedStoragePlacement>,
    ) -> bool {
        let target = checked.calls@[call].inputs.ports.signature.target;
        match primitive {
            None => target is Routine,
            Some(item) => {
                &&& self.call_wires_result(checked, width, ports, call as usize, Ok(item.rows))
                &&& resolved_bits(row_model(item.rows@), definitions, item.arguments)
                &&& match item.placement {
                    PrimitivePlacement::Nor(gate) => target is Nor && gate < gates.len()
                        && item.outputs == seq![Wire::Gate(gate)]
                        && item.arguments.len() == 2
                        && gates[gate as int] == (NorGate { left: item.arguments[0], right: item.arguments[1] }),
                    PrimitivePlacement::Storage(index) => target is StateElement && index < storage.len()
                        && index < sites.len() && sites[index as int].call_index == call
                        && sites[index as int].at == checked.calls@[call].at
                        && self.placement_matches(checked, width, sites[index as int])
                        && item.outputs == storage_outputs(sites[index as int].outputs)
                        && sites[index as int].storage_inputs_match(item.arguments, Some(storage[index as int])),
                }
            },
        }
    }

    #[verifier::opaque]
    spec fn hierarchy_primitives_bound(
        &self, checked: &ModuleCalls, width: u64, ports: &ClockedModuleOutputs, definitions: Seq<Wire>,
        primitives: Seq<Option<PrimitiveWiring>>, gates: Seq<NorGate>,
        storage: Seq<ClockedStorageInputs>, sites: Seq<ClockedStoragePlacement>,
    ) -> bool {
        &&& primitives.len() <= checked.calls@.len()
        &&& forall|i: int| 0 <= i < primitives.len() ==> self.hierarchy_primitive_bound(
            checked, width, ports, definitions, i, #[trigger] primitives[i], gates, storage, sites)
    }

    proof fn extend_hierarchy_primitives(
        &self, checked: &ModuleCalls, width: u64, ports: &ClockedModuleOutputs, definitions: Seq<Wire>,
        before: Seq<Option<PrimitiveWiring>>, added: Option<PrimitiveWiring>,
        prior_gates: Seq<NorGate>, gates: Seq<NorGate>, prior_storage: Seq<ClockedStorageInputs>,
        storage: Seq<ClockedStorageInputs>, sites: Seq<ClockedStoragePlacement>,
    )
        requires
            before.len() < checked.calls@.len(),
            prior_gates.len() <= gates.len(), gates.take(prior_gates.len() as int) == prior_gates,
            prior_storage.len() <= storage.len(), storage.take(prior_storage.len() as int) == prior_storage,
            self.hierarchy_primitives_bound(checked, width, ports, definitions, before, prior_gates, prior_storage, sites),
            self.hierarchy_primitive_bound(checked, width, ports, definitions, before.len() as int, added, gates, storage, sites),
        ensures self.hierarchy_primitives_bound(checked, width, ports, definitions, before.push(added), gates, storage, sites),
    {
        reveal(UseAliases::hierarchy_primitives_bound);
        let next = before.push(added);
        assert forall|i: int| 0 <= i < next.len() implies self.hierarchy_primitive_bound(
            checked, width, ports, definitions, i, #[trigger] next[i], gates, storage, sites) by {
            if i < before.len() {
                assert(next[i] == before[i]);
                if let Some(item) = before[i] {
                    match item.placement {
                        PrimitivePlacement::Nor(gate) => { assert(gates[gate as int] == prior_gates[gate as int]); },
                        PrimitivePlacement::Storage(index) => { assert(storage[index as int] == prior_storage[index as int]); },
                    }
                }
            } else {
                assert(next[i] == added);
            }
        };
    }

    #[verifier::opaque]
    spec fn hierarchy_public_wiring(
        &self, checked: &ModuleCalls, width: u64, ports: &ClockedModuleOutputs, wiring: &HierarchyWiring, outputs: Seq<Wire>,
    ) -> bool {
        let definitions = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@;
        &&& wiring.origins.len() == definitions.len() == ports.definitions.ranges_model().len()
        &&& wiring.definitions.len() == ports.definitions.total_bits_model()
        &&& resolved_bits(row_model(ports.drivers@), wiring.definitions, outputs)
        &&& wiring.routines.len() == checked.calls@.len()
        &&& forall|call: int| 0 <= call < checked.calls@.len() ==>
            ((#[trigger] wiring.routines[call]).is_some()
                == (checked.calls@[call].inputs.ports.signature.target is Routine))
        &&& forall|i: int| 0 <= i < wiring.routines.len() ==> ((#[trigger] wiring.routines[i]) matches Some(routine) ==> {
            &&& self.call_wires_result(checked, width, ports, i as usize, Ok(routine.argument_rows))
            &&& resolved_bits(row_model(routine.argument_rows@), wiring.definitions, routine.external)
        })
        &&& forall|slot: int| 0 <= slot < definitions.len() ==> #[trigger]
            self.hierarchy_definition_wiring(checked, ports, wiring, slot)
    }

    spec fn hierarchy_definition_wiring(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, wiring: &HierarchyWiring, slot: int,
    ) -> bool {
        let parent = ports.definitions.ranges_model()[slot];
        let expected = wiring.definitions.subrange(parent.start as int, parent.end as int);
        match wiring.origins[slot] {
            HierarchyRowOrigin::Local(wires) => {
                self.wire_definition_without_call_matches(checked, ports, slot as usize, Some(wires))
                    && resolved_bits(wires@, wiring.definitions, expected)
            },
            HierarchyRowOrigin::Call(call) => {
                &&& self.source_vm_root_slot(checked, slot, call as int)
                &&& call < wiring.routines.len()
                &&& match wiring.routines[call as int] {
                    None => self.source_vm_direct_slot(checked, slot, call as int)
                        && (wiring.primitives[call as int] matches Some(primitive) && expected == primitive.outputs),
                    Some(routine) => {
                        let port = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[slot].result_index as int;
                        &&& port < routine.layout.ranges_model().len()
                        &&& {
                            let child = routine.layout.ranges_model()[port];
                            expected == routine.outputs.subrange(child.start as int, child.end as int)
                        }
                    },
                }
            },
        }
    }

    // 子モジュールは依存先の展開結果、関数は解決済み宣言の展開結果を使う。
    spec fn routine_uses_selected_template(
        checked: &ModuleCalls, edges: Seq<Option<usize>>, networks: Seq<Option<ClockedModuleNetwork>>,
        functions: Map<(usize, usize), ClockedFunctionTemplate>, call: int,
        callee: NorNetlist, inputs: PortBitLayout, outputs: PortBitLayout, devices: Seq<ClockedStorageInputs>,
    ) -> bool {
        match edges[call] {
            Some(child) => child < networks.len() && (networks[child as int] matches Some(network) && {
                &&& callee == network.circuit.netlist_model()
                &&& inputs == network.inputs && outputs == network.outputs
                &&& devices == network.storage@
            }),
            None => function_target(checked, edges, call) matches Some(key) && {
                let template = functions[key];
                &&& functions.contains_key(key)
                &&& callee == template.circuit.netlist_model()
                &&& inputs == template.inputs && outputs == template.outputs
                &&& devices.len() == 0
            },
        }
    }

    #[verifier::opaque]
    spec fn network_uses_selected_templates(
        checked: &ModuleCalls, edges: Seq<Option<usize>>, networks: Seq<Option<ClockedModuleNetwork>>,
        functions: Map<(usize, usize), ClockedFunctionTemplate>, network: &ClockedModuleNetwork,
    ) -> bool {
        &&& edges.len() == checked.calls@.len()
        &&& network._hierarchy_wiring@ matches Some(wiring)
        &&& wiring.routines.len() == checked.calls@.len()
        &&& forall|i: int| 0 <= i < wiring.routines.len() ==> ((#[trigger] wiring.routines[i]) matches Some(routine)
            ==> Self::routine_uses_selected_template(checked, edges, networks, functions, i, routine.callee,
                routine.inputs, routine.layout, routine.devices))
    }

    proof fn selected_templates_survive_extension(
        checked: &ModuleCalls, edges: Seq<Option<usize>>, old_networks: Seq<Option<ClockedModuleNetwork>>,
        new_networks: Seq<Option<ClockedModuleNetwork>>, old_functions: Map<(usize, usize), ClockedFunctionTemplate>,
        new_functions: Map<(usize, usize), ClockedFunctionTemplate>, network: &ClockedModuleNetwork,
    )
        requires
            Self::network_uses_selected_templates(checked, edges, old_networks, old_functions, network),
            old_networks.len() == new_networks.len(),
            function_cache_extends(old_functions, new_functions),
            forall|i: int| 0 <= i < edges.len() ==> ((#[trigger] edges[i]) matches Some(child)
                ==> child < old_networks.len() && old_networks[child as int] == new_networks[child as int]),
        ensures Self::network_uses_selected_templates(checked, edges, new_networks, new_functions, network),
    {
        reveal(UseAliases::network_uses_selected_templates);
        let wiring = network._hierarchy_wiring@->Some_0;
        assert forall|i: int| 0 <= i < wiring.routines.len() implies ((#[trigger] wiring.routines[i]) matches Some(routine)
            ==> Self::routine_uses_selected_template(checked, edges, new_networks, new_functions, i,
                routine.callee, routine.inputs, routine.layout, routine.devices)) by {
            if let Some(routine) = wiring.routines[i] {
                assert(Self::routine_uses_selected_template(checked, edges, old_networks, old_functions, i,
                    routine.callee, routine.inputs, routine.layout, routine.devices));
            }
        };
    }

    // 処理済みの宣言が、その依存先として記録した展開結果を参照する。
    #[verifier::opaque]
    spec fn hierarchy_templates_through(
        &self, hierarchy: &ClockedHierarchy, limits: ClockedModuleVmLimits, end: int,
        networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
    ) -> bool {
        &&& 0 <= end <= hierarchy.order@.len()
        &&& networks.len() == hierarchy.positions@.len()
        &&& forall|i: int| 0 <= i < end ==> {
            let node = #[trigger] hierarchy.order@[i] as int;
            &&& 0 <= node < networks.len()
            &&& (hierarchy.modules@[node] matches Some(checked) ==> networks[node] matches Some(network) && {
                &&& self.hierarchy_network_wiring(&checked, limits, &network)
                &&& Self::network_uses_selected_templates(&checked, hierarchy.graph@[node]@, networks, functions, &network)
            })
        }
    }

    proof fn append_hierarchy_template(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        index: int, before: Seq<Option<ClockedModuleNetwork>>, after: Seq<Option<ClockedModuleNetwork>>,
        old_functions: Map<(usize, usize), ClockedFunctionTemplate>,
        functions: Map<(usize, usize), ClockedFunctionTemplate>, compiled: Option<ClockedModuleNetwork>,
    )
        requires
            self.clocked_hierarchy_matches(owner, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, index, before, old_functions),
            function_cache_extends(old_functions, functions),
            0 <= index < hierarchy.order@.len(),
            ({
                let node = hierarchy.order@[index] as int;
                &&& 0 <= node < before.len()
                &&& match (hierarchy.modules@[node], compiled) {
                    (None, None) => after == before,
                    (Some(checked), Some(network)) => after == before.update(node, Some(network))
                        && self.hierarchy_network_wiring(&checked, limits, &network)
                        && Self::network_uses_selected_templates(&checked, hierarchy.graph@[node]@, before, functions, &network),
                    _ => false,
                }
            }),
        ensures self.hierarchy_templates_through(hierarchy, limits, index + 1, after, functions),
    {
        reveal(UseAliases::hierarchy_templates_through);
        self.clocked_hierarchy_evidence(owner, limits.width, hierarchy);
        let node = hierarchy.order@[index] as int;
        assert(hierarchy.rank@[node] == index);
        assert forall|i: int| 0 <= i <= index implies {
            let loaded = #[trigger] hierarchy.order@[i] as int;
            &&& 0 <= loaded < after.len()
            &&& (hierarchy.modules@[loaded] matches Some(checked) ==> after[loaded] matches Some(network) && {
                &&& self.hierarchy_network_wiring(&checked, limits, &network)
                &&& Self::network_uses_selected_templates(&checked, hierarchy.graph@[loaded]@, after, functions, &network)
            })
        } by {
            let loaded = hierarchy.order@[i] as int;
            assert(hierarchy.rank@[loaded] == i);
            if i < index {
                assert(loaded != node);
                assert(after[loaded] == before[loaded]);
            }
            if let Some(checked) = hierarchy.modules@[loaded] {
                let network = after[loaded]->Some_0;
                let edges = hierarchy.graph@[loaded]@;
                assert forall|call: int| 0 <= call < edges.len() implies ((#[trigger] edges[call]) matches Some(child)
                    ==> child < before.len() && after[child as int] == before[child as int]) by {
                    if let Some(child) = edges[call] {
                        self.clocked_hierarchy_edge(owner, limits.width, hierarchy, loaded, call);
                        assert(hierarchy.rank@[child as int] < i);
                        assert(child as int != node);
                        assert(after[child as int] == before[child as int]);
                    }
                };
                if i == index {
                    Self::selected_templates_survive_extension(&checked, edges, before, after, functions, functions, &network);
                } else {
                    Self::selected_templates_survive_extension(&checked, edges, before, after, old_functions, functions, &network);
                }
            }
        };
    }

    spec fn hierarchy_compilation_snapshot(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, vm: &ClockedModuleVm,
        hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
        functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int,
    ) -> bool {
        &&& self.clocked_hierarchy_matches(owner, limits.width, &hierarchy)
        &&& self.hierarchy_templates_through(&hierarchy, limits, end, networks, functions)
        &&& self.clocked_functions_match(functions, limits.width, limits.wiring_bits, limits.gates)
        &&& 0 < end <= hierarchy.order@.len() && hierarchy.order@[end - 1] == 0
        &&& networks.len() > 0
        &&& networks[0] matches Some(network)
        &&& hierarchy.modules@.len() > 0 && hierarchy.modules@[0].is_some()
        &&& self.network_vm_on_reset(&network, limits.state_bits, vm)
        &&& self.hierarchy_network_wiring(&hierarchy.modules@[0]->Some_0, limits, &network)
        &&& network.circuit.netlist_model().gates@.len() <= limits.gates
        &&& network.circuit.netlist_model().input_count <= limits.wiring_bits
    }

    /// ルートの定義と公開ポートの配線に対応するネットワークから、VM が初期化されることを表す。
    pub closed spec fn clocked_module_hierarchy_vm(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, vm: &ClockedModuleVm,
    ) -> bool {
        exists|hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
            functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int|
            #[trigger] self.hierarchy_compilation_snapshot(owner, limits, vm, hierarchy, networks, functions, end)
    }

    /// 失敗した関数の展開を、階層中の宣言と、そこで最初に失敗した呼び出しに対応付ける。
    pub closed spec fn clocked_hierarchy_function_failure(
        &self, root: ModuleBodyPosition, limits: ClockedModuleVmLimits, failed: ModuleBodyPosition,
        site: LocatedName, expansion: crate::project::ExpandFunctionsError,
    ) -> bool {
        exists|hierarchy: ClockedHierarchy, node: int, cache: Map<(usize, usize), crate::project::use_aliases::bit_func::ClockedFunctionTemplate>|
            #[trigger] self.clocked_hierarchy_matches(root, limits.width, &hierarchy)
            && 0 <= node < hierarchy.positions@.len()
            && hierarchy.positions@[node] == failed && hierarchy.modules@[node].is_some()
            && self.clocked_functions_match(cache, limits.width, limits.wiring_bits, limits.gates)
            && #[trigger] self.function_expansion_stops_at(&hierarchy.modules@[node]->Some_0,
                hierarchy.graph@[node]@, cache, limits.width, limits.wiring_bits, limits.gates, site, expansion)
    }

    pub(super) fn lower_clocked_hierarchy_vm(&self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits)
        -> (result: Result<Option<ClockedModuleVm>, ClockedModuleVmError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            result matches Ok(Some(compiled)) ==> compiled.vm.valid() && compiled.vm.initial()
                && compiled.vm.external_count() == compiled.inputs.total_bits_model()
                && self.clocked_module_hierarchy_vm(owner, limits, &compiled),
            result matches Err(ClockedModuleVmError::Hierarchy(super::super::super::ClockedModuleError::Recursion(path))) ==>
                self.clocked_hierarchy_recursion(owner, limits.width, path@),
            result matches Err(ClockedModuleVmError::InModule { owner: failed, reason }) ==>
                ((*reason) matches ClockedModuleVmError::Hierarchy(super::super::super::ClockedModuleError::Function { call, expansion })
                    ==> self.clocked_hierarchy_function_failure(owner, limits, failed, call, expansion)),
            result matches Err(ClockedModuleVmError::InModule { reason, .. }) ==>
                ((*reason) matches ClockedModuleVmError::ChildStateCapacity { used, width, capacity, .. }
                    ==> capacity == limits.wiring_bits && used <= capacity && used + width > capacity),
            !(result matches Err(ClockedModuleVmError::Endpoints(_))),
    {
        let hierarchy = match self.checked_clocked_hierarchy(owner, limits.width) {
            Ok(Some(hierarchy)) => hierarchy,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ClockedModuleVmError::Hierarchy(error)),
        };
        let count = hierarchy.positions.len();
        let mut networks = Vec::new();
        let mut functions = FunctionTemplates::new();
        if networks.try_reserve_exact(count).is_err() { return Err(ClockedModuleVmError::Allocation); }
        let mut index = 0;
        while index < count
            invariant index == networks@.len() <= count,
            decreases count - index,
        {
            networks.push(None);
            index += 1;
        }
        let mut index = 0;
        assert(self.hierarchy_templates_through(&hierarchy, limits, 0, networks@, functions@)) by {
            reveal(UseAliases::hierarchy_templates_through);
        };
        while index < hierarchy.order.len()
            invariant
                self.can_resolve(), self.clocked_hierarchy_matches(owner, limits.width, &hierarchy),
                obeys_cmp::<(usize, usize)>(),
                self.clocked_functions_match(functions@, limits.width, limits.wiring_bits, limits.gates),
                index <= hierarchy.order@.len(), networks@.len() == count == hierarchy.positions@.len(),
                self.hierarchy_templates_through(&hierarchy, limits, index as int, networks@, functions@),
            decreases hierarchy.order@.len() - index,
        {
            proof { self.clocked_hierarchy_evidence(owner, limits.width, &hierarchy); }
            let node = hierarchy.order[index];
            if node >= count { return Err(ClockedModuleVmError::InstanceCount); }
            if let Some(checked) = &hierarchy.modules[node] {
                let position = hierarchy.positions[node];
                let ghost old_functions = functions@;
                proof {
                    assert(hierarchy.rank@[node as int] == index);
                    assert(self.function_targets_are_declared(checked, hierarchy.graph@[node as int]@)) by {
                        assert forall|i: int| 0 <= i < checked.calls@.len() implies
                            ((#[trigger] function_target(checked, hierarchy.graph@[node as int]@, i)) matches Some(target)
                                ==> crate::project::use_aliases::call_dependencies::function_position(
                                    self.targets.project_model().circuits_model(), target)) by {
                            self.clocked_hierarchy_edge(owner, limits.width, &hierarchy, node as int, i);
                        };
                    };
                    assert forall|call: int| 0 <= call < hierarchy.graph@[node as int]@.len()
                        implies ((#[trigger] hierarchy.graph@[node as int]@[call]) matches Some(child)
                            ==> child < networks@.len() && networks@[child as int].is_some()
                                && (checked.calls@[call].inputs.ports.signature.target is Routine)) by {
                        if let Some(child) = hierarchy.graph@[node as int]@[call] {
                            self.clocked_hierarchy_edge(owner, limits.width, &hierarchy, node as int, call);
                            let rank = hierarchy.rank@[child as int];
                            assert(hierarchy.order@[rank as int] == child);
                            assert(networks@[hierarchy.order@[rank as int] as int].is_some()) by {
                                reveal(UseAliases::hierarchy_templates_through);
                            };
                        }
                    };
                }
                let network = match self.assemble_hierarchy_network(position, limits, checked, &hierarchy.graph[node], &networks, &mut functions) {
                    Ok(network) => network,
                    Err(reason) => {
                        proof {
                            if let ClockedModuleVmError::Hierarchy(super::super::super::ClockedModuleError::Function { call, expansion }) = &reason {
                                assert(self.clocked_hierarchy_function_failure(owner, limits, position, *call, *expansion)) by {
                                    assert(self.function_expansion_stops_at(checked, hierarchy.graph@[node as int]@,
                                        functions@, limits.width, limits.wiring_bits, limits.gates, *call, *expansion));
                                };
                            }
                        }
                        return Err(ClockedModuleVmError::InModule { owner: position, reason: Box::new(reason) });
                    },
                };
                if node == 0 {
                    let ghost source = network;
                    let ghost completed = networks@.update(0, Some(source));
                    proof {
                        self.append_hierarchy_template(owner, limits, &hierarchy, index as int, networks@, completed,
                            old_functions, functions@, Some(source));
                    }
                    return match self.initialize_clocked_network(network, limits.state_bits) {
                        Ok(vm) => {
                            assert(self.clocked_module_hierarchy_vm(owner, limits, &vm)) by {
                                assert(self.network_vm_on_reset(&source, limits.state_bits, &vm));
                                assert(self.hierarchy_templates_through(&hierarchy, limits, index + 1, completed, functions@));
                                assert(self.hierarchy_compilation_snapshot(owner, limits, &vm, hierarchy,
                                    completed, functions@, index + 1));
                            };
                            Ok(Some(vm))
                        },
                        Err(error) => match error {
                            ClockedModuleVmError::Vm(_, _) => Err(error),
                            _ => Err(ClockedModuleVmError::InstanceCount),
                        },
                    };
                }
                let ghost previous = networks@;
                let ghost source = network;
                networks.set(node, Some(network));
                proof {
                    self.append_hierarchy_template(owner, limits, &hierarchy, index as int, previous, networks@,
                        old_functions, functions@, Some(source));
                }
            } else {
                assert(hierarchy.modules@[node as int].is_none());
                proof {
                    self.append_hierarchy_template(owner, limits, &hierarchy, index as int, networks@, networks@,
                        functions@, functions@, None);
                }
            }
            index += 1;
        }
        Err(ClockedModuleVmError::InstanceCount)
    }

    fn assemble_hierarchy_network(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, checked: &ModuleCalls<'p, 'a>,
        edges: &[Option<usize>], networks: &[Option<ClockedModuleNetwork<'p, 'a>>],
        functions: &mut FunctionTemplates<'p, 'a>,
    ) -> (result: Result<ClockedModuleNetwork<'p, 'a>, ClockedModuleVmError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
            edges@.len() == checked.calls@.len(),
            obeys_cmp::<(usize, usize)>(),
            self.clocked_functions_match(old(functions)@, limits.width, limits.wiring_bits, limits.gates),
            self.function_targets_are_declared(checked, edges@),
            forall|call: int| 0 <= call < edges@.len() ==> ((#[trigger] edges@[call]) matches Some(child)
                ==> child < networks@.len() && networks@[child as int].is_some()
                    && (checked.calls@[call].inputs.ports.signature.target is Routine)),
        ensures result matches Ok(network) ==> network.circuit.netlist_model().gates@.len() <= limits.gates
            && network.circuit.netlist_model().input_count <= limits.wiring_bits,
            result matches Ok(network) ==> self.hierarchy_network_wiring(checked, limits, &network),
            self.clocked_functions_match(final(functions)@, limits.width, limits.wiring_bits, limits.gates),
            function_cache_extends(old(functions)@, final(functions)@),
            result matches Ok(network) ==> Self::network_uses_selected_templates(checked, edges@,
                networks@, final(functions)@, &network),
            result matches Err(ClockedModuleVmError::ChildStateCapacity { used, width, capacity, .. }) ==>
                capacity == limits.wiring_bits && used <= capacity && used + width > capacity,
            result matches Err(ClockedModuleVmError::Hierarchy(super::super::super::ClockedModuleError::Function { call, expansion })) ==>
                self.function_expansion_stops_at(checked, edges@, final(functions)@,
                    limits.width, limits.wiring_bits, limits.gates, call, expansion),
    {
        proof { self.module_calls_type_evidence(owner, limits.width, checked); }
        let ports = match self.wire_clocked_outputs(owner, limits.width, limits.wiring_bits, &checked.module) {
            Ok(ports) => ports,
            Err(error) => return Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::Ports(error))),
        };
        let external = ports.inputs.total_bits();
        if external > limits.wiring_bits {
            return Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::Storage(ClockedStorageLayoutError::ExternalCapacity)));
        }
        let direct = match self.place_clocked_storage(owner, checked, limits.width, external, limits.wiring_bits) {
            Ok(direct) => direct,
            Err(error) => return Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::Storage(error))),
        };
        if let Err(error) = self.prepare_clocked_functions(owner, limits.width, limits.wiring_bits, limits.gates, checked, edges, functions) {
            return Err(ClockedModuleVmError::Hierarchy(error));
        }

        let mut placements = Vec::<Option<CallPlacement>>::new();
        let mut total_gates = 0;
        // 直接の状態素子が使う入力の直後に、子の状態出力を呼び出し順で並べる。
        let mut total_inputs = direct.augmented_inputs;
        let mut call = 0;
        let count = checked.calls.len();
        if total_inputs > limits.wiring_bits || direct.by_call.len() != count {
            return Err(ClockedModuleVmError::InstanceCount);
        }
        if placements.try_reserve_exact(count).is_err() { return Err(ClockedModuleVmError::Allocation); }
        while call < count
            invariant
                self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
                self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(ports)),
                call == placements@.len() <= count == edges@.len() == checked.calls@.len(),
                self.storage_on_checked(checked, limits.width, external, limits.wiring_bits, Ok(direct)),
                external == ports.inputs.total_bits_model(),
                direct.augmented_inputs <= total_inputs <= limits.wiring_bits, total_gates <= limits.gates,
                obeys_cmp::<(usize, usize)>(),
                function_templates_cover(checked, edges@, functions@, count as int),
                self.clocked_functions_match(functions@, limits.width, limits.wiring_bits, limits.gates),
                function_cache_extends(old(functions)@, functions@),
                forall|i: int| 0 <= i < call ==> (#[trigger] placements@[i]).is_some()
                    == (checked.calls@[i].inputs.ports.signature.target is Routine),
                forall|i: int| 0 <= i < call ==> ((#[trigger] placements@[i]) matches Some(placed) ==> {
                    &&& self.call_wires_result(checked, limits.width, &ports, i as usize, Ok(placed._argument_rows@))
                    &&& row_model(placed._argument_rows@@) == placed.arguments@
                }),
                forall|i: int| 0 <= i < call ==> ((#[trigger] placements@[i]) matches Some(placed) ==>
                    Self::routine_uses_selected_template(checked, edges@, networks@, functions@, i,
                        placed.circuit.netlist_model(), *placed.inputs, *placed.outputs, placed.storage@)),
                forall|i: int| 0 <= i < edges@.len() ==> ((#[trigger] edges@[i]) matches Some(child)
                    ==> child < networks@.len() && networks@[child as int].is_some()
                        && (checked.calls@[i].inputs.ports.signature.target is Routine)),
            decreases count - call,
        {
            let mut placement = None;
            let routine = if let Some(child) = edges[call] {
                let Some(child) = &networks[child] else { unreachable!() };
                Some((&child.circuit, &child.inputs, &child.outputs, child.storage.as_slice(), child.storage_sites.as_slice()))
            } else if let ModuleCallTarget::Routine { position, .. } = &checked.calls[call].inputs.ports.signature.target {
                let key = (position.file, position.entry);
                assert(function_target(checked, edges@, call as int) == Some(key));
                let Some(function) = functions.get(&key) else { unreachable!() };
                Some((&function.circuit, &function.inputs, &function.outputs, [].as_slice(), [].as_slice()))
            } else {
                None
            };
            if let Some((circuit, inputs, outputs, storage, storage_sites)) = routine {
                assert(Self::routine_uses_selected_template(checked, edges@, networks@, functions@, call as int,
                    circuit.netlist_model(), *inputs, *outputs, storage@));
                let template = circuit.checked_netlist();
                let child_external = inputs.total_bits();
                if child_external > template.input_count { return Err(ClockedModuleVmError::InstanceCount); }
                let width = template.input_count - child_external;
                if width > limits.wiring_bits - total_inputs {
                    return Err(ClockedModuleVmError::ChildStateCapacity {
                        call: call_site(checked, call), used: total_inputs, width, capacity: limits.wiring_bits,
                    });
                }
                let gates = template.gates.len();
                if gates > limits.gates - total_gates {
                    return Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::GateCapacity(call_site(checked, call))));
                }
                let rows = match self.wire_call_arguments(owner, limits.width, limits.wiring_bits, checked, &ports, call) {
                    Ok(rows) => rows,
                    Err(error) => return Err(ClockedModuleVmError::Arguments(error)),
                };
                let arguments = self.flatten_clocked_arguments(&rows)?;
                if arguments.len() != child_external { return Err(ClockedModuleVmError::CallWiring(call_site(checked, call))); }
                placement = Some(CallPlacement { circuit, inputs, outputs, storage, storage_sites, gates: total_gates..total_gates + gates,
                    states: total_inputs..total_inputs + width, arguments, _argument_rows: Ghost(rows) });
                total_inputs += width;
                total_gates += gates;
            } else if matches!(checked.calls[call].inputs.ports.signature.target, ModuleCallTarget::Nor) {
                if total_gates == limits.gates {
                    return Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::GateCapacity(call_site(checked, call))));
                }
                total_gates += 1;
            }
            let ghost previous = placements@;
            placements.push(placement);
            assert forall|i: int| 0 <= i <= call implies (#[trigger] placements@[i]).is_some()
                == (checked.calls@[i].inputs.ports.signature.target is Routine) by {
                if i < call { assert(placements@[i] == previous[i]); }
            };
            assert forall|i: int| 0 <= i <= call implies ((#[trigger] placements@[i]) matches Some(placed) ==> {
                &&& self.call_wires_result(checked, limits.width, &ports, i as usize, Ok(placed._argument_rows@))
                &&& row_model(placed._argument_rows@@) == placed.arguments@
            }) by {
                if i < call { assert(placements@[i] == previous[i]); }
            };
            assert forall|i: int| 0 <= i <= call implies ((#[trigger] placements@[i]) matches Some(placed) ==>
                Self::routine_uses_selected_template(checked, edges@, networks@, functions@, i,
                    placed.circuit.netlist_model(), *placed.inputs, *placed.outputs, placed.storage@)) by {
                if i < call { assert(placements@[i] == previous[i]); }
            };
            call += 1;
        }
        let symbolic = self.bind_hierarchy_rows(owner, limits, checked, &ports, &direct, &placements)?;
        let definitions = self.resolve_hierarchy_rows(owner, limits, checked, &ports, &symbolic, &placements, total_inputs, total_gates)?;
        let result = self.finish_hierarchy_network(owner, limits, checked, ports, direct, &placements, &symbolic, &definitions, total_inputs, total_gates);
        proof {
            if let Ok(network) = &result {
                assert(Self::network_uses_selected_templates(checked, edges@, networks@, functions@, network)) by {
                    reveal(UseAliases::network_uses_selected_templates);
                    let wiring = network._hierarchy_wiring@->Some_0;
                    assert forall|i: int| 0 <= i < wiring.routines.len() implies ((#[trigger] wiring.routines[i]) matches Some(routine)
                        ==> Self::routine_uses_selected_template(checked, edges@, networks@, functions@, i,
                            routine.callee, routine.inputs, routine.layout, routine.devices)) by {
                        if let Some(routine) = wiring.routines[i] {
                            let placed = placements@[i]->Some_0;
                            assert(Self::routine_uses_selected_template(checked, edges@, networks@, functions@, i,
                                placed.circuit.netlist_model(), *placed.inputs, *placed.outputs, placed.storage@));
                        }
                    };
                };
            }
        }
        result
    }

    fn flatten_clocked_arguments(
        &self, rows: &[Vec<ClockedWireDriver>],
    ) -> (result: Result<Vec<ClockedWireDriver>, ClockedModuleVmError<'p, 'a>>)
        ensures result matches Ok(arguments) ==> arguments@ == row_model(rows@),
            result matches Err(error) ==> error is Allocation,
    {
        let mut arguments = Vec::new();
        let mut row = 0;
        while row < rows.len()
            invariant row <= rows@.len(), arguments@ == row_model(rows@.take(row as int)),
            decreases rows@.len() - row,
        {
            let wires = &rows[row];
            if arguments.try_reserve(wires.len()).is_err() { return Err(ClockedModuleVmError::Allocation); }
            if wires.len() > usize::MAX - arguments.len() { return Err(ClockedModuleVmError::Allocation); }
            self.append_definition_wires(&mut arguments, wires);
            proof {
                let previous = rows@.take(row as int).map_values(|item: Vec<ClockedWireDriver>| item@);
                let next = rows@.take(row + 1).map_values(|item: Vec<ClockedWireDriver>| item@);
                assert(next =~= previous.push(wires@));
                previous.lemma_flatten_push(wires@);
            }
            row += 1;
        }
        assert(rows@.take(row as int) =~= rows@);
        Ok(arguments)
    }

    // 定義に対応する部分列が、局所式または同じ呼び出しの出力から得られる。
    #[verifier::opaque]
    spec fn hierarchy_row_matches(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, calls: Seq<Option<CallPlacement>>,
        bits: Seq<ClockedWireDriver>, slot: int, origin: HierarchyRowOrigin,
    ) -> bool {
        let range = ports.definitions.ranges_model()[slot];
        let row = bits.subrange(range.start as int, range.end as int);
        let def = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[slot];
        &&& 0 <= slot < ports.definitions.ranges_model().len()
        &&& slot < checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len()
        &&& range.start <= range.end <= bits.len()
        &&& match origin {
            HierarchyRowOrigin::Local(wires) =>
                self.wire_definition_without_call_matches(checked, ports, slot as usize, Some(wires)) && wires@ == row,
            HierarchyRowOrigin::Call(call) => {
                &&& call < calls.len()
                &&& self.wire_definition_without_call_matches(checked, ports, slot as usize, None)
                &&& match calls[call as int] {
                    Some(placed) => self.source_vm_root_slot(checked, slot, call as int)
                        && child_port_drivers_match(placed.circuit, placed.outputs, def.result_index,
                            placed.arguments@, placed.states, placed.gates, row),
                    None => self.source_vm_direct_slot(checked, slot, call as int),
                }
            },
        }
    }

    fn bind_hierarchy_rows(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, checked: &ModuleCalls<'p, 'a>,
        ports: &ClockedModuleOutputs, direct: &ClockedStorageLayout<'p, 'a>, calls: &[Option<CallPlacement<'_, 'p, 'a>>],
    ) -> (result: Result<HierarchyRows, ClockedModuleVmError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(*ports)),
            calls@.len() == checked.calls@.len(),
        ensures !(result matches Err(ClockedModuleVmError::Hierarchy(_) | ClockedModuleVmError::ChildStateCapacity { .. })),
            result matches Ok(symbolic) ==> {
            &&& symbolic.bits@.len() == ports.definitions.total_bits_model()
            &&& symbolic._origins@.len() == checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len()
            &&& forall|i: int| 0 <= i < symbolic._origins@.len() ==> #[trigger]
                self.hierarchy_row_matches(checked, ports, calls@, symbolic.bits@, i, symbolic._origins@[i])
            &&& forall|i: int| 0 <= i < symbolic._origins@.len() ==> #[trigger]
                primitive_symbolic_row(checked, ports, calls@, direct, symbolic.bits@, i, symbolic._origins@[i])
        },
    {
        let expressions = &checked.module.expressions;
        let drivers = &expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, limits.width, checked);
            self.module_output_types_evidence(owner, limits.width, checked.module);
            self.module_selections_evidence(owner, limits.width, *expressions);
            self.module_alias_types_evidence(owner, limits.width, expressions.typed);
            self.module_type_sources_bounds(owner, limits.width, expressions.typed.sources);
            self.clocked_output_layouts(&checked.module, limits.width, limits.wiring_bits, ports);
        }
        let mut symbolic = Vec::new();
        if symbolic.try_reserve_exact(ports.definitions.total_bits()).is_err() { return Err(ClockedModuleVmError::Allocation); }
        let mut slot = 0;
        let mut call = 0;
        let mut gates = 0usize;
        proof { gate_cursor_zero(checked, calls@); }
        let ghost mut origins = Seq::<HierarchyRowOrigin>::empty();
        while slot < drivers.definitions.len()
            invariant
                self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
                self.module_drivers_result(owner, limits.width, Ok(Some(*drivers))),
                *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
                self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(*ports)),
                slot <= drivers.definitions@.len(), call <= calls@.len() == checked.calls@.len(),
                slot == origins.len(),
                gates == gate_cursor(checked, calls@, call as nat),
                forall|i: int| 0 <= i < slot ==> #[trigger]
                    self.hierarchy_row_matches(checked, ports, calls@, symbolic@, i, origins[i]),
                forall|i: int| 0 <= i < slot ==> #[trigger]
                    primitive_symbolic_row(checked, ports, calls@, direct, symbolic@, i, origins[i]),
            decreases drivers.definitions@.len() - slot,
        {
            let Some(range) = ports.definitions.range(slot) else { return Err(ClockedModuleVmError::InstanceCount); };
            assert(slot < ports.definitions.ranges_model().len() && range == ports.definitions.ranges_model()[slot as int]);
            if range.start != symbolic.len() { return Err(ClockedModuleVmError::InstanceCount); }
            let width = range.end - range.start;
            let ghost before = symbolic@;
            let ghost previous = origins;
            let local = match self.wire_definition_without_call(owner, limits.width, limits.wiring_bits, checked, ports, slot) {
                Ok(local) => local,
                Err(error) => return Err(ClockedModuleVmError::Endpoints(error)),
            };
            if let Some(wires) = local {
                if wires.len() != width { return Err(ClockedModuleVmError::InstanceCount); }
                self.append_definition_wires(&mut symbolic, &wires);
                proof {
                    let origin = HierarchyRowOrigin::Local(wires);
                    origins = previous.push(origin);
                    assert(local == Some(wires));
                    assert(self.wire_definition_without_call_matches(checked, ports, slot, Some(wires)));
                    assert(range.end == symbolic@.len());
                    assert(symbolic@.subrange(range.start as int, range.end as int) =~= wires@);
                    assert(self.hierarchy_row_matches(checked, ports, calls@, symbolic@, slot as int, origin)) by {
                        reveal(UseAliases::hierarchy_row_matches);
                    };
                    assert(primitive_symbolic_row(checked, ports, calls@, direct, symbolic@, slot as int, origins[slot as int]));
                }
            } else if call < calls.len() && calls[call].is_some() {
                let Some(placement) = &calls[call] else { return Err(ClockedModuleVmError::InstanceCount); };
                let wires = match self.bind_child_definition(owner, limits, checked, ports, slot, call,
                    placement.circuit, placement.outputs, &placement.arguments, &placement.states, &placement.gates) {
                    Ok(wires) => wires,
                    Err(error) => return Err(ClockedModuleVmError::Endpoints(error)),
                };
                if wires.len() != width { return Err(ClockedModuleVmError::InstanceCount); }
                self.append_definition_wires(&mut symbolic, &wires);
                proof {
                    let origin = HierarchyRowOrigin::Call(call);
                    origins = previous.push(origin);
                    assert(symbolic@.subrange(range.start as int, range.end as int) =~= wires@);
                    assert(self.hierarchy_row_matches(checked, ports, calls@, symbolic@, slot as int, origin)) by {
                        reveal(UseAliases::hierarchy_row_matches);
                    };
                    assert(primitive_symbolic_row(checked, ports, calls@, direct, symbolic@, slot as int, origins[slot as int]));
                }
                let port = drivers.definitions[slot].result_index;
                let port_count = placement.outputs.ranges().len();
                if port >= port_count { return Err(ClockedModuleVmError::InstanceCount); }
                if port + 1 == port_count {
                    proof { gate_cursor_next(checked, calls@, call as nat); }
                    gates = placement.gates.end;
                    call += 1;
                }
            } else {
                if call >= calls.len() || !self.direct_slot(owner, limits.width, checked, drivers, slot, call) {
                    return Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::Unsupported(
                        self.source_driver_location(owner, limits.width, drivers, slot))));
                }
                let ghost cursor = gates;
                if matches!(checked.calls[call].inputs.ports.signature.target, ModuleCallTarget::Nor) {
                    if width != 1 || gates >= limits.gates { return Err(ClockedModuleVmError::InstanceCount); }
                    symbolic.push(ClockedWireDriver::Terminal(Wire::Gate(gates)));
                    gates += 1;
                    assert(symbolic@.subrange(range.start as int, range.end as int)
                        =~= seq![ClockedWireDriver::Terminal(Wire::Gate(cursor))]);
                } else {
                    if call >= direct.by_call.len() { return Err(ClockedModuleVmError::InstanceCount); }
                    let Some(instance) = direct.by_call[call] else { return Err(ClockedModuleVmError::InstanceCount); };
                    if instance >= direct.instances.len() { return Err(ClockedModuleVmError::InstanceCount); }
                    let placement = &direct.instances[instance];
                    if placement.outputs.start > placement.outputs.end || placement.outputs.end - placement.outputs.start != width {
                        return Err(ClockedModuleVmError::InstanceCount);
                    }
                    let mut bit = 0;
                    while bit < width
                        invariant bit <= width, symbolic@.len() == before.len() + bit,
                            symbolic@.take(before.len() as int) == before,
                            placement.outputs.start + width == placement.outputs.end,
                            forall|j: int| 0 <= j < bit ==> (#[trigger] symbolic@[before.len() + j])
                                == ClockedWireDriver::Terminal(Wire::Input((placement.outputs.start + j) as usize)),
                        decreases width - bit,
                    {
                        let Some(wire) = placement.output_wire(bit) else { return Err(ClockedModuleVmError::InstanceCount); };
                        let ghost prior = symbolic@;
                        symbolic.push(ClockedWireDriver::Terminal(wire));
                        assert(symbolic@.take(before.len() as int) =~= before);
                        assert forall|j: int| 0 <= j <= bit implies (#[trigger] symbolic@[before.len() + j])
                            == ClockedWireDriver::Terminal(Wire::Input((placement.outputs.start + j) as usize)) by {
                            if j < bit { assert(symbolic@[before.len() + j] == prior[before.len() + j]); }
                        };
                        bit += 1;
                    }
                    proof {
                        let row = symbolic@.subrange(range.start as int, range.end as int);
                        let terminals = storage_outputs(placement.outputs)
                            .map_values(|wire: Wire| ClockedWireDriver::Terminal(wire));
                        assert(range.start == before.len() && range.end == symbolic@.len());
                        assert(row.len() == terminals.len());
                        assert forall|j: int| 0 <= j < row.len() implies (#[trigger] row[j]) == terminals[j] by {
                            assert(row[j] == symbolic@[before.len() + j]);
                        };
                        assert(row =~= terminals);
                    }
                }
                proof {
                    let origin = HierarchyRowOrigin::Call(call);
                    origins = previous.push(origin);
                    assert(self.hierarchy_row_matches(checked, ports, calls@, symbolic@, slot as int, origin)) by {
                        reveal(UseAliases::hierarchy_row_matches);
                    };
                    assert(primitive_symbolic_row(checked, ports, calls@, direct, symbolic@, slot as int, origins[slot as int]));
                    gate_cursor_next(checked, calls@, call as nat);
                }
                call += 1;
            }
            assert(symbolic@.take(before.len() as int) =~= before);
            assert forall|i: int| 0 <= i < slot + 1 implies #[trigger]
                self.hierarchy_row_matches(checked, ports, calls@, symbolic@, i, origins[i]) by {
                if i < slot {
                    assert(origins[i] == previous[i]);
                    assert(self.hierarchy_row_matches(checked, ports, calls@, before, i, previous[i]));
                    reveal(UseAliases::hierarchy_row_matches);
                    let old = ports.definitions.ranges_model()[i];
                    assert(symbolic@.subrange(old.start as int, old.end as int)
                        =~= before.subrange(old.start as int, old.end as int));
                } else {
                    assert(origins[i] == origins.last());
                }
            };
            assert forall|i: int| 0 <= i < slot + 1 implies #[trigger]
                primitive_symbolic_row(checked, ports, calls@, direct, symbolic@, i, origins[i]) by {
                if i < slot {
                    assert(origins[i] == previous[i]);
                    assert(self.hierarchy_row_matches(checked, ports, calls@, before, i, previous[i]));
                    assert(primitive_symbolic_row(checked, ports, calls@, direct, before, i, previous[i]));
                    reveal(UseAliases::hierarchy_row_matches);
                    let old = ports.definitions.ranges_model()[i];
                    assert(symbolic@.subrange(old.start as int, old.end as int)
                        =~= before.subrange(old.start as int, old.end as int));
                } else {
                    assert(origins[i] == origins.last());
                }
            };
            slot += 1;
        }
        if call != calls.len() || symbolic.len() != ports.definitions.total_bits() {
            return Err(ClockedModuleVmError::InstanceCount);
        }
        Ok(HierarchyRows { bits: symbolic, _origins: Ghost(origins) })
    }

    fn resolve_hierarchy_rows(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, checked: &ModuleCalls<'p, 'a>,
        ports: &ClockedModuleOutputs, symbolic: &HierarchyRows, calls: &[Option<CallPlacement<'_, 'p, 'a>>],
        inputs: usize, gates: usize,
    ) -> (result: Result<Vec<Wire>, ClockedModuleVmError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(*ports)),
            symbolic._origins@.len() == checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len(),
            forall|i: int| 0 <= i < symbolic._origins@.len() ==> #[trigger]
                self.hierarchy_row_matches(checked, ports, calls@, symbolic.bits@, i, symbolic._origins@[i]),
        ensures result matches Ok(definitions) ==> definitions@.len() == symbolic.bits@.len()
                && clocked_wires_match(symbolic.bits@, definitions@),
            !(result matches Err(ClockedModuleVmError::Hierarchy(_) | ClockedModuleVmError::ChildStateCapacity { .. })),
    {
        let expressions = &checked.module.expressions;
        let drivers = &expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, limits.width, checked);
            self.module_output_types_evidence(owner, limits.width, checked.module);
            self.module_selections_evidence(owner, limits.width, *expressions);
            self.module_alias_types_evidence(owner, limits.width, expressions.typed);
            self.module_type_sources_bounds(owner, limits.width, expressions.typed.sources);
        }
        match clocked_resolve(&symbolic.bits, inputs, gates) {
            Ok(definitions) => Ok(definitions),
            Err(ClockedPlanError::AliasCycle(bits)) => {
                let mut sites = Vec::new();
                if sites.try_reserve_exact(bits.len()).is_err() { return Err(ClockedModuleVmError::Allocation); }
                let mut i = 0;
                while i < bits.len()
                    invariant i <= bits@.len(),
                        clocked_wire_cycle(symbolic.bits@, bits@),
                        forall|j: int| 0 <= j < bits@.len() ==> #[trigger] bits@[j] < symbolic.bits@.len(),
                        self.can_resolve(), self.module_drivers_result(owner, limits.width, Ok(Some(*drivers))),
                        *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
                        self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
                        self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(*ports)),
                        symbolic._origins@.len() == drivers.definitions@.len(),
                        forall|j: int| 0 <= j < symbolic._origins@.len() ==> #[trigger]
                            self.hierarchy_row_matches(checked, ports, calls@, symbolic.bits@, j, symbolic._origins@[j]),
                    decreases bits@.len() - i,
                {
                    let bit = bits[i];
                    let Some(slot) = ports.definitions.port_at_bit(bit) else { return Err(ClockedModuleVmError::InstanceCount); };
                    if slot >= drivers.definitions.len() { return Err(ClockedModuleVmError::InstanceCount); }
                    proof { clocked_cycle_edge(symbolic.bits@, bits@, i as int); }
                    let site = self.hierarchy_cycle_site(owner, limits, checked, ports, slot, bit, symbolic, calls);
                    sites.push(site);
                    i += 1;
                }
                Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::AliasCycle(sites)))
            },
            Err(ClockedPlanError::Wire(bit)) => {
                let Some(slot) = ports.definitions.port_at_bit(bit) else { return Err(ClockedModuleVmError::InstanceCount); };
                if slot >= drivers.definitions.len() { return Err(ClockedModuleVmError::InstanceCount); }
                Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::Driver(
                    self.source_driver_location(owner, limits.width, drivers, slot))))
            },
            Err(ClockedPlanError::GateCapacity(_)) => Err(ClockedModuleVmError::InstanceCount),
        }
    }

    /// 閉路の配線に対応する参照範囲を返す。子の直結出力は親で受け取る左辺を指す。
    fn hierarchy_cycle_site(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, checked: &ModuleCalls<'p, 'a>,
        ports: &ClockedModuleOutputs, slot: usize, bit: usize, _rows: &HierarchyRows,
        _calls: &[Option<CallPlacement<'_, 'p, 'a>>],
    ) -> (site: LocatedName<'p, 'a>)
        requires self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(*ports)),
            slot < checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len(),
            slot < _rows._origins@.len(),
            slot < ports.definitions.ranges_model().len(),
            self.hierarchy_row_matches(checked, ports, _calls@, _rows.bits@, slot as int, _rows._origins@[slot as int]),
            ports.definitions.ranges_model()[slot as int].start <= bit < ports.definitions.ranges_model()[slot as int].end,
            _rows.bits@[bit as int] is Alias,
    {
        let expressions = &checked.module.expressions;
        let drivers = &expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, limits.width, checked);
            self.module_output_types_evidence(owner, limits.width, checked.module);
            self.module_selections_evidence(owner, limits.width, *expressions);
            self.module_alias_types_evidence(owner, limits.width, expressions.typed);
            self.module_type_sources_bounds(owner, limits.width, expressions.typed.sources);
        }
        if self.endpoint_projection_at(checked, slot).is_some() {
            return self.endpoint_projection_site(owner, limits.width, checked, slot);
        }
        if expressions.concats[slot].is_some() {
            let Some(range) = ports.definitions.range(slot) else { unreachable!() };
            let ghost row = _rows.bits@.subrange(range.start as int, range.end as int);
            let offset = bit - range.start;
            proof {
                reveal(UseAliases::hierarchy_row_matches);
                assert(_rows._origins@[slot as int] is Local);
                let wires = _rows._origins@[slot as int]->Local_0;
                assert(self.endpoint_concat_wires(checked, ports, slot as int, wires@));
                assert(row[offset as int] == _rows.bits@[bit as int]);
            }
            return self.endpoint_concat_site(owner, limits.width, checked, ports, slot, offset, Ghost(row));
        }
        self.source_driver_location(owner, limits.width, drivers, slot)
    }

    /// 子の出力を受け取る各定義の配線が、移設済みのインスタンスの出力と一致する。
    proof fn placed_outputs_match_definitions(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, calls: Seq<Option<CallPlacement>>,
        rows: &HierarchyRows, definitions: Seq<Wire>, call: usize, arguments: Seq<Wire>, outputs: Seq<Wire>,
    )
        requires
            call < calls.len(), calls[call as int].is_some(),
            clocked_wires_match(rows.bits@, definitions),
            forall|i: int| 0 <= i < rows._origins@.len() ==> #[trigger]
                self.hierarchy_row_matches(checked, ports, calls, rows.bits@, i, rows._origins@[i]),
            ({
                let placement = calls[call as int]->Some_0;
                &&& placement.states.start <= placement.states.end
                &&& resolved_bits(placement.arguments@, definitions, arguments)
                &&& instance_outputs_match(placement.circuit.netlist_model().outputs@,
                    clocked_stateful_arguments(arguments, placement.states.start,
                        (placement.states.end - placement.states.start) as nat), placement.gates.start, outputs)
            }),
        ensures
            forall|i: int| 0 <= i < rows._origins@.len() && #[trigger] rows._origins@[i] == HierarchyRowOrigin::Call(call) ==> {
                let placement = calls[call as int]->Some_0;
                let port = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[i].result_index;
                let child = placement.outputs.ranges_model()[port as int];
                let parent = ports.definitions.ranges_model()[i];
                definitions.subrange(parent.start as int, parent.end as int)
                    == outputs.subrange(child.start as int, child.end as int)
            },
    {
        let placement = calls[call as int]->Some_0;
        assert forall|i: int| 0 <= i < rows._origins@.len() && #[trigger] rows._origins@[i] == HierarchyRowOrigin::Call(call) implies {
            let port = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[i].result_index;
            let child = placement.outputs.ranges_model()[port as int];
            let parent = ports.definitions.ranges_model()[i];
            definitions.subrange(parent.start as int, parent.end as int)
                == outputs.subrange(child.start as int, child.end as int)
        } by {
            assert(self.hierarchy_row_matches(checked, ports, calls, rows.bits@, i, rows._origins@[i]));
            reveal(UseAliases::hierarchy_row_matches);
            let port = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[i].result_index;
            let child = placement.outputs.ranges_model()[port as int];
            let parent = ports.definitions.ranges_model()[i];
            let local = rows.bits@.subrange(parent.start as int, parent.end as int);
            let actual = outputs.subrange(child.start as int, child.end as int);
            let expected = definitions.subrange(parent.start as int, parent.end as int);
            child_port_resolves_to_instance(placement.circuit.netlist_model().outputs@, child, local,
                placement.arguments@, definitions, arguments, placement.states, placement.gates, outputs);
            assert(resolved_bits(local, definitions, actual));
            assert(child.start < child.end && child.end <= outputs.len());
            assert(parent.start < parent.end <= rows.bits@.len());
            clocked_wire_at(rows.bits@, definitions, parent.start as int);
            assert(expected.len() == local.len() == actual.len());
            assert forall|b: int| 0 <= b < actual.len() implies (#[trigger] actual[b]) == expected[b] by {
                clocked_wire_at(rows.bits@, definitions, parent.start + b);
                assert(local[b] == rows.bits@[parent.start + b]);
                assert(resolved_driver(local[b], definitions) == Some(expected[b]));
            };
            assert(actual =~= expected);
        };
    }

    spec fn captured_call_output(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, calls: Seq<Option<CallPlacement>>,
        rows: &HierarchyRows, definitions: Seq<Wire>, call: int, output: Option<RoutineWiring>,
    ) -> bool {
        match (calls[call], output) {
            (None, None) => true,
            (Some(placed), Some(routine)) => {
                &&& routine.layout == *placed.outputs
                &&& routine.inputs == *placed.inputs
                &&& routine.callee == placed.circuit.netlist_model()
                &&& routine.devices == placed.storage@
                &&& routine.gates == placed.gates && routine.state_inputs == placed.states
                &&& routine.argument_rows == placed._argument_rows@
                &&& resolved_bits(placed.arguments@, definitions, routine.external)
                &&& forall|slot: int| 0 <= slot < rows._origins@.len()
                    && #[trigger] rows._origins@[slot] == HierarchyRowOrigin::Call(call as usize) ==> {
                    let port = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[slot].result_index as int;
                    let child = routine.layout.ranges_model()[port];
                    let parent = ports.definitions.ranges_model()[slot];
                    definitions.subrange(parent.start as int, parent.end as int)
                        == routine.outputs.subrange(child.start as int, child.end as int)
                }
            },
            _ => false,
        }
    }

    fn finish_hierarchy_network(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, checked: &ModuleCalls<'p, 'a>,
        ports: ClockedModuleOutputs, direct: ClockedStorageLayout<'p, 'a>,
        calls: &[Option<CallPlacement<'_, 'p, 'a>>], _rows: &HierarchyRows, definitions: &[Wire], total_inputs: usize, total_gates: usize,
    ) -> (result: Result<ClockedModuleNetwork<'p, 'a>, ClockedModuleVmError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(ports)),
            self.storage_on_checked(checked, limits.width, ports.inputs.total_bits_model(), limits.wiring_bits, Ok(direct)),
            calls@.len() == checked.calls@.len(),
            forall|i: int| 0 <= i < calls@.len() ==> (#[trigger] calls@[i]).is_some()
                == (checked.calls@[i].inputs.ports.signature.target is Routine),
            forall|i: int| 0 <= i < calls@.len() ==> ((#[trigger] calls@[i]) matches Some(placed) ==> {
                &&& self.call_wires_result(checked, limits.width, &ports, i as usize, Ok(placed._argument_rows@))
                &&& row_model(placed._argument_rows@@) == placed.arguments@
            }),
            total_inputs <= limits.wiring_bits, total_gates <= limits.gates,
            clocked_wires_match(_rows.bits@, definitions@),
            _rows._origins@.len() == checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len(),
            _rows.bits@.len() == definitions@.len() == ports.definitions.total_bits_model(),
            forall|i: int| 0 <= i < _rows._origins@.len() ==> #[trigger]
                self.hierarchy_row_matches(checked, &ports, calls@, _rows.bits@, i, _rows._origins@[i]),
            forall|i: int| 0 <= i < _rows._origins@.len() ==> #[trigger]
                primitive_symbolic_row(checked, &ports, calls@, &direct, _rows.bits@, i, _rows._origins@[i]),
        ensures result matches Ok(network) ==> network.circuit.netlist_model().gates@.len() <= limits.gates
            && network.circuit.netlist_model().input_count <= limits.wiring_bits,
            result matches Ok(network) ==> self.hierarchy_network_wiring(checked, limits, &network),
            result matches Ok(network) ==> (network._hierarchy_wiring@ matches Some(wiring) && {
                &&& wiring.routines.len() == calls@.len()
                &&& forall|i: int| 0 <= i < wiring.routines.len() ==> ((#[trigger] wiring.routines[i]) matches Some(routine) ==> {
                    &&& calls@[i] matches Some(placed)
                    &&& routine.callee == placed.circuit.netlist_model()
                    &&& routine.inputs == *placed.inputs && routine.layout == *placed.outputs
                    &&& routine.devices == placed.storage@
                })
            }),
            !(result matches Err(ClockedModuleVmError::Hierarchy(_) | ClockedModuleVmError::ChildStateCapacity { .. })),
    {
        let mut gates = Vec::new();
        let mut storage: Vec<ClockedStorageInputs> = Vec::new();
        let mut child_storage: Vec<ClockedStorageInputs> = Vec::new();
        let mut child_sites = Vec::new();
        let ghost mut captured = Seq::<Option<RoutineWiring>>::empty();
        let ghost mut primitives = Seq::<Option<PrimitiveWiring>>::empty();
        let ghost mut boundaries = seq![CallBoundary { gates: 0, direct: 0, child: 0 }];
        let first_state = direct.augmented_inputs;
        let mut next_state = first_state;
        proof {
            gate_cursor_zero(checked, calls@);
            empty_routines(first_state);
            empty_routine_pins(total_inputs, total_gates as nat);
            assert(call_partition_matches(boundaries, captured, primitives,
                CallBoundary { gates: 0, direct: 0, child: 0 })) by { reveal(call_partition_matches); };
            assert(self.hierarchy_primitives_bound(checked, limits.width, &ports, definitions@, primitives,
                gates@, storage@, direct.instances@)) by { reveal(UseAliases::hierarchy_primitives_bound); };
        }
        if gates.try_reserve_exact(total_gates).is_err() || storage.try_reserve_exact(direct.instances.len()).is_err() {
            return Err(ClockedModuleVmError::Allocation);
        }
        let mut call = 0;
        while call < calls.len()
            invariant
                call <= calls@.len() == checked.calls@.len(),
                call == captured.len(),
                call == primitives.len(),
                call_partition_matches(boundaries, captured, primitives,
                    CallBoundary { gates: gates@.len(), direct: storage@.len(), child: child_storage@.len() }),
                gates@.len() == gate_cursor(checked, calls@, call as nat),
                forall|i: int| 0 <= i < call ==> primitive_follows_plan(
                    checked, calls@, &direct, i, #[trigger] primitives[i]),
                self.hierarchy_primitives_bound(checked, limits.width, &ports, definitions@, primitives,
                    gates@, storage@, direct.instances@),
                routines_placed(captured, gates@, child_storage@, first_state, next_state),
                routines_pins_valid(captured, total_inputs, total_gates as nat),
                forall|i: int| 0 <= i < calls@.len() ==> (#[trigger] calls@[i]).is_some()
                    == (checked.calls@[i].inputs.ports.signature.target is Routine),
                self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
                self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(ports)),
                self.storage_on_checked(checked, limits.width, ports.inputs.total_bits_model(), limits.wiring_bits, Ok(direct)),
                storage@.len() <= direct.instances@.len(),
                forall|i: int| 0 <= i < storage@.len() ==>
                    (#[trigger] direct.instances@[i]).outputs.start + (#[trigger] storage@[i]).data@.len()
                        == direct.instances@[i].outputs.end,
                clocked_wires_match(_rows.bits@, definitions@),
                forall|i: int| 0 <= i < call ==> #[trigger]
                    self.captured_call_output(checked, &ports, calls@, _rows, definitions@, i, captured[i]),
                forall|i: int| 0 <= i < _rows._origins@.len() ==> #[trigger]
                    self.hierarchy_row_matches(checked, &ports, calls@, _rows.bits@, i, _rows._origins@[i]),
            decreases calls@.len() - call,
        {
            let ghost before = captured;
            let ghost prior_gates = gates@;
            let ghost prior_storage = child_storage@;
            let ghost prior_state = next_state;
            let ghost prior_direct = storage@;
            let ghost first = CallBoundary { gates: prior_gates.len(), direct: prior_direct.len(), child: prior_storage.len() };
            let ghost mut primitive = None::<PrimitiveWiring>;
            proof { vstd::std_specs::vec::axiom_spec_len(&child_storage); }
            if let Some(placement) = &calls[call] {
                let mut arguments = Vec::new();
                match append_row(&mut arguments, &placement.arguments, definitions) {
                    Ok(()) => {},
                    Err(ResolveRowError::Allocation) => return Err(ClockedModuleVmError::Allocation),
                    Err(ResolveRowError::Driver(_)) => return Err(ClockedModuleVmError::CallWiring(call_site(checked, call))),
                }
                if gates.len() != placement.gates.start || next_state != placement.states.start {
                    return Err(ClockedModuleVmError::InstanceCount);
                }
                proof {
                    assert(arguments@.skip(0) =~= arguments@);
                    assert(resolved_bits(placement.arguments@, definitions@, arguments@));
                }
                let mut instance = match placement.circuit.append_stateful_instance(
                    &mut gates, placement.storage, &arguments, &mut next_state, total_inputs, total_gates,
                ) {
                    Ok(instance) => instance,
                    Err(ClockedStatefulInstanceError::Allocation) => return Err(ClockedModuleVmError::Allocation),
                    Err(_) => return Err(ClockedModuleVmError::CallWiring(call_site(checked, call))),
                };
                if gates.len() != placement.gates.end || next_state != placement.states.end
                    || instance.storage.len() != placement.storage_sites.len() {
                    return Err(ClockedModuleVmError::InstanceCount);
                }
                proof {
                    let width = clocked_storage_output_width(placement.storage@);
                    assert(placement.states.start + width == placement.states.end);
                    assert(instance_outputs_match(placement.circuit.netlist_model().outputs@,
                        clocked_stateful_arguments(arguments@, placement.states.start, width),
                        placement.gates.start, instance.outputs@));
                    self.placed_outputs_match_definitions(checked, &ports, calls@, _rows, definitions@,
                        call, arguments@, instance.outputs@);
                }
                if child_storage.try_reserve(instance.storage.len()).is_err()
                    || child_sites.try_reserve(instance.storage.len()).is_err() {
                    return Err(ClockedModuleVmError::Allocation);
                }
                let ghost placed_devices = instance.storage@;
                proof {
                    let pins = clocked_stateful_arguments(arguments@, placement.states.start,
                        clocked_storage_output_width(placement.storage@));
                    assert(placed_devices.len() == placement.storage@.len());
                    assert forall|i: int| 0 <= i < placed_devices.len() implies placement.storage@[i].parent_placement_matches(
                        pins, placement.gates.start, &(#[trigger] placed_devices[i])) by {
                        assert(placed_devices[i] == instance.storage@[i]);
                    };
                }
                child_storage.append(&mut instance.storage);
                proof {
                    vstd::std_specs::vec::axiom_spec_len(&child_storage);
                    let routine = RoutineWiring {
                        inputs: *placement.inputs, layout: *placement.outputs, outputs: instance.outputs@,
                        callee: placement.circuit.netlist_model(), devices: placement.storage@, external: arguments@,
                        gates: placement.gates, state_inputs: placement.states,
                        argument_rows: placement._argument_rows@,
                        storage: Range { start: prior_storage.len() as usize, end: child_storage@.len() as usize },
                    };
                    let output = Some(routine);
                    assert(self.captured_call_output(checked, &ports, calls@, _rows, definitions@, call as int, output));
                    assert(child_storage@ == prior_storage + placed_devices);
                    assert(child_storage@.take(prior_storage.len() as int) =~= prior_storage);
                    assert(routine_placed(routine, gates@, child_storage@, next_state)) by {
                        let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
                            clocked_storage_output_width(routine.devices));
                        assert forall|i: int| 0 <= i < routine.devices.len() implies routine.devices[i].parent_placement_matches(
                            pins, routine.gates.start, &(#[trigger] child_storage@[routine.storage.start + i])) by {
                            assert(child_storage@[routine.storage.start + i] == placed_devices[i]);
                        };
                    };
                    extend_routines(before, output, prior_gates, gates@, prior_storage, child_storage@,
                        first_state, prior_state, next_state);
                    assert(routine_pins_valid(routine, total_inputs, total_gates as nat));
                    extend_routine_pins(before, output, total_inputs, total_gates as nat);
                    captured = before.push(output);
                }
                let external = placement.inputs.total_bits();
                let mut i = 0;
                while i < placement.storage_sites.len()
                    invariant i <= placement.storage_sites@.len(),
                        routines_placed(captured, gates@, child_storage@, first_state, next_state),
                        routines_pins_valid(captured, total_inputs, total_gates as nat),
                    decreases placement.storage_sites@.len() - i,
                {
                    let site = &placement.storage_sites[i];
                    if external > site.outputs.start || site.outputs.start > site.outputs.end
                        || placement.states.start > placement.states.end
                        || site.outputs.end - external > placement.states.end - placement.states.start {
                        return Err(ClockedModuleVmError::InstanceCount);
                    }
                    let start = placement.states.start + (site.outputs.start - external);
                    let end = placement.states.start + (site.outputs.end - external);
                    child_sites.push(ClockedStoragePlacement {
                        call_index: site.call_index, at: site.at, call: copy_location(&site.call),
                        address_bits: site.address_bits, outputs: start..end,
                    });
                    i += 1;
                }
            } else {
                proof {
                    assert(self.captured_call_output(checked, &ports, calls@, _rows, definitions@, call as int, None));
                    captured = before.push(None);
                    extend_routine_pins(before, None, total_inputs, total_gates as nat);
                }
                let rows = match self.wire_call_arguments(owner, limits.width, limits.wiring_bits, checked, &ports, call) {
                    Ok(rows) => rows,
                    Err(error) => return Err(ClockedModuleVmError::Arguments(error)),
                };
                let arguments = match resolve_rows(&rows, definitions) {
                    Ok(arguments) => arguments,
                    Err(ResolveRowsError::Allocation) => return Err(ClockedModuleVmError::Allocation),
                    Err(ResolveRowsError::Driver { .. }) => return Err(ClockedModuleVmError::CallWiring(call_site(checked, call))),
                };
                if matches!(checked.calls[call].inputs.ports.signature.target, ModuleCallTarget::Nor) {
                    if arguments.len() != 2 || gates.len() >= total_gates {
                        return Err(ClockedModuleVmError::CallWiring(call_site(checked, call)));
                    }
                    let ghost gate = gates@.len() as usize;
                    gates.push(NorGate { left: arguments[0], right: arguments[1] });
                    proof {
                        primitive = Some(PrimitiveWiring {
                            placement: PrimitivePlacement::Nor(gate), rows, arguments: arguments@,
                            outputs: seq![Wire::Gate(gate)],
                        });
                    }
                } else {
                    if call >= direct.by_call.len() { return Err(ClockedModuleVmError::InstanceCount); }
                    let Some(instance) = direct.by_call[call] else { return Err(ClockedModuleVmError::InstanceCount); };
                    if instance != storage.len() || instance >= direct.instances.len() {
                        return Err(ClockedModuleVmError::InstanceCount);
                    }
                    let Some(inputs) = direct.instances[instance].storage_inputs(&arguments) else {
                        return Err(ClockedModuleVmError::CallWiring(call_site(checked, call)));
                    };
                    proof {
                        self.storage_layout_call(checked, limits.width, ports.inputs.total_bits_model(),
                            limits.wiring_bits, &direct, call);
                        direct.instances@[instance as int].storage_inputs_width(arguments@, inputs);
                        primitive = Some(PrimitiveWiring {
                            placement: PrimitivePlacement::Storage(instance), rows, arguments: arguments@,
                            outputs: storage_outputs(direct.instances@[instance as int].outputs),
                        });
                    }
                    storage.push(inputs);
                    assert forall|i: int| 0 <= i < storage@.len() implies
                        (#[trigger] direct.instances@[i]).outputs.start + (#[trigger] storage@[i]).data@.len()
                            == direct.instances@[i].outputs.end by {
                        if i < instance {
                            assert(storage@[i] == prior_direct[i]);
                        }
                    };
                }
                proof {
                    assert(gates@.take(prior_gates.len() as int) =~= prior_gates);
                    assert(child_storage@.take(prior_storage.len() as int) =~= prior_storage);
                    extend_routines(before, None, prior_gates, gates@, prior_storage, child_storage@,
                        first_state, prior_state, next_state);
                }
            }
            proof {
                assert(gates@.take(prior_gates.len() as int) =~= prior_gates);
                assert(storage@.take(prior_direct.len() as int) =~= prior_direct);
                gate_cursor_next(checked, calls@, call as nat);
                assert(self.hierarchy_primitive_bound(checked, limits.width, &ports, definitions@, call as int,
                    primitive, gates@, storage@, direct.instances@));
                self.extend_hierarchy_primitives(checked, limits.width, &ports, definitions@, primitives, primitive,
                    prior_gates, gates@, prior_direct, storage@, direct.instances@);
                let next = primitives.push(primitive);
                assert forall|i: int| 0 <= i < next.len() implies primitive_follows_plan(
                    checked, calls@, &direct, i, #[trigger] next[i]) by {
                    if i < call { assert(next[i] == primitives[i]); }
                    else { assert(next[i] == primitive); }
                };
                let last = CallBoundary { gates: gates@.len(), direct: storage@.len(), child: child_storage@.len() };
                assert(captured == before.push(captured.last()));
                assert(call_interval_matches(first, last, captured.last(), primitive));
                extend_call_partition(boundaries, before, primitives, first, last, captured.last(), primitive);
                boundaries = boundaries.push(last);
                primitives = next;
            }
            assert forall|i: int| 0 <= i <= call implies #[trigger]
                self.captured_call_output(checked, &ports, calls@, _rows, definitions@, i, captured[i]) by {
                if i < call { assert(captured[i] == before[i]); }
            };
            call += 1;
        }
        if gates.len() != total_gates || next_state != total_inputs || storage.len() != direct.instances.len() {
            return Err(ClockedModuleVmError::InstanceCount);
        }
        let ghost direct_wiring = storage@;
        let ghost direct_sites = direct.instances@;
        let ghost source_direct = direct;
        let ghost routine_storage = child_storage@;
        proof {
            self.placed_storage_width_evidence(checked, limits.width, ports.inputs.total_bits_model(),
                limits.wiring_bits, &direct, direct_wiring);
            routines_output_width(captured, gates@, routine_storage, first_state, next_state);
            clocked_storage_width_concat(direct_wiring, routine_storage);
        }
        let mut storage_sites = direct.instances;
        if storage.try_reserve(child_storage.len()).is_err() || storage_sites.try_reserve(child_sites.len()).is_err() {
            return Err(ClockedModuleVmError::Allocation);
        }
        let direct_devices = storage.len();
        storage.append(&mut child_storage);
        assert(storage@.skip(direct_devices as int) =~= routine_storage);
        assert(storage@.take(direct_devices as int) =~= direct_wiring);
        proof {
            assert(storage@ =~= direct_wiring + routine_storage);
            join_routine_input_offsets(captured, gates@, storage@, direct_devices, ports.inputs.total_bits_model(),
                first_state, next_state);
        }
        storage_sites.append(&mut child_sites);
        assert(storage_sites@.take(direct_devices as int) =~= direct_sites);
        let outputs = match resolve_rows(&ports.drivers, definitions) {
            Ok(outputs) => outputs,
            Err(ResolveRowsError::Allocation) => return Err(ClockedModuleVmError::Allocation),
            Err(ResolveRowsError::Driver { port, bit }) => {
                let declared = &checked.module.expressions.typed.sources.roots.wiring.drivers.signature.outputs;
                let site = if port < declared.len() { Some(copy_location(&declared[port].annotation)) } else { None };
                return Err(ClockedModuleVmError::OutputWiring { port, bit, site });
            },
        };
        let circuit = match ClockedNor::check(NorNetlist { input_count: total_inputs, gates, outputs }) {
            Ok(circuit) => circuit,
            Err(error) => return Err(ClockedModuleVmError::Netlist(error)),
        };
        let ghost source_ports = ports;
        let ghost wiring = HierarchyWiring {
            definitions: definitions@, origins: _rows._origins@, routines: captured, primitives,
            boundaries, direct_devices, first_child_input: first_state,
        };
        proof {
            self.module_calls_type_evidence(owner, limits.width, checked);
            self.module_output_types_evidence(owner, limits.width, checked.module);
            self.clocked_output_layouts(&checked.module, limits.width, limits.wiring_bits, &source_ports);
            self.module_selections_evidence(owner, limits.width, checked.module.expressions);
            self.clocked_definition_layout_evidence(&checked.module.expressions, limits.width, limits.wiring_bits,
                &source_ports.definitions, 0);
            assert(self.hierarchy_public_wiring(checked, limits.width, &source_ports, &wiring, circuit.netlist_model().outputs@)) by {
                reveal(UseAliases::hierarchy_public_wiring);
                assert forall|i: int| 0 <= i < captured.len() implies
                    (#[trigger] captured[i]).is_some() == (checked.calls@[i].inputs.ports.signature.target is Routine) by {
                    assert(self.captured_call_output(checked, &source_ports, calls@, _rows, definitions@, i, captured[i]));
                };
                assert forall|i: int| 0 <= i < captured.len() implies ((#[trigger] captured[i]) matches Some(routine) ==> {
                    &&& self.call_wires_result(checked, limits.width, &source_ports, i as usize, Ok(routine.argument_rows))
                    &&& resolved_bits(row_model(routine.argument_rows@), definitions@, routine.external)
                }) by {
                    assert(self.captured_call_output(checked, &source_ports, calls@, _rows, definitions@, i, captured[i]));
                };
                assert forall|slot: int| 0 <= slot < wiring.origins.len() implies #[trigger]
                    self.hierarchy_definition_wiring(checked, &source_ports, &wiring, slot) by {
                    assert(self.hierarchy_row_matches(checked, &source_ports, calls@, _rows.bits@, slot, _rows._origins@[slot]));
                    reveal(UseAliases::hierarchy_row_matches);
                    match _rows._origins@[slot] {
                        HierarchyRowOrigin::Call(index) => {
                            assert(self.captured_call_output(checked, &source_ports, calls@, _rows, definitions@, index as int, captured[index as int]));
                            if calls@[index as int].is_none() {
                                reveal(UseAliases::hierarchy_primitives_bound);
                                assert(self.hierarchy_primitive_bound(checked, limits.width, &source_ports, definitions@,
                                    index as int, primitives[index as int], circuit.netlist_model().gates@,
                                    direct_wiring, direct_sites));
                                let item = primitives[index as int]->Some_0;
                                assert(primitive_follows_plan(checked, calls@, &source_direct, index as int, Some(item)));
                                assert(primitive_symbolic_row(checked, &source_ports, calls@, &source_direct,
                                    _rows.bits@, slot, _rows._origins@[slot]));
                                let range = source_ports.definitions.ranges_model()[slot];
                                let expected = definitions@.subrange(range.start as int, range.end as int);
                                let symbols = _rows.bits@.subrange(range.start as int, range.end as int);
                                assert(symbols =~= item.outputs.map_values(|wire: Wire| ClockedWireDriver::Terminal(wire)));
                                assert forall|bit: int| 0 <= bit < expected.len() implies
                                    (#[trigger] expected[bit]) == (#[trigger] item.outputs[bit]) by {
                                    clocked_wire_at(_rows.bits@, definitions@, range.start + bit);
                                    assert(_rows.bits@[range.start + bit] == symbols[bit]);
                                };
                                assert(expected =~= item.outputs);
                            }
                        },
                        HierarchyRowOrigin::Local(wires) => {
                            let range = source_ports.definitions.ranges_model()[slot];
                            let expected = definitions@.subrange(range.start as int, range.end as int);
                            assert(expected.len() == wires@.len());
                            assert forall|bit: int| 0 <= bit < expected.len() implies
                                resolved_driver(wires@[bit], definitions@) == Some(#[trigger] expected[bit]) by {
                                clocked_wire_at(_rows.bits@, definitions@, range.start + bit);
                                assert(wires@[bit] == _rows.bits@[range.start + bit]);
                                assert(expected[bit] == definitions@[range.start + bit]);
                            };
                            assert(resolved_bits(wires@, definitions@, expected));
                        },
                    }
                };
            };
        }
        let network = ClockedModuleNetwork {
            inputs: ports.inputs, outputs: ports.outputs, circuit, storage, storage_sites, _hierarchy_wiring: Ghost(Some(wiring)),
        };
        assert(self.hierarchy_network_wiring(checked, limits, &network)) by {
            assert(self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(source_ports)));
        };
        assert forall|i: int| 0 <= i < captured.len() implies ((#[trigger] captured[i]) matches Some(routine) ==> {
            &&& calls@[i] matches Some(placed)
            &&& routine.callee == placed.circuit.netlist_model()
            &&& routine.inputs == *placed.inputs && routine.layout == *placed.outputs
            &&& routine.devices == placed.storage@
        }) by {
            assert(self.captured_call_output(checked, &source_ports, calls@, _rows, definitions@, i, captured[i]));
        };
        Ok(network)
    }
}

} // verus!
