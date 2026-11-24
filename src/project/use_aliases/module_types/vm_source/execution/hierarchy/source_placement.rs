//! 子のソース端子を親の実引数と呼び出し経路に対応付ける。

use super::placement_model::{
    RoutineWiring, placed_routine_evidence, routine_storage_mapping, routine_vm_input_offsets, routines_placed,
};
use super::source_ids::{
    HierarchySourceIds, child_source_ids_at, children_follow_calls, source_device_under, source_ids_match_network,
};
use super::{ClockedModuleNetwork, ClockedModuleVmLimits, ModuleCalls, UseAliases};
use crate::netlist::{
    ClockedStorageInputs, NorNetlist, SourceStorage, SourceVmCircuit, SourceVmNor, SourceVmWire, Wire,
    clocked_stateful_arguments, clocked_storage_output_width, instance_gates_at, instance_outputs_match, instance_wire,
    source_gate_under, source_vm_layout_for_orders, source_vm_layout_matches, source_vm_layout_port_evidence,
    source_vm_row_pair, source_vm_storage_pair, source_vm_terminal_pair,
};
use crate::project::DefinitionPosition;
use vstd::prelude::*;

verus! {

/// 子の外部入力は親の実引数で置き換え、子の内部素子には呼び出し位置を付ける。
pub(super) open spec fn source_vm_terminal_in_parent(
    site: DefinitionPosition, arguments: Seq<SourceVmWire>, terminal: SourceVmWire,
) -> SourceVmWire {
    match terminal {
        SourceVmWire::Input(index) => arguments[index as int],
        SourceVmWire::Constant(bit) => SourceVmWire::Constant(bit),
        SourceVmWire::Gate(id) => SourceVmWire::Gate(source_gate_under(seq![site], id)),
        SourceVmWire::Registered(id, bit) => SourceVmWire::Registered(source_device_under(site, id), bit),
    }
}

/// 一つの子呼び出しを親に移した配線と、同じ呼び出しをソース上で展開した配線の対応。
pub(super) proof fn source_vm_terminal_placement(
    netlist: &NorNetlist, external: usize, storage: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_child_input: usize, call: int,
    site: DefinitionPosition, child: HierarchySourceIds, parent: HierarchySourceIds,
    arguments: Seq<SourceVmWire>, terminal: SourceVmWire, flat: Wire,
)
    requires
        routines_placed(routines, netlist.gates@, storage.skip(direct as int), first_child_input, netlist.input_count),
        routine_vm_input_offsets(routines, storage, direct, external),
        0 <= call < routines.len(), routines[call].is_some(),
        child_source_ids_at(site, routines[call]->Some_0, direct, child, parent),
        parent.devices.no_duplicates(),
        ({
            let routine = routines[call]->Some_0;
            &&& source_vm_row_pair(external, storage, &source_vm_layout_for_orders(parent.gates, parent.devices),
                arguments, routine.external)
            &&& source_vm_terminal_pair(routine.external.len() as usize, routine.devices,
                &source_vm_layout_for_orders(child.gates, child.devices), terminal, flat)
        }),
    ensures ({
        let routine = routines[call]->Some_0;
        let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
            clocked_storage_output_width(routine.devices));
        source_vm_terminal_pair(external, storage, &source_vm_layout_for_orders(parent.gates, parent.devices),
            source_vm_terminal_in_parent(site, arguments, terminal), instance_wire(flat, pins, routine.gates.start))
    }),
{
    let routine = routines[call]->Some_0;
    let child_layout = source_vm_layout_for_orders(child.gates, child.devices);
    let parent_layout = source_vm_layout_for_orders(parent.gates, parent.devices);
    let width = clocked_storage_output_width(routine.devices);
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start, width);
    placed_routine_evidence(routines, netlist.gates@, storage.skip(direct as int), first_child_input, netlist.input_count, call);
    parent.gates.to_set_ensures();
    parent.devices.to_set_ensures();
    child.devices.to_set_ensures();
    match terminal {
        SourceVmWire::Input(index) => {
            assert(index < routine.external.len());
            assert(pins[index as int] == routine.external[index as int]);
        },
        SourceVmWire::Constant(_) => {},
        SourceVmWire::Gate(id) => {
            let local = flat->Gate_0;
            let i = routine.gates.start + local;
            assert(i < routine.gates.end);
            assert(parent.gates[i] == source_gate_under(seq![site], id));
            assert(parent_layout.gate_index.contains_key(parent.gates[i]));
        },
        SourceVmWire::Registered(id, bit) => {
            let local = child_layout.device_index[id];
            let relative = clocked_storage_output_width(routine.devices.take(local));
            let parent_index = direct + routine.storage.start + local;
            let mapped = source_device_under(site, id);
            assert(child.devices[local] == id);
            assert(parent.devices[parent_index] == mapped);
            assert(parent_layout.device_index.contains_key(mapped));
            assert(parent.devices[parent_layout.device_index[mapped]] == mapped);
            assert(parent_layout.device_index[mapped] == parent_index);
            routine_storage_mapping(netlist, external, storage, routines, direct, first_child_input, call, local);
            assert(relative + bit < width);
            let port = flat->Input_0 as int;
            assert(port == routine.external.len() + relative + bit);
            assert(pins[port] == Wire::Input((routine.state_inputs.start + relative + bit) as usize));
        },
    }
}

proof fn source_vm_row_placement(
    netlist: &NorNetlist, external: usize, storage: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_child_input: usize, call: int,
    site: DefinitionPosition, child: HierarchySourceIds, parent: HierarchySourceIds,
    arguments: Seq<SourceVmWire>, row: Seq<SourceVmWire>, flat: Seq<Wire>, placed: Seq<Wire>,
)
    requires
        routines_placed(routines, netlist.gates@, storage.skip(direct as int), first_child_input, netlist.input_count),
        routine_vm_input_offsets(routines, storage, direct, external),
        0 <= call < routines.len(), routines[call].is_some(),
        child_source_ids_at(site, routines[call]->Some_0, direct, child, parent),
        parent.devices.no_duplicates(),
        ({
            let routine = routines[call]->Some_0;
            &&& source_vm_row_pair(external, storage, &source_vm_layout_for_orders(parent.gates, parent.devices),
                arguments, routine.external)
            &&& source_vm_row_pair(routine.external.len() as usize, routine.devices,
                &source_vm_layout_for_orders(child.gates, child.devices), row, flat)
            &&& instance_outputs_match(flat, clocked_stateful_arguments(routine.external, routine.state_inputs.start,
                clocked_storage_output_width(routine.devices)), routine.gates.start, placed)
        }),
    ensures source_vm_row_pair(external, storage, &source_vm_layout_for_orders(parent.gates, parent.devices),
        row.map_values(|terminal: SourceVmWire| source_vm_terminal_in_parent(site, arguments, terminal)), placed),
{
    let routine = routines[call]->Some_0;
    let parent_layout = source_vm_layout_for_orders(parent.gates, parent.devices);
    let source = row.map_values(|terminal: SourceVmWire| source_vm_terminal_in_parent(site, arguments, terminal));
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
        clocked_storage_output_width(routine.devices));
    assert forall|i: int| 0 <= i < placed.len() implies
        source_vm_terminal_pair(external, storage, &parent_layout, source[i], #[trigger] placed[i]) by {
        assert(placed[i] == instance_wire(flat[i], pins, routine.gates.start));
        source_vm_terminal_placement(netlist, external, storage, routines, direct, first_child_input,
            call, site, child, parent, arguments, row[i], flat[i]);
    };
}

/// 子の NOR の左右入力を、親の回路を参照する端子に移す。
pub(super) open spec fn source_vm_gate_in_parent(
    site: DefinitionPosition, arguments: Seq<SourceVmWire>, gate: SourceVmNor,
) -> SourceVmNor {
    SourceVmNor { left: source_vm_terminal_in_parent(site, arguments, gate.left),
        right: source_vm_terminal_in_parent(site, arguments, gate.right) }
}

/// 子の状態素子について、端子の種類と各ビットの順を保って親に移す。
pub(super) open spec fn source_vm_storage_in_parent(
    site: DefinitionPosition, arguments: Seq<SourceVmWire>, storage: SourceStorage,
) -> SourceStorage {
    SourceStorage {
        address: match storage.address {
            Some(row) => Some(row.map_values(|wire: SourceVmWire| source_vm_terminal_in_parent(site, arguments, wire))),
            None => None,
        },
        data: storage.data.map_values(|wire: SourceVmWire| source_vm_terminal_in_parent(site, arguments, wire)),
        enable: source_vm_terminal_in_parent(site, arguments, storage.enable),
    }
}

pub(super) open spec fn source_vm_child_ports_match(
    netlist: &NorNetlist, external: usize, storage: Seq<ClockedStorageInputs>, direct: usize,
    routine: RoutineWiring, site: DefinitionPosition, child: HierarchySourceIds, parent: HierarchySourceIds,
    arguments: Seq<SourceVmWire>, source: &SourceVmCircuit,
) -> bool {
    let layout = source_vm_layout_for_orders(parent.gates, parent.devices);
    &&& source_vm_row_pair(external, storage, &layout, source.outputs.map_values(
        |wire: SourceVmWire| source_vm_terminal_in_parent(site, arguments, wire)), routine.outputs)
    &&& forall|i: int| 0 <= i < child.gates.len() ==> {
        let flat = #[trigger] netlist.gates@[routine.gates.start + i];
        let gate = source_vm_gate_in_parent(site, arguments, source.gates[child.gates[i]]);
        &&& source_vm_terminal_pair(external, storage, &layout, gate.left, flat.left)
        &&& source_vm_terminal_pair(external, storage, &layout, gate.right, flat.right)
    }
    &&& forall|i: int| 0 <= i < child.devices.len() ==> {
        let mapped = #[trigger] storage[direct + routine.storage.start + i];
        source_vm_storage_pair(external, storage, &layout,
            source_vm_storage_in_parent(site, arguments, source.storage[child.devices[i]]), mapped)
    }
}

/// 実引数を使って移設した子の全端子が、親のゲート・状態素子・呼び出し出力と対応する。
pub(super) proof fn source_vm_child_ports_placed(
    netlist: &NorNetlist, external: usize, storage: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_child_input: usize, call: int,
    site: DefinitionPosition, child: HierarchySourceIds, parent: HierarchySourceIds,
    arguments: Seq<SourceVmWire>, source: &SourceVmCircuit,
)
    requires
        routines_placed(routines, netlist.gates@, storage.skip(direct as int), first_child_input, netlist.input_count),
        routine_vm_input_offsets(routines, storage, direct, external),
        0 <= call < routines.len(), routines[call].is_some(),
        child_source_ids_at(site, routines[call]->Some_0, direct, child, parent),
        parent.devices.no_duplicates(),
        ({
            let routine = routines[call]->Some_0;
            &&& source_vm_row_pair(external, storage, &source_vm_layout_for_orders(parent.gates, parent.devices),
                arguments, routine.external)
            &&& source_vm_layout_matches(source, &routine.callee, routine.devices,
                &source_vm_layout_for_orders(child.gates, child.devices))
        }),
    ensures source_vm_child_ports_match(netlist, external, storage, direct, routines[call]->Some_0,
        site, child, parent, arguments, source),
{
    let routine = routines[call]->Some_0;
    let layout = source_vm_layout_for_orders(parent.gates, parent.devices);
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
        clocked_storage_output_width(routine.devices));
    placed_routine_evidence(routines, netlist.gates@, storage.skip(direct as int), first_child_input, netlist.input_count, call);
    source_vm_layout_port_evidence(source, &routine.callee, routine.devices, &source_vm_layout_for_orders(child.gates, child.devices));
    assert(source.input_count == routine.external.len());
    assert(instance_outputs_match(routine.callee.outputs@, pins, routine.gates.start, routine.outputs));
    source_vm_row_placement(netlist, external, storage, routines, direct, first_child_input, call, site,
        child, parent, arguments, source.outputs, routine.callee.outputs@, routine.outputs);
    assert(instance_gates_at(routine.callee.gates@, pins, routine.gates.start, netlist.gates@));
    assert forall|i: int| 0 <= i < child.gates.len() implies {
        let flat = #[trigger] netlist.gates@[routine.gates.start + i];
        let gate = source_vm_gate_in_parent(site, arguments, source.gates[child.gates[i]]);
        &&& source_vm_terminal_pair(external, storage, &layout, gate.left, flat.left)
        &&& source_vm_terminal_pair(external, storage, &layout, gate.right, flat.right)
    } by {
        let original = source.gates[child.gates[i]];
        let flat = routine.callee.gates@[i];
        source_vm_terminal_placement(netlist, external, storage, routines, direct, first_child_input,
            call, site, child, parent, arguments, original.left, flat.left);
        source_vm_terminal_placement(netlist, external, storage, routines, direct, first_child_input,
            call, site, child, parent, arguments, original.right, flat.right);
    };
    assert forall|i: int| 0 <= i < child.devices.len() implies
        source_vm_storage_pair(external, storage, &layout,
            source_vm_storage_in_parent(site, arguments, source.storage[child.devices[i]]),
            #[trigger] storage[direct + routine.storage.start + i]) by {
        let original = source.storage[child.devices[i]];
        let flat = routine.devices[i];
        let placed = storage[direct + routine.storage.start + i];
        routine_storage_mapping(netlist, external, storage, routines, direct, first_child_input, call, i);
        if let Some(address) = original.address {
            source_vm_row_placement(netlist, external, storage, routines, direct, first_child_input, call, site,
                child, parent, arguments, address, flat.address->Some_0@, placed.address->Some_0@);
        }
        source_vm_row_placement(netlist, external, storage, routines, direct, first_child_input, call, site,
            child, parent, arguments, original.data, flat.data@, placed.data@);
        source_vm_terminal_placement(netlist, external, storage, routines, direct, first_child_input,
            call, site, child, parent, arguments, original.enable, flat.enable);
    };
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 階層コンパイラが割り当てた区間から、子の配線対応を取り出す。
    pub(super) proof fn hierarchy_child_port_evidence(
        &self, limits: ClockedModuleVmLimits, checked: &ModuleCalls, network: &ClockedModuleNetwork,
        children: Seq<Option<HierarchySourceIds>>, parent: HierarchySourceIds, call: int,
        arguments: Seq<SourceVmWire>, source: &SourceVmCircuit,
    )
        requires
            self.hierarchy_network_wiring(checked, limits, network),
            children_follow_calls(&network._hierarchy_wiring@->Some_0, children),
            source_ids_match_network(parent, checked, network, children),
            0 <= call < checked.calls@.len(),
            ({
                let wiring = network._hierarchy_wiring@->Some_0;
                &&& wiring.routines[call].is_some() && children[call].is_some()
                &&& {
                    let routine = wiring.routines[call]->Some_0;
                    let child = children[call]->Some_0;
                    &&& source_vm_row_pair(network.inputs.total_bits_model(), network.storage@,
                        &source_vm_layout_for_orders(parent.gates, parent.devices), arguments, routine.external)
                    &&& source_vm_layout_matches(source, &routine.callee, routine.devices,
                        &source_vm_layout_for_orders(child.gates, child.devices))
                }
            }),
        ensures ({
            let wiring = network._hierarchy_wiring@->Some_0;
            source_vm_child_ports_match(&network.circuit.netlist_model(), network.inputs.total_bits_model(),
                network.storage@, wiring.direct_devices, wiring.routines[call]->Some_0, checked.calls@[call].at,
                children[call]->Some_0, parent, arguments, source)
        }),
    {
        self.child_source_ids_evidence(limits, checked, network, children, parent, call);
        reveal(UseAliases::hierarchy_public_wiring);
        let wiring = network._hierarchy_wiring@->Some_0;
        source_vm_child_ports_placed(&network.circuit.netlist_model(), network.inputs.total_bits_model(), network.storage@,
            wiring.routines, wiring.direct_devices, wiring.first_child_input, call, checked.calls@[call].at,
            children[call]->Some_0, parent, arguments, source);
    }
}

} // verus!
