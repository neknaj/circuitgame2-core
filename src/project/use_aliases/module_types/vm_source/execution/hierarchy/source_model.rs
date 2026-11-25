//! 型検査した親回路に、呼び出しごとの子の参照回路を組み込む。

use super::super::direct_source::{direct_storage_row, source_storage_row_matches};
use super::super::source_links::source_vm_links_resolved;
use super::source_ids::{
    HierarchySourceIds, children_follow_calls, device_owner, owner_is_partition_call, owning_call,
    source_id_dimensions, source_ids_match_network,
};
use super::source_links::{
    hierarchy_source_link, hierarchy_source_operand_pair, hierarchy_source_operand_row,
};
use super::source_placement::{
    source_vm_child_ports_match, source_vm_gate_in_parent, source_vm_storage_in_parent, source_vm_terminal_in_parent,
};
use super::source_widths::{HierarchyChildSource, hierarchy_child_sources_match, hierarchy_registered_widths};
use super::{
    ClockedModuleNetwork, ClockedModuleOutputs, ClockedModuleVmLimits, ClockedWireDriver, HierarchyRowOrigin,
    ModuleCalls, PartitionArea, PrimitivePlacement, UseAliases, call_interval_matches, call_partition_matches, row_model,
};
use crate::netlist::{
    SourceDeviceId, SourceGateId, SourceStorage, SourceVmCircuit, SourceVmNor, SourceVmWire,
    source_vm_layout_for_orders, source_vm_layout_from_pairs, source_vm_layout_matches, source_vm_layout_port_evidence,
    source_vm_row_pair, source_vm_storage_pair, source_vm_terminal_pair, source_vm_wiring_valid,
};
use vstd::prelude::*;

verus! {

/// 子の参照モデルを使い、同じ呼び出し順で素子の ID 列を取り出す。
pub(super) open spec fn hierarchy_child_ids(children: Seq<Option<HierarchyChildSource>>) -> Seq<Option<HierarchySourceIds>> {
    children.map_values(|child: Option<HierarchyChildSource>| match child {
        Some(model) => Some(model.ids),
        None => None,
    })
}

spec fn model_gate_at(
    checked: &ModuleCalls, network: &ClockedModuleNetwork, ids: HierarchySourceIds,
    children: Seq<Option<HierarchyChildSource>>, widths: Seq<nat>, definitions: Seq<SourceVmWire>, index: int,
) -> SourceVmNor {
    let wiring = network._hierarchy_wiring@->Some_0;
    let call = owning_call(&wiring, PartitionArea::Gate, index as nat);
    let external = network.inputs.total_bits_model();
    match children[call] {
        Some(child) => {
            let routine = wiring.routines[call]->Some_0;
            let args = hierarchy_source_operand_row(external, ids, widths, definitions, row_model(routine.argument_rows@));
            let local = index - wiring.boundaries[call].gates;
            source_vm_gate_in_parent(checked.calls@[call].at, args, child.circuit.gates[child.ids.gates[local]])
        },
        None => {
            let primitive = wiring.primitives[call]->Some_0;
            let args = hierarchy_source_operand_row(external, ids, widths, definitions, row_model(primitive.rows@));
            SourceVmNor { left: args[0], right: args[1] }
        },
    }
}

spec fn model_storage_at(
    checked: &ModuleCalls, network: &ClockedModuleNetwork, ids: HierarchySourceIds,
    children: Seq<Option<HierarchyChildSource>>, widths: Seq<nat>, definitions: Seq<SourceVmWire>, index: int,
) -> SourceStorage {
    let wiring = network._hierarchy_wiring@->Some_0;
    let call = device_owner(&wiring, index as nat);
    let external = network.inputs.total_bits_model();
    if index < wiring.direct_devices {
        let primitive = wiring.primitives[call]->Some_0;
        let args = hierarchy_source_operand_row(external, ids, widths, definitions, row_model(primitive.rows@));
        direct_storage_row(&network.storage_sites@[index], args)
    } else {
        let child = children[call]->Some_0;
        let routine = wiring.routines[call]->Some_0;
        let args = hierarchy_source_operand_row(external, ids, widths, definitions, row_model(routine.argument_rows@));
        let local = index - wiring.direct_devices - wiring.boundaries[call].child;
        source_vm_storage_in_parent(checked.calls@[call].at, args, child.circuit.storage[child.ids.devices[local]])
    }
}

spec fn hierarchy_network_source(
    checked: &ModuleCalls, network: &ClockedModuleNetwork, ports: &ClockedModuleOutputs, ids: HierarchySourceIds,
    children: Seq<Option<HierarchyChildSource>>, widths: Seq<nat>, definitions: Seq<SourceVmWire>,
) -> SourceVmCircuit {
    let layout = source_vm_layout_for_orders(ids.gates, ids.devices);
    let external = network.inputs.total_bits_model();
    SourceVmCircuit {
        input_count: external,
        gates: Map::new(layout.gate_index.dom(), |id: SourceGateId|
            model_gate_at(checked, network, ids, children, widths, definitions, layout.gate_index[id])),
        storage: Map::new(layout.device_index.dom(), |id: SourceDeviceId|
            model_storage_at(checked, network, ids, children, widths, definitions, layout.device_index[id])),
        outputs: hierarchy_source_operand_row(external, ids, widths, definitions, row_model(ports.drivers@)),
    }
}

spec fn child_definition_matches(
    checked: &ModuleCalls, network: &ClockedModuleNetwork, ports: &ClockedModuleOutputs, ids: HierarchySourceIds,
    children: Seq<Option<HierarchyChildSource>>, widths: Seq<nat>, definitions: Seq<SourceVmWire>, slot: int,
) -> bool {
    let wiring = network._hierarchy_wiring@->Some_0;
    match wiring.origins[slot] {
        HierarchyRowOrigin::Call(call) if wiring.routines[call as int].is_some() => {
            let child = children[call as int]->Some_0;
            let routine = wiring.routines[call as int]->Some_0;
            let child_port = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[slot].result_index as int;
            let source_range = routine.layout.ranges_model()[child_port];
            let local_range = ports.definitions.ranges_model()[slot];
            let site = checked.calls@[call as int].at;
            let args = hierarchy_source_operand_row(network.inputs.total_bits_model(), ids, widths, definitions,
                row_model(routine.argument_rows@));
            definitions.subrange(local_range.start as int, local_range.end as int)
                == child.circuit.outputs.subrange(source_range.start as int, source_range.end as int)
                    .map_values(|wire: SourceVmWire| source_vm_terminal_in_parent(site, args, wire))
        },
        _ => true,
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 参照回路は、型検査済みの定義と選んだ子の参照回路から構成される。
    pub(super) closed spec fn hierarchy_network_source_model(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
        children: Seq<Option<HierarchyChildSource>>, model: HierarchyChildSource,
    ) -> bool {
        let wiring = network._hierarchy_wiring@->Some_0;
        let external = network.inputs.total_bits_model();
        let widths = hierarchy_registered_widths(&wiring, network.storage_sites@, children, model.ids.devices.len());
        exists|ports: ClockedModuleOutputs, definitions: Seq<SourceVmWire>| {
            &&& #[trigger] self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(ports))
            &&& ports.inputs == network.inputs && ports.outputs == network.outputs
            &&& source_vm_links_resolved(wiring.symbolic.map_values(|driver: ClockedWireDriver|
                hierarchy_source_link(external, model.ids, widths, driver)), definitions)
            &&& forall|slot: int| 0 <= slot < wiring.origins.len() ==> #[trigger]
                child_definition_matches(checked, network, &ports, model.ids, children, widths, definitions, slot)
            &&& model.circuit == #[trigger] hierarchy_network_source(checked, network, &ports, model.ids, children, widths, definitions)
        }
    }

    /// 一つのネットワークの全端子を直接素子と子の参照回路から構成し、実配線と照合する。
    pub(super) proof fn compose_hierarchy_source_network(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
        ids: HierarchySourceIds, children: Seq<Option<HierarchyChildSource>>,
    ) -> (model: HierarchyChildSource)
        requires
            self.hierarchy_network_wiring(checked, limits, network),
            hierarchy_child_sources_match(&network._hierarchy_wiring@->Some_0, children),
            children_follow_calls(&network._hierarchy_wiring@->Some_0, hierarchy_child_ids(children)),
            source_ids_match_network(ids, checked, network, hierarchy_child_ids(children)),
        ensures
            model.ids == ids,
            self.hierarchy_network_source_model(checked, limits, network, children, model),
            source_vm_wiring_valid(&model.circuit),
            source_vm_layout_matches(&model.circuit, &network.circuit.netlist_model(), network.storage@,
                &source_vm_layout_for_orders(ids.gates, ids.devices)),
    {
        reveal(UseAliases::hierarchy_public_wiring);
        reveal(UseAliases::hierarchy_primitives_bound);
        reveal(call_partition_matches);
        source_id_dimensions(ids, checked, network, hierarchy_child_ids(children));
        let wiring = &network._hierarchy_wiring@->Some_0;
        let netlist = network.circuit.netlist_model();
        let flat_storage = network.storage@;
        let external = network.inputs.total_bits_model();
        let layout = source_vm_layout_for_orders(ids.gates, ids.devices);
        let ports = choose|ports: ClockedModuleOutputs| {
            &&& #[trigger] self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(ports))
            &&& network.inputs == ports.inputs && network.outputs == ports.outputs
            &&& self.hierarchy_public_wiring(checked, limits.width, &ports, wiring, netlist.outputs@)
            &&& self.hierarchy_primitives_bound(checked, limits.width, &ports, wiring.definitions, wiring.primitives,
                netlist.gates@, flat_storage.take(wiring.direct_devices as int),
                network.storage_sites@.take(wiring.direct_devices as int))
        };
        let widths = self.hierarchy_registered_width_evidence(checked, limits, network, &ports, children);
        let definitions = self.hierarchy_source_argument_and_output_rows(checked, limits, network, &ports, ids, widths);
        let source = hierarchy_network_source(checked, network, &ports, ids, children, widths, definitions);
        assert forall|slot: int| 0 <= slot < wiring.origins.len() implies #[trigger]
            child_definition_matches(checked, network, &ports, ids, children, widths, definitions, slot) by {
            assert(self.hierarchy_definition_wiring(checked, &ports, wiring, slot));
            if let HierarchyRowOrigin::Call(call) = wiring.origins[slot] {
                if let Some(routine) = wiring.routines[call as int] {
                    let child = children[call as int]->Some_0;
                    let args = hierarchy_source_operand_row(external, ids, widths, definitions, row_model(routine.argument_rows@));
                    self.hierarchy_child_port_evidence(limits, checked, network, hierarchy_child_ids(children), ids,
                        call as int, args, &child.circuit);
                    assert(source_vm_child_ports_match(&netlist, external, flat_storage, wiring.direct_devices,
                        routine, checked.calls@[call as int].at, child.ids, ids, args, &child.circuit));
                    self.hierarchy_definition_follows_child_output(checked, &ports, network, ids, child.ids,
                        &child.circuit, definitions, args, slot, call);
                }
            }
        };
        ids.gates.to_set_ensures();
        ids.devices.to_set_ensures();
        assert forall|i: int| 0 <= i < ids.gates.len() implies {
            let original = source.gates[ids.gates[i]];
            let flat = #[trigger] netlist.gates@[i];
            &&& source_vm_terminal_pair(external, flat_storage, &layout, original.left, flat.left)
            &&& source_vm_terminal_pair(external, flat_storage, &layout, original.right, flat.right)
        } by {
            let id = ids.gates[i];
            assert(ids.gates[layout.gate_index[id]] == id);
            assert(layout.gate_index[id] == i);
            owner_is_partition_call(wiring, PartitionArea::Gate, i as nat);
            let call = owning_call(wiring, PartitionArea::Gate, i as nat);
            assert(call_interval_matches(wiring.boundaries[call], wiring.boundaries[call + 1],
                wiring.routines[call], wiring.primitives[call]));
            if let Some(child) = children[call] {
                assert(wiring.routines[call].is_some());
                let routine = wiring.routines[call]->Some_0;
                let args = hierarchy_source_operand_row(external, ids, widths, definitions, row_model(routine.argument_rows@));
                self.hierarchy_child_port_evidence(limits, checked, network, hierarchy_child_ids(children), ids, call, args, &child.circuit);
                source_vm_layout_port_evidence(&child.circuit, &routine.callee, routine.devices,
                    &source_vm_layout_for_orders(child.ids.gates, child.ids.devices));
                let local = i - wiring.boundaries[call].gates;
                assert(routine.gates.start == wiring.boundaries[call].gates
                    && routine.gates.end == wiring.boundaries[call + 1].gates);
                assert(routine.gates.start + child.ids.gates.len() == routine.gates.end) by {
                    self.child_source_ids_evidence(limits, checked, network, hierarchy_child_ids(children), ids, call);
                };
                assert(0 <= local < child.ids.gates.len());
                assert(i == routine.gates.start + local);
            } else {
                assert(wiring.routines[call].is_none());
                let item = wiring.primitives[call]->Some_0;
                assert(item.placement == PrimitivePlacement::Nor(i as usize));
                self.hierarchy_primitive_argument_bounds(checked, limits, network, &ports, call);
                hierarchy_source_operand_pair(external, ids, widths, flat_storage, definitions, wiring.definitions,
                    row_model(item.rows@), item.arguments);
                assert(netlist.gates@[i].left == item.arguments[0] && netlist.gates@[i].right == item.arguments[1]);
            }
        };
        assert forall|i: int| 0 <= i < ids.devices.len() implies {
            let flat = #[trigger] flat_storage[i];
            &&& flat.data@.len() > 0
            &&& source_vm_storage_pair(external, flat_storage, &layout, source.storage[ids.devices[i]], flat)
        } by {
            let id = ids.devices[i];
            assert(ids.devices[layout.device_index[id]] == id);
            assert(layout.device_index[id] == i);
            let call = device_owner(wiring, i as nat);
            if i < wiring.direct_devices {
                owner_is_partition_call(wiring, PartitionArea::DirectStorage, i as nat);
                let item = wiring.primitives[call]->Some_0;
                assert(item.placement == PrimitivePlacement::Storage(i as usize));
                self.hierarchy_primitive_argument_bounds(checked, limits, network, &ports, call);
                hierarchy_source_operand_pair(external, ids, widths, flat_storage, definitions, wiring.definitions,
                    row_model(item.rows@), item.arguments);
                let row = hierarchy_source_operand_row(external, ids, widths, definitions, row_model(item.rows@));
                assert(network.storage_sites@.take(wiring.direct_devices as int)[i] == network.storage_sites@[i]);
                assert(flat_storage.take(wiring.direct_devices as int)[i] == flat_storage[i]);
                source_storage_row_matches(external, flat_storage, &layout, &network.storage_sites@[i],
                    row, item.arguments, flat_storage[i]);
            } else {
                let relative = (i - wiring.direct_devices) as nat;
                owner_is_partition_call(wiring, PartitionArea::ChildStorage, relative);
                assert(call_interval_matches(wiring.boundaries[call], wiring.boundaries[call + 1],
                    wiring.routines[call], wiring.primitives[call]));
                assert(wiring.routines[call].is_some());
                let routine = wiring.routines[call]->Some_0;
                let child = children[call]->Some_0;
                let args = hierarchy_source_operand_row(external, ids, widths, definitions, row_model(routine.argument_rows@));
                self.hierarchy_child_port_evidence(limits, checked, network, hierarchy_child_ids(children), ids, call, args, &child.circuit);
                source_vm_layout_port_evidence(&child.circuit, &routine.callee, routine.devices,
                    &source_vm_layout_for_orders(child.ids.gates, child.ids.devices));
                let local = relative - wiring.boundaries[call].child;
                assert(routine.storage.start == wiring.boundaries[call].child
                    && routine.storage.end == wiring.boundaries[call + 1].child);
                assert(routine.storage.start + child.ids.devices.len() == routine.storage.end) by {
                    self.child_source_ids_evidence(limits, checked, network, hierarchy_child_ids(children), ids, call);
                };
                assert(0 <= local < child.ids.devices.len());
                assert(i == wiring.direct_devices + routine.storage.start + local);
                super::placement_model::routine_storage_mapping(&netlist, external, flat_storage, wiring.routines,
                    wiring.direct_devices, wiring.first_child_input, call, local);
            }
        };
        source_vm_layout_from_pairs(&source, &netlist, flat_storage, ids.gates, ids.devices);
        let model = HierarchyChildSource { circuit: source, ids };
        assert(widths == hierarchy_registered_widths(wiring, network.storage_sites@, children, model.ids.devices.len()));
        assert(source_vm_links_resolved(wiring.symbolic.map_values(|driver: ClockedWireDriver|
            hierarchy_source_link(external, model.ids, widths, driver)), definitions));
        assert(self.hierarchy_network_source_model(checked, limits, network, children, model));
        model
    }
}

} // verus!
