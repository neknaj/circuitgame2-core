//! 型検査済みの状態素子と子の参照回路から、登録出力の幅を求める。

use super::placement_model::routine_storage_mapping;
use super::source_ids::{HierarchySourceIds, device_owner, owner_is_partition_call};
use super::source_links::source_registered_widths_match;
use super::{
    ClockedModuleNetwork, ClockedModuleOutputs, ClockedModuleVmLimits, ClockedStoragePlacement, HierarchyWiring,
    ClockedWireDriver, ModuleCalls, PartitionArea, PrimitivePlacement, UseAliases, call_partition_matches,
    resolved_bits, resolved_driver, row_model,
};
use crate::netlist::{
    SourceVmCircuit, output_ports_available, source_vm_layout_for_orders, source_vm_layout_matches,
    source_vm_layout_port_evidence, wire_available,
};
use vstd::prelude::*;

verus! {

/// 子の参照回路を、その呼び出しに使ったゲート・状態素子の配列順で保持する。
pub(super) struct HierarchyChildSource {
    pub circuit: SourceVmCircuit,
    pub ids: HierarchySourceIds,
}

/// 各子の参照回路は、親が選んだ同じ回路と状態素子に対応する。
pub(super) open spec fn hierarchy_child_sources_match(
    wiring: &HierarchyWiring, children: Seq<Option<HierarchyChildSource>>,
) -> bool {
    &&& children.len() == wiring.routines.len()
    &&& forall|call: int| 0 <= call < children.len() ==> match ((#[trigger] wiring.routines[call]), children[call]) {
        (Some(routine), Some(child)) => source_vm_layout_matches(&child.circuit, &routine.callee, routine.devices,
            &source_vm_layout_for_orders(child.ids.gates, child.ids.devices)),
        (None, None) => true,
        _ => false,
    }
}

/// 直接素子には宣言の幅を使い、子の素子には子の参照回路で定めた幅を使う。
pub(super) open spec fn hierarchy_registered_widths(
    wiring: &HierarchyWiring, sites: Seq<ClockedStoragePlacement>, children: Seq<Option<HierarchyChildSource>>,
    count: nat,
) -> Seq<nat> {
    Seq::new(count, |i: int| if i < wiring.direct_devices {
        (sites[i].outputs.end - sites[i].outputs.start) as nat
    } else {
        let call = device_owner(wiring, i as nat);
        let local = i - wiring.direct_devices - wiring.boundaries[call].child;
        let child = children[call]->Some_0;
        child.circuit.storage[child.ids.devices[local]].data.len()
    })
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 中間ネットワークでも、型検査済みの実引数と定義から直接素子の端子範囲を導く。
    pub(super) proof fn hierarchy_primitive_argument_bounds(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
        ports: &ClockedModuleOutputs, call: int,
    )
        requires
            self.hierarchy_network_wiring(checked, limits, network),
            self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(*ports)),
            ports.inputs == network.inputs,
            ({
                let wiring = network._hierarchy_wiring@->Some_0;
                &&& 0 <= call < wiring.primitives.len()
                &&& wiring.primitives[call].is_some()
                &&& self.hierarchy_primitives_bound(checked, limits.width, ports, wiring.definitions,
                    wiring.primitives, network.circuit.netlist_model().gates@,
                    network.storage@.take(wiring.direct_devices as int), network.storage_sites@.take(wiring.direct_devices as int))
            }),
        ensures ({
            let item = (network._hierarchy_wiring@->Some_0).primitives[call]->Some_0;
            let netlist = network.circuit.netlist_model();
            output_ports_available(item.arguments, netlist.input_count as nat, netlist.gates@.len(), item.arguments.len() as int)
        }),
    {
        reveal(UseAliases::hierarchy_primitives_bound);
        let wiring = network._hierarchy_wiring@->Some_0;
        let item = wiring.primitives[call]->Some_0;
        let netlist = network.circuit.netlist_model();
        let symbolic = row_model(item.rows@);
        self.call_wires_terminal_bounds(checked, limits.width, limits.wiring_bits, ports, call as usize, item.rows);
        assert(resolved_bits(symbolic, wiring.definitions, item.arguments));
        assert forall|i: int| 0 <= i < item.arguments.len() implies
            wire_available(#[trigger] item.arguments[i], netlist.input_count as nat, netlist.gates@.len()) by {
            assert(resolved_driver(symbolic[i], wiring.definitions) == Some(item.arguments[i]));
            match symbolic[i] {
                ClockedWireDriver::Terminal(wire) => {
                    assert(wire_available(wire, ports.inputs.total_bits_model() as nat, 0));
                },
                ClockedWireDriver::Alias(target) => {
                    assert(target < wiring.definitions.len());
                    assert(item.arguments[i] == wiring.definitions[target as int]);
                },
            }
        };
    }

    /// ソースから求めた登録出力幅は、展開後の VM の状態素子順と一致する。
    pub(super) proof fn hierarchy_registered_width_evidence(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
        ports: &ClockedModuleOutputs, children: Seq<Option<HierarchyChildSource>>,
    ) -> (widths: Seq<nat>)
        requires
            self.hierarchy_network_wiring(checked, limits, network),
            hierarchy_child_sources_match(&network._hierarchy_wiring@->Some_0, children),
            ({
                let wiring = network._hierarchy_wiring@->Some_0;
                self.hierarchy_primitives_bound(checked, limits.width, ports, wiring.definitions,
                    wiring.primitives, network.circuit.netlist_model().gates@,
                    network.storage@.take(wiring.direct_devices as int), network.storage_sites@.take(wiring.direct_devices as int))
            }),
        ensures
            widths == hierarchy_registered_widths(&network._hierarchy_wiring@->Some_0, network.storage_sites@,
                children, network.storage@.len()),
            source_registered_widths_match(widths, network.storage@),
    {
        let wiring = &network._hierarchy_wiring@->Some_0;
        let storage = network.storage@;
        let netlist = network.circuit.netlist_model();
        let sites = network.storage_sites@;
        let widths = hierarchy_registered_widths(wiring, sites, children, storage.len());
        reveal(call_partition_matches);
        reveal(UseAliases::hierarchy_primitives_bound);
        assert forall|i: int| 0 <= i < storage.len() implies (#[trigger] widths[i]) == storage[i].data@.len() by {
            let call = device_owner(wiring, i as nat);
            if i < wiring.direct_devices {
                owner_is_partition_call(wiring, PartitionArea::DirectStorage, i as nat);
                let primitive = wiring.primitives[call]->Some_0;
                assert(primitive.placement == PrimitivePlacement::Storage(i as usize));
                assert(wiring.primitives[call].is_some());
                let placed = sites.take(wiring.direct_devices as int)[i];
                let flat = storage.take(wiring.direct_devices as int)[i];
                assert(placed == sites[i] && flat == storage[i]);
                placed.storage_inputs_width(primitive.arguments, flat);
            } else {
                let relative = (i - wiring.direct_devices) as nat;
                owner_is_partition_call(wiring, PartitionArea::ChildStorage, relative);
                let routine = wiring.routines[call]->Some_0;
                let local = relative - wiring.boundaries[call].child;
                let child = children[call]->Some_0;
                let layout = source_vm_layout_for_orders(child.ids.gates, child.ids.devices);
                source_vm_layout_port_evidence(&child.circuit, &routine.callee, routine.devices, &layout);
                super::placement_model::placed_routine_evidence(wiring.routines, netlist.gates@,
                    storage.skip(wiring.direct_devices as int), wiring.first_child_input, netlist.input_count, call);
                assert(0 <= local < routine.devices.len());
                routine_storage_mapping(&netlist, network.inputs.total_bits_model(), storage, wiring.routines,
                    wiring.direct_devices, wiring.first_child_input, call, local);
                assert(i == wiring.direct_devices + routine.storage.start + local);
                assert(child.circuit.storage[child.ids.devices[local]].data.len() == routine.devices[local].data@.len());
            }
        };
        widths
    }
}

} // verus!
