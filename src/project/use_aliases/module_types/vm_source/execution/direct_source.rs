//! 直接呼び出しのソース位置を、ネットリスト上の素子順に対応付ける。

use super::{ClockedModuleEndpoints, ClockedModuleNetwork, ClockedModuleVm, ClockedModuleVmLimits, ModuleBodyPosition,
    ModuleCalls, UseAliases};
use super::source_links::{
    SourceVmLink, source_vm_link_pair, source_vm_link_value, source_vm_links_resolved, source_vm_operand_pair,
    source_vm_resolve_links,
};
use super::super::super::clocked_plan::{clocked_resolution_success, clocked_wire_at};
use crate::netlist::{
    ClockedStorage, ClockedStorageInputs, ClockedVm, NorNetlist, SourceDeviceId, SourceGateId, SourceStorage,
    SourceVmCircuit, SourceVmFrame, SourceVmLayout, SourceVmNor, SourceVmWire, Wire, clocked_vm_trace,
    clocked_wiring_endpoints, output_ports_available, source_vm_project_trace, source_vm_trace,
    source_vm_layout_for_orders, source_vm_layout_from_pairs, source_vm_layout_matches, source_vm_row_pair,
    source_vm_state_projection, source_vm_storage_pair, source_vm_terminal_pair, source_vm_wiring_valid, wire_available,
};
use crate::project::ClockedWireDriver;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

spec fn gate_call_order(
    calls: Seq<Option<usize>>, consumed: int, order: Seq<int>,
) -> bool {
    &&& 0 <= consumed <= calls.len()
    &&& forall|i: int| 0 <= i < order.len() ==> {
        let call = #[trigger] order[i];
        0 <= call < consumed && calls[call] == Some(i as usize)
    }
    &&& forall|call: int| 0 <= call < consumed ==> ((#[trigger] calls[call]) matches Some(gate) ==>
        gate < order.len() && order[gate as int] == call)
}

spec fn direct_device_ids(plan: &ClockedModuleEndpoints) -> Seq<SourceDeviceId> {
    plan.storage.instances@.map_values(|item: super::ClockedStoragePlacement| SourceDeviceId {
        instance: Seq::empty(), call: item.at,
    })
}

spec fn direct_source_link(
    plan: &ClockedModuleEndpoints, gates: Seq<SourceGateId>, driver: ClockedWireDriver,
) -> SourceVmLink {
    match driver {
        ClockedWireDriver::Alias(target) => SourceVmLink::Alias(target),
        ClockedWireDriver::Terminal(Wire::Constant(bit)) => SourceVmLink::Terminal(SourceVmWire::Constant(bit)),
        ClockedWireDriver::Terminal(Wire::Gate(index)) => SourceVmLink::Terminal(SourceVmWire::Gate(gates[index as int])),
        ClockedWireDriver::Terminal(Wire::Input(port)) => {
            let external = plan.ports.inputs.total_bits_model();
            if port < external {
                SourceVmLink::Terminal(SourceVmWire::Input(port))
            } else {
                let instances = plan.storage.instances@;
                let index = choose|i: int| 0 <= i < instances.len()
                    && (#[trigger] instances[i]).outputs.start <= port < instances[i].outputs.end;
                SourceVmLink::Terminal(SourceVmWire::Registered(direct_device_ids(plan)[index],
                    (port - instances[index].outputs.start) as usize))
            }
        },
    }
}

spec fn direct_source_row(
    plan: &ClockedModuleEndpoints, gates: Seq<SourceGateId>, definitions: Seq<SourceVmWire>,
    symbolic: Seq<ClockedWireDriver>,
) -> Seq<SourceVmWire> {
    symbolic.map_values(|driver: ClockedWireDriver| source_vm_link_value(direct_source_link(plan, gates, driver), definitions))
}

pub(super) open spec fn direct_storage_row(site: &super::ClockedStoragePlacement, row: Seq<SourceVmWire>) -> SourceStorage {
    let address = site.address_bits.unwrap_or(0) as int;
    let end = address + site.outputs.end - site.outputs.start;
    SourceStorage {
        address: if site.address_bits.is_some() { Some(row.take(address)) } else { None },
        data: row.subrange(address, end),
        enable: row[end],
    }
}

spec fn direct_source_circuit(
    plan: &ClockedModuleEndpoints, layout: &SourceVmLayout, order: Seq<int>,
    arguments: Seq<Vec<Vec<ClockedWireDriver>>>, definitions: Seq<SourceVmWire>,
) -> SourceVmCircuit {
    SourceVmCircuit {
        input_count: plan.ports.inputs.total_bits_model(),
        gates: Map::new(layout.gate_index.dom(), |id: SourceGateId| {
            let call = order[layout.gate_index[id]];
            let row = direct_source_row(plan, layout.gates, definitions, super::row_model(arguments[call]@));
            SourceVmNor { left: row[0], right: row[1] }
        }),
        storage: Map::new(layout.device_index.dom(), |id: SourceDeviceId| {
            let site = plan.storage.instances@[layout.device_index[id]];
            let row = direct_source_row(plan, layout.gates, definitions, super::row_model(arguments[site.call_index as int]@));
            direct_storage_row(&site, row)
        }),
        outputs: direct_source_row(plan, layout.gates, definitions, super::row_model(plan.ports.drivers@)),
    }
}

pub(super) proof fn source_storage_row_matches(
    external: usize, storage: Seq<ClockedStorageInputs>, layout: &crate::netlist::SourceVmLayout,
    site: &super::ClockedStoragePlacement, source: Seq<SourceVmWire>, flat: Seq<Wire>, lowered: ClockedStorageInputs,
)
    requires
        site.storage_inputs_match(flat, Some(lowered)),
        source_vm_row_pair(external, storage, layout, source, flat),
    ensures
        source_vm_storage_pair(external, storage, layout, direct_storage_row(site, source), lowered),
        direct_storage_row(site, source).data.len() > 0,
{
    site.storage_input_rows_evidence(flat, lowered);
    let address = site.address_bits.unwrap_or(0) as int;
    let end = address + site.outputs.end - site.outputs.start;
    assert(source_vm_row_pair(external, storage, layout, source.subrange(address, end), lowered.data@)) by {
        assert forall|i: int| 0 <= i < lowered.data@.len() implies
            source_vm_terminal_pair(external, storage, layout, source.subrange(address, end)[i], #[trigger] lowered.data@[i]) by {
            assert(lowered.data@[i] == flat[address + i]);
        };
    }
    if let Some(pins) = lowered.address {
        assert(source_vm_row_pair(external, storage, layout, source.take(address), pins@)) by {
            assert forall|i: int| 0 <= i < pins@.len() implies
                source_vm_terminal_pair(external, storage, layout, source.take(address)[i], #[trigger] pins@[i]) by {
                assert(pins@[i] == flat[i]);
            };
        }
    }
}

proof fn storage_call_row_bounds(
    site: &super::ClockedStoragePlacement, row: Seq<Wire>, wiring: ClockedStorageInputs, inputs: nat, gates: nat,
)
    requires site.storage_inputs_match(row, Some(wiring)), wiring.pins_available(inputs, gates),
    ensures output_ports_available(row, inputs, gates, row.len() as int),
{
    site.storage_input_rows_evidence(row, wiring);
    let address = site.address_bits.unwrap_or(0) as int;
    let end = address + site.outputs.end - site.outputs.start;
    assert forall|i: int| 0 <= i < row.len() implies wire_available(#[trigger] row[i], inputs, gates) by {
        if i < address {
            assert(wiring.address is Some);
            let pins = wiring.address->Some_0;
            assert(row[i] == pins@[i]);
        } else if i < end {
            assert(row[i] == wiring.data@[i - address]);
        } else {
            assert(row[i] == wiring.enable);
        }
    };
}

spec fn direct_port_rows_match(
    plan: &ClockedModuleEndpoints, netlist: &NorNetlist, storage: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    arguments: Seq<Vec<Vec<ClockedWireDriver>>>, definitions: Seq<SourceVmWire>, pins: Seq<Vec<Wire>>,
) -> bool {
    let external = plan.ports.inputs.total_bits_model();
    &&& source_vm_row_pair(external, storage, layout,
        direct_source_row(plan, layout.gates, definitions, super::row_model(plan.ports.drivers@)), netlist.outputs@)
    &&& forall|i: int| 0 <= i < pins.len() ==> {
        let source = direct_source_row(plan, layout.gates, definitions, super::row_model(arguments[i]@));
        &&& source_vm_row_pair(external, storage, layout, source, (#[trigger] pins[i])@)
        &&& match plan.gate_by_call@[i] {
            Some(index) => source.len() == 2
                && source_vm_terminal_pair(external, storage, layout, source[0], netlist.gates@[index as int].left)
                && source_vm_terminal_pair(external, storage, layout, source[1], netlist.gates@[index as int].right),
            None => plan.storage.by_call@[i] matches Some(index)
                && source_vm_storage_pair(external, storage, layout,
                    direct_storage_row(&plan.storage.instances@[index as int], source), storage[index as int])
                && storage[index as int].data@.len() > 0,
        }
    }
}

proof fn extend_gate_call_order(
    calls: Seq<Option<usize>>, consumed: int, order: Seq<int>,
) -> (next: Seq<int>)
    requires
        gate_call_order(calls, consumed, order),
        consumed < calls.len(),
        calls[consumed] matches Some(gate) ==> gate == order.len(),
    ensures gate_call_order(calls, consumed + 1, next),
        next.len() == order.len() + if calls[consumed].is_some() { 1int } else { 0int },
{
    let next = if calls[consumed].is_some() { order.push(consumed) } else { order };
    assert forall|i: int| 0 <= i < next.len() implies {
        let call = #[trigger] next[i];
        0 <= call < consumed + 1 && calls[call] == Some(i as usize)
    } by {
        if i < order.len() { assert(next[i] == order[i]); }
    };
    assert forall|call: int| 0 <= call < consumed + 1 implies
        ((#[trigger] calls[call]) matches Some(gate) ==> gate < next.len() && next[gate as int] == call) by {
        if let Some(gate) = calls[call] {
            if call < consumed { assert(next[gate as int] == order[gate as int]); }
        }
    };
    next
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    proof fn direct_gate_order_prefix(
        &self, checked: &ModuleCalls, plan: &ClockedModuleEndpoints, slot: int,
    ) -> (order: Seq<int>)
        requires
            self.endpoint_prefix(checked, &plan.ports, &plan.storage, plan._symbolic@, plan.gate_by_call@,
                plan._call_cursors@, plan._gate_cursors@),
            0 <= slot < plan._call_cursors@.len(),
        ensures
            order.len() == plan._gate_cursors@[slot],
            gate_call_order(plan.gate_by_call@, plan._call_cursors@[slot] as int, order),
            forall|i: int| 0 <= i < plan._call_cursors@[slot] && (#[trigger] plan.gate_by_call@[i]).is_some() ==>
                checked.calls@[i].inputs.ports.signature.target is Nor,
        decreases slot,
    {
        reveal(UseAliases::endpoint_prefix);
        if slot == 0 {
            return Seq::empty();
        }
        let before = self.direct_gate_order_prefix(checked, plan, slot - 1);
        self.endpoint_prefix_row(checked, &plan.ports, &plan.storage, plan._symbolic@, plan.gate_by_call@,
            plan._call_cursors@, plan._gate_cursors@, slot - 1);
        reveal(UseAliases::endpoint_row);
        let call = plan._call_cursors@[slot - 1] as int;
        if plan._call_cursors@[slot] == call {
            assert(plan._gate_cursors@[slot] == before.len());
            before
        } else {
            assert(plan._call_cursors@[slot] == call + 1);
            assert forall|i: int| 0 <= i < plan._call_cursors@[slot] && (#[trigger] plan.gate_by_call@[i]).is_some()
                implies checked.calls@[i].inputs.ports.signature.target is Nor by {
                if i == call {
                    assert(plan.gate_by_call@[call].is_some());
                }
            };
            extend_gate_call_order(plan.gate_by_call@, call, before)
        }
    }

    /// ゲート番号と呼び出し番号の対応を、直接経路が使う配置から導く。
    proof fn direct_gate_call_order(
        &self, checked: &ModuleCalls, plan: &ClockedModuleEndpoints, width_limit: u64, wire_limit: usize,
        gate_limit: usize,
    ) -> (order: Seq<int>)
        requires self.endpoints_on_checked(checked, width_limit, wire_limit, gate_limit, plan),
        ensures order.len() == plan.gate_count,
            gate_call_order(plan.gate_by_call@, checked.calls@.len() as int, order),
            forall|i: int| 0 <= i < checked.calls@.len() && (#[trigger] plan.gate_by_call@[i]).is_some() ==>
                checked.calls@[i].inputs.ports.signature.target is Nor,
    {
        reveal(UseAliases::endpoint_prefix);
        let slot = plan._call_cursors@.len() - 1;
        let order = self.direct_gate_order_prefix(checked, plan, slot);
        assert(plan._call_cursors@[slot] == checked.calls@.len());
        order
    }

    /// 直接呼び出しから生成した VM の素子順と、型検査した呼び出し位置との対応。
    pub closed spec fn clocked_direct_source_ids(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        gates: Seq<SourceGateId>, devices: Seq<SourceDeviceId>,
    ) -> bool {
        exists|checked: ModuleCalls, plan: ClockedModuleEndpoints, network: ClockedModuleNetwork, order: Seq<int>| {
            &&& #[trigger] self.module_calls_result(owner, limits.width, Ok(Some(checked)))
            &&& #[trigger] self.endpoints_on_checked(&checked, limits.width, limits.wiring_bits, limits.gates, &plan)
            &&& #[trigger] self.network_wiring_on_checked(limits, &checked, &plan, &network)
            &&& self.network_vm_on_reset(&network, limits.state_bits, compiled)
            &&& #[trigger] gate_call_order(plan.gate_by_call@, checked.calls@.len() as int, order)
            &&& order.len() == plan.gate_count
            &&& gates == order.map_values(|call: int| SourceGateId {
                instance: Seq::empty(), gate: checked.calls@[call].at,
            })
            &&& devices == direct_device_ids(&plan)
        }
    }

    /// 型検査済みの呼び出し位置を、直接経路が作った各ゲートと各状態素子に一度ずつ割り当てる。
    ///
    /// 返す列の添字は、その素子の VM 内での添字と一致する。直接経路なので経路は空になる。
    pub proof fn clocked_direct_source_id_order(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
    ) -> (ids: (Seq<SourceGateId>, Seq<SourceDeviceId>))
        requires self.can_resolve(), self.clocked_module_vm_wiring(owner, limits, compiled),
        ensures
            self.clocked_direct_source_ids(owner, limits, compiled, ids.0, ids.1),
            ids.0.len() == compiled.vm.netlist_model().gates@.len(),
            ids.1.len() == compiled.vm.storage_model().len(),
            ids.0.no_duplicates() && ids.1.no_duplicates(),
    {
        let (checked, plan, network) = choose|checked: ModuleCalls, plan: ClockedModuleEndpoints, network: ClockedModuleNetwork|
            #[trigger] self.module_calls_result(owner, limits.width, Ok(Some(checked)))
            && #[trigger] self.endpoints_on_checked(&checked, limits.width, limits.wiring_bits, limits.gates, &plan)
            && #[trigger] self.network_wiring_on_checked(limits, &checked, &plan, &network)
            && self.network_vm_on_reset(&network, limits.state_bits, compiled);
        let gate_calls = self.direct_gate_call_order(&checked, &plan, limits.width, limits.wiring_bits, limits.gates);
        let gates = gate_calls.map_values(|call: int| SourceGateId { instance: Seq::empty(), gate: checked.calls@[call].at });
        let placed = plan.storage.instances@;
        let devices = direct_device_ids(&plan);
        assert forall|i: int, j: int| 0 <= i < j < gates.len() implies (#[trigger] gates[i]) != (#[trigger] gates[j]) by {
            let a = gate_calls[i];
            let b = gate_calls[j];
            assert(plan.gate_by_call@[a] == Some(i as usize) && plan.gate_by_call@[b] == Some(j as usize));
            assert(i < j < gate_calls.len() <= usize::MAX);
            if a < b {
                self.module_call_sites_distinct(owner, limits.width, &checked, a, b);
            } else {
                assert(b < a);
                self.module_call_sites_distinct(owner, limits.width, &checked, b, a);
            }
        };
        assert forall|i: int, j: int| 0 <= i < j < devices.len() implies (#[trigger] devices[i]) != (#[trigger] devices[j]) by {
            self.storage_placements_on_calls_distinct(owner, limits.width, plan.ports.inputs.total_bits_model(),
                limits.wiring_bits, &checked, &plan.storage, i, j);
        };
        assert(gates.no_duplicates() && devices.no_duplicates());
        let (_, pins) = choose|arguments: Seq<Vec<Vec<super::ClockedWireDriver>>>, pins: Seq<Vec<super::Wire>>| {
            &&& #[trigger] self.vm_calls_bound(limits, &checked, &plan, arguments, pins,
                network.circuit.netlist_model().gates@, network.storage@)
            &&& pins.len() == checked.calls@.len()
            &&& network.circuit.netlist_model().gates@.len() == plan.gate_count
            &&& network.storage@.len() == placed.len()
        };
        assert(pins.len() == checked.calls@.len());
        assert(self.clocked_direct_source_ids(owner, limits, compiled, gates, devices));
        (gates, devices)
    }

    proof fn direct_storage_widths_on_plan(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, plan: &ClockedModuleEndpoints,
        netlist: &NorNetlist, storage: Seq<ClockedStorageInputs>,
        arguments: Seq<Vec<Vec<ClockedWireDriver>>>, pins: Seq<Vec<Wire>>,
    )
        requires
            self.endpoints_on_checked(checked, limits.width, limits.wiring_bits, limits.gates, plan),
            self.vm_calls_bound(limits, checked, plan, arguments, pins, netlist.gates@, storage),
            pins.len() == checked.calls@.len(),
            storage.len() == plan.storage.instances@.len(),
        ensures forall|i: int| 0 <= i < storage.len() ==>
            (#[trigger] plan.storage.instances@[i]).outputs.start + (#[trigger] storage[i]).data@.len()
                == plan.storage.instances@[i].outputs.end,
    {
        self.direct_gate_call_order(checked, plan, limits.width, limits.wiring_bits, limits.gates);
        reveal(UseAliases::vm_calls_bound);
        let external = plan.ports.inputs.total_bits_model();
        let placed = plan.storage.instances@;
        assert forall|i: int| 0 <= i < storage.len() implies
            (#[trigger] placed[i]).outputs.start + (#[trigger] storage[i]).data@.len() == placed[i].outputs.end by {
            let call = self.storage_layout_call_for_instance(checked, limits.width, external, limits.wiring_bits, &plan.storage, i);
            self.storage_layout_call(checked, limits.width, external, limits.wiring_bits, &plan.storage, call as usize);
            assert(checked.calls@[call].inputs.ports.signature.target is StateElement);
            assert(plan.gate_by_call@[call].is_none());
            placed[i].storage_inputs_width(pins[call]@, storage[i]);
        };
    }

    /// 直接コンパイルした状態素子の登録出力を、ソース ID とビット番号で指定する。
    ///
    /// 返した入力配線は、外部入力と先行する状態素子の出力の後にある。
    pub(crate) proof fn clocked_direct_registered_wire(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        gates: Seq<SourceGateId>, devices: Seq<SourceDeviceId>, index: int, bit: usize,
    ) -> (wire: Wire)
        requires
            self.can_resolve(), self.clocked_direct_source_ids(owner, limits, compiled, gates, devices),
            devices.no_duplicates(),
            0 <= index < devices.len() == compiled.vm.storage_model().len(),
            bit < compiled.vm.storage_model()[index].wiring_model().data@.len(),
        ensures source_vm_terminal_pair(
            compiled.vm.external_count(),
            compiled.vm.storage_model().map_values(|device: ClockedStorage| device.wiring_model()),
            &source_vm_layout_for_orders(gates, devices), SourceVmWire::Registered(devices[index], bit), wire),
    {
        let (checked, plan, network, order) =
            choose|checked: ModuleCalls, plan: ClockedModuleEndpoints, network: ClockedModuleNetwork, order: Seq<int>| {
                &&& #[trigger] self.module_calls_result(owner, limits.width, Ok(Some(checked)))
                &&& #[trigger] self.endpoints_on_checked(&checked, limits.width, limits.wiring_bits, limits.gates, &plan)
                &&& #[trigger] self.network_wiring_on_checked(limits, &checked, &plan, &network)
                &&& self.network_vm_on_reset(&network, limits.state_bits, compiled)
                &&& #[trigger] gate_call_order(plan.gate_by_call@, checked.calls@.len() as int, order)
                &&& order.len() == plan.gate_count
                &&& gates == order.map_values(|call: int| SourceGateId { instance: Seq::empty(), gate: checked.calls@[call].at })
                &&& devices == direct_device_ids(&plan)
            };
        let wiring = network.storage@;
        let netlist = network.circuit.netlist_model();
        let external = plan.ports.inputs.total_bits_model();
        let placed = plan.storage.instances@;
        let (arguments, pins) = choose|arguments: Seq<Vec<Vec<super::ClockedWireDriver>>>, pins: Seq<Vec<Wire>>| {
            &&& #[trigger] self.vm_calls_bound(limits, &checked, &plan, arguments, pins, netlist.gates@, wiring)
            &&& pins.len() == checked.calls@.len()
            &&& netlist.gates@.len() == plan.gate_count && wiring.len() == placed.len()
        };
        self.direct_storage_widths_on_plan(&checked, limits, &plan, &netlist, wiring, arguments, pins);
        self.placed_storage_range_evidence(&checked, limits.width, external, limits.wiring_bits, &plan.storage, wiring, index);
        assert(compiled.vm.storage_model().map_values(|device: ClockedStorage| device.wiring_model()) =~= wiring);
        devices.to_set_ensures();
        let layout = source_vm_layout_for_orders(gates, devices);
        let id = devices[index];
        assert(layout.device_index.contains_key(id));
        assert(devices[layout.device_index[id]] == id);
        assert(layout.device_index[id] == index);
        let start = placed[index].outputs.start;
        assert(compiled.vm.storage_model()[index].wiring_model() == wiring[index]);
        assert(start + wiring[index].data@.len() == placed[index].outputs.end);
        assert(start + bit < placed[index].outputs.end);
        Wire::Input((start + bit) as usize)
    }

    proof fn direct_source_link_matches(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, plan: &ClockedModuleEndpoints,
        storage: Seq<ClockedStorageInputs>, gates: Seq<SourceGateId>, driver: ClockedWireDriver,
    )
        requires
            self.endpoints_on_checked(checked, limits.width, limits.wiring_bits, limits.gates, plan),
            gates.len() == plan.gate_count,
            direct_device_ids(plan).no_duplicates(),
            storage.len() == plan.storage.instances@.len(),
            forall|i: int| 0 <= i < storage.len() ==>
                (#[trigger] plan.storage.instances@[i]).outputs.start + (#[trigger] storage[i]).data@.len()
                    == plan.storage.instances@[i].outputs.end,
            driver matches ClockedWireDriver::Terminal(wire) ==>
                wire_available(wire, plan.storage.augmented_inputs as nat, plan.gate_count as nat),
        ensures source_vm_link_pair(plan.ports.inputs.total_bits_model(), storage,
            &source_vm_layout_for_orders(gates, direct_device_ids(plan)), direct_source_link(plan, gates, driver), driver),
    {
        let external = plan.ports.inputs.total_bits_model();
        let devices = direct_device_ids(plan);
        let layout = source_vm_layout_for_orders(gates, devices);
        gates.to_set_ensures();
        devices.to_set_ensures();
        if let ClockedWireDriver::Terminal(Wire::Input(port)) = driver {
            if port >= external {
                self.storage_covers_augmented_input(checked, limits.width, external, limits.wiring_bits, &plan.storage, port);
                let instances = plan.storage.instances@;
                let index = choose|i: int| 0 <= i < instances.len()
                    && (#[trigger] instances[i]).outputs.start <= port < instances[i].outputs.end;
                self.placed_storage_range_evidence(checked, limits.width, external, limits.wiring_bits, &plan.storage, storage, index);
                let id = devices[index];
                assert(layout.device_index.contains_key(id));
                assert(devices[layout.device_index[id]] == id);
                assert(layout.device_index[id] == index);
                assert(instances[index].outputs.start + storage[index].data@.len() == instances[index].outputs.end);
            }
        }
    }

    /// 型検査済みの記号配線からソースの終点を求め、実際に使う解決済み配線と照合する。
    proof fn direct_source_definition_wires(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, plan: &ClockedModuleEndpoints,
        storage: Seq<ClockedStorageInputs>, gates: Seq<SourceGateId>,
    ) -> (wires: Seq<SourceVmWire>)
        requires
            self.endpoints_on_checked(checked, limits.width, limits.wiring_bits, limits.gates, plan),
            gates.len() == plan.gate_count,
            direct_device_ids(plan).no_duplicates(),
            storage.len() == plan.storage.instances@.len(),
            forall|i: int| 0 <= i < storage.len() ==>
                (#[trigger] plan.storage.instances@[i]).outputs.start + (#[trigger] storage[i]).data@.len()
                    == plan.storage.instances@[i].outputs.end,
        ensures
            source_vm_links_resolved(plan._symbolic@.map_values(|driver: ClockedWireDriver|
                direct_source_link(plan, gates, driver)), wires),
            source_vm_row_pair(plan.ports.inputs.total_bits_model(), storage,
                &source_vm_layout_for_orders(gates, direct_device_ids(plan)), wires, plan.definitions@),
    {
        let drivers = plan._symbolic@;
        let flat = plan.definitions@;
        let links = drivers.map_values(|driver: ClockedWireDriver| direct_source_link(plan, gates, driver));
        let external = plan.ports.inputs.total_bits_model();
        let layout = source_vm_layout_for_orders(gates, direct_device_ids(plan));
        clocked_resolution_success(drivers, plan.storage.augmented_inputs, plan.gate_count, plan.definitions);
        assert forall|i: int| 0 <= i < links.len() implies
            source_vm_link_pair(external, storage, &layout, #[trigger] links[i], drivers[i]) by {
            clocked_wire_at(drivers, flat, i);
            self.direct_source_link_matches(checked, limits, plan, storage, gates, drivers[i]);
        };
        source_vm_resolve_links(external, storage, &layout, links, drivers, flat)
    }

    /// 型付きの引数列または公開出力列を、宣言順とビット順を保ってソース端子に移す。
    proof fn direct_source_read_row(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, plan: &ClockedModuleEndpoints,
        storage: Seq<ClockedStorageInputs>, gates: Seq<SourceGateId>, definitions: Seq<SourceVmWire>,
        symbolic: Seq<ClockedWireDriver>, flat: Seq<Wire>,
    )
        requires
            self.endpoints_on_checked(checked, limits.width, limits.wiring_bits, limits.gates, plan),
            gates.len() == plan.gate_count,
            direct_device_ids(plan).no_duplicates(),
            storage.len() == plan.storage.instances@.len(),
            forall|i: int| 0 <= i < storage.len() ==>
                (#[trigger] plan.storage.instances@[i]).outputs.start + (#[trigger] storage[i]).data@.len()
                    == plan.storage.instances@[i].outputs.end,
            source_vm_row_pair(plan.ports.inputs.total_bits_model(), storage,
                &source_vm_layout_for_orders(gates, direct_device_ids(plan)), definitions, plan.definitions@),
            super::resolved_bits(symbolic, plan.definitions@, flat),
            output_ports_available(flat, plan.storage.augmented_inputs as nat, plan.gate_count as nat, flat.len() as int),
        ensures source_vm_row_pair(plan.ports.inputs.total_bits_model(), storage,
            &source_vm_layout_for_orders(gates, direct_device_ids(plan)), direct_source_row(plan, gates, definitions, symbolic), flat),
    {
        let external = plan.ports.inputs.total_bits_model();
        let layout = source_vm_layout_for_orders(gates, direct_device_ids(plan));
        let source = direct_source_row(plan, gates, definitions, symbolic);
        assert forall|i: int| 0 <= i < flat.len() implies
            source_vm_terminal_pair(external, storage, &layout, source[i], #[trigger] flat[i]) by {
            let driver = symbolic[i];
            assert(super::resolved_driver(driver, plan.definitions@) == Some(flat[i]));
            assert(wire_available(flat[i], plan.storage.augmented_inputs as nat, plan.gate_count as nat));
            self.direct_source_link_matches(checked, limits, plan, storage, gates, driver);
            let link = direct_source_link(plan, gates, driver);
            source_vm_operand_pair(external, storage, &layout, link, driver, definitions, plan.definitions@, flat[i]);
        };
    }

    /// 実際に束ねた呼び出しと公開出力の全ビットを、型検査済みの記号行に対応付ける。
    proof fn direct_source_ports_on_plan(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, plan: &ClockedModuleEndpoints,
        vm: &ClockedVm, netlist: NorNetlist, storage: Seq<ClockedStorageInputs>, gates: Seq<SourceGateId>,
        arguments: Seq<Vec<Vec<ClockedWireDriver>>>, pins: Seq<Vec<Wire>>,
    ) -> (definitions: Seq<SourceVmWire>)
        requires
            self.endpoints_on_checked(checked, limits.width, limits.wiring_bits, limits.gates, plan),
            gates.len() == plan.gate_count == netlist.gates@.len(),
            direct_device_ids(plan).no_duplicates(),
            storage.len() == plan.storage.instances@.len(),
            netlist.input_count == plan.storage.augmented_inputs,
            forall|i: int| 0 <= i < storage.len() ==>
                (#[trigger] plan.storage.instances@[i]).outputs.start + (#[trigger] storage[i]).data@.len()
                    == plan.storage.instances@[i].outputs.end,
            vm.layout_matches(netlist, plan.ports.inputs.total_bits_model(), storage),
            self.vm_calls_bound(limits, checked, plan, arguments, pins, netlist.gates@, storage),
            pins.len() == checked.calls@.len(),
            super::resolved_bits(super::row_model(plan.ports.drivers@), plan.definitions@, netlist.outputs@),
        ensures
            source_vm_links_resolved(plan._symbolic@.map_values(|driver: ClockedWireDriver|
                direct_source_link(plan, gates, driver)), definitions),
            direct_port_rows_match(plan, &netlist, storage, &source_vm_layout_for_orders(gates, direct_device_ids(plan)),
                arguments, definitions, pins),
    {
        reveal(UseAliases::vm_calls_bound);
        vm.network_pin_bounds();
        clocked_wiring_endpoints(&netlist);
        let definitions = self.direct_source_definition_wires(checked, limits, plan, storage, gates);
        self.direct_source_read_row(checked, limits, plan, storage, gates, definitions,
            super::row_model(plan.ports.drivers@), netlist.outputs@);
        let external = plan.ports.inputs.total_bits_model();
        let layout = source_vm_layout_for_orders(gates, direct_device_ids(plan));
        assert forall|i: int| 0 <= i < pins.len() implies {
            let source = direct_source_row(plan, gates, definitions, super::row_model(arguments[i]@));
            &&& source_vm_row_pair(external, storage, &layout, source, (#[trigger] pins[i])@)
            &&& match plan.gate_by_call@[i] {
                Some(index) => source.len() == 2
                    && source_vm_terminal_pair(external, storage, &layout, source[0], netlist.gates@[index as int].left)
                    && source_vm_terminal_pair(external, storage, &layout, source[1], netlist.gates@[index as int].right),
                None => plan.storage.by_call@[i] matches Some(index)
                    && source_vm_storage_pair(external, storage, &layout,
                        direct_storage_row(&plan.storage.instances@[index as int], source), storage[index as int])
                    && storage[index as int].data@.len() > 0,
            }
        } by {
            let flat = pins[i]@;
            let symbolic = super::row_model(arguments[i]@);
            if let Some(index) = plan.gate_by_call@[i] {
                let gate = netlist.gates@[index as int];
                assert(flat[0] == gate.left && flat[1] == gate.right);
                assert(output_ports_available(flat, netlist.input_count as nat, netlist.gates@.len(), flat.len() as int));
            } else {
                self.storage_layout_call(checked, limits.width, external, limits.wiring_bits, &plan.storage, i as usize);
                let index = plan.storage.by_call@[i]->Some_0 as int;
                let device = vm.storage_model()[index];
                assert(storage[index] == device.wiring_model());
                storage_call_row_bounds(&plan.storage.instances@[index], flat, storage[index],
                    netlist.input_count as nat, netlist.gates@.len());
            }
            self.direct_source_read_row(checked, limits, plan, storage, gates, definitions, symbolic, flat);
            if plan.gate_by_call@[i].is_none() {
                let index = plan.storage.by_call@[i]->Some_0 as int;
                source_storage_row_matches(external, storage, &layout, &plan.storage.instances@[index],
                    direct_source_row(plan, gates, definitions, symbolic), flat, storage[index]);
            }
        };
        assert(direct_port_rows_match(plan, &netlist, storage, &layout, arguments, definitions, pins));
        definitions
    }

    /// 直接配置した参照回路は、同じ型検査済みの定義と呼び出し行から構成される。
    pub closed spec fn clocked_direct_source_circuit(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, source: &SourceVmCircuit,
        layout: &SourceVmLayout,
    ) -> bool {
        exists|checked: ModuleCalls, plan: ClockedModuleEndpoints, order: Seq<int>,
            arguments: Seq<Vec<Vec<ClockedWireDriver>>>, definitions: Seq<SourceVmWire>|
            #[trigger] self.module_calls_result(owner, limits.width, Ok(Some(checked)))
            && #[trigger] self.endpoints_on_checked(&checked, limits.width, limits.wiring_bits, limits.gates, &plan)
            && #[trigger] gate_call_order(plan.gate_by_call@, checked.calls@.len() as int, order)
            && source_vm_links_resolved(plan._symbolic@.map_values(|driver: ClockedWireDriver|
                direct_source_link(&plan, layout.gates, driver)), definitions)
            && arguments.len() == checked.calls@.len()
            && (forall|i: int| 0 <= i < arguments.len() ==>
                self.call_wires_result(&checked, limits.width, &plan.ports, i as usize, Ok(#[trigger] arguments[i])))
            && layout.gates == order.map_values(|call: int| SourceGateId { instance: Seq::empty(), gate: checked.calls@[call].at })
            && layout.devices == direct_device_ids(&plan)
            && *layout == source_vm_layout_for_orders(layout.gates, layout.devices)
            && *source == #[trigger] direct_source_circuit(&plan, layout, order, arguments, definitions)
    }

    /// 直接コンパイルに成功した VM と、型検査済みソースの参照回路の対応を示す。
    ///
    /// ゲート、ラッチ、RAM の入力端子と、公開ポートの全ビットを対応付ける。
    /// この対応を使い、リセットから任意の有限入力列に対する公開出力を比較できる。
    pub proof fn clocked_direct_source_layout(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
    ) -> (model: (SourceVmCircuit, SourceVmLayout, Seq<ClockedStorageInputs>))
        requires self.can_resolve(), self.clocked_module_vm_wiring(owner, limits, compiled),
        ensures
            self.clocked_direct_source_circuit(owner, limits, &model.0, &model.1),
            source_vm_wiring_valid(&model.0),
            compiled.vm.layout_matches(compiled.vm.netlist_model(), model.0.input_count, model.2),
            source_vm_layout_matches(&model.0, &compiled.vm.netlist_model(), model.2, &model.1),
    {
        let (gates, devices) = self.clocked_direct_source_id_order(owner, limits, compiled);
        let (checked, plan, network, order) =
            choose|checked: ModuleCalls, plan: ClockedModuleEndpoints, network: ClockedModuleNetwork, order: Seq<int>| {
                &&& #[trigger] self.module_calls_result(owner, limits.width, Ok(Some(checked)))
                &&& #[trigger] self.endpoints_on_checked(&checked, limits.width, limits.wiring_bits, limits.gates, &plan)
                &&& #[trigger] self.network_wiring_on_checked(limits, &checked, &plan, &network)
                &&& self.network_vm_on_reset(&network, limits.state_bits, compiled)
                &&& #[trigger] gate_call_order(plan.gate_by_call@, checked.calls@.len() as int, order)
                &&& order.len() == plan.gate_count
                &&& gates == order.map_values(|call: int| SourceGateId { instance: Seq::empty(), gate: checked.calls@[call].at })
                &&& devices == direct_device_ids(&plan)
            };
        let netlist = network.circuit.netlist_model();
        let storage = network.storage@;
        let placed = plan.storage.instances@;
        let external = plan.ports.inputs.total_bits_model();
        let layout = source_vm_layout_for_orders(gates, devices);
        let (arguments, pins) = choose|arguments: Seq<Vec<Vec<ClockedWireDriver>>>, pins: Seq<Vec<Wire>>| {
            &&& #[trigger] self.vm_calls_bound(limits, &checked, &plan, arguments, pins, netlist.gates@, storage)
            &&& pins.len() == checked.calls@.len()
            &&& netlist.gates@.len() == plan.gate_count && storage.len() == placed.len()
            &&& netlist.input_count == plan.storage.augmented_inputs
            &&& super::resolved_bits(super::row_model(plan.ports.drivers@), plan.definitions@, netlist.outputs@)
        };
        self.direct_gate_call_order(&checked, &plan, limits.width, limits.wiring_bits, limits.gates);
        reveal(UseAliases::vm_calls_bound);
        self.direct_storage_widths_on_plan(&checked, limits, &plan, &netlist, storage, arguments, pins);
        self.placed_storage_width_evidence(&checked, limits.width, external, limits.wiring_bits, &plan.storage, storage);
        let definitions = self.direct_source_ports_on_plan(&checked, limits, &plan, &compiled.vm,
            netlist, storage, gates, arguments, pins);
        let source = direct_source_circuit(&plan, &layout, order, arguments, definitions);
        gates.to_set_ensures();
        devices.to_set_ensures();
        assert forall|i: int| 0 <= i < gates.len() implies {
            let original = source.gates[gates[i]];
            let flat = #[trigger] netlist.gates@[i];
            &&& source_vm_terminal_pair(external, storage, &layout, original.left, flat.left)
            &&& source_vm_terminal_pair(external, storage, &layout, original.right, flat.right)
        } by {
            let id = gates[i];
            assert(gates[layout.gate_index[id]] == id);
            assert(layout.gate_index[id] == i);
            let call = order[i];
            assert(plan.gate_by_call@[call] == Some(i as usize));
            assert(i < plan.gate_count);
            assert(pins[call]@.len() == 2);
        };
        assert forall|i: int| 0 <= i < devices.len() implies {
            let flat = #[trigger] storage[i];
            &&& flat.data@.len() > 0
            &&& source_vm_storage_pair(external, storage, &layout, source.storage[devices[i]], flat)
        } by {
            let id = devices[i];
            assert(devices[layout.device_index[id]] == id);
            assert(layout.device_index[id] == i);
            let call = self.storage_layout_call_for_instance(&checked, limits.width, external, limits.wiring_bits, &plan.storage, i);
            self.storage_layout_call(&checked, limits.width, external, limits.wiring_bits, &plan.storage, call as usize);
            assert(plan.gate_by_call@[call].is_none());
            let flat = pins[call]@;
            assert(placed[i].storage_inputs_match(flat, Some(storage[i])));
            placed[i].storage_input_rows_evidence(flat, storage[i]);
        };
        source_vm_layout_from_pairs(&source, &netlist, storage, gates, devices);
        assert(arguments.len() == checked.calls@.len());
        assert forall|i: int| 0 <= i < arguments.len() implies
            self.call_wires_result(&checked, limits.width, &plan.ports, i as usize, Ok(#[trigger] arguments[i])) by {
            assert(i < pins.len());
            assert(super::resolved_bits(super::row_model(arguments[i]@), plan.definitions@, pins[i]@));
        };
        assert(layout == source_vm_layout_for_orders(layout.gates, layout.devices));
        assert(self.clocked_direct_source_circuit(owner, limits, &source, &layout));
        (source, layout, storage)
    }

    /// 直接コンパイルした VM の公開出力が、リセットから全 tick でソースの実行と一致することを示す。
    pub proof fn clocked_direct_source_trace(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    ) -> (reference: (SourceVmCircuit, SourceVmLayout, Seq<SourceVmFrame>))
        requires
            self.can_resolve(), self.clocked_module_vm_wiring(owner, limits, compiled),
            clocked_vm_trace(inputs, states, outputs), states[0].same_layout(&compiled.vm),
        ensures
            self.clocked_direct_source_circuit(owner, limits, &reference.0, &reference.1),
            source_vm_wiring_valid(&reference.0),
            source_vm_trace(&reference.0, inputs, reference.2),
            reference.2.map_values(|frame: SourceVmFrame| frame.outputs) == outputs,
            reference.2 == Seq::new(outputs.len(), |i: int| SourceVmFrame {
                state: source_vm_state_projection(&states[i], &reference.1), outputs: outputs[i],
            }),
    {
        let (source, layout, storage) = self.clocked_direct_source_layout(owner, limits, compiled);
        let initial = &states[0];
        initial.reset_snapshot(outputs[0]);
        initial.preserve_layout_evidence(&compiled.vm, compiled.vm.netlist_model(), source.input_count, storage);
        let frames = source_vm_project_trace(&source, inputs, states, outputs, storage, &layout);
        (source, layout, frames)
    }
}

} // verus!
