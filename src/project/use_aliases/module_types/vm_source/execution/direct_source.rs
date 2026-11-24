//! 直接呼び出しのソース位置を、ネットリスト上の素子順に対応付ける。

use super::{ClockedModuleEndpoints, ClockedModuleNetwork, ClockedModuleVm, ClockedModuleVmLimits, ModuleBodyPosition,
    ModuleCalls, UseAliases};
use crate::netlist::{
    ClockedStorage, ClockedStorageInputs, SourceDeviceId, SourceGateId, SourceVmWire, Wire,
    source_vm_layout_for_orders, source_vm_terminal_pair,
};
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
            &&& devices == plan.storage.instances@.map_values(|item: super::ClockedStoragePlacement| SourceDeviceId {
                instance: Seq::empty(), call: item.at,
            })
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
        let devices = placed.map_values(|item: super::ClockedStoragePlacement| SourceDeviceId {
            instance: Seq::empty(), call: item.at,
        });
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
                &&& devices == plan.storage.instances@.map_values(|item: super::ClockedStoragePlacement| SourceDeviceId {
                    instance: Seq::empty(), call: item.at,
                })
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
        self.direct_gate_call_order(&checked, &plan, limits.width, limits.wiring_bits, limits.gates);
        reveal(UseAliases::vm_calls_bound);
        assert forall|i: int| 0 <= i < wiring.len() implies
            (#[trigger] placed[i]).outputs.start + (#[trigger] wiring[i]).data@.len() == placed[i].outputs.end by {
            let call = self.storage_layout_call_for_instance(&checked, limits.width, external, limits.wiring_bits, &plan.storage, i);
            self.storage_layout_call(&checked, limits.width, external, limits.wiring_bits, &plan.storage, call as usize);
            assert(checked.calls@[call].inputs.ports.signature.target is StateElement);
            assert(plan.gate_by_call@[call].is_none());
            assert(placed[i].storage_inputs_match(pins[call]@, Some(wiring[i])));
            placed[i].storage_inputs_width(pins[call]@, wiring[i]);
        };
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
}

} // verus!
