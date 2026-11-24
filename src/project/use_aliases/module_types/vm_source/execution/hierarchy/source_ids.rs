//! ソース上の呼び出し経路を、階層展開後の素子の添字に対応付ける。

use super::{
    ClockedFunctionTemplate, ClockedHierarchy, ClockedModuleNetwork, ClockedModuleVm, ClockedModuleVmLimits,
    HierarchyWiring, ModuleBodyPosition, ModuleCalls, PartitionArea, UseAliases, boundary_position,
    call_interval_matches, call_partition_matches, function_target, partition_owner,
};
use crate::netlist::{
    SourceDeviceId, SourceGateId, source_gate_belongs_to_call, source_gate_positions_distinct, source_gate_under,
    source_gate_under_distinct, source_trace_layout_counts,
};
use crate::project::DefinitionPosition;
use vstd::prelude::*;

verus! {

/// 子のネットリストと状態素子の配列順に並べたソース ID。
pub(super) struct HierarchySourceIds {
    pub gates: Seq<SourceGateId>,
    pub devices: Seq<SourceDeviceId>,
}

pub(super) open spec fn source_device_under(site: DefinitionPosition, child: SourceDeviceId) -> SourceDeviceId {
    SourceDeviceId { instance: seq![site] + child.instance, call: child.call }
}

spec fn source_device_belongs_to_call(site: DefinitionPosition, device: SourceDeviceId) -> bool {
    if device.instance.len() == 0 { device.call == site } else { device.instance[0] == site }
}

proof fn source_device_under_distinct(site: DefinitionPosition, a: SourceDeviceId, b: SourceDeviceId)
    requires a != b,
    ensures source_device_under(site, a) != source_device_under(site, b),
{
    let left = source_device_under(site, a);
    let right = source_device_under(site, b);
    assert(left.instance.skip(1) =~= a.instance);
    assert(right.instance.skip(1) =~= b.instance);
}

spec fn children_follow_calls(wiring: &HierarchyWiring, children: Seq<Option<HierarchySourceIds>>) -> bool {
    &&& children.len() == wiring.routines.len()
    &&& forall|call: int| 0 <= call < children.len() ==> match ((#[trigger] wiring.routines[call]), children[call]) {
        (Some(routine), Some(ids)) => ids.gates.len() == routine.callee.gates@.len()
            && ids.devices.len() == routine.devices.len()
            && routine.gates.start + ids.gates.len() == routine.gates.end
            && routine.storage.start + ids.devices.len() == routine.storage.end
            && ids.gates.no_duplicates() && ids.devices.no_duplicates(),
        (None, None) => true,
        _ => false,
    }
}

spec fn owning_call(wiring: &HierarchyWiring, area: PartitionArea, index: nat) -> int {
    choose|i: int| 0 <= i < wiring.routines.len()
        && boundary_position(wiring.boundaries[i], area) <= index
        && index < #[trigger] boundary_position(wiring.boundaries[i + 1], area)
}

proof fn owner_is_partition_call(wiring: &HierarchyWiring, area: PartitionArea, index: nat)
    requires
        call_partition_matches(wiring.boundaries, wiring.routines, wiring.primitives, wiring.boundaries.last()),
        index < boundary_position(wiring.boundaries.last(), area),
    ensures ({
        let call = owning_call(wiring, area, index);
        &&& 0 <= call < wiring.routines.len()
        &&& boundary_position(wiring.boundaries[call], area) <= index
        &&& index < boundary_position(wiring.boundaries[call + 1], area)
        &&& call_interval_matches(wiring.boundaries[call], wiring.boundaries[call + 1],
            wiring.routines[call], wiring.primitives[call])
    }),
{
    reveal(call_partition_matches);
    let found = partition_owner(wiring.boundaries, wiring.routines, wiring.primitives, area, index, wiring.routines.len() as int);
    assert(boundary_position(wiring.boundaries[found], area) <= index
        < boundary_position(wiring.boundaries[found + 1], area));
    let call = owning_call(wiring, area, index);
    assert(call == found);
}

spec fn parent_gate_id(
    checked: &ModuleCalls, wiring: &HierarchyWiring, children: Seq<Option<HierarchySourceIds>>, index: nat,
) -> SourceGateId {
    let call = owning_call(wiring, PartitionArea::Gate, index);
    let at = checked.calls@[call].at;
    match children[call] {
        Some(child) => source_gate_under(seq![at], child.gates[index - wiring.boundaries[call].gates]),
        None => SourceGateId { instance: Seq::empty(), gate: at },
    }
}

spec fn device_owner(wiring: &HierarchyWiring, index: nat) -> int {
    if index < wiring.direct_devices {
        owning_call(wiring, PartitionArea::DirectStorage, index)
    } else {
        owning_call(wiring, PartitionArea::ChildStorage, (index - wiring.direct_devices) as nat)
    }
}

spec fn parent_device_id(
    checked: &ModuleCalls, wiring: &HierarchyWiring, children: Seq<Option<HierarchySourceIds>>, index: nat,
) -> SourceDeviceId {
    let call = device_owner(wiring, index);
    let at = checked.calls@[call].at;
    if index < wiring.direct_devices {
        SourceDeviceId { instance: Seq::empty(), call: at }
    } else {
        source_device_under(at, children[call]->Some_0.devices[index - wiring.direct_devices - wiring.boundaries[call].child])
    }
}

spec fn selected_source_children(hierarchy: &ClockedHierarchy, node: int, orders: Seq<HierarchySourceIds>,
    functions: Map<(usize, usize), ClockedFunctionTemplate>,
) -> Seq<Option<HierarchySourceIds>> {
    let checked = hierarchy.modules@[node]->Some_0;
    let edges = hierarchy.graph@[node]@;
    Seq::new(checked.calls@.len(), |call: int|
        match edges[call] {
            Some(child) => Some(orders[hierarchy.rank@[child as int] as int]),
            None => match function_target(&checked, edges, call) {
                Some(key) => Some(HierarchySourceIds { gates: functions[key]._source@.1, devices: Seq::empty() }),
                None => None,
            },
        })
}

spec fn source_ids_match_network(ids: HierarchySourceIds, checked: &ModuleCalls, network: &ClockedModuleNetwork,
    children: Seq<Option<HierarchySourceIds>>,
) -> bool {
    let wiring = &network._hierarchy_wiring@->Some_0;
    &&& ids.gates.len() == network.circuit.netlist_model().gates@.len()
    &&& ids.devices.len() == network.storage@.len()
    &&& ids.gates.no_duplicates() && ids.devices.no_duplicates()
    &&& ids.gates == Seq::new(ids.gates.len(), |i: int| parent_gate_id(checked, wiring, children, i as nat))
    &&& ids.devices == Seq::new(ids.devices.len(), |i: int| parent_device_id(checked, wiring, children, i as nat))
}

#[verifier::opaque]
spec fn hierarchy_source_orders(hierarchy: &ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
    functions: Map<(usize, usize), ClockedFunctionTemplate>, orders: Seq<HierarchySourceIds>,
) -> bool {
    &&& orders.len() <= hierarchy.order@.len()
    &&& forall|rank: int| 0 <= rank < orders.len() ==> {
        let node = hierarchy.order@[rank] as int;
        let ids = #[trigger] orders[rank];
        hierarchy.modules@[node] matches Some(checked) ==> networks[node] matches Some(network)
            && source_ids_match_network(ids, &checked, &network,
                selected_source_children(hierarchy, node, orders.take(rank), functions))
    }
}

proof fn gate_owner_evidence(checked: &ModuleCalls, wiring: &HierarchyWiring,
    children: Seq<Option<HierarchySourceIds>>, index: nat)
    requires
        wiring.routines.len() == checked.calls@.len(),
        call_partition_matches(wiring.boundaries, wiring.routines, wiring.primitives, wiring.boundaries.last()),
        children_follow_calls(wiring, children),
        index < wiring.boundaries.last().gates,
    ensures ({
        let call = owning_call(wiring, PartitionArea::Gate, index);
        &&& 0 <= call < checked.calls@.len()
        &&& source_gate_belongs_to_call(checked.calls@[call].at, parent_gate_id(checked, wiring, children, index))
        &&& match children[call] {
            Some(child) => 0 <= index - wiring.boundaries[call].gates < child.gates.len()
                && child.gates.no_duplicates(),
            None => index == wiring.boundaries[call].gates,
        }
    }),
{
    owner_is_partition_call(wiring, PartitionArea::Gate, index);
    let call = owning_call(wiring, PartitionArea::Gate, index);
    let id = parent_gate_id(checked, wiring, children, index);
    if children[call].is_some() {
        assert(id.instance[0] == checked.calls@[call].at);
    }
}

proof fn device_owner_evidence(checked: &ModuleCalls, wiring: &HierarchyWiring,
    children: Seq<Option<HierarchySourceIds>>, index: nat)
    requires
        wiring.routines.len() == checked.calls@.len(),
        call_partition_matches(wiring.boundaries, wiring.routines, wiring.primitives, wiring.boundaries.last()),
        children_follow_calls(wiring, children),
        wiring.boundaries.last().direct == wiring.direct_devices,
        index < wiring.direct_devices + wiring.boundaries.last().child,
    ensures ({
        let call = device_owner(wiring, index);
        &&& 0 <= call < checked.calls@.len()
        &&& source_device_belongs_to_call(checked.calls@[call].at, parent_device_id(checked, wiring, children, index))
        &&& if index < wiring.direct_devices {
            children[call].is_none() && index == wiring.boundaries[call].direct
        } else {
            children[call] matches Some(child) &&
                0 <= index - wiring.direct_devices - wiring.boundaries[call].child < child.devices.len()
                && child.devices.no_duplicates()
        }
    }),
{
    if index < wiring.direct_devices {
        owner_is_partition_call(wiring, PartitionArea::DirectStorage, index);
    } else {
        owner_is_partition_call(wiring, PartitionArea::ChildStorage, (index - wiring.direct_devices) as nat);
        let id = parent_device_id(checked, wiring, children, index);
        assert(id.instance[0] == checked.calls@[device_owner(wiring, index)].at);
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 子の素子に呼び出し位置を付け、実際のゲート・状態素子順に並べる。
    ///
    /// 状態素子は直接呼び出した素子が先で、その後に子の素子が並ぶ。
    proof fn hierarchy_source_ids_on_network(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, checked: &ModuleCalls,
        network: &ClockedModuleNetwork, children: Seq<Option<HierarchySourceIds>>,
    ) -> (ids: HierarchySourceIds)
        requires
            self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
            self.hierarchy_network_wiring(checked, limits, network),
            children_follow_calls(&network._hierarchy_wiring@->Some_0, children),
        ensures source_ids_match_network(ids, checked, network, children),
    {
        reveal(call_partition_matches);
        let wiring = &network._hierarchy_wiring@->Some_0;
        let gates = Seq::new(network.circuit.netlist_model().gates@.len(), |i: int|
            parent_gate_id(checked, wiring, children, i as nat));
        let devices = Seq::new(network.storage@.len(), |i: int|
            parent_device_id(checked, wiring, children, i as nat));
        assert forall|i: int, j: int| 0 <= i < j < gates.len() implies (#[trigger] gates[i]) != (#[trigger] gates[j]) by {
            gate_owner_evidence(checked, wiring, children, i as nat);
            gate_owner_evidence(checked, wiring, children, j as nat);
            let left = owning_call(wiring, PartitionArea::Gate, i as nat);
            let right = owning_call(wiring, PartitionArea::Gate, j as nat);
            if left == right {
                let child = children[left]->Some_0;
                let start = wiring.boundaries[left].gates;
                assert(child.gates[i - start] != child.gates[j - start]);
                source_gate_under_distinct(seq![checked.calls@[left].at], child.gates[i - start], child.gates[j - start]);
            } else if left < right {
                self.module_call_sites_distinct(owner, limits.width, checked, left, right);
            } else {
                self.module_call_sites_distinct(owner, limits.width, checked, right, left);
            }
        };
        assert forall|i: int, j: int| 0 <= i < j < devices.len() implies (#[trigger] devices[i]) != (#[trigger] devices[j]) by {
            device_owner_evidence(checked, wiring, children, i as nat);
            device_owner_evidence(checked, wiring, children, j as nat);
            let left = device_owner(wiring, i as nat);
            let right = device_owner(wiring, j as nat);
            if left == right {
                let child = children[left]->Some_0;
                let start = wiring.direct_devices + wiring.boundaries[left].child;
                assert(child.devices[i - start] != child.devices[j - start]);
                source_device_under_distinct(checked.calls@[left].at, child.devices[i - start], child.devices[j - start]);
            } else if left < right {
                self.module_call_sites_distinct(owner, limits.width, checked, left, right);
            } else {
                self.module_call_sites_distinct(owner, limits.width, checked, right, left);
            }
        };
        HierarchySourceIds { gates, devices }
    }

    /// 選んだ関数展開が持つソース上のゲート順を、その呼び出しに使う。
    proof fn function_source_ids(&self, key: (usize, usize), limits: ClockedModuleVmLimits,
        template: &ClockedFunctionTemplate)
        requires self.clocked_function_template_matches(key, limits.width, limits.wiring_bits, limits.gates, template),
        ensures
            template._source@.1.len() == template.circuit.netlist_model().gates@.len(),
            template._source@.1.no_duplicates(),
    {
        self.clocked_function_template_evidence(key, limits.width, limits.wiring_bits, limits.gates, template);
        let (source, order, index) = template._source@;
        let flat = template.circuit.netlist_model();
        source_trace_layout_counts(&source, &flat, order, index);
        assert forall|i: int, j: int| 0 <= i < j < order.len() implies (#[trigger] order[i]) != (#[trigger] order[j]) by {
            source_gate_positions_distinct(&source, &flat, order, index, i, j);
        };
    }

    /// 依存先の ID を展開順に取り出し、親の素子順を一つずつ構成する。
    proof fn hierarchy_source_order_prefix(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
        end: int, count: int,
    ) -> (orders: Seq<HierarchySourceIds>)
        requires
            self.can_resolve(), self.clocked_hierarchy_matches(owner, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, end, networks, functions),
            self.clocked_functions_match(functions, limits.width, limits.wiring_bits, limits.gates),
            0 <= count <= end <= hierarchy.order@.len(),
        ensures orders.len() == count, hierarchy_source_orders(hierarchy, networks, functions, orders),
        decreases count,
    {
        reveal(hierarchy_source_orders);
        if count == 0 { return Seq::empty(); }
        let rank = count - 1;
        let before = self.hierarchy_source_order_prefix(owner, limits, hierarchy, networks, functions, end, rank);
        self.clocked_hierarchy_evidence(owner, limits.width, hierarchy);
        reveal(UseAliases::hierarchy_templates_through);
        let node = hierarchy.order@[rank] as int;
        assert(hierarchy.rank@[node] == rank);
        let ids = if let Some(checked) = hierarchy.modules@[node] {
            let network = networks[node]->Some_0;
            let wiring = &network._hierarchy_wiring@->Some_0;
            let edges = hierarchy.graph@[node]@;
            let children = selected_source_children(hierarchy, node, before, functions);
            reveal(UseAliases::network_uses_selected_templates);
            reveal(call_partition_matches);
            assert(children_follow_calls(wiring, children)) by {
                assert forall|call: int| 0 <= call < children.len()
                    implies match ((#[trigger] wiring.routines[call]), children[call]) {
                        (Some(routine), Some(child)) => child.gates.len() == routine.callee.gates@.len()
                            && child.devices.len() == routine.devices.len()
                            && routine.gates.start + child.gates.len() == routine.gates.end
                            && routine.storage.start + child.devices.len() == routine.storage.end
                            && child.gates.no_duplicates() && child.devices.no_duplicates(),
                        (None, None) => true,
                        _ => false,
                    } by {
                    self.clocked_hierarchy_edge(owner, limits.width, hierarchy, node, call);
                    if let Some(routine) = wiring.routines[call] {
                        assert(Self::routine_uses_selected_template(&checked, edges, networks, functions, call,
                            routine.callee, routine.inputs, routine.layout, routine.devices));
                        super::placement_model::placed_routine_evidence(wiring.routines, network.circuit.netlist_model().gates@,
                            network.storage@.skip(wiring.direct_devices as int), wiring.first_child_input,
                            network.circuit.netlist_model().input_count, call);
                        if let Some(child) = edges[call] {
                            let child_rank = hierarchy.rank@[child as int] as int;
                            assert(hierarchy.order@[child_rank] == child);
                            let child_ids = before[child_rank];
                            let target = networks[child as int]->Some_0;
                            assert(source_ids_match_network(child_ids, &hierarchy.modules@[child as int]->Some_0, &target,
                                selected_source_children(hierarchy, child as int, before.take(child_rank), functions)));
                        } else {
                            let key = function_target(&checked, edges, call)->Some_0;
                            let template = functions[key];
                            self.function_source_ids(key, limits, &template);
                        }
                    } else {
                        reveal(UseAliases::hierarchy_public_wiring);
                        assert(!(checked.calls@[call].inputs.ports.signature.target is Routine));
                        assert(edges[call].is_none());
                        assert(function_target(&checked, edges, call).is_none());
                    }
                };
            };
            self.hierarchy_source_ids_on_network(hierarchy.positions@[node], limits, &checked, &network, children)
        } else {
            HierarchySourceIds { gates: Seq::empty(), devices: Seq::empty() }
        };
        let after = before.push(ids);
        assert forall|i: int| 0 <= i < after.len() implies {
            let at = hierarchy.order@[i] as int;
            let item = #[trigger] after[i];
            hierarchy.modules@[at] matches Some(checked) ==> networks[at] matches Some(network)
                && source_ids_match_network(item, &checked, &network,
                    selected_source_children(hierarchy, at, after.take(i), functions))
        } by {
            if i < rank {
                assert(after[i] == before[i]);
                assert(after.take(i) =~= before.take(i));
            } else {
                assert(after.take(i) =~= before);
            }
        };
        after
    }

    /// 階層の各宣言と関数から得た素子 ID が、ルート VM の配列順に並ぶことを表す。
    pub closed spec fn clocked_hierarchy_source_ids(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        gates: Seq<SourceGateId>, devices: Seq<SourceDeviceId>,
    ) -> bool {
        exists|hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
            functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int, orders: Seq<HierarchySourceIds>|
            #[trigger] self.hierarchy_compilation_snapshot(owner, limits, compiled, hierarchy, networks, functions, end)
            && #[trigger] hierarchy_source_orders(&hierarchy, networks, functions, orders)
            && orders.len() == end
            && gates == orders[end - 1].gates && devices == orders[end - 1].devices
    }

    /// 階層コンパイルが作った VM の全素子を、ソースの呼び出し経路と位置で区別する。
    ///
    /// 列の添字は VM の素子順と一致し、同じ子を複数回呼び出しても ID は重ならない。
    pub proof fn clocked_hierarchy_source_id_order(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
    ) -> (ids: (Seq<SourceGateId>, Seq<SourceDeviceId>))
        requires self.can_resolve(), self.clocked_module_hierarchy_vm(owner, limits, compiled),
        ensures
            self.clocked_hierarchy_source_ids(owner, limits, compiled, ids.0, ids.1),
            ids.0.len() == compiled.vm.netlist_model().gates@.len(),
            ids.1.len() == compiled.vm.storage_model().len(),
            ids.0.no_duplicates() && ids.1.no_duplicates(),
    {
        let (hierarchy, networks, functions, end) =
            choose|hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
                functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int|
                #[trigger] self.hierarchy_compilation_snapshot(owner, limits, compiled, hierarchy, networks, functions, end);
        let orders = self.hierarchy_source_order_prefix(owner, limits, &hierarchy, networks, functions, end, end);
        reveal(hierarchy_source_orders);
        let root = orders[end - 1];
        assert(hierarchy.order@[end - 1] == 0);
        assert(self.clocked_hierarchy_source_ids(owner, limits, compiled, root.gates, root.devices));
        (root.gates, root.devices)
    }
}

} // verus!
