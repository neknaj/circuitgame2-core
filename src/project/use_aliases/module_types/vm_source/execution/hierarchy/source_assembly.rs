//! 展開順に子の参照回路を構成し、ルート VM の実行と照合する。

use super::source_ids::{
    HierarchySourceIds, hierarchy_source_orders, selected_source_children,
};
use super::source_model::hierarchy_child_ids;
use super::source_widths::{HierarchyChildSource, hierarchy_child_sources_match};
use super::{
    ClockedFunctionTemplate, ClockedHierarchy, ClockedModuleCompilation, ClockedModuleNetwork, ClockedModuleVm, ClockedModuleVmLimits,
    ModuleBodyPosition, UseAliases, function_target,
};
use crate::netlist::{
    ClockedStorageInputs, ClockedVm, SourceDeviceId, SourceVmCircuit, SourceVmFrame, SourceVmLayout, clocked_vm_trace,
    source_vm_layout_for_orders, source_vm_layout_matches, source_vm_layout_port_evidence, source_vm_project_trace, source_vm_stateless_model,
    source_vm_state_projection, source_vm_trace, source_vm_wiring_valid,
};
use vstd::prelude::*;

verus! {

spec fn child_models(
    hierarchy: &ClockedHierarchy, node: int, sources: Seq<Option<HierarchyChildSource>>,
    functions: Map<(usize, usize), ClockedFunctionTemplate>,
) -> Seq<Option<HierarchyChildSource>> {
    let checked = hierarchy.modules@[node]->Some_0;
    let edges = hierarchy.graph@[node]@;
    Seq::new(checked.calls@.len(), |call: int| {
        match edges[call] {
            Some(child) => sources[hierarchy.rank@[child as int] as int],
            None => match function_target(&checked, edges, call) {
                Some(key) => {
                    let (model, gates, _) = functions[key]._source@;
                    Some(HierarchyChildSource { circuit: source_vm_stateless_model(&model),
                        ids: HierarchySourceIds { gates, devices: Seq::empty() } })
                },
                None => None,
            },
        }
    })
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    spec fn hierarchy_source_models(
        &self, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
        functions: Map<(usize, usize), ClockedFunctionTemplate>, orders: Seq<HierarchySourceIds>,
        sources: Seq<Option<HierarchyChildSource>>,
    ) -> bool {
        &&& sources.len() <= orders.len() <= hierarchy.order@.len()
        &&& forall|rank: int| 0 <= rank < sources.len() ==> {
            let node = hierarchy.order@[rank] as int;
            let source = #[trigger] sources[rank];
            match hierarchy.modules@[node] {
                Some(checked) => source matches Some(model) && networks[node] matches Some(network) && {
                    &&& model.ids == orders[rank]
                    &&& source_vm_wiring_valid(&model.circuit)
                    &&& source_vm_layout_matches(&model.circuit, &network.circuit.netlist_model(), network.storage@,
                        &source_vm_layout_for_orders(model.ids.gates, model.ids.devices))
                    &&& self.hierarchy_network_source_model(&checked, limits, &network,
                        child_models(hierarchy, node, sources.take(rank), functions), model)
                },
                None => source.is_none(),
            }
        }
    }

    /// 選択済みの関数と、先に処理した子モジュールから、このモジュールの各子回路を得る。
    proof fn hierarchy_child_models_ready(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
        end: int, rank: int, orders: Seq<HierarchySourceIds>, sources: Seq<Option<HierarchyChildSource>>,
    )
        requires
            self.clocked_hierarchy_matches(owner, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, end, networks, functions),
            self.clocked_functions_match(functions, limits.width, limits.wiring_bits, limits.gates),
            self.hierarchy_source_models(limits, hierarchy, networks, functions, orders, sources),
            sources.len() == rank && 0 <= rank < end <= hierarchy.order@.len(),
            (hierarchy.order@[rank] as int) < hierarchy.modules@.len(),
            hierarchy.modules@[hierarchy.order@[rank] as int].is_some(),
        ensures ({
            let node = hierarchy.order@[rank] as int;
            let network = networks[node]->Some_0;
            let children = child_models(hierarchy, node, sources, functions);
            &&& hierarchy_child_sources_match(&network._hierarchy_wiring@->Some_0, children)
            &&& hierarchy_child_ids(children) == selected_source_children(hierarchy, node, orders.take(rank), functions)
        }),
    {
        reveal(UseAliases::hierarchy_source_models);
        reveal(UseAliases::hierarchy_templates_through);
        reveal(UseAliases::network_uses_selected_templates);
        reveal(UseAliases::hierarchy_public_wiring);
        self.clocked_hierarchy_evidence(owner, limits.width, hierarchy);
        let node = hierarchy.order@[rank] as int;
        let checked = hierarchy.modules@[node]->Some_0;
        let network = networks[node]->Some_0;
        let wiring = &network._hierarchy_wiring@->Some_0;
        let edges = hierarchy.graph@[node]@;
        let children = child_models(hierarchy, node, sources, functions);
        let expected = selected_source_children(hierarchy, node, orders.take(rank), functions);
        let ids = hierarchy_child_ids(children);
        assert(hierarchy.rank@[node] == rank);
        assert forall|call: int| 0 <= call < children.len() implies {
            &&& ids[call] == expected[call]
            &&& match ((#[trigger] wiring.routines[call]), children[call]) {
                (Some(routine), Some(child)) => source_vm_layout_matches(&child.circuit, &routine.callee, routine.devices,
                    &source_vm_layout_for_orders(child.ids.gates, child.ids.devices)),
                (None, None) => true,
                _ => false,
            }
        } by {
            self.clocked_hierarchy_edge(owner, limits.width, hierarchy, node, call);
            if let Some(routine) = wiring.routines[call] {
                assert(Self::routine_uses_selected_template(&checked, edges, networks, functions, call,
                    routine.callee, routine.inputs, routine.layout, routine.devices));
                if let Some(target) = edges[call] {
                    let child_rank = hierarchy.rank@[target as int] as int;
                    assert(hierarchy.order@[child_rank] == target);
                    let child = sources[child_rank]->Some_0;
                    assert(children[call] == Some(child));
                    assert(child.ids == orders[child_rank]);
                } else {
                    assert(function_target(&checked, edges, call).is_some());
                    self.hierarchy_function_source(limits, &checked, &network, edges, networks, functions, call);
                }
            } else {
                assert(!(checked.calls@[call].inputs.ports.signature.target is Routine));
                assert(edges[call].is_none());
                assert(function_target(&checked, edges, call).is_none());
            }
        };
        assert(ids =~= expected) by {
            assert(ids.len() == expected.len());
            assert forall|call: int| 0 <= call < ids.len() implies (#[trigger] ids[call]) == expected[call] by {
                let _placed = wiring.routines[call];
                assert(ids[call] == expected[call]);
            };
        };
    }

    /// 依存順の先頭から、各モジュールの参照配線を構成する。
    proof fn hierarchy_source_model_prefix(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, hierarchy: &ClockedHierarchy,
        networks: Seq<Option<ClockedModuleNetwork>>, functions: Map<(usize, usize), ClockedFunctionTemplate>,
        end: int, orders: Seq<HierarchySourceIds>, count: int,
    ) -> (sources: Seq<Option<HierarchyChildSource>>)
        requires
            self.can_resolve(), self.clocked_hierarchy_matches(owner, limits.width, hierarchy),
            self.hierarchy_templates_through(hierarchy, limits, end, networks, functions),
            self.clocked_functions_match(functions, limits.width, limits.wiring_bits, limits.gates),
            hierarchy_source_orders(hierarchy, networks, functions, orders),
            orders.len() == end, 0 <= count <= end <= hierarchy.order@.len(),
        ensures sources.len() == count,
            self.hierarchy_source_models(limits, hierarchy, networks, functions, orders, sources),
        decreases count,
    {
        reveal(UseAliases::hierarchy_source_models);
        if count == 0 { return Seq::empty(); }
        let rank = count - 1;
        let before = self.hierarchy_source_model_prefix(owner, limits, hierarchy, networks, functions, end, orders, rank);
        let node = hierarchy.order@[rank] as int;
        let current = if let Some(checked) = hierarchy.modules@[node] {
            self.clocked_hierarchy_evidence(owner, limits.width, hierarchy);
            reveal(UseAliases::hierarchy_templates_through);
            let network = networks[node]->Some_0;
            let children = child_models(hierarchy, node, before, functions);
            self.hierarchy_child_models_ready(owner, limits, hierarchy, networks, functions, end, rank, orders, before);
            self.hierarchy_source_order_at(hierarchy, networks, functions, orders, rank);
            Some(self.compose_hierarchy_source_network(&checked, limits, &network, orders[rank], children))
        } else {
            None
        };
        let after = before.push(current);
        assert forall|i: int| 0 <= i < after.len() implies {
            let at = hierarchy.order@[i] as int;
            let source = #[trigger] after[i];
            match hierarchy.modules@[at] {
                Some(checked) => source matches Some(model) && networks[at] matches Some(network) && {
                    &&& model.ids == orders[i]
                    &&& source_vm_wiring_valid(&model.circuit)
                    &&& source_vm_layout_matches(&model.circuit, &network.circuit.netlist_model(), network.storage@,
                        &source_vm_layout_for_orders(model.ids.gates, model.ids.devices))
                    &&& self.hierarchy_network_source_model(&checked, limits, &network,
                        child_models(hierarchy, at, after.take(i), functions), model)
                },
                None => source.is_none(),
            }
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

    /// 選択された宣言と各呼び出しに基づくルート参照回路を表す。
    pub closed spec fn clocked_hierarchy_source_circuit(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        source: &SourceVmCircuit, layout: &SourceVmLayout,
    ) -> bool {
        exists|hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
            functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int,
            orders: Seq<HierarchySourceIds>, sources: Seq<Option<HierarchyChildSource>>| {
            &&& #[trigger] self.hierarchy_compilation_snapshot(owner, limits, compiled, hierarchy, networks, functions, end)
            &&& #[trigger] hierarchy_source_orders(&hierarchy, networks, functions, orders)
            &&& #[trigger] self.hierarchy_source_models(limits, &hierarchy, networks, functions, orders, sources)
            &&& sources.len() == orders.len() == end
            &&& sources[end - 1] matches Some(root)
                && root.circuit == *source && *layout == source_vm_layout_for_orders(root.ids.gates, root.ids.devices)
        }
    }

    /// 階層コンパイルの成功結果と、型検査済みソースの参照回路を対応付ける。
    pub proof fn clocked_hierarchy_source_layout(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
    ) -> (model: (SourceVmCircuit, SourceVmLayout, Seq<ClockedStorageInputs>))
        requires self.can_resolve(), self.clocked_module_hierarchy_vm(owner, limits, compiled),
        ensures
            self.clocked_hierarchy_source_circuit(owner, limits, compiled, &model.0, &model.1),
            source_vm_wiring_valid(&model.0),
            compiled.vm.layout_matches(compiled.vm.netlist_model(), model.0.input_count, model.2),
            source_vm_layout_matches(&model.0, &compiled.vm.netlist_model(), model.2, &model.1),
    {
        let (hierarchy, networks, functions, end) =
            choose|hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
                functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int|
                #[trigger] self.hierarchy_compilation_snapshot(owner, limits, compiled, hierarchy, networks, functions, end);
        self.hierarchy_source_layout_on_snapshot(owner, limits, compiled, hierarchy, networks, functions, end)
    }

    /// 保持した直接素子の位置と同じ階層展開から、参照回路を構成する。
    pub(in crate::project::use_aliases::module_types::vm_source::execution) proof fn hierarchy_vram_source_layout(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, root: &ClockedModuleCompilation,
    ) -> (model: (SourceVmCircuit, SourceVmLayout, Seq<ClockedStorageInputs>))
        requires self.can_resolve(), self.hierarchy_compilation_retains_storage(owner, limits, root),
        ensures
            self.clocked_hierarchy_source_circuit(owner, limits, &root.compiled, &model.0, &model.1),
            source_vm_wiring_valid(&model.0),
            root.compiled.vm.layout_matches(root.compiled.vm.netlist_model(), model.0.input_count, model.2),
            source_vm_layout_matches(&model.0, &root.compiled.vm.netlist_model(), model.2, &model.1),
            Self::source_layout_keeps_root_devices(&model.1, root),
    {
        let (hierarchy, networks, functions, end) =
            choose|hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
                functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int| {
                &&& #[trigger] self.hierarchy_compilation_snapshot(owner, limits, &root.compiled, hierarchy, networks, functions, end)
                &&& self.root_storage_on_network(limits, root, &networks[0]->Some_0)
                &&& root._checked == hierarchy.modules@[0]->Some_0
            };
        self.hierarchy_source_layout_on_snapshot(owner, limits, &root.compiled, hierarchy, networks, functions, end)
    }

    proof fn hierarchy_source_layout_on_snapshot(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        hierarchy: ClockedHierarchy, networks: Seq<Option<ClockedModuleNetwork>>,
        functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int,
    ) -> (model: (SourceVmCircuit, SourceVmLayout, Seq<ClockedStorageInputs>))
        requires self.can_resolve(), self.hierarchy_compilation_snapshot(owner, limits, compiled, hierarchy, networks, functions, end),
        ensures
            self.clocked_hierarchy_source_circuit(owner, limits, compiled, &model.0, &model.1),
            source_vm_wiring_valid(&model.0),
            compiled.vm.layout_matches(compiled.vm.netlist_model(), model.0.input_count, model.2),
            source_vm_layout_matches(&model.0, &compiled.vm.netlist_model(), model.2, &model.1),
            ({
                let network = networks[0]->Some_0;
                &&& network._direct_devices <= model.1.devices.len()
                &&& network._direct_devices <= network.storage_sites@.len()
                &&& forall|i: int| 0 <= i < network._direct_devices ==> (#[trigger] model.1.devices[i]) ==
                    (SourceDeviceId { instance: Seq::empty(), call: network.storage_sites@[i].at })
            }),
    {
        let orders = self.hierarchy_source_order_prefix(owner, limits, &hierarchy, networks, functions, end, end);
        let sources = self.hierarchy_source_model_prefix(owner, limits, &hierarchy, networks, functions, end, orders, end);
        reveal(UseAliases::hierarchy_source_models);
        let network = networks[0]->Some_0;
        let root = sources[end - 1]->Some_0;
        let layout = source_vm_layout_for_orders(root.ids.gates, root.ids.devices);
        assert(hierarchy.order@[end - 1] == 0);
        assert(self.clocked_hierarchy_source_circuit(owner, limits, compiled, &root.circuit, &layout));
        source_vm_layout_port_evidence(&root.circuit, &network.circuit.netlist_model(), network.storage@, &layout);
        self.hierarchy_source_order_at(&hierarchy, networks, functions, orders, end - 1);
        let checked = hierarchy.modules@[0]->Some_0;
        let children = selected_source_children(&hierarchy, 0, orders.take(end - 1), functions);
        assert(root.ids == orders[end - 1]);
        assert forall|i: int| 0 <= i < network._direct_devices implies (#[trigger] layout.devices[i]) ==
            (SourceDeviceId { instance: Seq::empty(), call: network.storage_sites@[i].at }) by {
            self.hierarchy_direct_device_id(&checked, limits, &network, children, root.ids, i);
        };
        (root.circuit, layout, network.storage@)
    }

    /// 階層コンパイル後の実行は、リセットから全 tick で参照回路と同じ公開出力を返す。
    pub proof fn clocked_hierarchy_source_trace(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, compiled: &ClockedModuleVm,
        inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    ) -> (reference: (SourceVmCircuit, SourceVmLayout, Seq<SourceVmFrame>))
        requires
            self.can_resolve(), self.clocked_module_hierarchy_vm(owner, limits, compiled),
            clocked_vm_trace(inputs, states, outputs), states[0].same_layout(&compiled.vm),
        ensures
            self.clocked_hierarchy_source_circuit(owner, limits, compiled, &reference.0, &reference.1),
            source_vm_wiring_valid(&reference.0),
            source_vm_trace(&reference.0, inputs, reference.2),
            reference.2.map_values(|frame: SourceVmFrame| frame.outputs) == outputs,
            reference.2 == Seq::new(outputs.len(), |i: int| SourceVmFrame {
                state: source_vm_state_projection(&states[i], &reference.1), outputs: outputs[i],
            }),
    {
        let (source, layout, storage) = self.clocked_hierarchy_source_layout(owner, limits, compiled);
        let initial = &states[0];
        initial.reset_snapshot(outputs[0]);
        initial.preserve_layout_evidence(&compiled.vm, compiled.vm.netlist_model(), source.input_count, storage);
        let frames = source_vm_project_trace(&source, inputs, states, outputs, storage, &layout);
        (source, layout, frames)
    }
}

} // verus!
