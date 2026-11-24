//! 子を先に展開し、各呼び出しに独立したゲートと状態出力の区間を割り当てる。

use super::super::super::{ClockedModuleOutputs, ClockedStorageLayout, ClockedStorageLayoutError, ClockedStoragePlacement,
    ClockedWireDriver, clocked_source::ClockedHierarchy, copy_location};
use super::super::super::clocked_source::function_templates::FunctionTemplates;
#[cfg(verus_only)]
use super::super::super::clocked_source::function_templates::{function_target, function_templates_cover};
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
use crate::netlist::{clocked_stateful_arguments, clocked_storage_output_width, instance_outputs_match};
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

fn call_site<'p, 'a>(checked: &ModuleCalls<'p, 'a>, call: usize) -> (site: LocatedName<'p, 'a>)
    requires call < checked.calls@.len(),
    ensures site.source == checked.calls@[call as int].inputs.ports.signature.source
        && site.span == checked.calls@[call as int].inputs.ports.signature.call.span,
{
    let signature = &checked.calls[call].inputs.ports.signature;
    LocatedName { source: signature.source, span: signature.call.span.start..signature.call.span.end }
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

    spec fn hierarchy_network_ports(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
    ) -> bool {
        exists|ports: ClockedModuleOutputs|
            #[trigger] self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(ports))
            && network.inputs == ports.inputs && network.outputs == ports.outputs
    }

    /// VM の公開ポートが階層のルート宣言に対応し、組み立てたネットワークから初期化されることを表す。
    pub closed spec fn clocked_module_hierarchy_vm(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, vm: &ClockedModuleVm,
    ) -> bool {
        exists|hierarchy: ClockedHierarchy, network: ClockedModuleNetwork|
            #[trigger] self.clocked_hierarchy_matches(owner, limits.width, &hierarchy)
            && #[trigger] self.network_vm_on_reset(&network, limits.state_bits, vm)
            && hierarchy.modules@[0].is_some()
            && self.hierarchy_network_ports(&hierarchy.modules@[0]->Some_0, limits, &network)
            && network.circuit.netlist_model().gates@.len() <= limits.gates
            && network.circuit.netlist_model().input_count <= limits.wiring_bits
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
        while index < hierarchy.order.len()
            invariant
                self.can_resolve(), self.clocked_hierarchy_matches(owner, limits.width, &hierarchy),
                obeys_cmp::<(usize, usize)>(),
                self.clocked_functions_match(functions@, limits.width, limits.wiring_bits, limits.gates),
                index <= hierarchy.order@.len(), networks@.len() == count == hierarchy.positions@.len(),
                forall|i: int| 0 <= i < index && hierarchy.modules@[hierarchy.order@[i] as int].is_some() ==>
                    (#[trigger] networks@[hierarchy.order@[i] as int]).is_some()
                    && self.hierarchy_network_ports(&hierarchy.modules@[hierarchy.order@[i] as int]->Some_0,
                        limits, &networks@[hierarchy.order@[i] as int]->Some_0),
            decreases hierarchy.order@.len() - index,
        {
            proof { self.clocked_hierarchy_evidence(owner, limits.width, &hierarchy); }
            let node = hierarchy.order[index];
            if node >= count { return Err(ClockedModuleVmError::InstanceCount); }
            if let Some(checked) = &hierarchy.modules[node] {
                let position = hierarchy.positions[node];
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
                            ==> child < networks@.len() && networks@[child as int].is_some()) by {
                        if let Some(child) = hierarchy.graph@[node as int]@[call] {
                            self.clocked_hierarchy_edge(owner, limits.width, &hierarchy, node as int, call);
                            let rank = hierarchy.rank@[child as int];
                            assert(hierarchy.order@[rank as int] == child);
                            assert(networks@[hierarchy.order@[rank as int] as int].is_some());
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
                    return match self.initialize_clocked_network(network, limits.state_bits) {
                        Ok(vm) => {
                            assert(self.clocked_module_hierarchy_vm(owner, limits, &vm)) by {
                                assert(self.network_vm_on_reset(&source, limits.state_bits, &vm));
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
                networks.set(node, Some(network));
                assert forall|i: int| 0 <= i <= index && hierarchy.modules@[hierarchy.order@[i] as int].is_some()
                    implies (#[trigger] networks@[hierarchy.order@[i] as int]).is_some()
                        && self.hierarchy_network_ports(&hierarchy.modules@[hierarchy.order@[i] as int]->Some_0,
                            limits, &networks@[hierarchy.order@[i] as int]->Some_0) by {
                    if i < index {
                        let earlier = hierarchy.order@[i];
                        assert(hierarchy.rank@[earlier as int] == i);
                        assert(earlier != node);
                        assert(networks@[earlier as int] == previous[earlier as int]);
                    }
                };
            } else {
                assert(hierarchy.modules@[node as int].is_none());
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
                ==> child < networks@.len() && networks@[child as int].is_some()),
        ensures result matches Ok(network) ==> network.circuit.netlist_model().gates@.len() <= limits.gates
            && network.circuit.netlist_model().input_count <= limits.wiring_bits,
            result matches Ok(network) ==> self.hierarchy_network_ports(checked, limits, &network),
            self.clocked_functions_match(final(functions)@, limits.width, limits.wiring_bits, limits.gates),
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
                direct.augmented_inputs <= total_inputs <= limits.wiring_bits, total_gates <= limits.gates,
                obeys_cmp::<(usize, usize)>(),
                function_templates_cover(checked, edges@, functions@, count as int),
                self.clocked_functions_match(functions@, limits.width, limits.wiring_bits, limits.gates),
                forall|i: int| 0 <= i < edges@.len() ==> ((#[trigger] edges@[i]) matches Some(child)
                    ==> child < networks@.len() && networks@[child as int].is_some()),
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
                    states: total_inputs..total_inputs + width, arguments });
                total_inputs += width;
                total_gates += gates;
            } else if matches!(checked.calls[call].inputs.ports.signature.target, ModuleCallTarget::Nor) {
                if total_gates == limits.gates {
                    return Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::GateCapacity(call_site(checked, call))));
                }
                total_gates += 1;
            }
            placements.push(placement);
            call += 1;
        }
        let symbolic = self.bind_hierarchy_rows(owner, limits, checked, &ports, &direct, &placements)?;
        let definitions = self.resolve_hierarchy_rows(owner, limits, checked, &ports, &symbolic, &placements, total_inputs, total_gates)?;
        self.finish_hierarchy_network(owner, limits, checked, ports, direct, &placements, &symbolic, &definitions, total_inputs, total_gates)
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
        let ghost mut origins = Seq::<HierarchyRowOrigin>::empty();
        while slot < drivers.definitions.len()
            invariant
                self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
                self.module_drivers_result(owner, limits.width, Ok(Some(*drivers))),
                *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
                self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(*ports)),
                slot <= drivers.definitions@.len(), call <= calls@.len() == checked.calls@.len(),
                slot == origins.len(),
                forall|i: int| 0 <= i < slot ==> #[trigger]
                    self.hierarchy_row_matches(checked, ports, calls@, symbolic@, i, origins[i]),
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
                }
                let port = drivers.definitions[slot].result_index;
                let port_count = placement.outputs.ranges().len();
                if port >= port_count { return Err(ClockedModuleVmError::InstanceCount); }
                if port + 1 == port_count {
                    gates = placement.gates.end;
                    call += 1;
                }
            } else {
                if call >= calls.len() || !self.direct_slot(owner, limits.width, checked, drivers, slot, call) {
                    return Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::Unsupported(
                        self.source_driver_location(owner, limits.width, drivers, slot))));
                }
                if matches!(checked.calls[call].inputs.ports.signature.target, ModuleCallTarget::Nor) {
                    if width != 1 || gates >= limits.gates { return Err(ClockedModuleVmError::InstanceCount); }
                    symbolic.push(ClockedWireDriver::Terminal(Wire::Gate(gates)));
                    gates += 1;
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
                        decreases width - bit,
                    {
                        let Some(wire) = placement.output_wire(bit) else { return Err(ClockedModuleVmError::InstanceCount); };
                        symbolic.push(ClockedWireDriver::Terminal(wire));
                        assert(symbolic@.take(before.len() as int) =~= before);
                        bit += 1;
                    }
                }
                proof {
                    let origin = HierarchyRowOrigin::Call(call);
                    origins = previous.push(origin);
                    assert(self.hierarchy_row_matches(checked, ports, calls@, symbolic@, slot as int, origin)) by {
                        reveal(UseAliases::hierarchy_row_matches);
                    };
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
        ensures result matches Ok(definitions) ==> clocked_wires_match(symbolic.bits@, definitions@),
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

    fn finish_hierarchy_network(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, checked: &ModuleCalls<'p, 'a>,
        ports: ClockedModuleOutputs, direct: ClockedStorageLayout<'p, 'a>,
        calls: &[Option<CallPlacement<'_, 'p, 'a>>], _rows: &HierarchyRows, definitions: &[Wire], total_inputs: usize, total_gates: usize,
    ) -> (result: Result<ClockedModuleNetwork<'p, 'a>, ClockedModuleVmError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(ports)),
            calls@.len() == checked.calls@.len(),
            total_inputs <= limits.wiring_bits, total_gates <= limits.gates,
            clocked_wires_match(_rows.bits@, definitions@),
            forall|i: int| 0 <= i < _rows._origins@.len() ==> #[trigger]
                self.hierarchy_row_matches(checked, &ports, calls@, _rows.bits@, i, _rows._origins@[i]),
        ensures result matches Ok(network) ==> network.circuit.netlist_model().gates@.len() <= limits.gates
            && network.circuit.netlist_model().input_count <= limits.wiring_bits,
            result matches Ok(network) ==> self.hierarchy_network_ports(checked, limits, &network),
            !(result matches Err(ClockedModuleVmError::Hierarchy(_) | ClockedModuleVmError::ChildStateCapacity { .. })),
    {
        let mut gates = Vec::new();
        let mut storage = Vec::new();
        let mut child_storage: Vec<ClockedStorageInputs> = Vec::new();
        let mut child_sites = Vec::new();
        let mut next_state = direct.augmented_inputs;
        if gates.try_reserve_exact(total_gates).is_err() || storage.try_reserve_exact(direct.instances.len()).is_err() {
            return Err(ClockedModuleVmError::Allocation);
        }
        let mut call = 0;
        while call < calls.len()
            invariant
                call <= calls@.len() == checked.calls@.len(),
                self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
                self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(ports)),
                clocked_wires_match(_rows.bits@, definitions@),
                forall|i: int| 0 <= i < _rows._origins@.len() ==> #[trigger]
                    self.hierarchy_row_matches(checked, &ports, calls@, _rows.bits@, i, _rows._origins@[i]),
            decreases calls@.len() - call,
        {
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
                child_storage.append(&mut instance.storage);
                let external = placement.inputs.total_bits();
                let mut i = 0;
                while i < placement.storage_sites.len()
                    invariant i <= placement.storage_sites@.len(),
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
                    gates.push(NorGate { left: arguments[0], right: arguments[1] });
                } else {
                    if call >= direct.by_call.len() { return Err(ClockedModuleVmError::InstanceCount); }
                    let Some(instance) = direct.by_call[call] else { return Err(ClockedModuleVmError::InstanceCount); };
                    if instance != storage.len() || instance >= direct.instances.len() {
                        return Err(ClockedModuleVmError::InstanceCount);
                    }
                    let Some(inputs) = direct.instances[instance].storage_inputs(&arguments) else {
                        return Err(ClockedModuleVmError::CallWiring(call_site(checked, call)));
                    };
                    storage.push(inputs);
                }
            }
            call += 1;
        }
        if gates.len() != total_gates || next_state != total_inputs || storage.len() != direct.instances.len() {
            return Err(ClockedModuleVmError::InstanceCount);
        }
        let mut storage_sites = direct.instances;
        if storage.try_reserve(child_storage.len()).is_err() || storage_sites.try_reserve(child_sites.len()).is_err() {
            return Err(ClockedModuleVmError::Allocation);
        }
        storage.append(&mut child_storage);
        storage_sites.append(&mut child_sites);
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
        let network = ClockedModuleNetwork { inputs: ports.inputs, outputs: ports.outputs, circuit, storage, storage_sites };
        assert(self.hierarchy_network_ports(checked, limits, &network)) by {
            assert(self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(source_ports)));
        };
        Ok(network)
    }
}

} // verus!
