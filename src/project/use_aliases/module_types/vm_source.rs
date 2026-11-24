//! モジュールの直接呼び出しを、ゲートと状態素子の配線に対応付ける。

mod execution;
pub use execution::{ClockedModuleVm, ClockedModuleVmError, ClockedModuleVmLimits};

use super::{ClockedModuleOutputs, ClockedModuleOutputsError, ClockedStorageLayout, ClockedStorageLayoutError,
    ModuleCalls, ModuleCallsError, UseAliases};
use crate::netlist::Wire;
use crate::project::{LocatedName, ModuleBodyPosition, ModuleCallTarget, ModuleDrivers};
use alloc::vec::Vec;
#[cfg(verus_only)]
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence};

verus! {

/// モジュールの直接呼び出しと、定義の各ビットを駆動する配線。
#[derive(Debug)]
struct ClockedModuleEndpoints<'p, 'a> {
    /// 公開ポートの配置、定義の配置、公開出力の駆動元。
    ports: ClockedModuleOutputs,
    /// 呼び出し順に置いた状態素子と、増補入力の配置。
    storage: ClockedStorageLayout<'p, 'a>,
    /// 定義のビット順に並ぶ配線。状態素子の出力は増補入力の添字を持つ。
    definitions: Vec<Wire>,
    /// 呼び出し順のゲート番号。状態素子に対応する要素は `None`。
    gate_by_call: Vec<Option<usize>>,
    /// 基底 NOR の数。
    gate_count: usize,
}

/// 定義の配線を割り当てられなかった理由。
#[derive(Debug)]
pub enum ClockedEndpointError<'p, 'a> {
    /// モジュールの型または呼び出しの検査に失敗した。
    Calls(ModuleCallsError<'p, 'a>),
    /// 入出力または定義のビット配置に失敗した。
    Ports(ClockedModuleOutputsError<'p, 'a>),
    /// 状態素子を増補入力に配置できなかった。
    Storage(ClockedStorageLayoutError<'p, 'a>),
    /// 配置に必要な配列を確保できなかった。
    Allocation,
    /// 定義の範囲と平坦な定義列の長さが一致しない。
    Layout,
    /// 直接の基底 NOR、ラッチ、RAM の呼び出しとして展開できない定義または呼び出し。
    Unsupported(LocatedName<'p, 'a>),
    /// ゲート数の上限を超えた最初の定義。
    GateCapacity(LocatedName<'p, 'a>),
    /// 呼び出しが出力するビット数と、定義に割り当てられたビット数が異なる。
    Width {
        /// 定義の左辺の範囲。
        definition: LocatedName<'p, 'a>,
        /// 呼び出し先の出力に必要なビット数。
        produced: usize,
        /// 定義に割り当てられたビット数。
        allocated: usize,
    },
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn source_vm_direct_slot(&self, checked: &ModuleCalls, slot: int) -> bool {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        let row = checked.calls@[slot];
        let origin = drivers.origins@[slot];
        let target = drivers.definitions@[slot];
        let parsed = self.targets.project_model().circuits_model()[row.at.file as int];
        &&& 0 <= slot < checked.calls@.len()
        &&& origin.file == row.at.file && origin.entry == row.at.entry
        &&& target.result_index == 0 && row.at.reference == 0
        &&& target.definition == parsed.entry_ranges@[row.at.entry as int].definitions.start + row.at.definition
        &&& row.inputs.ports.signature.call.form == parsed.definitions@[target.definition as int].expression.start
        &&& (row.inputs.ports.signature.target is Nor || row.inputs.ports.signature.target is StateElement)
    }

    fn direct_slot(
        &self, _owner: ModuleBodyPosition, _limit: u64, checked: &ModuleCalls<'p, 'a>, drivers: &ModuleDrivers<'p, 'a>, slot: usize,
    ) -> (direct: bool)
        requires
            self.can_resolve(), self.module_calls_result(_owner, _limit, Ok(Some(*checked))),
            self.module_drivers_result(_owner, _limit, Ok(Some(*drivers))),
            *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
            slot < drivers.definitions@.len(),
        ensures direct == self.source_vm_direct_slot(checked, slot as int),
    {
        if slot >= checked.calls.len() { return false; }
        proof {
            self.module_driver_sites(_owner, _limit, *drivers, slot as int);
            self.module_calls_item_evidence(_owner, _limit, checked, slot as int);
            self.module_call_ports_evidence(checked.calls@[slot as int].at, _limit, checked.calls@[slot as int].inputs.ports);
            self.module_call_site_evidence(checked.calls@[slot as int].at, _limit, checked.calls@[slot as int].inputs.ports.signature);
        }
        let row = &checked.calls[slot];
        let origin = drivers.origins[slot];
        let target = &drivers.definitions[slot];
        if origin.file != row.at.file || origin.entry != row.at.entry || row.at.reference != 0 || target.result_index != 0 {
            return false;
        }
        let parsed = &self.targets.project().circuits()[row.at.file];
        let _source = row.inputs.ports.signature.source;
        let ghost model = parsed.build_model();
        proof {
            parsed_index_evidence(*_source, *parsed);
            build_entry_ranges_evidence(_source.text, &model, row.at.entry as int);
        }
        let defs = &parsed.entry_ranges[row.at.entry].definitions;
        if target.definition - defs.start != row.at.definition { return false; }
        proof { build_definition_scope_evidence(_source.text, &model, row.at.entry as int, target.definition as int); }
        let definition = &parsed.definitions[target.definition];
        row.inputs.ports.signature.call.form == definition.expression.start
            && matches!(row.inputs.ports.signature.target, ModuleCallTarget::Nor | ModuleCallTarget::StateElement { .. })
    }

    #[verifier::opaque]
    spec fn endpoint_prefix(
        &self, checked: &ModuleCalls, storage: &ClockedStorageLayout, ranges: Seq<Range<usize>>,
        definitions: Seq<Wire>, gates: Seq<Option<usize>>, cursors: Seq<usize>,
    ) -> bool {
        &&& gates.len() <= ranges.len()
        &&& cursors.len() == gates.len() + 1 && cursors[0] == 0
        &&& definitions.len() == if gates.len() == 0 { 0 } else { ranges[gates.len() - 1].end }
        &&& forall|slot: int| 0 <= slot < gates.len() ==> {
            let gate = #[trigger] gates[slot];
            let range = ranges[slot];
            &&& self.source_vm_direct_slot(checked, slot)
            &&& range.start == (if slot == 0 { 0 } else { ranges[slot - 1].end as int })
            &&& range.start < range.end <= definitions.len()
            &&& match gate {
                Some(gate) => {
                    &&& checked.calls@[slot].inputs.ports.signature.target is Nor
                    &&& gate == cursors[slot] && cursors[slot + 1] == gate + 1
                    &&& range.end == range.start + 1
                    &&& definitions[range.start as int] == Wire::Gate(gate)
                },
                None => storage.by_call@[slot] matches Some(instance) && instance < storage.instances@.len() && {
                    let outputs = storage.instances@[instance as int].outputs;
                    &&& cursors[slot + 1] == cursors[slot]
                    &&& range.end - range.start == outputs.end - outputs.start
                    &&& forall|bit: int| 0 <= bit < range.end - range.start ==>
                        #[trigger] definitions[range.start + bit] == Wire::Input((outputs.start + bit) as usize)
                },
            }
        }
    }

    fn bind_endpoint_blocks(
        &self, owner: ModuleBodyPosition, limit: u64, _capacity: usize, gate_limit: usize,
        checked: &ModuleCalls<'p, 'a>, ports: &ClockedModuleOutputs, storage: &ClockedStorageLayout<'p, 'a>,
    ) -> (result: Result<(Vec<Wire>, Vec<Option<usize>>, usize), ClockedEndpointError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*ports)),
            self.storage_on_checked(checked, limit, ports.inputs.total_bits_model(), _capacity, Ok(*storage)),
        ensures result matches Ok((definitions, gates, gate_count)) ==>
            definitions@.len() == ports.definitions.total_bits_model()
                && gates@.len() == checked.calls@.len() && gate_count <= gate_limit
                && (exists|cursors: Seq<usize>| #[trigger] self.endpoint_prefix(checked, storage,
                    ports.definitions.ranges_model(), definitions@, gates@, cursors)
                    && 0 < cursors.len() && cursors.last() == gate_count),
    {
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, limit, checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, checked.module.expressions);
            self.clocked_output_layouts(&checked.module, limit, _capacity, ports);
            self.clocked_definition_layout_evidence(&checked.module.expressions, limit, _capacity, &ports.definitions, 0);
        }
        let mut definitions = Vec::new();
        let mut gates = Vec::new();
        if definitions.try_reserve_exact(ports.definitions.total_bits()).is_err()
            || gates.try_reserve_exact(drivers.definitions.len()).is_err() {
            return Err(ClockedEndpointError::Allocation);
        }
        let mut gate_count = 0usize;
        let mut slot = 0usize;
        let ghost mut cursors = seq![0usize];
        assert(self.endpoint_prefix(checked, storage, ports.definitions.ranges_model(), definitions@, gates@, cursors)) by {
            reveal(UseAliases::endpoint_prefix);
        };
        while slot < drivers.definitions.len()
            invariant
                self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
                self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
                *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
                self.storage_on_checked(checked, limit, ports.inputs.total_bits_model(), _capacity, Ok(*storage)),
                slot == gates@.len() <= drivers.definitions@.len() == ports.definitions.ranges_model().len(),
                slot <= checked.calls@.len(), gate_count <= gate_limit, cursors.len() == slot + 1 && cursors.last() == gate_count,
                self.endpoint_prefix(checked, storage, ports.definitions.ranges_model(), definitions@, gates@, cursors),
            decreases drivers.definitions@.len() - slot,
        {
            if !self.direct_slot(owner, limit, checked, drivers, slot) {
                return Err(ClockedEndpointError::Unsupported(self.source_driver_location(owner, limit, drivers, slot)));
            }
            proof { self.storage_layout_call(checked, limit, ports.inputs.total_bits_model(), _capacity, storage, slot); }
            let Some(range) = ports.definitions.range(slot) else { unreachable!() };
            let width = range.end - range.start;
            if range.start != definitions.len() {
                return Err(ClockedEndpointError::Layout);
            }
            let ghost before = definitions@;
            let ghost prior_gates = gates@;
            let ghost prior_cursors = cursors;
            if let Some(instance) = storage.by_call[slot] {
                let placement = &storage.instances[instance];
                let produced = placement.outputs.end - placement.outputs.start;
                if produced != width {
                    return Err(ClockedEndpointError::Width {
                        definition: self.source_driver_location(owner, limit, drivers, slot), produced, allocated: width,
                    });
                }
                let mut bit = 0usize;
                while bit < width
                    invariant
                        bit <= width,
                        definitions@.len() == before.len() + bit, definitions@.take(before.len() as int) == before,
                        range.start == before.len() && range.end == range.start + width,
                        placement.outputs.start + width == placement.outputs.end,
                        forall|i: int| 0 <= i < bit ==> #[trigger] definitions@[range.start + i]
                            == Wire::Input((placement.outputs.start + i) as usize),
                    decreases width - bit,
                {
                    let Some(wire) = placement.output_wire(bit) else { unreachable!() };
                    let ghost pre = definitions@;
                    definitions.push(wire);
                    assert forall|i: int| 0 <= i <= bit implies #[trigger] definitions@[range.start + i]
                        == Wire::Input((placement.outputs.start + i) as usize) by {
                        if i < bit { assert(definitions@[range.start + i] == pre[range.start + i]); }
                    };
                    bit += 1;
                }
                gates.push(None);
            } else {
                if width != 1 {
                    return Err(ClockedEndpointError::Width {
                        definition: self.source_driver_location(owner, limit, drivers, slot), produced: 1, allocated: width,
                    });
                }
                if gate_count == gate_limit {
                    return Err(ClockedEndpointError::GateCapacity(self.source_driver_location(owner, limit, drivers, slot)));
                }
                definitions.push(Wire::Gate(gate_count));
                gates.push(Some(gate_count));
                gate_count += 1;
            }
            proof {
                cursors = cursors.push(gate_count);
                assert(definitions@.take(before.len() as int) =~= before);
                assert(gates@.take(slot as int) =~= prior_gates);
                assert(cursors.take(slot + 1) =~= prior_cursors);
                self.extend_endpoint_prefix(checked, storage, ports.definitions.ranges_model(),
                    before, prior_gates, prior_cursors, definitions@, gates@, cursors, slot as int);
            }
            slot += 1;
        }
        if slot < checked.calls.len() {
            let call = &checked.calls[slot].inputs.ports.signature;
            return Err(ClockedEndpointError::Unsupported(LocatedName {
                source: call.source, span: call.call.span.start..call.call.span.end,
            }));
        }
        if definitions.len() != ports.definitions.total_bits() {
            return Err(ClockedEndpointError::Layout);
        }
        Ok((definitions, gates, gate_count))
    }

    proof fn extend_endpoint_prefix(
        &self, checked: &ModuleCalls, storage: &ClockedStorageLayout, ranges: Seq<Range<usize>>,
        before: Seq<Wire>, prior_gates: Seq<Option<usize>>, prior_cursors: Seq<usize>,
        definitions: Seq<Wire>, gates: Seq<Option<usize>>, cursors: Seq<usize>, slot: int,
    )
        requires
            self.endpoint_prefix(checked, storage, ranges, before, prior_gates, prior_cursors),
            slot == prior_gates.len() < ranges.len(),
            self.source_vm_direct_slot(checked, slot),
            gates.len() == slot + 1 && gates.take(slot) == prior_gates,
            cursors.len() == slot + 2 && cursors.take(slot + 1) == prior_cursors,
            ranges[slot].start == before.len() < ranges[slot].end == definitions.len(),
            definitions.take(before.len() as int) == before,
            match gates[slot] {
                Some(gate) => {
                    &&& checked.calls@[slot].inputs.ports.signature.target is Nor
                    &&& gate == cursors[slot] && cursors[slot + 1] == gate + 1
                    &&& ranges[slot].end == ranges[slot].start + 1
                    &&& definitions[ranges[slot].start as int] == Wire::Gate(gate)
                },
                None => storage.by_call@[slot] matches Some(instance) && instance < storage.instances@.len() && {
                    let outputs = storage.instances@[instance as int].outputs;
                    let range = ranges[slot];
                    &&& cursors[slot + 1] == cursors[slot]
                    &&& range.end - range.start == outputs.end - outputs.start
                    &&& forall|bit: int| 0 <= bit < range.end - range.start ==>
                        #[trigger] definitions[range.start + bit] == Wire::Input((outputs.start + bit) as usize)
                },
            },
        ensures self.endpoint_prefix(checked, storage, ranges, definitions, gates, cursors),
    {
        reveal(UseAliases::endpoint_prefix);
        assert forall|i: int| 0 <= i < gates.len() implies {
            let gate = #[trigger] gates[i];
            let range = ranges[i];
            &&& self.source_vm_direct_slot(checked, i)
            &&& range.start == (if i == 0 { 0 } else { ranges[i - 1].end as int })
            &&& range.start < range.end <= definitions.len()
            &&& match gate {
                Some(gate) => {
                    &&& checked.calls@[i].inputs.ports.signature.target is Nor
                    &&& gate == cursors[i] && cursors[i + 1] == gate + 1
                    &&& range.end == range.start + 1
                    &&& definitions[range.start as int] == Wire::Gate(gate)
                },
                None => storage.by_call@[i] matches Some(instance) && instance < storage.instances@.len() && {
                    let outputs = storage.instances@[instance as int].outputs;
                    &&& cursors[i + 1] == cursors[i]
                    &&& range.end - range.start == outputs.end - outputs.start
                    &&& forall|bit: int| 0 <= bit < range.end - range.start ==>
                        #[trigger] definitions[range.start + bit] == Wire::Input((outputs.start + bit) as usize)
                },
            }
        } by {
            if i < slot {
                assert(gates[i] == prior_gates[i]);
                assert(cursors[i] == prior_cursors[i] && cursors[i + 1] == prior_cursors[i + 1]);
                assert forall|j: int| bit_in_slot(ranges, i, j) implies
                    #[trigger] definitions[j] == before[j] by {
                    assert(ranges[i].end <= before.len());
                };
            }
        };
    }

    spec fn endpoints_on_checked(
        &self, checked: &ModuleCalls, limit: u64, capacity: usize, gate_limit: usize, plan: &ClockedModuleEndpoints,
    ) -> bool {
        &&& self.outputs_on_checked(&checked.module, limit, capacity, Ok(plan.ports))
        &&& self.storage_on_checked(checked, limit, plan.ports.inputs.total_bits_model(), capacity, Ok(plan.storage))
        &&& plan.definitions@.len() == plan.ports.definitions.total_bits_model()
        &&& plan.gate_by_call@.len() == checked.calls@.len()
        &&& plan.gate_count <= gate_limit
        &&& exists|cursors: Seq<usize>| #[trigger] self.endpoint_prefix(checked, &plan.storage,
            plan.ports.definitions.ranges_model(), plan.definitions@, plan.gate_by_call@, cursors)
            && 0 < cursors.len() && cursors.last() == plan.gate_count
    }

    fn prepare_vm_endpoints(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, gate_limit: usize, checked: &ModuleCalls<'p, 'a>,
    ) -> (result: Result<ClockedModuleEndpoints<'p, 'a>, ClockedEndpointError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
        ensures result matches Ok(plan) ==> self.endpoints_on_checked(checked, limit, capacity, gate_limit, &plan),
    {
        proof { self.module_calls_type_evidence(owner, limit, checked); }
        let ports = match self.wire_clocked_outputs(owner, limit, capacity, &checked.module) {
            Ok(ports) => ports,
            Err(error) => return Err(ClockedEndpointError::Ports(error)),
        };
        let external = ports.inputs.total_bits();
        if external > capacity {
            return Err(ClockedEndpointError::Storage(ClockedStorageLayoutError::ExternalCapacity));
        }
        let storage = match self.place_clocked_storage(owner, checked, limit, external, capacity) {
            Ok(storage) => storage,
            Err(error) => return Err(ClockedEndpointError::Storage(error)),
        };
        let (definitions, gate_by_call, gate_count) = self.bind_endpoint_blocks(owner, limit, capacity, gate_limit, checked, &ports, &storage)?;
        Ok(ClockedModuleEndpoints { ports, storage, definitions, gate_by_call, gate_count })
    }


}

spec fn bit_in_slot(ranges: Seq<Range<usize>>, i: int, bit: int) -> bool {
    ranges[i].start <= bit < ranges[i].end
}

} // verus!
