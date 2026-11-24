//! モジュールの定義を、直接の配線、ゲート、状態素子に対応付ける。

mod execution;
pub use execution::{ClockedModuleVm, ClockedModuleVmError, ClockedModuleVmLimits};

use super::{ClockedModuleOutputs, ClockedModuleOutputsError, ClockedStorageLayout, ClockedStorageLayoutError,
    ClockedDriverBitsError, ClockedPlanError, ClockedWireDriver, ModuleCalls, ModuleCallsError, UseAliases,
    clocked_driver_bits, clocked_plan::{TerminalResolution, clocked_resolve, resolve_terminal_wires}};
#[cfg(verus_only)]
use super::{clocked_plan::clocked_resolution_result, clocked_driver_bits_result,
    driver_bits::clocked_whole_port_bits, selections::bound_type};
#[cfg(verus_only)]
use crate::project::{OutputDriver, PortDirection, StructureLayouts};
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
struct ClockedModuleEndpoints<'p, 'a> {
    /// 公開ポートの配置、定義の配置、公開出力の駆動元。
    ports: ClockedModuleOutputs,
    /// 呼び出し順に置いた状態素子と、増補入力の配置。
    storage: ClockedStorageLayout<'p, 'a>,
    /// 定義のビット順に並ぶ配線。状態素子の出力は増補入力の添字を持つ。
    definitions: Vec<Wire>,
    _symbolic: Ghost<Seq<ClockedWireDriver>>,
    _call_cursors: Ghost<Seq<usize>>,
    _gate_cursors: Ghost<Seq<usize>>,
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
    /// 信号名の直結や、基底 NOR、ラッチ、RAM の直接呼び出しとして展開できない定義または呼び出し。
    Unsupported(LocatedName<'p, 'a>),
    /// 右辺の信号をビット列に展開できなかった。
    AliasBits {
        /// 右辺の信号名の範囲。
        reference: LocatedName<'p, 'a>,
        /// 信号の配線を生成できなかった理由。
        reason: ClockedDriverBitsError,
    },
    /// 定義の駆動元が配置の範囲外だった。
    Driver(LocatedName<'p, 'a>),
    /// 直結が閉路を構成する。各要素は閉路の順に並べた右辺の参照位置。
    AliasCycle(Vec<LocatedName<'p, 'a>>),
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
    spec fn source_vm_direct_slot(&self, checked: &ModuleCalls, slot: int, call: int) -> bool {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        let row = checked.calls@[call];
        let origin = drivers.origins@[slot];
        let target = drivers.definitions@[slot];
        let parsed = self.targets.project_model().circuits_model()[row.at.file as int];
        &&& 0 <= call < checked.calls@.len()
        &&& origin.file == row.at.file && origin.entry == row.at.entry
        &&& target.result_index == 0 && row.at.reference == 0
        &&& target.definition == parsed.entry_ranges@[row.at.entry as int].definitions.start + row.at.definition
        &&& row.inputs.ports.signature.call.form == parsed.definitions@[target.definition as int].expression.start
        &&& (row.inputs.ports.signature.target is Nor || row.inputs.ports.signature.target is StateElement)
    }

    fn direct_slot(
        &self, _owner: ModuleBodyPosition, _limit: u64, checked: &ModuleCalls<'p, 'a>, drivers: &ModuleDrivers<'p, 'a>, slot: usize, call: usize,
    ) -> (direct: bool)
        requires
            self.can_resolve(), self.module_calls_result(_owner, _limit, Ok(Some(*checked))),
            self.module_drivers_result(_owner, _limit, Ok(Some(*drivers))),
            *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
            slot < drivers.definitions@.len(),
        ensures direct == self.source_vm_direct_slot(checked, slot as int, call as int),
    {
        if call >= checked.calls.len() { return false; }
        proof {
            self.module_driver_sites(_owner, _limit, *drivers, slot as int);
            self.module_calls_item_evidence(_owner, _limit, checked, call as int);
            self.module_call_ports_evidence(checked.calls@[call as int].at, _limit, checked.calls@[call as int].inputs.ports);
            self.module_call_site_evidence(checked.calls@[call as int].at, _limit, checked.calls@[call as int].inputs.ports.signature);
        }
        let row = &checked.calls[call];
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
    spec fn endpoint_row(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, storage: &ClockedStorageLayout,
        bits: Seq<ClockedWireDriver>, gates: Seq<Option<usize>>, slot: int,
        call: usize, next_call: usize, gate: usize, next_gate: usize,
    ) -> bool {
        let range = ports.definitions.ranges_model()[slot];
        let aliases = checked.module.expressions.typed.sources.aliases@;
        &&& 0 <= slot < aliases.len()
        &&& bits.len() == range.end - range.start
        &&& match aliases[slot] {
            Some(alias) => {
                &&& next_call == call && next_gate == gate
                &&& exists|wires: Vec<ClockedWireDriver>|
                    #[trigger] clocked_driver_bits_result(&ports.inputs, &ports.definitions, alias.driver, None, Ok(wires))
                    && wires@ == bits
            },
            None => {
                &&& self.source_vm_direct_slot(checked, slot, call as int)
                &&& call < gates.len() && next_call == call + 1
                &&& match gates[call as int] {
                    Some(index) => {
                        &&& checked.calls@[call as int].inputs.ports.signature.target is Nor
                        &&& index == gate && next_gate == gate + 1
                        &&& bits.len() == 1
                        &&& bits[0] == ClockedWireDriver::Terminal(Wire::Gate(gate))
                    },
                    None => storage.by_call@[call as int] matches Some(instance) && instance < storage.instances@.len() && {
                        let outputs = storage.instances@[instance as int].outputs;
                        &&& next_gate == gate
                        &&& bits.len() == outputs.end - outputs.start
                        &&& forall|bit: int| 0 <= bit < bits.len() ==>
                            #[trigger] bits[bit] == ClockedWireDriver::Terminal(Wire::Input((outputs.start + bit) as usize))
                    },
                }
            },
        }
    }

    #[verifier::opaque]
    spec fn endpoint_prefix(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, storage: &ClockedStorageLayout,
        bits: Seq<ClockedWireDriver>, gates: Seq<Option<usize>>, calls: Seq<usize>, cursors: Seq<usize>,
    ) -> bool {
        let ranges = ports.definitions.ranges_model();
        let count = calls.len() - 1;
        &&& 0 <= count <= ranges.len()
        &&& cursors.len() == calls.len() && calls[0] == 0 && cursors[0] == 0
        &&& calls.last() == gates.len()
        &&& bits.len() == if count == 0 { 0 } else { ranges[count - 1].end }
        &&& forall|slot: int| 0 <= slot < count ==> {
            let range = #[trigger] ranges[slot];
            &&& range.start == if slot == 0 { 0 } else { ranges[slot - 1].end as int }
            &&& range.start < range.end <= bits.len()
            &&& self.endpoint_row(checked, ports, storage, bits.subrange(range.start as int, range.end as int),
                gates, slot, calls[slot], calls[slot + 1], cursors[slot], cursors[slot + 1])
        }
    }

    proof fn keep_endpoint_row(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, storage: &ClockedStorageLayout,
        bits: Seq<ClockedWireDriver>, before: Seq<Option<usize>>, after: Seq<Option<usize>>, slot: int,
        call: usize, next_call: usize, gate: usize, next_gate: usize,
    )
        requires
            self.endpoint_row(checked, ports, storage, bits, before, slot, call, next_call, gate, next_gate),
            after.take(before.len() as int) == before,
            before.len() <= after.len(),
        ensures self.endpoint_row(checked, ports, storage, bits, after, slot, call, next_call, gate, next_gate),
    {
        reveal(UseAliases::endpoint_row);
        if checked.module.expressions.typed.sources.aliases@[slot].is_none() {
            assert(after[call as int] == before[call as int]);
        }
    }

    proof fn endpoint_prefix_row(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, storage: &ClockedStorageLayout,
        bits: Seq<ClockedWireDriver>, gates: Seq<Option<usize>>, calls: Seq<usize>, cursors: Seq<usize>, slot: int,
    )
        requires self.endpoint_prefix(checked, ports, storage, bits, gates, calls, cursors),
            0 <= slot < calls.len() - 1,
        ensures ({
            let ranges = ports.definitions.ranges_model();
            let range = ranges[slot];
            &&& range.start == if slot == 0 { 0 } else { ranges[slot - 1].end as int }
            &&& range.start < range.end <= bits.len()
            &&& self.endpoint_row(checked, ports, storage, bits.subrange(range.start as int, range.end as int),
                gates, slot, calls[slot], calls[slot + 1], cursors[slot], cursors[slot + 1])
        }),
    {
        reveal(UseAliases::endpoint_prefix);
    }

    proof fn extend_endpoint_prefix(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, storage: &ClockedStorageLayout,
        before: (Seq<ClockedWireDriver>, Seq<Option<usize>>, Seq<usize>, Seq<usize>),
        bits: Seq<ClockedWireDriver>, gates: Seq<Option<usize>>, next_call: usize, next_gate: usize, slot: int,
    )
        requires
            self.endpoint_prefix(checked, ports, storage, before.0, before.1, before.2, before.3),
            slot == before.2.len() - 1 < ports.definitions.ranges_model().len(),
            ({
                let range = ports.definitions.ranges_model()[slot];
                &&& range.start == before.0.len() < range.end == bits.len()
                &&& bits.take(range.start as int) == before.0
                &&& before.1.len() <= gates.len() && gates.take(before.1.len() as int) == before.1
                &&& gates.len() == next_call
                &&& self.endpoint_row(checked, ports, storage, bits.subrange(range.start as int, range.end as int),
                    gates, slot, before.2.last(), next_call, before.3.last(), next_gate)
            }),
        ensures self.endpoint_prefix(checked, ports, storage, bits, gates,
            before.2.push(next_call), before.3.push(next_gate)),
    {
        let ranges = ports.definitions.ranges_model();
        let calls = before.2.push(next_call);
        let cursors = before.3.push(next_gate);
        assert(calls.len() == cursors.len() && calls[0] == 0 && cursors[0] == 0) by {
            reveal(UseAliases::endpoint_prefix);
        };
        assert(ranges[slot].start == if slot == 0 { 0 } else { ranges[slot - 1].end as int }) by {
            reveal(UseAliases::endpoint_prefix);
        };
        assert forall|i: int| 0 <= i <= slot implies {
            let range = #[trigger] ranges[i];
            &&& range.start == if i == 0 { 0 } else { ranges[i - 1].end as int }
            &&& range.start < range.end <= bits.len()
            &&& self.endpoint_row(checked, ports, storage, bits.subrange(range.start as int, range.end as int),
                gates, i, calls[i], calls[i + 1], cursors[i], cursors[i + 1])
        } by {
            if i < slot {
                self.endpoint_prefix_row(checked, ports, storage, before.0, before.1, before.2, before.3, i);
                let range = ranges[i];
                assert(bits.subrange(range.start as int, range.end as int)
                    =~= before.0.subrange(range.start as int, range.end as int));
                assert(calls[i] == before.2[i] && calls[i + 1] == before.2[i + 1]);
                assert(cursors[i] == before.3[i] && cursors[i + 1] == before.3[i + 1]);
                self.keep_endpoint_row(checked, ports, storage,
                    bits.subrange(range.start as int, range.end as int), before.1, gates, i,
                    calls[i], calls[i + 1], cursors[i], cursors[i + 1]);
            }
        };
        reveal(UseAliases::endpoint_prefix);
    }

    /// 裸名の定義の配置幅は、同じ型を持つ駆動元から展開したビット数に等しい。
    proof fn alias_endpoint_width(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, checked: &ModuleCalls,
        ports: &ClockedModuleOutputs, slot: usize, wires: Vec<ClockedWireDriver>,
    )
        requires
            self.can_resolve(),
            self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limit, capacity, Ok(*ports)),
            slot < checked.module.expressions.typed.sources.aliases@.len(),
            checked.module.expressions.typed.sources.aliases@[slot as int] matches Some(alias)
                && clocked_driver_bits_result(&ports.inputs, &ports.definitions, alias.driver, None, Ok(wires)),
        ensures ({
            let range = ports.definitions.ranges_model()[slot as int];
            wires@.len() == range.end - range.start
        }),
    {
        self.module_calls_type_evidence(owner, limit, checked);
        self.module_output_types_evidence(owner, limit, checked.module);
        let expressions = checked.module.expressions;
        self.module_selections_evidence(owner, limit, expressions);
        self.module_alias_types_evidence(owner, limit, expressions.typed);
        self.module_type_sources_bounds(owner, limit, expressions.typed.sources);
        self.module_selection_alias_binding(owner, limit, expressions, slot);
        self.clocked_output_layouts(&checked.module, limit, capacity, ports);
        self.clocked_definition_layout_evidence(&expressions, limit, capacity, &ports.definitions, slot);
        let driver = expressions.typed.sources.aliases@[slot as int]->Some_0.driver;
        let signature = expressions.typed.sources.roots.wiring.drivers.signature;
        clocked_whole_port_bits(&ports.inputs, &ports.definitions, driver, wires);
        match driver {
            OutputDriver::Input(port) =>
                self.routine_bit_layout_port(signature, limit, capacity, &ports.inputs, &ports.outputs, PortDirection::Input, port),
            OutputDriver::Definition(definition) =>
                self.clocked_definition_layout_evidence(&expressions, limit, capacity, &ports.definitions, definition),
        }
        let ty = expressions.types@[slot as int]->Some_0.ty;
        assert(bound_type(&expressions.typed, expressions.types@, driver) matches Some(bound) && bound.ty == ty);
        if ty is Struct {
            let range = ports.definitions.ranges_model()[slot as int];
            let width = range.end - range.start;
            let source = choose|table: StructureLayouts| self.structure_types_match(limit, Ok(table))
                && #[trigger] self.layout_port_width_matches(&table, ty, wires@.len() as int);
            let destination = choose|table: StructureLayouts| self.structure_types_match(limit, Ok(table))
                && #[trigger] self.layout_port_width_matches(&table, ty, width);
            self.layout_port_widths_agree_across_tables(limit, &source, &destination, ty, wires@.len() as int, width);
        }
    }

    fn bind_endpoint_blocks(
        &self, owner: ModuleBodyPosition, limit: u64, _capacity: usize, gate_limit: usize,
        checked: &ModuleCalls<'p, 'a>, ports: &ClockedModuleOutputs, storage: &ClockedStorageLayout<'p, 'a>,
    ) -> (result: Result<(Vec<ClockedWireDriver>, Vec<Option<usize>>, usize, Ghost<Seq<usize>>, Ghost<Seq<usize>>),
        ClockedEndpointError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*ports)),
            self.storage_on_checked(checked, limit, ports.inputs.total_bits_model(), _capacity, Ok(*storage)),
        ensures result matches Ok((bits, gates, gate_count, calls, cursors)) ==>
            bits@.len() == ports.definitions.total_bits_model()
                && gates@.len() == checked.calls@.len() && gate_count <= gate_limit
                && calls@.len() == ports.definitions.ranges_model().len() + 1
                && cursors@.last() == gate_count
                && self.endpoint_prefix(checked, ports, storage, bits@, gates@, calls@, cursors@),
            !(result matches Err(ClockedEndpointError::Calls(_))),
    {
        let expressions = &checked.module.expressions;
        let drivers = &expressions.typed.sources.roots.wiring.drivers;
        let aliases = &expressions.typed.sources.aliases;
        proof {
            self.module_calls_type_evidence(owner, limit, checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, *expressions);
            self.module_alias_types_evidence(owner, limit, expressions.typed);
            self.module_type_sources_bounds(owner, limit, expressions.typed.sources);
            self.clocked_output_layouts(&checked.module, limit, _capacity, ports);
            self.clocked_definition_layout_evidence(expressions, limit, _capacity, &ports.definitions, 0);
        }
        let mut definitions = Vec::new();
        let mut gates = Vec::new();
        if definitions.try_reserve_exact(ports.definitions.total_bits()).is_err()
            || gates.try_reserve_exact(checked.calls.len()).is_err() {
            return Err(ClockedEndpointError::Allocation);
        }
        let mut gate_count = 0usize;
        let mut slot = 0usize;
        let mut call = 0usize;
        let ghost mut calls = seq![0usize];
        let ghost mut cursors = seq![0usize];
        assert(self.endpoint_prefix(checked, ports, storage, definitions@, gates@, calls, cursors)) by {
            reveal(UseAliases::endpoint_prefix);
        };
        while slot < drivers.definitions.len()
            invariant
                self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
                self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
                *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
                *aliases == checked.module.expressions.typed.sources.aliases,
                self.storage_on_checked(checked, limit, ports.inputs.total_bits_model(), _capacity, Ok(*storage)),
                self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*ports)),
                slot <= drivers.definitions@.len() == aliases@.len() == ports.definitions.ranges_model().len(),
                call == gates@.len() <= checked.calls@.len(), gate_count <= gate_limit,
                calls.len() == cursors.len() == slot + 1, calls.last() == call, cursors.last() == gate_count,
                self.endpoint_prefix(checked, ports, storage, definitions@, gates@, calls, cursors),
            decreases drivers.definitions@.len() - slot,
        {
            let Some(range) = ports.definitions.range(slot) else { unreachable!() };
            let width = range.end - range.start;
            assert(ports.definitions.ranges_model()[slot as int] == range);
            assert(slot < checked.module.expressions.typed.sources.aliases@.len());
            if range.start != definitions.len() { return Err(ClockedEndpointError::Layout); }
            let ghost before = (definitions@, gates@, calls, cursors);
            if let Some(alias) = &aliases[slot] {
                assert(checked.module.expressions.typed.sources.aliases@[slot as int] == Some(*alias));
                let wires = match clocked_driver_bits(&ports.inputs, &ports.definitions, alias.driver, None) {
                    Ok(wires) => wires,
                    Err(reason) => return Err(ClockedEndpointError::AliasBits {
                        reference: crate::project::use_aliases::function_atoms::copy_location(&alias.reference), reason,
                    }),
                };
                proof { self.alias_endpoint_width(owner, limit, _capacity, checked, ports, slot, wires); }
                self.append_alias_wires(&mut definitions, &wires);
                assert(definitions@.subrange(range.start as int, range.end as int) =~= wires@);
                assert(self.endpoint_row(checked, ports, storage, wires@, gates@, slot as int,
                    call, call, gate_count, gate_count)) by {
                    reveal(UseAliases::endpoint_row);
                    assert(exists|row: Vec<ClockedWireDriver>|
                        #[trigger] clocked_driver_bits_result(&ports.inputs, &ports.definitions, alias.driver, None, Ok(row))
                        && row@ == wires@) by {
                        assert(clocked_driver_bits_result(&ports.inputs, &ports.definitions, alias.driver, None, Ok(wires)));
                    };
                };
            } else {
                assert(checked.module.expressions.typed.sources.aliases@[slot as int].is_none());
                if !self.direct_slot(owner, limit, checked, drivers, slot, call) {
                    return Err(ClockedEndpointError::Unsupported(self.source_driver_location(owner, limit, drivers, slot)));
                }
                proof {
                    vstd::std_specs::vec::axiom_spec_len(&checked.calls);
                    self.storage_layout_call(checked, limit, ports.inputs.total_bits_model(), _capacity, storage, call);
                }
                if let Some(instance) = storage.by_call[call] {
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
                            definitions@.len() == before.0.len() + bit, definitions@.take(before.0.len() as int) == before.0,
                            range.start == before.0.len() && range.end == range.start + width,
                            placement.outputs.start + width == placement.outputs.end,
                            forall|i: int| 0 <= i < bit ==> #[trigger] definitions@[range.start + i]
                                == ClockedWireDriver::Terminal(Wire::Input((placement.outputs.start + i) as usize)),
                        decreases width - bit,
                    {
                        let Some(wire) = placement.output_wire(bit) else { unreachable!() };
                        let ghost pre = definitions@;
                        definitions.push(ClockedWireDriver::Terminal(wire));
                        assert forall|i: int| 0 <= i <= bit implies #[trigger] definitions@[range.start + i]
                            == ClockedWireDriver::Terminal(Wire::Input((placement.outputs.start + i) as usize)) by {
                            if i < bit { assert(definitions@[range.start + i] == pre[range.start + i]); }
                        };
                        bit += 1;
                    }
                    let ghost row = definitions@.subrange(range.start as int, range.end as int);
                    assert forall|i: int| 0 <= i < row.len() implies
                        #[trigger] row[i] == ClockedWireDriver::Terminal(Wire::Input((placement.outputs.start + i) as usize)) by {
                        assert(row[i] == definitions@[range.start + i]);
                    };
                    gates.push(None);
                    assert(gates@[call as int].is_none());
                    assert(self.source_vm_direct_slot(checked, slot as int, call as int));
                    assert(self.endpoint_row(checked, ports, storage, row, gates@, slot as int,
                        call, (call + 1) as usize, gate_count, gate_count)) by { reveal(UseAliases::endpoint_row); };
                } else {
                    if width != 1 {
                        return Err(ClockedEndpointError::Width {
                            definition: self.source_driver_location(owner, limit, drivers, slot), produced: 1, allocated: width,
                        });
                    }
                    if gate_count == gate_limit {
                        return Err(ClockedEndpointError::GateCapacity(self.source_driver_location(owner, limit, drivers, slot)));
                    }
                    definitions.push(ClockedWireDriver::Terminal(Wire::Gate(gate_count)));
                    gates.push(Some(gate_count));
                    assert(gates@[call as int] == Some(gate_count));
                    assert(checked.calls@[call as int].inputs.ports.signature.target is Nor);
                    gate_count += 1;
                    assert(self.endpoint_row(checked, ports, storage,
                        definitions@.subrange(range.start as int, range.end as int), gates@, slot as int,
                        call, (call + 1) as usize, (gate_count - 1) as usize, gate_count)) by {
                        reveal(UseAliases::endpoint_row);
                        assert(definitions@[range.start as int] == ClockedWireDriver::Terminal(Wire::Gate((gate_count - 1) as usize)));
                    };
                }
                assert(call < checked.calls@.len());
                call += 1;
            }
            proof {
                assert(definitions@.take(before.0.len() as int) =~= before.0);
                assert(gates@.take(before.1.len() as int) =~= before.1);
                self.extend_endpoint_prefix(checked, ports, storage, before, definitions@, gates@, call, gate_count, slot as int);
                calls = calls.push(call);
                cursors = cursors.push(gate_count);
            }
            slot += 1;
        }
        if call < checked.calls.len() {
            let remaining = &checked.calls[call].inputs.ports.signature;
            return Err(ClockedEndpointError::Unsupported(LocatedName {
                source: remaining.source, span: remaining.call.span.start..remaining.call.span.end,
            }));
        }
        if definitions.len() != ports.definitions.total_bits() {
            return Err(ClockedEndpointError::Layout);
        }
        Ok((definitions, gates, gate_count, Ghost(calls), Ghost(cursors)))
    }

    fn append_alias_wires(&self, definitions: &mut Vec<ClockedWireDriver>, wires: &[ClockedWireDriver])
        requires old(definitions)@.len() + wires@.len() <= usize::MAX,
        ensures final(definitions)@ == old(definitions)@ + wires@,
    {
        let mut i = 0usize;
        while i < wires.len()
            invariant i <= wires@.len(), definitions@ == old(definitions)@ + wires@.take(i as int),
                old(definitions)@.len() + wires@.len() <= usize::MAX,
            decreases wires@.len() - i,
        {
            definitions.push(wires[i]);
            assert(wires@.take((i + 1) as int) =~= wires@.take(i as int).push(wires@[i as int]));
            i += 1;
        }
        assert(wires@.take(i as int) =~= wires@);
    }

    spec fn endpoints_on_checked(
        &self, checked: &ModuleCalls, limit: u64, capacity: usize, gate_limit: usize, plan: &ClockedModuleEndpoints,
    ) -> bool {
        &&& self.outputs_on_checked(&checked.module, limit, capacity, Ok(plan.ports))
        &&& self.storage_on_checked(checked, limit, plan.ports.inputs.total_bits_model(), capacity, Ok(plan.storage))
        &&& plan.definitions@.len() == plan.ports.definitions.total_bits_model()
        &&& plan.gate_by_call@.len() == checked.calls@.len()
        &&& plan.gate_count <= gate_limit
        &&& plan._call_cursors@.len() == plan.ports.definitions.ranges_model().len() + 1
        &&& plan._gate_cursors@.last() == plan.gate_count
        &&& self.endpoint_prefix(checked, &plan.ports, &plan.storage, plan._symbolic@, plan.gate_by_call@,
            plan._call_cursors@, plan._gate_cursors@)
        &&& clocked_resolution_result(plan._symbolic@, plan.storage.augmented_inputs, plan.gate_count, Ok(plan.definitions))
    }

    fn prepare_vm_endpoints(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, gate_limit: usize, checked: &ModuleCalls<'p, 'a>,
    ) -> (result: Result<ClockedModuleEndpoints<'p, 'a>, ClockedEndpointError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
        ensures
            result matches Ok(plan) ==> self.endpoints_on_checked(checked, limit, capacity, gate_limit, &plan),
            !(result matches Err(ClockedEndpointError::Calls(_))),
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
        let (symbolic, gate_by_call, gate_count, call_cursors, gate_cursors) =
            self.bind_endpoint_blocks(owner, limit, capacity, gate_limit, checked, &ports, &storage)?;
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, checked.module.expressions);
            self.module_alias_types_evidence(owner, limit, checked.module.expressions.typed);
            self.module_type_sources_bounds(owner, limit, checked.module.expressions.typed.sources);
            self.clocked_output_layouts(&checked.module, limit, capacity, &ports);
            self.clocked_definition_layout_evidence(&checked.module.expressions, limit, capacity, &ports.definitions, 0);
        }
        let resolved = match resolve_terminal_wires(symbolic.as_slice(), storage.augmented_inputs, gate_count) {
            TerminalResolution::Wires(wires) => Ok(wires),
            TerminalResolution::FirstInvalid(bit) => Err(ClockedPlanError::Wire(bit)),
            TerminalResolution::Allocation => return Err(ClockedEndpointError::Allocation),
            TerminalResolution::HasAlias => clocked_resolve(symbolic.as_slice(), storage.augmented_inputs, gate_count),
        };
        let definitions = match resolved {
            Ok(definitions) => definitions,
            Err(ClockedPlanError::GateCapacity(_)) => unreachable!(),
            Err(ClockedPlanError::Wire(bit)) => {
                let Some(slot) = ports.definitions.port_at_bit(bit) else { unreachable!() };
                return Err(ClockedEndpointError::Driver(self.source_driver_location(owner, limit, drivers, slot)));
            },
            Err(ClockedPlanError::AliasCycle(cycle)) => {
                let aliases = &checked.module.expressions.typed.sources.aliases;
                let mut sites = Vec::new();
                if sites.try_reserve_exact(cycle.len()).is_err() { return Err(ClockedEndpointError::Allocation); }
                let mut i = 0usize;
                while i < cycle.len()
                    invariant
                        i <= cycle@.len(), sites@.len() == i,
                        aliases@.len() == drivers.definitions@.len() == ports.definitions.ranges_model().len(),
                        ports.definitions.total_bits_model() == symbolic@.len(),
                        self.can_resolve(), self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
                        forall|j: int| 0 <= j < cycle@.len() ==> #[trigger] cycle@[j] < symbolic@.len(),
                    decreases cycle@.len() - i,
                {
                    let Some(slot) = ports.definitions.port_at_bit(cycle[i]) else { unreachable!() };
                    let site = match &aliases[slot] {
                        Some(alias) => crate::project::use_aliases::function_atoms::copy_location(&alias.reference),
                        None => self.source_driver_location(owner, limit, drivers, slot),
                    };
                    sites.push(site);
                    i += 1;
                }
                return Err(ClockedEndpointError::AliasCycle(sites));
            },
        };
        Ok(ClockedModuleEndpoints { ports, storage, definitions, _symbolic: Ghost(symbolic@),
            _call_cursors: call_cursors, _gate_cursors: gate_cursors, gate_by_call, gate_count })
    }


}

} // verus!
