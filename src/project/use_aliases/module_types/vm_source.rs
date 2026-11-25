//! モジュールの定義を、直接の配線、ゲート、状態素子に対応付ける。

mod concat;
mod execution;
mod vram;
pub use execution::{ClockedModuleVm, ClockedModuleVmError, ClockedModuleVmLimits};
pub use execution::{ClockedDeviceVm, ClockedDeviceVmError, DevicePortBits};
pub use execution::{ClockedVramVm, VramDeclaration, VramSetupError, VramView};
pub use vram::{VramOutputError, VramTarget};
#[cfg(verus_only)]
pub use execution::ClockedModuleObservation;

use super::{ClockedModuleOutputs, ClockedModuleOutputsError, ClockedStorageLayout, ClockedStorageLayoutError,
    ClockedDriverBitsError, ClockedPlanError, ClockedWireDriver, ModuleCalls, ModuleCallsError, UseAliases,
    clocked_driver_bits, clocked_plan::{TerminalResolution, clocked_resolve, resolve_terminal_wires}};
#[cfg(verus_only)]
use super::{clocked_plan::{clocked_cycle_edge, clocked_resolution_result, clocked_wire_cycle}, clocked_driver_bits_result,
    driver_bits::{checked_selection_wiring_error, clocked_selected_port_bits, clocked_selected_port_ready, clocked_whole_port_bits}, selections::bound_type};
#[cfg(verus_only)]
use crate::project::{PortDirection, StructureLayouts};
use crate::netlist::Wire;
use crate::project::{CheckedBitSelection, LocatedName, ModuleBodyPosition, ModuleCallTarget, ModuleDrivers, OutputDriver};
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
    /// 直結、ビット選択、連接、基底 NOR・ラッチ・RAM の直接呼び出しのいずれでも展開できない定義。
    Unsupported(LocatedName<'p, 'a>),
    /// 右辺の信号またはリテラルをビット列に展開できなかった。
    AliasBits {
        /// 展開する信号名またはリテラルのソース範囲。
        reference: LocatedName<'p, 'a>,
        /// 信号の配線を生成できなかった理由。
        reason: ClockedDriverBitsError,
    },
    /// 定義の駆動元が配置の範囲外だった。
    Driver(LocatedName<'p, 'a>),
    /// 直結、ビット選択、連接からなる閉路。各要素は閉路順に並べた信号参照の位置。
    AliasCycle(Vec<LocatedName<'p, 'a>>),
    /// ゲート数の上限を超えた最初の定義。
    GateCapacity(LocatedName<'p, 'a>),
    /// 右辺が出力するビット数と、定義に割り当てられたビット数が異なる。
    Width {
        /// 定義の左辺の範囲。
        definition: LocatedName<'p, 'a>,
        /// 右辺の出力に必要なビット数。
        produced: usize,
        /// 定義に割り当てられたビット数。
        allocated: usize,
    },
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn source_vm_root_slot(&self, checked: &ModuleCalls, slot: int, call: int) -> bool {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        let row = checked.calls@[call];
        let origin = drivers.origins@[slot];
        let target = drivers.definitions@[slot];
        let parsed = self.targets.project_model().circuits_model()[row.at.file as int];
        &&& 0 <= call < checked.calls@.len()
        &&& origin.file == row.at.file && origin.entry == row.at.entry
        &&& row.at.reference == 0
        &&& target.definition == parsed.entry_ranges@[row.at.entry as int].definitions.start + row.at.definition
        &&& row.inputs.ports.signature.call.form == parsed.definitions@[target.definition as int].expression.start
    }

    fn root_call_slot(
        &self, _owner: ModuleBodyPosition, _limit: u64, checked: &ModuleCalls<'p, 'a>, drivers: &ModuleDrivers<'p, 'a>, slot: usize, call: usize,
    ) -> (direct: bool)
        requires
            self.can_resolve(), self.module_calls_result(_owner, _limit, Ok(Some(*checked))),
            self.module_drivers_result(_owner, _limit, Ok(Some(*drivers))),
            *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
            slot < drivers.definitions@.len(),
        ensures direct == self.source_vm_root_slot(checked, slot as int, call as int),
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
        if origin.file != row.at.file || origin.entry != row.at.entry || row.at.reference != 0 {
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
    }

    spec fn source_vm_direct_slot(&self, checked: &ModuleCalls, slot: int, call: int) -> bool {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        let target = checked.calls@[call].inputs.ports.signature.target;
        self.source_vm_root_slot(checked, slot, call) && drivers.definitions@[slot].result_index == 0
            && (target is Nor || target is StateElement)
    }

    fn direct_slot(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls<'p, 'a>, drivers: &ModuleDrivers<'p, 'a>,
        slot: usize, call: usize,
    ) -> (direct: bool)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
            *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
            slot < drivers.definitions@.len(),
        ensures direct == self.source_vm_direct_slot(checked, slot as int, call as int),
    {
        self.root_call_slot(owner, limit, checked, drivers, slot, call)
            && drivers.definitions[slot].result_index == 0
            && matches!(checked.calls[call].inputs.ports.signature.target,
                ModuleCallTarget::Nor | ModuleCallTarget::StateElement { .. })
    }

    spec fn endpoint_projection(checked: &ModuleCalls, slot: int) -> Option<(OutputDriver, Option<CheckedBitSelection>)> {
        let expressions = checked.module.expressions;
        match expressions.typed.sources.aliases@[slot] {
            Some(alias) => Some((alias.driver, None)),
            None => match expressions.selections@[slot] {
                Some(selected) => Some((selected.driver, Some(selected.projection))),
                None => None,
            },
        }
    }

    fn endpoint_projection_at(&self, checked: &ModuleCalls<'p, 'a>, slot: usize)
        -> (projection: Option<(OutputDriver, Option<CheckedBitSelection>)>)
        requires
            slot < checked.module.expressions.typed.sources.aliases@.len(),
            slot < checked.module.expressions.selections@.len(),
        ensures projection == Self::endpoint_projection(checked, slot as int),
    {
        let expressions = &checked.module.expressions;
        if let Some(alias) = &expressions.typed.sources.aliases[slot] {
            Some((alias.driver, None))
        } else if let Some(selected) = &expressions.selections[slot] {
            Some((selected.driver, Some(selected.projection)))
        } else {
            None
        }
    }

    fn endpoint_projection_site(&self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls<'p, 'a>, slot: usize)
        -> (site: LocatedName<'p, 'a>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            slot < checked.module.expressions.typed.sources.aliases@.len(),
            slot < checked.module.expressions.selections@.len(),
            Self::endpoint_projection(checked, slot as int).is_some(),
        ensures self.endpoint_projection_site_at(checked, slot as int, site),
    {
        let expressions = &checked.module.expressions;
        if let Some(alias) = &expressions.typed.sources.aliases[slot] {
            crate::project::use_aliases::function_atoms::copy_location(&alias.reference)
        } else {
            proof { self.module_calls_type_evidence(owner, limit, checked); self.module_output_types_evidence(owner, limit, checked.module); }
            self.module_selection_operand(owner, limit, expressions, slot)
        }
    }

    spec fn endpoint_projection_site_at(&self, checked: &ModuleCalls, slot: int, site: LocatedName) -> bool {
        let expressions = checked.module.expressions;
        match expressions.typed.sources.aliases@[slot] {
            Some(alias) => site == alias.reference,
            None => self.module_selection_operand_at(&expressions, slot, site),
        }
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
        &&& match Self::endpoint_projection(checked, slot) {
            Some((driver, projection)) => {
                &&& next_call == call && next_gate == gate
                &&& exists|wires: Vec<ClockedWireDriver>|
                    #[trigger] clocked_driver_bits_result(&ports.inputs, &ports.definitions, driver, projection, Ok(wires))
                    && wires@ == bits
            },
            None if checked.module.expressions.concats@[slot].is_some() =>
                next_call == call && next_gate == gate && self.endpoint_concat_wires(checked, ports, slot, bits),
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
        if Self::endpoint_projection(checked, slot).is_none() && checked.module.expressions.concats@[slot].is_none() {
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

    /// 選択が収まる基底信号の幅を、その信号に割り当てた範囲の幅と照合する。
    proof fn selected_endpoint_ready(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, checked: &ModuleCalls,
        ports: &ClockedModuleOutputs, slot: usize,
    )
        requires
            self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limit, capacity, Ok(*ports)),
            slot < checked.module.expressions.selections@.len(),
            checked.module.expressions.selections@[slot as int].is_some(),
        ensures ({
            let selection = checked.module.expressions.selections@[slot as int]->Some_0;
            clocked_selected_port_ready(&ports.inputs, &ports.definitions, selection.driver, selection.projection)
        }),
    {
        self.module_calls_type_evidence(owner, limit, checked);
        self.module_output_types_evidence(owner, limit, checked.module);
        let expressions = checked.module.expressions;
        self.module_selections_evidence(owner, limit, expressions);
        self.module_selection_evidence(owner, limit, expressions, slot);
        self.clocked_output_layouts(&checked.module, limit, capacity, ports);
        let driver = expressions.selections@[slot as int]->Some_0.driver;
        let signature = expressions.typed.sources.roots.wiring.drivers.signature;
        match driver {
            OutputDriver::Input(port) =>
                self.routine_bit_layout_port(signature, limit, capacity, &ports.inputs, &ports.outputs, PortDirection::Input, port),
            OutputDriver::Definition(definition) =>
                self.clocked_definition_layout_evidence(&expressions, limit, capacity, &ports.definitions, definition),
        }
    }

    spec fn wire_definition_without_call_matches(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, slot: usize, result: Option<Vec<ClockedWireDriver>>,
    ) -> bool {
        let projection = Self::endpoint_projection(checked, slot as int);
        let concat = checked.module.expressions.concats@[slot as int];
        let range = ports.definitions.ranges_model()[slot as int];
        match result {
            Some(wires) => wires@.len() == range.end - range.start && match projection {
                Some((driver, selection)) =>
                    clocked_driver_bits_result(&ports.inputs, &ports.definitions, driver, selection, Ok(wires)),
                None => concat.is_some() && self.endpoint_concat_wires(checked, ports, slot as int, wires@),
            },
            None => projection.is_none() && concat.is_none(),
        }
    }

    /// 呼び出しを伴わない定義を配線に変える。呼び出しを展開する定義では `None` を返す。
    fn wire_definition_without_call(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, checked: &ModuleCalls<'p, 'a>,
        ports: &ClockedModuleOutputs, slot: usize,
    ) -> (result: Result<Option<Vec<ClockedWireDriver>>, ClockedEndpointError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limit, capacity, Ok(*ports)),
            slot < checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len(),
        ensures
            result matches Ok(wires) ==> self.wire_definition_without_call_matches(checked, ports, slot, wires),
            result matches Err(error) ==> error is AliasBits || error is Allocation,
    {
        let expressions = &checked.module.expressions;
        proof {
            self.module_calls_type_evidence(owner, limit, checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, *expressions);
            self.module_alias_types_evidence(owner, limit, expressions.typed);
            self.module_type_sources_bounds(owner, limit, expressions.typed.sources);
            self.clocked_output_layouts(&checked.module, limit, capacity, ports);
            self.clocked_definition_layout_evidence(expressions, limit, capacity, &ports.definitions, slot);
        }
        if let Some((driver, projection)) = self.endpoint_projection_at(checked, slot) {
            let wires = match clocked_driver_bits(&ports.inputs, &ports.definitions, driver, projection) {
                Ok(wires) => wires,
                Err(reason) => {
                    proof {
                        if let Some(selected) = projection {
                            self.selected_endpoint_ready(owner, limit, capacity, checked, ports, slot);
                            checked_selection_wiring_error(&ports.inputs, &ports.definitions, driver, selected, reason);
                        }
                    }
                    let reference = self.endpoint_projection_site(owner, limit, checked, slot);
                    return Err(ClockedEndpointError::AliasBits { reference, reason });
                },
            };
            proof {
                if let Some(selected) = projection {
                    self.module_selection_width(owner, limit, *expressions, slot);
                    clocked_selected_port_bits(&ports.inputs, &ports.definitions, driver, selected, wires);
                } else {
                    self.alias_endpoint_width(owner, limit, capacity, checked, ports, slot, wires);
                }
            }
            Ok(Some(wires))
        } else if expressions.concats[slot].is_some() {
            Ok(Some(self.wire_concat_definition(owner, limit, capacity, checked, ports, slot)?))
        } else {
            Ok(None)
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
            !(result matches Err(ClockedEndpointError::AliasCycle(_))),
    {
        let expressions = &checked.module.expressions;
        let drivers = &expressions.typed.sources.roots.wiring.drivers;
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
                self.storage_on_checked(checked, limit, ports.inputs.total_bits_model(), _capacity, Ok(*storage)),
                self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*ports)),
                slot <= drivers.definitions@.len() == ports.definitions.ranges_model().len(),
                checked.module.expressions.typed.sources.aliases@.len() == drivers.definitions@.len(),
                checked.module.expressions.selections@.len() == drivers.definitions@.len(),
                checked.module.expressions.concats@.len() == drivers.definitions@.len(),
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
            if let Some(wires) = self.wire_definition_without_call(owner, limit, _capacity, checked, ports, slot)? {
                self.append_definition_wires(&mut definitions, &wires);
                assert(definitions@.subrange(range.start as int, range.end as int) =~= wires@);
                assert(self.endpoint_row(checked, ports, storage, wires@, gates@, slot as int,
                    call, call, gate_count, gate_count)) by {
                    reveal(UseAliases::endpoint_row);
                    if let Some((driver, projection)) = Self::endpoint_projection(checked, slot as int) {
                        assert(exists|row: Vec<ClockedWireDriver>|
                            #[trigger] clocked_driver_bits_result(&ports.inputs, &ports.definitions, driver, projection, Ok(row))
                            && row@ == wires@) by {
                            assert(clocked_driver_bits_result(&ports.inputs, &ports.definitions, driver, projection, Ok(wires)));
                        };
                    }
                };
            } else {
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

    fn append_definition_wires(&self, definitions: &mut Vec<ClockedWireDriver>, wires: &[ClockedWireDriver])
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

    /// 配線の閉路を構成するビットは、終端を持つ呼び出しからは生じない。
    proof fn cycle_has_wire_definition(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, storage: &ClockedStorageLayout,
        bits: Seq<ClockedWireDriver>, gates: Seq<Option<usize>>, calls: Seq<usize>, cursors: Seq<usize>,
        slot: usize, bit: usize,
    )
        requires
            self.endpoint_prefix(checked, ports, storage, bits, gates, calls, cursors),
            slot < calls.len() - 1,
            ({
                let range = ports.definitions.ranges_model()[slot as int];
                range.start <= bit < range.end
            }),
            bits[bit as int] is Alias,
        ensures
            Self::endpoint_projection(checked, slot as int).is_none() ==> {
                let range = ports.definitions.ranges_model()[slot as int];
                &&& checked.module.expressions.concats@[slot as int].is_some()
                &&& self.endpoint_concat_wires(checked, ports, slot as int, bits.subrange(range.start as int, range.end as int))
            },
    {
        self.endpoint_prefix_row(checked, ports, storage, bits, gates, calls, cursors, slot as int);
        reveal(UseAliases::endpoint_row);
        if Self::endpoint_projection(checked, slot as int).is_none() && checked.module.expressions.concats@[slot as int].is_none() {
            let range = ports.definitions.ranges_model()[slot as int];
            let row = bits.subrange(range.start as int, range.end as int);
            let offset = bit - range.start;
            assert(row[offset] == bits[bit as int]);
            if let Some(gate) = gates[calls[slot as int] as int] {
                assert(offset == 0 && row[offset] == ClockedWireDriver::Terminal(Wire::Gate(gate)));
            } else {
                let instance = storage.by_call@[calls[slot as int] as int]->Some_0;
                let outputs = storage.instances@[instance as int].outputs;
                assert(row[offset] == ClockedWireDriver::Terminal(Wire::Input((outputs.start + offset) as usize)));
            }
        }
    }

    spec fn endpoint_wire_site_at(&self, checked: &ModuleCalls, slot: int, bit: int, site: LocatedName) -> bool {
        if Self::endpoint_projection(checked, slot).is_some() {
            self.endpoint_projection_site_at(checked, slot, site)
        } else {
            self.endpoint_concat_site_at(checked, slot, bit, site)
        }
    }

    #[verifier::opaque]
    spec fn projection_cycle_locations(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, cycle: Seq<usize>, sites: Seq<LocatedName>,
    ) -> bool {
        &&& sites.len() <= cycle.len()
        &&& forall|i: int| 0 <= i < sites.len() ==> {
            let site = #[trigger] sites[i];
            exists|slot: int| {
                let range = #[trigger] ports.definitions.ranges_model()[slot];
                &&& 0 <= slot < ports.definitions.ranges_model().len()
                &&& range.start <= cycle[i] < range.end
                &&& self.endpoint_wire_site_at(checked, slot, cycle[i] - range.start, site)
            }
        }
    }

    proof fn append_projection_cycle_location(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, cycle: Seq<usize>,
        sites: Seq<LocatedName>, slot: usize, site: LocatedName,
    )
        requires
            self.projection_cycle_locations(checked, ports, cycle, sites),
            sites.len() < cycle.len(),
            slot < ports.definitions.ranges_model().len(),
            ports.definitions.ranges_model()[slot as int].start <= cycle[sites.len() as int]
                < ports.definitions.ranges_model()[slot as int].end,
            self.endpoint_wire_site_at(checked, slot as int,
                cycle[sites.len() as int] - ports.definitions.ranges_model()[slot as int].start, site),
        ensures self.projection_cycle_locations(checked, ports, cycle, sites.push(site)),
    {
        reveal(UseAliases::projection_cycle_locations);
        let next = sites.push(site);
        assert forall|i: int| 0 <= i < next.len() implies {
            let at = #[trigger] next[i];
            exists|index: int| {
                let range = #[trigger] ports.definitions.ranges_model()[index];
                &&& 0 <= index < ports.definitions.ranges_model().len()
                &&& range.start <= cycle[i] < range.end
                &&& self.endpoint_wire_site_at(checked, index, cycle[i] - range.start, at)
            }
        } by {
            if i < sites.len() {
                assert(next[i] == sites[i]);
            } else {
                assert(next[i] == site);
                assert(ports.definitions.ranges_model()[slot as int].start <= cycle[i]
                    < ports.definitions.ranges_model()[slot as int].end);
            }
        };
    }

    spec fn cycle_on_checked(
        &self, checked: &ModuleCalls, limit: u64, capacity: usize, gate_limit: usize, sites: Seq<LocatedName>,
    ) -> bool {
        exists|ports: ClockedModuleOutputs, storage: ClockedStorageLayout, bits: Seq<ClockedWireDriver>,
            gates: Seq<Option<usize>>, calls: Seq<usize>, cursors: Seq<usize>, gate_count: usize, cycle: Vec<usize>|
            #[trigger] self.endpoint_prefix(checked, &ports, &storage, bits, gates, calls, cursors)
            && #[trigger] self.projection_cycle_locations(checked, &ports, cycle@, sites)
            && #[trigger] clocked_resolution_result(bits, storage.augmented_inputs, gate_count, Err(ClockedPlanError::AliasCycle(cycle)))
            && self.outputs_on_checked(&checked.module, limit, capacity, Ok(ports))
            && self.storage_on_checked(checked, limit, ports.inputs.total_bits_model(), capacity, Ok(storage))
            && calls.len() == ports.definitions.ranges_model().len() + 1
            && cursors.last() == gate_count && gate_count <= gate_limit
            && clocked_wire_cycle(bits, cycle@) && cycle@.len() == sites.len()
    }

    fn prepare_vm_endpoints(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, gate_limit: usize, checked: &ModuleCalls<'p, 'a>,
    ) -> (result: Result<ClockedModuleEndpoints<'p, 'a>, ClockedEndpointError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
        ensures
            result matches Ok(plan) ==> self.endpoints_on_checked(checked, limit, capacity, gate_limit, &plan),
            !(result matches Err(ClockedEndpointError::Calls(_))),
            result matches Err(ClockedEndpointError::AliasCycle(sites)) ==>
                self.cycle_on_checked(checked, limit, capacity, gate_limit, sites@),
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
                let mut sites = Vec::new();
                if sites.try_reserve_exact(cycle.len()).is_err() { return Err(ClockedEndpointError::Allocation); }
                assert(self.projection_cycle_locations(checked, &ports, cycle@, sites@)) by {
                    reveal(UseAliases::projection_cycle_locations);
                };
                let mut i = 0usize;
                while i < cycle.len()
                    invariant
                        i <= cycle@.len(), sites@.len() == i,
                        drivers.definitions@.len() == ports.definitions.ranges_model().len(),
                        checked.module.expressions.typed.sources.aliases@.len() == drivers.definitions@.len(),
                        checked.module.expressions.selections@.len() == drivers.definitions@.len(),
                        checked.module.expressions.concats@.len() == drivers.definitions@.len(),
                        self.module_calls_result(owner, limit, Ok(Some(*checked))),
                        self.outputs_on_checked(&checked.module, limit, capacity, Ok(ports)),
                        self.storage_on_checked(checked, limit, ports.inputs.total_bits_model(), capacity, Ok(storage)),
                        ports.definitions.total_bits_model() == symbolic@.len(),
                        self.can_resolve(),
                        call_cursors@.len() == ports.definitions.ranges_model().len() + 1,
                        self.endpoint_prefix(checked, &ports, &storage, symbolic@, gate_by_call@,
                            call_cursors@, gate_cursors@),
                        gate_cursors@.last() == gate_count && gate_count <= gate_limit,
                        clocked_wire_cycle(symbolic@, cycle@),
                        clocked_resolution_result(symbolic@, storage.augmented_inputs, gate_count,
                            Err(ClockedPlanError::AliasCycle(cycle))),
                        self.projection_cycle_locations(checked, &ports, cycle@, sites@),
                        forall|j: int| 0 <= j < cycle@.len() ==> #[trigger] cycle@[j] < symbolic@.len(),
                    decreases cycle@.len() - i,
                {
                    let bit = cycle[i];
                    let Some(slot) = ports.definitions.port_at_bit(bit) else { unreachable!() };
                    let Some(range) = ports.definitions.range(slot) else { unreachable!() };
                    proof {
                        clocked_cycle_edge(symbolic@, cycle@, i as int);
                        self.cycle_has_wire_definition(checked, &ports, &storage, symbolic@, gate_by_call@,
                            call_cursors@, gate_cursors@, slot, bit);
                    }
                    let offset = bit - range.start;
                    let site = if self.endpoint_projection_at(checked, slot).is_some() {
                        self.endpoint_projection_site(owner, limit, checked, slot)
                    } else {
                        let ghost row = symbolic@.subrange(range.start as int, range.end as int);
                        assert(row[offset as int] == symbolic@[bit as int]);
                        self.endpoint_concat_site(owner, limit, checked, &ports, slot, offset, Ghost(row))
                    };
                    let ghost prior = sites@;
                    sites.push(site);
                    proof { self.append_projection_cycle_location(checked, &ports, cycle@, prior, slot, site); }
                    i += 1;
                }
                assert(self.cycle_on_checked(checked, limit, capacity, gate_limit, sites@));
                return Err(ClockedEndpointError::AliasCycle(sites));
            },
        };
        Ok(ClockedModuleEndpoints { ports, storage, definitions, _symbolic: Ghost(symbolic@),
            _call_cursors: call_cursors, _gate_cursors: gate_cursors, gate_by_call, gate_count })
    }


}

} // verus!
