//! 型を照合したモジュールの出力を、宣言順にビット配線へ変換する。

use super::{ClockedDefinitionLayoutError, ClockedDriverBitsError, ClockedWireDriver, ModuleCallsError, ModuleOutputTypes, UseAliases,
    clocked_driver_bits, copy_location};
use crate::netlist::{PortBitLayout, PortBitLayoutError};
use crate::project::{LocatedName, ModuleBodyPosition, PortDirection, StructureTypeError};
use crate::project::use_aliases::bit_func::RoutineBitLayoutError;
#[cfg(verus_only)]
use super::{ModuleCalls, clocked_driver_bits_result,
    driver_bits::clocked_whole_port_bits, selections::bound_type};
#[cfg(verus_only)]
use crate::project::{OutputDriver, ResolvedPortType, StructureLayouts};
#[cfg(verus_only)]
use crate::project::use_aliases::bit_func::has_structure_port;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 公開出力を接続するときに使うポートと定義の配置、および出力の駆動元。
#[derive(Debug)]
pub struct ClockedModuleOutputs {
    /// 宣言順の入力ポートのビット範囲。
    pub inputs: PortBitLayout,
    /// 宣言順の公開出力ポートのビット範囲。
    pub outputs: PortBitLayout,
    /// モジュール本体と全断片を通した、定義順のビット範囲。
    pub definitions: PortBitLayout,
    /// 宣言順に並んだ公開出力の配線。ポート内では最下位ビットが先頭。
    pub drivers: Vec<Vec<ClockedWireDriver>>,
}

/// 公開出力の配線を作れなかった理由。
#[derive(Debug)]
pub enum ClockedModuleOutputsError<'p, 'a> {
    /// モジュール本体または断片の配線、型、呼び出しに違反がある。
    Calls(ModuleCallsError<'p, 'a>),
    /// ポートに用いる構造体を配置できなかった。
    Structure(StructureTypeError<'p, 'a>),
    /// ポートにビット範囲を割り当てられなかった。
    Port {
        /// 入力ポートか公開出力ポートかを示す。
        direction: PortDirection,
        /// ポートの型注釈の範囲。
        site: LocatedName<'p, 'a>,
        /// ポート番号、幅、容量に関する診断。
        layout: PortBitLayoutError,
    },
    /// 定義にビット範囲を割り当てられなかった。
    Definitions(ClockedDefinitionLayoutError<'p, 'a>),
    /// 公開出力の一覧に必要なメモリを確保できなかった。
    Allocation,
    /// 公開出力を駆動するビットの配線列を作れなかった。
    Wiring {
        /// 出力ポートの型注釈の範囲。
        site: LocatedName<'p, 'a>,
        /// 配線列を作れなかった理由。
        reason: ClockedDriverBitsError,
    },
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    spec fn output_wiring_prefix(
        &self, checked: &ModuleOutputTypes, plan: &ClockedModuleOutputs, wires: Seq<Vec<ClockedWireDriver>>,
    ) -> bool {
        let drivers = checked.expressions.typed.sources.roots.wiring.drivers;
        &&& wires.len() <= drivers.outputs@.len() == plan.outputs.ranges_model().len()
        &&& forall|port: int| 0 <= port < wires.len() ==> {
            let row = #[trigger] wires[port];
            let range = plan.outputs.ranges_model()[port];
            &&& row@.len() == range.end - range.start
            &&& clocked_driver_bits_result(&plan.inputs, &plan.definitions, drivers.outputs@[port], None, Ok(row))
        }
    }

    proof fn output_driver_width_matches(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, checked: &ModuleOutputTypes,
        plan: &ClockedModuleOutputs, index: usize, bits: Vec<ClockedWireDriver>,
    )
        requires
            self.can_resolve(),
            self.module_output_types_result(owner, limit, Ok(Some(*checked))),
            self.module_drivers_result(owner, limit, Ok(Some(checked.expressions.typed.sources.roots.wiring.drivers))),
            self.routine_bit_layouts_match(checked.expressions.typed.sources.roots.wiring.drivers.signature,
                limit, capacity, &plan.inputs, &plan.outputs),
            self.clocked_definition_layout_on_checked(&checked.expressions, limit, capacity, Ok(plan.definitions)),
            index < checked.expressions.typed.sources.roots.wiring.drivers.outputs@.len(),
            clocked_driver_bits_result(&plan.inputs, &plan.definitions,
                checked.expressions.typed.sources.roots.wiring.drivers.outputs@[index as int], None, Ok(bits)),
        ensures bits@.len() == plan.outputs.ranges_model()[index as int].end - plan.outputs.ranges_model()[index as int].start,
    {
        let drivers = checked.expressions.typed.sources.roots.wiring.drivers;
        let signature = drivers.signature;
        let driver = drivers.outputs@[index as int];
        self.module_output_driver(owner, limit, drivers, index as int);
        self.module_output_binding_type(owner, limit, *checked, index);
        self.routine_bit_layout_port(signature, limit, capacity, &plan.inputs, &plan.outputs, PortDirection::Output, index);
        self.module_output_types_evidence(owner, limit, *checked);
        self.module_selections_evidence(owner, limit, checked.expressions);
        self.module_selection_type_declarations(owner, limit, checked.expressions);
        self.typed_signature_types_declared(owner.file, owner.entry, limit, signature);
        clocked_whole_port_bits(&plan.inputs, &plan.definitions, driver, bits);
        let actual = bound_type(&checked.expressions.typed, checked.expressions.types@, driver);
        match driver {
            OutputDriver::Input(port) =>
                self.routine_bit_layout_port(signature, limit, capacity, &plan.inputs, &plan.outputs, PortDirection::Input, port),
            OutputDriver::Definition(slot) =>
                self.clocked_definition_layout_evidence(&checked.expressions, limit, capacity, &plan.definitions, slot),
        }
        assert(actual.is_some());
        let ty = actual->Some_0.ty;
        let expected = signature.outputs@[index as int].ty;
        self.equivalent_declared_port_types(ty, expected);
        if ty is Struct {
            let range = plan.outputs.ranges_model()[index as int];
            let outgoing = range.end - range.start;
            let source_layout = choose|table: StructureLayouts|
                self.structure_types_match(limit, Ok(table))
                    && #[trigger] self.layout_port_width_matches(&table, ty, bits@.len() as int);
            let output_layout = choose|table: StructureLayouts|
                self.structure_types_match(limit, Ok(table))
                    && #[trigger] self.layout_port_width_matches(&table, ty, outgoing);
            self.layout_port_widths_agree_across_tables(limit, &source_layout, &output_layout, ty,
                bits@.len() as int, outgoing);
        }
    }

    /// 配置と配線を、呼び出し側が保持している出力の型検査結果に結び付ける。
    pub(super) closed spec fn outputs_on_checked(
        &self, checked: &ModuleOutputTypes, limit: u64, capacity: usize,
        result: Result<ClockedModuleOutputs, ClockedModuleOutputsError>,
    ) -> bool {
        let drivers = checked.expressions.typed.sources.roots.wiring.drivers;
        match result {
            Ok(plan) => self.routine_bit_layouts_match(drivers.signature, limit, capacity, &plan.inputs, &plan.outputs)
                && self.clocked_definition_layout_on_checked(&checked.expressions, limit, capacity, Ok(plan.definitions))
                && self.output_wiring_prefix(checked, &plan, plan.drivers@)
                && plan.drivers@.len() == drivers.outputs@.len(),
            Err(ClockedModuleOutputsError::Structure(error)) => self.structure_types_match(limit, Err(error))
                && (has_structure_port(drivers.signature.inputs@) || has_structure_port(drivers.signature.outputs@)),
            Err(ClockedModuleOutputsError::Port { direction, site, layout }) =>
                self.routine_bit_layout_failure(drivers.signature, limit, capacity, direction, site, layout),
            Err(ClockedModuleOutputsError::Definitions(error)) =>
                self.clocked_definition_layout_on_checked(&checked.expressions, limit, capacity, Err(error))
                && (exists|inputs: PortBitLayout, outputs: PortBitLayout|
                    #[trigger] self.routine_bit_layouts_match(drivers.signature, limit, capacity, &inputs, &outputs)),
            Err(ClockedModuleOutputsError::Allocation) => exists|plan: ClockedModuleOutputs|
                #[trigger] self.routine_bit_layouts_match(drivers.signature, limit, capacity, &plan.inputs, &plan.outputs)
                && self.clocked_definition_layout_on_checked(&checked.expressions, limit, capacity, Ok(plan.definitions))
                && plan.drivers@.len() == 0,
            Err(ClockedModuleOutputsError::Wiring { site, reason }) =>
                exists|plan: ClockedModuleOutputs| {
                    let port = plan.drivers@.len();
                    &&& self.routine_bit_layouts_match(drivers.signature, limit, capacity, &plan.inputs, &plan.outputs)
                    &&& self.clocked_definition_layout_on_checked(&checked.expressions, limit, capacity, Ok(plan.definitions))
                    &&& #[trigger] self.output_wiring_prefix(checked, &plan, plan.drivers@)
                    &&& port < drivers.outputs@.len()
                    &&& site == drivers.signature.outputs@[port as int].annotation
                    &&& clocked_driver_bits_result(&plan.inputs, &plan.definitions,
                        drivers.outputs@[port as int], None, Err(reason))
                },
            Err(ClockedModuleOutputsError::Calls(_)) => false,
        }
    }

    /// 出力の配線列と宣言順の駆動元との対応を取り出す。
    pub(super) proof fn clocked_output_wiring_port(
        &self, checked: &ModuleOutputTypes, limit: u64, capacity: usize, plan: &ClockedModuleOutputs, port: usize,
    )
        requires self.outputs_on_checked(checked, limit, capacity, Ok(*plan)),
        ensures
            plan.drivers@.len() == plan.outputs.ranges_model().len(),
            port < plan.drivers@.len() ==> {
                let drivers = checked.expressions.typed.sources.roots.wiring.drivers;
                let row = plan.drivers@[port as int];
                let range = plan.outputs.ranges_model()[port as int];
                &&& row@.len() == range.end - range.start
                &&& clocked_driver_bits_result(&plan.inputs, &plan.definitions, drivers.outputs@[port as int], None, Ok(row))
            },
    {
        reveal(UseAliases::output_wiring_prefix);
    }

    /// 同じ型表を使ってポートと定義を配置し、公開出力を駆動する配線を作る。
    pub(super) fn wire_clocked_outputs(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, checked: &ModuleOutputTypes<'p, 'a>,
    ) -> (result: Result<ClockedModuleOutputs, ClockedModuleOutputsError<'p, 'a>>)
        requires self.can_resolve(), self.module_output_types_result(owner, limit, Ok(Some(*checked))),
        ensures
            self.outputs_on_checked(checked, limit, capacity, result),
            result matches Ok(plan) ==> plan.drivers@.len() == plan.outputs.ranges_model().len(),
    {
        let drivers = &checked.expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_output_types_evidence(owner, limit, *checked);
            self.module_selections_evidence(owner, limit, checked.expressions);
            self.module_output_driver(owner, limit, *drivers, 0);
            self.typed_signature_bit_widths(owner.file, owner.entry, limit, drivers.signature);
        }
        let (inputs, outputs) = match self.prepare_routine_bit_layouts((owner.file, owner.entry), &drivers.signature, limit, capacity) {
            Ok(layouts) => layouts,
            Err(RoutineBitLayoutError::Structure(error)) => return Err(ClockedModuleOutputsError::Structure(error)),
            Err(RoutineBitLayoutError::Port(direction, site, layout)) => return Err(ClockedModuleOutputsError::Port { direction, site, layout }),
        };
        let definitions = match self.place_clocked_definitions(owner, limit, capacity, &checked.expressions) {
            Ok(layout) => layout,
            Err(error) => return Err(ClockedModuleOutputsError::Definitions(error)),
        };
        let mut plan = ClockedModuleOutputs { inputs, outputs, definitions, drivers: Vec::new() };
        if plan.drivers.try_reserve_exact(drivers.outputs.len()).is_err() {
            assert(self.outputs_on_checked(checked, limit, capacity, Err(ClockedModuleOutputsError::Allocation)));
            return Err(ClockedModuleOutputsError::Allocation);
        }
        let mut index = 0;
        assert(self.output_wiring_prefix(checked, &plan, plan.drivers@)) by { reveal(UseAliases::output_wiring_prefix); };
        while index < drivers.outputs.len()
            invariant
                self.can_resolve(),
                self.module_output_types_result(owner, limit, Ok(Some(*checked))),
                self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
                *drivers == checked.expressions.typed.sources.roots.wiring.drivers,
                index == plan.drivers@.len() <= drivers.outputs@.len()
                    == drivers.signature.outputs@.len() == plan.outputs.ranges_model().len(),
                self.routine_bit_layouts_match(drivers.signature, limit, capacity, &plan.inputs, &plan.outputs),
                self.clocked_definition_layout_on_checked(&checked.expressions, limit, capacity, Ok(plan.definitions)),
                self.output_wiring_prefix(checked, &plan, plan.drivers@),
            decreases drivers.outputs@.len() - index,
        {
            let driver = drivers.outputs[index];
            let wires = match clocked_driver_bits(&plan.inputs, &plan.definitions, driver, None) {
                Ok(wires) => wires,
                Err(reason) => {
                    let site = copy_location(&drivers.signature.outputs[index].annotation);
                    assert(self.outputs_on_checked(checked, limit, capacity, Err(ClockedModuleOutputsError::Wiring { site, reason })));
                    return Err(ClockedModuleOutputsError::Wiring { site, reason });
                },
            };
            proof { self.output_driver_width_matches(owner, limit, capacity, checked, &plan, index, wires); }
            let ghost previous = plan;
            plan.drivers.push(wires);
            assert(self.output_wiring_prefix(checked, &plan, plan.drivers@)) by {
                reveal(UseAliases::output_wiring_prefix);
                assert forall|i: int| 0 <= i < plan.drivers@.len() implies {
                    let row = #[trigger] plan.drivers@[i];
                    let range = plan.outputs.ranges_model()[i];
                    &&& row@.len() == range.end - range.start
                    &&& clocked_driver_bits_result(&plan.inputs, &plan.definitions, drivers.outputs@[i], None, Ok(row))
                } by {
                    if i < index { assert(plan.drivers@[i] == previous.drivers@[i]); }
                };
            };
            index += 1;
        }
        Ok(plan)
    }

    /// 出力の配線と診断が、同じモジュールの型検査結果に対応することを表す。
    pub closed spec fn clocked_module_outputs_result(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize,
        result: Result<Option<ClockedModuleOutputs>, ClockedModuleOutputsError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_calls_result(owner, limit, Ok(None)),
            Err(ClockedModuleOutputsError::Calls(error)) => self.module_calls_result(owner, limit, Err(error)),
            _ => exists|checked: ModuleCalls| #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
                && self.outputs_on_checked(&checked.module, limit, capacity, match result {
                    Ok(Some(plan)) => Ok(plan),
                    Err(error) => Err(error),
                    _ => arbitrary(),
                }),
        }
    }

    /// 公開出力を宣言順に、入力ビットまたは定義スロット内のビットへ結び付ける。
    ///
    /// `capacity` は入力、出力、定義の各平坦ビット列に対する上限。
    /// 指定した位置でモジュール本体が得られなければ `Ok(None)` を返す。
    ///
    /// # Errors
    ///
    /// 型と呼び出し、入出力ポートの配置、定義の配置、公開出力の配線の順に検査する。
    pub fn plan_clocked_outputs(&self, owner: ModuleBodyPosition, limit: u64, capacity: usize)
        -> (result: Result<Option<ClockedModuleOutputs>, ClockedModuleOutputsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            self.clocked_module_outputs_result(owner, limit, capacity, result),
            result matches Ok(Some(plan)) ==> plan.drivers@.len() == plan.outputs.ranges_model().len(),
    {
        let checked = match self.check_module_calls(owner, limit) {
            Ok(Some(checked)) => checked,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ClockedModuleOutputsError::Calls(error)),
        };
        proof { self.module_calls_type_evidence(owner, limit, &checked); }
        match self.wire_clocked_outputs(owner, limit, capacity, &checked.module) {
            Ok(plan) => Ok(Some(plan)),
            Err(error) => Err(error),
        }
    }
}

} // verus!
