//! 型と結線が確定したビット列の組み合わせ回路を表す。

mod frontend;
mod lowering;
mod semantics;

pub use frontend::{BitFuncError, UnsupportedBitFunc};
pub use lowering::{BitFuncLowerError, LoweredBitFunc};
#[cfg(verus_only)]
pub use lowering::{bit_func_lowering_preserves_evaluation, lowered_bit_func_result, port_values};
#[cfg(verus_only)]
pub use semantics::{bit_func_evaluation, bit_func_evaluations_agree};

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{OutputDriver, ResolvedPortType, SingleBitOperand, TypedRoutineSignature};
use super::selection_arguments::CheckedBitSelection;
use crate::project::LocatedName;
#[cfg(verus_only)]
use crate::project::{bit_selection_matches, location_in_source};

verus! {

/// 信号参照を解決し、選択範囲を検査した定義の右辺。
#[derive(Clone, Copy, Debug)]
pub(super) enum BitFuncRhs {
    /// 同じ幅の入力または先行定義との接続。
    Driver(OutputDriver),
    /// 1ビットの定数。
    Constant(bool),
    /// 1ビット入力2本の基底 NOR。
    Nor { left: SingleBitOperand, right: SingleBitOperand },
    /// 入力または先行定義のビット列から値を選ぶ。
    Selection { input: OutputDriver, selection: CheckedBitSelection },
}

/// 元ソース位置と値の幅が確定した定義。
#[derive(Debug)]
pub(super) struct CheckedBitDefinition<'p, 'a> {
    pub(super) expression: LocatedName<'p, 'a>,
    pub(super) width: u64,
    pub(super) rhs: BitFuncRhs,
}

/// 入出力の幅、定義の順序、出力の駆動元が確定した組み合わせ回路。
#[derive(Debug)]
pub struct CheckedBitFunc<'p, 'a> {
    pub(super) signature: TypedRoutineSignature<'p, 'a>,
    pub(super) definitions: Vec<CheckedBitDefinition<'p, 'a>>,
    pub(super) output_drivers: Vec<OutputDriver>,
}

impl<'p, 'a> CheckedBitFunc<'p, 'a> {
    #[verifier::type_invariant]
    spec fn drivers_and_widths_match(&self) -> bool {
        checked_bit_func_available(self)
    }
}

pub(super) open spec fn bit_driver_width(
    signature: &TypedRoutineSignature, prior: Seq<CheckedBitDefinition>, driver: OutputDriver,
) -> Option<u64> {
    match driver {
        OutputDriver::Input(port) => {
            if port < signature.inputs@.len() {
                match signature.inputs@[port as int].ty {
                    ResolvedPortType::Bits(width) => Some(width),
                    _ => None,
                }
            } else {
                None
            }
        },
        OutputDriver::Definition(index) => {
            if index < prior.len() { Some(prior[index as int].width) } else { None }
        },
    }
}

pub(super) open spec fn nor_operand_matches(
    signature: &TypedRoutineSignature, prior: Seq<CheckedBitDefinition>, operand: SingleBitOperand,
) -> bool {
    match operand {
        SingleBitOperand::Driver(driver) => bit_driver_width(signature, prior, driver) == Some(1),
        SingleBitOperand::Constant(_) => true,
    }
}

/// 参照する幅が定義済みで、各右辺の結果幅と定義幅が一致することを表す。
pub(super) open spec fn bit_definition_matches(
    signature: &TypedRoutineSignature, prior: Seq<CheckedBitDefinition>, definition: CheckedBitDefinition,
) -> bool {
    &&& definition.width > 0
    &&& location_in_source(definition.expression)
    &&& match definition.rhs {
        BitFuncRhs::Driver(driver) => bit_driver_width(signature, prior, driver) == Some(definition.width),
        BitFuncRhs::Constant(_) => definition.width == 1,
        BitFuncRhs::Nor { left, right } => definition.width == 1
            && nor_operand_matches(signature, prior, left) && nor_operand_matches(signature, prior, right),
        BitFuncRhs::Selection { input, selection } =>
            bit_driver_width(signature, prior, input) matches Some(width)
            && definition.width == selection.count
            && bit_selection_matches(width, selection.start, selection.count, selection.stride, Ok(selection.last)),
    }
}

/// すべてのポートに正の幅があり、定義と出力の駆動元が型に合うことを表す。
#[verifier::opaque]
pub closed spec fn checked_bit_func_available(function: &CheckedBitFunc) -> bool {
    let signature = &function.signature;
    let definitions = function.definitions@;
    let drivers = function.output_drivers@;
    &&& forall|i: int| 0 <= i < signature.inputs@.len() ==>
        ((#[trigger] signature.inputs@[i]).ty matches ResolvedPortType::Bits(width) && width > 0)
    &&& 0 < signature.outputs@.len() == drivers.len()
    &&& forall|i: int| 0 <= i < drivers.len() ==> {
        let port = #[trigger] signature.outputs@[i];
        &&& port.ty matches ResolvedPortType::Bits(width)
        &&& width > 0
        &&& bit_driver_width(signature, definitions, drivers[i]) == Some(width)
    }
    &&& forall|i: int| 0 <= i < definitions.len() ==>
        bit_definition_matches(signature, definitions.take(i), #[trigger] definitions[i])
}

} // verus!
