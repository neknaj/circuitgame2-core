//! 型と結線が確定したビット列の組み合わせ回路を表す。

mod compile;
mod frontend;
mod generated;
#[cfg(verus_only)]
pub use generated::{expanded_bit_func_matches, expanded_definition_cause_location, expanded_definition_diagnostic_wraps, expanded_function_diagnostic_source, expanded_function_wiring_diagnostic};
pub use generated::{CheckedGeneratedAliasFunc, ExpandedFuncWiringError, GeneratedWiringError};
#[cfg(verus_only)]
pub use generated::{
    collected_aliases_match, collected_alias_prefix, collected_alias_step, function_generated_aliases_match,
    generated_alias_element_matches, generated_alias_elements_match, generated_alias_function_wiring, generated_port_names_match,
};
pub use compile::{ExpandFunctionsError, ExpandedFunctions, FunctionBuildDiagnostic};
pub(super) use compile::ClockedFunctionTemplate;
mod expansion;
mod templates;
mod instances;
mod lowering;
mod semantics;

pub use frontend::{BitFuncError, UnsupportedBitFunc};
pub(super) use frontend::RoutineBitLayoutError;
#[cfg(verus_only)]
pub(super) use frontend::has_structure_port;
pub use lowering::{BitFuncLowerError, LoweredBitFunc};
#[cfg(verus_only)]
pub use lowering::{bit_func_lowering_preserves_evaluation, lowered_bit_func_result, port_values};
#[cfg(verus_only)]
pub use semantics::{bit_func_evaluation, bit_func_evaluations_agree};

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{OutputDriver, SingleBitOperand, TypedRoutineSignature};
use super::selection_arguments::CheckedBitSelection;
use crate::project::LocatedName;
#[cfg(verus_only)]
use crate::project::{bit_selection_matches, location_in_source};
#[cfg(verus_only)]
use crate::syntax::{AtomKind, bare_atom_kind, bit_literal_value_at};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

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
    /// 引数順にビット列を連接する。各引数は定義の `operands` に保持する。
    Concat,
    /// 元の二進または十六進リテラルを、確定した幅の定数配線にする。
    BitVector,
    /// 展開する呼び出しの番号と、その宣言上の出力ポート番号。
    CallOutput { group: usize, port: usize },
    /// 根 NOR の候補表を指す添字。出力は1ビット。
    NorCallOutput { root: usize },
}

/// 元ソース位置と値の幅が確定した定義。
#[derive(Debug)]
pub(super) struct CheckedBitDefinition<'p, 'a> {
    pub(super) expression: LocatedName<'p, 'a>,
    pub(super) width: u64,
    pub(super) rhs: BitFuncRhs,
    pub(super) operands: Vec<(SingleBitOperand, u64)>,
}

/// 入出力の幅、定義の順序、出力の駆動元が確定した組み合わせ回路。
#[derive(Debug)]
pub struct CheckedBitFunc<'p, 'a> {
    pub(super) signature: TypedRoutineSignature<'p, 'a>,
    pub(super) input_widths: Vec<u64>,
    pub(super) output_widths: Vec<u64>,
    pub(super) definitions: Vec<CheckedBitDefinition<'p, 'a>>,
    pub(super) output_drivers: Vec<OutputDriver>,
}

impl<'p, 'a> CheckedBitFunc<'p, 'a> {
    /// 元の宣言型とソース位置を保持する入出力の署名を返す。
    pub fn signature(&self) -> (signature: &TypedRoutineSignature<'p, 'a>)
        ensures *signature == self.signature_model(),
    {
        &self.signature
    }

    /// 配線変換の対象になった関数の署名を表す。
    pub closed spec fn signature_model(&self) -> TypedRoutineSignature<'p, 'a> {
        self.signature
    }

    #[verifier::type_invariant]
    spec fn drivers_and_widths_match(&self) -> bool {
        checked_bit_func_available(self)
    }
}

pub(super) open spec fn bit_driver_width(
    inputs: Seq<u64>, prior: Seq<CheckedBitDefinition>, driver: OutputDriver,
) -> Option<u64> {
    match driver {
        OutputDriver::Input(port) => {
            if port < inputs.len() { Some(inputs[port as int]) } else { None }
        },
        OutputDriver::Definition(index) => {
            if index < prior.len() { Some(prior[index as int].width) } else { None }
        },
    }
}

pub(super) open spec fn nor_operand_matches(
    inputs: Seq<u64>, prior: Seq<CheckedBitDefinition>, operand: SingleBitOperand,
) -> bool {
    match operand {
        SingleBitOperand::Driver(driver) => bit_driver_width(inputs, prior, driver) == Some(1),
        SingleBitOperand::Constant(_) => true,
    }
}

pub(super) open spec fn concat_operands_fit(
    inputs: Seq<u64>, prior: Seq<CheckedBitDefinition>, operands: Seq<(SingleBitOperand, u64)>,
) -> bool {
    forall|i: int| 0 <= i < operands.len() ==> {
        let (operand, width) = #[trigger] operands[i];
        &&& width > 0
        &&& match operand {
            SingleBitOperand::Constant(_) => width == 1,
            SingleBitOperand::Driver(driver) => bit_driver_width(inputs, prior, driver) == Some(width),
        }
    }
}

pub(super) open spec fn literal_bytes(location: LocatedName) -> Seq<u8> {
    location.source.text.spec_bytes()[location.span.start as int..location.span.end as int]
}

pub(super) open spec fn bit_vector_token(bytes: Seq<u8>) -> bool {
    bare_atom_kind(bytes) == Some(AtomKind::Binary) || bare_atom_kind(bytes) == Some(AtomKind::Hexadecimal)
}

/// 参照する幅が定義済みで、各右辺の結果幅と定義幅が一致することを表す。
pub(super) open spec fn bit_definition_matches(
    inputs: Seq<u64>, prior: Seq<CheckedBitDefinition>, definition: CheckedBitDefinition,
) -> bool {
    &&& definition.width > 0
    &&& location_in_source(definition.expression)
    &&& !(definition.rhs is Concat) ==> definition.operands@.len() == 0
    &&& match definition.rhs {
        BitFuncRhs::CallOutput { .. } | BitFuncRhs::NorCallOutput { .. } => false,
        BitFuncRhs::Driver(driver) => bit_driver_width(inputs, prior, driver) == Some(definition.width),
        BitFuncRhs::Constant(_) => definition.width == 1,
        BitFuncRhs::Nor { left, right } => definition.width == 1
            && nor_operand_matches(inputs, prior, left) && nor_operand_matches(inputs, prior, right),
        BitFuncRhs::Selection { input, selection } =>
            bit_driver_width(inputs, prior, input) matches Some(width)
            && definition.width == selection.count
            && bit_selection_matches(width, selection.start, selection.count, selection.stride, Ok(selection.last)),
        BitFuncRhs::Concat => 0 < definition.operands@.len()
            && concat_operands_fit(inputs, prior, definition.operands@)
            && crate::project::concat_prefix_width(
                definition.operands@.map_values(|item: (SingleBitOperand, u64)| item.1),
                definition.operands@.len()) == definition.width,
        BitFuncRhs::BitVector => bit_vector_token(literal_bytes(definition.expression))
            && forall|bit: nat| bit >= definition.width ==> !#[trigger] bit_literal_value_at(literal_bytes(definition.expression), bit),
    }
}

/// すべてのポートに正の幅があり、定義と出力の駆動元が型に合うことを表す。
#[verifier::opaque]
pub closed spec fn checked_bit_func_available(function: &CheckedBitFunc) -> bool {
    let signature = &function.signature;
    let definitions = function.definitions@;
    let drivers = function.output_drivers@;
    &&& function.input_widths@.len() == signature.inputs@.len()
    &&& function.output_widths@.len() == signature.outputs@.len()
    &&& forall|i: int| 0 <= i < function.input_widths@.len() ==> (#[trigger] function.input_widths@[i]) > 0
    &&& 0 < function.output_widths@.len() == drivers.len()
    &&& forall|i: int| 0 <= i < drivers.len() ==> {
        let width = #[trigger] function.output_widths@[i];
        &&& width > 0
        &&& bit_driver_width(function.input_widths@, definitions, drivers[i]) == Some(width)
    }
    &&& forall|i: int| 0 <= i < definitions.len() ==>
        bit_definition_matches(function.input_widths@, definitions.take(i), #[trigger] definitions[i])
}

} // verus!
