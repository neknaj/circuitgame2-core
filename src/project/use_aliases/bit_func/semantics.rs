//! ポートと定義ごとのビット列で組み合わせ回路の評価を定める。

use vstd::prelude::*;
#[cfg(verus_only)]
use super::{BitFuncRhs, CheckedBitDefinition, CheckedBitFunc, OutputDriver, SingleBitOperand, checked_bit_func_available, literal_bytes};
#[cfg(verus_only)]
use crate::syntax::bit_literal_value_at;
#[cfg(verus_only)]
use crate::project::bit_selection_matches;

verus! {

pub(super) open spec fn driver_values(inputs: Seq<Seq<bool>>, definitions: Seq<Seq<bool>>, driver: OutputDriver) -> Seq<bool> {
    match driver {
        OutputDriver::Input(port) => inputs[port as int],
        OutputDriver::Definition(index) => definitions[index as int],
    }
}

pub(super) open spec fn operand_value(inputs: Seq<Seq<bool>>, definitions: Seq<Seq<bool>>, operand: SingleBitOperand) -> bool {
    match operand {
        SingleBitOperand::Driver(driver) => driver_values(inputs, definitions, driver)[0],
        SingleBitOperand::Constant(value) => value,
    }
}

/// 宣言順の連接引数から、引数ごとの低位順のビット列を得る。
pub(super) open spec fn concat_operand_values(
    inputs: Seq<Seq<bool>>, definitions: Seq<Seq<bool>>, operands: Seq<(SingleBitOperand, u64)>,
) -> Seq<Seq<bool>> {
    operands.map_values(|item: (SingleBitOperand, u64)| match item.0 {
        SingleBitOperand::Constant(bit) => seq![bit],
        SingleBitOperand::Driver(driver) => driver_values(inputs, definitions, driver),
    })
}

#[verifier::opaque]
pub(super) open spec fn definition_values(rhs: BitFuncRhs, inputs: Seq<Seq<bool>>, definitions: Seq<Seq<bool>>) -> Seq<bool> {
    match rhs {
        BitFuncRhs::Driver(driver) => driver_values(inputs, definitions, driver),
        BitFuncRhs::Constant(bit) => seq![bit],
        BitFuncRhs::Nor { left, right } =>
            seq![!(operand_value(inputs, definitions, left) || operand_value(inputs, definitions, right))],
        BitFuncRhs::Selection { input, selection } =>
            Seq::new(selection.count as nat,
                |i: int| driver_values(inputs, definitions, input)[selection.start + i * selection.stride]),
        BitFuncRhs::Concat | BitFuncRhs::BitVector => Seq::empty(),
        BitFuncRhs::CallOutput { .. } | BitFuncRhs::NorCallOutput { .. } => arbitrary(),
    }
}

pub(super) open spec fn checked_definition_values(
    definition: CheckedBitDefinition, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>,
) -> Seq<bool> {
    if definition.rhs is BitVector {
        Seq::new(definition.width as nat,
            |i: int| bit_literal_value_at(literal_bytes(definition.expression), i as nat))
    } else if definition.rhs is Concat {
        concat_operand_values(inputs, prior, definition.operands@).flatten()
    } else {
        definition_values(definition.rhs, inputs, prior)
    }
}

/// 入力上の半開区間が、直結または刻み1の選択に対応することを表す。
pub(super) open spec fn contiguous_rhs_matches(
    rhs: BitFuncRhs, input: OutputDriver, start: u64, end: u64, width: u64,
) -> bool {
    &&& start < end <= width
    &&& if start == 0 && end == width {
        rhs == BitFuncRhs::Driver(input)
    } else {
        rhs matches BitFuncRhs::Selection { input: driver, selection }
            && driver == input
            && selection.start == start && selection.count == end - start && selection.stride == 1
            && selection.last == end - 1
            && bit_selection_matches(width, selection.start, selection.count, selection.stride, Ok(selection.last))
    }
}

/// 直結と刻み1の選択が、半開区間のビットを元の順序で返すことを示す。
pub(super) proof fn contiguous_rhs_preserves_range(
    rhs: BitFuncRhs, inputs: Seq<Seq<bool>>, definitions: Seq<Seq<bool>>,
    input: OutputDriver, start: u64, end: u64, width: u64,
)
    requires
        contiguous_rhs_matches(rhs, input, start, end, width),
        driver_values(inputs, definitions, input).len() == width,
    ensures
        definition_values(rhs, inputs, definitions)
            == driver_values(inputs, definitions, input).subrange(start as int, end as int),
{
    reveal(definition_values);
    let value = driver_values(inputs, definitions, input);
    assert(definition_values(rhs, inputs, definitions) =~= value.subrange(start as int, end as int));
}

pub(super) open spec fn bit_func_inputs_match(source: &CheckedBitFunc, inputs: Seq<Seq<bool>>) -> bool {
    &&& inputs.len() == source.input_widths@.len()
    &&& forall|i: int| 0 <= i < inputs.len()
        ==> (#[trigger] inputs[i]).len() == source.input_widths@[i]
}

#[verifier::opaque]
pub(super) open spec fn bit_func_definitions_match(source: &CheckedBitFunc, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>) -> bool {
    &&& values.len() == source.definitions@.len()
    &&& forall|i: int| 0 <= i < values.len() ==> {
        let definition = source.definitions@[i];
        &&& (#[trigger] values[i]).len() == definition.width
        &&& values[i] == checked_definition_values(definition, inputs, values.take(i))
    }
}

pub(super) open spec fn bit_func_outputs_match(
    source: &CheckedBitFunc, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
) -> bool {
    &&& outputs.len() == source.output_drivers@.len()
    &&& forall|i: int| 0 <= i < outputs.len() ==>
        (#[trigger] outputs[i]) == driver_values(inputs, values, source.output_drivers@[i])
}

/// 署名に合う入力から各定義を評価し、宣言順に出力のビット列を得ることを表す。
pub closed spec fn bit_func_evaluation(source: &CheckedBitFunc, inputs: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>) -> bool {
    &&& checked_bit_func_available(source)
    &&& bit_func_inputs_match(source, inputs)
    &&& exists|values: Seq<Seq<bool>>| #[trigger] bit_func_definitions_match(source, inputs, values)
        && bit_func_outputs_match(source, inputs, values, outputs)
}

pub(super) proof fn bit_func_evaluation_intro(
    source: &CheckedBitFunc, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
)
    requires
        checked_bit_func_available(source),
        bit_func_inputs_match(source, inputs),
        bit_func_definitions_match(source, inputs, values),
        bit_func_outputs_match(source, inputs, values, outputs),
    ensures bit_func_evaluation(source, inputs, outputs),
{
}

pub(super) proof fn bit_func_evaluation_values(
    source: &CheckedBitFunc, inputs: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
) -> (values: Seq<Seq<bool>>)
    requires bit_func_evaluation(source, inputs, outputs),
    ensures
        checked_bit_func_available(source),
        bit_func_inputs_match(source, inputs),
        bit_func_definitions_match(source, inputs, values),
        bit_func_outputs_match(source, inputs, values, outputs),
{
    choose|values: Seq<Seq<bool>>| #[trigger] bit_func_definitions_match(source, inputs, values)
        && bit_func_outputs_match(source, inputs, values, outputs)
}

proof fn definition_values_prefix_agree(
    source: &CheckedBitFunc, inputs: Seq<Seq<bool>>, left: Seq<Seq<bool>>, right: Seq<Seq<bool>>, end: nat,
)
    requires
        bit_func_definitions_match(source, inputs, left),
        bit_func_definitions_match(source, inputs, right),
        end <= source.definitions@.len(),
    ensures left.take(end as int) == right.take(end as int),
    decreases end,
{
    if end == 0 {
        assert(left.take(0) =~= right.take(0));
    } else {
        let i = (end - 1) as int;
        definition_values_prefix_agree(source, inputs, left, right, i as nat);
        let definition = source.definitions@[i];
        assert(left[i] == checked_definition_values(definition, inputs, left.take(i))) by {
            reveal(bit_func_definitions_match);
        };
        assert(right[i] == checked_definition_values(definition, inputs, right.take(i))) by {
            reveal(bit_func_definitions_match);
        };
        assert(left.len() == right.len() == source.definitions@.len()) by {
            reveal(bit_func_definitions_match);
        };
        assert forall|j: int| 0 <= j < end implies
            (#[trigger] left.take(end as int)[j]) == (#[trigger] right.take(end as int)[j]) by {
            if j < i {
                assert(left.take(i)[j] == right.take(i)[j]);
            }
        };
        assert(left.take(end as int) =~= right.take(end as int));
    }
}

/// 同じ関数と入力に対し、宣言順の出力と各ポートのビット列が一意に定まることを示す。
pub proof fn bit_func_evaluations_agree(
    source: &CheckedBitFunc, inputs: Seq<Seq<bool>>, left: Seq<Seq<bool>>, right: Seq<Seq<bool>>,
)
    requires bit_func_evaluation(source, inputs, left), bit_func_evaluation(source, inputs, right),
    ensures left == right,
{
    let a = choose|values: Seq<Seq<bool>>| #[trigger] bit_func_definitions_match(source, inputs, values)
        && bit_func_outputs_match(source, inputs, values, left);
    let b = choose|values: Seq<Seq<bool>>| #[trigger] bit_func_definitions_match(source, inputs, values)
        && bit_func_outputs_match(source, inputs, values, right);
    definition_values_prefix_agree(source, inputs, a, b, source.definitions@.len());
    assert(a.len() == b.len() == source.definitions@.len()) by { reveal(bit_func_definitions_match); };
    assert(a =~= a.take(a.len() as int));
    assert(b =~= b.take(b.len() as int));

    assert(left =~= right);
}

} // verus!
