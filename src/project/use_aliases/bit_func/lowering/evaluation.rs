//! 生成したネットリストの評価を、ポートと定義ごとの参照意味論に対応付ける。

use super::*;
use super::super::semantics::{
    bit_func_definitions_match, bit_func_evaluation, bit_func_evaluation_intro, bit_func_inputs_match, bit_func_outputs_match,
    definition_values, driver_values, operand_value,
};
use crate::netlist::{NorEvaluationError, gate_values_match, nor_evaluation, nor_evaluation_result, output_values_match, wire_value};

verus! {

#[verifier::opaque]
/// 平坦なビット列を、配置に従ってポートごとのビット列へ分ける。
pub open spec fn port_values(layout: &PortBitLayout, flat: Seq<bool>) -> Seq<Seq<bool>> {
    Seq::new(layout.ranges_model().len(), |i: int| {
        let range = layout.ranges_model()[i];
        flat.subrange(range.start as int, range.end as int)
    })
}

#[verifier::opaque]
spec fn definition_wire_values(lowered: &LoweredBitFunc, input: Seq<bool>, gates: Seq<bool>) -> Seq<Seq<bool>> {
    let ranges = lowered.layouts.definitions.ranges_model();
    Seq::new(ranges.len(), |i: int| {
        let range = ranges[i];
        Seq::new((range.end - range.start) as nat, |bit: int|
            wire_value(lowered.definition_wires@[range.start + bit], input, gates))
    })
}

proof fn driver_bit_value(
    source: &CheckedBitFunc, lowered: &LoweredBitFunc, capacity: usize, scope: int,
    input: Seq<bool>, gates: Seq<bool>, driver: OutputDriver, width: u64, bit: int,
)
    requires
        layouts_result(source, capacity, Ok(lowered.layouts)),
        input.len() == lowered.layouts.inputs.total_bits_model(),
        lowered.definition_wires@.len() == lowered.layouts.definitions.total_bits_model(),
        0 <= scope <= source.definitions@.len(),
        bit_driver_width(&source.signature, source.definitions@.take(scope), driver) == Some(width),
        0 <= bit < width,
    ensures
        driver_values(port_values(&lowered.layouts.inputs, input),
            definition_wire_values(lowered, input, gates).take(scope), driver).len() == width,
        driver_values(port_values(&lowered.layouts.inputs, input),
            definition_wire_values(lowered, input, gates).take(scope), driver)[bit] == wire_value(
                driver_wire(lowered.layouts.inputs.ranges_model(), lowered.layouts.definitions.ranges_model(),
                    lowered.definition_wires@, driver, bit), input, gates),
{
    reveal(layouts_result);
    match driver {
        OutputDriver::Input(port) => {
            reveal(port_values);
            let range = lowered.layouts.inputs.ranges_model()[port as int];
            assert(port_widths(source.signature.inputs@)[port as int] == width);
            assert(port_values(&lowered.layouts.inputs, input)[port as int]
                == input.subrange(range.start as int, range.end as int));
        },
        OutputDriver::Definition(index) => {
            reveal(definition_wire_values);
            let range = lowered.layouts.definitions.ranges_model()[index as int];
            assert(definition_widths(source.definitions@)[index as int] == width);
            let values = definition_wire_values(lowered, input, gates);
            assert(values.take(scope)[index as int] == values[index as int]);
            assert(values[index as int] == Seq::new(width as nat, |j: int|
                wire_value(lowered.definition_wires@[range.start + j], input, gates)));
        },
    }
}

proof fn operand_matches_wire(
    source: &CheckedBitFunc, lowered: &LoweredBitFunc, capacity: usize, scope: usize,
    input: Seq<bool>, gates: Seq<bool>, operand: SingleBitOperand,
)
    requires
        layouts_result(source, capacity, Ok(lowered.layouts)),
        input.len() == lowered.layouts.inputs.total_bits_model(),
        lowered.definition_wires@.len() == lowered.layouts.definitions.total_bits_model(),
        scope < source.definitions@.len(),
        nor_operand_matches(&source.signature, source.definitions@.take(scope as int), operand),
         scope < lowered.layouts.definitions.ranges_model().len(),
         lowered.layouts.definitions.ranges_model()[scope as int].start
            == preceding_port_bits(definition_widths(source.definitions@), scope as nat),

    ensures
        operand_value(port_values(&lowered.layouts.inputs, input),
            definition_wire_values(lowered, input, gates).take(scope as int), operand)
            == wire_value(operand_wire(lowered.layouts.inputs.ranges_model(), lowered.layouts.definitions.ranges_model(),
                lowered.definition_wires@.take(lowered.layouts.definitions.ranges_model()[scope as int].start as int), operand),
                input, gates),
{
    if let SingleBitOperand::Driver(driver) = operand {
        reveal(layouts_result);
        let range = lowered.layouts.definitions.ranges_model()[scope as int];
        let used = range.start as int;
        assert(range.end <= lowered.definition_wires@.len());
        driver_bits_fit_layout(source, &lowered.layouts, capacity, scope as int, used, driver, 1, 0);
        driver_bit_value(source, lowered, capacity, scope as int, input, gates, driver, 1, 0);
        if let OutputDriver::Definition(i) = driver {
            let index = lowered.layouts.definitions.ranges_model()[i as int].start as int;
            assert(lowered.definition_wires@.take(used)[index] == lowered.definition_wires@[index]);
        }
    }
}

proof fn definition_values_match_wiring(
    source: &CheckedBitFunc, lowered: &LoweredBitFunc, capacity: usize, i: usize,
    input: Seq<bool>, gates: Seq<bool>,
)
    requires
        checked_bit_func_available(source),
        lowered_bit_func_result(source, capacity, Ok(*lowered)),
        input.len() == lowered.layouts.inputs.total_bits_model(),
        gate_values_match(input, lowered.netlist.gates@, gates),
        lowered.netlist.gates@.len() == gates.len(),
        i < source.definitions@.len(),
    ensures
        definition_wire_values(lowered, input, gates)[i as int].len() == source.definitions@[i as int].width,
        definition_wire_values(lowered, input, gates)[i as int] == definition_values(
            source.definitions@[i as int].rhs, port_values(&lowered.layouts.inputs, input),
            definition_wire_values(lowered, input, gates).take(i as int)),
{
    reveal(lowered_bit_func_result);
    use_bit_definition(source, i as int);
    use_layouts(source, capacity, &lowered.layouts);
    port_bit_layout_port(definition_widths(source.definitions@), capacity, lowered.layouts.definitions, i);

    assert(definition_wiring_matches(source, &lowered.layouts, lowered.definition_wires@,
        lowered.netlist.gates@, lowered.gate_definitions@, i as int));
    reveal(definition_wiring_matches);
    reveal(definition_values);
    reveal(definition_wire_values);
    let value = definition_wire_values(lowered, input, gates)[i as int];
    let inputs = port_values(&lowered.layouts.inputs, input);
    let values = definition_wire_values(lowered, input, gates).take(i as int);
    let definition = source.definitions@[i as int];
    let range = lowered.layouts.definitions.ranges_model()[i as int];
    let expected = definition_values(definition.rhs, inputs, values);
    let prefix = lowered.definition_wires@.take(range.start as int);
    let input_ranges = lowered.layouts.inputs.ranges_model();
    let definition_ranges = lowered.layouts.definitions.ranges_model();

    match definition.rhs {
        BitFuncRhs::Constant(value_bit) => {
            assert(lowered.definition_wires@[range.start as int] == Wire::Constant(value_bit));
            assert(value[0] == value_bit);
            assert(value =~= expected);
        },
        BitFuncRhs::Nor { left, right } => {
            let wire = lowered.definition_wires@[range.start as int];
            let gate = wire->Gate_0;
            let operands = lowered.netlist.gates@[gate as int];
            operand_matches_wire(source, lowered, capacity, i, input, gates, left);
            operand_matches_wire(source, lowered, capacity, i, input, gates, right);
            assert(gates[gate as int] == !(wire_value(operands.left, input, gates) || wire_value(operands.right, input, gates))) by {
                reveal(gate_values_match);
            };
            assert(value[0] == expected[0]);
            assert(value =~= expected);
        },
        _ => {
            let (driver, offset, stride) = match definition.rhs {
                BitFuncRhs::Driver(driver) => (driver, 0int, 1int),
                BitFuncRhs::Selection { input, selection } => (input, selection.start as int, selection.stride as int),
                _ => arbitrary(),
            };
            let driver_width = bit_driver_width(&source.signature, source.definitions@.take(i as int), driver)->Some_0;
            assert(expected.len() == definition.width) by {
                if definition.rhs is Driver {
                    driver_bit_value(source, lowered, capacity, i as int, input, gates, driver, driver_width, 0);
                }
            };
            assert forall|bit: int| 0 <= bit < definition.width implies
                (#[trigger] value[bit]) == (#[trigger] expected[bit]) by {
                let selected = offset + bit * stride;
                if let BitFuncRhs::Selection { selection, .. } = definition.rhs {
                    selected_bit_in_range(driver_width, selection.start, selection.count, selection.stride, selection.last, bit);
                }
                driver_bits_fit_layout(source, &lowered.layouts, capacity, i as int, range.start as int, driver, driver_width, selected);
                driver_bit_value(source, lowered, capacity, i as int, input, gates, driver, driver_width, selected);
                if let OutputDriver::Definition(from) = driver {
                    let from_index = definition_ranges[from as int].start + selected;
                    assert(prefix[from_index] == lowered.definition_wires@[from_index]);
                }
                assert(lowered.definition_wires@[range.start + bit]
                    == driver_wire(input_ranges, definition_ranges, prefix, driver, selected));
                assert(expected[bit] == driver_values(inputs, values, driver)[selected]);
            };
            assert(value =~= expected);
        },
    }
}

/// 合法な入力とネットリストの評価結果をポートごとに組み直すと、関数の参照評価になる。
pub(super) proof fn lowered_bit_func_refines_evaluation(
    source: &CheckedBitFunc, capacity: usize, lowered: &LoweredBitFunc, input: Seq<bool>, output: Seq<bool>,
)
    requires
        checked_bit_func_available(source),
        lowered_bit_func_result(source, capacity, Ok(*lowered)),
        nor_evaluation(&lowered.netlist, input, output),
    ensures bit_func_evaluation(source, port_values(&lowered.layouts.inputs, input), port_values(&lowered.layouts.outputs, output)),
{
    reveal(lowered_bit_func_result);
    reveal(nor_evaluation);
    let gates = choose|g: Seq<bool>| #[trigger] gate_values_match(input, lowered.netlist.gates@, g)
        && g.len() == lowered.netlist.gates@.len() && output_values_match(input, g, lowered.netlist.outputs@, output);
    let inputs = port_values(&lowered.layouts.inputs, input);
    let outputs = port_values(&lowered.layouts.outputs, output);
    let values = definition_wire_values(lowered, input, gates);
    reveal(layouts_result);
    reveal(port_values);

    assert(inputs.len() == source.signature.inputs@.len()) by { reveal(port_values); };
    assert(bit_func_inputs_match(source, inputs)) by {
        reveal(checked_bit_func_available);
        assert forall|i: int| 0 <= i < inputs.len() implies
            (#[trigger] inputs[i]).len() == source.signature.inputs@[i].ty->Bits_0 by {
            let range = lowered.layouts.inputs.ranges_model()[i];
            assert(inputs[i] == input.subrange(range.start as int, range.end as int));
            assert(port_widths(source.signature.inputs@)[i] == source.signature.inputs@[i].ty->Bits_0);
        };
    };
    assert(bit_func_definitions_match(source, inputs, values)) by {
        reveal(bit_func_definitions_match);
        use_layouts(source, capacity, &lowered.layouts);
        assert(values.len() == source.definitions@.len()) by { reveal(definition_wire_values); };
        vstd::std_specs::vec::axiom_spec_len(&source.definitions);
        assert forall|i: int| 0 <= i < values.len() implies {
            &&& (#[trigger] values[i]).len() == source.definitions@[i].width
            &&& values[i] == definition_values(source.definitions@[i].rhs, inputs, values.take(i))
        } by {
            definition_values_match_wiring(source, lowered, capacity, i as usize, input, gates);
        };
    };
    assert(bit_func_outputs_match(source, inputs, values, outputs)) by {
        reveal(output_wiring_matches);
        assert(outputs.len() == source.output_drivers@.len()) by { reveal(checked_bit_func_available); };
        assert forall|i: int| 0 <= i < outputs.len() implies
            (#[trigger] outputs[i]) == driver_values(inputs, values, source.output_drivers@[i]) by {
            use_bit_output(source, i);
            let driver = source.output_drivers@[i];
            let range = lowered.layouts.outputs.ranges_model()[i];
            let port = outputs[i];
            let scope = source.definitions@.len() as int;
            assert(values.take(scope) =~= values) by { reveal(definition_wire_values); };
            let expected = driver_values(inputs, values, driver);
            let width = source.signature.outputs@[i].ty->Bits_0;
            assert(port == output.subrange(range.start as int, range.end as int));
            assert(port_widths(source.signature.outputs@)[i] == width);
            driver_bit_value(source, lowered, capacity, scope, input, gates, driver, width, 0);
            assert forall|bit: int| 0 <= bit < width implies
                (#[trigger] port[bit]) == (#[trigger] expected[bit]) by {
                driver_bit_value(source, lowered, capacity, scope, input, gates, driver, width, bit);
                let j = range.start + bit;
                assert(port[bit] == output[j]);
                assert(lowered.netlist.outputs@[range.start + bit] == driver_wire(
                    lowered.layouts.inputs.ranges_model(), lowered.layouts.definitions.ranges_model(),
                    lowered.definition_wires@, driver, bit));
            };
            assert(port =~= expected);
        };
    };
    bit_func_evaluation_intro(source, inputs, values, outputs);
}

/// 宣言された総入力ビット数を渡すと評価が成功し、参照評価と出力が一致することを示す。
pub proof fn bit_func_lowering_preserves_evaluation(
    source: &CheckedBitFunc, capacity: usize, lowered: &LoweredBitFunc, input: Seq<bool>,
    output: Result<Vec<bool>, NorEvaluationError>,
)
    requires
        checked_bit_func_available(source),
        lowered_bit_func_result(source, capacity, Ok(*lowered)),
        input.len() == lowered.input_layout_model().total_bits_model(),
        nor_evaluation_result(lowered.netlist_model(), input, output),
    ensures
        output matches Ok(bits) &&
            bit_func_evaluation(source, port_values(lowered.input_layout_model(), input),
                port_values(lowered.output_layout_model(), bits@)),
{
    assert(nor_evaluation_ready(&lowered.netlist, input.len()));
    let bits = output->Ok_0;
    lowered_bit_func_refines_evaluation(source, capacity, lowered, input, bits@);
}

} // verus!
