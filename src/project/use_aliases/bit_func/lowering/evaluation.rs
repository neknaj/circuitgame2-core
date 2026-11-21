//! 生成したネットリストの評価を、ポートと定義ごとの参照意味論に対応付ける。

use super::*;
use super::call_group::WiringView;
use super::super::semantics::{
    bit_func_definitions_match, bit_func_evaluation, bit_func_evaluation_intro, bit_func_inputs_match, bit_func_outputs_match,
    checked_definition_values, concat_operand_values, definition_values, driver_values, operand_value,
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

/// 各定義のビット範囲を使って、配線から定義順の値を得る。
pub(super) open spec fn definition_values_from_wires(
    layout: &PortBitLayout, wires: Seq<Wire>, inputs: Seq<bool>, gates: Seq<bool>,
) -> Seq<Seq<bool>> {
    let ranges = layout.ranges_model();
    Seq::new(ranges.len(), |i: int| {
        let range = ranges[i];
        Seq::new((range.end - range.start) as nat, |bit: int|
            wire_value(wires[range.start + bit], inputs, gates))
    })
}

#[verifier::opaque]
spec fn definition_wire_values(lowered: &LoweredBitFunc, input: Seq<bool>, gates: Seq<bool>) -> Seq<Seq<bool>> {
    definition_values_from_wires(&lowered.layouts.definitions, lowered.definition_wires@, input, gates)
}

proof fn driver_bit_value(
    input_widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, wires: Seq<Wire>, capacity: usize, scope: int,
    input: Seq<bool>, gates: Seq<bool>, driver: OutputDriver, width: u64, bit: int,
)
    requires
        body_definition_layouts(input_widths, definitions, capacity, layouts),
        input.len() == layouts.inputs.total_bits_model(),
        0 <= scope <= definitions.len(),
        preceding_port_bits(definition_widths(definitions), scope as nat) <= wires.len(),
        wires_available(wires, layouts.inputs.total_bits_model(), gates.len()),
        bit_driver_width(input_widths, definitions.take(scope), driver) == Some(width),
        0 <= bit < width,
    ensures
        driver_values(port_values(&layouts.inputs, input),
            definition_values_from_wires(&layouts.definitions, wires, input, gates).take(scope), driver).len() == width,
        driver_values(port_values(&layouts.inputs, input),
            definition_values_from_wires(&layouts.definitions, wires, input, gates).take(scope), driver)[bit] == wire_value(
                driver_wire(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
                    wires, driver, bit), input, gates),
{
    match driver {
        OutputDriver::Input(port) => {
            reveal(port_values);
            let range = layouts.inputs.ranges_model()[port as int];
            assert(input_widths[port as int] == width);
            assert(port_values(&layouts.inputs, input)[port as int]
                == input.subrange(range.start as int, range.end as int));
        },
        OutputDriver::Definition(index) => {
            let widths = definition_widths(definitions);
            port_bit_layout_port(widths, capacity, layouts.definitions, index);
            preceding_port_bits_grow(widths, (index + 1) as nat, scope as nat);
            let range = layouts.definitions.ranges_model()[index as int];
            assert(definition_widths(definitions)[index as int] == width);
            let values = definition_values_from_wires(&layouts.definitions, wires, input, gates);
            assert(values.take(scope)[index as int] == values[index as int]);
            assert(values[index as int] == Seq::new(width as nat, |j: int|
                wire_value(wires[range.start + j], input, gates)));
        },
    }
}

proof fn operand_matches_wire(
    input_widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, wires: Seq<Wire>, capacity: usize, scope: usize,
    input: Seq<bool>, gates: Seq<bool>, operand: SingleBitOperand,
)
    requires
        body_definition_layouts(input_widths, definitions, capacity, layouts),
        input.len() == layouts.inputs.total_bits_model(),
        scope < definitions.len(),
        nor_operand_matches(input_widths, definitions.take(scope as int), operand),
        scope < layouts.definitions.ranges_model().len(),
        layouts.definitions.ranges_model()[scope as int].end <= wires.len(),
        wires_available(wires, layouts.inputs.total_bits_model(), gates.len()),
        layouts.definitions.ranges_model()[scope as int].start
            == preceding_port_bits(definition_widths(definitions), scope as nat),

    ensures
        operand_value(port_values(&layouts.inputs, input),
            definition_values_from_wires(&layouts.definitions, wires, input, gates).take(scope as int), operand)
            == wire_value(operand_wire(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
                wires.take(layouts.definitions.ranges_model()[scope as int].start as int), operand),
                input, gates),
{
    if let SingleBitOperand::Driver(driver) = operand {
        let range = layouts.definitions.ranges_model()[scope as int];
        let used = range.start as int;
        assert(range.end <= wires.len());
        body_driver_bits_fit_layout(input_widths, definitions, layouts, capacity, scope as int, used, driver, 1, 0);
        driver_bit_value(input_widths, definitions, layouts, wires, capacity, scope as int, input, gates, driver, 1, 0);
        if let OutputDriver::Definition(i) = driver {
            let index = layouts.definitions.ranges_model()[i as int].start as int;
            assert(wires.take(used)[index] == wires[index]);
        }
    }
}

proof fn mapped_wire_parts_flatten(
    parts: Seq<Seq<Wire>>, input: Seq<bool>, gates: Seq<bool>,
)
    ensures parts.flatten().map_values(|wire: Wire| wire_value(wire, input, gates))
        == parts.map_values(|part: Seq<Wire>| part.map_values(|wire: Wire| wire_value(wire, input, gates))).flatten(),
    decreases parts.len(),
{
    if parts.len() > 0 {
        let earlier = parts.drop_last();
        let last = parts.last();
        let value = |wire: Wire| wire_value(wire, input, gates);
        let values = |part: Seq<Wire>| part.map_values(value);
        let mapped = earlier.map_values(values);
        mapped_wire_parts_flatten(earlier, input, gates);
        assert(earlier.push(last) =~= parts);
        earlier.lemma_flatten_push(last);
        assert(mapped.push(last.map_values(value)) =~= parts.map_values(values));
        mapped.lemma_flatten_push(last.map_values(value));
        assert((earlier.flatten() + last).map_values(value) =~=
            earlier.flatten().map_values(value) + last.map_values(value));
    }
}

/// 連接で追加した配線の値を、引数ごとの参照値の連接に対応付ける。
proof fn concat_wiring_preserves_values(
    input_widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, wiring: WiringView, capacity: usize, i: usize,
    input: Seq<bool>, gates: Seq<bool>,
)
    requires
        body_definition_layouts(input_widths, definitions, capacity, layouts),
        input.len() == layouts.inputs.total_bits_model(),
        i < definitions.len(),
        bit_definition_matches(input_widths, definitions.take(i as int), definitions[i as int]),
        definitions[i as int].rhs is Concat,
        slot_wiring_matches(definitions[i as int], layouts, wiring.definitions, wiring.gates, wiring.origins, i as int),
        wires_available(wiring.definitions, layouts.inputs.total_bits_model(), gates.len()),
    ensures
        definition_values_from_wires(&layouts.definitions, wiring.definitions, input, gates)[i as int] == checked_definition_values(
            definitions[i as int], port_values(&layouts.inputs, input),
            definition_values_from_wires(&layouts.definitions, wiring.definitions, input, gates).take(i as int)),
{
    let wires = wiring.definitions;
    let operands = definitions[i as int].operands@;
    let input_ranges = layouts.inputs.ranges_model();
    let definition_ranges = layouts.definitions.ranges_model();
    let range = definition_ranges[i as int];
    port_bit_layout_port(definition_widths(definitions), capacity, layouts.definitions, i);
    let prefix = wires.take(range.start as int);
    let parts = concat_operand_wires(input_ranges, definition_ranges, prefix, operands);
    let inputs = port_values(&layouts.inputs, input);
    let values = definition_values_from_wires(&layouts.definitions, wiring.definitions, input, gates).take(i as int);
    let expected = concat_operand_values(inputs, values, operands);
    let mapped = parts.map_values(|part: Seq<Wire>| part.map_values(|wire: Wire| wire_value(wire, input, gates)));
    assert forall|j: int| 0 <= j < operands.len() implies (#[trigger] mapped[j]) == expected[j] by {
        let (operand, width) = operands[j];
        assert(parts[j].len() == width && width > 0);
        match operand {
            SingleBitOperand::Constant(bit) => {
                assert(width == 1);
                assert(mapped[j] =~= seq![bit]);
            },
            SingleBitOperand::Driver(driver) => {
                driver_bit_value(input_widths, definitions, layouts, wires, capacity, i as int, input, gates, driver, width, 0);
                let values = expected[j];
                let part = mapped[j];
                assert(values.len() == part.len());
                assert forall|bit: int| 0 <= bit < width implies (#[trigger] part[bit]) == values[bit] by {
                    body_driver_bits_fit_layout(input_widths, definitions, layouts, capacity, i as int, range.start as int, driver, width, bit);
                    driver_bit_value(input_widths, definitions, layouts, wires, capacity, i as int, input, gates, driver, width, bit);
                    if let OutputDriver::Definition(from) = driver {
                        let at = definition_ranges[from as int].start + bit;
                        assert(prefix[at] == wires[at]);
                    }
                    let generated = Seq::new(width as nat, |at: int| projected_wire(
                        input_ranges, definition_ranges, prefix, concat_operand_projection(operand), at));
                    assert(parts[j] == generated);
                    assert(generated[bit] == projected_wire(
                        input_ranges, definition_ranges, prefix, concat_operand_projection(operand), bit));
                    vstd::arithmetic::mul::lemma_mul_basics(bit);
                    assert(parts[j][bit] == driver_wire(input_ranges, definition_ranges, prefix, driver, bit));
                };
                assert(part =~= values);
            },
        }
    };
    assert(mapped =~= expected);
    mapped_wire_parts_flatten(parts, input, gates);
    let flat = wires.subrange(range.start as int, range.end as int);
    assert(flat == parts.flatten());
    assert(definition_values_from_wires(&layouts.definitions, wiring.definitions, input, gates)[i as int]
        =~= flat.map_values(|wire: Wire| wire_value(wire, input, gates)));
}

/// 一つの定義の配線を評価し、型検査済みの右辺から定まる値と一致することを示す。
pub(super) proof fn slot_values_match_wiring(
    input_widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, wiring: WiringView, capacity: usize, i: usize,
    input: Seq<bool>, gates: Seq<bool>,
)
    requires
        body_definition_layouts(input_widths, definitions, capacity, layouts),
        input.len() == layouts.inputs.total_bits_model(),
        gate_values_match(input, wiring.gates, gates),
        wiring.gates.len() == gates.len(),
        i < definitions.len(),
        bit_definition_matches(input_widths, definitions.take(i as int), definitions[i as int]),
        slot_wiring_matches(definitions[i as int], layouts, wiring.definitions, wiring.gates, wiring.origins, i as int),
        wires_available(wiring.definitions, layouts.inputs.total_bits_model(), gates.len()),
    ensures
        definition_values_from_wires(&layouts.definitions, wiring.definitions, input, gates)[i as int].len() == definitions[i as int].width,
        definition_values_from_wires(&layouts.definitions, wiring.definitions, input, gates)[i as int] == checked_definition_values(
            definitions[i as int], port_values(&layouts.inputs, input),
            definition_values_from_wires(&layouts.definitions, wiring.definitions, input, gates).take(i as int)),
{
    let wires = wiring.definitions;
    port_bit_layout_port(definition_widths(definitions), capacity, layouts.definitions, i);
    reveal(definition_values);
    let value = definition_values_from_wires(&layouts.definitions, wiring.definitions, input, gates)[i as int];
    let inputs = port_values(&layouts.inputs, input);
    let values = definition_values_from_wires(&layouts.definitions, wiring.definitions, input, gates).take(i as int);
    let definition = definitions[i as int];
    let range = layouts.definitions.ranges_model()[i as int];
    let expected = definition_values(definition.rhs, inputs, values);
    let prefix = wires.take(range.start as int);
    let input_ranges = layouts.inputs.ranges_model();
    let definition_ranges = layouts.definitions.ranges_model();

    match definition.rhs {
        BitFuncRhs::BitVector => {
            assert forall|bit: int| 0 <= bit < definition.width implies
                (#[trigger] value[bit]) == checked_definition_values(definition, inputs, values)[bit] by {
                assert(wires[range.start + bit] == Wire::Constant(
                    bit_literal_value_at(literal_bytes(definition.expression), bit as nat)));
            };
            assert(value =~= checked_definition_values(definition, inputs, values));
        },
        BitFuncRhs::Concat => {
            concat_wiring_preserves_values(input_widths, definitions, layouts, wiring, capacity, i, input, gates);
        },
        BitFuncRhs::Constant(value_bit) => {
            assert(wires[range.start as int] == Wire::Constant(value_bit));
            assert(value[0] == value_bit);
            assert(value =~= expected);
        },
        BitFuncRhs::Nor { left, right } => {
            let wire = wires[range.start as int];
            let gate = wire->Gate_0;
            assert(wire == Wire::Gate(gate) && gate < wiring.gates.len());
            let operands = wiring.gates[gate as int];
            operand_matches_wire(input_widths, definitions, layouts, wires, capacity, i, input, gates, left);
            operand_matches_wire(input_widths, definitions, layouts, wires, capacity, i, input, gates, right);
            assert(gates[gate as int] == !(wire_value(operands.left, input, gates) || wire_value(operands.right, input, gates))) by {
                reveal(gate_values_match);
            };
            assert(value[0] == expected[0]);
            assert(value =~= expected);
        },
        BitFuncRhs::CallOutput { .. } => { assert(false); },
        rhs @ (BitFuncRhs::Driver(_) | BitFuncRhs::Selection { .. }) => {
            let (driver, offset, stride) = match rhs {
                BitFuncRhs::Driver(driver) => (driver, 0int, 1int),
                BitFuncRhs::Selection { input, selection } => (input, selection.start as int, selection.stride as int),
                _ => arbitrary(),
            };
            let driver_width = bit_driver_width(input_widths, definitions.take(i as int), driver)->Some_0;
            assert(expected.len() == definition.width) by {
                if definition.rhs is Driver {
                    driver_bit_value(input_widths, definitions, layouts, wires, capacity, i as int, input, gates, driver, driver_width, 0);
                }
            };
            assert forall|bit: int| 0 <= bit < definition.width implies
                (#[trigger] value[bit]) == (#[trigger] expected[bit]) by {
                let selected = offset + bit * stride;
                match rhs {
                    BitFuncRhs::Driver(plain) => {
                        assert(plain == driver && offset == 0 && stride == 1);
                        assert(bit_driver_width(input_widths, definitions.take(i as int), plain)
                            == Some(definition.width));
                        vstd::arithmetic::mul::lemma_mul_basics(bit);
                        assert(selected == bit && driver_width == definition.width);
                        assert(expected == driver_values(inputs, values, driver));
                    },
                    BitFuncRhs::Selection { input: selected_driver, selection } => {
                        assert(driver == selected_driver && offset == selection.start && stride == selection.stride);
                        selected_bit_in_range(driver_width, selection.start, selection.count, selection.stride, selection.last, bit);
                        let selected_values = Seq::new(selection.count as nat,
                            |at: int| driver_values(inputs, values, driver)[selection.start + at * selection.stride]);
                        assert(expected == selected_values);
                        assert(selected_values[bit] == driver_values(inputs, values, driver)[selected]);
                    },
                    _ => { assert(false); },
                }
                body_driver_bits_fit_layout(input_widths, definitions, layouts, capacity, i as int, range.start as int, driver, driver_width, selected);
                driver_bit_value(input_widths, definitions, layouts, wires, capacity, i as int, input, gates, driver, driver_width, selected);
                if let OutputDriver::Definition(from) = driver {
                    let from_index = definition_ranges[from as int].start + selected;
                    assert(prefix[from_index] == wires[from_index]);
                }
                assert(wires[range.start + bit]
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
    let wiring = WiringView {
        definitions: lowered.definition_wires@, gates: lowered.netlist.gates@, origins: lowered.gate_definitions@,
    };
    reveal(layouts_result);
    reveal(nor_evaluation);
    let gates = choose|g: Seq<bool>| #[trigger] gate_values_match(input, lowered.netlist.gates@, g)
        && g.len() == lowered.netlist.gates@.len() && output_values_match(input, g, lowered.netlist.outputs@, output);
    let inputs = port_values(&lowered.layouts.inputs, input);
    let outputs = port_values(&lowered.layouts.outputs, output);
    let values = definition_wire_values(lowered, input, gates);
    reveal(layouts_result);
    reveal(port_values);

    assert(inputs.len() == source.input_widths@.len()) by { reveal(port_values); };
    assert(bit_func_inputs_match(source, inputs)) by {
        reveal(checked_bit_func_available);
        assert forall|i: int| 0 <= i < inputs.len() implies
            (#[trigger] inputs[i]).len() == source.input_widths@[i] by {
            let range = lowered.layouts.inputs.ranges_model()[i];
            assert(inputs[i] == input.subrange(range.start as int, range.end as int));
        };
    };
    assert(bit_func_definitions_match(source, inputs, values)) by {
        reveal(bit_func_definitions_match);
        use_layouts(source, capacity, &lowered.layouts);
        assert(values.len() == source.definitions@.len()) by { reveal(definition_wire_values); };
        vstd::std_specs::vec::axiom_spec_len(&source.definitions);
        assert forall|i: int| 0 <= i < values.len() implies {
            &&& (#[trigger] values[i]).len() == source.definitions@[i].width
            &&& values[i] == checked_definition_values(source.definitions@[i], inputs, values.take(i))
        } by {
            use_bit_definition(source, i);
            assert(definition_wiring_matches(source, &lowered.layouts, wiring.definitions, wiring.gates, wiring.origins, i));
            reveal(definition_wiring_matches);
            reveal(definition_wire_values);
            slot_values_match_wiring(source.input_widths@, source.definitions@, &lowered.layouts, wiring, capacity, i as usize, input, gates);
        };
    };
    assert(bit_func_outputs_match(source, inputs, values, outputs)) by {
        port_bit_layout_size(definition_widths(source.definitions@), capacity, &lowered.layouts.definitions);
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
            let width = source.output_widths@[i];
            assert(port == output.subrange(range.start as int, range.end as int));
            reveal(definition_wire_values);
            driver_bit_value(source.input_widths@, source.definitions@, &lowered.layouts, wiring.definitions, capacity, scope, input, gates, driver, width, 0);
            assert forall|bit: int| 0 <= bit < width implies
                (#[trigger] port[bit]) == (#[trigger] expected[bit]) by {
                driver_bit_value(source.input_widths@, source.definitions@, &lowered.layouts, wiring.definitions, capacity, scope, input, gates, driver, width, bit);
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
