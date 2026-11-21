//! 展開した呼び出しの入力値を、元の引数フォームの値に対応付ける。

use super::*;
use super::super::call_arguments::{argument_driver_value, literal_word, lowered_argument_port_value};
use super::super::evaluation::definition_values_from_wires;
use super::super::super::expansion::{
    call_literal_bit, source_argument_bytes, source_call_argument_value, source_call_arguments_match,
};
use super::super::super::semantics::driver_values;
use crate::netlist::wire_value;
use crate::project::FuncWiringResult;
use crate::syntax::{form_span, circuit::call_argument_positions};
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 呼び出し直前の配線から、先行する定義の値を定義順に読む。
spec fn prior_definition_values(
    layouts: &Layouts, step: WiringStep, inputs: Seq<bool>, gates: Seq<bool>,
) -> Seq<Seq<bool>> {
    Seq::new(step.from as nat, |index: int| {
        let range = layouts.definitions.ranges_model()[index];
        Seq::new((range.end - range.start) as nat,
            |bit: int| wire_value(step.before.definitions[range.start + bit], inputs, gates))
    })
}

/// 先行定義の値は、呼び出し直前の配線から読んでも最終配線から読んでも等しい。
proof fn prior_definition_values_from_final(
    body: &LoweringBody, layouts: &Layouts, capacity: usize, step: WiringStep, final_wiring: WiringView,
    inputs: Seq<bool>, gates: Seq<bool>,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        step.from <= body.definitions@.len(),
        step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), step.from as nat),
        wiring_view_is_prefix(step.before, final_wiring),
    ensures
        prior_definition_values(layouts, step, inputs, gates)
            == definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, gates).take(step.from as int),
{
    let prior = prior_definition_values(layouts, step, inputs, gates);
    let final_values = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, gates);
    let prefix = final_values.take(step.from as int);
    let widths = definition_widths(body.definitions@);
    assert forall|i: int| 0 <= i < step.from implies #[trigger] prior[i] == prefix[i] by {
        port_bit_layout_port(widths, capacity, layouts.definitions, i as usize);
        preceding_port_bits_grow(widths, (i + 1) as nat, step.from as nat);
        let range = layouts.definitions.ranges_model()[i];
        assert forall|bit: int| 0 <= bit < prior[i].len() implies #[trigger] prior[i][bit] == prefix[i][bit] by {
            assert(range.start + bit < step.before.definitions.len());
            assert(step.before.definitions[range.start + bit] == final_wiring.definitions[range.start + bit]);
        };
        assert(prior[i] =~= prefix[i]);
    };
    assert(prior =~= prefix);
}

/// 型検査で決まった幅から、駆動元の全ビットが呼び出し前に読めることを示す。
proof fn call_driver_range(
    body: &LoweringBody, layouts: &Layouts, capacity: usize, step: WiringStep, driver: OutputDriver, width: u64,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        step.from <= body.definitions@.len(),
        step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), step.from as nat),
        bit_driver_width(body.input_widths@, body.definitions@.take(step.from as int), driver) == Some(width),
    ensures match driver {
        OutputDriver::Input(i) => {
            let range = layouts.inputs.ranges_model()[i as int];
            &&& i < layouts.inputs.ranges_model().len()
            &&& range.end <= layouts.inputs.total_bits_model()
            &&& range.end - range.start == width
        },
        OutputDriver::Definition(i) => {
            let range = layouts.definitions.ranges_model()[i as int];
            &&& i < step.from && i < layouts.definitions.ranges_model().len()
            &&& range.end <= step.before.definitions.len()
            &&& range.end - range.start == width
        },
    },
{
    if let OutputDriver::Definition(i) = driver {
        let widths = definition_widths(body.definitions@);
        port_bit_layout_port(widths, capacity, layouts.definitions, i);
        preceding_port_bits_grow(widths, (i + 1) as nat, step.from as nat);
    }
}

/// 一つの入力ポートを読み、駆動元の値またはリテラルの値と一致することを示す。
proof fn expanded_port_value(
    body: &LoweringBody, layouts: &Layouts, layout_limit: usize, binding: CallBinding, step: WiringStep,
    forms: Seq<Form>, invocation: CallerArguments, mapped: Seq<Wire>, outputs: Seq<Wire>,
    inputs: Seq<bool>, gates: Seq<bool>, width_limit: u64, port: usize,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        binding_ready(binding, layouts, forms, definition_widths(body.definitions@)),
        step.from == binding.group.outputs.start <= body.definitions@.len(),
        step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), step.from as nat),
        inputs.len() == layouts.inputs.total_bits_model(),
        wires_available(step.after.definitions, layouts.inputs.total_bits_model(), gates.len()),
        call_group_wires_match(binding.group, forms, binding.arguments@, layouts, binding.callee,
            step.before, step.after, binding._output_widths@, invocation, mapped, outputs),
        port < binding._input_widths@.len() == binding.arguments@.len(),
        argument_matches_width(binding.group.expression.source, forms, body.input_widths@,
            body.definitions@.take(step.from as int), binding.arguments@[port as int], binding._input_widths@[port as int], width_limit),
    ensures ({
        let width = binding._input_widths@[port as int];
        let value = port_values(binding.callee.input_layout_model(), instance_wire_values(mapped, inputs, gates))[port as int];
        let argument = binding.arguments@[port as int];
        &&& value.len() == width
        &&& match argument.source {
            CallArgumentSource::Driver(driver) =>
                value == driver_values(port_values(&layouts.inputs, inputs),
                    prior_definition_values(layouts, step, inputs, gates), driver),
            CallArgumentSource::Literal(bits) => {
                let bytes = source_argument_bytes(binding.group.expression.source, forms, argument.form);
                width == bits && value == Seq::new(width as nat, |bit: int| call_literal_bit(bytes, bit as nat))
            },
            CallArgumentSource::Deferred | CallArgumentSource::NestedCall => false,
        }
    }),
{
    reveal(binding_ready);
    reveal(port_values);
    reveal(wires_available);
    let argument = binding.arguments@[port as int];
    let widths = binding._input_widths@;
    port_bit_layout_size(widths, binding._layout_limit@, binding.callee.input_layout_model());
    if let CallArgumentSource::Driver(driver) = argument.source {
        call_driver_range(body, layouts, layout_limit, step, driver, widths[port as int]);
    }
    if argument.source is Literal {
        let span = form_span(forms[argument.form as int]);
        reveal(form_spans_valid);
        assert(span.start < span.end <= invocation.source.text.spec_bytes().len());
    }
    if let CallArgumentSource::Driver(OutputDriver::Definition(i)) = argument.source {
        let bits = invocation.definitions@[i as int];
        assert forall|bit: int| bits.start <= bit < bits.end implies
            wire_available(#[trigger] invocation.wires@[bit], inputs.len(), gates.len()) by {
            assert(step.after.definitions[bit] == invocation.wires@[bit]);
            assert(wire_available(step.after.definitions[bit], inputs.len(), gates.len()));
        };
    }
    lowered_argument_port_value(&invocation, binding.arguments@, binding.callee.input_layout_model(), widths,
        binding._layout_limit@, mapped, inputs, gates, port);
    let value = port_values(binding.callee.input_layout_model(), instance_wire_values(mapped, inputs, gates))[port as int];
    match argument.source {
        CallArgumentSource::Driver(driver) => {
            assert(value == argument_driver_value(&invocation, inputs, gates, driver));
            assert(value == driver_values(port_values(&layouts.inputs, inputs),
                prior_definition_values(layouts, step, inputs, gates), driver));
        },
        CallArgumentSource::Literal(bits) => {
            let raw = literal_word(&invocation, argument.form);
            let source = source_argument_bytes(binding.group.expression.source, forms, argument.form);
            assert(raw == source);
            assert(value == Seq::new(bits as nat, |bit: int| call_literal_bit(source, bit as nat)));
        },
        CallArgumentSource::Deferred | CallArgumentSource::NestedCall => {},
    };
}

proof fn trace_call_frame(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, limit: usize,
    steps: Seq<WiringStep>, slot: usize, group: usize, final_wiring: WiringView, at: int,
)
    requires
        mixed_trace(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring),
        0 <= at < steps.len(),
        steps[at].group_before != steps[at].group_after,
    ensures ({
        let step = steps[at];
        let binding = bindings[step.group_before as int];
        &&& step.group_before < bindings.len()
        &&& step.from == binding.group.outputs.start <= body.definitions@.len()
        &&& step.to == binding.group.outputs.end
        &&& binding.callee.netlist_model().outputs@.len() == binding.callee.output_layout_model().total_bits_model()
        &&& step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), step.from as nat)
        &&& binding_ready(binding, layouts, forms, definition_widths(body.definitions@))
        &&& binding.arguments@.len() == binding._input_widths@.len()
        &&& port_bit_layout_result(binding._input_widths@, binding._layout_limit@, Ok(*binding.callee.input_layout_model()))
        &&& wiring_view_is_prefix(step.before, final_wiring)
        &&& wires_available(step.after.definitions, layouts.inputs.total_bits_model(), final_wiring.gates.len())
    }),
{
    mixed_trace_step_prefix(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring, at);
    reveal(mixed_trace);
    reveal(wiring_step_valid);
    reveal(binding_ready);
    let step = steps[at];
    existing_wires_keep_availability(step.after.definitions, layouts.inputs.total_bits_model(),
        step.after.gates.len(), final_wiring.gates.len());
}

/// 呼び出しの出力ポートを宣言順に並べると、呼び出し元の左辺の値列に一致する。
proof fn call_output_ports_match_definitions(
    body: &LoweringBody, layouts: &Layouts, capacity: usize, binding: CallBinding, forms: Seq<Form>,
    final_wiring: WiringView, inputs: Seq<bool>, gates: Seq<bool>, outputs: Seq<bool>,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        binding_ready(binding, layouts, forms, definition_widths(body.definitions@)),
        outputs.len() == binding.callee.output_layout_model().total_bits_model(),
        forall|port: int, bit: int| 0 <= port < binding._output_widths@.len() && 0 <= bit < binding._output_widths@[port] ==>
            #[trigger] call_output_bit_has_value(layouts, binding.callee, final_wiring.definitions,
                binding.group.outputs.start, port, bit, inputs, gates, outputs),
    ensures
        port_values(binding.callee.output_layout_model(), outputs)
            == definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, gates)
                .subrange(binding.group.outputs.start as int, binding.group.outputs.end as int),
{
    reveal(binding_ready);
    reveal(port_values);
    let widths = binding._output_widths@;
    let start = binding.group.outputs.start as int;
    let end = binding.group.outputs.end as int;
    let layout = binding.callee.output_layout_model();
    let ports = port_values(layout, outputs);
    let definitions = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, gates);
    let assigned = definitions.subrange(start, end);
    port_bit_layout_size(widths, binding._layout_limit@, layout);
    assert forall|port: int| 0 <= port < widths.len() implies #[trigger] ports[port] == assigned[port] by {
        port_bit_layout_port(widths, binding._layout_limit@, *layout, port as usize);
        let source = layout.ranges_model()[port];
        let target = layouts.definitions.ranges_model()[start + port];
        let width = widths[port];
        assert(definition_widths(body.definitions@)[start + port] == width);
        assert(assigned[port] == definitions[start + port]);
        assert(ports[port].len() == assigned[port].len() == width);
        assert forall|bit: int| 0 <= bit < width implies #[trigger] ports[port][bit] == assigned[port][bit] by {
            assert(call_output_bit_has_value(layouts, binding.callee, final_wiring.definitions,
                binding.group.outputs.start, port, bit, inputs, gates, outputs));
            assert(ports[port][bit] == outputs[source.start + bit]);
            assert(assigned[port][bit] == wire_value(final_wiring.definitions[target.start + bit], inputs, gates));
        };
        assert(ports[port] =~= assigned[port]);
    };
    assert(ports =~= assigned);
}

/// 展開した引数配線から読んだ値を、元の呼び出しにある全引数の値に対応付ける。
proof fn mixed_trace_source_call_values(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
    selected: ResolvedTemplateCall, body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    limit: usize, layout_limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, final_wiring: WiringView,
    at: int, inputs: Seq<bool>, values: Seq<bool>,
) -> (result: (Seq<bool>, Seq<bool>))
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
        prepared.typed.literals.wiring matches FuncWiringResult::Checked(wiring)
            && body.input_widths@.len() == wiring.drivers.signature.inputs@.len(),
        ({
            let project = aliases.targets.project_model();
            &&& caller.0 < project.circuits_model().len() && caller.0 < project.sources_model().len()
            &&& forms == project.circuits_model()[caller.0 as int].syntax.forms@
        }),
        mixed_trace(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring),
        0 <= at < steps.len(),
        steps[at].group_before != steps[at].group_after,
        ({
            let index = steps[at].group_before as int;
            &&& aliases.resolved_template_call_matches(plan, caller, prepared, index, selected)
            &&& index < bindings.len()
            &&& binding_matches_selection(bindings[index], selected)
        }),
        resolved_call_fits_body(selected, body.input_widths@, body.definitions@, forms, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        gate_values_match(inputs, final_wiring.gates, values),
        values.len() == final_wiring.gates.len() <= usize::MAX,
        inputs.len() == layouts.inputs.total_bits_model(),
    ensures ({
        let step = steps[at];
        let binding = bindings[step.group_before as int];
        let project = aliases.targets.project_model();
        let parsed = &project.circuits_model()[caller.0 as int];
        let source = &project.sources_model()[caller.0 as int];
        let wiring = prepared.typed.literals.wiring->Checked_0;
        let root = prepared.projections.calls@[step.group_before as int];
        let ports = port_values(binding.callee.input_layout_model(), result.0);
        let incoming = port_values(&layouts.inputs, inputs);
        let prior = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values).take(step.from as int);

        &&& nor_evaluation(binding.callee.netlist_model(), result.0, result.1)
        &&& source_call_arguments_match(source, parsed, &wiring, caller.1, root.definition,
            binding.group._signature@.call.call, caller.2, incoming, prior, binding._input_widths@, ports)
        &&& port_values(binding.callee.output_layout_model(), result.1)
            == definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values)
                .subrange(step.from as int, step.to as int)
    }),
{
    let result = mixed_trace_call_values(body, layouts, forms, bindings, limit, layout_limit, steps, slot, group,
        final_wiring, at, inputs, values);
    trace_call_frame(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring, at);
    let step = steps[at];
    let index = step.group_before as int;
    let binding = bindings[index];
    let (invocation, mapped, wires) = choose|invocation: CallerArguments, mapped: Seq<Wire>, wires: Seq<Wire>|
        call_group_wires_match(binding.group, forms, binding.arguments@, layouts, binding.callee,
            step.before, step.after, binding._output_widths@, invocation, mapped, wires)
        && result.0 == instance_wire_values(mapped, inputs, values)
        && result.1 == instance_wire_values(wires, inputs, values);

    let layout = binding.callee.input_layout_model();
    let widths = binding._input_widths@;
    let ports = port_values(layout, result.0);
    let incoming = port_values(&layouts.inputs, inputs);
    let prior = prior_definition_values(layouts, step, inputs, values);
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[caller.0 as int];
    let parsed = &project.circuits_model()[caller.0 as int];
    let wiring = prepared.typed.literals.wiring->Checked_0;
    let root = prepared.projections.calls@[index];
    let projections = &prepared.projections.call_arguments;
    let range = projections.ranges@[index];
    let positions = Seq::new(binding.arguments@.len(), |port: int| binding.arguments@[port].form);
    aliases.checked_types_keep_wiring(caller.0, caller.1, caller.2, prepared.typed, wiring);
    aliases.expansion_callee_template_evidence(*plan, caller, prepared, index);
    assert(binding.arguments@ == projections.arguments@.subrange(range.start as int, range.end as int));
    aliases.expansion_arguments_in_source_order(*plan, caller, prepared.typed, &wiring, root, range, projections,
        *binding.group);
    port_bit_layout_size(widths, binding._layout_limit@, layout);
    reveal(port_values);

    assert(positions.len() == ports.len() == widths.len());
    assert forall|port: int| 0 <= port < positions.len() implies
        source_call_argument_value(source, parsed, &wiring, caller.1, root.definition, #[trigger] positions[port],
            caller.2, incoming, prior, widths[port], ports[port]) by {
        let argument = binding.arguments@[port];
        assert(argument == projections.arguments@[range.start + port]);
        assert(argument_matches_width(source, forms, body.input_widths@, body.definitions@.take(step.from as int),
            argument, widths[port], caller.2));
        expanded_port_value(body, layouts, layout_limit, binding, step, forms, invocation, mapped, wires,
            inputs, values, caller.2, port as usize);
        aliases.expansion_argument_value_from_source(*plan, caller, prepared.typed, &wiring, root, range, projections,
            *binding.group, port, incoming, prior, widths[port], ports[port]);
    };
    assert(call_argument_positions(forms, binding.group._signature@.call.call, positions));
    prior_definition_values_from_final(body, layouts, layout_limit, step, final_wiring, inputs, values);
    assert(result.1.len() == binding.callee.output_layout_model().total_bits_model()) by {
        reveal(nor_evaluation);
    };
    call_output_ports_match_definitions(body, layouts, layout_limit, binding, forms, final_wiring, inputs, values, result.1);
    result
}

/// 変換に成功した関数で、指定した呼び出しの引数値と左辺の値を取り出す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn mixed_function_source_call_values(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
    selected: ResolvedTemplateCall, index: int, body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>,
    bindings: Seq<CallBinding>, widths: Seq<u64>, drivers: Seq<OutputDriver>, layout_limit: usize, gate_limit: usize,
    function: &LoweredBitFunc, steps: Ghost<Seq<WiringStep>>, inputs: Seq<bool>, values: Seq<bool>,
) -> (result: (Seq<bool>, Seq<bool>))
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
        prepared.typed.literals.wiring matches FuncWiringResult::Checked(wiring)
            && body.input_widths@.len() == wiring.drivers.signature.inputs@.len(),
        ({
            let project = aliases.targets.project_model();
            &&& caller.0 < project.circuits_model().len() && caller.0 < project.sources_model().len()
            &&& forms == project.circuits_model()[caller.0 as int].syntax.forms@
        }),
        mixed_function_result(body, layouts, forms, bindings, widths, drivers, gate_limit, Ok((*function, steps))),
        ordered_bindings(bindings),
        0 <= index < bindings.len(),
        binding_matches_selection(bindings[index], selected),
        aliases.resolved_template_call_matches(plan, caller, prepared, index, selected),
        resolved_call_fits_body(selected, body.input_widths@, body.definitions@, forms, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        gate_values_match(inputs, function.netlist_model().gates@, values),
        values.len() == function.netlist_model().gates@.len() <= usize::MAX,
        inputs.len() == layouts.inputs.total_bits_model(),
    ensures ({
        let project = aliases.targets.project_model();
        let source = &project.sources_model()[caller.0 as int];
        let parsed = &project.circuits_model()[caller.0 as int];
        let wiring = prepared.typed.literals.wiring->Checked_0;
        let root = prepared.projections.calls@[index];
        let callee = selected.template.circuit_model();
        let first = selected.group.outputs.start as int;
        let end = selected.group.outputs.end as int;
        let definitions = definition_values_from_wires(&layouts.definitions, function.definition_wires@, inputs, values);
        &&& nor_evaluation(callee.netlist_model(), result.0, result.1)
        &&& source_call_arguments_match(source, parsed, &wiring, caller.1, root.definition,
            selected.group._signature@.call.call, caller.2, port_values(&layouts.inputs, inputs), definitions.take(first),
            selected.template.input_widths_model(), port_values(callee.input_layout_model(), result.0))
        &&& port_values(callee.output_layout_model(), result.1) == definitions.subrange(first, end)
    }),
{
    let wiring = WiringView { definitions: function.definition_wires@,
        gates: function.netlist.gates@, origins: function.gate_definitions@ };
    let end = steps@.len() as int - 1;
    vstd::slice::axiom_spec_len(body.definitions);
    let slot = body.definitions@.len() as usize;
    let group = bindings.len() as usize;
    assert(0 <= end && steps@[end].to == slot) by { reveal(mixed_trace); };
    let first = selected.group.outputs.start as int;
    assert(first < body.definitions@.len());
    assert(binding_covers(bindings, first));
    let at = mixed_trace_definition_step(body, layouts, forms, bindings, gate_limit, steps@, slot, group, wiring, end, first);
    let step = steps@[at];
    assert(step.group_before != step.group_after && step.group_before == index) by {
        reveal(wiring_step_valid);
        if step.group_before == step.group_after {
            assert(step.from == first);
            assert(!binding_covers(bindings, first));
        } else {
            let actual = step.group_before as int;
            assert(bindings[actual].group.outputs.start <= first < bindings[actual].group.outputs.end);
            if actual < index {
                assert(bindings[actual].group.outputs.end <= bindings[index].group.outputs.start);
            } else if index < actual {
                assert(bindings[index].group.outputs.end <= bindings[actual].group.outputs.start);
            }
        }
    };
    let result = mixed_trace_source_call_values(aliases, plan, caller, prepared, selected, body, layouts, forms, bindings,
        gate_limit, layout_limit, steps@, slot, group, wiring, at, inputs, values);
    reveal(wiring_step_valid);
    result
}

} // verus!
