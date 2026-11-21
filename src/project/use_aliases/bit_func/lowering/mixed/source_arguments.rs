//! 展開した呼び出しの入力値を、元の引数フォームの値に対応付ける。

use super::*;
use super::super::call_arguments::child_calls::{
    ChildCall, NestedRootEvaluation, child_call_abi, child_call_binding, child_nested_port_value, child_output_evaluates,
    child_port_reads_producer, child_ranges_match, child_value_flows_to_root, child_wiring_trace_matches,
    nor_root_children_bound, root_port_reads_child,
};
use super::super::call_group::{nested_call_group_values, nested_group_invocation_matches, nor_group_invocation_matches};
use super::super::call_arguments::{
    argument_driver_value, argument_prefix_wires, argument_source_available, literal_word, lowered_argument_port_value,
};
use super::super::evaluation::definition_values_from_wires;
use super::super::super::expansion::{
    call_literal_bit, prepared_nested_output_matches, source_argument_bytes, source_call_argument_value, source_call_arguments_match,
};
use super::super::super::frontend::{expression_input_width, nor_definition_determined, nor_root_arguments_match_widths};
use super::super::super::semantics::driver_values;
use super::super::super::templates::ResolvedExpressionCall;
use super::super::super::super::call_arity::CallArgumentSource;
use crate::netlist::wire_value;
use crate::project::FuncWiringResult;
use crate::syntax::{form_span, circuit::call_argument_positions};
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 呼び出し直前の配線から、先行する定義の値を定義順に読む。
pub(super) open spec fn prior_definition_values(
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
    body: &LoweringBody, layouts: &Layouts, layout_limit: usize, step: WiringStep,
    arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout, widths: Seq<u64>, argument_limit: usize,
    invocation: CallerArguments, mapped: Seq<Wire>,
    inputs: Seq<bool>, gates: Seq<bool>, width_limit: u64, port: usize,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        step.from <= body.definitions@.len(),
        step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), step.from as nat),
        inputs.len() == layouts.inputs.total_bits_model(),
        step.before.definitions.len() <= step.after.definitions.len(),
        step.after.definitions.take(step.before.definitions.len() as int) == step.before.definitions,
        wires_available(step.after.definitions, layouts.inputs.total_bits_model(), gates.len()),
        invocation.inputs@ == layouts.inputs.ranges_model(),
        invocation.definitions@ == layouts.definitions.ranges_model(),
        invocation.wires@ == step.before.definitions,
        form_spans_valid(invocation.source.text, invocation.forms@, invocation.source.text.spec_bytes().len() as int),
        port_bit_layout_result(widths, argument_limit, Ok(*layout)),
        argument_prefix_wires(&invocation, arguments, layout.ranges_model(), arguments.len() as int, mapped),
        mapped.len() == layout.total_bits_model(),
        port < widths.len(), port < arguments.len(),
        arguments[port as int].source.has_direct_wires(),
        argument_matches_width(invocation.source, invocation.forms@, body.input_widths@,
            body.definitions@.take(step.from as int), arguments[port as int], widths[port as int], width_limit),
    ensures ({
        let width = widths[port as int];
        let value = port_values(layout, instance_wire_values(mapped, inputs, gates))[port as int];
        let argument = arguments[port as int];
        &&& value.len() == width
        &&& match argument.source {
            CallArgumentSource::Driver(driver) =>
                value == driver_values(port_values(&layouts.inputs, inputs),
                    prior_definition_values(layouts, step, inputs, gates), driver),
            CallArgumentSource::Literal(bits) => {
                let bytes = source_argument_bytes(invocation.source, invocation.forms@, argument.form);
                width == bits && value == Seq::new(width as nat, |bit: int| call_literal_bit(bytes, bit as nat))
            },
            CallArgumentSource::Deferred | CallArgumentSource::NestedCall(_) => false,
        }
    }),
{
    reveal(port_values);
    reveal(wires_available);
    let argument = arguments[port as int];
    port_bit_layout_size(widths, argument_limit, layout);
    if let CallArgumentSource::Driver(driver) = argument.source {
        call_driver_range(body, layouts, layout_limit, step, driver, widths[port as int]);
    }
    if argument.source is Literal {
        let span = form_span(invocation.forms@[argument.form as int]);
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
    lowered_argument_port_value(&invocation, arguments, layout, widths, argument_limit, mapped, inputs, gates, port);
    let value = port_values(layout, instance_wire_values(mapped, inputs, gates))[port as int];
    match argument.source {
        CallArgumentSource::Driver(driver) => {
            assert(value == argument_driver_value(&invocation, inputs, gates, driver));
            assert(value == driver_values(port_values(&layouts.inputs, inputs),
                prior_definition_values(layouts, step, inputs, gates), driver));
        },
        CallArgumentSource::Literal(bits) => {
            let raw = literal_word(&invocation, argument.form);
            let source = source_argument_bytes(invocation.source, invocation.forms@, argument.form);
            assert(raw == source);
            assert(value == Seq::new(bits as nat, |bit: int| call_literal_bit(source, bit as nat)));
        },
        CallArgumentSource::Deferred | CallArgumentSource::NestedCall(_) => {},
    };
}

/// 根の信号またはリテラルの値を、厳格構文木の同じ引数位置に結び付ける。
pub(super) proof fn nested_root_atom_value(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
    index: int, selected: ResolvedTemplateCall, body: &LoweringBody, layouts: &Layouts, layout_limit: usize,
    step: WiringStep, forms: Seq<Form>, root: &NestedRootEvaluation, inputs: Seq<bool>, gates: Seq<bool>, port: usize,
)
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
        aliases.resolved_template_call_matches(plan, caller, prepared, index, selected),
        prepared.typed.literals.wiring matches FuncWiringResult::Checked(wiring)
            && body.input_widths@.len() == wiring.drivers.signature.inputs@.len(),
        ({
            let project = aliases.targets.project_model();
            &&& caller.0 < project.circuits_model().len() && caller.0 < project.sources_model().len()
            &&& forms == project.circuits_model()[caller.0 as int].syntax.forms@
        }),
        resolved_call_fits_body(selected, body.input_widths@, body.definitions@, forms, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        step.from == selected.group.outputs.start,
        step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), step.from as nat),
        step.before.definitions.len() <= step.after.definitions.len(),
        step.after.definitions.take(step.before.definitions.len() as int) == step.before.definitions,
        wires_available(step.after.definitions, layouts.inputs.total_bits_model(), gates.len()),
        inputs.len() == layouts.inputs.total_bits_model(),
        port < selected.arguments@.len(),
        selected.arguments@[port as int].source.has_direct_wires(),
        ({
            let layout = selected.template.circuit_model().input_layout_model();
            &&& port_bit_layout_result(selected.template.input_widths_model(), selected.template.bit_limit_model(), Ok(*layout))
            &&& root.invocation.source == selected.group.expression.source && root.invocation.forms@ == forms
            &&& root.invocation.inputs@ == layouts.inputs.ranges_model()
            &&& root.invocation.definitions@ == layouts.definitions.ranges_model()
            &&& root.invocation.wires@ == step.before.definitions
            &&& argument_prefix_wires(&root.invocation, selected.arguments@, layout.ranges_model(),
                selected.arguments@.len() as int, root.mapped)
            &&& root.mapped.len() == layout.total_bits_model()
            &&& root.arguments == instance_wire_values(root.mapped, inputs, gates)
        }),
    ensures ({
        let project = aliases.targets.project_model();
        let layout = selected.template.circuit_model().input_layout_model();
        let positions = Seq::new(selected.arguments@.len(), |i: int| selected.arguments@[i].form);
        &&& call_argument_positions(forms, selected.group._signature@.call.call, positions)
        &&& source_call_argument_value(&project.sources_model()[caller.0 as int], &project.circuits_model()[caller.0 as int],
            &prepared.typed.literals.wiring->Checked_0, caller.1, prepared.projections.calls@[index].definition,
            selected.arguments@[port as int].form, caller.2, port_values(&layouts.inputs, inputs),
            prior_definition_values(layouts, step, inputs, gates), selected.template.input_widths_model()[port as int],
            port_values(layout, root.arguments)[port as int])
    }),
{
    let template = selected.template;
    let layout = template.circuit_model().input_layout_model();
    let widths = template.input_widths_model();
    let argument = selected.arguments@[port as int];
    let wiring = prepared.typed.literals.wiring->Checked_0;
    let source_call = prepared.projections.calls@[index];
    let projections = &prepared.projections.call_arguments;
    let range = projections.ranges@[index];
    let incoming = port_values(&layouts.inputs, inputs);
    let prior = prior_definition_values(layouts, step, inputs, gates);
    let value = port_values(layout, root.arguments)[port as int];

    aliases.checked_types_keep_wiring(caller.0, caller.1, caller.2, prepared.typed, wiring);
    aliases.expansion_callee_template_evidence(*plan, caller, prepared, index);
    aliases.expansion_arguments_in_source_order(*plan, caller, prepared.typed, &wiring, source_call, range, projections,
        *selected.group);
    assert(argument == projections.arguments@[range.start + port]);
    assert(root_argument_matches_width(selected.group.expression.source, forms, body.input_widths@,
        body.definitions@, selected, port as int, caller.2));
    expanded_port_value(body, layouts, layout_limit, step, selected.arguments@, layout, widths, template.bit_limit_model(),
        root.invocation, root.mapped, inputs, gates, caller.2, port);
    reveal(port_values);
    aliases.expansion_argument_value_from_source(*plan, caller, prepared.typed, &wiring, source_call, range, projections,
        *selected.group, port as int, incoming, prior, widths[port as int], value);
}

/// 一つの呼び出しの入力ビット、ポートごとの入力値、出力ビット。
pub(in crate::project::use_aliases::bit_func) struct EvaluatedCallBits {
    pub(in crate::project::use_aliases::bit_func) input: Seq<bool>,
    pub(in crate::project::use_aliases::bit_func) ports: Seq<Seq<bool>>,
    pub(in crate::project::use_aliases::bit_func) output: Seq<bool>,
}

/// 子の評価値と、その入力値を読んだ配線を同じ後順履歴から得る。
#[verifier::spinoff_prover]
proof fn trace_child_wire_values<'s, 'p, 'a>(
    selected: ResolvedExpressionCall<'s, 'p, 'a>, references: core::ops::Range<usize>,
    builtin: &(NorNetlist, PortBitLayout), invocation: CallerArguments<'s, 'p, 'a>,
    calls: Seq<ChildCall<'s, 'p, 'a>>, initial: Seq<NorGate>, root: &NestedRootEvaluation<'s, 'p, 'a>,
    combined: Seq<NorGate>, inputs: Seq<bool>, gates: Seq<bool>, input_bits: usize, child_index: usize,
) -> (result: (EvaluatedCallBits, CallerArguments<'s, 'p, 'a>, Seq<Wire>))
    requires
        references.start <= references.end, child_index < calls.len(),
        child_call_binding(selected, references, builtin, calls[child_index as int]),
        child_wiring_trace_matches(&invocation, calls, calls.len(), (references.end - references.start) as usize,
            initial, root.trace, root.end, input_bits),
        child_ranges_match(calls, calls.len(), root.end.table.ranges@),
        root.end.gates.len() <= combined.len() && root.end.gates == combined.take(root.end.gates.len() as int),
        inputs.len() == input_bits,
        gate_values_match(inputs, combined, gates), gates.len() == combined.len() <= usize::MAX,
    ensures ({
        let (evaluation, mapped_from, mapped) = result;
        let call = calls[child_index as int];
        let before = root.trace[child_index as int].table;
        let reference = call.reference as int;
        &&& child_index < root.trace.len()
        &&& mapped_from.source == invocation.source && mapped_from.forms@ == invocation.forms@
        &&& mapped_from.inputs@ == invocation.inputs@ && mapped_from.definitions@ == invocation.definitions@
        &&& mapped_from.wires@ == invocation.wires@
        &&& mapped_from.child_ranges@ == before.ranges@ && mapped_from.child_wires@ == before.wires@
        &&& argument_prefix_wires(&mapped_from, call.arguments@, call.inputs.ranges_model(), call.arguments@.len() as int, mapped)
        &&& mapped.len() == call.inputs.total_bits_model()
        &&& evaluation.input == instance_wire_values(mapped, inputs, gates)
        &&& evaluation.ports == port_values(call.inputs, evaluation.input)
        &&& evaluation.ports.len() == call.arguments@.len()
        &&& nor_evaluation(call.circuit, evaluation.input, evaluation.output)
        &&& (selected.template.is_none() ==> {
            let input = evaluation.input;
            &&& input.len() == 2
            &&& evaluation.ports == seq![seq![input[0]], seq![input[1]]]
            &&& evaluation.output == seq![!(input[0] || input[1])]
        })
        &&& arguments_are_determined(call.arguments@)
        &&& 0 <= reference < root.end.table.ranges@.len()
        &&& root.end.table.ranges@[reference] matches Some(range)
            && range.start <= range.end <= root.end.table.wires@.len()
            && evaluation.output == instance_wire_values(
                root.end.table.wires@.subrange(range.start as int, range.end as int), inputs, gates)
    }),
{
    let child = child_index as int;
    let call = calls[child];
    let count = (references.end - references.start) as usize;
    let (input, output) = child_output_evaluates(&invocation, calls, calls.len(), count, initial, root.trace, root.end,
        child_index, combined, inputs, gates, input_bits);
    if selected.template.is_none() {
        super::super::call_arguments::builtin_nor_evaluation(builtin, input, output);
    }
    assert(root.trace.len() == calls.len() + 1) by { reveal(child_wiring_trace_matches); };
    let before = root.trace[child].table;
    let (mapped_from, mapped) = choose|mapped_from: CallerArguments<'s, 'p, 'a>, mapped: Seq<Wire>|
        #[trigger] argument_prefix_wires(&mapped_from, call.arguments@, call.inputs.ranges_model(),
            call.arguments@.len() as int, mapped)
        && mapped_from.source == invocation.source && mapped_from.forms@ == invocation.forms@
        && mapped_from.inputs@ == invocation.inputs@ && mapped_from.definitions@ == invocation.definitions@
        && mapped_from.wires@ == invocation.wires@
        && mapped_from.child_ranges@ == before.ranges@ && mapped_from.child_wires@ == before.wires@
        && mapped.len() == call.inputs.total_bits_model() && input == instance_wire_values(mapped, inputs, gates);
    let ports = port_values(call.inputs, input);
    assert(ports.len() == call.arguments@.len()) by { reveal(port_values); };
    port_bit_layout_size(call._input_widths@, call._layout_limit@, call.inputs);
    assert forall|p: int| 0 <= p < call.arguments@.len() implies
        !((#[trigger] call.arguments@[p]).source is Deferred) by {
        reveal(argument_prefix_wires);
        let slot = call.inputs.ranges_model()[p];
        assert(slot.end <= mapped.len());
        assert(argument_source_available(&mapped_from, call.arguments@[p].source));
    };
    (EvaluatedCallBits { input, ports, output }, mapped_from, mapped)
}

pub(super) open spec fn nor_source_binding_matches(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
    prepared: &PreparedExpansionBody, binding: &NorBinding, forms: Seq<Form>,
) -> bool {
    let project = aliases.targets.project_model();
    let parsed = &project.circuits_model()[caller.0 as int];
    let source = &project.sources_model()[caller.0 as int];
    let root = binding.selected.prepared;
    &&& aliases.can_resolve()
    &&& aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared)
    &&& binding.candidate < prepared.nor_roots@.len() && *root == prepared.nor_roots@[binding.candidate as int]
    &&& aliases.nor_binding_context(plan, table, caller.2, prepared.projections.call_arguments.arguments@, *binding)
    &&& caller.0 < project.circuits_model().len() && caller.0 < project.sources_model().len()
    &&& root.definition < parsed.definitions@.len()
    &&& *binding.references == parsed.definitions@[root.definition as int].references
    &&& forms == parsed.syntax.forms@ && root.root.expression.source == source
    &&& form_spans_valid(source.text, forms, source.text.spec_bytes().len() as int)
}

/// 根 NOR の直接引数を実配線から読み、同じ厳格定義の引数フォームの値に結び付ける。
#[verifier::spinoff_prover]
proof fn nor_root_atom_value(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
    prepared: &PreparedExpansionBody,
    binding: &NorBinding, body: &LoweringBody, layouts: &Layouts, layout_limit: usize, forms: Seq<Form>,
    final_wiring: WiringView, traced: &RootedNorEvaluation, inputs: Seq<bool>, values: Seq<bool>, port: usize,
)
    requires
        nor_source_binding_matches(aliases, plan, table, caller, prepared, binding, forms),
        nor_binding_fits_body(*binding, binding.selected.prepared.root.expression.source, forms,
            body.input_widths@, body.definitions@, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        body.input_widths@.len() == prepared.typed.literals.wiring->Checked_0.drivers.signature.inputs@.len(),
        traced.step.from == binding.selected.prepared.output_slot,
        traced.step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), traced.step.from as nat),
        wiring_view_is_prefix(traced.step.before, traced.step.after),
        wiring_view_is_prefix(traced.step.before, final_wiring),
        wiring_view_is_prefix(traced.step.after, final_wiring),
        wires_available(final_wiring.definitions, layouts.inputs.total_bits_model(), values.len()),
        inputs.len() == layouts.inputs.total_bits_model(),
        nor_call_group_evaluation_matches(&binding.selected, *binding.references, forms, layouts, &traced.builtin,
            traced.step.before, traced.step.after, final_wiring.gates, inputs, values, traced.evaluation),
        port < 2 && binding.selected.arguments@[port as int].source.has_direct_wires(),
    ensures ({
        let project = aliases.targets.project_model();
        let assigned = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values);
        source_call_argument_value(&project.sources_model()[caller.0 as int], &project.circuits_model()[caller.0 as int],
            &prepared.typed.literals.wiring->Checked_0, caller.1, binding.selected.prepared.definition,
            binding.selected.arguments@[port as int].form, caller.2, port_values(&layouts.inputs, inputs),
            assigned.take(traced.step.from as int), 1, port_values(&traced.builtin.1, traced.evaluation.2.arguments)[port as int])
    }),
{
    reveal(nor_call_group_evaluation_matches);
    reveal(nor_group_invocation_matches);
    let selected = &binding.selected;
    let root = &traced.evaluation.2;
    let step = traced.step;
    assert(wires_available(step.after.definitions, layouts.inputs.total_bits_model(), values.len())) by {
        reveal(wires_available);
        assert forall|i: int| 0 <= i < step.after.definitions.len() implies
            wire_available(#[trigger] step.after.definitions[i], layouts.inputs.total_bits_model() as nat, values.len()) by {
            assert(step.after.definitions[i] == final_wiring.definitions[i]);
        };
    };
    reveal(nor_root_arguments_match_widths);
    expanded_port_value(body, layouts, layout_limit, step, selected.arguments@, &traced.builtin.1,
        seq![1u64, 1u64], 2, root.invocation, root.mapped, inputs, values, caller.2, port);
    prior_definition_values_from_final(body, layouts, layout_limit, step, final_wiring, inputs, values);
    port_bit_layout_size(body.input_widths@, layout_limit, &layouts.inputs);
    reveal(port_values);
    aliases.prepared_nor_output_evidence(*plan, caller, prepared, binding.candidate as int);
    aliases.prepared_nor_argument_evidence(*plan, caller, prepared, binding.candidate as int, step.from,
        selected.prepared.postorder@.len() as int, port as int);
    let argument = selected.arguments@[port as int];
    let range = selected.prepared.root.arguments;
    assert(argument == prepared.projections.call_arguments.arguments@[range.start + port]);
    reveal(source_call_argument_value);
}

/// 入れ子の引数を、根が実際に読んだ子の出力と厳格構文木のフォームに対応付ける。
#[verifier::spinoff_prover]
proof fn nor_root_child_value(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
    prepared: &PreparedExpansionBody, binding: &NorBinding, layouts: &Layouts, forms: Seq<Form>,
    traced: &RootedNorEvaluation, combined: Seq<NorGate>, inputs: Seq<bool>, values: Seq<bool>, port: usize,
) -> (child: (usize, Seq<bool>, Seq<bool>))
    requires
        nor_source_binding_matches(aliases, plan, table, caller, prepared, binding, forms),
        nor_call_group_evaluation_matches(&binding.selected, *binding.references, forms, layouts, &traced.builtin,
            traced.step.before, traced.step.after, combined, inputs, values, traced.evaluation),
        gate_values_match(inputs, combined, values), values.len() == combined.len() <= usize::MAX,
        inputs.len() == layouts.inputs.total_bits_model(),
        port < 2 && binding.selected.arguments@[port as int].source is NestedCall,
    ensures ({
        let (index, input, output) = child;
        let argument = binding.selected.arguments@[port as int];
        let selected_child = binding.selected.children@[index as int];
        &&& index < binding.selected.children@.len()
        &&& selected_child.child.reference == binding.references.start + argument.source->NestedCall_0
        &&& selected_child.child._signature@.call.call.form == argument.form
        &&& selected_child.child._signature@.call.target.port_counts().outputs == 1
        &&& output == port_values(&traced.builtin.1, traced.evaluation.2.arguments)[port as int]
        &&& match selected_child.template {
            Some(template) => nor_evaluation(template.circuit_model().netlist_model(), input, output),
            None => input.len() == 2 && output == seq![!(input[0] || input[1])],
        }
        &&& root_port_reads_child(&traced.evaluation.2, binding.selected.arguments@, &traced.builtin.1, port, inputs, values)
    }),
{
    reveal(nor_call_group_evaluation_matches);
    reveal(nor_root_children_bound);
    let selected = &binding.selected;
    let (calls, invocation, root) = traced.evaluation;
    let count = (binding.references.end - binding.references.start) as usize;
    vstd::std_specs::vec::axiom_spec_len(&selected.children);
    vstd::std_specs::vec::axiom_spec_len(&root.end.table.wires);
    assert forall|i: int| 0 <= i < calls.len() implies child_call_abi(#[trigger] calls[i]) by {
        assert(child_call_binding(selected.children@[i], *binding.references, &traced.builtin, calls[i]));
    };
    let child = child_value_flows_to_root(&invocation, calls, count, traced.step.before.gates, &root, selected.arguments@,
        &traced.builtin.1, seq![1u64, 1u64], 2, port, combined, inputs, values, layouts.inputs.total_bits_model());
    let argument = selected.arguments@[port as int];
    let range = selected.prepared.root.arguments;
    let postorder = selected.prepared.postorder@;
    let slot = selected.prepared.output_slot;
    aliases.prepared_nor_output_evidence(*plan, caller, prepared, binding.candidate as int);
    aliases.prepared_nor_argument_evidence(*plan, caller, prepared, binding.candidate as int,
        slot, postorder.len() as int, port as int);
    assert(argument == prepared.projections.call_arguments.arguments@[range.start + port]);
    let index = choose|i: int| 0 <= i < postorder.len()
        && (#[trigger] postorder[i]).reference == binding.references.start + argument.source->NestedCall_0
        && postorder[i]._signature@.call.call.form == argument.form
        && postorder[i]._signature@.call.target.port_counts().outputs == 1;
    reveal(UseAliases::resolved_expression_calls_match);
    reveal(UseAliases::resolved_expression_call_matches);
    assert(*selected.children@[index].child == postorder[index]);
    assert(child_call_binding(selected.children@[index], *binding.references, &traced.builtin, calls[index]));
    assert(child_call_binding(selected.children@[child.0 as int], *binding.references, &traced.builtin, calls[child.0 as int]));
    if index < child.0 { assert(calls[index].reference != calls[child.0 as int].reference); }
    if child.0 < index { assert(calls[child.0 as int].reference != calls[index].reference); }
    assert(child.0 == index);
    if selected.children@[index].template.is_none() {
        super::super::call_arguments::builtin_nor_evaluation(&traced.builtin, child.1, child.2);
    }
    child
}

/// 根 NOR の子の評価値を、同じ配線履歴と厳格構文木の引数に対応付ける。
#[verifier::opaque]
pub(super) open spec fn evaluated_nor_child(
    aliases: &UseAliases, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, binding: &NorBinding,
    layouts: &Layouts, forms: Seq<Form>, final_wiring: WiringView, traced: &RootedNorEvaluation,
    inputs: Seq<bool>, values: Seq<bool>, child_index: usize, evaluation: EvaluatedCallBits,
) -> bool {
    let project = aliases.targets.project_model();
    let child = child_index as int;
    let selected = binding.selected.children@[child];
    let (calls, _, root) = traced.evaluation;
    let call = calls[child];
    let positions = Seq::new(call.arguments@.len(), |p: int| call.arguments@[p].form);
    let incoming = port_values(&layouts.inputs, inputs);
    let assigned = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values);
    let prior = assigned.take(binding.selected.prepared.output_slot as int);
    let reference = call.reference as int;
    &&& child < calls.len() == binding.selected.children@.len()
    &&& selected.child._signature@.call.target.port_counts().outputs == 1
    &&& (selected.child._signature@.signature matches crate::project::FuncCallSignature::Function(ports)
        ==> ports.outputs@.len() == 1)
    &&& arguments_are_determined(call.arguments@)
    &&& evaluation.ports == port_values(call.inputs, evaluation.input)
    &&& evaluation.ports.len() == call.arguments@.len()
    &&& match selected.template {
        Some(template) => call.inputs == template.circuit_model().input_layout_model()
            && nor_evaluation(template.circuit_model().netlist_model(), evaluation.input, evaluation.output),
        None => evaluation.input.len() == 2
            && evaluation.ports == seq![seq![evaluation.input[0]], seq![evaluation.input[1]]]
            && evaluation.output == seq![!(evaluation.input[0] || evaluation.input[1])],
    }
    &&& 0 <= reference < root.end.table.ranges@.len()
    &&& root.end.table.ranges@[reference] matches Some(range)
        && range.start <= range.end <= root.end.table.wires@.len()
        && evaluation.output == instance_wire_values(
            root.end.table.wires@.subrange(range.start as int, range.end as int), inputs, values)
    &&& call_argument_positions(forms, selected.child._signature@.call.call, positions)
    &&& forall|p: int| 0 <= p < call.arguments@.len() ==> {
        let argument = #[trigger] call.arguments@[p];
        let width = expression_input_width(selected, p);
        &&& evaluation.ports[p].len() == width
        &&& if argument.source.has_direct_wires() {
            source_call_argument_value(&project.sources_model()[caller.0 as int], &project.circuits_model()[caller.0 as int],
                &prepared.typed.literals.wiring->Checked_0, caller.1, binding.selected.prepared.definition,
                positions[p], caller.2, incoming, prior, width, evaluation.ports[p])
        } else {
            &&& argument.source is NestedCall
            &&& exists|producer: usize| #[trigger] child_port_reads_producer(calls, root.end, producer, child_index,
                    p as usize, evaluation.input, inputs, values)
                && binding.selected.children@[producer as int].child._signature@.call.call.form == positions[p]
        }
    }
}

/// 子の直接引数は元の定義から読み、入れ子の引数は同じ後順履歴にある出力から読む。
#[verifier::spinoff_prover]
proof fn nor_trace_child_values<'s, 'p, 'a>(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
    prepared: &PreparedExpansionBody, binding: &NorBinding, body: &LoweringBody, layouts: &Layouts,
    layout_limit: usize, forms: Seq<Form>, final_wiring: WiringView, traced: &RootedNorEvaluation<'s, 'p, 'a>,
    inputs: Seq<bool>, values: Seq<bool>, child_index: usize,
) -> (evaluation: EvaluatedCallBits)
    requires
        nor_source_binding_matches(aliases, plan, table, caller, prepared, binding, forms),
        nor_definition_determined(binding.selected.prepared, prepared.projections.call_arguments.arguments@),
        nor_binding_fits_body(*binding, binding.selected.prepared.root.expression.source, forms,
            body.input_widths@, body.definitions@, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        body.input_widths@.len() == prepared.typed.literals.wiring->Checked_0.drivers.signature.inputs@.len(),
        traced.step.from == binding.selected.prepared.output_slot,
        traced.step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), traced.step.from as nat),
        wiring_view_is_prefix(traced.step.before, traced.step.after),
        wiring_view_is_prefix(traced.step.before, final_wiring),
        wiring_view_is_prefix(traced.step.after, final_wiring),
        wires_available(final_wiring.definitions, layouts.inputs.total_bits_model(), values.len()),
        gate_values_match(inputs, final_wiring.gates, values), values.len() == final_wiring.gates.len() <= usize::MAX,
        inputs.len() == layouts.inputs.total_bits_model(),
        nor_call_group_evaluation_matches(&binding.selected, *binding.references, forms, layouts, &traced.builtin,
            traced.step.before, traced.step.after, final_wiring.gates, inputs, values, traced.evaluation),
        child_index < binding.selected.children@.len(),
    ensures evaluated_nor_child(aliases, caller, prepared, binding, layouts, forms, final_wiring, traced,
        inputs, values, child_index, evaluation),
{
    reveal(evaluated_nor_child);
    reveal(nor_call_group_evaluation_matches);
    reveal(nor_root_children_bound);
    reveal(nor_group_invocation_matches);
    reveal(UseAliases::resolved_expression_calls_match);
    reveal(UseAliases::resolved_expression_call_matches);
    let (calls, invocation, root) = traced.evaluation;
    let child = child_index as int;
    let selected = &binding.selected;
    let selected_child = selected.children@[child];
    let postorder = selected.prepared.postorder@;
    let call = calls[child];
    let step = traced.step;
    let references = *binding.references;
    let count = (references.end - references.start) as usize;
    let input_bits = layouts.inputs.total_bits_model();
    assert(child_call_binding(selected_child, references, &traced.builtin, call));
    let (evaluation, mapped_from, mapped) = trace_child_wire_values(selected_child, references, &traced.builtin,
        invocation, calls, step.before.gates, &root, final_wiring.gates, inputs, values, input_bits, child_index);

    aliases.prepared_nor_output_evidence(*plan, caller, prepared, binding.candidate as int);
    aliases.prepared_nor_arguments_in_source_order(*plan, caller, prepared, binding.candidate as int, child);
    aliases.prepared_nor_child_single_output(*plan, caller, prepared, binding.candidate as int, child);
    assert(*selected_child.child == postorder[child]);
    let range = selected_child.child.arguments;
    let projected = prepared.projections.call_arguments.arguments@.subrange(range.start as int, range.end as int);
    assert(call.arguments@ == projected);
    let positions = Seq::new(call.arguments@.len(), |p: int| call.arguments@[p].form);
    assert(call_argument_positions(forms, selected_child.child._signature@.call.call, positions));

    prior_definition_values_from_final(body, layouts, layout_limit, step, final_wiring, inputs, values);
    port_bit_layout_size(body.input_widths@, layout_limit, &layouts.inputs);
    port_bit_layout_size(call._input_widths@, call._layout_limit@, call.inputs);
    reveal(port_values);
    assert(wires_available(step.after.definitions, input_bits, values.len())) by {
        reveal(wires_available);
        assert forall|i: int| 0 <= i < step.after.definitions.len() implies
            wire_available(#[trigger] step.after.definitions[i], input_bits as nat, values.len()) by {
            assert(step.after.definitions[i] == final_wiring.definitions[i]);
        };
    };
    let incoming = port_values(&layouts.inputs, inputs);
    let assigned = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values);
    let prior = assigned.take(step.from as int);
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[caller.0 as int];
    let parsed = &project.circuits_model()[caller.0 as int];
    let wiring = prepared.typed.literals.wiring->Checked_0;
    assert forall|p: int| 0 <= p < call.arguments@.len() implies {
        let argument = #[trigger] call.arguments@[p];
        let width = expression_input_width(selected_child, p);
        &&& evaluation.ports[p].len() == width
        &&& if argument.source.has_direct_wires() {
            source_call_argument_value(source, parsed, &wiring, caller.1, selected.prepared.definition,
                positions[p], caller.2, incoming, prior, width, evaluation.ports[p])
        } else {
            &&& argument.source is NestedCall
            &&& exists|producer: usize| #[trigger] child_port_reads_producer(calls, root.end, producer, child_index,
                    p as usize, evaluation.input, inputs, values)
                && selected.children@[producer as int].child._signature@.call.call.form == positions[p]
        }
    } by {
        let argument = call.arguments@[p];
        assert(argument == prepared.projections.call_arguments.arguments@[range.start + p]);
        aliases.prepared_nor_argument_evidence(*plan, caller, prepared, binding.candidate as int, step.from, child, p);
        assert(call._input_widths@[p] == expression_input_width(selected_child, p));
        port_bit_layout_port(call._input_widths@, call._layout_limit@, *call.inputs, p as usize);
        if argument.source.has_direct_wires() {
            reveal(nor_root_arguments_match_widths);
            assert(argument == selected.children@[child].arguments@[p]);
            expanded_port_value(body, layouts, layout_limit, step, call.arguments@, call.inputs, call._input_widths@,
                call._layout_limit@, mapped_from, mapped, inputs, values, caller.2, p as usize);
            reveal(source_call_argument_value);
        } else {
            assert(argument.source is NestedCall);
            let producer = child_nested_port_value(&invocation, calls, calls.len(), count, step.before.gates,
                root.trace, root.end, child_index, p as usize, &mapped_from, mapped, inputs, values, input_bits);
            assert(child_port_reads_producer(calls, root.end, producer, child_index, p as usize,
                evaluation.input, inputs, values));
            let earlier = choose|i: int| 0 <= i < child
                && (#[trigger] postorder[i]).reference == references.start + argument.source->NestedCall_0
                && postorder[i]._signature@.call.call.form == argument.form;
            assert(*selected.children@[earlier].child == postorder[earlier]);
            assert(child_call_binding(selected.children@[earlier], references, &traced.builtin, calls[earlier]));
            if earlier < producer { assert(calls[earlier].reference != calls[producer as int].reference); }
            if producer < earlier { assert(calls[producer as int].reference != calls[earlier].reference); }
            assert(earlier == producer);
        }
    };
    evaluation
}

/// 後順で評価した子の呼び出しを、元の引数と先行する出力に対応付ける。
pub(in crate::project::use_aliases::bit_func) open spec fn evaluated_expression_child_matches(
    aliases: &UseAliases, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, definition: usize,
    reference_start: usize, selected: Seq<ResolvedExpressionCall>, incoming: Seq<Seq<bool>>, prior: Seq<Seq<bool>>,
    children: Seq<EvaluatedCallBits>, child: int,
) -> bool {
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[caller.0 as int];
    let parsed = &project.circuits_model()[caller.0 as int];
    let wiring = &prepared.typed.literals.wiring->Checked_0;
    let expression = selected[child];
    let values = children[child];
    &&& 0 <= child < children.len() == selected.len()
    &&& values.ports.len() == expression.arguments@.len()
    &&& match expression.template {
        Some(template) => {
            let circuit = template.circuit_model();
            &&& nor_evaluation(circuit.netlist_model(), values.input, values.output)
            &&& values.ports == port_values(circuit.input_layout_model(), values.input)
        },
        None => {
            &&& values.input.len() == 2
            &&& values.ports == seq![seq![values.input[0]], seq![values.input[1]]]
            &&& values.output == seq![!(values.input[0] || values.input[1])]
        },
    }
    &&& forall|port: int| 0 <= port < expression.arguments@.len() ==> {
        let argument = #[trigger] expression.arguments@[port];
        let width = expression_input_width(expression, port);
        let value = values.ports[port];
        &&& value.len() == width
        &&& if argument.source.has_direct_wires() {
            source_call_argument_value(source, parsed, wiring, caller.1, definition, argument.form, caller.2,
                incoming, prior, width, value)
        } else {
            &&& argument.source is NestedCall
            &&& exists|producer: int| 0 <= producer < child
                && (#[trigger] selected[producer]).child.reference == reference_start + argument.source->NestedCall_0
                && selected[producer].child._signature@.call.call.form == argument.form
                && value == children[producer].output
        }
    }
}

pub(in crate::project::use_aliases::bit_func) open spec fn evaluated_nor_root_port_matches(
    aliases: &UseAliases, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, binding: &NorBinding,
    incoming: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, ports: Seq<Seq<bool>>, children: Seq<EvaluatedCallBits>, port: int,
) -> bool {
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[caller.0 as int];
    let parsed = &project.circuits_model()[caller.0 as int];
    let wiring = &prepared.typed.literals.wiring->Checked_0;
    let selected = &binding.selected;
    let argument = selected.arguments@[port];
    let value = ports[port];
    &&& value.len() == 1
    &&& if argument.source.has_direct_wires() {
        source_call_argument_value(source, parsed, wiring, caller.1, selected.prepared.definition, argument.form,
            caller.2, incoming, prior, 1, value)
    } else {
        &&& argument.source is NestedCall
        &&& exists|producer: int| 0 <= producer < children.len()
            && (#[trigger] selected.children@[producer]).child.reference
                == binding.references.start + argument.source->NestedCall_0
            && selected.children@[producer].child._signature@.call.call.form == argument.form
            && value == children[producer].output
    }
}

/// 根 NOR の後順列にある各子が、型検査済みの出力を一つ持つことを表す。
#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func) open spec fn nor_children_have_single_output(
    selected: Seq<ResolvedExpressionCall>,
) -> bool {
    forall|i: int| 0 <= i < selected.len() ==> {
        let child = (#[trigger] selected[i]).child;
        &&& child._signature@.call.target.port_counts().outputs == 1
        &&& (child._signature@.signature matches crate::project::FuncCallSignature::Function(ports)
            ==> ports.outputs@.len() == 1)
    }
}

/// 根 NOR の評価を、最終的な定義の値と後順の子の入出力に対応付ける。
pub(in crate::project::use_aliases::bit_func) open spec fn evaluated_nor_call_matches(
    aliases: &UseAliases, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, binding: &NorBinding,
    incoming: Seq<Seq<bool>>, assigned: Seq<Seq<bool>>, evaluation: EvaluatedNestedCall,
) -> bool {
    let selected = &binding.selected;
    let first = selected.prepared.output_slot as int;
    let prior = assigned.take(first);
    let root = evaluation.root;
    &&& 0 <= first < assigned.len() && assigned[first] == root.output
    &&& root.input.len() == 2
    &&& root.ports == seq![seq![root.input[0]], seq![root.input[1]]]
    &&& root.output == seq![!(root.input[0] || root.input[1])]
    &&& selected.arguments@.len() == 2
    &&& evaluation.children.len() == selected.children@.len()
    &&& nor_children_have_single_output(selected.children@)
    &&& forall|port: int| 0 <= port < 2 ==>
        #[trigger] evaluated_nor_root_port_matches(aliases, caller, prepared, binding, incoming, prior,
            root.ports, evaluation.children, port)
    &&& forall|i: int| #![trigger evaluation.children[i]] 0 <= i < evaluation.children.len() ==>
        evaluated_expression_child_matches(aliases, caller, prepared, selected.prepared.definition,
            binding.references.start, selected.children@, incoming, prior, evaluation.children, i)
}

/// 同じ末尾配線表を参照した値を照合し、各子の入力と先行する子の出力の等式を得る。
#[verifier::spinoff_prover]
proof fn nor_evaluated_child_sources(
    aliases: &UseAliases, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, binding: &NorBinding,
    layouts: &Layouts, forms: Seq<Form>, final_wiring: WiringView, traced: &RootedNorEvaluation,
    inputs: Seq<bool>, values: Seq<bool>, children: Seq<EvaluatedCallBits>, child: int,
)
    requires
        nor_call_group_evaluation_matches(&binding.selected, *binding.references, forms, layouts, &traced.builtin,
            traced.step.before, traced.step.after, final_wiring.gates, inputs, values, traced.evaluation),
        caller.0 < aliases.targets.project_model().sources_model().len(),
        caller.0 < aliases.targets.project_model().circuits_model().len(),
        prepared.typed.literals.wiring is Checked,
        0 <= child < children.len() == binding.selected.children@.len() <= usize::MAX,
        forall|i: int| 0 <= i < children.len() ==>
            evaluated_nor_child(aliases, caller, prepared, binding, layouts, forms, final_wiring, traced,
                inputs, values, i as usize, #[trigger] children[i]),
    ensures evaluated_expression_child_matches(aliases, caller, prepared, binding.selected.prepared.definition,
        binding.references.start, binding.selected.children@, port_values(&layouts.inputs, inputs),
        definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values)
            .take(binding.selected.prepared.output_slot as int), children, child),
{
    reveal(evaluated_nor_child);
    reveal(nor_call_group_evaluation_matches);
    reveal(nor_root_children_bound);
    let selected = &binding.selected;
    let expression = selected.children@[child];
    let value = children[child];
    let (calls, _, root) = traced.evaluation;
    let call = calls[child];
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[caller.0 as int];
    let parsed = &project.circuits_model()[caller.0 as int];
    let wiring = &prepared.typed.literals.wiring->Checked_0;
    let incoming = port_values(&layouts.inputs, inputs);
    let assigned = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values);
    let prior = assigned.take(selected.prepared.output_slot as int);
    assert(evaluated_nor_child(aliases, caller, prepared, binding, layouts, forms, final_wiring, traced,
        inputs, values, child as usize, value));
    assert(child_call_binding(expression, *binding.references, &traced.builtin, call));
    vstd::slice::axiom_spec_len(expression.arguments);
    assert(expression.arguments@.len() <= usize::MAX);
    assert forall|port: int| 0 <= port < expression.arguments@.len() implies {
        let argument = #[trigger] expression.arguments@[port];
        let width = expression_input_width(expression, port);
        let bits = value.ports[port];
        &&& bits.len() == width
        &&& if argument.source.has_direct_wires() {
            source_call_argument_value(source, parsed, wiring, caller.1, selected.prepared.definition, argument.form,
                caller.2, incoming, prior, width, bits)
        } else {
            &&& argument.source is NestedCall
            &&& exists|producer: int| 0 <= producer < child
                && (#[trigger] selected.children@[producer]).child.reference
                    == binding.references.start + argument.source->NestedCall_0
                && selected.children@[producer].child._signature@.call.call.form == argument.form
                && bits == children[producer].output
        }
    } by {
        let argument = expression.arguments@[port];
        assert(argument == call.arguments@[port]);
        if !argument.source.has_direct_wires() {
            let input_port = port as usize;
            assert(input_port as int == port);
            let producer = choose|i: usize| #[trigger] child_port_reads_producer(calls, root.end, i, child as usize,
                    input_port, value.input, inputs, values)
                && selected.children@[i as int].child._signature@.call.call.form == argument.form;
            let i = producer as int;
            assert(child_port_reads_producer(calls, root.end, producer, child as usize,
                input_port, value.input, inputs, values));
            assert(i < child);
            assert(evaluated_nor_child(aliases, caller, prepared, binding, layouts, forms, final_wiring, traced,
                inputs, values, producer, children[i]));
            assert(child_call_binding(selected.children@[i], *binding.references, &traced.builtin, calls[i]));
            let reference = calls[i].reference as int;
            let range = root.end.table.ranges@[reference]->Some_0;
            let output = instance_wire_values(
                root.end.table.wires@.subrange(range.start as int, range.end as int), inputs, values);
            assert(children[i].output == output);
            assert(port_values(call.inputs, value.input)[port] == output);
            assert(value.ports == port_values(call.inputs, value.input));
            assert(value.ports[port] == children[i].output);
            assert(selected.children@[i].child.reference == binding.references.start + argument.source->NestedCall_0);
        }
    };
}

/// 最終配線から根 NOR と全ての子の値を取り出す。
///
/// 根と子で同じ末尾の配線表を使い、入れ子の実引数を対応する子の出力に結び付ける。
#[verifier::spinoff_prover]
pub(super) proof fn rooted_nor_source_arguments<'s, 'p, 'a>(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
    prepared: &PreparedExpansionBody, body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>,
    bindings: Seq<CallBinding>, roots: Seq<NorBinding<'s, 'p, 'a>>, limit: usize, layout_limit: usize,
    steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, final_wiring: WiringView,
    index: int, inputs: Seq<bool>, values: Seq<bool>,
) -> (evaluation: EvaluatedNestedCall)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring),
        0 <= index < roots.len(), roots[index].selected.prepared.output_slot < slot,
        forall|i: int, j: int| 0 <= i < j < roots.len() ==>
            (#[trigger] roots[i]).selected.prepared.output_slot < (#[trigger] roots[j]).selected.prepared.output_slot,
        nor_source_binding_matches(aliases, plan, table, caller, prepared, &roots[index], forms),
        nor_definition_determined(roots[index].selected.prepared, prepared.projections.call_arguments.arguments@),
        nor_binding_fits_body(roots[index], roots[index].selected.prepared.root.expression.source, forms,
            body.input_widths@, body.definitions@, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        body.input_widths@.len() == prepared.typed.literals.wiring->Checked_0.drivers.signature.inputs@.len(),
        gate_values_match(inputs, final_wiring.gates, values), values.len() == final_wiring.gates.len() <= usize::MAX,
        wires_available(final_wiring.definitions, layouts.inputs.total_bits_model(), values.len()),
        inputs.len() == layouts.inputs.total_bits_model(),
    ensures evaluated_nor_call_matches(aliases, caller, prepared, &roots[index], port_values(&layouts.inputs, inputs),
        definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values), evaluation),
{
    let binding = roots[index];
    let selected = &binding.selected;
    let traced = rooted_trace_nor_evaluation(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor,
        final_wiring, index, inputs, values);
    let count = selected.children@.len();
    vstd::std_specs::vec::axiom_spec_len(&selected.children);
    assert forall|i: int| #![trigger selected.children@[i]] 0 <= i < count implies
        exists|value: EvaluatedCallBits|
            #[trigger] evaluated_nor_child(aliases, caller, prepared, &binding, layouts, forms, final_wiring, &traced,
                inputs, values, i as usize, value) by {
        nor_trace_child_values(aliases, plan, table, caller, prepared, &binding, body, layouts, layout_limit,
            forms, final_wiring, &traced, inputs, values, i as usize);
    };
    let children = Seq::new(count, |i: int| choose|value: EvaluatedCallBits|
        #[trigger] evaluated_nor_child(aliases, caller, prepared, &binding, layouts, forms, final_wiring, &traced,
            inputs, values, i as usize, value));
    assert forall|i: int| 0 <= i < children.len() implies
        evaluated_nor_child(aliases, caller, prepared, &binding, layouts, forms, final_wiring, &traced,
            inputs, values, i as usize, #[trigger] children[i]) by {
        let selected_child = selected.children@[i];
    };
    let ports = port_values(&traced.builtin.1, traced.evaluation.2.arguments);
    assert(ports.len() == 2) by { reveal(nor_call_group_evaluation_matches); };
    let assigned = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values);
    let prior = assigned.take(selected.prepared.output_slot as int);
    let incoming = port_values(&layouts.inputs, inputs);
    assert forall|p: int| 0 <= p < 2 implies
        #[trigger] evaluated_nor_root_port_matches(aliases, caller, prepared, &binding, incoming, prior,
            ports, children, p) by {
        reveal(evaluated_nor_root_port_matches);
        let argument = selected.arguments@[p];
        if argument.source.has_direct_wires() {
            nor_root_atom_value(aliases, plan, table, caller, prepared, &binding, body, layouts, layout_limit, forms,
                final_wiring, &traced, inputs, values, p as usize);
        } else {
            assert(argument.source is NestedCall) by {
                reveal(nor_call_group_evaluation_matches);
                reveal(argument_prefix_wires);
                reveal(argument_source_available);
                port_bit_layout_port(seq![1u64, 1u64], 2, traced.builtin.1, p as usize);
                assert(argument_source_available(&traced.evaluation.2.invocation, argument.source));
            };
            let child = nor_root_child_value(aliases, plan, table, caller, prepared, &binding, layouts, forms,
                &traced, final_wiring.gates, inputs, values, p as usize);
            assert(child.2 == ports[p]);
            let i = child.0 as int;
            assert(evaluated_nor_child(aliases, caller, prepared, &binding, layouts, forms, final_wiring, &traced,
                inputs, values, child.0, children[i]));
            reveal(evaluated_nor_child);
            reveal(nor_call_group_evaluation_matches);
            reveal(nor_root_children_bound);
            let calls = traced.evaluation.0;
            assert(child_call_binding(selected.children@[i], *binding.references, &traced.builtin, calls[i]));
            assert(calls[i].reference == argument.source->NestedCall_0);
            assert(children[i].output == ports[p]);
        }
        assert(ports[p].len() == 1) by {
            reveal(nor_call_group_evaluation_matches);
            assert(p == 0 || p == 1);
        };
    };
    assert forall|i: int| #![trigger children[i]] 0 <= i < children.len() implies
        evaluated_expression_child_matches(aliases, caller, prepared, selected.prepared.definition,
            binding.references.start, selected.children@, incoming, prior, children, i) by {
        nor_evaluated_child_sources(aliases, caller, prepared, &binding, layouts, forms, final_wiring,
            &traced, inputs, values, children, i);
    };
    assert(nor_children_have_single_output(selected.children@)) by {
        reveal(nor_children_have_single_output);
        assert forall|i: int| 0 <= i < selected.children@.len() implies {
            let child = (#[trigger] selected.children@[i]).child;
            &&& child._signature@.call.target.port_counts().outputs == 1
            &&& (child._signature@.signature matches crate::project::FuncCallSignature::Function(ports)
                ==> ports.outputs@.len() == 1)
        } by {
            reveal(evaluated_nor_child);
            assert(evaluated_nor_child(aliases, caller, prepared, &binding, layouts, forms, final_wiring, &traced,
                inputs, values, i as usize, children[i]));
        };
    };
    let root = traced.evaluation.2;
    assert(root.arguments.len() == 2 && ports == seq![seq![root.arguments[0]], seq![root.arguments[1]]]) by {
        reveal(nor_call_group_evaluation_matches);
    };
    let evaluation = EvaluatedNestedCall { root: EvaluatedCallBits { input: root.arguments, ports, output: root.outputs }, children };
    assert(selected.arguments@.len() == 2) by { reveal(nor_root_arguments_match_widths); };
    assert(0 <= selected.prepared.output_slot < assigned.len());
    assert(assigned[selected.prepared.output_slot as int] == root.outputs);
    assert(root.outputs == seq![!(root.arguments[0] || root.arguments[1])]);
    assert(evaluation.children.len() == selected.children@.len());
    assert forall|port: int| 0 <= port < 2 implies
        #[trigger] evaluated_nor_root_port_matches(aliases, caller, prepared, &binding, incoming,
            assigned.take(selected.prepared.output_slot as int), evaluation.root.ports, evaluation.children, port) by {
        assert(evaluated_nor_root_port_matches(aliases, caller, prepared, &binding, incoming, prior, ports, children, port));
    };
    assert(evaluated_nor_call_matches(aliases, caller, prepared, &binding, incoming, assigned, evaluation)) by {
        reveal(evaluated_nor_call_matches);
    };
    evaluation
}

#[verifier::opaque]
spec fn evaluated_nested_child(
    aliases: &UseAliases, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, index: int,
    selected: &ResolvedTemplateCall, layouts: &Layouts, step: WiringStep, forms: Seq<Form>,
    calls: Seq<ChildCall>, root: &NestedRootEvaluation, inputs: Seq<bool>, gates: Seq<bool>,
    child_index: usize, evaluation: EvaluatedCallBits,
) -> bool {
    let project = aliases.targets.project_model();
    let selected_child = selected.children@[child_index as int];
    let call = calls[child_index as int];
    let positions = Seq::new(call.arguments@.len(), |port: int| call.arguments@[port].form);
    let ports = evaluation.ports;
    let prior = prior_definition_values(layouts, step, inputs, gates);
    let incoming = port_values(&layouts.inputs, inputs);
    let wiring = prepared.typed.literals.wiring->Checked_0;
    let reference = call.reference as int;
    &&& arguments_are_determined(call.arguments@)
    &&& ports == port_values(call.inputs, evaluation.input)
    &&& ports.len() == call.arguments@.len()
    &&& nor_evaluation(call.circuit, evaluation.input, evaluation.output)
    &&& (selected_child.template.is_none() ==> {
        let arguments = evaluation.input;
        &&& arguments.len() == 2
        &&& ports == seq![seq![arguments[0]], seq![arguments[1]]]
        &&& evaluation.output == seq![!(arguments[0] || arguments[1])]
        })
    &&& 0 <= reference < root.end.table.ranges@.len()
    &&& root.end.table.ranges@[reference] matches Some(range)
            && range.start <= range.end <= root.end.table.wires@.len()
            && evaluation.output == instance_wire_values(
                root.end.table.wires@.subrange(range.start as int, range.end as int), inputs, gates)
    &&& call_argument_positions(forms, selected_child.child._signature@.call.call, positions)
    &&& forall|port: int| 0 <= port < call.arguments@.len()
            && call.arguments@[port].source.has_direct_wires() ==>
            source_call_argument_value(&project.sources_model()[caller.0 as int], &project.circuits_model()[caller.0 as int],
                &wiring, caller.1, prepared.projections.calls@[index].definition, #[trigger] positions[port], caller.2,
                incoming, prior, call._input_widths@[port], ports[port])
    &&& forall|port: usize| port < call.arguments@.len()
            && (#[trigger] call.arguments@[port as int]).source is NestedCall ==>
            exists|producer: usize| #[trigger] child_port_reads_producer(calls, root.end, producer, child_index, port,
                evaluation.input, inputs, gates)
                && selected.children@[producer as int].child._signature@.call.call.form == positions[port as int]
}

/// 子の評価と、元の引数または先行する子の出力に対応する入力値を、同じ配線履歴から取り出す。
proof fn nested_child_values<'s, 'p, 'a>(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
    index: int, selected: &ResolvedTemplateCall, body: &LoweringBody, layouts: &Layouts, layout_limit: usize,
    step: WiringStep, forms: Seq<Form>, builtin: &(NorNetlist, PortBitLayout), invocation: CallerArguments<'s, 'p, 'a>,
    calls: Seq<ChildCall<'s, 'p, 'a>>, root: &NestedRootEvaluation<'s, 'p, 'a>, combined: Seq<NorGate>,
    inputs: Seq<bool>, gates: Seq<bool>,
    child_index: usize,
) -> (evaluation: EvaluatedCallBits)
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
        aliases.resolved_template_call_matches(plan, caller, prepared, index, *selected),
        selected_children_reachable(selected, prepared.projections.call_arguments.arguments@),
        prepared.typed.literals.wiring matches FuncWiringResult::Checked(wiring)
            && body.input_widths@.len() == wiring.drivers.signature.inputs@.len(),
        ({
            let project = aliases.targets.project_model();
            &&& caller.0 < project.circuits_model().len() && caller.0 < project.sources_model().len()
            &&& forms == project.circuits_model()[caller.0 as int].syntax.forms@
        }),
        resolved_call_fits_body(*selected, body.input_widths@, body.definitions@, forms, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        step.from == selected.group.outputs.start,
        step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), step.from as nat),
        wiring_view_is_prefix(step.before, step.after),
        wires_available(step.after.definitions, layouts.inputs.total_bits_model(), gates.len()),
        nested_group_invocation_matches(selected, forms, layouts, builtin, step.before, invocation, calls),
        selected.group.references.start <= selected.group.references.end,
        child_index < calls.len() == selected.children@.len(),
        child_wiring_trace_matches(&invocation, calls, calls.len(),
            (selected.group.references.end - selected.group.references.start) as usize,
            step.before.gates, root.trace, root.end, layouts.inputs.total_bits_model()),
        child_ranges_match(calls, calls.len(), root.end.table.ranges@),
        root.end.gates.len() <= combined.len() && root.end.gates == combined.take(root.end.gates.len() as int),
        inputs.len() == layouts.inputs.total_bits_model(),
        gate_values_match(inputs, combined, gates), gates.len() == combined.len() <= usize::MAX,
    ensures evaluated_nested_child(aliases, caller, prepared, index, selected, layouts, step, forms,
        calls, root, inputs, gates, child_index, evaluation),
{
    reveal(evaluated_nested_child);
    reveal(nested_group_invocation_matches);
    reveal(selected_children_reachable);
    let child = child_index as int;
    let call = calls[child];
    let selected_child = selected.children@[child];
    assert(child_call_binding(selected_child, selected.group.references, builtin, call));
    let count = (selected.group.references.end - selected.group.references.start) as usize;
    let (evaluation, arguments_from, mapped) = trace_child_wire_values(selected_child, selected.group.references, builtin,
        invocation, calls, step.before.gates, root, combined, inputs, gates, layouts.inputs.total_bits_model(), child_index);
    aliases.expansion_callee_template_evidence(*plan, caller, prepared, index);
    aliases.expansion_child_arguments_in_source_order(*plan, caller, prepared, index, child);
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[caller.0 as int];
    let parsed = &project.circuits_model()[caller.0 as int];
    let wiring = prepared.typed.literals.wiring->Checked_0;
    let definition = prepared.projections.calls@[index].definition;
    let range = selected_child.child.arguments;
    let projected = prepared.projections.call_arguments.arguments@.subrange(range.start as int, range.end as int);
    assert(call.arguments@ == projected);
    let positions = Seq::new(call.arguments@.len(), |port: int| call.arguments@[port].form);
    assert(call_argument_positions(forms, selected_child.child._signature@.call.call, positions));
    let ports = evaluation.ports;
    let incoming = port_values(&layouts.inputs, inputs);
    let prior = prior_definition_values(layouts, step, inputs, gates);
    reveal(port_values);
    assert forall|port: int| 0 <= port < call.arguments@.len()
        && call.arguments@[port].source.has_direct_wires() implies
        source_call_argument_value(source, parsed, &wiring, caller.1, definition, #[trigger] positions[port],
            caller.2, incoming, prior, call._input_widths@[port], ports[port]) by {
        assert(expression_argument_matches_width(source, forms, body.input_widths@, body.definitions@,
            *selected, child, port, caller.2));
        assert(call._input_widths@[port] == super::super::super::frontend::expression_input_width(selected_child, port));
        assert(call.arguments@[port] == prepared.projections.call_arguments.arguments@[range.start + port]);
        expanded_port_value(body, layouts, layout_limit, step, call.arguments@, call.inputs, call._input_widths@,
            call._layout_limit@, arguments_from, mapped, inputs, gates, caller.2, port as usize);
        aliases.expansion_child_atom_value_from_source(*plan, caller, prepared, index, child, port,
            incoming, prior, call._input_widths@[port], ports[port]);
    };
    assert forall|port: usize| port < call.arguments@.len()
        && (#[trigger] call.arguments@[port as int]).source is NestedCall implies
        exists|producer: usize| #[trigger] child_port_reads_producer(calls, root.end, producer, child_index, port,
            evaluation.input, inputs, gates)
            && selected.children@[producer as int].child._signature@.call.call.form == positions[port as int] by {
        let producer = child_nested_port_value(&invocation, calls, calls.len(), count, step.before.gates, root.trace,
            root.end, child_index, port, &arguments_from, mapped, inputs, gates, layouts.inputs.total_bits_model());
        assert(child_port_reads_producer(calls, root.end, producer, child_index, port, evaluation.input, inputs, gates));
        assert(call.arguments@[port as int] == prepared.projections.call_arguments.arguments@[range.start + port]);
        aliases.expansion_child_argument_evidence(*plan, caller, prepared, index, child, port as int);
        let group = selected.group;
        let children = group.postorder->Some_0@;
        let argument = call.arguments@[port as int];
        let earlier = choose|i: int| 0 <= i < child
            && (#[trigger] children[i]).reference == group.references.start + argument.source->NestedCall_0
            && children[i]._signature@.call.call.form == argument.form;
        assert(child_call_binding(selected.children@[earlier], group.references, builtin, calls[earlier]));
        assert(child_call_binding(selected.children@[producer as int], group.references, builtin, calls[producer as int]));
        if earlier < producer {
            assert(calls[earlier].reference != calls[producer as int].reference);
        } else if producer < earlier {
            assert(calls[producer as int].reference != calls[earlier].reference);
        }
        assert(earlier == producer);
    };
    assert(evaluated_nested_child(aliases, caller, prepared, index, selected, layouts, step, forms,
        calls, root, inputs, gates, child_index, evaluation));
    evaluation
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
        &&& wiring_view_is_prefix(step.before, step.after)
        &&& wiring_view_is_prefix(step.before, final_wiring)
        &&& wires_available(step.after.definitions, layouts.inputs.total_bits_model(), final_wiring.gates.len())
    }),
{
    mixed_trace_step_prefix(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring, at);
    reveal(mixed_trace);
    reveal(wiring_step_valid);
    reveal(binding_ready);
    let step = steps[at];
    wiring_step_keeps_prefix(body, layouts, forms, bindings, limit, step);
    if let Some(nested) = step.nested {
        let binding = bindings[step.group_before as int];
        nested_call_group_frame(&binding._selection@, forms, layouts, &nested.builtin, step.before, step.after,
            limit, nested.child_limit, definition_widths(body.definitions@), Ok(()));
    }
    existing_wires_keep_availability(step.after.definitions, layouts.inputs.total_bits_model(),
        step.after.gates.len(), final_wiring.gates.len());
}

/// 同じ末尾配線表から、全ての子の入出力を後順に取り出す。
proof fn collect_nested_child_values<'s, 'p, 'a>(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
    index: int, selected: &ResolvedTemplateCall, body: &LoweringBody, layouts: &Layouts, layout_limit: usize,
    step: WiringStep, forms: Seq<Form>, builtin: &(NorNetlist, PortBitLayout), invocation: CallerArguments<'s, 'p, 'a>,
    calls: Seq<ChildCall<'s, 'p, 'a>>, root: &NestedRootEvaluation<'s, 'p, 'a>, combined: Seq<NorGate>,
    inputs: Seq<bool>, gates: Seq<bool>,
) -> (children: Seq<EvaluatedCallBits>)
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
        aliases.resolved_template_call_matches(plan, caller, prepared, index, *selected),
        selected_children_reachable(selected, prepared.projections.call_arguments.arguments@),
        prepared.typed.literals.wiring matches FuncWiringResult::Checked(wiring)
            && body.input_widths@.len() == wiring.drivers.signature.inputs@.len(),
        ({
            let project = aliases.targets.project_model();
            &&& caller.0 < project.circuits_model().len() && caller.0 < project.sources_model().len()
            &&& forms == project.circuits_model()[caller.0 as int].syntax.forms@
        }),
        resolved_call_fits_body(*selected, body.input_widths@, body.definitions@, forms, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        step.from == selected.group.outputs.start,
        step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), step.from as nat),
        wiring_view_is_prefix(step.before, step.after),
        wires_available(step.after.definitions, layouts.inputs.total_bits_model(), gates.len()),
        nested_group_invocation_matches(selected, forms, layouts, builtin, step.before, invocation, calls),
        selected.group.references.start <= selected.group.references.end,
        calls.len() == selected.children@.len(),
        child_wiring_trace_matches(&invocation, calls, calls.len(),
            (selected.group.references.end - selected.group.references.start) as usize,
            step.before.gates, root.trace, root.end, layouts.inputs.total_bits_model()),
        child_ranges_match(calls, calls.len(), root.end.table.ranges@),
        root.end.gates.len() <= combined.len() && root.end.gates == combined.take(root.end.gates.len() as int),
        inputs.len() == layouts.inputs.total_bits_model(),
        gate_values_match(inputs, combined, gates), gates.len() == combined.len() <= usize::MAX,
    ensures
        children.len() == calls.len(),
        forall|i: int| 0 <= i < children.len() ==>
            evaluated_nested_child(aliases, caller, prepared, index, selected, layouts, step, forms,
                calls, root, inputs, gates, i as usize, #[trigger] children[i]),
{
    vstd::std_specs::vec::axiom_spec_len(&selected.children);
    assert forall|i: int| #![trigger calls[i]] 0 <= i < calls.len() implies exists|value: EvaluatedCallBits|
        #[trigger] evaluated_nested_child(aliases, caller, prepared, index, selected, layouts, step, forms,
            calls, root, inputs, gates, i as usize, value) by {
        nested_child_values(aliases, plan, caller, prepared, index, selected, body, layouts, layout_limit,
            step, forms, builtin, invocation, calls, root, combined, inputs, gates, i as usize);
    };
    let children = Seq::new(calls.len(), |i: int| choose|value: EvaluatedCallBits|
        #[trigger] evaluated_nested_child(aliases, caller, prepared, index, selected, layouts, step, forms,
            calls, root, inputs, gates, i as usize, value));
    assert forall|i: int| 0 <= i < children.len() implies
        evaluated_nested_child(aliases, caller, prepared, index, selected, layouts, step, forms,
            calls, root, inputs, gates, i as usize, #[trigger] children[i]) by {
        assert(i < calls.len());
        assert(child_call_binding(selected.children@[i], selected.group.references, builtin, calls[i])) by {
            reveal(nested_group_invocation_matches);
        };
        assert(exists|value: EvaluatedCallBits| #[trigger] evaluated_nested_child(aliases, caller, prepared, index,
            selected, layouts, step, forms, calls, root, inputs, gates, i as usize, value));
    };
    children
}

/// 根と後順の子を、同じ配線履歴とゲートの値割当で評価した結果。
pub(in crate::project::use_aliases::bit_func) struct EvaluatedNestedCall {
    pub(in crate::project::use_aliases::bit_func) root: EvaluatedCallBits,
    pub(in crate::project::use_aliases::bit_func) children: Seq<EvaluatedCallBits>,
}

/// 配線の評価から、根と各子が元の引数位置で読んだ値を取り出す。
pub(in crate::project::use_aliases::bit_func) open spec fn evaluated_nested_call_matches(
    aliases: &UseAliases, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, index: int,
    selected: &ResolvedTemplateCall, incoming: Seq<Seq<bool>>, assigned: Seq<Seq<bool>>, evaluation: EvaluatedNestedCall,
) -> bool {
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[caller.0 as int];
    let parsed = &project.circuits_model()[caller.0 as int];
    let wiring = &prepared.typed.literals.wiring->Checked_0;
    let definition = prepared.projections.calls@[index].definition;
    let callee = selected.template.circuit_model();
    let start = selected.group.outputs.start as int;
    let end = selected.group.outputs.end as int;
    let prior = assigned.take(start);
    &&& selected.group.postorder matches Some(postorder) && postorder@.len() == evaluation.children.len()
    &&& evaluation.children.len() == selected.children@.len()
    &&& forall|i: int| 0 <= i < evaluation.children.len() ==>
        #[trigger] expansion_child_reachable(selected.group, prepared.projections.call_arguments.arguments@,
            evaluation.children.len() as int, i)
    &&& nor_evaluation(callee.netlist_model(), evaluation.root.input, evaluation.root.output)
    &&& evaluation.root.ports == port_values(callee.input_layout_model(), evaluation.root.input)
    &&& evaluation.root.ports.len() == selected.arguments@.len()
    &&& port_values(callee.output_layout_model(), evaluation.root.output) == assigned.subrange(start, end)
    &&& forall|port: int| 0 <= port < selected.arguments@.len() ==> {
        let argument = #[trigger] selected.arguments@[port];
        let value = evaluation.root.ports[port];
        &&& value.len() == selected.template.input_widths_model()[port]
        &&& if argument.source.has_direct_wires() {
            source_call_argument_value(source, parsed, wiring, caller.1, definition, argument.form, caller.2,
                incoming, prior, selected.template.input_widths_model()[port], value)
        } else {
            &&& argument.source is NestedCall
            &&& exists|producer: int| 0 <= producer < evaluation.children.len()
                && (#[trigger] selected.children@[producer]).child.reference
                    == selected.group.references.start + argument.source->NestedCall_0
                && selected.children@[producer].child._signature@.call.call.form == argument.form
                && value == evaluation.children[producer].output
        }
    }
    &&& forall|child: int| #![trigger evaluation.children[child]] 0 <= child < evaluation.children.len() ==> {
        evaluated_expression_child_matches(aliases, caller, prepared, definition, selected.group.references.start,
            selected.children@, incoming, prior, evaluation.children, child)
    }
}

/// 入れ子の配線段から、各実引数に渡った値と最終配線に残った根の出力値を取り出す。
proof fn nested_trace_call_values(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
    selected: &ResolvedTemplateCall, body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    limit: usize, layout_limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, final_wiring: WiringView,
    at: int, inputs: Seq<bool>, gates: Seq<bool>,
) -> (evaluation: EvaluatedNestedCall)
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
        steps[at].nested matches Some(nested) && nested.arguments == prepared.projections.call_arguments.arguments@,
        ({
            let index = steps[at].group_before as int;
            &&& index < bindings.len()
            &&& binding_matches_selection(bindings[index], *selected)
            &&& aliases.resolved_template_call_matches(plan, caller, prepared, index, *selected)
        }),
        resolved_call_fits_body(*selected, body.input_widths@, body.definitions@, forms, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        gate_values_match(inputs, final_wiring.gates, gates),
        gates.len() == final_wiring.gates.len() <= usize::MAX,
        inputs.len() == layouts.inputs.total_bits_model(),
    ensures evaluated_nested_call_matches(aliases, caller, prepared, steps[at].group_before as int, selected,
        port_values(&layouts.inputs, inputs),
        definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, gates), evaluation),
{
    let step = steps[at];
    let index = step.group_before as int;
    let binding = bindings[index];
    let nested = step.nested->Some_0;
    let builtin = &nested.builtin;
    let widths = definition_widths(body.definitions@);
    let template = selected.template;
    let callee = template.circuit_model();
    let combined = final_wiring.gates;
    assert(binding_ready(binding, layouts, forms, widths)
        && selected_children_reachable(selected, prepared.projections.call_arguments.arguments@)
        && nested_call_group_result(selected, forms, layouts, builtin, step.before, step.after,
            limit, nested.child_limit, widths, Ok(()))) by {
        reveal(mixed_trace);
        reveal(wiring_step_valid);
    };
    assert(nor_evaluation_ready(callee.netlist_model(), callee.input_layout_model().total_bits_model() as nat)
        && callee.netlist_model().outputs@.len() == callee.output_layout_model().total_bits_model()
        && port_bit_layout_result(template.input_widths_model(), template.bit_limit_model(), Ok(*callee.input_layout_model()))
        && port_bit_layout_result(template.output_widths_model(), template.bit_limit_model(), Ok(*callee.output_layout_model()))
        && selected.group.outputs.start + template.output_widths_model().len() == selected.group.outputs.end
        && selected.group.outputs.end <= widths.len()
        && selected.arguments@.len() == template.input_widths_model().len()
        && forall|i: int| 0 <= i < template.output_widths_model().len() ==>
            widths[selected.group.outputs.start + i] == #[trigger] template.output_widths_model()[i]) by {
        reveal(binding_ready);
    };
    trace_call_frame(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring, at);
    mixed_trace_step_prefix(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring, at);
    let (calls, invocation, root) = nested_call_group_values(selected, forms, layouts, builtin, step.before, step.after,
        limit, nested.child_limit, widths, layout_limit, combined, inputs, gates);
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[caller.0 as int];
    let parsed = &project.circuits_model()[caller.0 as int];
    let wiring = &prepared.typed.literals.wiring->Checked_0;
    let definition = prepared.projections.calls@[index].definition;
    aliases.checked_types_keep_wiring(caller.0, caller.1, caller.2, prepared.typed, *wiring);
    aliases.expansion_child_scope_evidence(*plan, caller, prepared, index);
    assert(selected.group.references.start <= selected.group.references.end);
    vstd::std_specs::vec::axiom_spec_len(&selected.children);
    let incoming = port_values(&layouts.inputs, inputs);
    prior_definition_values_from_final(body, layouts, layout_limit, step, final_wiring, inputs, gates);
    let assigned = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, gates);
    let prior = assigned.take(selected.group.outputs.start as int);

    reveal(nested_group_invocation_matches);
    assert(calls.len() == selected.children@.len());
    let children = collect_nested_child_values(aliases, plan, caller, prepared, index, selected, body, layouts,
        layout_limit, step, forms, builtin, invocation, calls, &root, combined, inputs, gates);
    assert(selected.group.postorder matches Some(postorder) && postorder@.len() == children.len()) by {
        reveal(selected_children_reachable);
    };
    assert forall|i: int| 0 <= i < children.len() implies
        #[trigger] expansion_child_reachable(selected.group, prepared.projections.call_arguments.arguments@,
            children.len() as int, i) by {
        reveal(selected_children_reachable);
        assert(*selected.children@[i].child == selected.group.postorder->Some_0@[i]);
    };
    let root_layout = callee.input_layout_model();
    let ports = port_values(root_layout, root.arguments);
    let root_widths = template.input_widths_model();
    port_bit_layout_size(root_widths, template.bit_limit_model(), root_layout);
    assert(ports.len() == selected.arguments@.len()) by { reveal(port_values); };
    assert forall|port: int| 0 <= port < selected.arguments@.len() implies {
        let argument = #[trigger] selected.arguments@[port];
        let value = ports[port];
        &&& value.len() == root_widths[port]
        &&& if argument.source.has_direct_wires() {
            source_call_argument_value(source, parsed, wiring, caller.1, definition, argument.form, caller.2,
                incoming, prior, root_widths[port], value)
        } else {
            &&& argument.source is NestedCall
            &&& exists|producer: int| 0 <= producer < children.len()
                && (#[trigger] selected.children@[producer]).child.reference
                    == selected.group.references.start + argument.source->NestedCall_0
                && selected.children@[producer].child._signature@.call.call.form == argument.form
                && value == children[producer].output
        }
    } by {
        let argument = selected.arguments@[port];
        reveal(nor_evaluation);
        reveal(port_values);
        port_bit_layout_port(root_widths, template.bit_limit_model(), *root_layout, port as usize);
        if argument.source.has_direct_wires() {
            nested_root_atom_value(aliases, plan, caller, prepared, index, *selected, body, layouts, layout_limit,
                step, forms, &root, inputs, gates, port as usize);
        } else {
            reveal(argument_prefix_wires);
            reveal(argument_source_available);
            let span = root_layout.ranges_model()[port];
            assert(span.end <= root.mapped.len());
            assert(argument_source_available(&root.invocation, argument.source));
            assert(argument.source is NestedCall);
            let reference = argument.source->NestedCall_0;
            assert(root_port_reads_child(&root, selected.arguments@, root_layout, port as usize, inputs, gates));
            aliases.expansion_callee_template_evidence(*plan, caller, prepared, index);
            let range = prepared.projections.call_arguments.ranges@[index];
            let projections = &prepared.projections.call_arguments;
            assert(argument == projections.arguments@[range.start + port]);
            aliases.expansion_argument_evidence(*plan, caller, prepared.typed, wiring, prepared.projections.calls@[index],
                range, projections, *selected.group, port);
            let postorder = selected.group.postorder->Some_0@;
            let expected = selected.group._signature@.signature->Function_0.inputs@[port].ty;
            assert(prepared_nested_output_matches(postorder, selected.group.references.start, postorder.len() as int,
                argument, expected));
            let producer = choose|i: int| 0 <= i < postorder.len() as int
                && (#[trigger] postorder[i]).reference == selected.group.references.start + argument.source->NestedCall_0
                && postorder[i]._signature@.call.call.form == argument.form
                && postorder[i]._signature@.call.target.port_counts().outputs == 1
                && match postorder[i]._signature@.signature {
                    crate::project::FuncCallSignature::Nor =>
                        crate::project::port_types_equal(crate::project::ResolvedPortType::Bits(1), expected),
                    crate::project::FuncCallSignature::Function(ports) => ports.outputs@.len() == 1
                        && crate::project::port_types_equal(ports.outputs@[0].ty, expected),
                };
            assert(*selected.children@[producer].child == postorder[producer]) by { reveal(selected_children_reachable); };
            assert(child_call_binding(selected.children@[producer], selected.group.references, builtin, calls[producer]));
            assert(calls[producer].reference == reference);
            assert(evaluated_nested_child(aliases, caller, prepared, index, selected, layouts, step, forms,
                calls, &root, inputs, gates, producer as usize, children[producer]));
            reveal(evaluated_nested_child);
            assert(ports[port] == children[producer].output);
        }
    };
    assert forall|child: int| #![trigger children[child]] 0 <= child < children.len() implies {
        evaluated_expression_child_matches(aliases, caller, prepared, definition, selected.group.references.start,
            selected.children@, incoming, prior, children, child)
    } by {
        let expression = selected.children@[child];
        let values = children[child];
        let call = calls[child];
        reveal(evaluated_nested_child);
        assert(child_call_binding(expression, selected.group.references, builtin, call));
        assert(call.arguments@ == expression.arguments@);
        assert(evaluated_nested_child(aliases, caller, prepared, index, selected, layouts, step, forms,
            calls, &root, inputs, gates, child as usize, values));
        assert(values.ports.len() == expression.arguments@.len());
        assert(match expression.template {
            Some(template) => nor_evaluation(template.circuit_model().netlist_model(), values.input, values.output)
                && values.ports == port_values(template.circuit_model().input_layout_model(), values.input),
            None => values.input.len() == 2 && values.ports == seq![seq![values.input[0]], seq![values.input[1]]]
                && values.output == seq![!(values.input[0] || values.input[1])],
        });
        assert forall|port: int| 0 <= port < expression.arguments@.len() implies {
            let argument = #[trigger] expression.arguments@[port];
            let width = expression_input_width(expression, port);
            let value = values.ports[port];
            &&& value.len() == width
            &&& if argument.source.has_direct_wires() {
                source_call_argument_value(source, parsed, wiring, caller.1, definition, argument.form, caller.2,
                    incoming, prior, width, value)
            } else {
                &&& argument.source is NestedCall
                &&& exists|producer: int| 0 <= producer < child
                    && (#[trigger] selected.children@[producer]).child.reference
                        == selected.group.references.start + argument.source->NestedCall_0
                    && selected.children@[producer].child._signature@.call.call.form == argument.form
                    && value == children[producer].output
            }
        } by {
            let argument = expression.arguments@[port];
            let positions = Seq::new(call.arguments@.len(), |port: int| call.arguments@[port].form);
            assert(call.arguments@[port] == argument);
            assert(port < call.arguments@.len() <= usize::MAX) by {
                vstd::slice::axiom_spec_len(call.arguments);
            };
            assert(positions[port] == argument.form);
            reveal(nor_evaluation);
            reveal(port_values);
            port_bit_layout_port(call._input_widths@, call._layout_limit@, *call.inputs, port as usize);
            assert(call._input_widths@[port] == expression_input_width(expression, port));
            if !argument.source.has_direct_wires() {
                assert(argument.source is NestedCall);
                assert(call.arguments@[port as int].source is NestedCall);
                assert(port as usize as int == port);
                assert(exists|producer: usize| #[trigger] child_port_reads_producer(calls, root.end, producer,
                    child as usize, port as usize, values.input, inputs, gates)
                    && selected.children@[producer as int].child._signature@.call.call.form == positions[port]);
                let producer = choose|producer: usize|
                    #[trigger] child_port_reads_producer(calls, root.end, producer, child as usize, port as usize,
                        values.input, inputs, gates)
                    && selected.children@[producer as int].child._signature@.call.call.form == positions[port];
                assert(producer < child);
                assert(child_call_binding(selected.children@[producer as int], selected.group.references, builtin, calls[producer as int]));
                assert(evaluated_nested_child(aliases, caller, prepared, index, selected, layouts, step, forms,
                    calls, &root, inputs, gates, producer, children[producer as int]));
                assert(child_port_reads_producer(calls, root.end, producer, child as usize, port as usize,
                    values.input, inputs, gates));
                assert(values.ports[port] == children[producer as int].output);
            }
        };
    };
    assert forall|port: int, bit: int| 0 <= port < template.output_widths_model().len()
        && 0 <= bit < template.output_widths_model()[port] implies
        #[trigger] call_output_bit_has_value(layouts, callee, final_wiring.definitions, selected.group.outputs.start,
            port, bit, inputs, gates, root.outputs) by {
        assert(call_output_bit_has_value(layouts, callee, step.after.definitions, selected.group.outputs.start,
            port, bit, inputs, gates, root.outputs));
        reveal(call_output_bit_has_value);
    };
    assert(root.outputs.len() == callee.output_layout_model().total_bits_model()) by { reveal(nor_evaluation); };
    call_output_ports_match_definitions(body, layouts, layout_limit, binding, forms, final_wiring, inputs, gates, root.outputs);
    assert(port_values(callee.output_layout_model(), root.outputs)
        == assigned.subrange(selected.group.outputs.start as int, selected.group.outputs.end as int));
    EvaluatedNestedCall { root: EvaluatedCallBits { input: root.arguments, ports, output: root.outputs }, children }
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
        steps[at].nested.is_none(),
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
        assert(root_argument_matches_width(selected.group.expression.source, forms, body.input_widths@,
            body.definitions@, selected, port, caller.2));
        assert(argument_matches_width(source, forms, body.input_widths@, body.definitions@.take(step.from as int),
            argument, widths[port], caller.2));
        reveal(binding_ready);
        reveal(argument_prefix_wires);
        port_bit_layout_port(widths, binding._layout_limit@, *layout, port as usize);
        assert(argument_source_available(&invocation, argument.source));
        assert(argument.source.has_direct_wires());
        expanded_port_value(body, layouts, layout_limit, step, binding.arguments@, layout, widths,
            binding._layout_limit@, invocation, mapped, inputs, values, caller.2, port as usize);
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

/// 配線履歴から得た、実際の呼び出し段に対応する入出力値。
pub(in crate::project::use_aliases::bit_func) enum MixedCallEvaluation {
    Flat(Seq<bool>, Seq<bool>),
    Nested(EvaluatedNestedCall),
}

pub(in crate::project::use_aliases::bit_func) open spec fn evaluated_flat_call_matches(
    aliases: &UseAliases, caller: (usize, usize, u64), prepared: &PreparedExpansionBody, index: int,
    selected: ResolvedTemplateCall, incoming: Seq<Seq<bool>>, definitions: Seq<Seq<bool>>, input: Seq<bool>, output: Seq<bool>,
) -> bool {
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[caller.0 as int];
    let parsed = &project.circuits_model()[caller.0 as int];
    let wiring = prepared.typed.literals.wiring->Checked_0;
    let root = prepared.projections.calls@[index];
    let callee = selected.template.circuit_model();
    let first = selected.group.outputs.start as int;
    let end = selected.group.outputs.end as int;

    &&& nor_evaluation(callee.netlist_model(), input, output)
    &&& source_call_arguments_match(source, parsed, &wiring, caller.1, root.definition,
        selected.group._signature@.call.call, caller.2, incoming, definitions.take(first),
        selected.template.input_widths_model(), port_values(callee.input_layout_model(), input))
    &&& port_values(callee.output_layout_model(), output) == definitions.subrange(first, end)
}

/// 変換に成功した関数で、指定した呼び出しの引数値と左辺の値を取り出す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn mixed_function_call_evaluation(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
    selected: ResolvedTemplateCall, index: int, body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>,
    bindings: Seq<CallBinding>, widths: Seq<u64>, drivers: Seq<OutputDriver>, layout_limit: usize, gate_limit: usize,
    function: &LoweredBitFunc, steps: Ghost<Seq<WiringStep>>, inputs: Seq<bool>, values: Seq<bool>,
) -> (result: MixedCallEvaluation)
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
        mixed_function_success(body, layouts, forms, bindings, widths, drivers, gate_limit, function, steps@),
        wiring_trace_arguments_match(steps@, prepared.projections.call_arguments.arguments@),
        ordered_bindings(bindings),
        0 <= index < bindings.len(),
        binding_matches_selection(bindings[index], selected),
        aliases.resolved_template_call_matches(plan, caller, prepared, index, selected),
        resolved_call_fits_body(selected, body.input_widths@, body.definitions@, forms, caller.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        gate_values_match(inputs, function.netlist_model().gates@, values),
        values.len() == function.netlist_model().gates@.len() <= usize::MAX,
        inputs.len() == layouts.inputs.total_bits_model(),
    ensures
        flat_wiring_trace(steps@) ==> result is Flat,
        ({
            let definitions = definition_values_from_wires(&layouts.definitions, function.definition_wires@, inputs, values);
            let incoming = port_values(&layouts.inputs, inputs);
            match result {
                MixedCallEvaluation::Flat(input, output) =>
                    evaluated_flat_call_matches(aliases, caller, prepared, index, selected, incoming, definitions, input, output),
                MixedCallEvaluation::Nested(evaluation) =>
                    evaluated_nested_call_matches(aliases, caller, prepared, index, &selected, incoming, definitions, evaluation),
            }
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
    if step.nested.is_some() {
        assert(!flat_wiring_trace(steps@)) by { reveal(flat_wiring_trace); };
        assert(step.nested->Some_0.arguments == prepared.projections.call_arguments.arguments@) by {
            reveal(wiring_trace_arguments_match);
        };
        let evaluation = nested_trace_call_values(aliases, plan, caller, prepared, &selected, body, layouts, forms, bindings,
            gate_limit, layout_limit, steps@, slot, group, wiring, at, inputs, values);
        MixedCallEvaluation::Nested(evaluation)
    } else {
        let (input, output) = mixed_trace_source_call_values(aliases, plan, caller, prepared, selected, body, layouts, forms, bindings,
            gate_limit, layout_limit, steps@, slot, group, wiring, at, inputs, values);
        reveal(wiring_step_valid);
        MixedCallEvaluation::Flat(input, output)
    }
}

} // verus!
