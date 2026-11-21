//! 通常の定義と関数呼び出しを、同じ配線列へ定義順に変換する。

#[cfg(verus_only)]
mod source_arguments;
#[cfg(verus_only)]
pub(super) use source_arguments::mixed_function_source_call_values;

use super::*;
#[cfg(verus_only)]
use super::evaluation::{definition_values_from_wires, slot_values_match_wiring};
#[cfg(verus_only)]
use super::super::semantics::checked_definition_values;
use super::super::expansion::{CheckedExpansionCall, PreparedExpansionBody};
use super::super::templates::ResolvedTemplateCall;
use crate::project::{FunctionExpansionOrder, UseAliases};
#[cfg(verus_only)]
use super::super::frontend::{argument_matches_width, call_covers};
#[cfg(verus_only)]
use super::super::super::call_arity::CallArgumentSource;
use super::super::super::call_arity::ProjectedCallArgument;
use super::call_group::{BodyWiring, CallGroupError, lower_call_group};
use crate::syntax::Form;
#[cfg(verus_only)]
use super::call_group::{WiringView, call_group_result, call_group_values, call_group_wires_match, call_output_bit_has_value};
#[cfg(verus_only)]
use super::super::instances::{instance_gates_match, instance_wire_values};
#[cfg(verus_only)]
use crate::netlist::{gate_values_match, nor_evaluation};
#[cfg(verus_only)]
use super::call_arguments::{CallerArguments, layout_argument_ready};
#[cfg(verus_only)]
use crate::syntax::form_spans_valid;

verus! {

/// 先行する関数のネットリストと、呼び出し元の実引数。
pub(super) struct CallBinding<'s, 'p, 'a> {
    pub(super) group: &'s CheckedExpansionCall<'p, 'a>,
    pub(super) arguments: &'s [ProjectedCallArgument],
    pub(super) callee: &'s LoweredBitFunc,
    pub(super) _input_widths: Ghost<Seq<u64>>,
    pub(super) _output_widths: Ghost<Seq<u64>>,
    pub(super) _layout_limit: Ghost<usize>,
}

/// 定義順に配線へ変換するときの診断。
#[derive(Debug)]
pub(in crate::project::use_aliases::bit_func) enum MixedWiringError<'p, 'a> {
    /// 基底 NOR を追加できなかった右辺の範囲。
    LocalGateCapacity(LocatedName<'p, 'a>),
    /// 呼び出し式または実引数の診断。
    Call(CallGroupError<'p, 'a>),
}

pub(super) struct WiringStep {
    #[cfg(verus_only)]
    from: usize,
    #[cfg(verus_only)]
    to: usize,
    #[cfg(verus_only)]
    group_before: usize,
    #[cfg(verus_only)]
    group_after: usize,
    #[cfg(verus_only)]
    before: WiringView,
    #[cfg(verus_only)]
    after: WiringView,
}

pub(super) open spec fn binding_covers(bindings: Seq<CallBinding>, slot: int) -> bool {
    exists|g: int| 0 <= g < bindings.len()
        && (#[trigger] bindings[g]).group.outputs.start <= slot < bindings[g].group.outputs.end
}

#[verifier::opaque]
pub(super) closed spec fn binding_ready(
    binding: CallBinding, layouts: &Layouts, forms: Seq<Form>, widths: Seq<u64>,
) -> bool {
    let group = binding.group;
    let callee = binding.callee;
    let inputs = binding._input_widths@;
    let outputs = binding._output_widths@;
    let limit = binding._layout_limit@;
    &&& form_spans_valid(group.expression.source.text, forms, group.expression.source.text.spec_bytes().len() as int)
    &&& group.outputs.start < group.outputs.end <= widths.len()
    &&& group.outputs.start + outputs.len() == group.outputs.end
    &&& binding.arguments@.len() == inputs.len()
    &&& port_bit_layout_result(inputs, limit, Ok(*callee.input_layout_model()))
    &&& port_bit_layout_result(outputs, limit, Ok(*callee.output_layout_model()))
    &&& nor_evaluation_ready(callee.netlist_model(), callee.input_layout_model().total_bits_model() as nat)
    &&& callee.netlist_model().outputs@.len() == callee.output_layout_model().total_bits_model()
    &&& forall|i: int| 0 <= i < outputs.len() ==> widths[group.outputs.start + i] == #[trigger] outputs[i]
    &&& forall|i: int| 0 <= i < binding.arguments@.len() ==> {
        let range = callee.input_layout_model().ranges_model()[i];
        layout_argument_ready(group.expression.source, forms, layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
            preceding_port_bits(widths, group.outputs.start as nat) as int, #[trigger] binding.arguments@[i],
            (range.end - range.start) as usize)
    }
}

/// 先行定義の幅と、呼び出し先の入力ポートごとのビット範囲を結び付ける。
proof fn call_argument_bits_available(
    binding: CallBinding, body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>,
    capacity: usize, width_limit: u64, port: int,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        binding.group.outputs.start <= body.definitions@.len(),
        0 <= port < binding.arguments@.len() == binding._input_widths@.len(),
        port_bit_layout_result(binding._input_widths@, binding._layout_limit@, Ok(*binding.callee.input_layout_model())),
        argument_matches_width(binding.group.expression.source, forms, body.input_widths@,
            body.definitions@.take(binding.group.outputs.start as int), binding.arguments@[port],
            binding._input_widths@[port], width_limit),
    ensures ({
        let range = binding.callee.input_layout_model().ranges_model()[port];
        layout_argument_ready(binding.group.expression.source, forms,
            layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
            preceding_port_bits(definition_widths(body.definitions@), binding.group.outputs.start as nat) as int,
            binding.arguments@[port], (range.end - range.start) as usize)
    }),
{
    let inputs = binding._input_widths@;
    let layout = binding.callee.input_layout_model();
    port_bit_layout_size(inputs, binding._layout_limit@, layout);
    port_bit_layout_port(inputs, binding._layout_limit@, *layout, port as usize);
    let range = layout.ranges_model()[port];
    let width = (range.end - range.start) as usize;
    assert(width == inputs[port]);
    if let CallArgumentSource::Driver(driver) = binding.arguments@[port].source {
        let first = binding.group.outputs.start;
        let used = preceding_port_bits(definition_widths(body.definitions@), first as nat) as int;
        assert forall|bit: int| 0 <= bit < width implies
            #[trigger] driver_bit_available(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), used, driver, bit) by {
            body_driver_bits_fit_layout(body.input_widths@, body.definitions@, layouts, capacity, first as int, used, driver, inputs[port], bit);
        };
    }
}

pub(in crate::project::use_aliases::bit_func) open spec fn resolved_call_fits_body(
    call: ResolvedTemplateCall, inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>, forms: Seq<Form>, limit: u64,
) -> bool {
    let first = call.group.outputs.start;
    let end = call.group.outputs.end;
    let outputs = call.template.output_widths_model();
    let callee_inputs = call.template.input_widths_model();
    &&& form_spans_valid(call.group.expression.source.text, forms, call.group.expression.source.text.spec_bytes().len() as int)
    &&& first < end <= definitions.len()
    &&& first + outputs.len() == end
    &&& forall|i: int| 0 <= i < outputs.len() ==> definitions[first + i].width == #[trigger] outputs[i]
    &&& forall|port: int| 0 <= port < call.arguments@.len() ==>
        argument_matches_width(call.group.expression.source, forms, inputs, definitions.take(first as int),
            #[trigger] call.arguments@[port], callee_inputs[port], limit)
}

pub(super) open spec fn binding_matches_selection(binding: CallBinding, call: ResolvedTemplateCall) -> bool {
    &&& binding.group == call.group
    &&& binding.arguments == call.arguments
    &&& binding.callee == call.template.circuit_model()
    &&& binding._input_widths@ == call.template.input_widths_model()
    &&& binding._output_widths@ == call.template.output_widths_model()
    &&& binding._layout_limit@ == call.template.bit_limit_model()
}

/// 選択した呼び出し先と元の実引数を借り、配線生成に渡す。
pub(super) fn bind_resolved_call<'s, 'p, 'a>(
    _aliases: &UseAliases<'_, 'p, 'a>, selected: &ResolvedTemplateCall<'s, 'p, 'a>, _body: &LoweringBody,
    _layouts: &Layouts, Ghost(forms): Ghost<Seq<Form>>, Ghost(capacity): Ghost<usize>,
    Ghost(context): Ghost<(&FunctionExpansionOrder<'p, 'a>, (usize, usize, u64), &PreparedExpansionBody<'p, 'a>, int)>,
) -> (binding: CallBinding<'s, 'p, 'a>)
    requires
        _aliases.resolved_template_call_matches(context.0, context.1, context.2, context.3, *selected),
        body_definition_layouts(_body.input_widths@, _body.definitions@, capacity, _layouts),
        resolved_call_fits_body(*selected, _body.input_widths@, _body.definitions@, forms, context.1.2),
    ensures
        binding_matches_selection(binding, *selected),
        binding_ready(binding, _layouts, forms, definition_widths(_body.definitions@)),
{
    let template = selected.template;
    let binding = CallBinding {
        group: selected.group,
        arguments: selected.arguments,
        callee: template.circuit(),
        _input_widths: Ghost(template.input_widths_model()),
        _output_widths: Ghost(template.output_widths_model()),
        _layout_limit: Ghost(template.bit_limit_model()),
    };
    proof {
        let position = context.0.position_model(selected.group._order@.0)->Some_0;
        let width_limit = context.1.2;
        _aliases.template_circuit_evidence(position, width_limit, template);
        reveal(binding_ready);
        assert forall|i: int| 0 <= i < binding.arguments@.len() implies {
            let range = binding.callee.input_layout_model().ranges_model()[i];
            layout_argument_ready(binding.group.expression.source, forms, _layouts.inputs.ranges_model(),
                _layouts.definitions.ranges_model(), preceding_port_bits(definition_widths(_body.definitions@),
                    binding.group.outputs.start as nat) as int, #[trigger] binding.arguments@[i],
                (range.end - range.start) as usize)
        } by {
            call_argument_bits_available(binding, _body, _layouts, forms, capacity, width_limit, i);
        };
    }
    binding
}

/// 元の定義順を保ち、選択済みの各呼び出しを配線生成用の参照に変換する。
fn bind_resolved_calls<'s, 'p, 'a>(
    aliases: &UseAliases<'_, 'p, 'a>, selected: &[ResolvedTemplateCall<'s, 'p, 'a>], body: &LoweringBody,
    layouts: &Layouts, Ghost(forms): Ghost<Seq<Form>>, Ghost(capacity): Ghost<usize>,
    Ghost(context): Ghost<(&FunctionExpansionOrder<'p, 'a>, (usize, usize, u64), &PreparedExpansionBody<'p, 'a>)>,
) -> (bindings: Vec<CallBinding<'s, 'p, 'a>>)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        forall|index: int| 0 <= index < selected@.len() ==> {
            let call = #[trigger] selected@[index];
            &&& aliases.resolved_template_call_matches(context.0, context.1, context.2, index, call)
            &&& resolved_call_fits_body(call, body.input_widths@, body.definitions@, forms, context.1.2)
        },
    ensures
        bindings@.len() == selected@.len(),
        forall|index: int| 0 <= index < bindings@.len() ==> {
            let binding = #[trigger] bindings@[index];
            &&& binding_matches_selection(binding, selected@[index])
            &&& binding_ready(binding, layouts, forms, definition_widths(body.definitions@))
        },
{
    let mut bindings = Vec::new();
    let mut index = 0;
    while index < selected.len()
        invariant
            index == bindings@.len() <= selected@.len(),
            body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
            forall|i: int| 0 <= i < selected@.len() ==> {
                let call = #[trigger] selected@[i];
                &&& aliases.resolved_template_call_matches(context.0, context.1, context.2, i, call)
                &&& resolved_call_fits_body(call, body.input_widths@, body.definitions@, forms, context.1.2)
            },
            forall|i: int| 0 <= i < bindings@.len() ==> {
                let binding = #[trigger] bindings@[i];
                &&& binding_matches_selection(binding, selected@[i])
                &&& binding_ready(binding, layouts, forms, definition_widths(body.definitions@))
            },
        decreases selected@.len() - index,
    {
        let binding = bind_resolved_call(aliases, &selected[index], body, layouts, Ghost(forms), Ghost(capacity),
            Ghost((context.0, context.1, context.2, index as int)));
        bindings.push(binding);
        index += 1;
    }
    bindings
}

pub(super) open spec fn ordered_bindings(bindings: Seq<CallBinding>) -> bool {
    forall|a: int, b: int| 0 <= a < b < bindings.len() ==>
        (#[trigger] bindings[a]).group.outputs.end <= (#[trigger] bindings[b]).group.outputs.start
}

spec fn binding_cursor(bindings: Seq<CallBinding>, slot: usize, cursor: int) -> bool {
    &&& 0 <= cursor <= bindings.len()
    &&& forall|g: int| 0 <= g < cursor ==> (#[trigger] bindings[g]).group.outputs.end <= slot
    &&& forall|g: int| cursor <= g < bindings.len() ==> slot <= (#[trigger] bindings[g]).group.outputs.start
}

proof fn advance_binding_cursor(bindings: Seq<CallBinding>, slot: usize, cursor: usize, end: usize, call: bool)
    requires
        ordered_bindings(bindings), binding_cursor(bindings, slot, cursor as int),
        forall|g: int| 0 <= g < bindings.len() ==>
            (#[trigger] bindings[g]).group.outputs.start < bindings[g].group.outputs.end,
        if call {
            cursor < bindings.len() && bindings[cursor as int].group.outputs.start == slot
                && end == bindings[cursor as int].group.outputs.end > slot
        } else {
            end == slot + 1
                && (cursor < bindings.len() ==> slot < bindings[cursor as int].group.outputs.start)
        },
    ensures
        binding_cursor(bindings, end, if call { cursor + 1 } else { cursor as int }),
        !call ==> !binding_covers(bindings, slot as int),
{
    if call {
        assert(cursor + 1 <= bindings.len());
        assert forall|g: int| 0 <= g <= cursor implies
            (#[trigger] bindings[g]).group.outputs.end <= end by {
            if g < cursor { assert(bindings[g].group.outputs.end <= slot); }
        };
        assert forall|g: int| cursor < g < bindings.len() implies
            end <= (#[trigger] bindings[g]).group.outputs.start by {
            assert(bindings[cursor as int].group.outputs.end <= bindings[g].group.outputs.start);
        };
    } else {
        assert forall|g: int| cursor <= g < bindings.len() implies
            slot < (#[trigger] bindings[g]).group.outputs.start by {
            if cursor < g {
                assert(bindings[cursor as int].group.outputs.end <= bindings[g].group.outputs.start);
            }
        };
    }
}

spec fn wiring_empty(view: WiringView) -> bool {
    view.definitions.len() == 0 && view.gates.len() == 0 && view.origins.len() == 0
}

spec fn local_step(
    body: &LoweringBody, layouts: &Layouts, step: WiringStep,
) -> bool {
    let at = step.from as int;
    let definition = body.definitions@[at];
    &&& step.to == step.from + 1
    &&& step.group_before == step.group_after
    &&& slot_wiring_matches(definition, layouts, step.after.definitions, step.after.gates, step.after.origins, at)
    &&& step.after.definitions.take(step.before.definitions.len() as int) == step.before.definitions
    &&& gate_step_matches(layouts, step.before.definitions, definition.rhs, step.from,
        step.before.gates, step.after.gates, step.before.origins, step.after.origins)
}

#[verifier::opaque]
spec fn wiring_step_valid(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    limit: usize, step: WiringStep,
) -> bool {
    let widths = definition_widths(body.definitions@);
    &&& step.from < step.to <= body.definitions@.len()
    &&& step.before.definitions.len() == preceding_port_bits(widths, step.from as nat)
    &&& step.after.definitions.len() == preceding_port_bits(widths, step.to as nat)
    &&& step.before.gates.len() == step.before.origins.len() <= limit
    &&& step.after.gates.len() == step.after.origins.len() <= limit
    &&& if step.group_before == step.group_after {
        !binding_covers(bindings, step.from as int) && local_step(body, layouts, step)
    } else {
        let group = step.group_before as int;
        let binding = bindings[group];
        &&& 0 <= group < bindings.len() && step.group_after == group + 1
        &&& step.from == binding.group.outputs.start && step.to == binding.group.outputs.end
        &&& binding_ready(binding, layouts, forms, widths)
        &&& call_group_result(binding.group, forms, binding.arguments@, layouts, binding.callee,
            step.before, step.after, limit, definition_widths(body.definitions@), binding._output_widths@, Ok(()))
    }
}

#[verifier::opaque]
pub(super) closed spec fn mixed_trace(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, limit: usize,
    steps: Seq<WiringStep>, slot: usize, group: usize, wiring: WiringView,
) -> bool {
    &&& if steps.len() == 0 { slot == 0 && group == 0 && wiring_empty(wiring) }
        else {
            let last = steps.last();
            last.to == slot && last.group_after == group && last.after == wiring
        }
    &&& forall|i: int| 0 <= i < steps.len() ==> {
        let step = #[trigger] steps[i];
        &&& wiring_step_valid(body, layouts, forms, bindings, limit, step)
        &&& if i == 0 { step.from == 0 && step.group_before == 0 && wiring_empty(step.before) }
            else {
                let prior = steps[i - 1];
                prior.to == step.from && prior.group_after == step.group_before && prior.after == step.before
            }
    }
}

/// 変換履歴の途中までに生成した定義について、その定義を追加した段階を得る。
proof fn mixed_trace_definition_step(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, limit: usize,
    steps: Seq<WiringStep>, slot: usize, group: usize, wiring: WiringView, end: int, definition: int,
) -> (at: int)
    requires
        mixed_trace(body, layouts, forms, bindings, limit, steps, slot, group, wiring),
        0 <= end < steps.len(),
        0 <= definition < steps[end].to,
    ensures
        0 <= at <= end,
        steps[at].from <= definition < steps[at].to,
        wiring_step_valid(body, layouts, forms, bindings, limit, steps[at]),
    decreases end,
{
    reveal(mixed_trace);
    if steps[end].from <= definition {
        end
    } else {
        assert(end > 0 && steps[end - 1].to == steps[end].from);
        mixed_trace_definition_step(body, layouts, forms, bindings, limit, steps, slot, group, wiring, end - 1, definition)
    }
}

spec fn wiring_view_is_prefix(before: WiringView, after: WiringView) -> bool {
    &&& before.gates.len() <= after.gates.len()
    &&& before.definitions.len() <= after.definitions.len()
    &&& before.origins.len() <= after.origins.len()
    &&& after.origins.take(before.origins.len() as int) == before.origins
    &&& after.gates.take(before.gates.len() as int) == before.gates
    &&& after.definitions.take(before.definitions.len() as int) == before.definitions
}

proof fn wiring_step_keeps_prefix(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    limit: usize, step: WiringStep,
)
    requires wiring_step_valid(body, layouts, forms, bindings, limit, step),
    ensures wiring_view_is_prefix(step.before, step.after),
{
    reveal(wiring_step_valid);
    if step.group_before == step.group_after {
        reveal(gate_step_matches);
        let definition = body.definitions@[step.from as int];
        if let Some(gate) = rhs_gate(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
            step.before.definitions, definition.rhs) {
            assert(step.after.gates == step.before.gates.push(gate));
            assert(step.after.gates.take(step.before.gates.len() as int) =~= step.before.gates);
        } else {
            assert(step.after.gates == step.before.gates);
            assert(step.after.gates.take(step.before.gates.len() as int) =~= step.before.gates);
        }
        assert(step.after.definitions.take(step.before.definitions.len() as int) == step.before.definitions);
        assert(step.after.origins.take(step.before.origins.len() as int) =~= step.before.origins);
    } else {
        let binding = bindings[step.group_before as int];
        let (invocation, mapped, outputs) = choose|invocation: CallerArguments, mapped: Seq<Wire>, outputs: Seq<Wire>|
            #[trigger] call_group_wires_match(binding.group, forms, binding.arguments@, layouts, binding.callee,
                step.before, step.after, binding._output_widths@, invocation, mapped, outputs);
        assert(instance_gates_match(step.before.gates, binding.callee.netlist_model().gates@, mapped, step.after.gates));
        assert(step.after.gates.take(step.before.gates.len() as int) == step.before.gates);
        assert(step.after.definitions.take(step.before.definitions.len() as int) =~= step.before.definitions);
    }
    assert(step.before.definitions.len() <= step.after.definitions.len()) by {
        let widths = definition_widths(body.definitions@);
        preceding_port_bits_grow(widths, step.from as nat, step.to as nat);
    };
}

/// 途中で追加したゲートと配線が、最終状態でも同じ添字にあることを示す。
proof fn mixed_trace_preserves_prefix(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, limit: usize,
    steps: Seq<WiringStep>, slot: usize, group: usize, final_wiring: WiringView, at: int, end: int,
)
    requires
        mixed_trace(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring),
        0 <= at <= end < steps.len(),
    ensures wiring_view_is_prefix(steps[at].after, steps[end].after),
    decreases end - at,
{
    reveal(mixed_trace);
    if at < end {
        mixed_trace_preserves_prefix(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring, at, end - 1);
        let early = steps[at].after;
        let last = steps[end];
        assert(last.before == steps[end - 1].after);
        wiring_step_keeps_prefix(body, layouts, forms, bindings, limit, last);
        assert(last.after.gates.take(early.gates.len() as int) =~= early.gates);
        assert(last.after.origins.take(early.origins.len() as int) =~= early.origins);
        assert(last.after.definitions.take(early.definitions.len() as int) =~= early.definitions);
    } else {
        assert(steps[end].after.gates.take(steps[end].after.gates.len() as int) =~= steps[end].after.gates);
        assert(steps[end].after.origins.take(steps[end].after.origins.len() as int) =~= steps[end].after.origins);
        assert(steps[end].after.definitions.take(steps[end].after.definitions.len() as int) =~= steps[end].after.definitions);
    }
}

/// 指定した変換の前後にある配線が、最終配線の接頭辞であることを示す。
proof fn mixed_trace_step_prefix(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, limit: usize,
    steps: Seq<WiringStep>, slot: usize, group: usize, final_wiring: WiringView, at: int,
)
    requires
        mixed_trace(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring),
        0 <= at < steps.len(),
    ensures
        wiring_view_is_prefix(steps[at].before, final_wiring),
        wiring_view_is_prefix(steps[at].after, final_wiring),
        steps[at].from <= body.definitions@.len(),
        steps[at].before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), steps[at].from as nat),
{
    mixed_trace_preserves_prefix(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring,
        at, steps.len() as int - 1);
    reveal(mixed_trace);
    reveal(wiring_step_valid);
    let step = steps[at];
    wiring_step_keeps_prefix(body, layouts, forms, bindings, limit, step);
    assert(final_wiring.gates.take(step.before.gates.len() as int) =~= step.before.gates);
    assert(final_wiring.origins.take(step.before.origins.len() as int) =~= step.before.origins);
    assert(final_wiring.definitions.take(step.before.definitions.len() as int) =~= step.before.definitions);
}

/// 通常の定義を変換した箇所では、最終配線から読んだ値が型検査済みの右辺の値に一致する。
proof fn mixed_trace_local_value(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    limit: usize, layout_limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize,
    final_wiring: WiringView, at: int, inputs: Seq<bool>, gates: Seq<bool>,
)
    requires
        mixed_trace(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring),
        0 <= at < steps.len(),
        steps[at].group_before == steps[at].group_after,
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        forall|i: int| 0 <= i < body.definitions@.len() && !binding_covers(bindings, i) ==>
            bit_definition_matches(body.input_widths@, body.definitions@.take(i), #[trigger] body.definitions@[i]),
        inputs.len() == layouts.inputs.total_bits_model(),
        gate_values_match(inputs, final_wiring.gates, gates),
        gates.len() == final_wiring.gates.len(),
        wires_available(final_wiring.definitions, layouts.inputs.total_bits_model(), gates.len()),
    ensures ({
        let i = steps[at].from as int;
        let definitions = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, gates);
        &&& 0 <= i < body.definitions@.len()
        &&& definitions[i].len() == body.definitions@[i].width
        &&& definitions[i] == checked_definition_values(body.definitions@[i], port_values(&layouts.inputs, inputs),
            definitions.take(i))
    }),
{
    mixed_trace_step_prefix(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring, at);
    reveal(mixed_trace);
    reveal(wiring_step_valid);
    let step = steps[at];
    let i = step.from as int;
    slot_wiring_is_preserved(body.definitions@[i], layouts, i, step.after.definitions, final_wiring.definitions,
        step.after.gates, final_wiring.gates, step.after.origins, final_wiring.origins);
    slot_values_match_wiring(body.input_widths@, body.definitions@, layouts, final_wiring, layout_limit,
        step.from, inputs, gates);
}

/// 変換に成功した関数で、通常の定義の値を最終配線から求める。
pub(super) proof fn mixed_function_local_value(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    widths: Seq<u64>, drivers: Seq<OutputDriver>, layout_limit: usize, gate_limit: usize,
    function: &LoweredBitFunc, steps: Ghost<Seq<WiringStep>>, i: int, inputs: Seq<bool>, gates: Seq<bool>,
)
    requires
        mixed_function_result(body, layouts, forms, bindings, widths, drivers, gate_limit, Ok((*function, steps))),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        0 <= i < body.definitions@.len(),
        !binding_covers(bindings, i),
        forall|j: int| 0 <= j < body.definitions@.len() && !binding_covers(bindings, j) ==>
            bit_definition_matches(body.input_widths@, body.definitions@.take(j), #[trigger] body.definitions@[j]),
        inputs.len() == layouts.inputs.total_bits_model(),
        gate_values_match(inputs, function.netlist.gates@, gates),
        gates.len() == function.netlist.gates@.len(),
    ensures ({
        let definitions = definition_values_from_wires(&layouts.definitions, function.definition_wires@, inputs, gates);
        &&& definitions[i].len() == body.definitions@[i].width
        &&& definitions[i] == checked_definition_values(body.definitions@[i], port_values(&layouts.inputs, inputs),
            definitions.take(i))
    }),
{
    let wiring = WiringView { definitions: function.definition_wires@,
        gates: function.netlist.gates@, origins: function.gate_definitions@ };
    let end = steps@.len() as int - 1;
    vstd::slice::axiom_spec_len(body.definitions);
    let slot = body.definitions@.len() as usize;
    let group = bindings.len() as usize;
    assert(0 <= end && steps@[end].to == slot) by { reveal(mixed_trace); };
    let at = mixed_trace_definition_step(body, layouts, forms, bindings, gate_limit, steps@, slot, group, wiring, end, i);
    assert(steps@[at].from == i && steps@[at].group_before == steps@[at].group_after) by {
        reveal(wiring_step_valid);
        reveal(binding_covers);
        let step = steps@[at];
        if step.group_before != step.group_after {
            assert(bindings[step.group_before as int].group.outputs.start <= i
                < bindings[step.group_before as int].group.outputs.end);
            assert(binding_covers(bindings, i));
        }
    };
    mixed_trace_local_value(body, layouts, forms, bindings, gate_limit, layout_limit, steps@, slot, group,
        wiring, at, inputs, gates);
}

/// 評価済みの最終配線から、指定した呼び出しの入力と出力を得る。
proof fn mixed_trace_call_values(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, limit: usize,
    layout_limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, final_wiring: WiringView, at: int,
    inputs: Seq<bool>, values: Seq<bool>,
) -> (result: (Seq<bool>, Seq<bool>))
    requires
        mixed_trace(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring),
        0 <= at < steps.len(),
        steps[at].group_before != steps[at].group_after,
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        gate_values_match(inputs, final_wiring.gates, values),
        values.len() == final_wiring.gates.len() <= usize::MAX,
        inputs.len() == layouts.inputs.total_bits_model(),
    ensures ({
        let step = steps[at];
        let binding = bindings[step.group_before as int];

        &&& nor_evaluation(binding.callee.netlist_model(), result.0, result.1)
        &&& exists|invocation: CallerArguments, mapped: Seq<Wire>, wires: Seq<Wire>|
            #[trigger] call_group_wires_match(binding.group, forms, binding.arguments@, layouts,
                binding.callee, step.before, step.after, binding._output_widths@, invocation, mapped, wires)
            && result.0 == instance_wire_values(mapped, inputs, values)
            && result.1 == instance_wire_values(wires, inputs, values)
        &&& forall|port: int, bit: int| 0 <= port < binding._output_widths@.len() && 0 <= bit < binding._output_widths@[port] ==>
            #[trigger] call_output_bit_has_value(layouts, binding.callee, final_wiring.definitions, step.from, port, bit,
                inputs, values, result.1)
    }),
{
    mixed_trace_step_prefix(body, layouts, forms, bindings, limit, steps, slot, group, final_wiring, at);
    let step = steps[at];
    assert(wiring_step_valid(body, layouts, forms, bindings, limit, step)) by { reveal(mixed_trace); };
    reveal(wiring_step_valid);
    reveal(binding_ready);
    let binding = bindings[step.group_before as int];
    let result = call_group_values(binding.group, forms, binding.arguments@, layouts, binding.callee,
        step.before, step.after, limit, definition_widths(body.definitions@), binding._output_widths@,
        layout_limit, binding._layout_limit@, final_wiring.gates, inputs, values);
    assert forall|port: int, bit: int| 0 <= port < binding._output_widths@.len() && 0 <= bit < binding._output_widths@[port]
        implies #[trigger] call_output_bit_has_value(layouts, binding.callee, final_wiring.definitions, step.from, port, bit,
            inputs, values, result.1) by {
        assert(call_output_bit_has_value(layouts, binding.callee, step.after.definitions, step.from, port, bit,
            inputs, values, result.1));
    };
    result
}

proof fn extend_mixed_trace(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, limit: usize,
    steps: Seq<WiringStep>, step: WiringStep,
)
    requires
        mixed_trace(body, layouts, forms, bindings, limit, steps, step.from, step.group_before, step.before),
        wiring_step_valid(body, layouts, forms, bindings, limit, step),
    ensures mixed_trace(body, layouts, forms, bindings, limit, steps.push(step), step.to, step.group_after, step.after),
{
    reveal(mixed_trace);
    let next = steps.push(step);
    assert forall|i: int| 0 <= i < next.len() implies {
        let current = #[trigger] next[i];
        &&& wiring_step_valid(body, layouts, forms, bindings, limit, current)
        &&& if i == 0 { current.from == 0 && current.group_before == 0 && wiring_empty(current.before) }
            else {
                let prior = next[i - 1];
                prior.to == current.from && prior.group_after == current.group_before && prior.after == current.before
            }
    } by {
        if i < steps.len() { assert(next[i] == steps[i]); }
        if i > 0 { assert(next[i - 1] == steps[i - 1]); }
    };
}

pub(super) closed spec fn mixed_error_at(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    limit: usize, before: WiringView, slot: usize, group: usize, error: MixedWiringError,
) -> bool {
    &&& slot < body.definitions@.len()
    &&& binding_cursor(bindings, slot, group as int)
    &&& match error {
        MixedWiringError::LocalGateCapacity(site) =>
            !binding_covers(bindings, slot as int) && body.definitions@[slot as int].rhs is Nor
                && site == body.definitions@[slot as int].expression && before.gates.len() == limit,
        MixedWiringError::Call(error) =>
            group < bindings.len() && bindings[group as int].group.outputs.start == slot
            && {
                let binding = bindings[group as int];
                call_group_result(binding.group, forms, binding.arguments@, layouts, binding.callee, before, before,
                    limit, definition_widths(body.definitions@), binding._output_widths@, Err(error))
            },
    }
}

/// 通常の定義は一件ずつ、呼び出しは出力区間ごとに配線を追加する。
///
/// # Errors
///
/// 定義順で最初に失敗した右辺または実引数の範囲を返す。
#[verifier::rlimit(24)]
pub(super) fn lower_mixed_body<'s, 'p, 'a>(
    body: &LoweringBody<'s, 'p, 'a>, layouts: &Layouts, forms: &[Form], bindings: &[CallBinding<'s, 'p, 'a>],
    layout_limit: usize, gate_limit: usize,
) -> (result: Result<(BodyWiring, Ghost<Seq<WiringStep>>), MixedWiringError<'p, 'a>>)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        ordered_bindings(bindings@),
        forall|g: int| 0 <= g < bindings@.len() ==> binding_ready(
            #[trigger] bindings@[g], layouts, forms@, definition_widths(body.definitions@)),
        forall|slot: int| 0 <= slot < body.definitions@.len() && !binding_covers(bindings@, slot) ==>
            bit_definition_matches(body.input_widths@, body.definitions@.take(slot), #[trigger] body.definitions@[slot]),
    ensures match result {
        Ok((state, steps)) => {
            &&& mixed_trace(body, layouts, forms@, bindings@, gate_limit, steps@, body.definitions@.len() as usize,
                bindings@.len() as usize, state.model())
            &&& state.definitions@.len() == layouts.definitions.total_bits_model()
            &&& state.gates@.len() == state.origins@.len() <= gate_limit
            &&& gates_available(state.gates@, layouts.inputs.total_bits_model() as nat, state.gates@.len() as int)
            &&& wires_available(state.definitions@, layouts.inputs.total_bits_model(), state.gates@.len())
        },
        Err(error) => exists|steps: Seq<WiringStep>, slot: usize, group: usize, wiring: WiringView|
            #[trigger] mixed_trace(body, layouts, forms@, bindings@, gate_limit, steps, slot, group, wiring)
            && mixed_error_at(body, layouts, forms@, bindings@, gate_limit, wiring, slot, group, error),
    },
{
    let mut state = BodyWiring { definitions: Vec::new(), gates: Vec::new(), origins: Vec::new() };
    let ghost mut steps = Seq::<WiringStep>::empty();
    let mut slot = 0usize;
    let mut group = 0usize;
    let ghost widths = definition_widths(body.definitions@);
    let ghost input_count = layouts.inputs.total_bits_model();
    proof {
        reveal(mixed_trace);
        reveal(wires_available);
        reveal(preceding_port_bits);
        body_inputs_end_within_layout(body, layout_limit, layouts);
        assert forall|g: int| 0 <= g < bindings@.len() implies {
            let binding = #[trigger] bindings@[g];
            &&& binding.group.outputs.start < binding.group.outputs.end <= body.definitions@.len()
        } by { reveal(binding_ready); };
    }
    while slot < body.definitions.len()
        invariant
            body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
            widths == definition_widths(body.definitions@),
            input_count == layouts.inputs.total_bits_model(),
            forall|i: int| 0 <= i < layouts.inputs.ranges_model().len() ==>
                (#[trigger] layouts.inputs.ranges_model()[i]).end <= input_count,
            ordered_bindings(bindings@), binding_cursor(bindings@, slot, group as int),
            forall|g: int| 0 <= g < bindings@.len() ==>
                (#[trigger] bindings@[g]).group.outputs.start < bindings@[g].group.outputs.end <= body.definitions@.len(),
            forall|g: int| 0 <= g < bindings@.len() ==> binding_ready(#[trigger] bindings@[g], layouts, forms@, widths),
            forall|i: int| 0 <= i < body.definitions@.len() && !binding_covers(bindings@, i) ==>
                bit_definition_matches(body.input_widths@, body.definitions@.take(i), #[trigger] body.definitions@[i]),
            slot <= body.definitions@.len(),
            state.definitions@.len() == preceding_port_bits(widths, slot as nat),
            state.gates@.len() == state.origins@.len() <= gate_limit,
            gates_available(state.gates@, input_count as nat, state.gates@.len() as int),
            wires_available(state.definitions@, input_count, state.gates@.len()),
            mixed_trace(body, layouts, forms@, bindings@, gate_limit, steps, slot, group, state.model()),
        decreases body.definitions@.len() - slot,
    {
        let ghost before = state.model();
        let ghost start = slot;
        let ghost cursor = group;
        if group < bindings.len() && bindings[group].group.outputs.start == slot {
            let binding = &bindings[group];
            proof { reveal(binding_ready); }
            match lower_call_group(binding.group, forms, binding.arguments, layouts, binding.callee, &mut state, gate_limit,
                Ghost(widths), Ghost(binding._input_widths@), Ghost(binding._output_widths@),
                Ghost(layout_limit), Ghost(binding._layout_limit@)) {
                Err(error) => {
                    let result = MixedWiringError::Call(error);
                    assert(mixed_error_at(body, layouts, forms@, bindings@, gate_limit, before, slot, group, result));
                    return Err(result);
                },
                Ok(()) => {},
            }
            let end = binding.group.outputs.end;
            proof { advance_binding_cursor(bindings@, slot, group, end, true); }
            slot = end;
            group += 1;
        } else {
            proof { advance_binding_cursor(bindings@, slot, group, (slot + 1) as usize, false); }
            match lower_definition(body, layouts, layout_limit, gate_limit, slot,
                &mut state.definitions, &mut state.gates, &mut state.origins) {
                Err(site) => {
                    let result = MixedWiringError::LocalGateCapacity(site);
                    assert(mixed_error_at(body, layouts, forms@, bindings@, gate_limit, before, slot, group, result));
                    return Err(result);
                },
                Ok(()) => {},
            }
            slot += 1;
        }
        proof {
            let step = WiringStep { from: start, to: slot, group_before: cursor, group_after: group, before, after: state.model() };
            assert(wiring_step_valid(body, layouts, forms@, bindings@, gate_limit, step)) by { reveal(wiring_step_valid); };
            extend_mixed_trace(body, layouts, forms@, bindings@, gate_limit, steps, step);
            steps = steps.push(step);
        }
    }
    proof {
        if group < bindings@.len() {
            assert(slot <= bindings@[group as int].group.outputs.start);
            assert(false);
        }
        port_bit_layout_size(widths, layout_limit, &layouts.definitions);
    }
    Ok((state, Ghost(steps)))
}

pub(super) open spec fn mixed_function_result(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    output_widths: Seq<u64>, output_drivers: Seq<OutputDriver>, gate_limit: usize,
    result: Result<(LoweredBitFunc, Ghost<Seq<WiringStep>>), MixedWiringError>,
) -> bool {
    match result {
        Ok((value, steps)) => {
            &&& value.layouts == *layouts
            &&& bindings.len() <= usize::MAX
            &&& value.netlist.input_count == layouts.inputs.total_bits_model()
            &&& value.netlist.outputs@.len() == layouts.outputs.total_bits_model()
            &&& value.definition_wires@.len() == layouts.definitions.total_bits_model()
            &&& wires_available(value.definition_wires@, layouts.inputs.total_bits_model(), value.netlist.gates@.len())
            &&& value.netlist.gates@.len() == value.gate_definitions@.len() <= gate_limit
            &&& nor_evaluation_ready(&value.netlist, layouts.inputs.total_bits_model() as nat)
            &&& body_output_wiring_matches(output_drivers, layouts, value.definition_wires@, value.netlist.outputs@,
                output_widths.len() as int)
            &&& mixed_trace(body, layouts, forms, bindings, gate_limit, steps@, body.definitions@.len() as usize,
                bindings.len() as usize, WiringView { definitions: value.definition_wires@,
                    gates: value.netlist.gates@, origins: value.gate_definitions@ })
        },
        Err(error) => exists|steps: Seq<WiringStep>, slot: usize, group: usize, wiring: WiringView|
            #[trigger] mixed_trace(body, layouts, forms, bindings, gate_limit, steps, slot, group, wiring)
            && mixed_error_at(body, layouts, forms, bindings, gate_limit, wiring, slot, group, error),
    }
}

/// 変換済みの定義から宣言順に出力を結線し、評価できるネットリストを返す。
///
/// # Errors
///
/// 本体の配線変換で最初に見つかった診断を返す。
pub(super) fn lower_mixed_function<'s, 'p, 'a>(
    body: &LoweringBody<'s, 'p, 'a>, layouts: Layouts, forms: &[Form], bindings: &[CallBinding<'s, 'p, 'a>],
    output_widths: &[u64], output_drivers: &[OutputDriver],
    layout_limit: usize, gate_limit: usize,
) -> (result: Result<(LoweredBitFunc, Ghost<Seq<WiringStep>>), MixedWiringError<'p, 'a>>)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, &layouts),
        widths_layout(output_widths@, layout_limit, &layouts.outputs),
        output_widths@.len() == output_drivers@.len(),
        forall|p: int| 0 <= p < output_widths@.len() ==>
            bit_driver_width(body.input_widths@, body.definitions@, #[trigger] output_drivers@[p]) == Some(output_widths@[p]),
        ordered_bindings(bindings@),
        forall|g: int| 0 <= g < bindings@.len() ==> binding_ready(
            #[trigger] bindings@[g], &layouts, forms@, definition_widths(body.definitions@)),
        forall|slot: int| 0 <= slot < body.definitions@.len() && !binding_covers(bindings@, slot) ==>
            bit_definition_matches(body.input_widths@, body.definitions@.take(slot), #[trigger] body.definitions@[slot]),
    ensures mixed_function_result(body, &layouts, forms@, bindings@, output_widths@, output_drivers@, gate_limit, result),
{
    proof { vstd::slice::axiom_spec_len(bindings); }
    let (state, Ghost(steps)) = match lower_mixed_body(body, &layouts, forms, bindings, layout_limit, gate_limit) {
        Ok(lowered) => lowered,
        Err(error) => return Err(error),
    };
    proof {
        port_bit_layout_size(definition_widths(body.definitions@), layout_limit, &layouts.definitions);
    }
    let outputs = lower_body_outputs(body, output_widths, output_drivers, &layouts, layout_limit,
        state.definitions.as_slice(), state.gates.len());
    let input_count = layouts.inputs.total_bits();
    let netlist = NorNetlist { input_count, outputs, gates: state.gates };
    assert(nor_evaluation_ready(&netlist, input_count as nat));
    let lowered = LoweredBitFunc { netlist, layouts, definition_wires: state.definitions, gate_definitions: state.origins };
    Ok((lowered, Ghost(steps)))
}
pub(super) open spec fn bindings_match_calls(
    bindings: Seq<CallBinding>, selected: Seq<ResolvedTemplateCall>,
) -> bool {
    &&& bindings.len() == selected.len()
    &&& forall|i: int| 0 <= i < bindings.len() ==> binding_matches_selection(#[trigger] bindings[i], selected[i])
}

/// 呼び出しを借用する前後で、各定義が属する呼び出しとその順序が等しいことを示す。
pub(super) proof fn bindings_preserve_definition_order(
    bindings: Seq<CallBinding>, calls: Seq<CheckedExpansionCall>,
)
    requires
        bindings.len() == calls.len(),
        forall|i: int| 0 <= i < bindings.len() ==> *(#[trigger] bindings[i]).group == calls[i],
        forall|a: int, b: int| 0 <= a < b < calls.len() ==>
            (#[trigger] calls[a]).outputs.end <= (#[trigger] calls[b]).outputs.start,
    ensures
        ordered_bindings(bindings),
        forall|slot: int| #[trigger] binding_covers(bindings, slot) <==> call_covers(calls, slot),
{
    assert forall|a: int, b: int| 0 <= a < b < bindings.len() implies
        (#[trigger] bindings[a]).group.outputs.end <= (#[trigger] bindings[b]).group.outputs.start by {
        assert(calls[a].outputs.end <= calls[b].outputs.start);
    };
    assert forall|slot: int| #[trigger] binding_covers(bindings, slot) <==> call_covers(calls, slot) by {
        if binding_covers(bindings, slot) {
            let g = choose|g: int| 0 <= g < bindings.len()
                && (#[trigger] bindings[g]).group.outputs.start <= slot < bindings[g].group.outputs.end;
            assert(calls[g].outputs.start <= slot < calls[g].outputs.end);
        }
        if call_covers(calls, slot) {
            let g = choose|g: int| 0 <= g < calls.len()
                && (#[trigger] calls[g]).outputs.start <= slot < calls[g].outputs.end;
            assert(bindings[g].group.outputs.start <= slot < bindings[g].group.outputs.end);
        }
    };
}

/// 解決済みの呼び出しと通常の定義を合わせ、同じ定義順で配線へ変換する。
///
/// # Errors
///
/// 最初に配線へ変換できなかった定義または呼び出しの診断を返す。
pub(super) fn lower_resolved_function<'s, 'p, 'a>(
    aliases: &UseAliases<'_, 'p, 'a>, body: &LoweringBody<'s, 'p, 'a>, layouts: Layouts, forms: &[Form],
    selected: &[ResolvedTemplateCall<'s, 'p, 'a>], output_widths: &[u64], output_drivers: &[OutputDriver],
    layout_limit: usize, gate_limit: usize,
    Ghost(context): Ghost<(&FunctionExpansionOrder<'p, 'a>, (usize, usize, u64), &PreparedExpansionBody<'p, 'a>)>,
) -> (result: Result<(LoweredBitFunc, Ghost<Seq<WiringStep>>), MixedWiringError<'p, 'a>>)
    requires
        aliases.prepared_expansion_body_matches(*context.0, context.1.0, context.1.1, context.1.2, context.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, &layouts),
        widths_layout(output_widths@, layout_limit, &layouts.outputs),
        output_widths@.len() == output_drivers@.len(),
        forall|p: int| 0 <= p < output_widths@.len() ==>
            bit_driver_width(body.input_widths@, body.definitions@, #[trigger] output_drivers@[p]) == Some(output_widths@[p]),
        selected@.len() == context.2.calls@.len(),
        forall|g: int| 0 <= g < selected@.len() ==> {
            let call = #[trigger] selected@[g];
            &&& aliases.resolved_template_call_matches(context.0, context.1, context.2, g, call)
            &&& resolved_call_fits_body(call, body.input_widths@, body.definitions@, forms@, context.1.2)
        },
        forall|slot: int| 0 <= slot < body.definitions@.len() && !call_covers(context.2.calls@, slot) ==>
            bit_definition_matches(body.input_widths@, body.definitions@.take(slot), #[trigger] body.definitions@[slot]),
    ensures exists|bindings: Seq<CallBinding>|
        #[trigger] bindings_match_calls(bindings, selected@)
            && mixed_function_result(body, &layouts, forms@, bindings, output_widths@, output_drivers@, gate_limit, result),
{
    let bindings = bind_resolved_calls(aliases, selected, body, &layouts, Ghost(forms@), Ghost(layout_limit), Ghost(context));
    proof {
        assert(bindings_match_calls(bindings@, selected@));
        assert forall|i: int| 0 <= i < bindings@.len() implies
            *(#[trigger] bindings@[i]).group == context.2.calls@[i] by {
            assert(bindings@[i].group == selected@[i].group);
        };
        bindings_preserve_definition_order(bindings@, context.2.calls@);
        assert forall|slot: int| 0 <= slot < body.definitions@.len() && !binding_covers(bindings@, slot) implies
            bit_definition_matches(body.input_widths@, body.definitions@.take(slot), #[trigger] body.definitions@[slot]) by {
            assert(!call_covers(context.2.calls@, slot));
        };
    }
    let result = lower_mixed_function(body, layouts, forms, bindings.as_slice(),
        output_widths, output_drivers, layout_limit, gate_limit);
    assert(exists|rows: Seq<CallBinding>| #[trigger] bindings_match_calls(rows, selected@)
        && mixed_function_result(body, &layouts, forms@, rows, output_widths@, output_drivers@, gate_limit, result)) by {
        assert(bindings_match_calls(bindings@, selected@));
    };
    result
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn mixed_body_passes_outputs_through_successive_calls() {
    use alloc::vec;
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};
    use crate::project::circuits::form_location;
    use crate::project::FuncWiringResult;

    let project = parse_circuit_project(&[SourceSnapshot {
        path: "mixed.ncg2",
        revision: 1,
        text: "(using nor)
               (func caller (in (a (bits 4)) b) (out y)
                   (def (word bit) (pair a b))
                   (def (again final) (pair word bit))
                   (def y (nor final final)))
               (func pair (in (a (bits 4)) b) (out (a (bits 4)) inverted)
                   (def inverted (nor b b)))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, 0, 1, 8).unwrap();
    let group = &prepared.calls[0];
    let following = &prepared.calls[1];
    let source = &project.sources()[0];
    let parsed = &project.circuits()[0];
    let forms = parsed.syntax.forms.as_slice();
    let mut templates = aliases.new_function_templates(&plan, Ghost(8u64));
    let position = plan.get(templates.next_index()).unwrap();
    assert_eq!(position, (0, 2));
    assert_ne!(plan.template_at(templates.next_index()), Some(templates.next_index()));
    let checked = aliases.check_bit_func(position.0, position.1, 8).unwrap();
    let circuit = checked.lower_bit_func(8).unwrap();
    let callee = aliases.standalone_function_template(position, 8, checked, circuit, 8);
    aliases.insert_function_template(&plan, &mut templates, callee, Ghost(8u64));
    let selected = aliases.resolve_template_calls(&plan, &templates, prepared.calls.as_slice(),
        prepared.projections.call_arguments.arguments.as_slice(), Ghost(prepared), Ghost((0usize, 1usize, 8u64)));

    let bit = SingleBitOperand::Driver(OutputDriver::Definition(3));
    let slots = vec![
        CheckedBitDefinition { expression: copy_location(&group.expression), width: 4,
            rhs: BitFuncRhs::CallOutput { group: 0, port: 0 }, operands: Vec::new() },
        CheckedBitDefinition { expression: copy_location(&group.expression), width: 1,
            rhs: BitFuncRhs::CallOutput { group: 0, port: 1 }, operands: Vec::new() },
        CheckedBitDefinition { expression: copy_location(&following.expression), width: 4,
            rhs: BitFuncRhs::CallOutput { group: 1, port: 0 }, operands: Vec::new() },
        CheckedBitDefinition { expression: copy_location(&following.expression), width: 1,
            rhs: BitFuncRhs::CallOutput { group: 1, port: 1 }, operands: Vec::new() },
        CheckedBitDefinition { expression: form_location(source, forms, parsed.definitions[2].expression.start), width: 1,
            rhs: BitFuncRhs::Nor { left: bit, right: bit }, operands: Vec::new() },
    ];
    let FuncWiringResult::Checked(wiring) = &prepared.typed.literals.wiring else {
        panic!("expected checked caller wiring");
    };
    let ports = aliases.prepare_routine_ports(0, 1, 8, wiring, prepared.projections.layouts).unwrap();
    let body = LoweringBody { input_widths: ports.inputs.as_slice(), definitions: slots.as_slice() };
    let output_widths = ports.outputs.as_slice();
    let output_drivers = wiring.drivers.outputs.as_slice();
    let limited = prepare_body_layouts(body.input_widths, body.definitions, output_widths, 16).unwrap();
    let Err(MixedWiringError::LocalGateCapacity(site)) = lower_resolved_function(
        &aliases, &body, limited, forms, selected.as_slice(), output_widths, output_drivers, 16, 2,
        Ghost((&plan, (0usize, 1usize, 8u64), &prepared)),
    ) else {
        panic!("expected the caller NOR to exceed the gate limit");
    };
    assert_eq!(&source.text[site.span], "(nor final final)");

    let layout = prepare_body_layouts(body.input_widths, body.definitions, output_widths, 16).unwrap();
    let (lowered, _) = lower_resolved_function(
        &aliases, &body, layout, forms, selected.as_slice(), output_widths, output_drivers, 16, 3,
        Ghost((&plan, (0usize, 1usize, 8u64), &prepared)),
    ).unwrap();
    assert_eq!(lowered.gate_definitions(), [0, 2, 4]);
    assert_eq!(lowered.netlist().evaluate(&[true, false, true, false, true]).unwrap(), [false]);
    assert_eq!(lowered.netlist().evaluate(&[true, false, true, false, false]).unwrap(), [true]);
}

} // verus!
