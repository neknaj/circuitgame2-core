//! 通常の定義と関数呼び出しを、同じ配線列へ定義順に変換する。

#[cfg(verus_only)]
mod source_arguments;
#[cfg(verus_only)]
pub(super) use source_arguments::mixed_function_call_evaluation;
#[cfg(verus_only)]
pub(in crate::project::use_aliases::bit_func) use source_arguments::{
    EvaluatedCallBits, EvaluatedNestedCall, MixedCallEvaluation, evaluated_flat_call_matches, evaluated_nested_call_matches,
    evaluated_expression_child_matches, evaluated_nor_call_matches, evaluated_nor_root_port_matches,
    nor_children_have_single_output,
};

use super::super::expansion::{ExpansionSlot, expansion_call_at_slot};
use super::*;
#[cfg(verus_only)]
use super::evaluation::{definition_values_from_wires, slot_values_match_wiring};
#[cfg(verus_only)]
use super::super::semantics::checked_definition_values;
use super::super::expansion::{CheckedExpansionCall, PreparedExpansionBody};
#[cfg(verus_only)]
use super::super::expansion::{expansion_arguments_determined, expansion_child_reachable, expansion_parent_range};
use super::super::templates::{FunctionTemplates, NorBinding, ResolvedTemplateCall};
use crate::project::{FunctionExpansionOrder, UseAliases};
#[cfg(verus_only)]
use super::super::frontend::{
    argument_matches_width, call_covers, expression_argument_matches_width, nor_binding_covers, nor_binding_fits_body,
    root_argument_matches_width,
};
use super::super::super::call_arity::{CallArgumentSource, ProjectedCallArgument};
use super::call_group::{BodyWiring, CallGroupError, lower_call_group, lower_nested_call_group, lower_nor_call_group};
use super::call_arguments::{CallWiringError, ChildCallWiringError, builtin_nor_call};
use super::call_arguments::child_calls::NestedCallWiringError;
#[cfg(verus_only)]
use super::call_arguments::child_calls::{ChildCall, NestedRootEvaluation};
use crate::syntax::Form;
#[cfg(verus_only)]
use super::call_group::{
    WiringView, call_group_result, call_group_values, call_group_wires_match, call_output_bit_has_value, wiring_view_is_prefix,
    nested_call_group_frame, nested_call_group_result, nor_call_group_evaluation_matches, nor_call_group_frame,
    nor_call_group_result, nor_call_group_values,
};
#[cfg(verus_only)]
use super::super::instances::{instance_gates_match, instance_wire_values};
#[cfg(verus_only)]
use crate::netlist::{gate_values_match, nor_evaluation};
#[cfg(verus_only)]
use super::call_arguments::{CallerArguments, layout_argument_from_width, layout_argument_ready};
#[cfg(verus_only)]
use super::call_arguments::builtin_nor_call_matches;
#[cfg(verus_only)]
use crate::syntax::form_spans_valid;

verus! {

/// 先行する関数のネットリストと、呼び出し元の実引数。
pub(super) struct CallBinding<'s, 'p, 'a> {
    pub(super) group: &'s CheckedExpansionCall<'p, 'a>,
    pub(super) arguments: &'s [ProjectedCallArgument],
    pub(super) callee: &'s LoweredBitFunc,
    /// 配線履歴を元の選択に戻すため、子を含む呼び出し全体を証明で保持する。
    pub(super) _selection: Ghost<ResolvedTemplateCall<'s, 'p, 'a>>,
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
    /// 子の出力を保持する一時配線表の容量を超えた。
    CallOutputCapacity { site: LocatedName<'p, 'a>, used: usize, width: usize, capacity: usize },
}

/// 子を含む呼び出しを、同じ本体の配線ループで処理するための入力。
#[derive(Clone, Copy)]
struct NestedWiring<'s, 'p, 'a> {
    selected: &'s [ResolvedTemplateCall<'s, 'p, 'a>],
    builtin: &'s (NorNetlist, PortBitLayout),
    child_limit: usize,
    _arguments: Ghost<Seq<ProjectedCallArgument>>,
}

/// 定義順の配線で失敗した箇所と、その処理が返した診断。
enum MixedBodyError<'p, 'a> {
    Flat(MixedWiringError<'p, 'a>),
    Nested(LocatedName<'p, 'a>, NestedCallWiringError<'p, 'a>),
    /// 根 NOR の式範囲と、子または根の診断。
    Nor(LocatedName<'p, 'a>, NestedCallWiringError<'p, 'a>),
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
    nor_before: usize,
    #[cfg(verus_only)]
    nor_after: usize,
    #[cfg(verus_only)]
    before: WiringView,
    #[cfg(verus_only)]
    after: WiringView,
    #[cfg(verus_only)]
    nested: Option<NestedCallStep>,
}

/// 入れ子の配線結果を照合するための基底回路、一時配線の上限、型検査済みの引数列。
#[cfg(verus_only)]
struct NestedCallStep {
    builtin: (NorNetlist, PortBitLayout),
    child_limit: usize,
    arguments: Seq<ProjectedCallArgument>,
}

pub(super) closed spec fn flat_wiring_trace(steps: Seq<WiringStep>) -> bool {
    forall|i: int| 0 <= i < steps.len() ==> (#[trigger] steps[i]).nested.is_none()
}

/// 入れ子を展開した段が、呼び出し元の平坦な実引数列に対応することを表す。
pub(super) closed spec fn wiring_trace_arguments_match(steps: Seq<WiringStep>, arguments: Seq<ProjectedCallArgument>) -> bool {
    forall|i: int| 0 <= i < steps.len() ==> ((#[trigger] steps[i]).nested matches Some(nested)
        ==> nested.arguments == arguments)
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
    layout_argument_from_width(body, layouts, capacity, binding.group.outputs.start,
        binding.group.expression.source, forms, binding.arguments@[port], inputs[port], width_limit);
}

pub(in crate::project::use_aliases::bit_func) open spec fn resolved_call_fits_body(
    call: ResolvedTemplateCall, inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>, forms: Seq<Form>, limit: u64,
) -> bool {
    let first = call.group.outputs.start;
    let end = call.group.outputs.end;
    let outputs = call.template.output_widths_model();
    &&& form_spans_valid(call.group.expression.source.text, forms, call.group.expression.source.text.spec_bytes().len() as int)
    &&& first < end <= definitions.len()
    &&& first + outputs.len() == end
    &&& forall|i: int| 0 <= i < outputs.len() ==> definitions[first + i].width == #[trigger] outputs[i]
    &&& forall|port: int| 0 <= port < call.arguments@.len() ==>
        #[trigger] root_argument_matches_width(call.group.expression.source, forms, inputs, definitions, call, port, limit)
    &&& forall|child: int, port: int| 0 <= child < call.children@.len()
        && 0 <= port < call.children@[child].arguments@.len() ==>
        #[trigger] expression_argument_matches_width(call.group.expression.source, forms, inputs, definitions,
            call, child, port, limit)
}

pub(super) open spec fn binding_matches_selection(binding: CallBinding, call: ResolvedTemplateCall) -> bool {
    &&& binding._selection@ == call
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
        _selection: Ghost(*selected),
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
            assert(root_argument_matches_width(selected.group.expression.source, forms, _body.input_widths@,
                _body.definitions@, *selected, i, width_limit));
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

spec fn nor_cursor(roots: Seq<NorBinding>, slot: usize, cursor: int) -> bool {
    &&& 0 <= cursor <= roots.len()
    &&& forall|i: int| 0 <= i < cursor ==> (#[trigger] roots[i]).selected.prepared.output_slot < slot
    &&& forall|i: int| cursor <= i < roots.len() ==> slot <= (#[trigger] roots[i]).selected.prepared.output_slot
}

spec fn no_nor_in_range(roots: Seq<NorBinding>, start: usize, end: usize) -> bool {
    forall|i: int| 0 <= i < roots.len() ==> {
        let slot = (#[trigger] roots[i]).selected.prepared.output_slot;
        !(start <= slot < end)
    }
}

proof fn advance_nor_cursor(
    roots: Seq<NorBinding>, slot: usize, cursor: usize, end: usize, take_root: bool,
)
    requires
        nor_cursor(roots, slot, cursor as int), slot < end,
        take_root ==> cursor < roots.len() && roots[cursor as int].selected.prepared.output_slot == slot,
        forall|i: int| cursor + (if take_root { 1int } else { 0int }) <= i < roots.len() ==>
            end <= (#[trigger] roots[i]).selected.prepared.output_slot,
    ensures
        nor_cursor(roots, end, cursor + (if take_root { 1int } else { 0int })),
        !take_root ==> !nor_binding_covers(roots, slot as int),
        !take_root ==> no_nor_in_range(roots, slot, end),
{
    assert forall|i: int| 0 <= i < cursor + (if take_root { 1int } else { 0int }) implies
        (#[trigger] roots[i]).selected.prepared.output_slot < end by {
        if i == cursor { assert(take_root); }
    };
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
    &&& step.nor_before == step.nor_after
    &&& if step.group_before == step.group_after {
        step.nested.is_none() && !binding_covers(bindings, step.from as int) && local_step(body, layouts, step)
    } else {
        let group = step.group_before as int;
        let binding = bindings[group];
        &&& 0 <= group < bindings.len() && step.group_after == group + 1
        &&& step.from == binding.group.outputs.start && step.to == binding.group.outputs.end
        &&& binding_ready(binding, layouts, forms, widths)
        &&& match step.nested {
            None => call_group_result(binding.group, forms, binding.arguments@, layouts, binding.callee,
                step.before, step.after, limit, widths, binding._output_widths@, Ok(())),
            Some(nested) => {
                &&& binding_matches_selection(binding, binding._selection@)
                &&& builtin_nor_call_matches(&nested.builtin)
                &&& selected_children_reachable(&binding._selection@, nested.arguments)
                &&& nested_call_group_result(&binding._selection@, forms, layouts, &nested.builtin,
                    step.before, step.after, limit, nested.child_limit, widths, Ok(()))
            },
        }
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

#[verifier::opaque]
spec fn nor_wiring_step_valid(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, roots: Seq<NorBinding>,
    limit: usize, step: WiringStep,
) -> bool {
    let index = step.nor_before as int;
    let binding = roots[index];
    let widths = definition_widths(body.definitions@);
    &&& 0 <= index < roots.len() && step.nor_after == index + 1
    &&& step.group_before == step.group_after
    &&& step.from == binding.selected.prepared.output_slot
    &&& step.to == step.from + 1 <= body.definitions@.len()
    &&& step.before.definitions.len() == preceding_port_bits(widths, step.from as nat)
    &&& step.nested matches Some(nested)
    &&& nor_call_group_result(&binding.selected, *binding.references, forms, layouts, &nested.builtin,
        step.before, step.after, limit, nested.child_limit, widths, Ok(()))
}

/// 直前の配線状態と両カーソルを、次の定義の開始時に引き継ぐ。
#[verifier::opaque]
pub(super) closed spec fn rooted_mixed_trace(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, wiring: WiringView,
) -> bool {
    &&& if steps.len() == 0 { slot == 0 && group == 0 && nor == 0 && wiring_empty(wiring) }
        else {
            let last = steps.last();
            last.to == slot && last.group_after == group && last.nor_after == nor && last.after == wiring
        }
    &&& forall|i: int| 0 <= i < steps.len() ==> {
        let step = #[trigger] steps[i];
        &&& if step.nor_before != step.nor_after {
            !binding_covers(bindings, step.from as int)
            && nor_wiring_step_valid(body, layouts, forms, roots, limit, step)
        } else {
            no_nor_in_range(roots, step.from, step.to)
            && wiring_step_valid(body, layouts, forms, bindings, limit, step)
        }
        &&& if i == 0 { step.from == 0 && step.group_before == 0 && step.nor_before == 0 && wiring_empty(step.before) }
            else {
                let prior = steps[i - 1];
                prior.to == step.from && prior.group_after == step.group_before
                    && prior.nor_after == step.nor_before && prior.after == step.before
            }
    }
}

proof fn rooted_trace_without_roots(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, wiring: WiringView,
)
    requires roots.len() == 0, rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, wiring),
    ensures mixed_trace(body, layouts, forms, bindings, limit, steps, slot, group, wiring),
{
    reveal(rooted_mixed_trace);
    reveal(nor_wiring_step_valid);
    reveal(mixed_trace);
    assert forall|i: int| 0 <= i < steps.len() implies
        wiring_step_valid(body, layouts, forms, bindings, limit, #[trigger] steps[i]) by {
        assert(steps[i].nor_before == steps[i].nor_after);
    };
}

proof fn extend_rooted_trace(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    limit: usize, steps: Seq<WiringStep>, step: WiringStep,
)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, step.from, step.group_before, step.nor_before, step.before),
        if step.nor_before != step.nor_after {
            !binding_covers(bindings, step.from as int) && nor_wiring_step_valid(body, layouts, forms, roots, limit, step)
        } else {
            no_nor_in_range(roots, step.from, step.to) && wiring_step_valid(body, layouts, forms, bindings, limit, step)
        },
    ensures rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps.push(step),
        step.to, step.group_after, step.nor_after, step.after),
{
    reveal(rooted_mixed_trace);
    let next = steps.push(step);
    assert forall|i: int| 0 <= i < next.len() implies {
        let current = #[trigger] next[i];
        &&& if current.nor_before != current.nor_after {
            !binding_covers(bindings, current.from as int)
                && nor_wiring_step_valid(body, layouts, forms, roots, limit, current)
        } else {
            no_nor_in_range(roots, current.from, current.to)
                && wiring_step_valid(body, layouts, forms, bindings, limit, current)
        }
        &&& if i == 0 { current.from == 0 && current.group_before == 0 && current.nor_before == 0 && wiring_empty(current.before) }
            else {
                let prior = next[i - 1];
                prior.to == current.from && prior.group_after == current.group_before
                    && prior.nor_after == current.nor_before && prior.after == current.before
            }
    } by {
        if i < steps.len() { assert(next[i] == steps[i]); }
        if i > 0 { assert(next[i - 1] == steps[i - 1]); }
    };
}

proof fn trace_step_covering_slot(steps: Seq<WiringStep>, end: int, definition: int) -> (at: int)
    requires
        0 <= end < steps.len(),
        0 <= definition < steps[end].to,
        forall|i: int| 0 <= i <= end ==> {
            let current = #[trigger] steps[i];
            if i == 0 { current.from == 0 } else { steps[i - 1].to == current.from }
        },
    ensures 0 <= at <= end, steps[at].from <= definition < steps[at].to,
    decreases end,
{
    if definition < steps[end].from {
        assert(end > 0 && steps[end - 1].to == steps[end].from);
        trace_step_covering_slot(steps, end - 1, definition)
    } else {
        end
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
{
    reveal(mixed_trace);
    trace_step_covering_slot(steps, end, definition)
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
    } else if let Some(nested) = step.nested {
        let binding = bindings[step.group_before as int];
        nested_call_group_frame(&binding._selection@, forms, layouts, &nested.builtin, step.before, step.after,
            limit, nested.child_limit, definition_widths(body.definitions@), Ok(()));
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

proof fn wiring_prefix_transitive(early: WiringView, middle: WiringView, last: WiringView)
    requires wiring_view_is_prefix(early, middle), wiring_view_is_prefix(middle, last),
    ensures wiring_view_is_prefix(early, last),
{
    assert(last.gates.take(early.gates.len() as int) =~= early.gates);
    assert(last.origins.take(early.origins.len() as int) =~= early.origins);
    assert(last.definitions.take(early.definitions.len() as int) =~= early.definitions);
}

proof fn wiring_prefix_reflexive(wiring: WiringView)
    ensures wiring_view_is_prefix(wiring, wiring),
{
    assert(wiring.gates.take(wiring.gates.len() as int) =~= wiring.gates);
    assert(wiring.origins.take(wiring.origins.len() as int) =~= wiring.origins);
    assert(wiring.definitions.take(wiring.definitions.len() as int) =~= wiring.definitions);
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
        wiring_prefix_transitive(early, last.before, last.after);
    } else {
        wiring_prefix_reflexive(steps[end].after);
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
    wiring_prefix_transitive(step.before, step.after, final_wiring);
}

proof fn rooted_wiring_step_keeps_prefix(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, final_wiring: WiringView, at: int,
)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring),
        0 <= at < steps.len(),
    ensures wiring_view_is_prefix(steps[at].before, steps[at].after),
{
    reveal(rooted_mixed_trace);
    let step = steps[at];
    if step.nor_before == step.nor_after {
        wiring_step_keeps_prefix(body, layouts, forms, bindings, limit, step);
    } else {
        reveal(nor_wiring_step_valid);
        let binding = roots[step.nor_before as int];
        let nested = step.nested->Some_0;
        nor_call_group_frame(&binding.selected, *binding.references, forms, layouts, &nested.builtin,
            step.before, step.after, limit, nested.child_limit, definition_widths(body.definitions@), Ok(()));
    }
}

/// 根 NOR を含む履歴でも、各段の配線が後続の状態に同じ添字で残る。
proof fn rooted_trace_preserves_prefix(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, final_wiring: WiringView, at: int, end: int,
)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring),
        0 <= at <= end < steps.len(),
    ensures wiring_view_is_prefix(steps[at].after, steps[end].after),
    decreases end - at,
{
    if at < end {
        rooted_trace_preserves_prefix(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring, at, end - 1);
        rooted_wiring_step_keeps_prefix(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring, end);
        assert(steps[end - 1].after == steps[end].before) by { reveal(rooted_mixed_trace); };
        wiring_prefix_transitive(steps[at].after, steps[end].before, steps[end].after);
    } else {
        wiring_prefix_reflexive(steps[end].after);
    }
}

/// 本体に展開した根 NOR の配線状態と、同じ配線を評価した値。
#[cfg(verus_only)]
pub(super) struct RootedNorEvaluation<'s, 'p, 'a> {
    pub(super) step: WiringStep,
    pub(super) builtin: (NorNetlist, PortBitLayout),
    pub(super) evaluation: (Seq<ChildCall<'s, 'p, 'a>>, CallerArguments<'s, 'p, 'a>, NestedRootEvaluation<'s, 'p, 'a>),
}

proof fn rooted_trace_step_for_nor(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, final_wiring: WiringView, index: int,
) -> (at: int)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring),
        0 <= index < roots.len(), roots[index].selected.prepared.output_slot < slot,
        forall|i: int, j: int| 0 <= i < j < roots.len() ==>
            (#[trigger] roots[i]).selected.prepared.output_slot < (#[trigger] roots[j]).selected.prepared.output_slot,
    ensures
        0 <= at < steps.len(),
        steps[at].nor_before == index,
        steps[at].from == roots[index].selected.prepared.output_slot,
        steps[at].before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), steps[at].from as nat),
        steps[at].nested.is_some(),
        ({
            let binding = roots[index];
            let step = steps[at];
            let nested = step.nested->Some_0;
            nor_call_group_result(&binding.selected, *binding.references, forms, layouts, &nested.builtin,
                step.before, step.after, limit, nested.child_limit, definition_widths(body.definitions@), Ok(()))
        }),
        wiring_view_is_prefix(steps[at].before, steps[at].after),
        wiring_view_is_prefix(steps[at].before, final_wiring),
        wiring_view_is_prefix(steps[at].after, final_wiring),
{
    reveal(rooted_mixed_trace);
    let definition = roots[index].selected.prepared.output_slot as int;
    let end = steps.len() as int - 1;
    assert(0 <= end && steps[end].to == slot);
    let at = trace_step_covering_slot(steps, end, definition);
    let step = steps[at];
    if step.nor_before == step.nor_after {
        assert(no_nor_in_range(roots, step.from, step.to));
        assert(!(step.from <= definition < step.to));
    }
    reveal(nor_wiring_step_valid);
    assert(definition == step.from);
    let root_index = step.nor_before as int;
    assert(roots[root_index].selected.prepared.output_slot == definition);
    if root_index < index { assert(roots[root_index].selected.prepared.output_slot < roots[index].selected.prepared.output_slot); }
    if index < root_index { assert(roots[index].selected.prepared.output_slot < roots[root_index].selected.prepared.output_slot); }
    assert(root_index == index);
    rooted_trace_preserves_prefix(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring, at, end);
    rooted_wiring_step_keeps_prefix(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring, at);
    wiring_prefix_transitive(step.before, step.after, final_wiring);
    at
}

proof fn nor_evaluation_matches_final_definition(
    binding: &NorBinding, forms: Seq<Form>, layouts: &Layouts, result: &RootedNorEvaluation,
    final_wiring: WiringView, inputs: Seq<bool>, values: Seq<bool>,
)
    requires
        wiring_view_is_prefix(result.step.after, final_wiring),
        nor_call_group_evaluation_matches(&binding.selected, *binding.references, forms, layouts, &result.builtin,
            result.step.before, result.step.after, final_wiring.gates, inputs, values, result.evaluation),
    ensures ({
        let definition = binding.selected.prepared.output_slot as int;
        let definitions = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values);
        let root = result.evaluation.2;
        &&& 0 <= definition < definitions.len()
        &&& definitions[definition] == root.outputs
        &&& definitions[definition] == seq![!(root.arguments[0] || root.arguments[1])]
    }),
{
    reveal(nor_call_group_evaluation_matches);
    let definition = binding.selected.prepared.output_slot as int;
    let bit = result.step.before.definitions.len() as int;
    assert(final_wiring.definitions[bit] == result.step.after.definitions[bit]);
    let definitions = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values);
    assert(definitions[definition].len() == 1);
    assert(definitions[definition][0] == result.evaluation.2.outputs[0]);
    assert(definitions[definition] =~= result.evaluation.2.outputs);
}

/// 最終配線から根 NOR の入力と出力を取り出し、元の候補が指す定義の値に対応付ける。
#[verifier::spinoff_prover]
proof fn rooted_trace_nor_evaluation<'s, 'p, 'a>(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding<'s, 'p, 'a>>,
    limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, final_wiring: WiringView,
    index: int, inputs: Seq<bool>, values: Seq<bool>,
) -> (result: RootedNorEvaluation<'s, 'p, 'a>)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring),
        0 <= index < roots.len(), roots[index].selected.prepared.output_slot < slot,
        forall|i: int, j: int| 0 <= i < j < roots.len() ==>
            (#[trigger] roots[i]).selected.prepared.output_slot < (#[trigger] roots[j]).selected.prepared.output_slot,
        gate_values_match(inputs, final_wiring.gates, values),
        values.len() == final_wiring.gates.len() <= usize::MAX,
        inputs.len() == layouts.inputs.total_bits_model(),
    ensures
        result.step.from == roots[index].selected.prepared.output_slot,
        result.step.before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), result.step.from as nat),
        wiring_view_is_prefix(result.step.before, result.step.after),
        wiring_view_is_prefix(result.step.before, final_wiring),
        wiring_view_is_prefix(result.step.after, final_wiring),
        nor_call_group_evaluation_matches(&roots[index].selected, *roots[index].references, forms, layouts, &result.builtin,
            result.step.before, result.step.after, final_wiring.gates, inputs, values, result.evaluation),
        ({
            let definition = roots[index].selected.prepared.output_slot as int;
            let definitions = definition_values_from_wires(&layouts.definitions, final_wiring.definitions, inputs, values);
            let root = result.evaluation.2;
            &&& 0 <= definition < definitions.len()
            &&& definitions[definition] == root.outputs
            &&& definitions[definition] == seq![!(root.arguments[0] || root.arguments[1])]
        }),
{
    let at = rooted_trace_step_for_nor(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring, index);
    let binding = roots[index];
    let step = steps[at];
    let nested = step.nested->Some_0;
    let evaluation = nor_call_group_values(&binding.selected, *binding.references, forms, layouts, &nested.builtin,
        step.before, step.after, limit, nested.child_limit, definition_widths(body.definitions@),
        final_wiring.gates, inputs, values);
    let result = RootedNorEvaluation { step, builtin: nested.builtin, evaluation };
    nor_evaluation_matches_final_definition(&binding, forms, layouts, &result, final_wiring, inputs, values);
    result
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
        mixed_function_success(body, layouts, forms, bindings, widths, drivers, gate_limit, function, steps@),
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
        steps[at].nested.is_none(),
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
        MixedWiringError::CallOutputCapacity { .. } => false,
    }
}

pub(in crate::project::use_aliases::bit_func) open spec fn arguments_are_determined(arguments: Seq<ProjectedCallArgument>) -> bool {
    forall|port: int| 0 <= port < arguments.len() ==> !((#[trigger] arguments[port]).source is Deferred)
}

/// 引数に未確定の式が残っていれば、その時点で走査を終える。
pub(in crate::project::use_aliases::bit_func) fn arguments_are_determined_exec(arguments: &[ProjectedCallArgument]) -> (determined: bool)
    ensures determined == arguments_are_determined(arguments@),
{
    let mut port = 0;
    while port < arguments.len()
        invariant
            port <= arguments@.len(),
            forall|i: int| 0 <= i < port ==> !((#[trigger] arguments@[i]).source is Deferred),
        decreases arguments@.len() - port,
    {
        if matches!(arguments[port].source, CallArgumentSource::Deferred) {
            return false;
        }
        port += 1;
    }
    true
}

#[verifier::opaque]
spec fn nested_arguments_ready(call: &ResolvedTemplateCall) -> bool {
    &&& call.children@.len() > 0
    &&& arguments_are_determined(call.arguments@)
    &&& forall|i: int| 0 <= i < call.children@.len() ==>
        arguments_are_determined((#[trigger] call.children@[i]).arguments@)
}

#[verifier::opaque]
spec fn selected_children_reachable(call: &ResolvedTemplateCall, arguments: Seq<ProjectedCallArgument>) -> bool {
    let group = call.group;
    &&& group.postorder matches Some(children)
    &&& group.arguments.start <= group.arguments.end <= arguments.len()
    &&& call.arguments@ == arguments.subrange(group.arguments.start as int, group.arguments.end as int)
    &&& call.children@.len() == children@.len()
    &&& forall|i: int| 0 <= i < children@.len() ==> {
        let child = #[trigger] call.children@[i];
        let range = children@[i].arguments;
        &&& *child.child == children@[i]
        &&& range.start <= range.end <= arguments.len()
        &&& child.arguments@ == arguments.subrange(range.start as int, range.end as int)
        &&& expansion_child_reachable(group, arguments, children@.len() as int, i)
    }
}

/// 実際に選んだ根と子の引数列から、根がすべての子を参照することを示す。
proof fn prove_selected_children_reachable(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
    prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>, index: usize,
)
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
        aliases.expansion_selection_matches(plan, table, caller, prepared, selected),
        index < selected.len(),
        nested_arguments_ready(&selected[index as int]),
    ensures selected_children_reachable(&selected[index as int], prepared.projections.call_arguments.arguments@),
{
    reveal(nested_arguments_ready);
    reveal(selected_children_reachable);
    reveal(UseAliases::resolved_expression_call_matches);
    let call = &selected[index as int];
    let group = call.group;
    let arguments = prepared.projections.call_arguments.arguments@;
    assert(aliases.resolved_expression_calls_match(plan, table, caller.2, group.postorder, arguments, call.children@));
    assert(group.postorder.is_some());
    let children = group.postorder->Some_0@;
    assert forall|parent: int| 0 <= parent <= children.len() implies {
        let range = #[trigger] expansion_parent_range(group, children, parent);
        &&& range.start <= range.end <= arguments.len()
        &&& forall|at: int| range.start <= at < range.end ==> !((#[trigger] arguments[at]).source is Deferred)
    } by {
        let range = expansion_parent_range(group, children, parent);
        let projected = if parent == children.len() {
            call.arguments@
        } else {
            let child = call.children@[parent];
            assert(aliases.resolved_expression_call_matches(plan, table, caller.2, arguments, children[parent], child));
            child.arguments@
        };
        assert(projected == arguments.subrange(range.start as int, range.end as int));
        assert(arguments_are_determined(projected));
        assert forall|at: int| range.start <= at < range.end implies !((#[trigger] arguments[at]).source is Deferred) by {
            assert(arguments[at] == projected[at - range.start]);
        };
    };
    assert(*group == prepared.calls@[index as int]);
    assert(expansion_arguments_determined(group, arguments));
    aliases.expansion_reaches_every_child(*plan, caller, prepared, index as int);
    assert forall|i: int| 0 <= i < children.len() implies {
        let child = #[trigger] call.children@[i];
        let range = children[i].arguments;
        &&& *child.child == children[i]
        &&& range.start <= range.end <= arguments.len()
        &&& child.arguments@ == arguments.subrange(range.start as int, range.end as int)
        &&& expansion_child_reachable(group, arguments, children.len() as int, i)
    } by {
        assert(aliases.resolved_expression_call_matches(plan, table, caller.2, arguments, children[i], call.children@[i]));
    };
}

/// 根または子に未確定の引数が残る呼び出しは、従来の引数診断へ渡す。
fn can_lower_nested_arguments(call: &ResolvedTemplateCall) -> (ready: bool)
    ensures ready == nested_arguments_ready(call),
{
    reveal(nested_arguments_ready);
    if call.children.len() == 0 || !arguments_are_determined_exec(call.arguments) {
        return false;
    }
    let mut child = 0;
    while child < call.children.len()
        invariant
            call.children@.len() > 0,
            arguments_are_determined(call.arguments@),
            child <= call.children@.len(),
            forall|i: int| 0 <= i < child ==> arguments_are_determined((#[trigger] call.children@[i]).arguments@),
        decreases call.children@.len() - child,
    {
        let selected = &call.children[child];
        if !arguments_are_determined_exec(selected.arguments) {
            assert(!nested_arguments_ready(call)) by {
                reveal(nested_arguments_ready);
                assert(*selected == call.children@[child as int]);
                assert(!arguments_are_determined(call.children@[child as int].arguments@));
            };
            return false;
        }
        child += 1;
    }
    true
}

spec fn mixed_body_error_at(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, limit: usize,
    before: WiringView, slot: usize, group: usize, nested: Option<NestedWiring>, error: MixedBodyError,
) -> bool {
    match error {
        MixedBodyError::Flat(error) => {
            &&& mixed_error_at(body, layouts, forms, bindings, limit, before, slot, group, error)
            &&& (error is Call ==> (nested matches Some(mode) ==>
                group < mode.selected@.len() && !nested_arguments_ready(&mode.selected@[group as int])))
        },
        MixedBodyError::Nested(site, error) => {
            &&& nested matches Some(mode)
            &&& slot < body.definitions@.len()
            &&& binding_cursor(bindings, slot, group as int)
            &&& group < bindings.len() && group < mode.selected@.len()
            &&& bindings[group as int].group.outputs.start == slot
            &&& bindings[group as int]._selection@ == mode.selected@[group as int]
            &&& site == mode.selected@[group as int].group.expression
            &&& nested_arguments_ready(&mode.selected@[group as int])
            &&& selected_children_reachable(&mode.selected@[group as int], mode._arguments@)
            &&& match error {
                NestedCallWiringError::Child(index, _) => index < mode.selected@[group as int].children@.len(),
                NestedCallWiringError::Root(_) => true,
            }
            &&& nested_call_group_result(&mode.selected@[group as int], forms, layouts, mode.builtin,
                before, before, limit, mode.child_limit, definition_widths(body.definitions@), Err(error))
        },
        MixedBodyError::Nor(_, _) => false,
    }
}

spec fn wiring_step_uses_mode(step: WiringStep, mode: Option<NestedWiring>) -> bool {
    if step.nor_before != step.nor_after {
        &&& mode matches Some(mode)
        &&& step.nested matches Some(nested)
        &&& nested.builtin == *mode.builtin && nested.child_limit == mode.child_limit
        &&& nested.arguments == mode._arguments@
    } else if step.group_before == step.group_after {
        step.nested.is_none()
    } else if let Some(mode) = mode {
        let group = step.group_before as int;
        &&& group < mode.selected@.len()
        &&& if nested_arguments_ready(&mode.selected@[group]) {
            step.nested matches Some(nested) && nested.builtin == *mode.builtin && nested.child_limit == mode.child_limit
                && nested.arguments == mode._arguments@
        } else {
            step.nested.is_none()
        }
    } else {
        step.nested.is_none()
    }
}

spec fn wiring_trace_uses_mode(steps: Seq<WiringStep>, mode: Option<NestedWiring>) -> bool {
    forall|i: int| 0 <= i < steps.len() ==> wiring_step_uses_mode(#[trigger] steps[i], mode)
}

#[verifier::opaque]
spec fn mixed_body_failed(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, gate_limit: usize,
    nested: Option<NestedWiring>, error: MixedBodyError,
) -> bool {
    exists|steps: Seq<WiringStep>, slot: usize, group: usize, wiring: WiringView|
        #[trigger] mixed_trace(body, layouts, forms, bindings, gate_limit, steps, slot, group, wiring)
        && (nested.is_none() ==> flat_wiring_trace(steps))
        && wiring_trace_uses_mode(steps, nested)
        && mixed_body_error_at(body, layouts, forms, bindings, gate_limit, wiring, slot, group, nested, error)
}

spec fn rooted_error_at(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    limit: usize, wiring: WiringView, slot: usize, group: usize, nor: usize, nested: Option<NestedWiring>, error: MixedBodyError,
) -> bool {
    &&& binding_cursor(bindings, slot, group as int)
    &&& nor_cursor(roots, slot, nor as int)
    &&& match error {
        MixedBodyError::Nor(site, error) => {
            let binding = roots[nor as int];
            &&& nested matches Some(mode)
            &&& nor < roots.len() && slot < body.definitions@.len()
            &&& binding.selected.prepared.output_slot == slot
            &&& !binding_covers(bindings, slot as int)
            &&& site == binding.selected.prepared.root.expression
            &&& nor_call_group_result(&binding.selected, *binding.references, forms, layouts, mode.builtin,
                wiring, wiring, limit, mode.child_limit, definition_widths(body.definitions@), Err(error))
        },
        _ => !nor_binding_covers(roots, slot as int)
            && mixed_body_error_at(body, layouts, forms, bindings, limit, wiring, slot, group, nested, error),
    }
}

#[verifier::opaque]
spec fn rooted_body_failed(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    limit: usize, nested: Option<NestedWiring>, error: MixedBodyError,
) -> bool {
    exists|steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, wiring: WiringView|
        #[trigger] rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, wiring)
        && (nested.is_none() ==> flat_wiring_trace(steps))
        && wiring_trace_uses_mode(steps, nested)
        && rooted_error_at(body, layouts, forms, bindings, roots, limit, wiring, slot, group, nor, nested, error)
}

proof fn mixed_failure_after_prefix(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    gate_limit: usize, nested: Option<NestedWiring>, error: MixedBodyError,
    steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, wiring: WiringView,
)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, gate_limit, steps, slot, group, nor, wiring),
        nested.is_none() ==> flat_wiring_trace(steps),
        wiring_trace_uses_mode(steps, nested),
        rooted_error_at(body, layouts, forms, bindings, roots, gate_limit, wiring, slot, group, nor, nested, error),
    ensures
        rooted_body_failed(body, layouts, forms, bindings, roots, gate_limit, nested, error),
        roots.len() == 0 ==> mixed_body_failed(body, layouts, forms, bindings, gate_limit, nested, error),
{
    reveal(rooted_body_failed);
    reveal(mixed_body_failed);
    if roots.len() == 0 {
        rooted_trace_without_roots(body, layouts, forms, bindings, roots, gate_limit, steps, slot, group, nor, wiring);
        assert(mixed_body_error_at(body, layouts, forms, bindings, gate_limit, wiring, slot, group, nested, error));
    }
}

/// 同じ定義区間に対して呼び出しを展開し、成功したときだけ履歴に追加できる段を返す。
#[verifier::rlimit(32)]
fn lower_mixed_call<'s, 'p, 'a>(
    layouts: &Layouts, forms: &[Form], bindings: &[CallBinding<'s, 'p, 'a>],
    state: &mut BodyWiring, gate_limit: usize, group: usize,
    nested: Option<NestedWiring<'s, 'p, 'a>>,
    Ghost(body): Ghost<&LoweringBody<'s, 'p, 'a>>, Ghost(layout_limit): Ghost<usize>, Ghost(slot): Ghost<usize>,
    Ghost(nor): Ghost<usize>,
    Ghost(context): Ghost<Option<(&UseAliases<'_, 'p, 'a>, &FunctionExpansionOrder<'p, 'a>,
        &FunctionTemplates<'p, 'a>, (usize, usize, u64), &PreparedExpansionBody<'p, 'a>)>>,
) -> (result: Result<Ghost<WiringStep>, MixedBodyError<'p, 'a>>)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        group < bindings@.len(),
        binding_cursor(bindings@, slot, group as int),
        bindings@[group as int].group.outputs.start == slot,
        slot < body.definitions@.len(),
        binding_ready(bindings@[group as int], layouts, forms@, definition_widths(body.definitions@)),
        old(state).definitions@.len() == preceding_port_bits(definition_widths(body.definitions@), slot as nat),
        old(state).gates@.len() == old(state).origins@.len() <= gate_limit,
        gates_available(old(state).gates@, layouts.inputs.total_bits_model() as nat, old(state).gates@.len() as int),
        wires_available(old(state).definitions@, layouts.inputs.total_bits_model(), old(state).gates@.len()),
        nested matches Some(mode) ==> {
            &&& context matches Some((aliases, plan, table, caller, prepared))
            &&& aliases.can_resolve()
            &&& aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared)
            &&& mode._arguments@ == prepared.projections.call_arguments.arguments@
            &&& aliases.expansion_selection_matches(plan, table, caller, prepared, mode.selected@)
            &&& bindings_match_calls(bindings@, mode.selected@)
            &&& builtin_nor_call_matches(mode.builtin)
            &&& resolved_call_fits_body(mode.selected@[group as int], body.input_widths@, body.definitions@, forms@, caller.2)
        },
    ensures match result {
        Ok(step) => {
            let binding = bindings@[group as int];
            &&& step@.from == slot && step@.to == binding.group.outputs.end
            &&& step@.group_before == group && step@.group_after == group + 1
            &&& step@.nor_before == nor && step@.nor_after == nor
            &&& step@.before == old(state).model() && step@.after == final(state).model()
            &&& wiring_step_valid(body, layouts, forms@, bindings@, gate_limit, step@)
            &&& wiring_step_uses_mode(step@, nested)
            &&& final(state).definitions@.len() == preceding_port_bits(definition_widths(body.definitions@), step@.to as nat)
            &&& final(state).gates@.len() == final(state).origins@.len() <= gate_limit
            &&& gates_available(final(state).gates@, layouts.inputs.total_bits_model() as nat, final(state).gates@.len() as int)
            &&& wires_available(final(state).definitions@, layouts.inputs.total_bits_model(), final(state).gates@.len())
        },
        Err(error) => {
            &&& final(state).model() == old(state).model()
            &&& mixed_body_error_at(body, layouts, forms@, bindings@, gate_limit, old(state).model(),
                slot, group, nested, error)
        },
    },
{
    let binding = &bindings[group];
    let ghost before = state.model();
    let ghost widths = definition_widths(body.definitions@);
    proof { reveal(binding_ready); }
    let nested_call = match &nested {
        Some(mode) => {
            let selected = &mode.selected[group];
            if can_lower_nested_arguments(selected) { Some((mode, selected)) } else { None }
        },
        None => None,
    };
    let ghost from = slot;
    let ghost to = binding.group.outputs.end;
    let ghost following = (group + 1) as usize;
    let Ghost(step) = if let Some((mode, selected)) = nested_call {
        let ghost (aliases, plan, table, caller, prepared) = context->Some_0;
        assert(binding_matches_selection(*binding, *selected));
        proof {
            prove_selected_children_reachable(aliases, plan, table, caller, prepared, mode.selected@, group);
        }
        let expanded = lower_nested_call_group(selected, forms, layouts, mode.builtin, &mut *state, gate_limit,
            mode.child_limit, Ghost(body), Ghost(aliases),
            Ghost((plan, table, caller.2, prepared.projections.call_arguments.arguments@)), Ghost(layout_limit));
        assert(nested_call_group_result(selected, forms@, layouts, mode.builtin, before, state.model(),
            gate_limit, mode.child_limit, widths, expanded));
        let ghost outcome = expanded;
        match expanded {
            Err(error) => {
                proof {
                    assert(outcome == Err(error));
                    nested_call_group_frame(selected, forms@, layouts, mode.builtin, before, state.model(),
                        gate_limit, mode.child_limit, widths, outcome);
                    assert(state.model() == before);
                }
                return Err(MixedBodyError::Nested(copy_location(&selected.group.expression), error));
            },
            Ok(()) => proof {
                assert(outcome is Ok);
                nested_call_group_frame(selected, forms@, layouts, mode.builtin, before, state.model(),
                    gate_limit, mode.child_limit, widths, outcome);
            },
        };
        let ghost child_step = NestedCallStep { builtin: *mode.builtin, child_limit: mode.child_limit, arguments: mode._arguments@ };
        let ghost step = WiringStep { from, to, group_before: group, group_after: following, nor_before: nor, nor_after: nor,
            before, after: state.model(), nested: Some(child_step) };
        assert(wiring_step_valid(body, layouts, forms@, bindings@, gate_limit, step)) by { reveal(wiring_step_valid); };
        Ghost(step)
    } else {
        if let Err(error) = lower_call_group(binding.group, forms, binding.arguments, layouts, binding.callee, &mut *state, gate_limit,
            Ghost(widths), Ghost(binding._input_widths@), Ghost(binding._output_widths@),
            Ghost(layout_limit), Ghost(binding._layout_limit@)) {
            let result = MixedWiringError::Call(error);
            assert(mixed_error_at(body, layouts, forms@, bindings@, gate_limit, before, slot, group, result));
            return Err(MixedBodyError::Flat(result));
        }
        let ghost step = WiringStep { from, to, group_before: group, group_after: following, nor_before: nor, nor_after: nor,
            before, after: state.model(), nested: None };
        assert(wiring_step_valid(body, layouts, forms@, bindings@, gate_limit, step)) by { reveal(wiring_step_valid); };
        Ghost(step)
    };
    Ok(Ghost(step))
}

spec fn nor_roots_ready(
    body: &LoweringBody, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    nested: Option<NestedWiring>,
    context: Option<(&UseAliases, &FunctionExpansionOrder, &FunctionTemplates, (usize, usize, u64), &PreparedExpansionBody)>,
) -> bool {
    roots.len() > 0 ==> {
        &&& nested matches Some(mode)
        &&& context matches Some((aliases, plan, table, caller, prepared))
        &&& forall|i: int| 0 <= i < roots.len() ==> {
            let binding = #[trigger] roots[i];
            let root = binding.selected.prepared;
            let source = root.root.expression.source;
            &&& !binding_covers(bindings, root.output_slot as int)
            &&& nor_binding_fits_body(binding, source, forms, body.input_widths@, body.definitions@, caller.2)
            &&& aliases.nor_binding_context(plan, table, caller.2, mode._arguments@, binding)
            &&& form_spans_valid(source.text, forms, source.text.spec_bytes().len() as int)
        }
        &&& forall|i: int, j: int| 0 <= i < j < roots.len() ==>
            (#[trigger] roots[i]).selected.prepared.output_slot < (#[trigger] roots[j]).selected.prepared.output_slot
    }
}

/// 通常の定義と根 NOR は一件ずつ、関数呼び出しは出力区間ごとに配線を追加する。
///
/// # Errors
///
/// 定義順で最初に失敗した右辺または実引数の範囲を返す。
#[verifier::spinoff_prover]
#[verifier::rlimit(72)]
fn lower_mixed_body<'s, 'p, 'a>(
    body: &LoweringBody<'s, 'p, 'a>, layouts: &Layouts, forms: &[Form], bindings: &[CallBinding<'s, 'p, 'a>],
    roots: &[NorBinding<'s, 'p, 'a>],
    layout_limit: usize, gate_limit: usize, nested: Option<NestedWiring<'s, 'p, 'a>>,
    Ghost(context): Ghost<Option<(&UseAliases<'_, 'p, 'a>, &FunctionExpansionOrder<'p, 'a>,
        &FunctionTemplates<'p, 'a>, (usize, usize, u64), &PreparedExpansionBody<'p, 'a>)>>,
) -> (result: Result<(BodyWiring, Ghost<Seq<WiringStep>>), MixedBodyError<'p, 'a>>)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, layouts),
        ordered_bindings(bindings@),
        forall|g: int| 0 <= g < bindings@.len() ==> binding_ready(
            #[trigger] bindings@[g], layouts, forms@, definition_widths(body.definitions@)),
        nor_roots_ready(body, forms@, bindings@, roots@, nested, context),
        forall|slot: int| 0 <= slot < body.definitions@.len() && !binding_covers(bindings@, slot) && !nor_binding_covers(roots@, slot) ==>
            bit_definition_matches(body.input_widths@, body.definitions@.take(slot), #[trigger] body.definitions@[slot]),
        nested matches Some(mode) ==> {
            &&& context matches Some((aliases, plan, table, caller, prepared))
            &&& aliases.can_resolve()
            &&& aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared)
            &&& mode._arguments@ == prepared.projections.call_arguments.arguments@
            &&& aliases.expansion_selection_matches(plan, table, caller, prepared, mode.selected@)
            &&& bindings_match_calls(bindings@, mode.selected@)
            &&& builtin_nor_call_matches(mode.builtin)
            &&& forall|i: int| 0 <= i < mode.selected@.len() ==>
                resolved_call_fits_body(#[trigger] mode.selected@[i], body.input_widths@, body.definitions@, forms@, caller.2)
        },
    ensures match result {
        Ok((state, steps)) => {
            &&& rooted_mixed_trace(body, layouts, forms@, bindings@, roots@, gate_limit, steps@,
                body.definitions@.len() as usize, bindings@.len() as usize, roots@.len() as usize, state.model())
            &&& roots@.len() == 0 ==> mixed_trace(body, layouts, forms@, bindings@, gate_limit, steps@,
                body.definitions@.len() as usize, bindings@.len() as usize, state.model())
            &&& (nested.is_none() ==> flat_wiring_trace(steps@))
            &&& wiring_trace_uses_mode(steps@, nested)
            &&& state.definitions@.len() == layouts.definitions.total_bits_model()
            &&& state.gates@.len() == state.origins@.len() <= gate_limit
            &&& gates_available(state.gates@, layouts.inputs.total_bits_model() as nat, state.gates@.len() as int)
            &&& wires_available(state.definitions@, layouts.inputs.total_bits_model(), state.gates@.len())
        },
        Err(error) => rooted_body_failed(body, layouts, forms@, bindings@, roots@, gate_limit, nested, error)
            && (roots@.len() == 0 ==> mixed_body_failed(body, layouts, forms@, bindings@, gate_limit, nested, error)),
    },
{
    let mut state = BodyWiring { definitions: Vec::new(), gates: Vec::new(), origins: Vec::new() };
    let ghost mut steps = Seq::<WiringStep>::empty();
    let mut slot = 0usize;
    let mut group = 0usize;
    let mut nor = 0usize;
    let ghost widths = definition_widths(body.definitions@);
    let ghost input_count = layouts.inputs.total_bits_model();
    proof {
        reveal(rooted_mixed_trace);
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
            nor_roots_ready(body, forms@, bindings@, roots@, nested, context),
            nor_cursor(roots@, slot, nor as int),
            forall|i: int| 0 <= i < body.definitions@.len() && !binding_covers(bindings@, i) && !nor_binding_covers(roots@, i) ==>
                bit_definition_matches(body.input_widths@, body.definitions@.take(i), #[trigger] body.definitions@[i]),
            slot <= body.definitions@.len(),
            state.definitions@.len() == preceding_port_bits(widths, slot as nat),
            state.gates@.len() == state.origins@.len() <= gate_limit,
            gates_available(state.gates@, input_count as nat, state.gates@.len() as int),
            wires_available(state.definitions@, input_count, state.gates@.len()),
            rooted_mixed_trace(body, layouts, forms@, bindings@, roots@, gate_limit, steps, slot, group, nor, state.model()),
            nested.is_none() ==> flat_wiring_trace(steps),
            wiring_trace_uses_mode(steps, nested),
            nested matches Some(mode) ==> {
                &&& context matches Some((aliases, plan, table, caller, prepared))
                &&& aliases.can_resolve()
                &&& aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared)
                &&& mode._arguments@ == prepared.projections.call_arguments.arguments@
                &&& aliases.expansion_selection_matches(plan, table, caller, prepared, mode.selected@)
                &&& bindings_match_calls(bindings@, mode.selected@)
                &&& builtin_nor_call_matches(mode.builtin)
                &&& forall|i: int| 0 <= i < mode.selected@.len() ==>
                    resolved_call_fits_body(#[trigger] mode.selected@[i], body.input_widths@, body.definitions@, forms@, caller.2)
            },
        decreases body.definitions@.len() - slot,
    {
        let ghost before = state.model();
        let ghost start = slot;
        let ghost cursor = group;
        let ghost root_cursor = nor;
        let ghost step: WiringStep;
        let head = if group < bindings.len() { Some(bindings[group].group.outputs.start) } else { None };
        let nor_head = if nor < roots.len() { Some(roots[nor].selected.prepared.output_slot) } else { None };
        proof {
            if group < bindings.len() && nor < roots.len() && head == nor_head {
                assert(binding_covers(bindings@, roots@[nor as int].selected.prepared.output_slot as int));
                assert(false);
            }
        }
        let kind = expansion_call_at_slot(head, nor_head, slot);
        if matches!(kind, ExpansionSlot::Function) {
            let end = bindings[group].group.outputs.end;
            proof {
                assert forall|i: int| nor <= i < roots@.len() implies
                    end <= (#[trigger] roots@[i]).selected.prepared.output_slot by {
                    let at = roots@[i].selected.prepared.output_slot as int;
                    assert(!binding_covers(bindings@, at));
                    if at < end { assert(binding_covers(bindings@, at)); }
                };
                advance_nor_cursor(roots@, slot, nor, end, false);
            }
            match lower_mixed_call(layouts, forms, bindings, &mut state, gate_limit, group, nested,
                Ghost(body), Ghost(layout_limit), Ghost(slot), Ghost(nor), Ghost(context)) {
                Ok(recorded) => {
                    let Ghost(call_step) = recorded;
                    proof { step = call_step; }
                },
                Err(error) => {
                    proof {
                        mixed_failure_after_prefix(body, layouts, forms@, bindings@, roots@, gate_limit, nested, error,
                            steps, slot, group, nor, before);
                    }
                    return Err(error);
                },
            };
            proof { advance_binding_cursor(bindings@, slot, group, end, true); }
            slot = end;
            group += 1;
        } else if matches!(kind, ExpansionSlot::Nor) {
            let binding = &roots[nor];
            let Some(mode) = nested else {
                proof { assert(false); }
                unreachable!()
            };
            let ghost (aliases, plan, table, caller, prepared) = context->Some_0;
            let result = lower_nor_call_group(&binding.selected, binding.references, forms, layouts, mode.builtin,
                &mut state, gate_limit, mode.child_limit, Ghost(body), Ghost(aliases),
                Ghost((plan, table, caller.2, prepared.projections.call_arguments.arguments@)), Ghost(layout_limit));
            let ghost after = state.model();
            assert(nor_call_group_result(&binding.selected, *binding.references, forms@, layouts, mode.builtin,
                before, after, gate_limit, mode.child_limit, widths, result));
            let ghost outcome = result;
            match result {
                Err(error) => {
                    proof {
                        assert(outcome == Err(error));
                        nor_call_group_frame(&binding.selected, *binding.references, forms@, layouts, mode.builtin,
                            before, after, gate_limit, mode.child_limit, widths, outcome);
                    }
                    let raw = MixedBodyError::Nor(copy_location(&binding.selected.prepared.root.expression), error);
                    proof {
                        mixed_failure_after_prefix(body, layouts, forms@, bindings@, roots@, gate_limit, nested, raw,
                            steps, slot, group, nor, before);
                    }
                    return Err(raw);
                },
                Ok(()) => proof {
                    assert(outcome is Ok);
                    nor_call_group_frame(&binding.selected, *binding.references, forms@, layouts, mode.builtin,
                        before, after, gate_limit, mode.child_limit, widths, outcome);
                },
            }
            proof {
                assert(*binding == roots@[root_cursor as int]);
                assert(binding.selected.prepared.output_slot == start);
                assert(start < body.definitions@.len());
                assert(before.definitions.len() == preceding_port_bits(widths, start as nat));
                assert(nor_call_group_result(&binding.selected, *binding.references, forms@, layouts, mode.builtin,
                    before, after, gate_limit, mode.child_limit, widths, Ok(())));
                advance_binding_cursor(bindings@, slot, group, (slot + 1) as usize, false);
                assert forall|i: int| nor < i < roots@.len() implies
                    slot < (#[trigger] roots@[i]).selected.prepared.output_slot by {
                    assert(roots@[nor as int].selected.prepared.output_slot < roots@[i].selected.prepared.output_slot);
                };
                advance_nor_cursor(roots@, slot, nor, (slot + 1) as usize, true);
            }
            slot += 1;
            nor += 1;
            proof {
                step = WiringStep { from: start, to: slot, group_before: cursor, group_after: group,
                    nor_before: root_cursor, nor_after: nor, before, after,
                    nested: Some(NestedCallStep { builtin: *mode.builtin, child_limit: mode.child_limit, arguments: mode._arguments@ }) };
                assert(nor_wiring_step_valid(body, layouts, forms@, roots@, gate_limit, step)) by {
                    reveal(nor_wiring_step_valid);
                    let descriptor = step.nested->Some_0;
                    assert(descriptor.builtin == *mode.builtin);
                    assert(nor_call_group_result(&binding.selected, *binding.references, forms@, layouts, &descriptor.builtin,
                        before, after, gate_limit, descriptor.child_limit, widths, Ok(())));
                };
            }
        } else {
            proof {
                assert forall|i: int| nor <= i < roots@.len() implies
                    slot < (#[trigger] roots@[i]).selected.prepared.output_slot by {
                    if nor < i { assert(roots@[nor as int].selected.prepared.output_slot < roots@[i].selected.prepared.output_slot); }
                };
                advance_nor_cursor(roots@, slot, nor, (slot + 1) as usize, false);
            }
            proof { advance_binding_cursor(bindings@, slot, group, (slot + 1) as usize, false); }
            match lower_definition(body, layouts, layout_limit, gate_limit, slot,
                &mut state.definitions, &mut state.gates, &mut state.origins) {
                Err(site) => {
                    let result = MixedWiringError::LocalGateCapacity(site);
                    assert(mixed_error_at(body, layouts, forms@, bindings@, gate_limit, before, slot, group, result));
                    proof {
                        mixed_failure_after_prefix(body, layouts, forms@, bindings@, roots@, gate_limit, nested,
                            MixedBodyError::Flat(result), steps, slot, group, nor, before);
                    }
                    return Err(MixedBodyError::Flat(result));
                },
                Ok(()) => {},
            }
            slot += 1;
            proof {
                step = WiringStep { from: start, to: slot, group_before: cursor, group_after: group,
                    nor_before: root_cursor, nor_after: nor, before, after: state.model(), nested: None };
                assert(wiring_step_valid(body, layouts, forms@, bindings@, gate_limit, step)) by { reveal(wiring_step_valid); };
            }
        }
        proof {
            extend_rooted_trace(body, layouts, forms@, bindings@, roots@, gate_limit, steps, step);
            assert(wiring_step_uses_mode(step, nested));
            assert(wiring_trace_uses_mode(steps.push(step), nested));
            assert(nested.is_none() ==> flat_wiring_trace(steps.push(step))) by {
                reveal(wiring_step_uses_mode);
            };
            steps = steps.push(step);
        }
    }
    proof {
        if group < bindings@.len() {
            assert(slot <= bindings@[group as int].group.outputs.start);
            assert(false);
        }
        if nor < roots@.len() {
            assert(slot <= roots@[nor as int].selected.prepared.output_slot);
            assert(false);
        }
        if roots@.len() == 0 {
            rooted_trace_without_roots(body, layouts, forms@, bindings@, roots@, gate_limit, steps, slot, group, nor, state.model());
        }
        port_bit_layout_size(widths, layout_limit, &layouts.definitions);
    }
    Ok((state, Ghost(steps)))
}

pub(super) open spec fn mixed_function_outputs_match(
    layouts: &Layouts,
    output_widths: Seq<u64>, output_drivers: Seq<OutputDriver>, gate_limit: usize,
    value: &LoweredBitFunc,
) -> bool {
    &&& value.layouts == *layouts
    &&& value.netlist.input_count == layouts.inputs.total_bits_model()
    &&& value.netlist.outputs@.len() == layouts.outputs.total_bits_model()
    &&& value.definition_wires@.len() == layouts.definitions.total_bits_model()
    &&& wires_available(value.definition_wires@, layouts.inputs.total_bits_model(), value.netlist.gates@.len())
    &&& value.netlist.gates@.len() == value.gate_definitions@.len() <= gate_limit
    &&& nor_evaluation_ready(&value.netlist, layouts.inputs.total_bits_model() as nat)
    &&& body_output_wiring_matches(output_drivers, layouts, value.definition_wires@, value.netlist.outputs@,
        output_widths.len() as int)
}

pub(super) open spec fn mixed_function_success(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    output_widths: Seq<u64>, output_drivers: Seq<OutputDriver>, gate_limit: usize,
    value: &LoweredBitFunc, steps: Seq<WiringStep>,
) -> bool {
    &&& mixed_function_outputs_match(layouts, output_widths, output_drivers, gate_limit, value)
    &&& bindings.len() <= usize::MAX
    &&& mixed_trace(body, layouts, forms, bindings, gate_limit, steps, body.definitions@.len() as usize,
        bindings.len() as usize, WiringView { definitions: value.definition_wires@,
            gates: value.netlist.gates@, origins: value.gate_definitions@ })
}

pub(super) open spec fn rooted_mixed_function_success(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    output_widths: Seq<u64>, output_drivers: Seq<OutputDriver>, gate_limit: usize,
    value: &LoweredBitFunc, steps: Seq<WiringStep>,
) -> bool {
    &&& mixed_function_outputs_match(layouts, output_widths, output_drivers, gate_limit, value)
    &&& bindings.len() <= usize::MAX && roots.len() <= usize::MAX
    &&& rooted_mixed_trace(body, layouts, forms, bindings, roots, gate_limit, steps, body.definitions@.len() as usize,
        bindings.len() as usize, roots.len() as usize, WiringView { definitions: value.definition_wires@,
            gates: value.netlist.gates@, origins: value.gate_definitions@ })
}

/// 一つの式の中間出力を保持できる配線数を、対象環境の配列のバイト上限から求める。
fn child_output_limit() -> (limit: usize)
    ensures limit == child_output_limit_spec(),
{
    let element_size = core::mem::size_of::<Wire>();
    if element_size == 0 { usize::MAX } else { isize::MAX as usize / element_size }
}

spec fn child_output_limit_spec() -> usize {
    let element_size = vstd::layout::size_of::<Wire>();
    if element_size == 0 { usize::MAX } else { (isize::MAX as nat / element_size) as usize }
}

spec fn mixed_wiring_diagnostic<'p, 'a>(error: MixedBodyError<'p, 'a>) -> MixedWiringError<'p, 'a> {
    match error {
        MixedBodyError::Flat(error) => error,
        MixedBodyError::Nested(site, error) | MixedBodyError::Nor(site, error) => match error {
            NestedCallWiringError::Child(_, ChildCallWiringError::OutputCapacity { site, used, width, capacity }) =>
                MixedWiringError::CallOutputCapacity { site, used, width, capacity },
            NestedCallWiringError::Child(_, ChildCallWiringError::DeferredArgument(argument))
            | NestedCallWiringError::Root(CallWiringError::DeferredArgument(argument)) =>
                MixedWiringError::Call(CallGroupError::DeferredArgument(argument)),
            NestedCallWiringError::Child(_, ChildCallWiringError::GateCapacity(child)) =>
                MixedWiringError::Call(CallGroupError::GateCapacity(child)),
            NestedCallWiringError::Root(CallWiringError::GateCapacity) =>
                MixedWiringError::Call(CallGroupError::GateCapacity(site)),
        },
    }
}

/// 失敗した引数や式の範囲を保ち、一時配線表の上限違反を区別する。
fn normalize_mixed_wiring_diagnostic<'p, 'a>(error: MixedBodyError<'p, 'a>) -> (diagnostic: MixedWiringError<'p, 'a>)
    ensures diagnostic == mixed_wiring_diagnostic(error),
{
    match error {
        MixedBodyError::Flat(error) => error,
        MixedBodyError::Nested(site, error) | MixedBodyError::Nor(site, error) => match error {
            NestedCallWiringError::Child(_, ChildCallWiringError::OutputCapacity { site, used, width, capacity }) =>
                MixedWiringError::CallOutputCapacity { site, used, width, capacity },
            NestedCallWiringError::Child(_, ChildCallWiringError::DeferredArgument(argument))
            | NestedCallWiringError::Root(CallWiringError::DeferredArgument(argument)) =>
                MixedWiringError::Call(CallGroupError::DeferredArgument(argument)),
            NestedCallWiringError::Child(_, ChildCallWiringError::GateCapacity(child)) =>
                MixedWiringError::Call(CallGroupError::GateCapacity(child)),
            NestedCallWiringError::Root(CallWiringError::GateCapacity) =>
                MixedWiringError::Call(CallGroupError::GateCapacity(site)),
        },
    }
}

spec fn resolved_mixed_mode_matches(
    bindings: Seq<CallBinding>, arguments: Seq<ProjectedCallArgument>, mode: Option<NestedWiring>,
) -> bool {
    match mode {
        Some(mode) => mode._arguments@ == arguments && mode.child_limit == child_output_limit_spec()
            && builtin_nor_call_matches(mode.builtin) && bindings_match_calls(bindings, mode.selected@)
            && exists|i: int| 0 <= i < mode.selected@.len() && (#[trigger] mode.selected@[i]).children@.len() > 0,
        None => forall|i: int| 0 <= i < bindings.len() ==> (#[trigger] bindings[i])._selection@.children@.len() == 0,
    }
}

pub(super) closed spec fn resolved_mixed_trace(
    bindings: Seq<CallBinding>, arguments: Seq<ProjectedCallArgument>, steps: Seq<WiringStep>,
) -> bool {
    exists|mode: Option<NestedWiring>| #[trigger] wiring_trace_uses_mode(steps, mode)
        && resolved_mixed_mode_matches(bindings, arguments, mode)
}

pub(super) closed spec fn mixed_function_failure(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    arguments: Seq<ProjectedCallArgument>, gate_limit: usize, diagnostic: MixedWiringError,
) -> bool {
    exists|mode: Option<NestedWiring>, raw: MixedBodyError|
        #[trigger] mixed_body_failed(body, layouts, forms, bindings, gate_limit, mode, raw)
        && mixed_wiring_diagnostic(raw) == diagnostic
        && resolved_mixed_mode_matches(bindings, arguments, mode)
}

pub(super) open spec fn mixed_function_result(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    output_widths: Seq<u64>, output_drivers: Seq<OutputDriver>, arguments: Seq<ProjectedCallArgument>, gate_limit: usize,
    result: Result<(LoweredBitFunc, Ghost<Seq<WiringStep>>), MixedWiringError>,
) -> bool {
    match result {
        Ok((value, steps)) => mixed_function_success(body, layouts, forms, bindings, output_widths, output_drivers,
            gate_limit, &value, steps@) && wiring_trace_arguments_match(steps@, arguments)
            && resolved_mixed_trace(bindings, arguments, steps@),
        Err(error) => mixed_function_failure(body, layouts, forms, bindings, arguments, gate_limit, error),
    }
}

/// 本体を配線し、宣言順に出力を結線して、配線履歴とともにネットリストを返す。
///
/// # Errors
///
/// 選んだ展開経路で最初に失敗した定義または呼び出しの診断を返す。
fn lower_mixed_function_with_mode<'s, 'p, 'a>(
    body: &LoweringBody<'s, 'p, 'a>, layouts: Layouts, forms: &[Form], bindings: &[CallBinding<'s, 'p, 'a>],
    roots: &[NorBinding<'s, 'p, 'a>],
    output_widths: &[u64], output_drivers: &[OutputDriver],
    layout_limit: usize, gate_limit: usize, nested: Option<NestedWiring<'s, 'p, 'a>>,
    Ghost(context): Ghost<Option<(&UseAliases<'_, 'p, 'a>, &FunctionExpansionOrder<'p, 'a>,
        &FunctionTemplates<'p, 'a>, (usize, usize, u64), &PreparedExpansionBody<'p, 'a>)>>,
) -> (result: Result<(LoweredBitFunc, Ghost<Seq<WiringStep>>), MixedBodyError<'p, 'a>>)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, &layouts),
        widths_layout(output_widths@, layout_limit, &layouts.outputs),
        output_widths@.len() == output_drivers@.len(),
        forall|p: int| 0 <= p < output_widths@.len() ==>
            bit_driver_width(body.input_widths@, body.definitions@, #[trigger] output_drivers@[p]) == Some(output_widths@[p]),
        ordered_bindings(bindings@),
        forall|g: int| 0 <= g < bindings@.len() ==> binding_ready(
            #[trigger] bindings@[g], &layouts, forms@, definition_widths(body.definitions@)),
        nor_roots_ready(body, forms@, bindings@, roots@, nested, context),
        forall|slot: int| 0 <= slot < body.definitions@.len() && !binding_covers(bindings@, slot) && !nor_binding_covers(roots@, slot) ==>
            bit_definition_matches(body.input_widths@, body.definitions@.take(slot), #[trigger] body.definitions@[slot]),
        nested matches Some(mode) ==> {
            &&& context matches Some((aliases, plan, table, caller, prepared))
            &&& aliases.can_resolve()
            &&& aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared)
            &&& mode._arguments@ == prepared.projections.call_arguments.arguments@
            &&& aliases.expansion_selection_matches(plan, table, caller, prepared, mode.selected@)
            &&& bindings_match_calls(bindings@, mode.selected@)
            &&& builtin_nor_call_matches(mode.builtin)
            &&& forall|i: int| 0 <= i < mode.selected@.len() ==>
                resolved_call_fits_body(#[trigger] mode.selected@[i], body.input_widths@, body.definitions@, forms@, caller.2)
        },
    ensures match result {
        Ok((value, steps)) => {
            &&& rooted_mixed_function_success(body, &layouts, forms@, bindings@, roots@, output_widths@, output_drivers@,
                gate_limit, &value, steps@)
            &&& roots@.len() == 0 ==> mixed_function_success(body, &layouts, forms@, bindings@, output_widths@, output_drivers@,
                gate_limit, &value, steps@)
            &&& wiring_trace_uses_mode(steps@, nested)
            &&& (nested.is_none() ==> flat_wiring_trace(steps@))
            &&& forall|arguments: Seq<ProjectedCallArgument>| #![trigger wiring_trace_arguments_match(steps@, arguments)]
                (nested.is_none() || (nested matches Some(mode) && mode._arguments@ == arguments))
                    ==> wiring_trace_arguments_match(steps@, arguments)
        },
        Err(error) => rooted_body_failed(body, &layouts, forms@, bindings@, roots@, gate_limit, nested, error)
            && (roots@.len() == 0 ==> mixed_body_failed(body, &layouts, forms@, bindings@, gate_limit, nested, error)),
    },
{
    proof {
        vstd::slice::axiom_spec_len(bindings);
        vstd::slice::axiom_spec_len(roots);
    }
    let (state, Ghost(steps)) = match lower_mixed_body(body, &layouts, forms, bindings, roots, layout_limit, gate_limit, nested, Ghost(context)) {
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
    assert forall|arguments: Seq<ProjectedCallArgument>|
        nested.is_none() || (nested matches Some(mode) && mode._arguments@ == arguments) implies
        #[trigger] wiring_trace_arguments_match(steps, arguments) by {
        reveal(wiring_trace_arguments_match);
        assert forall|i: int| 0 <= i < steps.len() implies ((#[trigger] steps[i]).nested matches Some(step)
            ==> step.arguments == arguments) by {
            assert(wiring_step_uses_mode(steps[i], nested));
        };
    };
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

/// 一時配線を使う子呼び出しがあるか、解決済みの一覧から調べる。
fn selected_has_child_calls(selected: &[ResolvedTemplateCall]) -> (present: bool)
    ensures present <==> exists|i: int| 0 <= i < selected@.len() && (#[trigger] selected@[i]).children@.len() > 0,
{
    let mut i = 0;
    while i < selected.len()
        invariant i <= selected@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] selected@[j]).children@.len() == 0,
        decreases selected@.len() - i,
    {
        if !selected[i].children.is_empty() {
            return true;
        }
        i += 1;
    }
    false
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
    Ghost(templates): Ghost<&FunctionTemplates<'p, 'a>>,
) -> (result: Result<(LoweredBitFunc, Ghost<Seq<WiringStep>>), MixedWiringError<'p, 'a>>)
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*context.0, context.1.0, context.1.1, context.1.2, context.2),
        body_definition_layouts(body.input_widths@, body.definitions@, layout_limit, &layouts),
        widths_layout(output_widths@, layout_limit, &layouts.outputs),
        output_widths@.len() == output_drivers@.len(),
        forall|p: int| 0 <= p < output_widths@.len() ==>
            bit_driver_width(body.input_widths@, body.definitions@, #[trigger] output_drivers@[p]) == Some(output_widths@[p]),
        aliases.expansion_selection_matches(context.0, templates, context.1, context.2, selected@),
        forall|g: int| 0 <= g < selected@.len() ==>
            resolved_call_fits_body(#[trigger] selected@[g], body.input_widths@, body.definitions@, forms@, context.1.2),
        forall|slot: int| 0 <= slot < body.definitions@.len() && !call_covers(context.2.calls@, slot) ==>
            bit_definition_matches(body.input_widths@, body.definitions@.take(slot), #[trigger] body.definitions@[slot]),
    ensures exists|bindings: Seq<CallBinding>|
        #[trigger] bindings_match_calls(bindings, selected@)
            && mixed_function_result(body, &layouts, forms@, bindings, output_widths@, output_drivers@,
                context.2.projections.call_arguments.arguments@, gate_limit, result),
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
    let builtin = if selected_has_child_calls(selected) { Some(builtin_nor_call()) } else { None };
    let ghost arguments = context.2.projections.call_arguments.arguments@;
    let nested = match &builtin {
        Some(builtin) => Some(NestedWiring { selected, builtin, child_limit: child_output_limit(), _arguments: Ghost(arguments) }),
        None => None,
    };
    assert(resolved_mixed_mode_matches(bindings@, arguments, nested)) by {
        if nested.is_none() {
            assert forall|i: int| 0 <= i < bindings@.len() implies
                (#[trigger] bindings@[i])._selection@.children@.len() == 0 by {
                assert(bindings@[i]._selection@ == selected@[i]);
            };
        }
    };
    let roots: &[NorBinding] = &[];
    assert(roots@ =~= Seq::empty());
    let raw = lower_mixed_function_with_mode(body, layouts, forms, bindings.as_slice(), roots,
        output_widths, output_drivers, layout_limit, gate_limit, nested,
        Ghost(Some((aliases, context.0, templates, context.1, context.2))));
    let result = match raw {
        Ok(lowered) => {
            assert(resolved_mixed_trace(bindings@, arguments, lowered.1@)) by {
                assert(wiring_trace_uses_mode(lowered.1@, nested));
            };
            Ok(lowered)
        },
        Err(error) => {
            let ghost cause = error;
            let diagnostic = normalize_mixed_wiring_diagnostic(error);
            assert(mixed_function_failure(body, &layouts, forms@, bindings@, arguments, gate_limit, diagnostic)) by {
                assert(mixed_body_failed(body, &layouts, forms@, bindings@, gate_limit, nested, cause));
            };
            Err(diagnostic)
        },
    };
    assert(exists|rows: Seq<CallBinding>| #[trigger] bindings_match_calls(rows, selected@)
        && mixed_function_result(body, &layouts, forms@, rows, output_widths@, output_drivers@, arguments, gate_limit, result)) by {
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
        Ghost((&plan, (0usize, 1usize, 8u64), &prepared)), Ghost(&templates),
    ) else {
        panic!("expected the caller NOR to exceed the gate limit");
    };
    assert_eq!(&source.text[site.span], "(nor final final)");

    let layout = prepare_body_layouts(body.input_widths, body.definitions, output_widths, 16).unwrap();
    let (lowered, _) = lower_resolved_function(
        &aliases, &body, layout, forms, selected.as_slice(), output_widths, output_drivers, 16, 3,
        Ghost((&plan, (0usize, 1usize, 8u64), &prepared)), Ghost(&templates),
    ).unwrap();
    assert_eq!(lowered.gate_definitions(), [0, 2, 4]);
    assert_eq!(lowered.netlist().evaluate(&[true, false, true, false, true]).unwrap(), [false]);
    assert_eq!(lowered.netlist().evaluate(&[true, false, true, false, false]).unwrap(), [true]);
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn mixed_body_lowers_a_child_then_uses_the_root_output() {
    check_mixed_body_nested_fixture(
        "(using nor) (func id (in a) (out a))
               (func caller (in a) (out y)
                   (def earlier (id 0))
                   (def nested (id (nor earlier a)))
                   (def y (nor nested nested)))",
        None,
    );
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn mixed_body_reports_the_original_argument_before_child_capacity() {
    check_mixed_body_nested_fixture(
        "(using nor) (func id (in a) (out a))
               (func caller (in a) (out y)
                   (def earlier (id 0))
                   (def nested (id (nor (nor earlier a) (bit earlier 0))))
                   (def y (nor nested nested)))",
        Some("(nor (nor earlier a) (bit earlier 0))"),
    );
}

#[cfg(all(test, not(verus_only)))]
fn check_mixed_body_nested_fixture(text: &str, deferred: Option<&str>) {
    use super::call_arguments::{ChildCallWiringError, builtin_nor_call};
    use crate::project::{FuncWiringResult, SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    let project = parse_circuit_project(&[SourceSnapshot {
        path: "nested-mixed.ncg2",
        revision: 1,
        text,
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let mut templates = aliases.new_function_templates(&plan, Ghost(1u64));
    let id = plan.get(0).unwrap();
    let checked = aliases.check_bit_func(id.0, id.1, 1).unwrap();
    let circuit = checked.lower_bit_func(1).unwrap();
    let template = aliases.standalone_function_template(id, 1, checked, circuit, 1);
    aliases.insert_function_template(&plan, &mut templates, template, Ghost(1u64));

    let caller = plan.get(1).unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, caller.0, caller.1, 1).unwrap();
    let FuncWiringResult::Checked(wiring) = &prepared.typed.literals.wiring else {
        panic!("expected checked output drivers");
    };
    let selected = aliases.resolve_template_calls(&plan, &templates, &prepared.calls,
        &prepared.projections.call_arguments.arguments, Ghost(prepared), Ghost((caller.0, caller.1, 1u64)));
    let source = &project.sources()[caller.0];
    let parsed = &project.circuits()[caller.0];
    let forms = &parsed.syntax.forms;
    let mut definitions: Vec<_> = selected.iter().enumerate().map(|(group, call)| CheckedBitDefinition {
        expression: copy_location(&call.group.expression), width: 1,
        rhs: BitFuncRhs::CallOutput { group, port: 0 }, operands: Vec::new(),
    }).collect();
    let nested = SingleBitOperand::Driver(OutputDriver::Definition(1));
    definitions.push(CheckedBitDefinition {
        expression: crate::project::circuits::form_location(source, forms, parsed.definitions[2].expression.start),
        width: 1, rhs: BitFuncRhs::Nor { left: nested, right: nested }, operands: Vec::new(),
    });
    let body = LoweringBody { input_widths: &[1], definitions: &definitions };
    let layouts = prepare_body_layouts(&[1], &definitions, &[1], 3).unwrap();
    let bindings = bind_resolved_calls(&aliases, &selected, &body, &layouts, Ghost(forms@), Ghost(3usize),
        Ghost((&plan, (caller.0, caller.1, 1u64), &prepared)));
    let builtin = builtin_nor_call();
    let lower = |gate_limit| lower_mixed_function_with_mode(&body,
        prepare_body_layouts(&[1], &definitions, &[1], 3).unwrap(), forms, &bindings, &[], &[1], wiring.drivers.outputs.as_slice(),
        3, gate_limit,
        Some(NestedWiring { selected: &selected, builtin: &builtin, child_limit: 1,
            _arguments: Ghost(prepared.projections.call_arguments.arguments@) }),
        Ghost(Some((&aliases, &plan, &templates, (caller.0, caller.1, 1u64), &prepared))));

    if let Some(expected) = deferred {
        assert!(selected[1].children.len() > 1);
        let Err(MixedBodyError::Flat(MixedWiringError::Call(CallGroupError::DeferredArgument(site)))) = lower(0)
            else { panic!("expected the original argument diagnostic"); };
        assert_eq!(&site.source.text[site.span], expected);
        return;
    }
    let Err(MixedBodyError::Nested(_, NestedCallWiringError::Child(0, ChildCallWiringError::GateCapacity(site)))) = lower(0)
        else { panic!("expected the child call to reach the gate limit"); };
    assert_eq!(&site.source.text[site.span], "(nor earlier a)");
    let Ok((circuit, _)) = lower(2) else { panic!("expected a wired body"); };
    assert_eq!(circuit.gate_definitions(), [1, 2]);
    let netlist = circuit.netlist();
    assert_eq!(netlist.evaluate(&[false]).unwrap(), [false]);
    assert_eq!(netlist.evaluate(&[true]).unwrap(), [true]);
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn mixed_function_wires_a_nor_root_between_a_function_call_and_a_local_definition() {
    use crate::project::{FuncWiringResult, SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    let text = "(using nor) (func id (in a) (out a))
        (func caller (in a) (out y)
            (def earlier (id 0))
            (def nested (nor (id a) earlier))
            (def y (nor nested nested)))";
    let project = parse_circuit_project(&[SourceSnapshot { path: "rooted-mixed.ncg2", revision: 1, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let mut templates = aliases.new_function_templates(&plan, Ghost(1u64));
    let id = plan.get(0).unwrap();
    let checked = aliases.check_bit_func(id.0, id.1, 1).unwrap();
    let circuit = checked.lower_bit_func(1).unwrap();
    let template = aliases.standalone_function_template(id, 1, checked, circuit, 1);
    aliases.insert_function_template(&plan, &mut templates, template, Ghost(1u64));
    let caller = plan.get(1).unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, caller.0, caller.1, 1).unwrap();
    let FuncWiringResult::Checked(wiring) = &prepared.typed.literals.wiring else {
        panic!("expected checked output drivers");
    };
    let arguments = &prepared.projections.call_arguments.arguments;
    let selected = aliases.resolve_template_calls(&plan, &templates, &prepared.calls, arguments,
        Ghost(prepared), Ghost((caller.0, caller.1, 1u64)));
    let parsed = &project.circuits()[caller.0];
    let forms = &parsed.syntax.forms;
    let source = &project.sources()[caller.0];
    let root = &prepared.nor_roots[0];
    let nor = aliases.resolve_nor_root(&plan, &templates, root, arguments,
        Ghost((caller.0, caller.1, 1u64)), Ghost(&prepared), Ghost(0int));
    let roots = [NorBinding { candidate: 0, selected: nor, references: &parsed.definitions[root.definition].references }];
    let input = SingleBitOperand::Driver(OutputDriver::Definition(1));
    let definitions = [
        CheckedBitDefinition { expression: copy_location(&selected[0].group.expression), width: 1,
            rhs: BitFuncRhs::CallOutput { group: 0, port: 0 }, operands: Vec::new() },
        CheckedBitDefinition { expression: copy_location(&root.root.expression), width: 1,
            rhs: BitFuncRhs::NorCallOutput { root: 0 }, operands: Vec::new() },
        CheckedBitDefinition { expression: crate::project::circuits::form_location(source, forms,
            parsed.definitions[root.definition + 1].expression.start), width: 1,
            rhs: BitFuncRhs::Nor { left: input, right: input }, operands: Vec::new() },
    ];
    let body = LoweringBody { input_widths: &[1], definitions: &definitions };
    let layouts = prepare_body_layouts(&[1], &definitions, &[1], 3).unwrap();
    let bindings = bind_resolved_calls(&aliases, &selected, &body, &layouts, Ghost(forms@), Ghost(3usize),
        Ghost((&plan, (caller.0, caller.1, 1u64), &prepared)));
    let builtin = builtin_nor_call();
    let mode = Some(NestedWiring { selected: &selected, builtin: &builtin, child_limit: 1, _arguments: Ghost(arguments@) });
    let lower = |gate_limit| lower_mixed_function_with_mode(&body,
        prepare_body_layouts(&[1], &definitions, &[1], 3).unwrap(), forms, &bindings, &roots,
        &[1], wiring.drivers.outputs.as_slice(), 3, gate_limit, mode,
        Ghost(Some((&aliases, &plan, &templates, (caller.0, caller.1, 1u64), &prepared))));
    let Err(raw) = lower(0) else { panic!("expected root capacity error"); };
    assert!(matches!(&raw, MixedBodyError::Nor(_, NestedCallWiringError::Root(CallWiringError::GateCapacity))));
    let MixedWiringError::Call(CallGroupError::GateCapacity(site)) = normalize_mixed_wiring_diagnostic(raw)
        else { panic!("expected the root diagnostic"); };
    assert_eq!(&text[site.span], "(nor (id a) earlier)");
    let Err(MixedBodyError::Flat(MixedWiringError::LocalGateCapacity(site))) = lower(1)
        else { panic!("expected the later local capacity error"); };
    assert_eq!(&text[site.span], "(nor nested nested)");
    let Ok((circuit, _)) = lower(2) else { panic!("expected a wired function"); };
    assert_eq!(circuit.definition_wires, [Wire::Constant(false), Wire::Gate(0), Wire::Gate(1)]);
    assert_eq!(circuit.gate_definitions(), [1, 2]);
    let netlist = circuit.netlist();
    assert_eq!(netlist.outputs, [Wire::Gate(1)]);
    assert_eq!(netlist.evaluate(&[false]).unwrap(), [false]);
    assert_eq!(netlist.evaluate(&[true]).unwrap(), [true]);
}

} // verus!
