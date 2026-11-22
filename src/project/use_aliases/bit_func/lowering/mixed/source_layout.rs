//! コンパイラの配線履歴を、定義単位のソース配線の証明に渡す。

use super::*;
use super::super::call_arguments::source_wires::{
    SourceArguments, SourceChildModel, source_call_definition_wiring, source_child_site, source_gate_in_definition,
};
use super::super::source_calls::{
    nested_definition_source_wiring, nor_definition_source_wiring, source_definition_start, source_models_match_calls,
};
use super::super::source_calls::flat::flat_definition_source_wiring;
use super::super::source_calls::local::local_definition_source_wiring;
use super::super::source_wires::{source_definition_outputs, source_local_nor, source_local_wires};
use crate::netlist::{SourceNor, source_clocked_layout, source_wire_pair};
use crate::project::DefinitionPosition;

verus! {

/// 配線履歴の一段で変換した右辺の種類。呼び出しでは選択済みの列の添字を持つ。
pub(in crate::project::use_aliases::bit_func) enum SourceStepTarget {
    Local,
    Function(int),
    Nor(int),
}

/// 一つの右辺が書き込む左辺スロットの半開区間。
pub(in crate::project::use_aliases::bit_func) closed spec fn source_step_slots(step: WiringStep) -> Range<usize> {
    step.from..step.to
}

/// 履歴の呼び出しカーソルから、その段で変換した右辺を特定する。
pub(in crate::project::use_aliases::bit_func) closed spec fn source_step_target(step: WiringStep) -> SourceStepTarget {
    if step.nor_before != step.nor_after { SourceStepTarget::Nor(step.nor_before as int) }
    else if step.group_before != step.group_after { SourceStepTarget::Function(step.group_before as int) }
    else { SourceStepTarget::Local }
}

/// この定義の直前に確定した配線。
pub(in crate::project::use_aliases::bit_func::lowering) closed spec fn source_step_before(step: WiringStep) -> WiringView {
    step.before
}

/// この定義を追加した直後の配線。
pub(in crate::project::use_aliases::bit_func::lowering) closed spec fn source_step_after(step: WiringStep) -> WiringView {
    step.after
}

/// 展開履歴のスロット区間を、型検査で選んだ右辺に対応付ける。
pub(in crate::project::use_aliases::bit_func) closed spec fn source_step_range_matches(
    step: WiringStep, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, count: nat,
) -> bool {
    let slots = source_step_slots(step);
    &&& slots.start < slots.end <= count
    &&& match source_step_target(step) {
        SourceStepTarget::Local => slots.end == slots.start + 1
            && !nor_binding_covers(roots, slots.start as int)
            && !call_covers(Seq::new(selected.len(), |i: int| *selected[i].group), slots.start as int),
        SourceStepTarget::Function(i) => 0 <= i < selected.len() && slots == selected[i].group.outputs,
        SourceStepTarget::Nor(i) => 0 <= i < roots.len() && slots.start == roots[i].selected.prepared.output_slot
            && slots.end == slots.start + 1,
    }
}

/// ゲートを一つも追加しない段も含め、履歴の各段が書き込んだ左辺を取り出す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn rooted_source_step_range(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, limit: usize, steps: Seq<WiringStep>,
    slot: usize, group: usize, nor: usize, wiring: WiringView, at: int,
)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, wiring),
        bindings_match_calls(bindings, selected), 0 <= at < steps.len(),
    ensures source_step_range_matches(steps[at], selected, roots, body.definitions@.len()),
{
    reveal(rooted_mixed_trace);
    reveal(wiring_step_valid);
    reveal(nor_wiring_step_valid);
    let step = steps[at];
    if source_step_target(step) is Local {
        let calls = Seq::new(selected.len(), |i: int| *selected[i].group);
        assert(!call_covers(calls, step.from as int)) by {
            if call_covers(calls, step.from as int) {
                let i = choose|i: int| 0 <= i < calls.len()
                    && (#[trigger] calls[i]).outputs.start <= step.from < calls[i].outputs.end;
                assert(binding_matches_selection(bindings[i], selected[i]));
                assert(*bindings[i].group == calls[i]);
                assert(binding_covers(bindings, step.from as int));
            }
        };
    } else if let SourceStepTarget::Function(i) = source_step_target(step) {
        assert(binding_matches_selection(bindings[i], selected[i]));
    }
}

/// 型付きの右辺と先行するソース配線から、この定義が追加する配線を求める。
pub(in crate::project::use_aliases::bit_func::lowering) closed spec fn source_step_layout(
    context: &SourceArguments, body: &LoweringBody, target: SourceStepTarget,
    selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, definition: DefinitionPosition,
    prior: Seq<SourceGateId>, ordinary: Option<SourceChildModel>, children: Seq<Option<SourceChildModel>>,
) -> Option<(Seq<SourceGateId>, Seq<SourceNor>, Seq<Seq<SourceWire>>)> {
    match target {
        SourceStepTarget::Local => {
            let slot = body.definitions@[context.definitions.len() as int];
            let gate = SourceGateId { instance: Seq::empty(), gate: source_child_site(definition, 0) };
            if let Some(wires) = source_local_wires(context.input_widths, context.definitions, slot, gate) {
                let (order, gates) = match slot.rhs {
                    BitFuncRhs::Nor { left, right } => (prior.push(gate), seq![source_local_nor(
                        context.input_widths, context.definitions, left, right)]),
                    _ => (prior, Seq::empty()),
                };
                Some((order, gates, context.definitions.push(wires)))
            } else { None }
        },
        SourceStepTarget::Function(index) => {
            let call = selected[index];
            let template = call.template;
            let ports = template.circuit_model().output_layout_model().ranges_model();
            if let Some((order, gates, wires)) = source_call_definition_wiring(context, definition,
                call.group.references.start, prior, call.children@, children, ordinary, call.arguments@, template.input_widths_model())
            {
                Some((order, gates, source_definition_outputs(context.definitions, wires, ports)))
            } else { None }
        },
        SourceStepTarget::Nor(index) => {
            let root = roots[index];
            if let Some((order, gates, wires)) = source_call_definition_wiring(context, definition,
                root.references.start, prior, root.selected.children@, children, None, root.selected.arguments@, seq![1u64, 1u64])
            {
                Some((order, gates, source_definition_outputs(context.definitions, wires, seq![0usize..1usize])))
            } else { None }
        },
    }
}

/// 成功履歴の一段を、該当する右辺のソース配線と照合する。
#[verifier::spinoff_prover]
pub(in crate::project::use_aliases::bit_func::lowering) proof fn rooted_source_step(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    bindings: Seq<CallBinding>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, limit: usize,
    steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, final_wiring: WiringView, at: int,
    definition: DefinitionPosition, prior: Seq<SourceGateId>, ordinary: Option<SourceChildModel>,
    children: Seq<Option<SourceChildModel>>, arguments: Seq<ProjectedCallArgument>,
) -> (result: (Seq<SourceGateId>, Seq<SourceNor>, Seq<Seq<SourceWire>>))
    requires
        rooted_mixed_trace(body, layouts, context.forms, bindings, roots, limit, steps, slot, group, nor, final_wiring),
        resolved_mixed_trace(bindings, roots, arguments, steps),
        bindings_match_calls(bindings, selected),
        0 <= at < steps.len(),
        source_definition_start(context, body, layouts, capacity, source_step_before(steps[at]), source_step_slots(steps[at]).start, definition, prior),
        ({
            let step = steps[at];
            let slots = source_step_slots(step);
            match source_step_target(step) {
                SourceStepTarget::Local => slots.start < body.definitions@.len()
                    && bit_definition_matches(body.input_widths@, body.definitions@.take(slots.start as int),
                        body.definitions@[slots.start as int]),
                SourceStepTarget::Function(index) => 0 <= index < selected.len() && {
                    let call = selected[index];
                    let template = call.template.circuit_model();
                    &&& context.source == call.group.expression.source
                    &&& resolved_call_fits_body(call, body.input_widths@, body.definitions@, context.forms, width_limit)
                    &&& source_models_match_calls(call.children@, children, call.group.references)
                    &&& (call.children@.len() > 0 ==> nested_arguments_ready(&call))
                    &&& ordinary matches Some(model)
                        && source_clocked_layout(&model.circuit, template.netlist_model(), model.order, model.index)
                },
                SourceStepTarget::Nor(index) => 0 <= index < roots.len() && {
                    let root = roots[index];
                    &&& nor_binding_fits_body(root, context.source, context.forms, body.input_widths@, body.definitions@, width_limit)
                    &&& source_models_match_calls(root.selected.children@, children, *root.references)
                },
            }
        }),
    ensures ({
        let step = steps[at];
        let (order, gates, definitions) = result;
        &&& source_step_range_matches(step, selected, roots, body.definitions@.len())
        &&& source_step_layout(context, body, source_step_target(step), selected, roots, definition, prior, ordinary, children) == Some(result)
        &&& order.take(prior.len() as int) == prior
        &&& order.len() == source_step_after(step).gates.len() == prior.len() + gates.len()
        &&& order.no_duplicates()
        &&& wiring_view_is_prefix(source_step_before(step), source_step_after(step))
        &&& definitions.len() == source_step_slots(step).end
        &&& definition_wires_pair(order, definitions, layouts.definitions.ranges_model(), source_step_after(step).definitions)
        &&& forall|i: int| 0 <= i < gates.len() ==> {
            let source = #[trigger] gates[i];
            let flat = source_step_after(step).gates[prior.len() + i];
            &&& source_gate_in_definition(definition, order[prior.len() + i])
            &&& source_wire_pair(order, source.left, flat.left)
            &&& source_wire_pair(order, source.right, flat.right)
        }
    }),
{
    rooted_source_step_range(body, layouts, context.forms, bindings, selected, roots, limit, steps,
        slot, group, nor, final_wiring, at);
    let step = steps[at];
    assert(if source_step_target(step) is Nor { nor_wiring_step_valid(body, layouts, context.forms, roots, limit, step) }
        else { wiring_step_valid(body, layouts, context.forms, bindings, limit, step) }) by {
        reveal(rooted_mixed_trace);
    };
    match source_step_target(step) {
        SourceStepTarget::Local => {
            reveal(wiring_step_valid);
            assert(local_step(body, layouts, step));
            let widths = definition_widths(body.definitions@);
            port_bit_layout_port(widths, capacity, layouts.definitions, step.from);
            assert(step.before.definitions.len() < step.after.definitions.len()) by {
                let span = layouts.definitions.ranges_model()[step.from as int];
                let slot = body.definitions@[step.from as int];
                assert(slot_wiring_matches(slot, layouts, step.after.definitions, step.after.gates, step.after.origins, step.from as int));
                assert(span.start == step.before.definitions.len());
            };
            local_definition_source_wiring(context, body, layouts, capacity, step.before, step.after,
                step.from, definition, prior)
        },
        SourceStepTarget::Function(index) => {
            reveal(wiring_step_valid);
            let binding = bindings[index];
            let call = selected[index];
            assert(binding_matches_selection(binding, call));
            reveal(binding_ready);
            assert(nor_evaluation_ready(call.template.circuit_model().netlist_model(),
                call.template.circuit_model().input_layout_model().total_bits_model() as nat));
            let model = ordinary->Some_0;
            if let Some(nested) = step.nested {
                nested_definition_source_wiring(context, body, layouts, capacity, width_limit, &call, &nested.builtin,
                    step.before, step.after, limit, nested.child_limit, definition, prior, children, model)
            } else {
                assert(call.children@.len() == 0) by {
                    reveal(resolved_mixed_trace);
                    let mode = choose|mode: Option<NestedWiring>| #[trigger] wiring_trace_uses_mode(steps, mode)
                        && resolved_mixed_mode_matches(bindings, roots, arguments, mode);
                    assert(wiring_step_uses_mode(step, mode));
                    if let Some(mode) = mode {
                        assert(mode.selected@[index] == call);
                        assert(!nested_arguments_ready(&call));
                    }
                };
                assert(children =~= Seq::empty());
                flat_definition_source_wiring(context, body, layouts, capacity, width_limit, &call,
                    step.before, step.after, limit, definition, prior, model)
            }
        },
        SourceStepTarget::Nor(index) => {
            reveal(nor_wiring_step_valid);
            let root = roots[index];
            let nested = step.nested->Some_0;
            nor_definition_source_wiring(context, body, layouts, capacity, width_limit, &root.selected,
                *root.references, &nested.builtin, step.before, step.after, limit, nested.child_limit, definition, prior, children)
        },
    }
}

} // verus!
