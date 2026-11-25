//! 成功した呼び出しの配線履歴から、実引数の条件を取り出す。

use super::*;
use super::super::super::call_arguments::{argument_prefix_wires, argument_source_available};
use super::super::super::call_group::{call_group_wires_match, flat_call_group_wiring};

verus! {

/// 入れ子の展開では根と子の引数が確定し、直接配線では根の全引数をその場で配線できる。
pub(in crate::project::use_aliases::bit_func) closed spec fn source_call_step_arguments(
    step: WiringStep, call: ResolvedTemplateCall,
) -> bool {
    if step.nested.is_some() {
        nested_arguments_ready(&call)
    } else {
        forall|port: int| 0 <= port < call.arguments@.len() ==>
            (#[trigger] call.arguments@[port]).source.has_direct_wires()
    }
}

/// 一段の呼び出しが成功したとき、履歴の展開方式に応じた実引数の条件を示す。
#[verifier::spinoff_prover]
pub(in crate::project::use_aliases::bit_func::lowering) proof fn rooted_source_call_mode(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, arguments: Seq<ProjectedCallArgument>,
    limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, final_wiring: WiringView,
    at: int, index: int,
)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring),
        resolved_mixed_trace(bindings, roots, arguments, steps),
        bindings_match_calls(bindings, selected),
        0 <= at < steps.len(), 0 <= index < selected.len(),
        source_step_target(steps[at]) == SourceStepTarget::Function(index),
    ensures
        source_call_step_arguments(steps[at], selected[index]),
        nested_arguments_ready(&selected[index]) || (forall|port: int| 0 <= port < selected[index].arguments@.len() ==>
            (#[trigger] selected[index].arguments@[port]).source.has_direct_wires()),
{
    let step = steps[at];
    let call = selected[index];
    reveal(source_step_target);
    let binding = bindings[index];
    assert(binding_matches_selection(binding, call));

    if step.nested.is_some() {
        reveal(resolved_mixed_trace);
        let mode = choose|mode: Option<NestedWiring>| #[trigger] wiring_trace_uses_mode(steps, mode)
            && resolved_mixed_mode_matches(bindings, roots, arguments, mode);
        assert(wiring_step_uses_mode(step, mode));
        assert(mode.is_some());
        let active = mode->Some_0;
        assert(binding_matches_selection(binding, active.selected@[index]));
        assert(active.selected@[index] == call);
        assert(nested_arguments_ready(&call));
    } else {
        assert(wiring_step_valid(body, layouts, forms, bindings, limit, step)) by {
            reveal(rooted_mixed_trace);
        };
        reveal(wiring_step_valid);
        let widths = definition_widths(body.definitions@);
        let (invocation, mapped, outputs) = flat_call_group_wiring(binding.group, forms, binding.arguments@,
            layouts, binding.callee, step.before, step.after, limit, widths, binding._output_widths@);
        assert(call_group_wires_match(binding.group, forms, binding.arguments@, layouts, binding.callee,
            step.before, step.after, binding._output_widths@, invocation, mapped, outputs));
        let ranges = binding.callee.input_layout_model().ranges_model();
        assert(argument_prefix_wires(&invocation, call.arguments@, ranges, call.arguments@.len() as int, mapped));
        assert forall|port: int| 0 <= port < call.arguments@.len() implies
            (#[trigger] call.arguments@[port]).source.has_direct_wires() by {
            reveal(argument_prefix_wires);
            let source = call.arguments@[port].source;
            assert(ranges[port].end <= mapped.len());
            assert(argument_source_available(&invocation, source));
            assert(invocation.child_ranges@.len() == 0);
        };
    }
}

} // verus!
