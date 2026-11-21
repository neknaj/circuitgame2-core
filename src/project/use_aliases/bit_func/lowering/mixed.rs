//! 通常の定義と関数呼び出しを、同じ配線列へ定義順に変換する。

use super::*;
use super::super::expansion::CheckedExpansionCall;
use super::super::super::call_arity::ProjectedCallArgument;
use super::call_group::{BodyWiring, CallGroupError, lower_call_group};
use crate::syntax::Form;
#[cfg(verus_only)]
use super::call_group::{WiringView, call_group_result};
#[cfg(verus_only)]
use super::call_arguments::layout_argument_ready;
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
pub(super) enum MixedWiringError<'p, 'a> {
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
    ensures match result {
        Ok((value, steps)) => {
            &&& value.layouts == layouts
            &&& value.netlist.input_count == layouts.inputs.total_bits_model()
            &&& value.netlist.outputs@.len() == layouts.outputs.total_bits_model()
            &&& value.definition_wires@.len() == layouts.definitions.total_bits_model()
            &&& value.netlist.gates@.len() == value.gate_definitions@.len() <= gate_limit
            &&& nor_evaluation_ready(&value.netlist, layouts.inputs.total_bits_model() as nat)
            &&& body_output_wiring_matches(output_drivers@, &layouts, value.definition_wires@, value.netlist.outputs@,
                output_widths@.len() as int)
            &&& mixed_trace(body, &layouts, forms@, bindings@, gate_limit, steps@, body.definitions@.len() as usize,
                bindings@.len() as usize, WiringView { definitions: value.definition_wires@,
                    gates: value.netlist.gates@, origins: value.gate_definitions@ })
        },
        Err(error) => exists|steps: Seq<WiringStep>, slot: usize, group: usize, wiring: WiringView|
            #[trigger] mixed_trace(body, &layouts, forms@, bindings@, gate_limit, steps, slot, group, wiring)
            && mixed_error_at(body, &layouts, forms@, bindings@, gate_limit, wiring, slot, group, error),
    },
{
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
#[cfg(all(test, not(verus_only)))]
#[test]
fn mixed_body_uses_a_call_output_in_the_next_nor() {
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
                   (def y (nor bit bit)))
               (func pair (in (a (bits 4)) b) (out (a (bits 4)) inverted)
                   (def inverted (nor b b)))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, 0, 1, 8).unwrap();
    let group = &prepared.calls[0];
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
    let callee = aliases.template_for_expansion_call(&plan, &templates, group,
        Ghost((0usize, 1usize, 8u64)), Ghost(&prepared), Ghost(0int));
    let binding = CallBinding {
        group,
        arguments: &prepared.projections.call_arguments.arguments[group.arguments.clone()],
        callee: &callee.circuit,
        _input_widths: Ghost(callee.inputs@),
        _output_widths: Ghost(callee.outputs@),
        _layout_limit: Ghost(8usize),
    };
    let bit = SingleBitOperand::Driver(OutputDriver::Definition(1));
    let slots = vec![
        CheckedBitDefinition { expression: copy_location(&group.expression), width: 4,
            rhs: BitFuncRhs::CallOutput { group: 0, port: 0 }, operands: Vec::new() },
        CheckedBitDefinition { expression: copy_location(&group.expression), width: 1,
            rhs: BitFuncRhs::CallOutput { group: 0, port: 1 }, operands: Vec::new() },
        CheckedBitDefinition { expression: form_location(source, forms, parsed.definitions[1].expression.start), width: 1,
            rhs: BitFuncRhs::Nor { left: bit, right: bit }, operands: Vec::new() },
    ];
    let FuncWiringResult::Checked(wiring) = &prepared.typed.literals.wiring else {
        panic!("expected checked caller wiring");
    };
    let ports = aliases.prepare_routine_ports(0, 1, 8, wiring, prepared.projections.layouts).unwrap();
    let body = LoweringBody { input_widths: ports.inputs.as_slice(), definitions: slots.as_slice() };
    let output_widths = ports.outputs.as_slice();
    let output_drivers = wiring.drivers.outputs.as_slice();
    let bindings = [binding];
    let limited = prepare_body_layouts(body.input_widths, body.definitions, output_widths, 8).unwrap();
    let Err(MixedWiringError::LocalGateCapacity(site)) = lower_mixed_function(&body, limited, forms, &bindings,
        output_widths, output_drivers, 8, 1) else {
        panic!("expected the second NOR to exceed the gate limit");
    };
    assert_eq!(&source.text[site.span], "(nor bit bit)");

    let layout = prepare_body_layouts(body.input_widths, body.definitions, output_widths, 8).unwrap();
    let (lowered, _) = lower_mixed_function(&body, layout, forms, &bindings, output_widths, output_drivers, 8, 2).unwrap();
    assert_eq!(lowered.gate_definitions(), [0, 2]);
    assert_eq!(lowered.netlist().evaluate(&[true, false, true, false, true]).unwrap(), [true]);
    assert_eq!(lowered.netlist().evaluate(&[true, false, true, false, false]).unwrap(), [false]);
}

} // verus!
