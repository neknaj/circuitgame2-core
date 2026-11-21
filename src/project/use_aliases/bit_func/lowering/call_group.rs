//! 呼び出しを一度展開し、出力とゲートの由来を呼び出し元へ追加する。

use super::super::expansion::CheckedExpansionCall;
use super::super::instances::append_instance_outputs;
use super::super::templates::{FunctionTemplates, ResolvedTemplateCall};
use super::call_arguments::{CallWiringError, CallerArguments, lower_projected_call};
use super::call_arguments::child_calls::{NestedCallWiringError, bind_child_calls, lower_root_with_children};
use super::{Layouts, LoweredBitFunc, LoweringBody, NorGate, Wire, Vec};
use super::super::super::call_arity::ProjectedCallArgument;
use super::super::super::function_atoms::copy_location;
use crate::project::{FunctionExpansionOrder, LocatedName, UseAliases};
use crate::syntax::Form;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::call_arguments::{argument_prefix_wires, argument_wires_ready, layout_argument_ready};
#[cfg(verus_only)]
use super::call_arguments::child_calls::{
    ChildCall, NestedRootEvaluation, child_call_binding, child_call_ready, nested_root_values,
    nested_root_wiring_result, root_arguments_fit_children,
};
#[cfg(verus_only)]
use super::mixed::resolved_call_fits_body;
#[cfg(verus_only)]
use super::super::instances::{
    call_output_range_matches, instance_evaluates_from_caller, instance_gates_match, instance_outputs_match, instance_wire_values,
};
#[cfg(verus_only)]
use super::{existing_wires_keep_availability, wires_available};
#[cfg(verus_only)]
use crate::netlist::{
    gate_values_match, gates_available, nor_evaluation, nor_evaluation_ready, output_ports_available, output_values_match,
    port_bit_layout_port, port_bit_layout_result, port_bit_layout_size, preceding_port_bits, wire_available, wire_value,
};
use crate::netlist::{NorNetlist, PortBitLayout};
#[cfg(verus_only)]
use crate::project::circuits::is_form_location;
#[cfg(verus_only)]
use crate::syntax::form_spans_valid;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 呼び出し元の処理済み定義の配線、ゲート列、各ゲートを追加した定義の番号。
pub(super) struct BodyWiring {
    pub(super) definitions: Vec<Wire>,
    pub(super) gates: Vec<NorGate>,
    pub(super) origins: Vec<usize>,
}

/// 呼び出しの展開で検出した、元ソース位置付きの失敗。
#[derive(Debug)]
pub(in crate::project::use_aliases::bit_func) enum CallGroupError<'p, 'a> {
    /// 配線を確定できなかった引数の範囲。
    DeferredArgument(LocatedName<'p, 'a>),
    /// ゲート数の上限を超えた呼び出し式の範囲。
    GateCapacity(LocatedName<'p, 'a>),
}

#[cfg(verus_only)]
pub(super) struct WiringView {
    pub(super) definitions: Seq<Wire>,
    pub(super) gates: Seq<NorGate>,
    pub(super) origins: Seq<usize>,
}

impl BodyWiring {
    pub(super) open spec fn model(&self) -> WiringView {
        WiringView { definitions: self.definitions@, gates: self.gates@, origins: self.origins@ }
    }
}

pub(super) open spec fn call_group_wires_match(
    group: &CheckedExpansionCall, forms: Seq<Form>, arguments: Seq<ProjectedCallArgument>,
    caller: &Layouts, callee: &LoweredBitFunc, before: WiringView, after: WiringView, output_widths: Seq<u64>,
    invocation: CallerArguments, mapped: Seq<Wire>, outputs: Seq<Wire>,
) -> bool {
    &&& argument_prefix_wires(&invocation, arguments, callee.input_layout_model().ranges_model(),
        arguments.len() as int, mapped)
    &&& invocation.source == group.expression.source && invocation.forms@ == forms
    &&& invocation.inputs@ == caller.inputs.ranges_model()
    &&& invocation.definitions@ == caller.definitions.ranges_model()
    &&& invocation.wires@ == before.definitions
    &&& invocation.child_ranges@.len() == 0
    &&& mapped.len() == callee.input_layout_model().total_bits_model()
    &&& wires_available(mapped, caller.inputs.total_bits_model(), before.gates.len())
    &&& instance_gates_match(before.gates, callee.netlist_model().gates@, mapped, after.gates)
    &&& instance_outputs_match(callee.netlist_model().outputs@, mapped, before.gates.len() as usize, outputs)
    &&& after.definitions == before.definitions + outputs
    &&& forall|port: int, bit: int|
        #![trigger after.definitions[caller.definitions.ranges_model()[group.outputs.start + port].start + bit]]
        0 <= port < output_widths.len() && 0 <= bit < output_widths[port] ==>
            after.definitions[caller.definitions.ranges_model()[group.outputs.start + port].start + bit]
                == outputs[callee.output_layout_model().ranges_model()[port].start + bit]
}

pub(super) open spec fn call_group_result(
    group: &CheckedExpansionCall, forms: Seq<Form>, arguments: Seq<ProjectedCallArgument>,
    caller: &Layouts, callee: &LoweredBitFunc, before: WiringView, after: WiringView,
    gate_limit: usize, destination_widths: Seq<u64>, output_widths: Seq<u64>,
    result: Result<(), CallGroupError>,
) -> bool {
    match result {
        Ok(()) => {
            &&& after.gates.len() == before.gates.len() + callee.netlist_model().gates@.len() <= gate_limit
            &&& after.origins.len() == after.gates.len()
            &&& after.origins.take(before.origins.len() as int) == before.origins
            &&& forall|i: int| before.origins.len() <= i < after.origins.len() ==>
                (#[trigger] after.origins[i]) == group.outputs.start
            &&& after.definitions.len() == preceding_port_bits(destination_widths, group.outputs.end as nat)
            &&& gates_available(after.gates, caller.inputs.total_bits_model() as nat, after.gates.len() as int)
            &&& wires_available(after.definitions, caller.inputs.total_bits_model(), after.gates.len())
            &&& exists|invocation: CallerArguments, mapped: Seq<Wire>, outputs: Seq<Wire>|
                #[trigger] call_group_wires_match(group, forms, arguments, caller, callee, before, after,
                    output_widths, invocation, mapped, outputs)
        },
        Err(error) => {
            &&& after.definitions == before.definitions
            &&& after.gates == before.gates
            &&& after.origins == before.origins
            &&& match error {
                CallGroupError::DeferredArgument(site) => exists|port: int| 0 <= port < arguments.len()
                    && !(#[trigger] arguments[port]).source.has_direct_wires()
                    && is_form_location(group.expression.source, forms[arguments[port].form as int], site)
                    && forall|earlier: int| 0 <= earlier < port ==> (#[trigger] arguments[earlier]).source.has_direct_wires(),
                CallGroupError::GateCapacity(site) => site == group.expression
                    && before.gates.len() + callee.netlist_model().gates@.len() > gate_limit
                    && forall|port: int| 0 <= port < arguments.len() ==> (#[trigger] arguments[port]).source.has_direct_wires(),
            }
        },
    }
}

pub(super) open spec fn call_output_bit_has_value(
    caller: &Layouts, callee: &LoweredBitFunc, definitions: Seq<Wire>, first: usize, port: int, bit: int,
    inputs: Seq<bool>, values: Seq<bool>, outputs: Seq<bool>,
) -> bool {
    let dst = caller.definitions.ranges_model()[first + port].start + bit;
    let src = callee.output_layout_model().ranges_model()[port].start + bit;
    &&& 0 <= dst < definitions.len()
    &&& 0 <= src < outputs.len()
    &&& wire_available(definitions[dst], inputs.len(), values.len())
    &&& outputs[src] == wire_value(definitions[dst], inputs, values)
}

/// 呼び出し元の評価から一回の呼び出しの入力値と出力値を取り出す。
/// 引数列との対応と、各出力ビットを受け取る左辺との対応を保持する。
pub(super) proof fn call_group_values(
    group: &CheckedExpansionCall, forms: Seq<Form>, arguments: Seq<ProjectedCallArgument>,
    caller: &Layouts, callee: &LoweredBitFunc, before: WiringView, after: WiringView, gate_limit: usize,
    destination_widths: Seq<u64>, output_widths: Seq<u64>, destination_limit: usize, output_limit: usize,
    combined: Seq<NorGate>, inputs: Seq<bool>, values: Seq<bool>,
) -> (result: (Seq<bool>, Seq<bool>))
    requires
        call_group_result(group, forms, arguments, caller, callee, before, after,
            gate_limit, destination_widths, output_widths, Ok(())),
        after.gates.len() <= combined.len() && after.gates == combined.take(after.gates.len() as int),
        gate_values_match(inputs, combined, values), values.len() == combined.len() <= usize::MAX,
        inputs.len() == caller.inputs.total_bits_model(),
        nor_evaluation_ready(callee.netlist_model(), callee.input_layout_model().total_bits_model() as nat),
        port_bit_layout_result(destination_widths, destination_limit, Ok(caller.definitions)),
        port_bit_layout_result(output_widths, output_limit, Ok(*callee.output_layout_model())),
        group.outputs.start + output_widths.len() == group.outputs.end <= destination_widths.len(),
        before.definitions.len() == preceding_port_bits(destination_widths, group.outputs.start as nat),
        forall|i: int| 0 <= i < output_widths.len() ==> destination_widths[group.outputs.start + i] == #[trigger] output_widths[i],
        callee.netlist_model().outputs@.len() == callee.output_layout_model().total_bits_model(),
    ensures
        nor_evaluation(callee.netlist_model(), result.0, result.1),
        exists|invocation: CallerArguments, mapped: Seq<Wire>, outputs: Seq<Wire>|
            #[trigger] call_group_wires_match(group, forms, arguments, caller, callee, before, after, output_widths,
                invocation, mapped, outputs)
            && result.0 == instance_wire_values(mapped, inputs, values)
            && result.1 == instance_wire_values(outputs, inputs, values)
            && output_values_match(inputs, values, outputs, result.1),
        forall|port: int, bit: int| 0 <= port < output_widths.len() && 0 <= bit < output_widths[port] ==>
            #[trigger] call_output_bit_has_value(caller, callee, after.definitions, group.outputs.start, port, bit,
                inputs, values, result.1),
{
    let (invocation, mapped, outputs) = choose|invocation: CallerArguments, mapped: Seq<Wire>, outputs: Seq<Wire>|
        #[trigger] call_group_wires_match(group, forms, arguments, caller, callee, before, after, output_widths,
            invocation, mapped, outputs);
    reveal(wires_available);
    instance_evaluates_from_caller(before.gates, callee.netlist_model(), combined, mapped, outputs, inputs, values);
    let input_values = instance_wire_values(mapped, inputs, values);
    let output_values = instance_wire_values(outputs, inputs, values);
    port_bit_layout_size(output_widths, output_limit, callee.output_layout_model());
    assert forall|port: int, bit: int| 0 <= port < output_widths.len() && 0 <= bit < output_widths[port]
        implies #[trigger] call_output_bit_has_value(caller, callee, after.definitions, group.outputs.start, port, bit,
            inputs, values, output_values) by {
        port_bit_layout_port(output_widths, output_limit, *callee.output_layout_model(), port as usize);
        call_output_range_matches(destination_widths, output_widths, group.outputs.start, port as usize,
            caller.definitions, *callee.output_layout_model(), destination_limit, output_limit);
        let dst = caller.definitions.ranges_model()[group.outputs.start + port].start + bit;
        let range = callee.output_layout_model().ranges_model()[port];
        let src = range.start + bit;
        assert(0 <= src < outputs.len());
        assert(dst == before.definitions.len() + src);
        assert(dst < after.definitions.len());
        assert(after.definitions[dst] == outputs[src]);
        assert(wire_available(outputs[src], inputs.len(), values.len()));
    };
    (input_values, output_values)
}

fn append_call_origins(origins: &mut Vec<usize>, total: usize, first: usize)
    requires old(origins)@.len() <= total,
    ensures
        final(origins)@.len() == total,
        final(origins)@.take(old(origins)@.len() as int) == old(origins)@,
        forall|i: int| old(origins)@.len() <= i < total ==> (#[trigger] final(origins)@[i]) == first,
{
    let ghost before = origins@;
    assert(origins@.take(before.len() as int) =~= before);
    while origins.len() < total
        invariant
            before.len() <= origins@.len() <= total,
            origins@.take(before.len() as int) == before,
            forall|i: int| before.len() <= i < origins@.len() ==> (#[trigger] origins@[i]) == first,
        decreases total - origins@.len(),
    {
        let ghost prior = origins@;
        origins.push(first);
        assert(origins@.take(before.len() as int) =~= before);
        assert forall|i: int| before.len() <= i < origins@.len() implies (#[trigger] origins@[i]) == first by {
            if i < prior.len() { assert(origins@[i] == prior[i]); }
        };
    }
}

/// 呼び出し先のゲートと全出力を一度追加し、新しいゲートを呼び出し元の定義に対応付ける。
///
/// # Errors
///
/// 引数の配線を確定できない場合は引数順で最初の範囲を返す。すべて確定していてゲート数が上限を
/// 超える場合は、呼び出し式の範囲を返す。どちらの場合も追加前の配線、ゲート、由来を保つ。
pub(super) fn lower_call_group<'s, 'p, 'a>(
    group: &CheckedExpansionCall<'p, 'a>, forms: &'s [Form], arguments: &[ProjectedCallArgument],
    caller: &Layouts, callee: &LoweredBitFunc, state: &mut BodyWiring, gate_limit: usize,
    Ghost(destination_widths): Ghost<Seq<u64>>, Ghost(input_widths): Ghost<Seq<u64>>,
    Ghost(output_widths): Ghost<Seq<u64>>, Ghost(caller_limit): Ghost<usize>, Ghost(callee_limit): Ghost<usize>,
) -> (result: Result<(), CallGroupError<'p, 'a>>)
    requires
        form_spans_valid(group.expression.source.text, forms@, group.expression.source.text.spec_bytes().len() as int),
        port_bit_layout_result(destination_widths, caller_limit, Ok(caller.definitions)),
        port_bit_layout_result(input_widths, callee_limit, Ok(*callee.input_layout_model())),
        port_bit_layout_result(output_widths, callee_limit, Ok(*callee.output_layout_model())),
        arguments@.len() == input_widths.len(),
        nor_evaluation_ready(callee.netlist_model(), callee.input_layout_model().total_bits_model() as nat),
        callee.netlist_model().outputs@.len() == callee.output_layout_model().total_bits_model(),
        group.outputs.start + output_widths.len() == group.outputs.end <= destination_widths.len(),
        old(state).definitions@.len() == preceding_port_bits(destination_widths, group.outputs.start as nat),
        old(state).origins@.len() == old(state).gates@.len() <= gate_limit,
        gates_available(old(state).gates@, caller.inputs.total_bits_model() as nat, old(state).gates@.len() as int),
        wires_available(old(state).definitions@, caller.inputs.total_bits_model(), old(state).gates@.len()),
        forall|i: int| 0 <= i < caller.inputs.ranges_model().len() ==>
            (#[trigger] caller.inputs.ranges_model()[i]).end <= caller.inputs.total_bits_model(),
        forall|i: int| 0 <= i < output_widths.len() ==> destination_widths[group.outputs.start + i] == #[trigger] output_widths[i],
        forall|i: int| 0 <= i < arguments@.len() ==> layout_argument_ready(group.expression.source, forms@,
            caller.inputs.ranges_model(), caller.definitions.ranges_model(), old(state).definitions@.len() as int,
            #[trigger] arguments@[i],
            (callee.input_layout_model().ranges_model()[i].end - callee.input_layout_model().ranges_model()[i].start) as usize),
    ensures call_group_result(group, forms@, arguments@, caller, callee, old(state).model(), final(state).model(),
        gate_limit, destination_widths, output_widths, result),
{
    let ghost before = state.model();
    let ghost before_gates = state.gates@;
    let ghost before_definitions = state.definitions@;
    let invocation = CallerArguments { source: group.expression.source, forms,
        inputs: caller.inputs.ranges(), definitions: caller.definitions.ranges(), wires: state.definitions.as_slice(),
        child_ranges: &[], child_wires: &[] };
    let ghost invoked = invocation;
    let callee_input = callee.inputs();
    let callee_output = callee.outputs();
    let input_count = caller.inputs.total_bits();
    proof {
        reveal(argument_wires_ready);
        assert(wires_available(invocation.child_wires@, input_count, before_gates.len())) by {
            reveal(wires_available);
        };
    }
    let mut outputs = match lower_projected_call(&invocation, arguments, callee_input, callee.netlist(),
        &mut state.gates, gate_limit, Ghost(input_widths), Ghost(callee_limit), Ghost(input_count)) {
        Ok(outputs) => outputs,
        Err(CallWiringError::DeferredArgument(site)) => return Err(CallGroupError::DeferredArgument(site)),
        Err(CallWiringError::GateCapacity) => return Err(CallGroupError::GateCapacity(copy_location(&group.expression))),
    };
    let ghost produced = outputs@;
    let ghost mapped = choose|mapped: Seq<Wire>| #[trigger] argument_prefix_wires(&invoked, arguments@,
        callee_input.ranges_model(), arguments@.len() as int, mapped)
            && mapped.len() == callee_input.total_bits_model()
            && wires_available(mapped, input_count, before_gates.len())
            && instance_gates_match(before_gates, callee.netlist_model().gates@, mapped, state.gates@)
            && instance_outputs_match(callee.netlist_model().outputs@, mapped, before_gates.len() as usize, produced);
    proof {
        assert(state.gates@.len() == before_gates.len() + callee.netlist_model().gates@.len());
        assert(produced.len() == callee_output.total_bits_model());
        existing_wires_keep_availability(before_definitions, input_count, before_gates.len(), state.gates@.len());
        reveal(wires_available);
    }
    append_call_origins(&mut state.origins, state.gates.len(), group.outputs.start);
    append_instance_outputs(&mut state.definitions, &mut outputs, group.outputs.start,
        Ghost(destination_widths), Ghost(output_widths), Ghost(&caller.definitions), Ghost(callee_output),
        Ghost(caller_limit), Ghost(callee_limit), Ghost(input_count as nat), Ghost(state.gates@.len()));
    proof {
        reveal(wires_available);
        assert(call_group_wires_match(group, forms@, arguments@, caller, callee, before, state.model(),
            output_widths, invoked, mapped, produced));
    }
    Ok(())
}

#[verifier::opaque]
pub(super) open spec fn nested_group_invocation_matches(
    selected: &ResolvedTemplateCall, forms: Seq<Form>, caller: &Layouts, builtin: &(NorNetlist, PortBitLayout),
    before: WiringView, invocation: CallerArguments, calls: Seq<ChildCall>,
) -> bool {
    let group = selected.group;
    &&& invocation.source == group.expression.source && invocation.forms@ == forms
    &&& invocation.inputs@ == caller.inputs.ranges_model() && invocation.definitions@ == caller.definitions.ranges_model()
    &&& invocation.wires@ == before.definitions && invocation.child_ranges@.len() == 0 && invocation.child_wires@.len() == 0
    &&& calls.len() == selected.children@.len()
    &&& forall|i: int| 0 <= i < calls.len() ==>
        child_call_binding(selected.children@[i], group.references, builtin, #[trigger] calls[i])
        && child_call_ready(&invocation, calls, i)
    &&& forall|i: int, j: int| 0 <= i < j < calls.len() ==>
        (#[trigger] calls[i]).reference != (#[trigger] calls[j]).reference
    &&& root_arguments_fit_children(&invocation, calls, selected.arguments@, selected.template.circuit_model().input_layout_model())
}

/// 子と根の配線履歴を保持し、根の出力を左辺のポート順に追加したことを表す。
#[verifier::opaque]
pub(super) closed spec fn nested_call_group_result(
    selected: &ResolvedTemplateCall, forms: Seq<Form>, caller: &Layouts, builtin: &(NorNetlist, PortBitLayout),
    before: WiringView, after: WiringView, gate_limit: usize, child_limit: usize, destination_widths: Seq<u64>,
    result: Result<(), NestedCallWiringError>,
) -> bool {
    let group = selected.group;
    let callee = selected.template.circuit_model();
    let input_bits = caller.inputs.total_bits_model();
    let output_widths = selected.template.output_widths_model();
    let produced = after.definitions.subrange(before.definitions.len() as int, after.definitions.len() as int);
    let root = match result { Ok(()) => Ok(produced), Err(error) => Err(error) };
    &&& group.references.start <= group.references.end
    &&& exists|calls: Seq<ChildCall>, invocation: CallerArguments|
        #[trigger] nested_group_invocation_matches(selected, forms, caller, builtin, before, invocation, calls)
        && nested_root_wiring_result(&invocation, calls, (group.references.end - group.references.start) as usize,
            selected.arguments@, callee.input_layout_model(), callee.netlist_model(), before.gates, after.gates,
            gate_limit, child_limit, input_bits, root)
    &&& match result {
        Ok(()) => {
            &&& after.origins.len() == after.gates.len()
            &&& after.origins.take(before.origins.len() as int) == before.origins
            &&& forall|i: int| before.origins.len() <= i < after.origins.len() ==>
                (#[trigger] after.origins[i]) == group.outputs.start
            &&& after.definitions == before.definitions + produced
            &&& after.definitions.len() == preceding_port_bits(destination_widths, group.outputs.end as nat)
            &&& wires_available(after.definitions, input_bits, after.gates.len())
            &&& forall|port: int, bit: int|
                #![trigger after.definitions[caller.definitions.ranges_model()[group.outputs.start + port].start + bit]]
                0 <= port < output_widths.len() && 0 <= bit < output_widths[port] ==>
                    after.definitions[caller.definitions.ranges_model()[group.outputs.start + port].start + bit]
                        == produced[callee.output_layout_model().ranges_model()[port].start + bit]
        },
        Err(_) => after.definitions == before.definitions && after.gates == before.gates && after.origins == before.origins,
    }
}

/// 同じゲートの値割当で根の入力と出力を読み、出力ビットを呼び出し元の左辺に対応付ける。
pub(super) proof fn nested_call_group_values<'s, 'p, 'a>(
    selected: &ResolvedTemplateCall<'s, 'p, 'a>, forms: Seq<Form>, caller: &Layouts, builtin: &(NorNetlist, PortBitLayout),
    before: WiringView, after: WiringView, gate_limit: usize, child_limit: usize, destination_widths: Seq<u64>,
    destination_limit: usize, combined: Seq<NorGate>, inputs: Seq<bool>, values: Seq<bool>,
) -> (evaluation: (Seq<ChildCall<'s, 'p, 'a>>, CallerArguments<'s, 'p, 'a>, NestedRootEvaluation<'s, 'p, 'a>))
    requires
        nested_call_group_result(selected, forms, caller, builtin, before, after, gate_limit, child_limit, destination_widths, Ok(())),
        after.gates.len() <= combined.len() && after.gates == combined.take(after.gates.len() as int),
        gate_values_match(inputs, combined, values), values.len() == combined.len() <= usize::MAX,
        inputs.len() == caller.inputs.total_bits_model(),
        port_bit_layout_result(destination_widths, destination_limit, Ok(caller.definitions)),
        port_bit_layout_result(selected.template.output_widths_model(), selected.template.bit_limit_model(),
            Ok(*selected.template.circuit_model().output_layout_model())),
        selected.template.circuit_model().netlist_model().outputs@.len()
            == selected.template.circuit_model().output_layout_model().total_bits_model(),
        nor_evaluation_ready(selected.template.circuit_model().netlist_model(),
            selected.template.circuit_model().input_layout_model().total_bits_model() as nat),
        selected.group.outputs.start + selected.template.output_widths_model().len() == selected.group.outputs.end
            <= destination_widths.len(),
        before.definitions.len() == preceding_port_bits(destination_widths, selected.group.outputs.start as nat),
        forall|i: int| 0 <= i < selected.template.output_widths_model().len() ==>
            destination_widths[selected.group.outputs.start + i] == #[trigger] selected.template.output_widths_model()[i],
    ensures
        nested_group_invocation_matches(selected, forms, caller, builtin, before, evaluation.1, evaluation.0),
        ({
            let (calls, invocation, root) = evaluation;
            let group = selected.group;
            let callee = selected.template.circuit_model();
            let count = (group.references.end - group.references.start) as usize;
            let input_bits = caller.inputs.total_bits_model();
            &&& super::call_arguments::child_calls::child_wiring_trace_matches(&invocation, calls, calls.len(), count,
                before.gates, root.trace, root.end, input_bits)
            &&& super::call_arguments::child_calls::child_ranges_match(calls, calls.len(), root.end.table.ranges@)
            &&& root.end.table.wires@.len() == super::call_arguments::child_calls::child_sizes(calls, calls.len()).1
            &&& root.end.gates.len() <= combined.len() && root.end.gates == combined.take(root.end.gates.len() as int)
            &&& root.invocation.source == invocation.source && root.invocation.forms@ == invocation.forms@
            &&& root.invocation.inputs@ == invocation.inputs@ && root.invocation.definitions@ == invocation.definitions@
            &&& root.invocation.wires@ == invocation.wires@
            &&& root.invocation.child_ranges@ == root.end.table.ranges@
            &&& root.invocation.child_wires@ == root.end.table.wires@
            &&& argument_prefix_wires(&root.invocation, selected.arguments@, callee.input_layout_model().ranges_model(),
                selected.arguments@.len() as int, root.mapped)
            &&& root.mapped.len() == callee.input_layout_model().total_bits_model()
            &&& root.arguments == instance_wire_values(root.mapped, inputs, values)
            &&& nor_evaluation(callee.netlist_model(), root.arguments, root.outputs)
            &&& forall|port: int, bit: int| 0 <= port < selected.template.output_widths_model().len()
                && 0 <= bit < selected.template.output_widths_model()[port] ==>
                #[trigger] call_output_bit_has_value(caller, callee, after.definitions, group.outputs.start, port, bit,
                    inputs, values, root.outputs)
        }),
{
    reveal(nested_call_group_result);
    reveal(nested_root_wiring_result);
    let group = selected.group;
    let template = selected.template;
    let callee = template.circuit_model();
    let count = (group.references.end - group.references.start) as usize;
    let input_bits = caller.inputs.total_bits_model();
    let produced = after.definitions.subrange(before.definitions.len() as int, after.definitions.len() as int);
    let (calls, invocation) = choose|calls: Seq<ChildCall>, invocation: CallerArguments|
        #[trigger] nested_group_invocation_matches(selected, forms, caller, builtin, before, invocation, calls)
        && nested_root_wiring_result(&invocation, calls, count, selected.arguments@, callee.input_layout_model(),
            callee.netlist_model(), before.gates, after.gates, gate_limit, child_limit, input_bits, Ok(produced));
    let root = nested_root_values(&invocation, calls, count, selected.arguments@, callee.input_layout_model(),
        callee.netlist_model(), before.gates, after.gates, produced, combined, inputs, values, input_bits);
    let output_widths = template.output_widths_model();
    let output_layout = callee.output_layout_model();
    let limit = template.bit_limit_model();
    port_bit_layout_size(destination_widths, destination_limit, &caller.definitions);
    assert forall|port: int, bit: int| 0 <= port < output_widths.len() && 0 <= bit < output_widths[port]
        implies #[trigger] call_output_bit_has_value(caller, callee, after.definitions, group.outputs.start, port, bit,
            inputs, values, root.outputs) by {
        port_bit_layout_port(output_widths, limit, *output_layout, port as usize);
        call_output_range_matches(destination_widths, output_widths, group.outputs.start, port as usize,
            caller.definitions, *output_layout, destination_limit, limit);
        let dst = caller.definitions.ranges_model()[group.outputs.start + port].start + bit;
        let src = output_layout.ranges_model()[port].start + bit;
        assert(dst == before.definitions.len() + src);
        assert(0 <= src < produced.len());
        assert(after.definitions[dst] == produced[src]);
        assert(wire_available(produced[src], inputs.len(), values.len()));
    };
    (calls, invocation, root)
}

/// 後順の子と根を展開し、根の出力と全ゲートの由来を呼び出し元へ追加する。
///
/// # Errors
///
/// 最初に失敗した子または根の診断を返す。失敗時は定義配線、ゲート列、由来を保つ。
pub(super) fn lower_nested_call_group<'s, 'p, 'a>(
    selected: &'s ResolvedTemplateCall<'s, 'p, 'a>, forms: &[Form], caller: &Layouts,
    builtin: &'s (NorNetlist, PortBitLayout),
    state: &mut BodyWiring, gate_limit: usize, child_limit: usize,
    Ghost(body): Ghost<&LoweringBody<'_, 'p, 'a>>,
    Ghost(aliases): Ghost<&UseAliases<'_, 'p, 'a>>,
    Ghost(context): Ghost<(&FunctionExpansionOrder<'p, 'a>, &FunctionTemplates<'p, 'a>, u64, Seq<ProjectedCallArgument>)>,
    Ghost(caller_limit): Ghost<usize>,
) -> (result: Result<(), NestedCallWiringError<'p, 'a>>)
    requires
        aliases.expansion_child_scope(selected.group),
        aliases.resolved_expression_calls_match(context.0, context.1, context.2, selected.group.postorder, context.3, selected.children@),
        super::call_arguments::builtin_nor_call_matches(builtin),
        super::body_definition_layouts(body.input_widths@, body.definitions@, caller_limit, caller),
        resolved_call_fits_body(*selected, body.input_widths@, body.definitions@, forms@, context.2),
        port_bit_layout_result(selected.template.input_widths_model(), selected.template.bit_limit_model(),
            Ok(*selected.template.circuit_model().input_layout_model())),
        port_bit_layout_result(selected.template.output_widths_model(), selected.template.bit_limit_model(),
            Ok(*selected.template.circuit_model().output_layout_model())),
        selected.arguments@.len() == selected.template.input_widths_model().len(),
        nor_evaluation_ready(selected.template.circuit_model().netlist_model(),
            selected.template.circuit_model().input_layout_model().total_bits_model() as nat),
        selected.template.circuit_model().netlist_model().outputs@.len()
            == selected.template.circuit_model().output_layout_model().total_bits_model(),
        old(state).definitions@.len() == preceding_port_bits(super::definition_widths(body.definitions@),
            selected.group.outputs.start as nat),
        old(state).origins@.len() == old(state).gates@.len() <= gate_limit,
        gates_available(old(state).gates@, caller.inputs.total_bits_model() as nat, old(state).gates@.len() as int),
        wires_available(old(state).definitions@, caller.inputs.total_bits_model(), old(state).gates@.len()),
    ensures nested_call_group_result(selected, forms@, caller, builtin, old(state).model(), final(state).model(),
        gate_limit, child_limit, super::definition_widths(body.definitions@), result),
{
    let group = selected.group;
    let template = selected.template;
    let callee = template.circuit();
    let ghost input_bits = caller.inputs.total_bits_model();
    let ghost widths = super::definition_widths(body.definitions@);
    let ghost before = state.model();
    let invocation = CallerArguments { source: group.expression.source, forms,
        inputs: caller.inputs.ranges(), definitions: caller.definitions.ranges(), wires: state.definitions.as_slice(),
        child_ranges: &[], child_wires: &[] };
    let ghost invoked = invocation;
    proof { super::body_inputs_end_within_layout(body, caller_limit, caller); }
    let (count, children) = bind_child_calls(selected, builtin, Ghost(aliases), Ghost(context),
        Ghost(&invocation), Ghost((body, caller, caller_limit)));
    assert(nested_group_invocation_matches(selected, forms@, caller, builtin, before, invoked, children@)) by {
        reveal(nested_group_invocation_matches);
    };
    let expanded = lower_root_with_children(&invocation, children.as_slice(), count, selected.arguments,
        callee.inputs(), callee.netlist(), &mut state.gates, gate_limit, child_limit,
        Ghost((template.input_widths_model(), template.bit_limit_model())), Ghost(input_bits));
    let mut outputs = match expanded {
        Ok(outputs) => outputs,
        Err(error) => {
            assert(nested_call_group_result(selected, forms@, caller, builtin, before, state.model(),
                gate_limit, child_limit, widths, Err(error))) by {
                reveal(nested_call_group_result);
                reveal(nested_root_wiring_result);
                assert(nested_root_wiring_result(&invoked, children@, count, selected.arguments@, callee.input_layout_model(),
                    callee.netlist_model(), before.gates, state.gates@, gate_limit, child_limit, input_bits, Err(error)));
            };
            return Err(error);
        },
    };
    let ghost produced = outputs@;
    proof {
        reveal(nested_root_wiring_result);
        existing_wires_keep_availability(before.definitions, input_bits, before.gates.len(), state.gates@.len());
        reveal(wires_available);
    }
    append_call_origins(&mut state.origins, state.gates.len(), group.outputs.start);
    append_instance_outputs(&mut state.definitions, &mut outputs, group.outputs.start,
        Ghost(widths), Ghost(template.output_widths_model()), Ghost(&caller.definitions), Ghost(callee.output_layout_model()),
        Ghost(caller_limit), Ghost(template.bit_limit_model()), Ghost(input_bits as nat), Ghost(state.gates@.len()));
    proof {
        assert(state.definitions@.subrange(before.definitions.len() as int, state.definitions@.len() as int) =~= produced);
        assert(nested_call_group_result(selected, forms@, caller, builtin, before, state.model(),
            gate_limit, child_limit, widths, Ok(()))) by {
            reveal(nested_call_group_result);
            reveal(wires_available);
            assert(nested_root_wiring_result(&invoked, children@, count, selected.arguments@, callee.input_layout_model(),
                callee.netlist_model(), before.gates, state.gates@, gate_limit, child_limit, input_bits, Ok(produced)));
        };
    }
    Ok(())
}

} // verus!
