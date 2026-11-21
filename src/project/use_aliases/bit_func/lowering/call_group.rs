//! 呼び出しを一度展開し、出力とゲートの由来を呼び出し元へ追加する。

use super::super::expansion::CheckedExpansionCall;
use super::super::instances::append_instance_outputs;
use super::call_arguments::{CallWiringError, CallerArguments, lower_projected_call};
use super::{Layouts, LoweredBitFunc, NorGate, Wire, Vec};
use super::super::super::call_arity::ProjectedCallArgument;
use super::super::super::function_atoms::copy_location;
use crate::project::LocatedName;
use crate::syntax::Form;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::call_arguments::{argument_prefix_wires, argument_wires_ready, layout_argument_ready};
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
        inputs: caller.inputs.ranges(), definitions: caller.definitions.ranges(), wires: state.definitions.as_slice() };
    let ghost invoked = invocation;
    let callee_input = callee.inputs();
    let callee_output = callee.outputs();
    let input_count = caller.inputs.total_bits();
    proof { reveal(argument_wires_ready); }
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

} // verus!
