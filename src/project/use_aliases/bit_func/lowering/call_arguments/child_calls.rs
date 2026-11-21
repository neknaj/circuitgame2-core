//! 子呼び出しを内側から展開し、失敗したときは追加したゲートを取り除く。

use super::*;
#[cfg(verus_only)]
use super::super::existing_wires_keep_availability;

verus! {

/// 後順の一項目。参照添字は、この定義の先頭の参照を起点とする。
pub(in crate::project::use_aliases::bit_func::lowering) struct ChildCall<'s> {
    pub(in crate::project::use_aliases::bit_func::lowering) reference: usize,
    pub(in crate::project::use_aliases::bit_func::lowering) arguments: &'s [ProjectedCallArgument],
    pub(in crate::project::use_aliases::bit_func::lowering) inputs: &'s PortBitLayout,
    pub(in crate::project::use_aliases::bit_func::lowering) circuit: &'s NorNetlist,
    pub(in crate::project::use_aliases::bit_func::lowering) _input_widths: Ghost<Seq<u64>>,
    pub(in crate::project::use_aliases::bit_func::lowering) _layout_limit: Ghost<usize>,
}

#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_sizes(calls: Seq<ChildCall>, end: nat) -> (nat, nat)
    decreases end,
{
    if end == 0 || end > calls.len() {
        (0, 0)
    } else {
        let before = child_sizes(calls, (end - 1) as nat);
        let circuit = calls[end - 1].circuit;
        (before.0 + circuit.gates@.len(), before.1 + circuit.outputs@.len())
    }
}

proof fn child_sizes_grow(calls: Seq<ChildCall>, first: nat, end: nat)
    requires first <= end <= calls.len(),
    ensures child_sizes(calls, first).1 <= child_sizes(calls, end).1,
    decreases end - first,
{
    if first < end {
        child_sizes_grow(calls, first, (end - 1) as nat);
        reveal(child_sizes);
    }
}

proof fn child_sizes_step(calls: Seq<ChildCall>, index: int)
    requires 0 <= index < calls.len(),
    ensures
        child_sizes(calls, (index + 1) as nat).0 == child_sizes(calls, index as nat).0 + calls[index].circuit.gates@.len(),
        child_sizes(calls, (index + 1) as nat).1 == child_sizes(calls, index as nat).1 + calls[index].circuit.outputs@.len(),
{
    reveal(child_sizes);
}

#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_call_ready(
    caller: &CallerArguments, calls: Seq<ChildCall>, index: int,
) -> bool {
    &&& 0 <= index < calls.len()
    &&& ({
        let call = calls[index];
        &&& port_bit_layout_result(call._input_widths@, call._layout_limit@, Ok(*call.inputs))
        &&& call.arguments@.len() == call.inputs.ranges_model().len() == call._input_widths@.len()
        &&& nor_evaluation_ready(call.circuit, call.inputs.total_bits_model() as nat)
        &&& forall|port: int| 0 <= port < call.arguments@.len() ==> {
            let argument = #[trigger] call.arguments@[port];
            let span = call.inputs.ranges_model()[port];
            let width = (span.end - span.start) as usize;
            &&& layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
                caller.wires@.len() as int, argument, width)
            &&& if let CallArgumentSource::NestedCall(reference) = argument.source {
                exists|earlier: int| 0 <= earlier < index && (#[trigger] calls[earlier]).reference == reference
                    && calls[earlier].circuit.outputs@.len() == width
            } else { true }
        }
    })
}

#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_ranges_match(
    calls: Seq<ChildCall>, end: nat, ranges: Seq<Option<Range<usize>>>,
) -> bool {
    &&& end <= calls.len()
    &&& forall|i: int| 0 <= i < end ==> {
        let reference = (#[trigger] calls[i]).reference;
        &&& reference < ranges.len()
        &&& ranges[reference as int] == Some((child_sizes(calls, i as nat).1 as usize)
            ..(child_sizes(calls, (i + 1) as nat).1 as usize))
    }
    &&& forall|r: int| 0 <= r < ranges.len() && (#[trigger] ranges[r]).is_some() ==>
        exists|i: int| 0 <= i < end && (#[trigger] calls[i]).reference == r
}

pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_arguments_determined(calls: Seq<ChildCall>, stop: nat) -> bool {
    &&& stop <= calls.len()
    &&& forall|i: int, j: int| 0 <= i < stop && 0 <= j < calls[i].arguments@.len() ==>
        !((#[trigger] calls[i].arguments@[j]).source is Deferred)
}

proof fn extend_determined_children(calls: Seq<ChildCall>, index: usize, ranges: Seq<Option<Range<usize>>>)
    requires
        index < calls.len(),
        child_arguments_determined(calls, index as nat),
        forall|j: int| 0 <= j < calls[index as int].arguments@.len() ==>
            projected_source_available(ranges, (#[trigger] calls[index as int].arguments@[j]).source),
    ensures child_arguments_determined(calls, (index + 1) as nat),
{
    assert forall|i: int, j: int| 0 <= i <= index && 0 <= j < calls[i].arguments@.len()
        implies !((#[trigger] calls[i].arguments@[j]).source is Deferred) by {
        if i == index {
            assert(projected_source_available(ranges, calls[i].arguments@[j].source));
        }
    };
}

proof fn next_child_readiness(
    caller: &CallerArguments, calls: Seq<ChildCall>, index: usize,
    ranges: Seq<Option<Range<usize>>>, wires: nat,
)
    requires
        index < calls.len(), child_call_ready(caller, calls, index as int),
        calls[index as int].reference < ranges.len(),
        child_ranges_match(calls, index as nat, ranges),
        wires == child_sizes(calls, index as nat).1,
        child_sizes(calls, calls.len()).1 <= usize::MAX,
        forall|i: int, j: int| 0 <= i < j < calls.len() ==>
            (#[trigger] calls[i]).reference != (#[trigger] calls[j]).reference,
    ensures ({
        let call = calls[index as int];
        &&& ranges[call.reference as int].is_none()
        &&& wires + call.circuit.outputs@.len() <= usize::MAX
        &&& port_bit_layout_result(call._input_widths@, call._layout_limit@, Ok(*call.inputs))
        &&& call.arguments@.len() == call.inputs.ranges_model().len() == call._input_widths@.len()
        &&& nor_evaluation_ready(call.circuit, call.inputs.total_bits_model() as nat)
        &&& forall|port: int| 0 <= port < call.arguments@.len() ==> {
            let argument = #[trigger] call.arguments@[port];
            let span = call.inputs.ranges_model()[port];
            let width = (span.end - span.start) as usize;
            &&& layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
                caller.wires@.len() as int, argument, width)
            &&& child_argument_width_ready(ranges, wires, argument.source, width)
            &&& (!(argument.source is Deferred) ==> projected_source_available(ranges, argument.source))
        }
    }),
{
    reveal(child_call_ready);
    reveal(child_ranges_match);
    child_sizes_step(calls, index as int);
    child_sizes_grow(calls, (index + 1) as nat, calls.len());
    let call = calls[index as int];
    if ranges[call.reference as int].is_some() {
        let earlier = choose|i: int| 0 <= i < index && (#[trigger] calls[i]).reference == call.reference;
        assert(calls[earlier].reference != call.reference);
    }
    assert forall|port: int| 0 <= port < call.arguments@.len() implies {
        let argument = #[trigger] call.arguments@[port];
        let span = call.inputs.ranges_model()[port];
        let width = (span.end - span.start) as usize;
        &&& child_argument_width_ready(ranges, wires, argument.source, width)
        &&& (!(argument.source is Deferred) ==> projected_source_available(ranges, argument.source))
    } by {
        if let CallArgumentSource::NestedCall(reference) = call.arguments@[port].source {
            let span = call.inputs.ranges_model()[port];
            let earlier = choose|i: int| 0 <= i < index && (#[trigger] calls[i]).reference == reference
                && calls[i].circuit.outputs@.len() == (span.end - span.start) as usize;
            child_sizes_grow(calls, (earlier + 1) as nat, index as nat);
            child_sizes_step(calls, earlier);
            assert(ranges[reference as int] == Some((child_sizes(calls, earlier as nat).1 as usize)
                ..(child_sizes(calls, (earlier + 1) as nat).1 as usize)));
        }
    };
}

proof fn extend_child_ranges(
    calls: Seq<ChildCall>, index: usize,
    before: Seq<Option<Range<usize>>>, after: Seq<Option<Range<usize>>>,
)
    requires
        index < calls.len(), calls[index as int].reference < before.len(),
        child_ranges_match(calls, index as nat, before),
        after == before.update(calls[index as int].reference as int, Some((child_sizes(calls, index as nat).1 as usize)
            ..(child_sizes(calls, (index + 1) as nat).1 as usize))),
        forall|i: int, j: int| 0 <= i < j < calls.len() ==>
            (#[trigger] calls[i]).reference != (#[trigger] calls[j]).reference,
    ensures child_ranges_match(calls, (index + 1) as nat, after),
{
    reveal(child_ranges_match);
    assert forall|i: int| 0 <= i < index + 1 implies {
        let reference = (#[trigger] calls[i]).reference;
        &&& reference < after.len()
        &&& after[reference as int] == Some((child_sizes(calls, i as nat).1 as usize)
            ..(child_sizes(calls, (i + 1) as nat).1 as usize))
    } by {
        if i < index { assert(after[calls[i].reference as int] == before[calls[i].reference as int]); }
    };
    assert forall|r: int| 0 <= r < after.len() && (#[trigger] after[r]).is_some()
        implies exists|i: int| 0 <= i < index + 1 && (#[trigger] calls[i]).reference == r by {
        if r != calls[index as int].reference { assert(after[r] == before[r]); }
    };
}

/// 後順の子を展開し、全件に成功したときだけ一時配線表を返す。
///
/// # Errors
///
/// 失敗した子の位置と診断を返す。その場合は、この処理を始める前のゲート列を保つ。
pub(in crate::project::use_aliases::bit_func::lowering) fn lower_child_calls<'s, 'p, 'a>(
    caller: &CallerArguments<'s, 'p, 'a>, calls: &[ChildCall<'s>], reference_count: usize,
    gates: &mut Vec<NorGate>, capacity: usize, Ghost(input_bits): Ghost<usize>,
) -> (result: Result<ChildOutputWires, (usize, CallWiringError<'p, 'a>)>)
    requires
        form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
        old(gates)@.len() <= capacity,
        gates_available(old(gates)@, input_bits as nat, old(gates)@.len() as int),
        wires_available(caller.wires@, input_bits, old(gates)@.len()),
        child_sizes(calls@, calls@.len()).1 <= usize::MAX,
        forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
        forall|i: int| 0 <= i < calls@.len() ==>
            (#[trigger] calls@[i]).reference < reference_count && child_call_ready(caller, calls@, i),
        forall|i: int, j: int| 0 <= i < j < calls@.len() ==>
            (#[trigger] calls@[i]).reference != (#[trigger] calls@[j]).reference,
    ensures
        result matches Ok(table) ==> {
            &&& table.ranges@.len() == reference_count
            &&& child_ranges_match(calls@, calls@.len(), table.ranges@)
            &&& table.wires@.len() == child_sizes(calls@, calls@.len()).1
            &&& final(gates)@.len() == old(gates)@.len() + child_sizes(calls@, calls@.len()).0 <= capacity
            &&& final(gates)@.take(old(gates)@.len() as int) == old(gates)@
            &&& gates_available(final(gates)@, input_bits as nat, final(gates)@.len() as int)
            &&& wires_available(table.wires@, input_bits, final(gates)@.len())
            &&& child_arguments_determined(calls@, calls@.len())
        },
        result matches Err((i, _)) ==> i < calls@.len(),
        result.is_err() ==> final(gates)@ == old(gates)@,
        result matches Err((i, _)) ==> old(gates)@.len() + child_sizes(calls@, i as nat).0 <= capacity,
        result matches Err((i, _)) ==> child_arguments_determined(calls@, i as nat),
        result matches Err((i, error)) ==> i < calls@.len() && match error {
                CallWiringError::DeferredArgument(site) => {
                    let projected = calls@[i as int].arguments@;
                    exists|port: int| 0 <= port < projected.len() && (#[trigger] projected[port]).source is Deferred
                        && is_form_location(caller.source, caller.forms@[projected[port].form as int], site)
                        && forall|j: int| 0 <= j < port ==> !((#[trigger] projected[j]).source is Deferred)
                },
                CallWiringError::GateCapacity =>
                    old(gates)@.len() + child_sizes(calls@, (i + 1) as nat).0 > capacity
                    && child_arguments_determined(calls@, (i + 1) as nat),
        },
{
    let mut table = ChildOutputWires::new(reference_count);
    let checkpoint = gates.len();
    let ghost initial = gates@;
    let mut index = 0;
    proof {
        assert(child_sizes(calls@, 0) == (0nat, 0nat)) by { reveal(child_sizes); };
        reveal(wires_available);
        assert(child_ranges_match(calls@, 0, table.ranges@)) by { reveal(child_ranges_match); };
        assert(gates@.take(checkpoint as int) =~= initial);
    }
    while index < calls.len()
        invariant
            index <= calls@.len(), checkpoint == initial.len(), initial == old(gates)@,
            table.ranges@.len() == reference_count,
            child_ranges_match(calls@, index as nat, table.ranges@),
            child_arguments_determined(calls@, index as nat),
            table.wires@.len() == child_sizes(calls@, index as nat).1,
            gates@.len() == checkpoint + child_sizes(calls@, index as nat).0 <= capacity,
            gates@.take(checkpoint as int) == initial,
            gates_available(gates@, input_bits as nat, gates@.len() as int),
            wires_available(caller.wires@, input_bits, gates@.len()),
            wires_available(table.wires@, input_bits, gates@.len()),
            child_sizes(calls@, calls@.len()).1 <= usize::MAX,
            form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
            forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
            forall|i: int| 0 <= i < calls@.len() ==>
                (#[trigger] calls@[i]).reference < reference_count && child_call_ready(caller, calls@, i),
            forall|i: int, j: int| 0 <= i < j < calls@.len() ==>
                (#[trigger] calls@[i]).reference != (#[trigger] calls@[j]).reference,
        decreases calls@.len() - index,
    {
        let call = &calls[index];
        let ghost ranges = table.ranges@;
        let ghost before = gates@;
        proof {
            child_sizes_step(calls@, index as int);
            next_child_readiness(caller, calls@, index, ranges, table.wires@.len());
        }
        let error = lower_child_call(caller, call.arguments, call.inputs, call.circuit, &mut table,
            call.reference, gates, capacity, Ghost(call._input_widths@), Ghost(call._layout_limit@), Ghost(input_bits));
        if let Err(error) = error {
            proof {
                match &error {
                    CallWiringError::GateCapacity => {
                        extend_determined_children(calls@, index, ranges);
                        assert(checkpoint + child_sizes(calls@, (index + 1) as nat).0 > capacity);
                    },
                    CallWiringError::DeferredArgument(site) => {
                        let arguments = call.arguments@;
                        let port = choose|port: int| 0 <= port < arguments.len()
                            && !projected_source_available(ranges, (#[trigger] arguments[port]).source)
                            && is_form_location(caller.source, caller.forms@[arguments[port].form as int], *site)
                            && forall|j: int| 0 <= j < port ==> projected_source_available(ranges, (#[trigger] arguments[j]).source);
                        assert(arguments[port].source is Deferred);
                        assert forall|j: int| 0 <= j < port implies !((#[trigger] arguments[j]).source is Deferred) by {};
                        assert(exists|p: int| 0 <= p < arguments.len() && (#[trigger] arguments[p]).source is Deferred
                            && is_form_location(caller.source, caller.forms@[arguments[p].form as int], *site)
                            && forall|j: int| 0 <= j < p ==> !((#[trigger] arguments[j]).source is Deferred));
                    },
                }
            }
            gates.truncate(checkpoint);
            assert(gates@ =~= initial);
            assert(checkpoint + child_sizes(calls@, index as nat).0 <= capacity);
            assert(child_arguments_determined(calls@, index as nat));
            return Err((index, error));
        }
        proof {
            assert(gates@.take(checkpoint as int) =~= initial);
            existing_wires_keep_availability(caller.wires@, input_bits, before.len(), gates@.len());
            extend_child_ranges(calls@, index, ranges, table.ranges@);
            extend_determined_children(calls@, index, ranges);
        }
        index += 1;
    }
    Ok(table)
}

} // verus!
