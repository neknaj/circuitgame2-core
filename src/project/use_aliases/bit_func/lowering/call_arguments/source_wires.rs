//! 型付きの実引数が参照するソース配線と、変換で渡す配線を照合する。

use super::*;
use super::super::source_wires::{
    definition_wires_pair, flatten_source_wire_pairs, port_ranges_cover, source_driver_wire,
    source_driver_wire_agrees, source_wires_pair,
};
use super::super::super::expansion::source_argument_bytes;
use crate::netlist::{
    SourceGateId, SourceWire, SourceTickCircuit, source_wire_pair, source_clocked_layout, source_instance_gate_agrees,
    source_instance_order_at, source_instance_outputs_agree, source_trace_layout_counts, source_wire_in_parent,
};
use super::child_calls::{
    ChildCall, ChildWiringSnapshot, child_call_ready, child_wiring_instance_at, child_wiring_trace_matches,
    preceding_child_argument_widths,
};

verus! {

/// 呼び出し元で確定した配線。子の出力は同じ定義内の参照番号で引く。
pub(in crate::project::use_aliases::bit_func::lowering) struct SourceArguments<'p, 'a> {
    pub(in crate::project::use_aliases::bit_func::lowering) source: &'p ProjectSource<'a>,
    pub(in crate::project::use_aliases::bit_func::lowering) forms: Seq<Form>,
    pub(in crate::project::use_aliases::bit_func::lowering) input_widths: Seq<u64>,
    pub(in crate::project::use_aliases::bit_func::lowering) definitions: Seq<Seq<SourceWire>>,
    pub(in crate::project::use_aliases::bit_func::lowering) children: Map<usize, Seq<SourceWire>>,
}

/// 信号、元のリテラル、または同じ定義内で先に展開した子の出力から配線を得る。
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn source_argument_wire(
    context: &SourceArguments, argument: ProjectedCallArgument, bit: int,
) -> Option<SourceWire> {
    match argument.source {
        CallArgumentSource::Driver(driver) =>
            Some(source_driver_wire(context.input_widths, context.definitions, driver, bit)),
        CallArgumentSource::Literal(_) =>
            Some(SourceWire::Constant(call_literal_bit(source_argument_bytes(context.source, context.forms, argument.form), bit as nat))),
        CallArgumentSource::NestedCall(reference) =>
            if context.children.dom().contains(reference) && 0 <= bit < context.children[reference].len() {
                Some(context.children[reference][bit])
            } else { None },
        CallArgumentSource::Deferred => None,
    }
}

/// 子の参照番号と、その出力が入った配線範囲を対応付ける。
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn source_child_outputs_pair(
    order: Seq<SourceGateId>, children: Map<usize, Seq<SourceWire>>, ranges: Seq<Option<Range<usize>>>, wires: Seq<Wire>,
) -> bool {
    forall|reference: usize| {
        let present = #[trigger] children.dom().contains(reference);
        &&& present <==> (reference < ranges.len() && ranges[reference as int].is_some())
        &&& present ==> {
            let range = ranges[reference as int]->Some_0;
            &&& range.start <= range.end <= wires.len()
            &&& source_wires_pair(order, children[reference], wires.subrange(range.start as int, range.end as int))
        }
    }
}

/// 子の出力を参照番号へ登録し、先行する子の出力配線を保つ。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn source_child_outputs_registered(
    order: Seq<SourceGateId>, children: Map<usize, Seq<SourceWire>>, outputs: Seq<SourceWire>,
    before: &ChildOutputWires, after: &ChildOutputWires, reference: usize,
    callee: &NorNetlist, inputs: Seq<Wire>, old_gates: Seq<NorGate>, new_gates: Seq<NorGate>, input_bits: usize,
)
    requires
        source_child_outputs_pair(order, children, before.ranges@, before.wires@),
        child_outputs_appended(before, after, reference, callee, inputs, old_gates, new_gates, input_bits),
        source_wires_pair(order, outputs, after.wires@.subrange(before.wires@.len() as int, after.wires@.len() as int)),
    ensures source_child_outputs_pair(order, children.insert(reference, outputs), after.ranges@, after.wires@),
{
    let next = children.insert(reference, outputs);
    let start = before.wires@.len();
    let end = after.wires@.len();
    assert forall|i: usize| {
        let present = #[trigger] next.dom().contains(i);
        &&& present <==> (i < after.ranges@.len() && after.ranges@[i as int].is_some())
        &&& present ==> {
            let range = after.ranges@[i as int]->Some_0;
            &&& range.start <= range.end <= end
            &&& source_wires_pair(order, next[i], after.wires@.subrange(range.start as int, range.end as int))
        }
    } by {
        if i == reference {
            assert(after.ranges@[i as int] == Some((start as usize)..(end as usize)));
            assert(next[i] == outputs);
        } else {
            assert(next.dom().contains(i) == children.dom().contains(i));
            if i < before.ranges@.len() {
                assert(after.ranges@[i as int] == before.ranges@[i as int]);
            }
            if children.dom().contains(i) {
                let range = before.ranges@[i as int]->Some_0;
                assert(next[i] == children[i]);
                assert(after.wires@.subrange(range.start as int, range.end as int)
                    =~= before.wires@.subrange(range.start as int, range.end as int));
            }
        }
    };
}

pub(in crate::project::use_aliases::bit_func::lowering) open spec fn source_argument_port_defined(
    context: &SourceArguments, argument: ProjectedCallArgument, width: u64,
) -> bool {
    &&& width > 0
    &&& forall|bit: int| 0 <= bit < width ==> #[trigger] source_argument_wire(context, argument, bit).is_some()
}

/// 宣言順に入力ポートを並べ、ポート内は最下位ビットから読む。
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn source_argument_wires(
    context: &SourceArguments, arguments: Seq<ProjectedCallArgument>, widths: Seq<u64>,
) -> Option<Seq<SourceWire>> {
    if widths.len() == arguments.len() && forall|port: int| 0 <= port < widths.len() ==>
        source_argument_port_defined(context, #[trigger] arguments[port], widths[port])
    {
        Some(Seq::new(widths.len(), |port: int| Seq::new(widths[port] as nat, |bit: int|
            source_argument_wire(context, arguments[port], bit)->Some_0)).flatten())
    } else { None }
}

proof fn source_argument_bit_agrees(
    context: &SourceArguments, caller: &CallerArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize,
    order: Seq<SourceGateId>, argument: ProjectedCallArgument, width: u64, width_limit: u64, bit: int,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        context.source == caller.source && context.forms == caller.forms@,
        context.input_widths == body.input_widths@,
        context.definitions.len() <= body.definitions@.len(),
        caller.inputs@ == layouts.inputs.ranges_model() && caller.definitions@ == layouts.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body.definitions@), context.definitions.len()),
        definition_wires_pair(order, context.definitions, caller.definitions@, caller.wires@),
        source_child_outputs_pair(order, context.children, caller.child_ranges@, caller.child_wires@),
        argument_matches_width(context.source, context.forms, context.input_widths, body.definitions@.take(context.definitions.len() as int),
            argument, width, width_limit),
        argument_source_available(caller, argument.source),
        child_argument_width_ready(caller.child_ranges@, caller.child_wires@.len(), argument.source, width as usize),
        0 <= bit < width <= usize::MAX,
    ensures source_argument_wire(context, argument, bit) matches Some(source)
        && source_wire_pair(order, source, argument_wire(caller, argument, bit)),
{
    reveal(argument_wire);
    match argument.source {
        CallArgumentSource::Driver(driver) => {
            source_driver_wire_agrees(context.input_widths, body.definitions@, layouts, capacity, context.definitions,
                caller.wires@, order, driver, bit, width);
        },
        CallArgumentSource::Literal(_) => {
            assert(source_argument_bytes(context.source, context.forms, argument.form) == literal_word(caller, argument.form));
        },
        CallArgumentSource::NestedCall(reference) => {
            let range = caller.child_ranges@[reference as int]->Some_0;
            let part = caller.child_wires@.subrange(range.start as int, range.end as int);
            assert(context.children.dom().contains(reference));
            assert(source_wires_pair(order, context.children[reference], part));
            assert(range.start <= range.end <= caller.child_wires@.len() && range.end - range.start == width);
            assert(part[bit] == caller.child_wires@[range.start + bit]);
        },
        CallArgumentSource::Deferred => { assert(false); },
    }
}

proof fn mapped_argument_port(
    caller: &CallerArguments, arguments: Seq<ProjectedCallArgument>, ranges: Seq<Range<usize>>, mapped: Seq<Wire>, port: int,
)
    requires
        argument_prefix_wires(caller, arguments, ranges, arguments.len() as int, mapped),
        0 <= port < arguments.len(),
    ensures
        argument_source_available(caller, arguments[port].source),
        forall|bit: int| 0 <= bit < ranges[port].end - ranges[port].start
            ==> (#[trigger] mapped[ranges[port].start + bit]) == argument_wire(caller, arguments[port], bit),
{
    reveal(argument_prefix_wires);
    assert(ranges[port].end <= mapped.len());
}

/// 入れ子を含む一つの呼び出しで、実引数の各ビットが同じ配線元を参照することを示す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn source_argument_wires_agree(
    context: &SourceArguments, caller: &CallerArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize,
    order: Seq<SourceGateId>, arguments: Seq<ProjectedCallArgument>, widths: Seq<u64>, width_limit: u64,
    callee_inputs: &PortBitLayout, callee_limit: usize, mapped: Seq<Wire>,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        context.source == caller.source && context.forms == caller.forms@,
        context.input_widths == body.input_widths@,
        context.definitions.len() <= body.definitions@.len(),
        caller.inputs@ == layouts.inputs.ranges_model() && caller.definitions@ == layouts.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body.definitions@), context.definitions.len()),
        definition_wires_pair(order, context.definitions, caller.definitions@, caller.wires@),
        source_child_outputs_pair(order, context.children, caller.child_ranges@, caller.child_wires@),
        port_bit_layout_result(widths, callee_limit, Ok(*callee_inputs)), widths.len() == arguments.len(),
        mapped.len() == callee_inputs.total_bits_model(),
        argument_prefix_wires(caller, arguments, callee_inputs.ranges_model(), arguments.len() as int, mapped),
        forall|port: int| 0 <= port < arguments.len() ==> {
            let argument = #[trigger] arguments[port];
            &&& argument_matches_width(context.source, context.forms, context.input_widths,
                body.definitions@.take(context.definitions.len() as int), argument, widths[port], width_limit)
            &&& widths[port] <= usize::MAX
            &&& child_argument_width_ready(caller.child_ranges@, caller.child_wires@.len(), argument.source, widths[port] as usize)
        },
    ensures source_argument_wires(context, arguments, widths) matches Some(source)
        && source_wires_pair(order, source, mapped),
{
    port_bit_layout_size(widths, callee_limit, callee_inputs);
    let ranges = callee_inputs.ranges_model();
    let source = Seq::new(widths.len(), |port: int| Seq::new(widths[port] as nat, |bit: int|
        source_argument_wire(context, arguments[port], bit)->Some_0));
    let pieces = Seq::new(widths.len(), |port: int| mapped.subrange(ranges[port].start as int, ranges[port].end as int));
    assert forall|port: int| 0 <= port < source.len() implies {
        &&& source_wires_pair(order, #[trigger] source[port], pieces[port])
        &&& source_argument_port_defined(context, arguments[port], widths[port])
    } by {
        let argument = arguments[port];
        let width = widths[port];
        port_bit_layout_port(widths, callee_limit, *callee_inputs, port as usize);
        let range = ranges[port];
        assert(range.start < range.end <= mapped.len() && range.end - range.start == width);
        let a = source[port];
        let b = pieces[port];
        assert(a.len() == b.len() == width);
        mapped_argument_port(caller, arguments, ranges, mapped, port);
        assert forall|bit: int| 0 <= bit < width implies #[trigger] source_argument_wire(context, argument, bit).is_some() by {
            source_argument_bit_agrees(context, caller, body, layouts, capacity, order, argument, width, width_limit, bit);
        };
        assert(source_argument_port_defined(context, argument, width)) by { reveal(source_argument_port_defined); };
        assert forall|bit: int| 0 <= bit < a.len() implies source_wire_pair(order, #[trigger] a[bit], b[bit]) by {
            source_argument_bit_agrees(context, caller, body, layouts, capacity, order, argument, width, width_limit, bit);
            assert(a[bit] == source_argument_wire(context, argument, bit)->Some_0);
            assert(b[bit] == mapped[range.start + bit]);
            assert(mapped[range.start + bit] == argument_wire(caller, argument, bit));
        };
    };
    assert forall|port: int| 0 <= port < widths.len() implies
        source_argument_port_defined(context, #[trigger] arguments[port], widths[port]) by {
        assert(source_wires_pair(order, source[port], pieces[port]));
    };
    flatten_source_wire_pairs(order, source, pieces);
    port_ranges_cover(widths, callee_inputs, callee_limit, mapped, widths.len());
    assert(pieces.take(widths.len() as int) =~= pieces);
    assert(mapped.take(mapped.len() as int) =~= mapped);
}

/// 子のソース出力を親の引数と呼び出し経路で置き換える。
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn source_child_outputs(
    prefix: Seq<crate::project::DefinitionPosition>, source: &SourceTickCircuit, arguments: Seq<SourceWire>,
) -> Seq<SourceWire> {
    Seq::new(source.outputs.len(), |bit: int| source_wire_in_parent(prefix, arguments, source.outputs[bit]))
}

/// 同じ呼び出しの実引数を子の配線へ渡し、親のゲート区間と出力表に対応付ける。
#[verifier::spinoff_prover]
pub(in crate::project::use_aliases::bit_func::lowering) proof fn source_child_placement_agrees(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    caller: &CallerArguments, calls: Seq<ChildCall>, count: usize, initial: Seq<NorGate>,
    trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot, input_bits: usize, i: int,
    prefix: Seq<crate::project::DefinitionPosition>, source: &SourceTickCircuit, child_order: Seq<SourceGateId>,
    child_index: Map<SourceGateId, int>, order: Seq<SourceGateId>,
) -> (arguments: Seq<SourceWire>)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        context.source == caller.source && context.forms == caller.forms@,
        context.input_widths == body.input_widths@, context.definitions.len() <= body.definitions@.len(),
        caller.inputs@ == layouts.inputs.ranges_model() && caller.definitions@ == layouts.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body.definitions@), context.definitions.len()),
        definition_wires_pair(order, context.definitions, caller.definitions@, caller.wires@),
        child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace, end, input_bits),
        0 <= i < calls.len(), child_call_ready(caller, calls, i),
        forall|left: int, right: int| 0 <= left < right < calls.len() ==>
            (#[trigger] calls[left]).reference != (#[trigger] calls[right]).reference,
        ({
            let call = calls[i];
            let before = trace[i];
            &&& source_child_outputs_pair(order, context.children, before.table.ranges@, before.table.wires@)
            &&& source_clocked_layout(source, call.circuit, child_order, child_index)
            &&& source_instance_order_at(prefix, child_order, order, before.gates.len() as usize)
            &&& before.gates.len() <= usize::MAX
            &&& forall|port: int| 0 <= port < call.arguments@.len() ==>
                argument_matches_width(context.source, context.forms, context.input_widths,
                    body.definitions@.take(context.definitions.len() as int), #[trigger] call.arguments@[port],
                    call._input_widths@[port], width_limit)
        }),
    ensures ({
        let call = calls[i];
        let before = trace[i];
        let after = trace[i + 1];
        &&& source_argument_wires(context, call.arguments@, call._input_widths@) == Some(arguments)
        &&& source_child_outputs_pair(order, context.children.insert(call.reference, source_child_outputs(prefix, source, arguments)),
            after.table.ranges@, after.table.wires@)
        &&& before.gates.len() + child_order.len() == after.gates.len()
        &&& forall|gate: int| 0 <= gate < child_order.len() ==> {
            let original = source.gates[child_order[gate]];
            let flat = #[trigger] after.gates[before.gates.len() + gate];
            &&& source_wire_pair(order, source_wire_in_parent(prefix, arguments, original.left), flat.left)
            &&& source_wire_pair(order, source_wire_in_parent(prefix, arguments, original.right), flat.right)
        }
    }),
{
    reveal(child_call_ready);
    let call = calls[i];
    let before = trace[i];
    let after = trace[i + 1];
    let (invocation, mapped) = child_wiring_instance_at(caller, calls, count, initial, trace, end, input_bits, i);
    let widths = call._input_widths@;
    let cap = call._layout_limit@;
    preceding_child_argument_widths(caller, calls, count, initial, trace, end, input_bits, i as nat, call.arguments@,
        call.inputs, widths, cap);
    source_argument_wires_agree(context, &invocation, body, layouts, capacity, order, call.arguments@,
        widths, width_limit, call.inputs, cap, mapped);
    let arguments = source_argument_wires(context, call.arguments@, widths)->Some_0;
    let base = before.gates.len() as usize;
    let wires = after.table.wires@.subrange(before.table.wires@.len() as int, after.table.wires@.len() as int);
    source_trace_layout_counts(source, call.circuit, child_order, child_index);
    assert(mapped.len() == call.circuit.input_count) by { reveal(nor_evaluation_ready); };
    assert forall|gate: int| 0 <= gate < child_order.len() implies {
        let original = source.gates[child_order[gate]];
        let flat = #[trigger] after.gates[before.gates.len() + gate];
        &&& source_wire_pair(order, source_wire_in_parent(prefix, arguments, original.left), flat.left)
        &&& source_wire_pair(order, source_wire_in_parent(prefix, arguments, original.right), flat.right)
    } by {
        source_instance_gate_agrees(prefix, source, call.circuit, child_order, child_index, order, arguments, mapped,
            after.gates, base, gate);
    };
    source_instance_outputs_agree(prefix, source, call.circuit, child_order, child_index, order, arguments, mapped, base, wires);
    let outputs = source_child_outputs(prefix, source, arguments);
    assert forall|bit: int| 0 <= bit < outputs.len() implies source_wire_pair(order, #[trigger] outputs[bit], wires[bit]) by {
        assert(outputs[bit] == source_wire_in_parent(prefix, arguments, source.outputs[bit]));
    };
    source_child_outputs_registered(order, context.children, outputs, &before.table, &after.table, call.reference,
        call.circuit, mapped, before.gates, after.gates, input_bits);
    arguments
}

} // verus!
