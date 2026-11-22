//! 型付きの実引数が参照するソース配線と、変換で渡す配線を照合する。

use super::*;
use super::super::source_wires::{
    definition_wires_in_extension, definition_wires_pair, flatten_source_wire_pairs, port_ranges_cover, source_driver_wire,
    source_driver_wire_agrees, source_wires_pair, source_wires_pair_in_extension,
};
use super::super::super::expansion::source_argument_bytes;
use super::super::super::templates::ResolvedExpressionCall;
use crate::netlist::{
    builtin_nor_source, builtin_nor_source_layout, builtin_nor_template,
    source_call_gate_order, source_call_order_appended, source_gate_belongs_to_call, source_gate_positions_distinct,
    source_instance_order_appended,
    SourceGateId, SourceNor, SourceWire, SourceTickCircuit, source_wire_pair, source_clocked_layout, source_instance_gate_agrees,
    source_instance_order_at, source_instance_outputs_agree, source_trace_layout_counts, source_wire_in_parent,
};
use crate::project::DefinitionPosition;
use super::child_calls::{
    ChildCall, ChildWiringSnapshot, child_call_binding, child_call_ready, child_wiring_instance_at, child_wiring_trace_matches,
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

/// 子のゲートを呼び出し位置で識別し、実引数の配線と出力先を展開履歴に対応付ける。
/// 解決済みの呼び出しから種類を判定する。先行ゲートの識別子は展開済みのゲート番号順に渡す。
/// 基底 NOR は呼び出し位置そのものを使い、通常呼び出しは子の識別子に経路を付ける。
#[verifier::spinoff_prover]
pub(in crate::project::use_aliases::bit_func::lowering) proof fn source_child_placement_agrees(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    caller: &CallerArguments, calls: Seq<ChildCall>, count: usize, initial: Seq<NorGate>,
    trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot, input_bits: usize, i: int,
    site: DefinitionPosition, selected: ResolvedExpressionCall, references: Range<usize>, builtin: &(NorNetlist, PortBitLayout),
    source: &SourceTickCircuit, child_order: Seq<SourceGateId>,
    child_index: Map<SourceGateId, int>, prior_order: Seq<SourceGateId>,
) -> (result: (Seq<SourceGateId>, Seq<SourceWire>))
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        context.source == caller.source && context.forms == caller.forms@,
        context.input_widths == body.input_widths@, context.definitions.len() <= body.definitions@.len(),
        caller.inputs@ == layouts.inputs.ranges_model() && caller.definitions@ == layouts.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body.definitions@), context.definitions.len()),
        definition_wires_pair(prior_order, context.definitions, caller.definitions@, caller.wires@),
        prior_order.no_duplicates(),
        forall|gate: int| 0 <= gate < prior_order.len() ==> !source_gate_belongs_to_call(site, #[trigger] prior_order[gate]),
        selected.template.is_none() ==> child_order == source_call_gate_order(site, None),
        child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace, end, input_bits),
        0 <= i < calls.len(), child_call_ready(caller, calls, i),
        forall|left: int, right: int| 0 <= left < right < calls.len() ==>
            (#[trigger] calls[left]).reference != (#[trigger] calls[right]).reference,
        ({
            let call = calls[i];
            let before = trace[i];
            &&& child_call_binding(selected, references, builtin, call)
            &&& site.reference == call.reference
            &&& source_child_outputs_pair(prior_order, context.children, before.table.ranges@, before.table.wires@)
            &&& source_clocked_layout(source, call.circuit, child_order, child_index)
            &&& prior_order.len() == before.gates.len()
            &&& trace[i + 1].gates.len() <= usize::MAX
            &&& forall|port: int| 0 <= port < call.arguments@.len() ==>
                argument_matches_width(context.source, context.forms, context.input_widths,
                    body.definitions@.take(context.definitions.len() as int), #[trigger] call.arguments@[port],
                    call._input_widths@[port], width_limit)
        }),
    ensures ({
        let (order, arguments) = result;
        let primitive = selected.template.is_none();
        let prefix = if primitive { Seq::empty() } else { seq![site] };
        let child = if primitive { None } else { Some(child_order) };
        let call = calls[i];
        let before = trace[i];
        let after = trace[i + 1];
        &&& order == prior_order + source_call_gate_order(site, child)
        &&& order.take(prior_order.len() as int) == prior_order
        &&& order.len() == after.gates.len()
        &&& after.gates.take(before.gates.len() as int) == before.gates
        &&& order.no_duplicates()
        &&& forall|gate: int| prior_order.len() <= gate < order.len() ==>
            source_gate_belongs_to_call(site, #[trigger] order[gate])
        &&& source_instance_order_at(prefix, child_order, order, before.gates.len() as usize)
        &&& source_argument_wires(context, call.arguments@, call._input_widths@) == Some(arguments)
        &&& forall|bit: int| 0 <= bit < arguments.len() ==>
            ((#[trigger] arguments[bit]) matches SourceWire::Gate(id) ==> prior_order.contains(id))
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
    let primitive = selected.template.is_none();
    let prefix = if primitive { Seq::empty() } else { seq![site] };
    let child = if primitive { None } else { Some(child_order) };
    let order = prior_order + source_call_gate_order(site, child);
    source_trace_layout_counts(source, call.circuit, child_order, child_index);
    assert forall|a: int, b: int| 0 <= a < child_order.len() && 0 <= b < child_order.len() && a != b
        implies #[trigger] child_order[a] != #[trigger] child_order[b] by {
        if a < b {
            source_gate_positions_distinct(source, call.circuit, child_order, child_index, a, b);
        } else {
            source_gate_positions_distinct(source, call.circuit, child_order, child_index, b, a);
        }
    };
    source_call_order_appended(prior_order, site, child);
    if primitive {
        assert(source_call_gate_order(site, child) =~= crate::netlist::source_instance_order(prefix, child_order));
    }
    source_instance_order_appended(prefix, child_order, prior_order);
    assert(source_child_outputs_pair(order, context.children, before.table.ranges@, before.table.wires@)) by {
        assert forall|r: usize| #[trigger] context.children.dom().contains(r) implies {
            let range = before.table.ranges@[r as int]->Some_0;
            source_wires_pair(order, context.children[r], before.table.wires@.subrange(range.start as int, range.end as int))
        } by {
            let range = before.table.ranges@[r as int]->Some_0;
            source_wires_pair_in_extension(prior_order, order, context.children[r],
                before.table.wires@.subrange(range.start as int, range.end as int));
        };
    };
    let widths = call._input_widths@;
    let cap = call._layout_limit@;
    preceding_child_argument_widths(caller, calls, count, initial, trace, end, input_bits, i as nat, call.arguments@,
        call.inputs, widths, cap);
    source_argument_wires_agree(context, &invocation, body, layouts, capacity, prior_order, call.arguments@,
        widths, width_limit, call.inputs, cap, mapped);
    let arguments = source_argument_wires(context, call.arguments@, widths)->Some_0;
    assert forall|bit: int| 0 <= bit < arguments.len() implies
        ((#[trigger] arguments[bit]) matches SourceWire::Gate(id) ==> prior_order.contains(id)) by {
        if let SourceWire::Gate(id) = arguments[bit] {
            assert(source_wire_pair(prior_order, arguments[bit], mapped[bit]));
            let gate = mapped[bit]->Gate_0;
            assert(gate < prior_order.len() && prior_order[gate as int] == id);
        }
    };
    source_wires_pair_in_extension(prior_order, order, arguments, mapped);
    let base = before.gates.len() as usize;
    let wires = after.table.wires@.subrange(before.table.wires@.len() as int, after.table.wires@.len() as int);
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
    (order, arguments)
}

/// 定義の厳格索引位置と、定義内での参照番号から子の位置を得る。
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn source_child_site(
    definition: DefinitionPosition, reference: usize,
) -> DefinitionPosition {
    DefinitionPosition { reference, ..definition }
}

/// ソースで定めた子ゲートの左右を、呼び出し元の引数とゲート識別子で表す。
spec fn source_child_gate(
    prefix: Seq<DefinitionPosition>, arguments: Seq<SourceWire>, gate: SourceNor,
) -> SourceNor {
    SourceNor {
        left: source_wire_in_parent(prefix, arguments, gate.left),
        right: source_wire_in_parent(prefix, arguments, gate.right),
    }
}

/// 各子のソース回路と、ゲート識別子から変換先の番号を引く対応表。
pub(in crate::project::use_aliases::bit_func::lowering) struct SourceChildModel {
    pub(in crate::project::use_aliases::bit_func::lowering) circuit: SourceTickCircuit,
    pub(in crate::project::use_aliases::bit_func::lowering) order: Seq<SourceGateId>,
    pub(in crate::project::use_aliases::bit_func::lowering) index: Map<SourceGateId, int>,
}

spec fn source_child_model(site: DefinitionPosition, primitive: bool, ordinary: Option<SourceChildModel>)
    -> Option<SourceChildModel>
{
    if primitive {
        let (circuit, order, index) = builtin_nor_source(site);
        Some(SourceChildModel { circuit, order, index })
    } else { ordinary }
}

/// 変換履歴を使わず、型付きの子呼び出し列から配線を組み立てる。
pub(in crate::project::use_aliases::bit_func::lowering) closed spec fn source_children_wiring(
    context: &SourceArguments, definition: DefinitionPosition, first_ref: usize, initial_order: Seq<SourceGateId>,
    selected: Seq<ResolvedExpressionCall>, children: Seq<Option<SourceChildModel>>, stop: nat,
) -> Option<(Seq<SourceGateId>, Map<usize, Seq<SourceWire>>, Seq<SourceNor>)>
    decreases stop,
{
    if stop == 0 {
        Some((initial_order, context.children, Seq::empty()))
    } else if stop <= selected.len() && stop <= children.len() {
        let call = selected[stop - 1];
        if call.child.reference < first_ref {
            None
        } else if let Some((before, outputs, gates)) =
            source_children_wiring(context, definition, first_ref, initial_order, selected, children, (stop - 1) as nat)
        {
            let reference = (call.child.reference - first_ref) as usize;
            let site = source_child_site(definition, reference);
            if let Some(model) = source_child_model(site, call.template.is_none(), children[stop - 1]) {
                let child = if call.template.is_none() { None } else { Some(model.order) };
                let prefix = if child.is_none() { Seq::empty() } else { seq![site] };
                let widths = match call.template {
                    Some(template) => template.input_widths_model(),
                    None => seq![1u64, 1u64],
                };
                let available = SourceArguments { children: outputs, ..*context };
                if let Some(arguments) = source_argument_wires(&available, call.arguments@, widths) {
                    let order = before + source_call_gate_order(site, child);
                    let added = Seq::new(model.order.len(), |gate: int|
                        source_child_gate(prefix, arguments, model.circuit.gates[model.order[gate]]));
                    Some((order, outputs.insert(reference, source_child_outputs(prefix, &model.circuit, arguments)), gates + added))
                } else { None }
            } else { None }
        } else { None }
    } else { None }
}

/// 子呼び出しの後順列を展開履歴と照合し、各子のゲートと出力を組み立てる。
#[verifier::spinoff_prover]
pub(in crate::project::use_aliases::bit_func::lowering) proof fn source_children_placement(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    caller: &CallerArguments, calls: Seq<ChildCall>, references: Range<usize>, builtin: &(NorNetlist, PortBitLayout),
    trace: Seq<ChildWiringSnapshot>, input_bits: usize, definition: DefinitionPosition, initial_order: Seq<SourceGateId>,
    selected: Seq<ResolvedExpressionCall>, children: Seq<Option<SourceChildModel>>,
    stop: nat,
) -> (result: (Seq<SourceGateId>, Map<usize, Seq<SourceWire>>, Seq<SourceNor>))
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        context.source == caller.source && context.forms == caller.forms@,
        context.input_widths == body.input_widths@, context.definitions.len() <= body.definitions@.len(),
        context.children == Map::<usize, Seq<SourceWire>>::empty(),
        caller.inputs@ == layouts.inputs.ranges_model() && caller.definitions@ == layouts.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body.definitions@), context.definitions.len()),
        definition_wires_pair(initial_order, context.definitions, caller.definitions@, caller.wires@),
        stop <= calls.len() == selected.len() == children.len(),
        trace.len() == calls.len() + 1, references.start <= references.end,
        child_wiring_trace_matches(caller, calls, calls.len(), (references.end - references.start) as usize,
            trace[0].gates, trace, trace[calls.len() as int], input_bits),
        initial_order.len() == trace[0].gates.len(), initial_order.no_duplicates(),
        forall|a: int, b: int| 0 <= a < b < calls.len() ==>
            (#[trigger] calls[a]).reference != (#[trigger] calls[b]).reference,
        forall|i: int| 0 <= i < calls.len() ==> {
            let call = #[trigger] calls[i];
            let site = source_child_site(definition, call.reference);
            &&& child_call_ready(caller, calls, i)
            &&& child_call_binding(selected[i], references, builtin, call)
            &&& if selected[i].template.is_none() {
                children[i].is_none()
            } else {
                children[i] matches Some(model) && source_clocked_layout(&model.circuit, call.circuit, model.order, model.index)
            }
            &&& trace[i + 1].gates.len() <= usize::MAX
            &&& forall|gate: int| 0 <= gate < initial_order.len() ==>
                !source_gate_belongs_to_call(site, #[trigger] initial_order[gate])
            &&& forall|port: int| 0 <= port < call.arguments@.len() ==>
                argument_matches_width(context.source, context.forms, context.input_widths,
                    body.definitions@.take(context.definitions.len() as int), #[trigger] call.arguments@[port],
                    call._input_widths@[port], width_limit)
        },
    ensures ({
        let (order, outputs, gates) = result;
        let flat = trace[stop as int];
        &&& source_children_wiring(context, definition, references.start, initial_order, selected, children, stop) == Some(result)
        &&& order.len() == flat.gates.len()
        &&& order.len() == initial_order.len() + gates.len()
        &&& order.take(initial_order.len() as int) == initial_order
        &&& order.no_duplicates()
        &&& source_child_outputs_pair(order, outputs, flat.table.ranges@, flat.table.wires@)
        &&& definition_wires_pair(order, context.definitions, caller.definitions@, caller.wires@)
        &&& forall|i: int, gate: int| 0 <= gate < order.len() && stop <= i < calls.len() ==>
            !source_gate_belongs_to_call(source_child_site(definition, (#[trigger] calls[i]).reference), #[trigger] order[gate])
        &&& forall|gate: int| 0 <= gate < gates.len() ==> {
            let source = #[trigger] gates[gate];
            let lowered = flat.gates[initial_order.len() + gate];
            &&& source_wire_pair(order, source.left, lowered.left)
            &&& source_wire_pair(order, source.right, lowered.right)
        }
    }),
    decreases stop,
{
    if stop == 0 {
        reveal(child_wiring_trace_matches);
        assert(initial_order.take(initial_order.len() as int) =~= initial_order);
        assert(source_child_outputs_pair(initial_order, context.children, trace[0].table.ranges@, trace[0].table.wires@)) by {
            assert forall|r: usize| !(#[trigger] context.children.dom().contains(r))
                && !(r < trace[0].table.ranges@.len() && trace[0].table.ranges@[r as int].is_some()) by {};
        };
        assert forall|i: int, gate: int| 0 <= gate < initial_order.len() && 0 <= i < calls.len() implies
            !source_gate_belongs_to_call(source_child_site(definition, (#[trigger] calls[i]).reference),
                #[trigger] initial_order[gate]) by {};
        return (initial_order, context.children, Seq::empty());
    }

    let i = stop - 1;
    let (prior, outputs, gates) = source_children_placement(context, body, layouts, capacity, width_limit, caller, calls,
        references, builtin, trace, input_bits, definition, initial_order, selected, children, i as nat);
    let call = calls[i];
    let site = source_child_site(definition, call.reference);
    let primitive = selected[i].template.is_none();
    let model = source_child_model(site, primitive, children[i])->Some_0;
    if primitive {
        assert(builtin_nor_template(call.circuit)) by { reveal(nor_evaluation_ready); };
        builtin_nor_source_layout(site, call.circuit);
        assert(model.order == source_call_gate_order(site, None));
    }
    let before = trace[i];
    let after = trace[i + 1];
    let available = SourceArguments { children: outputs, ..*context };
    assert forall|gate: int| 0 <= gate < prior.len() implies
        !source_gate_belongs_to_call(site, #[trigger] prior[gate]) by {
        assert(calls[i] == call);
    };
    let (order, arguments) = source_child_placement_agrees(&available, body, layouts, capacity, width_limit, caller, calls,
        (references.end - references.start) as usize, trace[0].gates, trace, trace[calls.len() as int], input_bits,
        i, site, selected[i], references, builtin, &model.circuit, model.order, model.index, prior);
    let prefix = if selected[i].template.is_none() { Seq::empty() } else { seq![site] };
    let added = Seq::new(model.order.len(), |gate: int|
        source_child_gate(prefix, arguments, model.circuit.gates[model.order[gate]]));
    let all = gates + added;
    assert(order.take(initial_order.len() as int) =~= initial_order) by {
        assert forall|gate: int| 0 <= gate < initial_order.len() implies
            #[trigger] order.take(initial_order.len() as int)[gate] == initial_order[gate] by {
            assert(order[gate] == prior[gate]);
            assert(prior[gate] == initial_order[gate]);
        };
    };
    assert forall|j: int, gate: int| 0 <= gate < order.len() && stop <= j < calls.len() implies
        !source_gate_belongs_to_call(source_child_site(definition, (#[trigger] calls[j]).reference),
            #[trigger] order[gate]) by {
        let later = source_child_site(definition, calls[j].reference);
        if gate < prior.len() {
            assert(order[gate] == prior[gate]);
        } else {
            assert(calls[i].reference != calls[j].reference);
            assert(site != later);
            assert(source_gate_belongs_to_call(site, order[gate]));
        }
    };
    definition_wires_in_extension(prior, order, context.definitions, caller.definitions@, caller.wires@);
    assert forall|gate: int| 0 <= gate < all.len() implies {
        let source = #[trigger] all[gate];
        let flat = after.gates[initial_order.len() + gate];
        &&& source_wire_pair(order, source.left, flat.left)
        &&& source_wire_pair(order, source.right, flat.right)
    } by {
        let index = initial_order.len() + gate;
        if gate < gates.len() {
            assert(all[gate] == gates[gate]);
            assert(after.gates[index] == before.gates[index]);
            let flat = before.gates[index];
            let source = gates[gate];
            assert(source_wire_pair(prior, source.left, flat.left) && source_wire_pair(prior, source.right, flat.right));
            if let Wire::Gate(left) = flat.left {
                assert(order[left as int] == prior[left as int]);
            }
            if let Wire::Gate(right) = flat.right {
                assert(order[right as int] == prior[right as int]);
            }
        } else {
            let local = gate - gates.len();
            assert(index == prior.len() + local);
            assert(all[gate] == added[local]);
        }
    };
    let result = (order, outputs.insert(call.reference, source_child_outputs(prefix, &model.circuit, arguments)), all);
    assert(source_children_wiring(context, definition, references.start, initial_order, selected, children, stop) == Some(result)) by {
        reveal_with_fuel(source_children_wiring, 2);
        let chosen = selected[i];
        assert(chosen.child.reference == references.start + call.reference);
        assert(chosen.arguments@ == call.arguments@);
        assert(match chosen.template {
            Some(template) => call._input_widths@ == template.input_widths_model(),
            None => call._input_widths@ == seq![1u64, 1u64],
        });
    };
    result
}

} // verus!
