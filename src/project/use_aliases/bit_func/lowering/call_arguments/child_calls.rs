//! 子呼び出しを内側から展開し、失敗したときは追加したゲートを取り除く。

use super::*;
use super::super::super::templates::{FunctionTemplates, ResolvedExpressionCall, ResolvedNorRoot};
#[cfg(verus_only)]
use super::super::{Layouts, LoweringBody};
#[cfg(verus_only)]
use super::super::super::templates::ResolvedTemplateCall;
use crate::project::{FunctionExpansionOrder, UseAliases};
#[cfg(verus_only)]
use super::super::{existing_wires_keep_availability, port_values};
#[cfg(verus_only)]
use super::super::super::instances::{instance_evaluates_from_caller, instance_wire_values};
#[cfg(verus_only)]
use super::super::super::frontend::{
    argument_matches_width, expression_argument_matches_width, expression_input_width, expression_output_bits,
    nested_argument_output_matches,
    nor_root_arguments_match_widths, root_argument_matches_width, selected_child_output_matches,
};
#[cfg(verus_only)]
use super::super::mixed::resolved_call_fits_body;
#[cfg(verus_only)]
use crate::netlist::{gate_values_match, nor_evaluation, output_values_match};

verus! {

/// 後順の一項目。参照添字は、この定義の先頭の参照を起点とする。
pub(in crate::project::use_aliases::bit_func::lowering) struct ChildCall<'s, 'p, 'a> {
    pub(in crate::project::use_aliases::bit_func::lowering) reference: usize,
    /// 容量診断で示す元の呼び出し式全体の範囲。
    pub(in crate::project::use_aliases::bit_func::lowering) expression: &'s LocatedName<'p, 'a>,
    pub(in crate::project::use_aliases::bit_func::lowering) arguments: &'s [ProjectedCallArgument],
    pub(in crate::project::use_aliases::bit_func::lowering) inputs: &'s PortBitLayout,
    pub(in crate::project::use_aliases::bit_func::lowering) circuit: &'s NorNetlist,
    pub(in crate::project::use_aliases::bit_func::lowering) _input_widths: Ghost<Seq<u64>>,
    pub(in crate::project::use_aliases::bit_func::lowering) _layout_limit: Ghost<usize>,
}

pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_call_abi(call: ChildCall) -> bool {
    &&& port_bit_layout_result(call._input_widths@, call._layout_limit@, Ok(*call.inputs))
    &&& call.arguments@.len() == call.inputs.ranges_model().len() == call._input_widths@.len()
    &&& nor_evaluation_ready(call.circuit, call.inputs.total_bits_model() as nat)
}

pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_call_binding(
    selected: ResolvedExpressionCall, references: Range<usize>, builtin: &(NorNetlist, PortBitLayout), call: ChildCall,
) -> bool {
    &&& references.start <= selected.child.reference < references.end
    &&& call.reference == selected.child.reference - references.start
    &&& *call.expression == selected.child.expression
    &&& call.arguments@ == selected.arguments@
    &&& child_call_abi(call)
    &&& match selected.template {
        Some(template) => {
            &&& call.inputs == template.circuit_model().input_layout_model()
            &&& call.circuit == template.circuit_model().netlist_model()
            &&& call._input_widths@ == template.input_widths_model()
            &&& call._layout_limit@ == template.bit_limit_model()
        },
        None => builtin_nor_call_matches(builtin) && *call.inputs == builtin.1 && *call.circuit == builtin.0
            && call._input_widths@ == seq![1u64, 1u64] && call._layout_limit@ == 2,
    }
}

/// 子を後順に保ち、定義の参照区間を起点とする添字で実引数、入力配置、回路を結び付ける。
pub(in crate::project::use_aliases::bit_func::lowering) fn bind_child_calls<'s, 'p, 'a>(
    references: &Range<usize>, selected: &'s [ResolvedExpressionCall<'s, 'p, 'a>],
    builtin: &'s (NorNetlist, PortBitLayout),
    Ghost(aliases): Ghost<&UseAliases<'_, 'p, 'a>>,
    _context: Ghost<(&FunctionExpansionOrder<'p, 'a>, &FunctionTemplates<'p, 'a>, u64, Seq<ProjectedCallArgument>)>,
    Ghost(source): Ghost<&ProjectSource<'a>>,
    Ghost(postorder): Ghost<Option<Vec<super::super::super::expansion::PreparedExpressionCall<'p, 'a>>>>,
) -> (bound: (usize, Vec<ChildCall<'s, 'p, 'a>>))
    requires
        aliases.expression_children_in_reference_range(*references, source, postorder),
        aliases.resolved_expression_calls_match(_context@.0, _context@.1, _context@.2, postorder, _context@.3, selected@),
        builtin_nor_call_matches(builtin),
    ensures
        bound.0 == references.end - references.start,
        bound.1@.len() == selected@.len(),
        forall|i: int| 0 <= i < bound.1@.len() ==>
            (#[trigger] bound.1@[i]).reference < bound.0
            && location_in_source(*bound.1@[i].expression)
            && *bound.1@[i].expression.source == *source
            && child_call_binding(selected@[i], *references, builtin, bound.1@[i]),
        forall|i: int, j: int| 0 <= i < j < bound.1@.len() ==>
            (#[trigger] bound.1@[i]).reference != (#[trigger] bound.1@[j]).reference,
{
    let count = references.end - references.start;
    let mut calls: Vec<ChildCall<'s, 'p, 'a>> = Vec::new();
    let mut index = 0;
    while index < selected.len()
        invariant
            count == references.end - references.start,
            aliases.expression_children_in_reference_range(*references, source, postorder),
            aliases.resolved_expression_calls_match(_context@.0, _context@.1, _context@.2, postorder,
                _context@.3, selected@),
            builtin_nor_call_matches(builtin),
            index == calls@.len() <= selected@.len(),
            forall|i: int| 0 <= i < calls@.len() ==>
                (#[trigger] calls@[i]).reference < count
                && location_in_source(*calls@[i].expression)
                && *calls@[i].expression.source == *source
                && child_call_binding(selected@[i], *references, builtin, calls@[i]),
        decreases selected@.len() - index,
    {
        let child = &selected[index];
        proof {
            reveal(UseAliases::resolved_expression_call_matches);
            assert(postorder is Some);
            let row = postorder->Some_0@[index as int];
            assert(aliases.resolved_expression_call_matches(_context@.0, _context@.1, _context@.2, _context@.3, row, *child));
            assert(references.start <= child.child.reference < references.end);
        }
        let reference = child.child.reference - references.start;
        let call = if let Some(template) = child.template {
            proof {
                let target = _context@.0.position_model(child.child._rank@->Some_0)->Some_0;
                aliases.template_circuit_evidence(target, _context@.2, template);
                aliases.template_port_evidence(target, _context@.2, template);
                aliases.template_port_counts(template.signature_model(), _context@.2, template.input_widths_model(),
                    template.output_widths_model(), template.structure_layouts_model());
                port_bit_layout_size(template.input_widths_model(), template.bit_limit_model(),
                    template.circuit_model().input_layout_model());
            }
            let circuit = template.circuit();
            ChildCall { reference, expression: &child.child.expression,
                arguments: child.arguments, inputs: circuit.inputs(), circuit: circuit.netlist(),
                _input_widths: Ghost(template.input_widths_model()), _layout_limit: Ghost(template.bit_limit_model()) }
        } else {
            let ghost widths = seq![1u64, 1u64];
            proof { port_bit_layout_size(widths, 2, &builtin.1); }
            ChildCall { reference, expression: &child.child.expression,
                arguments: child.arguments, inputs: &builtin.1, circuit: &builtin.0,
                _input_widths: Ghost(widths), _layout_limit: Ghost(2usize) }
        };
        assert(child_call_binding(*child, *references, builtin, call));
        let ghost before = calls@;
        calls.push(call);
        assert forall|i: int| 0 <= i < calls@.len() implies
            (#[trigger] calls@[i]).reference < count
                && location_in_source(*calls@[i].expression)
                && *calls@[i].expression.source == *source
                && child_call_binding(selected@[i], *references, builtin, calls@[i]) by {
            if i < index { assert(calls@[i] == before[i]); }
        };
        index += 1;
    }
    proof {
        assert forall|i: int, j: int| 0 <= i < j < calls@.len() implies
            (#[trigger] calls@[i]).reference != (#[trigger] calls@[j]).reference by {
            reveal(UseAliases::resolved_expression_call_matches);
            let rows = postorder->Some_0;
            assert(*selected@[i].child == rows@[i] && *selected@[j].child == rows@[j]);
            assert(rows@[i].reference != rows@[j].reference);
        };
    }
    (count, calls)
}

/// 通常関数を根とする呼び出しで、根と子の全実引数が幅に合う配線を読めることを示す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn bound_template_arguments_ready(
    selected: &ResolvedTemplateCall, builtin: &(NorNetlist, PortBitLayout),
    caller: &CallerArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize,
    width_limit: u64, calls: Seq<ChildCall>,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        caller.source == selected.group.expression.source,
        caller.inputs@ == layouts.inputs.ranges_model(),
        caller.definitions@ == layouts.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body.definitions@), selected.group.outputs.start as nat),
        resolved_call_fits_body(*selected, body.input_widths@, body.definitions@, caller.forms@, width_limit),
        port_bit_layout_result(selected.template.input_widths_model(), selected.template.bit_limit_model(),
            Ok(*selected.template.circuit_model().input_layout_model())),
        selected.arguments@.len() == selected.template.input_widths_model().len(),
        calls.len() == selected.children@.len(),
        forall|i: int| 0 <= i < calls.len() ==>
            child_call_binding(selected.children@[i], selected.group.references, builtin, #[trigger] calls[i]),
    ensures
        forall|i: int| 0 <= i < calls.len() ==> #[trigger] child_call_ready(caller, calls, i),
        root_arguments_fit_children(caller, calls, selected.arguments@, selected.template.circuit_model().input_layout_model()),
{
    assert forall|i: int| 0 <= i < calls.len() implies #[trigger] child_call_ready(caller, calls, i) by {
        assert(child_call_binding(selected.children@[i], selected.group.references, builtin, calls[i]));
        assert forall|port: int| 0 <= port < selected.children@[i].arguments@.len() implies
            #[trigger] expression_argument_matches_width(caller.source, caller.forms@, body.input_widths@,
                body.definitions@, *selected, i, port, width_limit) by {
            assert(expression_argument_matches_width(caller.source, caller.forms@, body.input_widths@,
                body.definitions@, *selected, i, port, width_limit));
        };
        bound_child_call_ready(body, layouts, capacity, width_limit, caller, *selected, builtin, calls, i);
    };
    bound_root_arguments_ready(body, layouts, capacity, width_limit, caller, *selected, builtin, calls);
}

/// 子を一件ずつ処理した境界の、検証に使う配線表とゲート列。
#[cfg(verus_only)]
pub(in crate::project::use_aliases::bit_func::lowering) struct ChildWiringSnapshot {
    pub(in crate::project::use_aliases::bit_func::lowering) table: ChildOutputWires,
    pub(in crate::project::use_aliases::bit_func::lowering) gates: Seq<NorGate>,
}

/// 各子の入力配線と出力の変換を、同じ配線表とゲート列で順につなぐ。
#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_wiring_trace_matches(
    caller: &CallerArguments, calls: Seq<ChildCall>, stop: nat, reference_count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot, input_bits: usize,
) -> bool {
    &&& stop <= calls.len()
    &&& trace.len() == stop + 1
    &&& trace[0].table.ranges@.len() == reference_count
    &&& forall|r: int| 0 <= r < reference_count ==> (#[trigger] trace[0].table.ranges@[r]).is_none()
    &&& trace[0].table.wires@.len() == 0
    &&& trace[0].gates == initial
    &&& trace[stop as int] == end
    &&& forall|i: int| 0 <= i < stop ==> {
        let call = calls[i];
        let before = #[trigger] trace[i];
        let after = trace[i + 1];
        child_instance_matches(caller, call.arguments@, call.inputs, call.circuit, &before.table, &after.table,
            call.reference, before.gates, after.gates, input_bits)
    }
}

proof fn extend_child_wiring_trace(
    caller: &CallerArguments, calls: Seq<ChildCall>, index: usize, reference_count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>,
    before: ChildWiringSnapshot, after: ChildWiringSnapshot, input_bits: usize,
)
    requires
        index < calls.len(),
        child_wiring_trace_matches(caller, calls, index as nat, reference_count, initial, trace, before, input_bits),
        ({
            let call = calls[index as int];
            child_instance_matches(caller, call.arguments@, call.inputs, call.circuit, &before.table, &after.table,
                call.reference, before.gates, after.gates, input_bits)
        }),
    ensures child_wiring_trace_matches(
        caller, calls, (index + 1) as nat, reference_count, initial, trace.push(after), after, input_bits),
{
    reveal(child_wiring_trace_matches);
    let extended = trace.push(after);
    assert(extended[0] == trace[0]);
    assert forall|i: int| 0 <= i <= index implies {
        let call = calls[i];
        let prior = #[trigger] extended[i];
        let next = extended[i + 1];
        child_instance_matches(caller, call.arguments@, call.inputs, call.circuit, &prior.table, &next.table,
            call.reference, prior.gates, next.gates, input_bits)
    } by {
        if i < index {
            assert(extended[i] == trace[i] && extended[i + 1] == trace[i + 1]);
        }
    };
}

/// 後から処理した子が、先行する子の出力配線やゲート番号を変えないことを示す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn child_wiring_prefix_preserved(
    caller: &CallerArguments, calls: Seq<ChildCall>, stop: nat, reference_count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot,
    earlier: nat, later: nat, input_bits: usize,
)
    requires
        child_wiring_trace_matches(caller, calls, stop, reference_count, initial, trace, end, input_bits),
        earlier <= later <= stop,
    ensures ({
        let first = trace[earlier as int];
        let last = trace[later as int];
        &&& first.gates.len() <= last.gates.len()
        &&& first.table.wires@.len() <= last.table.wires@.len()
        &&& last.gates.take(first.gates.len() as int) == first.gates
        &&& last.table.wires@.take(first.table.wires@.len() as int) == first.table.wires@
    }),
    decreases later - earlier,
{
    reveal(child_wiring_trace_matches);
    let first = trace[earlier as int];
    let last = trace[later as int];
    if earlier < later {
        let index = later - 1;
        let previous = trace[index];
        let call = calls[index];
        child_wiring_prefix_preserved(caller, calls, stop, reference_count, initial, trace, end,
            earlier, index as nat, input_bits);
        assert(child_instance_matches(caller, call.arguments@, call.inputs, call.circuit,
            &previous.table, &last.table, call.reference, previous.gates, last.gates, input_bits));
        reveal(child_instance_matches);
        assert(last.gates.take(previous.gates.len() as int) == previous.gates);
        assert(last.table.wires@.take(previous.table.wires@.len() as int) == previous.table.wires@);
    }
    assert(last.gates.take(first.gates.len() as int) =~= first.gates);
    assert(last.table.wires@.take(first.table.wires@.len() as int) =~= first.table.wires@);
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
    ensures child_sizes(calls, first).0 <= child_sizes(calls, end).0,
        child_sizes(calls, first).1 <= child_sizes(calls, end).1,
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

proof fn child_wiring_trace_sizes(
    caller: &CallerArguments, calls: Seq<ChildCall>, stop: nat, reference_count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot,
    at: nat, input_bits: usize,
)
    requires
        child_wiring_trace_matches(caller, calls, stop, reference_count, initial, trace, end, input_bits),
        at <= stop,
    ensures
        trace[at as int].table.wires@.len() == child_sizes(calls, at).1,
        trace[at as int].gates.len() == initial.len() + child_sizes(calls, at).0,
        trace[at as int].table.ranges@.len() == reference_count,
    decreases at,
{
    reveal(child_wiring_trace_matches);
    if at == 0 {
        reveal(child_sizes);
    } else {
        let i = at - 1;
        child_wiring_trace_sizes(caller, calls, stop, reference_count, initial, trace, end, i as nat, input_bits);
        child_sizes_step(calls, i);
        let call = calls[i];
        let before = trace[i];
        let after = trace[at as int];
        assert(child_instance_matches(caller, call.arguments@, call.inputs, call.circuit, &before.table, &after.table,
            call.reference, before.gates, after.gates, input_bits));
        reveal(child_instance_matches);
    }
}

/// 子を登録した参照枠は、後続の子を展開した後も同じ配線範囲を指す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn child_output_range_preserved(
    caller: &CallerArguments, calls: Seq<ChildCall>, stop: nat, reference_count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot,
    child: nat, at: nat, input_bits: usize,
)
    requires
        child_wiring_trace_matches(caller, calls, stop, reference_count, initial, trace, end, input_bits),
        child < at <= stop <= calls.len(),
        forall|i: int, j: int| 0 <= i < j < stop ==> (#[trigger] calls[i]).reference != (#[trigger] calls[j]).reference,
    ensures ({
        let reference = calls[child as int].reference as int;
        let table = trace[at as int].table;
        &&& 0 <= reference < table.ranges@.len()
        &&& table.ranges@[reference] == Some((child_sizes(calls, child).1 as usize)
            ..(child_sizes(calls, child + 1).1 as usize))
    }),
    decreases at - child,
{
    reveal(child_wiring_trace_matches);
    let i = at - 1;
    let call = calls[i];
    let before = trace[i];
    let after = trace[at as int];
    assert(child_instance_matches(caller, call.arguments@, call.inputs, call.circuit, &before.table, &after.table,
        call.reference, before.gates, after.gates, input_bits));
    reveal(child_instance_matches);
    let reference = calls[child as int].reference as int;
    if child == i {
        child_wiring_trace_sizes(caller, calls, stop, reference_count, initial, trace, end, i as nat, input_bits);
        child_wiring_trace_sizes(caller, calls, stop, reference_count, initial, trace, end, at, input_bits);
    } else {
        child_output_range_preserved(caller, calls, stop, reference_count, initial, trace, end, child, i as nat, input_bits);
        assert(reference != call.reference);
        assert(after.table.ranges@[reference] == before.table.ranges@[reference]);
    }
}

proof fn child_output_slice_in_final(
    caller: &CallerArguments, calls: Seq<ChildCall>, stop: nat, reference_count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot,
    index: usize, combined: Seq<NorGate>, input_bits: usize,
)
    requires
        child_wiring_trace_matches(caller, calls, stop, reference_count, initial, trace, end, input_bits),
        child_ranges_match(calls, stop, end.table.ranges@),
        index < stop <= calls.len(),
        end.gates.len() <= combined.len() && end.gates == combined.take(end.gates.len() as int),
    ensures ({
        let reference = calls[index as int].reference as int;
        let before = trace[index as int];
        let after = trace[index + 1];
        &&& 0 <= reference < end.table.ranges@.len()
        &&& after.gates.len() <= combined.len()
        &&& after.gates == combined.take(after.gates.len() as int)
        &&& end.table.ranges@[reference] matches Some(range)
            && range.start <= range.end <= end.table.wires@.len()
            && end.table.wires@.subrange(range.start as int, range.end as int)
                == after.table.wires@.subrange(before.table.wires@.len() as int, after.table.wires@.len() as int)
    }),
{
    child_wiring_prefix_preserved(caller, calls, stop, reference_count, initial, trace, end, (index + 1) as nat, stop, input_bits);
    child_wiring_trace_sizes(caller, calls, stop, reference_count, initial, trace, end, index as nat, input_bits);
    child_wiring_trace_sizes(caller, calls, stop, reference_count, initial, trace, end, (index + 1) as nat, input_bits);
    child_sizes_grow(calls, index as nat, (index + 1) as nat);
    assert(trace.len() == stop + 1 && trace[stop as int] == end) by {
        reveal(child_wiring_trace_matches);
    };
    let before = trace[index as int];
    let after = trace[index + 1];
    vstd::std_specs::vec::axiom_spec_len(&before.table.wires);
    vstd::std_specs::vec::axiom_spec_len(&after.table.wires);
    let reference = calls[index as int].reference as int;
    let start = before.table.wires@.len() as int;
    let finish = after.table.wires@.len() as int;
    assert(0 <= reference < end.table.ranges@.len()
        && end.table.ranges@[reference] == Some((start as usize)..(finish as usize))) by {
        reveal(child_ranges_match);
    };
    assert(0 <= start <= finish <= end.table.wires@.len());
    assert(end.table.wires@.subrange(start, finish) =~= after.table.wires@.subrange(start, finish));
    assert(after.gates =~= combined.take(after.gates.len() as int));
}

/// 一つの子の出力範囲から読んだ値は、実引数の値を渡した呼び出し先の評価結果に一致する。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn child_output_evaluates(
    caller: &CallerArguments, calls: Seq<ChildCall>, stop: nat, reference_count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot,
    index: usize, combined: Seq<NorGate>, inputs: Seq<bool>, values: Seq<bool>, input_bits: usize,
) -> (result: (Seq<bool>, Seq<bool>))
    requires
        child_wiring_trace_matches(caller, calls, stop, reference_count, initial, trace, end, input_bits),
        child_ranges_match(calls, stop, end.table.ranges@),
        index < stop <= calls.len(),
        nor_evaluation_ready(calls[index as int].circuit, calls[index as int].inputs.total_bits_model() as nat),
        end.gates.len() <= combined.len() && end.gates == combined.take(end.gates.len() as int),
        gate_values_match(inputs, combined, values), values.len() == combined.len() <= usize::MAX,
        inputs.len() == input_bits,
    ensures ({
        let call = calls[index as int];
        let before = trace[index as int];
        let reference = call.reference as int;
        &&& 0 <= reference < end.table.ranges@.len()
        &&& end.table.ranges@[reference] matches Some(range)
            && range.start <= range.end <= end.table.wires@.len()
            && result.1 == instance_wire_values(end.table.wires@.subrange(range.start as int, range.end as int), inputs, values)
            && output_values_match(inputs, values,
                end.table.wires@.subrange(range.start as int, range.end as int), result.1)
        &&& nor_evaluation(call.circuit, result.0, result.1)
        &&& exists|invocation: CallerArguments, mapped: Seq<Wire>|
            #[trigger] argument_prefix_wires(&invocation, call.arguments@, call.inputs.ranges_model(), call.arguments@.len() as int, mapped)
            && invocation.source == caller.source && invocation.forms@ == caller.forms@
            && invocation.inputs@ == caller.inputs@ && invocation.definitions@ == caller.definitions@
            && invocation.wires@ == caller.wires@
            && invocation.child_ranges@ == before.table.ranges@ && invocation.child_wires@ == before.table.wires@
            && mapped.len() == call.inputs.total_bits_model()
            && result.0 == instance_wire_values(mapped, inputs, values)
    }),
{
    reveal(child_wiring_trace_matches);
    let call = calls[index as int];
    let before = trace[index as int];
    let after = trace[index + 1];
    assert(child_instance_matches(caller, call.arguments@, call.inputs, call.circuit, &before.table, &after.table,
        call.reference, before.gates, after.gates, input_bits));
    reveal(child_instance_matches);
    let (invocation, mapped) = choose|invocation: CallerArguments, mapped: Seq<Wire>|
        #[trigger] argument_prefix_wires(&invocation, call.arguments@, call.inputs.ranges_model(), call.arguments@.len() as int, mapped)
        && invocation.source == caller.source && invocation.forms@ == caller.forms@
        && invocation.inputs@ == caller.inputs@ && invocation.definitions@ == caller.definitions@
        && invocation.wires@ == caller.wires@
        && invocation.child_ranges@ == before.table.ranges@ && invocation.child_wires@ == before.table.wires@
        && mapped.len() == call.inputs.total_bits_model()
        && wires_available(mapped, input_bits, before.gates.len())
        && child_outputs_appended(&before.table, &after.table, call.reference, call.circuit, mapped,
            before.gates, after.gates, input_bits);
    child_output_slice_in_final(caller, calls, stop, reference_count, initial, trace, end, index, combined, input_bits);
    let range = end.table.ranges@[call.reference as int]->Some_0;
    let outputs = end.table.wires@.subrange(range.start as int, range.end as int);
    reveal(wires_available);
    instance_evaluates_from_caller(before.gates, call.circuit, combined, mapped, outputs, inputs, values);
    (instance_wire_values(mapped, inputs, values), instance_wire_values(outputs, inputs, values))
}

/// 先行する子の出力配線を読むと、後続の呼び出しの指定ポートの値になる。
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_port_reads_producer(
    calls: Seq<ChildCall>, end: ChildWiringSnapshot, producer: usize, consumer: usize, port: usize,
    arguments: Seq<bool>, inputs: Seq<bool>, values: Seq<bool>,
) -> bool {
    let call = calls[consumer as int];
    let reference = calls[producer as int].reference;
    &&& producer < consumer < calls.len()
    &&& port < call.arguments@.len() && port < call.inputs.ranges_model().len() && port < call._input_widths@.len()
    &&& call.arguments@[port as int].source == CallArgumentSource::NestedCall(reference)
    &&& reference < end.table.ranges@.len()
    &&& end.table.ranges@[reference as int] matches Some(range)
    &&& range.start <= range.end <= end.table.wires@.len()
    &&& range.end - range.start == call._input_widths@[port as int]
    &&& port_values(call.inputs, arguments)[port as int]
        == instance_wire_values(end.table.wires@.subrange(range.start as int, range.end as int), inputs, values)
}

/// 後続の子が実際に読んだポートから、同じ値を出した先行子を求める。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn child_nested_port_value(
    caller: &CallerArguments, calls: Seq<ChildCall>, stop: nat, reference_count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot,
    consumer: usize, port: usize, invocation: &CallerArguments, mapped: Seq<Wire>,
    inputs: Seq<bool>, values: Seq<bool>, input_bits: usize,
) -> (producer: usize)
    requires
        child_wiring_trace_matches(caller, calls, stop, reference_count, initial, trace, end, input_bits),
        child_ranges_match(calls, stop, end.table.ranges@),
        consumer < stop <= calls.len(),
        forall|i: int, j: int| 0 <= i < j < stop ==> (#[trigger] calls[i]).reference != (#[trigger] calls[j]).reference,
        child_call_ready(caller, calls, consumer as int),
        port < calls[consumer as int].arguments@.len(),
        calls[consumer as int].arguments@[port as int].source is NestedCall,
        invocation.child_ranges@ == trace[consumer as int].table.ranges@,
        invocation.child_wires@ == trace[consumer as int].table.wires@,
        ({
            let call = calls[consumer as int];
            &&& argument_prefix_wires(invocation, call.arguments@, call.inputs.ranges_model(),
                call.arguments@.len() as int, mapped)
            &&& mapped.len() == call.inputs.total_bits_model()
        }),
    ensures child_port_reads_producer(calls, end, producer, consumer, port,
        instance_wire_values(mapped, inputs, values), inputs, values),
{
    let call = calls[consumer as int];
    assert(child_call_abi(call)) by { reveal(child_call_ready); };
    assert(trace.len() == stop + 1 && trace[stop as int] == end) by {
        reveal(child_wiring_trace_matches);
    };
    let before = trace[consumer as int];
    let reference = call.arguments@[port as int].source->NestedCall_0;
    let dest = call.inputs.ranges_model()[port as int];
    port_bit_layout_port(call._input_widths@, call._layout_limit@, *call.inputs, port);
    assert(exists|i: int| 0 <= i < consumer && (#[trigger] calls[i]).reference == reference
        && calls[i].circuit.outputs@.len() == (dest.end - dest.start) as usize) by {
        reveal(child_call_ready);
    };
    let child = choose|i: int| 0 <= i < consumer && (#[trigger] calls[i]).reference == reference
        && calls[i].circuit.outputs@.len() == (dest.end - dest.start) as usize;
    child_output_range_preserved(caller, calls, stop, reference_count, initial, trace, end,
        child as nat, consumer as nat, input_bits);
    child_wiring_trace_sizes(caller, calls, stop, reference_count, initial, trace, end, consumer as nat, input_bits);
    vstd::std_specs::vec::axiom_spec_len(&before.table.wires);
    child_sizes_grow(calls, (child + 1) as nat, consumer as nat);
    child_sizes_step(calls, child as int);
    let range = before.table.ranges@[reference as int]->Some_0;
    assert(range.start <= range.end <= before.table.wires@.len());
    assert(range.end - range.start == dest.end - dest.start == call._input_widths@[port as int]);
    reveal(child_ranges_match);
    assert(end.table.ranges@[reference as int] == Some(range));
    child_wiring_prefix_preserved(caller, calls, stop, reference_count, initial, trace, end, consumer as nat, stop, input_bits);
    assert(invocation.child_wires@.subrange(range.start as int, range.end as int)
        =~= end.table.wires@.subrange(range.start as int, range.end as int));
    lowered_nested_argument_port_value(invocation, call.arguments@, call.inputs, call._input_widths@, call._layout_limit@,
        mapped, inputs, values, port, reference);
    child as usize
}

#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_call_ready(
    caller: &CallerArguments, calls: Seq<ChildCall>, index: int,
) -> bool {
    &&& 0 <= index < calls.len()
    &&& ({
        let call = calls[index];
        &&& child_call_abi(call)
        &&& arguments_fit_preceding_children(caller, calls, index, call.arguments@, call.inputs)
    })
}

/// 型検査済みの実引数と割り当て済みの範囲から、後順の一項目を展開できることを示す。
///
/// 定義を読む引数は左辺より先行する配線を参照し、入れ子の引数は後順で先行する子の出力を参照する。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn bound_child_call_ready(
    body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    caller: &CallerArguments, selected: ResolvedTemplateCall, builtin: &(NorNetlist, PortBitLayout),
    calls: Seq<ChildCall>, index: int,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        selected.group.outputs.start <= body.definitions@.len(),
        caller.source == selected.group.expression.source,
        caller.inputs@ == layouts.inputs.ranges_model(),
        caller.definitions@ == layouts.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body.definitions@), selected.group.outputs.start as nat),
        0 <= index < calls.len() == selected.children@.len(),
        forall|i: int| 0 <= i < calls.len() ==>
            child_call_binding(selected.children@[i], selected.group.references, builtin, #[trigger] calls[i]),
        forall|port: int| 0 <= port < selected.children@[index].arguments@.len() ==>
            #[trigger] expression_argument_matches_width(caller.source, caller.forms@, body.input_widths@,
                body.definitions@, selected, index, port, width_limit),
    ensures child_call_ready(caller, calls, index),
{
    let call = calls[index];
    let child = selected.children@[index];
    reveal(child_call_ready);
    assert(child_call_binding(child, selected.group.references, builtin, call));
    assert forall|port: int| 0 <= port < call.arguments@.len() implies {
        let argument = #[trigger] call.arguments@[port];
        let width = call._input_widths@[port];
        &&& argument_matches_width(caller.source, caller.forms@, body.input_widths@,
            body.definitions@.take(selected.group.outputs.start as int), argument, width, width_limit)
        &&& selected_child_output_matches(selected.children@, selected.group.references.start, index, argument, width)
    } by {
        reveal(nested_argument_output_matches);
        let argument = call.arguments@[port];
        assert(argument == child.arguments@[port]);
        assert(call._input_widths@[port] == expression_input_width(child, port));
        assert(expression_argument_matches_width(caller.source, caller.forms@, body.input_widths@,
            body.definitions@, selected, index, port, width_limit));
    };
    bound_arguments_ready(body, layouts, capacity, width_limit, caller, selected.group.outputs.start,
        selected.group.references, selected.children@, builtin, calls, index,
        call.arguments@, call.inputs, call._input_widths@, call._layout_limit@);
}

/// 選択時に確定した子の出力幅を、同じ位置にある配線用の回路へ引き継ぐ。
proof fn bound_argument_output_width(
    children: Seq<ResolvedExpressionCall>, references: Range<usize>, builtin: &(NorNetlist, PortBitLayout), calls: Seq<ChildCall>,
    before: int, argument: ProjectedCallArgument, width: u64,
)
    requires
        calls.len() == children.len(),
        forall|i: int| 0 <= i < calls.len() ==>
            child_call_binding(children[i], references, builtin, #[trigger] calls[i]),
        argument.source is NestedCall,
        selected_child_output_matches(children, references.start, before, argument, width),
    ensures exists|i: int| 0 <= i < before <= calls.len()
        && (#[trigger] calls[i]).reference == argument.source->NestedCall_0
        && calls[i].circuit.outputs@.len() == width,
{
    let reference = argument.source->NestedCall_0;
    let earlier = choose|i: int| 0 <= i < before
        && (#[trigger] children[i]).child.reference == references.start + reference
        && expression_output_bits(children[i]) == width;
    let call = calls[earlier];
    let producer = children[earlier];
    assert(child_call_binding(producer, references, builtin, call));
    assert(call.reference == reference);
    assert(call.circuit.outputs@.len() == expression_output_bits(producer));
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

/// 展開済みの子の範囲は、一時配線表の内部にあり、その子の出力本数と同じ幅を持つ。
proof fn produced_child_argument_ready(
    calls: Seq<ChildCall>, stop: nat, ranges: Seq<Option<Range<usize>>>, wires: nat,
    earlier: int, reference: usize, width: usize,
)
    requires
        child_ranges_match(calls, stop, ranges),
        wires == child_sizes(calls, stop).1 <= usize::MAX,
        0 <= earlier < stop,
        calls[earlier].reference == reference,
        calls[earlier].circuit.outputs@.len() == width,
    ensures
        projected_source_available(ranges, CallArgumentSource::NestedCall(reference)),
        child_argument_width_ready(ranges, wires, CallArgumentSource::NestedCall(reference), width),
{
    reveal(child_ranges_match);
    child_sizes_grow(calls, (earlier + 1) as nat, stop);
    child_sizes_step(calls, earlier);
    assert(ranges[reference as int] == Some((child_sizes(calls, earlier as nat).1 as usize)
        ..(child_sizes(calls, (earlier + 1) as nat).1 as usize)));
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
        wires <= usize::MAX,
        forall|i: int, j: int| 0 <= i < j < calls.len() ==>
            (#[trigger] calls[i]).reference != (#[trigger] calls[j]).reference,
    ensures ({
        let call = calls[index as int];
        &&& ranges[call.reference as int].is_none()
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
            produced_child_argument_ready(calls, index as nat, ranges, wires, earlier, reference,
                (span.end - span.start) as usize);
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

pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_wiring_failure(
    caller: &CallerArguments, calls: Seq<ChildCall>, index: usize, error: ChildCallWiringError,
    initial_gates: int, capacity: usize, output_capacity: usize,
) -> bool {
    &&& index < calls.len()
    &&& child_arguments_determined(calls, index as nat)
    &&& initial_gates + child_sizes(calls, index as nat).0 <= capacity
    &&& child_sizes(calls, index as nat).1 <= output_capacity
    &&& match error {
        ChildCallWiringError::DeferredArgument(site) => {
            let projected = calls[index as int].arguments@;
            exists|port: int| 0 <= port < projected.len() && (#[trigger] projected[port]).source is Deferred
                && is_form_location(caller.source, caller.forms@[projected[port].form as int], site)
                && forall|j: int| 0 <= j < port ==> !((#[trigger] projected[j]).source is Deferred)
        },
        ChildCallWiringError::GateCapacity(site) =>
            site == *calls[index as int].expression
            && initial_gates + child_sizes(calls, (index + 1) as nat).0 > capacity
            && child_arguments_determined(calls, (index + 1) as nat),
        ChildCallWiringError::OutputCapacity { site, used, width, capacity: available } => {
            &&& site == *calls[index as int].expression
            &&& available == output_capacity
            &&& used == child_sizes(calls, index as nat).1
            &&& width == calls[index as int].circuit.outputs@.len()
            &&& child_sizes(calls, (index + 1) as nat).1 == used + width > output_capacity
            &&& initial_gates + child_sizes(calls, (index + 1) as nat).0 <= capacity
            &&& child_arguments_determined(calls, (index + 1) as nat)
        },
    }
}

/// 後順の子を展開し、全件に成功したときだけ一時配線表を返す。
///
/// # Errors
///
/// 最初に失敗した子の位置と診断を返す。その場合は、この処理を始める前のゲート列を保つ。
/// 一時配線表の上限は、呼び出し元のポートや定義に割り当てるビット数とは独立に指定する。
pub(in crate::project::use_aliases::bit_func::lowering) fn lower_child_calls<'s, 'p, 'a>(
    caller: &CallerArguments<'s, 'p, 'a>, calls: &[ChildCall<'s, 'p, 'a>], reference_count: usize,
    gates: &mut Vec<NorGate>, capacity: usize, output_capacity: usize, Ghost(input_bits): Ghost<usize>,
) -> (result: Result<ChildOutputWires, (usize, ChildCallWiringError<'p, 'a>)>)
    requires
        form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
        old(gates)@.len() <= capacity,
        gates_available(old(gates)@, input_bits as nat, old(gates)@.len() as int),
        wires_available(caller.wires@, input_bits, old(gates)@.len()),
        forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
        forall|i: int| 0 <= i < calls@.len() ==>
            (#[trigger] calls@[i]).reference < reference_count && child_call_ready(caller, calls@, i)
            && location_in_source(*calls@[i].expression) && *calls@[i].expression.source == *caller.source,
        forall|i: int, j: int| 0 <= i < j < calls@.len() ==>
            (#[trigger] calls@[i]).reference != (#[trigger] calls@[j]).reference,
    ensures
        result.is_ok() <==> child_arguments_determined(calls@, calls@.len())
            && old(gates)@.len() + child_sizes(calls@, calls@.len()).0 <= capacity
            && child_sizes(calls@, calls@.len()).1 <= output_capacity,
        result matches Ok(table) ==> {
            &&& table.ranges@.len() == reference_count
            &&& child_ranges_match(calls@, calls@.len(), table.ranges@)
            &&& table.wires@.len() == child_sizes(calls@, calls@.len()).1 <= output_capacity
            &&& final(gates)@.len() == old(gates)@.len() + child_sizes(calls@, calls@.len()).0 <= capacity
            &&& final(gates)@.take(old(gates)@.len() as int) == old(gates)@
            &&& gates_available(final(gates)@, input_bits as nat, final(gates)@.len() as int)
            &&& wires_available(table.wires@, input_bits, final(gates)@.len())
            &&& child_arguments_determined(calls@, calls@.len())
            &&& exists|trace: Seq<ChildWiringSnapshot>| #[trigger] child_wiring_trace_matches(
                caller, calls@, calls@.len(), reference_count, old(gates)@, trace,
                ChildWiringSnapshot { table, gates: final(gates)@ }, input_bits)
        },
        result matches Err((i, error)) ==> final(gates)@ == old(gates)@
            && child_wiring_failure(caller, calls@, i, error, old(gates)@.len() as int, capacity, output_capacity),
{
    let mut table = ChildOutputWires::new(reference_count);
    let checkpoint = gates.len();
    let ghost initial = gates@;
    let ghost first = ChildWiringSnapshot { table, gates: initial };
    let ghost mut trace = seq![first];
    let mut index = 0;
    proof {
        assert(child_sizes(calls@, 0) == (0nat, 0nat)) by { reveal(child_sizes); };
        reveal(wires_available);
        assert(child_ranges_match(calls@, 0, table.ranges@)) by { reveal(child_ranges_match); };
        assert(gates@.take(checkpoint as int) =~= initial);
        assert(child_wiring_trace_matches(caller, calls@, 0, reference_count, initial, trace, first, input_bits)) by {
            reveal(child_wiring_trace_matches);
        };
    }
    while index < calls.len()
        invariant
            index <= calls@.len(), checkpoint == initial.len(), initial == old(gates)@,
            table.ranges@.len() == reference_count,
            child_ranges_match(calls@, index as nat, table.ranges@),
            child_arguments_determined(calls@, index as nat),
            child_wiring_trace_matches(caller, calls@, index as nat, reference_count, initial,
                trace, ChildWiringSnapshot { table, gates: gates@ }, input_bits),
            table.wires@.len() == child_sizes(calls@, index as nat).1 <= output_capacity,
            gates@.len() == checkpoint + child_sizes(calls@, index as nat).0 <= capacity,
            gates@.take(checkpoint as int) == initial,
            gates_available(gates@, input_bits as nat, gates@.len() as int),
            wires_available(caller.wires@, input_bits, gates@.len()),
            wires_available(table.wires@, input_bits, gates@.len()),
            form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
            forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
            forall|i: int| 0 <= i < calls@.len() ==>
                (#[trigger] calls@[i]).reference < reference_count && child_call_ready(caller, calls@, i)
                && location_in_source(*calls@[i].expression) && *calls@[i].expression.source == *caller.source,
            forall|i: int, j: int| 0 <= i < j < calls@.len() ==>
                (#[trigger] calls@[i]).reference != (#[trigger] calls@[j]).reference,
        decreases calls@.len() - index,
    {
        let call = &calls[index];
        let ghost ranges = table.ranges@;
        let ghost before = gates@;
        let ghost previous = ChildWiringSnapshot { table, gates: before };
        proof {
            child_sizes_step(calls@, index as int);
            next_child_readiness(caller, calls@, index, ranges, table.wires@.len());
        }
        let error = lower_child_call(caller, call.arguments, call.inputs, call.circuit, &mut table,
            call.reference, gates, capacity, output_capacity, call.expression,
            Ghost(call._input_widths@), Ghost(call._layout_limit@), Ghost(input_bits));
        if let Err(error) = error {
            proof {
                child_sizes_grow(calls@, (index + 1) as nat, calls@.len());
                match &error {
                    ChildCallWiringError::GateCapacity(_) => {
                        extend_determined_children(calls@, index, ranges);
                        assert(checkpoint + child_sizes(calls@, (index + 1) as nat).0 > capacity);
                    },
                    ChildCallWiringError::OutputCapacity { .. } => {
                        extend_determined_children(calls@, index, ranges);
                        assert(checkpoint + child_sizes(calls@, (index + 1) as nat).0 <= capacity);
                        assert(child_sizes(calls@, (index + 1) as nat).1 > output_capacity);
                    },
                    ChildCallWiringError::DeferredArgument(site) => {
                        let arguments = call.arguments@;
                        let port = choose|port: int| 0 <= port < arguments.len()
                            && !projected_source_available(ranges, (#[trigger] arguments[port]).source)
                            && is_form_location(caller.source, caller.forms@[arguments[port].form as int], *site)
                            && forall|j: int| 0 <= j < port ==> projected_source_available(ranges, (#[trigger] arguments[j]).source);
                        assert(arguments[port].source is Deferred);
                        assert(!child_arguments_determined(calls@, calls@.len()));
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
            let next = ChildWiringSnapshot { table, gates: gates@ };
            extend_child_wiring_trace(caller, calls@, index, reference_count, initial, trace, previous, next, input_bits);
            trace = trace.push(next);
        }
        index += 1;
    }
    Ok(table)
}

/// 後順の子と根を配線するとき、どちらの段階で失敗したかを保持する。
#[derive(Debug)]
pub(in crate::project::use_aliases::bit_func::lowering) enum NestedCallWiringError<'p, 'a> {
    /// 最初に失敗した子の後順添字と診断。
    Child(usize, ChildCallWiringError<'p, 'a>),
    /// 子の展開後に、根の引数または容量を検査して得た診断。
    Root(CallWiringError<'p, 'a>),
}

pub(in crate::project::use_aliases::bit_func::lowering) open spec fn root_arguments_fit_children(
    caller: &CallerArguments, calls: Seq<ChildCall>, arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout,
) -> bool {
    arguments_fit_preceding_children(caller, calls, calls.len() as int, arguments, layout)
}

/// 配線を読む時点より前に展開した子だけを、入れ子の引数から参照できる。
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn arguments_fit_preceding_children(
    caller: &CallerArguments, calls: Seq<ChildCall>, before: int,
    arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout,
) -> bool {
    &&& 0 <= before <= calls.len()
    &&& arguments.len() == layout.ranges_model().len()
    &&& forall|port: int| 0 <= port < arguments.len() ==> {
        let argument = #[trigger] arguments[port];
        let span = layout.ranges_model()[port];
        let width = (span.end - span.start) as usize;
        &&& layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
            caller.wires@.len() as int, argument, width)
        &&& if let CallArgumentSource::NestedCall(reference) = argument.source {
            exists|i: int| 0 <= i < before && (#[trigger] calls[i]).reference == reference
                && calls[i].circuit.outputs@.len() == width
        } else { true }
    }
}

/// 根の各入力幅を、先行配線または子の出力本数に対応付ける。
proof fn bound_root_arguments_ready(
    body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    caller: &CallerArguments, selected: ResolvedTemplateCall, builtin: &(NorNetlist, PortBitLayout),
    calls: Seq<ChildCall>,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        caller.source == selected.group.expression.source,
        caller.inputs@ == layouts.inputs.ranges_model(),
        caller.definitions@ == layouts.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body.definitions@), selected.group.outputs.start as nat),
        resolved_call_fits_body(selected, body.input_widths@, body.definitions@, caller.forms@, width_limit),
        port_bit_layout_result(selected.template.input_widths_model(), selected.template.bit_limit_model(),
            Ok(*selected.template.circuit_model().input_layout_model())),
        selected.arguments@.len() == selected.template.input_widths_model().len(),
        calls.len() == selected.children@.len(),
        forall|i: int| 0 <= i < calls.len() ==>
            child_call_binding(selected.children@[i], selected.group.references, builtin, #[trigger] calls[i]),
    ensures root_arguments_fit_children(caller, calls, selected.arguments@, selected.template.circuit_model().input_layout_model()),
{
    let layout = selected.template.circuit_model().input_layout_model();
    let widths = selected.template.input_widths_model();
    assert forall|port: int| 0 <= port < selected.arguments@.len() implies {
        let argument = #[trigger] selected.arguments@[port];
        let width = widths[port];
        &&& argument_matches_width(caller.source, caller.forms@, body.input_widths@,
            body.definitions@.take(selected.group.outputs.start as int), argument, width, width_limit)
        &&& selected_child_output_matches(selected.children@, selected.group.references.start,
            calls.len() as int, argument, width)
    } by {
        reveal(nested_argument_output_matches);
        assert(root_argument_matches_width(caller.source, caller.forms@, body.input_widths@,
            body.definitions@, selected, port, width_limit));
    };
    bound_arguments_ready(body, layouts, capacity, width_limit, caller, selected.group.outputs.start,
        selected.group.references, selected.children@, builtin, calls, calls.len() as int,
        selected.arguments@, layout, widths, selected.template.bit_limit_model());
}

/// 型検査済みの入力幅とポート配置から、先行配線と展開済みの子の出力を読めることを示す。
proof fn bound_arguments_ready(
    body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    caller: &CallerArguments, first_output: usize, references: Range<usize>, children: Seq<ResolvedExpressionCall>,
    builtin: &(NorNetlist, PortBitLayout), calls: Seq<ChildCall>, before: int,
    arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout, widths: Seq<u64>, layout_limit: usize,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        first_output <= body.definitions@.len(),
        caller.inputs@ == layouts.inputs.ranges_model(),
        caller.definitions@ == layouts.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body.definitions@), first_output as nat),
        port_bit_layout_result(widths, layout_limit, Ok(*layout)),
        arguments.len() == widths.len(),
        0 <= before <= calls.len() == children.len(),
        forall|i: int| 0 <= i < calls.len() ==>
            child_call_binding(children[i], references, builtin, #[trigger] calls[i]),
        forall|port: int| 0 <= port < arguments.len() ==> {
            let argument = #[trigger] arguments[port];
            let width = widths[port];
            &&& argument_matches_width(caller.source, caller.forms@, body.input_widths@,
                body.definitions@.take(first_output as int), argument, width, width_limit)
            &&& selected_child_output_matches(children, references.start, before, argument, width)
        },
    ensures arguments_fit_preceding_children(caller, calls, before, arguments, layout),
{
    port_bit_layout_size(widths, layout_limit, layout);
    assert forall|port: int| 0 <= port < arguments.len() implies {
        let argument = #[trigger] arguments[port];
        let span = layout.ranges_model()[port];
        let width = (span.end - span.start) as usize;
        &&& layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
            caller.wires@.len() as int, argument, width)
        &&& if let CallArgumentSource::NestedCall(reference) = argument.source {
            exists|i: int| 0 <= i < before && (#[trigger] calls[i]).reference == reference
                && calls[i].circuit.outputs@.len() == width
        } else { true }
    } by {
        let argument = arguments[port];
        let bits = widths[port];
        port_bit_layout_port(widths, layout_limit, *layout, port as usize);
        let span = layout.ranges_model()[port];
        assert(0 < span.end - span.start == bits <= usize::MAX);
        layout_argument_from_width(body, layouts, capacity, first_output, caller.source,
            caller.forms@, argument, bits, width_limit);
        if argument.source is NestedCall {
            bound_argument_output_width(children, references, builtin, calls, before, argument, bits);
        }
    };
}

/// 子の開始状態から、子の出力を読む根の実引数と展開後の出力までをつなぐ。
#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn nested_root_wiring_matches(
    caller: &CallerArguments, calls: Seq<ChildCall>, count: usize, arguments: Seq<ProjectedCallArgument>,
    layout: &PortBitLayout, callee: &NorNetlist, initial: Seq<NorGate>, final_gates: Seq<NorGate>,
    input_bits: usize, outputs: Seq<Wire>,
) -> bool {
    exists|trace: Seq<ChildWiringSnapshot>, invocation: CallerArguments, mapped: Seq<Wire>| #![trigger
        child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace, trace[calls.len() as int], input_bits),
        argument_prefix_wires(&invocation, arguments, layout.ranges_model(), arguments.len() as int, mapped)] {
        let end = trace[calls.len() as int];
        &&& child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace, end, input_bits)
        &&& child_ranges_match(calls, calls.len(), end.table.ranges@)
        &&& end.table.wires@.len() == child_sizes(calls, calls.len()).1
        &&& invocation.source == caller.source && invocation.forms@ == caller.forms@
        &&& invocation.inputs@ == caller.inputs@ && invocation.definitions@ == caller.definitions@
        &&& invocation.wires@ == caller.wires@
        &&& invocation.child_ranges@ == end.table.ranges@ && invocation.child_wires@ == end.table.wires@
        &&& argument_prefix_wires(&invocation, arguments, layout.ranges_model(), arguments.len() as int, mapped)
        &&& mapped.len() == layout.total_bits_model()
        &&& wires_available(mapped, input_bits, end.gates.len())
        &&& instance_gates_match(end.gates, callee.gates@, mapped, final_gates)
        &&& instance_outputs_match(callee.outputs@, mapped, end.gates.len() as usize, outputs)
    }
}

proof fn child_gate_step(
    caller: &CallerArguments, calls: Seq<ChildCall>, stop: nat, count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot,
    input_bits: usize, gate: int, prefix: nat,
) -> (child: int)
    requires
        child_wiring_trace_matches(caller, calls, stop, count, initial, trace, end, input_bits),
        prefix <= stop, initial.len() <= gate < trace[prefix as int].gates.len(),
    ensures
        0 <= child < prefix,
        trace[child].gates.len() <= gate < trace[child + 1].gates.len(),
    decreases prefix,
{
    reveal(child_wiring_trace_matches);
    assert(prefix > 0);
    let child = prefix as int - 1;
    if trace[child].gates.len() <= gate {
        child
    } else {
        child_gate_step(caller, calls, stop, count, initial, trace, end, input_bits, gate, child as nat)
    }
}

pub(in crate::project::use_aliases::bit_func::lowering) closed spec fn nested_gate_instance(
    caller: &CallerArguments, calls: Seq<ChildCall>, count: usize, arguments: Seq<ProjectedCallArgument>,
    layout: &PortBitLayout, callee: &NorNetlist, initial: Seq<NorGate>, final_gates: Seq<NorGate>,
    input_bits: usize, outputs: Seq<Wire>, gate: int, index: int, before: Seq<NorGate>, mapped: Seq<Wire>,
) -> bool {
    &&& 0 <= index <= calls.len()
    &&& before.len() == initial.len() + child_sizes(calls, index as nat).0 <= gate
    &&& before == final_gates.take(before.len() as int)
    &&& exists|trace: Seq<ChildWiringSnapshot>, invocation: CallerArguments|
        #![trigger child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace,
            trace[calls.len() as int], input_bits), invocation.child_ranges@]
    {
        &&& child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace,
            trace[calls.len() as int], input_bits)
        &&& before == trace[index].gates
        &&& invocation.source == caller.source && invocation.forms@ == caller.forms@
        &&& invocation.inputs@ == caller.inputs@ && invocation.definitions@ == caller.definitions@
        &&& invocation.wires@ == caller.wires@
        &&& invocation.child_ranges@ == trace[index].table.ranges@
        &&& invocation.child_wires@ == trace[index].table.wires@
        &&& wires_available(mapped, input_bits, before.len())
        &&& {
            let (inputs, target, projected, after) = if index < calls.len() {
                let child = calls[index];
                (child.inputs, child.circuit, child.arguments@, trace[index + 1].gates)
            } else { (layout, callee, arguments, final_gates) };
            &&& before.len() <= gate < after.len() <= final_gates.len()
            &&& after == final_gates.take(after.len() as int)
            &&& argument_prefix_wires(&invocation, projected, inputs.ranges_model(), projected.len() as int, mapped)
            &&& mapped.len() == inputs.total_bits_model()
            &&& instance_gates_match(before, target.gates@, mapped, after)
            &&& 0 <= gate - before.len() < target.gates@.len()
            &&& if index < calls.len() {
                child_outputs_appended(&trace[index].table, &trace[index + 1].table, calls[index].reference, target,
                    mapped, before, after, input_bits)
            } else {
                instance_outputs_match(target.outputs@, mapped, before.len() as usize, outputs)
            }
        }
    }
}

/// 入れ子の展開で追加したゲートを、子の添字または根と、その呼び出しに渡した配線へ対応付ける。
///
/// 子の個数と等しい添字は、子の出力を受け取る根を表す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn nested_gate_instance_at(
    caller: &CallerArguments, calls: Seq<ChildCall>, count: usize, arguments: Seq<ProjectedCallArgument>,
    layout: &PortBitLayout, callee: &NorNetlist, initial: Seq<NorGate>, final_gates: Seq<NorGate>,
    input_bits: usize, outputs: Seq<Wire>, gate: int,
) -> (result: (int, Seq<NorGate>, Seq<Wire>))
    requires
        nested_root_wiring_matches(caller, calls, count, arguments, layout, callee, initial, final_gates, input_bits, outputs),
        initial.len() <= gate < final_gates.len() <= usize::MAX,
    ensures nested_gate_instance(caller, calls, count, arguments, layout, callee, initial, final_gates,
        input_bits, outputs, gate, result.0, result.1, result.2),
        ({
            let (i, before, mapped) = result;
            let target = if i == calls.len() { callee } else { calls[i].circuit };
            &&& 0 <= i <= calls.len()
            &&& initial.len() <= before.len() <= gate < before.len() + target.gates@.len() <= final_gates.len()
            &&& instance_gates_match(before, target.gates@, mapped,
                final_gates.take((before.len() + target.gates@.len()) as int))
        }),
{
    reveal(child_wiring_trace_matches);
    let stop = calls.len();
    let (trace, invocation, mapped) = nested_root_wire_trace(caller, calls, count, arguments, layout, callee,
        initial, final_gates, input_bits, outputs);
    let end = trace[stop as int];
    if end.gates.len() <= gate {
        child_wiring_trace_sizes(caller, calls, stop, count, initial, trace, end, stop, input_bits);
        assert(final_gates.take(final_gates.len() as int) =~= final_gates);
        assert(end.gates == final_gates.take(end.gates.len() as int));
        assert(0 <= gate - end.gates.len() < callee.gates@.len());
        assert(nested_gate_instance(caller, calls, count, arguments, layout, callee, initial, final_gates,
            input_bits, outputs, gate, stop as int, end.gates, mapped));
        (stop as int, end.gates, mapped)
    } else {
        let child = child_gate_step(caller, calls, stop, count, initial, trace, end, input_bits, gate, stop);
        let before = trace[child];
        let after = trace[child + 1];
        child_wiring_trace_sizes(caller, calls, stop, count, initial, trace, end, child as nat, input_bits);
        child_wiring_prefix_preserved(caller, calls, stop, count, initial, trace, end, (child + 1) as nat, stop, input_bits);
        assert(after.gates == final_gates.take(after.gates.len() as int));
        let (used, inputs) = child_wiring_instance_at(caller, calls, count, initial, trace, end, input_bits, child);
        assert(before.gates == final_gates.take(before.gates.len() as int));
        assert(nested_gate_instance(caller, calls, count, arguments, layout, callee, initial, final_gates,
            input_bits, outputs, gate, child, before.gates, inputs));
        (child, before.gates, inputs)
    }
}

#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn nested_root_wiring_result(
    caller: &CallerArguments, calls: Seq<ChildCall>, reference_count: usize, arguments: Seq<ProjectedCallArgument>,
    layout: &PortBitLayout, callee: &NorNetlist, before: Seq<NorGate>, after: Seq<NorGate>,
    capacity: usize, output_capacity: usize, input_bits: usize, result: Result<Seq<Wire>, NestedCallWiringError>,
) -> bool {
    &&& result matches Ok(outputs) ==> {
        &&& after.len() == before.len() + child_sizes(calls, calls.len()).0 + callee.gates@.len() <= capacity
        &&& after.take(before.len() as int) == before
        &&& gates_available(after, input_bits as nat, after.len() as int)
        &&& outputs.len() == callee.outputs@.len()
        &&& output_ports_available(outputs, input_bits as nat, after.len(), outputs.len() as int)
        &&& nested_root_wiring_matches(caller, calls, reference_count, arguments, layout, callee,
            before, after, input_bits, outputs)
    }
    &&& result matches Err(error) ==> {
        &&& after == before
        &&& match error {
            NestedCallWiringError::Child(index, failure) => child_wiring_failure(caller, calls, index, failure,
                before.len() as int, capacity, output_capacity),
            NestedCallWiringError::Root(failure) => {
                let size = before.len() + child_sizes(calls, calls.len()).0;
                &&& child_arguments_determined(calls, calls.len())
                &&& size <= capacity && child_sizes(calls, calls.len()).1 <= output_capacity
                &&& match failure {
                    CallWiringError::DeferredArgument(site) =>
                        exists|i: int| 0 <= i < arguments.len() && (#[trigger] arguments[i]).source is Deferred
                            && is_form_location(caller.source, caller.forms@[arguments[i].form as int], site)
                            && forall|j: int| 0 <= j < i ==> !((#[trigger] arguments[j]).source is Deferred),
                    CallWiringError::GateCapacity => size + callee.gates@.len() > capacity
                        && forall|j: int| 0 <= j < arguments.len() ==> !((#[trigger] arguments[j]).source is Deferred),
                }
            },
        }
    }
}

/// 子の変換履歴と、根が実際に読んだ配線およびその評価値。
#[cfg(verus_only)]
pub(in crate::project::use_aliases::bit_func::lowering) struct NestedRootEvaluation<'s, 'p, 'a> {
    pub(in crate::project::use_aliases::bit_func::lowering) trace: Seq<ChildWiringSnapshot>,
    pub(in crate::project::use_aliases::bit_func::lowering) end: ChildWiringSnapshot,
    pub(in crate::project::use_aliases::bit_func::lowering) invocation: CallerArguments<'s, 'p, 'a>,
    pub(in crate::project::use_aliases::bit_func::lowering) mapped: Seq<Wire>,
    pub(in crate::project::use_aliases::bit_func::lowering) arguments: Seq<bool>,
    pub(in crate::project::use_aliases::bit_func::lowering) outputs: Seq<bool>,
}

pub(in crate::project::use_aliases::bit_func::lowering) open spec fn root_port_reads_child(
    root: &NestedRootEvaluation, arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout,
    port: usize, inputs: Seq<bool>, values: Seq<bool>,
) -> bool {
    &&& port < arguments.len() && port < layout.ranges_model().len()
    &&& arguments[port as int].source matches CallArgumentSource::NestedCall(reference)
    &&& reference < root.end.table.ranges@.len()
    &&& root.end.table.ranges@[reference as int] matches Some(range)
    &&& range.start <= range.end <= root.end.table.wires@.len()
    &&& port_values(layout, root.arguments)[port as int]
        == instance_wire_values(root.end.table.wires@.subrange(range.start as int, range.end as int), inputs, values)
}

/// 子の出力配線を読んだ値が、根の実引数に渡ることを示す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn child_value_flows_to_root(
    caller: &CallerArguments, calls: Seq<ChildCall>, count: usize, initial: Seq<NorGate>, root: &NestedRootEvaluation,
    arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout, widths: Seq<u64>, limit: usize, port: usize,
    combined: Seq<NorGate>, inputs: Seq<bool>, values: Seq<bool>, input_bits: usize,
) -> (child: (usize, Seq<bool>, Seq<bool>))
    requires
        child_wiring_trace_matches(caller, calls, calls.len(), count, initial, root.trace, root.end, input_bits),
        calls.len() <= usize::MAX,
        child_ranges_match(calls, calls.len(), root.end.table.ranges@),
        root.end.table.wires@.len() == child_sizes(calls, calls.len()).1 <= usize::MAX,
        root.end.gates.len() <= combined.len() && root.end.gates == combined.take(root.end.gates.len() as int),
        gate_values_match(inputs, combined, values), values.len() == combined.len() <= usize::MAX, inputs.len() == input_bits,
        forall|i: int| 0 <= i < calls.len() ==> child_call_abi(#[trigger] calls[i]),
        port_bit_layout_result(widths, limit, Ok(*layout)), port < widths.len(), port < arguments.len(),
        arguments[port as int].source is NestedCall,
        root_arguments_fit_children(caller, calls, arguments, layout),
        root.invocation.child_ranges@ == root.end.table.ranges@ && root.invocation.child_wires@ == root.end.table.wires@,
        argument_prefix_wires(&root.invocation, arguments, layout.ranges_model(), arguments.len() as int, root.mapped),
        root.mapped.len() == layout.total_bits_model(),
        root.arguments == instance_wire_values(root.mapped, inputs, values),
    ensures
        child.0 < calls.len(),
        arguments[port as int].source == CallArgumentSource::NestedCall(calls[child.0 as int].reference),
        nor_evaluation(calls[child.0 as int].circuit, child.1, child.2),
        port_values(layout, root.arguments)[port as int] == child.2,
        root_port_reads_child(root, arguments, layout, port, inputs, values),
{
    let projected = arguments[port as int];
    let reference = projected.source->NestedCall_0;
    port_bit_layout_port(widths, limit, *layout, port);
    let span = layout.ranges_model()[port as int];
    let width = (span.end - span.start) as usize;
    reveal(root_arguments_fit_children);
    assert(exists|i: int| 0 <= i < calls.len() && (#[trigger] calls[i]).reference == reference
        && calls[i].circuit.outputs@.len() == width);
    let index = choose|i: int| 0 <= i < calls.len() && (#[trigger] calls[i]).reference == reference
        && calls[i].circuit.outputs@.len() == width;
    let child_index = index as usize;
    assert(child_index as int == index);
    produced_child_argument_ready(calls, calls.len(), root.end.table.ranges@, root.end.table.wires@.len(),
        index, reference, width);
    let (argument_values, output_values) = child_output_evaluates(caller, calls, calls.len(), count, initial,
        root.trace, root.end, child_index, combined, inputs, values, input_bits);
    lowered_nested_argument_port_value(&root.invocation, arguments, layout, widths, limit, root.mapped, inputs, values,
        port, reference);
    let range = root.end.table.ranges@[reference as int]->Some_0;
    assert(output_values == instance_wire_values(
        root.end.table.wires@.subrange(range.start as int, range.end as int), inputs, values));
    (child_index, argument_values, output_values)
}

/// 消費側の直前の配線表で、先行する子の出力幅が入力ポートの幅と一致することを示す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn preceding_child_argument_widths(
    caller: &CallerArguments, calls: Seq<ChildCall>, count: usize, initial: Seq<NorGate>,
    trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot, input_bits: usize,
    before: nat, arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout, widths: Seq<u64>, capacity: usize,
)
    requires
        child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace, end, input_bits),
        before <= calls.len(),
        forall|i: int, j: int| 0 <= i < j < calls.len() ==> (#[trigger] calls[i]).reference != (#[trigger] calls[j]).reference,
        arguments_fit_preceding_children(caller, calls, before as int, arguments, layout),
        port_bit_layout_result(widths, capacity, Ok(*layout)), widths.len() == arguments.len(),
    ensures forall|port: int| 0 <= port < arguments.len() ==> {
        let argument = #[trigger] arguments[port];
        let table = trace[before as int].table;
        &&& widths[port] <= usize::MAX
        &&& child_argument_width_ready(table.ranges@, table.wires@.len(), argument.source, widths[port] as usize)
    },
{
    port_bit_layout_size(widths, capacity, layout);
    child_wiring_trace_sizes(caller, calls, calls.len(), count, initial, trace, end, before, input_bits);
    let table = trace[before as int].table;
    assert forall|port: int| 0 <= port < arguments.len() implies {
        let argument = #[trigger] arguments[port];
        &&& widths[port] <= usize::MAX
        &&& child_argument_width_ready(table.ranges@, table.wires@.len(), argument.source, widths[port] as usize)
    } by {
        let argument = arguments[port];
        let width = widths[port];
        port_bit_layout_port(widths, capacity, *layout, port as usize);
        if let CallArgumentSource::NestedCall(reference) = argument.source {
            let span = layout.ranges_model()[port];
            assert(span.end - span.start == width <= usize::MAX);
            let producer = choose|i: int| 0 <= i < before && (#[trigger] calls[i]).reference == reference
                && calls[i].circuit.outputs@.len() == width;
            child_output_range_preserved(caller, calls, calls.len(), count, initial, trace, end, producer as nat, before, input_bits);
            child_wiring_trace_sizes(caller, calls, calls.len(), count, initial, trace, end, (producer + 1) as nat, input_bits);
            child_sizes_step(calls, producer);
            child_sizes_grow(calls, (producer + 1) as nat, before);
            vstd::std_specs::vec::axiom_spec_len(&table.wires);
            let range = table.ranges@[reference as int]->Some_0;
            assert(range.start <= range.end <= table.wires@.len());
            assert(range.end - range.start == width);
        }
    };
}

/// 選んだ子が受け取った実引数と、その子の出力を登録した直後の状態を示す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn child_wiring_instance_at<'s, 'p, 'a>(
    caller: &CallerArguments<'s, 'p, 'a>, calls: Seq<ChildCall>, count: usize, initial: Seq<NorGate>,
    trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot, input_bits: usize, index: int,
) -> (result: (CallerArguments<'s, 'p, 'a>, Seq<Wire>))
    requires
        child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace, end, input_bits),
        0 <= index < calls.len(),
    ensures ({
        let (invocation, mapped) = result;
        let call = calls[index];
        let before = trace[index];
        let after = trace[index + 1];
        &&& trace.len() == calls.len() + 1
        &&& invocation.source == caller.source && invocation.forms@ == caller.forms@
        &&& invocation.inputs@ == caller.inputs@ && invocation.definitions@ == caller.definitions@
        &&& invocation.wires@ == caller.wires@
        &&& invocation.child_ranges@ == before.table.ranges@ && invocation.child_wires@ == before.table.wires@
        &&& argument_prefix_wires(&invocation, call.arguments@, call.inputs.ranges_model(), call.arguments@.len() as int, mapped)
        &&& mapped.len() == call.inputs.total_bits_model()
        &&& wires_available(mapped, input_bits, before.gates.len())
        &&& child_outputs_appended(&before.table, &after.table, call.reference, call.circuit, mapped,
            before.gates, after.gates, input_bits)
    }),
{
    reveal(child_wiring_trace_matches);
    reveal(child_instance_matches);
    let call = calls[index];
    let before = trace[index];
    let after = trace[index + 1];
    choose|invocation: CallerArguments<'s, 'p, 'a>, mapped: Seq<Wire>|
        #[trigger] argument_prefix_wires(&invocation, call.arguments@, call.inputs.ranges_model(), call.arguments@.len() as int, mapped)
        && invocation.source == caller.source && invocation.forms@ == caller.forms@
        && invocation.inputs@ == caller.inputs@ && invocation.definitions@ == caller.definitions@
        && invocation.wires@ == caller.wires@
        && invocation.child_ranges@ == before.table.ranges@ && invocation.child_wires@ == before.table.wires@
        && mapped.len() == call.inputs.total_bits_model()
        && wires_available(mapped, input_bits, before.gates.len())
        && child_outputs_appended(&before.table, &after.table, call.reference, call.circuit, mapped,
            before.gates, after.gates, input_bits)
}

/// 呼び出し全体の成功履歴から、子の配線表と根に実際に渡した配線を取り出す。
///
/// ゲートを持たない子や根も、出力の配線をこの履歴に保持する。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn nested_root_wire_trace<'s, 'p, 'a>(
    caller: &CallerArguments<'s, 'p, 'a>, calls: Seq<ChildCall>, count: usize, arguments: Seq<ProjectedCallArgument>,
    layout: &PortBitLayout, callee: &NorNetlist, initial: Seq<NorGate>, after: Seq<NorGate>, input_bits: usize, wires: Seq<Wire>,
) -> (result: (Seq<ChildWiringSnapshot>, CallerArguments<'s, 'p, 'a>, Seq<Wire>))
    requires
        nested_root_wiring_matches(caller, calls, count, arguments, layout, callee, initial, after, input_bits, wires),
        after.len() <= usize::MAX,
    ensures ({
        let (trace, invocation, mapped) = result;
        let end = trace[calls.len() as int];
        &&& trace.len() == calls.len() + 1
        &&& child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace, end, input_bits)
        &&& child_ranges_match(calls, calls.len(), end.table.ranges@)
        &&& end.table.wires@.len() == child_sizes(calls, calls.len()).1
        &&& end.gates.len() <= after.len()
        &&& invocation.source == caller.source && invocation.forms@ == caller.forms@
        &&& invocation.inputs@ == caller.inputs@ && invocation.definitions@ == caller.definitions@
        &&& invocation.wires@ == caller.wires@
        &&& invocation.child_ranges@ == end.table.ranges@ && invocation.child_wires@ == end.table.wires@
        &&& argument_prefix_wires(&invocation, arguments, layout.ranges_model(), arguments.len() as int, mapped)
        &&& mapped.len() == layout.total_bits_model()
        &&& wires_available(mapped, input_bits, end.gates.len())
        &&& instance_gates_match(end.gates, callee.gates@, mapped, after)
        &&& instance_outputs_match(callee.outputs@, mapped, end.gates.len() as usize, wires)
    }),
{
    reveal(nested_root_wiring_matches);
    let (trace, invocation, mapped) = choose|trace: Seq<ChildWiringSnapshot>, invocation: CallerArguments, mapped: Seq<Wire>|
        #![trigger child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace, trace[calls.len() as int], input_bits),
        argument_prefix_wires(&invocation, arguments, layout.ranges_model(), arguments.len() as int, mapped)] {
        let end = trace[calls.len() as int];
        &&& child_wiring_trace_matches(caller, calls, calls.len(), count, initial, trace, end, input_bits)
        &&& child_ranges_match(calls, calls.len(), end.table.ranges@)
        &&& end.table.wires@.len() == child_sizes(calls, calls.len()).1
        &&& invocation.source == caller.source && invocation.forms@ == caller.forms@
        &&& invocation.inputs@ == caller.inputs@ && invocation.definitions@ == caller.definitions@
        &&& invocation.wires@ == caller.wires@
        &&& invocation.child_ranges@ == end.table.ranges@ && invocation.child_wires@ == end.table.wires@
        &&& argument_prefix_wires(&invocation, arguments, layout.ranges_model(), arguments.len() as int, mapped)
        &&& mapped.len() == layout.total_bits_model()
        &&& wires_available(mapped, input_bits, end.gates.len())
        &&& instance_gates_match(end.gates, callee.gates@, mapped, after)
        &&& instance_outputs_match(callee.outputs@, mapped, end.gates.len() as usize, wires)
    };
    reveal(child_wiring_trace_matches);
    (trace, invocation, mapped)
}

/// 根のゲートに対応する区間は、全子を配線した直後から始まる。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn nested_root_values<'s, 'p, 'a>(
    caller: &CallerArguments<'s, 'p, 'a>, calls: Seq<ChildCall>, count: usize, arguments: Seq<ProjectedCallArgument>,
    layout: &PortBitLayout, callee: &NorNetlist, initial: Seq<NorGate>, after: Seq<NorGate>, wires: Seq<Wire>,
    combined: Seq<NorGate>, inputs: Seq<bool>, values: Seq<bool>, input_bits: usize,
) -> (evaluation: NestedRootEvaluation<'s, 'p, 'a>)
    requires
        nested_root_wiring_matches(caller, calls, count, arguments, layout, callee, initial, after, input_bits, wires),
        nor_evaluation_ready(callee, layout.total_bits_model() as nat),
        after.len() <= combined.len() && after == combined.take(after.len() as int),
        gate_values_match(inputs, combined, values), values.len() == combined.len() <= usize::MAX,
        inputs.len() == input_bits,
    ensures
        child_wiring_trace_matches(caller, calls, calls.len(), count, initial, evaluation.trace, evaluation.end, input_bits),
        child_ranges_match(calls, calls.len(), evaluation.end.table.ranges@),
        evaluation.end.table.wires@.len() == child_sizes(calls, calls.len()).1,
        evaluation.end.gates.len() <= combined.len(),
        evaluation.end.gates == combined.take(evaluation.end.gates.len() as int),
        evaluation.invocation.source == caller.source && evaluation.invocation.forms@ == caller.forms@,
        evaluation.invocation.inputs@ == caller.inputs@ && evaluation.invocation.definitions@ == caller.definitions@,
        evaluation.invocation.wires@ == caller.wires@,
        evaluation.invocation.child_ranges@ == evaluation.end.table.ranges@,
        evaluation.invocation.child_wires@ == evaluation.end.table.wires@,
        argument_prefix_wires(&evaluation.invocation, arguments, layout.ranges_model(), arguments.len() as int, evaluation.mapped),
        evaluation.mapped.len() == layout.total_bits_model(),
        evaluation.arguments == instance_wire_values(evaluation.mapped, inputs, values),
        evaluation.outputs == instance_wire_values(wires, inputs, values),
        nor_evaluation(callee, evaluation.arguments, evaluation.outputs),
        output_values_match(inputs, values, wires, evaluation.outputs),
{
    let (trace, invocation, mapped) = nested_root_wire_trace(caller, calls, count, arguments, layout, callee,
        initial, after, input_bits, wires);
    let end = trace[calls.len() as int];
    assert(end.gates =~= combined.take(end.gates.len() as int));
    reveal(wires_available);
    instance_evaluates_from_caller(end.gates, callee, combined, mapped, wires, inputs, values);
    NestedRootEvaluation { trace, end, invocation, mapped, arguments: instance_wire_values(mapped, inputs, values),
        outputs: instance_wire_values(wires, inputs, values) }
}

/// 子を後順に展開し、その出力を根の入力へ渡す。
///
/// # Errors
///
/// 子の最初の失敗を返す。すべての子が成功した場合は、根の最初の未確定引数またはゲート上限を返す。
/// 子と根のどちらで失敗しても、呼び出し前のゲート列に戻す。
pub(in crate::project::use_aliases::bit_func::lowering) fn lower_root_with_children<'s, 'p, 'a>(
    caller: &CallerArguments<'s, 'p, 'a>, calls: &[ChildCall<'s, 'p, 'a>], reference_count: usize,
    arguments: &[ProjectedCallArgument], layout: &PortBitLayout, callee: &NorNetlist,
    gates: &mut Vec<NorGate>, capacity: usize, output_capacity: usize,
    Ghost(root_layout): Ghost<(Seq<u64>, usize)>, Ghost(input_bits): Ghost<usize>,
) -> (result: Result<Vec<Wire>, NestedCallWiringError<'p, 'a>>)
    requires
        form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
        old(gates)@.len() <= capacity,
        gates_available(old(gates)@, input_bits as nat, old(gates)@.len() as int),
        wires_available(caller.wires@, input_bits, old(gates)@.len()),
        forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
        forall|i: int| 0 <= i < calls@.len() ==>
            (#[trigger] calls@[i]).reference < reference_count && child_call_ready(caller, calls@, i)
            && location_in_source(*calls@[i].expression) && *calls@[i].expression.source == *caller.source,
        forall|i: int, j: int| 0 <= i < j < calls@.len() ==>
            (#[trigger] calls@[i]).reference != (#[trigger] calls@[j]).reference,
        port_bit_layout_result(root_layout.0, root_layout.1, Ok(*layout)),
        arguments@.len() == root_layout.0.len(),
        nor_evaluation_ready(callee, layout.total_bits_model() as nat),
        root_arguments_fit_children(caller, calls@, arguments@, layout),
    ensures nested_root_wiring_result(caller, calls@, reference_count, arguments@, layout, callee,
        old(gates)@, final(gates)@, capacity, output_capacity, input_bits,
        match result { Ok(outputs) => Ok(outputs@), Err(error) => Err(error) }),
{
    proof { reveal(nested_root_wiring_result); }
    let checkpoint = gates.len();
    let ghost initial = gates@;
    let table = match lower_child_calls(caller, calls, reference_count, gates, capacity, output_capacity, Ghost(input_bits)) {
        Ok(table) => table,
        Err((index, error)) => return Err(NestedCallWiringError::Child(index, error)),
    };
    let invocation = CallerArguments { child_ranges: table.ranges.as_slice(), child_wires: table.wires.as_slice(), ..*caller };
    let ghost end = ChildWiringSnapshot { table, gates: gates@ };
    proof {
        reveal(argument_wires_ready);
        existing_wires_keep_availability(caller.wires@, input_bits, initial.len(), end.gates.len());
        assert forall|port: int| 0 <= port < arguments@.len() implies {
            let argument = #[trigger] arguments@[port];
            let range = layout.ranges_model()[port];
            &&& argument_wires_ready(&invocation, argument, (range.end - range.start) as usize)
            &&& argument_source_available(&invocation, argument.source) == !(argument.source is Deferred)
        } by {
            let argument = arguments@[port];
            if let CallArgumentSource::NestedCall(reference) = argument.source {
                let range = layout.ranges_model()[port];
                let width = (range.end - range.start) as usize;
                let i = choose|i: int| 0 <= i < calls@.len() && (#[trigger] calls@[i]).reference == reference
                    && calls@[i].circuit.outputs@.len() == width;
                produced_child_argument_ready(calls@, calls@.len(), table.ranges@, table.wires@.len(), i, reference, width);
            }
        };
    }
    let result = lower_projected_call(&invocation, arguments, layout, callee, gates, capacity,
        Ghost(root_layout.0), Ghost(root_layout.1), Ghost(input_bits));
    match result {
        Ok(outputs) => {
            proof {
                let mapped = choose|mapped: Seq<Wire>| #[trigger] argument_prefix_wires(&invocation, arguments@,
                    layout.ranges_model(), arguments@.len() as int, mapped)
                    && mapped.len() == layout.total_bits_model()
                    && wires_available(mapped, input_bits, end.gates.len())
                    && instance_gates_match(end.gates, callee.gates@, mapped, gates@)
                    && instance_outputs_match(callee.outputs@, mapped, end.gates.len() as usize, outputs@);
                let trace = choose|trace: Seq<ChildWiringSnapshot>| #[trigger] child_wiring_trace_matches(
                    caller, calls@, calls@.len(), reference_count, initial, trace, end, input_bits);
                assert(trace[calls@.len() as int] == end) by { reveal(child_wiring_trace_matches); };
                assert(gates@.take(checkpoint as int) =~= initial);
                assert(nested_root_wiring_matches(caller, calls@, reference_count, arguments@, layout, callee,
                    initial, gates@, input_bits, outputs@)) by { reveal(nested_root_wiring_matches); };
            }
            Ok(outputs)
        },
        Err(error) => {
            gates.truncate(checkpoint);
            assert(gates@ =~= initial);
            Err(NestedCallWiringError::Root(error))
        },
    }
}

/// 後順の子ごとに、入力を読めることと、定義内で参照添字が重複しないことを表す。
#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn nor_root_children_bound(
    selected: &ResolvedNorRoot, references: Range<usize>, caller: &CallerArguments, builtin: &(NorNetlist, PortBitLayout),
    calls: Seq<ChildCall>,
) -> bool {
    let count = (references.end - references.start) as usize;
    &&& calls.len() == selected.children@.len()
    &&& forall|i: int| 0 <= i < calls.len() ==>
        child_call_binding(selected.children@[i], references, builtin, #[trigger] calls[i])
        && child_call_ready(caller, calls, i)
        && calls[i].reference < count && location_in_source(*calls[i].expression)
        && *calls[i].expression.source == *caller.source
    &&& forall|i: int, j: int| 0 <= i < j < calls.len() ==>
        (#[trigger] calls[i]).reference != (#[trigger] calls[j]).reference
    &&& root_arguments_fit_children(caller, calls, selected.arguments@, &builtin.1)
}

/// 基底 NOR の配線結果と、その根に入力を渡した子の配線履歴を表す。
#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn nor_root_wiring_result(
    selected: &ResolvedNorRoot, references: Range<usize>, caller: &CallerArguments, builtin: &(NorNetlist, PortBitLayout),
    before: Seq<NorGate>, after: Seq<NorGate>, gate_limit: usize, child_limit: usize, input_bits: usize,
    result: Result<Wire, NestedCallWiringError>,
) -> bool {
    let count = (references.end - references.start) as usize;
    let wires = match result { Ok(output) => Ok(seq![output]), Err(error) => Err(error) };
    &&& builtin_nor_call_matches(builtin)
    &&& references.start <= references.end
    &&& result matches Ok(output) ==> 0 < after.len() && output == Wire::Gate((after.len() - 1) as usize)
    &&& result.is_err() ==> after == before
    &&& exists|calls: Seq<ChildCall>| #[trigger] nor_root_children_bound(selected, references, caller, builtin, calls)
        && nested_root_wiring_result(caller, calls, count, selected.arguments@, &builtin.1, &builtin.0,
            before, after, gate_limit, child_limit, input_bits, wires)
}

/// 根 NOR の固定入力に子の出力をつなぎ、最後に追加したゲートの配線を返す。
///
/// # Errors
///
/// 子の最初の失敗を優先し、全子が展開できた場合は根の失敗を返す。
/// どちらの場合もゲート列を呼び出し前の状態に戻す。
pub(in crate::project::use_aliases::bit_func::lowering) fn lower_resolved_nor_root<'s, 'p, 'a>(
    selected: &'s ResolvedNorRoot<'s, 'p, 'a>, references: &Range<usize>, caller: &CallerArguments<'s, 'p, 'a>,
    builtin: &'s (NorNetlist, PortBitLayout), gates: &mut Vec<NorGate>, gate_limit: usize, child_limit: usize,
    Ghost(aliases): Ghost<&UseAliases<'_, 'p, 'a>>,
    Ghost(context): Ghost<(&FunctionExpansionOrder<'p, 'a>, &FunctionTemplates<'p, 'a>, u64, Seq<ProjectedCallArgument>)>,
    Ghost(scope): Ghost<(&super::super::LoweringBody<'_, 'p, 'a>, &super::super::Layouts, usize, usize)>,
) -> (result: Result<Wire, NestedCallWiringError<'p, 'a>>)
    requires
        caller.source == selected.prepared.root.expression.source,
        references.start == selected.prepared.root.reference,
        selected.prepared.root.arguments.start <= selected.prepared.root.arguments.end <= context.3.len(),
        selected.arguments@ == context.3.subrange(selected.prepared.root.arguments.start as int,
            selected.prepared.root.arguments.end as int),
        aliases.expression_children_in_reference_range(*references, caller.source, Some(selected.prepared.postorder)),
        aliases.resolved_expression_calls_match(context.0, context.1, context.2, Some(selected.prepared.postorder),
            context.3, selected.children@),
        builtin_nor_call_matches(builtin),
        body_definition_layouts(scope.0.input_widths@, scope.0.definitions@, scope.2, scope.1),
        caller.inputs@ == scope.1.inputs.ranges_model(),
        caller.definitions@ == scope.1.definitions.ranges_model(),
        scope.3 <= scope.0.definitions@.len(),
        caller.wires@.len() == preceding_port_bits(definition_widths(scope.0.definitions@), scope.3 as nat),
        nor_root_arguments_match_widths(selected, *references, caller.source, caller.forms@,
            scope.0.input_widths@, scope.0.definitions@, scope.3, context.2),
        form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
        old(gates)@.len() <= gate_limit,
        gates_available(old(gates)@, scope.1.inputs.total_bits_model() as nat, old(gates)@.len() as int),
        wires_available(caller.wires@, scope.1.inputs.total_bits_model(), old(gates)@.len()),
    ensures nor_root_wiring_result(selected, *references, caller, builtin, old(gates)@, final(gates)@,
        gate_limit, child_limit, scope.1.inputs.total_bits_model(), result),
{
    let ghost before = gates@;
    let ghost input_bits = scope.1.inputs.total_bits_model();
    let (count, bound) = bind_child_calls(references, selected.children.as_slice(), builtin, Ghost(aliases),
        Ghost(context), Ghost(caller.source), Ghost(Some(selected.prepared.postorder)));
    proof {
        super::super::body_inputs_end_within_layout(scope.0, scope.2, scope.1);
        assert forall|i: int| 0 <= i < bound@.len() implies #[trigger] child_call_ready(caller, bound@, i) by {
            let call = bound@[i];
            let child = selected.children@[i];
            assert(child_call_binding(child, *references, builtin, call));
            assert forall|port: int| 0 <= port < call.arguments@.len() implies {
                let arg = #[trigger] call.arguments@[port];
                let width = call._input_widths@[port];
                &&& argument_matches_width(caller.source, caller.forms@, scope.0.input_widths@,
                    scope.0.definitions@.take(scope.3 as int), arg, width, context.2)
                &&& selected_child_output_matches(selected.children@, references.start, i, arg, width)
            } by {
                assert(call.arguments@[port] == child.arguments@[port]);
                assert(call._input_widths@[port] == expression_input_width(child, port));
            };
            bound_arguments_ready(scope.0, scope.1, scope.2, context.2, caller, scope.3, *references,
                selected.children@, builtin, bound@, i, call.arguments@, call.inputs, call._input_widths@, call._layout_limit@);
            reveal(child_call_ready);
        };
        bound_arguments_ready(scope.0, scope.1, scope.2, context.2, caller, scope.3, *references, selected.children@,
            builtin, bound@, bound@.len() as int, selected.arguments@, &builtin.1, seq![1u64, 1u64], 2);
    }
    assert(nor_root_children_bound(selected, *references, caller, builtin, bound@)) by {
        reveal(nor_root_children_bound);
    };
    let lowered = lower_root_with_children(caller, bound.as_slice(), count, selected.arguments, &builtin.1, &builtin.0,
        gates, gate_limit, child_limit, Ghost((seq![1u64, 1u64], 2usize)), Ghost(input_bits));
    let ghost after = gates@;
    match lowered {
        Ok(outputs) => {
            proof { reveal(nested_root_wiring_result); }
            assert(outputs@.len() == 1);
            let output = outputs[0];
            proof {
                assert(outputs@ =~= seq![output]);
                let layout = &builtin.1;
                let circuit = &builtin.0;
                assert(nested_root_wiring_matches(caller, bound@, count, selected.arguments@, layout, circuit,
                    before, after, input_bits, outputs@));
                assert(output == Wire::Gate((after.len() - 1) as usize) && after.len() > 0) by {
                    reveal(nested_root_wiring_matches);
                    let (prefix, mapped) = choose|prefix: Seq<NorGate>, mapped: Seq<Wire>|
                        #[trigger] instance_gates_match(prefix, circuit.gates@, mapped, after)
                        && instance_outputs_match(circuit.outputs@, mapped, prefix.len() as usize, outputs@);
                    let stop = prefix.len();
                    assert(after.len() == stop + 1);
                    assert(outputs@[0] == super::super::super::instances::instance_wire(Wire::Gate(0), mapped, stop as usize));
                };
                assert(nor_root_wiring_result(selected, *references, caller, builtin, before, after, gate_limit,
                    child_limit, input_bits, Ok(output))) by {
                    reveal(nor_root_wiring_result);
                    assert(nested_root_wiring_result(caller, bound@, count, selected.arguments@, layout, circuit,
                        before, after, gate_limit, child_limit, input_bits, Ok(seq![output])));
                };
            }
            Ok(output)
        },
        Err(error) => {
            assert(nor_root_wiring_result(selected, *references, caller, builtin, before, after, gate_limit,
                child_limit, input_bits, Err(error))) by {
                reveal(nor_root_wiring_result);
                reveal(nested_root_wiring_result);
                assert(nested_root_wiring_result(caller, bound@, count, selected.arguments@, &builtin.1, &builtin.0,
                    before, after, gate_limit, child_limit, input_bits, Err(error)));
            };
            Err(error)
        },
    }
}

} // verus!
