//! 子呼び出しを内側から展開し、失敗したときは追加したゲートを取り除く。

use super::*;
use super::super::{Layouts, LoweringBody};
use super::super::super::templates::{FunctionTemplates, ResolvedExpressionCall, ResolvedTemplateCall};
use crate::project::{FunctionExpansionOrder, UseAliases};
#[cfg(verus_only)]
use super::super::{existing_wires_keep_availability, port_values};
#[cfg(verus_only)]
use super::super::super::instances::{instance_evaluates_from_caller, instance_wire_values};
#[cfg(verus_only)]
use super::super::super::frontend::{
    expression_argument_matches_width, expression_input_width, expression_output_bits, nested_argument_output_matches,
    root_argument_matches_width,
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

/// 同じ定義の子を後順に並べたまま参照添字を相対化し、実引数、入力配置、回路を借りる。
///
/// 根と子の確定済みの実引数について、現在の配線と先行する子が供給する幅を照合する。
pub(in crate::project::use_aliases::bit_func::lowering) fn bind_child_calls<'s, 'p, 'a>(
    selected: &'s ResolvedTemplateCall<'s, 'p, 'a>, builtin: &'s (NorNetlist, PortBitLayout),
    Ghost(aliases): Ghost<&UseAliases<'_, 'p, 'a>>,
    context: Ghost<(&FunctionExpansionOrder<'p, 'a>, &FunctionTemplates<'p, 'a>, u64, Seq<ProjectedCallArgument>)>,
    Ghost(caller): Ghost<&CallerArguments<'_, 'p, 'a>>,
    Ghost(body_layout): Ghost<(&LoweringBody<'_, 'p, 'a>, &Layouts, usize)>,
) -> (bound: (usize, Vec<ChildCall<'s, 'p, 'a>>))
    requires
        aliases.expansion_child_scope(selected.group),
        aliases.resolved_expression_calls_match(context@.0, context@.1, context@.2, selected.group.postorder,
            context@.3, selected.children@),
        builtin_nor_call_matches(builtin),
        body_definition_layouts(body_layout.0.input_widths@, body_layout.0.definitions@, body_layout.2, body_layout.1),
        caller.source == selected.group.expression.source,
        caller.inputs@ == body_layout.1.inputs.ranges_model(),
        caller.definitions@ == body_layout.1.definitions.ranges_model(),
        caller.wires@.len() == preceding_port_bits(definition_widths(body_layout.0.definitions@), selected.group.outputs.start as nat),
        resolved_call_fits_body(*selected, body_layout.0.input_widths@, body_layout.0.definitions@, caller.forms@, context@.2),
        port_bit_layout_result(selected.template.input_widths_model(), selected.template.bit_limit_model(),
            Ok(*selected.template.circuit_model().input_layout_model())),
        selected.arguments@.len() == selected.template.input_widths_model().len(),
    ensures
        bound.0 == selected.group.references.end - selected.group.references.start,
        bound.1@.len() == selected.children@.len(),
        forall|i: int| 0 <= i < bound.1@.len() ==>
            (#[trigger] bound.1@[i]).reference < bound.0
            && location_in_source(*bound.1@[i].expression)
            && *bound.1@[i].expression.source == *selected.group.expression.source
            && child_call_binding(selected.children@[i], selected.group.references, builtin, bound.1@[i])
            && child_call_ready(caller, bound.1@, i),
        forall|i: int, j: int| 0 <= i < j < bound.1@.len() ==>
            (#[trigger] bound.1@[i]).reference != (#[trigger] bound.1@[j]).reference,
        root_arguments_fit_children(caller, bound.1@, selected.arguments@, selected.template.circuit_model().input_layout_model()),
{
    let references = &selected.group.references;
    let count = references.end - references.start;
    let mut calls: Vec<ChildCall<'s, 'p, 'a>> = Vec::new();
    let mut index = 0;
    while index < selected.children.len()
        invariant
            references == &selected.group.references,
            count == references.end - references.start,
            aliases.expansion_child_scope(selected.group),
            aliases.resolved_expression_calls_match(context@.0, context@.1, context@.2, selected.group.postorder,
                context@.3, selected.children@),
            builtin_nor_call_matches(builtin),
            index == calls@.len() <= selected.children@.len(),
            forall|i: int| 0 <= i < calls@.len() ==>
                (#[trigger] calls@[i]).reference < count
                && location_in_source(*calls@[i].expression)
                && *calls@[i].expression.source == *selected.group.expression.source
                && child_call_binding(selected.children@[i], *references, builtin, calls@[i]),
        decreases selected.children@.len() - index,
    {
        let child = &selected.children[index];
        proof {
            reveal(UseAliases::resolved_expression_call_matches);
            assert(selected.group.postorder is Some);
            let row = selected.group.postorder->Some_0@[index as int];
            assert(aliases.resolved_expression_call_matches(context@.0, context@.1, context@.2, context@.3, row, *child));
            assert(references.start <= child.child.reference < references.end);
        }
        let reference = child.child.reference - references.start;
        let call = if let Some(template) = child.template {
            proof {
                let target = context@.0.position_model(child.child._rank@->Some_0)->Some_0;
                aliases.template_circuit_evidence(target, context@.2, template);
                aliases.template_port_evidence(target, context@.2, template);
                aliases.template_port_counts(template.signature_model(), context@.2, template.input_widths_model(),
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
                && *calls@[i].expression.source == *selected.group.expression.source
                && child_call_binding(selected.children@[i], *references, builtin, calls@[i]) by {
            if i < index { assert(calls@[i] == before[i]); }
        };
        index += 1;
    }
    proof {
        assert forall|i: int, j: int| 0 <= i < j < calls@.len() implies
            (#[trigger] calls@[i]).reference != (#[trigger] calls@[j]).reference by {
            reveal(UseAliases::resolved_expression_call_matches);
            let source = selected.group.postorder->Some_0;
            assert(*selected.children@[i].child == source@[i] && *selected.children@[j].child == source@[j]);
            assert(source@[i].reference != source@[j].reference);
        };
        let (body, layouts, capacity) = body_layout;
        assert forall|i: int| 0 <= i < calls@.len() implies
            #[trigger] child_call_ready(caller, calls@, i) by {
            assert(child_call_binding(selected.children@[i], *references, builtin, calls@[i]));
            assert forall|port: int| 0 <= port < selected.children@[i].arguments@.len() implies
                #[trigger] expression_argument_matches_width(caller.source, caller.forms@, body.input_widths@,
                    body.definitions@, *selected, i, port, context@.2) by {
                assert(expression_argument_matches_width(caller.source, caller.forms@, body.input_widths@,
                    body.definitions@, *selected, i, port, context@.2));
            };
            bound_child_call_ready(body, layouts, capacity, context@.2, caller, *selected, builtin, calls@, i);
        };
        bound_root_arguments_ready(body, layouts, capacity, context@.2, caller, *selected, builtin, calls@);
    }
    (count, calls)
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

/// 子の評価で得た出力が、後続の呼び出しの指定した入力ポートに入ることを示す。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn child_value_flows_to_consumer(
    caller: &CallerArguments, calls: Seq<ChildCall>, stop: nat, reference_count: usize,
    initial: Seq<NorGate>, trace: Seq<ChildWiringSnapshot>, end: ChildWiringSnapshot,
    child: usize, consumer: usize, port: usize, combined: Seq<NorGate>, inputs: Seq<bool>, values: Seq<bool>, input_bits: usize,
) -> (result: ((Seq<bool>, Seq<bool>), (Seq<bool>, Seq<bool>)))
    requires
        child_wiring_trace_matches(caller, calls, stop, reference_count, initial, trace, end, input_bits),
        child_ranges_match(calls, stop, end.table.ranges@),
        child < consumer < stop <= calls.len(),
        forall|i: int, j: int| 0 <= i < j < stop ==> (#[trigger] calls[i]).reference != (#[trigger] calls[j]).reference,
        child_call_ready(caller, calls, child as int), child_call_ready(caller, calls, consumer as int),
        port < calls[consumer as int].arguments@.len(),
        calls[consumer as int].arguments@[port as int].source == CallArgumentSource::NestedCall(calls[child as int].reference),
        end.gates.len() <= combined.len() && end.gates == combined.take(end.gates.len() as int),
        gate_values_match(inputs, combined, values), values.len() == combined.len() <= usize::MAX,
        inputs.len() == input_bits,
    ensures
        nor_evaluation(calls[child as int].circuit, result.0.0, result.0.1),
        nor_evaluation(calls[consumer as int].circuit, result.1.0, result.1.1),
        port_values(calls[consumer as int].inputs, result.1.0)[port as int] == result.0.1,
{
    reveal(child_call_ready);
    let producer = calls[child as int];
    let call = calls[consumer as int];
    let produced = child_output_evaluates(caller, calls, stop, reference_count, initial, trace, end,
        child, combined, inputs, values, input_bits);
    let consumed = child_output_evaluates(caller, calls, stop, reference_count, initial, trace, end,
        consumer, combined, inputs, values, input_bits);
    assert(trace.len() == stop + 1 && trace[stop as int] == end) by {
        reveal(child_wiring_trace_matches);
    };
    let before = trace[consumer as int];
    let (invocation, mapped) = choose|invocation: CallerArguments, mapped: Seq<Wire>|
        #[trigger] argument_prefix_wires(&invocation, call.arguments@, call.inputs.ranges_model(), call.arguments@.len() as int, mapped)
        && invocation.child_ranges@ == before.table.ranges@ && invocation.child_wires@ == before.table.wires@
        && mapped.len() == call.inputs.total_bits_model()
        && consumed.0 == instance_wire_values(mapped, inputs, values);

    let reference = producer.reference;
    let dest = call.inputs.ranges_model()[port as int];
    port_bit_layout_port(call._input_widths@, call._layout_limit@, *call.inputs, port);
    let earlier = choose|i: int| 0 <= i < consumer && (#[trigger] calls[i]).reference == reference
        && calls[i].circuit.outputs@.len() == (dest.end - dest.start) as usize;
    assert(earlier == child) by {
        if earlier < child { assert(calls[earlier].reference != calls[child as int].reference); }
        if child < earlier { assert(calls[child as int].reference != calls[earlier].reference); }
    };
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
    lowered_nested_argument_port_value(&invocation, call.arguments@, call.inputs, call._input_widths@, call._layout_limit@,
        mapped, inputs, values, port, reference);
    (produced, consumed)
}

#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn child_call_ready(
    caller: &CallerArguments, calls: Seq<ChildCall>, index: int,
) -> bool {
    &&& 0 <= index < calls.len()
    &&& ({
        let call = calls[index];
        &&& child_call_abi(call)
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
    port_bit_layout_size(call._input_widths@, call._layout_limit@, call.inputs);
    assert forall|port: int| 0 <= port < call.arguments@.len() implies {
        let argument = #[trigger] call.arguments@[port];
        let span = call.inputs.ranges_model()[port];
        let width = (span.end - span.start) as usize;
        &&& layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
            caller.wires@.len() as int, argument, width)
        &&& if let CallArgumentSource::NestedCall(reference) = argument.source {
            exists|earlier: int| 0 <= earlier < index && (#[trigger] calls[earlier]).reference == reference
                && calls[earlier].circuit.outputs@.len() == width
        } else { true }
    } by {
        let argument = call.arguments@[port];
        assert(argument == child.arguments@[port]);
        let bits = expression_input_width(child, port);
        assert(call._input_widths@[port] == bits);
        assert(expression_argument_matches_width(caller.source, caller.forms@, body.input_widths@,
            body.definitions@, selected, index, port, width_limit));
        port_bit_layout_port(call._input_widths@, call._layout_limit@, *call.inputs, port as usize);
        let span = call.inputs.ranges_model()[port];
        assert(0 < span.end - span.start == bits <= usize::MAX);
        let width = (span.end - span.start) as usize;
        layout_argument_from_width(body, layouts, capacity, selected.group.outputs.start, caller.source,
            caller.forms@, argument, bits, width_limit);
        assert(layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
            caller.wires@.len() as int, argument, width));
        if argument.source is NestedCall {
            bound_argument_output_width(selected, builtin, calls, index, argument, bits);
        }
    };
}

/// 選択時に確定した子の出力幅を、同じ位置にある配線用の回路へ引き継ぐ。
proof fn bound_argument_output_width(
    selected: ResolvedTemplateCall, builtin: &(NorNetlist, PortBitLayout), calls: Seq<ChildCall>,
    before: int, argument: ProjectedCallArgument, width: u64,
)
    requires
        calls.len() == selected.children@.len(),
        forall|i: int| 0 <= i < calls.len() ==>
            child_call_binding(selected.children@[i], selected.group.references, builtin, #[trigger] calls[i]),
        argument.source is NestedCall,
        nested_argument_output_matches(selected, before, argument, width),
    ensures exists|i: int| 0 <= i < before <= calls.len()
        && (#[trigger] calls[i]).reference == argument.source->NestedCall_0
        && calls[i].circuit.outputs@.len() == width,
{
    reveal(nested_argument_output_matches);
    let reference = argument.source->NestedCall_0;
    let earlier = choose|i: int| 0 <= i < before
        && (#[trigger] selected.children@[i]).child.reference == selected.group.references.start + reference
        && expression_output_bits(selected.children@[i]) == width;
    let call = calls[earlier];
    let producer = selected.children@[earlier];
    assert(child_call_binding(producer, selected.group.references, builtin, call));
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
    &&& arguments.len() == layout.ranges_model().len()
    &&& forall|port: int| 0 <= port < arguments.len() ==> {
        let argument = #[trigger] arguments[port];
        let span = layout.ranges_model()[port];
        let width = (span.end - span.start) as usize;
        &&& layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
            caller.wires@.len() as int, argument, width)
        &&& if let CallArgumentSource::NestedCall(reference) = argument.source {
            exists|i: int| 0 <= i < calls.len() && (#[trigger] calls[i]).reference == reference
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
    let limit = selected.template.bit_limit_model();
    port_bit_layout_size(widths, limit, layout);
    assert forall|port: int| 0 <= port < selected.arguments@.len() implies {
        let argument = #[trigger] selected.arguments@[port];
        let span = layout.ranges_model()[port];
        let width = (span.end - span.start) as usize;
        &&& layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
            caller.wires@.len() as int, argument, width)
        &&& if let CallArgumentSource::NestedCall(reference) = argument.source {
            exists|i: int| 0 <= i < calls.len() && (#[trigger] calls[i]).reference == reference
                && calls[i].circuit.outputs@.len() == width
        } else { true }
    } by {
        let argument = selected.arguments@[port];
        let bits = widths[port];
        assert(root_argument_matches_width(caller.source, caller.forms@, body.input_widths@,
            body.definitions@, selected, port, width_limit));
        port_bit_layout_port(widths, limit, *layout, port as usize);
        let span = layout.ranges_model()[port];
        assert(0 < span.end - span.start == bits <= usize::MAX);
        layout_argument_from_width(body, layouts, capacity, selected.group.outputs.start, caller.source,
            caller.forms@, argument, bits, width_limit);
        if argument.source is NestedCall {
            bound_argument_output_width(selected, builtin, calls, calls.len() as int, argument, bits);
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

} // verus!
