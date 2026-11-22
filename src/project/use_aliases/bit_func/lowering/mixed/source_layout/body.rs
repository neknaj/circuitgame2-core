//! 型付きの定義列から関数本体のソース配線を組み立てる。

use super::*;
use super::super::super::source_calls::final_layout::{function_source_circuit, function_source_layout};
use crate::project::ProjectSource;

verus! {

/// 厳格な定義の位置と、型検査で決まった左辺と呼び出し先。
pub(in crate::project::use_aliases::bit_func::lowering) struct SourceBodyDefinition {
    pub(in crate::project::use_aliases::bit_func::lowering) site: DefinitionPosition,
    pub(in crate::project::use_aliases::bit_func::lowering) slots: Range<usize>,
    pub(in crate::project::use_aliases::bit_func::lowering) target: SourceStepTarget,
    pub(in crate::project::use_aliases::bit_func::lowering) ordinary: Option<SourceChildModel>,
    pub(in crate::project::use_aliases::bit_func::lowering) children: Seq<Option<SourceChildModel>>,
}

/// コンパイラの配線履歴を参照せず、先行定義から順に各右辺を解釈する。
pub(in crate::project::use_aliases::bit_func::lowering) closed spec fn source_body_wires(
    source: &ProjectSource, forms: Seq<Form>, body: &LoweringBody, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>,
    definitions: Seq<SourceBodyDefinition>, count: nat,
) -> Option<(Seq<SourceGateId>, Seq<SourceNor>, Seq<Seq<SourceWire>>)>
    decreases count,
{
    if count == 0 {
        Some((Seq::empty(), Seq::empty(), Seq::empty()))
    } else if count <= definitions.len() {
        let row = definitions[count - 1];
        if let Some((prior, gates, slots)) =
            source_body_wires(source, forms, body, selected, roots, definitions, (count - 1) as nat)
        {
            if row.slots.start != slots.len() { None } else {
                let context = SourceArguments {
                    source, forms, input_widths: body.input_widths@, definitions: slots, children: Map::empty(),
                };
                if let Some((order, added, next)) = source_step_layout(&context, body, row.target, selected, roots,
                    row.site, prior, row.ordinary, row.children)
                {
                    if next.len() == row.slots.end { Some((order, gates + added, next)) } else { None }
                } else { None }
            }
        } else { None }
    } else { None }
}

/// 呼び出し元の定義番号を得る。展開した回路では呼び出し経路の先頭を使う。
pub(in crate::project::use_aliases::bit_func::lowering) closed spec fn gate_definition_number(gate: SourceGateId) -> usize {
    if gate.instance.len() == 0 { gate.gate.definition } else { gate.instance[0].definition }
}

/// 型付きの定義列と、変換の各段が同じ左辺を同じ順で処理することを表す。
pub(in crate::project::use_aliases::bit_func::lowering) closed spec fn source_body_matches_steps(
    source: &ProjectSource, forms: Seq<Form>, body: &LoweringBody, width_limit: u64,
    selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, definitions: Seq<SourceBodyDefinition>,
    steps: Seq<WiringStep>,
) -> bool {
    &&& definitions.len() == steps.len()
    &&& forall|i: int| 0 <= i < definitions.len() ==> {
        let row = #[trigger] definitions[i];
        &&& row.slots == source_step_slots(steps[i])
        &&& row.target == source_step_target(steps[i])
        &&& source_step_ready(source, forms, body, width_limit, row.target, row.slots.start,
            selected, roots, row.ordinary, row.children)
    }
    &&& forall|i: int, j: int| 0 <= i < j < definitions.len() ==>
        (#[trigger] definitions[i]).site.definition < (#[trigger] definitions[j]).site.definition
}

/// 履歴の各段と同じ定義を順に解釈し、先行配線を保ちながら本体全体の対応を組み立てる。
#[verifier::spinoff_prover]
pub(in crate::project::use_aliases::bit_func::lowering) proof fn rooted_source_body_wires(
    source: &ProjectSource, forms: Seq<Form>, body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    bindings: Seq<CallBinding>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, limit: usize,
    steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, final_wiring: WiringView,
    definitions: Seq<SourceBodyDefinition>, arguments: Seq<ProjectedCallArgument>, count: nat,
) -> (result: (Seq<SourceGateId>, Seq<SourceNor>, Seq<Seq<SourceWire>>))
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, final_wiring),
        resolved_mixed_trace(bindings, roots, arguments, steps),
        bindings_match_calls(bindings, selected),
        count <= definitions.len(),
        source_body_matches_steps(source, forms, body, width_limit, selected, roots, definitions, steps),
    ensures ({
        let (order, gates, slots) = result;
        &&& source_body_wires(source, forms, body, selected, roots, definitions, count) == Some(result)
        &&& order.len() == gates.len()
        &&& order.no_duplicates()
        &&& if count == 0 {
            order.len() == 0 && slots.len() == 0
        } else {
            let end = source_step_after(steps[count - 1]);
            &&& slots.len() == source_step_slots(steps[count - 1]).end
            &&& order.len() == end.gates.len()
            &&& definition_wires_pair(order, slots, layouts.definitions.ranges_model(), end.definitions)
            &&& forall|i: int| 0 <= i < gates.len() ==> {
                let gate = #[trigger] gates[i];
                let flat = end.gates[i];
                &&& source_wire_pair(order, gate.left, flat.left)
                &&& source_wire_pair(order, gate.right, flat.right)
            }
        }
        &&& forall|i: int| 0 <= i < order.len() ==> 0 < count
            && gate_definition_number(#[trigger] order[i]) <= definitions[count - 1].site.definition
    }),
    decreases count,
{
    if count == 0 {
        return (Seq::empty(), Seq::empty(), Seq::empty());
    }
    let at = count - 1;
    let (prior, gates, slots) = rooted_source_body_wires(source, forms, body, layouts, capacity, width_limit, bindings,
        selected, roots, limit, steps, slot, group, nor, final_wiring, definitions, arguments, at as nat);
    let row = definitions[at];
    let step = steps[at];
    let context = SourceArguments {
        source, forms, input_widths: body.input_widths@, definitions: slots, children: Map::empty(),
    };
    assert(at > 0 ==> source_step_after(steps[at - 1]) == step.before) by { reveal(rooted_mixed_trace); };
    assert(slots.len() == step.from && prior.len() == step.before.gates.len()
        && definition_wires_pair(prior, slots, layouts.definitions.ranges_model(), step.before.definitions)) by {
        reveal(rooted_mixed_trace);
        if at == 0 {
            assert(wiring_empty(step.before));
        } else {
            assert(steps[at - 1].after == step.before);
            assert(steps[at - 1].to == step.from);
        }
    };
    assert forall|i: int| 0 <= i < prior.len() implies !source_gate_in_definition(row.site, #[trigger] prior[i]) by {
        assert(0 < at);
        assert(gate_definition_number(prior[i]) <= definitions[at - 1].site.definition < row.site.definition);
        reveal(source_gate_in_definition);
    };
    assert(source_definition_start(&context, body, layouts, capacity, step.before, step.from, row.site, prior)) by {
        reveal(rooted_mixed_trace);
        reveal(wiring_step_valid);
        reveal(nor_wiring_step_valid);
    };
    let (order, added, next) = rooted_source_step(&context, body, layouts, capacity, width_limit, bindings, selected,
        roots, limit, steps, slot, group, nor, final_wiring, at, row.site, prior, row.ordinary, row.children, arguments);
    let all = gates + added;
    assert forall|i: int| 0 <= i < all.len() implies {
        let gate = #[trigger] all[i];
        let flat = step.after.gates[i];
        &&& source_wire_pair(order, gate.left, flat.left)
        &&& source_wire_pair(order, gate.right, flat.right)
    } by {
        if i < gates.len() {
            assert(all[i] == gates[i] && step.after.gates[i] == step.before.gates[i]);
            assert(0 < at);
            let gate = gates[i];
            let previous = source_step_after(steps[at - 1]);
            let flat = previous.gates[i];
            assert(previous == step.before);
            assert(source_wire_pair(prior, gate.left, flat.left) && source_wire_pair(prior, gate.right, flat.right));
            if let Wire::Gate(left) = flat.left { assert(order[left as int] == prior[left as int]); }
            if let Wire::Gate(right) = flat.right { assert(order[right as int] == prior[right as int]); }
        } else {
            assert(all[i] == added[i - gates.len()]);
        }
    };
    assert forall|i: int| 0 <= i < order.len() implies
        gate_definition_number(#[trigger] order[i]) <= row.site.definition by {
        if i < prior.len() {
            assert(order[i] == prior[i]);
            assert(0 < at);
            assert(gate_definition_number(prior[i]) <= definitions[at - 1].site.definition < row.site.definition);
        } else {
            let local = i - prior.len();
            assert(0 <= local < added.len());
            let gate = added[local];
            let flat = source_step_after(step).gates[i];
            assert(source_wire_pair(order, gate.left, flat.left));
            assert(source_gate_in_definition(row.site, order[i]));
            reveal(source_gate_in_definition);
        }
    };
    assert(source_body_wires(source, forms, body, selected, roots, definitions, count) == Some((order, all, next))) by {
        reveal_with_fuel(source_body_wires, 2);
    };
    (order, all, next)
}

/// 定義の配線に公開ポートを結び付け、変換済み関数と対応する tick のソース回路を得る。
#[verifier::spinoff_prover]
pub(in crate::project::use_aliases::bit_func::lowering) proof fn rooted_function_source_layout(
    source: &ProjectSource, forms: Seq<Form>, body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    bindings: Seq<CallBinding>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, limit: usize,
    widths: Seq<u64>, drivers: Seq<OutputDriver>, arguments: Seq<ProjectedCallArgument>, function: &LoweredBitFunc,
    definitions: Seq<SourceBodyDefinition>, steps: Ghost<Seq<WiringStep>>,
) -> (model: SourceChildModel)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        widths_layout(widths, capacity, &layouts.outputs),
        widths.len() == drivers.len(),
        forall|port: int| 0 <= port < widths.len() ==>
            bit_driver_width(body.input_widths@, body.definitions@, #[trigger] drivers[port]) == Some(widths[port]),
        mixed_function_result(body, layouts, forms, bindings, roots, widths, drivers, arguments, limit, Ok((*function, steps))),
        bindings_match_calls(bindings, selected),
        source_body_matches_steps(source, forms, body, width_limit, selected, roots, definitions, steps@),
    ensures
        source_clocked_layout(&model.circuit, function.netlist_model(), model.order, model.index),
        source_body_wires(source, forms, body, selected, roots, definitions, definitions.len()) matches Some((order, gates, slots))
            && model.order == order
            && model.circuit == function_source_circuit(layouts.inputs.total_bits_model(), order, gates,
                source_output_wires(body.input_widths@, slots, widths, drivers)),
{
    let wiring = WiringView { definitions: function.definition_wires@, gates: function.netlist.gates@, origins: function.gate_definitions@ };
    vstd::slice::axiom_spec_len(body.definitions);
    assert(bindings.len() <= usize::MAX && roots.len() <= usize::MAX);
    let (order, gates, slots) = rooted_source_body_wires(source, forms, body, layouts, capacity, width_limit, bindings,
        selected, roots, limit, steps@, body.definitions@.len() as usize, bindings.len() as usize, roots.len() as usize, wiring,
        definitions, arguments, definitions.len());
    assert(slots.len() == body.definitions@.len() && order.len() == wiring.gates.len()
        && definition_wires_pair(order, slots, layouts.definitions.ranges_model(), wiring.definitions)) by {
        reveal(rooted_mixed_trace);
        if steps@.len() == 0 { assert(wiring_empty(wiring)); }
        else { assert(steps@.last().after == wiring); }
    };
    mixed_function_output_wires(body, layouts, widths, drivers, capacity, limit, function, slots, order);
    let outputs = source_output_wires(body.input_widths@, slots, widths, drivers);
    assert forall|i: int| 0 <= i < gates.len() implies {
        let gate = #[trigger] gates[i];
        let flat = function.netlist_model().gates@[i];
        &&& source_wire_pair(order, gate.left, flat.left)
        &&& source_wire_pair(order, gate.right, flat.right)
    } by {
        reveal(rooted_mixed_trace);
        assert(steps@[steps@.len() - 1].after == wiring);
        assert(source_step_after(steps@[steps@.len() - 1]) == wiring);
    };
    function_source_layout(layouts.inputs.total_bits_model(), order, gates, outputs, function.netlist_model())
}

} // verus!
