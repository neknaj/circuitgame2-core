//! 呼び出し右辺のソース配線を、変換済みの左辺スロットと照合する。

pub(super) mod flat;

use super::*;
use super::super::frontend::{
    argument_matches_width, expression_argument_matches_width, expression_input_width, nor_root_arguments_match_widths,
    root_argument_matches_width,
};
use super::super::instances::call_output_range_matches;
use super::super::templates::{FunctionTemplate, ResolvedExpressionCall, ResolvedNorRoot};
use super::call_arguments::child_calls::{child_call_binding, nested_root_wiring_result, nor_root_children_bound};
use super::call_arguments::source_wires::{
    SourceArguments, SourceChildModel, source_call_definition_agrees, source_call_definition_wiring,
    source_child_calls_ready, source_gate_in_definition,
};
use super::call_group::{
    WiringView, nested_call_group_frame, nested_call_group_result, nested_call_group_wiring,
    nested_group_invocation_matches, nor_call_group_frame, nor_call_group_result, nor_call_group_wiring,
    nor_group_invocation_matches, wiring_view_is_prefix,
};
use super::source_wires::{
    definition_wires_pair, source_definition_outputs, source_definition_outputs_agree, source_wires_pair,
};
use crate::netlist::{SourceGateId, SourceNor, SourceWire, builtin_nor_template, source_clocked_layout, source_wire_pair};
use crate::project::DefinitionPosition;

verus! {

/// 型検査を終えた右辺へ渡す、先行する定義とゲートの対応を表す。
pub(super) open spec fn source_definition_start(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize,
    before: WiringView, first: usize, definition: DefinitionPosition, order: Seq<SourceGateId>,
) -> bool {
    &&& body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts)
    &&& context.input_widths == body.input_widths@ && context.definitions.len() == first <= body.definitions@.len()
    &&& context.children == Map::<usize, Seq<SourceWire>>::empty()
    &&& before.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), first as nat)
    &&& definition_wires_pair(order, context.definitions, layouts.definitions.ranges_model(), before.definitions)
    &&& order.len() == before.gates.len() && order.no_duplicates()
    &&& forall|gate: int| 0 <= gate < order.len() ==> !source_gate_in_definition(definition, #[trigger] order[gate])
}

/// 通常の子回路は解決済みテンプレートに対応し、基底 NOR の回路は呼び出し位置から得る。
pub(super) open spec fn source_models_match_calls(
    children: Seq<ResolvedExpressionCall>, models: Seq<Option<SourceChildModel>>, references: Range<usize>,
) -> bool {
    &&& references.start <= references.end
    &&& children.len() == models.len()
    &&& forall|i: int| 0 <= i < children.len() ==> {
        let child = #[trigger] children[i];
        &&& references.start < child.child.reference < references.end
        &&& match child.template {
            Some(template) => models[i] matches Some(model)
                && source_clocked_layout(&model.circuit, template.circuit_model().netlist_model(), model.order, model.index),
            None => models[i].is_none(),
        }
    }
}

/// 通常関数の出力ポートを呼び出し元の連続した左辺に割り当てる。
proof fn append_template_output_ports(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize, first: usize,
    before: Seq<Wire>, after: Seq<Wire>, template: &FunctionTemplate, source: Seq<SourceWire>, outputs: Seq<Wire>,
    prior: Seq<SourceGateId>, order: Seq<SourceGateId>,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        context.definitions.len() == first <= body.definitions@.len(),
        definition_wires_pair(prior, context.definitions, layouts.definitions.ranges_model(), before),
        before.len() == preceding_port_bits(definition_widths(body.definitions@), first as nat),
        port_bit_layout_result(template.output_widths_model(), template.bit_limit_model(),
            Ok(*template.circuit_model().output_layout_model())),
        first + template.output_widths_model().len() <= body.definitions@.len(),
        forall|i: int| 0 <= i < template.output_widths_model().len() ==>
            body.definitions@[first + i].width == #[trigger] template.output_widths_model()[i],
        order.take(prior.len() as int) == prior, prior.len() <= order.len(),
        source_wires_pair(order, source, outputs),
        outputs.len() == template.circuit_model().output_layout_model().total_bits_model(),
        after == before + outputs,
    ensures definition_wires_pair(order,
        source_definition_outputs(context.definitions, source, template.circuit_model().output_layout_model().ranges_model()),
        layouts.definitions.ranges_model(), after),
{
    let widths = template.output_widths_model();
    let port_layout = template.circuit_model().output_layout_model();
    let ports = port_layout.ranges_model();
    let ranges = layouts.definitions.ranges_model();
    let definition_widths = definition_widths(body.definitions@);
    port_bit_layout_size(widths, template.bit_limit_model(), port_layout);
    port_bit_layout_size(definition_widths, capacity, &layouts.definitions);
    assert forall|i: int| 0 <= i < widths.len() implies
        definition_widths[first + i] == #[trigger] widths[i] by {
        assert(definition_widths[first + i] == body.definitions@[first + i].width);
    };
    assert forall|i: int| 0 <= i < ports.len() implies {
        let port = #[trigger] ports[i];
        let slot = ranges[first + i];
        &&& port.start <= port.end <= outputs.len()
        &&& slot.start == before.len() + port.start && slot.end == before.len() + port.end
    } by {
        port_bit_layout_port(widths, template.bit_limit_model(), *port_layout, i as usize);
        call_output_range_matches(definition_widths, widths, first, i as usize, layouts.definitions, *port_layout,
            capacity, template.bit_limit_model());
    };
    source_definition_outputs_agree(prior, order, context.definitions, before, after, ranges, source, outputs, ports);
}

/// 入れ子の通常呼び出しが生成したゲートと、左辺が受け取った各出力ポートを照合する。
#[verifier::spinoff_prover]
pub(super) proof fn nested_definition_source_wiring(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    selected: &ResolvedTemplateCall, builtin: &(NorNetlist, PortBitLayout), before: WiringView, after: WiringView,
    gate_limit: usize, child_limit: usize, definition: DefinitionPosition, prior: Seq<SourceGateId>,
    children: Seq<Option<SourceChildModel>>, model: SourceChildModel,
) -> (result: (Seq<SourceGateId>, Seq<SourceNor>, Seq<Seq<SourceWire>>))
    requires
        context.source == selected.group.expression.source,
        source_definition_start(context, body, layouts, capacity, before, selected.group.outputs.start, definition, prior),
        resolved_call_fits_body(*selected, body.input_widths@, body.definitions@, context.forms, width_limit),
        nested_call_group_result(selected, context.forms, layouts, builtin, before, after, gate_limit, child_limit,
            definition_widths(body.definitions@), Ok(())),
        source_models_match_calls(selected.children@, children, selected.group.references),
        ({
            let callee = selected.template.circuit_model();
            let capacity = selected.template.bit_limit_model();
            &&& port_bit_layout_result(selected.template.input_widths_model(), capacity, Ok(*callee.input_layout_model()))
            &&& port_bit_layout_result(selected.template.output_widths_model(), capacity, Ok(*callee.output_layout_model()))
            &&& selected.arguments@.len() == selected.template.input_widths_model().len()
            &&& callee.netlist_model().input_count == callee.input_layout_model().total_bits_model()
            &&& callee.netlist_model().outputs@.len() == callee.output_layout_model().total_bits_model()
            &&& source_clocked_layout(&model.circuit, callee.netlist_model(), model.order, model.index)
        }),
    ensures ({
        let (order, gates, definitions) = result;
        let template = selected.template;
        &&& order.take(prior.len() as int) == prior
        &&& order.len() == after.gates.len() == prior.len() + gates.len()
        &&& order.no_duplicates()
        &&& wiring_view_is_prefix(before, after)
        &&& definitions.len() == selected.group.outputs.end
        &&& definition_wires_pair(order, definitions, layouts.definitions.ranges_model(), after.definitions)
        &&& source_call_definition_wiring(context, definition, selected.group.references.start, prior, selected.children@,
            children, Some(model), selected.arguments@, template.input_widths_model()) matches Some(source)
            && source.0 == order && source.1 == gates
            && definitions == source_definition_outputs(context.definitions, source.2, template.circuit_model().output_layout_model().ranges_model())
        &&& forall|i: int| 0 <= i < gates.len() ==> {
            let source = #[trigger] gates[i];
            let flat = after.gates[prior.len() + i];
            &&& source_gate_in_definition(definition, order[prior.len() + i])
            &&& source_wire_pair(order, source.left, flat.left)
            &&& source_wire_pair(order, source.right, flat.right)
        }
    }),
{
    let widths = definition_widths(body.definitions@);
    let template = selected.template;
    let callee = template.circuit_model();
    let input_widths = template.input_widths_model();
    let references = selected.group.references;
    let (invocation, calls, outputs) = nested_call_group_wiring(selected, context.forms, layouts, builtin, before, after,
        gate_limit, child_limit, widths);
    nested_call_group_frame(selected, context.forms, layouts, builtin, before, after, gate_limit, child_limit, widths, Ok(()));
    reveal(nested_group_invocation_matches);
    assert(source_child_calls_ready(context, body, width_limit, &invocation, calls, references, builtin,
        definition, prior, selected.children@, children)) by {
        assert forall|i: int| 0 <= i < calls.len() implies {
            let call = #[trigger] calls[i];
            let child = selected.children@[i];
            &&& call.reference > 0
            &&& forall|port: int| 0 <= port < call.arguments@.len() ==>
                argument_matches_width(context.source, context.forms, context.input_widths,
                    body.definitions@.take(context.definitions.len() as int), #[trigger] call.arguments@[port],
                    call._input_widths@[port], width_limit)
        } by {
            let call = calls[i];
            let child = selected.children@[i];
            assert(child_call_binding(child, references, builtin, call));
            assert(references.start < child.child.reference < references.end);
            assert forall|port: int| 0 <= port < call.arguments@.len() implies
                argument_matches_width(context.source, context.forms, context.input_widths,
                    body.definitions@.take(context.definitions.len() as int), #[trigger] call.arguments@[port],
                    call._input_widths@[port], width_limit) by {
                assert(expression_argument_matches_width(context.source, context.forms, body.input_widths@,
                    body.definitions@, *selected, i, port, width_limit));
                assert(call._input_widths@[port] == expression_input_width(child, port));
            };
        };
    };
    assert forall|port: int| 0 <= port < selected.arguments@.len() implies
        argument_matches_width(context.source, context.forms, context.input_widths,
            body.definitions@.take(context.definitions.len() as int), #[trigger] selected.arguments@[port],
            input_widths[port], width_limit) by {
        assert(root_argument_matches_width(context.source, context.forms, body.input_widths@,
            body.definitions@, *selected, port, width_limit));
    };
    let (order, gates, source) = source_call_definition_agrees(context, body, layouts, capacity, width_limit, &invocation,
        calls, references, builtin, definition, prior, selected.children@, children, Some(model), selected.arguments@,
        input_widths, callee.input_layout_model(), template.bit_limit_model(), callee.netlist_model(),
        before.gates, after.gates, layouts.inputs.total_bits_model(), outputs);
    assert(after.definitions =~= before.definitions + outputs);
    assert(outputs.len() == callee.netlist_model().outputs@.len()) by { reveal(nested_root_wiring_result); };
    let ports = callee.output_layout_model().ranges_model();
    port_bit_layout_size(template.output_widths_model(), template.bit_limit_model(), callee.output_layout_model());
    append_template_output_ports(context, body, layouts, capacity, selected.group.outputs.start, before.definitions,
        after.definitions, template, source, outputs, prior, order);
    (order, gates, source_definition_outputs(context.definitions, source, ports))
}

/// 基底 NOR の右辺全体を照合し、左辺の1ビットを定義配線表に追加する。
#[verifier::spinoff_prover]
pub(super) proof fn nor_definition_source_wiring(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    selected: &ResolvedNorRoot, references: Range<usize>, builtin: &(NorNetlist, PortBitLayout),
    before: WiringView, after: WiringView, gate_limit: usize, child_limit: usize,
    definition: DefinitionPosition, prior: Seq<SourceGateId>, children: Seq<Option<SourceChildModel>>,
) -> (result: (Seq<SourceGateId>, Seq<SourceNor>, Seq<Seq<SourceWire>>))
    requires
        context.source == selected.prepared.root.expression.source,
        source_definition_start(context, body, layouts, capacity, before, selected.prepared.output_slot, definition, prior),
        selected.prepared.output_slot < body.definitions@.len(),
        body.definitions@[selected.prepared.output_slot as int].width == 1,
        nor_root_arguments_match_widths(selected, references, context.source, context.forms, body.input_widths@,
            body.definitions@, selected.prepared.output_slot, width_limit),
        nor_call_group_result(selected, references, context.forms, layouts, builtin, before, after, gate_limit, child_limit,
            definition_widths(body.definitions@), Ok(())),
        source_models_match_calls(selected.children@, children, references),
    ensures ({
        let (order, gates, definitions) = result;
        &&& order.take(prior.len() as int) == prior
        &&& order.len() == after.gates.len() == prior.len() + gates.len()
        &&& order.no_duplicates()
        &&& wiring_view_is_prefix(before, after)
        &&& definitions.len() == selected.prepared.output_slot + 1
        &&& definition_wires_pair(order, definitions, layouts.definitions.ranges_model(), after.definitions)
        &&& source_call_definition_wiring(context, definition, references.start, prior, selected.children@,
            children, None, selected.arguments@, seq![1u64, 1u64]) matches Some(source)
            && source.0 == order && source.1 == gates
            && definitions == source_definition_outputs(context.definitions, source.2, seq![0usize..1usize])
        &&& forall|i: int| 0 <= i < gates.len() ==> {
            let source = #[trigger] gates[i];
            let flat = after.gates[prior.len() + i];
            &&& source_gate_in_definition(definition, order[prior.len() + i])
            &&& source_wire_pair(order, source.left, flat.left)
            &&& source_wire_pair(order, source.right, flat.right)
        }
    }),
{
    let widths = definition_widths(body.definitions@);
    let slot = selected.prepared.output_slot;
    let (invocation, calls, outputs) = nor_call_group_wiring(selected, references, context.forms,
        layouts, builtin, before, after, gate_limit, child_limit, widths);
    nor_call_group_frame(selected, references, context.forms, layouts, builtin, before, after,
        gate_limit, child_limit, widths, Ok(()));
    reveal(nor_group_invocation_matches);
    reveal(nor_root_children_bound);
    assert(builtin_nor_template(&builtin.0)) by { reveal(nor_evaluation_ready); };
    assert(source_child_calls_ready(context, body, width_limit, &invocation, calls, references, builtin,
        definition, prior, selected.children@, children)) by {
        assert forall|i: int| 0 <= i < calls.len() implies {
            let call = #[trigger] calls[i];
            &&& call.reference > 0
            &&& forall|port: int| 0 <= port < call.arguments@.len() ==>
                argument_matches_width(context.source, context.forms, context.input_widths,
                    body.definitions@.take(context.definitions.len() as int), #[trigger] call.arguments@[port],
                    call._input_widths@[port], width_limit)
        } by {
            let call = calls[i];
            let child = selected.children@[i];
            assert(child_call_binding(child, references, builtin, call));
            assert(references.start < child.child.reference < references.end);
            assert forall|port: int| 0 <= port < call.arguments@.len() implies
                argument_matches_width(context.source, context.forms, context.input_widths,
                    body.definitions@.take(context.definitions.len() as int), #[trigger] call.arguments@[port],
                    call._input_widths@[port], width_limit) by {
                assert(call.arguments@[port] == child.arguments@[port]);
                assert(call._input_widths@[port] == expression_input_width(child, port));
            };
        };
    };
    let input_widths = seq![1u64, 1u64];
    assert forall|port: int| 0 <= port < selected.arguments@.len() implies
        argument_matches_width(context.source, context.forms, context.input_widths,
            body.definitions@.take(context.definitions.len() as int), #[trigger] selected.arguments@[port],
            input_widths[port], width_limit) by {
        assert(input_widths[port] == 1);
    };
    let (order, gates, source) = source_call_definition_agrees(context, body, layouts, capacity, width_limit, &invocation,
        calls, references, builtin, definition, prior, selected.children@, children, None, selected.arguments@,
        input_widths, &builtin.1, 2, &builtin.0, before.gates, after.gates, layouts.inputs.total_bits_model(), outputs);
    port_bit_layout_size(widths, capacity, &layouts.definitions);
    port_bit_layout_port(widths, capacity, layouts.definitions, slot);
    let ranges = layouts.definitions.ranges_model();
    let range = ranges[slot as int];
    assert(range.start == before.definitions.len() && range.end == after.definitions.len());
    assert(after.definitions =~= before.definitions + outputs);
    let ports = seq![0usize..1usize];
    source_definition_outputs_agree(prior, order, context.definitions, before.definitions, after.definitions, ranges,
        source, outputs, ports);
    (order, gates, source_definition_outputs(context.definitions, source, ports))
}

} // verus!
