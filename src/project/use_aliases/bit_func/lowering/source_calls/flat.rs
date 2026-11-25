//! 入れ子を含まない通常呼び出しのソース配線を照合する。

use super::*;
use super::super::super::frontend::nested_argument_output_matches;
use super::super::call_arguments::child_argument_width_ready;
use super::super::call_arguments::source_wires::{
    source_call_definition_without_children, source_child_outputs_pair, source_child_site, source_root_placement_agrees,
};
use super::super::call_group::{call_group_result, call_group_wires_match, flat_call_group_wiring};
use crate::netlist::source_gate_belongs_to_call;

verus! {

/// 成功した通常呼び出しの配線を、ソースの引数と左辺に対応付ける。
///
/// 呼び出し先のゲートが空の場合も、左辺に渡す出力配線を照合する。
#[verifier::spinoff_prover]
pub(in crate::project::use_aliases::bit_func::lowering) proof fn flat_definition_source_wiring(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize, width_limit: u64,
    selected: &ResolvedTemplateCall, before: WiringView, after: WiringView, gate_limit: usize,
    definition: DefinitionPosition, prior: Seq<SourceGateId>, model: SourceChildModel,
) -> (result: (Seq<SourceGateId>, Seq<SourceNor>, Seq<Seq<SourceWire>>))
    requires
        context.source == selected.group.expression.source,
        source_definition_start(context, body, layouts, capacity, before, selected.group.outputs.start, definition, prior),
        before.origins.len() == before.gates.len(),
        resolved_call_fits_body(*selected, body.input_widths@, body.definitions@, context.forms, width_limit),
        selected.children@.len() == 0,
        call_group_result(selected.group, context.forms, selected.arguments@, layouts, selected.template.circuit_model(),
            before, after, gate_limit, definition_widths(body.definitions@), selected.template.output_widths_model(), Ok(())),
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
        &&& source_call_definition_wiring(context, definition, selected.group.references.start, prior,
            selected.children@, Seq::empty(), Some(model), selected.arguments@, template.input_widths_model()) matches Some(source)
            && source.0 == order && source.1 == gates
            && definitions == source_definition_outputs(context.definitions, source.2,
                template.circuit_model().output_layout_model().ranges_model())
        &&& forall|i: int| 0 <= i < gates.len() ==> {
            let source = #[trigger] gates[i];
            let flat = after.gates[prior.len() + i];
            &&& source_gate_in_definition(definition, order[prior.len() + i])
            &&& source_wire_pair(order, source.left, flat.left)
            &&& source_wire_pair(order, source.right, flat.right)
        }
    }),
{
    let template = selected.template;
    let callee = template.circuit_model();
    let widths = template.input_widths_model();
    let input_layout = callee.input_layout_model();
    let arguments = selected.arguments@;
    let first = selected.group.outputs.start;
    let site = source_child_site(definition, 0);
    let (invocation, mapped, outputs) = flat_call_group_wiring(selected.group, context.forms, arguments, layouts, callee,
        before, after, gate_limit, definition_widths(body.definitions@), template.output_widths_model());
    port_bit_layout_size(widths, template.bit_limit_model(), input_layout);
    assert(source_child_outputs_pair(prior, context.children, invocation.child_ranges@, invocation.child_wires@));
    assert forall|i: int| 0 <= i < prior.len() implies
        !source_gate_belongs_to_call(site, #[trigger] prior[i]) by {
        if source_gate_belongs_to_call(site, prior[i]) {
            assert(source_gate_in_definition(definition, prior[i]));
        }
    };
    assert forall|port: int| 0 <= port < arguments.len() implies {
        let argument = #[trigger] arguments[port];
        &&& argument_matches_width(context.source, context.forms, context.input_widths,
            body.definitions@.take(context.definitions.len() as int), argument, widths[port], width_limit)
        &&& widths[port] <= usize::MAX
        &&& child_argument_width_ready(invocation.child_ranges@, invocation.child_wires@.len(), argument.source, widths[port] as usize)
    } by {
        assert(root_argument_matches_width(context.source, context.forms, body.input_widths@,
            body.definitions@, *selected, port, width_limit));
        reveal(nested_argument_output_matches);
        assert(nested_argument_output_matches(*selected, 0, arguments[port], widths[port]));
        assert(!(arguments[port].source is NestedCall));
        port_bit_layout_port(widths, template.bit_limit_model(), *input_layout, port as usize);
    };
    let (order, gates, source) = source_root_placement_agrees(context, body, layouts, capacity, width_limit, &invocation,
        arguments, widths, input_layout, template.bit_limit_model(), callee.netlist_model(), mapped, outputs,
        before.gates, after.gates, site, prior, Some(model));
    assert(selected.children@ =~= Seq::empty());
    source_call_definition_without_children(context, definition, selected.group.references.start, prior,
        Some(model), arguments, widths);
    assert(wiring_view_is_prefix(before, after)) by {
        reveal(call_group_result);
        reveal(call_group_wires_match);
        assert(after.definitions.take(before.definitions.len() as int) =~= before.definitions);
    };
    assert forall|i: int| 0 <= i < gates.len() implies {
        let source = #[trigger] gates[i];
        let flat = after.gates[prior.len() + i];
        &&& source_gate_in_definition(definition, order[prior.len() + i])
        &&& source_wire_pair(order, source.left, flat.left)
        &&& source_wire_pair(order, source.right, flat.right)
    } by {
        assert(source_gate_belongs_to_call(site, order[prior.len() + i]));
    };
    let ports = callee.output_layout_model().ranges_model();
    port_bit_layout_size(template.output_widths_model(), template.bit_limit_model(), callee.output_layout_model());
    append_template_output_ports(context, body, layouts, capacity, first, before.definitions, after.definitions,
        template, source, outputs, prior, order);
    (order, gates, source_definition_outputs(context.definitions, source, ports))
}

} // verus!
