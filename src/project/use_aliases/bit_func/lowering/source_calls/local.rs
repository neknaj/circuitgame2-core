//! 単独の基底 NOR と、配線だけで表せる右辺をソースの配線と照合する。

use super::*;
use super::super::call_arguments::source_wires::source_child_site;
use super::super::source_wires::{
    definition_wire_row_pair, definition_wires_in_extension, local_slot_wires_pair, source_local_nor,
    source_local_slot_agrees, source_local_wires,
};

verus! {

/// ローカル定義の出力を先行定義の配線表に追加する。
///
/// 基底 NOR では右辺の位置にゲートを1個対応付ける。ほかの右辺は配線表だけを延長する。
#[verifier::spinoff_prover]
pub(in crate::project::use_aliases::bit_func::lowering) proof fn local_definition_source_wiring(
    context: &SourceArguments, body: &LoweringBody, layouts: &Layouts, capacity: usize,
    before: WiringView, after: WiringView, first: usize, definition: DefinitionPosition, prior: Seq<SourceGateId>,
) -> (result: (Seq<SourceGateId>, Seq<SourceNor>, Seq<Seq<SourceWire>>))
    requires
        source_definition_start(context, body, layouts, capacity, before, first, definition, prior),
        first < body.definitions@.len(),
        before.gates.len() <= usize::MAX,
        ({
            let slot = body.definitions@[first as int];
            &&& bit_definition_matches(body.input_widths@, body.definitions@.take(first as int), slot)
            &&& slot_wiring_matches(slot, layouts, after.definitions, after.gates, after.origins, first as int)
            &&& gate_step_matches(layouts, before.definitions, slot.rhs, first, before.gates, after.gates,
                before.origins, after.origins)
            &&& after.definitions.take(before.definitions.len() as int) == before.definitions
            &&& after.definitions.len() == preceding_port_bits(definition_widths(body.definitions@), (first + 1) as nat)
            &&& slot.rhs is Nor ==> before.definitions.len() < after.definitions.len()
                && after.definitions[before.definitions.len() as int] == Wire::Gate(before.gates.len() as usize)
        }),
    ensures ({
        let (order, gates, definitions) = result;
        let slot = body.definitions@[first as int];
        let gate = SourceGateId { instance: Seq::empty(), gate: source_child_site(definition, 0) };
        let range = layouts.definitions.ranges_model()[first as int];
        let port = after.definitions.subrange(range.start as int, range.end as int);
        &&& order.take(prior.len() as int) == prior
        &&& order.len() == after.gates.len() == prior.len() + gates.len()
        &&& order.no_duplicates()
        &&& wiring_view_is_prefix(before, after)
        &&& definitions.len() == first + 1
        &&& definition_wires_pair(order, definitions, layouts.definitions.ranges_model(), after.definitions)
        &&& local_slot_wires_pair(context.input_widths, context.definitions, slot, gate, order, port, after.gates)
        &&& source_local_wires(context.input_widths, context.definitions, slot, gate) matches Some(wires)
        &&& definitions == context.definitions.push(wires)
        &&& match slot.rhs {
            BitFuncRhs::Nor { left, right } => order == prior.push(gate)
                && gates == seq![source_local_nor(context.input_widths, context.definitions, left, right)],
            _ => order == prior && gates.len() == 0,
        }
        &&& forall|i: int| 0 <= i < gates.len() ==> {
            let source = #[trigger] gates[i];
            let flat = after.gates[prior.len() + i];
            &&& source_gate_in_definition(definition, order[prior.len() + i])
            &&& source_wire_pair(order, source.left, flat.left)
            &&& source_wire_pair(order, source.right, flat.right)
        }
    }),
{
    let slots = body.definitions@;
    let slot = slots[first as int];
    let id = SourceGateId { instance: Seq::empty(), gate: source_child_site(definition, 0) };
    let (order, gates) = match slot.rhs {
        BitFuncRhs::Nor { left, right } =>
            (prior.push(id), seq![source_local_nor(context.input_widths, context.definitions, left, right)]),
        _ => (prior, Seq::<SourceNor>::empty()),
    };
    assert(source_gate_in_definition(definition, id));
    assert(order.no_duplicates()) by {
        if slot.rhs is Nor {
            assert(forall|i: int| 0 <= i < prior.len() ==> #[trigger] prior[i] != id);
        }
    };
    assert(order.take(prior.len() as int) =~= prior);
    definition_wires_in_extension(prior, order, context.definitions, layouts.definitions.ranges_model(), before.definitions);

    let widths = definition_widths(slots);
    port_bit_layout_size(widths, capacity, &layouts.definitions);
    port_bit_layout_port(widths, capacity, layouts.definitions, first);
    let ranges = layouts.definitions.ranges_model();
    let range = ranges[first as int];
    let start = range.start as int;
    let end = range.end as int;
    assert(start == before.definitions.len() && end == after.definitions.len());
    assert(after.definitions.take(start) == before.definitions);
    assert(wiring_view_is_prefix(before, after) && order.len() == after.gates.len() == prior.len() + gates.len()) by {
        reveal(gate_step_matches);
        assert(after.gates.len() == before.gates.len() + (if slot.rhs is Nor { 1int } else { 0int }));
        assert(after.gates.take(before.gates.len() as int) =~= before.gates);
        assert(after.origins.take(before.origins.len() as int) =~= before.origins);
    };
    if slot.rhs is Nor {
        assert(after.definitions[start] == Wire::Gate(prior.len() as usize));
        assert(order[prior.len() as int] == id);
    }
    assert(context.definitions.len() == first);
    assert(bit_definition_matches(body.input_widths@, slots.take(context.definitions.len() as int),
        slots[context.definitions.len() as int]));
    assert(slot_wiring_matches(slots[context.definitions.len() as int], layouts,
        after.definitions, after.gates, after.origins, context.definitions.len() as int));
    assert(definition_wires_pair(order, context.definitions, ranges, after.definitions.take(start)));
    assert(slot.rhs is Nor ==> (after.definitions[start] matches Wire::Gate(index)
        && index < order.len() && order[index as int] == id));
    source_local_slot_agrees(body.input_widths@, slots, layouts, capacity, context.definitions, after.definitions,
        after.gates, after.origins, order, id);

    let port = after.definitions.subrange(start, end);
    assert(local_slot_wires_pair(body.input_widths@, context.definitions, slot, id, order, port, after.gates));
    let source = source_local_wires(context.input_widths, context.definitions, slot, id)->Some_0;
    let definitions = context.definitions.push(source);
    assert forall|i: int| 0 <= i < definitions.len() implies
        definition_wire_row_pair(order, #[trigger] definitions[i], ranges[i], after.definitions) by {
        if i < first {
            let range = ranges[i];
            assert(definition_wire_row_pair(order, context.definitions[i], range, before.definitions));
            assert(after.definitions.subrange(range.start as int, range.end as int)
                =~= before.definitions.subrange(range.start as int, range.end as int));
        }
    };
    assert forall|i: int| 0 <= i < gates.len() implies {
        let source = #[trigger] gates[i];
        let flat = after.gates[prior.len() + i];
        &&& source_gate_in_definition(definition, order[prior.len() + i])
        &&& source_wire_pair(order, source.left, flat.left)
        &&& source_wire_pair(order, source.right, flat.right)
    } by {
        if let BitFuncRhs::Nor { left, right } = slot.rhs {
            assert(i == 0);
            let index = prior.len() as usize;
            assert(port[0] == Wire::Gate(index));
            assert(order[prior.len() as int] == id);
            let nor = source_local_nor(body.input_widths@, context.definitions, left, right);
            assert(source_wire_pair(order, nor.left, after.gates[index as int].left));
            assert(source_wire_pair(order, nor.right, after.gates[index as int].right));
            assert(gates[i] == nor);
        }
    };
    (order, gates, definitions)
}

} // verus!
