//! 呼び出し先の入力とゲートを、呼び出し元の配線番号に対応付ける。

use alloc::vec::Vec;
use crate::netlist::{NorGate, NorNetlist, PortBitLayout, Wire};
#[cfg(verus_only)]
use crate::netlist::{
    gate_values_match, gates_available, nor_evaluation, nor_evaluation_ready, output_ports_available,
    output_values_match, port_bit_layout_port, port_bit_layout_result, preceding_port_bits,
    wire_available, wire_value,
};
use vstd::prelude::*;

verus! {

/// 呼び出し先の入力を実引数で置き換え、ゲート番号を追加位置から数え直す。
pub(super) open spec fn instance_wire(wire: Wire, arguments: Seq<Wire>, base: usize) -> Wire {
    match wire {
        Wire::Input(index) => arguments[index as int],
        Wire::Constant(value) => Wire::Constant(value),
        Wire::Gate(index) => Wire::Gate((base + index) as usize),
    }
}

/// 呼び出し先の1ビット分の配線を、呼び出し元の配線に変換する。
pub(super) fn instantiate_wire(wire: Wire, arguments: &[Wire], base: usize)
    -> (mapped: Wire)
    requires
        wire matches Wire::Input(index) ==> index < arguments@.len(),
        wire matches Wire::Gate(index) ==> base + index <= usize::MAX,
    ensures mapped == instance_wire(wire, arguments@, base),
{
    match wire {
        Wire::Input(index) => arguments[index],
        Wire::Constant(value) => Wire::Constant(value),
        Wire::Gate(index) => Wire::Gate(base + index),
    }
}

/// 呼び出し先で参照できる配線は、番号を変換しても参照できる。
pub(super) proof fn instance_wire_available(
    wire: Wire, arguments: Seq<Wire>, base: usize, caller_inputs: nat, callee_gates: nat,
)
    requires
        wire_available(wire, arguments.len(), callee_gates),
        base + callee_gates <= usize::MAX,
        forall|i: int| 0 <= i < arguments.len() ==>
            wire_available(#[trigger] arguments[i], caller_inputs, base as nat),
    ensures wire_available(instance_wire(wire, arguments, base), caller_inputs, (base + callee_gates) as nat),
{
    match wire {
        Wire::Input(index) => {
            assert(wire_available(arguments[index as int], caller_inputs, base as nat));
        },
        Wire::Constant(_) => {},
        Wire::Gate(_) => {},
    }
}

/// 実引数の値と追加したゲートの値が対応するとき、変換後の配線も同じ値を持つ。
pub(super) proof fn instance_wire_preserves_value(
    wire: Wire, arguments: Seq<Wire>, base: usize, inputs: Seq<bool>, gates: Seq<bool>,
    callee_inputs: Seq<bool>, callee_gates: Seq<bool>,
)
    requires
        wire_available(wire, callee_inputs.len(), callee_gates.len()),
        arguments.len() == callee_inputs.len(),
        base + callee_gates.len() <= gates.len() <= usize::MAX,
        forall|i: int| 0 <= i < arguments.len() ==> {
            let argument = #[trigger] arguments[i];
            wire_available(argument, inputs.len(), base as nat)
                && wire_value(argument, inputs, gates) == callee_inputs[i]
        },
        forall|i: int| 0 <= i < callee_gates.len() ==> gates[base + i] == #[trigger] callee_gates[i],
    ensures
        wire_available(instance_wire(wire, arguments, base), inputs.len(), gates.len()),
        wire_value(instance_wire(wire, arguments, base), inputs, gates) == wire_value(wire, callee_inputs, callee_gates),
{
    instance_wire_available(wire, arguments, base, inputs.len(), callee_gates.len());
    match wire {
        Wire::Input(index) => {
            assert(wire_value(arguments[index as int], inputs, gates) == callee_inputs[index as int]);
        },
        Wire::Constant(_) => {},
        Wire::Gate(index) => {
            assert(gates[base + index] == callee_gates[index as int]);
        },
    }
}

pub(super) open spec fn instance_gates_match(
    before: Seq<NorGate>, callee: Seq<NorGate>, arguments: Seq<Wire>, added: Seq<NorGate>,
) -> bool {
    &&& added.len() == before.len() + callee.len()
    &&& added.take(before.len() as int) == before
    &&& forall|i: int| 0 <= i < callee.len() ==> {
        let original = callee[i];
        let next = #[trigger] added[before.len() + i];
        &&& next.left == instance_wire(original.left, arguments, before.len() as usize)
        &&& next.right == instance_wire(original.right, arguments, before.len() as usize)
    }
}

/// 呼び出し先のゲートを先頭から追加する。指定した最大件数を超える場合は追加しない。
pub(super) fn append_instance_gates(
    caller: &mut Vec<NorGate>, callee: &[NorGate], arguments: &[Wire],
    capacity: usize, Ghost(inputs): Ghost<nat>,
) -> (appended: bool)
    requires
        old(caller)@.len() <= capacity,
        gates_available(old(caller)@, inputs, old(caller)@.len() as int),
        gates_available(callee@, arguments@.len(), callee@.len() as int),
        forall|i: int| 0 <= i < arguments@.len() ==>
            wire_available(#[trigger] arguments@[i], inputs, old(caller)@.len()),
    ensures
        appended <==> old(caller)@.len() + callee@.len() <= capacity,
        !appended ==> final(caller)@ == old(caller)@,
        appended ==> instance_gates_match(old(caller)@, callee@, arguments@, final(caller)@)
            && gates_available(final(caller)@, inputs, final(caller)@.len() as int),
{
    let base = caller.len();
    if callee.len() > capacity - base {
        return false;
    }
    let ghost before = caller@;
    assert(caller@.take(base as int) =~= before);
    let mut i = 0;
    while i < callee.len()
        invariant
            i <= callee@.len(), base == before.len(), base + callee@.len() <= capacity,
            gates_available(callee@, arguments@.len(), callee@.len() as int),
            gates_available(caller@, inputs, caller@.len() as int),
            instance_gates_match(before, callee@.take(i as int), arguments@, caller@),
            forall|j: int| 0 <= j < arguments@.len() ==> wire_available(#[trigger] arguments@[j], inputs, base as nat),
        decreases callee@.len() - i,
    {
        let gate = callee[i];
        let left = instantiate_wire(gate.left, arguments, base);
        let right = instantiate_wire(gate.right, arguments, base);
        proof {
            instance_wire_available(gate.left, arguments@, base, inputs, i as nat);
            instance_wire_available(gate.right, arguments@, base, inputs, i as nat);
        }
        let ghost previous = caller@;
        caller.push(NorGate { left, right });
        proof {
            assert(caller@.take(base as int) =~= before);
            assert forall|j: int| 0 <= j < caller@.len() implies {
                &&& wire_available((#[trigger] caller@[j]).left, inputs, j as nat)
                &&& wire_available(caller@[j].right, inputs, j as nat)
            } by {
                if j < previous.len() { assert(caller@[j] == previous[j]); }
            };
            assert forall|j: int| 0 <= j < i + 1 implies {
                let original = callee@[j];
                let next = #[trigger] caller@[base + j];
                &&& next.left == instance_wire(original.left, arguments@, base)
                &&& next.right == instance_wire(original.right, arguments@, base)
            } by {
                if j < i {
                    assert(caller@[base + j] == previous[base + j]);
                    assert(callee@.take(i as int)[j] == callee@[j]);
                }
            };
        }
        i += 1;
    }
    assert(callee@.take(i as int) =~= callee@);
    true
}

pub(super) open spec fn instance_outputs_match(
    callee: Seq<Wire>, arguments: Seq<Wire>, base: usize, mapped: Seq<Wire>,
) -> bool {
    &&& mapped.len() == callee.len()
    &&& forall|i: int| 0 <= i < mapped.len() ==> (#[trigger] mapped[i]) == instance_wire(callee[i], arguments, base)
}

/// 呼び出し先を一度追加し、出力をポートの宣言順・ポート内のビット順で返す。
/// ゲートの最大件数を超える場合は、呼び出し元の配線を変更せずに `None` を返す。
pub(super) fn append_instance(
    caller: &mut Vec<NorGate>, callee: &NorNetlist, arguments: &[Wire],
    capacity: usize, Ghost(inputs): Ghost<nat>,
) -> (outputs: Option<Vec<Wire>>)
    requires
        old(caller)@.len() <= capacity,
        gates_available(old(caller)@, inputs, old(caller)@.len() as int),
        nor_evaluation_ready(callee, arguments@.len()),
        forall|i: int| 0 <= i < arguments@.len() ==>
            wire_available(#[trigger] arguments@[i], inputs, old(caller)@.len()),
    ensures
        outputs.is_some() <==> old(caller)@.len() + callee.gates@.len() <= capacity,
        outputs.is_none() ==> final(caller)@ == old(caller)@,
        outputs matches Some(mapped) ==> {
            &&& instance_gates_match(old(caller)@, callee.gates@, arguments@, final(caller)@)
            &&& gates_available(final(caller)@, inputs, final(caller)@.len() as int)
            &&& instance_outputs_match(callee.outputs@, arguments@, old(caller)@.len() as usize, mapped@)
            &&& output_ports_available(mapped@, inputs, final(caller)@.len(), mapped@.len() as int)
        },
{
    let base = caller.len();
    let ghost before = caller@;
    if !append_instance_gates(caller, callee.gates.as_slice(), arguments, capacity, Ghost(inputs)) {
        return None;
    }
    let mut mapped: Vec<Wire> = Vec::new();
    let mut i = 0;
    while i < callee.outputs.len()
        invariant
            base == before.len(), caller@.len() == base + callee.gates@.len() <= capacity,
            i == mapped@.len() <= callee.outputs@.len(),
            nor_evaluation_ready(callee, arguments@.len()),
            instance_gates_match(before, callee.gates@, arguments@, caller@),
            gates_available(caller@, inputs, caller@.len() as int),
            instance_outputs_match(callee.outputs@.take(i as int), arguments@, base, mapped@),
            output_ports_available(mapped@, inputs, caller@.len(), i as int),
            forall|j: int| 0 <= j < arguments@.len() ==> wire_available(#[trigger] arguments@[j], inputs, base as nat),
        decreases callee.outputs@.len() - i,
    {
        let output = callee.outputs[i];
        let wire = instantiate_wire(output, arguments, base);
        proof { instance_wire_available(output, arguments@, base, inputs, callee.gates@.len()); }
        let ghost previous = mapped@;
        mapped.push(wire);
        proof {
            assert forall|j: int| 0 <= j < mapped@.len() implies {
                &&& (#[trigger] mapped@[j]) == instance_wire(callee.outputs@[j], arguments@, base)
                &&& wire_available(mapped@[j], inputs, caller@.len())
            } by {
                if j < i {
                    assert(mapped@[j] == previous[j]);
                    assert(callee.outputs@.take(i as int)[j] == callee.outputs@[j]);
                }
            };
        }
        i += 1;
    }
    assert(callee.outputs@.take(i as int) =~= callee.outputs@);
    Some(mapped)
}

pub(super) open spec fn instance_arguments_match(
    arguments: Seq<Wire>, inputs: Seq<bool>, gates: Seq<bool>, base: nat, callee_inputs: Seq<bool>,
) -> bool {
    &&& arguments.len() == callee_inputs.len()
    &&& forall|i: int| 0 <= i < arguments.len() ==> {
        let argument = #[trigger] arguments[i];
        &&& wire_available(argument, inputs.len(), base)
        &&& wire_value(argument, inputs, gates) == callee_inputs[i]
    }
}

proof fn instance_gate_values_agree(
    before: Seq<NorGate>, callee: Seq<NorGate>, combined: Seq<NorGate>, arguments: Seq<Wire>,
    inputs: Seq<bool>, values: Seq<bool>, callee_inputs: Seq<bool>, callee_values: Seq<bool>, count: nat,
)
    requires
        before.len() + callee.len() <= combined.len(),
        instance_gates_match(before, callee, arguments, combined.take((before.len() + callee.len()) as int)),
        gate_values_match(inputs, combined, values),
        gate_values_match(callee_inputs, callee, callee_values),
        values.len() == combined.len() <= usize::MAX, callee_values.len() == callee.len(),
        instance_arguments_match(arguments, inputs, values, before.len(), callee_inputs),
        count <= callee.len(),
    ensures forall|i: int| 0 <= i < count ==> values[before.len() + i] == #[trigger] callee_values[i],
    decreases count,
{
    if count > 0 {
        let i = count - 1;
        instance_gate_values_agree(before, callee, combined, arguments, inputs, values, callee_inputs, callee_values, i as nat);
        reveal(gate_values_match);
        let base = before.len() as usize;
        let gate = callee[i];
        let next = combined[base + i];
        assert(next == combined.take((before.len() + callee.len()) as int)[before.len() + i]);
        let prefix = callee_values.take(i);
        assert forall|j: int| 0 <= j < prefix.len() implies values[base + j] == #[trigger] prefix[j] by {
            assert(prefix[j] == callee_values[j]);
        };
        instance_wire_preserves_value(gate.left, arguments, base, inputs, values, callee_inputs, prefix);
        instance_wire_preserves_value(gate.right, arguments, base, inputs, values, callee_inputs, prefix);
        assert(wire_value(gate.left, callee_inputs, prefix) == wire_value(gate.left, callee_inputs, callee_values));
        assert(wire_value(gate.right, callee_inputs, prefix) == wire_value(gate.right, callee_inputs, callee_values));
        assert(next.left == instance_wire(gate.left, arguments, base));
        assert(next.right == instance_wire(gate.right, arguments, base));
        assert(values[base + i] == callee_values[i]);
        assert forall|j: int| 0 <= j < count implies values[base + j] == #[trigger] callee_values[j] by {};
    }
}

/// 追加先で評価した各出力が、実引数を渡した呼び出し先の評価と一致することを示す。
pub(super) proof fn instance_preserves_outputs(
    before: Seq<NorGate>, callee: &NorNetlist, combined: Seq<NorGate>, arguments: Seq<Wire>, mapped: Seq<Wire>,
    inputs: Seq<bool>, values: Seq<bool>, callee_inputs: Seq<bool>, output: Seq<bool>,
)
    requires
        before.len() + callee.gates@.len() <= combined.len(),
        instance_gates_match(before, callee.gates@, arguments, combined.take((before.len() + callee.gates@.len()) as int)),
        instance_outputs_match(callee.outputs@, arguments, before.len() as usize, mapped),
        gate_values_match(inputs, combined, values), values.len() == combined.len() <= usize::MAX,
        instance_arguments_match(arguments, inputs, values, before.len(), callee_inputs),
        nor_evaluation(callee, callee_inputs, output),
    ensures output_values_match(inputs, values, mapped, output),
{
    reveal(nor_evaluation);
    let callee_values = choose|gates: Seq<bool>| #[trigger] gate_values_match(callee_inputs, callee.gates@, gates)
        && gates.len() == callee.gates@.len() && output_values_match(callee_inputs, gates, callee.outputs@, output);
    instance_gate_values_agree(before, callee.gates@, combined, arguments, inputs, values,
        callee_inputs, callee_values, callee_values.len());
    assert forall|i: int| 0 <= i < output.len() implies {
        &&& wire_available(#[trigger] mapped[i], inputs.len(), values.len())
        &&& (#[trigger] output[i]) == wire_value(mapped[i], inputs, values)
    } by {
        instance_wire_preserves_value(callee.outputs@[i], arguments, before.len() as usize,
            inputs, values, callee_inputs, callee_values);
    };
}

proof fn ordered_output_bit_offset(definitions: Seq<u64>, outputs: Seq<u64>, first: nat, count: nat)
    requires
        first + outputs.len() <= definitions.len(), count <= outputs.len(),
        forall|port: int| 0 <= port < outputs.len() ==> definitions[first + port] == #[trigger] outputs[port],
    ensures preceding_port_bits(definitions, (first + count) as nat)
        == preceding_port_bits(definitions, first) + preceding_port_bits(outputs, count),
    decreases count,
{
    reveal_with_fuel(preceding_port_bits, 1);
    if count > 0 {
        let previous = (count - 1) as nat;
        ordered_output_bit_offset(definitions, outputs, first, previous);
        let offset = (first + previous) as int;
        assert(definitions[offset] == outputs[previous as int]);
        assert(preceding_port_bits(definitions, (first + count) as nat)
            == preceding_port_bits(definitions, (first + previous) as nat) + definitions[offset]);
        assert(preceding_port_bits(outputs, count) == preceding_port_bits(outputs, previous) + outputs[previous as int]);
    }
}

/// 同じ幅が宣言順に並ぶ出力と左辺を、ポート内のビット順を保って対応付ける。
pub(super) proof fn call_output_range_matches(
    definitions: Seq<u64>, outputs: Seq<u64>, first: usize, port: usize,
    caller: PortBitLayout, callee: PortBitLayout, caller_limit: usize, callee_limit: usize,
)
    requires
        port_bit_layout_result(definitions, caller_limit, Ok(caller)),
        port_bit_layout_result(outputs, callee_limit, Ok(callee)),
        first + outputs.len() <= definitions.len(), port < outputs.len(),
        forall|i: int| 0 <= i < outputs.len() ==> definitions[first + i] == #[trigger] outputs[i],
    ensures ({
        let base = preceding_port_bits(definitions, first as nat);
        let dst = caller.ranges_model()[first + port];
        let src = callee.ranges_model()[port as int];
        &&& dst.start == base + src.start
        &&& dst.end == base + src.end
        &&& forall|bit: usize| bit < outputs[port as int]
            ==> (#[trigger] caller.bit_index_model((first + port) as usize, bit))
                == Some((base + src.start + bit) as usize)
    }),
{
    crate::netlist::port_bit_layout_size(definitions, caller_limit, &caller);
    port_bit_layout_port(definitions, caller_limit, caller, (first + port) as usize);
    port_bit_layout_port(outputs, callee_limit, callee, port);
    ordered_output_bit_offset(definitions, outputs, first as nat, port as nat);
    ordered_output_bit_offset(definitions, outputs, first as nat, (port + 1) as nat);
}

/// 一回の展開で得た全出力を、呼び出し元の連続した左辺へ並べる。
pub(super) fn append_instance_outputs(
    definitions: &mut Vec<Wire>, outputs: &mut Vec<Wire>, first: usize,
    Ghost(caller_widths): Ghost<Seq<u64>>, Ghost(callee_widths): Ghost<Seq<u64>>,
    Ghost(caller): Ghost<&PortBitLayout>, Ghost(callee): Ghost<&PortBitLayout>,
    Ghost(caller_limit): Ghost<usize>, Ghost(callee_limit): Ghost<usize>,
    Ghost(inputs): Ghost<nat>, Ghost(gates): Ghost<nat>,
)
    requires
        port_bit_layout_result(caller_widths, caller_limit, Ok(*caller)),
        port_bit_layout_result(callee_widths, callee_limit, Ok(*callee)),
        first + callee_widths.len() <= caller_widths.len(),
        old(definitions)@.len() == preceding_port_bits(caller_widths, first as nat),
        old(outputs)@.len() == callee.total_bits_model(),
        output_ports_available(old(definitions)@, inputs, gates, old(definitions)@.len() as int),
        output_ports_available(old(outputs)@, inputs, gates, old(outputs)@.len() as int),
        forall|i: int| 0 <= i < callee_widths.len() ==> caller_widths[first + i] == #[trigger] callee_widths[i],
    ensures
        final(definitions)@ == old(definitions)@ + old(outputs)@,
        final(outputs)@.len() == 0,
        final(definitions)@.len() == preceding_port_bits(caller_widths, (first + callee_widths.len()) as nat),
        output_ports_available(final(definitions)@, inputs, gates, final(definitions)@.len() as int),
        forall|port: int, bit: int| #![trigger final(definitions)@[caller.ranges_model()[first + port].start + bit]]
            0 <= port < callee_widths.len() && 0 <= bit < callee_widths[port] ==> {
            let dst = caller.ranges_model()[first + port];
            let src = callee.ranges_model()[port];
            final(definitions)@[dst.start + bit] == old(outputs)@[src.start + bit]
        },
{
    let ghost prior = definitions@;
    let ghost produced = outputs@;
    proof {
        crate::netlist::port_bit_layout_size(caller_widths, caller_limit, caller);
        crate::netlist::port_bit_layout_size(callee_widths, callee_limit, callee);
        ordered_output_bit_offset(caller_widths, callee_widths, first as nat, callee_widths.len());
        crate::netlist::preceding_port_bits_grow(caller_widths, (first + callee_widths.len()) as nat, caller_widths.len());
        assert(prior.len() + produced.len() <= caller.total_bits_model());
    }
    definitions.append(outputs);
    proof {
        assert forall|at: int| 0 <= at < definitions@.len()
            implies wire_available(#[trigger] definitions@[at], inputs, gates) by {
            if at < prior.len() { assert(definitions@[at] == prior[at]); }
            else { assert(definitions@[at] == produced[at - prior.len()]); }
        };
        assert forall|port: int, bit: int| #![trigger definitions@[caller.ranges_model()[first + port].start + bit]]
            0 <= port < callee_widths.len() && 0 <= bit < callee_widths[port]
            implies {
                let dst = caller.ranges_model()[first + port];
                let src = callee.ranges_model()[port];
                definitions@[dst.start + bit] == produced[src.start + bit]
            } by {
                let dst = caller.ranges_model()[first + port];
                let src = callee.ranges_model()[port];
                port_bit_layout_port(callee_widths, callee_limit, *callee, port as usize);
                call_output_range_matches(caller_widths, callee_widths, first, port as usize,
                    *caller, *callee, caller_limit, callee_limit);
                assert(dst.start == prior.len() + src.start);
            };
    }
}

} // verus!
