//! 回路全体に予約した番号を使い、順序回路のインスタンスの配線を接続する。

use super::{ClockedNor, Wire, wire_within};
use crate::netlist::{NorGate, instances::instantiate_wire};
#[cfg(verus_only)]
use super::{NorNetlist, TickFrame, clocked_gate_updates, clocked_wiring_valid, gate_prefix_valid, tick_matches};
#[cfg(verus_only)]
use crate::netlist::{instances::{instance_gates_at, instance_gates_match, instance_outputs_match, instance_wire},
    output_values_match, wire_available, wire_value};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 子回路のゲートを追加する前に見つかった組み立て上の違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedInstanceError {
    /// 実引数のビット数が子回路の入力数と異なる。
    InputCount,
    /// 追加後のゲート数が、親回路全体で予約した件数を超える。
    GateCapacity,
    /// 最初に見つかった、親回路の範囲外を指す実引数の添字。
    Argument(usize),
}

spec fn arguments_valid(arguments: Seq<Wire>, inputs: usize, planned: usize, end: int) -> bool {
    &&& 0 <= end <= arguments.len()
    &&& forall|i: int| 0 <= i < end ==> wire_available(#[trigger] arguments[i], inputs as nat, planned as nat)
}

/// 追加前のゲート列、実引数、予約件数から、接続結果と最初の診断を定める。
pub closed spec fn clocked_instance_result(
    callee: &NorNetlist, before: Seq<NorGate>, arguments: Seq<Wire>, inputs: usize, planned: usize,
    after: Seq<NorGate>, result: Result<Vec<Wire>, ClockedInstanceError>,
) -> bool {
    let total = before.len() + callee.gates@.len();
    match result {
        Err(error) => after == before && match error {
            ClockedInstanceError::InputCount => arguments.len() != callee.input_count,
            ClockedInstanceError::GateCapacity => arguments.len() == callee.input_count && total > planned,
            ClockedInstanceError::Argument(at) => arguments.len() == callee.input_count && total <= planned
                && at < arguments.len() && arguments_valid(arguments, inputs, planned, at as int)
                && !wire_available(arguments[at as int], inputs as nat, planned as nat),
        },
        Ok(outputs) =>
            arguments.len() == callee.input_count && total <= planned
                && arguments_valid(arguments, inputs, planned, arguments.len() as int)
                && instance_gates_match(before, callee.gates@, arguments, after)
                && instance_outputs_match(callee.outputs@, arguments, before.len() as usize, outputs@)
                && (forall|i: int| before.len() <= i < after.len() ==> {
                    let gate = #[trigger] after[i];
                    wire_available(gate.left, inputs as nat, planned as nat)
                        && wire_available(gate.right, inputs as nat, planned as nat)
                })
                && (forall|i: int| 0 <= i < outputs@.len() ==>
                    wire_available(#[trigger] outputs@[i], inputs as nat, planned as nat)),
    }
}

proof fn mapped_wire_available(
    wire: Wire, arguments: Seq<Wire>, base: usize, inputs: usize, planned: usize, callee_gates: nat,
)
    requires wire_available(wire, arguments.len(), callee_gates), base + callee_gates <= planned,
        arguments_valid(arguments, inputs, planned, arguments.len() as int),
    ensures wire_available(instance_wire(wire, arguments, base), inputs as nat, planned as nat),
{
    if let Wire::Input(i) = wire {
        assert(wire_available(arguments[i as int], inputs as nat, planned as nat));
    }
}

impl ClockedNor {
    /// 子回路の全ゲートを順に追加し、親回路での出力配線を宣言順に返す。
    ///
    /// `inputs` は親回路の入力ビット数、`planned` は親回路全体の最終ゲート数。
    /// 実引数には後から追加するゲートの出力も指定できる。各ゲートは tick ごとに1回更新する。
    /// 全ゲートを追加した後、[`Self::check`] で親回路全体の配線を検査する。
    ///
    /// # Errors
    ///
    /// 実引数のビット数、追加後のゲート件数、各実引数の参照先の順に検査する。
    /// 違反があれば、親回路のゲート列を変更せずに診断を返す。
    pub fn append_instance(
        &self, caller: &mut Vec<NorGate>, arguments: &[Wire], inputs: usize, planned: usize,
    ) -> (result: Result<Vec<Wire>, ClockedInstanceError>)
        ensures
            clocked_instance_result(&self.netlist_model(), old(caller)@, arguments@, inputs, planned, final(caller)@, result),
            result.is_err() ==> final(caller)@ == old(caller)@,
            result matches Ok(outputs) ==> {
                let base = old(caller)@.len() as usize;
                &&& final(caller)@.len() == base + self.netlist_model().gates@.len() <= planned
                &&& final(caller)@.take(base as int) == old(caller)@
                &&& instance_gates_at(self.netlist_model().gates@, arguments@, base, final(caller)@)
                &&& instance_outputs_match(self.netlist_model().outputs@, arguments@, base, outputs@)
                &&& forall|i: int| base <= i < final(caller)@.len() ==> {
                    let gate = #[trigger] final(caller)@[i];
                    wire_available(gate.left, inputs as nat, planned as nat)
                        && wire_available(gate.right, inputs as nat, planned as nat)
                }
                &&& forall|i: int| 0 <= i < outputs@.len() ==>
                    wire_available(#[trigger] outputs@[i], inputs as nat, planned as nat)
            },
    {
        proof { use_type_invariant(self); }
        let callee = &self.netlist;
        let base = caller.len();
        let count = callee.gates.len();
        let ghost before = caller@;
        if arguments.len() != callee.input_count { return Err(ClockedInstanceError::InputCount); }
        if base > planned || count > planned - base { return Err(ClockedInstanceError::GateCapacity); }
        let mut i = 0;
        while i < arguments.len()
            invariant
                caller@ == before, base == before.len(),
                count == callee.gates@.len(), base + count <= planned,
                arguments@.len() == callee.input_count, *callee == self.netlist_model(),
                arguments_valid(arguments@, inputs, planned, i as int),
            decreases arguments@.len() - i,
        {
            if !wire_within(arguments[i], inputs, planned) {
                assert(clocked_instance_result(callee, before, arguments@, inputs, planned, caller@,
                    Err(ClockedInstanceError::Argument(i))));
                return Err(ClockedInstanceError::Argument(i));
            }
            i += 1;
        }
        let mut i = 0;
        assert(caller@.take(base as int) =~= before);
        while i < count
            invariant
                base == before.len(), count == callee.gates@.len(), base + count <= planned,
                arguments@.len() == callee.input_count, i <= count,
                clocked_wiring_valid(callee), arguments_valid(arguments@, inputs, planned, arguments@.len() as int),
                instance_gates_match(before, callee.gates@.take(i as int), arguments@, caller@),
                forall|j: int| base <= j < caller@.len() ==> {
                    let gate = #[trigger] caller@[j];
                    wire_available(gate.left, inputs as nat, planned as nat)
                        && wire_available(gate.right, inputs as nat, planned as nat)
                },
            decreases count - i,
        {
            let gate = callee.gates[i];
            proof { assert(gate_prefix_valid(callee, count as int)); }
            let left = instantiate_wire(gate.left, arguments, base);
            let right = instantiate_wire(gate.right, arguments, base);
            proof {
                mapped_wire_available(gate.left, arguments@, base, inputs, planned, count as nat);
                mapped_wire_available(gate.right, arguments@, base, inputs, planned, count as nat);
            }
            let ghost prior = caller@;
            caller.push(NorGate { left, right });
            assert(caller@.take(base as int) =~= before);
            assert forall|j: int| 0 <= j < i + 1 implies {
                let saved = #[trigger] caller@[base + j];
                let original = callee.gates@.take(i + 1)[j];
                &&& saved.left == instance_wire(original.left, arguments@, base)
                &&& saved.right == instance_wire(original.right, arguments@, base)
                &&& wire_available(saved.left, inputs as nat, planned as nat)
                &&& wire_available(saved.right, inputs as nat, planned as nat)
            } by {
                if j < i {
                    assert(caller@[base + j] == prior[base + j]);
                    assert(callee.gates@.take(i as int)[j] == callee.gates@[j]);
                }
            };
            i += 1;
        }
        assert(callee.gates@.take(count as int) =~= callee.gates@);
        let mut outputs = Vec::with_capacity(callee.outputs.len());
        let mut i = 0;
        while i < callee.outputs.len()
            invariant
                base == before.len(), count == callee.gates@.len(), base + count <= planned,
                arguments@.len() == callee.input_count, i == outputs@.len() <= callee.outputs@.len(),
                clocked_wiring_valid(callee), arguments_valid(arguments@, inputs, planned, arguments@.len() as int),
                instance_outputs_match(callee.outputs@.take(i as int), arguments@, base, outputs@),
                forall|j: int| 0 <= j < i ==> wire_available(#[trigger] outputs@[j], inputs as nat, planned as nat),
            decreases callee.outputs@.len() - i,
        {
            let output = callee.outputs[i];
            let wire = instantiate_wire(output, arguments, base);
            proof { mapped_wire_available(output, arguments@, base, inputs, planned, count as nat); }
            let ghost prior = outputs@;
            outputs.push(wire);
            assert forall|j: int| 0 <= j < outputs@.len() implies {
                let mapped = #[trigger] outputs@[j];
                mapped == instance_wire(callee.outputs@.take(i + 1)[j], arguments@, base)
                    && wire_available(mapped, inputs as nat, planned as nat)
            } by {
                if j < i {
                    assert(outputs@[j] == prior[j]);
                    assert(callee.outputs@.take(i as int)[j] == callee.outputs@[j]);
                }
            };
            i += 1;
        }
        assert(callee.outputs@.take(i as int) =~= callee.outputs@);
        Ok(outputs)
    }
}

/// 指定した親回路の状態で、子回路の入力に接続した配線の値を読む。
pub open spec fn clocked_instance_inputs(arguments: Seq<Wire>, input: Seq<bool>, state: Seq<bool>) -> Seq<bool> {
    Seq::new(arguments.len(), |i: int| wire_value(arguments[i], input, state))
}

proof fn mapped_wire_value(
    wire: Wire, arguments: Seq<Wire>, base: usize, count: nat, input: Seq<bool>, state: Seq<bool>,
)
    requires base + count <= state.len() <= usize::MAX, wire_available(wire, arguments.len(), count),
        forall|i: int| 0 <= i < arguments.len() ==> wire_available(#[trigger] arguments[i], input.len(), state.len()),
    ensures wire_value(instance_wire(wire, arguments, base), input, state)
        == wire_value(wire, clocked_instance_inputs(arguments, input, state), state[base as int..base + count]),
{
}

/// 親回路の1 tick が、子回路の各ゲートを同じ開始状態から1回更新することを示す。
pub proof fn clocked_instance_steps_match(
    callee: &NorNetlist, parent: &NorNetlist, arguments: Seq<Wire>, base: usize,
    input: Seq<bool>, previous: Seq<bool>, frame: TickFrame,
)
    requires
        clocked_wiring_valid(callee), tick_matches(parent, previous, input, frame),
        callee.input_count == arguments.len(),
        instance_gates_at(callee.gates@, arguments, base, parent.gates@),
        forall|i: int| 0 <= i < arguments.len() ==> wire_available(#[trigger] arguments[i], input.len(), previous.len()),
    ensures
        clocked_gate_updates(callee.gates@, clocked_instance_inputs(arguments, input, previous),
            previous[base as int..base + callee.gates@.len()],
            frame.gates@[base as int..base + callee.gates@.len()]),
{
    let count = callee.gates@.len();
    vstd::std_specs::vec::axiom_spec_len(&parent.gates);
    let local_before = previous[base as int..base + count];
    let local_after = frame.gates@[base as int..base + count];
    let inputs = clocked_instance_inputs(arguments, input, previous);
    assert forall|i: int| 0 <= i < local_after.len() implies {
        let gate = callee.gates@[i];
        (#[trigger] local_after[i]) == !(wire_value(gate.left, inputs, local_before)
            || wire_value(gate.right, inputs, local_before))
    } by {
        let gate = callee.gates@[i];
        let mapped = parent.gates@[base + i];
        assert(mapped.left == instance_wire(gate.left, arguments, base));
        assert(mapped.right == instance_wire(gate.right, arguments, base));
        mapped_wire_value(gate.left, arguments, base, count, input, previous);
        mapped_wire_value(gate.right, arguments, base, count, input, previous);
        assert(local_after[i] == frame.gates@[base + i]);
    };
}

/// 観測対象の親回路の状態から、子回路の出力配線も同じ値を読むことを示す。
///
/// tick 後の観測では確定済みの状態を渡す。子の出力が実引数に直結している場合も、その値を使う。
pub proof fn clocked_instance_outputs_match(
    callee: &NorNetlist, arguments: Seq<Wire>, mapped: Seq<Wire>, base: usize,
    input: Seq<bool>, state: Seq<bool>, values: Seq<bool>,
)
    requires
        clocked_wiring_valid(callee), callee.input_count == arguments.len(),
        base + callee.gates@.len() <= state.len() <= usize::MAX,
        instance_outputs_match(callee.outputs@, arguments, base, mapped), values.len() == mapped.len(),
        output_values_match(input, state, mapped, values),
        forall|i: int| 0 <= i < arguments.len() ==> wire_available(#[trigger] arguments[i], input.len(), state.len()),
    ensures output_values_match(clocked_instance_inputs(arguments, input, state),
        state[base as int..base + callee.gates@.len()], callee.outputs@, values),
{
    let count = callee.gates@.len();
    let inputs = clocked_instance_inputs(arguments, input, state);
    let local = state[base as int..base + count];
    assert forall|i: int| 0 <= i < values.len() implies
        (#[trigger] values[i]) == wire_value(callee.outputs@[i], inputs, local) by {
        let output = callee.outputs@[i];
        assert(mapped[i] == instance_wire(output, arguments, base));
        mapped_wire_value(output, arguments, base, count, input, state);
    };
}

} // verus!
