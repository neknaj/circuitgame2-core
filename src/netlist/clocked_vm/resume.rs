//! 確定済みの VM 状態から再開したときの観測と遷移の一致を証明する。

use super::checkpoint::{ClockedVmCheckpoint, same_ordered_netlist, same_ordered_storage_wiring};
use super::{ClockedVm, clocked_gate_updates, clocked_vm_trace, input_snapshot, laid_out, output_values_match, snapshot_segment};
use crate::netlist::{clocked_storage_pin_values, clocked_storage_steps_agree};
use vstd::prelude::*;

verus! {

impl ClockedVm {
    /// 現在の登録出力と指定した外部入力を使って、全出力ポートを宣言順に読んだことを表す。
    pub open spec fn current_observation_matches(&self, input: Seq<bool>, output: Seq<bool>) -> bool {
        &&& output.len() == self.netlist_model().outputs@.len()
        &&& exists|bits: Seq<bool>| #[trigger] self.augmented_input_matches(input, bits)
            && output_values_match(bits, self.gate_values_model(), self.netlist_model().outputs@, output)
    }

    /// 二つの VM で、順序付き配線、確定済みゲート値、全素子の登録出力と RAM 内容が等しいことを表す。
    pub open spec fn resume_state_matches(&self, other: &Self) -> bool {
        &&& self.external_count() == other.external_count()
        &&& same_ordered_netlist(&self.netlist_model(), &other.netlist_model())
        &&& self.gate_values_model() == other.gate_values_model()
        &&& self.storage_model().len() == other.storage_model().len()
        &&& forall|i: int| 0 <= i < self.storage_model().len() ==> {
            let first = #[trigger] self.storage_model()[i];
            let second = #[trigger] other.storage_model()[i];
            &&& same_ordered_storage_wiring(&first.wiring_model(), &second.wiring_model())
            &&& first.output_model() == second.output_model()
            &&& first.memory_model() == second.memory_model()
        }
    }

    /// 同じ状態と外部入力を観測した二つの公開出力は等しい。
    pub proof fn resumed_observations_agree(
        &self, other: &Self, input: Seq<bool>, first: Seq<bool>, second: Seq<bool>,
    )
        requires self.valid(), other.valid(), self.resume_state_matches(other),
            self.current_observation_matches(input, first),
            other.current_observation_matches(input, second),
        ensures first == second,
    {
        let a = choose|bits: Seq<bool>| #[trigger] self.augmented_input_matches(input, bits)
            && output_values_match(bits, self.gate_values_model(), self.netlist_model().outputs@, first);
        let b = choose|bits: Seq<bool>| #[trigger] other.augmented_input_matches(input, bits)
            && output_values_match(bits, other.gate_values_model(), other.netlist_model().outputs@, second);
        self.augmented_inputs_agree(other, input, a, b);
        assert(first =~= second);
    }

    proof fn augmented_inputs_agree(&self, other: &Self, input: Seq<bool>, first: Seq<bool>, second: Seq<bool>)
        requires self.valid(), other.valid(), self.resume_state_matches(other),
            self.augmented_input_matches(input, first), other.augmented_input_matches(input, second),
        ensures first == second,
    {
        reveal(ClockedVm::valid);
        reveal(ClockedVm::augmented_input_matches);
        reveal(laid_out);
        reveal(input_snapshot);
        let count = self.storage@.len();
        resume_snapshot_prefix_agrees(self, other, input, first, second, count);
        assert(first.take(first.len() as int) =~= first);
        assert(second.take(second.len() as int) =~= second);
    }

    /// 同じ確定済み状態から同じ入力を適用すると、次の全状態と公開出力も等しい。
    pub proof fn resumed_ticks_agree(
        &self, other: &Self, first_next: &Self, second_next: &Self,
        input: Seq<bool>, first_output: Seq<bool>, second_output: Seq<bool>,
    )
        requires self.resume_state_matches(other),
            first_next.tick_matches(self, input, first_output),
            second_next.tick_matches(other, input, second_output),
        ensures first_next.resume_state_matches(second_next), first_output == second_output,
    {
        let (first_before, first_after) = first_next.tick_snapshots(self, input, first_output);
        let (second_before, second_after) = second_next.tick_snapshots(other, input, second_output);
        self.augmented_inputs_agree(other, input, first_before, second_before);
        reveal(ClockedVm::same_layout);
        reveal(ClockedVm::valid);
        let first_gates = first_next.gate_values_model();
        let second_gates = second_next.gate_values_model();
        assert(first_gates =~= second_gates);
        assert forall|i: int| 0 <= i < first_next.storage_model().len() implies {
            let first = #[trigger] first_next.storage_model()[i];
            let second = #[trigger] second_next.storage_model()[i];
            &&& same_ordered_storage_wiring(&first.wiring_model(), &second.wiring_model())
            &&& first.output_model() == second.output_model()
            &&& first.memory_model() == second.memory_model()
        } by {
            let prior_a = &self.storage_model()[i];
            let prior_b = &other.storage_model()[i];
            assert(clocked_storage_pin_values(&prior_a.wiring_model(), first_before, self.gate_values_model())
                == clocked_storage_pin_values(&prior_b.wiring_model(), second_before, other.gate_values_model()));
            clocked_storage_steps_agree(prior_a, &first_next.storage_model()[i],
                prior_b, &second_next.storage_model()[i],
                first_before, self.gate_values_model(), second_before, other.gate_values_model());
        };
        assert(first_next.resume_state_matches(second_next));
        first_next.augmented_inputs_agree(second_next, input, first_after, second_after);
        assert(first_output =~= second_output);
    }
}

proof fn resume_snapshot_prefix_agrees(
    first: &ClockedVm, second: &ClockedVm, input: Seq<bool>, a: Seq<bool>, b: Seq<bool>, count: nat,
)
    requires first.valid(), second.valid(), first.resume_state_matches(second),
        first.augmented_input_matches(input, a), second.augmented_input_matches(input, b),
        count <= first.storage_model().len(),
    ensures first.starts@[count as int] == second.starts@[count as int],
        a.take(first.starts@[count as int] as int) == b.take(second.starts@[count as int] as int),
    decreases count,
{
    reveal(ClockedVm::valid);
    reveal(ClockedVm::augmented_input_matches);
    reveal(laid_out);
    reveal(input_snapshot);
    if count > 0 {
        let i = count - 1;
        resume_snapshot_prefix_agrees(first, second, input, a, b, i as nat);
        let old_end = first.starts@[i];
        let end = first.starts@[count as int];
        assert(first.storage@[i].output_model() == second.storage@[i].output_model());
        assert(snapshot_segment(a, first.starts@, i, first.storage@[i].output_model()));
        assert(snapshot_segment(b, second.starts@, i, second.storage@[i].output_model()));
        assert(end == second.starts@[count as int]);
        assert forall|j: int| 0 <= j < end implies (#[trigger] a[j]) == (#[trigger] b[j]) by {
            if j < old_end {
                assert(a.take(old_end as int)[j] == b.take(old_end as int)[j]);
            } else {
                assert(a.subrange(old_end as int, end as int)[j - old_end]
                    == b.subrange(old_end as int, end as int)[j - old_end]);
            }
        };
        assert(a.take(end as int) =~= b.take(end as int));
    }
}

impl ClockedVmCheckpoint {
    /// 同じ保存データに一致する二つの VM は、同じ配線と確定済み状態を持つ。
    pub proof fn restored_states_agree(&self, before: &ClockedVm, restored: &ClockedVm)
        requires self.layout_matches(before), self.state_matches(before),
            self.layout_matches(restored), self.state_matches(restored),
        ensures before.resume_state_matches(restored),
    {
        assert forall|i: int| 0 <= i < before.storage_model().len() implies {
            let a = #[trigger] before.storage_model()[i];
            let b = #[trigger] restored.storage_model()[i];
            &&& same_ordered_storage_wiring(&a.wiring_model(), &b.wiring_model())
            &&& a.output_model() == b.output_model()
            &&& a.memory_model() == b.memory_model()
        } by {
            let saved = self.storage@[i];
            assert(same_ordered_storage_wiring(&saved.wiring, &before.storage_model()[i].wiring_model()));
            assert(same_ordered_storage_wiring(&saved.wiring, &restored.storage_model()[i].wiring_model()));
            assert(saved.values_match(&before.storage_model()[i]));
            assert(saved.values_match(&restored.storage_model()[i]));
        };
    }
}

/// 初期観測と、その後に残りの入力を一つずつ適用した状態・公開出力の列。
pub open spec fn clocked_vm_resume_trace(
    last_input: Seq<bool>, inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
) -> bool {
    &&& states.len() == outputs.len() == inputs.len() + 1
    &&& states[0].valid()
    &&& states[0].current_observation_matches(last_input, outputs[0])
    &&& forall|i: int| 0 < i < states.len() ==>
        (#[trigger] states[i]).tick_matches(&states[i - 1], inputs[i - 1], outputs[i])
}

/// 再開履歴の最後に `step` で進めた1 tick を追加する。
pub proof fn clocked_vm_resume_trace_push_tick(
    last_input: Seq<bool>, inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    input: Seq<bool>, state: ClockedVm, output: Seq<bool>,
)
    requires clocked_vm_resume_trace(last_input, inputs, states, outputs),
        state.tick_matches(&states.last(), input, output),
    ensures clocked_vm_resume_trace(last_input, inputs.push(input), states.push(state), outputs.push(output)),
{
    assert forall|i: int| 0 < i < states.len() + 1 implies
        (#[trigger] states.push(state)[i]).tick_matches(&states.push(state)[i - 1],
            inputs.push(input)[i - 1], outputs.push(output)[i]) by {
        if i < states.len() { assert(states.push(state)[i] == states[i]); }
    };
}

/// reset から続けた履歴を、指定した確定 tick から始まる再開履歴として取り出す。
///
/// tick 0 の最後の入力は幅の合うゼロ列で、それ以降は直前に適用した入力である。
pub proof fn clocked_vm_trace_suffix(
    inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>, tick: int,
) -> (last_input: Seq<bool>)
    requires clocked_vm_trace(inputs, states, outputs), 0 <= tick < states.len(),
    ensures
        last_input == if tick == 0 {
            Seq::new(states[0].external_count() as nat, |_: int| false)
        } else {
            inputs[tick - 1]
        },
        clocked_vm_resume_trace(last_input, inputs.skip(tick), states.skip(tick), outputs.skip(tick)),
{
    let current = &states[tick];
    let output = outputs[tick];
    let last_input = if tick == 0 {
        let bits = current.reset_snapshot(output);
        let zeros = Seq::new(current.external_count() as nat, |_: int| false);
        assert(current.augmented_input_matches(zeros, bits));
        assert(current.current_observation_matches(zeros, output));
        zeros
    } else {
        assert(current.tick_matches(&states[tick - 1], inputs[tick - 1], output));
        let (_, bits) = current.tick_snapshots(&states[tick - 1], inputs[tick - 1], output);
        assert(current.current_observation_matches(inputs[tick - 1], output));
        inputs[tick - 1]
    };
    assert forall|i: int| 0 < i < states.skip(tick).len() implies
        (#[trigger] states.skip(tick)[i]).tick_matches(&states.skip(tick)[i - 1],
            inputs.skip(tick)[i - 1], outputs.skip(tick)[i]) by {
        assert(states.skip(tick)[i] == states[tick + i]);
    };
    last_input
}

proof fn clocked_vm_resume_tick_agrees(
    last_input: Seq<bool>, inputs: Seq<Seq<bool>>,
    first: Seq<ClockedVm>, first_outputs: Seq<Seq<bool>>,
    second: Seq<ClockedVm>, second_outputs: Seq<Seq<bool>>, tick: nat,
)
    requires clocked_vm_resume_trace(last_input, inputs, first, first_outputs),
        clocked_vm_resume_trace(last_input, inputs, second, second_outputs),
        first[0].resume_state_matches(&second[0]), tick < first.len(),
    ensures first[tick as int].resume_state_matches(&second[tick as int]),
        first_outputs[tick as int] == second_outputs[tick as int],
    decreases tick,
{
    if tick == 0 {
        first[0].resumed_observations_agree(&second[0], last_input, first_outputs[0], second_outputs[0]);
    } else {
        clocked_vm_resume_tick_agrees(last_input, inputs, first, first_outputs,
            second, second_outputs, (tick - 1) as nat);
        first[tick - 1].resumed_ticks_agree(&second[tick - 1], &first[tick as int], &second[tick as int],
            inputs[tick - 1], first_outputs[tick as int], second_outputs[tick as int]);
    }
}

/// 同じ確定状態から同じ残り入力で再開した履歴は、各 tick の全状態・公開出力が等しい。
pub proof fn clocked_vm_resume_trace_agrees(
    last_input: Seq<bool>, inputs: Seq<Seq<bool>>,
    first: Seq<ClockedVm>, first_outputs: Seq<Seq<bool>>,
    second: Seq<ClockedVm>, second_outputs: Seq<Seq<bool>>,
)
    requires clocked_vm_resume_trace(last_input, inputs, first, first_outputs),
        clocked_vm_resume_trace(last_input, inputs, second, second_outputs),
        first[0].resume_state_matches(&second[0]),
    ensures first_outputs == second_outputs,
        forall|i: int| 0 <= i < first.len() ==>
            (#[trigger] first[i]).resume_state_matches(&(#[trigger] second[i])),
{
    assert forall|i: int| 0 <= i < first.len() implies
        (#[trigger] first[i]).resume_state_matches(&(#[trigger] second[i])) by {
        clocked_vm_resume_tick_agrees(last_input, inputs, first, first_outputs, second, second_outputs, i as nat);
    };
    assert forall|i: int| 0 <= i < first_outputs.len() implies
        (#[trigger] first_outputs[i]) == (#[trigger] second_outputs[i]) by {
        clocked_vm_resume_tick_agrees(last_input, inputs, first, first_outputs, second, second_outputs, i as nat);
    };
    assert(first_outputs =~= second_outputs);
}

} // verus!
