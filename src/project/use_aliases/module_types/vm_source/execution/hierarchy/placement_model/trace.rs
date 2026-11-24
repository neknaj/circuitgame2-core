//! 子回路の状態と観測を、親 VM の有限実行から取り出す。

use super::{RoutineWiring, routine_reset_observation, routine_tick_observation, routine_vm_input_offsets,
    routines_pins_valid, routines_placed};
use crate::netlist::{ClockedStorageInputs, ClockedVm, NorNetlist, clocked_gate_updates, clocked_instance_inputs,
    clocked_stateful_arguments,
    clocked_storage_memory_width, clocked_storage_output_width, clocked_storage_pin_values,
    clocked_storage_value_transition, clocked_vm_trace, output_values_match};
use vstd::prelude::*;

verus! {

/// 素子の登録出力と、RAM の場合はアドレス順の記憶ビット。
pub(in super::super) struct RoutineDeviceValues {
    registered: Seq<bool>,
    memory: Option<Seq<bool>>,
}

/// 一つの子回路を観測したときの入力、状態、出力。
pub(in super::super) struct RoutineFrame {
    input: Seq<bool>,
    gates: Seq<bool>,
    devices: Seq<RoutineDeviceValues>,
    output: Seq<bool>,
}

spec fn registered_inputs(
    devices: Seq<ClockedStorageInputs>, external: nat, input: Seq<bool>, values: Seq<RoutineDeviceValues>,
) -> bool {
    &&& values.len() == devices.len()
    &&& input.len() == external + clocked_storage_output_width(devices)
    &&& forall|i: int| 0 <= i < devices.len() ==> {
        let value = #[trigger] values[i];
        let start = external as int + clocked_storage_output_width(devices.take(i));
        let end = start + devices[i].data@.len();
        &&& end <= input.len()
        &&& input.subrange(start, end) == value.registered
    }
}

spec fn frame_matches(
    callee: &NorNetlist, devices: Seq<ClockedStorageInputs>, external: nat, frame: RoutineFrame,
) -> bool {
    &&& frame.input.len() == callee.input_count
    &&& frame.gates.len() == callee.gates@.len()
    &&& registered_inputs(devices, external, frame.input, frame.devices)
    &&& frame.output.len() == callee.outputs@.len()
    &&& output_values_match(frame.input, frame.gates, callee.outputs@, frame.output)
}

spec fn frame_is_reset(callee: &NorNetlist, devices: Seq<ClockedStorageInputs>, external: nat, frame: RoutineFrame) -> bool {
    &&& frame_matches(callee, devices, external, frame)
    &&& frame.gates == Seq::new(callee.gates@.len(), |_: int| false)
    &&& forall|i: int| 0 <= i < devices.len() ==> {
        let value = #[trigger] frame.devices[i];
        &&& value.registered == Seq::new(devices[i].data@.len(), |_: int| false)
        &&& value.memory == match clocked_storage_memory_width(&devices[i]) {
            Some(width) => Some(Seq::new(width, |_: int| false)),
            None => None,
        }
    }
}

spec fn frame_steps(
    callee: &NorNetlist, devices: Seq<ClockedStorageInputs>, external: nat,
    previous: RoutineFrame, next: RoutineFrame, update_input: Seq<bool>,
) -> bool {
    &&& frame_matches(callee, devices, external, next)
    &&& update_input.len() == callee.input_count
    &&& registered_inputs(devices, external, update_input, previous.devices)
    &&& clocked_gate_updates(callee.gates@, update_input, previous.gates, next.gates)
    &&& forall|i: int| 0 <= i < devices.len() ==> {
        let before = previous.devices[i];
        let after = #[trigger] next.devices[i];
        clocked_storage_value_transition(before.registered, before.memory, after.registered, after.memory,
            clocked_storage_pin_values(&devices[i], update_input, previous.gates))
    }
}

/// 子の reset と各 tick の観測を表す。更新に使う入力は、更新後の観測用入力と別に渡す。
pub(in super::super) closed spec fn routine_trace(
    callee: &NorNetlist, devices: Seq<ClockedStorageInputs>, external: nat,
    frames: Seq<RoutineFrame>, update_inputs: Seq<Seq<bool>>,
) -> bool {
    &&& frames.len() == update_inputs.len() + 1
    &&& frame_is_reset(callee, devices, external, frames[0])
    &&& forall|i: int| 0 < i < frames.len() ==> frame_steps(callee, devices, external,
        frames[i - 1], #[trigger] frames[i], update_inputs[i - 1])
}

spec fn state_at(vm: &ClockedVm, routine: RoutineWiring, direct: usize, input: Seq<bool>, output: Seq<bool>) -> RoutineFrame {
    RoutineFrame {
        input,
        output,
        gates: vm.gate_values_model().subrange(routine.gates.start as int, routine.gates.end as int),
        devices: Seq::new(routine.devices.len(), |i: int| {
            let device = vm.storage_model()[direct + routine.storage.start + i];
            RoutineDeviceValues { registered: device.output_model(), memory: device.memory_model() }
        }),
    }
}

pub(in super::super) closed spec fn frame_observed_from(
    vm: &ClockedVm, routine: RoutineWiring, direct: usize, external: Seq<bool>, frame: RoutineFrame,
) -> bool {
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
        clocked_storage_output_width(routine.devices));
    &&& frame == state_at(vm, routine, direct, frame.input, frame.output)
    &&& exists|parent: Seq<bool>| #[trigger] vm.augmented_input_matches(external, parent)
        && frame.input == clocked_instance_inputs(pins, parent, vm.gate_values_model())
        && frame.output == clocked_instance_inputs(routine.outputs, parent, vm.gate_values_model())
}

pub(in super::super) closed spec fn update_input_read_from(
    vm: &ClockedVm, routine: RoutineWiring, external: Seq<bool>, input: Seq<bool>,
) -> bool {
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
        clocked_storage_output_width(routine.devices));
    exists|parent: Seq<bool>| #[trigger] vm.augmented_input_matches(external, parent)
        && input == clocked_instance_inputs(pins, parent, vm.gate_values_model())
}

/// 親 VM の reset と任意の有限入力列から、一つの呼び出しの状態と観測の列を得る。
pub(in super::super) proof fn project_routine_trace(
    inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int, steps: nat,
) -> (result: (Seq<RoutineFrame>, Seq<Seq<bool>>))
    requires
        clocked_vm_trace(inputs, states, outputs),
        steps <= inputs.len(),
        states[0].layout_matches(states[0].netlist_model(), states[0].external_count(), wiring),
        routines_placed(routines, states[0].netlist_model().gates@, wiring.skip(direct as int), first_state,
            states[0].netlist_model().input_count),
        routine_vm_input_offsets(routines, wiring, direct, states[0].external_count()),
        routines_pins_valid(routines, states[0].netlist_model().input_count, states[0].netlist_model().gates@.len()),
        0 <= call < routines.len(),
        routines[call].is_some(),
    ensures
        states[steps as int].layout_matches(states[0].netlist_model(), states[0].external_count(), wiring),
        result.1.len() == steps,
        ({
            let routine = routines[call]->Some_0;
            &&& routine_trace(&routine.callee, routine.devices, routine.external.len(), result.0, result.1)
            &&& frame_observed_from(&states[0], routine, direct,
                Seq::new(states[0].external_count() as nat, |_: int| false), result.0[0])
            &&& forall|i: int| 0 < i <= steps ==> frame_observed_from(&states[i], routine, direct, inputs[i - 1],
                #[trigger] result.0[i])
            &&& forall|i: int| 0 <= i < steps ==> update_input_read_from(&states[i], routine, inputs[i],
                #[trigger] result.1[i])
        }),
    decreases steps,
{
    let root = states[0];
    let routine = routines[call]->Some_0;
    let external = routine.external.len();
    if steps == 0 {
        let (input, output) = routine_reset_observation(&root, outputs[0], wiring, routines, direct, first_state, call);
        let frame = state_at(&root, routine, direct, input, output);
        let zero = Seq::new(root.external_count() as nat, |_: int| false);
        let bits = root.reset_snapshot(outputs[0]);
        assert(frame_observed_from(&root, routine, direct, zero, frame));
        assert(frame_is_reset(&routine.callee, routine.devices, external, frame)) by {
            assert forall|i: int| 0 <= i < routine.devices.len() implies {
                let stored = #[trigger] frame.devices[i];
                let device = root.storage_model()[direct + routine.storage.start + i];
                &&& stored.registered == device.output_model()
                &&& stored.memory == device.memory_model()
            } by {
                let parent = direct + routine.storage.start + i;
                assert(0 <= parent < root.storage_model().len());
                assert(root.storage_model()[parent].output_model().len() == routine.devices[i].data@.len());
            };
        };
        (seq![frame], Seq::empty())
    } else {
        let (frames, updates) = project_routine_trace(inputs, states, outputs, wiring, routines, direct, first_state, call,
            (steps - 1) as nat);
        let i = steps as int;
        let previous = states[i - 1];
        let current = states[i];
        let root_input = inputs[i - 1];
        assert(current.tick_matches(&previous, root_input, outputs[i]));
        let (old_input, observed_input, output) = routine_tick_observation(&current, &previous, root_input, outputs[i],
            wiring, routines, direct, first_state, call);
        current.tick_snapshots(&previous, root_input, outputs[i]);
        current.preserve_layout_evidence(&previous, root.netlist_model(), root.external_count(), wiring);
        let next = state_at(&current, routine, direct, observed_input, output);
        let before = frames.last();
        assert(before == state_at(&previous, routine, direct, before.input, before.output));
        assert(frame_steps(&routine.callee, routine.devices, external, before, next, old_input)) by {
            assert forall|j: int| #![trigger routine.devices[j]]
                0 <= j < routine.devices.len() implies {
                let parent = direct + routine.storage.start + j;
                let start = external as int + clocked_storage_output_width(routine.devices.take(j));
                let end = start + routine.devices[j].data@.len();
                &&& 0 <= parent < previous.storage_model().len()
                &&& parent < current.storage_model().len()
                &&& end <= old_input.len() && end <= observed_input.len()
                &&& old_input.subrange(start, end) == before.devices[j].registered
                &&& observed_input.subrange(start, end) == next.devices[j].registered
                &&& next.devices[j].registered == current.storage_model()[parent].output_model()
                &&& before.devices[j].registered == previous.storage_model()[parent].output_model()
                &&& clocked_storage_value_transition(before.devices[j].registered, before.devices[j].memory,
                    next.devices[j].registered, next.devices[j].memory,
                    clocked_storage_pin_values(&routine.devices[j], old_input, before.gates))
            } by {
                let parent = direct + routine.storage.start + j;
                assert(before.devices[j].memory == previous.storage_model()[parent].memory_model());
                assert(next.devices[j].memory == current.storage_model()[parent].memory_model());
            };
            assert(registered_inputs(routine.devices, external, old_input, before.devices));
            assert(registered_inputs(routine.devices, external, observed_input, next.devices));
            assert(frame_matches(&routine.callee, routine.devices, external, next));
        };
        assert(frame_observed_from(&current, routine, direct, root_input, next));
        assert(update_input_read_from(&previous, routine, root_input, old_input));
        let extended = frames.push(next);
        let extended_updates = updates.push(old_input);
        assert forall|j: int| 0 < j < extended.len() implies frame_steps(&routine.callee, routine.devices, external,
            extended[j - 1], #[trigger] extended[j], extended_updates[j - 1]) by {
            if j < i {
                assert(extended[j] == frames[j]);
                assert(extended[j - 1] == frames[j - 1]);
            } else {
                assert(extended[j - 1] == before);
            }
        };
        assert forall|j: int| 0 < j <= steps implies frame_observed_from(&states[j], routine, direct, inputs[j - 1],
            #[trigger] extended[j]) by {
            if j < i { assert(extended[j] == frames[j]); }
        };
        assert forall|j: int| 0 <= j < steps implies update_input_read_from(&states[j], routine, inputs[j],
            #[trigger] extended_updates[j]) by {
            if j < i - 1 { assert(extended_updates[j] == updates[j]); }
        };
        (extended, extended_updates)
    }
}

} // verus!
