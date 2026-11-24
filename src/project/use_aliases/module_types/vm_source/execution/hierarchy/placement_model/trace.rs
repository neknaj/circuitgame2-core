//! 子回路の状態と観測を、親 VM の有限実行から取り出す。

use super::{RoutineWiring, routine_reset_observation, routine_tick_observation, routine_vm_input_offsets,
    routine_storage_mapping, routine_placed, routines_pins_valid, routines_placed};
use crate::netlist::{ClockedStorageInputs, ClockedVm, NorNetlist, clocked_gate_updates, clocked_instance_inputs,
    clocked_instance_gate_updates_match, clocked_instance_outputs_match, clocked_mapped_storage_reads_match,
    clocked_stateful_arguments,
    clocked_storage_memory_width, clocked_storage_output_width, clocked_storage_pin_values,
    clocked_storage_value_transition, clocked_vm_trace, output_values_match, wire_value};
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

/// フレームに含まれるゲートと状態素子の数。
pub(in super::super) closed spec fn frame_state_lengths(frame: RoutineFrame) -> (nat, nat) {
    (frame.gates.len(), frame.devices.len())
}

/// 指定区間のゲート値と状態素子の値を、同じ順序で子の状態に対応付ける。
pub(in super::super) closed spec fn frame_state_slice(
    parent: RoutineFrame, child: RoutineFrame, gate: nat, gates: nat, device: nat, devices: nat,
) -> bool {
    &&& gate + gates <= parent.gates.len()
    &&& device + devices <= parent.devices.len()
    &&& child.gates == parent.gates.subrange(gate as int, gate as int + gates)
    &&& child.devices == parent.devices.subrange(device as int, device as int + devices)
}

/// 空の呼び出し経路は、開始モジュールの状態全体を指す。
pub(in super::super) proof fn frame_identity_slice(frame: RoutineFrame)
    ensures frame_state_slice(frame, frame, 0, frame_state_lengths(frame).0, 0, frame_state_lengths(frame).1),
{
    assert(frame.gates.subrange(0, frame.gates.len() as int) =~= frame.gates);
    assert(frame.devices.subrange(0, frame.devices.len() as int) =~= frame.devices);
}

spec fn vm_storage_values(vm: &ClockedVm) -> Seq<RoutineDeviceValues> {
    Seq::new(vm.storage_model().len(), |i: int| {
        let device = vm.storage_model()[i];
        RoutineDeviceValues { registered: device.output_model(), memory: device.memory_model() }
    })
}

/// 子の状態を、ルート VM が保持するゲート値、登録出力、RAM の記憶の区間に対応付ける。
pub(in super::super) closed spec fn vm_state_slice(
    vm: &ClockedVm, child: RoutineFrame, gate: nat, gates: nat, device: nat, devices: nat,
) -> bool {
    &&& gate + gates <= vm.gate_values_model().len()
    &&& device + devices <= vm.storage_model().len()
    &&& child.gates == vm.gate_values_model().subrange(gate as int, gate as int + gates)
    &&& child.devices == vm_storage_values(vm).subrange(device as int, device as int + devices)
}

/// 二段の配置を合成しても、各値の並びは親の元の部分列と一致する。
pub(in super::super) proof fn join_frame_state_slices(
    parent: RoutineFrame, child: RoutineFrame, leaf: RoutineFrame,
    first: (nat, nat, nat, nat), rest: (nat, nat, nat, nat),
)
    requires frame_state_slice(parent, child, first.0, first.1, first.2, first.3),
        frame_state_slice(child, leaf, rest.0, rest.1, rest.2, rest.3),
    ensures frame_state_slice(parent, leaf, first.0 + rest.0, rest.1, first.2 + rest.2, rest.3),
{
    let gate = first.0 as int + rest.0;
    let device = first.2 as int + rest.2;
    assert(leaf.gates =~= parent.gates.subrange(gate, gate + rest.1));
    assert(leaf.devices =~= parent.devices.subrange(device, device + rest.3));
}

/// 子の部分列から、ルート VM の元の部分列を直接参照できる。
pub(in super::super) proof fn join_vm_state_slices(
    parent: &ClockedVm, child: RoutineFrame, leaf: RoutineFrame,
    first: (nat, nat, nat, nat), rest: (nat, nat, nat, nat),
)
    requires vm_state_slice(parent, child, first.0, first.1, first.2, first.3),
        frame_state_slice(child, leaf, rest.0, rest.1, rest.2, rest.3),
    ensures vm_state_slice(parent, leaf, first.0 + rest.0, rest.1, first.2 + rest.2, rest.3),
{
    let whole = RoutineFrame { input: Seq::empty(), output: Seq::empty(),
        gates: parent.gate_values_model(), devices: vm_storage_values(parent) };
    join_frame_state_slices(whole, child, leaf, first, rest);
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

/// 即時の観測を含む各フレームの状態列は、回路と素子列の長さに従う。
pub(in super::super) proof fn trace_frame_lengths(
    callee: &NorNetlist, devices: Seq<ClockedStorageInputs>, external: nat,
    frames: Seq<RoutineFrame>, updates: Seq<Seq<bool>>, tick: int,
)
    requires routine_trace(callee, devices, external, frames, updates), 0 <= tick < frames.len(),
    ensures frame_state_lengths(frames[tick]) == (callee.gates@.len(), devices.len()),
{
    if tick > 0 {
        assert(frame_steps(callee, devices, external, frames[tick - 1], frames[tick], updates[tick - 1]));
    }
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
        result.0.len() == steps + 1, result.1.len() == steps,
        ({
            let routine = routines[call]->Some_0;
            &&& routine_trace(&routine.callee, routine.devices, routine.external.len(), result.0, result.1)
            &&& frame_observed_from(&states[0], routine, direct,
                Seq::new(states[0].external_count() as nat, |_: int| false), result.0[0])
            &&& forall|i: int| 0 < i <= steps ==> frame_observed_from(&states[i], routine, direct, inputs[i - 1],
                #[trigger] result.0[i])
            &&& forall|i: int| 0 <= i < steps ==> update_input_read_from(&states[i], routine, inputs[i],
                #[trigger] result.1[i])
            &&& forall|i: int| 0 <= i <= steps ==> vm_state_slice(&states[i], #[trigger] result.0[i],
                routine.gates.start as nat, routine.callee.gates@.len(),
                (direct + routine.storage.start) as nat, routine.devices.len())
        }),
    decreases steps,
{
    let root = states[0];
    let routine = routines[call]->Some_0;
    reveal(routines_placed);
    assert(routine_placed(routine, root.netlist_model().gates@, wiring.skip(direct as int), root.netlist_model().input_count));
    let external = routine.external.len();
    if steps == 0 {
        let (input, output) = routine_reset_observation(&root, outputs[0], wiring, routines, direct, first_state, call);
        let frame = state_at(&root, routine, direct, input, output);
        let zero = Seq::new(root.external_count() as nat, |_: int| false);
        let bits = root.reset_snapshot(outputs[0]);
        assert(frame_observed_from(&root, routine, direct, zero, frame));
        observed_vm_state_slice(&root, routine, direct, zero, frame);
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
        observed_vm_state_slice(&current, routine, direct, root_input, next);
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
        assert forall|j: int| 0 <= j <= steps implies vm_state_slice(&states[j], #[trigger] extended[j],
            routine.gates.start as nat, routine.callee.gates@.len(),
            (direct + routine.storage.start) as nat, routine.devices.len()) by {
            if j < i { assert(extended[j] == frames[j]); }
        };
        (extended, extended_updates)
    }
}

spec fn routine_arguments(routine: RoutineWiring) -> Seq<crate::netlist::Wire> {
    clocked_stateful_arguments(routine.external, routine.state_inputs.start,
        clocked_storage_output_width(routine.devices))
}

spec fn local_devices(routine: RoutineWiring, direct: usize, parent: Seq<RoutineDeviceValues>) -> Seq<RoutineDeviceValues> {
    parent.subrange(direct + routine.storage.start, direct + routine.storage.end)
}

spec fn local_frame(routine: RoutineWiring, direct: usize, parent: RoutineFrame) -> RoutineFrame {
    RoutineFrame {
        input: clocked_instance_inputs(routine_arguments(routine), parent.input, parent.gates),
        output: clocked_instance_inputs(routine.outputs, parent.input, parent.gates),
        gates: parent.gates.subrange(routine.gates.start as int, routine.gates.end as int),
        devices: local_devices(routine, direct, parent.devices),
    }
}

/// 子の各値が、同じ時点の親の状態と配線から得られることを表す。
pub(in super::super) closed spec fn nested_trace_projects(
    routine: RoutineWiring, direct: usize, frames: Seq<RoutineFrame>, updates: Seq<Seq<bool>>,
    child_frames: Seq<RoutineFrame>, child_updates: Seq<Seq<bool>>,
) -> bool {
    &&& child_frames == Seq::new(frames.len(), |i: int| local_frame(routine, direct, frames[i]))
    &&& child_updates == Seq::new(updates.len(), |i: int|
        clocked_instance_inputs(routine_arguments(routine), updates[i], frames[i].gates))
}

/// 一段のトレース射影から、その時点の状態の区間を取り出す。
pub(in super::super) proof fn nested_state_slice(
    routine: RoutineWiring, direct: usize, frames: Seq<RoutineFrame>, updates: Seq<Seq<bool>>,
    child_frames: Seq<RoutineFrame>, child_updates: Seq<Seq<bool>>, tick: int,
    gates: nat, devices: nat,
)
    requires
        nested_trace_projects(routine, direct, frames, updates, child_frames, child_updates),
        0 <= tick < frames.len(),
        routine.gates.start + routine.callee.gates@.len() == routine.gates.end <= gates,
        routine.storage.start + routine.devices.len() == routine.storage.end,
        direct + routine.storage.end <= devices,
        frame_state_lengths(frames[tick]) == (gates, devices),
    ensures frame_state_slice(frames[tick], child_frames[tick], routine.gates.start as nat, routine.callee.gates@.len(),
        (direct + routine.storage.start) as nat, routine.devices.len()),
{
}

/// 実 VM の観測から、同じ時点の状態が占める区間を取り出す。
pub(in super::super) proof fn observed_vm_state_slice(
    vm: &ClockedVm, routine: RoutineWiring, direct: usize, input: Seq<bool>, frame: RoutineFrame,
)
    requires
        frame_observed_from(vm, routine, direct, input, frame),
        routine.gates.start + routine.callee.gates@.len() == routine.gates.end <= vm.gate_values_model().len(),
        routine.storage.start + routine.devices.len() == routine.storage.end,
        direct + routine.storage.end <= vm.storage_model().len(),
    ensures vm_state_slice(vm, frame, routine.gates.start as nat, routine.callee.gates@.len(),
        (direct + routine.storage.start) as nat, routine.devices.len()),
{
    let storage = vm_storage_values(vm);
    let selected = storage.subrange(direct + routine.storage.start, direct + routine.storage.end);
    assert(selected =~= frame.devices);
}

/// 親の軌跡から子を取り出すために必要な配線と配置の条件。
pub(in super::super) open spec fn trace_projection_ready(
    netlist: &NorNetlist, external: usize, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int,
) -> bool {
    &&& routines_placed(routines, netlist.gates@, wiring.skip(direct as int), first_state, netlist.input_count)
    &&& routine_vm_input_offsets(routines, wiring, direct, external)
    &&& routines_pins_valid(routines, netlist.input_count, netlist.gates@.len())
    &&& 0 <= call < routines.len()
    &&& routines[call].is_some()
}

proof fn local_input_has_registered_outputs(
    netlist: &NorNetlist, external: usize, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int,
    input: Seq<bool>, gates: Seq<bool>, values: Seq<RoutineDeviceValues>,
)
    requires
        trace_projection_ready(netlist, external, wiring, routines, direct, first_state, call),
        registered_inputs(wiring, external as nat, input, values),
        input.len() == netlist.input_count,
    ensures
        ({
            let routine = routines[call]->Some_0;
            registered_inputs(routine.devices, routine.external.len(),
                clocked_instance_inputs(routine_arguments(routine), input, gates), local_devices(routine, direct, values))
        }),
{
    reveal(routines_placed);
    let routine = routines[call]->Some_0;
    let pins = routine_arguments(routine);
    let child = clocked_instance_inputs(pins, input, gates);
    let ext = routine.external.len() as int;
    let devices = local_devices(routine, direct, values);
    assert(routine_placed(routine, netlist.gates@, wiring.skip(direct as int), netlist.input_count));
    assert forall|i: int| 0 <= i < routine.devices.len() implies {
        let value = #[trigger] devices[i];
        let relative = clocked_storage_output_width(routine.devices.take(i)) as int;
        let start = ext + relative;
        let end = start + routine.devices[i].data@.len();
        &&& end <= child.len()
        &&& child.subrange(start, end) == value.registered
    } by {
        routine_storage_mapping(netlist, external, wiring, routines, direct, first_state, call, i);
        let parent = direct + routine.storage.start + i;
        let relative = clocked_storage_output_width(routine.devices.take(i)) as int;
        let width = routine.devices[i].data@.len();
        let start = ext + relative;
        let end = start + width;
        let parent_start = routine.state_inputs.start + relative;
        let row = child.subrange(start, end);
        let parent_row = input.subrange(parent_start, parent_start + width);
        assert(devices[i] == values[parent]);
        assert(parent_row == values[parent].registered);
        assert(row.len() == parent_row.len());
        assert forall|j: int| 0 <= j < row.len() implies (#[trigger] row[j]) == parent_row[j] by {
            assert(pins[start + j] == crate::netlist::Wire::Input((parent_start + j) as usize));
            assert(wire_value(pins[start + j], input, gates) == input[parent_start + j]);
        };
        assert(row =~= parent_row);
    };
}

proof fn local_frame_matches(
    netlist: &NorNetlist, external: usize, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int, frame: RoutineFrame,
)
    requires trace_projection_ready(netlist, external, wiring, routines, direct, first_state, call),
        frame_matches(netlist, wiring, external as nat, frame),
    ensures
        ({
            let routine = routines[call]->Some_0;
            frame_matches(&routine.callee, routine.devices, routine.external.len(), local_frame(routine, direct, frame))
        }),
{
    reveal(routines_placed);
    reveal(routines_pins_valid);
    let routine = routines[call]->Some_0;
    let child = local_frame(routine, direct, frame);
    vstd::std_specs::vec::axiom_spec_len(&netlist.gates);
    local_input_has_registered_outputs(netlist, external, wiring, routines, direct, first_state, call,
        frame.input, frame.gates, frame.devices);
    assert(output_values_match(frame.input, frame.gates, routine.outputs, child.output));
    clocked_instance_outputs_match(&routine.callee, routine_arguments(routine), routine.outputs, routine.gates.start,
        frame.input, frame.gates, child.output);
}

/// 親の有限トレースから子のトレースを導く。得られた列を次の子の親として使える。
pub(in super::super) proof fn project_nested_trace(
    netlist: &NorNetlist, external: usize, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int,
    frames: Seq<RoutineFrame>, updates: Seq<Seq<bool>>,
) -> (result: (Seq<RoutineFrame>, Seq<Seq<bool>>))
    requires
        trace_projection_ready(netlist, external, wiring, routines, direct, first_state, call),
        routine_trace(netlist, wiring, external as nat, frames, updates),
    ensures
        ({
            let routine = routines[call]->Some_0;
            &&& result.1.len() == updates.len()
            &&& result.0.len() == frames.len()
            &&& routine_trace(&routine.callee, routine.devices, routine.external.len(), result.0, result.1)
            &&& nested_trace_projects(routine, direct, frames, updates, result.0, result.1)
        }),
{
    reveal(routines_placed);
    reveal(routines_pins_valid);
    let routine = routines[call]->Some_0;
    let pins = routine_arguments(routine);
    let child_frames = Seq::new(frames.len(), |i: int| local_frame(routine, direct, frames[i]));
    let child_updates = Seq::new(updates.len(), |i: int| clocked_instance_inputs(pins, updates[i], frames[i].gates));
    vstd::std_specs::vec::axiom_spec_len(&netlist.gates);
    let initial = frames[0];
    let child_initial = child_frames[0];
    local_frame_matches(netlist, external, wiring, routines, direct, first_state, call, initial);
    assert(child_initial.gates =~= Seq::new(routine.callee.gates@.len(), |_: int| false));
    assert forall|j: int| 0 <= j < routine.devices.len() implies {
        let value = #[trigger] child_initial.devices[j];
        &&& value.registered == Seq::new(routine.devices[j].data@.len(), |_: int| false)
        &&& value.memory == match clocked_storage_memory_width(&routine.devices[j]) {
            Some(width) => Some(Seq::new(width, |_: int| false)),
            None => None,
        }
    } by {
        routine_storage_mapping(netlist, external, wiring, routines, direct, first_state, call, j);
        let parent = direct + routine.storage.start + j;
        assert(child_initial.devices[j] == initial.devices[parent]);
        assert(clocked_storage_memory_width(&routine.devices[j]) == clocked_storage_memory_width(&wiring[parent]));
    };
    assert(frame_is_reset(&routine.callee, routine.devices, routine.external.len(), child_initial));
    assert forall|i: int| 0 < i < child_frames.len() implies frame_steps(
        &routine.callee, routine.devices, routine.external.len(), child_frames[i - 1], #[trigger] child_frames[i],
        child_updates[i - 1],
    ) by {
        let previous = frames[i - 1];
        let next = frames[i];
        let update = updates[i - 1];
        let child_before = child_frames[i - 1];
        let child_after = child_frames[i];
        let child_update = child_updates[i - 1];
        assert(frame_steps(netlist, wiring, external as nat, previous, next, update));
        if i == 1 {
            assert(frame_matches(netlist, wiring, external as nat, previous));
        } else {
            assert(frame_steps(netlist, wiring, external as nat, frames[i - 2], previous, updates[i - 2]));
        }
        local_frame_matches(netlist, external, wiring, routines, direct, first_state, call, next);
        local_input_has_registered_outputs(netlist, external, wiring, routines, direct, first_state, call,
            update, previous.gates, previous.devices);
        clocked_instance_gate_updates_match(&routine.callee, netlist.gates@, pins, routine.gates.start,
            update, previous.gates, next.gates);
        assert forall|j: int| 0 <= j < routine.devices.len() implies {
            let before = child_before.devices[j];
            let after = #[trigger] child_after.devices[j];
            clocked_storage_value_transition(before.registered, before.memory, after.registered, after.memory,
                clocked_storage_pin_values(&routine.devices[j], child_update, child_before.gates))
        } by {
            routine_storage_mapping(netlist, external, wiring, routines, direct, first_state, call, j);
            let parent = direct + routine.storage.start + j;
            assert(child_before.devices[j] == previous.devices[parent]);
            assert(child_after.devices[j] == next.devices[parent]);
            clocked_mapped_storage_reads_match(routine.devices, j, &wiring[parent], pins, routine.gates.start,
                routine.callee.gates@.len() as usize, update, previous.gates);
        };
    };
    (child_frames, child_updates)
}

} // verus!
