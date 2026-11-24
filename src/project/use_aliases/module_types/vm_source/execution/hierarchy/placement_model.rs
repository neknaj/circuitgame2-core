//! 各呼び出しが占める区間と、親回路に移した実際の配線を対応付ける。

#[cfg(verus_only)]
pub(super) mod trace;

use crate::netlist::{ClockedStorageInputs, NorNetlist, PortBitLayout, Wire};
#[cfg(verus_only)]
use crate::netlist::{ClockedVm, NorGate, clocked_gate_updates, clocked_instance_gate_updates_match,
    clocked_instance_inputs, clocked_instance_outputs_match, clocked_mapped_storage_reads_match,
    clocked_stateful_arguments, clocked_storage_memory_width, clocked_storage_output_width, clocked_storage_pin_values,
    clocked_storage_pins_valid, clocked_storage_value_transition, output_ports_available, output_values_match,
    clocked_storage_width_concat, clocked_storage_widths_agree, instance_gates_at, wire_value,
    instance_gates_in_extension, instance_outputs_match, clocked_wiring_valid, wire_available};
use core::ops::Range;
use alloc::vec::Vec;
use crate::project::ClockedWireDriver;
use vstd::prelude::*;

verus! {

/// 子のポートと、親回路におけるゲート・状態出力・状態素子の配置。
pub(super) struct RoutineWiring {
    pub inputs: PortBitLayout,
    pub layout: PortBitLayout,
    pub outputs: Seq<Wire>,
    pub callee: NorNetlist,
    pub devices: Seq<ClockedStorageInputs>,
    pub external: Seq<Wire>,
    pub argument_rows: Vec<Vec<ClockedWireDriver>>,
    pub gates: Range<usize>,
    pub state_inputs: Range<usize>,
    pub storage: Range<usize>,
}

pub(super) open spec fn routine_placed(
    routine: RoutineWiring, gates: Seq<NorGate>, storage: Seq<ClockedStorageInputs>, inputs: usize,
) -> bool {
    let width = clocked_storage_output_width(routine.devices);
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start, width);
    &&& routine.external.len() + width == routine.callee.input_count
    &&& routine.state_inputs.start + width == routine.state_inputs.end <= inputs
    &&& routine.gates.start + routine.callee.gates@.len() == routine.gates.end <= gates.len()
    &&& routine.storage.start + routine.devices.len() == routine.storage.end <= storage.len()
    &&& instance_outputs_match(routine.callee.outputs@, pins, routine.gates.start, routine.outputs)
    &&& instance_gates_at(routine.callee.gates@, pins, routine.gates.start, gates)
    &&& forall|i: int| 0 <= i < routine.devices.len() ==> routine.devices[i].parent_placement_matches(
        pins, routine.gates.start, &(#[trigger] storage[routine.storage.start + i]))
}

/// 子の端子と実引数は、親回路全体の配置が終わった時点で有効な配線を参照する。
pub(super) open spec fn routine_pins_valid(routine: RoutineWiring, inputs: usize, gates: nat) -> bool {
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
        clocked_storage_output_width(routine.devices));
    &&& clocked_wiring_valid(&routine.callee)
    &&& clocked_storage_pins_valid(routine.devices, routine.callee.input_count, routine.callee.gates@.len() as usize)
    &&& output_ports_available(routine.outputs, inputs as nat, gates, routine.outputs.len() as int)
    &&& forall|i: int| 0 <= i < pins.len() ==> wire_available(#[trigger] pins[i], inputs as nat, gates)
}

#[verifier::opaque]
pub(super) closed spec fn routines_pins_valid(routines: Seq<Option<RoutineWiring>>, inputs: usize, gates: nat) -> bool {
    forall|i: int| 0 <= i < routines.len() ==> ((#[trigger] routines[i]) matches Some(routine)
        ==> routine_pins_valid(routine, inputs, gates))
}

/// 子に渡す実引数の端子は、親の増補入力列とゲート列の範囲内にある。
pub(super) proof fn routine_external_pin_bounds(
    routines: Seq<Option<RoutineWiring>>, inputs: usize, gates: nat, call: int,
)
    requires routines_pins_valid(routines, inputs, gates), 0 <= call < routines.len(), routines[call].is_some(),
    ensures ({
        let external = routines[call]->Some_0.external;
        output_ports_available(external, inputs as nat, gates, external.len() as int)
    }),
{
    reveal(routines_pins_valid);
    let routine = routines[call]->Some_0;
    let args = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
        clocked_storage_output_width(routine.devices));
    assert forall|i: int| 0 <= i < routine.external.len() implies
        wire_available(#[trigger] routine.external[i], inputs as nat, gates) by {
        assert(routine.external[i] == args[i]);
    };
}

pub(super) proof fn empty_routine_pins(inputs: usize, gates: nat)
    ensures routines_pins_valid(Seq::empty(), inputs, gates),
{
    reveal(routines_pins_valid);
}

pub(super) proof fn extend_routine_pins(
    routines: Seq<Option<RoutineWiring>>, added: Option<RoutineWiring>, inputs: usize, gates: nat,
)
    requires routines_pins_valid(routines, inputs, gates),
        added matches Some(routine) ==> routine_pins_valid(routine, inputs, gates),
    ensures routines_pins_valid(routines.push(added), inputs, gates),
{
    reveal(routines_pins_valid);
    let next = routines.push(added);
    assert forall|i: int| 0 <= i < next.len() implies ((#[trigger] next[i]) matches Some(routine)
        ==> routine_pins_valid(routine, inputs, gates)) by {
        if i < routines.len() { assert(next[i] == routines[i]); }
        else { assert(next[i] == added); }
    };
}

pub(super) open spec fn routine_before(first: RoutineWiring, second: RoutineWiring) -> bool {
    &&& first.gates.end <= second.gates.start
    &&& first.state_inputs.end <= second.state_inputs.start
    &&& first.storage.end <= second.storage.start
}

/// 各呼び出しが、それ以前の呼び出しとは重ならない区間を占める。
#[verifier::opaque]
pub(super) closed spec fn routines_placed(
    routines: Seq<Option<RoutineWiring>>, gates: Seq<NorGate>, storage: Seq<ClockedStorageInputs>,
    first_state: usize, next_state: usize,
) -> bool {
    &&& first_state <= next_state
    &&& first_state + clocked_storage_output_width(storage) == next_state
    &&& forall|i: int| 0 <= i < routines.len() ==> ((#[trigger] routines[i]) matches Some(routine)
        ==> first_state <= routine.state_inputs.start
            && routine.state_inputs.start == first_state + clocked_storage_output_width(storage.take(routine.storage.start as int))
            && routine_placed(routine, gates, storage, next_state))
    &&& forall|i: int, j: int| 0 <= i < j < routines.len() ==>
        ((#[trigger] routines[i], #[trigger] routines[j]) matches (Some(first), Some(second))
            ==> routine_before(first, second))
}

/// 出力を連結した子回路列が占める増補入力の幅。
pub(super) proof fn routines_output_width(
    routines: Seq<Option<RoutineWiring>>, gates: Seq<NorGate>, storage: Seq<ClockedStorageInputs>,
    first_state: usize, next_state: usize,
)
    requires routines_placed(routines, gates, storage, first_state, next_state),
    ensures first_state + clocked_storage_output_width(storage) == next_state,
{
    reveal(routines_placed);
}

/// 呼び出し列全体の配置から、指定した子の配線と区間を取り出す。
pub(super) proof fn placed_routine_evidence(
    routines: Seq<Option<RoutineWiring>>, gates: Seq<NorGate>, storage: Seq<ClockedStorageInputs>,
    first_state: usize, next_state: usize, call: int,
)
    requires routines_placed(routines, gates, storage, first_state, next_state),
        0 <= call < routines.len(), routines[call].is_some(),
    ensures routine_placed(routines[call]->Some_0, gates, storage, next_state),
{
    reveal(routines_placed);
}

/// 同じ親が順に呼ぶ二つの子は、ゲートと状態素子の配置を共有しない。
pub(super) proof fn sibling_routines_order(
    routines: Seq<Option<RoutineWiring>>, gates: Seq<NorGate>, storage: Seq<ClockedStorageInputs>,
    first_state: usize, next_state: usize, first: int, second: int,
)
    requires routines_placed(routines, gates, storage, first_state, next_state),
        0 <= first < second < routines.len(), routines[first].is_some(), routines[second].is_some(),
    ensures routine_before(routines[first]->Some_0, routines[second]->Some_0),
{
    reveal(routines_placed);
}

/// 空の子回路列には予約済みの区間がない。
pub(super) proof fn empty_routines(first_state: usize)
    ensures routines_placed(Seq::empty(), Seq::empty(), Seq::empty(), first_state, first_state),
{
    reveal(routines_placed);
    clocked_storage_width_concat(Seq::empty(), Seq::empty());
    assert(Seq::<ClockedStorageInputs>::empty() + Seq::empty() =~= Seq::empty());
}

/// 後続の呼び出しを足しても、それまでの区間と配線は保たれる。
pub(super) proof fn extend_routines(
    prior: Seq<Option<RoutineWiring>>, new: Option<RoutineWiring>,
    before_gates: Seq<NorGate>, after_gates: Seq<NorGate>,
    before_storage: Seq<ClockedStorageInputs>, after_storage: Seq<ClockedStorageInputs>,
    first_state: usize, before_state: usize, after_state: usize,
)
    requires
        routines_placed(prior, before_gates, before_storage, first_state, before_state),
        before_gates.len() <= after_gates.len(), before_storage.len() <= after_storage.len(),
        after_gates.take(before_gates.len() as int) == before_gates,
        after_storage.take(before_storage.len() as int) == before_storage,
        before_state <= after_state,
        new.is_none() ==> before_state == after_state && before_storage == after_storage,
        new matches Some(routine) ==> {
            &&& routine_placed(routine, after_gates, after_storage, after_state)
            &&& routine.gates.start == before_gates.len()
            &&& routine.storage.start == before_storage.len()
            &&& routine.state_inputs.start == before_state
            &&& routine.storage.end == after_storage.len()
            &&& routine.state_inputs.end == after_state
        },
    ensures routines_placed(prior.push(new), after_gates, after_storage, first_state, after_state),
{
    reveal(routines_placed);
    if let Some(routine) = new {
        let local = after_storage.skip(before_storage.len() as int);
        assert(local.len() == routine.devices.len());
        assert forall|i: int| 0 <= i < local.len() implies
            (#[trigger] local[i]).data@.len() == (#[trigger] routine.devices[i]).data@.len() by {
            let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
                clocked_storage_output_width(routine.devices));
            assert(local[i] == after_storage[routine.storage.start + i]);
            assert(routine.devices[i].parent_placement_matches(pins, routine.gates.start, &local[i]));
        };
        clocked_storage_widths_agree(local, routine.devices);
        clocked_storage_width_concat(before_storage, local);
        assert(after_storage =~= before_storage + local);
    }
    let following = prior.push(new);
    assert forall|i: int| 0 <= i < following.len() implies ((#[trigger] following[i]) matches Some(routine)
        ==> first_state <= routine.state_inputs.start
            && routine.state_inputs.start == first_state + clocked_storage_output_width(after_storage.take(routine.storage.start as int))
            && routine_placed(routine, after_gates, after_storage, after_state)) by {
        if i < prior.len() {
            assert(following[i] == prior[i]);
            if let Some(routine) = prior[i] {
                let width = clocked_storage_output_width(routine.devices);
                let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start, width);
                assert(routine_placed(routine, before_gates, before_storage, before_state));
                assert(after_storage.take(routine.storage.start as int) =~= before_storage.take(routine.storage.start as int));
                instance_gates_in_extension(routine.callee.gates@, pins, routine.gates.start, before_gates, after_gates);
                assert forall|j: int| 0 <= j < routine.devices.len() implies routine.devices[j].parent_placement_matches(
                    pins, routine.gates.start, &(#[trigger] after_storage[routine.storage.start + j])) by {
                    assert(after_storage[routine.storage.start + j] == before_storage[routine.storage.start + j]);
                };
            }
        } else {
            assert(following[i] == new);
        }
    };
    assert forall|i: int, j: int| 0 <= i < j < following.len() implies
        ((#[trigger] following[i], #[trigger] following[j]) matches (Some(first), Some(second))
            ==> routine_before(first, second)) by {
        assert(following[i] == prior[i]);
        if j < prior.len() {
            assert(following[j] == prior[j]);
        } else if let (Some(first), Some(second)) = (prior[i], new) {
            assert(following[j] == new);
            assert(routine_placed(first, before_gates, before_storage, before_state));
            assert(routine_before(first, second));
        }
    };
}

/// 子が使う増補入力の先頭は、VM の全状態素子列で先行する出力幅から決まる。
pub(super) closed spec fn routine_vm_input_offsets(
    routines: Seq<Option<RoutineWiring>>, storage: Seq<ClockedStorageInputs>, direct: usize, external: usize,
) -> bool {
    &&& direct <= storage.len()
    &&& forall|i: int| 0 <= i < routines.len() ==> ((#[trigger] routines[i]) matches Some(routine)
        ==> direct + routine.storage.start <= storage.len()
            && routine.state_inputs.start == external
                + clocked_storage_output_width(storage.take(direct + routine.storage.start)))
}

pub(super) proof fn join_routine_input_offsets(
    routines: Seq<Option<RoutineWiring>>, gates: Seq<NorGate>, storage: Seq<ClockedStorageInputs>,
    direct: usize, external: usize, first_state: usize, inputs: usize,
)
    requires
        direct <= storage.len(),
        external + clocked_storage_output_width(storage) == inputs,
        routines_placed(routines, gates, storage.skip(direct as int), first_state, inputs),
    ensures routine_vm_input_offsets(routines, storage, direct, external),
{
    reveal(routines_placed);
    let prefix = storage.take(direct as int);
    let suffix = storage.skip(direct as int);
    clocked_storage_width_concat(prefix, suffix);
    assert(storage =~= prefix + suffix);
    assert(first_state == external + clocked_storage_output_width(prefix));
    assert forall|i: int| 0 <= i < routines.len() implies ((#[trigger] routines[i]) matches Some(routine)
        ==> direct + routine.storage.start <= storage.len()
            && routine.state_inputs.start == external
                + clocked_storage_output_width(storage.take(direct + routine.storage.start))) by {
        if let Some(routine) = routines[i] {
            let previous = suffix.take(routine.storage.start as int);
            assert(routine_placed(routine, gates, suffix, inputs));
            assert(prefix + previous =~= storage.take(direct + routine.storage.start));
            clocked_storage_width_concat(prefix, previous);
        }
    };
}

/// 子の素子の配線と登録出力が、親側のどの添字とビット位置に対応するかを示す。
pub(super) proof fn routine_storage_mapping(
    netlist: &NorNetlist, external: usize, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int, device: int,
)
    requires
        routines_placed(routines, netlist.gates@, wiring.skip(direct as int), first_state, netlist.input_count),
        routine_vm_input_offsets(routines, wiring, direct, external),
        0 <= call < routines.len(),
        routines[call] matches Some(routine) && 0 <= device < routine.devices.len(),
    ensures
        ({
            let routine = routines[call]->Some_0;
            let parent = direct + routine.storage.start + device;
            let relative_start = clocked_storage_output_width(routine.devices.take(device));
            let relative_end = relative_start + routine.devices[device].data@.len();
            let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
                clocked_storage_output_width(routine.devices));
            &&& 0 <= parent < wiring.len()
            &&& routine.devices[device].parent_placement_matches(pins, routine.gates.start, &wiring[parent])
            &&& wiring[parent].data@.len() == routine.devices[device].data@.len()
            &&& routine.state_inputs.start + relative_start
                == external + clocked_storage_output_width(wiring.take(parent))
            &&& routine.state_inputs.start + relative_end <= routine.state_inputs.end <= netlist.input_count
        }),
{
    reveal(routines_placed);
    let routine = routines[call]->Some_0;
    let suffix = wiring.skip(direct as int);
    assert(routine_placed(routine, netlist.gates@, suffix, netlist.input_count));
    let base = direct + routine.storage.start;
    let parent = base + device;
    let mapped = wiring.skip(base).take(device);
    let local = routine.devices.take(device);
    let width = clocked_storage_output_width(routine.devices);
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start, width);
    assert(base + routine.devices.len() <= wiring.len());
    assert forall|i: int| 0 <= i < device implies (#[trigger] mapped[i]).data@.len() == (#[trigger] local[i]).data@.len() by {
        assert(mapped[i] == suffix[routine.storage.start + i]);
        assert(local[i].parent_placement_matches(pins, routine.gates.start, &mapped[i]));
    };
    clocked_storage_widths_agree(mapped, local);
    let prior = wiring.take(base);
    clocked_storage_width_concat(prior, mapped);
    assert(prior + mapped =~= wiring.take(parent));
    assert(wiring[parent] == suffix[routine.storage.start + device]);
    assert(routine.devices[device].parent_placement_matches(pins, routine.gates.start, &wiring[parent]));
    assert(wiring[parent].data@.len() == routine.devices[device].data@.len());
    let relative_start = clocked_storage_output_width(local);
    let relative_end = relative_start + routine.devices[device].data@.len();
    let through_device = routine.devices.take(device + 1);
    assert(local.push(routine.devices[device]) =~= through_device);
    crate::netlist::clocked_storage_width_push(local, routine.devices[device]);
    let trailing = routine.devices.skip(device + 1);
    clocked_storage_width_concat(through_device, trailing);
    assert(through_device + trailing =~= routine.devices);
    assert(relative_end <= width);
}

/// 子の登録出力を、親 VM のスナップショットから同じビット順で取り出す。
///
/// `device` は子が持つ状態素子の添字。親の添字には直接素子と先行する子の素子を加える。
pub(super) proof fn routine_storage_snapshot(
    vm: &ClockedVm, input: Seq<bool>, bits: Seq<bool>, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int, device: int,
)
    requires
        vm.layout_matches(vm.netlist_model(), vm.external_count(), wiring),
        vm.augmented_input_matches(input, bits),
        routines_placed(routines, vm.netlist_model().gates@, wiring.skip(direct as int), first_state,
            vm.netlist_model().input_count),
        routine_vm_input_offsets(routines, wiring, direct, vm.external_count()),
        0 <= call < routines.len(),
        routines[call] matches Some(routine) && 0 <= device < routine.devices.len(),
    ensures
        ({
            let routine = routines[call]->Some_0;
            let parent = direct + routine.storage.start + device;
            let relative_start = clocked_storage_output_width(routine.devices.take(device));
            let relative_end = relative_start + routine.devices[device].data@.len();
            let range = vm.storage_input_range_model(parent);
            &&& 0 <= parent < vm.storage_model().len()
            &&& range.start == routine.state_inputs.start + relative_start
            &&& range.end == routine.state_inputs.start + relative_end
            &&& range.end <= routine.state_inputs.end <= bits.len()
            &&& bits.subrange(routine.state_inputs.start as int, routine.state_inputs.end as int)
                .subrange(relative_start as int, relative_end as int) == vm.storage_model()[parent].output_model()
        }),
{
    routine_storage_mapping(&vm.netlist_model(), vm.external_count(), wiring, routines, direct, first_state, call, device);
    let routine = routines[call]->Some_0;
    let parent = direct + routine.storage.start + device;
    vm.storage_input_range_evidence(parent);
    vm.augmented_storage_segment(input, bits, parent);
    vm.augmented_input_shape(input, bits);
    let relative_start = clocked_storage_output_width(routine.devices.take(device));
    let relative_end = relative_start + routine.devices[device].data@.len();
    let range = vm.storage_input_range_model(parent);
    let child_bits = bits.subrange(routine.state_inputs.start as int, routine.state_inputs.end as int);
    assert(child_bits.subrange(relative_start as int, relative_end as int)
        =~= bits.subrange(range.start as int, range.end as int));
}

/// 子の増補入力は、親の状態で読んだ実引数に、子の各素子の登録出力を続けた列になる。
pub(super) proof fn routine_augmented_snapshot(
    vm: &ClockedVm, input: Seq<bool>, bits: Seq<bool>, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int,
) -> (child: Seq<bool>)
    requires
        vm.layout_matches(vm.netlist_model(), vm.external_count(), wiring),
        vm.augmented_input_matches(input, bits),
        routines_placed(routines, vm.netlist_model().gates@, wiring.skip(direct as int), first_state,
            vm.netlist_model().input_count),
        routine_vm_input_offsets(routines, wiring, direct, vm.external_count()),
        0 <= call < routines.len(),
        routines[call].is_some(),
    ensures
        ({
            let routine = routines[call]->Some_0;
            let width = clocked_storage_output_width(routine.devices);
            let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start, width);
            let external = routine.external.len() as int;
            &&& child.len() == routine.callee.input_count
            &&& child == clocked_instance_inputs(pins, bits, vm.gate_values_model())
            &&& child.take(external) == clocked_instance_inputs(routine.external, bits, vm.gate_values_model())
            &&& forall|device: int| #![trigger routine.devices[device]]
                0 <= device < routine.devices.len() ==> {
                let start = external + clocked_storage_output_width(routine.devices.take(device));
                let end = start + routine.devices[device].data@.len();
                let parent = direct + routine.storage.start + device;
                &&& 0 <= parent < vm.storage_model().len()
                &&& end <= child.len()
                &&& child.subrange(start, end) == vm.storage_model()[parent].output_model()
            }
        }),
{
    reveal(routines_placed);
    let routine = routines[call]->Some_0;
    let width = clocked_storage_output_width(routine.devices);
    let wires = routine.external;
    let gates = vm.gate_values_model();
    let pins = clocked_stateful_arguments(wires, routine.state_inputs.start, width);
    let external = clocked_instance_inputs(wires, bits, gates);
    let local_storage = bits.subrange(routine.state_inputs.start as int, routine.state_inputs.end as int);
    let child = external + local_storage;
    assert(routine_placed(routine, vm.netlist_model().gates@, wiring.skip(direct as int), vm.netlist_model().input_count));
    vm.augmented_input_shape(input, bits);
    assert(child.take(wires.len() as int) =~= external);
    let mapped = clocked_instance_inputs(pins, bits, gates);
    assert forall|i: int| 0 <= i < child.len() implies (#[trigger] child[i]) == mapped[i] by {
        if i < external.len() {
            assert(pins[i] == wires[i]);
        } else {
            let j = i - external.len();
            assert(pins[i] == Wire::Input((routine.state_inputs.start + j) as usize));
            assert(wire_value(pins[i], bits, gates) == local_storage[j]);
        }
    };
    assert(child =~= mapped);
    assert forall|device: int| #![trigger routine.devices[device]]
        0 <= device < routine.devices.len() implies {
        let relative = clocked_storage_output_width(routine.devices.take(device));
        let start = external.len() as int + relative;
        let end = start + routine.devices[device].data@.len();
        let parent = direct + routine.storage.start + device;
        &&& 0 <= parent < vm.storage_model().len()
        &&& end <= child.len()
        &&& child.subrange(start, end) == vm.storage_model()[parent].output_model()
    } by {
        routine_storage_snapshot(vm, input, bits, wiring, routines, direct, first_state, call, device);
        let start = clocked_storage_output_width(routine.devices.take(device)) as int;
        let end = start + routine.devices[device].data@.len();
        assert(child.subrange(external.len() + start, external.len() + end) =~= local_storage.subrange(start, end));
    };
    child
}

/// 親 VM の tick を、子の入力、ゲートと状態素子の更新、更新後の出力に対応付ける。
///
/// 実引数は親の各時点の配線から読む。更新後の観測には、更新後の実引数を使う。
pub(super) proof fn routine_tick_observation(
    vm: &ClockedVm, previous: &ClockedVm, input: Seq<bool>, output: Seq<bool>, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int,
) -> (result: (Seq<bool>, Seq<bool>, Seq<bool>))
    requires
        previous.layout_matches(previous.netlist_model(), previous.external_count(), wiring),
        vm.tick_matches(previous, input, output),
        routines_placed(routines, previous.netlist_model().gates@, wiring.skip(direct as int), first_state,
            previous.netlist_model().input_count),
        routine_vm_input_offsets(routines, wiring, direct, previous.external_count()),
        routines_pins_valid(routines, previous.netlist_model().input_count, previous.netlist_model().gates@.len()),
        0 <= call < routines.len(),
        routines[call].is_some(),
    ensures
        ({
            let routine = routines[call]->Some_0;
            let start = routine.gates.start as int;
            let end = routine.gates.end as int;
            let old_gates = previous.gate_values_model().subrange(start, end);
            let new_gates = vm.gate_values_model().subrange(start, end);
            let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
                clocked_storage_output_width(routine.devices));
            &&& routine.external.len() + clocked_storage_output_width(routine.devices) == routine.callee.input_count
            &&& result.0.len() == result.1.len() == routine.callee.input_count
            &&& old_gates.len() == new_gates.len() == routine.callee.gates@.len()
            &&& clocked_gate_updates(routine.callee.gates@, result.0, old_gates, new_gates)
            &&& result.2.len() == routine.callee.outputs@.len()
            &&& output_values_match(result.1, new_gates, routine.callee.outputs@, result.2)
            &&& forall|device: int| #![trigger routine.devices[device]]
                0 <= device < routine.devices.len() ==> {
                    let parent = direct + routine.storage.start + device;
                    let from = routine.external.len() as int
                        + clocked_storage_output_width(routine.devices.take(device));
                    let to = from + routine.devices[device].data@.len();
                    &&& 0 <= parent < previous.storage_model().len()
                    &&& parent < vm.storage_model().len()
                    &&& to <= result.0.len() && to <= result.1.len()
                    &&& result.0.subrange(from, to) == previous.storage_model()[parent].output_model()
                    &&& result.1.subrange(from, to) == vm.storage_model()[parent].output_model()
                    &&& clocked_storage_value_transition(previous.storage_model()[parent].output_model(),
                        previous.storage_model()[parent].memory_model(), vm.storage_model()[parent].output_model(),
                        vm.storage_model()[parent].memory_model(),
                        clocked_storage_pin_values(&routine.devices[device], result.0, old_gates))
                }
            &&& exists|before: Seq<bool>, after: Seq<bool>| {
                &&& #[trigger] previous.augmented_input_matches(input, before)
                &&& #[trigger] vm.augmented_input_matches(input, after)
                &&& result.0 == clocked_instance_inputs(pins, before, previous.gate_values_model())
                &&& result.1 == clocked_instance_inputs(pins, after, vm.gate_values_model())
                &&& result.2 == clocked_instance_inputs(routine.outputs, after, vm.gate_values_model())
            }
        }),
{
    reveal(routines_placed);
    reveal(routines_pins_valid);
    let routine = routines[call]->Some_0;
    let netlist = previous.netlist_model();
    vstd::std_specs::vec::axiom_spec_len(&netlist.gates);
    let snapshots = vm.tick_snapshots(previous, input, output);
    vm.preserve_layout_evidence(previous, netlist, previous.external_count(), wiring);
    assert(vm.netlist_model() == netlist && vm.external_count() == previous.external_count());
    let old_input = routine_augmented_snapshot(previous, input, snapshots.0, wiring, routines, direct, first_state, call);
    let new_input = routine_augmented_snapshot(vm, input, snapshots.1, wiring, routines, direct, first_state, call);
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
        clocked_storage_output_width(routine.devices));
    let base = routine.gates.start;
    let old_gates = previous.gate_values_model();
    let new_gates = vm.gate_values_model();
    clocked_instance_gate_updates_match(&routine.callee, netlist.gates@, pins, base, snapshots.0, old_gates, new_gates);
    let observed = clocked_instance_inputs(routine.outputs, snapshots.1, new_gates);
    assert(output_values_match(snapshots.1, new_gates, routine.outputs, observed));
    clocked_instance_outputs_match(&routine.callee, pins, routine.outputs, base, snapshots.1, new_gates, observed);
    let suffix = wiring.skip(direct as int);
    let child_gates = old_gates.subrange(routine.gates.start as int, routine.gates.end as int);
    assert(routine_placed(routine, netlist.gates@, suffix, netlist.input_count));
    assert forall|device: int| #![trigger routine.devices[device]]
        0 <= device < routine.devices.len() implies {
            let parent = direct + routine.storage.start + device;
            let from = routine.external.len() as int
                + clocked_storage_output_width(routine.devices.take(device));
            let to = from + routine.devices[device].data@.len();
            &&& 0 <= parent < previous.storage_model().len()
            &&& parent < vm.storage_model().len()
            &&& to <= old_input.len() && to <= new_input.len()
            &&& old_input.subrange(from, to) == previous.storage_model()[parent].output_model()
            &&& new_input.subrange(from, to) == vm.storage_model()[parent].output_model()
            &&& clocked_storage_value_transition(previous.storage_model()[parent].output_model(),
                previous.storage_model()[parent].memory_model(), vm.storage_model()[parent].output_model(),
                vm.storage_model()[parent].memory_model(),
                clocked_storage_pin_values(&routine.devices[device], old_input, child_gates))
        } by {
            let relative = routine.storage.start + device;
            let parent = direct + relative;
            let mapped = previous.storage_model()[parent].wiring_model();
            assert(mapped == wiring[parent]);
            assert(wiring[parent] == suffix[relative]);
            assert(routine.devices[device].parent_placement_matches(pins, base, &mapped));
            clocked_mapped_storage_reads_match(routine.devices, device, &mapped, pins, base,
                routine.callee.gates@.len() as usize, snapshots.0, old_gates);
            vm.storage_model()[parent].tick_values(&previous.storage_model()[parent], snapshots.0, old_gates);
        };
    (old_input, new_input, observed)
}

/// reset で子のゲートと状態素子が初期化され、その時点の親の配線から子の出力を読める。
///
/// ルートの外部入力はゼロになる。子の実引数は親の配線を読むため、定数に接続したビットはその値を取る。
pub(super) proof fn routine_reset_observation(
    vm: &ClockedVm, output: Seq<bool>, wiring: Seq<ClockedStorageInputs>,
    routines: Seq<Option<RoutineWiring>>, direct: usize, first_state: usize, call: int,
) -> (result: (Seq<bool>, Seq<bool>))
    requires
        vm.layout_matches(vm.netlist_model(), vm.external_count(), wiring),
        vm.reset_matches(output),
        routines_placed(routines, vm.netlist_model().gates@, wiring.skip(direct as int), first_state,
            vm.netlist_model().input_count),
        routine_vm_input_offsets(routines, wiring, direct, vm.external_count()),
        routines_pins_valid(routines, vm.netlist_model().input_count, vm.netlist_model().gates@.len()),
        0 <= call < routines.len(),
        routines[call].is_some(),
    ensures
        ({
            let routine = routines[call]->Some_0;
            let parent_bits = Seq::new(vm.netlist_model().input_count as nat, |_: int| false);
            let gates = vm.gate_values_model();
            let local_gates = gates.subrange(routine.gates.start as int, routine.gates.end as int);
            let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start,
                clocked_storage_output_width(routine.devices));
            &&& local_gates == Seq::new(routine.callee.gates@.len(), |_: int| false)
            &&& result.0.len() == routine.callee.input_count
            &&& result.0 == clocked_instance_inputs(pins, parent_bits, gates)
            &&& result.1.len() == routine.callee.outputs@.len()
            &&& result.1 == clocked_instance_inputs(routine.outputs, parent_bits, gates)
            &&& output_values_match(result.0, local_gates, routine.callee.outputs@, result.1)
            &&& forall|device: int| #![trigger routine.devices[device]]
                0 <= device < routine.devices.len() ==> {
                    let parent = direct + routine.storage.start + device;
                    let stored = vm.storage_model()[parent];
                    let width = routine.devices[device].data@.len();
                    let start = routine.external.len() as int + clocked_storage_output_width(routine.devices.take(device));
                    &&& 0 <= parent < vm.storage_model().len()
                    &&& start + width <= result.0.len()
                    &&& result.0.subrange(start, start + width) == stored.output_model()
                    &&& stored.output_model() == Seq::new(width, |_: int| false)
                    &&& stored.memory_model() == match clocked_storage_memory_width(&routine.devices[device]) {
                        Some(size) => Some(Seq::new(size, |_: int| false)),
                        None => None,
                    }
                }
        }),
{
    reveal(routines_placed);
    reveal(routines_pins_valid);
    let routine = routines[call]->Some_0;
    let netlist = vm.netlist_model();
    let source_input = Seq::new(vm.external_count() as nat, |_: int| false);
    let bits = vm.reset_snapshot(output);
    assert(bits =~= Seq::new(netlist.input_count as nat, |_: int| false));
    let child = routine_augmented_snapshot(vm, source_input, bits, wiring, routines, direct, first_state, call);
    let width = clocked_storage_output_width(routine.devices);
    let pins = clocked_stateful_arguments(routine.external, routine.state_inputs.start, width);
    let gates = vm.gate_values_model();
    let local = gates.subrange(routine.gates.start as int, routine.gates.end as int);
    vstd::std_specs::vec::axiom_spec_len(&netlist.gates);
    assert(local =~= Seq::new(routine.callee.gates@.len(), |_: int| false));
    let observed = clocked_instance_inputs(routine.outputs, bits, gates);
    assert(output_values_match(bits, gates, routine.outputs, observed));
    clocked_instance_outputs_match(&routine.callee, pins, routine.outputs, routine.gates.start, bits, gates, observed);
    let suffix = wiring.skip(direct as int);
    assert forall|device: int| #![trigger routine.devices[device]]
        0 <= device < routine.devices.len() implies {
            let parent = direct + routine.storage.start + device;
            let stored = vm.storage_model()[parent];
            let width = routine.devices[device].data@.len();
            &&& stored.output_model() == Seq::new(width, |_: int| false)
            &&& stored.memory_model() == match clocked_storage_memory_width(&routine.devices[device]) {
                Some(size) => Some(Seq::new(size, |_: int| false)),
                None => None,
            }
        } by {
        let relative = routine.storage.start + device;
        let parent = direct + relative;
        let mapped = vm.storage_model()[parent].wiring_model();
        assert(mapped == wiring[parent]);
        assert(wiring[parent] == suffix[relative]);
        assert(routine.devices[device].parent_placement_matches(pins, routine.gates.start, &mapped));
        assert(clocked_storage_memory_width(&routine.devices[device]) == clocked_storage_memory_width(&mapped));
        vm.initial_storage_values(parent);
    };
    (child, observed)
}

} // verus!
