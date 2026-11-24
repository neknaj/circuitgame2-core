//! 各呼び出しが占める区間と、親回路に移した実際の配線を対応付ける。

use crate::netlist::{ClockedStorageInputs, NorNetlist, PortBitLayout, Wire};
#[cfg(verus_only)]
use crate::netlist::{NorGate, clocked_stateful_arguments, clocked_storage_output_width, clocked_storage_width_concat,
    clocked_storage_widths_agree, instance_gates_at,
    instance_gates_in_extension, instance_outputs_match};
use core::ops::Range;
use alloc::vec::Vec;
use crate::project::ClockedWireDriver;
use vstd::prelude::*;

verus! {

/// 子のポートと、親回路におけるゲート・状態出力・状態素子の配置。
pub(super) struct RoutineWiring {
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

} // verus!
