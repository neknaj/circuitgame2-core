//! NOR と状態素子を同じ tick で更新する。

pub(super) mod checkpoint;

use super::clocked::observe;
use super::{ClockedNor, ClockedStorage, ClockedStorageError, ClockedStorageInputs, NorNetlist, TickInputError};
use core::ops::Range;
use crate::project::clocked_nor_settling_bound;
#[cfg(verus_only)]
use super::{clocked_gate_updates, clocked_storage_result, clocked_wiring_endpoints, clocked_wiring_valid,
    output_values_match};
#[cfg(verus_only)]
use super::clocked_storage::{storage_capacity, storage_fits};
#[cfg(verus_only)]
use crate::project::{clocked_nor_bound_matches, clocked_nor_states_settle, fixed_nor_states};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 混在回路を初期化できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedVmError {
    /// 外部入力と状態素子出力の合計が、ネットリストの入力幅と一致しないか、配列に収まらない。
    InputLayout,
    /// 指定した状態素子の配線または初期化に失敗した。
    Storage {
        /// 構築時に渡した状態素子の添字。
        instance: usize,
        /// 状態素子の入力配線または記憶部に関する違反。
        error: ClockedStorageError,
    },
}

/// 平坦化した NOR 回路、ラッチ、RAM の現在の状態。
pub struct ClockedVm {
    circuit: ClockedNor,
    external: usize,
    storage: Vec<ClockedStorage>,
    starts: Vec<usize>,
    gates: Vec<bool>,
}

#[verifier::opaque]
spec fn used_bits(wiring: Seq<ClockedStorageInputs>, count: nat) -> nat
    recommends count <= wiring.len(),
    decreases count,
{
    if count == 0 || count > wiring.len() { 0 } else {
        used_bits(wiring, (count - 1) as nat) + storage_capacity(&wiring[count - 1])
    }
}

spec fn laid_out(storage: Seq<ClockedStorage>, starts: Seq<usize>, external: usize, inputs: usize, gates: nat) -> bool {
    &&& starts.len() == storage.len() + 1
    &&& starts[0] == external
    &&& forall|i: int| 0 <= i < storage.len() ==> {
        let device = #[trigger] storage[i];
        &&& device.input_count_model() == inputs
        &&& device.gate_count_model() == gates
        &&& device.wiring_model().pins_available(inputs as nat, gates)
        &&& device.output_model().len() == device.wiring_model().data@.len()
        &&& device.memory_shape()
        &&& starts[i + 1] == starts[i] + device.output_model().len()
        &&& starts[i + 1] <= inputs
    }
}

proof fn update_layout(storage: Seq<ClockedStorage>, starts: Seq<usize>, external: usize,
    inputs: usize, gates: nat, index: int, next: ClockedStorage,
)
    requires
        laid_out(storage, starts, external, inputs, gates),
        0 <= index < storage.len(),
        next.input_count_model() == storage[index].input_count_model(),
        next.gate_count_model() == storage[index].gate_count_model(),
        next.wiring_model() == storage[index].wiring_model(),
        next.output_model().len() == storage[index].output_model().len(),
        next.memory_shape(),
    ensures laid_out(storage.update(index, next), starts, external, inputs, gates),
{
    let updated = storage.update(index, next);
    assert forall|j: int| 0 <= j < updated.len() implies {
        let device = #[trigger] updated[j];
        &&& device.input_count_model() == inputs
        &&& device.gate_count_model() == gates
        &&& device.wiring_model().pins_available(inputs as nat, gates)
        &&& device.output_model().len() == device.wiring_model().data@.len()
        &&& device.memory_shape()
        &&& starts[j + 1] == starts[j] + device.output_model().len()
        &&& starts[j + 1] <= inputs
    } by {
        if j != index { assert(updated[j] == storage[j]); }
    };
}

spec fn starts_model(wiring: Seq<ClockedStorageInputs>, starts: Seq<usize>, external: usize, inputs: usize) -> bool {
    &&& 0 < starts.len() <= wiring.len() + 1
    &&& starts[0] == external
    &&& forall|i: int| 0 <= i + 1 < starts.len() && i >= 0 ==>
        (#[trigger] starts[i + 1]) == starts[i] + wiring[i].data@.len() && starts[i + 1] <= inputs
}

#[verifier::opaque]
pub(super) open spec fn wiring_width(wiring: Seq<ClockedStorageInputs>, count: nat) -> nat
    recommends count <= wiring.len(),
    decreases count,
{
    if count == 0 || count > wiring.len() { 0 } else {
        wiring_width(wiring, (count - 1) as nat) + wiring[count - 1].data@.len()
    }
}

/// 増補入力列で、状態素子の登録出力が占めるビット数を表す。
pub closed spec fn clocked_storage_output_width(wiring: Seq<ClockedStorageInputs>) -> nat {
    wiring_width(wiring, wiring.len())
}

pub(super) proof fn storage_output_width_total(wiring: Seq<ClockedStorageInputs>)
    ensures clocked_storage_output_width(wiring) == wiring_width(wiring, wiring.len()),
{
}

pub(super) proof fn wiring_width_zero(wiring: Seq<ClockedStorageInputs>)
    ensures wiring_width(wiring, 0) == 0,
{
    reveal(wiring_width);
}

pub(super) proof fn wiring_width_step(wiring: Seq<ClockedStorageInputs>, i: nat)
    requires i < wiring.len(),
    ensures wiring_width(wiring, i + 1) == wiring_width(wiring, i) + wiring[i as int].data@.len(),
{
    reveal(wiring_width);
}

proof fn equal_wiring_prefix_width(first: Seq<ClockedStorageInputs>, second: Seq<ClockedStorageInputs>, count: nat)
    requires count <= first.len() && count <= second.len(),
        forall|i: int| 0 <= i < count ==> (#[trigger] first[i]).data@.len() == (#[trigger] second[i]).data@.len(),
    ensures wiring_width(first, count) == wiring_width(second, count),
    decreases count,
{
    if count == 0 {
        wiring_width_zero(first);
        wiring_width_zero(second);
    } else {
        let last = (count - 1) as nat;
        equal_wiring_prefix_width(first, second, last);
        assert(first[last as int].data@.len() == second[last as int].data@.len());
        wiring_width_step(first, last);
        wiring_width_step(second, last);
    }
}

/// 各状態素子の出力幅が一致すれば、増補入力で占める総幅も一致する。
pub proof fn clocked_storage_widths_agree(first: Seq<ClockedStorageInputs>, second: Seq<ClockedStorageInputs>)
    requires first.len() == second.len(),
        forall|i: int| 0 <= i < first.len() ==> (#[trigger] first[i]).data@.len() == (#[trigger] second[i]).data@.len(),
    ensures clocked_storage_output_width(first) == clocked_storage_output_width(second),
{
    equal_wiring_prefix_width(first, second, first.len());
}

proof fn concatenated_wiring_prefix_width(
    first: Seq<ClockedStorageInputs>, second: Seq<ClockedStorageInputs>, count: nat,
)
    requires count <= second.len(),
    ensures wiring_width(first + second, first.len() + count) == wiring_width(first, first.len()) + wiring_width(second, count),
    decreases count,
{
    let joined = first + second;
    if count == 0 {
        assert forall|i: int| 0 <= i < first.len() implies (#[trigger] joined[i]).data@.len() == (#[trigger] first[i]).data@.len() by {
            assert(joined[i] == first[i]);
        };
        equal_wiring_prefix_width(joined, first, first.len());
        wiring_width_zero(second);
    } else {
        let last = (count - 1) as nat;
        concatenated_wiring_prefix_width(first, second, last);
        assert(joined[(first.len() + last) as int] == second[last as int]);
        wiring_width_step(joined, first.len() + last);
        wiring_width_step(second, last);
    }
}

/// 状態素子列を連結すると、それぞれが使う増補入力の幅が加算される。
pub proof fn clocked_storage_width_concat(first: Seq<ClockedStorageInputs>, second: Seq<ClockedStorageInputs>)
    ensures clocked_storage_output_width(first + second) == clocked_storage_output_width(first) + clocked_storage_output_width(second),
{
    concatenated_wiring_prefix_width(first, second, second.len());
}

/// 状態素子を末尾に置くと、登録出力の幅だけ増補入力が広がる。
pub proof fn clocked_storage_width_push(wiring: Seq<ClockedStorageInputs>, added: ClockedStorageInputs)
    ensures clocked_storage_output_width(wiring.push(added)) ==
        clocked_storage_output_width(wiring) + added.data@.len(),
{
    let extended = wiring.push(added);
    assert forall|i: int| 0 <= i < wiring.len() implies
        (#[trigger] wiring[i]).data@.len() == (#[trigger] extended[i]).data@.len() by {
        assert(extended[i] == wiring[i]);
    };
    equal_wiring_prefix_width(wiring, extended, wiring.len());
    wiring_width_step(extended, wiring.len());
}

pub(super) proof fn wiring_width_grows(wiring: Seq<ClockedStorageInputs>, before: nat, end: nat)
    requires before <= end <= wiring.len(),
    ensures wiring_width(wiring, before) <= wiring_width(wiring, end),
    decreases end - before,
{
    reveal(wiring_width);
    if before < end { wiring_width_grows(wiring, before, (end - 1) as nat); }
}

fn plan_inputs(wiring: &[ClockedStorageInputs], external: usize, inputs: usize) -> (result: Option<Vec<usize>>)
    ensures
        result.is_some() <==> inputs <= isize::MAX && external + wiring_width(wiring@, wiring@.len()) == inputs,
        result matches Some(starts) ==> starts@.len() == wiring@.len() + 1 && starts@.last() == inputs
            && starts_model(wiring@, starts@, external, inputs),
{
    proof { wiring_width_zero(wiring@); }
    if external > inputs || inputs > isize::MAX as usize { return None; }
    let mut starts = Vec::new();
    let mut used = external;
    let mut i = 0;
    starts.push(used);
    while i < wiring.len()
        invariant
            i <= wiring@.len(), starts@.len() == i + 1, starts@.last() == used,
            starts_model(wiring@, starts@, external, inputs),
            used == external + wiring_width(wiring@, i as nat) <= inputs <= isize::MAX,
        decreases wiring@.len() - i,
    {
        let width = wiring[i].data.len();
        proof { wiring_width_step(wiring@, i as nat); }
        if width > inputs - used {
            proof { wiring_width_grows(wiring@, (i + 1) as nat, wiring@.len()); }
            return None;
        }
        let ghost before = starts@;
        used += width;
        starts.push(used);
        assert(starts_model(wiring@, starts@, external, inputs)) by {
            assert forall|j: int| 0 <= j + 1 < starts@.len() && j >= 0 implies
                (#[trigger] starts@[j + 1]) == starts@[j] + wiring@[j].data@.len() && starts@[j + 1] <= inputs by {
                if j < i { assert(starts@[j + 1] == before[j + 1]); }
            };
        };
        i += 1;
    }
    if used == inputs { Some(starts) } else { None }
}

spec fn initialized(device: ClockedStorage) -> bool {
    &&& device.output_model() == Seq::new(device.output_model().len(), |_: int| false)
    &&& (device.memory_model() matches Some(memory) ==> memory == Seq::new(memory.len(), |_: int| false))
}

spec fn snapshot_segment(bits: Seq<bool>, starts: Seq<usize>, index: int, expected: Seq<bool>) -> bool {
    &&& 0 <= index && index + 1 < starts.len()
    &&& starts[index] <= starts[index + 1] <= bits.len()
    &&& bits.subrange(starts[index] as int, starts[index + 1] as int) == expected
}

spec fn input_snapshot(
    input: Seq<bool>, devices: Seq<ClockedStorage>, starts: Seq<usize>, count: nat, bits: Seq<bool>,
) -> bool {
    &&& count <= devices.len() && starts.len() == devices.len() + 1
    &&& input.len() == starts[0] <= bits.len() == starts[count as int]
    &&& bits.take(input.len() as int) == input
    &&& forall|i: int| 0 <= i < count ==>
        snapshot_segment(bits, starts, i, (#[trigger] devices[i]).output_model())
}

proof fn append_snapshot(
    input: Seq<bool>, devices: Seq<ClockedStorage>, starts: Seq<usize>, count: nat, prior: Seq<bool>,
    external: usize, inputs: usize, gates: nat,
)
    requires
        count < devices.len(),
        laid_out(devices, starts, external, inputs, gates),
        input_snapshot(input, devices, starts, count, prior),
    ensures input_snapshot(input, devices, starts, count + 1, prior + devices[count as int].output_model()),
{
    let next = prior + devices[count as int].output_model();
    reveal(input_snapshot);
    assert(count + 1 <= devices.len());
    assert(starts.len() == devices.len() + 1);
    assert(input.len() == starts[0] <= next.len());
    assert(next.len() == starts[(count + 1) as int]);
    assert(next.take(input.len() as int) =~= prior.take(input.len() as int));
    assert(next.take(input.len() as int) == input);
    assert forall|i: int| 0 <= i < (count + 1) implies
        snapshot_segment(next, starts, i, (#[trigger] devices[i]).output_model()) by {
        if i < count {
            assert(snapshot_segment(prior, starts, i, devices[i].output_model()));
            assert(next.subrange(starts[i] as int, starts[i + 1] as int)
                =~= prior.subrange(starts[i] as int, starts[i + 1] as int));
        } else {
            assert(i == count && starts[i] == prior.len());
            assert(next.subrange(starts[i] as int, starts[i + 1] as int) =~= devices[i].output_model());
        }
    };
    assert(input_snapshot(input, devices, starts, count + 1, next));
}

fn append_bits(bits: &mut Vec<bool>, source: &[bool])
    ensures final(bits)@ == old(bits)@ + source@,
{
    bits.extend_from_slice(source);
    assert(bits@ =~= old(bits)@ + source@);
}

// 状態素子の現在の出力だけを複製し、RAM の記憶部は複製しない。
fn snapshot(input: &[bool], devices: &[ClockedStorage], _starts: &[usize], inputs: usize, Ghost(gates): Ghost<nat>)
    -> (bits: Vec<bool>)
    requires laid_out(devices@, _starts@, input.len(), inputs, gates),
        _starts@.last() == inputs <= isize::MAX,
    ensures input_snapshot(input@, devices@, _starts@, devices@.len(), bits@),
{
    let mut bits = Vec::with_capacity(inputs);
    append_bits(&mut bits, input);
    assert(bits@ =~= input@);
    assert(bits@.take(input@.len() as int) =~= input@);
    let mut i = 0;
    while i < devices.len()
        invariant
            i <= devices@.len(),
            laid_out(devices@, _starts@, input.len(), inputs, gates),
            input_snapshot(input@, devices@, _starts@, i as nat, bits@),
        decreases devices@.len() - i,
    {
        let ghost prior = bits@;
        assert(input_snapshot(input@, devices@, _starts@, i as nat, prior));
        let device = &devices[i];
        let output = device.output();
        append_bits(&mut bits, output);
        proof {
            append_snapshot(input@, devices@, _starts@, i as nat, prior, input.len(), inputs, gates);
        }
        i += 1;
    }
    bits
}

spec fn checked_storage_prefix(wiring: Seq<ClockedStorageInputs>, inputs: usize, gates: usize,
    limit: usize, count: nat,
) -> bool {
    &&& count <= wiring.len()
    &&& forall|j: int| 0 <= j < count ==> {
        #[trigger] storage_fits(&wiring[j], inputs, gates, (limit - used_bits(wiring, j as nat)) as usize)
    }
}

proof fn checked_storage_prefix_push(wiring: Seq<ClockedStorageInputs>, inputs: usize, gates: usize,
    limit: usize, count: nat, left: usize,
)
    requires
        count < wiring.len(),
        checked_storage_prefix(wiring, inputs, gates, limit, count),
        left + used_bits(wiring, count) == limit,
        storage_fits(&wiring[count as int], inputs, gates, left),
    ensures checked_storage_prefix(wiring, inputs, gates, limit, count + 1),
{
    assert forall|j: int| 0 <= j < count + 1 implies {
        #[trigger] storage_fits(&wiring[j], inputs, gates, (limit - used_bits(wiring, j as nat)) as usize)
    } by {
        if j == count {
            assert(left == (limit - used_bits(wiring, j as nat)) as usize);
        }
    };
}

spec fn vm_storage_failure(circuit: &ClockedNor, external: usize, wiring: Seq<ClockedStorageInputs>,
    limit: usize, instance: usize, error: ClockedStorageError,
) -> bool {
    let netlist = circuit.netlist_model();
    let inputs = netlist.input_count;
    let gates = netlist.gates@.len() as usize;
    let used = used_bits(wiring, instance as nat);
    &&& inputs <= isize::MAX
    &&& external + wiring_width(wiring, wiring.len()) == inputs
    &&& instance < wiring.len() && used <= limit
    &&& checked_storage_prefix(wiring, inputs, gates, limit, instance as nat)
    &&& clocked_storage_result(&wiring[instance as int], inputs, gates, (limit - used) as usize, Err(error))
}

/// 回路と状態素子を束ねた結果、または構築に使った配線と上限に対応するエラー。
pub closed spec fn clocked_vm_result(
    circuit: &ClockedNor, external: usize, wiring: Seq<ClockedStorageInputs>, state_bit_limit: usize,
    result: Result<ClockedVm, ClockedVmError>,
) -> bool {
    match result {
        Ok(vm) => vm.initial() && vm.circuit == *circuit && vm.external == external
            && vm.storage@.len() == wiring.len()
            && used_bits(wiring, wiring.len()) <= state_bit_limit
            && forall|i: int| 0 <= i < vm.storage@.len() ==> (#[trigger] vm.storage@[i]).wiring_model() == wiring[i],
        Err(ClockedVmError::InputLayout) => circuit.netlist_model().input_count > isize::MAX
            || external + wiring_width(wiring, wiring.len()) != circuit.netlist_model().input_count,
        Err(ClockedVmError::Storage { instance, error }) =>
            vm_storage_failure(circuit, external, wiring, state_bit_limit, instance, error),
    }
}

fn bind_storage(circuit: &ClockedNor, _external: usize, mut pending: Vec<ClockedStorageInputs>,
    _starts: &[usize], state_bit_limit: usize, Ghost(declared): Ghost<Seq<ClockedStorageInputs>>,
) -> (result: Result<Vec<ClockedStorage>, ClockedVmError>)
    requires
        pending@ == declared,
        ({
            let inputs = circuit.netlist_model().input_count;
            &&& inputs <= isize::MAX
            &&& _external + wiring_width(declared, declared.len()) == inputs
            &&& _starts@.len() == declared.len() + 1 && _starts@.last() == inputs
            &&& starts_model(declared, _starts@, _external, inputs)
        }),
    ensures match result {
        Ok(storage) => {
            let netlist = circuit.netlist_model();
            &&& laid_out(storage@, _starts@, _external, netlist.input_count, netlist.gates@.len())
            &&& used_bits(declared, declared.len()) <= state_bit_limit
            &&& storage@.len() == declared.len()
            &&& forall|j: int| 0 <= j < storage@.len() ==>
                initialized(#[trigger] storage@[j]) && storage@[j].wiring_model() == declared[j]
        },
        Err(ClockedVmError::Storage { instance, error }) =>
            vm_storage_failure(circuit, _external, declared, state_bit_limit, instance, error),
        Err(ClockedVmError::InputLayout) => false,
    },
{
    let netlist = circuit.checked_netlist();
    let inputs = netlist.input_count;
    let gates = netlist.gates.len();
    let mut left = state_bit_limit;
    let mut storage: Vec<ClockedStorage> = Vec::with_capacity(pending.len());
    let mut i = 0;
    assert(used_bits(declared, 0) == 0) by { reveal(used_bits); };
    while i < pending.len()
        invariant
            i == storage@.len() <= pending@.len() == declared.len(),
            *netlist == circuit.netlist_model(),
            inputs == netlist.input_count <= isize::MAX, gates == netlist.gates@.len(),
            _starts@.len() == declared.len() + 1, _starts@.last() == inputs,
            starts_model(declared, _starts@, _external, inputs),
            _external + wiring_width(declared, declared.len()) == inputs,
            laid_out(storage@, _starts@.take(i + 1), _external, inputs, gates as nat),
            left + used_bits(declared, i as nat) == state_bit_limit,
            forall|j: int| i <= j < declared.len() ==> (#[trigger] pending@[j]) == declared[j],
            forall|j: int| 0 <= j < i ==> initialized(#[trigger] storage@[j]) && storage@[j].wiring_model() == declared[j],
            checked_storage_prefix(declared, inputs, gates, state_bit_limit, i as nat),
        decreases pending@.len() - i,
    {
        let mut ports = ClockedStorageInputs {
            address: None, data: Vec::new(), enable: super::Wire::Constant(false),
        };
        core::mem::swap(&mut ports, &mut pending[i]);
        let device = match ClockedStorage::bind(ports, inputs, gates, left) {
            Ok(device) => device,
            Err(error) => {
                assert(clocked_storage_result(&declared[i as int], inputs, gates, left, Err(error)));
                assert(left == (state_bit_limit - used_bits(declared, i as nat)) as usize);
                let result = ClockedVmError::Storage { instance: i, error };
                assert(vm_storage_failure(circuit, _external, declared, state_bit_limit, i, error));
                return Err(result);
            },
        };
        let size = device.resident_bits();
        let ghost previous = storage@;
        proof {
            super::clocked_storage::storage_bound(&ports, inputs, gates, left, device);
            assert(ports == declared[i as int]);
            checked_storage_prefix_push(declared, inputs, gates, state_bit_limit, i as nat, left);
            assert(left == (state_bit_limit - used_bits(declared, i as nat)) as usize);
            assert(used_bits(declared, (i + 1) as nat) == used_bits(declared, i as nat) + size) by {
                reveal(used_bits);
            };
        }
        left -= size;
        storage.push(device);
        proof {
            assert(laid_out(storage@, _starts@.take(i + 2), _external, inputs, gates as nat)) by {
                assert forall|j: int| 0 <= j < storage@.len() implies {
                    let device = #[trigger] storage@[j];
                    &&& device.input_count_model() == inputs
                    &&& device.gate_count_model() == gates
                    &&& device.wiring_model().pins_available(inputs as nat, gates as nat)
                    &&& device.output_model().len() == device.wiring_model().data@.len()
                    &&& device.memory_shape()
                    &&& _starts@.take(i + 2)[j + 1] == _starts@.take(i + 2)[j] + device.output_model().len()
                    &&& _starts@.take(i + 2)[j + 1] <= inputs
                } by {
                    if j < i { assert(storage@[j] == previous[j]); }
                    assert(_starts@[j + 1] == _starts@[j] + declared[j].data@.len());
                };
            };
        }
        i += 1;
    }
    assert(_starts@.take(i + 1) =~= _starts@);
    Ok(storage)
}

impl ClockedVm {
    /// ネットリストと状態素子の入力範囲が対応することを表す。
    pub closed spec fn valid(&self) -> bool {
        let netlist = self.circuit.netlist_model();
        &&& clocked_wiring_valid(&netlist)
        &&& netlist.input_count <= isize::MAX
        &&& self.gates@.len() == netlist.gates@.len()
        &&& laid_out(self.storage@, self.starts@, self.external, netlist.input_count, netlist.gates@.len())
        &&& self.starts@.last() == netlist.input_count
    }

    /// この回路の外部入力ビット数。
    pub closed spec fn external_count(&self) -> usize { self.external }

    /// 状態素子を、増補入力に登録出力を並べる順に表す。
    pub closed spec fn storage_model(&self) -> Seq<ClockedStorage> { self.storage@ }

    /// 展開後の配線と状態素子の有無から、定常化の上界を定める。
    pub closed spec fn settling_bound_matches(&self, bound: Option<usize>) -> bool {
        if self.storage_model().len() == 0 {
            clocked_nor_bound_matches(&self.netlist_model(), bound)
        } else {
            bound.is_none()
        }
    }

    /// 固定入力で定常化するまでの tick 数の上界を返す。
    ///
    /// 階層展開後のすべてのゲートを調べる。ラッチや RAM がある回路と、ゲート間に閉路がある回路には
    /// `None` を返す。ゲートも状態素子もない回路には `Some(0)` を返す。
    pub fn settling_bound(&self) -> (bound: Option<usize>)
        ensures self.settling_bound_matches(bound),
    {
        if self.storage.is_empty() {
            clocked_nor_settling_bound(&self.circuit)
        } else {
            None
        }
    }

    /// 固定入力を与えた1 tick で、この状態に遷移できることを表す。
    #[verifier::opaque]
    pub closed spec fn fixed_input_tick_matches(&self, previous: &Self, input: Seq<bool>) -> bool {
        exists|observed: Seq<bool>| #[trigger] self.tick_matches(previous, input, observed)
    }

    /// 任意の初期状態から、各 tick に同じ入力を与えて進めた VM の状態列。
    pub open spec fn fixed_input_states(&self, input: Seq<bool>, states: Seq<ClockedVm>) -> bool {
        &&& input.len() == self.external_count()
        &&& forall|i: int| 0 <= i < states.len() ==> (#[trigger] states[i]).valid() && states[i].same_layout(self)
        &&& forall|i: int| 0 < i < states.len() ==>
            (#[trigger] states[i]).fixed_input_tick_matches(&states[i - 1], input)
    }

    /// 現在の VM 状態を、固定入力で進める履歴の先頭に置く。
    pub proof fn fixed_input_states_start(&self, input: Seq<bool>)
        requires self.valid(), input.len() == self.external_count(),
        ensures self.fixed_input_states(input, seq![*self]),
    {
    }

    /// 同じ入力で進めた `step` の成功結果を、固定入力の履歴に追加する。
    pub proof fn fixed_input_states_push_tick(&self, input: Seq<bool>, states: Seq<ClockedVm>, next: ClockedVm, output: Seq<bool>)
        requires
            states.len() > 0, self.fixed_input_states(input, states),
            next.tick_matches(&states.last(), input, output),
        ensures self.fixed_input_states(input, states.push(next)),
    {
        let extended = states.push(next);
        reveal(ClockedVm::fixed_input_states);
        next.tick_snapshots(&states.last(), input, output);
        assert(states.last().same_layout(self));
        assert(next.same_layout(self));
        assert forall|i: int| 0 <= i < extended.len() implies
            (#[trigger] extended[i]).valid() && extended[i].same_layout(self) by {
            if i < states.len() { assert(extended[i] == states[i]); }
        };
        assert forall|i: int| 0 < i < extended.len() implies
            (#[trigger] extended[i]).fixed_input_tick_matches(&extended[i - 1], input) by {
            assert(extended[i - 1] == states[i - 1]);
            if i < states.len() {
                assert(extended[i] == states[i]);
            } else {
                assert(extended[i] == next);
                assert(extended[i].tick_matches(&extended[i - 1], input, output));
                reveal(ClockedVm::fixed_input_tick_matches);
            }
        };
        assert(self.fixed_input_states(input, extended));
    }

    proof fn gate_only_history(&self, input: Seq<bool>, states: Seq<ClockedVm>)
        requires self.valid(), self.storage_model().len() == 0, self.fixed_input_states(input, states),
        ensures fixed_nor_states(&self.netlist_model(), input,
            states.map_values(|state: ClockedVm| state.gate_values_model())),
    {
        let netlist = self.netlist_model();
        let gates = states.map_values(|state: ClockedVm| state.gate_values_model());
        assert(self.starts@.len() == 1 && self.starts@[0] == netlist.input_count);
        assert forall|i: int| 0 <= i < gates.len() implies (#[trigger] gates[i]).len() == netlist.gates@.len() by {
            assert(gates[i] == states[i].gate_values_model());
            assert(states[i].netlist_model() == netlist);
        };
        assert forall|i: int| 0 < i < gates.len() implies
            #[trigger] clocked_gate_updates(netlist.gates@, input, gates[i - 1], gates[i]) by {
            let current = &states[i];
            let previous = &states[i - 1];
            assert(current.fixed_input_tick_matches(previous, input));
            reveal(ClockedVm::fixed_input_tick_matches);
            let output = choose|output: Seq<bool>| #[trigger] current.tick_matches(previous, input, output);
            let (old_inputs, _) = current.tick_snapshots(previous, input, output);
            assert(current.netlist_model() == netlist);
            assert(old_inputs.take(input.len() as int) =~= old_inputs);
        };
    }

    /// 同じ固定入力で進めた二つの履歴で、定常化の上界以降の VM 状態が一致する。
    ///
    /// 初期ゲート値や比較時点までの経過 tick 数が異なる履歴も比較できる。
    pub proof fn settling_states_agree(
        &self, bound: usize, input: Seq<bool>, first: Seq<ClockedVm>, second: Seq<ClockedVm>, a: int, b: int,
    )
        requires self.valid(), self.settling_bound_matches(Some(bound)),
            self.fixed_input_states(input, first), self.fixed_input_states(input, second),
            bound <= a < first.len(), bound <= b < second.len(),
        ensures
            first[a].same_layout(&second[b]),
            first[a].storage_model().len() == 0 && second[b].storage_model().len() == 0,
            first[a].gate_values_model() == second[b].gate_values_model(),
    {
        self.gate_only_history(input, first);
        self.gate_only_history(input, second);
        let first_gates = first.map_values(|state: ClockedVm| state.gate_values_model());
        let second_gates = second.map_values(|state: ClockedVm| state.gate_values_model());
        clocked_nor_states_settle(&self.netlist_model(), bound, input, first_gates, second_gates, a, b);
        assert(first[a].same_layout(self) && second[b].same_layout(self));
    }

    /// 定常化の上界が `within` 以下なら、固定入力の履歴で `period` tick 離れた状態が一致する。
    ///
    /// `period` には正の間隔を指定する。`within` 以降の `tick` と、そこから `period` tick 後の
    /// 両方を履歴に含める。
    pub proof fn settling_states_repeat(
        &self, bound: usize, within: nat, period: nat, input: Seq<bool>, states: Seq<ClockedVm>, tick: nat,
    )
        requires
            self.valid(), self.settling_bound_matches(Some(bound)),
            self.fixed_input_states(input, states),
            bound as nat <= within <= tick, 0 < period,
            tick + period < states.len(),
        ensures
            states[tick as int].same_layout(&states[(tick + period) as int]),
            states[tick as int].storage_model().len() == 0
                && states[(tick + period) as int].storage_model().len() == 0,
            states[tick as int].gate_values_model() == states[(tick + period) as int].gate_values_model(),
    {
        self.settling_states_agree(bound, input, states, states, tick as int, (tick + period) as int);
    }

    /// tick の更新に使う平坦な NOR ゲート列と公開出力の配線を借りる。
    ///
    /// 入力幅には外部入力と各状態素子の登録出力を含む。ゲートの添字は tick の状態列と共通で、
    /// 配列内で自身より後ろのゲートも参照できる。
    pub fn netlist(&self) -> (netlist: &NorNetlist)
        ensures *netlist == self.netlist_model(), clocked_wiring_valid(netlist),
    {
        self.circuit.checked_netlist()
    }

    /// tick に渡す外部入力のビット数を返す。
    pub fn external_input_count(&self) -> (count: usize)
        ensures count == self.external_count(),
    {
        self.external
    }

    /// 増補入力に登録出力を並べる順序で数えた、状態素子の個数を返す。
    pub fn storage_count(&self) -> (count: usize)
        ensures count == self.storage_model().len(),
    {
        self.storage.len()
    }

    /// 状態素子の配線と、その登録出力が占める増補入力上の半開区間を返す。
    ///
    /// 添字は [状態素子の個数][Self::storage_count] で数える順序に従う。区間には外部入力の
    /// ビット数を含めて添字を付ける。RAM では登録読み出し出力の区間を返す。
    /// 添字が範囲外なら `None` を返す。
    pub fn storage_wiring(&self, index: usize) -> (view: Option<(&ClockedStorageInputs, Range<usize>)>)
        ensures
            index >= self.storage_model().len() ==> view.is_none(),
            self.valid() && index < self.storage_model().len() ==> view.is_some(),
            view matches Some((wiring, range)) ==> {
                &&& index < self.storage_model().len()
                &&& *wiring == self.storage_model()[index as int].wiring_model()
                &&& range == self.storage_input_range_model(index as int)
                &&& (self.valid() ==>
                    range.start + wiring.data@.len() == range.end <= self.netlist_model().input_count
                    && wiring.pins_available(self.netlist_model().input_count as nat, self.netlist_model().gates@.len()))
            },
    {
        if index >= self.storage.len() { return None; }
        let start = *self.starts.get(index)?;
        let end = *self.starts.get(index + 1)?;
        let wiring = self.storage[index].wiring();
        Some((wiring, start..end))
    }

    /// 指定した状態素子の RAM 記憶部を読み取る。
    ///
    /// 直近の tick が確定した時点の記憶部を返す。語はアドレス順で、各語の中は最下位ビットから並ぶ。
    /// 初期化とリセットの直後は、記憶部の全ビットが0になる。
    /// 添字が範囲外か、指定した素子がラッチの場合は `None` を返す。
    pub fn ram_memory(&self, index: usize) -> (bits: Option<&[bool]>)
        ensures
            index >= self.storage_model().len() ==> bits.is_none(),
            index < self.storage_model().len() ==> self.storage_model()[index as int].memory_model() == match bits {
                Some(memory) => Some(memory@),
                None => None,
            },
    {
        if index < self.storage.len() {
            self.storage[index].ram_memory()
        } else {
            None
        }
    }

    /// ゲートの登録値をネットリスト順に並べた列。
    pub closed spec fn gate_values_model(&self) -> Seq<bool> { self.gates@ }

    /// 階層展開後の2入力 NOR ゲートの数を返す。
    ///
    /// ラッチや RAM は別の状態素子として保持するため、この数に含めない。
    pub fn nor_gate_count(&self) -> (count: usize)
        ensures count == self.netlist_model().gates@.len(),
    {
        self.circuit.checked_netlist().gates.len()
    }

    /// 回路の出力フレームのビット数を返す。
    pub fn output_count(&self) -> (count: usize)
        ensures count == self.netlist_model().outputs@.len(),
    {
        self.circuit.output_count()
    }

    /// ゲートと公開出力が参照する回路のネットリスト。
    pub closed spec fn netlist_model(&self) -> NorNetlist { self.circuit.netlist_model() }

    /// VM のすべての端子が、同じ増補入力列とゲート列の範囲内にあることを示す。
    pub(crate) proof fn network_pin_bounds(&self)
        requires self.valid(),
        ensures clocked_wiring_valid(&self.netlist_model()),
            forall|i: int| 0 <= i < self.storage_model().len() ==>
                (#[trigger] self.storage_model()[i]).wiring_model().pins_available(
                    self.netlist_model().input_count as nat, self.netlist_model().gates@.len()),
    {
    }

    /// 指定した状態素子の登録出力を読む、増補入力上の半開区間。
    pub closed spec fn storage_input_range_model(&self, device: int) -> core::ops::Range<usize>
        recommends 0 <= device < self.storage_model().len(),
    {
        core::ops::Range { start: self.starts@[device], end: self.starts@[device + 1] }
    }

    proof fn state_start_is_prefix(&self, index: nat)
        requires self.valid(), index <= self.storage@.len(),
        ensures self.starts@[index as int] == self.external + wiring_width(
            self.storage@.map_values(|device: ClockedStorage| device.wiring_model()), index),
        decreases index,
    {
        let wiring = self.storage@.map_values(|device: ClockedStorage| device.wiring_model());
        if index == 0 {
            wiring_width_zero(wiring);
        } else {
            let previous = (index - 1) as nat;
            self.state_start_is_prefix(previous);
            wiring_width_step(wiring, previous);
            let device = self.storage@[previous as int];
            assert(wiring[previous as int] == device.wiring_model());
            assert(self.starts@[index as int] == self.starts@[previous as int] + device.output_model().len());
        }
    }

    /// VM が使う状態素子の区間は、外部入力と手前の登録出力を足し合わせた位置にある。
    pub proof fn storage_input_range_evidence(&self, device: int)
        requires self.valid(), 0 <= device < self.storage_model().len(),
        ensures
            ({
                let range = self.storage_input_range_model(device);
                let wiring = self.storage_model().map_values(|item: ClockedStorage| item.wiring_model());
                &&& range.start == self.external_count() + clocked_storage_output_width(wiring.take(device))
                &&& range.end == range.start + wiring[device].data@.len()
                &&& range.end <= self.netlist_model().input_count
            }),
    {
        let wiring = self.storage@.map_values(|item: ClockedStorage| item.wiring_model());
        let prefix = wiring.take(device);
        self.state_start_is_prefix(device as nat);
        assert forall|i: int| 0 <= i < device implies (#[trigger] prefix[i]).data@.len() == (#[trigger] wiring[i]).data@.len() by {
            assert(prefix[i] == wiring[i]);
        };
        equal_wiring_prefix_width(prefix, wiring, device as nat);
        assert(wiring[device] == self.storage@[device].wiring_model());
    }

    /// 外部入力の後に、この状態の各素子の登録出力を並べた増補入力を表す。
    pub closed spec fn augmented_input_matches(&self, input: Seq<bool>, bits: Seq<bool>) -> bool {
        input_snapshot(input, self.storage@, self.starts@, self.storage@.len(), bits)
    }

    /// 増補入力の幅はネットリストに従い、先頭は外部入力のままである。
    pub proof fn augmented_input_shape(&self, input: Seq<bool>, bits: Seq<bool>)
        requires self.valid(), self.augmented_input_matches(input, bits),
        ensures input.len() == self.external_count(), bits.len() == self.netlist_model().input_count,
            bits.take(input.len() as int) == input,
    {
        reveal(input_snapshot);
    }

    /// 指定した素子の登録出力を、増補入力の実際の区間から取り出せることを示す。
    pub proof fn augmented_storage_segment(&self, input: Seq<bool>, bits: Seq<bool>, device: int)
        requires self.valid(), self.augmented_input_matches(input, bits),
            0 <= device < self.storage_model().len(),
        ensures
            ({
                let range = self.storage_input_range_model(device);
                &&& range.start <= range.end <= bits.len()
                &&& bits.subrange(range.start as int, range.end as int) == self.storage_model()[device].output_model()
            }),
    {
        reveal(input_snapshot);
        assert(snapshot_segment(bits, self.starts@, device, self.storage@[device].output_model()));
    }

    /// ゼロに初期化した NOR、ラッチ、RAM の状態。
    pub closed spec fn initial(&self) -> bool {
        &&& self.valid()
        &&& self.gates@ == Seq::new(self.gates@.len(), |_: int| false)
        &&& forall|i: int| 0 <= i < self.storage@.len() ==> initialized(#[trigger] self.storage@[i])
    }

    /// 初期状態では、指定した素子の登録出力と RAM の全記憶ビットがゼロになる。
    pub proof fn initial_storage_values(&self, index: int)
        requires self.initial(), 0 <= index < self.storage_model().len(),
        ensures
            ({
                let device = self.storage_model()[index];
                &&& device.output_model() == Seq::new(device.wiring_model().data@.len(), |_: int| false)
                &&& device.memory_shape()
                &&& (device.memory_model() matches Some(memory) ==>
                    memory == Seq::new(memory.len(), |_: int| false))
            }),
    {
        assert(initialized(self.storage@[index]));
    }

    /// 実行中も、状態素子の登録出力幅と記憶容量は配線に対応する。
    pub proof fn storage_shape_evidence(&self, index: int)
        requires self.valid(), 0 <= index < self.storage_model().len(),
        ensures self.storage_model()[index].memory_shape(),
            self.storage_model()[index].output_model().len() == self.storage_model()[index].wiring_model().data@.len(),
    {
    }

    /// すべての更新が同じ旧状態を読み、観測が更新後の状態を読むことを表す。
    pub closed spec fn tick_matches(&self, previous: &Self, input: Seq<bool>, output: Seq<bool>) -> bool {
        let netlist = self.circuit.netlist_model();
        &&& self.valid() && previous.valid()
        &&& self.circuit == previous.circuit && self.external == previous.external && self.starts@ == previous.starts@
        &&& self.storage@.len() == previous.storage@.len()
        &&& exists|old_inputs: Seq<bool>, new_inputs: Seq<bool>| {
            &&& #[trigger] input_snapshot(input, previous.storage@, self.starts@, previous.storage@.len(), old_inputs)
            &&& #[trigger] input_snapshot(input, self.storage@, self.starts@, self.storage@.len(), new_inputs)
            &&& clocked_gate_updates(netlist.gates@, old_inputs, previous.gates@, self.gates@)
            &&& forall|i: int| 0 <= i < self.storage@.len() ==>
                (#[trigger] self.storage@[i]).storage_tick_matches(&previous.storage@[i], old_inputs, previous.gates@)
            &&& output.len() == netlist.outputs@.len()
            &&& output_values_match(new_inputs, self.gates@, netlist.outputs@, output)
        }
    }

    /// 1 tick の遷移から、更新に使った旧状態と公開出力に使った新状態の増補入力を取り出す。
    pub proof fn tick_snapshots(&self, previous: &Self, input: Seq<bool>, output: Seq<bool>)
        -> (snapshots: (Seq<bool>, Seq<bool>))
        requires self.tick_matches(previous, input, output),
        ensures
            self.valid() && previous.valid(),
            self.same_layout(previous),
            previous.augmented_input_matches(input, snapshots.0),
            self.augmented_input_matches(input, snapshots.1),
            input.len() == self.external_count(),
            snapshots.0.len() == snapshots.1.len() == self.netlist_model().input_count,
            snapshots.0.take(input.len() as int) == input && snapshots.1.take(input.len() as int) == input,
            previous.gate_values_model().len() == self.gate_values_model().len() == self.netlist_model().gates@.len(),
            clocked_gate_updates(self.netlist_model().gates@, snapshots.0,
                previous.gate_values_model(), self.gate_values_model()),
            forall|i: int| 0 <= i < self.storage_model().len() ==>
                (#[trigger] self.storage_model()[i]).storage_tick_matches(
                    &previous.storage_model()[i], snapshots.0, previous.gate_values_model()),
            output.len() == self.netlist_model().outputs@.len(),
            output_values_match(snapshots.1, self.gate_values_model(), self.netlist_model().outputs@, output),
    {
        let netlist = self.circuit.netlist_model();
        let snapshots = choose|old_inputs: Seq<bool>, new_inputs: Seq<bool>| {
            &&& #[trigger] input_snapshot(input, previous.storage@, self.starts@, previous.storage@.len(), old_inputs)
            &&& #[trigger] input_snapshot(input, self.storage@, self.starts@, self.storage@.len(), new_inputs)
            &&& clocked_gate_updates(netlist.gates@, old_inputs, previous.gates@, self.gates@)
            &&& forall|i: int| 0 <= i < self.storage@.len() ==>
                (#[trigger] self.storage@[i]).storage_tick_matches(&previous.storage@[i], old_inputs, previous.gates@)
            &&& output_values_match(new_inputs, self.gates@, netlist.outputs@, output)
        };
        reveal(input_snapshot);
        assert forall|i: int| 0 <= i < self.storage@.len() implies
            (#[trigger] self.storage@[i]).wiring_model() == previous.storage@[i].wiring_model() by {
            super::clocked_storage::storage_tick_shape(&previous.storage@[i], &self.storage@[i],
                snapshots.0, previous.gates@);
        };
        snapshots
    }

    /// 回路を束ね、NOR と全状態素子をゼロで初期化する。
    ///
    /// ネットリストの入力番号は、外部入力、その後に状態素子の出力をインスタンス順で並べた列を指す。
    /// `state_bit_limit` はラッチの保持出力、RAM の記憶部と登録出力の合計に適用する。
    ///
    /// # Errors
    ///
    /// 入力の総幅を確認し、その後で状態素子を指定順に構築する。最初に見つかった違反を返す。
    pub fn new(circuit: ClockedNor, external: usize, wiring: Vec<ClockedStorageInputs>, state_bit_limit: usize)
        -> (result: Result<Self, ClockedVmError>)
        ensures
            clocked_vm_result(&circuit, external, wiring@, state_bit_limit, result),
            result matches Ok(vm) ==> vm.valid() && vm.initial() && vm.external_count() == external,
            result.is_ok() ==> external + clocked_storage_output_width(wiring@) == circuit.netlist_model().input_count,
    {
        let netlist = circuit.checked_netlist();
        let inputs = netlist.input_count;
        let Some(starts) = plan_inputs(wiring.as_slice(), external, inputs) else { return Err(ClockedVmError::InputLayout) };
        let ghost declared = wiring@;
        let storage = match bind_storage(&circuit, external, wiring, starts.as_slice(), state_bit_limit, Ghost(declared)) {
            Ok(storage) => storage,
            Err(error) => return Err(error),
        };
        let gates = circuit.reset().gates;
        Ok(Self { circuit, external, storage, starts, gates })
    }

    /// 回路と各インスタンスの配線が、状態を更新する前と同じであることを表す。
    pub closed spec fn same_layout(&self, previous: &Self) -> bool {
        &&& self.circuit == previous.circuit && self.external == previous.external && self.starts@ == previous.starts@
        &&& self.storage@.len() == previous.storage@.len()
        &&& forall|i: int| 0 <= i < self.storage@.len() ==>
            (#[trigger] self.storage@[i]).wiring_model() == previous.storage@[i].wiring_model()
    }

    /// 配線が同じ VM では、入出力フレームの幅も同じになる。
    pub proof fn same_layout_frame_widths(&self, previous: &Self)
        requires self.same_layout(previous),
        ensures self.external_count() == previous.external_count(),
            self.netlist_model().outputs@.len() == previous.netlist_model().outputs@.len(),
    {
    }

    /// VM の配線を、展開時に渡したネットリストと状態素子の並びに対応付ける。
    pub open spec fn layout_matches(&self, netlist: NorNetlist, external: usize, wiring: Seq<ClockedStorageInputs>) -> bool {
        &&& self.valid()
        &&& self.netlist_model() == netlist
        &&& self.external_count() == external
        &&& self.storage_model().map_values(|device: ClockedStorage| device.wiring_model()) == wiring
    }

    /// 初期化に成功した VM の配線は、初期化に渡した配線と一致する。
    pub proof fn initialized_layout_evidence(&self, circuit: &ClockedNor, external: usize,
        wiring: Seq<ClockedStorageInputs>, limit: usize)
        requires clocked_vm_result(circuit, external, wiring, limit, Ok(*self)),
        ensures self.layout_matches(circuit.netlist_model(), external, wiring),
    {
        assert(self.storage@.map_values(|device: ClockedStorage| device.wiring_model()) =~= wiring);
    }

    /// reset や tick を挟んでも、同じ展開結果に状態を対応付けられる。
    pub proof fn preserve_layout_evidence(&self, previous: &Self, netlist: NorNetlist, external: usize,
        wiring: Seq<ClockedStorageInputs>)
        requires self.valid(), self.same_layout(previous), previous.layout_matches(netlist, external, wiring),
        ensures self.layout_matches(netlist, external, wiring),
    {
        assert(self.storage@.map_values(|device: ClockedStorage| device.wiring_model())
            =~= previous.storage@.map_values(|device: ClockedStorage| device.wiring_model()));
    }

    /// reset 直後に、ゼロ入力と初期状態から公開出力を読んだことを表す。
    pub closed spec fn reset_matches(&self, output: Seq<bool>) -> bool {
        let netlist = self.circuit.netlist_model();
        &&& self.initial()
        &&& output.len() == netlist.outputs@.len()
        &&& output_values_match(Seq::new(netlist.input_count as nat, |_: int| false),
            self.gates@, netlist.outputs@, output)
    }

    /// reset 後の観測に使う増補入力は、ゼロ入力と初期化した素子の登録出力からなる。
    pub proof fn reset_snapshot(&self, output: Seq<bool>) -> (bits: Seq<bool>)
        requires self.reset_matches(output),
        ensures
            self.initial() && self.valid(),
            bits == Seq::new(self.netlist_model().input_count as nat, |_: int| false),
            self.augmented_input_matches(Seq::new(self.external_count() as nat, |_: int| false), bits),
            self.gate_values_model() == Seq::new(self.netlist_model().gates@.len(), |_: int| false),
            output.len() == self.netlist_model().outputs@.len(),
            output_values_match(bits, self.gate_values_model(), self.netlist_model().outputs@, output),
    {
        let bits = Seq::new(self.netlist_model().input_count as nat, |_: int| false);
        let input = Seq::new(self.external as nat, |_: int| false);
        let count = self.storage@.len();
        reveal(input_snapshot);
        self.state_start_is_prefix(count);
        assert(self.starts@[count as int] == bits.len());
        assert(input.len() <= bits.len());
        assert(bits.take(input.len() as int) =~= input);
        assert forall|i: int| 0 <= i < count implies
            snapshot_segment(bits, self.starts@, i, (#[trigger] self.storage@[i]).output_model()) by {
            let start = self.starts@[i];
            let end = self.starts@[i + 1];
            let registered = self.storage@[i].output_model();
            assert(start <= end <= bits.len());
            assert(bits.subrange(start as int, end as int) =~= registered);
        };
        assert(input_snapshot(input, self.storage@, self.starts@, count, bits));
        bits
    }

    /// 全素子を初期状態に戻し、外部入力がゼロのときの公開出力を返す。
    pub fn reset(&mut self) -> (output: Vec<bool>)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).reset_matches(output@), final(self).same_layout(old(self)),
    {
        let ghost netlist = self.circuit.netlist_model();
        let mut i = 0;
        while i < self.storage.len()
            invariant
                i <= self.storage@.len() == old(self).storage@.len(),
                self.circuit == old(self).circuit,
                self.starts@ == old(self).starts@, self.external == old(self).external,
                laid_out(self.storage@, self.starts@, self.external, netlist.input_count, netlist.gates@.len()),
                forall|j: int| 0 <= j < i ==> initialized(#[trigger] self.storage@[j]),
                forall|j: int| 0 <= j < self.storage@.len() ==> (#[trigger] self.storage@[j]).wiring_model()
                    == old(self).storage@[j].wiring_model(),
            decreases self.storage@.len() - i,
        {
            let ghost prior = self.storage@;
            let ghost updated: ClockedStorage;
            {
                let device = &mut self.storage[i];
                device.reset();
                proof { updated = *device; }
            }
            proof {
                update_layout(prior, self.starts@, self.external, netlist.input_count, netlist.gates@.len(), i as int, updated);
                assert(initialized(updated));
            }
            i += 1;
        }
        let frame = self.circuit.reset();
        self.gates = frame.gates;
        frame.outputs
    }

    /// 外部入力を適用し、1 tick 後の公開出力を返す。
    ///
    /// # Errors
    ///
    /// 外部入力の長さが違う場合は状態を変更せずに入力数のエラーを返す。
    pub fn step(&mut self, input: &[bool]) -> (result: Result<Vec<bool>, TickInputError>)
        requires old(self).valid(),
        ensures
            final(self).valid(), final(self).same_layout(old(self)),
            result.is_ok() <==> input@.len() == old(self).external_count(),
            match result {
                Ok(output) => final(self).tick_matches(old(self), input@, output@),
                Err(error) => error == TickInputError::InputCount
                    && *final(self) == *old(self),
            },
    {
        if input.len() != self.external { return Err(TickInputError::InputCount); }
        let netlist = self.circuit.checked_netlist();
        let inputs = netlist.input_count;
        let ghost gates = self.gates@.len();
        let old_inputs = snapshot(input, self.storage.as_slice(), self.starts.as_slice(), inputs, Ghost(gates));
        let next = self.circuit.next_gates(self.gates.as_slice(), old_inputs.as_slice());
        let mut i = 0;
        while i < self.storage.len()
            invariant
                i <= self.storage@.len() == old(self).storage@.len(),
                self.gates@ == old(self).gates@,
                self.circuit == old(self).circuit, self.starts@ == old(self).starts@, self.external == old(self).external,
                inputs == netlist.input_count == old_inputs@.len(),
                gates == self.gates@.len() == netlist.gates@.len(),
                laid_out(self.storage@, self.starts@, self.external, inputs, gates),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.storage@[j])
                    .storage_tick_matches(&old(self).storage@[j], old_inputs@, self.gates@),
                forall|j: int| i <= j < self.storage@.len() ==> (#[trigger] self.storage@[j]) == old(self).storage@[j],
            decreases self.storage@.len() - i,
        {
            let ghost prior = self.storage@;
            let ghost updated: ClockedStorage;
            {
                let device = &mut self.storage[i];
                let _result = device.step(old_inputs.as_slice(), self.gates.as_slice());
                assert(_result.is_ok());
                proof {
                    super::clocked_storage::storage_tick_shape(&prior[i as int], &*device, old_inputs@, self.gates@);
                    updated = *device;
                }
            }
            proof { update_layout(prior, self.starts@, self.external, inputs, gates, i as int, updated); }
            i += 1;
        }
        self.gates = next;
        let new_inputs = snapshot(input, self.storage.as_slice(), self.starts.as_slice(), inputs, Ghost(gates));
        proof { clocked_wiring_endpoints(netlist); }
        let output = observe(netlist.outputs.as_slice(), new_inputs.as_slice(), self.gates.as_slice());
        proof { self.tick_snapshots(old(self), input@, output@); }
        Ok(output)
    }
}

/// reset と有限入力列の各 tick に対応する状態と公開出力。
pub open spec fn clocked_vm_trace(
    inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
) -> bool {
    &&& states.len() == outputs.len() == inputs.len() + 1
    &&& states[0].reset_matches(outputs[0])
    &&& forall|i: int| 0 < i < states.len() ==>
        (#[trigger] states[i]).tick_matches(&states[i - 1], inputs[i - 1], outputs[i])
}

/// reset 直後の観測を、入力がまだない trace として扱えることを示す。
pub proof fn clocked_vm_trace_from_reset(state: ClockedVm, output: Seq<bool>)
    requires state.reset_matches(output),
    ensures clocked_vm_trace(Seq::empty(), seq![state], seq![output]),
{
}

/// 同じ VM を1 tick 進めた状態と出力を、既存の trace に追加できることを示す。
pub proof fn clocked_vm_trace_push_tick(
    inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    input: Seq<bool>, state: ClockedVm, output: Seq<bool>,
)
    requires clocked_vm_trace(inputs, states, outputs), state.tick_matches(&states.last(), input, output),
    ensures clocked_vm_trace(inputs.push(input), states.push(state), outputs.push(output)),
{
    assert forall|i: int| 0 < i < states.len() + 1 implies
        (#[trigger] states.push(state)[i]).tick_matches(&states.push(state)[i - 1],
            inputs.push(input)[i - 1], outputs.push(output)[i]) by {
        if i < states.len() { assert(states.push(state)[i] == states[i]); }
    };
}

/// 任意の有効な状態を取り、`step` の事後条件から固定入力の履歴を組み立てる例。
proof fn fixed_input_states_example(start: ClockedVm, input: Seq<bool>, next: ClockedVm, output: Seq<bool>)
    requires start.valid(), input.len() == start.external_count(), next.tick_matches(&start, input, output),
    ensures start.fixed_input_states(input, seq![start, next]),
{
    start.fixed_input_states_start(input);
    start.fixed_input_states_push_tick(input, seq![start], next, output);
    assert(seq![start].push(next) =~= seq![start, next]);
}

} // verus!
