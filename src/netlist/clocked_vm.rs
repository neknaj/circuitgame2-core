//! NOR と状態素子を同じ tick で更新する。

use super::clocked::observe;
use super::{ClockedNor, ClockedStorage, ClockedStorageError, ClockedStorageInputs, TickInputError};
#[cfg(verus_only)]
use super::{clocked_gate_updates, clocked_storage_result, clocked_wiring_endpoints, clocked_wiring_valid,
    output_values_match};
#[cfg(verus_only)]
use super::clocked_storage::{storage_capacity, storage_fits};
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
        &&& device.output_model().len() == device.wiring_model().data@.len()
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
    ensures laid_out(storage.update(index, next), starts, external, inputs, gates),
{
    let updated = storage.update(index, next);
    assert forall|j: int| 0 <= j < updated.len() implies {
        let device = #[trigger] updated[j];
        &&& device.input_count_model() == inputs
        &&& device.gate_count_model() == gates
        &&& device.output_model().len() == device.wiring_model().data@.len()
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
                    &&& device.output_model().len() == device.wiring_model().data@.len()
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

    /// ゼロに初期化した NOR、ラッチ、RAM の状態。
    pub closed spec fn initial(&self) -> bool {
        &&& self.valid()
        &&& self.gates@ == Seq::new(self.gates@.len(), |_: int| false)
        &&& forall|i: int| 0 <= i < self.storage@.len() ==> initialized(#[trigger] self.storage@[i])
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

    /// reset 直後に、ゼロ入力と初期状態から公開出力を読んだことを表す。
    pub closed spec fn reset_matches(&self, output: Seq<bool>) -> bool {
        let netlist = self.circuit.netlist_model();
        &&& self.initial()
        &&& output.len() == netlist.outputs@.len()
        &&& output_values_match(Seq::new(netlist.input_count as nat, |_: int| false),
            self.gates@, netlist.outputs@, output)
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
        ensures final(self).valid(), match result {
            Ok(output) => final(self).tick_matches(old(self), input@, output@),
            Err(error) => error == TickInputError::InputCount && input@.len() != old(self).external_count()
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

} // verus!
