//! tick 開始時の配線から状態素子の入力を採取する。

use super::clocked::{observe, wire_within};
use super::{LatchState, RamState, StateAllocationError, TickInputError, Wire, read_wire};
#[cfg(verus_only)]
use super::{latch_next, output_ports_available, output_values_match, ram_address_value, ram_next_memory, ram_read_word,
    ram_resident_bits, state_bits_fit, wire_available, wire_value};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 状態素子の入力ポートが読む配線。
///
/// 配線は回路全体の入力ビット（状態素子の出力を含む）、または NOR の出力を指す。
/// 各列の添字0は最下位ビットに対応する。
#[derive(Debug)]
pub struct ClockedStorageInputs {
    /// RAM のアドレス配線。ラッチにはアドレス入力がない。
    pub address: Option<Vec<Wire>>,
    /// 保持または書き込みに使うデータの配線。列の長さが出力の幅になる。
    pub data: Vec<Wire>,
    /// ラッチの許可または RAM の書き込み許可を駆動する配線。
    pub enable: Wire,
}

/// 状態素子の配線または初期化の違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedStorageError {
    /// アドレス入力にある最初の不正な配線の添字。
    Address(usize),
    /// データ入力にある最初の不正な配線の添字。
    Data(usize),
    /// 許可入力が存在しない配線元を参照した。
    Enable,
    /// 状態の幅または記憶領域に問題があった。
    State(StateAllocationError),
}

enum StorageState {
    Latch(LatchState),
    Ram(RamState),
}

/// 配線と状態の幅を検査済みの状態素子1インスタンス。
pub struct ClockedStorage {
    wiring: ClockedStorageInputs,
    inputs: usize,
    gates: usize,
    state: StorageState,
}

spec fn first_unavailable(wires: Seq<Wire>, inputs: nat, gates: nat, index: int) -> bool {
    &&& 0 <= index < wires.len()
    &&& output_ports_available(wires, inputs, gates, index)
    &&& !wire_available(wires[index], inputs, gates)
}

fn invalid_wire(wires: &[Wire], inputs: usize, gates: usize) -> (result: Option<usize>)
    ensures
        match result {
            None => output_ports_available(wires@, inputs as nat, gates as nat, wires@.len() as int),
            Some(index) => first_unavailable(wires@, inputs as nat, gates as nat, index as int),
        },
{
    let mut i = 0;
    while i < wires.len()
        invariant
            i <= wires@.len(),
            output_ports_available(wires@, inputs as nat, gates as nat, i as int),
        decreases wires@.len() - i,
    {
        if !wire_within(wires[i], inputs, gates) {
            return Some(i);
        }
        i += 1;
    }
    None
}

spec fn storage_wires_valid(wiring: &ClockedStorageInputs, inputs: usize, gates: usize) -> bool {
    &&& (wiring.address matches Some(address) ==>
        output_ports_available(address@, inputs as nat, gates as nat, address@.len() as int))
    &&& output_ports_available(wiring.data@, inputs as nat, gates as nat, wiring.data@.len() as int)
    &&& wire_available(wiring.enable, inputs as nat, gates as nat)
}

pub(super) open spec fn storage_capacity(wiring: &ClockedStorageInputs) -> nat {
    match wiring.address {
        Some(address) => ram_resident_bits(address@.len(), wiring.data@.len()),
        None => wiring.data@.len(),
    }
}

pub(super) closed spec fn storage_fits(wiring: &ClockedStorageInputs, inputs: usize, gates: usize, limit: usize) -> bool {
    storage_wires_valid(wiring, inputs, gates) && wiring.data@.len() > 0
        && state_bits_fit(storage_capacity(wiring), limit)
}

impl StorageState {
    spec fn address_width(&self) -> Option<nat> {
        match self { Self::Latch(_) => None, Self::Ram(ram) => Some(ram.address_bits_model()) }
    }

    spec fn data_width(&self) -> nat {
        match self { Self::Latch(latch) => latch.value().len(), Self::Ram(ram) => ram.word_bits_model() }
    }

    spec fn output_bits(&self) -> Seq<bool> {
        match self { Self::Latch(latch) => latch.value(), Self::Ram(ram) => ram.output_model() }
    }

    spec fn memory_bits(&self) -> Option<Seq<bool>> {
        match self { Self::Latch(_) => None, Self::Ram(ram) => Some(ram.memory_model()) }
    }

    fn reset(&mut self)
        ensures
            final(self).address_width() == old(self).address_width(),
            final(self).data_width() == old(self).data_width(),
            final(self).output_bits() == Seq::new(old(self).output_bits().len(), |_: int| false),
            final(self).memory_bits() == match old(self).memory_bits() {
                Some(before) => Some(Seq::new(before.len(), |_: int| false)),
                None => None,
            },
        no_unwind
    {
        match self {
            StorageState::Latch(latch) => latch.reset(),
            StorageState::Ram(ram) => ram.reset(),
        }
    }

    fn step(&mut self, address: Option<&[bool]>, data: &[bool], enabled: bool)
        requires
            old(self).address_width() == (match address { Some(bits) => Some(bits@.len()), None => None }),
            old(self).data_width() == data@.len(),
        ensures
            final(self).address_width() == old(self).address_width(),
            final(self).data_width() == old(self).data_width(),
            storage_transition(old(self), final(self), match address { Some(bits) => Some(bits@), None => None }, data@, enabled),
        no_unwind
    {
        match self {
            StorageState::Latch(latch) => {
                let _result = latch.step(data, enabled);
                assert(_result.is_ok());
            },
            StorageState::Ram(ram) => {
                let Some(bits) = address else { unreachable!() };
                let _result = ram.step_bits(bits, data, enabled);
                assert(_result.is_ok());
            },
        }
    }
}

spec fn state_shape(wiring: &ClockedStorageInputs, state: &StorageState) -> bool {
    &&& state.address_width() == (match wiring.address { Some(wires) => Some(wires@.len()), None => None })
    &&& state.data_width() == wiring.data@.len()
}

spec fn storage_transition(
    previous: &StorageState, next: &StorageState, address: Option<Seq<bool>>, data: Seq<bool>, enabled: bool,
) -> bool {
    match address {
        None => next.memory_bits().is_none() && previous.memory_bits().is_none()
            && next.output_bits() == latch_next(previous.output_bits(), data, enabled),
        Some(bits) => {
            let a = ram_address_value(bits);
            let memory = previous.memory_bits()->Some_0;
            &&& previous.memory_bits().is_some()
            &&& a * data.len() + data.len() <= memory.len()
            &&& next.output_bits() == ram_read_word(memory, a, data.len())
            &&& next.memory_bits() == Some(ram_next_memory(memory, a, data, enabled))
        },
    }
}

/// 検査済みの配線と初期状態、または最初の構築エラーの根拠を表す。
pub closed spec fn clocked_storage_result(
    wiring: &ClockedStorageInputs, inputs: usize, gates: usize, bit_limit: usize,
    result: Result<ClockedStorage, ClockedStorageError>,
) -> bool {
    let address = match wiring.address { Some(wires) => wires@, None => Seq::<Wire>::empty() };
    let address_valid = output_ports_available(address, inputs as nat, gates as nat, address.len() as int);
    let data_valid = output_ports_available(wiring.data@, inputs as nat, gates as nat, wiring.data@.len() as int);
    let width = wiring.data@.len();
    match result {
        Ok(device) => storage_wires_valid(wiring, inputs, gates) && width > 0
            && state_bits_fit(storage_capacity(wiring), bit_limit)
            && device.wiring == *wiring && device.inputs == inputs && device.gates == gates
            && state_shape(wiring, &device.state)
            && device.output_model() == Seq::new(width, |_: int| false)
            && device.memory_model() == match wiring.address {
                Some(_) => Some(Seq::new((storage_capacity(wiring) - width) as nat, |_: int| false)),
                None => None,
            },
        Err(ClockedStorageError::Address(i)) => first_unavailable(address, inputs as nat, gates as nat, i as int),
        Err(ClockedStorageError::Data(i)) => address_valid
            && first_unavailable(wiring.data@, inputs as nat, gates as nat, i as int),
        Err(ClockedStorageError::Enable) => address_valid && data_valid
            && !wire_available(wiring.enable, inputs as nat, gates as nat),
        Err(ClockedStorageError::State(error)) => storage_wires_valid(wiring, inputs, gates)
            && match error {
                StateAllocationError::ZeroWidth => width == 0,
                StateAllocationError::Capacity => width > 0 && !state_bits_fit(storage_capacity(wiring), bit_limit),
                StateAllocationError::Allocation => width > 0 && state_bits_fit(storage_capacity(wiring), bit_limit),
            },
    }
}

pub(super) proof fn storage_bound(
    wiring: &ClockedStorageInputs, inputs: usize, gates: usize, budget: usize, device: ClockedStorage,
)
    requires clocked_storage_result(wiring, inputs, gates, budget, Ok(device)),
    ensures
        storage_fits(wiring, inputs, gates, budget),
        device.input_count_model() == inputs, device.gate_count_model() == gates,
        device.wiring_model() == *wiring,
        device.output_model() == Seq::new(wiring.data@.len(), |_: int| false),
        device.memory_model() matches Some(memory) ==> memory == Seq::new(memory.len(), |_: int| false),
        device.output_model().len() + (match device.memory_model() { Some(memory) => memory.len(), None => 0nat })
            == storage_capacity(wiring), storage_capacity(wiring) <= budget,
{
    if wiring.address.is_some() {
        assert(storage_capacity(wiring) >= wiring.data@.len()) by (nonlinear_arith)
            requires storage_capacity(wiring) == (vstd::arithmetic::power2::pow2(wiring.address->Some_0@.len()) + 1)
                * wiring.data@.len(),
        {}
    }
}

pub(super) proof fn storage_tick_shape(old: &ClockedStorage, next: &ClockedStorage, input: Seq<bool>, gates: Seq<bool>)
    requires
        next.storage_tick_matches(old, input, gates),
        old.output_model().len() == old.wiring_model().data@.len(),
    ensures
        next.input_count_model() == old.input_count_model(), next.gate_count_model() == old.gate_count_model(),
        next.wiring_model() == old.wiring_model(),
        next.output_model().len() == next.wiring_model().data@.len(),
{
}

impl ClockedStorage {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        storage_wires_valid(&self.wiring, self.inputs, self.gates) && state_shape(&self.wiring, &self.state)
    }

    /// インスタンスが参照する配線。
    pub closed spec fn wiring_model(&self) -> ClockedStorageInputs { self.wiring }

    /// インスタンスが入力として読める配線のビット数。
    pub closed spec fn input_count_model(&self) -> usize { self.inputs }

    /// インスタンスが参照できる NOR の数。
    pub closed spec fn gate_count_model(&self) -> usize { self.gates }

    /// 現在の保持出力または登録読み出し出力。
    pub closed spec fn output_model(&self) -> Seq<bool> {
        self.state.output_bits()
    }

    /// RAM の記憶部。ラッチの状態はその保持出力に含まれる。
    pub closed spec fn memory_model(&self) -> Option<Seq<bool>> {
        self.state.memory_bits()
    }

    /// 配線元の添字を検査し、状態素子を0に初期化する。
    ///
    /// # Errors
    ///
    /// アドレス、データ、許可の順に配線を検査し、その後で幅と記憶容量を検査する。
    /// 指定上限に収まる場合も、アロケーターが領域を確保できなければエラーを返す。
    pub fn bind(wiring: ClockedStorageInputs, inputs: usize, gates: usize, bit_limit: usize)
        -> (result: Result<Self, ClockedStorageError>)
        ensures clocked_storage_result(&wiring, inputs, gates, bit_limit, result),
    {
        if let Some(address) = &wiring.address {
            if let Some(i) = invalid_wire(address.as_slice(), inputs, gates) {
                return Err(ClockedStorageError::Address(i));
            }
        }
        if let Some(i) = invalid_wire(wiring.data.as_slice(), inputs, gates) {
            return Err(ClockedStorageError::Data(i));
        }
        if !wire_within(wiring.enable, inputs, gates) {
            return Err(ClockedStorageError::Enable);
        }
        let width = wiring.data.len();
        let state = match &wiring.address {
            Some(address) => match RamState::new(address.len() as u64, width, bit_limit) {
                Ok(ram) => {
                    assert(ram.memory_model().len() == storage_capacity(&wiring) - width) by (nonlinear_arith)
                        requires
                            ram.memory_model().len() == vstd::arithmetic::power2::pow2(address@.len()) * width,
                            storage_capacity(&wiring) == ram_resident_bits(address@.len(), width as nat),
                    {}
                    StorageState::Ram(ram)
                },
                Err(error) => return Err(ClockedStorageError::State(error)),
            },
            None => match LatchState::new(width, bit_limit) {
                Ok(latch) => StorageState::Latch(latch),
                Err(error) => return Err(ClockedStorageError::State(error)),
            },
        };
        Ok(Self { wiring, inputs, gates, state })
    }

    pub(super) fn resident_bits(&self) -> (bits: usize)
        ensures bits == self.output_model().len() + match self.memory_model() {
            Some(memory) => memory.len(), None => 0nat,
        },
    {
        match &self.state {
            StorageState::Latch(latch) => latch.output().len(),
            StorageState::Ram(ram) => ram.resident_bits(),
        }
    }

    /// 現在の出力を低位ビットから返す。
    pub fn output(&self) -> (bits: &[bool])
        ensures bits@ == self.output_model(), bits@.len() == self.wiring_model().data@.len(),
    {
        proof { use_type_invariant(self); }
        match &self.state {
            StorageState::Latch(latch) => latch.output(),
            StorageState::Ram(ram) => ram.output(),
        }
    }

    /// 状態素子をゼロで初期化したときの記憶と出力に戻す。
    pub fn reset(&mut self)
        ensures
            final(self).input_count_model() == old(self).input_count_model(),
            final(self).gate_count_model() == old(self).gate_count_model(),
            final(self).wiring_model() == old(self).wiring_model(),
            final(self).output_model() == Seq::new(old(self).output_model().len(), |_: int| false),
            final(self).memory_model() == match old(self).memory_model() {
                Some(before) => Some(Seq::new(before.len(), |_: int| false)),
                None => None,
            },
    {
        proof { use_type_invariant(&*self); }
        self.state.reset();
    }

    /// 指定した tick 開始時の配線値から、状態素子の次の状態を定める。
    pub closed spec fn storage_tick_matches(
        &self, previous: &Self, input: Seq<bool>, gates: Seq<bool>,
    ) -> bool {
        let wiring = &self.wiring;
        let data = Seq::new(wiring.data@.len(), |i: int| wire_value(wiring.data@[i], input, gates));
        let enabled = wire_value(wiring.enable, input, gates);
        &&& storage_wires_valid(wiring, previous.inputs, previous.gates)
        &&& previous.inputs == input.len() && previous.gates == gates.len()
        &&& self.wiring == previous.wiring
        &&& self.inputs == previous.inputs && self.gates == previous.gates
        &&& storage_transition(&previous.state, &self.state, match wiring.address {
            None => None,
            Some(address) => Some(Seq::new(address@.len(), |i: int| wire_value(address@[i], input, gates))),
        }, data, enabled)
    }

    /// 回路で共有する tick 開始時の入力値と NOR 出力を読み、状態を1 tick 進める。
    ///
    /// # Errors
    ///
    /// 入力値のビット数、NOR の値の数をこの順に検査する。違反がある場合は状態を更新しない。
    pub fn step(&mut self, input: &[bool], gates: &[bool]) -> (result: Result<(), TickInputError>)
        ensures match result {
            Ok(()) => final(self).storage_tick_matches(old(self), input@, gates@),
            Err(error) => *final(self) == *old(self) && if input@.len() != old(self).input_count_model() {
                error == TickInputError::InputCount
            } else {
                error == TickInputError::GateCount && gates@.len() != old(self).gate_count_model()
            },
        },
    {
        proof { use_type_invariant(&*self); }
        if input.len() != self.inputs {
            return Err(TickInputError::InputCount);
        }
        if gates.len() != self.gates {
            return Err(TickInputError::GateCount);
        }
        let enabled = read_wire(self.wiring.enable, input, gates).unwrap();
        let data = observe(self.wiring.data.as_slice(), input, gates);
        let ghost data_model = Seq::new(self.wiring.data@.len(), |i: int| wire_value(self.wiring.data@[i], input@, gates@));
        assert(data@ =~= data_model);
        let address = match &self.wiring.address {
            Some(wires) => {
                let sampled = observe(wires.as_slice(), input, gates);
                let ghost expected = Seq::new(wires@.len(), |i: int| wire_value(wires@[i], input@, gates@));
                assert(sampled@ =~= expected);
                Some(sampled)
            },
            None => None,
        };
        let address_bits = match &address { Some(bits) => Some(bits.as_slice()), None => None };
        self.state.step(address_bits, data.as_slice(), enabled);
        Ok(())
    }
}

} // verus!
