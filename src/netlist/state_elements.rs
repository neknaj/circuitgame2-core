//! ラッチと RAM の状態および tick ごとの更新。

use alloc::vec::Vec;
#[cfg(verus_only)]
use vstd::arithmetic::power2::{lemma_pow2_pos, lemma_pow2_strictly_increases, lemma_pow2_unfold, pow2};
use vstd::prelude::*;

verus! {

/// 状態素子の初期化に失敗した理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StateAllocationError {
    /// データ幅が0ビットだった。
    ZeroWidth,
    /// 必要な記憶領域が指定された上限または実行環境の表現範囲を超えた。
    Capacity,
    /// アロケーターが必要な領域を確保できなかった。
    Allocation,
}

/// 状態を更新できなかった入力。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StateInputError {
    /// 入力データの長さが宣言されたビット幅と異なる。
    Width,
    /// 指定された RAM のアドレスが範囲外だった。
    Address,
}

/// ラッチの1 tick 後の保持値。
pub open spec fn latch_next(previous: Seq<bool>, data: Seq<bool>, enabled: bool) -> Seq<bool> {
    if enabled { data } else { previous }
}

/// RAM の記憶部と読み出し出力に必要なビット数。
pub open spec fn ram_resident_bits(address_bits: nat, word_bits: nat) -> nat {
    (pow2(address_bits) + 1) * word_bits
}

/// RAM の1 tick 後の記憶部。語はアドレス順に並ぶ。
pub open spec fn ram_next_memory(memory: Seq<bool>, address: nat, data: Seq<bool>, write: bool) -> Seq<bool>
    recommends address * data.len() + data.len() <= memory.len(),
{
    let start = address * data.len();
    if write {
        Seq::new(memory.len(), |i: int| if start <= i < start + data.len() { data[i - start] } else { memory[i] })
    } else {
        memory
    }
}

/// RAM の1 tick 後の読み出し出力。対象語は tick 開始時の記憶部から読む。
pub open spec fn ram_read_word(memory: Seq<bool>, address: nat, word_bits: nat) -> Seq<bool>
    recommends address * word_bits + word_bits <= memory.len(),
{
    memory.subrange((address * word_bits) as int, (address * word_bits + word_bits) as int)
}

/// ビット数が設定値と実行環境の割り当て上限に収まる条件。
pub open spec fn state_bits_fit(bits: nat, bit_limit: usize) -> bool {
    bits <= bit_limit && bits <= isize::MAX
}

fn zero_bits(count: usize) -> (result: Result<Vec<bool>, StateAllocationError>)
    requires count <= isize::MAX,
    ensures match result {
        Ok(bits) => bits@ == Seq::new(count as nat, |_: int| false),
        Err(error) => error == StateAllocationError::Allocation,
    },
{
    let mut bits: Vec<bool> = Vec::new();
    if bits.try_reserve_exact(count).is_err() {
        return Err(StateAllocationError::Allocation);
    }
    while bits.len() < count
        invariant bits@.len() <= count, forall|i: int| 0 <= i < bits@.len() ==> !#[trigger] bits@[i],
        decreases count - bits@.len(),
    {
        bits.push(false);
    }
    assert(bits@ =~= Seq::new(count as nat, |_: int| false));
    Ok(bits)
}

fn clear_bits(bits: &mut Vec<bool>)
    ensures final(bits)@ == Seq::new(old(bits)@.len(), |_: int| false),
    no_unwind
{
    let mut i = 0;
    while i < bits.len()
        invariant i <= bits@.len() == old(bits)@.len(),
            forall|j: int| 0 <= j < i ==> !#[trigger] bits@[j],
        decreases bits@.len() - i,
    {
        bits[i] = false;
        i += 1;
    }
    assert(bits@ =~= Seq::new(old(bits)@.len(), |_: int| false));
}

/// 指定幅の値を保持するラッチ。保持値が tick 確定後の出力になる。
pub struct LatchState {
    bits: Vec<bool>,
}

impl LatchState {
    /// 現在の出力のビット列。
    pub closed spec fn value(&self) -> Seq<bool> {
        self.bits@
    }

    /// 全ビットを0に初期化する。
    ///
    /// # Errors
    ///
    /// 幅が0の場合は幅エラーを返す。幅が `bit_limit` または実行環境の上限を超える場合は
    /// 容量エラーを返す。領域を確保できなかった場合は割り当てエラーを返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::netlist::LatchState;
    ///
    /// let mut latch = LatchState::new(2, 2).unwrap();
    /// latch.step(&[true, false], true).unwrap();
    /// latch.step(&[false, true], false).unwrap();
    /// assert_eq!(latch.output(), &[true, false]);
    /// ```
    pub fn new(width: usize, bit_limit: usize) -> (result: Result<Self, StateAllocationError>)
        ensures match result {
            Ok(state) => width > 0 && state_bits_fit(width as nat, bit_limit)
                && state.value() == Seq::new(width as nat, |_: int| false),
            Err(StateAllocationError::ZeroWidth) => width == 0,
            Err(StateAllocationError::Capacity) => width > 0 && !state_bits_fit(width as nat, bit_limit),
            Err(StateAllocationError::Allocation) => width > 0 && state_bits_fit(width as nat, bit_limit),
        },
    {
        if width == 0 {
            return Err(StateAllocationError::ZeroWidth);
        }
        if width > bit_limit || width > isize::MAX as usize {
            return Err(StateAllocationError::Capacity);
        }
        Ok(Self { bits: zero_bits(width)? })
    }

    /// 現在の保持値を返す。
    pub fn output(&self) -> (bits: &[bool])
        ensures bits@ == self.value(),
    {
        self.bits.as_slice()
    }

    /// 現在の保持値を0に戻す。ビット幅は変わらない。
    pub fn reset(&mut self)
        ensures final(self).value() == Seq::new(old(self).value().len(), |_: int| false),
    {
        clear_bits(&mut self.bits);
    }

    /// 許可ビットが1なら入力値を保持し、0なら保持値を保存する。
    ///
    /// # Errors
    ///
    /// データのビット幅が異なる場合は、現在の保持値を変更せずにエラーを返す。
    pub fn step(&mut self, data: &[bool], enabled: bool) -> (result: Result<(), StateInputError>)
        ensures match result {
            Ok(()) => data@.len() == old(self).value().len()
                && final(self).value() == latch_next(old(self).value(), data@, enabled),
            Err(error) => error == StateInputError::Width && data@.len() != old(self).value().len()
                && final(self).value() == old(self).value(),
        },
    {
        if data.len() != self.bits.len() {
            return Err(StateInputError::Width);
        }
        if enabled {
            let mut i = 0;
            while i < data.len()
                invariant i <= data@.len() == self.bits@.len(),
                    forall|j: int| 0 <= j < i ==> #[trigger] self.bits@[j] == data@[j],
                decreases data@.len() - i,
            {
                self.bits[i] = data[i];
                i += 1;
            }
            assert(self.bits@ =~= data@);
        }
        Ok(())
    }
}

fn address_count(address_bits: u64) -> (count: Option<usize>)
    ensures
        count.is_some() <==> pow2(address_bits as nat) <= usize::MAX,
        count matches Some(words) ==> words == pow2(address_bits as nat) && words > 0,
{
    let mut used = 0;
    let mut words: usize = 1;
    assert(pow2(0) == 1) by { reveal(vstd::arithmetic::power::pow); };
    while used < address_bits
        invariant used <= address_bits, words == pow2(used as nat), words > 0,
        decreases address_bits - used,
    {
        used += 1;
        proof { lemma_pow2_unfold(used as nat); }
        match words.checked_mul(2) {
            Some(next) => words = next,
            None => {
                proof {
                    if used < address_bits {
                        lemma_pow2_strictly_increases(used as nat, address_bits as nat);
                    }
                }
                return None;
            },
        }
    }
    Some(words)
}

fn ram_layout(address_bits: u64, word_bits: usize, bit_limit: usize) -> (result: Option<(usize, usize)>)
    requires word_bits > 0,
    ensures
        result.is_some() <==> state_bits_fit(ram_resident_bits(address_bits as nat, word_bits as nat), bit_limit),
        result matches Some((words, size)) ==>
            words == pow2(address_bits as nat) && words > 0 && size == words * word_bits,
{
    let ghost total = ram_resident_bits(address_bits as nat, word_bits as nat);
    proof {
        lemma_pow2_pos(address_bits as nat);
        assert(total == pow2(address_bits as nat) * word_bits + word_bits
            && total >= pow2(address_bits as nat)) by (nonlinear_arith)
            requires
                word_bits > 0,
                total == (pow2(address_bits as nat) + 1) * word_bits,
    }
    let words = address_count(address_bits)?;
    let size = words.checked_mul(word_bits)?;
    let resident = size.checked_add(word_bits)?;
    if resident > bit_limit || resident > isize::MAX as usize {
        return None;
    }
    Some((words, size))
}

/// 同期 RAM 1インスタンスの記憶部と登録読み出し出力。
pub struct RamState {
    words: usize,
    word_bits: usize,
    memory: Vec<bool>,
    output: Vec<bool>,
}

impl RamState {
    /// アドレスの個数。
    pub closed spec fn words_model(&self) -> nat {
        self.words as nat
    }

    /// 1語のビット幅。
    pub closed spec fn word_bits_model(&self) -> nat {
        self.word_bits as nat
    }

    /// アドレス順に並べた全記憶ビット。
    pub closed spec fn memory_model(&self) -> Seq<bool> {
        self.memory@
    }

    /// 登録読み出し出力のビット列。
    pub closed spec fn output_model(&self) -> Seq<bool> {
        self.output@
    }

    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        &&& self.words > 0
        &&& self.word_bits > 0
        &&& self.memory@.len() == self.words * self.word_bits
        &&& self.output@.len() == self.word_bits
    }

    /// `2^address_bits` 語の記憶部と読み出し出力を0に初期化する。
    ///
    /// # Errors
    ///
    /// 1語の幅が0の場合は幅エラーを返す。記憶部と読み出し出力の合計が
    /// `bit_limit` または実行環境の上限を超えた場合は容量エラーを返す。
    /// 領域を確保できなかった場合は割り当てエラーを返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::netlist::RamState;
    ///
    /// let mut ram = RamState::new(1, 2, 6).unwrap();
    /// ram.step(1, &[true, false], true).unwrap();
    /// assert_eq!(ram.output(), &[false, false]);
    /// ram.step(1, &[false, false], false).unwrap();
    /// assert_eq!(ram.output(), &[true, false]);
    /// ```
    pub fn new(address_bits: u64, word_bits: usize, bit_limit: usize) -> (result: Result<Self, StateAllocationError>)
        ensures match result {
            Ok(state) => word_bits > 0 && state_bits_fit(ram_resident_bits(address_bits as nat, word_bits as nat), bit_limit)
                && state.words_model() == pow2(address_bits as nat) && state.word_bits_model() == word_bits
                && state.memory_model() == Seq::new(pow2(address_bits as nat) * word_bits as nat, |_: int| false)
                && state.output_model() == Seq::new(word_bits as nat, |_: int| false),
            Err(StateAllocationError::ZeroWidth) => word_bits == 0,
            Err(StateAllocationError::Capacity) => word_bits > 0
                && !state_bits_fit(ram_resident_bits(address_bits as nat, word_bits as nat), bit_limit),
            Err(StateAllocationError::Allocation) => word_bits > 0
                && state_bits_fit(ram_resident_bits(address_bits as nat, word_bits as nat), bit_limit),
        },
    {
        if word_bits == 0 {
            return Err(StateAllocationError::ZeroWidth);
        }
        let Some((words, size)) = ram_layout(address_bits, word_bits, bit_limit) else {
            return Err(StateAllocationError::Capacity);
        };
        assert(size + word_bits == ram_resident_bits(address_bits as nat, word_bits as nat)) by (nonlinear_arith)
            requires size == pow2(address_bits as nat) * word_bits,
        {
        }
        let memory = zero_bits(size)?;
        let output = zero_bits(word_bits)?;
        Ok(Self { words, word_bits, memory, output })
    }

    /// 最新の tick で読み出した値を返す。初期化と reset の直後は0を返す。
    pub fn output(&self) -> (bits: &[bool])
        ensures bits@ == self.output_model(),
    {
        self.output.as_slice()
    }

    /// 記憶部と読み出し出力を0に戻す。語数とビット幅は変わらない。
    pub fn reset(&mut self)
        ensures
            final(self).words_model() == old(self).words_model(),
            final(self).word_bits_model() == old(self).word_bits_model(),
            final(self).memory_model() == Seq::new(old(self).memory_model().len(), |_: int| false),
            final(self).output_model() == Seq::new(old(self).output_model().len(), |_: int| false),
    {
        proof { use_type_invariant(&*self); }
        clear_bits(&mut self.memory);
        clear_bits(&mut self.output);
    }

    /// 対象語の更新前の値を読み出し出力へ格納する。
    /// 書き込み許可が1なら、その tick に対象語を入力データで更新する。
    ///
    /// # Errors
    ///
    /// アドレスの範囲、入力データのビット幅の順に検査する。
    /// エラーの場合は記憶部と読み出し出力を保持する。
    pub fn step(&mut self, address: usize, data: &[bool], write: bool) -> (result: Result<(), StateInputError>)
        ensures
            final(self).words_model() == old(self).words_model(),
            final(self).word_bits_model() == old(self).word_bits_model(),
            match result {
                Ok(()) => address < old(self).words_model() && data@.len() == old(self).word_bits_model()
                    && address * data@.len() + data@.len() <= old(self).memory_model().len()
                    && final(self).output_model() == ram_read_word(old(self).memory_model(), address as nat, data@.len())
                    && final(self).memory_model() == ram_next_memory(old(self).memory_model(), address as nat, data@, write),
                Err(error) => final(self).memory_model() == old(self).memory_model()
                    && final(self).output_model() == old(self).output_model()
                    && if address >= old(self).words_model() {
                        error == StateInputError::Address
                    } else {
                        error == StateInputError::Width && data@.len() != old(self).word_bits_model()
                    },
            },
    {
        proof { use_type_invariant(&*self); }
        if address >= self.words {
            return Err(StateInputError::Address);
        }
        if data.len() != self.word_bits {
            return Err(StateInputError::Width);
        }
        let width = self.word_bits;
        let ghost words = self.words;
        let ghost size = self.memory.len();
        assert(0 <= address * width && address * width + width <= size) by (nonlinear_arith)
            requires address < words, size == words * width,
        {
        }
        let start = address * width;
        update_ram_word(&mut self.memory, &mut self.output, Ghost(address), start, data, write);
        Ok(())
    }
}

fn update_ram_word(memory: &mut Vec<bool>, output: &mut Vec<bool>, _address: Ghost<usize>, start: usize,
    data: &[bool], write: bool,
)
    requires
        start == _address@ * data@.len(),
        start + data@.len() <= old(memory)@.len(),
        old(output)@.len() == data@.len(),
    ensures
        final(memory)@.len() == old(memory)@.len(),
        final(output)@.len() == old(output)@.len(),
        final(output)@ == ram_read_word(old(memory)@, _address@ as nat, data@.len()),
        final(memory)@ == ram_next_memory(old(memory)@, _address@ as nat, data@, write),
    no_unwind
{
    let width = data.len();
    let ghost size = memory.len();
    let ghost previous = memory@;
    let mut bit = 0;
    while bit < width
        invariant
            bit <= width == data@.len() == output@.len(),
            memory@.len() == previous.len() == size,
            start == _address@ * width,
            start + width <= size,
            previous == old(memory)@,
            forall|i: int| 0 <= i < bit ==> #[trigger] output@[i] == previous[start + i],
            forall|i: int| 0 <= i < previous.len() ==>
                #[trigger] memory@[i] == if write && start <= i < start + bit { data@[i - start] } else { previous[i] },
        decreases width - bit,
    {
        let index = start + bit;
        // 先に更新したのは別のビットなので、ここでは対象ビットの更新前の値を読める。
        output[bit] = memory[index];
        if write {
            memory[index] = data[bit];
        }
        bit += 1;
    }
    assert(output@ =~= previous.subrange(start as int, start + width));
    assert(memory@ =~= ram_next_memory(previous, _address@ as nat, data@, write));
}

}
