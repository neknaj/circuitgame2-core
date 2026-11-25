#![no_std]

//! NOR の1ワードを32個の独立した回路実行として扱う。

mod clocked;

pub use clocked::{ClockedPlanError, ClockedTickError, PackedClockedNorPlan32};
#[cfg(verus_only)]
pub use clocked::{clocked_ports_fit, clocked_tick_error, packed_clocked_tick_matches};


#[cfg(not(verus_only))]
use verus_builtin_macros::verus;
#[cfg(verus_only)]
use vstd::prelude::*;

verus! {

/// 最下位から数えて、指定したレーンの値を表す。
pub open spec fn nor_lane_bit32(word: u32, lane: u32) -> bool
    recommends lane < 32,
{
    (word >> lane) & 1u32 == 1u32
}


/// ワードから指定したレーンの値を取り出す。レーン番号は最下位を0とする。
///
/// 32以上のレーン番号には `None` を返す。
#[inline]
pub fn read_lane32(word: u32, lane: u32) -> (result: Option<bool>)
    ensures result == if lane < 32 { Some(nor_lane_bit32(word, lane)) } else { None },
{
    if lane < 32 { Some((word >> lane) & 1 == 1) } else { None }
}

/// 指定したレーンだけに新しい値を設定し、残りのレーンを保つ。
///
/// 32以上のレーン番号には `None` を返す。
#[inline]
pub fn replace_lane32(word: u32, lane: u32, level: bool) -> (result: Option<u32>)
    ensures
        result.is_some() <==> lane < 32,
        result matches Some(updated) ==> forall|other: u32| other < 32 ==>
            #[trigger] nor_lane_bit32(updated, other)
                == if other == lane { level } else { nor_lane_bit32(word, other) },
{
    if lane >= 32 { return None; }
    let mask = 1u32 << lane;
    let updated = if level { word | mask } else { word & !mask };
    assert forall|other: u32| other < 32 implies
        #[trigger] nor_lane_bit32(updated, other)
            == if other == lane { level } else { nor_lane_bit32(word, other) } by {
        assert(lane < 32 && other < 32 ==> {
            let mask = 1u32 << lane;
            let updated = if level { word | mask } else { word & !mask };
            ((((updated >> other) & 1u32) == 1u32)
                == if other == lane { level } else { ((word >> other) & 1u32) == 1u32 })
        }) by (bit_vector);
    };
    Some(updated)
}

/// 同じ NOR を32個の独立した入力対に適用する。
///
/// ビット k の結果は、両入力のビット k だけから決まる。ビット0が最下位に当たる。
#[inline]
pub fn nor_word32(left: u32, right: u32) -> (word: u32)
    ensures
        word == !(left | right),
        forall|lane: u32| lane < 32 ==> #[trigger] nor_lane_bit32(word, lane)
            == !(nor_lane_bit32(left, lane) || nor_lane_bit32(right, lane)),
{
    let word = !(left | right);
    assert forall|lane: u32| lane < 32 implies #[trigger] nor_lane_bit32(word, lane)
        == !(nor_lane_bit32(left, lane) || nor_lane_bit32(right, lane)) by {
        assert(lane < 32 ==> (((!(left | right) >> lane) & 1u32 == 1u32)
            == !(((left >> lane) & 1u32 == 1u32) || ((right >> lane) & 1u32 == 1u32)))) by (bit_vector);
    };
    word
}


/// 一つの NOR ゲートが前の状態から読む二つの配線番号。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PackedNorGate32 {
    /// 左入力の配線番号。
    pub left: usize,
    /// 右入力の配線番号。
    pub right: usize,
}

/// 配線番号が入力配列の範囲外だった場所。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PackedNorWireError {
    /// ゲートの添字。
    pub gate: usize,
    /// 範囲外の配線番号。同じゲートでは左から調べる。
    pub wire: usize,
}

/// 1 tick に渡した配列の長さが計画に合わない。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackedNorSizeError {
    /// 入力側の配線数が合わない。
    Source,
    /// 書き出し側のゲート数が合わない。
    Destination,
}

pub open spec fn wires_fit(gates: Seq<PackedNorGate32>, sources: usize) -> bool {
    forall|i: int| 0 <= i < gates.len() ==> {
        let gate = #[trigger] gates[i];
        gate.left < sources && gate.right < sources
    }
}

pub open spec fn gate_value_matches(
    gate: PackedNorGate32, source: Seq<u32>, result: u32,
) -> bool {
    let left = source[gate.left as int];
    let right = source[gate.right as int];
    &&& result == !(left | right)
    &&& forall|lane: u32| lane < 32 ==> #[trigger] nor_lane_bit32(result, lane)
        == !(nor_lane_bit32(left, lane) || nor_lane_bit32(right, lane))
}

/// 前の状態だけを読む、配線番号検査済みの NOR 計画。
pub struct PackedNorPlan32<'a> {
    gates: &'a [PackedNorGate32],
    source_count: usize,
}

impl<'a> PackedNorPlan32<'a> {
    /// ゲート順の配線を表す。
    pub closed spec fn gates_model(&self) -> Seq<PackedNorGate32> { self.gates@ }

    /// 読み取り配列が含む配線の数を表す。
    pub closed spec fn source_count_model(&self) -> usize { self.source_count }

    #[verifier::type_invariant]
    spec fn wires_are_valid(&self) -> bool {
        wires_fit(self.gates@, self.source_count)
    }

    /// ゲート順に配線番号を検査し、繰り返し使う計画を作る。
    ///
    /// # Errors
    ///
    /// 最初に範囲外だったゲートと配線番号を返す。
    pub fn new(gates: &'a [PackedNorGate32], source_count: usize)
        -> (result: Result<Self, PackedNorWireError>)
        ensures
            result.is_ok() <==> wires_fit(gates@, source_count),
            match result {
                Ok(plan) => plan.gates_model() == gates@ && plan.source_count_model() == source_count,
                Err(error) => {
                    let gate = gates@[error.gate as int];
                    &&& error.gate < gates.len()
                    &&& wires_fit(gates@.take(error.gate as int), source_count)
                    &&& error.wire >= source_count
                    &&& error.wire == if gate.left >= source_count { gate.left } else { gate.right }
                },
            },
    {
        let mut i = 0;
        while i < gates.len()
            invariant i <= gates.len(), wires_fit(gates@.take(i as int), source_count),
            decreases gates.len() - i,
        {
            let gate = gates[i];
            if gate.left >= source_count {
                return Err(PackedNorWireError { gate: i, wire: gate.left });
            }
            if gate.right >= source_count {
                return Err(PackedNorWireError { gate: i, wire: gate.right });
            }
            assert forall|k: int| 0 <= k < i + 1 implies {
                let row = #[trigger] gates@[k];
                row.left < source_count && row.right < source_count
            } by {
                if k < i { assert(gates@.take(i as int)[k] == gates@[k]); }
            };
            i += 1;
        }
        assert(gates@.take(i as int) =~= gates@);
        Ok(Self { gates, source_count })
    }

    /// 32レーンの次のゲート状態を、呼び出し側のバッファーに書く。
    ///
    /// 外部入力と直前のゲート状態を読み取り配列に並べる順序は、計画の配線番号で決まる。
    ///
    /// # Errors
    ///
    /// 読み取り配列、書き出し配列の順に長さを検査する。エラー時は出力を変えない。
    pub fn step(&self, source: &[u32], next: &mut [u32])
        -> (result: Result<(), PackedNorSizeError>)
        ensures
            final(next)@.len() == old(next)@.len(),
            if source.len() != self.source_count_model() {
                result == Err(PackedNorSizeError::Source) && final(next)@ == old(next)@
            } else if old(next)@.len() != self.gates_model().len() {
                result == Err(PackedNorSizeError::Destination) && final(next)@ == old(next)@
            } else {
                result == Ok(()) && forall|i: int| 0 <= i < self.gates_model().len()
                    ==> #[trigger] gate_value_matches(self.gates_model()[i], source@, final(next)@[i])
            },
    {
        if source.len() != self.source_count {
            return Err(PackedNorSizeError::Source);
        }
        if next.len() != self.gates.len() {
            return Err(PackedNorSizeError::Destination);
        }
        proof { use_type_invariant(self); }
        let mut i = 0;
        while i < next.len()
            invariant
                source.len() == self.source_count,
                wires_fit(self.gates@, self.source_count),
                next@.len() == self.gates@.len() == old(next)@.len(),
                i <= next.len(),
                forall|k: int| 0 <= k < i ==>
                    #[trigger] gate_value_matches(self.gates@[k], source@, next@[k]),
            decreases next.len() - i,
        {
            let gate = self.gates[i];
            assert(gate.left < source.len() && gate.right < source.len());
            let word = nor_word32(source[gate.left], source[gate.right]);
            assert(gate_value_matches(gate, source@, word));
            next[i] = word;
            i += 1;
        }
        Ok(())
    }
}

} // verus!
