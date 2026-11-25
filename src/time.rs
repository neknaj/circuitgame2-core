//! 論理 tick と有理数で表した時刻の対応を扱う。

mod event_queue;
mod events;

pub use circuitgame2_device_timing::{ClockError, PendingClockChange, SimulationClock, TickPosition, exact_microseconds};
#[cfg(verus_only)]
pub use circuitgame2_device_timing::clock_change_matches;
pub(crate) use event_queue::PendingEvents;
pub use event_queue::{ScheduledEvent, ScheduledEvents};
#[cfg(verus_only)]
pub use event_queue::{events_at_tick, events_by_reset_generation, next_event_matches};
pub use events::{EventTimeStatus, classify_event_time, ready_event_indices};
#[cfg(verus_only)]
pub use events::{event_indices_match, event_time_status};

use vstd::prelude::*;

#[cfg(verus_only)]
use vstd::arithmetic::{
    div_mod::{lemma_fundamental_div_mod, lemma_mod_bound},
    mul::{
        lemma_mul_inequality, lemma_mul_is_commutative,
        lemma_mul_is_distributive_add_other_way, lemma_mul_is_distributive_sub_other_way,
    },
};

verus! {

/// プロジェクト設定の `tick-ns` が指定する1 tick のナノ秒数。
///
/// 分子と分母は正で、どちらも `i64::MAX` 以下。設定で指定した比を保持する。
#[derive(Debug)]
pub struct TickPeriod {
    numerator: u64,
    denominator: u64,
}

/// 有理数で指定した時刻を tick に対応付けられなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TickTimeError {
    /// 時刻の分母が0である。
    ZeroDenominator,
    /// 時刻以後にある最初の tick が `u64::MAX` を超える。
    TickOutOfRange,
}

/// 設定で指定できる1 tick の分子と分母を表す。
pub open spec fn valid_tick_period(numerator: u64, denominator: u64) -> bool {
    0 < numerator <= i64::MAX as u64 && 0 < denominator <= i64::MAX as u64
}

impl TickPeriod {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        valid_tick_period(self.numerator, self.denominator)
    }

    /// 1 tick のナノ秒数を表す分子と分母。
    pub closed spec fn period(&self) -> (u64, u64) {
        (self.numerator, self.denominator)
    }

    /// tick 境界に達していて、その直前の境界が指定時刻より早いことを表す。
    ///
    /// 時刻は `numerator / denominator` ns。tick 0 の時刻は0。
    pub open spec fn first_tick_at_or_after_time(&self, numerator: u64, denominator: u64, tick: nat) -> bool {
        let (ns_num, ns_den) = self.period();
        let target = (numerator as int) * (ns_den as int);
        let scale = (denominator as int) * (ns_num as int);
        &&& valid_tick_period(ns_num, ns_den)
        &&& denominator > 0
        &&& target <= (tick as int) * scale
        &&& (tick == 0 || ((tick as int) - 1) * scale < target)
    }

    /// 指定時刻以後の tick 境界が `u64` の範囲に存在することを表す。
    pub open spec fn time_fits_ticks(&self, numerator: u64, denominator: u64) -> bool {
        let (ns_num, ns_den) = self.period();
        &&& valid_tick_period(ns_num, ns_den)
        &&& denominator > 0
        &&& (numerator as int) * (ns_den as int)
            <= (u64::MAX as int) * ((denominator as int) * (ns_num as int))
    }

    /// 有理数で指定した時間間隔が1 tick 以上であることを表す。
    pub open spec fn interval_spans_tick(&self, numerator: u64, denominator: u64) -> bool {
        let (ns_num, ns_den) = self.period();
        &&& denominator > 0
        &&& (numerator as int) * (ns_den as int) >= (denominator as int) * (ns_num as int)
    }

    /// 有理数の時間間隔が1 tick 以上なら `true` を返す。
    ///
    /// 時間間隔は `numerator / denominator` ns で渡す。分母が0なら `false` を返す。
    pub fn interval_at_least_one_tick(&self, numerator: u64, denominator: u64) -> (result: bool)
        ensures result <==> self.interval_spans_tick(numerator, denominator),
    {
        denominator != 0
            && multiply_u64(numerator, self.denominator) >= multiply_u64(denominator, self.numerator)
    }

    /// 開始 tick から指定時間が経過した時刻以後の最初の境界を表す。
    pub open spec fn first_tick_from_start(
        &self, start: u64, numerator: u64, denominator: u64, tick: nat,
    ) -> bool {
        &&& start as nat <= tick
        &&& self.first_tick_at_or_after_time(numerator, denominator, (tick - start as nat) as nat)
    }

    /// 開始 tick の境界から指定時間が経過した時刻以後の、最初の論理 tick を返す。
    ///
    /// 経過時間は `numerator / denominator` ns。UART などでは、同じ開始 tick を
    /// 基準にして、各境界までの丸め前の経過時間を渡す。
    ///
    /// # Errors
    ///
    /// 分母が0なら [`TickTimeError::ZeroDenominator`]、開始 tick を含む結果が
    /// `u64` に収まらないなら [`TickTimeError::TickOutOfRange`] を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::time::{TickPeriod, TickTimeError};
    ///
    /// let period = TickPeriod::new(10, 1).unwrap();
    /// assert_eq!(period.tick_at_or_after_from(100, 1_000_000_000, 115_200), Ok(969));
    /// assert_eq!(period.tick_at_or_after_from(100, 10_000_000_000, 115_200), Ok(8_781));
    /// assert_eq!(
    ///     period.tick_at_or_after_from(u64::MAX, 1, 1),
    ///     Err(TickTimeError::TickOutOfRange)
    /// );
    /// ```
    pub fn tick_at_or_after_from(
        &self, start: u64, numerator: u64, denominator: u64,
    ) -> (result: Result<u64, TickTimeError>)
        ensures
            result.is_ok() <==> exists|tick: u64|
                #[trigger] self.first_tick_from_start(start, numerator, denominator, tick as nat),
            result.is_ok() ==> self.first_tick_from_start(start, numerator, denominator, result.unwrap() as nat),
            result == Err(TickTimeError::ZeroDenominator) <==> denominator == 0,
            result == Err(TickTimeError::TickOutOfRange) <==> denominator > 0 && !result.is_ok(),
    {
        proof { use_type_invariant(self); }
        match self.tick_at_or_after(numerator, denominator) {
            Ok(elapsed) => {
                if let Some(tick) = start.checked_add(elapsed) {
                    assert(self.first_tick_from_start(start, numerator, denominator, tick as nat));
                    Ok(tick)
                } else {
                    proof {
                        assert forall|tick: u64| !#[trigger] self.first_tick_from_start(
                            start, numerator, denominator, tick as nat
                        ) by {
                            if self.first_tick_from_start(start, numerator, denominator, tick as nat) {
                                self.first_tick_is_unique(
                                    numerator, denominator, (tick as nat - start as nat) as nat, elapsed as nat
                                );
                            }
                        }
                    }
                    Err(TickTimeError::TickOutOfRange)
                }
            }
            Err(error) => {
                proof {
                    assert forall|tick: u64| !#[trigger] self.first_tick_from_start(
                        start, numerator, denominator, tick as nat
                    ) by {
                        if self.first_tick_from_start(start, numerator, denominator, tick as nat) {
                            if denominator > 0 {
                                let (ns_num, ns_den) = self.period();
                                let offset = tick as int - start as int;
                                let scale = denominator as int * ns_num as int;
                                lemma_mul_inequality(0, denominator as int, ns_num as int);
                                lemma_mul_inequality(offset, u64::MAX as int, scale);
                                assert(numerator as int * ns_den as int <= offset * scale);
                                assert(self.time_fits_ticks(numerator, denominator));
                            }
                        }
                    }
                }
                Err(error)
            }
        }
    }
    /// 同じ時刻に対する最初の tick 境界は一意である。
    pub proof fn first_tick_is_unique(&self, numerator: u64, denominator: u64, left: nat, right: nat)
        requires
            self.first_tick_at_or_after_time(numerator, denominator, left),
            self.first_tick_at_or_after_time(numerator, denominator, right),
        ensures left == right,
    {
        let (ns_num, _) = self.period();
        let scale = (denominator as int) * (ns_num as int);
        lemma_mul_inequality(0, denominator as int, ns_num as int);
        if left < right {
            lemma_mul_inequality(left as int, (right as int) - 1, scale);
        } else if right < left {
            lemma_mul_inequality(right as int, (left as int) - 1, scale);
        }
    }

    /// `tick-ns` の値域に入る分子と分母から1 tick の長さを作る。
    ///
    /// 値域外なら `None` を返す。
    pub fn new(numerator: u64, denominator: u64) -> (result: Option<Self>)
        ensures
            result.is_some() <==> valid_tick_period(numerator, denominator),
            result.is_some() ==> result.unwrap().period() == (numerator, denominator),
    {
        if numerator == 0 || denominator == 0
            || numerator > i64::MAX as u64 || denominator > i64::MAX as u64
        {
            None
        } else {
            Some(Self { numerator, denominator })
        }
    }

    /// 指定した時刻より早くない最初の論理 tick を返す。
    ///
    /// 時刻は `numerator / denominator` ns で渡す。有理数のまま比較するので、
    /// 時刻が tick 境界に一致するときはその tick を返す。
    ///
    /// # Errors
    ///
    /// 時刻の分母が0の場合は [`TickTimeError::ZeroDenominator`]、最初の tick が
    /// `u64` に収まらない場合は [`TickTimeError::TickOutOfRange`] を返す。
    ///
    /// # Examples
    ///
    /// UART の第 `n` ビットの境界は `n × 1_000_000_000 / baud` ns として渡す。
    /// tick に丸めるのは各境界の時刻を求めた後に行う。
    ///
    /// ```
    /// use circuitgame2_core::time::TickPeriod;
    ///
    /// let period = TickPeriod::new(10, 1).unwrap();
    /// assert_eq!(period.tick_at_or_after(1_000_000_000, 115_200), Ok(869));
    /// assert_eq!(period.tick_at_or_after(10_000_000_000, 115_200), Ok(8_681));
    /// ```
    pub fn tick_at_or_after(&self, numerator: u64, denominator: u64) -> (result: Result<u64, TickTimeError>)
        ensures
            result.is_ok() <==> self.time_fits_ticks(numerator, denominator),
            result.is_ok() ==> self.first_tick_at_or_after_time(numerator, denominator, result.unwrap() as nat),
            result == Err(TickTimeError::ZeroDenominator) <==> denominator == 0,
            result == Err(TickTimeError::TickOutOfRange)
                <==> denominator > 0 && !self.time_fits_ticks(numerator, denominator),
    {
        proof { use_type_invariant(self); }
        if denominator == 0 {
            return Err(TickTimeError::ZeroDenominator);
        }

        // 分数同士の割り算を、拡幅した二つの整数の割り算にする。
        let target = multiply_u64(numerator, self.denominator);
        let scale = multiply_u64(denominator, self.numerator);
        assert(0 < scale) by (nonlinear_arith)
            requires scale as int == (denominator as int) * (self.numerator as int),
                denominator > 0, self.numerator > 0;
        let quotient = target / scale;
        let remainder = target % scale;
        let ghost tick = if remainder == 0 { quotient as int } else { (quotient as int) + 1 };
        proof {
            let d = scale as int;
            let q = quotient as int;
            lemma_fundamental_div_mod(target as int, d);
            lemma_mod_bound(target as int, d);
            lemma_mul_is_commutative(d, q);
            assert(target as int == q * d + (remainder as int));
            if remainder == 0 {
                if quotient > 0 {
                    lemma_mul_is_distributive_sub_other_way(d, q, 1);
                }
            } else {
                lemma_mul_is_distributive_add_other_way(d, q, 1);
            }
            assert(self.first_tick_at_or_after_time(numerator, denominator, tick as nat));
            if tick <= u64::MAX {
                lemma_mul_inequality(tick, u64::MAX as int, scale as int);
            } else {
                lemma_mul_inequality(u64::MAX as int, tick - 1, scale as int);
            }
            assert(self.time_fits_ticks(numerator, denominator) <==> tick <= u64::MAX);
        }
        if quotient > u64::MAX as u128
            || (quotient == u64::MAX as u128 && remainder != 0)
        {
            return Err(TickTimeError::TickOutOfRange);
        }
        let quotient = quotient as u64;
        Ok(if remainder == 0 { quotient } else { quotient + 1 })
    }
}

fn multiply_u64(left: u64, right: u64) -> (product: u128)
    ensures product as int == (left as int) * (right as int),
{
    proof {
        lemma_mul_inequality(left as int, u64::MAX as int, right as int);
        lemma_mul_inequality(right as int, u64::MAX as int, u64::MAX as int);
        assert((u64::MAX as int) * (u64::MAX as int) <= u128::MAX as int) by (compute);
    }
    (left as u128) * (right as u128)
}

proof fn representative_tick_boundaries() {
    let period = TickPeriod { numerator: 10, denominator: 1 };
    assert(period.first_tick_at_or_after_time(0, 1, 0)) by (compute);
    assert(period.first_tick_at_or_after_time(20, 1, 2)) by (compute);
    assert(period.first_tick_at_or_after_time(1_000_000_000, 115_200, 869)) by (compute);
    assert(period.first_tick_at_or_after_time(10_000_000_000, 115_200, 8_681)) by (compute);
    assert(!period.time_fits_ticks(20, 0)) by (compute);

    assert(period.interval_spans_tick(1_000_000_000, 115_200)) by (compute);
    assert(!period.interval_spans_tick(9, 1)) by (compute);
    assert(period.interval_spans_tick(20, 2)) by (compute);
    assert(!period.interval_spans_tick(20, 0)) by (compute);
    assert(period.first_tick_from_start(100, 10_000_000_000, 115_200, 8_781)) by (compute);
    assert(!period.first_tick_from_start(100, 10_000_000_000, 115_200, 8_790)) by (compute);

    let unit = TickPeriod { numerator: 1, denominator: 1 };
    assert(unit.first_tick_at_or_after_time(u64::MAX, 1, u64::MAX as nat)) by (compute);

    // 切り捨てた商は u64::MAX でも、端数があるので境界はその次の tick となる。
    let shorter = TickPeriod { numerator: 1, denominator: 7 };
    assert(!shorter.time_fits_ticks(10_540_996_613_548_315_209, 4)) by (compute);
}

} // verus!
