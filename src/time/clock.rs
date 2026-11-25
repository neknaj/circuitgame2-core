//! tick と reset の準備および確定を扱う。

use vstd::prelude::*;

verus! {

/// 確定済みの状態や外部イベントに付ける論理時刻。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TickPosition {
    /// その状態を初期化した reset の世代。起動時は0。
    pub generation: u64,
    /// その世代で最後に確定した tick 番号。初期状態は0。
    pub tick: u64,
}

/// 論理時刻を進められなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockError {
    /// 次の tick 番号が `u64` に収まらない。
    TickOutOfRange,
    /// 次の reset 世代が `u64` に収まらない。
    GenerationOutOfRange,
    /// 準備した時点から、確定済みの論理時刻が変わった。
    StaleChange,
}

/// 最後に確定した tick と reset 世代を保持する。
///
/// 回路やデバイスの状態が確定できる段階で、論理時刻も確定する。
/// 実行側は中断した tick の変更を破棄する。reset を受け付けたときも、
/// 中断した tick の変更を取り除いてから reset を評価する。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::time::{ClockError, SimulationClock, TickPosition};
///
/// let mut clock = SimulationClock::new();
/// let old_tick = clock.prepare_tick().unwrap();
/// assert_eq!(old_tick.target(), TickPosition { generation: 0, tick: 1 });
/// assert_eq!(clock.position().tick, 0);
/// let reset = clock.prepare_reset().unwrap();
/// clock.commit(reset).unwrap();
/// assert_eq!(clock.commit(old_tick), Err(ClockError::StaleChange));
/// assert_eq!(clock.position(), TickPosition { generation: 1, tick: 0 });
/// ```
#[derive(Debug)]
pub struct SimulationClock {
    position: TickPosition,
}

/// 確定待ちの tick または reset の論理時刻。
///
/// 準備した時点の論理時刻を保持する。確定せずに破棄すれば時計は進まない。
#[derive(Debug)]
pub struct PendingClockChange {
    from: TickPosition,
    to: TickPosition,
}

/// 同一世代の次の tick か、新しい世代の tick 0 への遷移を表す。
pub open spec fn clock_change_matches(from: TickPosition, to: TickPosition) -> bool {
    ||| (to.generation == from.generation && (to.tick as int) == (from.tick as int) + 1)
    ||| ((to.generation as int) == (from.generation as int) + 1 && to.tick == 0)
}

impl PendingClockChange {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        clock_change_matches(self.from, self.to)
    }

    /// 準備を始めた論理時刻と、確定時に移る論理時刻。
    pub closed spec fn change_model(&self) -> (TickPosition, TickPosition) {
        (self.from, self.to)
    }

    /// 今回の回路・デバイスの更新に渡す予定の論理時刻。
    pub fn target(&self) -> (position: TickPosition)
        ensures position == self.change_model().1,
    {
        self.to
    }
}

impl SimulationClock {
    /// 最後に確定した論理時刻。
    pub closed spec fn position_model(&self) -> TickPosition {
        self.position
    }

    /// 起動時の論理時刻を、世代0の tick 0 に設定する。
    pub fn new() -> (clock: Self)
        ensures clock.position_model() == (TickPosition { generation: 0, tick: 0 }),
    {
        Self { position: TickPosition { generation: 0, tick: 0 } }
    }

    /// 最後に確定した論理時刻を返す。
    pub fn position(&self) -> (position: TickPosition)
        ensures position == self.position_model(),
    {
        self.position
    }

    /// 同じ reset 世代の次の tick を準備する。
    ///
    /// # Errors
    ///
    /// 現在の tick 番号が `u64::MAX` の場合はエラーを返す。
    pub fn prepare_tick(&self) -> (result: Result<PendingClockChange, ClockError>)
        ensures
            result.is_ok() <==> self.position_model().tick < u64::MAX,
            result.is_ok() ==> {
                let (from, to) = result.unwrap().change_model();
                &&& from == self.position_model()
                &&& to.generation == from.generation
                &&& to.tick as int == from.tick as int + 1
            },
            result.is_err() ==> result == Err(ClockError::TickOutOfRange),
    {
        let from = self.position;
        if from.tick == u64::MAX {
            return Err(ClockError::TickOutOfRange);
        }
        let to = TickPosition { generation: from.generation, tick: from.tick + 1 };
        Ok(PendingClockChange { from, to })
    }

    /// reset が成功した場合に使う次の世代と tick 0 を準備する。
    ///
    /// # Errors
    ///
    /// 現在の reset 世代が `u64::MAX` の場合はエラーを返す。
    pub fn prepare_reset(&self) -> (result: Result<PendingClockChange, ClockError>)
        ensures
            result.is_ok() <==> self.position_model().generation < u64::MAX,
            result.is_ok() ==> {
                let (from, to) = result.unwrap().change_model();
                &&& from == self.position_model()
                &&& to.generation as int == from.generation as int + 1
                &&& to.tick == 0
            },
            result.is_err() ==> result == Err(ClockError::GenerationOutOfRange),
    {
        let from = self.position;
        if from.generation == u64::MAX {
            return Err(ClockError::GenerationOutOfRange);
        }
        let to = TickPosition { generation: from.generation + 1, tick: 0 };
        Ok(PendingClockChange { from, to })
    }

    /// 更新結果を採用する際に、準備済みの論理時刻を確定する。
    ///
    /// 同じ実行で準備し、回路やデバイスの更新がそろった後に呼び出す。
    /// 時計は時刻で照合するため、実行インスタンスとの対応は呼び出し側が保持する。
    /// エラー時は時刻を保持する。
    ///
    /// # Errors
    ///
    /// 準備時と現在の世代または tick 番号が異なる場合は失敗する。
    pub fn commit(&mut self, change: PendingClockChange) -> (result: Result<(), ClockError>)
        ensures
            result.is_ok() <==> old(self).position_model() == change.change_model().0,
            result.is_ok() ==> {
                &&& final(self).position_model() == change.change_model().1
                &&& clock_change_matches(old(self).position_model(), final(self).position_model())
            },
            result.is_err() ==> {
                &&& result == Err(ClockError::StaleChange)
                &&& final(self).position_model() == old(self).position_model()
            },
    {
        proof { use_type_invariant(&change); }
        if self.position.tick != change.from.tick
            || self.position.generation != change.from.generation
        {
            return Err(ClockError::StaleChange);
        }
        self.position = change.to;
        Ok(())
    }
}

} // verus!
