//! 外部イベントの消費を回路の tick 確定に結び付ける。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{ClockedSession, PendingVmTick, TickInputError};
use crate::time::{ClockError, PendingEvents, ScheduledEvent, ScheduledEvents, TickPosition};
#[cfg(verus_only)]
use crate::time::{events_at_tick, events_by_reset_generation, next_event_matches};

verus! {

/// 回路が確定するまで、対象 tick のイベントを未消費のまま保持する。
///
/// デバイスの状態遷移には [`Self::previous_output`] と [`Self::next_event`] を渡す。
/// 評価の中断や失敗により更新を破棄するときは [`Self::cancel`] を呼ぶ。
pub struct PendingIoTick<'a, T> {
    circuit: PendingVmTick<'a>,
    events: PendingEvents<'a, T>,
}

impl ClockedSession {
    /// 1回の回路更新を準備し、その tick に渡す外部イベントの集合を固定する。
    ///
    /// 回路とイベント列を排他的に借りる。評価を再開する場合は同じ準備結果を使う。
    ///
    /// # Errors
    ///
    /// tick 番号が上限に達していれば、回路とイベント列を保持してエラーを返す。
    pub fn prepare_io_tick<'a, T>(&'a mut self, events: &'a mut ScheduledEvents<T>)
        -> (result: Result<PendingIoTick<'a, T>, ClockError>)
        requires old(self).valid(),
        ensures
            result.is_ok() <==> old(self).position_model().tick < u64::MAX,
            match result {
                Ok(pending) => {
                    &&& pending.before_circuit() == *old(self)
                    &&& pending.after_circuit() == *final(self)
                    &&& pending.before_events() == old(events).model()
                    &&& pending.after_events() == final(events).model()
                    &&& pending.target_model().generation == old(self).position_model().generation
                    &&& pending.target_model().tick as int == old(self).position_model().tick as int + 1
                },
                Err(error) => error == ClockError::TickOutOfRange
                    && *final(self) == *old(self) && final(events).model() == old(events).model(),
            },
    {
        let circuit = self.prepare_tick()?;
        let target = circuit.target();
        Ok(PendingIoTick { circuit, events: events.prepare(target) })
    }

    /// 回路を新しい世代の tick 0 に戻し、旧世代の待ちイベントを取り出す。
    ///
    /// デバイスの初期化がすべて成功した後に呼び出す。評価中の tick は先に取り消す。
    /// 新しい世代以降に指定されたイベントを到着順のまま保持する。
    ///
    /// # Errors
    ///
    /// 世代番号が上限に達していれば、回路とイベント列を保持してエラーを返す。
    pub fn reset_io<T>(&mut self, events: &mut ScheduledEvents<T>)
        -> (result: Result<Vec<ScheduledEvent<T>>, ClockError>)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            result.is_ok() <==> old(self).position_model().generation < u64::MAX,
            match result {
                Ok(removed) => {
                    let generation = final(self).position_model().generation;
                    &&& generation as int == old(self).position_model().generation as int + 1
                    &&& final(self).position_model().tick == 0
                    &&& final(self).vm_model().same_layout(&old(self).vm_model())
                    &&& final(self).vm_model().reset_matches(final(self).output_model())
                    &&& final(events).model() == events_by_reset_generation(old(events).model(), generation, false)
                    &&& removed@ == events_by_reset_generation(old(events).model(), generation, true)
                },
                Err(error) => error == ClockError::GenerationOutOfRange
                    && *final(self) == *old(self) && final(events).model() == old(events).model(),
            },
    {
        self.reset()?;
        Ok(events.take_older_generations(self.position().generation))
    }
}

impl<'a, T> PendingIoTick<'a, T> {
    #[verifier::type_invariant]
    spec fn same_target(&self) -> bool {
        self.circuit.target_model() == self.events.target_model()
    }

    /// 準備中に観測できる確定済みの回路状態。
    pub closed spec fn before_circuit(&self) -> ClockedSession { self.circuit.before_model() }

    /// 確定または取り消しの後の回路状態。
    #[verifier::prophetic]
    pub closed spec fn after_circuit(&self) -> ClockedSession { self.circuit.after_model() }

    /// 評価を始める時点の未消費イベント列。
    pub closed spec fn before_events(&self) -> Seq<ScheduledEvent<T>> { self.events.before_model() }

    /// 確定または取り消しの後の未消費イベント列。
    #[verifier::prophetic]
    pub closed spec fn after_events(&self) -> Seq<ScheduledEvent<T>> { self.events.after_model() }

    /// 評価対象の論理時刻。
    pub closed spec fn target_model(&self) -> TickPosition { self.circuit.target_model() }

    /// 更新が成功した後の世代および tick 番号を返す。
    pub fn target(&self) -> (target: TickPosition)
        ensures target == self.target_model(),
    {
        self.circuit.target()
    }

    /// 直前の tick で確定した回路出力をポートのビット順で返す。
    pub fn previous_output(&self) -> (output: &[bool])
        ensures output@ == self.before_circuit().output_model(),
    {
        self.circuit.previous_output()
    }

    /// `from` 以降の最初の対象イベントと、開始時の列での添字を返す。
    ///
    /// 次のイベントを読むときは、返った添字の次から探す。
    pub fn next_event(&self, from: usize) -> (result: Option<(usize, &ScheduledEvent<T>)>)
        ensures next_event_matches(self.before_events(), self.target_model(), from, result),
    {
        proof { use_type_invariant(self); }
        self.events.next_ready(from)
    }

    /// 回路の更新が成功した場合に時刻、出力、イベント消費を確定する。
    ///
    /// 成功時は、今回取り出したイベントを到着順のまま返す。
    ///
    /// # Errors
    ///
    /// 外部入力のビット数が違う場合は、回路とイベント列を保持してエラーを返す。
    pub fn commit(self, input: &[bool]) -> (result: Result<Vec<ScheduledEvent<T>>, TickInputError>)
        ensures
            self.after_circuit().valid(),
            result.is_ok() <==> input@.len() == self.before_circuit().vm_model().external_count(),
            match result {
                Ok(consumed) => {
                    &&& self.after_circuit().position_model() == self.target_model()
                    &&& self.after_circuit().vm_model().tick_matches(
                        &self.before_circuit().vm_model(), input@, self.after_circuit().output_model())
                    &&& self.after_events() == events_at_tick(self.before_events(), self.target_model(), false)
                    &&& consumed@ == events_at_tick(self.before_events(), self.target_model(), true)
                },
                Err(error) => error == TickInputError::InputCount
                    && self.after_circuit() == self.before_circuit()
                    && self.after_events() == self.before_events(),
            },
    {
        proof { use_type_invariant(&self); }
        let Self { circuit, events } = self;
        match circuit.commit(input) {
            Ok(()) => Ok(events.commit()),
            Err(error) => {
                events.cancel();
                Err(error)
            },
        }
    }

    /// 更新を取り消し、回路、時刻、出力、イベント列を保持する。
    pub fn cancel(self)
        ensures self.after_circuit() == self.before_circuit(),
            self.after_events() == self.before_events(),
    {
        let Self { circuit, events } = self;
        circuit.cancel();
        events.cancel();
    }
}

} // verus!
