//! 外部 I/O が観測する、確定済みの回路出力と論理時刻を管理する。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{ClockedVm, TickInputError};
use crate::time::{ClockError, PendingClockChange, SimulationClock, TickPosition};

verus! {

/// 回路 VM と、最後に確定した論理時刻および公開出力。
pub struct ClockedSession {
    vm: ClockedVm,
    clock: SimulationClock,
    output: Vec<bool>,
}

/// 1回の tick 更新を準備した回路実行。
///
/// 準備時に回路実行を排他的に借りる。確定せずに破棄した場合、時刻と回路の状態を保つ。
pub struct PendingVmTick<'a> {
    session: &'a mut ClockedSession,
    change: PendingClockChange,
}

impl ClockedSession {
    /// 回路 VM が初期化済みで、更新できることを表す。
    pub closed spec fn valid(&self) -> bool {
        self.vm.valid()
    }

    /// 最後に確定した論理時刻。
    pub closed spec fn position_model(&self) -> TickPosition { self.clock.position_model() }

    /// 最後に確定した出力ビット列。
    pub closed spec fn output_model(&self) -> Seq<bool> { self.output@ }

    /// 最後に確定した回路 VM。
    pub closed spec fn vm_model(&self) -> ClockedVm { self.vm }

    /// 検査済みの回路 VM を初期化し、世代0の tick 0 の状態から実行を始める。
    pub fn new(mut vm: ClockedVm) -> (session: Self)
        requires vm.valid(),
        ensures
            session.valid(),
            session.position_model() == (TickPosition { generation: 0, tick: 0 }),
            session.vm_model().same_layout(&vm),
            session.vm_model().reset_matches(session.output_model()),
    {
        let output = vm.reset();
        Self { vm, clock: SimulationClock::new(), output }
    }

    /// 最後に確定した論理時刻を返す。
    pub fn position(&self) -> (position: TickPosition)
        ensures position == self.position_model(),
    {
        self.clock.position()
    }

    /// 最後に確定した公開出力をポートのビット順に返す。
    pub fn output(&self) -> (output: &[bool])
        ensures output@ == self.output_model(),
    {
        self.output.as_slice()
    }

    /// 現在の状態を保ったまま、次の tick の更新を準備する。
    ///
    /// # Errors
    ///
    /// tick 番号が上限に達していれば、時刻と回路を保持してエラーを返す。
    pub fn prepare_tick(&mut self) -> (result: Result<PendingVmTick<'_>, ClockError>)
        requires old(self).valid(),
        ensures
            result.is_ok() <==> old(self).position_model().tick < u64::MAX,
            match result {
                Ok(pending) => {
                    &&& pending.before_model() == *old(self)
                    &&& pending.after_model() == *final(self)
                    &&& pending.target_model().generation == old(self).position_model().generation
                    &&& pending.target_model().tick as int == old(self).position_model().tick as int + 1
                },
                Err(error) => error == ClockError::TickOutOfRange && *final(self) == *old(self),
            },
    {
        let change = self.clock.prepare_tick()?;
        Ok(PendingVmTick { session: self, change })
    }

    /// 回路を初期化して reset 世代を進め、tick 0 の公開出力に更新する。
    ///
    /// # Errors
    ///
    /// 世代番号が上限に達していれば、時刻と回路を保持してエラーを返す。
    pub fn reset(&mut self) -> (result: Result<(), ClockError>)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            result.is_ok() <==> old(self).position_model().generation < u64::MAX,
            result.is_ok() ==> {
                &&& final(self).position_model().generation as int
                    == old(self).position_model().generation as int + 1
                &&& final(self).position_model().tick == 0
                &&& final(self).vm_model().same_layout(&old(self).vm_model())
                &&& final(self).vm_model().reset_matches(final(self).output_model())
            },
            result.is_err() ==> result == Err(ClockError::GenerationOutOfRange) && *final(self) == *old(self),
    {
        let change = self.clock.prepare_reset()?;
        self.output = self.vm.reset();
        self.clock.commit_current(change);
        Ok(())
    }
}

impl<'a> PendingVmTick<'a> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        self.session.valid() && self.session.position_model() == self.change.change_model().0
    }

    /// 準備中に観測する確定済みの回路状態。
    pub closed spec fn before_model(&self) -> ClockedSession { *self.session }

    /// 準備を終えた後の回路状態。
    #[verifier::prophetic]
    pub closed spec fn after_model(&self) -> ClockedSession { *final(self.session) }

    /// 確定したときに進む時刻。
    pub closed spec fn target_model(&self) -> TickPosition { self.change.change_model().1 }

    /// 確定後の論理時刻を返す。
    pub fn target(&self) -> (position: TickPosition)
        ensures position == self.target_model(),
    {
        self.change.target()
    }

    /// デバイスの遷移が読む、前の tick で確定した公開出力を返す。
    pub fn previous_output(&self) -> (output: &[bool])
        ensures output@ == self.before_model().output_model(),
    {
        self.session.output()
    }

    /// 外部入力による回路更新が成功した場合に、時刻と公開出力も一緒に確定する。
    ///
    /// # Errors
    ///
    /// 外部入力のビット数が違う場合は、時刻と回路を保持してエラーを返す。
    pub fn commit(self, input: &[bool]) -> (result: Result<(), TickInputError>)
        ensures
            self.after_model().valid(),
            result.is_ok() <==> input@.len() == self.before_model().vm_model().external_count(),
            result.is_ok() ==> {
                &&& self.after_model().position_model() == self.target_model()
                &&& self.after_model().vm_model().tick_matches(
                    &self.before_model().vm_model(), input@, self.after_model().output_model())
            },
            result.is_err() ==> self.after_model() == self.before_model()
                && result == Err(TickInputError::InputCount),
    {
        proof { use_type_invariant(&self); }
        let session = self.session;
        let output = session.vm.step(input)?;
        session.output = output;
        session.clock.commit_current(self.change);
        Ok(())
    }

    /// 今回の更新を取り消し、時刻と回路を保持する。
    pub fn cancel(self)
        ensures self.after_model() == self.before_model(),
    {
    }
}

} // verus!
