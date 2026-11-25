//! 回路、要求台帳、応答キューを一つの実行として保持する。

use alloc::vec::Vec;
use vstd::prelude::*;

use crate::netlist::{ClockedSession, ClockedVm, PendingIoReset, PendingIoTick};
use crate::time::{ClockError, ScheduledEvent, ScheduledEvents, TickPosition};
use super::{HostRequestId, RegisterRequestError, RequestIdError, RequestIds, RequestLedger,
    ResponseTickError, ScheduleResponseError, ScheduledResponse};
#[cfg(verus_only)]
use super::{ResponseStatus, delivery_matches, response_keys, response_update};
#[cfg(verus_only)]
use crate::time::{events_at_tick, events_by_reset_generation, next_event_matches};

verus! {

type ResponseEvent<T> = ScheduledEvent<ScheduledResponse<T>>;

/// 応答を扱う一つの回路実行。
///
/// 採番、要求台帳、応答キューはこの実行が所有する。tick や reset の準備中は
/// 同じ実行に新しい要求や応答を登録できない。
pub struct DeviceResponseSession<T> {
    circuit: ClockedSession,
    ids: RequestIds,
    ledger: RequestLedger,
    events: ScheduledEvents<ScheduledResponse<T>>,
}

/// 回路を更新するまで、同じ実行の台帳と応答列を保持した tick。
pub struct PendingDeviceTick<'a, T> {
    tick: PendingIoTick<'a, ScheduledResponse<T>>,
    ledger: &'a mut RequestLedger,
}

/// 次の世代をデバイスへ通知し、回路と要求の状態を後で初期化するための準備。
pub struct PendingDeviceReset<'a, T> {
    reset: PendingIoReset<'a, ScheduledResponse<T>>,
    ledger: &'a mut RequestLedger,
    ids: &'a mut RequestIds,
}

/// 確定済み tick の要求を登録できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RequestIssueError {
    /// tick 0 の初期状態では要求を発行できない。
    BeforeFirstTick,
    /// 通し番号を確保できない。
    Number(RequestIdError),
    /// 台帳に要求を追加できない。
    Registration(RegisterRequestError),
}

impl<T> DeviceResponseSession<T> {
    /// 現在の回路、台帳、応答列。
    pub closed spec fn model(&self) -> (ClockedSession, RequestLedger, Seq<ResponseEvent<T>>) {
        (self.circuit, self.ledger, self.events.model())
    }

    /// 現在の採番状態。
    pub closed spec fn ids_model(&self) -> RequestIds { self.ids }

    /// 回路と要求管理が同じ世代にあり、次の更新を準備できることを表す。
    pub open spec fn valid(&self) -> bool {
        let (circuit, ledger, _) = self.model();
        &&& circuit.valid()
        &&& circuit.position_model().generation == ledger.generation_model()
        &&& circuit.position_model().generation == self.ids_model().generation_model()
    }

    /// 検査済みの回路 VM を受け取り、世代0の tick 0 から実行を始める。
    pub fn new(vm: ClockedVm) -> (session: Self)
        requires vm.valid(),
        ensures
            session.valid(),
            session.model().0.position_model() == (TickPosition { generation: 0, tick: 0 }),
            session.model().0.vm_model().same_layout(&vm),
            session.model().0.vm_model().reset_matches(session.model().0.output_model()),
            session.ids_model().next_model() == 0,
            session.model().1.requests().len() == 0,
            session.model().2.len() == 0,
    {
        Self {
            circuit: ClockedSession::new(vm),
            ids: RequestIds::new(0),
            ledger: RequestLedger::new(0),
            events: ScheduledEvents::new(),
        }
    }

    /// 最後に確定した世代と tick を返す。
    pub fn position(&self) -> (position: TickPosition)
        ensures position == self.model().0.position_model(),
    {
        self.circuit.position()
    }

    /// 確定した tick で発行する要求を、同じ実行の台帳に登録する。
    ///
    /// 採番や台帳の検査に失敗した場合は、次の番号と台帳を保持する。
    ///
    /// # Errors
    ///
    /// tick 0 では発行できない。以降は番号の枯渇、台帳への登録の順に検査する。
    pub fn issue_request(&mut self, instance: usize, tag: u64) -> (result: Result<HostRequestId, RequestIssueError>)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            final(self).model().0 == old(self).model().0,
            final(self).model().2 == old(self).model().2,
            result.is_err() ==> final(self).model() == old(self).model()
                && final(self).ids_model() == old(self).ids_model(),
            result == Err(RequestIssueError::BeforeFirstTick) <==> old(self).model().0.position_model().tick == 0,
            result == Err(RequestIssueError::Number(RequestIdError::SerialOutOfRange)) <==>
                old(self).model().0.position_model().tick > 0 && !old(self).ids_model().fits(1),
            result.is_ok() <==> {
                let current = old(self).model().0.position_model();
                let id = HostRequestId { instance, generation: current.generation,
                    serial: old(self).ids_model().next_model() as u64 };
                &&& current.tick > 0
                &&& old(self).ids_model().fits(1)
                &&& old(self).model().1.registration_error(id, tag, current.tick).is_none()
            },
            result matches Err(RequestIssueError::Registration(error)) ==> {
                let current = old(self).model().0.position_model();
                let id = HostRequestId { instance, generation: current.generation,
                    serial: old(self).ids_model().next_model() as u64 };
                &&& current.tick > 0
                &&& old(self).ids_model().fits(1)
                &&& old(self).model().1.registration_error(id, tag, current.tick) == Some(error)
            },
            result matches Ok(id) ==> {
                let current = old(self).model().0.position_model();
                &&& id.instance == instance
                &&& id.generation == current.generation
                &&& id.serial as int == old(self).ids_model().next_model()
                &&& final(self).ids_model().next_model() == id.serial as int + 1
                &&& final(self).model().1.requests().len() == old(self).model().1.requests().len() + 1
                &&& final(self).model().1.requests().drop_last() == old(self).model().1.requests()
                &&& final(self).model().1.requests().last().0 == id
                &&& final(self).model().1.requests().last().1 == tag
                &&& final(self).model().1.requests().last().2.issued_model() == current.tick
                &&& final(self).model().1.requests().last().2.status_model() == ResponseStatus::Awaiting
            },
    {
        let current = self.circuit.position();
        if current.tick == 0 { return Err(RequestIssueError::BeforeFirstTick); }
        let pending = match self.ids.prepare(1) {
            Ok(pending) => pending,
            Err(error) => return Err(RequestIssueError::Number(error)),
        };
        let id = pending.first_id(instance);
        if let Err(error) = self.ledger.register(id, tag, current.tick) {
            pending.cancel();
            return Err(RequestIssueError::Registration(error));
        }
        pending.commit();
        Ok(id)
    }

    /// 照合した応答を、この実行の未開始 tick に予約する。
    ///
    /// 呼び出し側は先にデバイスの記述に従って payload を検査する。
    ///
    /// # Errors
    ///
    /// [`ClockedSession::schedule_response`] の規則で診断する。エラー時は実行状態を保持する。
    pub fn schedule_response(&mut self, id: HostRequestId, delivery: TickPosition, payload: T)
        -> (result: Result<(), ScheduleResponseError>)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            final(self).ids_model() == old(self).ids_model(),
            final(self).model().0 == old(self).model().0,
            result.is_err() ==> final(self).model() == old(self).model()
                && final(self).ids_model() == old(self).ids_model(),
            result == Err(ScheduleResponseError::DifferentGeneration) <==>
                delivery.generation != old(self).model().0.position_model().generation,
            result == Err(ScheduleResponseError::AlreadyCommitted) <==>
                delivery.generation == old(self).model().0.position_model().generation
                && delivery.tick <= old(self).model().0.position_model().tick,
            result matches Err(ScheduleResponseError::Response(error)) ==> {
                let (circuit, ledger, _) = old(self).model();
                &&& delivery.generation == circuit.position_model().generation
                &&& delivery.tick > circuit.position_model().tick
                &&& ledger.rejects_response(id, delivery, error)
            },
            result.is_ok() <==> {
                let (circuit, ledger, _) = old(self).model();
                &&& delivery.generation == circuit.position_model().generation
                &&& delivery.tick > circuit.position_model().tick
                &&& ledger.accepts_response(id, delivery)
            },
            result.is_ok() ==> {
                &&& final(self).model().2.len() == old(self).model().2.len() + 1
                &&& final(self).model().2.drop_last() == old(self).model().2
                &&& final(self).model().2.last().position == delivery
                &&& final(self).model().2.last().payload.model().0 == id
                &&& final(self).model().2.last().payload.model().2 == payload
                &&& exists|i: int| #[trigger] old(self).model().1.found_request(id, i) && response_update(
                    old(self).model().1.requests(), final(self).model().1.requests(), i,
                    ResponseStatus::Awaiting, ResponseStatus::Held(delivery),
                    final(self).model().2.last().payload.model().1,
                )
            },
    {
        self.circuit.schedule_response(&mut self.ledger, &mut self.events, id, delivery, payload)
    }

    /// 回路と台帳を一緒に借り、次の tick の応答列を固定する。
    ///
    /// # Errors
    ///
    /// tick 番号が上限なら、状態を保持してエラーを返す。
    pub fn prepare_tick(&mut self) -> (result: Result<PendingDeviceTick<'_, T>, ClockError>)
        requires old(self).valid(),
        ensures
            final(self).ids_model() == old(self).ids_model(),
            result.is_ok() <==> old(self).model().0.position_model().tick < u64::MAX,
            result matches Ok(pending) ==> {
                &&& pending.before_model() == old(self).model()
                &&& pending.after_model() == final(self).model()
                &&& pending.target_model().tick as int == old(self).model().0.position_model().tick as int + 1
                &&& pending.target_model().generation == old(self).model().0.position_model().generation
            },
            result matches Err(error) ==> error == ClockError::TickOutOfRange
                && final(self).model() == old(self).model(),
    {
        let tick = self.circuit.prepare_io_tick(&mut self.events)?;
        Ok(PendingDeviceTick { tick, ledger: &mut self.ledger })
    }

    /// 次の世代を準備し、各デバイスを初期化する間は現在の状態を保持する。
    ///
    /// # Errors
    ///
    /// 世代番号が上限なら、状態を保持してエラーを返す。
    pub fn prepare_reset(&mut self) -> (result: Result<PendingDeviceReset<'_, T>, ClockError>)
        requires old(self).valid(),
        ensures
            result.is_ok() <==> old(self).model().0.position_model().generation < u64::MAX,
            result matches Ok(pending) ==> {
                &&& pending.before_model() == (old(self).model(), old(self).ids_model())
                &&& pending.after_model() == (final(self).model(), final(self).ids_model())
                &&& pending.target_model().generation as int == old(self).model().0.position_model().generation as int + 1
                &&& pending.target_model().tick == 0
            },
            result matches Err(error) ==> error == ClockError::GenerationOutOfRange
                && final(self).model() == old(self).model()
                && final(self).ids_model() == old(self).ids_model(),
    {
        let reset = self.circuit.prepare_io_reset(&mut self.events)?;
        Ok(PendingDeviceReset { reset, ledger: &mut self.ledger, ids: &mut self.ids })
    }
}

impl<'a, T> PendingDeviceTick<'a, T> {
    /// 準備前の回路、台帳、応答列。
    pub closed spec fn before_model(&self) -> (ClockedSession, RequestLedger, Seq<ResponseEvent<T>>) {
        (self.tick.before_circuit(), *self.ledger, self.tick.before_events())
    }

    /// 確定または取り消し後の回路、台帳、応答列。
    #[verifier::prophetic]
    pub closed spec fn after_model(&self) -> (ClockedSession, RequestLedger, Seq<ResponseEvent<T>>) {
        (self.tick.after_circuit(), *final(self.ledger), self.tick.after_events())
    }

    /// 確定予定の論理時刻。
    pub closed spec fn target_model(&self) -> TickPosition { self.tick.target_model() }

    /// 確定予定の世代と tick を返す。
    pub fn target(&self) -> (position: TickPosition)
        ensures position == self.target_model(),
    {
        self.tick.target()
    }

    /// 直前の tick で確定した出力を返す。
    pub fn previous_output(&self) -> (output: &[bool])
        ensures output@ == self.before_model().0.output_model(),
    {
        self.tick.previous_output()
    }

    /// 開始時の列で指定添字以降にある最初の対象応答を返す。
    pub fn next_response(&self, from: usize) -> (result: Option<(usize, &ResponseEvent<T>)>)
        ensures next_event_matches(self.before_model().2, self.target_model(), from, result),
    {
        self.tick.next_event(from)
    }

    /// 回路と論理時刻を進め、対象応答だけを同じ実行の台帳から消費する。
    ///
    /// # Errors
    ///
    /// 配送または入力幅のエラーでは回路、台帳、応答列を保持する。
    pub fn commit(self, input: &[bool]) -> (result: Result<Vec<ResponseEvent<T>>, ResponseTickError>)
        ensures
            self.before_model().0.valid() ==> self.after_model().0.valid(),
            self.after_model().1.generation_model() == self.before_model().1.generation_model(),
            result.is_ok() <==>
                self.before_model().1.valid_delivery(response_keys(self.before_model().2, self.target_model()), self.target_model())
                && input@.len() == self.before_model().0.vm_model().external_count(),
            result matches Err(ResponseTickError::Delivery(error)) ==> self.before_model().1.first_delivery_error(
                response_keys(self.before_model().2, self.target_model()), self.target_model(), error),
            result matches Err(ResponseTickError::Input(error)) ==>
                self.before_model().1.valid_delivery(response_keys(self.before_model().2, self.target_model()), self.target_model())
                && input@.len() != self.before_model().0.vm_model().external_count()
                && error == crate::netlist::TickInputError::InputCount,
            result.is_err() ==> self.after_model() == self.before_model(),
            result matches Ok(consumed) ==> {
                let (before, prior_ledger, events) = self.before_model();
                let (after, updated_ledger, remaining) = self.after_model();
                let target = self.target_model();
                &&& after.position_model() == target
                &&& after.vm_model().tick_matches(&before.vm_model(), input@, after.output_model())
                &&& remaining == events_at_tick(events, target, false)
                &&& consumed@ == events_at_tick(events, target, true)
                &&& delivery_matches(prior_ledger.requests(), updated_ledger.requests(), response_keys(events, target), target)
            },
    {
        let Self { tick, ledger } = self;
        tick.commit_responses(ledger, input)
    }

    /// 更新を取り消し、回路、時刻、台帳、応答列を保持する。
    pub fn cancel(self)
        ensures self.after_model() == self.before_model(),
    {
        self.tick.cancel();
    }
}

impl<'a, T> PendingDeviceReset<'a, T> {
    /// 準備前の回路と要求管理の状態。
    pub closed spec fn before_model(&self)
        -> ((ClockedSession, RequestLedger, Seq<ResponseEvent<T>>), RequestIds) {
        ((self.reset.before_circuit(), *self.ledger, self.reset.before_events()), *self.ids)
    }

    /// 確定または取り消し後の回路と要求管理の状態。
    #[verifier::prophetic]
    pub closed spec fn after_model(&self)
        -> ((ClockedSession, RequestLedger, Seq<ResponseEvent<T>>), RequestIds) {
        ((self.reset.after_circuit(), *final(self.ledger), self.reset.after_events()), *final(self.ids))
    }

    /// 次の世代の tick 0。
    pub closed spec fn target_model(&self) -> TickPosition { self.reset.target_model() }

    /// デバイスの初期化に渡す次世代の tick 0。
    pub fn target(&self) -> (position: TickPosition)
        ensures position == self.target_model(), position.tick == 0,
    {
        self.reset.target()
    }

    /// 全デバイスの初期化が成功した後に、回路、採番、台帳を新世代へ移す。
    ///
    /// 期限切れの応答を到着順に返す。
    pub fn commit(self) -> (removed: Vec<ResponseEvent<T>>)
        ensures
            self.after_model().0.0.valid(),
            self.after_model().0.0.position_model() == self.target_model(),
            self.after_model().0.0.vm_model().same_layout(&self.before_model().0.0.vm_model()),
            self.after_model().0.0.vm_model().reset_matches(self.after_model().0.0.output_model()),
            self.after_model().0.1.generation_model() == self.target_model().generation,
            self.after_model().0.1.requests().len() == 0,
            self.after_model().1.generation_model() == self.target_model().generation,
            self.after_model().1.next_model() == 0,
            self.after_model().0.2 == events_by_reset_generation(self.before_model().0.2, self.target_model().generation, false),
            removed@ == events_by_reset_generation(self.before_model().0.2, self.target_model().generation, true),
    {
        let Self { reset, ledger, ids } = self;
        let target = reset.target();
        let removed = reset.commit();
        *ledger = RequestLedger::new(target.generation);
        *ids = RequestIds::new(target.generation);
        removed
    }

    /// デバイスの初期化が失敗した場合などに、現在の実行を保持する。
    pub fn cancel(self)
        ensures self.after_model() == self.before_model(),
    {
        self.reset.cancel();
    }
}

} // verus!
