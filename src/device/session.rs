//! 回路、要求台帳、応答キューを一つの実行として保持する。

use alloc::vec::Vec;
use vstd::prelude::*;

use crate::netlist::{ClockedSession, ClockedVm, PendingIoReset, PendingIoTick};
use super::scheduling::{QueuedResponse, commit_queued_events};
use super::{DeviceEvent, ScheduleInputError};
use crate::time::{ClockError, ScheduledEvent, ScheduledEvents, TickPosition};
use super::{BatchRegistrationError, HostRequestId, IssuedRequestIds, RegisterRequestError, RequestIdError, RequestIds, RequestKey, RequestLedger,
    ResponseTickError, ScheduleResponseError, ScheduledResponse};
#[cfg(verus_only)]
use super::{ResponseStatus, first_batch_request_error, delivery_matches, issued_rows_match, queued_response_keys, response_update, valid_request_batch};
#[cfg(verus_only)]
use crate::time::{events_at_tick, events_by_reset_generation, next_event_matches};

verus! {

type SessionEvent<E> = ScheduledEvent<E>;

/// 照合済み応答だけを受け取る実行セッション。
pub type DeviceResponseSession<R> = DeviceSession<ScheduledResponse<R>>;

/// 外部入力と照合済み応答を同じ列で受け取る実行セッション。
pub type DeviceEventSession<I, R> = DeviceSession<DeviceEvent<I, R>>;

/// 応答専用の実行で準備した tick。
pub type PendingDeviceTick<'a, R> = PendingDeviceEvents<'a, ScheduledResponse<R>>;

/// 応答専用の実行で準備した reset。
pub type PendingDeviceReset<'a, R> = PendingDeviceEventsReset<'a, ScheduledResponse<R>>;

/// 応答を扱う一つの回路実行。
///
/// 採番、要求台帳、応答キューはこの実行が所有する。tick や reset の準備中は
/// 同じ実行に新しい要求や応答を登録できない。
pub struct DeviceSession<E> {
    circuit: ClockedSession,
    ids: RequestIds,
    ledger: RequestLedger,
    events: ScheduledEvents<E>,
}

/// 回路を更新するまで、同じ実行の台帳と応答列を保持した tick。
pub struct PendingDeviceEvents<'a, E> {
    tick: PendingIoTick<'a, E>,
    ledger: &'a mut RequestLedger,
    ids: &'a mut RequestIds,
}

/// 次の世代をデバイスへ通知し、回路と要求の状態を後で初期化するための準備。
pub struct PendingDeviceEventsReset<'a, E> {
    reset: PendingIoReset<'a, E>,
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

/// 新規要求を伴う tick を確定できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RequestBatchTickError {
    /// 発行順に割り当てる通し番号が不足した。
    Number(RequestIdError),
    /// 発行予定の要求を検査できなかった。
    Registration(BatchRegistrationError),
    /// 回路入力または受信予定の応答に問題があった。
    Tick(ResponseTickError),
}

impl<E: QueuedResponse> DeviceSession<E> {
    /// 現在の回路、台帳、応答列。
    pub closed spec fn model(&self) -> (ClockedSession, RequestLedger, Seq<SessionEvent<E>>) {
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

    /// 最後に確定した回路の公開出力を、ポートのビット順に借りる。
    pub fn output(&self) -> (bits: &[bool])
        ensures bits@ == self.model().0.output_model(),
    {
        self.circuit.output()
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
        let Some(id) = pending.proposed_id(0, instance) else { unreachable!() };
        if let Err(error) = self.ledger.register(id, tag, current.tick) {
            pending.cancel();
            return Err(RequestIssueError::Registration(error));
        }
        pending.commit();
        Ok(id)
    }

    /// 回路と台帳を一緒に借り、次の tick のイベント列を固定する。
    ///
    /// # Errors
    ///
    /// tick 番号が上限なら、状態を保持してエラーを返す。
    pub fn prepare_tick(&mut self) -> (result: Result<PendingDeviceEvents<'_, E>, ClockError>)
        requires old(self).valid(),
        ensures
            result.is_err() ==> final(self).ids_model() == old(self).ids_model(),
            result.is_ok() <==> old(self).model().0.position_model().tick < u64::MAX,
            result matches Ok(pending) ==> {
                &&& pending.before_model() == old(self).model()
                &&& pending.after_model() == final(self).model()
                &&& pending.before_ids() == old(self).ids_model()
                &&& pending.after_ids() == final(self).ids_model()
                &&& pending.target_model().tick as int == old(self).model().0.position_model().tick as int + 1
                &&& pending.target_model().generation == old(self).model().0.position_model().generation
            },
            result matches Err(error) ==> error == ClockError::TickOutOfRange
                && final(self).model() == old(self).model(),
    {
        let tick = self.circuit.prepare_io_tick(&mut self.events)?;
        Ok(PendingDeviceEvents { tick, ledger: &mut self.ledger, ids: &mut self.ids })
    }

    /// 次の世代を準備し、各デバイスを初期化する間は現在の状態を保持する。
    ///
    /// # Errors
    ///
    /// 世代番号が上限なら、状態を保持してエラーを返す。
    pub fn prepare_reset(&mut self) -> (result: Result<PendingDeviceEventsReset<'_, E>, ClockError>)
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
        Ok(PendingDeviceEventsReset { reset, ledger: &mut self.ledger, ids: &mut self.ids })
    }
}

impl<T> DeviceSession<ScheduledResponse<T>> {
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
}

impl<I, R> DeviceSession<DeviceEvent<I, R>> {
    /// 外部入力を、この実行の未開始 tick に予約する。
    ///
    /// インスタンスが入力を受け付けることと、payload が種別に対応することは呼び出し側で確認する。
    ///
    /// # Errors
    ///
    /// 異なる世代や確定済みの tick を指定したときは、実行状態を保持する。
    pub fn schedule_input(&mut self, instance: usize, delivery: TickPosition, payload: I)
        -> (result: Result<(), ScheduleInputError>)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            final(self).ids_model() == old(self).ids_model(),
            final(self).model().0 == old(self).model().0,
            final(self).model().1 == old(self).model().1,
            result.is_err() ==> final(self).model() == old(self).model(),
            result == Err(ScheduleInputError::DifferentGeneration) <==>
                delivery.generation != old(self).model().0.position_model().generation,
            result == Err(ScheduleInputError::AlreadyCommitted) <==>
                delivery.generation == old(self).model().0.position_model().generation
                && delivery.tick <= old(self).model().0.position_model().tick,
            result.is_ok() ==> final(self).model().2 == old(self).model().2.push(ScheduledEvent {
                position: delivery, payload: DeviceEvent::Input { instance, payload },
            }),
    {
        self.circuit.schedule_device_input(&mut self.events, instance, delivery, payload)
    }

    /// 照合した応答を、この実行の未開始 tick に予約する。
    ///
    /// 呼び出し側は先にデバイスの記述に従って payload を検査する。
    ///
    /// # Errors
    ///
    /// [`ClockedSession::schedule_device_response`] の規則で診断する。エラー時は実行状態を保持する。
    pub fn schedule_response(&mut self, id: HostRequestId, delivery: TickPosition, payload: R)
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
                &&& match final(self).model().2.last().payload {
                    DeviceEvent::Response(response) => {
                        &&& response.model().0 == id
                        &&& response.model().2 == payload
                        &&& exists|i: int| #[trigger] old(self).model().1.found_request(id, i) && response_update(
                            old(self).model().1.requests(), final(self).model().1.requests(), i,
                            ResponseStatus::Awaiting, ResponseStatus::Held(delivery), response.model().1,
                        )
                    },
                    DeviceEvent::Input { .. } => false,
                }
            },
    {
        self.circuit.schedule_device_response(&mut self.ledger, &mut self.events, id, delivery, payload)
    }
}

impl<'a, E: QueuedResponse> PendingDeviceEvents<'a, E> {
    /// 準備前の回路、台帳、イベント列。
    pub closed spec fn before_model(&self) -> (ClockedSession, RequestLedger, Seq<SessionEvent<E>>) {
        (self.tick.before_circuit(), *self.ledger, self.tick.before_events())
    }

    /// 確定または取り消し後の回路、台帳、イベント列。
    #[verifier::prophetic]
    pub closed spec fn after_model(&self) -> (ClockedSession, RequestLedger, Seq<SessionEvent<E>>) {
        (self.tick.after_circuit(), *final(self.ledger), self.tick.after_events())
    }

    /// 確定前の採番状態。
    pub closed spec fn before_ids(&self) -> RequestIds { *self.ids }

    /// 確定または取り消し後の採番状態。
    #[verifier::prophetic]
    pub closed spec fn after_ids(&self) -> RequestIds { *final(self.ids) }

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

    /// 開始時の列で指定添字以降にある最初の対象イベントを返す。
    pub fn next_event(&self, from: usize) -> (result: Option<(usize, &SessionEvent<E>)>)
        ensures next_event_matches(self.before_model().2, self.target_model(), from, result),
    {
        self.tick.next_event(from)
    }

    /// 回路と論理時刻を進め、対象イベントを到着順で消費する。
    ///
    /// # Errors
    ///
    /// 配送または入力幅のエラーでは、回路、台帳、イベント列を保持する。
    /// 配送エラーの添字は、対象 tick の応答だけを数えた位置を指す。
    pub fn commit(self, input: &[bool]) -> (result: Result<Vec<SessionEvent<E>>, ResponseTickError>)
        ensures
            self.before_model().0.valid() ==> self.after_model().0.valid(),
            self.after_ids() == self.before_ids(),
            self.after_model().1.generation_model() == self.before_model().1.generation_model(),
            result.is_ok() <==>
                self.before_model().1.valid_delivery(queued_response_keys(self.before_model().2, self.target_model()), self.target_model())
                && input@.len() == self.before_model().0.vm_model().external_count(),
            result matches Err(ResponseTickError::Delivery(error)) ==> self.before_model().1.first_delivery_error(
                queued_response_keys(self.before_model().2, self.target_model()), self.target_model(), error),
            result matches Err(ResponseTickError::Input(error)) ==>
                self.before_model().1.valid_delivery(queued_response_keys(self.before_model().2, self.target_model()), self.target_model())
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
                &&& delivery_matches(prior_ledger.requests(), updated_ledger.requests(), queued_response_keys(events, target), target)
            },
    {
        let Self { tick, ledger, ids: _ } = self;
        commit_queued_events(tick, ledger, input)
    }

    /// 要求を含む tick を確定できない場合に、入力から決まる診断を表す。
    ///
    /// メモリの確保に失敗する場合は、採番の検査まで成功している。
    pub open spec fn request_batch_error(
        &self, input: Seq<bool>, requests: Seq<RequestKey>, error: RequestBatchTickError,
    ) -> bool {
        let ids = self.before_ids();
        let (before, ledger, events) = self.before_model();
        let target = self.target_model();
        let keys = queued_response_keys(events, target);
        match error {
            RequestBatchTickError::Number(reason) =>
                reason == RequestIdError::SerialOutOfRange && !ids.fits(requests.len() as u64),
            RequestBatchTickError::Registration(reason) =>
                ids.fits(requests.len() as u64)
                && (reason == BatchRegistrationError::Allocation || first_batch_request_error(
                    &ledger, requests, ids.generation_model(), ids.next_model(), target.tick, reason,
                )),
            RequestBatchTickError::Tick(reason) => {
                &&& ids.fits(requests.len() as u64)
                &&& valid_request_batch(&ledger, requests, ids.generation_model(), ids.next_model(), target.tick)
                &&& match reason {
                    ResponseTickError::Delivery(reason) => ledger.first_delivery_error(keys, target, reason),
                    ResponseTickError::Input(reason) => ledger.valid_delivery(keys, target)
                        && input.len() != before.vm_model().external_count()
                        && reason == crate::netlist::TickInputError::InputCount,
                }
            },
        }
    }

    /// 回路の更新、応答の消費、新規要求の登録と採番が同じ tick に確定したことを表す。
    #[verifier::prophetic]
    pub open spec fn request_batch_committed(
        &self, input: Seq<bool>, requests: Seq<RequestKey>,
        consumed: Seq<SessionEvent<E>>, issued: IssuedRequestIds,
    ) -> bool {
        let (before, prior_ledger, events) = self.before_model();
        let (after, updated_ledger, remaining) = self.after_model();
        let target = self.target_model();
        let count = prior_ledger.requests().len() as int;
        &&& (before.valid() ==> after.valid())
        &&& after.position_model() == target
        &&& after.vm_model().tick_matches(&before.vm_model(), input, after.output_model())
        &&& remaining == events_at_tick(events, target, false)
        &&& consumed == events_at_tick(events, target, true)
        &&& updated_ledger.generation_model() == prior_ledger.generation_model()
        &&& delivery_matches(prior_ledger.requests(), updated_ledger.requests().take(count),
            queued_response_keys(events, target), target)
        &&& issued.generation_model() == self.before_ids().generation_model()
        &&& issued.first_model() == self.before_ids().next_model()
        &&& issued.count_model() as nat == requests.len()
        &&& valid_request_batch(&prior_ledger, requests, issued.generation_model(), issued.first_model(), target.tick)
        &&& self.after_ids().generation_model() == self.before_ids().generation_model()
        &&& self.after_ids().next_model() == issued.first_model() + requests.len() as int
        &&& issued_rows_match(updated_ledger.requests().skip(count), requests,
            issued.generation_model(), issued.first_model(), target.tick)
    }

    /// 応答と新規要求を、同じ回路更新で確定する。
    ///
    /// 新規要求は実行設定のインスタンス順、各デバイスの要求リスト順に渡す。
    /// 同じ tick で消費する応答のタグも、次の tick まで再利用できない。
    /// 成功時は実際に消費した応答と、発行に使う番号を返す。
    ///
    /// # Errors
    ///
    /// 採番、要求の登録検査、配送と回路入力の順で診断する。失敗時は確定済みの状態を保持する。
    pub fn commit_with_requests(self, input: &[bool], requests: &[RequestKey])
        -> (result: Result<(Vec<SessionEvent<E>>, IssuedRequestIds), RequestBatchTickError>)
        ensures
            result.is_err() ==> {
                &&& self.after_model().0 == self.before_model().0
                &&& self.after_model().1.generation_model() == self.before_model().1.generation_model()
                &&& self.after_model().1.requests() == self.before_model().1.requests()
                &&& self.after_model().2 == self.before_model().2
                &&& self.after_ids() == self.before_ids()
            },
            result matches Err(error) ==> self.request_batch_error(input@, requests@, error),
            result matches Ok((consumed, issued)) ==>
                self.request_batch_committed(input@, requests@, consumed@, issued),
    {
        let ghost (_, original_ledger, _) = self.before_model();
        let ghost original_ids = self.before_ids();
        let Self { tick, ledger, ids } = self;
        let target = tick.target();
        let count = requests.len() as u64;
        let pending_ids = match ids.prepare(count) {
            Ok(pending) => pending,
            Err(error) => {
                tick.cancel();
                return Err(RequestBatchTickError::Number(error));
            },
        };
        let prepared = match ledger.prepare_issuance(&pending_ids, requests, target.tick) {
            Ok(prepared) => prepared,
            Err(error) => {
                pending_ids.cancel();
                tick.cancel();
                return Err(RequestBatchTickError::Registration(error));
            },
        };
        let ghost delivery_ledger = *ledger;
        assert(delivery_ledger.requests() == original_ledger.requests());
        assert(original_ids.fits(count));
        assert(valid_request_batch(&original_ledger, requests@, original_ids.generation_model(),
            original_ids.next_model(), target.tick));
        match commit_queued_events(tick, ledger, input) {
            Ok(events) => {
                let ghost prior = ledger.requests();
                let ghost added = prepared.model();
                ledger.append_issued(prepared);
                assert(ledger.requests().take(prior.len() as int) =~= prior);
                assert(ledger.requests().skip(prior.len() as int) =~= added);
                Ok((events, pending_ids.commit()))
            },
            Err(error) => {
                pending_ids.cancel();
                Err(RequestBatchTickError::Tick(error))
            },
        }
    }

    /// 更新を取り消し、回路、時刻、台帳、イベント列を保持する。
    pub fn cancel(self)
        ensures self.after_model() == self.before_model(), self.after_ids() == self.before_ids(),
    {
        self.tick.cancel();
    }
}

impl<'a, T> PendingDeviceEvents<'a, ScheduledResponse<T>> {
    /// 開始時の列で指定添字以降にある最初の対象応答を返す。
    pub fn next_response(&self, from: usize)
        -> (result: Option<(usize, &ScheduledEvent<ScheduledResponse<T>>)>)
        ensures next_event_matches(self.before_model().2, self.target_model(), from, result),
    {
        self.next_event(from)
    }
}

impl<'a, E> PendingDeviceEventsReset<'a, E> {
    /// 準備前の回路と要求管理の状態。
    pub closed spec fn before_model(&self)
        -> ((ClockedSession, RequestLedger, Seq<SessionEvent<E>>), RequestIds) {
        ((self.reset.before_circuit(), *self.ledger, self.reset.before_events()), *self.ids)
    }

    /// 確定または取り消し後の回路と要求管理の状態。
    #[verifier::prophetic]
    pub closed spec fn after_model(&self)
        -> ((ClockedSession, RequestLedger, Seq<SessionEvent<E>>), RequestIds) {
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
    /// 旧世代のイベントを到着順に返す。
    pub fn commit(self) -> (removed: Vec<SessionEvent<E>>)
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
