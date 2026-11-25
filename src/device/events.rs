//! 外部入力と照合済みの応答を同じ到着順で管理する。

use alloc::vec::Vec;
use vstd::prelude::*;

use crate::netlist::{ClockedSession, PendingIoTick};
#[cfg(verus_only)]
use crate::netlist::TickInputError;
use crate::time::{ScheduledEvent, ScheduledEvents, TickPosition};
#[cfg(verus_only)]
use crate::time::events_at_tick;
use super::{HostRequestId, RequestLedger, ResponseKey, ResponseTickError, ScheduleResponseError, ScheduledResponse};
#[cfg(verus_only)]
use super::{ResponseStatus, delivery_matches, response_update};
use super::scheduling::{QueuedResponse, commit_queued_events};
#[cfg(verus_only)]
use super::scheduling::{push_queued_response_key, queued_response_keys};

verus! {

/// tick の開始時にデバイスへ渡す外部入力または照合済みの応答。
pub enum DeviceEvent<I, R> {
    /// 外部から特定のインスタンスへ与えた入力。
    Input {
        /// 入力を受け取るインスタンス。
        instance: usize,
        /// デバイスの種別に対応する入力データ。
        payload: I,
    },
    /// 台帳で照合と配送予約を済ませた応答。
    Response(ScheduledResponse<R>),
}

impl<I, R> QueuedResponse for DeviceEvent<I, R> {
    open spec fn key_model(&self) -> Option<ResponseKey> {
        match self {
            Self::Input { .. } => None,
            Self::Response(response) => response.key_model(),
        }
    }

    fn queued_key(&self) -> (key: Option<ResponseKey>) {
        match self {
            Self::Input { .. } => None,
            Self::Response(response) => response.queued_key(),
        }
    }
}

/// 外部入力を指定した tick に登録できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScheduleInputError {
    /// 指定した tick が現在の reset 世代に属さない。
    DifferentGeneration,
    /// 指定した tick は確定済みである。
    AlreadyCommitted,
}

/// 対象 tick の応答 ID とタグを、外部入力を除いて到着順に表す。
pub closed spec fn device_response_keys<I, R>(
    events: Seq<ScheduledEvent<DeviceEvent<I, R>>>, target: TickPosition,
) -> Seq<ResponseKey> {
    queued_response_keys(events, target)
}

/// 空の列と、末尾イベントを1件加えたときの応答キー列を示す。
pub proof fn device_response_keys_step<I, R>(
    events: Seq<ScheduledEvent<DeviceEvent<I, R>>>, target: TickPosition,
)
    ensures
        events.len() == 0 ==> device_response_keys(events, target).len() == 0,
        events.len() > 0 ==> {
            let previous = device_response_keys(events.drop_last(), target);
            let event = events.last();
            device_response_keys(events, target) == if event.position != target {
                previous
            } else {
                match event.payload {
                    DeviceEvent::Input { .. } => previous,
                    DeviceEvent::Response(response) => previous.push(ResponseKey {
                        id: response.model().0, tag: response.model().1,
                    }),
                }
            }
        },
{
    if events.len() > 0 {
        assert(events == events.drop_last().push(events.last()));
        push_queued_response_key(events.drop_last(), events.last(), target);
    }
}

impl ClockedSession {
    /// 未確定の tick に外部入力を登録する。
    ///
    /// 応答の予約にも同じイベント列を使う。適用 tick の割り当てとインスタンスの確認は呼び出し側が行う。
    ///
    /// # Errors
    ///
    /// 世代が違うか tick がすでに確定していれば、イベント列を保持してエラーを返す。
    pub fn schedule_device_input<I, R>(
        &self, events: &mut ScheduledEvents<DeviceEvent<I, R>>,
        instance: usize, delivery: TickPosition, payload: I,
    ) -> (result: Result<(), ScheduleInputError>)
        ensures
            result == Err(ScheduleInputError::DifferentGeneration) <==>
                delivery.generation != self.position_model().generation,
            result == Err(ScheduleInputError::AlreadyCommitted) <==>
                delivery.generation == self.position_model().generation
                && delivery.tick <= self.position_model().tick,
            result.is_ok() <==> delivery.generation == self.position_model().generation
                && delivery.tick > self.position_model().tick,
            result.is_err() ==> final(events).model() == old(events).model(),
            result.is_ok() ==> final(events).model() == old(events).model().push(ScheduledEvent {
                position: delivery, payload: DeviceEvent::Input { instance, payload },
            }),
    {
        let current = self.position();
        if delivery.generation != current.generation {
            return Err(ScheduleInputError::DifferentGeneration);
        }
        if delivery.tick <= current.tick {
            return Err(ScheduleInputError::AlreadyCommitted);
        }
        events.enqueue(ScheduledEvent { position: delivery, payload: DeviceEvent::Input { instance, payload } });
        Ok(())
    }

    /// 照合した応答を、外部入力と同じイベント列の末尾に登録する。
    ///
    /// 同じ実行の要求台帳を渡す。payload の型はデバイスの記述に従って先に検査する。
    ///
    /// # Errors
    ///
    /// 世代、配送予定の tick、要求との照合の順に検査する。失敗時は台帳とイベント列を保持する。
    pub fn schedule_device_response<I, R>(
        &self, ledger: &mut RequestLedger, events: &mut ScheduledEvents<DeviceEvent<I, R>>,
        id: HostRequestId, delivery: TickPosition, payload: R,
    ) -> (result: Result<(), ScheduleResponseError>)
        ensures
            result == Err(ScheduleResponseError::DifferentGeneration) <==>
                delivery.generation != self.position_model().generation,
            result == Err(ScheduleResponseError::AlreadyCommitted) <==>
                delivery.generation == self.position_model().generation
                && delivery.tick <= self.position_model().tick,
            result.is_ok() <==> delivery.generation == self.position_model().generation
                && delivery.tick > self.position_model().tick && old(ledger).accepts_response(id, delivery),
            result matches Err(ScheduleResponseError::Response(error)) ==>
                delivery.generation == self.position_model().generation
                && delivery.tick > self.position_model().tick
                && old(ledger).rejects_response(id, delivery, error),
            result.is_err() ==> {
                &&& *final(ledger) == *old(ledger)
                &&& final(events).model() == old(events).model()
            },
            result.is_ok() ==> {
                let event = final(events).model().last();
                &&& event.position == delivery
                &&& final(events).model() == old(events).model().push(event)
                &&& final(ledger).generation_model() == old(ledger).generation_model()
                &&& id.generation == delivery.generation == old(ledger).generation_model()
                &&& match event.payload {
                    DeviceEvent::Response(response) => {
                        &&& response.model().0 == id
                        &&& response.model().2 == payload
                        &&& exists|i: int| #[trigger] old(ledger).found_request(id, i) && response_update(
                            old(ledger).requests(), final(ledger).requests(), i,
                            ResponseStatus::Awaiting, ResponseStatus::Held(delivery), response.model().1,
                        )
                    },
                    DeviceEvent::Input { .. } => false,
                }
            },
    {
        let response = self.reserve_scheduled_response(ledger, id, delivery, payload)?;
        events.enqueue(ScheduledEvent { position: delivery, payload: DeviceEvent::Response(response) });
        Ok(())
    }
}

impl<'a, I, R> PendingIoTick<'a, DeviceEvent<I, R>> {
    /// 外部入力と応答を到着順のまま消費し、回路と台帳を同じ tick で更新する。
    ///
    /// 同じ実行の台帳を渡す。応答の照合を済ませた後で回路を更新する。
    /// 台帳で消費するのは応答だけで、外部入力は台帳を変更しない。
    /// 応答を含むイベント列は、この関数で確定する。
    ///
    /// # Errors
    ///
    /// 配送列の不一致を先に検査する。配送エラーの添字は、対象 tick の応答だけを数えた位置を指す。
    /// 配送または入力幅のエラーでは状態を保持する。
    pub fn commit_device_events(
        self, ledger: &mut RequestLedger, input: &[bool],
    ) -> (result: Result<Vec<ScheduledEvent<DeviceEvent<I, R>>>, ResponseTickError>)
        ensures
            self.before_circuit().valid() ==> self.after_circuit().valid(),
            result.is_ok() <==> old(ledger).valid_delivery(
                device_response_keys(self.before_events(), self.target_model()), self.target_model())
                && input@.len() == self.before_circuit().vm_model().external_count(),
            result matches Err(ResponseTickError::Delivery(error)) ==> old(ledger).first_delivery_error(
                device_response_keys(self.before_events(), self.target_model()), self.target_model(), error),
            result matches Err(ResponseTickError::Input(error)) ==>
                old(ledger).valid_delivery(device_response_keys(self.before_events(), self.target_model()), self.target_model())
                && input@.len() != self.before_circuit().vm_model().external_count()
                && error == TickInputError::InputCount,
            match result {
                Ok(consumed) => {
                    &&& self.after_circuit().position_model() == self.target_model()
                    &&& self.after_circuit().vm_model().tick_matches(
                        &self.before_circuit().vm_model(), input@, self.after_circuit().output_model())
                    &&& self.after_events() == events_at_tick(self.before_events(), self.target_model(), false)
                    &&& consumed@ == events_at_tick(self.before_events(), self.target_model(), true)
                    &&& final(ledger).generation_model() == old(ledger).generation_model()
                    &&& delivery_matches(old(ledger).requests(), final(ledger).requests(),
                        device_response_keys(self.before_events(), self.target_model()), self.target_model())
                },
                Err(_) => {
                    &&& self.after_circuit() == self.before_circuit()
                    &&& self.after_events() == self.before_events()
                    &&& *final(ledger) == *old(ledger)
                },
            },
    {
        commit_queued_events(self, ledger, input)
    }
}
} // verus!
