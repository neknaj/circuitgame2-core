//! 発行済みの要求に対する応答を、未開始の tick へ予約する。

use vstd::prelude::*;

use super::{HostRequestId, HostResponseError, RequestLedger};
#[cfg(verus_only)]
use super::{ResponseStatus, response_update};
use crate::netlist::ClockedSession;
use crate::time::{ScheduledEvent, ScheduledEvents, TickPosition};

verus! {

/// 要求との照合を済ませた、デバイスへ渡す応答。
pub struct ScheduledResponse<T> {
    id: HostRequestId,
    tag: u64,
    payload: T,
}

impl<T> ScheduledResponse<T> {
    /// 応答の元になった要求と、デバイス内タグおよびデータ。
    pub closed spec fn model(&self) -> (HostRequestId, u64, T) {
        (self.id, self.tag, self.payload)
    }

    /// 応答の元になった要求 ID を返す。
    pub fn request_id(&self) -> (id: HostRequestId)
        ensures id == self.model().0,
    {
        self.id
    }

    /// デバイス内のタグ番号を返す。
    pub fn tag(&self) -> (tag: u64)
        ensures tag == self.model().1,
    {
        self.tag
    }

    /// デバイスに渡す応答データを借りる。
    pub fn payload(&self) -> (payload: &T)
        ensures *payload == self.model().2,
    {
        &self.payload
    }
}

/// 応答を適用予定の tick に登録できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScheduleResponseError {
    /// 配送予定が回路の現在の世代と異なる。
    DifferentGeneration,
    /// 配送予定の tick はすでに確定している。
    AlreadyCommitted,
    /// 要求との照合に失敗した。
    Response(HostResponseError),
}

impl ClockedSession {
    /// 要求照合の成功時に、台帳を保留状態にして応答をイベント列の末尾へ登録する。
    ///
    /// 同じ実行の要求台帳と応答列を渡す。payload の型はデバイスの記述に従って先に検査する。
    /// tick の準備中は回路実行を排他的に借りているため、同じ実行でこの関数を呼べない。
    ///
    /// # Errors
    ///
    /// 回路の世代、配送予定の tick、要求との照合の順に検査する。失敗時は台帳とイベント列を保持する。
    pub fn schedule_response<T>(
        &self, ledger: &mut RequestLedger, events: &mut ScheduledEvents<ScheduledResponse<T>>,
        id: HostRequestId, delivery: TickPosition, payload: T,
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
                &&& delivery.generation == self.position_model().generation
                &&& delivery.tick > self.position_model().tick
                &&& id.generation == delivery.generation == old(ledger).generation_model()
                &&& final(ledger).generation_model() == old(ledger).generation_model()
                &&& final(events).model().len() == old(events).model().len() + 1
                &&& final(events).model().drop_last() == old(events).model()
                &&& final(events).model().last().position == delivery
                &&& final(events).model().last().payload.model().0 == id
                &&& final(events).model().last().payload.model().2 == payload
                &&& exists|i: int| #[trigger] old(ledger).found_request(id, i) && response_update(
                    old(ledger).requests(), final(ledger).requests(), i,
                    ResponseStatus::Awaiting, ResponseStatus::Held(delivery),
                    final(events).model().last().payload.model().1,
                )
            },
    {
        let current = self.position();
        if delivery.generation != current.generation {
            return Err(ScheduleResponseError::DifferentGeneration);
        }
        if delivery.tick <= current.tick {
            return Err(ScheduleResponseError::AlreadyCommitted);
        }
        let tag = match ledger.receive(id, delivery) {
            Ok(tag) => tag,
            Err(error) => return Err(ScheduleResponseError::Response(error)),
        };
        let event = ScheduledEvent { position: delivery, payload: ScheduledResponse { id, tag, payload } };
        events.enqueue(event);
        Ok(())
    }
}

} // verus!
