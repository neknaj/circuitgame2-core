//! 発行済みの要求に対する応答を、未開始の tick へ予約する。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{DeliveryError, HostRequestId, HostResponseError, RequestLedger, ResponseKey};
#[cfg(verus_only)]
use super::{ResponseStatus, delivery_matches, response_update};
use crate::netlist::{ClockedSession, PendingIoTick, TickInputError};
#[cfg(verus_only)]
use crate::time::events_at_tick;
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

/// 応答を伴う tick を確定できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResponseTickError {
    /// キューにある応答と台帳が一致しない。
    Delivery(DeliveryError),
    /// 回路へ渡した入力のビット数が違う。
    Input(TickInputError),
}

spec fn key_of<T>(event: ScheduledEvent<ScheduledResponse<T>>) -> ResponseKey {
    let (id, tag, _) = event.payload.model();
    ResponseKey { id, tag }
}

/// 対象 tick に渡す応答の要求 ID とタグを、到着順に表す。
pub closed spec fn response_keys<T>(
    events: Seq<ScheduledEvent<ScheduledResponse<T>>>, target: TickPosition,
) -> Seq<ResponseKey> {
    events_at_tick(events, target, true).map_values(|event| key_of(event))
}

proof fn skip_other_events<T>(
    events: Seq<ScheduledEvent<ScheduledResponse<T>>>, target: TickPosition, from: int, to: int,
)
    requires
        0 <= from <= to <= events.len(),
        forall|j: int| from <= j < to ==> (#[trigger] events[j]).position != target,
    ensures
        response_keys(events.take(to), target) == response_keys(events.take(from), target),
{
    let prefix = events.take(from);
    let skipped = events.subrange(from, to);
    let selected = |event: ScheduledEvent<ScheduledResponse<T>>| (event.position == target) == true;
    assert forall|j: int| 0 <= j < skipped.len() implies (#[trigger] skipped[j]).position != target by {
        assert(skipped[j] == events[from + j]);
    }
    skipped.lemma_all_neg_filter_empty(selected);
    assert(skipped.filter(selected) =~= Seq::<ScheduledEvent<ScheduledResponse<T>>>::empty());
    assert(events.take(to) =~= prefix + skipped);
    Seq::filter_distributes_over_add(prefix, skipped, selected);
}

proof fn append_response_key<T>(
    events: Seq<ScheduledEvent<ScheduledResponse<T>>>, target: TickPosition, index: int,
)
    requires 0 <= index < events.len(), events[index].position == target,
    ensures response_keys(events.take(index + 1), target) ==
        response_keys(events.take(index), target).push(key_of(events[index])),
{
    let prefix = events.take(index);
    let event = events[index];
    assert(events.take(index + 1) =~= prefix.push(event));
    prefix.lemma_filter_push(event, |e: ScheduledEvent<ScheduledResponse<T>>| (e.position == target) == true);
    assert(response_keys(events.take(index + 1), target) =~=
        response_keys(events.take(index), target).push(key_of(event)));
}

impl<'a, T> PendingIoTick<'a, ScheduledResponse<T>> {
    fn ready_keys(&self) -> (keys: Vec<ResponseKey>)
        ensures keys@ == response_keys(self.before_events(), self.target_model()),
    {
        let mut keys = Vec::new();
        let mut from = 0;
        let ghost events = self.before_events();
        let target = self.target();
        assert(response_keys(events.take(0), target).len() == 0);
        loop
            invariant
                from <= events.len(),
                events == self.before_events(),
                target == self.target_model(),
                keys@ == response_keys(events.take(from as int), target),
            decreases events.len() - from,
        {
            let Some((index, event)) = self.next_event(from) else {
                proof {
                    skip_other_events(events, target, from as int, events.len() as int);
                    assert(events.take(events.len() as int) =~= events);
                }
                return keys;
            };
            let key = ResponseKey { id: event.payload.request_id(), tag: event.payload.tag() };
            proof {
                skip_other_events(events, target, from as int, index as int);
                append_response_key(events, target, index as int);
                assert(key == key_of(events[index as int]));
            }
            keys.push(key);
            from = index + 1;
        }
    }

    /// 回路、時刻、イベント列、要求台帳をまとめて更新する。
    ///
    /// この実行の台帳を渡す。同じ tick の応答をすべて照合した後に回路を更新し、
    /// 成功した場合だけ応答を台帳から消費する。応答を予約したイベント列には、台帳と同時に確定するこの関数を使う。
    ///
    /// # Errors
    ///
    /// 配送列の不一致を先に検査する。配送または入力幅のエラーではどの状態も変更しない。
    pub fn commit_responses(
        self, ledger: &mut RequestLedger, input: &[bool],
    ) -> (result: Result<Vec<ScheduledEvent<ScheduledResponse<T>>>, ResponseTickError>)
        ensures
            self.before_circuit().valid() ==> self.after_circuit().valid(),
            result.is_ok() <==> old(ledger).valid_delivery(
                response_keys(self.before_events(), self.target_model()), self.target_model())
                && input@.len() == self.before_circuit().vm_model().external_count(),
            result matches Err(ResponseTickError::Delivery(error)) ==> {
                let keys = response_keys(self.before_events(), self.target_model());
                exists|i: usize| i < keys.len()
                    && #[trigger] old(ledger).delivery_issue_at(keys, self.target_model(), i) == Some(error)
                    && forall|j: usize| j < i ==>
                        #[trigger] old(ledger).delivery_issue_at(keys, self.target_model(), j).is_none()
            },
            result matches Err(ResponseTickError::Input(error)) ==>
                old(ledger).valid_delivery(response_keys(self.before_events(), self.target_model()), self.target_model())
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
                        response_keys(self.before_events(), self.target_model()), self.target_model())
                },
                Err(_) => {
                    &&& self.after_circuit() == self.before_circuit()
                    &&& self.after_events() == self.before_events()
                    &&& *final(ledger) == *old(ledger)
                },
            },
    {
        let target = self.target();
        let keys = self.ready_keys();
        let delivery = match ledger.prepare_delivery(keys.as_slice(), target) {
            Ok(delivery) => delivery,
            Err(error) => {
                self.cancel();
                return Err(ResponseTickError::Delivery(error));
            },
        };
        match self.commit(input) {
            Ok(events) => {
                delivery.commit();
                Ok(events)
            },
            Err(error) => {
                delivery.cancel();
                Err(ResponseTickError::Input(error))
            },
        }
    }
}
} // verus!
