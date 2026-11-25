//! 固定容量の台帳で、tick の進行、イベントの引き渡し、要求の発行を一括で確定する。

#[cfg(not(verus_only))]
use verus_builtin_macros::verus;
#[cfg(verus_only)]
use vstd::prelude::*;

use super::{FixedIssueError, FixedRequestLedger, FixedTickError};
#[cfg(verus_only)]
use super::delivery_due_at;
#[cfg(verus_only)]
use crate::ClockError;
use crate::{HostRequestId, IssuedRequestIds, RequestIdError, RequestKey, TickPosition};

verus! {

/// tick の候補を準備できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FixedPrepareError {
    /// 同じ世代の次の tick に進めない。
    Tick(FixedTickError),
    /// 指定した応答 ID が今回の引き渡し対象と一致しない。
    ///
    /// 数値は応答 ID の入力列における最初の違反の添字。
    Delivery(usize),
    /// 今回の引き渡し対象に入っていない応答がある。
    MissingDelivery,
    /// 一括発行に必要な通し番号が残っていない。
    Number(RequestIdError),
    /// 要求を発行できない。
    ///
    /// 添字は要求の入力順で最初に失敗した指定を指す。
    Request(usize, FixedIssueError),
}

/// 確定前の台帳を借りたまま、次の tick の候補を保持する。
///
/// この値を破棄すると、元の台帳と保持中の応答が残る。要求 ID は確定時に返す。
pub struct PreparedFixedTick<'l, 'k, R: Copy, const N: usize> {
    ledger: &'l mut FixedRequestLedger<R, N>,
    candidate: FixedRequestLedger<R, N>,
    outgoing: CommittedFixedTick<'k>,
}

/// 確定後にホストへ渡す要求 ID の範囲と、対応する設定順の要求列。
pub struct CommittedFixedTick<'k> {
    position: TickPosition,
    keys: &'k [RequestKey],
    ids: IssuedRequestIds,
}

spec fn advances<R: Copy, const N: usize>(before: FixedRequestLedger<R, N>, after: FixedRequestLedger<R, N>)
    -> bool
{
    &&& !before.has_due_response()
    &&& after.position_model().generation == before.position_model().generation
    &&& after.position_model().tick as int == before.position_model().tick as int + 1
    &&& after.rows_model() == before.rows_model()
    &&& after.next_serial_model() == before.next_serial_model()
    &&& after.delivered_tags_model() == Seq::new(N as nat, |i: int| None)
}

spec fn delivers<R: Copy, const N: usize>(
    before: FixedRequestLedger<R, N>, after: FixedRequestLedger<R, N>, id: HostRequestId,
) -> bool {
    &&& after.position_model() == before.position_model()
    &&& after.next_serial_model() == before.next_serial_model()
    &&& exists|i: int| #[trigger] before.holds_request(id, i)
        && delivery_due_at(before.rows_model(), before.position_model(), i)
        && after.rows_model() == before.rows_model().update(i, None)
        && after.delivered_tags_model() == before.delivered_tags_model().update(i, Some(before.rows_model()[i].unwrap().key))
}

spec fn issues<R: Copy, const N: usize>(
    before: FixedRequestLedger<R, N>, after: FixedRequestLedger<R, N>, key: RequestKey,
) -> bool {
    let id = HostRequestId {
        instance: key.instance, generation: before.position_model().generation, serial: before.next_serial_model() as u64,
    };
    &&& before.issue_error(key).is_none()
    &&& after.position_model() == before.position_model()
    &&& after.next_serial_model() == before.next_serial_model() + 1
    &&& after.delivered_tags_model() == before.delivered_tags_model()
    &&& exists|i: int| #[trigger] after.issued_at(&before, key, id, i)
}

spec fn deliveries_match<R: Copy, const N: usize>(
    deliveries: Seq<HostRequestId>, states: Seq<FixedRequestLedger<R, N>>,
) -> bool {
    &&& states.len() == deliveries.len() + 1
    &&& forall|i: int| 0 <= i < deliveries.len() ==> #[trigger] delivers(states[i], states[i + 1], deliveries[i])
}

spec fn requests_match<R: Copy, const N: usize>(
    keys: Seq<RequestKey>, states: Seq<FixedRequestLedger<R, N>>,
) -> bool {
    &&& states.len() == keys.len() + 1
    &&& forall|i: int| 0 <= i < keys.len() ==> #[trigger] issues(states[i], states[i + 1], keys[i])
}

impl<'k> CommittedFixedTick<'k> {
    /// 確定した tick の論理時刻。
    pub closed spec fn position_model(&self) -> TickPosition { self.position }
    /// 実行設定とデバイスの要求列の順に並ぶ、今回の要求先とタグ。
    pub closed spec fn keys_model(&self) -> Seq<RequestKey> { self.keys@ }
    /// 確定した要求 ID の範囲。
    pub closed spec fn ids_model(&self) -> IssuedRequestIds { self.ids }

    /// 確定した tick の時刻を返す。
    pub fn position(&self) -> (position: TickPosition)
        ensures position == self.position_model(),
    { self.position }

    /// 要求の入力順で ID を取り出す。添字が範囲外なら `None` を返す。
    pub fn id_at(&self, index: usize) -> (id: Option<HostRequestId>)
        ensures
            id.is_some() <==> index < self.keys_model().len() && index < self.ids_model().count_model(),
            id matches Some(id) ==> {
                &&& id.instance == self.keys_model()[index as int].instance
                &&& id.generation == self.ids_model().generation_model()
                &&& id.serial as int == self.ids_model().first_model() + index as int
            },
    {
        if index >= self.keys.len() {
            return None;
        }
        assert(index as u64 as int == index as int);
        self.ids.id_at(index as u64, self.keys[index].instance)
    }
}

impl<'l, 'k, R: Copy, const N: usize> PreparedFixedTick<'l, 'k, R, N> {
    /// 準備を始めた時点の確定台帳。
    pub closed spec fn before_model(&self) -> FixedRequestLedger<R, N> { *self.ledger }
    /// 確定または取り消しの後の台帳。
    #[verifier::prophetic]
    pub closed spec fn after_model(&self) -> FixedRequestLedger<R, N> { *final(self.ledger) }
    /// 確定する場合に採用する候補。
    pub closed spec fn candidate_model(&self) -> FixedRequestLedger<R, N> { self.candidate }
    /// 確定する場合に公開する要求 ID の範囲。
    pub closed spec fn outgoing_model(&self) -> CommittedFixedTick<'k> { self.outgoing }

    /// 回路と全デバイスの更新が成功した後に候補を採用し、今回はじめて要求 ID を公開する。
    pub fn commit(self) -> (committed: CommittedFixedTick<'k>)
        ensures self.after_model() == self.candidate_model(), committed == self.outgoing_model(),
    {
        *self.ledger = self.candidate;
        self.outgoing
    }

    /// 候補を取り消し、台帳と保持中の応答をそのまま残す。
    pub fn cancel(self)
        ensures self.after_model() == self.before_model(),
    {}
}

impl<R: Copy, const N: usize> FixedRequestLedger<R, N> {
    fn snapshot(&self) -> (snapshot: Self)
        ensures snapshot == *self,
    {
        proof { use_type_invariant(self); }
        Self { clock: self.clock.snapshot(), ids: self.ids.snapshot(),
            rows: self.rows, delivered_tags: self.delivered_tags }
    }

    /// 候補は同じ世代の次の tick へ進み、応答と要求をそれぞれの入力順で処理した結果を表す。
    pub closed spec fn tick_matches(
        &self, candidate: &Self, delivery_ids: Seq<HostRequestId>, keys: Seq<RequestKey>,
    ) -> bool {
        exists|deliveries: Seq<Self>, requests: Seq<Self>|
            #[trigger] deliveries_match(delivery_ids, deliveries)
            && #[trigger] requests_match(keys, requests)
            && advances(*self, deliveries[0])
            && !deliveries.last().has_due_response()
            && requests[0] == deliveries.last()
            && requests.last() == *candidate
    }

    /// tick の準備を中断する最初の段階と、その段階の違反を表す。
    pub closed spec fn tick_error_matches(
        &self, delivery_ids: Seq<HostRequestId>, keys: Seq<RequestKey>, error: FixedPrepareError,
    ) -> bool {
        match error {
            FixedPrepareError::Tick(FixedTickError::PendingDelivery) => self.has_due_response(),
            FixedPrepareError::Tick(FixedTickError::Clock(ClockError::TickOutOfRange)) =>
                !self.has_due_response() && self.position_model().tick == u64::MAX,
            FixedPrepareError::Tick(_) => false,
            FixedPrepareError::Delivery(index) => index < delivery_ids.len()
                && exists|states: Seq<Self>| #[trigger] deliveries_match(delivery_ids.take(index as int), states)
                    && advances(*self, states[0])
                    && forall|i: int| !((#[trigger] states.last().holds_request(delivery_ids[index as int], i))
                        && delivery_due_at(states.last().rows_model(), states.last().position_model(), i)),
            FixedPrepareError::MissingDelivery =>
                exists|states: Seq<Self>| #[trigger] deliveries_match(delivery_ids, states)
                    && advances(*self, states[0]) && states.last().has_due_response(),
            FixedPrepareError::Number(error) => error == RequestIdError::SerialOutOfRange
                && !self.ids.fits(keys.len() as u64)
                && exists|states: Seq<Self>| #[trigger] deliveries_match(delivery_ids, states)
                    && advances(*self, states[0]) && !states.last().has_due_response(),
            FixedPrepareError::Request(index, error) => index < keys.len() && self.ids.fits(keys.len() as u64)
                && exists|delivered: Seq<Self>, issued: Seq<Self>|
                    #[trigger] deliveries_match(delivery_ids, delivered)
                    && #[trigger] requests_match(keys.take(index as int), issued)
                    && advances(*self, delivered[0]) && !delivered.last().has_due_response()
                    && issued[0] == delivered.last() && issued.last().issue_error(keys[index as int]) == Some(error),
        }
    }

    /// 同じ世代の次の tick を、応答の引き渡しと複数要求の発行を含めて準備する。
    ///
    /// `delivery_ids` は今回はじめにデバイスに渡す応答 ID を、ホストが確定したイベント順で指定する。
    /// payload は事前に [Self::peek_at] で参照する。回路の `ready` が0の間は、
    /// デバイスが受け取った応答を自身の状態に保持できる。
    /// `keys` は新規要求を、実行設定と各デバイス内の要求リストの順で並べる。
    /// 台帳の候補1個分と、借用・時刻・ID 範囲の管理領域を追加で使う。
    /// 候補の作成と採用は容量に比例し、応答や要求を1件処理するごとにスロットを走査する。
    ///
    /// # Errors
    ///
    /// tick、指定順の応答 ID、未指定の応答、採番範囲、要求の順に検査する。
    /// 途中で失敗した場合、台帳と保持中の応答は変化しない。
    pub fn prepare_tick<'l, 'k>(
        &'l mut self, delivery_ids: &[HostRequestId], keys: &'k [RequestKey],
    ) -> (result: Result<PreparedFixedTick<'l, 'k, R, N>, FixedPrepareError>)
        ensures
            result matches Ok(pending) ==> {
                &&& pending.before_model() == *old(self)
                &&& old(self).tick_matches(&pending.candidate_model(), delivery_ids@, keys@)
                &&& pending.after_model() == *final(self)
                &&& pending.outgoing_model().keys_model() == keys@
                &&& pending.outgoing_model().position_model() == pending.candidate_model().position_model()
                &&& pending.outgoing_model().ids_model().generation_model() == old(self).position_model().generation
                &&& pending.outgoing_model().ids_model().first_model() == old(self).next_serial_model()
                &&& pending.outgoing_model().ids_model().count_model() == keys@.len()
                &&& pending.candidate_model().next_serial_model() == old(self).next_serial_model() + keys@.len()
                &&& pending.candidate_model().position_model().generation == old(self).position_model().generation
                &&& pending.candidate_model().position_model().tick as int == old(self).position_model().tick as int + 1
            },
            result matches Err(error) ==> *final(self) == *old(self)
                && old(self).tick_error_matches(delivery_ids@, keys@, error),
    {
        proof { use_type_invariant(&*self); }
        let mut candidate = self.snapshot();
        let target = match candidate.advance_tick() {
            Ok(target) => target,
            Err(error) => return Err(FixedPrepareError::Tick(error)),
        };
        let ghost mut delivered = seq![candidate];
        assert(advances(*self, delivered[0]));
        let mut delivery = 0;
        while delivery < delivery_ids.len()
            invariant
                delivery <= delivery_ids@.len(),
                candidate.position_model() == target,
                target.generation == self.position_model().generation,
                target.tick as int == self.position_model().tick as int + 1,
                candidate.next_serial_model() == self.next_serial_model(),
                advances(*self, delivered[0]),
                delivered.last() == candidate,
                deliveries_match(delivery_ids@.take(delivery as int), delivered),
            decreases delivery_ids.len() - delivery,
        {
            let ghost old_candidate = candidate;
            let id = delivery_ids[delivery];
            if candidate.consume(id).is_none() {
                assert(self.tick_error_matches(delivery_ids@, keys@, FixedPrepareError::Delivery(delivery)));
                return Err(FixedPrepareError::Delivery(delivery));
            }
            proof {
                let i = delivery as int;
                assert(delivers(old_candidate, candidate, id));
                let extended = delivered.push(candidate);
                assert forall|j: int| 0 <= j < i + 1 implies
                    #[trigger] delivers(extended[j], extended[j + 1], delivery_ids@[j]) by {
                    if j < i {
                        let prefix = delivery_ids@.take(i);
                        assert(prefix[j] == delivery_ids@[j]);
                        assert(delivers(delivered[j], delivered[j + 1], prefix[j]));
                    }
                };
                delivered = extended;
            }
            delivery += 1;
        }
        assert(delivery_ids@.take(delivery as int) =~= delivery_ids@);
        if candidate.has_due() {
            assert(self.tick_error_matches(delivery_ids@, keys@, FixedPrepareError::MissingDelivery));
            return Err(FixedPrepareError::MissingDelivery);
        }
        let mut range = self.ids.snapshot();
        let count = keys.len() as u64;
        assert(count as int == keys@.len());
        let preview = match range.prepare(count) {
            Ok(preview) => preview,
            Err(error) => {
                assert(self.tick_error_matches(delivery_ids@, keys@, FixedPrepareError::Number(error)));
                return Err(FixedPrepareError::Number(error));
            },
        };
        let ids = preview.commit();
        assert(ids.generation_model() == self.position_model().generation);
        assert(ids.first_model() == self.next_serial_model());
        assert(ids.count_model() == keys@.len());

        let ghost mut installed = seq![candidate];
        let mut request = 0;
        while request < keys.len()
            invariant
                request <= keys@.len(),
                candidate.position_model() == target,
                target.generation == self.position_model().generation,
                target.tick as int == self.position_model().tick as int + 1,
                candidate.next_serial_model() == self.next_serial_model() + request,
                installed.last() == candidate && installed[0] == delivered.last(),
                requests_match(keys@.take(request as int), installed),
                ids.generation_model() == self.position_model().generation,
                ids.first_model() == self.next_serial_model(),
                ids.count_model() == keys@.len(),
                delivered.len() > 0,
                deliveries_match(delivery_ids@, delivered),
                advances(*self, delivered[0]),
                !delivered.last().has_due_response(),
                self.ids.fits(keys@.len() as u64),
            decreases keys.len() - request,
        {
            let ghost old_candidate = candidate;
            let key = keys[request];
            let _id = match candidate.issue(key) {
                Ok(id) => id,
                Err(error) => {
                    assert(installed.last().issue_error(keys@[request as int]) == Some(error));
                    assert(self.tick_error_matches(delivery_ids@, keys@, FixedPrepareError::Request(request, error)));
                    return Err(FixedPrepareError::Request(request, error));
                },
            };
            proof {
                let i = request as int;
                assert(_id == (HostRequestId { instance: key.instance, generation: old_candidate.position_model().generation,
                    serial: old_candidate.next_serial_model() as u64 }));
                assert(issues(old_candidate, candidate, key));
                let extended = installed.push(candidate);
                assert forall|j: int| 0 <= j < i + 1 implies
                    #[trigger] issues(extended[j], extended[j + 1], keys@[j]) by {
                    if j < i {
                        let prefix = keys@.take(i);
                        assert(prefix[j] == keys@[j]);
                        assert(issues(installed[j], installed[j + 1], prefix[j]));
                    }
                };
                installed = extended;
            }
            request += 1;
        }
        assert(keys@.take(request as int) =~= keys@);
        assert(self.tick_matches(&candidate, delivery_ids@, keys@));
        let outgoing = CommittedFixedTick { position: target, keys, ids };
        Ok(PreparedFixedTick { ledger: self, candidate, outgoing })
    }
}

// 準備した値をスコープの終わりで破棄する呼び出しについても元状態の保持を確かめる。
#[cfg(verus_only)]
fn dropping_preparation_preserves_ledger<R: Copy, const N: usize>(
    ledger: &mut FixedRequestLedger<R, N>, deliveries: &[HostRequestId], requests: &[RequestKey],
)
    ensures *final(ledger) == *old(ledger),
{
    match ledger.prepare_tick(deliveries, requests) {
        Ok(_pending) => {},
        Err(_) => {},
    }
}

} // verus!
