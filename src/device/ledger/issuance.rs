//! 回路更新の前に、発行する要求の番号・タグ・格納先を準備する。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{HostRequestId, RegisterRequestError, RequestEntry, RequestLedger, ResponseSlot};
use crate::device::PendingRequestIds;

verus! {

/// 発行する要求のインスタンスと、そのデバイス内のタグ。
#[derive(Clone, Copy, Debug)]
pub struct RequestKey {
    /// 実行設定におけるデバイスの識別子。
    pub instance: usize,
    /// デバイス内のタグ番号。
    pub tag: u64,
}

/// 同じ tick の要求列を準備できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BatchRegistrationError {
    /// tick 開始時の台帳との不一致。添字は今回の入力列での位置。
    Registration(usize, RegisterRequestError),
    /// 同じ入力列にある、同じデバイスのタグの重複。
    DuplicateTag {
        /// 最初の指定の添字。
        first: usize,
        /// 重複した指定の添字。
        later: usize,
    },
    /// 発行する行を保持する領域を確保できない。
    Allocation,
}

pub(in crate::device) struct PreparedRequests {
    rows: Vec<RequestEntry>,
}

type RequestRow = (HostRequestId, u64, ResponseSlot);

impl PreparedRequests {
    pub(in crate::device) closed spec fn model(&self) -> Seq<RequestRow> {
        self.rows@.map_values(|entry: RequestEntry| (entry.response.id_model(), entry.tag, entry.response))
    }
}

/// 入力順で指定の要求に割り当てる ID。
pub open spec fn request_id_at(keys: Seq<RequestKey>, generation: u64, first: int, index: int) -> HostRequestId {
    HostRequestId { instance: keys[index].instance, generation, serial: (first + index) as u64 }
}

/// 指定した要求について、開始時の台帳との不一致を入力列内の重複より先に返す。
pub open spec fn batch_request_error(
    ledger: &RequestLedger, keys: Seq<RequestKey>, generation: u64, first: int, tick: u64, index: usize,
) -> Option<BatchRegistrationError> {
    let id = request_id_at(keys, generation, first, index as int);
    let key = keys[index as int];
    if let Some(error) = ledger.registration_error(id, key.tag, tick) {
        Some(BatchRegistrationError::Registration(index, error))
    } else if exists|j: usize| j < index && (#[trigger] keys[j as int]).instance == key.instance
        && keys[j as int].tag == key.tag && (forall|k: int| 0 <= k < j ==>
            (#[trigger] keys[k]).instance != key.instance || keys[k].tag != key.tag) {
        let j = choose|j: usize| j < index && (#[trigger] keys[j as int]).instance == key.instance
            && keys[j as int].tag == key.tag && (forall|k: int| 0 <= k < j ==>
                (#[trigger] keys[k]).instance != key.instance || keys[k].tag != key.tag);
        Some(BatchRegistrationError::DuplicateTag { first: j, later: index })
    } else {
        None
    }
}

/// 採番した要求列が、tick 開始時の台帳と両立することを表す。
pub open spec fn valid_request_batch(
    ledger: &RequestLedger, keys: Seq<RequestKey>, generation: u64, first: int, tick: u64,
) -> bool {
    forall|i: usize| i < keys.len() ==> #[trigger] batch_request_error(ledger, keys, generation, first, tick, i).is_none()
}

/// 入力順で最初の不一致と、その前の要求がすべて妥当であることを表す。
pub open spec fn first_batch_request_error(
    ledger: &RequestLedger, keys: Seq<RequestKey>, generation: u64, first: int, tick: u64,
    error: BatchRegistrationError,
) -> bool {
    exists|i: usize| i < keys.len() && #[trigger] batch_request_error(ledger, keys, generation, first, tick, i) == Some(error)
        && forall|j: usize| j < i ==> #[trigger] batch_request_error(ledger, keys, generation, first, tick, j).is_none()
}

fn first_tag(keys: &[RequestKey], end: usize, key: RequestKey) -> (result: Option<usize>)
    requires end <= keys@.len(),
    ensures match result {
        Some(j) => {
            &&& j < end
            &&& keys@[j as int].instance == key.instance
            &&& keys@[j as int].tag == key.tag
            &&& forall|k: int| 0 <= k < j ==> (#[trigger] keys@[k]).instance != key.instance
                || keys@[k].tag != key.tag
        },
        None => forall|k: int| 0 <= k < end ==> (#[trigger] keys@[k]).instance != key.instance
            || keys@[k].tag != key.tag,
    },
{
    let mut j = 0;
    while j < end
        invariant
            j <= end <= keys@.len(),
            forall|k: int| 0 <= k < j ==> (#[trigger] keys@[k]).instance != key.instance || keys@[k].tag != key.tag,
        decreases end - j,
    {
        let earlier = keys[j];
        if earlier.instance == key.instance && earlier.tag == key.tag {
            return Some(j);
        }
        j += 1;
    }
    None
}

/// 新たに記録する行が採番順と発行時の状態を保つことを表す。
pub open spec fn issued_rows_match(
    rows: Seq<RequestRow>, keys: Seq<RequestKey>, generation: u64, first: int, tick: u64,
) -> bool {
    &&& rows.len() == keys.len()
    &&& forall|i: int| 0 <= i < keys.len() ==> {
        let row = #[trigger] rows[i];
        &&& row.0 == request_id_at(keys, generation, first, i)
        &&& row.1 == keys[i].tag
        &&& row.2.id_model() == row.0
        &&& row.2.issued_model() == tick
        &&& row.2.status_model() == super::ResponseStatus::Awaiting
    }
}

impl RequestLedger {
    pub(in crate::device) fn prepare_issuance(
        &mut self, ids: &PendingRequestIds<'_>, keys: &[RequestKey], tick: u64,
    ) -> (result: Result<PreparedRequests, BatchRegistrationError>)
        requires keys@.len() == ids.count_model(),
        ensures
            final(self).requests() == old(self).requests(),
            final(self).generation_model() == old(self).generation_model(),
            result matches Ok(prepared) ==> {
                &&& issued_rows_match(prepared.model(), keys@, ids.before_model().generation_model(),
                    ids.before_model().next_model(), tick)
                &&& valid_request_batch(old(self), keys@, ids.before_model().generation_model(),
                    ids.before_model().next_model(), tick)
            },
            result matches Err(error) ==> error == BatchRegistrationError::Allocation
                || first_batch_request_error(old(self), keys@, ids.before_model().generation_model(),
                    ids.before_model().next_model(), tick, error),
    {
        let mut rows = Vec::new();
        let ghost generation = ids.before_model().generation_model();
        let ghost start = ids.before_model().next_model();
        if rows.try_reserve_exact(keys.len()).is_err() { return Err(BatchRegistrationError::Allocation); }
        let mut i = 0;
        while i < keys.len()
            invariant
                i <= keys@.len() == ids.count_model(),
                self.requests() == old(self).requests(),
                self.generation_model() == old(self).generation_model(),
                issued_rows_match(PreparedRequests { rows }.model(), keys@.take(i as int),
                    ids.before_model().generation_model(), ids.before_model().next_model(), tick),
                generation == ids.before_model().generation_model(), start == ids.before_model().next_model(),
                forall|j: usize| j < i ==> #[trigger] batch_request_error(old(self), keys@, generation, start, tick, j).is_none(),
            decreases keys@.len() - i,
        {
            let key = keys[i];
            let Some(id) = ids.proposed_id(i as u64, key.instance) else { unreachable!() };
            assert(id == request_id_at(keys@, generation, start, i as int));
            if let Err(error) = self.check_registration(id, key.tag, tick) {
                assert(batch_request_error(old(self), keys@, generation, start, tick, i) ==
                    Some(BatchRegistrationError::Registration(i, error)));
                return Err(BatchRegistrationError::Registration(i, error));
            }
            if let Some(first) = first_tag(keys, i, key) {
                proof {
                    let chosen = choose|j: usize| j < i && (#[trigger] keys@[j as int]).instance == key.instance
                        && keys@[j as int].tag == key.tag && (forall|k: int| 0 <= k < j ==>
                            (#[trigger] keys@[k]).instance != key.instance || keys@[k].tag != key.tag);
                    if first < chosen { assert(keys@[first as int].tag != key.tag || keys@[first as int].instance != key.instance); }
                    if chosen < first { assert(keys@[chosen as int].tag != key.tag || keys@[chosen as int].instance != key.instance); }
                    assert(chosen == first);
                }
                assert(batch_request_error(old(self), keys@, generation, start, tick, i) ==
                    Some(BatchRegistrationError::DuplicateTag { first, later: i }));
                return Err(BatchRegistrationError::DuplicateTag { first, later: i });
            }
            assert(batch_request_error(old(self), keys@, generation, start, tick, i).is_none());
            let ghost prior = PreparedRequests { rows }.model();
            let response = ResponseSlot::new(id, tick);
            rows.push(RequestEntry { tag: key.tag, response });
            proof {
                let staged = PreparedRequests { rows }.model();
                assert(staged =~= prior.push((id, key.tag, response)));
                assert(issued_rows_match(staged, keys@.take(i as int + 1),
                    ids.before_model().generation_model(), ids.before_model().next_model(), tick));
            }
            i += 1;
        }
        assert(keys@.take(i as int) =~= keys@);
        assert(valid_request_batch(old(self), keys@, generation, start, tick));
        if self.entries.try_reserve_exact(keys.len()).is_err() { return Err(BatchRegistrationError::Allocation); }
        Ok(PreparedRequests { rows })
    }

    pub(in crate::device) fn append_issued(&mut self, issued: PreparedRequests)
        ensures final(self).generation_model() == old(self).generation_model(),
            final(self).requests() == old(self).requests() + issued.model(),
    {
        // prepare_issuance が確保した領域を使い、回路更新後には再確保しない。
        let mut i = 0;
        while i < issued.rows.len()
            invariant
                i <= issued.rows@.len(),
                self.entries@ == old(self).entries@ + issued.rows@.take(i as int),
                self.generation == old(self).generation,
            decreases issued.rows@.len() - i,
        {
            let row = issued.rows[i];
            let ghost prefix = issued.rows@.take(i as int);
            self.entries.push(row);
            proof {
                Seq::push_distributes_over_add(old(self).entries@, prefix, row);
                assert(issued.rows@.take(i as int + 1) =~= prefix.push(row));
            }
            i += 1;
        }
        assert(issued.rows@.take(i as int) =~= issued.rows@);
        assert(self.requests() =~= old(self).requests() + issued.model());
    }
}

} // verus!
