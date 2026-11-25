//! 1回の tick で配送する応答を先に検査し、確定後に台帳へ反映する。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{HostRequestId, RequestEntry, RequestLedger, ResponseSlot, ResponseStatus, TickPosition};

verus! {

/// 予約済みのイベントが指す要求とデバイス内タグ。
#[derive(Clone, Copy, Debug)]
pub struct ResponseKey {
    /// 応答の元になった要求。
    pub id: HostRequestId,
    /// デバイスに渡すタグ番号。
    pub tag: u64,
}

/// 応答をまとめて配送できない理由。添字は入力列内の位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeliveryError {
    /// 登録されていない要求。
    Unknown(usize),
    /// 同じ要求が配送列に既出である。
    Duplicate(usize),
    /// 台帳のタグと配送列のタグが異なる。
    WrongTag(usize),
    /// 指定 tick に配送が予定されていない。
    NotHeld(usize),
}

#[derive(Clone, Copy)]
struct Update {
    index: usize,
    entry: RequestEntry,
}

/// 検査を終えた配送。回路の更新が成功するまで台帳を排他的に借りる。
pub struct PendingDelivery<'a> {
    ledger: &'a mut RequestLedger,
    updates: Vec<Update>,
    target: TickPosition,
}

type Row = (HostRequestId, u64, ResponseSlot);

spec fn updates_match(entries: Seq<RequestEntry>, updates: Seq<Update>, target: TickPosition) -> bool {
    &&& forall|i: int| 0 <= i < updates.len() ==> {
        let update = #[trigger] updates[i];
        let j = update.index as int;
        &&& 0 <= j < entries.len()
        &&& update.entry.tag == entries[j].tag
        &&& update.entry.response.id_model() == entries[j].response.id_model()
        &&& update.entry.response.issued_model() == entries[j].response.issued_model()
        &&& entries[j].response.status_model() == ResponseStatus::Held(target)
        &&& update.entry.response.status_model() == ResponseStatus::Consumed(target)
    }
    &&& forall|i: int, j: int| 0 <= i < j < updates.len() ==>
        (#[trigger] updates[i]).index != (#[trigger] updates[j]).index
}

/// 消費した要求行のみ変更し、台帳の行の順序と元の要求を保持する。
pub open spec fn delivery_matches(
    before: Seq<Row>, after: Seq<Row>, keys: Seq<ResponseKey>, target: TickPosition,
) -> bool {
    &&& after.len() == before.len()
    &&& forall|i: int| 0 <= i < before.len() ==> {
        let row = #[trigger] before[i];
        if exists|k: int| 0 <= k < keys.len() && (#[trigger] keys[k]).id == row.0
            && (forall|j: int| 0 <= j < i ==> (#[trigger] before[j]).0 != row.0) {
            &&& after[i].0 == row.0
            &&& after[i].1 == row.1
            &&& after[i].2.id_model() == row.2.id_model()
            &&& after[i].2.issued_model() == row.2.issued_model()
            &&& row.2.status_model() == ResponseStatus::Held(target)
            &&& after[i].2.status_model() == ResponseStatus::Consumed(target)
        } else {
            after[i] == row
        }
    }
}

spec fn key_matches_updates(entries: Seq<RequestEntry>, updates: Seq<Update>, keys: Seq<ResponseKey>) -> bool {
    &&& keys.len() == updates.len()
    &&& forall|i: int| 0 <= i < updates.len() ==> {
        let update = #[trigger] updates[i];
        let index = update.index as int;
        &&& keys[i].id == entries[index].response.id_model()
        &&& keys[i].tag == entries[index].tag
        &&& forall|j: int| 0 <= j < index ==> (#[trigger] entries[j]).response.id_model() != keys[i].id
    }
}

fn has_index(updates: &[Update], index: usize) -> (found: bool)
    ensures found <==> exists|i: int| 0 <= i < updates@.len() && (#[trigger] updates@[i]).index == index,
{
    let mut i = 0;
    while i < updates.len()
        invariant
            i <= updates@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] updates@[j]).index != index,
        decreases updates@.len() - i,
    {
        if updates[i].index == index {
            assert(updates@[i as int].index == index);
            return true;
        }
        i += 1;
    }
    false
}

impl RequestLedger {
    /// 入力列の指定位置について、検査順に最初のエラーを選ぶ。
    pub open spec fn delivery_issue_at(
        &self, keys: Seq<ResponseKey>, target: TickPosition, index: usize,
    ) -> Option<DeliveryError> {
        let key = keys[index as int];
        if exists|row: int| #[trigger] self.found_request(key.id, row) {
            let row = choose|row: int| #[trigger] self.found_request(key.id, row);
            if exists|earlier: int| 0 <= earlier < index && (#[trigger] keys[earlier]).id == key.id {
                Some(DeliveryError::Duplicate(index))
            } else if self.requests()[row].1 != key.tag {
                Some(DeliveryError::WrongTag(index))
            } else if self.requests()[row].2.status_model() != ResponseStatus::Held(target) {
                Some(DeliveryError::NotHeld(index))
            } else {
                None
            }
        } else {
            Some(DeliveryError::Unknown(index))
        }
    }

    /// 入力列のすべての応答を指定 tick に配送できることを表す。
    pub open spec fn valid_delivery(&self, keys: Seq<ResponseKey>, target: TickPosition) -> bool {
        !(exists|i: usize| i < keys.len() && #[trigger] self.delivery_issue_at(keys, target, i).is_some())
    }

    /// エラーが入力順で最初の配送エラーであることを表す。
    pub open spec fn first_delivery_error(
        &self, keys: Seq<ResponseKey>, target: TickPosition, error: DeliveryError,
    ) -> bool {
        exists|i: usize| i < keys.len()
            && #[trigger] self.delivery_issue_at(keys, target, i) == Some(error)
            && forall|j: usize| j < i ==> #[trigger] self.delivery_issue_at(keys, target, j).is_none()
    }

    proof fn prior_keys_use_index(
        &self, updates: Seq<Update>, keys: Seq<ResponseKey>, key: ResponseKey, index: int,
    )
        requires self.found_request(key.id, index),
            key_matches_updates(self.entries@, updates, keys),
            forall|i: int| 0 <= i < updates.len() ==> (#[trigger] updates[i]).index < self.entries@.len(),
        ensures
            (exists|k: int| 0 <= k < updates.len() && (#[trigger] updates[k]).index as int == index)
            <==> (exists|k: int| 0 <= k < keys.len() && (#[trigger] keys[k]).id == key.id),
    {
        assert forall|k: int| 0 <= k < keys.len() implies
            ((#[trigger] updates[k]).index as int == index <==> keys[k].id == key.id) by {
            if keys[k].id == key.id {
                let other = updates[k].index as int;
                assert(self.found_request(key.id, other)) by {
                    assert forall|j: int| 0 <= j < other implies (#[trigger] self.requests()[j]).0 != key.id by {
                        assert(self.requests()[j].0 == self.entries@[j].response.id_model());
                    }
                }
                self.found_request_is_unique(key.id, other, index);
            }
        }
        if exists|k: int| 0 <= k < updates.len() && (#[trigger] updates[k]).index as int == index {
            let k = choose|k: int| 0 <= k < updates.len() && (#[trigger] updates[k]).index as int == index;
            assert(keys[k].id == key.id);
        }
        if exists|k: int| 0 <= k < keys.len() && (#[trigger] keys[k]).id == key.id {
            let k = choose|k: int| 0 <= k < keys.len() && (#[trigger] keys[k]).id == key.id;
            assert(updates[k].index as int == index);
        }
    }

    /// 予定時刻とタグを照合し、成功した回路更新に対応する配送を準備する。
    ///
    /// 入力順に見て最初の不一致を返す。確定前は状態を保持する。
    ///
    /// # Errors
    ///
    /// 要求の欠落、重複、タグの不一致、配送時刻の不一致をこの順で検査する。
    pub fn prepare_delivery<'a>(&'a mut self, keys: &[ResponseKey], target: TickPosition)
        -> (result: Result<PendingDelivery<'a>, DeliveryError>)
        ensures
            result.is_ok() <==> old(self).valid_delivery(keys@, target),
            result matches Err(error) ==> {
                &&& *final(self) == *old(self)
                &&& old(self).first_delivery_error(keys@, target, error)
            },
            result matches Ok(pending) ==> {
                &&& pending.before_model() == *old(self)
                &&& pending.after_model() == *final(self)
                &&& pending.keys_model() == keys@
                &&& pending.target_model() == target
            },
    {
        let mut updates = Vec::new();
        let mut i = 0;
        while i < keys.len()
            invariant
                i <= keys@.len(),
                self.entries@ == old(self).entries@,
                self.generation == old(self).generation,
                updates_match(self.entries@, updates@, target),
                key_matches_updates(self.entries@, updates@, keys@.take(i as int)),
                *self == *old(self),
                forall|j: usize| j < i ==> !(#[trigger] old(self).delivery_issue_at(keys@, target, j).is_some()),
            decreases keys@.len() - i,
        {
            let key = keys[i];
            let Some(index) = self.find(key.id) else {
                assert(old(self).delivery_issue_at(keys@, target, i) == Some(DeliveryError::Unknown(i)));
                assert(old(self).delivery_issue_at(keys@, target, i).is_some());
                return Err(DeliveryError::Unknown(i));
            };
            proof {
                assert(self.found_request(key.id, index as int));
                let chosen = choose|row: int| #[trigger] self.found_request(key.id, row);
                self.found_request_is_unique(key.id, index as int, chosen);
                self.prior_keys_use_index(updates@, keys@.take(i as int), key, index as int);
                assert forall|k: int| 0 <= k < i implies (#[trigger] keys@.take(i as int)[k]) == keys@[k] by {};
            }
            if has_index(updates.as_slice(), index) {
                assert(old(self).delivery_issue_at(keys@, target, i) == Some(DeliveryError::Duplicate(i)));
                assert(old(self).delivery_issue_at(keys@, target, i).is_some());
                return Err(DeliveryError::Duplicate(i));
            }
            proof {
                assert forall|k: int| 0 <= k < i implies (#[trigger] keys@[k]).id != key.id by {
                    let prefix = keys@.take(i as int);
                    assert(prefix[k].id == keys@[k].id);
                }
            }
            let mut entry = self.entries[index];
            if entry.tag != key.tag {
                assert(old(self).delivery_issue_at(keys@, target, i) == Some(DeliveryError::WrongTag(i)));
                assert(old(self).delivery_issue_at(keys@, target, i).is_some());
                return Err(DeliveryError::WrongTag(i));
            }
            if !entry.response.consume_at(target) {
                assert(old(self).delivery_issue_at(keys@, target, i) == Some(DeliveryError::NotHeld(i)));
                assert(old(self).delivery_issue_at(keys@, target, i).is_some());
                return Err(DeliveryError::NotHeld(i));
            }
            assert(old(self).delivery_issue_at(keys@, target, i).is_none());
            updates.push(Update { index, entry });
            proof {
                assert(self.requests()[index as int].0 == key.id);
                assert(keys@.take(i as int + 1) =~= keys@.take(i as int).push(key));
                assert forall|j: int| 0 <= j < index implies
                    (#[trigger] self.entries@[j]).response.id_model() != key.id by {
                    assert(self.requests()[j].0 == self.entries@[j].response.id_model());
                }
                assert(updates_match(self.entries@, updates@, target));
                assert(key_matches_updates(self.entries@, updates@, keys@.take(i as int + 1)));
            }
            i += 1;
        }
        assert(keys@.take(i as int) =~= keys@);
        assert(old(self).valid_delivery(keys@, target));
        Ok(PendingDelivery { ledger: self, updates, target })
    }
}

impl<'a> PendingDelivery<'a> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        &&& updates_match(self.ledger.entries@, self.updates@, self.target)
        &&& key_matches_updates(self.ledger.entries@, self.updates@, self.keys_model())
    }

    /// 配送確定前の台帳。
    pub closed spec fn before_model(&self) -> RequestLedger { *self.ledger }

    /// 配送確定または取り消し後の台帳。
    #[verifier::prophetic]
    pub closed spec fn after_model(&self) -> RequestLedger { *final(self.ledger) }

    /// 配送予定の時刻。
    pub closed spec fn target_model(&self) -> TickPosition { self.target }

    /// 検査した要求とタグを入力順に表す。
    pub closed spec fn keys_model(&self) -> Seq<ResponseKey> {
        self.updates@.map_values(|update: Update| ResponseKey {
            id: update.entry.response.id_model(), tag: update.entry.tag,
        })
    }

    /// 回路更新が成功した後に、準備した応答だけを消費済みにする。
    pub fn commit(self)
        ensures
            self.after_model().generation_model() == self.before_model().generation_model(),
            delivery_matches(self.before_model().requests(), self.after_model().requests(),
                self.keys_model(), self.target_model()),
    {
        proof { use_type_invariant(&self); }
        let ghost original = self.before_model();
        let ghost keys = self.keys_model();
        let Self { ledger, updates, target } = self;
        let ghost before = ledger.entries@;
        let mut i = 0;
        while i < updates.len()
            invariant
                i <= updates@.len(),
                ledger.entries@.len() == before.len(),
                ledger.generation == original.generation_model(),
                original.entries@ == before,
                updates_match(before, updates@, target),
                key_matches_updates(before, updates@, keys),
                forall|j: int| 0 <= j < ledger.entries@.len() ==> {
                    let entry = #[trigger] ledger.entries@[j];
                    if exists|k: int| 0 <= k < i && (#[trigger] updates@[k]).index as int == j {
                        exists|k: int| 0 <= k < i && (#[trigger] updates@[k]).index as int == j && entry == updates@[k].entry
                    } else { entry == before[j] }
                },
            decreases updates@.len() - i,
        {
            let update = updates[i];
            assert(update == updates@[i as int]);
            ledger.entries.set(update.index, update.entry);
            i += 1;
        }
        proof {
            let old_rows = original.requests();
            let new_rows = ledger.requests();
            assert(new_rows.len() == old_rows.len());
            assert forall|j: int| 0 <= j < old_rows.len() implies {
                let row = #[trigger] old_rows[j];
                if exists|k: int| 0 <= k < keys.len() && (#[trigger] keys[k]).id == row.0
                    && (forall|h: int| 0 <= h < j ==> (#[trigger] old_rows[h]).0 != row.0) {
                    &&& new_rows[j].0 == row.0
                    &&& new_rows[j].1 == row.1
                    &&& new_rows[j].2.id_model() == row.2.id_model()
                    &&& new_rows[j].2.issued_model() == row.2.issued_model()
                    &&& row.2.status_model() == ResponseStatus::Held(target)
                    &&& new_rows[j].2.status_model() == ResponseStatus::Consumed(target)
                } else {
                    new_rows[j] == row
                }
            } by {
                let row = old_rows[j];
                if exists|k: int| 0 <= k < keys.len() && (#[trigger] keys[k]).id == row.0
                    && (forall|h: int| 0 <= h < j ==> (#[trigger] old_rows[h]).0 != row.0) {
                    let k = choose|k: int| 0 <= k < keys.len() && (#[trigger] keys[k]).id == row.0;
                    let index = updates@[k].index as int;
                    assert(original.found_request(keys[k].id, j));
                    assert(original.found_request(keys[k].id, index)) by {
                        assert forall|h: int| 0 <= h < index implies (#[trigger] old_rows[h]).0 != keys[k].id by {
                            assert(old_rows[h].0 == before[h].response.id_model());
                        }
                    }
                    original.found_request_is_unique(keys[k].id, index, j);
                    let witness = choose|h: int| 0 <= h < i
                        && (#[trigger] updates@[h]).index as int == j && ledger.entries@[j] == updates@[h].entry;
                    if witness != k {
                        assert(updates@[witness].index != updates@[k].index);
                    }
                    assert(ledger.entries@[j] == updates@[k].entry);
                } else if exists|k: int| 0 <= k < i && (#[trigger] updates@[k]).index as int == j {
                    let k = choose|k: int| 0 <= k < i && (#[trigger] updates@[k]).index as int == j;
                    assert(keys[k].id == row.0);
                    assert forall|h: int| 0 <= h < j implies (#[trigger] old_rows[h]).0 != row.0 by {
                        assert(old_rows[h].0 == before[h].response.id_model());
                    }
                    assert(false);
                }
            }
            assert(delivery_matches(old_rows, new_rows, keys, target));
        }
    }

    /// 回路更新を取り消し、台帳を準備前の内容で保持する。
    pub fn cancel(self)
        ensures self.after_model() == self.before_model(),
    {
    }
}

} // verus!
