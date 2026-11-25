//! 要求 ID とデバイス内タグを対応付け、応答の配送まで追跡する。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{HostRequestId, HostResponseError, ResponseSlot, ResponseStatus};
use crate::time::TickPosition;

verus! {

/// 発行済みの要求を台帳に追加できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RegisterRequestError {
    /// 要求 ID が台帳と異なる reset 世代を指す。
    DifferentGeneration,
    /// 同じ要求 ID が登録済みである。
    DuplicateId,
    /// 同じデバイスでこの tick の開始時に使用中のタグである。
    TagInUse,
}

#[derive(Clone, Copy)]
struct RequestEntry {
    tag: u64,
    response: ResponseSlot,
}

/// 同じ reset 世代に発行した要求と応答の台帳。
///
/// タグはホストが同じ識別子に同じ値を割り当てた番号で渡す。番号はデバイス間で共有できる。
/// 消費済みの行も、遅れて届いた重複応答と新規の要求を区別するため世代中は保持する。
pub struct RequestLedger {
    generation: u64,
    entries: Vec<RequestEntry>,
}

impl RequestLedger {

    /// 台帳の reset 世代。
    pub closed spec fn generation_model(&self) -> u64 { self.generation }

    /// 先頭から順に並ぶ要求 ID、タグ番号、応答の状態。
    pub closed spec fn requests(&self) -> Seq<(HostRequestId, u64, ResponseSlot)> {
        self.entries@.map_values(|entry: RequestEntry| (entry.response.id_model(), entry.tag, entry.response))
    }

    /// 指定の世代用に空の台帳を作る。
    pub fn new(generation: u64) -> (ledger: Self)
        ensures ledger.generation_model() == generation, ledger.requests().len() == 0,
    {
        Self { generation, entries: Vec::new() }
    }

    /// 同じデバイスの要求がこの tick の開始時点でタグを占有していることを表す。
    pub open spec fn tag_is_busy(&self, instance: usize, tag: u64, tick: u64) -> bool {
        exists|i: int| 0 <= i < self.requests().len()
            && (#[trigger] self.requests()[i]).0.instance == instance
            && self.requests()[i].1 == tag
            && busy_at(self.requests()[i].2.status_model(), tick)
    }

    /// 世代、要求 ID、タグの順で登録エラーを決める。
    pub open spec fn registration_error(&self, id: HostRequestId, tag: u64, tick: u64) -> Option<RegisterRequestError> {
        if id.generation != self.generation_model() {
            Some(RegisterRequestError::DifferentGeneration)
        } else if exists|i: int| 0 <= i < self.requests().len() && (#[trigger] self.requests()[i]).0 == id {
            Some(RegisterRequestError::DuplicateId)
        } else if self.tag_is_busy(id.instance, tag, tick) {
            Some(RegisterRequestError::TagInUse)
        } else {
            None
        }
    }

    /// 発行済みの要求を登録し、同じデバイスのタグを占有する。
    ///
    /// `tick` は要求を確定した tick 番号。応答を消費したタグはその次の tick から使える。
    ///
    /// # Errors
    ///
    /// 世代の不一致、ID の重複、タグの使用中をこの順で検査する。エラー時は台帳を保持する。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::{
    ///     device::{HostRequestId, HostResponseError, RegisterRequestError, RequestLedger},
    ///     time::TickPosition,
    /// };
    ///
    /// let generation = 3;
    /// let mut ledger = RequestLedger::new(generation);
    /// let id = |instance, serial| HostRequestId { instance, generation, serial };
    /// let delivery = TickPosition { generation, tick: 7 };
    /// ledger.register(id(0, 0), 12, 6).unwrap();
    /// ledger.register(id(1, 1), 12, 6).unwrap();
    ///
    /// assert_eq!(ledger.receive(id(0, 0), delivery), Ok(12));
    /// assert_eq!(ledger.consume_at(id(0, 0), delivery), Some(12));
    /// assert_eq!(ledger.register(id(0, 2), 12, 7), Err(RegisterRequestError::TagInUse));
    /// ledger.register(id(0, 2), 12, 8).unwrap();
    /// assert_eq!(ledger.receive(id(0, 0), delivery), Err(HostResponseError::DuplicateResponse));
    /// ```
    pub fn register(&mut self, id: HostRequestId, tag: u64, tick: u64)
        -> (result: Result<(), RegisterRequestError>)
        ensures
            final(self).generation_model() == old(self).generation_model(),
            match result {
                Ok(()) => {
                    &&& old(self).registration_error(id, tag, tick).is_none()
                    &&& final(self).requests().len() == old(self).requests().len() + 1
                    &&& final(self).requests().drop_last() == old(self).requests()
                    &&& final(self).requests().last().0 == id
                    &&& final(self).requests().last().1 == tag
                    &&& final(self).requests().last().2.id_model() == id
                    &&& final(self).requests().last().2.issued_model() == tick
                    &&& final(self).requests().last().2.status_model() == ResponseStatus::Awaiting
                },
                Err(error) => old(self).registration_error(id, tag, tick) == Some(error) && *final(self) == *old(self),
            },
    {
        if id.generation != self.generation {
            return Err(RegisterRequestError::DifferentGeneration);
        }
        if self.find(id).is_some() {
            return Err(RegisterRequestError::DuplicateId);
        }
        if self.has_busy_tag(id.instance, tag, tick) {
            return Err(RegisterRequestError::TagInUse);
        }
        self.entries.push(RequestEntry { tag, response: ResponseSlot::new(id, tick) });
        assert(self.requests().drop_last() =~= old(self).requests());
        Ok(())
    }

    /// 最初に登録した指定 ID の行を表す。
    pub open spec fn found_request(&self, id: HostRequestId, i: int) -> bool {
        &&& 0 <= i < self.requests().len()
        &&& self.requests()[i].0 == id
        &&& forall|j: int| 0 <= j < i ==> (#[trigger] self.requests()[j]).0 != id
    }

    /// 応答を保留し、デバイスへ渡すタグ番号を返す。
    ///
    /// 呼び出し側は配送先を決め、実 payload の型を検査してから呼び出す。
    ///
    /// # Errors
    ///
    /// 配送先または要求が他世代なら世代エラーを返す。同じ世代では要求 ID を引き、
    /// 重複応答や早すぎる配送を拒否する。エラー時は台帳を保持する。
    pub fn receive(&mut self, id: HostRequestId, position: TickPosition)
        -> (result: Result<u64, HostResponseError>)
        ensures
            final(self).generation_model() == old(self).generation_model(),
            result.is_err() ==> *final(self) == *old(self),
            result == Err(HostResponseError::DifferentGeneration) <==>
                id.generation != old(self).generation_model() || position.generation != old(self).generation_model(),
            match result {
                Ok(tag) => {
                    &&& id.generation == old(self).generation_model() == position.generation
                    &&& exists|i: int| old(self).found_request(id, i)
                        && response_update(
                            old(self).requests(), final(self).requests(), i,
                            ResponseStatus::Awaiting, ResponseStatus::Held(position), tag,
                        )
                        && old(self).requests()[i].2.issued_model() < position.tick
                },
                Err(HostResponseError::DifferentGeneration) =>
                    id.generation != old(self).generation_model() || position.generation != old(self).generation_model(),
                Err(HostResponseError::UnknownRequest) => forall|i: int| 0 <= i < old(self).requests().len()
                    ==> (#[trigger] old(self).requests()[i]).0 != id,
                Err(error) => exists|i: int| old(self).found_request(id, i)
                    && old(self).requests()[i].2.response_error(id, position) == Some(error),
            },
    {
        if id.generation != self.generation || position.generation != self.generation {
            return Err(HostResponseError::DifferentGeneration);
        }
        let Some(index) = self.find(id) else { return Err(HostResponseError::UnknownRequest); };
        let ghost before = self.entries@;
        let mut entry = self.entries[index];
        assert(old(self).found_request(id, index as int));
        entry.response.receive(id, position)?;
        self.entries.set(index, entry);
        proof { self.updated_response(before, index as int); }
        assert(response_update(old(self).requests(), self.requests(), index as int,
            ResponseStatus::Awaiting, ResponseStatus::Held(position), entry.tag));
        assert(old(self).requests()[index as int].2.issued_model() < position.tick);
        Ok(entry.tag)
    }

    /// 確定した配送 tick に一致する応答を消費し、タグ番号を返す。
    ///
    /// 更新の取り消しや失敗時には呼び出さない。配送予定が合わなければ台帳を保持する。
    pub fn consume_at(&mut self, id: HostRequestId, position: TickPosition) -> (result: Option<u64>)
        ensures
            final(self).generation_model() == old(self).generation_model(),
            result.is_none() ==> *final(self) == *old(self),
            result.is_some() <==> exists|i: int| old(self).found_request(id, i)
                && old(self).requests()[i].2.status_model() == ResponseStatus::Held(position),
            result matches Some(tag) ==> exists|i: int| old(self).found_request(id, i)
                && response_update(old(self).requests(), final(self).requests(), i,
                    ResponseStatus::Held(position), ResponseStatus::Consumed(position), tag),
    {
        let Some(index) = self.find(id) else { return None; };
        let ghost before = self.entries@;
        let mut entry = self.entries[index];
        proof {
            assert(old(self).found_request(id, index as int));
            assert forall|i: int| #[trigger] old(self).found_request(id, i) implies i == index by {
                if i < index {
                    assert(old(self).requests()[i].0 != id);
                } else if index < i {
                    assert(old(self).requests()[index as int].0 != id);
                }
            }
        }
        if !entry.response.consume_at(position) {
            assert(old(self).requests()[index as int].2.status_model() != ResponseStatus::Held(position));
            return None;
        }
        self.entries.set(index, entry);
        proof { self.updated_response(before, index as int); }
        assert(response_update(old(self).requests(), self.requests(), index as int,
            ResponseStatus::Held(position), ResponseStatus::Consumed(position), entry.tag));
        Some(entry.tag)
    }

    proof fn updated_response(&self, before: Seq<RequestEntry>, index: int)
        requires
            0 <= index < before.len(),
            self.entries@ == before.update(index, self.entries@[index]),
        ensures
            self.requests() == before.map_values(|entry: RequestEntry| {
                (entry.response.id_model(), entry.tag, entry.response)
            }).update(index, self.requests()[index]),
    {
        assert(self.requests() =~= before.map_values(|entry: RequestEntry| {
            (entry.response.id_model(), entry.tag, entry.response)
        }).update(index, self.requests()[index]));
    }

    fn find(&self, id: HostRequestId) -> (result: Option<usize>)
        ensures match result {
            Some(index) => {
                &&& index < self.requests().len()
                &&& self.requests()[index as int].0 == id
                &&& forall|i: int| 0 <= i < index ==> (#[trigger] self.requests()[i]).0 != id
            },
            None => forall|i: int| 0 <= i < self.requests().len() ==> (#[trigger] self.requests()[i]).0 != id,
        },
    {
        let mut index = 0;
        while index < self.entries.len()
            invariant
                index <= self.entries@.len(),
                forall|i: int| 0 <= i < index ==> (#[trigger] self.requests()[i]).0 != id,
            decreases self.entries@.len() - index,
        {
            let entry = &self.entries[index];
            assert(self.requests()[index as int].0 == entry.response.id_model());
            let found = entry.response.id();
            if found.instance == id.instance && found.serial == id.serial && found.generation == id.generation {
                assert(found == id);
                return Some(index);
            }
            index += 1;
        }
        None
    }

    fn has_busy_tag(&self, instance: usize, tag: u64, tick: u64) -> (busy: bool)
        ensures busy == self.tag_is_busy(instance, tag, tick),
    {
        let mut index = 0;
        while index < self.entries.len()
            invariant
                index <= self.entries@.len(),
                forall|i: int| 0 <= i < index ==>
                    (#[trigger] self.requests()[i]).0.instance != instance
                    || self.requests()[i].1 != tag || !busy_at(self.requests()[i].2.status_model(), tick),
            decreases self.entries@.len() - index,
        {
            let entry = &self.entries[index];
            assert(self.requests()[index as int] == (entry.response.id_model(), entry.tag, entry.response));
            if entry.response.id().instance == instance && entry.tag == tag {
                let occupied = match entry.response.status() {
                    ResponseStatus::Consumed(delivered) => tick <= delivered.tick,
                    ResponseStatus::Awaiting | ResponseStatus::Held(_) => true,
                };
                if occupied {
                    assert(busy_at(self.requests()[index as int].2.status_model(), tick));
                    assert(self.tag_is_busy(instance, tag, tick));
                    return true;
                }
            }
            index += 1;
        }
        false
    }
}

/// 元の行と同じ要求を保ち、指定した応答状態だけを更新する。
pub open spec fn response_update(
    before: Seq<(HostRequestId, u64, ResponseSlot)>, after: Seq<(HostRequestId, u64, ResponseSlot)>,
    index: int, from: ResponseStatus, to: ResponseStatus, tag: u64,
) -> bool {
    &&& 0 <= index < before.len() == after.len()
    &&& after == before.update(index, after[index])
    &&& before[index].0 == after[index].0
    &&& before[index].1 == after[index].1 == tag
    &&& before[index].2.id_model() == after[index].2.id_model()
    &&& before[index].2.issued_model() == after[index].2.issued_model()
    &&& before[index].2.status_model() == from
    &&& after[index].2.status_model() == to
}

/// 応答を消費した tick までタグを占有する。
pub open spec fn busy_at(status: ResponseStatus, tick: u64) -> bool {
    match status {
        ResponseStatus::Consumed(delivered) => tick <= delivered.tick,
        _ => true,
    }
}

} // verus!
