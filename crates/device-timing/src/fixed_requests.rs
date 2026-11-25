//! 固定容量のスロットで要求と応答を対応付ける。

#[cfg(not(verus_only))]
use verus_builtin_macros::verus;
#[cfg(verus_only)]
use vstd::prelude::*;

use super::{
    ClockError, HostRequestId, HostResponseError, RequestIdError, RequestIds, RequestKey,
    ResponseSlot, ResponseStatus, SimulationClock, TickPosition,
};

verus! {

broadcast use vstd::array::group_array_axioms;

/// 固定容量の台帳で要求を発行できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FixedIssueError {
    /// 最初の tick が確定していない。
    BeforeFirstTick,
    /// 同じインスタンスでこの tick の開始時に使用中のタグだった。
    TagInUse,
    /// 発行中または配送待ちの要求で全スロットを使っている。
    Capacity,
    /// 同じ世代で使える通し番号が残っていない。
    Number(RequestIdError),
}

/// 固定容量の台帳で応答を受理できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FixedReceiveError {
    /// 世代、要求 ID、受理状況または配送予定の違反。
    Response(HostResponseError),
    /// 発行済みの範囲に入る通し番号に、現在の要求が対応しない。
    ///
    /// インスタンスを含む ID 全体が、過去に発行されたことまでは示さない。
    Retired,
}

/// 台帳の論理 tick を進められなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FixedTickError {
    /// 現在の tick で受け取る応答が残っている。
    PendingDelivery,
    /// 次の tick 番号を表せない。
    Clock(ClockError),
}

/// 一つのスロットにある発行済みの要求と保持中の応答。
#[derive(Clone, Copy)]
pub struct FixedRequestRow<R: Copy> {
    /// 要求元のインスタンスとデバイス内のタグ。
    pub key: RequestKey,
    /// 受理したかどうかと配送先の tick。
    pub response: ResponseSlot,
    /// 応答受理後から配送まで保持する値。
    pub payload: Option<R>,
}

/// 要求の発行と応答の受理・配送を、同じ世代と論理 tick で管理する。
///
/// 容量 `N` は応答待ちと配送待ちを合わせた上限。配送後はスロットを再利用する。
/// 配送したタグは、その tick の間だけ対応するスロットに記録する。
pub struct FixedRequestLedger<R: Copy, const N: usize> {
    clock: SimulationClock,
    ids: RequestIds,
    rows: [Option<FixedRequestRow<R>>; N],
    delivered_tags: [Option<RequestKey>; N],
}

spec fn active_at<R: Copy>(rows: Seq<Option<FixedRequestRow<R>>>, id: HostRequestId, i: int) -> bool {
    0 <= i < rows.len() && (rows[i] matches Some(row) && row.response.id_model() == id)
}

/// スロットに、指定時刻に配送する応答が保持されていることを表す。
pub open spec fn delivery_due_at<R: Copy>(rows: Seq<Option<FixedRequestRow<R>>>, at: TickPosition, i: int) -> bool {
    0 <= i < rows.len() && (rows[i] matches Some(row) && row.response.status_model() == ResponseStatus::Held(at))
}

spec fn busy_key<R: Copy>(rows: Seq<Option<FixedRequestRow<R>>>, tags: Seq<Option<RequestKey>>,
    key: RequestKey, i: int,
) -> bool {
    &&& 0 <= i < rows.len()
    &&& (tags[i] == Some(key) || (rows[i] matches Some(row) && row.key == key))
}

spec fn valid_row<R: Copy>(row: Option<FixedRequestRow<R>>, tag: Option<RequestKey>,
    at: TickPosition, next: int,
) -> bool {
    if let Some(active) = row {
        &&& active.response.id_model().generation == at.generation
        &&& active.response.id_model().instance == active.key.instance
        &&& active.response.id_model().serial < next
        &&& active.response.issued_model() <= at.tick
        &&& tag.is_some() ==> active.response.issued_model() == at.tick
        &&& match active.response.status_model() {
            ResponseStatus::Awaiting => active.payload.is_none(),
            ResponseStatus::Held(delivery) => active.payload.is_some()
                && delivery.generation == at.generation && delivery.tick >= at.tick
                && delivery.tick > active.response.issued_model(),
            ResponseStatus::Consumed(_) => false,
        }
    } else { true }
}

spec fn serials_differ<R: Copy>(left: Option<FixedRequestRow<R>>, right: Option<FixedRequestRow<R>>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => left.response.id_model().serial != right.response.id_model().serial,
        _ => true,
    }
}

impl<R: Copy, const N: usize> FixedRequestLedger<R, N> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        &&& self.ids.generation_model() == self.clock.position_model().generation
        &&& forall|i: int| 0 <= i < N ==> #[trigger] valid_row(self.rows@[i], self.delivered_tags@[i],
            self.clock.position_model(), self.ids.next_model())
        &&& forall|i: int, j: int| 0 <= i < j < N ==> #[trigger] serials_differ(self.rows@[i], self.rows@[j])
    }

    /// 台帳で最後に確定した論理時刻。
    pub closed spec fn position_model(&self) -> TickPosition { self.clock.position_model() }
    /// 現世代で次に発行する通し番号。
    pub closed spec fn next_serial_model(&self) -> int { self.ids.next_model() }
    /// スロット順で並んだ応答待ちまたは配送待ちの要求。
    pub closed spec fn rows_model(&self) -> Seq<Option<FixedRequestRow<R>>> { self.rows@ }
    /// 現在の tick で消費し、同じ tick の間は再利用できないタグ。
    pub closed spec fn delivered_tags_model(&self) -> Seq<Option<RequestKey>> { self.delivered_tags@ }

    /// 現在の tick に配送する応答が残っていることを表す。
    pub closed spec fn has_due_response(&self) -> bool {
        exists|i: int| #[trigger] delivery_due_at(self.rows_model(), self.position_model(), i)
    }

    /// 指定された要求に対応する現役スロットを表す。
    pub closed spec fn holds_request(&self, id: HostRequestId, i: int) -> bool {
        active_at(self.rows_model(), id, i)
    }

    /// 現役の要求、または現在の tick で消費した応答がタグを占有することを表す。
    pub closed spec fn tag_in_use(&self, key: RequestKey) -> bool {
        exists|i: int| #[trigger] busy_key(self.rows_model(), self.delivered_tags_model(), key, i)
    }

    /// 同じ世代で、安全に受理できない応答の理由を優先順で選ぶ。
    pub closed spec fn receive_error(&self, id: HostRequestId, delivery: TickPosition) -> Option<FixedReceiveError> {
        if id.generation != self.position_model().generation || delivery.generation != self.position_model().generation {
            Some(FixedReceiveError::Response(HostResponseError::DifferentGeneration))
        } else if exists|i: int| #[trigger] self.holds_request(id, i) {
            let i = choose|i: int| #[trigger] self.holds_request(id, i);
            let row = self.rows_model()[i].unwrap();
            if let Some(error) = row.response.response_error(id, delivery) {
                Some(FixedReceiveError::Response(error))
            } else if delivery.tick <= self.position_model().tick {
                Some(FixedReceiveError::Response(HostResponseError::TooEarly))
            } else {
                None
            }
        } else if id.serial < self.next_serial_model() {
            Some(FixedReceiveError::Retired)
        } else {
            Some(FixedReceiveError::Response(HostResponseError::UnknownRequest))
        }
    }

    /// 容量を使い切る場合を含め、発行を拒否する理由を優先順で選ぶ。
    pub closed spec fn issue_error(&self, key: RequestKey) -> Option<FixedIssueError> {
        if self.position_model().tick == 0 { Some(FixedIssueError::BeforeFirstTick) }
        else if self.tag_in_use(key) { Some(FixedIssueError::TagInUse) }
        else if forall|i: int| 0 <= i < self.rows_model().len() ==> (#[trigger] self.rows_model()[i]).is_some() {
            Some(FixedIssueError::Capacity)
        } else if !self.ids.fits(1) { Some(FixedIssueError::Number(RequestIdError::SerialOutOfRange)) }
        else { None }
    }

    /// 世代0の tick 0 で空の台帳を作る。容量が0の場合も作成できる。
    pub fn new() -> (ledger: Self)
        ensures
            ledger.position_model() == (TickPosition { generation: 0, tick: 0 }),
            ledger.next_serial_model() == 0,
            ledger.rows_model() == Seq::new(N as nat, |i: int| None),
            ledger.delivered_tags_model() == Seq::new(N as nat, |i: int| None),
    {
        Self::empty_clock(SimulationClock::new())
    }

    fn empty_clock(clock: SimulationClock) -> (ledger: Self)
        ensures
            ledger.position_model() == clock.position_model(),
            ledger.next_serial_model() == 0,
            ledger.rows_model() == Seq::new(N as nat, |i: int| None),
            ledger.delivered_tags_model() == Seq::new(N as nat, |i: int| None),
    {
        let at = clock.position();
        let ids = RequestIds::new(at.generation);
        let rows: [Option<FixedRequestRow<R>>; N] = [None; N];
        let delivered_tags: [Option<RequestKey>; N] = [None; N];
        assert(rows@ =~= Seq::new(N as nat, |i: int| None));
        assert(delivered_tags@ =~= Seq::new(N as nat, |i: int| None));
        assert forall|i: int| 0 <= i < N implies
            #[trigger] valid_row(rows@[i], delivered_tags@[i], at, ids.next_model()) by {
            assert(rows@[i].is_none());
        };
        assert forall|i: int, j: int| 0 <= i < j < N implies
            #[trigger] serials_differ(rows@[i], rows@[j]) by {
            assert(rows@[i].is_none());
        };
        Self { clock, ids, rows, delivered_tags }
    }

    /// 最後に確定した論理時刻を返す。
    pub fn position(&self) -> (position: TickPosition)
        ensures position == self.position_model(),
    { self.clock.position() }

    proof fn unique_request(&self, id: HostRequestId, left: int, right: int)
        requires self.valid(), self.holds_request(id, left), self.holds_request(id, right),
        ensures left == right,
    {
        if left < right { assert(serials_differ(self.rows@[left], self.rows@[right])); }
        else if right < left { assert(serials_differ(self.rows@[right], self.rows@[left])); }
    }

    fn find(&self, id: HostRequestId) -> (row: Option<usize>)
        ensures match row {
            Some(index) => self.holds_request(id, index as int),
            None => forall|i: int| !#[trigger] self.holds_request(id, i),
        },
    {
        let mut i = 0;
        while i < N
            invariant i <= N,
                forall|j: int| 0 <= j < i ==> !#[trigger] self.holds_request(id, j),
            decreases N - i,
        {
            if let Some(row) = self.rows[i] {
                let found = row.response.id();
                if found.generation == id.generation && found.serial == id.serial && found.instance == id.instance {
                    assert(found == id);
                    return Some(i);
                }
            }
            assert(!self.holds_request(id, i as int));
            i += 1;
        }
        None
    }

    fn first_free(&self) -> (row: Option<usize>)
        ensures match row {
            Some(index) => index < N && self.rows_model()[index as int].is_none()
                && forall|i: int| 0 <= i < index ==> (#[trigger] self.rows_model()[i]).is_some(),
            None => forall|i: int| 0 <= i < N ==> (#[trigger] self.rows_model()[i]).is_some(),
        },
    {
        let mut i = 0;
        while i < N
            invariant i <= N, forall|j: int| 0 <= j < i ==> (#[trigger] self.rows_model()[j]).is_some(),
            decreases N - i,
        {
            if self.rows[i].is_none() { return Some(i); }
            assert(self.rows_model()[i as int].is_some());
            i += 1;
        }
        None
    }

    fn tag_busy(&self, key: RequestKey) -> (busy: bool)
        ensures busy == self.tag_in_use(key),
    {
        let mut i = 0;
        while i < N
            invariant i <= N,
                forall|j: int| 0 <= j < i ==> !#[trigger] busy_key(self.rows_model(), self.delivered_tags_model(), key, j),
            decreases N - i,
        {
            if let Some(tag) = self.delivered_tags[i] {
                if tag.instance == key.instance && tag.tag == key.tag {
                    assert(tag == key);
                    assert(busy_key(self.rows_model(), self.delivered_tags_model(), key, i as int));
                    return true;
                }
            }
            if let Some(row) = self.rows[i] {
                if row.key.instance == key.instance && row.key.tag == key.tag {
                    assert(row.key == key);
                    assert(busy_key(self.rows_model(), self.delivered_tags_model(), key, i as int));
                    return true;
                }
            }
            assert(!busy_key(self.rows_model(), self.delivered_tags_model(), key, i as int));
            i += 1;
        }
        false
    }

    fn has_due(&self) -> (has_due: bool)
        ensures has_due == self.has_due_response(),
    {
        let position = self.clock.position();
        let mut i = 0;
        while i < N
            invariant i <= N, position == self.position_model(),
                forall|j: int| 0 <= j < i ==> !#[trigger] delivery_due_at(self.rows_model(), position, j),
            decreases N - i,
        {
            if let Some(row) = self.rows[i] {
                if let ResponseStatus::Held(delivery) = row.response.status() {
                    if delivery.generation == position.generation && delivery.tick == position.tick {
                        assert(delivery == position);
                        assert(delivery_due_at(self.rows_model(), position, i as int));
                        return true;
                    }
                }
            }
            assert(!delivery_due_at(self.rows_model(), position, i as int));
            i += 1;
        }
        false
    }

    /// 現在の tick の更新を終え、同じ世代の次の tick に進む。
    ///
    /// 回路とデバイスの更新結果を採用するときに呼ぶ。次の tick へ渡す応答は
    /// 先に [Self::peek_at] で参照できる。現在の tick で消費したタグはここで解放する。
    ///
    /// # Errors
    ///
    /// 現在の tick の応答が残っている場合、または次の tick を表せない場合は状態を保持する。
    pub fn advance_tick(&mut self) -> (result: Result<TickPosition, FixedTickError>)
        ensures
            result.is_err() ==> *final(self) == *old(self),
            match result {
                Ok(position) => {
                    &&& !old(self).has_due_response()
                    &&& position == final(self).position_model()
                    &&& position.generation == old(self).position_model().generation
                    &&& position.tick as int == old(self).position_model().tick as int + 1
                    &&& final(self).rows_model() == old(self).rows_model()
                    &&& final(self).next_serial_model() == old(self).next_serial_model()
                    &&& final(self).delivered_tags_model() == Seq::new(N as nat, |i: int| None)
                },
                Err(FixedTickError::PendingDelivery) => old(self).has_due_response(),
                Err(FixedTickError::Clock(error)) => !old(self).has_due_response()
                    && error == ClockError::TickOutOfRange && old(self).position_model().tick == u64::MAX,
            },
    {
        proof { use_type_invariant(&*self); }
        let ghost current = self.position_model();
        if self.has_due() { return Err(FixedTickError::PendingDelivery); }
        let change = match self.clock.prepare_tick() {
            Ok(change) => change,
            Err(error) => return Err(FixedTickError::Clock(error)),
        };
        let target = change.target();
        let Ok(clock) = self.clock.project(change) else { unreachable!() };
        let tags: [Option<RequestKey>; N] = [None; N];
        proof {
            assert(tags@ =~= Seq::new(N as nat, |i: int| None));
            assert forall|i: int| 0 <= i < N implies
                #[trigger] valid_row(self.rows@[i], tags@[i], current, self.ids.next_model()) by {
                assert(valid_row(self.rows@[i], self.delivered_tags@[i], current, self.ids.next_model()));
            };
            assert forall|i: int| 0 <= i < N implies
                #[trigger] valid_row(self.rows@[i], tags@[i], target, self.ids.next_model()) by {
                assert(valid_row(self.rows@[i], self.delivered_tags@[i], current, self.ids.next_model()));
                assert(current == self.position_model());
                assert(!delivery_due_at(self.rows_model(), self.position_model(), i));
            };
        }
        self.delivered_tags = tags;
        self.clock = clock;
        Ok(target)
    }

    /// 回路とデバイスが reset に成功した後で、次の世代の tick 0 を確定する。
    ///
    /// # Errors
    ///
    /// 次の世代を表せない場合、または指定した時刻が次世代の tick 0 でなければ状態を保持する。
    pub fn reset(&mut self, target: TickPosition) -> (result: Result<(), ClockError>)
        ensures
            result.is_err() ==> *final(self) == *old(self),
            match result {
                Ok(()) => final(self).position_model() == target
                    && target.generation as int == old(self).position_model().generation as int + 1
                    && target.tick == 0 && final(self).next_serial_model() == 0
                    && final(self).rows_model() == Seq::new(N as nat, |i: int| None)
                    && final(self).delivered_tags_model() == Seq::new(N as nat, |i: int| None),
                Err(ClockError::GenerationOutOfRange) => old(self).position_model().generation == u64::MAX,
                Err(ClockError::StaleChange) => old(self).position_model().generation < u64::MAX
                    && (target.generation as int != old(self).position_model().generation as int + 1 || target.tick != 0),
                _ => false,
            },
    {
        let change = self.clock.prepare_reset()?;
        let next = change.target();
        if target.generation != next.generation || target.tick != next.tick {
            return Err(ClockError::StaleChange);
        }
        assert(target == next);
        let clock = self.clock.project(change)?;
        *self = Self::empty_clock(clock);
        Ok(())
    }

    /// 指定スロットに新しい要求を追加し、ほかの行を保持したことを表す。
    pub closed spec fn issued_at(&self, before: &Self, key: RequestKey, id: HostRequestId, i: int) -> bool {
        &&& self.holds_request(id, i)
        &&& before.rows_model()[i].is_none()
        &&& forall|j: int| 0 <= j < i ==> (#[trigger] before.rows_model()[j]).is_some()
        &&& self.rows_model() == before.rows_model().update(i, self.rows_model()[i])
        &&& {
            let row = self.rows_model()[i].unwrap();
            &&& row.key == key
            &&& row.response.issued_model() == before.position_model().tick
            &&& row.response.status_model() == ResponseStatus::Awaiting
            &&& row.payload.is_none()
        }
    }

    /// 確定済みの現在の tick に要求を1件発行する。
    ///
    /// 呼び出し順で ID を付ける。確定した回路更新の要求を実行設定と各要求リストの順で渡す。
    ///
    /// # Errors
    ///
    /// tick 0、占有中のタグ、空きスロット不足、通し番号の枯渇を順に検査する。
    /// 拒否時は通し番号も要求の状態も保持する。
    pub fn issue(&mut self, key: RequestKey) -> (result: Result<HostRequestId, FixedIssueError>)
        ensures
            result.is_err() ==> *final(self) == *old(self),
            match result {
                Ok(id) => {
                    &&& old(self).issue_error(key).is_none()
                    &&& id.instance == key.instance
                    &&& id.generation == old(self).position_model().generation
                    &&& id.serial as int == old(self).next_serial_model()
                    &&& final(self).next_serial_model() == old(self).next_serial_model() + 1
                    &&& final(self).position_model() == old(self).position_model()
                    &&& final(self).delivered_tags_model() == old(self).delivered_tags_model()
                    &&& exists|i: int| #[trigger] final(self).issued_at(old(self), key, id, i)
                },
                Err(error) => old(self).issue_error(key) == Some(error),
            },
    {
        proof { use_type_invariant(&*self); }
        let current = self.clock.position();
        if current.tick == 0 { return Err(FixedIssueError::BeforeFirstTick); }
        if self.tag_busy(key) { return Err(FixedIssueError::TagInUse); }
        let Some(index) = self.first_free() else { return Err(FixedIssueError::Capacity); };
        let (ids, id) = match self.ids.next_request(key.instance) {
            Ok(next) => next,
            Err(error) => return Err(FixedIssueError::Number(error)),
        };
        assert(old(self).issue_error(key).is_none());
        let response = ResponseSlot::new(id, current.tick);
        let row = FixedRequestRow { key, response, payload: None };
        proof {
            let index = index as int;
            let rows = self.rows@.update(index, Some(row));
            assert(rows.len() == N);
            assert forall|i: int| 0 <= i < N implies
                #[trigger] valid_row(self.rows@[i], self.delivered_tags@[i], current, ids.next_model()) by {
                assert(valid_row(self.rows@[i], self.delivered_tags@[i], current, self.ids.next_model()));
            };
            assert forall|i: int| 0 <= i < N implies
                #[trigger] valid_row(rows[i], self.delivered_tags@[i], current, ids.next_model()) by {
                if i != index {
                    assert(valid_row(self.rows@[i], self.delivered_tags@[i], current, self.ids.next_model()));
                }
            };
            assert forall|i: int, j: int| 0 <= i < j < N implies #[trigger] serials_differ(rows[i], rows[j]) by {
                if i == index {
                    assert(valid_row(self.rows@[j], self.delivered_tags@[j], current, self.ids.next_model()));
                } else if j == index {
                    assert(valid_row(self.rows@[i], self.delivered_tags@[i], current, self.ids.next_model()));
                } else {
                    assert(serials_differ(self.rows@[i], self.rows@[j]));
                }
            };
        }
        self.ids = ids;
        self.rows[index] = Some(row);
        proof {
            let i = index as int;
            assert(self.holds_request(id, i));
            assert(old(self).rows_model()[i].is_none());
            assert(self.rows_model() == old(self).rows_model().update(i, Some(row)));
            assert(self.rows_model()[i] == Some(row));
            assert forall|j: int| 0 <= j < i implies (#[trigger] old(self).rows_model()[j]).is_some() by {};
            assert(self.issued_at(old(self), key, id, i));
            assert(id.generation == old(self).position_model().generation);
            assert(id.serial as int == old(self).next_serial_model());
            assert(self.next_serial_model() == old(self).next_serial_model() + 1);
        }
        Ok(id)
    }

    /// 同じ世代の要求への応答を、未来の配送 tick まで保留する。
    ///
    /// # Errors
    ///
    /// 世代、要求 ID、受理済みかどうか、配送時刻の順で検査する。
    /// エラー時は応答もタグも変更しない。デバイスが必要とする payload の型は呼び出し側で照合する。
    pub fn receive(&mut self, id: HostRequestId, delivery: TickPosition, payload: R)
        -> (result: Result<(), FixedReceiveError>)
        ensures
            result.is_err() ==> *final(self) == *old(self),
            match result {
                Ok(()) => {
                    &&& old(self).receive_error(id, delivery).is_none()
                    &&& final(self).position_model() == old(self).position_model()
                    &&& final(self).next_serial_model() == old(self).next_serial_model()
                    &&& final(self).delivered_tags_model() == old(self).delivered_tags_model()
                    &&& exists|i: int| #[trigger] old(self).holds_request(id, i)
                        && final(self).holds_request(id, i)
                        && final(self).rows_model() == old(self).rows_model().update(i, final(self).rows_model()[i])
                        && {
                            let before = old(self).rows_model()[i].unwrap();
                            let after = final(self).rows_model()[i].unwrap();
                            &&& before.key == after.key
                            &&& before.response.issued_model() == after.response.issued_model()
                            &&& before.response.status_model() == ResponseStatus::Awaiting
                            &&& after.response.status_model() == ResponseStatus::Held(delivery)
                            &&& after.payload == Some(payload)
                        }
                },
                Err(error) => old(self).receive_error(id, delivery) == Some(error),
            },
    {
        proof { use_type_invariant(&*self); }
        let current = self.clock.position();
        if id.generation != current.generation || delivery.generation != current.generation {
            return Err(FixedReceiveError::Response(HostResponseError::DifferentGeneration));
        }
        let Some(index) = self.find(id) else {
            return Err(if self.ids.contains_serial(id.serial) { FixedReceiveError::Retired }
                else { FixedReceiveError::Response(HostResponseError::UnknownRequest) });
        };
        proof {
            let i = choose|i: int| #[trigger] self.holds_request(id, i);
            self.unique_request(id, index as int, i);
        }
        let Some(mut row) = self.rows[index] else { unreachable!() };
        if let Err(error) = row.response.receive(id, delivery) {
            return Err(FixedReceiveError::Response(error));
        }
        if delivery.tick <= current.tick {
            return Err(FixedReceiveError::Response(HostResponseError::TooEarly));
        }
        row.payload = Some(payload);
        proof {
            let index = index as int;
            let rows = self.rows@.update(index, Some(row));
            assert forall|i: int| 0 <= i < N implies
                #[trigger] valid_row(rows[i], self.delivered_tags@[i], current, self.ids.next_model()) by {
                assert(valid_row(self.rows@[i], self.delivered_tags@[i], current, self.ids.next_model()));
            };
            assert forall|i: int, j: int| 0 <= i < j < N implies #[trigger] serials_differ(rows[i], rows[j]) by {
                assert(serials_differ(self.rows@[i], self.rows@[j]));
            };
        }
        self.rows[index] = Some(row);
        assert(self.holds_request(id, index as int));
        Ok(())
    }

    /// 配送予定が一致する応答のタグと値を返す。台帳の状態は変更しない。
    pub fn peek_at(&self, id: HostRequestId, delivery: TickPosition) -> (result: Option<(u64, R)>)
        ensures
            result.is_some() <==> exists|i: int| self.holds_request(id, i)
                && #[trigger] delivery_due_at(self.rows_model(), delivery, i),
            result matches Some((tag, payload)) ==> exists|i: int|
                self.holds_request(id, i) && #[trigger] delivery_due_at(self.rows_model(), delivery, i) && {
                    let row = self.rows_model()[i].unwrap();
                    row.key.tag == tag && row.payload == Some(payload)
                },
    {
        proof { use_type_invariant(self); }
        let index = self.find(id)?;
        let Some(row) = self.rows[index] else { unreachable!() };
        let ResponseStatus::Held(target) = row.response.status() else {
            proof {
                assert forall|i: int| #[trigger] self.holds_request(id, i) implies i == index by {
                    self.unique_request(id, index as int, i);
                };
            }
            return None;
        };
        if delivery.tick != target.tick || delivery.generation != target.generation {
            proof {
                assert forall|i: int| #[trigger] self.holds_request(id, i) implies i == index by {
                    self.unique_request(id, index as int, i);
                };
            }
            return None;
        }
        assert(target == delivery);
        assert(delivery_due_at(self.rows_model(), delivery, index as int));
        assert(valid_row(self.rows@[index as int], self.delivered_tags@[index as int], self.position_model(), self.ids.next_model()));
        let Some(payload) = row.payload else { unreachable!() };
        Some((row.key.tag, payload))
    }

    /// 現在の tick に配送する応答を1回だけ取り出し、スロットを解放する。
    ///
    /// 更新を採用した後に呼び出す。同じ tick 中は応答のタグを再利用できない。
    /// 要求 ID または配送予定が合わなければ `None` を返し、状態を保持する。
    pub fn consume(&mut self, id: HostRequestId) -> (result: Option<(u64, R)>)
        ensures
            result.is_none() ==> *final(self) == *old(self),
            result.is_some() <==> exists|i: int| old(self).holds_request(id, i)
                && #[trigger] delivery_due_at(old(self).rows_model(), old(self).position_model(), i),
            result matches Some((tag, payload)) ==> {
                &&& final(self).position_model() == old(self).position_model()
                &&& final(self).next_serial_model() == old(self).next_serial_model()
                &&& exists|i: int| old(self).holds_request(id, i)
                    && #[trigger] delivery_due_at(old(self).rows_model(), old(self).position_model(), i)
                    && final(self).rows_model() == old(self).rows_model().update(i, None)
                    && {
                        let row = old(self).rows_model()[i].unwrap();
                        &&& row.key.tag == tag
                        &&& row.payload == Some(payload)
                        &&& old(self).delivered_tags_model()[i].is_none()
                        &&& final(self).delivered_tags_model() == old(self).delivered_tags_model().update(i, Some(row.key))
                    }
                &&& forall|i: int| !#[trigger] final(self).holds_request(id, i)
            },
    {
        proof { use_type_invariant(&*self); }
        let current = self.clock.position();
        let index = self.find(id)?;
        let Some(mut row) = self.rows[index] else { unreachable!() };
        proof {
            assert forall|i: int| #[trigger] old(self).holds_request(id, i) implies i == index by {
                old(self).unique_request(id, index as int, i);
            };
        }
        if !row.response.consume_at(current) { return None; }
        assert(delivery_due_at(old(self).rows_model(), current, index as int));
        assert(valid_row(self.rows@[index as int], self.delivered_tags@[index as int], current, self.ids.next_model()));
        assert(self.delivered_tags@[index as int].is_none());
        let Some(payload) = row.payload else { unreachable!() };
        proof {
            let rows = self.rows@.update(index as int, None);
            let tags = self.delivered_tags@.update(index as int, Some(row.key));
            assert forall|i: int| 0 <= i < N implies
                #[trigger] valid_row(rows[i], self.delivered_tags@[i], current, self.ids.next_model()) by {
                if i != index {
                    assert(valid_row(self.rows@[i], self.delivered_tags@[i], current, self.ids.next_model()));
                }
            };
            assert forall|i: int| 0 <= i < N implies
                #[trigger] valid_row(rows[i], tags[i], current, self.ids.next_model()) by {
                if i != index {
                    assert(valid_row(self.rows@[i], self.delivered_tags@[i], current, self.ids.next_model()));
                }
            };
            assert(rows.len() == N);
            assert forall|i: int, j: int| 0 <= i < j < N implies #[trigger] serials_differ(rows[i], rows[j]) by {
                if i == index { assert(rows[i].is_none()); }
                else if j == index { assert(rows[j].is_none()); }
                else { assert(serials_differ(self.rows@[i], self.rows@[j])); }
            };
        }
        self.rows[index] = None;
        self.delivered_tags[index] = Some(row.key);
        proof {
            assert forall|i: int| !#[trigger] self.holds_request(id, i) by {
                if self.holds_request(id, i) { assert(old(self).holds_request(id, i)); }
            };
        }
        proof {
            let i = index as int;
            let entry = old(self).rows_model()[i].unwrap();
            assert(old(self).holds_request(id, i));
            assert(delivery_due_at(old(self).rows_model(), old(self).position_model(), i));
            assert(self.rows_model() == old(self).rows_model().update(i, None));
            assert(self.delivered_tags_model() == old(self).delivered_tags_model().update(i, Some(entry.key)));
            assert(entry.key == row.key && entry.payload == Some(payload));
        }
        Some((row.key.tag, payload))
    }

}

} // verus!
