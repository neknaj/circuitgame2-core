//! tick 開始時に参照するイベントと、確定後まで保留するイベント列を管理する。

use alloc::{collections::VecDeque, vec::Vec};
use vstd::prelude::*;

use super::{EventTimeStatus, TickPosition, classify_event_time};

verus! {

/// ホストのイベントと、それを適用する世代および tick。
pub struct ScheduledEvent<T> {
    /// 適用する世代と tick。時刻の割り当てはホストが行う。
    pub position: TickPosition,
    /// デバイスに渡す入力または照合済みの応答。
    pub payload: T,
}

/// 到着順を保った、未消費イベントの列。
pub struct ScheduledEvents<T> {
    pending: VecDeque<ScheduledEvent<T>>,
}


/// 1回の tick の開始時に固定したイベント列。
///
/// 準備中は列を排他的に借りるため、評価途中に到着したイベントを同じ tick に追加できない。
pub struct PendingEvents<'a, T> {
    events: &'a mut ScheduledEvents<T>,
    target: TickPosition,
}

/// `from` 以降の最初の対象イベントとその添字を表す。
pub open spec fn next_event_matches<T>(
    events: Seq<ScheduledEvent<T>>, target: TickPosition, from: usize,
    result: Option<(usize, &ScheduledEvent<T>)>,
) -> bool {
    match result {
        Some((index, event)) => {
            &&& from <= index < events.len()
            &&& *event == events[index as int]
            &&& event.position == target
            &&& forall|i: int| from <= i < index ==> (#[trigger] events[i]).position != target
        },
        None => forall|i: int| from <= i < events.len() ==> (#[trigger] events[i]).position != target,
    }
}

/// 元の到着順で対象 tick のイベント、または対象外のイベントを取り出す。
pub open spec fn events_at_tick<T>(
    events: Seq<ScheduledEvent<T>>, target: TickPosition, matching: bool,
) -> Seq<ScheduledEvent<T>> {
    events.filter(|event: ScheduledEvent<T>| (event.position == target) == matching)
}

proof fn partition_append<T>(prefix: Seq<ScheduledEvent<T>>, event: ScheduledEvent<T>, target: TickPosition)
    ensures
        events_at_tick(prefix.push(event), target, true) ==
            if event.position == target { events_at_tick(prefix, target, true).push(event) }
            else { events_at_tick(prefix, target, true) },
        events_at_tick(prefix.push(event), target, false) ==
            if event.position == target { events_at_tick(prefix, target, false) }
            else { events_at_tick(prefix, target, false).push(event) },
{
    prefix.lemma_filter_push(event, |e: ScheduledEvent<T>| (e.position == target) == true);
    prefix.lemma_filter_push(event, |e: ScheduledEvent<T>| (e.position == target) == false);
}

impl<T> ScheduledEvents<T> {
    /// 到着順の未消費イベント。
    pub closed spec fn model(&self) -> Seq<ScheduledEvent<T>> { self.pending@ }

    /// 空のイベント列を作る。
    pub fn new() -> (events: Self)
        ensures events.model() == Seq::<ScheduledEvent<T>>::empty(),
    {
        Self { pending: VecDeque::new() }
    }

    /// イベントを列の末尾に記録する。
    ///
    /// ホストはこの関数を到着順に呼び出す。適用 tick の順に並べ替える必要はない。
    pub fn enqueue(&mut self, event: ScheduledEvent<T>)
        ensures final(self).model() == old(self).model().push(event),
    {
        self.pending.push_back(event);
    }

    /// 対象 tick のイベント列を、評価を始める時点の内容に固定する。
    pub fn prepare(&mut self, target: TickPosition) -> (pending: PendingEvents<'_, T>)
        ensures
            pending.before_model() == old(self).model(),
            pending.after_model() == final(self).model(),
            pending.target_model() == target,
    {
        PendingEvents { events: self, target }
    }

    fn next_ready(&self, target: TickPosition, from: usize)
        -> (result: Option<(usize, &ScheduledEvent<T>)>)
        ensures next_event_matches(self.model(), target, from, result),
    {
        let mut index = from;
        while index < self.pending.len()
            invariant
                from <= index,
                forall|i: int| from <= i < index && i < self.model().len() ==>
                    (#[trigger] self.model()[i]).position != target,
            decreases self.model().len() - index,
        {
            let event = &self.pending[index];
            if let EventTimeStatus::Ready = classify_event_time(target, event.position) {
                return Some((index, event));
            }
            index += 1;
        }
        None
    }

    fn consume_ready(&mut self, target: TickPosition) -> (consumed: Vec<ScheduledEvent<T>>)
        ensures
            final(self).model() == events_at_tick(old(self).model(), target, false),
            consumed@ == events_at_tick(old(self).model(), target, true),
    {
        let len = self.pending.len();
        let mut scanned = 0;
        let mut consumed = Vec::new();
        let ghost original = self.pending@;
        while scanned < len
            invariant
                len == original.len(),
                scanned <= len,
                original == old(self).model(),
                self.pending@ == original.skip(scanned as int)
                    + events_at_tick(original.take(scanned as int), target, false),
                consumed@ == events_at_tick(original.take(scanned as int), target, true),
            decreases len - scanned,
        {
            let ghost prefix = original.take(scanned as int);
            let ghost suffix = original.skip(scanned as int);
            let ghost next_prefix = original.take(scanned as int + 1);
            let ghost next_suffix = original.skip(scanned as int + 1);
            proof { assert(suffix.len() > 0); }
            let event = self.pending.pop_front().unwrap();
            proof {
                assert(event == original[scanned as int]);
                assert(self.pending@ =~= next_suffix + events_at_tick(prefix, target, false));
                assert(next_prefix =~= prefix.push(event));
                partition_append(prefix, event, target);
            }
            let status = classify_event_time(target, event.position);
            assert((status == EventTimeStatus::Ready) <==> event.position == target);
            if let EventTimeStatus::Ready = status {
                consumed.push(event);
            } else {
                proof { Seq::push_distributes_over_add(next_suffix, events_at_tick(prefix, target, false), event); }
                self.pending.push_back(event);
            }
            assert(self.pending@ == next_suffix + events_at_tick(next_prefix, target, false));
            assert(consumed@ == events_at_tick(next_prefix, target, true));
            scanned += 1;
        }
        assert(original.skip(len as int) =~= Seq::<ScheduledEvent<T>>::empty());
        assert(original.take(len as int) =~= original);
        consumed
    }
}

impl<'a, T> PendingEvents<'a, T> {
    /// 準備時点の未消費イベント。
    pub closed spec fn before_model(&self) -> Seq<ScheduledEvent<T>> { self.events.model() }

    /// 更新または取り消しを終えた後の未消費イベント。
    #[verifier::prophetic]
    pub closed spec fn after_model(&self) -> Seq<ScheduledEvent<T>> { final(self.events).model() }

    /// 評価対象の世代と tick。
    pub closed spec fn target_model(&self) -> TickPosition { self.target }

    /// `from` 以降で対象 tick に一致する先頭の添字とイベントを返す。
    ///
    /// 同じ tick の次のイベントを読むときは、返った添字の次から探す。
    pub fn next_ready(&self, from: usize) -> (result: Option<(usize, &ScheduledEvent<T>)>)
        ensures next_event_matches(self.before_model(), self.target_model(), from, result),
    {
        self.events.next_ready(self.target, from)
    }

    /// 対象 tick の全イベントを取り出し、到着順のまま返す。
    ///
    /// 回路とデバイスの更新を確定するときに呼び出す。残るイベントの順序を保つ。
    /// 評価が中断した場合は [`Self::cancel`] で取り消す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::time::{ScheduledEvent, ScheduledEvents, TickPosition};
    ///
    /// let target = TickPosition { generation: 1, tick: 2 };
    /// let mut events = ScheduledEvents::new();
    /// for (position, payload) in [
    ///     (TickPosition { generation: 1, tick: 3 }, "later"),
    ///     (target, "first"),
    ///     (TickPosition { generation: 0, tick: 2 }, "earlier generation"),
    ///     (target, "second"),
    /// ] {
    ///     events.enqueue(ScheduledEvent { position, payload });
    /// }
    /// let pending = events.prepare(target);
    /// let (index, first) = pending.next_ready(0).unwrap();
    /// assert_eq!(first.payload, "first");
    /// assert_eq!(pending.next_ready(index + 1).unwrap().1.payload, "second");
    /// let consumed = pending.commit();
    /// assert_eq!(consumed.len(), 2);
    /// assert_eq!(consumed[0].payload, "first");
    /// assert_eq!(consumed[1].payload, "second");
    /// assert!(events.prepare(target).next_ready(0).is_none());
    /// let later = TickPosition { generation: 1, tick: 3 };
    /// assert_eq!(events.prepare(later).next_ready(0).unwrap().1.payload, "later");
    /// ```
    pub fn commit(self) -> (consumed: Vec<ScheduledEvent<T>>)
        ensures
            self.after_model() == events_at_tick(self.before_model(), self.target_model(), false),
            consumed@ == events_at_tick(self.before_model(), self.target_model(), true),
    {
        self.events.consume_ready(self.target)
    }

    /// 評価を取り消し、未消費イベントを到着順のまま保持する。
    pub fn cancel(self)
        ensures self.after_model() == self.before_model(),
    {
    }
}
} // verus!
