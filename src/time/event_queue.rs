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
pub(crate) struct PendingEvents<'a, T> {
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
            &&& index < usize::MAX
            &&& *event == events[index as int]
            &&& event.position == target
            &&& forall|i: int| from <= i < index ==> (#[trigger] events[i]).position != target
        },
        None => forall|i: int| from <= i < events.len() ==> (#[trigger] events[i]).position != target,
    }
}

#[derive(Clone, Copy)]
enum EventSelection {
    Tick(TickPosition),
    OlderGeneration(u64),
}

impl EventSelection {
    spec fn matches(&self, position: TickPosition) -> bool {
        match self {
            Self::Tick(target) => position == *target,
            Self::OlderGeneration(generation) => position.generation < *generation,
        }
    }

    fn includes(&self, position: TickPosition) -> (selected: bool)
        ensures selected == self.matches(position),
    {
        match self {
            Self::Tick(target) => {
                let status = classify_event_time(*target, position);
                if let EventTimeStatus::Ready = status { true } else { false }
            },
            Self::OlderGeneration(generation) => position.generation < *generation,
        }
    }
}

spec fn filter_events<T>(
    events: Seq<ScheduledEvent<T>>, selection: EventSelection, matching: bool,
) -> Seq<ScheduledEvent<T>> {
    match selection {
        EventSelection::Tick(target) => events_at_tick(events, target, matching),
        EventSelection::OlderGeneration(generation) => events_by_reset_generation(events, generation, matching),
    }
}

/// 元の到着順で対象 tick のイベント、または対象外のイベントを取り出す。
pub open spec fn events_at_tick<T>(
    events: Seq<ScheduledEvent<T>>, target: TickPosition, matching: bool,
) -> Seq<ScheduledEvent<T>> {
    events.filter(|event: ScheduledEvent<T>| (event.position == target) == matching)
}

/// 元の到着順で指定の世代より古いイベント、またはその世代以降のイベントを取り出す。
pub open spec fn events_by_reset_generation<T>(
    events: Seq<ScheduledEvent<T>>, generation: u64, older: bool,
) -> Seq<ScheduledEvent<T>> {
    events.filter(|event: ScheduledEvent<T>| (event.position.generation < generation) == older)
}

proof fn partition_append<T>(
    prefix: Seq<ScheduledEvent<T>>, event: ScheduledEvent<T>, selection: EventSelection,
)
    ensures
        filter_events(prefix.push(event), selection, true) ==
            if selection.matches(event.position) { filter_events(prefix, selection, true).push(event) }
            else { filter_events(prefix, selection, true) },
        filter_events(prefix.push(event), selection, false) ==
            if selection.matches(event.position) { filter_events(prefix, selection, false) }
            else { filter_events(prefix, selection, false).push(event) },
{
    match selection {
        EventSelection::Tick(target) => {
            prefix.lemma_filter_push(event, |e: ScheduledEvent<T>| (e.position == target) == true);
            prefix.lemma_filter_push(event, |e: ScheduledEvent<T>| (e.position == target) == false);
        },
        EventSelection::OlderGeneration(generation) => {
            prefix.lemma_filter_push(event, |e: ScheduledEvent<T>| (e.position.generation < generation) == true);
            prefix.lemma_filter_push(event, |e: ScheduledEvent<T>| (e.position.generation < generation) == false);
        },
    }
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
    pub(crate) fn prepare(&mut self, target: TickPosition) -> (pending: PendingEvents<'_, T>)
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

    /// 新しい reset 世代に引き継がないイベントを、到着順のまま取り出す。
    pub(crate) fn take_older_generations(&mut self, generation: u64) -> (removed: Vec<ScheduledEvent<T>>)
        ensures
            final(self).model() == events_by_reset_generation(old(self).model(), generation, false),
            removed@ == events_by_reset_generation(old(self).model(), generation, true),
    {
        self.take_selected(EventSelection::OlderGeneration(generation))
    }

    fn take_selected(&mut self, selection: EventSelection) -> (consumed: Vec<ScheduledEvent<T>>)
        ensures
            final(self).model() == filter_events(old(self).model(), selection, false),
            consumed@ == filter_events(old(self).model(), selection, true),
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
                    + filter_events(original.take(scanned as int), selection, false),
                consumed@ == filter_events(original.take(scanned as int), selection, true),
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
                assert(self.pending@ =~= next_suffix + filter_events(prefix, selection, false));
                assert(next_prefix =~= prefix.push(event));
                partition_append(prefix, event, selection);
            }
            if selection.includes(event.position) {
                consumed.push(event);
            } else {
                proof { Seq::push_distributes_over_add(next_suffix, filter_events(prefix, selection, false), event); }
                self.pending.push_back(event);
            }
            assert(self.pending@ == next_suffix + filter_events(next_prefix, selection, false));
            assert(consumed@ == filter_events(next_prefix, selection, true));
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
    pub fn commit(self) -> (consumed: Vec<ScheduledEvent<T>>)
        ensures
            self.after_model() == events_at_tick(self.before_model(), self.target_model(), false),
            consumed@ == events_at_tick(self.before_model(), self.target_model(), true),
    {
        self.events.take_selected(EventSelection::Tick(self.target))
    }

    /// 評価を取り消し、未消費イベントを到着順のまま保持する。
    pub fn cancel(self)
        ensures self.after_model() == self.before_model(),
    {
    }
}
} // verus!
