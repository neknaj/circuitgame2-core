//! 外部イベントを、更新対象の世代と論理 tick に照合する。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::TickPosition;

verus! {

/// 指定された tick を始めるときに、外部イベントから読み取れる時刻の状態。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EventTimeStatus {
    /// 更新対象と同じ世代で、今回適用する。
    Ready,
    /// 同じ世代の後続 tick を待つ。
    Waiting,
    /// 同じ世代で、イベントの tick が更新対象より前にある。
    Missed,
    /// 更新対象の実行世代と一致しない。
    DifferentGeneration,
}

/// 外部イベントの世代を先に照合し、一致した場合だけ tick を比較する。
pub open spec fn event_time_status(target: TickPosition, event: TickPosition) -> EventTimeStatus {
    if event.generation != target.generation {
        EventTimeStatus::DifferentGeneration
    } else if event.tick < target.tick {
        EventTimeStatus::Missed
    } else if event.tick > target.tick {
        EventTimeStatus::Waiting
    } else {
        EventTimeStatus::Ready
    }
}

/// 外部イベントが今回の更新に適用できるかを調べる。
pub fn classify_event_time(target: TickPosition, event: TickPosition) -> (status: EventTimeStatus)
    ensures status == event_time_status(target, event),
{
    if event.generation != target.generation {
        EventTimeStatus::DifferentGeneration
    } else if event.tick < target.tick {
        EventTimeStatus::Missed
    } else if event.tick > target.tick {
        EventTimeStatus::Waiting
    } else {
        EventTimeStatus::Ready
    }
}

/// 選んだ添字が、与えた順番で同じ時刻の全イベントを指すことを表す。
pub open spec fn event_indices_match(
    target: TickPosition, schedule: Seq<TickPosition>, indices: Seq<usize>,
) -> bool {
    &&& forall|i: int| 0 <= i < indices.len() ==> {
        let index = #[trigger] indices[i] as int;
        0 <= index < schedule.len() && schedule[index] == target
    }
    &&& forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] < indices[j]
    &&& forall|index: int| 0 <= index < schedule.len() && #[trigger] schedule[index] == target ==>
        indices.contains(index as usize)
}

/// ホストが並べたイベントのうち、更新対象に渡すイベントの添字を返す。
///
/// 次の tick の準備で得た時刻を渡す。元の順序を保ったまま選別する。
/// 一時停止から再開するときは、同じイベント集合と添字を使う。
/// 実行側は、回路とデバイスの状態を確定するときにイベントを消費する。
/// 世代や時刻が合わなかった理由を調べるには [`classify_event_time`] を使う。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::time::{TickPosition, ready_event_indices};
///
/// let target = TickPosition { generation: 2, tick: 1 };
/// let earlier_generation = TickPosition { generation: 1, tick: 1 };
/// let later_tick = TickPosition { generation: 2, tick: 2 };
/// let schedule = [earlier_generation, target, later_tick, target];
/// assert_eq!(ready_event_indices(target, &schedule), [1, 3]);
/// ```
pub fn ready_event_indices(target: TickPosition, schedule: &[TickPosition]) -> (ready: Vec<usize>)
    ensures event_indices_match(target, schedule@, ready@),
{
    let mut ready = Vec::new();
    let mut next = 0;
    while next < schedule.len()
        invariant
            next <= schedule.len(),
            event_indices_match(target, schedule@.take(next as int), ready@),
        decreases schedule.len() - next,
    {
        let ghost previous = ready@;
        let event = schedule[next];
        if let EventTimeStatus::Ready = classify_event_time(target, event) {
            ready.push(next);
        }
        proof {
            let prefix = schedule@.take(next as int);
            let extended = schedule@.take(next as int + 1);
            assert forall|i: int| 0 <= i < ready@.len() implies {
                let index = #[trigger] ready@[i] as int;
                0 <= index < extended.len() && extended[index] == target
            } by {
                if i < previous.len() {
                    let index = previous[i] as int;
                    assert(prefix[index] == target);
                    assert(extended[index] == prefix[index]);
                }
            }
            assert forall|i: int, j: int| 0 <= i < j < ready@.len() implies ready@[i] < ready@[j] by {
                if j < previous.len() {
                    assert(previous[i] < previous[j]);
                } else {
                    assert(previous[i] < next);
                }
            }
            assert forall|index: int| 0 <= index < extended.len() && #[trigger] extended[index] == target implies
                ready@.contains(index as usize) by {
                if index < next {
                    assert(prefix[index] == extended[index]);
                    let witness = choose|i: int| 0 <= i < previous.len() && previous[i] == index as usize;
                    assert(ready@[witness] == index as usize);
                } else {
                    assert(ready@[previous.len() as int] == next);
                }
            }
        }
        next += 1;
    }
    assert(schedule@.take(next as int) =~= schedule@);
    ready
}

} // verus!
