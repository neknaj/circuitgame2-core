//! 編集前の元リストを検索し、再利用する前後の区間を選ぶ。

use core::ops::Range;
use vstd::prelude::*;

verus! {

/// 編集前の元リストのうち、そのまま再利用する前後の区間。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CircuitRecoveryReuseWindow {
    /// 接頭部の終了バイト位置。接頭部が空なら0。
    pub start: usize,
    /// 接尾部の開始バイト位置。
    pub join: usize,
    /// 接頭部に含まれる元リストの件数。
    pub head_count: usize,
    /// 接尾部に含まれる最初の元リストの添字。接尾部に元リストがなければ全件数。
    pub first_tail: usize,
}

impl CircuitRecoveryReuseWindow {
    /// 接頭部のリストは編集開始以前に閉じ、接尾部は編集終了以降の最初の閉じ括弧の後から始まる。
    pub open spec fn matches(self, lists: Seq<Range<usize>>, edit: Range<usize>) -> bool {
        let head = self.head_count as int;
        let tail = self.first_tail as int;
        &&& 0 <= head <= tail <= lists.len()
        &&& self.start <= edit.start <= edit.end <= self.join
        &&& self.start == if head == 0 { 0 } else { lists[head - 1].end }
        &&& self.join == if tail == 0 { 0 } else { lists[tail - 1].end }
        &&& forall|i: int| 0 <= i < lists.len() ==> (i < head <==> (#[trigger] lists[i]).end <= edit.start)
        &&& forall|i: int| 0 <= i < lists.len() ==> (tail <= i <==> self.join <= (#[trigger] lists[i]).start)
        &&& if edit.end == self.start {
            tail == head
        } else {
            &&& tail > 0
            &&& forall|i: int| 0 <= i < tail - 1 ==> (#[trigger] lists[i]).end < edit.end
        }
    }
}

pub(super) open spec fn original_lists_ordered(lists: Seq<Range<usize>>) -> bool {
    &&& forall|i: int| 0 <= i < lists.len() ==> (#[trigger] lists[i]).start < lists[i].end
    &&& forall|a: int, b: int| 0 <= a < b < lists.len() ==> (#[trigger] lists[a]).end <= (#[trigger] lists[b]).start
}

spec fn preceding(end: usize, position: usize, inclusive: bool) -> bool {
    end < position || inclusive && end == position
}

// 元リストは重ならず、終端も昇順なので境界を二分探索できる。
fn partition_by_end(lists: &[Range<usize>], position: usize, inclusive: bool) -> (cut: usize)
    requires original_lists_ordered(lists@),
    ensures cut <= lists@.len(),
        forall|i: int| 0 <= i < lists@.len() ==> (i < cut <==> preceding((#[trigger] lists@[i]).end, position, inclusive)),
{
    let mut lo = 0;
    let mut hi = lists.len();
    while lo < hi
        invariant
            original_lists_ordered(lists@),
            lo <= hi <= lists@.len(),
            forall|i: int| 0 <= i < lo ==> preceding((#[trigger] lists@[i]).end, position, inclusive),
            forall|i: int| hi <= i < lists@.len() ==> !preceding((#[trigger] lists@[i]).end, position, inclusive),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let end = lists[mid].end;
        if end < position || (inclusive && end == position) {
            assert forall|i: int| 0 <= i <= mid implies preceding((#[trigger] lists@[i]).end, position, inclusive) by {
                if i < mid { assert(lists@[i].end <= lists@[mid as int].start < end); }
            };
            lo = mid + 1;
        } else {
            assert forall|i: int| mid <= i < lists@.len() implies !preceding((#[trigger] lists@[i]).end, position, inclusive) by {
                if mid < i { assert(end <= lists@[i].start < lists@[i].end); }
            };
            hi = mid;
        }
    }
    lo
}

pub(super) fn select_recovery_window(lists: &[Range<usize>], edit: Range<usize>)
    -> (result: Option<CircuitRecoveryReuseWindow>)
    requires original_lists_ordered(lists@),
    ensures
        result matches Some(window) ==> window.matches(lists@, edit),
        result.is_some() <==> edit.start <= edit.end && (
            edit.end == 0 || exists|i: int| 0 <= i < lists@.len() && edit.end <= (#[trigger] lists@[i]).end),
{
    if edit.start > edit.end { return None; }
    let head_count = partition_by_end(lists, edit.start, true);
    let start = if head_count == 0 { 0 } else { lists[head_count - 1].end };
    let (join, first_tail) = if edit.end == start {
        (start, head_count)
    } else {
        let last = partition_by_end(lists, edit.end, false);
        if last == lists.len() { return None; }
        proof {
            assert(start < edit.end);
            if last < head_count {
                let end = head_count as int - 1;
                if last < end { assert(lists@[last as int].end <= lists@[end].start < start); }
                assert(lists@[last as int].end <= start);
                assert(lists@[last as int].end >= edit.end);
            }
        }
        (lists[last].end, last + 1)
    };
    assert forall|i: int| 0 <= i < lists@.len() implies
        (first_tail <= i <==> join <= (#[trigger] lists@[i]).start) by {
        if first_tail > 0 {
            let boundary = first_tail as int - 1;
            assert(join == lists@[boundary].end);
            if i <= boundary {
                if i < boundary { assert(lists@[i].end <= lists@[boundary].start); }
                assert(lists@[i].start < join);
            } else {
                assert(join <= lists@[i].start);
            }
        }
    };
    Some(CircuitRecoveryReuseWindow { start, join, head_count, first_tail })
}

} // verus!
