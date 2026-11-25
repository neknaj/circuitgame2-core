//! 全文の元リストと、保存する前後の区間の元リストを対応付ける。

use super::*;
use crate::recovery_boundary::replay_close_is_settled;

verus! {

// EOF では閉じ括弧が補われても、元入力の括弧で閉じたリストは増えない。
proof fn eof_keeps_original_lists(state: RecoveryState, eof: int)
    ensures finish_recovery(state, eof).original == state.original,
    decreases state.open.len(),
{
    reveal(finish_recovery);
    if state.open.len() != 0 {
        eof_keeps_original_lists(close_recovery_at_eof(state, eof as usize), eof);
    }
}

// 元リストの指定件数を確定した瞬間は、そのリストを実際に閉じた位置に当たる。
proof fn original_list_close(
    bytes: Seq<u8>, frames: Seq<ReplayFrame>, count: int, list: int,
) -> (at: int)
    requires replay_valid(bytes, frames), 0 <= count <= frames.len(),
        0 <= list < replay_at(frames, count).original.len(),
    ensures
        0 <= at < count,
        frames[at].segment.kind is Close,
        replay_at(frames, at).open.len() == 1,
        replay_at(frames, at + 1).original.len() == list + 1,
        frames[at].segment.span.end == replay_at(frames, count).original[list].end,
    decreases count,
{
    let i = count - 1;
    let before = replay_at(frames, i);
    let after = replay_at(frames, count);
    let segment = frames[i].segment;
    replay_frame_evidence(bytes, frames, i);
    reveal(apply_recovery_segment);
    if list < before.original.len() {
        let result = original_list_close(bytes, frames, i, list);
        assert(before.original[list] == after.original[list]);
        result
    } else {
        assert(after.original.len() == before.original.len() + 1);
        assert(segment.kind is Close);
        assert(before.open.len() == 1);
        assert(after.original[list].end == segment.span.end);
        i
    }
}

proof fn original_list_checkpoint(
    source: &str, frames: Seq<ReplayFrame>, lists: Seq<Range<usize>>, count: nat,
) -> (index: int)
    requires
        replay_valid(source.spec_bytes(), frames),
        lists == replay_at(frames, frames.len() as int).original,
        count <= lists.len(),
    ensures
        0 <= index <= frames.len(),
        replay_position(frames, index) == original_end(lists, count),
        !replay_separator(frames, index),
        replay_at(frames, index).open.len() == 0,
        replay_at(frames, index).root is None,
        replay_at(frames, index).original.len() == count,
        settled_recovery_boundary(source, original_end(lists, count)),
{
    if count == 0 {
        let bytes = source.spec_bytes();
        crate::recovery_boundary::replay_start_is_settled(source);
        0
    } else {
        let bytes = source.spec_bytes();
        let at = original_list_close(bytes, frames, frames.len() as int, count - 1);
        replay_close_is_settled(source, frames, at);
        replay_frame_evidence(bytes, frames, at);
        reveal(apply_recovery_segment);
        at + 1
    }
}

pub(crate) open spec fn original_end(lists: Seq<Range<usize>>, count: nat) -> usize {
    if count == 0 { 0 } else { lists[count - 1].end }
}

proof fn positions_increase(bytes: Seq<u8>, frames: Seq<ReplayFrame>, a: int, b: int)
    requires replay_valid(bytes, frames), 0 <= a < b <= frames.len(),
    ensures replay_position(frames, a) < replay_position(frames, b),
    decreases b - a,
{
    if a + 1 < b { positions_increase(bytes, frames, a, b - 1); }
    replay_frame_evidence(bytes, frames, b - 1);
    reveal(recovery_segment_at);
}

// 区切りより前の元リストは接頭部のものと一致し、後ろの元リストは接尾部のものを移した列になる。
pub(crate) proof fn retained_original_lists_agree(
    source: &str, whole: &crate::Recovered, head_text: &str, head: &crate::Recovered,
    tail_text: &str, tail: &crate::Recovered, kept: nat, first_tail: nat,
)
    requires
        3 * source.spec_bytes().len() + 1 < usize::MAX,
        kept <= first_tail <= whole.original_lists@.len(),
        original_end(whole.original_lists@, kept) <= source.spec_bytes().len(),
        original_end(whole.original_lists@, first_tail) <= source.spec_bytes().len(),
        head_text.spec_bytes() == source.spec_bytes()[..original_end(whole.original_lists@, kept) as int],
        tail_text.spec_bytes() == source.spec_bytes()[original_end(whole.original_lists@, first_tail) as int..],
        settled_recovery_boundary(head_text, original_end(whole.original_lists@, kept)),
        head.repairs@.len() == 0,
        recovered_replay_matches(source, whole.forms@, whole.repairs@, whole.original_lists@),
        recovered_replay_matches(head_text, head.forms@, head.repairs@, head.original_lists@),
        recovered_replay_matches(tail_text, tail.forms@, tail.repairs@, tail.original_lists@),
    ensures
        head.original_lists@ == whole.original_lists@.take(kept as int),
        whole.original_lists@.skip(first_tail as int) == tail.original_lists@.map_values(|span: Range<usize>|
            place_range(span, original_end(whole.original_lists@, first_tail) as int)),
{
    let bytes = source.spec_bytes();
    let eof = bytes.len() as int;
    let all = recovered_history(source, whole);
    let end = replay_at(all, all.len() as int);
    eof_keeps_original_lists(end, eof);
    let lists = whole.original_lists@;
    let head_end = original_end(lists, kept);
    let tail_start = original_end(lists, first_tail);

    let head_cut = original_list_checkpoint(source, all, lists, kept);
    let head_trace = clean_prefix_history(head_text, head, head_end);
    clean_prefix_frames_agree(bytes, head_text.spec_bytes(), all, head_trace);
    let n = head_trace.len() as int;
    assert(replay_position(all, n) == head_end);
    if n < head_cut { positions_increase(bytes, all, n, head_cut); }
    if head_cut < n { positions_increase(bytes, all, head_cut, n); }
    assert(head_cut == n);
    assert(replay_at(all, head_cut).original == head.original_lists@);
    original_prefix(bytes, all, head_cut, all.len() as int);
    assert(head.original_lists@ =~= lists.take(kept as int));

    let tail_cut = original_list_checkpoint(source, all, lists, first_tail);
    let tail_trace = recovered_history(tail_text, tail);
    encode_utf8_valid_utf8(source@);
    encode_utf8_valid_utf8(tail_text@);
    project_history_suffix(bytes, tail_text.spec_bytes(), all, tail_trace, tail_cut, tail_start);
    let prefix = replay_at(all, tail_cut);
    let rebased = tail.original_lists@.map_values(|span: Range<usize>| place_range(span, tail_start as int));
    assert(lists == prefix.original + rebased);
    assert(lists.skip(first_tail as int) =~= rebased);
}

proof fn original_prefix(bytes: Seq<u8>, frames: Seq<ReplayFrame>, a: int, b: int)
    requires replay_valid(bytes, frames), 0 <= a <= b <= frames.len(),
    ensures replay_at(frames, a).original.is_prefix_of(replay_at(frames, b).original),
    decreases b - a,
{
    if a < b {
        original_prefix(bytes, frames, a, b - 1);
        let before = replay_at(frames, b - 1);
        let after = replay_at(frames, b);
        replay_frame_evidence(bytes, frames, b - 1);
        reveal(apply_recovery_segment);
        assert(before.original.is_prefix_of(after.original));
    }
}

} // verus!
