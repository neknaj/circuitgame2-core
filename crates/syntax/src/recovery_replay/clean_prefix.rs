//! 閉じ括弧までの妥当な接頭部を、後続の入力から独立して回復する。

use super::{
    ReplayFrame, apply_recovery_segment, replay_at,
    replay_frame_evidence, replay_position, replay_separator, replay_valid,
};
use super::lexical_shift::lexeme_shifts;
use super::placement::place_segment;
use crate::{
    AtomKind, LexemeKind, Segment, SegmentKind, bare_atom_extent, lexeme_at, lexical_step_agrees,
    recovery_segment_at, segment_lexeme, trivia_extent,
};
use vstd::prelude::*;

verus! {

proof fn prefix_lexeme_matches(whole: Seq<u8>, prefix: Seq<u8>, start: int, end: int, kind: LexemeKind)
    requires
        prefix == whole.take(prefix.len() as int),
        prefix.len() <= whole.len(),
        lexeme_at(prefix, start, end, kind),
        end < prefix.len() || kind is Close,
    ensures lexeme_at(whole, start, end, kind),
{
    reveal(lexeme_at);
    assert(whole[start] == prefix[start]);
    match kind {
        LexemeKind::Open | LexemeKind::Close => {},
        LexemeKind::Atom(AtomKind::String) => { assert(prefix[start..end] =~= whole[start..end]); },
        LexemeKind::Atom(_) => {
            reveal(bare_atom_extent);
            assert(prefix[start..end] =~= whole[start..end]);
            assert(whole[end] == prefix[end]);
            assert forall|i: int| start <= i < end implies !crate::bare_atom_delimiter(#[trigger] whole[i]) by {
                assert(whole[i] == prefix[i]);
            };
        },
        LexemeKind::Whitespace | LexemeKind::Comment => {
            reveal(trivia_extent);
            let comment = kind is Comment;
            assert(whole[end] == prefix[end]);
            assert forall|i: int| start <= i < end implies crate::trivia_byte(#[trigger] whole[i], comment) by {
                assert(whole[i] == prefix[i]);
            };
        },
    }
}

proof fn repair_count_never_decreases(bytes: Seq<u8>, frames: Seq<ReplayFrame>, lo: int, hi: int)
    requires replay_valid(bytes, frames), 0 <= lo <= hi <= frames.len(),
    ensures replay_at(frames, lo).repairs.len() <= replay_at(frames, hi).repairs.len(),
    decreases hi - lo,
{
    if lo < hi {
        repair_count_never_decreases(bytes, frames, lo, hi - 1);
        let i = hi - 1;
        let prior = replay_at(frames, i);
        let segment = frames[i].segment;
        assert(frames[i].after == apply_recovery_segment(prior, segment)) by { reveal(replay_valid); };
        assert(prior.repairs.len() <= apply_recovery_segment(prior, segment).repairs.len()) by {
            reveal(apply_recovery_segment);
        };
    }
}

proof fn clean_frame_has_lexeme(bytes: Seq<u8>, frames: Seq<ReplayFrame>, i: int)
    requires
        replay_valid(bytes, frames),
        0 <= i < frames.len(),
        replay_at(frames, frames.len() as int).repairs.len() == 0,
    ensures segment_lexeme(frames[i].segment.kind).is_some(), !frames[i].segment.missing_separator,
{
    repair_count_never_decreases(bytes, frames, i + 1, frames.len() as int);
    let frame = frames[i];
    let prior = replay_at(frames, i);
    assert(frame.after == apply_recovery_segment(prior, frame.segment)) by { reveal(replay_valid); };
    assert(frame.segment.kind is Malformed || frame.segment.missing_separator
        ==> apply_recovery_segment(prior, frame.segment).repairs.len() > 0) by {
        reveal(apply_recovery_segment);
    };
}

proof fn clean_lexeme(prefix: Seq<u8>, before: Seq<ReplayFrame>, i: int) -> (kind: LexemeKind)
    requires
        replay_valid(prefix, before),
        0 <= i < before.len(),
        before.len() > 0 ==> before.last().segment.kind is Close,
        replay_at(before, before.len() as int).repairs.len() == 0,
    ensures
        before[i].segment.span.start == replay_position(before, i),
        before[i].segment.span.start < before[i].segment.span.end <= prefix.len(),
        before[i].segment.missing_separator == (replay_separator(before, i) && before[i].segment.kind.is_atom()),
        segment_lexeme(before[i].segment.kind) == Some(kind),
        lexeme_at(prefix, replay_position(before, i), before[i].segment.span.end as int, kind),
        before[i].segment.span.end < prefix.len() || kind is Close,
{
    clean_frame_has_lexeme(prefix, before, i);
    replay_frame_evidence(prefix, before, i);
    let observed = before[i].segment;
    let expected = segment_lexeme(observed.kind)->Some_0;
    let start = replay_position(before, i);
    let end = observed.span.end as int;
    assert(end < prefix.len() || expected is Close) by {
        if i + 1 < before.len() {
            reveal(replay_valid);
            reveal(recovery_segment_at);
            assert(recovery_segment_at(prefix, replay_position(before, i + 1),
                replay_separator(before, i + 1), before[i + 1].segment));
        }
    };
    assert(lexeme_at(prefix, start, end, expected)) by {
        reveal(replay_valid);
        reveal(recovery_segment_at);
        reveal(lexical_step_agrees);
        assert(recovery_segment_at(prefix, start, replay_separator(before, i), observed));
    };
    reveal(recovery_segment_at);
    expected
}

proof fn normal_segment_matches(
    bytes: Seq<u8>, start: int, separator: bool, got: Segment, wanted: Segment, kind: LexemeKind,
)
    requires
        recovery_segment_at(bytes, start, separator, got),
        lexeme_at(bytes, start, wanted.span.end as int, kind),
        wanted.span.start == start,
        segment_lexeme(wanted.kind) == Some(kind),
        wanted.missing_separator == (separator && wanted.kind.is_atom()),
    ensures got == wanted,
{
    reveal(recovery_segment_at);
    reveal(lexical_step_agrees);
    assert(segment_lexeme(got.kind) == Some(kind));
}

proof fn clean_frames_agree_at(
    full: Seq<u8>, prefix: Seq<u8>, all: Seq<ReplayFrame>, before: Seq<ReplayFrame>, i: int,
)
    requires
        prefix == full.take(prefix.len() as int),
        prefix.len() <= full.len(),
        replay_valid(full, all), replay_valid(prefix, before),
        0 <= i < all.len(), i < before.len(),
        before.len() > 0 ==> before.last().segment.kind is Close,
        replay_at(before, before.len() as int).repairs.len() == 0,
    ensures all[i] == before[i],
    decreases i,
{
    if i > 0 {
        clean_frames_agree_at(full, prefix, all, before, i - 1);
    }
    let observed = before[i].segment;
    let expected = clean_lexeme(prefix, before, i);
    let start = replay_position(before, i);
    let end = observed.span.end as int;
    prefix_lexeme_matches(full, prefix, start, end, expected);
    replay_frame_evidence(full, all, i);
    replay_frame_evidence(prefix, before, i);
    normal_segment_matches(full, start, replay_separator(before, i), all[i].segment, observed, expected);
}

proof fn clean_middle_segment_agrees(
    full: Seq<u8>, middle: Seq<u8>, all: Seq<ReplayFrame>, local: Seq<ReplayFrame>,
    split: int, base: int, i: int,
)
    requires
        0 <= base <= base + middle.len() <= full.len() <= usize::MAX,
        middle == full[base..base + middle.len()],
        replay_valid(full, all), replay_valid(middle, local),
        0 <= split <= split + i < all.len(),
        0 <= i < local.len(),
        replay_position(all, split) == base,
        !replay_separator(all, split),
        local.len() > 0 ==> local.last().segment.kind is Close,
        replay_at(local, local.len() as int).repairs.len() == 0,
    ensures all[split + i].segment == place_segment(local[i].segment, base),
    decreases i,
{
    if i > 0 {
        clean_middle_segment_agrees(full, middle, all, local, split, base, i - 1);
        assert(replay_position(all, split + i) == base + replay_position(local, i)) by {
            replay_frame_evidence(middle, local, i - 1);
            reveal(recovery_segment_at);
        };
        assert(replay_separator(all, split + i) == replay_separator(local, i));
    }
    let rest = full[base..];
    assert(middle =~= rest.take(middle.len() as int));
    let observed = local[i].segment;
    let expected = clean_lexeme(middle, local, i);
    let start = replay_position(local, i);
    let end = observed.span.end as int;
    prefix_lexeme_matches(rest, middle, start, end, expected);
    lexeme_shifts(full, rest, base, start, end, expected);
    replay_frame_evidence(full, all, split + i);
    normal_segment_matches(full, base + start, replay_separator(local, i),
        all[split + i].segment, place_segment(observed, base), expected);
}

/// 閉じ括弧で終わる妥当な区間の字句は、確認済みの再開位置から全文を読んでも一致する。
pub(super) proof fn clean_middle_segments_align(
    full: Seq<u8>, middle: Seq<u8>, all: Seq<ReplayFrame>, local: Seq<ReplayFrame>, split: int, base: int,
)
    requires
        0 <= base <= base + middle.len() <= full.len() <= usize::MAX,
        middle == full[base..base + middle.len()],
        replay_valid(full, all), replay_valid(middle, local),
        0 <= split <= all.len(),
        replay_position(all, split) == base,
        !replay_separator(all, split),
        replay_position(all, all.len() as int) == full.len(),
        replay_position(local, local.len() as int) == middle.len(),
        local.len() > 0 ==> local.last().segment.kind is Close,
        replay_at(local, local.len() as int).repairs.len() == 0,
    ensures split + local.len() <= all.len(),
        forall|i: int| 0 <= i < local.len() ==> all[split + i].segment == place_segment((#[trigger] local[i]).segment, base),
{
    let available = all.len() - split;
    let m = local.len() as int;
    if available < m {
        if available > 0 {
            clean_middle_segment_agrees(full, middle, all, local, split, base, available - 1);
        }
        reveal(replay_valid);
        reveal(recovery_segment_at);
        assert(recovery_segment_at(middle, replay_position(local, available),
            replay_separator(local, available), local[available].segment));
        if available > 0 {
            assert(replay_position(local, available) < middle.len());
            assert(replay_position(all, split + available) == base + replay_position(local, available));
        }
        assert(false);
    }
    assert forall|i: int| 0 <= i < m implies all[split + i].segment == place_segment((#[trigger] local[i]).segment, base) by {
        clean_middle_segment_agrees(full, middle, all, local, split, base, i);
    };
}

/// 妥当な接頭部が元の閉じ括弧で終わるとき、全文でその位置まで読んだ結果と一致する。
pub(super) proof fn clean_prefix_frames_agree(
    full: Seq<u8>, prefix: Seq<u8>, all: Seq<ReplayFrame>, before: Seq<ReplayFrame>,
)
    requires
        prefix == full.take(prefix.len() as int),
        prefix.len() <= full.len(),
        replay_valid(full, all), replay_valid(prefix, before),
        replay_position(all, all.len() as int) == full.len(),
        replay_position(before, before.len() as int) == prefix.len(),
        before.len() > 0 ==> before.last().segment.kind is Close,
        replay_at(before, before.len() as int).repairs.len() == 0,
    ensures before.len() <= all.len(), all.take(before.len() as int) == before,
{
    let n = all.len() as int;
    let m = before.len() as int;
    if n < m {
        if n > 0 {
            clean_frames_agree_at(full, prefix, all, before, n - 1);
        }
        assert(replay_position(before, n) == full.len());
        reveal(replay_valid);
        reveal(recovery_segment_at);
        assert(recovery_segment_at(prefix, replay_position(before, n), replay_separator(before, n), before[n].segment));
        assert(false);
    }
    assert forall|i: int| 0 <= i < m implies (#[trigger] all.take(m)[i]) == before[i] by {
        clean_frames_agree_at(full, prefix, all, before, i);
        assert(all.take(m)[i] == all[i]);
    };
    assert(all.take(m) =~= before);
}

} // verus!
