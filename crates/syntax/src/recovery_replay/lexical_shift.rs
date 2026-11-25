//! 接尾部を切り出して読んだ字句を、元のファイル内の位置に対応させる。

use super::{ReplayFrame, replay_position, replay_separator, replay_valid};
use super::placement::{place_error, place_segment};
use crate::{
    AtomKind, LexemeKind, Segment, bare_atom_extent, lexeme_at, lexical_step_agrees,
    malformed_segment_matches, recovery_segment_at, recovery_segments_agree, segment_lexeme, trivia_extent,
};
use vstd::{prelude::*, utf8::{
    is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq, valid_utf8,
}};

verus! {

proof fn bare_extent_shifts(full: Seq<u8>, tail: Seq<u8>, base: int, start: int, end: int)
    requires 0 <= base <= full.len(), tail == full[base..], 0 <= start < end <= tail.len(),
    ensures bare_atom_extent(tail, start, end) == bare_atom_extent(full, base + start, base + end),
{
    reveal(bare_atom_extent);
    if bare_atom_extent(tail, start, end) {
        assert forall|i: int| base + start <= i < base + end
            implies !crate::bare_atom_delimiter(#[trigger] full[i]) by {
            assert(full[i] == tail[i - base]);
        };
    }
    if bare_atom_extent(full, base + start, base + end) {
        assert forall|i: int| start <= i < end implies !crate::bare_atom_delimiter(#[trigger] tail[i]) by {
            assert(tail[i] == full[base + i]);
        };
    }
    if end < tail.len() {
        assert(tail[end] == full[base + end]);
    }
}

proof fn trivia_extent_shifts(full: Seq<u8>, tail: Seq<u8>, base: int, start: int, end: int, comment: bool)
    requires 0 <= base <= full.len(), tail == full[base..], 0 <= start < end <= tail.len(),
    ensures trivia_extent(tail, start, end, comment) == trivia_extent(full, base + start, base + end, comment),
{
    reveal(trivia_extent);
    assert(tail[start] == full[base + start]);
    if trivia_extent(tail, start, end, comment) {
        assert forall|i: int| base + start <= i < base + end
            implies crate::trivia_byte(#[trigger] full[i], comment) by {
            assert(full[i] == tail[i - base]);
        };
    }
    if trivia_extent(full, base + start, base + end, comment) {
        assert forall|i: int| start <= i < end implies crate::trivia_byte(#[trigger] tail[i], comment) by {
            assert(tail[i] == full[base + i]);
        };
    }
    if end < tail.len() {
        assert(tail[end] == full[base + end]);
    }
}

proof fn lexeme_shifts(full: Seq<u8>, tail: Seq<u8>, base: int, start: int, end: int, kind: LexemeKind)
    requires 0 <= base <= full.len(), tail == full[base..], 0 <= start < end <= tail.len(),
    ensures lexeme_at(tail, start, end, kind) == lexeme_at(full, base + start, base + end, kind),
{
    reveal(lexeme_at);
    match kind {
        LexemeKind::Whitespace => trivia_extent_shifts(full, tail, base, start, end, false),
        LexemeKind::Comment => trivia_extent_shifts(full, tail, base, start, end, true),
        LexemeKind::Open | LexemeKind::Close => { assert(tail[start] == full[base + start]); },
        LexemeKind::Atom(kind) => {
            assert(tail[start..end] =~= full[base + start..base + end]);
            if kind != AtomKind::String {
                bare_extent_shifts(full, tail, base, start, end);
            }
        },
    }
}

proof fn character_boundary_shifts(full: Seq<u8>, tail: Seq<u8>, base: int, offset: int)
    requires
        0 <= base <= full.len(),
        tail == full[base..],
        valid_utf8(full), valid_utf8(tail),
        0 <= offset <= tail.len(),
    ensures is_char_boundary(tail, offset) == is_char_boundary(full, base + offset),
{
    if offset < tail.len() {
        assert(tail[offset] == full[base + offset]);
        is_char_boundary_iff_not_is_continuation_byte(tail, offset);
        is_char_boundary_iff_not_is_continuation_byte(full, base + offset);
    } else {
        is_char_boundary_start_end_of_seq(tail);
        is_char_boundary_start_end_of_seq(full);
    }
}

/// 相対位置で選んだ字句と診断を、同じ接尾部を持つ本文へ移しても認識規則を満たす。
pub(super) proof fn recovery_segment_shifts(
    full: Seq<u8>, tail: Seq<u8>, base: int, from: int, separator: bool, segment: Segment,
)
    requires
        0 <= base <= full.len() <= usize::MAX,
        tail == full[base..],
        valid_utf8(full), valid_utf8(tail),
        recovery_segment_at(tail, from, separator, segment),
    ensures recovery_segment_at(full, base + from, separator, place_segment(segment, base)),
{
    reveal(recovery_segment_at);
    let end = segment.span.end as int;
    let shifted = place_segment(segment, base);
    character_boundary_shifts(full, tail, base, from);
    character_boundary_shifts(full, tail, base, end);
    let observed = segment_lexeme(segment.kind);
    assert(segment_lexeme(shifted.kind) == observed);
    assert(shifted.kind.is_atom() == segment.kind.is_atom());
    assert(lexical_step_agrees(full, base + from, base + end, observed)) by {
        reveal(lexical_step_agrees);
        if let Some(kind) = observed {
            lexeme_shifts(full, tail, base, from, end, kind);
        }
        assert forall|later: int, kind: LexemeKind|
            #[trigger] lexeme_at(full, base + from, later, kind) implies
                base + end == later && observed == Some(kind) by {
            reveal(lexeme_at);
            lexeme_shifts(full, tail, base, from, later - base, kind);
            assert(lexeme_at(tail, from, later - base, kind));
        };
    };
    if let crate::SegmentKind::Malformed(error) = segment.kind {
        let placed = place_error(error, base);
        assert(malformed_segment_matches(full, shifted.span, placed)) by {
            reveal(malformed_segment_matches);
            if error.kind is InvalidAtom {
                bare_extent_shifts(full, tail, base, from, end);
                assert(tail[from..end] =~= full[base + from..base + end]);
            } else {
                assert(tail[from..] =~= full[base + from..]);
                assert(tail[from] == full[base + from]);
                crate::strict_string_error::relocate_first_string_error(tail[from..], from, error, base);
            }
        };
    }
}

proof fn position_in_replay(bytes: Seq<u8>, frames: Seq<ReplayFrame>, count: int)
    requires replay_valid(bytes, frames), 0 <= count <= frames.len(),
    ensures 0 <= replay_position(frames, count) <= bytes.len(),
{
    if count > 0 {
        let last = count - 1;
        assert(recovery_segment_at(bytes, replay_position(frames, last), replay_separator(frames, last),
            frames[last].segment)) by { reveal(replay_valid); };
        reveal(recovery_segment_at);
    }
}

proof fn aligned_segment_at(
    full: Seq<u8>, tail: Seq<u8>, all: Seq<ReplayFrame>, part: Seq<ReplayFrame>, split: int, base: int, i: int,
)
    requires
        0 <= base <= full.len() <= usize::MAX,
        tail == full[base..],
        valid_utf8(full), valid_utf8(tail),
        replay_valid(full, all), replay_valid(tail, part),
        0 <= split <= split + i < all.len(),
        0 <= i < part.len(),
        replay_position(all, split) == base,
        !replay_separator(all, split),
    ensures all[split + i].segment == place_segment(part[i].segment, base),
    decreases i,
{
    if i > 0 {
        aligned_segment_at(full, tail, all, part, split, base, i - 1);
        position_in_replay(tail, part, i);
        assert(all[split + i - 1].segment == place_segment(part[i - 1].segment, base));
        assert(replay_position(all, split + i) == base + replay_position(part, i));
        assert(replay_separator(all, split + i) == replay_separator(part, i));
    }
    let from = replay_position(part, i);
    let mode = replay_separator(part, i);
    let left = all[split + i].segment;
    let right = part[i].segment;
    assert(recovery_segment_at(tail, from, mode, right)) by { reveal(replay_valid); };
    assert(recovery_segment_at(full, base + from, mode, left)) by { reveal(replay_valid); };
    recovery_segment_shifts(full, tail, base, from, mode, right);
    recovery_segments_agree(full, base + from, mode, left, place_segment(right, base));
}

/// 同じ接尾部を区切り不要の状態から読むと、字句数と相対位置が一致する。
pub(super) proof fn suffix_segments_align(
    full: Seq<u8>, tail: Seq<u8>, all: Seq<ReplayFrame>, part: Seq<ReplayFrame>, split: int, base: int,
)
    requires
        0 <= base <= full.len() <= usize::MAX,
        tail == full[base..],
        valid_utf8(full), valid_utf8(tail),
        replay_valid(full, all), replay_valid(tail, part),
        0 <= split <= all.len(),
        replay_position(all, split) == base,
        !replay_separator(all, split),
        replay_position(all, all.len() as int) == full.len(),
        replay_position(part, part.len() as int) == tail.len(),
    ensures
        all.len() == split + part.len(),
        forall|i: int| 0 <= i < part.len() ==> all[split + i].segment == place_segment((#[trigger] part[i]).segment, base),
{
    let n = all.len() - split;
    let m = part.len() as int;
    if n != m {
        let stop = if n < m { n } else { m };
        if stop > 0 {
            aligned_segment_at(full, tail, all, part, split, base, stop - 1);
            position_in_replay(tail, part, stop);
        }
        assert(replay_position(all, split + stop) == base + replay_position(part, stop));
        if n < m {
            assert(recovery_segment_at(tail, tail.len() as int, replay_separator(part, stop), part[stop].segment)) by {
                reveal(replay_valid);
            };
        } else {
            assert(recovery_segment_at(full, full.len() as int, replay_separator(all, split + stop), all[split + stop].segment)) by {
                reveal(replay_valid);
            };
        }
        reveal(recovery_segment_at);
        assert(false);
    }
    assert forall|i: int| 0 <= i < m implies all[split + i].segment == place_segment((#[trigger] part[i]).segment, base) by {
        aligned_segment_at(full, tail, all, part, split, base, i);
    };
}

} // verus!
