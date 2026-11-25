//! 回復解析の再開に使える、元のトップレベルの境界を確認する。

use crate::{Lexer, SegmentKind, SourceCursor};
use core::ops::Range;
#[cfg(verus_only)]
use crate::{Segment, is_suffix, recovery_segment_at, recovery_segments_agree};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::{encode_utf8_decode_utf8, encode_utf8_valid_utf8, is_char_boundary, valid_utf8}};

verus! {

#[cfg(verus_only)]
struct Step {
    segment: Segment,
    depth: nat,
}

spec fn offset_at(trace: Seq<Step>, count: int) -> int {
    if count == 0 { 0 } else { trace[count - 1].segment.span.end as int }
}

spec fn depth_at(trace: Seq<Step>, count: int) -> nat {
    if count == 0 { 0 } else { trace[count - 1].depth }
}

spec fn needs_separator_at(trace: Seq<Step>, count: int) -> bool {
    count != 0 && trace[count - 1].segment.kind.is_atom()
}

spec fn next_depth(previous: nat, kind: SegmentKind) -> nat {
    match kind {
        SegmentKind::Open => previous + 1,
        SegmentKind::Close => if previous == 0 { 0 } else { (previous - 1) as nat },
        _ => previous,
    }
}

#[verifier::opaque]
spec fn recovery_prefix(bytes: Seq<u8>, trace: Seq<Step>) -> bool {
    forall|i: int| 0 <= i < trace.len() ==> {
        let step = #[trigger] trace[i];
        &&& recovery_segment_at(bytes, offset_at(trace, i), needs_separator_at(trace, i), step.segment)
        &&& step.depth == next_depth(depth_at(trace, i), step.segment.kind)
    }
}

spec fn ends_at_boundary(trace: Seq<Step>, offset: int) -> bool {
    &&& offset_at(trace, trace.len() as int) == offset
    &&& (trace.len() == 0 || {
        &&& trace.last().segment.kind is Close
        &&& depth_at(trace, trace.len() - 1) == 1
        &&& depth_at(trace, trace.len() as int) == 0
    })
}

/// 検査対象の位置が、先頭か、深さ 1 から 0 に戻った元の閉じ括弧の直後であることを表す。
pub closed spec fn settled_recovery_boundary(source: &str, offset: usize) -> bool {
    let bytes = source.spec_bytes();
    &&& offset <= bytes.len()
    &&& is_char_boundary(bytes, offset as int)
    &&& exists|trace: Seq<Step>| #[trigger] recovery_prefix(bytes, trace)
        && ends_at_boundary(trace, offset as int)
}

/// 解析対象の本文に結び付いた、元の回復境界。
pub struct RecoveryBoundary<'a> {
    source: &'a str,
    offset: usize,
}

impl<'a> RecoveryBoundary<'a> {
    /// 検査した本文を表す。
    pub closed spec fn source_model(&self) -> &'a str { self.source }

    /// ファイル先頭から測った位置を表す。
    pub closed spec fn offset_model(&self) -> usize { self.offset }

    #[verifier::type_invariant]
    spec fn valid(&self) -> bool { settled_recovery_boundary(self.source, self.offset) }

    /// 境界の UTF-8 バイト位置を返す。
    pub fn offset(&self) -> (offset: usize)
        ensures offset == self.offset_model(),
    {
        self.offset
    }

    /// 境界から本文末尾までを返す。区切り要求や未終了のリストを引き継ぐ必要はない。
    pub fn suffix(&self) -> (suffix: &'a str)
        ensures
            settled_recovery_boundary(self.source_model(), self.offset_model()),
            suffix.spec_bytes() == self.source_model().spec_bytes()[self.offset_model() as int..],
    {
        proof {
            use_type_invariant(self);
            encode_utf8_valid_utf8(self.source@);
        }
        self.source.split_at(self.offset).1
    }

    /// 検査済みの境界から末尾までの UTF-8 バイト列を照合する。境界の位置は異なってよい。
    pub fn same_suffix(&self, other: &RecoveryBoundary<'_>) -> (matches: bool)
        ensures
            matches == (self.source_model().spec_bytes()[self.offset_model() as int..]
                == other.source_model().spec_bytes()[other.offset_model() as int..]),
            settled_recovery_boundary(self.source_model(), self.offset_model()),
            settled_recovery_boundary(other.source_model(), other.offset_model()),
    {
        let a = self.suffix();
        let b = other.suffix();
        proof {
            encode_utf8_decode_utf8(a@);
            encode_utf8_decode_utf8(b@);
        }
        a == b
    }
}

proof fn push_step(bytes: Seq<u8>, trace: Seq<Step>, segment: Segment, depth: nat)
    requires
        recovery_prefix(bytes, trace),
        recovery_segment_at(bytes, offset_at(trace, trace.len() as int), needs_separator_at(trace, trace.len() as int), segment),
        depth == next_depth(depth_at(trace, trace.len() as int), segment.kind),
    ensures recovery_prefix(bytes, trace.push(Step { segment, depth })),
{
    reveal(recovery_prefix);
    let next = trace.push(Step { segment, depth });
    assert forall|i: int| 0 <= i < next.len() implies {
        let step = #[trigger] next[i];
        &&& recovery_segment_at(bytes, offset_at(next, i), needs_separator_at(next, i), step.segment)
        &&& step.depth == next_depth(depth_at(next, i), step.segment.kind)
    } by {
        if i < trace.len() {
            assert(next[i] == trace[i]);
        }
    };
}

proof fn trace_offsets_increase(bytes: Seq<u8>, trace: Seq<Step>, low: int, high: int)
    requires recovery_prefix(bytes, trace), 0 <= low < high <= trace.len(),
    ensures offset_at(trace, low) < offset_at(trace, high),
    decreases high - low,
{
    assert(offset_at(trace, high - 1) < offset_at(trace, high)) by {
        reveal(recovery_prefix);
        reveal(recovery_segment_at);
        assert(recovery_segment_at(bytes, offset_at(trace, high - 1),
            needs_separator_at(trace, high - 1), trace[high - 1].segment));
    };
    if low < high - 1 {
        trace_offsets_increase(bytes, trace, low, high - 1);
    }
}

proof fn recovery_steps_agree(bytes: Seq<u8>, a: Seq<Step>, b: Seq<Step>, i: int)
    requires recovery_prefix(bytes, a), recovery_prefix(bytes, b), 0 <= i < a.len(), i < b.len(),
    ensures a[i] == b[i],
    decreases i,
{
    if i > 0 {
        recovery_steps_agree(bytes, a, b, i - 1);
    }
    assert(a[i] == b[i]) by {
        reveal(recovery_prefix);
        recovery_segments_agree(bytes, offset_at(a, i), needs_separator_at(a, i), a[i].segment, b[i].segment);
    };
}

proof fn observed_checkpoint(source: &str, offset: usize, observed: Seq<Step>)
    requires
        recovery_prefix(source.spec_bytes(), observed),
        0 < observed.len(),
        offset_at(observed, observed.len() - 1) < offset <= offset_at(observed, observed.len() as int),
        offset <= source.spec_bytes().len(),
        valid_utf8(source.spec_bytes()),
        is_char_boundary(source.spec_bytes(), offset as int),
    ensures settled_recovery_boundary(source, offset) == ends_at_boundary(observed, offset as int),
{
    let bytes = source.spec_bytes();
    if ends_at_boundary(observed, offset as int) {
        assert(exists|trace: Seq<Step>| #[trigger] recovery_prefix(bytes, trace)
            && ends_at_boundary(trace, offset as int));
    }
    if settled_recovery_boundary(source, offset) {
        let trace = choose|trace: Seq<Step>| #[trigger] recovery_prefix(bytes, trace)
            && ends_at_boundary(trace, offset as int);
        let n = observed.len() as int;
        let m = trace.len() as int;
        if m < n {
            if m > 0 {
                recovery_steps_agree(bytes, observed, trace, m - 1);
            }
            assert(offset_at(observed, m) == offset_at(trace, m));
            if m < n - 1 {
                trace_offsets_increase(bytes, observed, m, n - 1);
            }
            assert(false);
        } else if n < m {
            recovery_steps_agree(bytes, observed, trace, n - 1);
            assert(offset_at(observed, n) == offset_at(trace, n));
            trace_offsets_increase(bytes, trace, n, m);
            assert(false);
        }
        assert forall|i: int| 0 <= i < n implies #[trigger] observed[i] == trace[i] by {
            recovery_steps_agree(bytes, observed, trace, i);
        };
        assert(observed =~= trace);
    }
}

impl<'a> RecoveryBoundary<'a> {
    /// 確認済みの境界から字句を読み進め、指定した位置が境界かを確かめる。
    ///
    /// 指定位置はファイル先頭からの UTF-8 バイト位置である。現在の境界より手前では `None` を返す。
    /// 現在の境界より前にあった字句は読み直さない。
    pub fn scan_to(&self, offset: usize) -> (boundary: Option<Self>)
        ensures
            boundary.is_some() == (self.offset_model() <= offset && settled_recovery_boundary(self.source_model(), offset)),
            boundary matches Some(boundary) ==> boundary.source_model() == self.source_model() && boundary.offset_model() == offset,
    {
        proof { use_type_invariant(self); }
        let source = self.source;
        let length = source.as_bytes().len();
        if offset < self.offset || offset > length || !source.is_char_boundary(offset) {
            return None;
        }
        let ghost bytes = source.spec_bytes();
        proof { encode_utf8_valid_utf8(source@); }
        if offset == self.offset {
            return Some(RecoveryBoundary { source, offset });
        }
        let remaining = self.suffix();
        let cursor = SourceCursor { source, remaining };
        let mut lexer = Lexer { cursor, needs_separator: false };
        let ghost mut trace = choose|trace: Seq<Step>| #[trigger] recovery_prefix(bytes, trace)
            && ends_at_boundary(trace, self.offset as int);
        proof {
            assert(is_suffix(bytes, remaining.spec_bytes()));
            assert(lexer.cursor.position() == self.offset);
        }
        let mut depth = 0usize;
        loop
            invariant
                source == self.source,
                self.offset < offset,
                offset <= length,
                bytes == source.spec_bytes(),
                length == bytes.len(),
                valid_utf8(bytes),
                is_char_boundary(bytes, offset as int),
                lexer.cursor.valid(),
                lexer.cursor.source == source,
                lexer.cursor.position() < offset,
                recovery_prefix(bytes, trace),
                lexer.cursor.position() == offset_at(trace, trace.len() as int),
                lexer.needs_separator == needs_separator_at(trace, trace.len() as int),
                depth == depth_at(trace, trace.len() as int),
                depth <= lexer.cursor.position(),
            decreases offset - lexer.cursor.position(),
        {
            let Some((segment, next)) = lexer.next_segment() else { return None; };
            let end = segment.span.end;
            let previous = depth;
            match segment.kind {
                SegmentKind::Open => depth += 1,
                SegmentKind::Close if depth > 0 => depth -= 1,
                _ => {},
            }
            let ghost preceding = trace;
            proof {
                push_step(bytes, trace, segment, depth as nat);
                trace = trace.push(Step { segment, depth: depth as nat });
            }
            if end >= offset {
                proof {
                    assert(offset_at(trace, trace.len() - 1) == offset_at(preceding, preceding.len() as int));
                    assert(offset_at(trace, trace.len() as int) == end);
                    observed_checkpoint(source, offset, trace);
                }
                if end == offset && previous == 1 && matches!(segment.kind, SegmentKind::Close) {
                    assert(settled_recovery_boundary(source, offset)) by {
                        reveal(settled_recovery_boundary);
                        assert(depth_at(trace, trace.len() - 1) == depth_at(preceding, preceding.len() as int));
                        assert(ends_at_boundary(trace, offset as int));
                        assert(exists|candidate: Seq<Step>| #[trigger] recovery_prefix(bytes, candidate)
                            && ends_at_boundary(candidate, offset as int));
                    };
                    return Some(RecoveryBoundary { source, offset });
                }
                return None;
            }
            lexer = next;
        }
    }
}

/// 指定した位置が再開境界なら、その本文に結び付いた境界を返す。
///
/// 複数バイト文字の途中、文字列やコメントの中、未終了のリスト内は返さない。
/// 元の字句を先頭から指定位置まで確認する。指定位置はファイル先頭からの UTF-8 バイト位置。
/// 直前のリストに修復があっても、元の閉じ括弧で深さが 0 に戻れば境界として扱う。
/// 修復を挟まず閉じたリストは [`crate::Recovered::original_lists`] を参照する。
pub fn recovery_boundary_at(source: &str, offset: usize) -> (boundary: Option<RecoveryBoundary<'_>>)
    ensures
        boundary.is_some() == settled_recovery_boundary(source, offset),
        boundary matches Some(boundary) ==> boundary.source_model() == source && boundary.offset_model() == offset,
{
    proof {
        let bytes = source.spec_bytes();
        encode_utf8_valid_utf8(source@);
        let empty: Seq<Step> = Seq::empty();
        assert(recovery_prefix(bytes, empty)) by { reveal(recovery_prefix); };
        assert(exists|trace: Seq<Step>| #[trigger] recovery_prefix(bytes, trace) && ends_at_boundary(trace, 0));
    }
    let start = RecoveryBoundary { source, offset: 0 };
    start.scan_to(offset)
}

/// 編集後に読み直す、新旧それぞれの UTF-8 バイト範囲。
///
/// [`recovery_window`] が返す範囲の前後では、新旧の本文がそれぞれ一致する。
pub struct RecoveryWindow {
    /// 編集前の本文で読み直しに対応する範囲。
    pub old: Range<usize>,
    /// 編集後の本文で読み直す範囲。
    pub current: Range<usize>,
}

/// 再開・合流の候補が元の構文境界であり、その外側の本文が一致することを表す。
pub open spec fn recovery_window_allowed(
    old: &str, current: &str, start: usize, old_end: usize, current_end: usize,
) -> bool {
    &&& start <= old_end <= old.spec_bytes().len()
    &&& start <= current_end <= current.spec_bytes().len()
    &&& settled_recovery_boundary(old, start)
    &&& settled_recovery_boundary(current, start)
    &&& settled_recovery_boundary(old, old_end)
    &&& settled_recovery_boundary(current, current_end)
    &&& old.spec_bytes()[..start as int] == current.spec_bytes()[..start as int]
    &&& old.spec_bytes()[old_end as int..] == current.spec_bytes()[current_end as int..]
}

/// 候補の再開点と合流点を検査し、両方の本文で読み直し範囲を確定する。
///
/// 再開点は新旧で同じ位置を指定する。合流点は本文の長さの変化に応じて異なる位置を指定できる。
/// 元の構文境界や前後の本文が一致しなければ `None`。この関数は構文木を合成しない。
pub fn recovery_window(
    old: &str, current: &str, start: usize, old_end: usize, current_end: usize,
) -> (window: Option<RecoveryWindow>)
    ensures
        window.is_some() == recovery_window_allowed(old, current, start, old_end, current_end),
        window matches Some(window) ==> window.old == (start..old_end) && window.current == (start..current_end),
{
    if start > old_end || start > current_end {
        return None;
    }
    let old_start_boundary = recovery_boundary_at(old, start)?;
    let current_start_boundary = recovery_boundary_at(current, start)?;
    proof {
        reveal(settled_recovery_boundary);
        encode_utf8_valid_utf8(old@);
        encode_utf8_valid_utf8(current@);
    }
    let old_prefix = old.split_at(start).0;
    let current_prefix = current.split_at(start).0;
    proof {
        encode_utf8_decode_utf8(old_prefix@);
        encode_utf8_decode_utf8(current_prefix@);
    }
    if old_prefix != current_prefix {
        return None;
    }
    let old_end_boundary = old_start_boundary.scan_to(old_end)?;
    let current_end_boundary = current_start_boundary.scan_to(current_end)?;
    if !old_end_boundary.same_suffix(&current_end_boundary) {
        return None;
    }
    Some(RecoveryWindow { old: start..old_end, current: start..current_end })
}

} // verus!
