//! 元の字句と回復規則から、構文木と診断の列を定める。

use crate::{Error, ErrorKind, Form, Repair, Segment, SegmentKind, form_span, recovery_segment_at, recovery_segments_agree};
use core::ops::Range;
use vstd::{prelude::*, string::StringSliceAdditionalSpecFns};

mod placement;

verus! {

pub(super) struct RecoveryState {
    pub(super) forms: Seq<Form>,
    pub(super) open: Seq<usize>,
    pub(super) repairs: Seq<Repair>,
    pub(super) original: Seq<Range<usize>>,
    pub(super) root: Option<(usize, usize)>,
}

pub(super) struct ReplayFrame {
    pub(super) segment: Segment,
    pub(super) after: RecoveryState,
}

pub(super) open spec fn initial_recovery() -> RecoveryState {
    RecoveryState {
        forms: Seq::empty(),
        open: Seq::empty(),
        repairs: Seq::empty(),
        original: Seq::empty(),
        root: None,
    }
}

pub(super) open spec fn close_recovery_list(state: RecoveryState, index: usize, end: usize) -> RecoveryState {
    RecoveryState {
        forms: state.forms.update(index as int, Form::List {
            span: form_span(state.forms[index as int]).start..end,
            end: state.forms.len() as usize,
        }),
        open: state.open.drop_last(),
        ..state
    }
}

#[verifier::opaque]
pub(super) open spec fn apply_recovery_segment(state: RecoveryState, segment: Segment) -> RecoveryState {
    let span = segment.span;
    let state = if segment.missing_separator {
        RecoveryState {
            repairs: state.repairs.push(Repair::InsertedSeparator { offset: span.start }),
            ..state
        }
    } else { state };
    match segment.kind {
        SegmentKind::Whitespace | SegmentKind::Comment => state,
        SegmentKind::Malformed(error) => RecoveryState {
            repairs: state.repairs.push(Repair::Skipped { span, error }), ..state
        },
        SegmentKind::Atom(kind) => RecoveryState {
            forms: state.forms.push(Form::Atom { kind, span }), ..state
        },
        SegmentKind::Open => RecoveryState {
            forms: state.forms.push(Form::List { span, end: 0 }),
            open: state.open.push(state.forms.len() as usize),
            root: if state.open.len() == 0 { Some((span.start, state.repairs.len() as usize)) } else { state.root },
            ..state
        },
        SegmentKind::Close => if state.open.len() == 0 {
            RecoveryState {
                repairs: state.repairs.push(Repair::Skipped {
                    span,
                    error: Error { kind: ErrorKind::UnexpectedClose, span },
                }),
                ..state
            }
        } else {
            let closed = close_recovery_list(state, state.open.last(), span.end);
            if closed.open.len() > 0 { closed }
            else {
                let original = match state.root {
                    Some((start, before)) if before == state.repairs.len() =>
                        state.original.push(start..span.end),
                    _ => state.original,
                };
                RecoveryState { original, root: None, ..closed }
            }
        },
    }
}

pub(super) open spec fn close_recovery_at_eof(state: RecoveryState, eof: usize) -> RecoveryState {
    let list = state.open.last();
    RecoveryState {
        repairs: state.repairs.push(Repair::InsertedClose {
            offset: eof, opening: form_span(state.forms[list as int]), list,
        }),
        ..close_recovery_list(state, list, eof)
    }
}

#[verifier::opaque]
pub(super) open spec fn finish_recovery(state: RecoveryState, eof: int) -> RecoveryState
    decreases state.open.len(),
{
    if state.open.len() == 0 { state }
    else { finish_recovery(close_recovery_at_eof(state, eof as usize), eof) }
}

pub(super) open spec fn replay_at(frames: Seq<ReplayFrame>, count: int) -> RecoveryState {
    if count == 0 { initial_recovery() } else { frames[count - 1].after }
}

pub(super) open spec fn replay_position(frames: Seq<ReplayFrame>, count: int) -> int {
    if count == 0 { 0 } else { frames[count - 1].segment.span.end as int }
}

pub(super) open spec fn replay_separator(frames: Seq<ReplayFrame>, count: int) -> bool {
    count > 0 && frames[count - 1].segment.kind.is_atom()
}

#[verifier::opaque]
pub(super) open spec fn replay_valid(bytes: Seq<u8>, frames: Seq<ReplayFrame>) -> bool {
    forall|i: int| 0 <= i < frames.len() ==> {
        let frame = #[trigger] frames[i];
        recovery_segment_at(bytes, replay_position(frames, i), replay_separator(frames, i), frame.segment)
            && frame.after == apply_recovery_segment(replay_at(frames, i), frame.segment)
    }
}

pub(super) proof fn record_recovery_frame(
    bytes: Seq<u8>, frames: Seq<ReplayFrame>, segment: Segment, after: RecoveryState,
)
    requires
        replay_valid(bytes, frames),
        recovery_segment_at(bytes, replay_position(frames, frames.len() as int),
            replay_separator(frames, frames.len() as int), segment),
        after == apply_recovery_segment(replay_at(frames, frames.len() as int), segment),
    ensures replay_valid(bytes, frames.push(ReplayFrame { segment, after })),
{
    reveal(replay_valid);
    let updated = frames.push(ReplayFrame { segment, after });
    assert forall|i: int| 0 <= i < updated.len() implies {
        let frame = #[trigger] updated[i];
        recovery_segment_at(bytes, replay_position(updated, i), replay_separator(updated, i), frame.segment)
            && frame.after == apply_recovery_segment(replay_at(updated, i), frame.segment)
    } by {
        if i < frames.len() {
            assert(updated[i] == frames[i]);
        }
    };
}

/// 元の字句から全体を回復し、構文木・修復・確定した元リストが得られることを表す。
pub closed spec fn recovered_replay_matches(
    source: &str, forms: Seq<Form>, repairs: Seq<Repair>, original: Seq<Range<usize>>,
) -> bool {
    let bytes = source.spec_bytes();
    exists|frames: Seq<ReplayFrame>| {
        let eof = bytes.len() as int;
        let completed = finish_recovery(replay_at(frames, frames.len() as int), eof);
        &&& #[trigger] replay_valid(bytes, frames)
        &&& replay_position(frames, frames.len() as int) == eof
        &&& completed.forms == forms
        &&& completed.repairs == repairs
        &&& completed.original == original
    }
}

pub(super) proof fn seal_recovery(source: &str, frames: Seq<ReplayFrame>, completed: RecoveryState)
    requires
        replay_valid(source.spec_bytes(), frames),
        replay_position(frames, frames.len() as int) == source.spec_bytes().len(),
        completed == finish_recovery(replay_at(frames, frames.len() as int), source.spec_bytes().len() as int),
    ensures recovered_replay_matches(source, completed.forms, completed.repairs, completed.original),
{
    assert(exists|history: Seq<ReplayFrame>| {
        let eof = source.spec_bytes().len() as int;
        let result = finish_recovery(replay_at(history, history.len() as int), eof);
        &&& #[trigger] replay_valid(source.spec_bytes(), history)
        &&& replay_position(history, history.len() as int) == eof
        &&& result.forms == completed.forms
        &&& result.repairs == completed.repairs
        &&& result.original == completed.original
    });
}

proof fn frames_agree(bytes: Seq<u8>, left: Seq<ReplayFrame>, right: Seq<ReplayFrame>, i: int)
    requires replay_valid(bytes, left), replay_valid(bytes, right), 0 <= i < left.len(), i < right.len(),
    ensures left[i] == right[i],
    decreases i,
{
    if i > 0 { frames_agree(bytes, left, right, i - 1); }
    reveal(replay_valid);
    recovery_segments_agree(bytes, replay_position(left, i), replay_separator(left, i),
        left[i].segment, right[i].segment);
}

proof fn finished_frames_agree(bytes: Seq<u8>, left: Seq<ReplayFrame>, right: Seq<ReplayFrame>)
    requires
        replay_valid(bytes, left), replay_valid(bytes, right),
        replay_position(left, left.len() as int) == bytes.len(),
        replay_position(right, right.len() as int) == bytes.len(),
    ensures left == right,
{
    let n = left.len() as int;
    let m = right.len() as int;
    if n != m {
        let (short, long, stop) = if n < m { (left, right, n) } else { (right, left, m) };
        if stop > 0 { frames_agree(bytes, short, long, stop - 1); }
        assert(replay_position(long, stop) == bytes.len());
        reveal(replay_valid);
        reveal(recovery_segment_at);
        assert(recovery_segment_at(bytes, replay_position(long, stop), replay_separator(long, stop), long[stop].segment));
        assert(false);
    }
    assert forall|i: int| 0 <= i < n implies #[trigger] left[i] == right[i] by {
        frames_agree(bytes, left, right, i);
    };
    assert(left =~= right);
}

/// 同じ UTF-8 バイト列の回復結果は、診断順と関連範囲を含めて一致する。
pub proof fn recovered_replays_agree(
    old: &str, new: &str, left: &crate::Recovered, right: &crate::Recovered,
)
    requires
        old.spec_bytes() == new.spec_bytes(),
        recovered_replay_matches(old, left.forms@, left.repairs@, left.original_lists@),
        recovered_replay_matches(new, right.forms@, right.repairs@, right.original_lists@),
    ensures
        left.forms@ == right.forms@,
        left.repairs@ == right.repairs@,
        left.original_lists@ == right.original_lists@,
{
    let bytes = old.spec_bytes();
    let eof = bytes.len() as int;
    let a = choose|frames: Seq<ReplayFrame>| {
        let result = finish_recovery(replay_at(frames, frames.len() as int), eof);
        &&& #[trigger] replay_valid(bytes, frames)
        &&& replay_position(frames, frames.len() as int) == eof
        &&& result.forms == left.forms@
        &&& result.repairs == left.repairs@
        &&& result.original == left.original_lists@
    };
    let b = choose|frames: Seq<ReplayFrame>| {
        let result = finish_recovery(replay_at(frames, frames.len() as int), eof);
        &&& #[trigger] replay_valid(bytes, frames)
        &&& replay_position(frames, frames.len() as int) == eof
        &&& result.forms == right.forms@
        &&& result.repairs == right.repairs@
        &&& result.original == right.original_lists@
    };
    finished_frames_agree(bytes, a, b);
}

} // verus!
