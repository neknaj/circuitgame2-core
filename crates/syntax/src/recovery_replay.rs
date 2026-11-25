//! 元の字句と回復規則から、構文木と診断の列を定める。

use crate::{Error, ErrorKind, Form, Repair, Segment, SegmentKind, form_span, recovery_segment_at, recovery_segments_agree};
use crate::recovery_boundary::{settled_boundary_in_replay, settled_recovery_boundary};
use core::ops::Range;
use vstd::{prelude::*, string::StringSliceAdditionalSpecFns, utf8::encode_utf8_valid_utf8};

mod original_lists;
pub(crate) use original_lists::retained_original_lists_agree;
mod lexical_shift;
mod clean_prefix;
pub(super) mod placement;
use placement::{after_prefix, place_form, place_range, place_repair, place_segment,
    project_completed_suffix, project_recovery_frames};
use clean_prefix::{clean_middle_segments_align, clean_prefix_frames_agree};

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

pub(super) proof fn replay_frame_evidence(bytes: Seq<u8>, frames: Seq<ReplayFrame>, i: int)
    requires replay_valid(bytes, frames), 0 <= i < frames.len(),
    ensures
        recovery_segment_at(bytes, replay_position(frames, i), replay_separator(frames, i), frames[i].segment),
        frames[i].after == apply_recovery_segment(replay_at(frames, i), frames[i].segment),
{
    reveal(replay_valid);
}

#[verifier::opaque]
pub(super) open spec fn replay_checkpoint(
    bytes: Seq<u8>, frames: Seq<ReplayFrame>, position: int, separator: bool, state: RecoveryState,
) -> bool {
    let count = frames.len() as int;
    &&& replay_valid(bytes, frames)
    &&& replay_position(frames, count) == position
    &&& replay_separator(frames, count) == separator
    &&& replay_at(frames, count) == state
}

pub(super) proof fn start_recovery(bytes: Seq<u8>)
    ensures replay_checkpoint(bytes, Seq::empty(), 0, false, initial_recovery()),
{
    reveal(replay_valid);
    reveal(replay_checkpoint);
}

pub(super) proof fn record_recovery_frame(
    bytes: Seq<u8>, frames: Seq<ReplayFrame>, position: int, separator: bool, segment: Segment,
    before: RecoveryState, after: RecoveryState,
)
    requires
        replay_checkpoint(bytes, frames, position, separator, before),
        recovery_segment_at(bytes, position, separator, segment),
        after == apply_recovery_segment(before, segment),
    ensures replay_checkpoint(bytes, frames.push(ReplayFrame { segment, after }),
        segment.span.end as int, segment.kind.is_atom(), after),
{
    reveal(replay_checkpoint);
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

pub(super) proof fn seal_recovery(
    source: &str, frames: Seq<ReplayFrame>, separator: bool, before: RecoveryState, completed: RecoveryState,
)
    requires
        replay_checkpoint(source.spec_bytes(), frames, source.spec_bytes().len() as int, separator, before),
        completed == finish_recovery(before, source.spec_bytes().len() as int),
    ensures recovered_replay_matches(source, completed.forms, completed.repairs, completed.original),
{
    reveal(replay_checkpoint);
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

pub(super) proof fn recovery_replay_transfers_on_bytes(left: &str, right: &str, result: &crate::Recovered)
    requires
        left.spec_bytes() == right.spec_bytes(),
        recovered_replay_matches(left, result.forms@, result.repairs@, result.original_lists@),
    ensures recovered_replay_matches(right, result.forms@, result.repairs@, result.original_lists@),
{
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
    let a = recovered_history(old, left);
    let b = recovered_history(new, right);
    finished_frames_agree(old.spec_bytes(), a, b);
}

proof fn recovered_history(source: &str, recovered: &crate::Recovered) -> (frames: Seq<ReplayFrame>)
    requires recovered_replay_matches(source, recovered.forms@, recovered.repairs@, recovered.original_lists@),
    ensures
        replay_valid(source.spec_bytes(), frames),
        replay_position(frames, frames.len() as int) == source.spec_bytes().len(),
        ({
            let result = finish_recovery(replay_at(frames, frames.len() as int), source.spec_bytes().len() as int);
            result.forms == recovered.forms@ && result.repairs == recovered.repairs@ && result.original == recovered.original_lists@
        }),
{
    let bytes = source.spec_bytes();
    let eof = bytes.len() as int;
    choose|frames: Seq<ReplayFrame>| {
        let result = finish_recovery(replay_at(frames, frames.len() as int), eof);
        &&& #[trigger] replay_valid(bytes, frames)
        &&& replay_position(frames, frames.len() as int) == eof
        &&& result.forms == recovered.forms@
        &&& result.repairs == recovered.repairs@
        &&& result.original == recovered.original_lists@
    }
}

spec fn prefix_budget(state: RecoveryState, consumed: int) -> bool {
    &&& state.forms.len() <= consumed
    &&& state.repairs.len() <= 2 * consumed
    &&& state.open.len() <= state.forms.len()
    &&& forall|i: int| 0 <= i < state.open.len() ==> (#[trigger] state.open[i]) < state.forms.len()
    &&& state.root matches Some((_, before)) ==> before <= state.repairs.len()
}

proof fn replay_prefix_budget(bytes: Seq<u8>, frames: Seq<ReplayFrame>, count: int)
    requires
        3 * bytes.len() + 1 < usize::MAX,
        replay_valid(bytes, frames),
        0 <= count <= frames.len(),
    ensures
        0 <= replay_position(frames, count) <= bytes.len(),
        prefix_budget(replay_at(frames, count), replay_position(frames, count)),
    decreases count,
{
    if count > 0 {
        let i = count - 1;
        replay_prefix_budget(bytes, frames, i);
        let before = replay_at(frames, i);
        let from = replay_position(frames, i);
        let frame = frames[i];
        let segment = frame.segment;
        assert(recovery_segment_at(bytes, from, replay_separator(frames, i), segment)
            && frame.after == apply_recovery_segment(before, segment)) by { reveal(replay_valid); };
        reveal(recovery_segment_at);
        reveal(apply_recovery_segment);
        let after = frame.after;
        assert(after.forms.len() <= before.forms.len() + 1);
        assert(after.repairs.len() <= before.repairs.len() + 2);
        assert(after.repairs.len() >= before.repairs.len());
        assert(after.open.len() <= after.forms.len());
        assert forall|j: int| 0 <= j < after.open.len() implies (#[trigger] after.open[j]) < after.forms.len() by {
            if j < before.open.len() {
                assert(after.open[j] == before.open[j]);
            } else {
                assert(segment.kind is Open && j == before.open.len());
                assert(after.open[j] == before.forms.len());
            }
        };
    }
}

/// 全文の結果に含まれる接尾部と、接尾部を単独で読んだ結果との位置の対応を表す。
pub closed spec fn recovery_suffix_projection(
    whole: &crate::Recovered, tail: &crate::Recovered, base: usize, counts: (nat, nat, nat),
) -> bool {
    let (forms, repairs, original) = counts;
    &&& forms <= whole.forms@.len()
    &&& repairs <= whole.repairs@.len()
    &&& original <= whole.original_lists@.len()
    &&& whole.forms@ == whole.forms@.take(forms as int)
        + tail.forms@.map_values(|form: Form| place_form(form, forms as int, base as int))
    &&& whole.repairs@ == whole.repairs@.take(repairs as int)
        + tail.repairs@.map_values(|repair: Repair| place_repair(repair, forms as int, base as int))
    &&& whole.original_lists@ == whole.original_lists@.take(original as int)
        + tail.original_lists@.map_values(|span: Range<usize>| place_range(span, base as int))
}

proof fn project_history_suffix(
    full: Seq<u8>, tail: Seq<u8>, all: Seq<ReplayFrame>, part: Seq<ReplayFrame>, split: int, offset: usize,
)
    requires
        3 * full.len() + 1 < usize::MAX,
        offset <= full.len(),
        tail == full[offset as int..],
        vstd::utf8::valid_utf8(full), vstd::utf8::valid_utf8(tail),
        replay_valid(full, all), replay_valid(tail, part),
        0 <= split <= all.len(),
        replay_position(all, split) == offset,
        !replay_separator(all, split),
        replay_at(all, split).open.len() == 0,
        replay_at(all, split).root is None,
        replay_position(all, all.len() as int) == full.len(),
        replay_position(part, part.len() as int) == tail.len(),
    ensures finish_recovery(replay_at(all, all.len() as int), full.len() as int)
        == after_prefix(replay_at(all, split), finish_recovery(replay_at(part, part.len() as int), tail.len() as int), offset as int),
{
    let prefix = replay_at(all, split);
    replay_prefix_budget(full, all, split);
    assert forall|i: int| 0 <= i < part.len() implies {
        let before = replay_at(part, i);
        let segment = (#[trigger] part[i]).segment;
        &&& placement::can_place(prefix, before)
        &&& (segment.missing_separator ==> prefix.repairs.len() + before.repairs.len() + 1 < usize::MAX)
    } by {
        replay_prefix_budget(tail, part, i);
    };
    replay_prefix_budget(tail, part, part.len() as int);
    project_completed_suffix(full, tail, all, part, split, offset as int);
}

/// 確認済みの境界から末尾までを単独で回復した結果は、位置を移せば全文解析の同じ部分と一致する。
///
/// 戻り値は境界より前に確定した構文、修復、元リストの件数。本文長の条件は位置と件数の加算を保証する。
pub proof fn recovered_suffix_agrees(
    source: &str, suffix: &str, offset: usize, whole: &crate::Recovered, tail: &crate::Recovered,
) -> (counts: (nat, nat, nat))
    requires
        settled_recovery_boundary(source, offset),
        suffix.spec_bytes() == source.spec_bytes()[offset as int..],
        3 * source.spec_bytes().len() + 1 < usize::MAX,
        recovered_replay_matches(source, whole.forms@, whole.repairs@, whole.original_lists@),
        recovered_replay_matches(suffix, tail.forms@, tail.repairs@, tail.original_lists@),
    ensures recovery_suffix_projection(whole, tail, offset, counts),
{
    let full_bytes = source.spec_bytes();
    let tail_bytes = suffix.spec_bytes();
    encode_utf8_valid_utf8(source@);
    encode_utf8_valid_utf8(suffix@);
    let all = recovered_history(source, whole);
    let part = recovered_history(suffix, tail);
    let split = settled_boundary_in_replay(source, offset, all);
    let prefix = replay_at(all, split);
    project_history_suffix(full_bytes, tail_bytes, all, part, split, offset);
    let forms = prefix.forms.len();
    let repairs = prefix.repairs.len();
    let original = prefix.original.len();
    let moved = after_prefix(prefix, finish_recovery(replay_at(part, part.len() as int), tail_bytes.len() as int), offset as int);
    assert(whole.forms@.take(forms as int) =~= prefix.forms);
    assert(whole.repairs@.take(repairs as int) =~= prefix.repairs);
    assert(whole.original_lists@.take(original as int) =~= prefix.original);
    (forms, repairs, original)
}

proof fn clean_prefix_history(
    input: &str, recovered: &crate::Recovered, length: usize,
) -> (trace: Seq<ReplayFrame>)
    requires
        input.spec_bytes().len() == length,
        settled_recovery_boundary(input, length),
        recovered.repairs@.len() == 0,
        recovered_replay_matches(input, recovered.forms@, recovered.repairs@, recovered.original_lists@),
    ensures
        replay_valid(input.spec_bytes(), trace),
        replay_position(trace, trace.len() as int) == length,
        !replay_separator(trace, trace.len() as int),
        trace.len() > 0 ==> trace.last().segment.kind is Close,
        ({
            let state = replay_at(trace, trace.len() as int);
            &&& state.forms == recovered.forms@
            &&& state.repairs == recovered.repairs@
            &&& state.original == recovered.original_lists@
            &&& state.open.len() == 0
            &&& state.root is None
        }),
{
    let frames = recovered_history(input, recovered);
    let split = settled_boundary_in_replay(input, length, frames);
    let count = frames.len() as int;
    if split < count {
        assert(recovery_segment_at(input.spec_bytes(), length as int, replay_separator(frames, split),
            frames[split].segment)) by { reveal(replay_valid); };
        reveal(recovery_segment_at);
        assert(false);
    }
    reveal(finish_recovery);
    frames
}

pub(super) proof fn clean_prefix_form_count(input: &str, parsed: &crate::Recovered, length: usize)
    requires
        input.spec_bytes().len() == length,
        settled_recovery_boundary(input, length),
        parsed.repairs@.len() == 0,
        recovered_replay_matches(input, parsed.forms@, parsed.repairs@, parsed.original_lists@),
        3 * length + 1 < usize::MAX,
    ensures parsed.forms@.len() <= length,
{
    let frames = clean_prefix_history(input, parsed, length);
    replay_prefix_budget(input.spec_bytes(), frames, frames.len() as int);
}

spec fn project_parts_state(
    head: &crate::Recovered, changed: &crate::Recovered, tail: &crate::Recovered, start: usize, join: usize,
) -> RecoveryState {
    let prefix = RecoveryState {
        forms: head.forms@, open: Seq::empty(), repairs: head.repairs@, original: head.original_lists@, root: None,
    };
    let middle = RecoveryState {
        forms: changed.forms@, open: Seq::empty(), repairs: changed.repairs@, original: changed.original_lists@, root: None,
    };
    let suffix = RecoveryState {
        forms: tail.forms@, open: Seq::empty(), repairs: tail.repairs@, original: tail.original_lists@, root: None,
    };
    after_prefix(after_prefix(prefix, middle, start as int), suffix, join as int)
}

/// 前半・変更区間・接尾部の相対結果を並べたとき、全文の構文、修復、確定した元のリストになることを表す。
pub closed spec fn recovery_three_parts_projection(
    whole: &crate::Recovered, head: &crate::Recovered, changed: &crate::Recovered, tail: &crate::Recovered,
    start: usize, join: usize,
) -> bool {
    let placed = project_parts_state(head, changed, tail, start, join);
    &&& placed.forms == whole.forms@
    &&& placed.repairs == whole.repairs@
    &&& placed.original == whole.original_lists@
}

pub(super) proof fn observe_tail_repairs(
    whole: &crate::Recovered, head: &crate::Recovered, changed: &crate::Recovered, tail: &crate::Recovered,
    start: usize, join: usize,
)
    requires
        recovery_three_parts_projection(whole, head, changed, tail, start, join),
        head.repairs@.len() == 0,
        changed.repairs@.len() == 0,
    ensures whole.repairs@ == tail.repairs@.map_values(|repair: Repair|
        place_repair(repair, head.forms@.len() as int + changed.forms@.len(), join as int)),
{
    let placed = project_parts_state(head, changed, tail, start, join);
    let forms_before = head.forms@.len() as int + changed.forms@.len();
    assert(placed.repairs =~= tail.repairs@.map_values(|repair: Repair| place_repair(repair, forms_before, join as int)));
}

pub(super) proof fn observe_recovery_projection(
    whole: &crate::Recovered, head: &crate::Recovered, changed: &crate::Recovered, tail: &crate::Recovered,
    start: usize, join: usize, section: int, local: &crate::Recovered,
    byte: int, form_base: int, list_base: int,
)
    requires
        recovery_three_parts_projection(whole, head, changed, tail, start, join),
        0 <= section < 3,
        if section == 0 {
            local == head && byte == 0 && form_base == 0 && list_base == 0
        } else if section == 1 {
            local == changed && byte == start && form_base == head.forms@.len()
                && list_base == head.original_lists@.len()
        } else {
            local == tail && byte == join && form_base == head.forms@.len() + changed.forms@.len()
                && list_base == head.original_lists@.len() + changed.original_lists@.len()
        },
    ensures
        whole.repairs@.len() == head.repairs@.len() + changed.repairs@.len() + tail.repairs@.len(),
        whole.original_lists@.len() == head.original_lists@.len() + changed.original_lists@.len() + tail.original_lists@.len(),
        0 <= form_base && form_base + local.forms@.len() <= whole.forms@.len(),
        0 <= list_base && list_base + local.original_lists@.len() <= whole.original_lists@.len(),
        forall|i: int| 0 <= i < local.forms@.len()
            ==> form_span(#[trigger] whole.forms@[form_base + i]) == place_range(form_span(local.forms@[i]), byte),
        forall|i: int| 0 <= i < local.original_lists@.len()
            ==> #[trigger] whole.original_lists@[list_base + i] == place_range(local.original_lists@[i], byte),
{
    let placed = project_parts_state(head, changed, tail, start, join);
    assert(placed.forms == whole.forms@);
    assert(placed.repairs == whole.repairs@);
    assert(placed.original == whole.original_lists@);
    assert forall|i: int| 0 <= i < local.forms@.len() implies
        #[trigger] whole.forms@[form_base + i] == place_form(local.forms@[i], form_base, byte) by {
        if section == 0 {
            let form = local.forms@[i];
            assert(place_form(form, 0, 0) == form) by {
                assert(place_range(form_span(form), 0) == form_span(form));
            };
        }
    }
    assert forall|i: int| 0 <= i < local.forms@.len() implies
        form_span(#[trigger] whole.forms@[form_base + i]) == place_range(form_span(local.forms@[i]), byte) by {
        assert(whole.forms@[form_base + i] == place_form(local.forms@[i], form_base, byte));
    }
    assert forall|i: int| 0 <= i < local.original_lists@.len() implies
        #[trigger] whole.original_lists@[list_base + i] == place_range(local.original_lists@[i], byte) by {
        if section == 0 {
            let span = local.original_lists@[i];
            assert(place_range(span, 0) == span);
        }
    }
}

proof fn clean_middle_ends_at(
    all: Seq<ReplayFrame>, local: Seq<ReplayFrame>, split: int, start: usize, join: usize,
)
    requires
        start <= join,
        0 <= split <= split + local.len() <= all.len(),
        replay_position(all, split) == start,
        !replay_separator(all, split),
        replay_position(local, local.len() as int) == join - start,
        local.len() > 0 ==> local.last().segment.kind is Close,
        forall|i: int| 0 <= i < local.len() ==> all[split + i].segment == place_segment((#[trigger] local[i]).segment, start as int),
    ensures
        replay_position(all, split + local.len()) == join,
        !replay_separator(all, split + local.len()),
{
    if local.len() > 0 {
        let i = local.len() as int - 1;
        let segment = local[i].segment;
        assert(segment == local.last().segment);
        assert(segment.span.end == join - start);
        assert(all[split + i].segment == place_segment(segment, start as int));
        assert(all[split + i].segment.span.end == join);
        assert(all[split + i].segment.kind is Close);
    }
}

proof fn clean_middle_placement_budget(
    prefix: RecoveryState, middle: Seq<u8>, local: Seq<ReplayFrame>, start: usize,
)
    requires
        prefix_budget(prefix, start as int),
        3 * (start + middle.len()) + 1 < usize::MAX,
        replay_valid(middle, local),
    ensures
        forall|i: int| 0 <= i < local.len() ==> {
            let segment = (#[trigger] local[i]).segment;
            let state = replay_at(local, i);
            &&& placement::can_place(prefix, state)
            &&& (segment.missing_separator ==> prefix.repairs.len() + state.repairs.len() + 1 < usize::MAX)
        },
{
    assert forall|i: int| 0 <= i < local.len() implies {
        let segment = (#[trigger] local[i]).segment;
        let state = replay_at(local, i);
        &&& placement::can_place(prefix, state)
        &&& (segment.missing_separator ==> prefix.repairs.len() + state.repairs.len() + 1 < usize::MAX)
    } by {
        replay_prefix_budget(middle, local, i);
    };
}

proof fn compose_clean_middle(
    full: Seq<u8>, middle: Seq<u8>, all: Seq<ReplayFrame>, local: Seq<ReplayFrame>,
    split: int, start: usize, join: usize,
)
    requires
        3 * full.len() + 1 < usize::MAX,
        start <= join <= full.len(),
        middle == full[start as int..join as int],
        replay_valid(full, all), replay_valid(middle, local),
        0 <= split <= all.len(),
        replay_position(all, split) == start,
        !replay_separator(all, split),
        replay_at(all, split).open.len() == 0,
        replay_at(all, split).root is None,
        replay_position(all, all.len() as int) == full.len(),
        replay_position(local, local.len() as int) == middle.len(),
        local.len() > 0 ==> local.last().segment.kind is Close,
        replay_at(local, local.len() as int).repairs.len() == 0,
    ensures
        split + local.len() <= all.len(),
        replay_position(all, split + local.len()) == join,
        !replay_separator(all, split + local.len()),
        replay_at(all, split + local.len())
            == after_prefix(replay_at(all, split), replay_at(local, local.len() as int), start as int),
{
    let count = local.len() as int;
    let before = replay_at(all, split);
    clean_middle_segments_align(full, middle, all, local, split, start as int);
    clean_middle_ends_at(all, local, split, start, join);
    replay_prefix_budget(full, all, split);
    clean_middle_placement_budget(before, middle, local, start);
    assert forall|i: int| 0 <= i < count implies {
        let segment = (#[trigger] local[i]).segment;
        let state = replay_at(local, i);
        &&& all[split + i].segment == place_segment(segment, start as int)
        &&& placement::can_place(before, state)
        &&& (segment.missing_separator ==> before.repairs.len() + state.repairs.len() + 1 < usize::MAX)
    } by {
    };
    project_recovery_frames(full, middle, all, local, split, count, start as int);
}

/// 元の閉じ括弧で終わる妥当な接頭部と変更区間を使い、相対結果から全文の回復結果を求められることを示す。
pub proof fn recovered_three_parts_agree(
    source: &str, prefix: &str, middle: &str, suffix: &str, start: usize, join: usize,
    whole: &crate::Recovered, head: &crate::Recovered, changed: &crate::Recovered, tail: &crate::Recovered,
)
    requires
        3 * source.spec_bytes().len() + 1 < usize::MAX,
        start <= join <= source.spec_bytes().len(),
        prefix.spec_bytes() == source.spec_bytes()[..start as int],
        middle.spec_bytes() == source.spec_bytes()[start as int..join as int],
        suffix.spec_bytes() == source.spec_bytes()[join as int..],
        settled_recovery_boundary(prefix, start),
        settled_recovery_boundary(middle, (join - start) as usize),
        head.repairs@.len() == 0,
        changed.repairs@.len() == 0,
        recovered_replay_matches(source, whole.forms@, whole.repairs@, whole.original_lists@),
        recovered_replay_matches(prefix, head.forms@, head.repairs@, head.original_lists@),
        recovered_replay_matches(middle, changed.forms@, changed.repairs@, changed.original_lists@),
        recovered_replay_matches(suffix, tail.forms@, tail.repairs@, tail.original_lists@),
    ensures recovery_three_parts_projection(whole, head, changed, tail, start, join),
{
    let full_bytes = source.spec_bytes();
    let head_bytes = prefix.spec_bytes();
    let middle_bytes = middle.spec_bytes();
    let tail_bytes = suffix.spec_bytes();
    let all = recovered_history(source, whole);
    let first = clean_prefix_history(prefix, head, start);
    let local = clean_prefix_history(middle, changed, (join - start) as usize);
    let after = recovered_history(suffix, tail);
    let split = first.len() as int;
    let count = local.len() as int;
    clean_prefix_frames_agree(full_bytes, head_bytes, all, first);
    if split > 0 {
        assert(all.take(split)[split - 1] == all[split - 1]);
        assert(all[split - 1] == first[split - 1]);
    }
    assert(replay_at(all, split) == replay_at(first, split));
    assert(replay_position(all, split) == start);
    assert(!replay_separator(all, split));
    compose_clean_middle(full_bytes, middle_bytes, all, local, split, start, join);
    assert(replay_at(all, split + count).open.len() == 0);
    assert(replay_at(all, split + count).root is None);
    encode_utf8_valid_utf8(source@);
    encode_utf8_valid_utf8(suffix@);
    project_history_suffix(full_bytes, tail_bytes, all, after, split + count, join);
    assert(recovery_three_parts_projection(whole, head, changed, tail, start, join));
}

} // verus!
