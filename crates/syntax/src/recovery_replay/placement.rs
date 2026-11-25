//! 合流点の前に確定した出力が、後続の回復規則に与える影響を定める。

use super::{
    RecoveryState, ReplayFrame, apply_recovery_segment, close_recovery_at_eof, close_recovery_list,
    finish_recovery, initial_recovery, replay_at, replay_position, replay_separator, replay_valid,
};
use super::lexical_shift::suffix_segments_align;
use crate::{Error, ErrorKind, Form, Repair, Segment, SegmentKind};
use core::ops::Range;
use vstd::{prelude::*, utf8::valid_utf8};

verus! {

pub(crate) open spec fn place_range(span: Range<usize>, byte: int) -> Range<usize> {
    (byte + span.start) as usize..(byte + span.end) as usize
}

pub(crate) open spec fn place_error(error: Error, byte: int) -> Error {
    let kind = match error.kind {
        ErrorKind::InvalidEscape { opening } => ErrorKind::InvalidEscape { opening: (byte + opening) as usize },
        ErrorKind::NewlineInString { opening } => ErrorKind::NewlineInString { opening: (byte + opening) as usize },
        ErrorKind::UnclosedList { eof } => ErrorKind::UnclosedList { eof: (byte + eof) as usize },
        _ => error.kind,
    };
    Error { kind, span: place_range(error.span, byte) }
}

pub(super) open spec fn place_segment(segment: Segment, byte: int) -> Segment {
    let kind = match segment.kind {
        SegmentKind::Malformed(error) => SegmentKind::Malformed(place_error(error, byte)),
        _ => segment.kind,
    };
    Segment { kind, span: place_range(segment.span, byte), missing_separator: segment.missing_separator }
}

pub(super) open spec fn place_form(form: Form, base: int, byte: int) -> Form {
    match form {
        Form::List { span, end } => Form::List {
            span: place_range(span, byte),
            end: if end == 0 { 0 } else { (base + end) as usize },
        },
        Form::Atom { kind, span } => Form::Atom { kind, span: place_range(span, byte) },
    }
}

pub(crate) open spec fn place_repair(repair: Repair, base: int, byte: int) -> Repair {
    match repair {
        Repair::InsertedClose { offset, opening, list } =>
            Repair::InsertedClose {
                offset: (byte + offset) as usize,
                opening: place_range(opening, byte),
                list: (base + list) as usize,
            },
        Repair::InsertedSeparator { offset } =>
            Repair::InsertedSeparator { offset: (byte + offset) as usize },
        Repair::Skipped { span, error } =>
            Repair::Skipped { span: place_range(span, byte), error: place_error(error, byte) },
    }
}

pub(super) open spec fn after_prefix(prefix: RecoveryState, part: RecoveryState, byte: int) -> RecoveryState {
    let base = prefix.forms.len() as int;
    RecoveryState {
        forms: prefix.forms + part.forms.map_values(|form: Form| place_form(form, base, byte)),
        open: part.open.map_values(|index: usize| (base + index) as usize),
        repairs: prefix.repairs + part.repairs.map_values(|repair: Repair| place_repair(repair, base, byte)),
        original: prefix.original + part.original.map_values(|span: Range<usize>| place_range(span, byte)),
        root: match part.root {
            Some((start, count)) => Some(((byte + start) as usize, (prefix.repairs.len() + count) as usize)),
            None => None,
        },
    }
}

pub(super) open spec fn can_place(prefix: RecoveryState, part: RecoveryState) -> bool {
    &&& prefix.forms.len() + part.forms.len() < usize::MAX
    &&& prefix.repairs.len() + part.repairs.len() < usize::MAX
    &&& part.open.len() > 0 ==> part.open.last() < part.forms.len()
    &&& part.root matches Some((_, before)) ==> before <= part.repairs.len()
}

proof fn map_push<A, B>(seq: Seq<A>, item: A, map: spec_fn(A) -> B)
    ensures seq.push(item).map_values(map) == seq.map_values(map).push(map(item)),
{
    assert(seq.push(item).map_values(map) =~= seq.map_values(map).push(map(item)));
}

proof fn map_update<A, B>(seq: Seq<A>, index: int, item: A, map: spec_fn(A) -> B)
    requires 0 <= index < seq.len(),
    ensures seq.update(index, item).map_values(map) == seq.map_values(map).update(index, map(item)),
{
    assert(seq.update(index, item).map_values(map) =~= seq.map_values(map).update(index, map(item)));
}

proof fn prefix_preserves_close(prefix: RecoveryState, part: RecoveryState, end: usize, byte: int)
    requires can_place(prefix, part), part.open.len() > 0,
    ensures
        close_recovery_list(after_prefix(prefix, part, byte), after_prefix(prefix, part, byte).open.last(), (byte + end) as usize)
            == after_prefix(prefix, close_recovery_list(part, part.open.last(), end), byte),
{
    let base = prefix.forms.len() as int;
    let original = part.open.last();
    let full = after_prefix(prefix, part, byte);
    let chosen = close_recovery_list(part, original, end);
    let merged = close_recovery_list(full, full.open.last(), (byte + end) as usize);
    let mapped = |form: Form| place_form(form, base, byte);
    let changed = chosen.forms[original as int];
    assert(full.open.last() == base + original);
    assert(full.forms[base + original] == mapped(part.forms[original as int]));
    assert(merged.forms[base + original] == mapped(changed));
    map_update(part.forms, original as int, changed, mapped);
    assert(merged.forms =~= after_prefix(prefix, chosen, byte).forms);
    assert(merged.open =~= after_prefix(prefix, chosen, byte).open);
}

proof fn prefix_preserves_repair(prefix: RecoveryState, part: RecoveryState, repair: Repair, byte: int)
    ensures
        after_prefix(prefix, RecoveryState { repairs: part.repairs.push(repair), ..part }, byte).repairs
            == after_prefix(prefix, part, byte).repairs.push(place_repair(repair, prefix.forms.len() as int, byte)),
{
    let base = prefix.forms.len() as int;
    map_push(part.repairs, repair, |repair: Repair| place_repair(repair, base, byte));
    assert(after_prefix(prefix, RecoveryState { repairs: part.repairs.push(repair), ..part }, byte).repairs
        =~= after_prefix(prefix, part, byte).repairs.push(place_repair(repair, base, byte)));
}

/// 前の確定済みの出力を足しても、次の回復処理の選択は変わらない。
///
/// 字句の範囲をファイル先頭からの位置に移す。構文木の添字と、根を開いたときの修復数には前の出力の分を足す。
pub(super) proof fn prefix_preserves_recovery_step(prefix: RecoveryState, part: RecoveryState, segment: Segment, byte: int)
    requires
        can_place(prefix, part),
        segment.missing_separator ==> prefix.repairs.len() + part.repairs.len() + 1 < usize::MAX,
    ensures
        apply_recovery_segment(after_prefix(prefix, part, byte), place_segment(segment, byte))
            == after_prefix(prefix, apply_recovery_segment(part, segment), byte),
{
    let base = prefix.forms.len() as int;
    let initial = if segment.missing_separator {
        let inserted = Repair::InsertedSeparator { offset: segment.span.start };
        prefix_preserves_repair(prefix, part, inserted, byte);
        RecoveryState { repairs: part.repairs.push(inserted), ..part }
    } else { part };
    reveal(apply_recovery_segment);
    match segment.kind {
        SegmentKind::Whitespace | SegmentKind::Comment => {},
        SegmentKind::Atom(kind) => {
            let form = Form::Atom { kind, span: segment.span };
            map_push(initial.forms, form, |value: Form| place_form(value, base, byte));
        },
        SegmentKind::Open => {
            let form = Form::List { span: segment.span, end: 0 };
            map_push(initial.forms, form, |value: Form| place_form(value, base, byte));
            map_push(initial.open, initial.forms.len() as usize, |index: usize| (base + index) as usize);
        },
        SegmentKind::Malformed(error) => {
            prefix_preserves_repair(prefix, initial, Repair::Skipped { span: segment.span, error }, byte);
        },
        SegmentKind::Close => {
            if initial.open.len() == 0 {
                let span = segment.span;
                let error = crate::Error { kind: crate::ErrorKind::UnexpectedClose, span };
                prefix_preserves_repair(prefix, initial, Repair::Skipped { span, error }, byte);
            } else {
                prefix_preserves_close(prefix, initial, segment.span.end, byte);
                if let Some((start, count)) = initial.root {
                    assert(after_prefix(prefix, initial, byte).root == Some(((byte + start) as usize, (prefix.repairs.len() + count) as usize)));
                    map_push(initial.original, start..segment.span.end, |span: Range<usize>| place_range(span, byte));
                }
            }
        },
    }
    let plain = apply_recovery_segment(after_prefix(prefix, part, byte), place_segment(segment, byte));
    let carried = after_prefix(prefix, apply_recovery_segment(part, segment), byte);
    assert(plain.forms =~= carried.forms);
    assert(plain.original =~= carried.original);
}

/// 入力末尾で補う閉じ括弧も、同じリストと関連範囲を指す。
pub(super) proof fn prefix_preserves_end_repair(prefix: RecoveryState, part: RecoveryState, eof: usize, byte: int)
    requires can_place(prefix, part), part.open.len() > 0,
    ensures
        close_recovery_at_eof(after_prefix(prefix, part, byte), (byte + eof) as usize)
            == after_prefix(prefix, close_recovery_at_eof(part, eof), byte),
{
    prefix_preserves_close(prefix, part, eof, byte);
    let list = part.open.last();
    let opening = crate::form_span(part.forms[list as int]);
    prefix_preserves_repair(prefix, part, Repair::InsertedClose { offset: eof, opening, list }, byte);
    let full = after_prefix(prefix, part, byte);
    assert(full.open.last() == prefix.forms.len() + list);
    assert(crate::form_span(full.forms[full.open.last() as int]) == place_range(opening, byte));
}

/// 対応する字句列を読み終えた状態は、確定済みの前半に相対位置の結果を接いだ状態と一致する。
pub(super) proof fn project_recovery_frames(
    whole_bytes: Seq<u8>, part_bytes: Seq<u8>, whole: Seq<ReplayFrame>, part: Seq<ReplayFrame>,
    split: int, count: int, byte: int,
)
    requires
        0 <= split <= split + count <= whole.len(),
        0 <= count <= part.len(),
        replay_valid(whole_bytes, whole), replay_valid(part_bytes, part),
        replay_at(whole, split).open.len() == 0,
        replay_at(whole, split).root is None,
        forall|i: int| 0 <= i < count ==> {
            let prefix = replay_at(whole, split);
            let before = replay_at(part, i);
            let segment = (#[trigger] part[i]).segment;
            &&& whole[split + i].segment == place_segment(segment, byte)
            &&& can_place(prefix, before)
            &&& (segment.missing_separator ==> prefix.repairs.len() + before.repairs.len() + 1 < usize::MAX)
        },
    ensures replay_at(whole, split + count) == after_prefix(replay_at(whole, split), replay_at(part, count), byte),
    decreases count,
{
    let prefix = replay_at(whole, split);
    if count == 0 {
        let empty = after_prefix(prefix, initial_recovery(), byte);
        assert(empty.forms =~= prefix.forms);
        assert(empty.open =~= prefix.open);
        assert(empty.repairs =~= prefix.repairs);
        assert(empty.original =~= prefix.original);
    } else {
        let i = count - 1;
        project_recovery_frames(whole_bytes, part_bytes, whole, part, split, i, byte);
        let before = replay_at(part, i);
        let step = part[i];
        assert(whole[split + i].segment == place_segment(step.segment, byte));
        prefix_preserves_recovery_step(prefix, before, step.segment, byte);
        reveal(replay_valid);
        assert(step.after == apply_recovery_segment(before, step.segment));
        assert(whole[split + i].after == apply_recovery_segment(replay_at(whole, split + i), whole[split + i].segment));
    }
}

pub(super) open spec fn eof_can_place(prefix: RecoveryState, part: RecoveryState) -> bool {
    &&& prefix.forms.len() + part.forms.len() < usize::MAX
    &&& prefix.repairs.len() + part.repairs.len() + part.open.len() < usize::MAX
    &&& forall|i: int| 0 <= i < part.open.len() ==> (#[trigger] part.open[i]) < part.forms.len()
    &&& part.root matches Some((_, before)) ==> before <= part.repairs.len()
}

/// 末尾の補完まで行っても、前半の出力と後半の相対位置から元の結果を復元できる。
pub(super) proof fn project_recovery_eof(prefix: RecoveryState, part: RecoveryState, eof: usize, byte: int)
    requires
        0 <= byte && byte + eof <= usize::MAX,
        eof_can_place(prefix, part),
    ensures
        finish_recovery(after_prefix(prefix, part, byte), byte + eof)
            == after_prefix(prefix, finish_recovery(part, eof as int), byte),
    decreases part.open.len(),
{
    reveal(finish_recovery);
    if part.open.len() > 0 {
        let after = close_recovery_at_eof(part, eof);
        prefix_preserves_end_repair(prefix, part, eof, byte);
        assert forall|i: int| 0 <= i < after.open.len() implies (#[trigger] after.open[i]) < after.forms.len() by {
            assert(after.open[i] == part.open[i]);
        };
        project_recovery_eof(prefix, after, eof, byte);
    }
}

/// 共通の接尾部と、未終了のリストを持たない合流点から、末尾補完までの出力の一致を導く。
pub(super) proof fn project_completed_suffix(
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
        replay_at(all, split).open.len() == 0,
        replay_at(all, split).root is None,
        replay_position(all, all.len() as int) == full.len(),
        replay_position(part, part.len() as int) == tail.len(),
        forall|i: int| 0 <= i < part.len() ==> {
            let prefix = replay_at(all, split);
            let before = replay_at(part, i);
            let segment = (#[trigger] part[i]).segment;
            &&& can_place(prefix, before)
            &&& (segment.missing_separator ==> prefix.repairs.len() + before.repairs.len() + 1 < usize::MAX)
        },
        eof_can_place(replay_at(all, split), replay_at(part, part.len() as int)),
    ensures
        finish_recovery(replay_at(all, all.len() as int), full.len() as int)
            == after_prefix(replay_at(all, split),
                finish_recovery(replay_at(part, part.len() as int), tail.len() as int), base),
{
    suffix_segments_align(full, tail, all, part, split, base);
    project_recovery_frames(full, tail, all, part, split, part.len() as int, base);
    project_recovery_eof(replay_at(all, split), replay_at(part, part.len() as int), tail.len() as usize, base);
}

} // verus!
