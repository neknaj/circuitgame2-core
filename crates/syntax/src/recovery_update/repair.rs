//! 区間相対の修復記録を、現在の文書の位置とフォーム添字に変換する。

use core::ops::Range;
use vstd::prelude::*;

use super::ReparsedRecovery;
use crate::{Error, ErrorKind, Repair};
#[cfg(verus_only)]
use crate::{
    Recovered, atom_and_close_error_evidence, bare_atom_extent, form_span, form_spans_valid, inserted_closes_match,
    repair_input_spans_valid, syntax_error_evidence,
};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use crate::recovery_replay::{observe_tail_repairs, placement::{place_error, place_range, place_repair}};

verus! {

impl<'p, 's> ReparsedRecovery<'p, 's> {
    /// 現在の本文にある修復記録の件数。
    pub closed spec fn repair_count_model(&self) -> nat { self.tail.repairs@.len() }

    /// 現在の本文にある修復記録の件数を返す。
    pub fn repair_count(&self) -> (count: usize)
        ensures count == self.repair_count_model(),
    {
        self.tail.repairs.len()
    }

    /// 指定した修復記録を全文の位置に変換した結果を表す。
    pub closed spec fn repair_at_model(&self, index: int) -> Option<Repair> {
        let tail = self.section_model(2);
        if 0 <= index < tail.recovered.repairs@.len() {
            let repair = tail.recovered.repairs@[index];
            if repair_fits(repair, tail.form_base, tail.byte_base) {
                Some(place_repair(repair, tail.form_base as int, tail.byte_base as int))
            } else {
                None
            }
        } else {
            None
        }
    }

    /// 指定した修復記録の主範囲、関連位置、フォーム添字を現在の文書に揃えて返す。
    ///
    /// 添字が範囲外か、位置の加算が `usize` の上限を越える場合は `None` を返す。
    pub fn repair_at(&self, index: usize) -> (repair: Option<Repair>)
        ensures repair == self.repair_at_model(index as int),
    {
        let [_, _, tail] = self.sections();
        if index >= tail.recovered.repairs.len() {
            return None;
        }
        shift_repair(&tail.recovered.repairs[index], tail.form_base, tail.byte_base)
    }

    /// 修復記録の件数と取得した値が、同じ本文の全文回復解析と一致することを示す。
    pub proof fn repairs_agree_with_full(&self, whole: &Recovered)
        requires self.valid(), self.agrees_with(whole),
        ensures
            self.repair_count_model() == whole.repairs@.len(),
            forall|i: int| 0 <= i < self.repair_count_model()
                ==> #[trigger] self.repair_at_model(i) == Some(whole.repairs@[i]),
    {
        let (prefix, middle, suffix) = self._pieces@;
        super::clean_prefix_form_count(prefix, self.head, self.start);
        super::clean_prefix_form_count(middle, &self.changed, (self.join - self.start) as usize);
        observe_tail_repairs(whole, self.head, &self.changed, self.tail, self.start, self.join);
        let part = self.section_model(2);
        let before = self.head.forms@.len() + self.changed.forms@.len();
        assert(part.form_base == before && part.byte_base == self.join);
        reveal(ReparsedRecovery::valid);
        super::observe::form_count_bounded(suffix, self.tail.forms@);
        let length = suffix.spec_bytes().len();
        assert(length + self.join == self.source.spec_bytes().len());
        assert(before + self.tail.forms@.len() <= usize::MAX);
        assert forall|i: int| 0 <= i < self.repair_count_model() implies
            #[trigger] self.repair_at_model(i) == Some(whole.repairs@[i]) by {
            let row = self.tail.repairs@[i];
            assert(repair_in_region(row, length, self.tail.forms@.len()));
            assert(repair_fits(row, part.form_base, part.byte_base));
            assert(whole.repairs@[i] == place_repair(row, before as int, self.join as int));
        };
    }
}

// 旧本文と新本文で共通の区間に移せるように、修復の各位置を区間長で抑える。
pub(super) closed spec fn repairs_within(parsed: &Recovered, length: nat) -> bool {
    forall|i: int| 0 <= i < parsed.repairs@.len() ==>
        repair_in_region(#[trigger] parsed.repairs@[i], length, parsed.forms@.len())
}

spec fn repair_in_region(repair: Repair, length: nat, count: nat) -> bool {
    match repair {
        Repair::Skipped { span, error } => span.start <= span.end <= length
            && error.span.start <= error.span.end <= length
            && match error.kind {
                ErrorKind::InvalidEscape { opening } | ErrorKind::NewlineInString { opening } => opening < length,
                ErrorKind::UnclosedList { eof } => eof == length,
                _ => true,
            },
        Repair::InsertedSeparator { offset } => offset <= length,
        Repair::InsertedClose { offset, opening, list } => offset == length
            && opening.start <= opening.end <= length && list < count,
    }
}

pub(super) proof fn repaired_records_within(source: &str, parsed: &Recovered)
    requires
        repair_input_spans_valid(source, parsed.repairs@, source.spec_bytes().len() as int),
        inserted_closes_match(source, parsed.forms@, parsed.repairs@),
        form_spans_valid(source, parsed.forms@, source.spec_bytes().len() as int),
    ensures repairs_within(parsed, source.spec_bytes().len()),
{
    let length = source.spec_bytes().len();
    reveal(repair_input_spans_valid);
    reveal(inserted_closes_match);
    assert forall|i: int| 0 <= i < parsed.repairs@.len() implies
        repair_in_region(#[trigger] parsed.repairs@[i], length, parsed.forms@.len()) by {
        match parsed.repairs@[i] {
            Repair::Skipped { span, error } => {
                assert(span.start < span.end <= length);
                assert(syntax_error_evidence(source, error));
                reveal(syntax_error_evidence);
                reveal(atom_and_close_error_evidence);
                reveal(bare_atom_extent);
                let opening = crate::string_error_opening(error.kind, error.span);
                if let Some(opening) = opening {
                    let bytes = source.spec_bytes()[opening as int..];
                    assert(bytes.len() == length - opening);
                    assert(crate::string_error_site(bytes, opening as int, error));
                }
                assert(error.span.start <= error.span.end <= length);
            },
            Repair::InsertedSeparator { offset } => assert(offset <= length),
            Repair::InsertedClose { offset, opening, list } => {
                reveal(form_spans_valid);
                let span = form_span(parsed.forms@[list as int]);
                assert(span.start < span.end <= length);
                assert(opening.end == span.start + 1 <= length);
            },
        }
    };
}

spec fn range_fits(span: Range<usize>, byte: usize) -> bool {
    byte + span.start <= usize::MAX && byte + span.end <= usize::MAX
}

spec fn error_fits(error: Error, byte: usize) -> bool {
    &&& range_fits(error.span, byte)
    &&& match error.kind {
        ErrorKind::InvalidEscape { opening } | ErrorKind::NewlineInString { opening } =>
            byte + opening <= usize::MAX,
        ErrorKind::UnclosedList { eof } => byte + eof <= usize::MAX,
        _ => true,
    }
}

spec fn repair_fits(repair: Repair, form: usize, byte: usize) -> bool {
    match repair {
        Repair::Skipped { span, error } => range_fits(span, byte) && error_fits(error, byte),
        Repair::InsertedSeparator { offset } => byte + offset <= usize::MAX,
        Repair::InsertedClose { offset, opening, list } =>
            byte + offset <= usize::MAX && range_fits(opening, byte) && form + list <= usize::MAX,
    }
}

fn shift_range(span: &Range<usize>, byte: usize) -> (result: Option<Range<usize>>)
    ensures
        result.is_some() == range_fits(*span, byte),
        result matches Some(shifted) ==> shifted == place_range(*span, byte as int),
{
    Some(span.start.checked_add(byte)?..span.end.checked_add(byte)?)
}

fn shift_error(error: &Error, byte: usize) -> (result: Option<Error>)
    ensures
        result.is_some() == error_fits(*error, byte),
        result matches Some(shifted) ==> shifted == place_error(*error, byte as int),
{
    let span = shift_range(&error.span, byte)?;
    let kind = match error.kind {
        ErrorKind::InvalidEscape { opening } => ErrorKind::InvalidEscape { opening: opening.checked_add(byte)? },
        ErrorKind::NewlineInString { opening } => ErrorKind::NewlineInString { opening: opening.checked_add(byte)? },
        ErrorKind::UnclosedList { eof } => ErrorKind::UnclosedList { eof: eof.checked_add(byte)? },
        other => other,
    };
    Some(Error { kind, span })
}

fn shift_repair(repair: &Repair, form: usize, byte: usize) -> (result: Option<Repair>)
    ensures
        result.is_some() == repair_fits(*repair, form, byte),
        result matches Some(shifted) ==> shifted == place_repair(*repair, form as int, byte as int),
{
    Some(match repair {
        Repair::Skipped { span, error } => Repair::Skipped {
            span: shift_range(span, byte)?,
            error: shift_error(error, byte)?,
        },
        Repair::InsertedSeparator { offset } => Repair::InsertedSeparator {
            offset: offset.checked_add(byte)?,
        },
        Repair::InsertedClose { offset, opening, list } => Repair::InsertedClose {
            offset: offset.checked_add(byte)?,
            opening: shift_range(opening, byte)?,
            list: list.checked_add(form)?,
        },
    })
}

} // verus!
