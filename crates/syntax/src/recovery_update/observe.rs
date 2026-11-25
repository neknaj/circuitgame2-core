//! 区間内の添字と UTF-8 バイト範囲を編集中の文書の位置に変換する。

use core::ops::Range;
use vstd::prelude::*;

use super::{RecoverySection, ReparsedRecovery};
use crate::Form;
#[cfg(verus_only)]
use crate::{form_span, original_list_has_root, original_list_ranges};
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::{
    encode_utf8_valid_utf8, is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq,
}};

verus! {

/// 編集後の全文に対するフォームの位置。
#[derive(Debug, Eq, PartialEq)]
pub struct RecoveryFormLocation {
    /// 全文の先行順構文木でのフォーム添字。
    pub form: usize,
    /// 現在の本文に対する UTF-8 半開バイト範囲。
    pub span: Range<usize>,
}

impl<'p, 's> ReparsedRecovery<'p, 's> {
    /// いずれかの区間に修復があることを表す。
    pub open spec fn has_repairs_model(&self) -> bool {
        self.section_model(0).recovered.repairs@.len() != 0
            || self.section_model(1).recovered.repairs@.len() != 0
            || self.section_model(2).recovered.repairs@.len() != 0
    }

    /// 字句または S 式を修復した箇所があるかを返す。
    pub fn has_repairs(&self) -> (present: bool)
        ensures present == self.has_repairs_model(),
    {
        let [head, changed, tail] = self.sections();
        !head.recovered.repairs.is_empty() || !changed.recovered.repairs.is_empty()
            || !tail.recovered.repairs.is_empty()
    }

    fn section(&self, section: usize) -> (result: Option<RecoverySection<'_>>)
        ensures
            self.valid(),
            result.is_some() <==> section < 3,
            result matches Some(part) ==> part == self.section_model(section as int),
    {
        let [head, changed, tail] = self.sections();
        match section {
            0 => Some(head),
            1 => Some(changed),
            2 => Some(tail),
            _ => None,
        }
    }

    /// 区間内のフォームの、全文における添字とバイト範囲を返す。
    ///
    /// 区間は接頭部、変更区間、接尾部の順に 0 から数える。添字が範囲外なら `None`。
    pub fn form_location(&self, section: usize, form: usize) -> (location: Option<RecoveryFormLocation>)
        ensures
            location.is_some() <==> section < 3
                && form < self.section_model(section as int).recovered.forms@.len(),
            location matches Some(loc) ==> {
                let part = self.section_model(section as int);
                let span = form_span(part.recovered.forms@[form as int]);
                &&& loc.form as int == part.form_base + form
                &&& loc.span.start as int == part.byte_base + span.start
                &&& loc.span.end as int == part.byte_base + span.end
                &&& located_span(self.source_model(), loc.span)
            },
    {
        let part = self.section(section)?;
        if form >= part.recovered.forms.len() { return None; }
        let span = match &part.recovered.forms[form] {
            Form::List { span, .. } | Form::Atom { span, .. } => span,
        };
        proof {
            let (_, local, _) = self.section_bounds(section as int);
            let local_span = *span;
            assert(crate::form_spans_valid(local, part.recovered.forms@, local.spec_bytes().len() as int));
            reveal(crate::form_spans_valid);
            assert(form_span(part.recovered.forms@[form as int]) == local_span);
            assert(located_span(local, local_span));
            self.place_span(section as int, local_span);
            assert(part.form_base + form <= usize::MAX);
        }
        Some(RecoveryFormLocation {
            form: part.form_base + form,
            span: part.byte_base + span.start..part.byte_base + span.end,
        })
    }

    /// 区間の元リストに対応する、現在の文書のバイト範囲を返す。
    ///
    /// 区間またはリストの添字が範囲外なら `None`。修復で補ったリストは対象に含まれない。
    pub fn original_list_span(&self, section: usize, list: usize) -> (span: Option<Range<usize>>)
        ensures
            span.is_some() <==> section < 3
                && list < self.section_model(section as int).recovered.original_lists@.len(),
            span matches Some(span) ==> {
                let part = self.section_model(section as int);
                let local = part.recovered.original_lists@[list as int];
                &&& span.start as int == part.byte_base + local.start
                &&& span.end as int == part.byte_base + local.end
                &&& located_span(self.source_model(), span)
            },
    {
        let part = self.section(section)?;
        if list >= part.recovered.original_lists.len() { return None; }
        let span = &part.recovered.original_lists[list];
        proof {
            let (_, local, _) = self.section_bounds(section as int);
            reveal(original_list_ranges);
            assert(located_span(local, *span));
            self.place_span(section as int, *span);
        }
        Some(part.byte_base + span.start..part.byte_base + span.end)
    }

    /// 区間の元リストに対応する、全文のフォーム添字とバイト範囲を返す。
    ///
    /// 区間またはリストの添字が範囲外なら `None`。修復で作ったリストは対象に含まれない。
    pub fn original_list_location(&self, section: usize, list: usize) -> (location: Option<RecoveryFormLocation>)
        ensures
            location.is_some() <==> section < 3
                && list < self.section_model(section as int).recovered.original_lists@.len(),
            location matches Some(loc) ==> {
                let part = self.section_model(section as int);
                let span = part.recovered.original_lists@[list as int];
                &&& original_list_form(part, list as int, loc.form as int - part.form_base)
                &&& loc.span.start as int == part.byte_base + span.start
                &&& loc.span.end as int == part.byte_base + span.end
                &&& located_span(self.source_model(), loc.span)
            },
    {
        let part = self.section(section)?;
        if list >= part.recovered.original_lists.len() { return None; }
        let local_start = part.recovered.original_lists[list].start;
        proof { self.original_list_has_local_form(section as int, list as int); }
        let ghost expected = choose|form: int| original_list_form(part, list as int, form);
        proof {
            let (_, local, _) = self.section_bounds(section as int);
            assert(crate::form_spans_valid(local, part.recovered.forms@, local.spec_bytes().len() as int));
            reveal(crate::form_spans_valid);
            let forms = part.recovered.forms@;
            assert(ordered_starts(forms));
        }
        let form = search_form_start(part.recovered.forms.as_slice(), local_start, Ghost(expected));
        assert(form as int == expected);
        self.form_location(section, form)
    }

    /// 元リストの範囲に対応する区間内のルートが存在することを示す。
    pub proof fn original_list_has_local_form(&self, section: int, list: int)
        requires
            self.valid(), 0 <= section < 3,
            0 <= list < self.section_model(section).recovered.original_lists@.len(),
        ensures
            exists|form: int| original_list_form(self.section_model(section), list, form),
    {
        let part = self.section_model(section);
        self.section_bounds(section);
        original_list_has_root(part.recovered.forms@, part.recovered.original_lists@, list);
        let forms = part.recovered.forms@;
        let form = choose|form: int| #[trigger] crate::circuit::direct_form_in_range(forms, 0, forms.len() as int, form)
            && forms[form] is List && form_span(forms[form]) == part.recovered.original_lists@[list]
            && form < forms[form]->List_end <= forms.len();
        reveal(crate::circuit::direct_form_in_range);
        assert(original_list_form(part, list, form));
    }

    /// 指定区間より前の区間にある元リストの総数。
    pub open spec fn original_list_base(&self, section: int) -> int {
        if section == 0 { 0 }
        else if section == 1 { self.section_model(0).recovered.original_lists@.len() as int }
        else {
            self.section_model(0).recovered.original_lists@.len() as int
                + self.section_model(1).recovered.original_lists@.len()
        }
    }

    /// 全文解析との一致から、指定区間の位置と修復有無を導く。
    pub proof fn observations_agree_with_full(&self, whole: &crate::Recovered, section: int)
        requires self.valid(), self.agrees_with(whole), 0 <= section < 3,
        ensures
            self.has_repairs_model() <==> whole.repairs@.len() > 0,
            ({
                let part = self.section_model(section);
                let base = self.original_list_base(section);
                &&& part.form_base + part.recovered.forms@.len() <= whole.forms@.len()
                &&& 0 <= base <= base + part.recovered.original_lists@.len() <= whole.original_lists@.len()
                &&& forall|i: int| 0 <= i < part.recovered.forms@.len() ==> {
                    let span = form_span(part.recovered.forms@[i]);
                    let absolute = form_span(#[trigger] whole.forms@[part.form_base + i]);
                    absolute == ((part.byte_base + span.start) as usize..(part.byte_base + span.end) as usize)
                }
                &&& forall|i: int| 0 <= i < part.recovered.original_lists@.len() ==> {
                    let span = part.recovered.original_lists@[i];
                    let absolute = #[trigger] whole.original_lists@[base + i];
                    absolute == ((part.byte_base + span.start) as usize..(part.byte_base + span.end) as usize)
                }
            }),
    {
        let part = self.section_model(section);
        self.section_bounds(section);
        crate::recovery_replay::observe_recovery_projection(
            whole, self.head, &self.changed, self.tail, self.start, self.join, section,
            part.recovered, part.byte_base as int, part.form_base as int, self.original_list_base(section),
        );
    }

    spec fn section_source(&self, section: int) -> &str {
        let (head, middle, tail) = self._pieces@;
        if section == 0 { head } else if section == 1 { middle } else { tail }
    }

    proof fn section_bounds(&self, section: int) -> (out: (int, &str, int))
        requires self.valid(), 0 <= section < 3,
        ensures
            ({
                let (start, local, end) = out;
                let source = self.source_model();
                let part = self.section_model(section);
                let bytes = source.spec_bytes();
                &&& 0 <= start <= end <= bytes.len()
                &&& part.byte_base == start
                &&& local == self.section_source(section)
                &&& part.form_base as int == if section == 0 { 0 }
                    else if section == 1 { self.head.forms@.len() as int }
                    else { self.head.forms@.len() as int + self.changed.forms@.len() }
                &&& local.spec_bytes() == bytes.subrange(start, end)
                &&& vstd::utf8::valid_utf8(bytes)
                &&& is_char_boundary(bytes, start)
                &&& is_char_boundary(bytes, end)
                &&& super::parsed_from(local, part.recovered)
                &&& part.form_base + part.recovered.forms@.len() <= usize::MAX
            }),
    {
        let (prefix, middle, suffix) = self._pieces@;
        let bytes = self.source.spec_bytes();
        encode_utf8_valid_utf8(self.source@);
        is_char_boundary_start_end_of_seq(bytes);
        assert(self.valid());
        let start = self.start as int;
        let join = self.join as int;
        form_count_bounded(prefix, self.head.forms@);
        form_count_bounded(middle, self.changed.forms@);
        form_count_bounded(suffix, self.tail.forms@);
        if section == 0 {
            (0, prefix, start)
        } else if section == 1 {
            (start, middle, join)
        } else {
            (join, suffix, bytes.len() as int)
        }
    }

    proof fn place_span(&self, section: int, span: Range<usize>)
        requires
            self.valid(), 0 <= section < 3,
            located_span(self.section_source(section), span),
        ensures
            self.section_model(section).byte_base + span.end <= usize::MAX,
            located_span(self.source_model(), shifted_span(self.section_model(section).byte_base, span)),
    {
        let (start, local, end) = self.section_bounds(section);

        lift_boundary(self.source_model(), local, start, end, span.start as int);
        lift_boundary(self.source_model(), local, start, end, span.end as int);
    }
}

/// 空でないバイト範囲が一つの元入力を指すことを表す。
pub open spec fn located_span(source: &str, span: Range<usize>) -> bool {
    &&& span.start < span.end <= source.spec_bytes().len()
    &&& is_char_boundary(source.spec_bytes(), span.start as int)
    &&& is_char_boundary(source.spec_bytes(), span.end as int)
}

/// 回復時に元入力から確定したリストと、区間内のルート添字の対応を表す。
pub open spec fn original_list_form(section: RecoverySection, list: int, form: int) -> bool {
    let forms = section.recovered.forms@;
    &&& 0 <= form < forms.len()
    &&& crate::circuit::direct_form_in_range(forms, 0, forms.len() as int, form)
    &&& forms[form] is List
    &&& form_span(forms[form]) == section.recovered.original_lists@[list]
    &&& form < forms[form]->List_end <= forms.len()
}

spec fn shifted_span(base: usize, span: Range<usize>) -> Range<usize> {
    (base + span.start) as usize..(base + span.end) as usize
}

spec fn ordered_starts(forms: Seq<Form>) -> bool {
    forall|i: int| 0 < i < forms.len() ==> form_span(forms[i - 1]).start < form_span(#[trigger] forms[i]).start
}

proof fn earlier_form_starts_first(forms: Seq<Form>, earlier: int, later: int)
    requires ordered_starts(forms), 0 <= earlier < later < forms.len(),
    ensures form_span(forms[earlier]).start < form_span(forms[later]).start,
    decreases later - earlier,
{
    if earlier + 1 < later {
        earlier_form_starts_first(forms, earlier, later - 1);
    }
    assert(form_span(forms[later - 1]).start < form_span(forms[later]).start);
}

fn search_form_start(forms: &[Form], start: usize, Ghost(expected): Ghost<int>) -> (form: usize)
    requires
        ordered_starts(forms@),
        0 <= expected < forms@.len(),
        form_span(forms@[expected]).start == start,
    ensures form as int == expected,
{
    let mut lo = 0;
    let mut hi = forms.len();
    while lo < hi
        invariant lo <= expected < hi <= forms@.len(), ordered_starts(forms@),
            form_span(forms@[expected]).start == start,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let found = match &forms[mid] {
            Form::List { span, .. } | Form::Atom { span, .. } => span.start,
        };
        assert(found == form_span(forms@[mid as int]).start);
        if found < start {
            proof {
                if expected < mid { earlier_form_starts_first(forms@, expected, mid as int); }
                assert(mid < expected);
            }
            lo = mid + 1;
        } else if found > start {
            proof {
                if mid < expected { earlier_form_starts_first(forms@, mid as int, expected); }
                assert(expected < mid);
            }
            hi = mid;
        } else {
            proof {
                if expected < mid { earlier_form_starts_first(forms@, expected, mid as int); }
                if mid < expected { earlier_form_starts_first(forms@, mid as int, expected); }
            }
            return mid;
        }
    }
    proof { assert(false); }
    lo
}

proof fn form_start_at_least_index(source: &str, forms: Seq<Form>, index: int)
    requires
        crate::form_spans_valid(source, forms, source.spec_bytes().len() as int),
        0 <= index < forms.len(),
    ensures
        index <= form_span(forms[index]).start,
    decreases index,
{
    reveal(crate::form_spans_valid);
    if index > 0 {
        form_start_at_least_index(source, forms, index - 1);
        assert(form_span(forms[index - 1]).start < form_span(forms[index]).start);
    }
}

proof fn form_count_bounded(source: &str, forms: Seq<Form>)
    requires crate::form_spans_valid(source, forms, source.spec_bytes().len() as int),
    ensures forms.len() <= source.spec_bytes().len(),
{
    reveal(crate::form_spans_valid);
    if forms.len() > 0 {
        let last = forms.len() - 1;
        form_start_at_least_index(source, forms, last);
        assert(form_span(forms[last]).start < form_span(forms[last]).end <= source.spec_bytes().len());
    }
}

proof fn lift_boundary(source: &str, local: &str, start: int, end: int, offset: int)
    requires
        0 <= start <= end <= source.spec_bytes().len(),
        local.spec_bytes() == source.spec_bytes().subrange(start, end),
        is_char_boundary(source.spec_bytes(), end),
        is_char_boundary(local.spec_bytes(), offset),
        0 <= offset <= local.spec_bytes().len(),
    ensures is_char_boundary(source.spec_bytes(), start + offset),
{
    encode_utf8_valid_utf8(source@);
    encode_utf8_valid_utf8(local@);
    if offset < local.spec_bytes().len() {
        is_char_boundary_iff_not_is_continuation_byte(local.spec_bytes(), offset);
        is_char_boundary_iff_not_is_continuation_byte(source.spec_bytes(), start + offset);
        assert(local.spec_bytes()[offset] == source.spec_bytes()[start + offset]);
    }
}

} // verus!
