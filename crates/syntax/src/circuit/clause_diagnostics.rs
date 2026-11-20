//! 節の検査順から、診断の種別と範囲を一意に決める。

use super::clauses::{
    named_clause_error_span, named_clause_matches, natural_clause_error_evidence,
    natural_clause_matches, storage_arguments_match, storage_error_evidence, type_error_evidence, type_matches,
};
use super::{Clause, Form, Head, HeaderError, Range, form_span};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

pub(super) proof fn named_error_spans_agree(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize, clause: Clause,
    left: Range<usize>, right: Range<usize>,
)
    requires
        named_clause_error_span(source, forms, index, limit, closing, clause, left),
        named_clause_error_span(source, forms, index, limit, closing, clause, right),
    ensures left == right,
{
}

pub(super) proof fn named_match_excludes_error(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize, clause: Clause,
    after: int, span: Range<usize>,
)
    requires named_clause_matches(source, forms, index, limit, after, clause),
    ensures !named_clause_error_span(source, forms, index, limit, closing, clause, span),
{
}

/// 自然数の節に対する二つの診断は、先頭語から順に同じ違反を示す。
pub(super) proof fn natural_errors_agree(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize, clause: Clause,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        natural_clause_error_evidence(source, forms, index, limit, closing, clause, left.0, left.1),
        natural_clause_error_evidence(source, forms, index, limit, closing, clause, right.0, right.1),
    ensures left == right,
{
    let after = forms[index]->List_end as int;
    if named_clause_matches(source, forms, index, limit, after, clause) {
        named_match_excludes_error(source, forms, index, limit, closing, clause, after, left.1);
        named_match_excludes_error(source, forms, index, limit, closing, clause, after, right.1);
    } else {
        named_error_spans_agree(source, forms, index, limit, closing, clause, left.1, right.1);
    }
}

/// 自然数の節を受理できるとき、その節の診断は成立しない。
pub(super) proof fn natural_match_excludes_error(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize, clause: Clause,
    after: int, error: (HeaderError, Range<usize>),
)
    requires natural_clause_matches(source, forms, index, limit, after, clause),
    ensures !natural_clause_error_evidence(source, forms, index, limit, closing, clause, error.0, error.1),
{
    named_match_excludes_error(source, forms, index, limit, closing, clause, after, error.1);
}

/// 同じ型指定を受理した場合、その直後の添字は一定である。
pub(super) proof fn type_after_agrees(
    source: &str, forms: Seq<Form>, index: int, limit: int, left: int, right: int,
)
    requires
        type_matches(source, forms, index, limit, left),
        type_matches(source, forms, index, limit, right),
    ensures left == right,
{
}

/// 型指定の診断は種別と範囲が一意に決まる。
pub(super) proof fn type_errors_agree(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        type_error_evidence(source, forms, index, limit, closing, left.0, left.1),
        type_error_evidence(source, forms, index, limit, closing, right.0, right.1),
    ensures left == right,
{
    if index < limit && forms[index] is List {
        natural_errors_agree(source, forms, index, limit, closing, Clause::Bits, left, right);
    }
}

/// 型指定を受理できるとき、その型指定の診断は成立しない。
pub(super) proof fn type_match_excludes_error(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize,
    after: int, error: (HeaderError, Range<usize>),
)
    requires type_matches(source, forms, index, limit, after),
    ensures !type_error_evidence(source, forms, index, limit, closing, error.0, error.1),
{
    if forms[index] is List {
        natural_match_excludes_error(source, forms, index, limit, closing, Clause::Bits, after, error);
    }
}

proof fn natural_clause_error_agrees_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, index: int, limit: int, closing: usize, clause: Clause,
    error: (HeaderError, Range<usize>),
)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures natural_clause_error_evidence(left, forms, index, limit, closing, clause, error.0, error.1)
        == natural_clause_error_evidence(right, forms, index, limit, closing, clause, error.0, error.1),
{
    let after = forms[index]->List_end as int;
    assert forall|end: int| #[trigger] named_clause_matches(left, forms, index, limit, end, clause)
        implies end == after by {};
    assert forall|end: int| #[trigger] named_clause_matches(right, forms, index, limit, end, clause)
        implies end == after by {};
    assert(named_clause_matches(left, forms, index, limit, after, clause)
        == named_clause_matches(right, forms, index, limit, after, clause));
    assert(named_clause_error_span(left, forms, index, limit, closing, clause, error.1)
        == named_clause_error_span(right, forms, index, limit, closing, clause, error.1));
}

proof fn storage_arguments_transfer_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, first: int, limit: int, closing: usize, head: Head,
    error: (HeaderError, Range<usize>),
)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures
        storage_arguments_match(left, forms, first, limit, head) ==> storage_arguments_match(right, forms, first, limit, head),
        storage_error_evidence(left, forms, first, limit, closing, head, error.0, error.1)
            ==> storage_error_evidence(right, forms, first, limit, closing, head, error.0, error.1),
{
    let data = first + 3;
    if head is Latch {
        natural_clause_error_agrees_on_bytes(left, right, forms, first, limit, closing, Clause::Width, error);
        assert forall|after: int| #[trigger] natural_clause_matches(left, forms, first, limit, after, Clause::Width)
            implies after == data by {};
        assert(natural_clause_matches(left, forms, first, limit, data, Clause::Width)
            == natural_clause_matches(right, forms, first, limit, data, Clause::Width));
    } else if head is Memory {
        natural_clause_error_agrees_on_bytes(left, right, forms, first, limit, closing, Clause::Address, error);
        assert forall|after: int| #[trigger] natural_clause_matches(left, forms, first, limit, after, Clause::Address)
            implies after == data by {};
        assert(natural_clause_matches(left, forms, first, limit, data, Clause::Address)
            == natural_clause_matches(right, forms, first, limit, data, Clause::Address));
        let value = data + 2;
        if storage_arguments_match(left, forms, first, limit, head) {
            assert(named_clause_matches(right, forms, data, limit, limit, Clause::Data));
            assert(type_matches(right, forms, value, limit, limit));
        }
        if storage_error_evidence(left, forms, first, limit, closing, head, error.0, error.1)
            && !natural_clause_error_evidence(left, forms, first, limit, closing, Clause::Address, error.0, error.1)
        {
            if error.0 == HeaderError::ExpectedClause(Clause::Data)
                && named_clause_error_span(left, forms, data, limit, closing, Clause::Data, error.1)
            {
                assert(named_clause_error_span(right, forms, data, limit, closing, Clause::Data, error.1));
            } else {
                let data_end = forms[data]->List_end as int;
                assert forall|end: int| #[trigger] named_clause_matches(left, forms, data, limit, end, Clause::Data)
                    implies end == data_end by {};
                assert(named_clause_matches(right, forms, data, limit, data_end, Clause::Data));
                let close = (form_span(forms[data]).end - 1) as usize;
                natural_clause_error_agrees_on_bytes(left, right, forms, value, data_end, close, Clause::Bits, error);
                assert(type_error_evidence(left, forms, value, data_end, close, error.0, error.1)
                    == type_error_evidence(right, forms, value, data_end, close, error.0, error.1));
                if !type_error_evidence(left, forms, value, data_end, close, error.0, error.1) {
                    let after = choose|after: int| #[trigger] type_matches(left, forms, value, data_end, after)
                        && (after < data_end && error.1 == form_span(forms[after])
                            || after == data_end && data_end < limit && error.1 == form_span(forms[data_end]));
                    assert(type_matches(right, forms, value, data_end, after));
                }
            }
        }
    }
}

/// 同じ本文と構文木では、状態素子の引数の妥当性と最初の診断の根拠が一致する。
pub(super) proof fn storage_arguments_agree_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, first: int, limit: int, closing: usize, head: Head,
    error: (HeaderError, Range<usize>),
)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures
        storage_arguments_match(left, forms, first, limit, head) == storage_arguments_match(right, forms, first, limit, head),
        storage_error_evidence(left, forms, first, limit, closing, head, error.0, error.1)
            == storage_error_evidence(right, forms, first, limit, closing, head, error.0, error.1),
{
    storage_arguments_transfer_on_bytes(left, right, forms, first, limit, closing, head, error);
    storage_arguments_transfer_on_bytes(right, left, forms, first, limit, closing, head, error);
}

/// ラッチとメモリでは、幅とデータ型の節を検査する順序から同じ診断が得られる。
pub(super) proof fn storage_errors_agree(
    source: &str, forms: Seq<Form>, first: int, limit: int, closing: usize, head: Head,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        storage_error_evidence(source, forms, first, limit, closing, head, left.0, left.1),
        storage_error_evidence(source, forms, first, limit, closing, head, right.0, right.1),
    ensures left == right,
{
    let after = first + 3;
    if head is Latch {
        if natural_clause_matches(source, forms, first, limit, after, Clause::Width) {
            natural_match_excludes_error(source, forms, first, limit, closing, Clause::Width, after, left);
            natural_match_excludes_error(source, forms, first, limit, closing, Clause::Width, after, right);
        } else {
            natural_errors_agree(source, forms, first, limit, closing, Clause::Width, left, right);
        }
    } else if head is Memory {
        let data = after;
        if !natural_clause_matches(source, forms, first, limit, data, Clause::Address) {
            natural_errors_agree(source, forms, first, limit, closing, Clause::Address, left, right);
        } else {
            natural_match_excludes_error(source, forms, first, limit, closing, Clause::Address, data, left);
            natural_match_excludes_error(source, forms, first, limit, closing, Clause::Address, data, right);
            let data_end = forms[data]->List_end as int;
            if named_clause_matches(source, forms, data, limit, data_end, Clause::Data) {
                named_match_excludes_error(source, forms, data, limit, closing, Clause::Data, data_end, left.1);
                named_match_excludes_error(source, forms, data, limit, closing, Clause::Data, data_end, right.1);
                let value = data + 2;
                let close = (form_span(forms[data]).end - 1) as usize;
                if exists|end: int| #[trigger] type_matches(source, forms, value, data_end, end) {
                    let end = choose|end: int| #[trigger] type_matches(source, forms, value, data_end, end);
                    type_match_excludes_error(source, forms, value, data_end, close, end, left);
                    type_match_excludes_error(source, forms, value, data_end, close, end, right);
                    let a = choose|next: int| #[trigger] type_matches(source, forms, value, data_end, next)
                        && (next < data_end && left.1 == form_span(forms[next])
                            || next == data_end && data_end < limit && left.1 == form_span(forms[data_end]));
                    let b = choose|next: int| #[trigger] type_matches(source, forms, value, data_end, next)
                        && (next < data_end && right.1 == form_span(forms[next])
                            || next == data_end && data_end < limit && right.1 == form_span(forms[data_end]));
                    type_after_agrees(source, forms, value, data_end, a, b);
                } else {
                    type_errors_agree(source, forms, value, data_end, close, left, right);
                }
            } else {
                named_error_spans_agree(source, forms, data, limit, closing, Clause::Data, left.1, right.1);
            }
        }
    }
}

} // verus!
