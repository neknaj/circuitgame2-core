//! テスト項目の先頭語に応じて引数を検査する。

#[cfg(verus_only)]
use super::clauses::enclosing_region_bounds_form;
use super::clauses::read_named_clause;
use super::expressions::check_argument;
#[cfg(verus_only)]
use super::expressions::{argument_error, argument_matches};
use super::test_values::validate_test_values;
#[cfg(verus_only)]
use super::test_values::{test_values_before, test_values_error};
use super::*;

verus! {

/// `case` は入力節と期待節を一つずつ、この順に持つ。
pub(super) open spec fn test_case_matches(
    source: &str, forms: Seq<Form>, first: int, end: int,
) -> bool {
    exists|expected: int|
        #[trigger] named_clause_matches(source, forms, first, end, expected, Clause::In)
        && test_values_before(source, forms, first + 2, expected, expected, false)
        && named_clause_matches(source, forms, expected, end, end, Clause::Expect)
        && test_values_before(source, forms, expected + 2, end, end, true)
}

/// `case` の節名、値列、余剰引数を実行時の検査順で照合する。
pub(super) open spec fn test_case_error(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize,
    error: (HeaderError, Range<usize>),
) -> bool {
    (error.0 == HeaderError::ExpectedClause(Clause::In)
        && named_clause_error_span(source, forms, first, end, closing, Clause::In, error.1))
    || (exists|expected: int|
        #[trigger] named_clause_matches(source, forms, first, end, expected, Clause::In)
        && (test_values_error(source, forms, first + 2, expected, false, error)
            || (test_values_before(source, forms, first + 2, expected, expected, false)
                && ((error.0 == HeaderError::ExpectedClause(Clause::Expect)
                    && named_clause_error_span(source, forms, expected, end, closing, Clause::Expect, error.1))
                || (exists|after: int|
                    #[trigger] named_clause_matches(source, forms, expected, end, after, Clause::Expect)
                    && (test_values_error(source, forms, expected + 2, after, true, error)
                        || (test_values_before(source, forms, expected + 2, after, after, true)
                            && argument_error(forms, after, end, closing, HeaderError::UnexpectedArgument) == Some(error))))))))
}

fn validate_test_case(
    source: &str, forms: &[Form], first: usize, end: usize, closing: usize,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        first <= end <= forms@.len(),
        form_region_ends_at(forms@, first as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == b')',
    ensures
        result.is_ok() <==> test_case_matches(source, forms@, first as int, end as int),
        result matches Err(error) ==> test_case_error(source, forms@, first as int, end as int, closing, error),
{
    proof { enclosing_region_bounds_form(forms@, first as int, first as int, end as int); }
    let (expected, _) = read_named_clause(source, forms, first, end, closing, Clause::In)?;
    assert(named_clause_matches(source, forms@, first as int, end as int, expected as int, Clause::In));
    assert(form_region_ends_at(forms@, first + 2, expected as int));
    validate_test_values(source, forms, first + 2, expected, false)?;
    proof { enclosing_region_bounds_form(forms@, first as int, expected as int, end as int); }
    let (after, _) = read_named_clause(source, forms, expected, end, closing, Clause::Expect)?;
    assert(named_clause_matches(source, forms@, expected as int, end as int, after as int, Clause::Expect));
    assert(form_region_ends_at(forms@, expected + 2, after as int));
    validate_test_values(source, forms, expected + 2, after, true)?;
    check_argument(forms, after, end, closing, HeaderError::UnexpectedArgument)
}

/// 各テスト項目が要求する引数の並びを表す。
pub(super) open spec fn test_item_arguments_match(
    source: &str, forms: Seq<Form>, first: int, end: int, head: TestHead,
) -> bool {
    match head {
        TestHead::Case => test_case_matches(source, forms, first, end),
        TestHead::Reset => first == end,
        TestHead::Drive => test_values_before(source, forms, first, end, end, false),
        TestHead::Tick => first + 1 == end && natural_argument_at(forms, first, end),
        TestHead::Expect => test_values_before(source, forms, first, end, end, true),
    }
}

/// 各テスト項目の引数を検査したときの最初の違反を表す。
pub(super) open spec fn test_item_arguments_error(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, head: TestHead,
    error: (HeaderError, Range<usize>),
) -> bool {
    match head {
        TestHead::Case => test_case_error(source, forms, first, end, closing, error),
        TestHead::Reset => argument_error(forms, first, end, closing, HeaderError::UnexpectedArgument) == Some(error),
        TestHead::Drive => test_values_error(source, forms, first, end, false, error),
        TestHead::Tick => {
            if natural_argument_at(forms, first, end) {
                argument_error(forms, first + 1, end, closing, HeaderError::UnexpectedArgument) == Some(error)
            } else {
                argument_error(forms, first, end, closing, HeaderError::ExpectedNatural) == Some(error)
            }
        },
        TestHead::Expect => test_values_error(source, forms, first, end, true, error),
    }
}

/// テスト項目の引数を、項目の種類が定める順序で検査する。
///
/// # Errors
///
/// 最初に違反した引数または節の種別と UTF-8 バイト範囲を返す。
fn validate_test_item_arguments(
    source: &str, forms: &[Form], first: usize, end: usize, closing: usize, head: TestHead,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        first <= end <= forms@.len(),
        form_region_ends_at(forms@, first as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == b')',
    ensures
        result.is_ok() <==> test_item_arguments_match(source, forms@, first as int, end as int, head),
        result matches Err(error) ==> test_item_arguments_error(
            source, forms@, first as int, end as int, closing, head, error,
        ),
{
    match head {
        TestHead::Case => validate_test_case(source, forms, first, end, closing),
        TestHead::Reset => check_argument(forms, first, end, closing, HeaderError::UnexpectedArgument),
        TestHead::Drive => validate_test_values(source, forms, first, end, false),
        TestHead::Tick => {
            check_argument(forms, first, end, closing, HeaderError::ExpectedNatural)?;
            check_argument(forms, first + 1, end, closing, HeaderError::UnexpectedArgument)
        },
        TestHead::Expect => validate_test_values(source, forms, first, end, true),
    }
}

#[derive(Clone, Copy)]
struct TestItemHead {
    kind: TestHead,
    end: usize,
    closing: usize,
    word_start: usize,
    word_end: usize,
}

/// 項目がリストで始まり、その先頭語が指定したテスト項目の綴りに一致することを表す。
pub(super) open spec fn test_item_head_at(
    source: &str, forms: Seq<Form>, index: int, limit: int, head: TestHead,
) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& forms[index] is List
    &&& {
        let end = forms[index]->List_end as int;
        &&& index + 1 < end <= limit
        &&& argument_matches(forms, index + 1, end, HeaderError::ExpectedName)
        &&& {
            let span = form_span(forms[index + 1]);
            &&& span.start < span.end <= source.spec_bytes().len()
            &&& test_head_spelling(head).spec_bytes() == source.spec_bytes()[span.start as int..span.end as int]
        }
    }
}

/// 項目のリストまたは先頭語が構文に合わない場合に指す範囲を表す。
pub(super) open spec fn test_item_head_error(
    source: &str, forms: Seq<Form>, index: int, limit: int, error: (HeaderError, Range<usize>),
) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& !(exists|head: TestHead| #[trigger] test_item_head_at(source, forms, index, limit, head))
    &&& error.0 == HeaderError::ExpectedTestItem
    &&& match forms[index] {
        Form::Atom { span, .. } => error.1 == span,
        Form::List { span, end } => {
            &&& span.end > 0
            &&& directive_argument_error_span(forms, index + 1, end as int, (span.end - 1) as usize, error.1)
        },
    }
}

fn read_test_item_head(
    source: &str, forms: &[Form], index: usize, _limit: usize,
) -> (result: Result<TestItemHead, (HeaderError, Range<usize>)>)
    requires
        index < _limit <= forms@.len(),
        form_region_ends_at(forms@, index as int, _limit as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        forall|head: TestHead| #[trigger] test_item_head_at(source, forms@, index as int, _limit as int, head)
            <==> (result matches Ok(item) && item.kind == head),
        match result {
            Ok(item) => {
                &&& index + 1 < item.end <= _limit
                &&& forms@[index as int] is List
                &&& forms@[index as int]->List_end == item.end
                &&& item.closing + 1 == form_span(forms@[index as int]).end
                &&& item.closing < source.spec_bytes().len() && source.spec_bytes()[item.closing as int] == b')'
                &&& form_span(forms@[index + 1]) == (item.word_start..item.word_end)
                &&& following_direct_form(forms@, index as int, item.end as int)
            },
            Err(error) => test_item_head_error(source, forms@, index as int, _limit as int, error),
        },
{
    let expected = HeaderError::ExpectedTestItem;
    let form = &forms[index];
    let Form::List { span: list_span, end: list_end } = form else {
        return Err((expected, form_span_exec(form)));
    };
    proof {
        enclosing_region_bounds_form(forms@, index as int, index as int, _limit as int);
        reveal(list_source_delimiters);
        assert(list_delimited(source.spec_bytes(), *form, false));
    }
    let end = *list_end;
    let closing = list_span.end - 1;
    let head_index = index + 1;
    if let Err((_, span)) = check_argument(forms, head_index, end, closing, HeaderError::ExpectedName) {
        return Err((expected, span));
    }
    let head_form = &forms[head_index];
    let span = form_span_exec(head_form);
    proof {
        reveal(form_spans_valid);
        encode_utf8_valid_utf8(source@);
    }
    let word = source_span(source, span.start, span.end);
    let head = recognize_test_head(word);
    assert forall|kind: TestHead| #[trigger] test_item_head_at(source, forms@, index as int, _limit as int, kind)
        <==> head == Some(kind) by {
        let spelling = test_head_spelling(kind);
        encode_utf8_decode_utf8(word@);
        encode_utf8_decode_utf8(spelling@);
    };
    let Some(kind) = head else {
        return Err((expected, span));
    };
    proof { node_end_is_following_direct_form(forms@, index as int, end as int); }
    Ok(TestItemHead { kind, end, closing, word_start: span.start, word_end: span.end })
}

/// 先頭項目と同じ種類の列に属し、引数も文法に従う項目を表す。
pub(super) open spec fn test_item_matches(
    source: &str, forms: Seq<Form>, index: int, limit: int, first: TestHead,
) -> bool {
    exists|kind: TestHead| #[trigger] test_item_head_at(source, forms, index, limit, kind)
        && (first is Case) == (kind is Case)
        && test_item_arguments_match(source, forms, index + 2, forms[index]->List_end as int, kind)
}

/// 先頭語の違反、項目の混在、引数の違反の順で診断を定める。
pub(super) open spec fn test_item_error(
    source: &str, forms: Seq<Form>, index: int, limit: int, first: TestHead,
    first_span: Range<usize>, error: (HeaderError, Range<usize>),
) -> bool {
    test_item_head_error(source, forms, index, limit, error)
    || (exists|kind: TestHead| #[trigger] test_item_head_at(source, forms, index, limit, kind)
        && if (first is Case) != (kind is Case) {
            error == (HeaderError::MixedTestItems { first_head: (first_span.start, first_span.end) },
                form_span(forms[index + 1]))
        } else {
            let span = form_span(forms[index]);
            span.end > 0 && test_item_arguments_error(source, forms, index + 2,
                forms[index]->List_end as int, (span.end - 1) as usize, kind, error)
        })
}

/// 指定位置より前にある直接の項目が、すべて同じ種類の列に属し文法に従うことを表す。
#[verifier::opaque]
pub(super) open spec fn test_items_before(
    source: &str, forms: Seq<Form>, start: int, end: int, cursor: int, first: TestHead,
) -> bool {
    forall|item: int| #[trigger] direct_form_in_range(forms, start, end, item) && item < cursor
        ==> test_item_matches(source, forms, item, end, first)
}

/// 本体が空でなく、すべての項目がケース列または操作列を成すことを表す。
pub(super) open spec fn test_body_matches(
    source: &str, forms: Seq<Form>, start: int, end: int,
) -> bool {
    exists|first: TestHead| #[trigger] test_item_head_at(source, forms, start, end, first)
        && test_items_before(source, forms, start, end, end, first)
}

/// 本体の欠落、または最初に違反した直接の項目の診断を表す。
///
/// 混在を報告するときの関連範囲は、本体の先頭項目の先頭語を指す。
pub(super) open spec fn test_body_error(
    source: &str, forms: Seq<Form>, start: int, end: int, closing: usize,
    error: (HeaderError, Range<usize>),
) -> bool {
    if start == end {
        error == (HeaderError::ExpectedTestItem, closing..closing)
    } else {
        test_item_head_error(source, forms, start, end, error)
        || (exists|first: TestHead, index: int|
            #[trigger] test_item_head_at(source, forms, start, end, first)
            && #[trigger] direct_form_in_range(forms, start, end, index)
            && test_items_before(source, forms, start, end, index, first)
            && test_item_error(source, forms, index, end, first, form_span(forms[start + 1]), error))
    }
}

proof fn record_test_item(
    source: &str, forms: Seq<Form>, start: int, index: int, next: int, end: int, first: TestHead,
)
    requires
        index < next <= end,
        direct_form_in_range(forms, start, end, index),
        following_direct_form(forms, index, next),
        form_region_ends_at(forms, start, end),
        test_items_before(source, forms, start, end, index, first),
        test_item_matches(source, forms, index, end, first),
    ensures
        next < end ==> direct_form_in_range(forms, start, end, next),
        test_items_before(source, forms, start, end, next, first),
{
    reveal(following_direct_form);
    reveal(test_items_before);
    assert forall|item: int| #[trigger] direct_form_in_range(forms, start, end, item) && item < next
        implies test_item_matches(source, forms, item, end, first) by {
        if item > index {
            assert(!direct_form_in_range(forms, start, end, item));
        }
    };
}

proof fn reject_test_item(
    source: &str, forms: Seq<Form>, start: int, index: int, end: int, closing: usize, first: TestHead,
    error: (HeaderError, Range<usize>),
)
    requires
        0 <= start && start + 1 < end <= forms.len(),
        forall|kind: TestHead| #[trigger] test_item_head_at(source, forms, start, end, kind) <==> kind == first,
        direct_form_in_range(forms, start, end, index),
        test_items_before(source, forms, start, end, index, first),
        !test_item_matches(source, forms, index, end, first),
        test_item_error(source, forms, index, end, first, form_span(forms[start + 1]), error),
    ensures
        !test_body_matches(source, forms, start, end),
        test_body_error(source, forms, start, end, closing, error),
{
    reveal(direct_form_in_range);
    reveal(test_items_before);
    assert(test_item_head_at(source, forms, start, end, first));
    assert(!test_items_before(source, forms, start, end, end, first));
}

/// テスト本体の各項目を入力順に検査する。
///
/// # Errors
///
/// 最初の違反を返す。ケース列と操作列が混在する場合は、列の種類を変える項目と本体の先頭項目を指す。
fn validate_test_body(
    source: &str, forms: &[Form], start: usize, end: usize, closing: usize,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        start <= end <= forms@.len(),
        form_region_ends_at(forms@, start as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == b')',
    ensures
        result.is_ok() <==> test_body_matches(source, forms@, start as int, end as int),
        result matches Err(error) ==> test_body_error(source, forms@, start as int, end as int, closing, error),
{
    if start == end {
        return Err((HeaderError::ExpectedTestItem, closing..closing));
    }
    let first = read_test_item_head(source, forms, start, end)?;
    let mut index = start;
    proof {
        reveal(direct_form_in_range);
        reveal(test_items_before);
    }
    while index < end
        invariant
            start <= index <= end <= forms@.len(),
            form_region_ends_at(forms@, start as int, end as int),
            complete_list_indices(forms@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            forall|kind: TestHead| #[trigger] test_item_head_at(source, forms@, start as int, end as int, kind)
                <==> kind == first.kind,
            first.end <= end && start + 1 < first.end,
            forms@[start as int] is List && forms@[start as int]->List_end == first.end,
            first.closing < source.spec_bytes().len() && source.spec_bytes()[first.closing as int] == b')',
            first.closing + 1 == form_span(forms@[start as int]).end,
            form_span(forms@[start + 1]) == (first.word_start..first.word_end),
            following_direct_form(forms@, start as int, first.end as int),
            index < end ==> direct_form_in_range(forms@, start as int, end as int, index as int),
            test_items_before(source, forms@, start as int, end as int, index as int, first.kind),
        decreases end - index,
    {
        assert(form_region_ends_at(forms@, index as int, end as int));
        let item = if index == start {
            first
        } else {
            match read_test_item_head(source, forms, index, end) {
                Ok(item) => item,
                Err(error) => {
                    proof { reject_test_item(source, forms@, start as int, index as int,
                        end as int, closing, first.kind, error); }
                    return Err(error);
                }
            }
        };
        assert forall|kind: TestHead| #[trigger] test_item_head_at(source, forms@, index as int, end as int, kind)
            <==> kind == item.kind by {
        };
        assert(test_item_head_at(source, forms@, index as int, end as int, item.kind));
        assert(forms@[index as int]->List_end == item.end);
        assert(item.closing + 1 == form_span(forms@[index as int]).end);
        assert(form_span(forms@[index + 1]) == (item.word_start..item.word_end));
        // 混在は項目の引数を調べる前に検出し、先頭項目との違いを示す。
        if !same_test_item_kind(first.kind, item.kind) {
            let error = (HeaderError::MixedTestItems { first_head: (first.word_start, first.word_end) },
                item.word_start..item.word_end);
            proof { reject_test_item(source, forms@, start as int, index as int,
                end as int, closing, first.kind, error); }
            return Err(error);
        }
        let argument = index + 2;
        assert(form_region_ends_at(forms@, argument as int, item.end as int));
        if let Err(error) = validate_test_item_arguments(source, forms, argument, item.end, item.closing, item.kind) {
            proof { reject_test_item(source, forms@, start as int, index as int,
                end as int, closing, first.kind, error); }
            return Err(error);
        }
        proof { record_test_item(source, forms@, start as int, index as int, item.end as int,
            end as int, first.kind); }
        index = item.end;
    }
    assert(test_item_head_at(source, forms@, start as int, end as int, first.kind));
    Ok(())
}

/// テスト対象の参照の後に、文法に従うテスト本体が続くことを表す。
pub(super) open spec fn test_arguments_match(source: &str, forms: Seq<Form>, first: int, end: int) -> bool {
    argument_matches(forms, first, end, HeaderError::ExpectedReference)
        && test_body_matches(source, forms, first + 1, end)
}

/// 参照を先に検査し、その後にテスト本体の最初の診断を採用する。
pub(super) open spec fn test_arguments_error(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize,
    error: (HeaderError, Range<usize>),
) -> bool {
    if argument_matches(forms, first, end, HeaderError::ExpectedReference) {
        test_body_error(source, forms, first + 1, end, closing, error)
    } else {
        argument_error(forms, first, end, closing, HeaderError::ExpectedReference) == Some(error)
    }
}

/// テスト対象の参照と、テスト本体の項目列を検査する。
///
/// # Errors
///
/// 最初に違反した箇所の診断と範囲を返す。本文の項目が混在する場合は、関連範囲も返す。
pub(super) fn validate_test_arguments(
    source: &str, forms: &[Form], first: usize, end: usize, closing: usize,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        first <= end <= forms@.len(),
        form_region_ends_at(forms@, first as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == b')',
    ensures
        result.is_ok() <==> test_arguments_match(source, forms@, first as int, end as int),
        result matches Err(error) ==> test_arguments_error(source, forms@, first as int, end as int, closing, error),
{
    check_argument(forms, first, end, closing, HeaderError::ExpectedReference)?;
    assert(form_region_ends_at(forms@, first + 1, end as int));
    validate_test_body(source, forms, first + 1, end, closing)
}

} // verus!
