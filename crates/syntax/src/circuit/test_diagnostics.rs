//! テストの項目列と値列における最初の違反を特定する。

use super::expressions::{argument_error, argument_matches};
use super::test_items::{
    test_arguments_error, test_body_error, test_case_error,
    test_case_matches, test_item_arguments_error, test_item_arguments_match, test_item_error,
    test_item_head_at, test_item_head_error, test_item_matches, test_items_before,
};
use super::test_values::{test_value_error, test_value_matches, test_values_before, test_values_error};
use super::*;

verus! {

proof fn value_errors_agree(
    source: &str, forms: Seq<Form>, index: int, end: int, allow_any: bool,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        test_value_error(source, forms, index, end, allow_any, left),
        test_value_error(source, forms, index, end, allow_any, right),
    ensures left == right,
{
}

proof fn value_match_excludes_error(
    source: &str, forms: Seq<Form>, index: int, end: int, allow_any: bool,
    error: (HeaderError, Range<usize>),
)
    requires test_value_matches(source, forms, index, end, allow_any),
    ensures !test_value_error(source, forms, index, end, allow_any, error),
{
}

proof fn values_match_excludes_error(
    source: &str, forms: Seq<Form>, start: int, end: int, allow_any: bool,
    error: (HeaderError, Range<usize>),
)
    requires test_values_before(source, forms, start, end, end, allow_any),
    ensures !test_values_error(source, forms, start, end, allow_any, error),
{
    if test_values_error(source, forms, start, end, allow_any, error) {
        let index = choose|index: int| #[trigger] direct_form_in_range(forms, start, end, index)
            && test_values_before(source, forms, start, end, index, allow_any)
            && test_value_error(source, forms, index, end, allow_any, error);
        reveal(direct_form_in_range);
        reveal(test_values_before);
        value_match_excludes_error(source, forms, index, end, allow_any, error);
    }
}

proof fn values_errors_agree(
    source: &str, forms: Seq<Form>, start: int, end: int, allow_any: bool,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        test_values_error(source, forms, start, end, allow_any, left),
        test_values_error(source, forms, start, end, allow_any, right),
    ensures left == right,
{
    let a = choose|index: int| #[trigger] direct_form_in_range(forms, start, end, index)
        && test_values_before(source, forms, start, end, index, allow_any)
        && test_value_error(source, forms, index, end, allow_any, left);
    let b = choose|index: int| #[trigger] direct_form_in_range(forms, start, end, index)
        && test_values_before(source, forms, start, end, index, allow_any)
        && test_value_error(source, forms, index, end, allow_any, right);
    reveal(test_values_before);
    // 後の候補の根拠は、それより前にある候補の値が妥当であることを要求する。
    if a < b {
        value_match_excludes_error(source, forms, a, end, allow_any, left);
    } else if b < a {
        value_match_excludes_error(source, forms, b, end, allow_any, right);
    } else {
        value_errors_agree(source, forms, a, end, allow_any, left, right);
    }
}

proof fn case_match_excludes_error(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize,
    error: (HeaderError, Range<usize>),
)
    requires test_case_matches(source, forms, first, end),
    ensures !test_case_error(source, forms, first, end, closing, error),
{
    let expect = choose|expect: int|
        #[trigger] named_clause_matches(source, forms, first, end, expect, Clause::In)
        && test_values_before(source, forms, first + 2, expect, expect, false)
        && named_clause_matches(source, forms, expect, end, end, Clause::Expect)
        && test_values_before(source, forms, expect + 2, end, end, true);
    values_match_excludes_error(source, forms, first + 2, expect, false, error);
    values_match_excludes_error(source, forms, expect + 2, end, true, error);
    if test_case_error(source, forms, first, end, closing, error) {
        assert(!named_clause_error_span(source, forms, first, end, closing, Clause::In, error.1));
        assert(!named_clause_error_span(source, forms, expect, end, closing, Clause::Expect, error.1));
        assert(argument_error(forms, end, end, closing, HeaderError::UnexpectedArgument) is None);
    }
}

proof fn case_errors_agree(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        test_case_error(source, forms, first, end, closing, left),
        test_case_error(source, forms, first, end, closing, right),
    ensures left == right,
{
    let expect = forms[first]->List_end as int;
    if named_clause_matches(source, forms, first, end, expect, Clause::In) {
        if test_values_before(source, forms, first + 2, expect, expect, false) {
            values_match_excludes_error(source, forms, first + 2, expect, false, left);
            values_match_excludes_error(source, forms, first + 2, expect, false, right);
            let after = forms[expect]->List_end as int;
            if named_clause_matches(source, forms, expect, end, after, Clause::Expect) {
                if test_values_before(source, forms, expect + 2, after, after, true) {
                    values_match_excludes_error(source, forms, expect + 2, after, true, left);
                    values_match_excludes_error(source, forms, expect + 2, after, true, right);
                } else {
                    values_errors_agree(source, forms, expect + 2, after, true, left, right);
                }
            }
        } else {
            values_errors_agree(source, forms, first + 2, expect, false, left, right);
        }
    }
}

proof fn item_arguments_match_excludes_error(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, kind: TestHead,
    error: (HeaderError, Range<usize>),
)
    requires test_item_arguments_match(source, forms, first, end, kind),
    ensures !test_item_arguments_error(source, forms, first, end, closing, kind, error),
{
    match kind {
        TestHead::Case => case_match_excludes_error(source, forms, first, end, closing, error),
        TestHead::Drive => values_match_excludes_error(source, forms, first, end, false, error),
        TestHead::Expect => values_match_excludes_error(source, forms, first, end, true, error),
        _ => {},
    }
}

proof fn item_arguments_errors_agree(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, kind: TestHead,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        test_item_arguments_error(source, forms, first, end, closing, kind, left),
        test_item_arguments_error(source, forms, first, end, closing, kind, right),
    ensures left == right,
{
    match kind {
        TestHead::Case => case_errors_agree(source, forms, first, end, closing, left, right),
        TestHead::Drive => values_errors_agree(source, forms, first, end, false, left, right),
        TestHead::Expect => values_errors_agree(source, forms, first, end, true, left, right),
        _ => {},
    }
}

proof fn item_heads_agree(source: &str, forms: Seq<Form>, index: int, end: int, a: TestHead, b: TestHead)
    requires
        test_item_head_at(source, forms, index, end, a),
        test_item_head_at(source, forms, index, end, b),
    ensures a == b,
{
    encode_utf8_decode_utf8(test_head_spelling(a)@);
    encode_utf8_decode_utf8(test_head_spelling(b)@);
    assert(test_head_spelling(a)@ == test_head_spelling(b)@);
}

proof fn item_match_excludes_error(
    source: &str, forms: Seq<Form>, index: int, end: int, first: TestHead,
    first_span: Range<usize>, error: (HeaderError, Range<usize>),
)
    requires test_item_matches(source, forms, index, end, first),
    ensures !test_item_error(source, forms, index, end, first, first_span, error),
{
    let a = choose|kind: TestHead| #[trigger] test_item_head_at(source, forms, index, end, kind)
        && (first is Case) == (kind is Case)
        && test_item_arguments_match(source, forms, index + 2, forms[index]->List_end as int, kind);
    if test_item_error(source, forms, index, end, first, first_span, error) {
        let b = choose|kind: TestHead| #[trigger] test_item_head_at(source, forms, index, end, kind)
            && if (first is Case) != (kind is Case) {
                error == (HeaderError::MixedTestItems { first_head: (first_span.start, first_span.end) },
                    form_span(forms[index + 1]))
            } else {
                let span = form_span(forms[index]);
                span.end > 0 && test_item_arguments_error(source, forms, index + 2,
                    forms[index]->List_end as int, (span.end - 1) as usize, kind, error)
            };
        item_heads_agree(source, forms, index, end, a, b);
        item_arguments_match_excludes_error(source, forms, index + 2, forms[index]->List_end as int,
            (form_span(forms[index]).end - 1) as usize, a, error);
    }
}

proof fn item_errors_agree(
    source: &str, forms: Seq<Form>, index: int, end: int, first: TestHead,
    first_span: Range<usize>, left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        test_item_error(source, forms, index, end, first, first_span, left),
        test_item_error(source, forms, index, end, first, first_span, right),
    ensures left == right,
{
    if exists|head: TestHead| #[trigger] test_item_head_at(source, forms, index, end, head) {
        let a = choose|kind: TestHead| #[trigger] test_item_head_at(source, forms, index, end, kind)
            && if (first is Case) != (kind is Case) {
                left == (HeaderError::MixedTestItems { first_head: (first_span.start, first_span.end) },
                    form_span(forms[index + 1]))
            } else {
                let span = form_span(forms[index]);
                span.end > 0 && test_item_arguments_error(source, forms, index + 2,
                    forms[index]->List_end as int, (span.end - 1) as usize, kind, left)
            };
        let b = choose|kind: TestHead| #[trigger] test_item_head_at(source, forms, index, end, kind)
            && if (first is Case) != (kind is Case) {
                right == (HeaderError::MixedTestItems { first_head: (first_span.start, first_span.end) },
                    form_span(forms[index + 1]))
            } else {
                let span = form_span(forms[index]);
                span.end > 0 && test_item_arguments_error(source, forms, index + 2,
                    forms[index]->List_end as int, (span.end - 1) as usize, kind, right)
            };
        item_heads_agree(source, forms, index, end, a, b);
        if (first is Case) == (a is Case) {
            item_arguments_errors_agree(source, forms, index + 2, forms[index]->List_end as int,
                (form_span(forms[index]).end - 1) as usize, a, left, right);
        }
    }
}

proof fn body_errors_agree(
    source: &str, forms: Seq<Form>, start: int, end: int, closing: usize,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        test_body_error(source, forms, start, end, closing, left),
        test_body_error(source, forms, start, end, closing, right),
    ensures left == right,
{
    if start != end && (exists|first: TestHead| #[trigger] test_item_head_at(source, forms, start, end, first)) {
        let (a, index_a) = choose|first: TestHead, index: int|
            #[trigger] test_item_head_at(source, forms, start, end, first)
            && #[trigger] direct_form_in_range(forms, start, end, index)
            && test_items_before(source, forms, start, end, index, first)
            && test_item_error(source, forms, index, end, first, form_span(forms[start + 1]), left);
        let (b, index_b) = choose|first: TestHead, index: int|
            #[trigger] test_item_head_at(source, forms, start, end, first)
            && #[trigger] direct_form_in_range(forms, start, end, index)
            && test_items_before(source, forms, start, end, index, first)
            && test_item_error(source, forms, index, end, first, form_span(forms[start + 1]), right);
        item_heads_agree(source, forms, start, end, a, b);
        reveal(test_items_before);
        if index_a < index_b {
            item_match_excludes_error(source, forms, index_a, end, a, form_span(forms[start + 1]), left);
        } else if index_b < index_a {
            item_match_excludes_error(source, forms, index_b, end, b, form_span(forms[start + 1]), right);
        } else {
            item_errors_agree(source, forms, index_a, end, a, form_span(forms[start + 1]), left, right);
        }
    }
}

/// 同じテストフォームの診断は、種別、主範囲、関連範囲が一致する。
pub(super) proof fn test_arguments_errors_agree(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        test_arguments_error(source, forms, first, end, closing, left),
        test_arguments_error(source, forms, first, end, closing, right),
    ensures left == right,
{
    if argument_matches(forms, first, end, HeaderError::ExpectedReference) {
        body_errors_agree(source, forms, first + 1, end, closing, left, right);
    }
}

} // verus!
