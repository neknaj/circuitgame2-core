//! テストの入力値と期待値を検査する。

#[cfg(verus_only)]
use super::clauses::enclosing_region_bounds_form;
use super::expressions::check_argument;
#[cfg(verus_only)]
use super::expressions::{argument_error, argument_matches};
use super::*;

verus! {

/// 期待値の位置では単独の `any` も認める。
pub(super) open spec fn test_atom_matches(source: &str, form: Form, allow_any: bool) -> bool {
    match form {
        Form::Atom { kind, span } => {
            &&& span.start < span.end <= source.spec_bytes().len()
            &&& {
                let word = source.spec_bytes()[span.start as int..span.end as int];
                ||| kind is Binary || kind is Hexadecimal
                ||| kind is Natural && (word == "0".spec_bytes() || word == "1".spec_bytes())
                ||| allow_any && kind is Name && word == "any".spec_bytes()
            }
        },
        _ => false,
    }
}

fn read_test_atom(source: &str, forms: &[Form], index: usize, allow_any: bool) -> (accepted: bool)
    requires
        index < forms@.len(),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures accepted == test_atom_matches(source, forms@[index as int], allow_any),
{
    let form = &forms[index];
    let Form::Atom { kind: atom_kind, span: atom_span } = form else {
        return false;
    };
    proof {
        reveal(form_spans_valid);
        encode_utf8_valid_utf8(source@);
        assert(form_span(*form) == *atom_span);
    }
    let word = source_span(source, atom_span.start, atom_span.end);
    let accepted = test_atom(*atom_kind, word, allow_any);
    proof {
        encode_utf8_decode_utf8(word@);
        encode_utf8_decode_utf8("0"@);
        encode_utf8_decode_utf8("1"@);
        encode_utf8_decode_utf8("any"@);
    }
    accepted
}

/// 型付きテスト値の先頭語が無修飾の `as` であることを表す。
pub(super) open spec fn test_as_head(source: &str, forms: Seq<Form>, head: int, end: int) -> bool {
    &&& argument_matches(forms, head, end, HeaderError::ExpectedName)
    &&& {
        let span = form_span(forms[head]);
        &&& span.start < span.end <= source.spec_bytes().len()
        &&& source.spec_bytes()[span.start as int..span.end as int] == "as".spec_bytes()
    }
}

fn read_test_as(
    source: &str, forms: &[Form], head: usize, end: usize, closing: usize, expected: HeaderError,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        head <= end <= forms@.len(),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> test_as_head(source, forms@, head as int, end as int),
        result matches Err((kind, span)) ==> kind == expected
            && directive_argument_error_span(forms@, head as int, end as int, closing, span),
{
    if let Err((_, span)) = check_argument(forms, head, end, closing, HeaderError::ExpectedName) {
        return Err((expected, span));
    }
    let form = &forms[head];
    let span = form_span_exec(form);
    proof {
        reveal(form_spans_valid);
        encode_utf8_valid_utf8(source@);
    }
    let word = source_span(source, span.start, span.end);
    proof {
        encode_utf8_decode_utf8(word@);
        encode_utf8_decode_utf8("as"@);
    }
    if word == "as" { Ok(()) } else { Err((expected, span)) }
}

/// テスト値の位置では裸の値、または参照と値を一つずつ持つ `as` を認める。
pub(super) open spec fn test_value_matches(
    source: &str, forms: Seq<Form>, index: int, limit: int, allow_any: bool,
) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& match forms[index] {
        Form::Atom { .. } => test_atom_matches(source, forms[index], allow_any),
        Form::List { end, .. } => {
            &&& end == index + 4 <= limit
            &&& test_as_head(source, forms, index + 1, end as int)
            &&& argument_matches(forms, index + 2, end as int, HeaderError::ExpectedReference)
            &&& test_atom_matches(source, forms[index + 3], false)
        },
    }
}

/// 単独の `any` を許すかどうかに応じて値の診断種別を定める。
pub(super) open spec fn expected_test_value(allow_any: bool) -> HeaderError {
    if allow_any { HeaderError::ExpectedTestValueOrAny } else { HeaderError::ExpectedTestValue }
}

fn expected_test_value_kind(allow_any: bool) -> (kind: HeaderError)
    ensures kind == expected_test_value(allow_any),
{
    if allow_any { HeaderError::ExpectedTestValueOrAny } else { HeaderError::ExpectedTestValue }
}

/// テスト値を検査したときの最初の違反と診断範囲を表す。
pub(super) open spec fn test_value_error(
    source: &str, forms: Seq<Form>, index: int, limit: int, allow_any: bool,
    error: (HeaderError, Range<usize>),
) -> bool {
    let expected = expected_test_value(allow_any);
    &&& 0 <= index < limit <= forms.len()
    &&& match forms[index] {
        Form::Atom { span, .. } => !test_atom_matches(source, forms[index], allow_any)
            && error == (expected, span),
        Form::List { span, end } => {
            let head = index + 1;
            let value = index + 3;
            let end = end as int;
            let close = (span.end - 1) as usize;
            &&& index < end <= limit && span.end > 0
            &&& if !test_as_head(source, forms, head, end) {
                error.0 == expected && directive_argument_error_span(forms, head, end, close, error.1)
            } else if !argument_matches(forms, head + 1, end, HeaderError::ExpectedReference) {
                argument_error(forms, head + 1, end, close, HeaderError::ExpectedReference) == Some(error)
            } else if value == end || (value < end && !test_atom_matches(source, forms[value], false)) {
                error.0 == HeaderError::ExpectedTestValue
                    && directive_argument_error_span(forms, value, end, close, error.1)
            } else {
                value < end && argument_error(forms, value + 1, end, close, HeaderError::UnexpectedArgument) == Some(error)
            }
        },
    }
}

fn read_typed_test_value(
    source: &str, forms: &[Form], index: usize, _limit: usize, end: usize, closing: usize, allow_any: bool,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        index < end <= _limit <= forms@.len(),
        forms@[index as int] is List,
        forms@[index as int]->List_end == end,
        closing + 1 == form_span(forms@[index as int]).end,
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == b')',
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> test_value_matches(source, forms@, index as int, _limit as int, allow_any),
        result matches Err(error) ==> test_value_error(source, forms@, index as int, _limit as int, allow_any, error),
{
    let expected = expected_test_value_kind(allow_any);
    read_test_as(source, forms, index + 1, end, closing, expected)?;
    check_argument(forms, index + 2, end, closing, HeaderError::ExpectedReference)?;
    let value = index + 3;
    if value == end {
        return Err((HeaderError::ExpectedTestValue, closing..closing));
    }
    if !read_test_atom(source, forms, value, false) {
        return Err((HeaderError::ExpectedTestValue, form_span_exec(&forms[value])));
    }
    check_argument(forms, value + 1, end, closing, HeaderError::UnexpectedArgument)
}

fn read_test_value(
    source: &str, forms: &[Form], index: usize, _limit: usize, allow_any: bool,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        index < _limit <= forms@.len(),
        form_region_ends_at(forms@, index as int, _limit as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> test_value_matches(source, forms@, index as int, _limit as int, allow_any),
        result matches Ok(next) ==> index < next <= _limit
            && following_direct_form(forms@, index as int, next as int),
        result matches Err(error) ==> test_value_error(source, forms@, index as int, _limit as int, allow_any, error),
{
    let form = &forms[index];
    let next = if let Form::List { end: list_end, span: list_span } = form {
        proof {
            enclosing_region_bounds_form(forms@, index as int, index as int, _limit as int);
            reveal(list_source_delimiters);
            assert(list_delimited(source.spec_bytes(), *form, false));
        }
        read_typed_test_value(source, forms, index, _limit, *list_end, list_span.end - 1, allow_any)?;
        *list_end
    } else {
        if !read_test_atom(source, forms, index, allow_any) {
            let expected = expected_test_value_kind(allow_any);
            return Err((expected, form_span_exec(form)));
        }
        index + 1
    };
    proof { node_end_is_following_direct_form(forms@, index as int, next as int); }
    Ok(next)
}

/// 指定位置より前の直接の値がすべて文法に従うことを表す。
#[verifier::opaque]
pub(super) open spec fn test_values_before(
    source: &str, forms: Seq<Form>, start: int, end: int, cursor: int, allow_any: bool,
) -> bool {
    forall|index: int| #[trigger] direct_form_in_range(forms, start, end, index) && index < cursor
        ==> test_value_matches(source, forms, index, end, allow_any)
}

/// 最初に違反した値の診断と、それより前の値の妥当性を表す。
pub(super) open spec fn test_values_error(
    source: &str, forms: Seq<Form>, start: int, end: int, allow_any: bool, error: (HeaderError, Range<usize>),
) -> bool {
    exists|index: int| #[trigger] direct_form_in_range(forms, start, end, index)
        && test_values_before(source, forms, start, end, index, allow_any)
        && test_value_error(source, forms, index, end, allow_any, error)
}

proof fn record_test_value(
    source: &str, forms: Seq<Form>, start: int, index: int, next: int, end: int, allow_any: bool,
)
    requires
        index < next <= end,
        direct_form_in_range(forms, start, end, index),
        following_direct_form(forms, index, next),
        form_region_ends_at(forms, start, end),
        test_values_before(source, forms, start, end, index, allow_any),
        test_value_matches(source, forms, index, end, allow_any),
    ensures
        next < end ==> direct_form_in_range(forms, start, end, next),
        test_values_before(source, forms, start, end, next, allow_any),
{
    reveal(following_direct_form);
    reveal(test_values_before);
    assert forall|value: int| #[trigger] direct_form_in_range(forms, start, end, value) && value < next
        implies test_value_matches(source, forms, value, end, allow_any) by {
        if value > index {
            assert(!direct_form_in_range(forms, start, end, value));
        }
    };
}

/// 入力値列または期待値列を左から順に検査する。空の値列も認める。
///
/// # Errors
///
/// 最初に違反した値の種別と UTF-8 バイト範囲を返す。
pub(super) fn validate_test_values(
    source: &str, forms: &[Form], start: usize, end: usize, allow_any: bool,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        start <= end <= forms@.len(),
        form_region_ends_at(forms@, start as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> test_values_before(source, forms@, start as int, end as int, end as int, allow_any),
        result matches Err(error) ==> test_values_error(source, forms@, start as int, end as int, allow_any, error),
{
    let mut index = start;
    proof {
        reveal(direct_form_in_range);
        reveal(test_values_before);
    }
    while index < end
        invariant
            start <= index <= end <= forms@.len(),
            form_region_ends_at(forms@, start as int, end as int),
            complete_list_indices(forms@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            index < end ==> direct_form_in_range(forms@, start as int, end as int, index as int),
            test_values_before(source, forms@, start as int, end as int, index as int, allow_any),
        decreases end - index,
    {
        assert(form_region_ends_at(forms@, index as int, end as int));
        let next = match read_test_value(source, forms, index, end, allow_any) {
            Ok(next) => next,
            Err(error) => {
                assert(!test_values_before(source, forms@, start as int, end as int, end as int, allow_any)) by {
                    reveal(test_values_before);
                };
                return Err(error);
            }
        };
        proof { record_test_value(source, forms@, start as int, index as int, next as int, end as int, allow_any); }
        index = next;
    }
    Ok(())
}

} // verus!
