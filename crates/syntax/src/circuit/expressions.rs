//! リスト形式の式について、引数の配置と子式の範囲を検査する。

#[cfg(verus_only)]
use super::clauses::enclosing_region_bounds_form;
use super::*;

verus! {

/// フォームの直後を指す添字を表す。子式がリストなら部分木の末尾を使う。
pub(super) open spec fn after_form(forms: Seq<Form>, index: int) -> int {
    if 0 <= index < forms.len() && forms[index] is List {
        forms[index]->List_end as int
    } else {
        index + 1
    }
}

/// 引数の字句種別、子式の存在、または引数列の終端を判定する。
pub(super) open spec fn argument_matches(forms: Seq<Form>, index: int, end: int, expected: HeaderError) -> bool {
    if expected is UnexpectedArgument {
        index == end
    } else {
        &&& 0 <= index < end <= forms.len()
        &&& match expected {
            HeaderError::ExpectedReference => forms[index] is Atom
                && reference_atom(forms[index]->Atom_kind),
            HeaderError::ExpectedName => forms[index] is Atom
                && forms[index]->Atom_kind is Name,
            HeaderError::ExpectedNatural => natural_argument_at(forms, index, end),
            HeaderError::ExpectedExpression => true,
            _ => false,
        }
    }
}

/// 引数の種別違反、欠落、余剰に対応する診断の種別と範囲を定める。
pub(super) open spec fn argument_error(
    forms: Seq<Form>, index: int, end: int, closing: usize, expected: HeaderError,
) -> Option<(HeaderError, Range<usize>)> {
    if argument_matches(forms, index, end, expected) {
        None
    } else if 0 <= index < end <= forms.len() {
        Some((expected, form_span(forms[index])))
    } else {
        Some((expected, closing..closing))
    }
}

/// 先に調べる引数に違反があれば、その診断を採用する。
pub(super) open spec fn first_error(
    earlier: Option<(HeaderError, Range<usize>)>, later: Option<(HeaderError, Range<usize>)>,
) -> Option<(HeaderError, Range<usize>)> {
    if earlier is Some { earlier } else { later }
}

/// 式の文法に従い、必須引数から余剰引数まで左から順に検査する。
///
/// 子式の位置ではフォームが存在することを求める。その内容は子式を走査するときに検査する。
pub(super) open spec fn argument_shape_error(
    forms: Seq<Form>, first: int, end: int, closing: usize, builtin: Option<ExpressionHead>,
) -> Option<(HeaderError, Range<usize>)> {
    let value = if builtin == Some(ExpressionHead::As) { first + 1 } else { first };
    let next = if value < end { after_form(forms, value) } else { end };
    let present = argument_error(forms, value, end, closing, HeaderError::ExpectedExpression);
    match builtin {
        None => None,
        Some(ExpressionHead::Concat) => present,
        Some(ExpressionHead::As) => first_error(
            argument_error(forms, first, end, closing, HeaderError::ExpectedReference),
            first_error(present, argument_error(forms, next, end, closing, HeaderError::UnexpectedArgument)),
        ),
        Some(ExpressionHead::Slice) => {
            let after_count = next + 2;
            let after_step = if after_count < end { after_count + 1 } else { after_count };
            first_error(present, first_error(
                argument_error(forms, next, end, closing, HeaderError::ExpectedNatural),
                first_error(
                    argument_error(forms, next + 1, end, closing, HeaderError::ExpectedNatural),
                    first_error(
                        if after_count < end {
                            argument_error(forms, after_count, end, closing, HeaderError::ExpectedNatural)
                        } else { None },
                        argument_error(forms, after_step, end, closing, HeaderError::UnexpectedArgument),
                    ),
                ),
            ))
        },
        Some(head) => {
            let (auxiliary, after) = match head {
                ExpressionHead::Bit => (
                    argument_error(forms, next, end, closing, HeaderError::ExpectedNatural), next + 1,
                ),
                ExpressionHead::Field => (
                    argument_error(forms, next, end, closing, HeaderError::ExpectedName), next + 1,
                ),
                _ => (None, next),
            };
            first_error(present, first_error(auxiliary,
                argument_error(forms, after, end, closing, HeaderError::UnexpectedArgument)))
        },
    }
}

/// 指定した引数の種別または引数列の終端を検査する。
///
/// # Errors
///
/// 種別違反や余剰引数はそのフォームの範囲で、欠落は閉じ括弧の位置で報告する。
pub(super) fn check_argument(
    forms: &[Form], index: usize, end: usize, closing: usize, expected: HeaderError,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        index <= end <= forms@.len(),
        expected is ExpectedReference || expected is ExpectedNatural
            || expected is ExpectedName || expected is ExpectedExpression || expected is UnexpectedArgument,
    ensures
        result.is_ok() <==> argument_matches(forms@, index as int, end as int, expected),
        match result {
            Ok(()) => argument_error(forms@, index as int, end as int, closing, expected) is None,
            Err(error) => argument_error(forms@, index as int, end as int, closing, expected) == Some(error),
        },
{
    if index == end {
        return if matches!(expected, HeaderError::UnexpectedArgument) {
            Ok(())
        } else {
            Err((expected, closing..closing))
        };
    }
    let form = &forms[index];
    let accepted = match expected {
        HeaderError::ExpectedExpression => true,
        HeaderError::ExpectedReference => match form {
            Form::Atom { kind, .. } => is_reference(*kind),
            _ => false,
        },
        HeaderError::ExpectedName => matches!(form, Form::Atom { kind: AtomKind::Name, .. }),
        HeaderError::ExpectedNatural => matches!(form, Form::Atom { kind: AtomKind::Natural, .. }),
        _ => false,
    };
    if accepted { Ok(()) } else { Err((expected, form_span_exec(form))) }
}

/// 式の位置にあるフォームを一つ取り、その直後の添字を返す。
///
/// 式の内容は呼び出し側が検査する。
///
/// # Errors
///
/// フォームがなければ閉じ括弧の位置を長さ 0 の範囲で返す。
pub(super) fn read_expression_form(
    forms: &[Form], _first: usize, index: usize, end: usize, closing: usize,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        _first <= index <= end <= forms@.len(),
        form_region_ends_at(forms@, _first as int, end as int),
        nested_list_indices(forms@),
        complete_list_indices(forms@),
    ensures
        match result {
            Ok(next) => index < next <= end && next == after_form(forms@, index as int)
                && argument_error(forms@, index as int, end as int, closing,
                    HeaderError::ExpectedExpression) is None,
            Err(error) => argument_error(forms@, index as int, end as int, closing,
                HeaderError::ExpectedExpression) == Some(error),
        },
{
    check_argument(forms, index, end, closing, HeaderError::ExpectedExpression)?;
    proof { enclosing_region_bounds_form(forms@, _first as int, index as int, end as int); }
    Ok(match &forms[index] {
        Form::Atom { .. } => index + 1,
        Form::List { end, .. } => *end,
    })
}

/// ソース上の先頭語が、専用フォームの綴りに一致するかを表す。
pub(super) open spec fn list_head_matches(
    source: &str, forms: Seq<Form>, head: int, builtin: Option<ExpressionHead>,
) -> bool {
    &&& 0 <= head < forms.len()
    &&& {
        let span = form_span(forms[head]);
        &&& span.start < span.end <= source.spec_bytes().len()
        &&& forall|entry: ExpressionHead| #[trigger] expression_head_spelling(entry).spec_bytes()
            == source.spec_bytes()[span.start as int..span.end as int] <==> builtin == Some(entry)
    }
}

/// 専用フォームと通常呼び出しについて、文法が定める引数の配置と子式の区間を表す。
pub(super) open spec fn arguments_match(
    forms: Seq<Form>, first: int, end: int, builtin: Option<ExpressionHead>,
    child_start: int, child_end: int,
) -> bool {
    &&& 0 <= first <= child_start <= child_end <= end <= forms.len()
    &&& match builtin {
        None => child_start == first && child_end == end,
        Some(ExpressionHead::Concat) => child_start == first && first < child_end == end,
        Some(ExpressionHead::As) => child_start == first + 1 < child_end == end
            && child_end == after_form(forms, child_start)
            && argument_matches(forms, first, end, HeaderError::ExpectedReference),
        Some(head) => {
            &&& child_start == first < child_end
            &&& child_end == after_form(forms, first)
            &&& match head {
                ExpressionHead::Bit => child_end + 1 == end
                    && natural_argument_at(forms, child_end, end),
                ExpressionHead::Field => child_end + 1 == end
                    && argument_matches(forms, child_end, end, HeaderError::ExpectedName),
                ExpressionHead::Raw => child_end == end,
                ExpressionHead::Slice => natural_argument_at(forms, child_end, end)
                    && natural_argument_at(forms, child_end + 1, end)
                    && (child_end + 2 == end
                        || (child_end + 3 == end && natural_argument_at(forms, child_end + 2, end))),
                _ => false,
            }
        },
    }
}

/// リストの先頭語から式の種類を決め、子式が並ぶ半開区間を定める。
pub(super) open spec fn expression_child_range(
    source: &str, forms: Seq<Form>, index: int, end: int, child_start: int, child_end: int,
) -> bool {
    &&& 0 <= index < end <= forms.len()
    &&& forms[index] is List && forms[index]->List_end == end
    &&& argument_matches(forms, index + 1, end, HeaderError::ExpectedReference)
    &&& exists|builtin: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, index + 1, builtin)
        && arguments_match(forms, index + 2, end, builtin, child_start, child_end)
}

pub(super) proof fn same_expression_head(
    source: &str, forms: Seq<Form>, head: int, left: Option<ExpressionHead>, right: Option<ExpressionHead>,
)
    requires list_head_matches(source, forms, head, left), list_head_matches(source, forms, head, right),
    ensures left == right,
{
    if let Some(entry) = left {
        assert(expression_head_spelling(entry).spec_bytes()
            == source.spec_bytes()[form_span(forms[head]).start as int..form_span(forms[head]).end as int]);
    } else if let Some(entry) = right {
        assert(expression_head_spelling(entry).spec_bytes()
            == source.spec_bytes()[form_span(forms[head]).start as int..form_span(forms[head]).end as int]);
    }
}

fn read_expression_head(source: &str, form: &Form) -> (head: Option<ExpressionHead>)
    requires
        0 < form_span(*form).end <= source.spec_bytes().len(),
        form_span(*form).start < form_span(*form).end,
        is_char_boundary(source.spec_bytes(), form_span(*form).start as int),
        is_char_boundary(source.spec_bytes(), form_span(*form).end as int),
    ensures
        forall|entry: ExpressionHead| #[trigger] expression_head_spelling(entry).spec_bytes()
            == source.spec_bytes()[form_span(*form).start as int..form_span(*form).end as int]
            <==> head == Some(entry),
{
    let span = form_span_exec(form);
    let word = source_span(source, span.start, span.end);
    let head = recognize_expression_head(word);
    assert forall|entry: ExpressionHead| #[trigger] expression_head_spelling(entry).spec_bytes()
        == source.spec_bytes()[span.start as int..span.end as int] <==> head == Some(entry) by {
        let spelling = expression_head_spelling(entry);
        encode_utf8_decode_utf8(spelling@);
        encode_utf8_decode_utf8(word@);
    };
    head
}

/// リストの先頭語と引数のうち、最初の違反に対応する診断を表す。
pub(super) open spec fn expression_list_error(
    source: &str, forms: Seq<Form>, index: int, end: int, closing: usize,
    error: (HeaderError, Range<usize>),
) -> bool {
    let head_error = argument_error(forms, index + 1, end, closing, HeaderError::ExpectedReference);
    head_error == Some(error) || (head_error is None
        && (exists|builtin: Option<ExpressionHead>|
            #[trigger] list_head_matches(source, forms, index + 1, builtin)
            && argument_shape_error(forms, index + 2, end, closing, builtin) == Some(error)))
}

pub(super) proof fn same_expression_list_error(
    source: &str, forms: Seq<Form>, index: int, end: int, closing: usize,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        expression_list_error(source, forms, index, end, closing, left),
        expression_list_error(source, forms, index, end, closing, right),
    ensures left == right,
{
    if argument_error(forms, index + 1, end, closing, HeaderError::ExpectedReference) is None {
        let left_head = choose|builtin: Option<ExpressionHead>|
            #[trigger] list_head_matches(source, forms, index + 1, builtin)
            && argument_shape_error(forms, index + 2, end, closing, builtin) == Some(left);
        let right_head = choose|builtin: Option<ExpressionHead>|
            #[trigger] list_head_matches(source, forms, index + 1, builtin)
            && argument_shape_error(forms, index + 2, end, closing, builtin) == Some(right);
        same_expression_head(source, forms, index + 1, left_head, right_head);
    }
}

/// リスト形式の式の局所文法を検査し、走査する子式の添字範囲を返す。
///
/// # Errors
///
/// 先頭語に続いて引数の配置を検査し、最初の違反を UTF-8 のバイト範囲で返す。
/// 要素が欠けている場合は閉じ括弧の位置を長さ 0 の範囲で返す。
pub(super) fn expression_children(
    source: &str, forms: &[Form], index: usize, end: usize, closing: usize,
) -> (result: Result<(Range<usize>, Option<ExpressionHead>), (HeaderError, Range<usize>)>)
    requires
        index < end <= forms@.len(),
        forms@[index as int] is List,
        forms@[index as int]->List_end == end,
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing + 1 == form_span(forms@[index as int]).end,
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == b')',
    ensures
        forall|start: int, stop: int| #[trigger] expression_child_range(
            source, forms@, index as int, end as int, start, stop,
        ) <==> (result matches Ok((children, _)) && start == children.start && stop == children.end),
        match result {
            Ok((children, builtin)) => index + 1 < end && list_head_matches(source, forms@, index + 1, builtin)
                && argument_matches(forms@, index + 1, end as int, HeaderError::ExpectedReference)
                && arguments_match(forms@, index + 2, end as int, builtin,
                    children.start as int, children.end as int)
                && index < children.start <= children.end <= end
                && (children.end == end || (children.start < children.end
                    && children.end == after_form(forms@, children.start as int))),
            Err(_) => true,
        },
        match result {
            Ok(_) => true,
            Err(error) => expression_list_error(source, forms@, index as int, end as int, closing, error),
        },
{
    let head = index + 1;
    check_argument(forms, head, end, closing, HeaderError::ExpectedReference)?;
    proof {
        encode_utf8_valid_utf8(source@);
        reveal(form_spans_valid);
    }
    let builtin = read_expression_head(source, &forms[head]);
    assert(list_head_matches(source, forms@, head as int, builtin));
    let first = head + 1;
    assert(form_region_ends_at(forms@, first as int, end as int));
    let children = read_expression_arguments(forms, first, end, closing, builtin);
    assert forall|start: int, stop: int| #[trigger] expression_child_range(
        source, forms@, index as int, end as int, start, stop,
    ) <==> (children matches Ok(range) && start == range.start && stop == range.end) by {
        if expression_child_range(source, forms@, index as int, end as int, start, stop) {
            let witness = choose|candidate: Option<ExpressionHead>|
                #[trigger] list_head_matches(source, forms@, head as int, candidate)
                    && arguments_match(forms@, first as int, end as int, candidate, start, stop);
            same_expression_head(source, forms@, head as int, builtin, witness);
        }
    };
    match children {
        Ok(children) => Ok((children, builtin)),
        Err(error) => Err(error),
    }
}

fn read_expression_arguments(
    forms: &[Form], first: usize, end: usize, closing: usize, builtin: Option<ExpressionHead>,
) -> (result: Result<Range<usize>, (HeaderError, Range<usize>)>)
    requires
        first <= end <= forms@.len(),
        form_region_ends_at(forms@, first as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
    ensures
        forall|start: int, stop: int| #[trigger] arguments_match(forms@, first as int, end as int, builtin, start, stop)
            <==> (result matches Ok(children) && start == children.start && stop == children.end),
        match result {
            Ok(children) => first <= children.start <= children.end <= end
                && (children.end == end || (children.start < children.end
                    && children.end == after_form(forms@, children.start as int))),
            Err(error) => argument_shape_error(forms@, first as int, end as int, closing, builtin) == Some(error),
        },
{
    if matches!(builtin, Some(ExpressionHead::As)) {
        check_argument(forms, first, end, closing, HeaderError::ExpectedReference)?;
        let value = first + 1;
        let next = read_expression_form(forms, first, value, end, closing)?;
        check_argument(forms, next, end, closing, HeaderError::UnexpectedArgument)?;
        return Ok(value..next);
    }
    if builtin.is_none() {
        return Ok(first..end);
    }
    let next = read_expression_form(forms, first, first, end, closing)?;
    let after = match builtin {
        Some(ExpressionHead::Concat) => return Ok(first..end),
        Some(ExpressionHead::Bit) => {
            check_argument(forms, next, end, closing, HeaderError::ExpectedNatural)?;
            next + 1
        }
        Some(ExpressionHead::Slice) => {
            check_argument(forms, next, end, closing, HeaderError::ExpectedNatural)?;
            check_argument(forms, next + 1, end, closing, HeaderError::ExpectedNatural)?;
            let after_count = next + 2;
            if after_count < end {
                check_argument(forms, after_count, end, closing, HeaderError::ExpectedNatural)?;
                after_count + 1
            } else {
                after_count
            }
        }
        Some(ExpressionHead::Field) => {
            check_argument(forms, next, end, closing, HeaderError::ExpectedName)?;
            next + 1
        }
        _ => next,
    };
    check_argument(forms, after, end, closing, HeaderError::UnexpectedArgument)?;
    Ok(first..next)
}

} // verus!
