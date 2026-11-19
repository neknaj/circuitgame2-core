//! 回路宣言の署名に続く本体を検査する。

#[cfg(verus_only)]
use super::clauses::enclosing_region_bounds_form;
#[cfg(verus_only)]
use super::expression_forest::{
    expression_forest, expression_forest_error, expression_index_region,
    expression_reference_in_source, expression_references, expression_region,
};
use super::expression_forest::{inspect_expressions, inspect_expressions_into};
#[cfg(verus_only)]
use super::expressions::{after_form, argument_error, argument_matches};
use super::expressions::{check_argument, read_expression_form};
use super::ports::read_routine_signature;
use super::*;

verus! {

/// 一つの `def` と、その右辺に現れる回路名と型名。
#[derive(Debug, Eq, PartialEq)]
pub struct DefinitionReferences {
    /// 元の構文木で `def` のリストを指す添字。
    pub definition: usize,
    /// 右辺の式全体が占める、構文木の半開区間。
    pub expression: Range<usize>,
    /// 呼び出し名と型名を元ソース順に並べた一覧。
    pub references: Vec<ExpressionReference>,
}

/// 単独の名前、または名前を一つ以上含むリストを定義の左辺として認める。
pub(super) open spec fn targets_match(forms: Seq<Form>, index: int, end: int, after: int) -> bool {
    &&& 0 <= index < after <= end <= forms.len()
    &&& match forms[index] {
        Form::Atom { kind, .. } => kind is Name && after == index + 1,
        Form::List { end: target_end, .. } => {
            &&& after == target_end && index + 1 < after
            &&& forall|name: int| index < name < after
                ==> #[trigger] argument_matches(forms, name, after, HeaderError::ExpectedName)
        },
    }
}

/// 定義の左辺の欠落、字句種別の違反、またはリスト内の最初の違反を表す。
pub(super) open spec fn targets_error(
    forms: Seq<Form>, index: int, end: int, closing: usize, error: (HeaderError, Range<usize>),
) -> bool {
    &&& 0 <= index <= end <= forms.len()
    &&& if index == end {
        error == (HeaderError::ExpectedTarget, closing..closing)
    } else {
        match forms[index] {
            Form::Atom { kind, span } => !(kind is Name) && error == (HeaderError::ExpectedTarget, span),
            Form::List { end: target_end, span } => {
                let stop = target_end as int;
                let expected = HeaderError::ExpectedName;
                &&& index < stop <= end
                &&& span.end > 0
                &&& exists|bad: int| index < bad <= stop && (bad < stop || bad == index + 1)
                    && #[trigger] argument_error(forms, bad, stop, (span.end - 1) as usize, expected) == Some(error)
                    && (forall|name: int| index < name < bad
                        ==> #[trigger] argument_matches(forms, name, stop, expected))
            },
        }
    }
}

fn read_targets(
    _source: &str, forms: &[Form], index: usize, end: usize, closing: usize,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        index <= end <= forms@.len(),
        form_region_ends_at(forms@, index as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(_source, forms@, false),
    ensures
        forall|after: int| #[trigger] targets_match(forms@, index as int, end as int, after)
            <==> (result matches Ok(next) && after == next),
        result matches Ok(next) ==> index < next <= end,
        result matches Err(error) ==> targets_error(forms@, index as int, end as int, closing, error),
{
    if index == end {
        return Err((HeaderError::ExpectedTarget, closing..closing));
    }
    let form = &forms[index];
    let Form::List { end: target_end, span: list_span } = form else {
        if matches!(form, Form::Atom { kind: AtomKind::Name, .. }) {
            return Ok(index + 1);
        }
        return Err((HeaderError::ExpectedTarget, form_span_exec(form)));
    };
    proof {
        enclosing_region_bounds_form(forms@, index as int, index as int, end as int);
        reveal(list_source_delimiters);
        assert(list_delimited(_source.spec_bytes(), *form, false));
    }
    let stop = *target_end;
    let close = list_span.end - 1;
    let expected = HeaderError::ExpectedName;
    let mut name = index + 1;
    loop
        invariant
            index < name <= stop <= end <= forms@.len(),
            forms@[index as int] is List,
            forms@[index as int]->List_end == stop,
            close + 1 == form_span(forms@[index as int]).end,
            name < stop || name == index + 1,
            forall|seen: int| index < seen < name
                ==> #[trigger] argument_matches(forms@, seen, stop as int, HeaderError::ExpectedName),
            expected == HeaderError::ExpectedName,
        decreases stop - name,
    {
        check_argument(forms, name, stop, close, expected)?;
        name += 1;
        if name == stop {
            return Ok(stop);
        }
    }
}

/// 展開呼び出しには参照を、定義には左辺と式一つを求める。
///
/// 展開の参照より後ろには任意の S 式を置ける。
pub(super) open spec fn body_arguments_match(
    source: &str, forms: Seq<Form>, first: int, end: int, kind: BodyHead,
) -> bool {
    match kind {
        BodyHead::Expand => argument_matches(forms, first, end, HeaderError::ExpectedReference),
        BodyHead::Def => exists|value: int| #[trigger] targets_match(forms, first, end, value)
            && value < end && after_form(forms, value) == end
            && expression_forest(source, forms, value, end),
    }
}

/// 引数の配置を先に検査し、定義に式が一つある場合にその内容の診断を採用する。
pub(super) open spec fn body_arguments_error(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, kind: BodyHead,
    error: (HeaderError, Range<usize>),
) -> bool {
    match kind {
        BodyHead::Expand => argument_error(forms, first, end, closing, HeaderError::ExpectedReference) == Some(error),
        BodyHead::Def => targets_error(forms, first, end, closing, error)
            || (exists|value: int| #[trigger] targets_match(forms, first, end, value)
                && (if value == end {
                    argument_error(forms, value, end, closing, HeaderError::ExpectedExpression) == Some(error)
                } else {
                    let after = after_form(forms, value);
                    &&& value < after <= end
                    &&& if after < end {
                        argument_error(forms, after, end, closing, HeaderError::UnexpectedArgument) == Some(error)
                    } else {
                        expression_forest_error(source, forms, value, end, error)
                    }
                })),
    }
}

proof fn single_expression_region(forms: Seq<Form>, index: int, after: int)
    requires
        0 <= index < after <= forms.len(),
        after == after_form(forms, index),
        nested_list_indices(forms),
    ensures expression_region(forms, index, after),
{
    reveal(expression_region);
    reveal(nested_list_indices);
    assert forall|i: int| index <= i < after && #[trigger] forms[i] is List
        implies forms[i]->List_end <= after by {
        if index < i {
            assert(forms[index] is List);
        }
    };
}

/// 本体項目の残りの引数を検査し、定義なら右辺の範囲を返す。
///
/// # Errors
///
/// 引数の配置に違反があれば、その種別と UTF-8 バイト範囲を返す。
/// 右辺の検査に失敗した場合、違反より前に収集した参照は配列の末尾に残る。
fn inspect_body_arguments(
    source: &str, forms: &[Form], first: usize, end: usize, closing: usize, kind: BodyHead,
    collect: bool, references: &mut Vec<ExpressionReference>,
) -> (result: Result<Option<Range<usize>>, (HeaderError, Range<usize>)>)
    requires
        first <= end <= forms@.len(),
        form_region_ends_at(forms@, first as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == b')',
    ensures
        result.is_ok() <==> body_arguments_match(source, forms@, first as int, end as int, kind),
        result matches Err(error) ==> body_arguments_error(
            source, forms@, first as int, end as int, closing, kind, error,
        ),
        final(references)@.len() >= old(references)@.len(),
        final(references)@.take(old(references)@.len() as int) == old(references)@,
        !collect ==> final(references)@ == old(references)@,
        result matches Ok(None) ==> kind is Expand && final(references)@ == old(references)@,
        result matches Ok(Some(rhs)) ==> kind is Def
            && targets_match(forms@, first as int, end as int, rhs.start as int)
            && rhs.start < rhs.end == end && after_form(forms@, rhs.start as int) == rhs.end
            && expression_forest(source, forms@, rhs.start as int, rhs.end as int)
            && (collect ==> final(references)@ == old(references)@
                + expression_references(source, forms@, rhs.start as int, rhs.end as int)),
        forall|i: int| old(references)@.len() <= i < final(references)@.len()
            ==> expression_reference_in_source(source, forms@, #[trigger] final(references)@[i]),
{
    if matches!(kind, BodyHead::Expand) {
        check_argument(forms, first, end, closing, HeaderError::ExpectedReference)?;
        return Ok(None);
    }
    let value = read_targets(source, forms, first, end, closing)?;
    assert(targets_match(forms@, first as int, end as int, value as int));
    let after = read_expression_form(forms, first, value, end, closing)?;
    check_argument(forms, after, end, closing, HeaderError::UnexpectedArgument)?;
    proof { single_expression_region(forms@, value as int, after as int); }
    inspect_expressions_into(source, forms, value..after, collect, references)?;
    Ok(Some(value..after))
}

/// 本体項目の先頭に、指定した綴りが無修飾の名前として現れることを表す。
pub(super) open spec fn body_head_at(
    source: &str, forms: Seq<Form>, index: int, end: int, kind: BodyHead,
) -> bool {
    &&& argument_matches(forms, index, end, HeaderError::ExpectedName)
    &&& {
        let span = form_span(forms[index]);
        &&& span.start < span.end <= source.spec_bytes().len()
        &&& body_head_spelling(kind).spec_bytes() == source.spec_bytes()[span.start as int..span.end as int]
    }
}

fn read_body_item_head(
    source: &str, forms: &[Form], index: usize, end: usize, closing: usize,
) -> (result: Result<BodyHead, (HeaderError, Range<usize>)>)
    requires
        index <= end <= forms@.len(),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        forall|kind: BodyHead| #[trigger] body_head_at(source, forms@, index as int, end as int, kind)
            <==> result == Ok(kind),
        result matches Err((kind, span)) ==> kind == HeaderError::ExpectedBodyItem
            && directive_argument_error_span(forms@, index as int, end as int, closing, span),
{
    if let Err((_, span)) = check_argument(forms, index, end, closing, HeaderError::ExpectedName) {
        return Err((HeaderError::ExpectedBodyItem, span));
    }
    let form = &forms[index];
    let word_span = form_span_exec(form);
    proof {
        reveal(form_spans_valid);
        encode_utf8_valid_utf8(source@);
    }
    let word = source_span(source, word_span.start, word_span.end);
    let head = recognize_body_head(word);
    assert forall|kind: BodyHead| #[trigger] body_head_at(source, forms@, index as int, end as int, kind)
        <==> head == Some(kind) by {
        let spelling = body_head_spelling(kind);
        encode_utf8_decode_utf8(word@);
        encode_utf8_decode_utf8(spelling@);
    };
    match head {
        Some(kind) => Ok(kind),
        None => Err((HeaderError::ExpectedBodyItem, word_span)),
    }
}

/// 本体項目を、既知の先頭語と、それに対応する引数を持つリストとして定める。
pub(super) open spec fn body_item_matches(
    source: &str, forms: Seq<Form>, index: int, limit: int,
) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& forms[index] is List
    &&& {
        let end = forms[index]->List_end as int;
        &&& index < end <= limit
        &&& exists|kind: BodyHead| #[trigger] body_head_at(source, forms, index + 1, end, kind)
            && body_arguments_match(source, forms, index + 2, end, kind)
    }
}

/// リスト、先頭語、引数の順に本体項目を検査したときの診断を表す。
pub(super) open spec fn body_item_error(
    source: &str, forms: Seq<Form>, index: int, limit: int, error: (HeaderError, Range<usize>),
) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& match forms[index] {
        Form::Atom { span, .. } => error == (HeaderError::ExpectedBodyItem, span),
        Form::List { span, end } => {
            let end = end as int;
            let close = (span.end - 1) as usize;
            &&& index < end <= limit
            &&& span.end > 0
            &&& if exists|kind: BodyHead| #[trigger] body_head_at(source, forms, index + 1, end, kind) {
                exists|kind: BodyHead| #[trigger] body_head_at(source, forms, index + 1, end, kind)
                    && body_arguments_error(source, forms, index + 2, end, close, kind, error)
            } else {
                error.0 == HeaderError::ExpectedBodyItem
                    && directive_argument_error_span(forms, index + 1, end, close, error.1)
            }
        },
    }
}

fn read_body_item(
    source: &str, forms: &[Form], index: usize, _limit: usize,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        index < _limit <= forms@.len(),
        form_region_ends_at(forms@, index as int, _limit as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> body_item_matches(source, forms@, index as int, _limit as int),
        result matches Ok(next) ==> index < next <= _limit
            && following_direct_form(forms@, index as int, next as int),
        result matches Err(error) ==> body_item_error(source, forms@, index as int, _limit as int, error),
{
    let form = &forms[index];
    let Form::List { span: item_span, end: item_end } = form else {
        return Err((HeaderError::ExpectedBodyItem, form_span_exec(form)));
    };
    proof {
        enclosing_region_bounds_form(forms@, index as int, index as int, _limit as int);
        reveal(list_source_delimiters);
        assert(list_delimited(source.spec_bytes(), *form, false));
    }
    let end = *item_end;
    let closing = item_span.end - 1;
    let kind = read_body_item_head(source, forms, index + 1, end, closing)?;
    assert(body_head_at(source, forms@, index + 1, end as int, kind));
    let first = index + 2;
    assert(form_region_ends_at(forms@, first as int, end as int));
    let mut references = Vec::new();
    inspect_body_arguments(source, forms, first, end, closing, kind, false, &mut references)?;
    proof { node_end_is_following_direct_form(forms@, index as int, end as int); }
    Ok(end)
}

/// 指定した位置より前にある直接の本体項目がすべて文法に従うことを表す。
#[verifier::opaque]
pub(super) open spec fn body_items_before(
    source: &str, forms: Seq<Form>, start: int, end: int, cursor: int,
) -> bool {
    forall|index: int| #[trigger] direct_form_in_range(forms, start, end, index) && index < cursor
        ==> body_item_matches(source, forms, index, end)
}

/// 本体項目列のうち最初に失敗した項目の診断と、それより前の項目の妥当性を表す。
pub(super) open spec fn body_error(
    source: &str, forms: Seq<Form>, start: int, end: int, error: (HeaderError, Range<usize>),
) -> bool {
    exists|index: int| #[trigger] direct_form_in_range(forms, start, end, index)
        && body_items_before(source, forms, start, end, index)
        && body_item_error(source, forms, index, end, error)
}

proof fn record_body_item(
    source: &str, forms: Seq<Form>, start: int, index: int, next: int, end: int,
)
    requires
        index < next <= end,
        direct_form_in_range(forms, start, end, index),
        following_direct_form(forms, index, next),
        form_region_ends_at(forms, start, end),
        body_items_before(source, forms, start, end, index),
        body_item_matches(source, forms, index, end),
    ensures
        next < end ==> direct_form_in_range(forms, start, end, next),
        body_items_before(source, forms, start, end, next),
{
    reveal(following_direct_form);
    reveal(body_items_before);
    assert forall|item: int| #[trigger] direct_form_in_range(forms, start, end, item) && item < next
        implies body_item_matches(source, forms, item, end) by {
        if item > index {
            assert(!direct_form_in_range(forms, start, end, item));
        }
    };
}

/// 回路宣言の本体を、直接の本体項目が並ぶ順序で検査する。
///
/// # Errors
///
/// 最初に違反した本体項目の診断を返す。
fn validate_body(
    source: &str, forms: &[Form], start: usize, end: usize,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        start <= end <= forms@.len(),
        form_region_ends_at(forms@, start as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> body_items_before(source, forms@, start as int, end as int, end as int),
        result matches Err(error) ==> body_error(source, forms@, start as int, end as int, error),
{
    let mut index = start;
    proof {
        reveal(direct_form_in_range);
        reveal(body_items_before);
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
            body_items_before(source, forms@, start as int, end as int, index as int),
        decreases end - index,
    {
        assert(form_region_ends_at(forms@, index as int, end as int));
        let next = match read_body_item(source, forms, index, end) {
            Ok(next) => next,
            Err(error) => {
                assert(!body_items_before(source, forms@, start as int, end as int, end as int)) by {
                    reveal(body_items_before);
                };
                return Err(error);
            }
        };
        proof { record_body_item(source, forms@, start as int, index as int, next as int, end as int); }
        index = next;
    }
    Ok(())
}

/// 宣言の署名が定める開始位置から本体項目列が続くことを表す。
pub(super) open spec fn routine_arguments_match(
    source: &str, forms: Seq<Form>, first: int, end: int, head: Head,
) -> bool {
    exists|body: int| #[trigger] routine_signature_matches(source, forms, first, end, head, body)
        && body_items_before(source, forms, body, end, end)
}

/// 署名を先に検査し、有効な署名に続く本体の最初の違反を報告する。
pub(super) open spec fn routine_arguments_error(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, head: Head,
    error: (HeaderError, Range<usize>),
) -> bool {
    routine_signature_error_evidence(source, forms, first, end, closing, head, error.0, error.1)
    || (exists|body: int| #[trigger] routine_signature_matches(source, forms, first, end, head, body)
        && body_error(source, forms, body, end, error))
}

/// 関数、モジュール、モジュール断片の署名と本体を順に検査する。
///
/// # Errors
///
/// 署名から本体へ順に検査し、最初の違反の種別と UTF-8 バイト範囲を返す。
pub(super) fn validate_routine_arguments(
    source: &str, forms: &[Form], first: usize, end: usize, closing: usize, head: Head,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        first <= end <= forms@.len(),
        form_region_ends_at(forms@, first as int, end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == b')',
        head is Func || head is Module || head is ModulePart,
    ensures
        result.is_ok() <==> routine_arguments_match(source, forms@, first as int, end as int, head),
        result matches Err(error) ==> routine_arguments_error(
            source, forms@, first as int, end as int, closing, head, error,
        ),
{
    let body = read_routine_signature(source, forms, first, end, closing, head)?;
    assert(routine_signature_matches(source, forms@, first as int, end as int, head, body as int));
    assert(form_region_ends_at(forms@, body as int, end as int));
    validate_body(source, forms, body, end)
}

pub(super) open spec fn is_definition_at(
    source: &str, forms: Seq<Form>, start: int, end: int, item: int,
) -> bool {
    &&& direct_form_in_range(forms, start, end, item)
    &&& 0 <= item < end <= forms.len()
    &&& forms[item] is List
    &&& body_head_at(source, forms, item + 1, forms[item]->List_end as int, BodyHead::Def)
}

#[verifier::opaque]
pub(super) open spec fn definitions_before(
    source: &str, forms: Seq<Form>, start: int, end: int, cursor: int,
    rows: Seq<DefinitionReferences>,
) -> bool {
    &&& forall|i: int| 0 <= i < rows.len() ==> {
        let row = #[trigger] rows[i];
        let item = row.definition as int;
        let value = row.expression.start as int;
        let stop = row.expression.end as int;
        &&& is_definition_at(source, forms, start, end, item)
        &&& item < cursor
        &&& stop == forms[item]->List_end
        &&& targets_match(forms, item + 2, stop, value)
        &&& value < stop && after_form(forms, value) == stop
        &&& expression_forest(source, forms, value, stop)
        &&& row.references@ == expression_references(source, forms, value, stop)
        &&& forall|r: int| 0 <= r < row.references@.len()
            ==> expression_reference_in_source(source, forms, #[trigger] row.references@[r])
    }
    &&& forall|item: int| #[trigger] is_definition_at(source, forms, start, end, item) && item < cursor
        ==> exists|i: int| 0 <= i < rows.len() && (#[trigger] rows[i]).definition == item
    &&& forall|i: int, j: int| 0 <= i < j < rows.len()
        ==> (#[trigger] rows[i]).definition < (#[trigger] rows[j]).definition
}

/// 検査済みの署名から本体をたどり、各定義の右辺と参照を取り出す。
pub(super) fn collect_definitions(
    source: &str, forms: &[Form], first: usize, end: usize, closing: usize, head: Head,
) -> (rows: Vec<DefinitionReferences>)
    requires
        first <= end <= forms@.len(),
        form_region_ends_at(forms@, first as int, end as int),
        complete_list_indices(forms@), nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == b')',
        head is Func || head is Module || head is ModulePart,
        routine_arguments_match(source, forms@, first as int, end as int, head),
    ensures
        exists|body: int| #[trigger] routine_signature_matches(source, forms@, first as int, end as int, head, body)
            && definitions_before(source, forms@, body, end as int, end as int, rows@),
{
    let signature = read_routine_signature(source, forms, first, end, closing, head);
    let Ok(body) = signature else {
        proof { assert(false); }
        unreachable!();
    };
    assert(body_items_before(source, forms@, body as int, end as int, end as int));
    assert(form_region_ends_at(forms@, body as int, end as int));
    let mut rows: Vec<DefinitionReferences> = Vec::new();
    let mut index = body;
    proof {
        reveal(direct_form_in_range);
        reveal(definitions_before);
    }
    while index < end
        invariant
            body <= index <= end <= forms@.len(),
            form_region_ends_at(forms@, body as int, end as int),
            complete_list_indices(forms@), nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            index < end ==> direct_form_in_range(forms@, body as int, end as int, index as int),
            body_items_before(source, forms@, body as int, end as int, end as int),
            definitions_before(source, forms@, body as int, end as int, index as int, rows@),
        decreases end - index,
    {
        let ghost prior = rows@;
        proof {
            reveal(body_items_before);
            assert(body_item_matches(source, forms@, index as int, end as int));
        }
        let Form::List { span: item_span, end: stop } = &forms[index] else {
            proof { assert(false); }
            unreachable!();
        };
        proof {
            reveal(list_source_delimiters);
            assert(list_delimited(source.spec_bytes(), forms@[index as int], false));
        }
        let head = read_body_item_head(source, forms, index + 1, *stop, item_span.end - 1);
        let Ok(kind) = head else {
            proof { assert(false); }
            unreachable!();
        };
        assert(body_arguments_match(source, forms@, index + 2, *stop as int, kind));
        if matches!(kind, BodyHead::Def) {
            let first = index + 2;
            assert(form_region_ends_at(forms@, first as int, *stop as int));
            let value = read_targets(source, forms, first, *stop, item_span.end - 1);
            let Ok(start) = value else {
                proof { assert(false); }
                unreachable!();
            };
            proof { single_expression_region(forms@, start as int, *stop as int); }
            let references = inspect_expressions(source, forms, start..*stop, true);
            let Ok(references) = references else {
                proof { assert(false); }
                unreachable!();
            };
            rows.push(DefinitionReferences { definition: index, expression: start..*stop, references });
        }
        proof {
            reveal(definitions_before);
            node_end_is_following_direct_form(forms@, index as int, *stop as int);
            reveal(following_direct_form);
            assert(rows@.take(prior.len() as int) =~= prior);
            assert forall|i: int| #[trigger] is_definition_at(source, forms@, body as int, end as int, i)
                && i < *stop implies exists|j: int| 0 <= j < rows@.len() && (#[trigger] rows@[j]).definition == i by {
                if i < index {
                    let j = choose|j: int| 0 <= j < prior.len() && (#[trigger] prior[j]).definition == i;
                    assert(rows@[j] == rows@.take(prior.len() as int)[j]);
                } else {
                    assert(i == index);
                    assert(kind is Def);
                    assert(rows@[prior.len() as int].definition == i);
                }
            };
        }
        index = *stop;
    }
    rows
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn definition_inspection_appends_references_to_the_shared_buffer() {
        let source = "(def y (call x)) (expand ::macro (def y (ignore x))) (def (a b) (as ::lib::T (next x)))";
        let forms = parse(source).unwrap();
        let mut root = 0;
        let mut references = Vec::new();
        for (kind, expected) in [
            (BodyHead::Def, 1),
            (BodyHead::Expand, 1),
            (BodyHead::Def, 3),
        ] {
            let Form::List { span, end } = &forms[root] else {
                panic!("expected a body item");
            };
            let rhs = inspect_body_arguments(
                source,
                &forms,
                root + 2,
                *end,
                span.end - 1,
                kind,
                true,
                &mut references,
            )
            .unwrap();
            if let Some(rhs) = rhs {
                assert_eq!(rhs.end, *end);
            }
            assert_eq!(references.len(), expected);
            root = *end;
        }
        assert_eq!(
            references
                .iter()
                .map(|reference| &source[reference.span.clone()])
                .collect::<Vec<_>>(),
            ["call", "::lib::T", "next"]
        );
    }

    #[test]
    fn definition_inspection_rejects_extra_arguments_before_visiting_the_rhs() {
        let source = "(def y (as T) extra)";
        let forms = parse(source).unwrap();
        let mut references = Vec::new();
        let (kind, span) = inspect_body_arguments(
            source,
            &forms,
            2,
            forms.len(),
            source.len() - 1,
            BodyHead::Def,
            true,
            &mut references,
        )
        .unwrap_err();
        assert_eq!(kind, HeaderError::UnexpectedArgument);
        assert_eq!(&source[span], "extra");
        assert!(references.is_empty());
    }

    #[test]
    fn definition_inspection_preserves_the_prefix_when_a_nested_expression_fails() {
        let source = "(def y (first x)) (def z (outer (as T)))";
        let forms = parse(source).unwrap();
        let Form::List { span, end } = &forms[0] else {
            panic!("expected a definition list");
        };
        let mut references = Vec::new();
        inspect_body_arguments(
            source,
            &forms,
            2,
            *end,
            span.end - 1,
            BodyHead::Def,
            true,
            &mut references,
        )
        .unwrap();
        let (kind, _) = inspect_body_arguments(
            source,
            &forms,
            *end + 2,
            forms.len(),
            source.len() - 1,
            BodyHead::Def,
            true,
            &mut references,
        )
        .unwrap_err();
        assert_eq!(kind, HeaderError::ExpectedExpression);
        assert_eq!(&source[references[0].span.clone()], "first");
        assert_eq!(&source[references[1].span.clone()], "outer");
        assert_eq!(references.len(), 2);
    }
}
