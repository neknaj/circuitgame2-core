//! 回路宣言の署名に続く本体を検査する。

#[cfg(verus_only)]
use super::{call_shapes::list_children_region, clauses::enclosing_region_bounds_form};
#[cfg(verus_only)]
use super::expression_forest::{
    expression_forest, expression_forest_error, expression_forest_errors_agree,
    expression_forest_match_excludes_error, expression_index_region, expression_reference_in_source,
    expression_references, expression_region, expression_signals,
};
use super::expression_forest::{inspect_expressions, inspect_expressions_into};
#[cfg(verus_only)]
use super::expressions::{after_form, argument_error, argument_matches};
use super::expressions::{check_argument, read_expression_form};
#[cfg(verus_only)]
use super::ports::{
    RoutineLayout, routine_layout_matches, routine_signature_after_agrees,
    routine_signature_errors_agree, routine_signature_match_excludes_error,
};
use super::ports::{read_routine_signature, routine_layout};
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

/// 左辺の形式が正しければ、左辺を原因とする診断は成立しない。
proof fn targets_match_excludes_error(
    forms: Seq<Form>, index: int, end: int, closing: usize, after: int,
    error: (HeaderError, Range<usize>),
)
    requires
        targets_match(forms, index, end, after),
    ensures
        !targets_error(forms, index, end, closing, error),
{
    if targets_error(forms, index, end, closing, error) && forms[index] is List {
        let span = forms[index]->List_span;
        let expected = HeaderError::ExpectedName;
        let bad = choose|bad: int| index < bad <= after && (bad < after || bad == index + 1)
            && #[trigger] argument_error(forms, bad, after, (span.end - 1) as usize, expected) == Some(error)
            && (forall|name: int| index < name < bad
                ==> #[trigger] argument_matches(forms, name, after, expected));
        assert(index + 1 < after);
        assert(argument_matches(forms, bad, after, expected));
    }
}

/// 左辺がリストなら、最初に名前の規則に違反した要素を診断する。
proof fn targets_errors_agree(
    forms: Seq<Form>, index: int, end: int, closing: usize,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        targets_error(forms, index, end, closing, left),
        targets_error(forms, index, end, closing, right),
    ensures
        left == right,
{
    if index < end && forms[index] is List {
        let stop = forms[index]->List_end as int;
        let close = (forms[index]->List_span.end - 1) as usize;
        let expected = HeaderError::ExpectedName;
        let a = choose|bad: int| index < bad <= stop && (bad < stop || bad == index + 1)
            && #[trigger] argument_error(forms, bad, stop, close, expected) == Some(left)
            && (forall|name: int| index < name < bad
                ==> #[trigger] argument_matches(forms, name, stop, expected));
        let b = choose|bad: int| index < bad <= stop && (bad < stop || bad == index + 1)
            && #[trigger] argument_error(forms, bad, stop, close, expected) == Some(right)
            && (forall|name: int| index < name < bad
                ==> #[trigger] argument_matches(forms, name, stop, expected));
        if a < b {
            assert(argument_matches(forms, a, stop, expected));
        } else if b < a {
            assert(argument_matches(forms, b, stop, expected));
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

/// 左辺が文法に適合する定義で、右辺の式の個数と内容を順に検査した場合の診断根拠を表す。
pub(super) open spec fn definition_rhs_error(
    source: &str, forms: Seq<Form>, value: int, end: int, closing: usize,
    error: (HeaderError, Range<usize>),
) -> bool {
    if value == end {
        argument_error(forms, value, end, closing, HeaderError::ExpectedExpression) == Some(error)
    } else {
        let after = after_form(forms, value);
        &&& value < after <= end
        &&& if after < end {
            argument_error(forms, after, end, closing, HeaderError::UnexpectedArgument) == Some(error)
        } else {
            expression_forest_error(source, forms, value, end, error)
        }
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
                && definition_rhs_error(source, forms, value, end, closing, error)),
    }
}

proof fn body_arguments_match_excludes_error(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, kind: BodyHead,
    error: (HeaderError, Range<usize>),
)
    requires body_arguments_match(source, forms, first, end, kind),
    ensures !body_arguments_error(source, forms, first, end, closing, kind, error),
{
    if kind is Def && body_arguments_error(source, forms, first, end, closing, kind, error) {
        let value = choose|value: int| #[trigger] targets_match(forms, first, end, value)
            && value < end && after_form(forms, value) == end
            && expression_forest(source, forms, value, end);
        targets_match_excludes_error(forms, first, end, closing, value, error);
        let bad_value = choose|value: int| #[trigger] targets_match(forms, first, end, value)
            && definition_rhs_error(source, forms, value, end, closing, error);
        assert(value == after_form(forms, first) == bad_value);
        expression_forest_match_excludes_error(source, forms, value, end, error);
    }
}

proof fn body_arguments_errors_agree(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, kind: BodyHead,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        body_arguments_error(source, forms, first, end, closing, kind, left),
        body_arguments_error(source, forms, first, end, closing, kind, right),
    ensures left == right,
{
    if kind is Def {
        let value = after_form(forms, first);
        if targets_match(forms, first, end, value) {
            targets_match_excludes_error(forms, first, end, closing, value, left);
            targets_match_excludes_error(forms, first, end, closing, value, right);
            let left_value = choose|value: int| #[trigger] targets_match(forms, first, end, value)
                && definition_rhs_error(source, forms, value, end, closing, left);
            let right_value = choose|value: int| #[trigger] targets_match(forms, first, end, value)
                && definition_rhs_error(source, forms, value, end, closing, right);
            assert(left_value == value == right_value);
            if value < end && after_form(forms, value) == end {
                expression_forest_errors_agree(source, forms, value, end, left, right);
            }
        } else {
            targets_errors_agree(forms, first, end, closing, left, right);
        }
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
    signals: &mut Vec<usize>,
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
        !collect ==> final(signals)@ == old(signals)@,
        final(signals)@.len() >= old(signals)@.len(),
        final(signals)@.take(old(signals)@.len() as int) == old(signals)@,
        result matches Ok(None) ==> kind is Expand && final(references)@ == old(references)@
            && final(signals)@ == old(signals)@,
        result matches Ok(Some(rhs)) ==> kind is Def
            && targets_match(forms@, first as int, end as int, rhs.start as int)
            && rhs.start < rhs.end == end && after_form(forms@, rhs.start as int) == rhs.end
            && expression_forest(source, forms@, rhs.start as int, rhs.end as int)
            && (collect ==> final(references)@ == old(references)@
                + expression_references(source, forms@, rhs.start as int, rhs.end as int))
            && (collect ==> final(signals)@ == old(signals)@
                + expression_signals(source, forms@, rhs.start as int, rhs.end as int)),
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
    inspect_expressions_into(source, forms, value..after, collect, references, collect, signals)?;
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

proof fn body_heads_agree(
    source: &str, forms: Seq<Form>, index: int, end: int, left: BodyHead, right: BodyHead,
)
    requires
        body_head_at(source, forms, index, end, left),
        body_head_at(source, forms, index, end, right),
    ensures left == right,
{
    let left_word = body_head_spelling(left);
    let right_word = body_head_spelling(right);
    encode_utf8_decode_utf8(left_word@);
    encode_utf8_decode_utf8(right_word@);
    assert(left_word@ == right_word@);
}

proof fn body_item_match_excludes_error(
    source: &str, forms: Seq<Form>, index: int, limit: int, error: (HeaderError, Range<usize>),
)
    requires body_item_matches(source, forms, index, limit),
    ensures !body_item_error(source, forms, index, limit, error),
{
    if body_item_error(source, forms, index, limit, error) {
        let end = forms[index]->List_end as int;
        let close = (form_span(forms[index]).end - 1) as usize;
        let kind = choose|kind: BodyHead| #[trigger] body_head_at(source, forms, index + 1, end, kind)
            && body_arguments_match(source, forms, index + 2, end, kind);
        let bad_kind = choose|kind: BodyHead| #[trigger] body_head_at(source, forms, index + 1, end, kind)
            && body_arguments_error(source, forms, index + 2, end, close, kind, error);
        body_heads_agree(source, forms, index + 1, end, kind, bad_kind);
        body_arguments_match_excludes_error(source, forms, index + 2, end, close, kind, error);
    }
}

proof fn body_item_errors_agree(
    source: &str, forms: Seq<Form>, index: int, limit: int,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        body_item_error(source, forms, index, limit, left),
        body_item_error(source, forms, index, limit, right),
    ensures left == right,
{
    if forms[index] is List {
        let end = forms[index]->List_end as int;
        let close = (form_span(forms[index]).end - 1) as usize;
        if exists|kind: BodyHead| #[trigger] body_head_at(source, forms, index + 1, end, kind) {
            let left_kind = choose|kind: BodyHead| #[trigger] body_head_at(source, forms, index + 1, end, kind)
                && body_arguments_error(source, forms, index + 2, end, close, kind, left);
            let right_kind = choose|kind: BodyHead| #[trigger] body_head_at(source, forms, index + 1, end, kind)
                && body_arguments_error(source, forms, index + 2, end, close, kind, right);
            body_heads_agree(source, forms, index + 1, end, left_kind, right_kind);
            body_arguments_errors_agree(source, forms, index + 2, end, close, left_kind, left, right);
        }
    }
}

fn read_body_item(
    source: &str, forms: &[Form], index: usize, _limit: usize,
    collect: bool, references: &mut Vec<ExpressionReference>,
    signals: &mut Vec<usize>,
) -> (result: Result<(usize, Option<Range<usize>>), (HeaderError, Range<usize>)>)
    requires
        index < _limit <= forms@.len(),
        form_region_ends_at(forms@, index as int, _limit as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> body_item_matches(source, forms@, index as int, _limit as int),
        final(references)@.len() >= old(references)@.len(),
        final(references)@.take(old(references)@.len() as int) == old(references)@,
        !collect ==> final(references)@ == old(references)@,
        !collect ==> final(signals)@ == old(signals)@,
        final(signals)@.len() >= old(signals)@.len(),
        final(signals)@.take(old(signals)@.len() as int) == old(signals)@,
        forall|i: int| old(references)@.len() <= i < final(references)@.len()
            ==> expression_reference_in_source(source, forms@, #[trigger] final(references)@[i]),
        result matches Ok((next, rhs)) ==> index < next <= _limit
            && following_direct_form(forms@, index as int, next as int)
            && forms@[index as int] is List && forms@[index as int]->List_end == next
            && match rhs {
                Some(rhs) => body_head_at(source, forms@, index + 1, next as int, BodyHead::Def)
                    && targets_match(forms@, index + 2, next as int, rhs.start as int)
                    && rhs.start < rhs.end == next && after_form(forms@, rhs.start as int) == next
                    && expression_forest(source, forms@, rhs.start as int, rhs.end as int)
                    && (collect ==> final(references)@ == old(references)@ +
                        expression_references(source, forms@, rhs.start as int, rhs.end as int))
                    && (collect ==> final(signals)@ == old(signals)@
                        + expression_signals(source, forms@, rhs.start as int, rhs.end as int)),
                None => !body_head_at(source, forms@, index + 1, next as int, BodyHead::Def)
                    && final(references)@ == old(references)@
                    && final(signals)@ == old(signals)@,
            },
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
    let rhs = inspect_body_arguments(source, forms, first, end, closing, kind, collect, references, signals)?;
    proof { node_end_is_following_direct_form(forms@, index as int, end as int); }
    Ok((end, rhs))
}

/// 指定した位置より前にある直接の本体項目がすべて文法に従うことを表す。
#[verifier::opaque]
pub(super) open spec fn body_items_before(
    source: &str, forms: Seq<Form>, start: int, end: int, cursor: int,
) -> bool {
    forall|index: int| #[trigger] direct_form_in_range(forms, start, end, index) && index < cursor
        ==> body_item_matches(source, forms, index, end)
}

/// 指定したフォームが本体直下の展開呼び出しであることを表す。
pub closed spec fn routine_expansion_at(source: &str, forms: Seq<Form>, start: int, end: int, item: int) -> bool {
    &&& direct_form_in_range(forms, start, end, item)
    &&& forms[item] is List
    &&& body_head_at(source, forms, item + 1, forms[item]->List_end as int, BodyHead::Expand)
}

/// 回路本体の直下にある一つのマクロ呼び出し。
#[derive(Debug, Eq, PartialEq)]
pub struct RoutineExpansionSite {
    /// 元の構文木で呼び出し全体のリストを指す添字。
    pub form: usize,
    /// 呼び出し全体が占める元入力の半開バイト範囲。
    pub span: Range<usize>,
    /// 呼び出し先の参照が占める元入力の半開バイト範囲。
    pub callee: Range<usize>,
    /// 引数の部分木を並べた、元の構文木の半開区間。
    pub arguments: Range<usize>,
}

/// 列挙結果の呼び出し先と引数範囲が、元の構文木に対応することを表す。
pub open spec fn routine_expansion_site_at(
    source: &str, forms: Seq<Form>, start: int, stop: int, site: RoutineExpansionSite,
) -> bool {
    let item = site.form as int;
    &&& routine_expansion_at(source, forms, start, stop, item)
    &&& site.span == form_span(forms[item])
    &&& forms[item] is List
    &&& item + 2 < forms[item]->List_end <= forms.len()
    &&& forms[item + 2] is Atom && reference_atom(forms[item + 2]->Atom_kind)
    &&& expression_region(forms, item + 3, forms[item]->List_end as int)
    &&& site.callee == form_span(forms[item + 2])
    &&& site.arguments.start == item + 3
    &&& site.arguments.end == forms[item]->List_end
    &&& site.arguments.start <= site.arguments.end <= stop
}

/// 今回走査した範囲にある展開呼び出しが、返り値に過不足なく含まれることを表す。
pub open spec fn next_expansion_site_matches(
    source: &str, forms: Seq<Form>, start: int, stop: int, from: int, next: int, result: Option<RoutineExpansionSite>,
) -> bool {
    match result {
        Some(site) => {
            &&& from <= site.form
            &&& routine_expansion_site_at(source, forms, start, stop, site)
            &&& next == site.arguments.end && site.form < next
            &&& forall|item: int| from <= item < next && #[trigger] routine_expansion_at(source, forms, start, stop, item)
                ==> item == site.form
        },
        None => next == stop
            && forall|item: int| from <= item ==> !#[trigger] routine_expansion_at(source, forms, start, stop, item),
    }
}

/// 展開待ちの範囲が、指定された本体の最初の展開フォームに対応することを表す。
pub closed spec fn expansion_body_region_matches(
    source: &str, syntax: &CircuitForms, entry: int, region: Option<(usize, usize)>,
) -> bool {
    let entries = syntax.entries@;
    let forms = syntax.forms@;
    &&& region matches Some((start, end)) ==>
        start <= end <= forms.len() && form_region_ends_at(forms, start as int, end as int)
            && body_items_before(source, forms, start as int, end as int, end as int)
    &&& if 0 <= entry < entries.len() && entries[entry].head is ModulePart {
        let form = entries[entry].form as int;
        region matches Some((start, end)) && start == form + 3 && forms[form] is List
            && end == forms[form]->List_end
    } else {
        (region.is_none() && routine_layout_matches(source, syntax, entry, None))
            || exists|layout: RoutineLayout| #[trigger] routine_layout_matches(source, syntax, entry, Some(layout))
                && region == Some((layout.body, layout.end))
    }
}

fn expansion_body_region(source: &str, syntax: &CircuitForms, entry: usize) -> (region: Option<(usize, usize)>)
    requires circuit_index_matches(source, syntax.forms@, syntax.entries@),
        complete_list_indices(syntax.forms@), nested_list_indices(syntax.forms@),
    ensures expansion_body_region_matches(source, syntax, entry as int, region),
{
    if entry < syntax.entries.len() && matches!(syntax.entries[entry].head, Head::ModulePart) {
        let form = syntax.entries[entry].form;
        let forms = syntax.forms.as_slice();
        proof {
            indexed_entry_evidence(source, forms@, syntax.entries@, entry as int);
            reveal(super::form_has_head);
            reveal(header_arguments_match);
        }
        let Form::List { end: stop, .. } = &forms[form] else { proof { assert(false); } return None; };
        proof {
            let after = choose|after: int| #[trigger] routine_signature_matches(source, forms@, form + 2, *stop as int, Head::ModulePart, after)
                && body_items_before(source, forms@, after, *stop as int, *stop as int);
            reveal(body_items_before);
            assert(after == form + 3);
        }
        Some((form + 3, *stop))
    } else {
        match routine_layout(source, syntax, entry) {
            Some(layout) => {
                proof { reveal(body_items_before); }
                Some((layout.body, layout.end))
            },
            None => None,
        }
    }
}

pub closed spec fn routine_expansion_evidence(source: &str, syntax: &CircuitForms, entry: int, span: Option<Range<usize>>) -> bool {
    let forms = syntax.forms@;
    (expansion_body_region_matches(source, syntax, entry, None) && span.is_none())
        || exists|start: usize, end: usize| #[trigger] expansion_body_region_matches(source, syntax, entry, Some((start, end))) && {
            let start = start as int;
            let end = end as int;
            match span {
                Some(span) => exists|item: int| #[trigger] routine_expansion_at(source, forms, start, end, item)
                    && span == form_span(forms[item])
                    && forall|prior: int| prior < item ==> !#[trigger] routine_expansion_at(source, forms, start, end, prior),
                None => forall|item: int| !#[trigger] routine_expansion_at(source, forms, start, end, item),
            }
        }
}

/// `func`、`module`、`module-part` の本体から、最初の `expand` の元ソース範囲を返す。
///
/// `syntax` には同じ `source` から得た厳格索引を渡す。他の種別や範囲外の項目では `None`。
/// 本体項目だけをたどる。定義の右辺やマクロの引数は走査しない。
///
/// # Panics
///
/// 手動で組み立てた構文木と索引の添字が互いに対応しない場合はパニックすることがある。
pub fn first_routine_expansion(source: &str, syntax: &CircuitForms, entry: usize) -> (span: Option<Range<usize>>)
    requires
        circuit_index_matches(source, syntax.forms@, syntax.entries@),
        complete_list_indices(syntax.forms@), nested_list_indices(syntax.forms@),
        form_spans_valid(source, syntax.forms@, source.spec_bytes().len() as int),
    ensures routine_expansion_evidence(source, syntax, entry as int, span),
        span matches Some(span) ==> span.start < span.end <= source.spec_bytes().len()
            && is_char_boundary(source.spec_bytes(), span.start as int)
            && is_char_boundary(source.spec_bytes(), span.end as int),
{
    let Some((start, stop)) = expansion_body_region(source, syntax, entry) else { return None; };
    let forms = syntax.forms.as_slice();
    proof {
        reveal(direct_form_in_range);
    }
    let (_, site) = scan_expansion_site(source, forms, start, stop, start);
    proof {
        reveal(direct_form_in_range);
        assert forall|prior: int| prior < start implies
            !#[trigger] routine_expansion_at(source, forms@, start as int, stop as int, prior) by {};
    }
    match site {
        Some(site) => Some(site.span),
        None => None,
    }
}

fn scan_expansion_site(source: &str, forms: &[Form], _start: usize, stop: usize, from: usize)
    -> (result: (usize, Option<RoutineExpansionSite>))
    requires
        _start <= from <= stop <= forms@.len(),
        form_region_ends_at(forms@, _start as int, stop as int),
        from < stop ==> direct_form_in_range(forms@, _start as int, stop as int, from as int),
        body_items_before(source, forms@, _start as int, stop as int, stop as int),
        complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        next_expansion_site_matches(source, forms@, _start as int, stop as int, from as int, result.0 as int, result.1),
        result.0 < stop ==> direct_form_in_range(forms@, _start as int, stop as int, result.0 as int),
        result.0 <= stop,
        result.1 matches Some(site) ==> result.0 == site.arguments.end
            && from < result.0
            && site.span.start < site.span.end <= source.spec_bytes().len()
            && is_char_boundary(source.spec_bytes(), site.span.start as int)
            && is_char_boundary(source.spec_bytes(), site.span.end as int)
            && site.callee.start < site.callee.end <= source.spec_bytes().len()
            && is_char_boundary(source.spec_bytes(), site.callee.start as int)
            && is_char_boundary(source.spec_bytes(), site.callee.end as int),
        result.1.is_none() ==> result.0 == stop,
{
    let mut at = from;
    while at < stop
        invariant
            body_items_before(source, forms@, _start as int, stop as int, stop as int),
            _start <= from <= at <= stop <= forms@.len(),
            form_region_ends_at(forms@, _start as int, stop as int),
            at < stop ==> direct_form_in_range(forms@, _start as int, stop as int, at as int),
            complete_list_indices(forms@), nested_list_indices(forms@),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            forall|prior: int| from <= prior < at ==> !#[trigger] routine_expansion_at(source, forms@, _start as int, stop as int, prior),
        decreases stop - at,
    {
        proof {
            reveal(body_items_before);
            assert(body_item_matches(source, forms@, at as int, stop as int));
        }
        let Form::List { span: item_span, end: next } = &forms[at] else {
            proof { assert(false); }
            unreachable!();
        };
        proof { reveal(form_spans_valid); }
        let Ok(kind) = read_body_item_head(source, forms, at + 1, *next, item_span.end - 1) else {
            proof { assert(false); }
            unreachable!();
        };
        proof {
            node_end_is_following_direct_form(forms@, at as int, *next as int);
            reveal(following_direct_form);
        }
        if matches!(kind, BodyHead::Expand) {
            proof {
                let head = choose|head: BodyHead| #[trigger] body_head_at(source, forms@, at + 1, *next as int, head)
                    && body_arguments_match(source, forms@, at + 2, *next as int, head);
                assert(head == BodyHead::Expand);
                assert(argument_matches(forms@, at + 2, *next as int, HeaderError::ExpectedReference));
            }
            let site = RoutineExpansionSite {
                form: at,
                span: item_span.start..item_span.end,
                callee: form_span_exec(&forms[at + 2]),
                arguments: at + 3..*next,
            };
            proof {
                reveal(following_direct_form);
                list_children_region(forms@, at as int, at + 3, *next as int);
                assert(routine_expansion_site_at(source, forms@, _start as int, stop as int, site));
                assert forall|item: int| from <= item < *next
                    && #[trigger] routine_expansion_at(source, forms@, _start as int, stop as int, item)
                    implies item == at by {};
            }
            return (*next, Some(site));
        }
        proof {
            reveal(following_direct_form);
            assert forall|prior: int| from <= prior < *next implies
                !#[trigger] routine_expansion_at(source, forms@, _start as int, stop as int, prior) by {
                if prior == at {
                    assert(!body_head_at(source, forms@, at + 1, *next as int, BodyHead::Expand));
                }
            };
        }
        at = *next;
    }
    proof {
        reveal(direct_form_in_range);
        assert forall|item: int| from <= item implies
            !#[trigger] routine_expansion_at(source, forms@, _start as int, stop as int, item) by {};
    }
    (stop, None)
}

/// 検査済みの回路本体からマクロ呼び出しを元ソース順に取り出す。
pub struct RoutineExpansionSites<'a> {
    source: &'a str,
    syntax: &'a CircuitForms,
    start: usize,
    stop: usize,
    current: usize,
}

impl<'a> RoutineExpansionSites<'a> {

    /// カーソルの呼び出し範囲と参照範囲が対応する元入力を表す。
    pub closed spec fn source_model(&self) -> &str { self.source }

    /// 呼び出しと引数の添字が参照する厳格索引を表す。
    pub closed spec fn syntax_model(&self) -> &CircuitForms { self.syntax }

    /// 本体全体が占める、元の構文木の半開区間を表す。
    pub closed spec fn body_model(&self) -> Range<usize> { self.start..self.stop }

    /// 次に調べる位置を表す。末尾は本体の終了添字に等しい。
    pub closed spec fn position_model(&self) -> usize { self.current }

    /// 確認済みの本体の中で、次に調べる位置が直下のフォームか末尾であることを表す。
    pub closed spec fn valid(&self) -> bool {
        let forms = self.syntax.forms@;
        &&& self.start <= self.current <= self.stop <= forms.len()
        &&& self.current < self.stop ==>
            direct_form_in_range(forms, self.start as int, self.stop as int, self.current as int)
        &&& form_region_ends_at(forms, self.start as int, self.stop as int)
        &&& body_items_before(self.source, forms, self.start as int, self.stop as int, self.stop as int)
        &&& complete_list_indices(forms) && nested_list_indices(forms)
        &&& form_spans_valid(self.source, forms, self.source.spec_bytes().len() as int)
    }

    /// 返した項目が未走査の先頭であり、残りの走査がその部分木の外から続くことを表す。
    pub open spec fn advances(&self, next: &Self, result: Option<RoutineExpansionSite>) -> bool {
        &&& next.source_model() == self.source_model() && next.syntax_model() == self.syntax_model()
        &&& next.body_model() == self.body_model()
        &&& next_expansion_site_matches(self.source_model(), self.syntax_model().forms@,
            self.body_model().start as int, self.body_model().end as int,
            self.position_model() as int, next.position_model() as int, result)
    }

    /// 呼び出しと引数の添字が参照する厳格索引を借りる。
    pub fn syntax(&self) -> (syntax: &'a CircuitForms)
        requires self.valid(),
        ensures syntax == self.syntax_model(), complete_list_indices(syntax.forms@),
            nested_list_indices(syntax.forms@),
            form_spans_valid(self.source_model(), syntax.forms@, self.source_model().spec_bytes().len() as int),
    {
        self.syntax
    }

    /// 次の展開呼び出しを返す。走査の末尾では `None` を返す。
    ///
    /// 本体の直下だけを調べ、マクロの引数や定義の右辺に含まれる構文へは降りない。
    ///
    /// # Panics
    ///
    /// カーソルに同じ本文から作った厳格索引を渡していない場合はパニックすることがある。
    pub fn next_site(&mut self) -> (site: Option<RoutineExpansionSite>)
        requires old(self).valid(),
        ensures final(self).valid(), old(self).advances(final(self), site),
            site matches Some(site) ==>
                site.arguments.start <= site.arguments.end <= final(self).syntax_model().forms@.len()
                    && site.span.start < site.span.end <= final(self).source_model().spec_bytes().len()
                    && is_char_boundary(final(self).source_model().spec_bytes(), site.span.start as int)
                    && is_char_boundary(final(self).source_model().spec_bytes(), site.span.end as int)
                    && site.callee.start < site.callee.end <= final(self).source_model().spec_bytes().len()
                    && is_char_boundary(final(self).source_model().spec_bytes(), site.callee.start as int)
                    && is_char_boundary(final(self).source_model().spec_bytes(), site.callee.end as int),
    {
        let (next, site) = scan_expansion_site(self.source, self.syntax.forms.as_slice(), self.start, self.stop, self.current);
        self.current = next;
        site
    }
}

/// 指定した回路本体を列挙するためのカーソルが先頭にあることを表す。
pub open spec fn routine_expansion_sites_match(
    source: &str, syntax: &CircuitForms, entry: int, sites: Option<RoutineExpansionSites>,
) -> bool {
    match sites {
        Some(sites) => sites.valid() && sites.source_model() == source && sites.syntax_model() == syntax
            && sites.position_model() == sites.body_model().start
            && expansion_body_region_matches(source, syntax, entry,
                Some((sites.body_model().start, sites.body_model().end))),
        None => expansion_body_region_matches(source, syntax, entry, None),
    }
}

/// `func`、`module`、`module-part` の本体の展開呼び出しを列挙する。
///
/// `syntax` には同じ `source` から得た厳格索引を渡す。他の種別や範囲外の項目では `None`。
/// 引数の範囲には元の構文木の部分木が並ぶ。次の引数へ進むときは、アトムなら一つ進み、リストなら `Form::List::end` へ進む。
///
/// # Panics
///
/// 手動で組み立てた構文木と索引の添字が互いに対応しない場合はパニックすることがある。
///
/// # Examples
///
/// ```
/// use circuitgame2_syntax::circuit::{index_headers, routine_expansion_sites};
///
/// let source = "(func f (in x) (out y) (expand ::make (expand ignored x)) (expand finish y))";
/// let syntax = index_headers(source)?;
/// let mut sites = routine_expansion_sites(source, &syntax, 0).unwrap();
/// let make = sites.next_site().unwrap();
/// let finish = sites.next_site().unwrap();
/// assert_eq!(&source[make.callee], "::make");
/// assert_eq!(&source[finish.callee], "finish");
/// assert!(make.arguments.end > make.arguments.start + 1);
/// assert!(sites.next_site().is_none());
/// # Ok::<(), circuitgame2_syntax::circuit::CircuitFormError>(())
/// ```
pub fn routine_expansion_sites<'a>(source: &'a str, syntax: &'a CircuitForms, entry: usize)
    -> (sites: Option<RoutineExpansionSites<'a>>)
    requires
        circuit_index_matches(source, syntax.forms@, syntax.entries@),
        complete_list_indices(syntax.forms@), nested_list_indices(syntax.forms@),
        form_spans_valid(source, syntax.forms@, source.spec_bytes().len() as int),
    ensures routine_expansion_sites_match(source, syntax, entry as int, sites),
        sites.is_some() <==> entry < syntax.entries@.len() && {
            let head = syntax.entries@[entry as int].head;
            head is Func || head is Module || head is ModulePart
        },
        sites matches Some(sites) ==> sites.valid() && sites.source_model() == source && sites.syntax_model() == syntax,
{
    let Some((start, stop)) = expansion_body_region(source, syntax, entry) else { return None; };
    proof { reveal(direct_form_in_range); }
    Some(RoutineExpansionSites { source, syntax, start, stop, current: start })
}


/// 本体項目列のうち最初に失敗した項目の診断と、それより前の項目の妥当性を表す。
pub(super) open spec fn body_error(
    source: &str, forms: Seq<Form>, start: int, end: int, error: (HeaderError, Range<usize>),
) -> bool {
    exists|index: int| #[trigger] direct_form_in_range(forms, start, end, index)
        && body_items_before(source, forms, start, end, index)
        && body_item_error(source, forms, index, end, error)
}

proof fn body_errors_agree(
    source: &str, forms: Seq<Form>, start: int, end: int,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        body_error(source, forms, start, end, left),
        body_error(source, forms, start, end, right),
    ensures left == right,
{
    let a = choose|index: int| #[trigger] direct_form_in_range(forms, start, end, index)
        && body_items_before(source, forms, start, end, index)
        && body_item_error(source, forms, index, end, left);
    let b = choose|index: int| #[trigger] direct_form_in_range(forms, start, end, index)
        && body_items_before(source, forms, start, end, index)
        && body_item_error(source, forms, index, end, right);
    reveal(body_items_before);
    if a < b {
        body_item_match_excludes_error(source, forms, a, end, left);
    } else if b < a {
        body_item_match_excludes_error(source, forms, b, end, right);
    } else {
        body_item_errors_agree(source, forms, a, end, left, right);
    }
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

#[verifier::opaque]
pub(super) open spec fn flat_definition_matches(
    source: &str, forms: Seq<Form>, start: int, end: int, row: BuildDefinition,
    references: Seq<ExpressionReference>, signals: Seq<usize>,
) -> bool {
    let item = row.form as int;
    let first = row.references.start as int;
    let last = row.references.end as int;
    let value = row.expression.start as int;
    let stop = row.expression.end as int;
    &&& is_definition_at(source, forms, start, end, item)
    &&& stop == forms[item]->List_end
    &&& targets_match(forms, item + 2, stop, value)
    &&& value < stop && after_form(forms, value) == stop
    &&& expression_forest(source, forms, value, stop)
    &&& 0 <= first <= last <= references.len()
    &&& 0 <= row.signals.start <= row.signals.end <= signals.len()
    &&& signals[row.signals.start as int..row.signals.end as int] == expression_signals(source, forms, value, stop)
    &&& references[first..last] == expression_references(source, forms, value, stop)
    &&& forall|i: int| first <= i < last
        ==> expression_reference_in_source(source, forms, #[trigger] references[i])
}

/// 本体の検査済み部分にある定義が、平坦な配列の連続区間を占めることを表す。
#[verifier::opaque]
pub(super) open spec fn flat_body_matches(
    source: &str, forms: Seq<Form>, start: int, end: int, cursor: int,
    rows: Seq<BuildDefinition>, references: Seq<ExpressionReference>, signals: Seq<usize>, first: int, stop: int,
    first_signal: int, stop_signal: int,
) -> bool {
    &&& 0 <= first <= stop <= references.len()
    &&& stop == if rows.len() == 0 { first } else { rows.last().references.end as int }
    &&& 0 <= first_signal <= stop_signal <= signals.len()
    &&& stop_signal == if rows.len() == 0 { first_signal } else { rows.last().signals.end as int }
    &&& forall|i: int| 0 <= i < rows.len() ==> {
        let row = #[trigger] rows[i];
        &&& flat_definition_matches(source, forms, start, end, row, references, signals)
        &&& row.form < cursor
        &&& first_signal <= row.signals.start <= row.signals.end <= stop_signal
        &&& row.signals.start == if i == 0 { first_signal } else { rows[i - 1].signals.end as int }
        &&& first <= row.references.start <= row.references.end <= stop
        &&& row.references.start == if i == 0 { first } else { rows[i - 1].references.end as int }
    }
    &&& forall|i: int, j: int| 0 <= i < j < rows.len()
        ==> (#[trigger] rows[i]).form < (#[trigger] rows[j]).form
    &&& forall|i: int| #[trigger] is_definition_at(source, forms, start, end, i) && i < cursor
        ==> exists|j: int| 0 <= j < rows.len() && (#[trigger] rows[j]).form == i
}

/// 同じ UTF-8 本文では、同じ本体の宣言・参照範囲を再利用できる。
pub(super) proof fn flat_body_transfers_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, start: int, end: int, cursor: int,
    rows: Seq<BuildDefinition>, references: Seq<ExpressionReference>, signals: Seq<usize>,
    first: int, stop: int, first_signal: int, stop_signal: int,
)
    requires
        left.spec_bytes() == right.spec_bytes(),
        flat_body_matches(left, forms, start, end, cursor, rows, references, signals,
            first, stop, first_signal, stop_signal),
    ensures
        flat_body_matches(right, forms, start, end, cursor, rows, references, signals,
            first, stop, first_signal, stop_signal),
{
    reveal(flat_body_matches);
    assert forall|i: int| is_definition_at(right, forms, start, end, i) && i < cursor
        implies exists|j: int| 0 <= j < rows.len() && (#[trigger] rows[j]).form == i by {
        assert(is_definition_at(left, forms, start, end, i));
    };
    assert forall|i: int| 0 <= i < rows.len() implies
        flat_definition_matches(right, forms, start, end, #[trigger] rows[i], references, signals) by {
        let row = rows[i];
        assert(flat_definition_matches(left, forms, start, end, row, references, signals));
        reveal(flat_definition_matches);
        let lo = row.expression.start as int;
        let hi = row.expression.end as int;
        super::expression_forest::expression_forest_agrees_on_bytes(
            left, right, forms, lo, hi, (HeaderError::ExpectedList, 0..0),
        );
        super::expression_forest::expression_collections_agree_on_bytes(left, right, forms, lo, hi);
        assert forall|j: int| row.references.start <= j < row.references.end
            implies expression_reference_in_source(right, forms, #[trigger] references[j]) by {
            assert(expression_reference_in_source(left, forms, references[j]));
        };
    };
}

/// 平坦な本体の一行から、参照範囲と元ソースの根拠を取り出す。
pub(super) proof fn flat_body_reference_boundaries(
    source: &str, forms: Seq<Form>, body: int, end: int, rows: Seq<BuildDefinition>,
    refs: Seq<ExpressionReference>, signals: Seq<usize>, first: int, stop: int, first_signal: int, stop_signal: int,
)
    requires flat_body_matches(source, forms, body, end, end, rows, refs, signals, first, stop, first_signal, stop_signal),
    ensures
        stop == if rows.len() == 0 { first } else { rows.last().references.end as int },
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).references.start
            == if i == 0 { first } else { rows[i - 1].references.end as int },
{
    reveal(flat_body_matches);
}

pub(super) proof fn flat_body_row_evidence(
    source: &str, forms: Seq<Form>, start: int, end: int,
    definitions: Seq<BuildDefinition>, references: Seq<ExpressionReference>, signals: Seq<usize>,
    first: int, stop: int, first_signal: int, stop_signal: int, index: int,
)
    requires
        flat_body_matches(source, forms, start, end, end, definitions, references, signals, first, stop, first_signal, stop_signal),
        0 <= index < definitions.len(),
    ensures
        first <= definitions[index].references.start <= definitions[index].references.end <= stop,
        first_signal <= definitions[index].signals.start <= definitions[index].signals.end <= stop_signal,
        signals[definitions[index].signals.start as int..definitions[index].signals.end as int]
            == expression_signals(source, forms, definitions[index].expression.start as int, definitions[index].expression.end as int),
        ({
            let row = definitions[index];
            let value = row.expression.start as int;
            let end = row.expression.end as int;
            &&& value < end <= forms.len()
            &&& after_form(forms, value) == end
            &&& expression_forest(source, forms, value, end)
            &&& references[row.references.start as int..row.references.end as int]
                == expression_references(source, forms, value, end)
        }),
        targets_match(forms, definitions[index].form + 2, definitions[index].expression.end as int,
            definitions[index].expression.start as int),
        forall|i: int| definitions[index].references.start <= i < definitions[index].references.end
            ==> expression_reference_in_source(source, forms, #[trigger] references[i]),
{
    reveal(flat_body_matches);
    let row = definitions[index];
    assert(flat_definition_matches(source, forms, start, end, row, references, signals));
    reveal(flat_definition_matches);
}

pub(super) proof fn flat_body_signal_cursor(
    source: &str, forms: Seq<Form>, start: int, end: int,
    rows: Seq<BuildDefinition>, references: Seq<ExpressionReference>, signals: Seq<usize>,
    first: int, stop: int, first_signal: int, stop_signal: int, cursor: int,
)
    requires
        flat_body_matches(source, forms, start, end, end, rows, references, signals, first, stop, first_signal, stop_signal),
        0 <= cursor <= rows.len(),
    ensures
        ({
            let previous = if cursor == 0 { first_signal } else { rows[cursor - 1].signals.end as int };
            if cursor == rows.len() { previous == stop_signal }
            else { previous == rows[cursor].signals.start }
        }),
{
    reveal(flat_body_matches);
    if cursor == rows.len() && cursor > 0 {
        assert(rows.last() == rows[cursor - 1]);
    }
}

/// 参照配列の末尾への追加は、検査済みの定義が指す区間を変えない。
proof fn keep_flat_definition(
    source: &str, forms: Seq<Form>, start: int, end: int, row: BuildDefinition,
    before: Seq<ExpressionReference>, references: Seq<ExpressionReference>,
    old_signals: Seq<usize>, signals: Seq<usize>,
)
    requires
        flat_definition_matches(source, forms, start, end, row, before, old_signals),
        before.len() <= references.len(),
        references.take(before.len() as int) == before,
        old_signals.len() <= signals.len(),
        signals.take(old_signals.len() as int) == old_signals,
    ensures flat_definition_matches(source, forms, start, end, row, references, signals),
{
    reveal(flat_definition_matches);
    let lo = row.references.start as int;
    let hi = row.references.end as int;
    assert(before[lo..hi] =~= references[lo..hi]);
    assert(old_signals[row.signals.start as int..row.signals.end as int]
        =~= signals[row.signals.start as int..row.signals.end as int]);
    assert forall|j: int| lo <= j < hi
        implies expression_reference_in_source(source, forms, #[trigger] references[j]) by {
        assert(references[j] == before[j]);
    };
}

proof fn extend_flat_body(
    source: &str, forms: Seq<Form>, start: int, end: int, index: int, next: int,
    rows: Seq<BuildDefinition>, old_refs: Seq<ExpressionReference>, refs: Seq<ExpressionReference>,
    old_signals: Seq<usize>, signals: Seq<usize>, first: int, first_signal: int,
    new_row: Option<BuildDefinition>,
)
    requires
        direct_form_in_range(forms, start, end, index),
        form_region_ends_at(forms, start, end),
        following_direct_form(forms, index, next),
        index < next <= end,
        flat_body_matches(source, forms, start, end, index, rows, old_refs, old_signals, first, old_refs.len() as int, first_signal, old_signals.len() as int),
        old_refs.len() <= refs.len(),
        refs.take(old_refs.len() as int) == old_refs,
        old_signals.len() <= signals.len(),
        signals.take(old_signals.len() as int) == old_signals,
        match new_row {
            Some(row) => flat_definition_matches(source, forms, start, end, row, refs, signals)
                && row.form == index && row.references.start == old_refs.len() && row.references.end == refs.len()
                && row.signals.start == old_signals.len() && row.signals.end == signals.len(),
            None => !is_definition_at(source, forms, start, end, index) && refs == old_refs && signals == old_signals,
        },
    ensures
        flat_body_matches(source, forms, start, end, next,
            if let Some(row) = new_row { rows.push(row) } else { rows }, refs, signals, first, refs.len() as int, first_signal, signals.len() as int),
{
    reveal(flat_body_matches);
    reveal(following_direct_form);
    let extended = if let Some(row) = new_row { rows.push(row) } else { rows };
    assert forall|i: int| 0 <= i < rows.len()
        implies flat_definition_matches(source, forms, start, end, #[trigger] rows[i], refs, signals) by {
        keep_flat_definition(source, forms, start, end, rows[i], old_refs, refs, old_signals, signals);
    };
    assert forall|i: int| #[trigger] is_definition_at(source, forms, start, end, i) && i < next
        implies exists|j: int| 0 <= j < extended.len() && (#[trigger] extended[j]).form == i by {
        if i < index {
            let j = choose|j: int| 0 <= j < rows.len() && (#[trigger] rows[j]).form == i;
            assert(extended[j] == rows[j]);
        } else {
            assert(i == index);
            assert(new_row is Some);
            assert(extended[rows.len() as int].form == i);
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
    collect: bool, rows: &mut BuildRows,
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
        final(rows).entry_ranges == old(rows).entry_ranges,
        final(rows).definitions@.len() >= old(rows).definitions@.len(),
        final(rows).definitions@.take(old(rows).definitions@.len() as int) == old(rows).definitions@,
        final(rows).references@.len() >= old(rows).references@.len(),
        final(rows).references@.take(old(rows).references@.len() as int) == old(rows).references@,
        final(rows).signals@.len() >= old(rows).signals@.len(),
        final(rows).signals@.take(old(rows).signals@.len() as int) == old(rows).signals@,
        collect && result.is_ok() ==> flat_body_matches(source, forms@, start as int, end as int, end as int,
            final(rows).definitions@.skip(old(rows).definitions@.len() as int), final(rows).references@, final(rows).signals@,
            old(rows).references@.len() as int, final(rows).references@.len() as int,
            old(rows).signals@.len() as int, final(rows).signals@.len() as int),
{
    let mut index = start;
    let ghost initial = *rows;
    let ghost first_def = rows.definitions@.len() as int;
    let _ref_start = rows.references.len();
    let _signal_start = rows.signals.len();
    proof {
        reveal(direct_form_in_range);
        reveal(body_items_before);
        reveal(flat_body_matches);
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
            initial == *old(rows),
            _ref_start == initial.references@.len(),
            first_def == initial.definitions@.len(),
            rows.entry_ranges == initial.entry_ranges,
            rows.definitions@.len() >= first_def,
            rows.definitions@.take(first_def) == initial.definitions@,
            rows.references@.len() >= _ref_start,
            rows.references@.take(_ref_start as int) == initial.references@,
            _signal_start == initial.signals@.len(),
            rows.signals@.len() >= _signal_start,
            rows.signals@.take(_signal_start as int) == initial.signals@,
            collect ==> flat_body_matches(source, forms@, start as int, end as int, index as int,
                rows.definitions@.skip(first_def), rows.references@, rows.signals@,
                _ref_start as int, rows.references@.len() as int, _signal_start as int, rows.signals@.len() as int),
        decreases end - index,
    {
        assert(form_region_ends_at(forms@, index as int, end as int));
        let ghost prior_rows = rows.definitions@.skip(first_def);
        let ghost prior_refs = rows.references@;
        let reference_start = rows.references.len();
        let signal_start = rows.signals.len();
        let ghost prior_signals = rows.signals@;
        let (next, rhs) = match read_body_item(source, forms, index, end, collect, &mut rows.references, &mut rows.signals) {
            Ok(result) => result,
            Err(error) => {
                assert(!body_items_before(source, forms@, start as int, end as int, end as int)) by {
                    reveal(body_items_before);
                };
                return Err(error);
            }
        };
        if collect {
            if let Some(expression) = rhs {
                let row = BuildDefinition {
                    form: index,
                    expression,
                    references: reference_start..rows.references.len(),
                    signals: signal_start..rows.signals.len(),
                };
                proof {
                    assert(flat_definition_matches(source, forms@, start as int, end as int, row, rows.references@, rows.signals@)) by {
                        reveal(flat_definition_matches);
                        assert(rows.references@[reference_start as int..rows.references@.len() as int]
                            =~= expression_references(source, forms@, row.expression.start as int, row.expression.end as int));
                        assert(rows.signals@[signal_start as int..rows.signals@.len() as int]
                            =~= expression_signals(source, forms@, row.expression.start as int, row.expression.end as int));
                    }
                    extend_flat_body(source, forms@, start as int, end as int, index as int, next as int,
                        prior_rows, prior_refs, rows.references@, prior_signals, rows.signals@, _ref_start as int, _signal_start as int, Some(row));
                }
                let ghost expected = prior_rows.push(row);
                rows.definitions.push(row);
                assert(rows.definitions@.skip(first_def) =~= expected);
            } else {
                proof {
                    extend_flat_body(source, forms@, start as int, end as int, index as int, next as int,
                        prior_rows, prior_refs, rows.references@, prior_signals, rows.signals@, _ref_start as int, _signal_start as int, None);
                }
            }
        }
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

proof fn body_item_transfers_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, index: int, limit: int,
    error: (HeaderError, Range<usize>),
)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures
        body_item_matches(left, forms, index, limit) ==> body_item_matches(right, forms, index, limit),
        body_item_error(left, forms, index, limit, error) ==> body_item_error(right, forms, index, limit, error),
{
    if 0 <= index < limit <= forms.len() && forms[index] is List {
        let end = forms[index]->List_end as int;
        let first = index + 2;
        let span_end = form_span(forms[index]).end;
        let closing = if span_end > 0 { (span_end - 1) as usize } else { 0usize };
        assert forall|value: int| #[trigger] targets_match(forms, first, end, value) implies {
            &&& expression_forest(left, forms, value, end) == expression_forest(right, forms, value, end)
            &&& definition_rhs_error(left, forms, value, end, closing, error)
                == definition_rhs_error(right, forms, value, end, closing, error)
        } by {
            super::expression_forest::expression_forest_agrees_on_bytes(left, right, forms, value, end, error);
        };
        assert forall|kind: BodyHead| #[trigger] body_head_at(left, forms, index + 1, end, kind)
            == #[trigger] body_head_at(right, forms, index + 1, end, kind) by {};
        assert forall|kind: BodyHead| #[trigger] body_arguments_match(left, forms, first, end, kind)
            == #[trigger] body_arguments_match(right, forms, first, end, kind) by {
            if kind is Def {
                assert(body_arguments_match(left, forms, first, end, kind) == body_arguments_match(right, forms, first, end, kind));
            }
        };
        assert forall|kind: BodyHead| #[trigger] body_arguments_error(left, forms, first, end, closing, kind, error)
            == #[trigger] body_arguments_error(right, forms, first, end, closing, kind, error) by {
            if kind is Def {
                assert(body_arguments_error(left, forms, first, end, closing, kind, error)
                    == body_arguments_error(right, forms, first, end, closing, kind, error));
            }
        };
        if body_item_matches(left, forms, index, limit) {
            let kind = choose|kind: BodyHead| #[trigger] body_head_at(left, forms, index + 1, end, kind)
                && body_arguments_match(left, forms, first, end, kind);
            assert(body_head_at(right, forms, index + 1, end, kind)
                && body_arguments_match(right, forms, first, end, kind));
        }
        if body_item_error(left, forms, index, limit, error) {
            if exists|kind: BodyHead| #[trigger] body_head_at(left, forms, index + 1, end, kind) {
                let kind = choose|kind: BodyHead| #[trigger] body_head_at(left, forms, index + 1, end, kind)
                    && body_arguments_error(left, forms, first, end, closing, kind, error);
                assert(body_head_at(right, forms, index + 1, end, kind));
                assert(body_arguments_error(right, forms, first, end, closing, kind, error));
            } else {
                assert forall|kind: BodyHead| !#[trigger] body_head_at(right, forms, index + 1, end, kind) by {
                    assert(!body_head_at(left, forms, index + 1, end, kind));
                };
            }
        }
    }
}

/// 同じ UTF-8 本文と構文木なら、本体の文法判定と最初の診断が一致する。
pub(super) proof fn routine_body_agrees_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, start: int, end: int,
    error: (HeaderError, Range<usize>),
)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures
        body_items_before(left, forms, start, end, end) == body_items_before(right, forms, start, end, end),
        body_error(left, forms, start, end, error) == body_error(right, forms, start, end, error),
{
    assert forall|index: int| #[trigger] direct_form_in_range(forms, start, end, index) implies {
        &&& body_item_matches(left, forms, index, end) == body_item_matches(right, forms, index, end)
        &&& body_item_error(left, forms, index, end, error) == body_item_error(right, forms, index, end, error)
    } by {
        body_item_transfers_on_bytes(left, right, forms, index, end, error);
        body_item_transfers_on_bytes(right, left, forms, index, end, error);
    };
    assert forall|stop: int| #[trigger] body_items_before(left, forms, start, end, stop)
        == #[trigger] body_items_before(right, forms, start, end, stop) by {
        reveal(body_items_before);
    };
}

/// 署名を優先し、本体ではソース順で最初の違反を診断するため、種別と範囲が一意に定まる。
pub(super) proof fn routine_arguments_errors_agree(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, head: Head,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        routine_arguments_error(source, forms, first, end, closing, head, left),
        routine_arguments_error(source, forms, first, end, closing, head, right),
    ensures left == right,
{
    if exists|body: int| #[trigger] routine_signature_matches(source, forms, first, end, head, body) {
        let body = choose|body: int| #[trigger] routine_signature_matches(source, forms, first, end, head, body);
        routine_signature_match_excludes_error(source, forms, first, end, closing, head, body, left);
        routine_signature_match_excludes_error(source, forms, first, end, closing, head, body, right);
        let left_body = choose|body: int| #[trigger] routine_signature_matches(source, forms, first, end, head, body)
            && body_error(source, forms, body, end, left);
        let right_body = choose|body: int| #[trigger] routine_signature_matches(source, forms, first, end, head, body)
            && body_error(source, forms, body, end, right);
        routine_signature_after_agrees(source, forms, first, end, head, left_body, right_body);
        body_errors_agree(source, forms, left_body, end, left, right);
    } else {
        routine_signature_errors_agree(source, forms, first, end, closing, head, left, right);
    }
}

/// 関数、モジュール、モジュール断片の署名と本体を順に検査する。
///
/// # Errors
///
/// 署名から本体へ順に検査し、最初の違反の種別と UTF-8 バイト範囲を返す。
pub(super) fn validate_routine_arguments(
    source: &str, forms: &[Form], first: usize, end: usize, closing: usize, head: Head,
    collect: bool, rows: &mut BuildRows,
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
        final(rows).entry_ranges == old(rows).entry_ranges,
        final(rows).definitions@.len() >= old(rows).definitions@.len(),
        final(rows).definitions@.take(old(rows).definitions@.len() as int) == old(rows).definitions@,
        final(rows).references@.len() >= old(rows).references@.len(),
        final(rows).references@.take(old(rows).references@.len() as int) == old(rows).references@,
        final(rows).signals@.len() >= old(rows).signals@.len(),
        final(rows).signals@.take(old(rows).signals@.len() as int) == old(rows).signals@,
        collect && result.is_ok() ==>
            exists|body: int| #[trigger] routine_signature_matches(source, forms@, first as int, end as int, head, body)
                && flat_body_matches(source, forms@, body, end as int, end as int,
                    final(rows).definitions@.skip(old(rows).definitions@.len() as int), final(rows).references@, final(rows).signals@,
                    old(rows).references@.len() as int, final(rows).references@.len() as int,
                    old(rows).signals@.len() as int, final(rows).signals@.len() as int),
{
    let body = read_routine_signature(source, forms, first, end, closing, head)?;
    assert(routine_signature_matches(source, forms@, first as int, end as int, head, body as int));
    assert(form_region_ends_at(forms@, body as int, end as int));
    validate_body(source, forms, body, end, collect, rows)
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

proof fn same_definition_prefix(
    source: &str, forms: Seq<Form>, start: int, end: int,
    flat: Seq<BuildDefinition>, references: Seq<ExpressionReference>, signals: Seq<usize>,
    first: int, stop: int, first_signal: int, stop_signal: int,
    nested: Seq<DefinitionReferences>, count: int,
)
    requires
        flat_body_matches(source, forms, start, end, end, flat, references, signals,
            first, stop, first_signal, stop_signal),
        definitions_before(source, forms, start, end, end, nested),
        0 <= count <= flat.len(),
        count <= nested.len(),
    ensures
        forall|i: int| 0 <= i < count ==> (#[trigger] flat[i]).form == (#[trigger] nested[i]).definition,
    decreases count,
{
    if count == 0 {
        return;
    }
    let i = count - 1;
    // 両列は同じ定義を元ソース順に網羅するので、先行項目が一致すれば次の項目も一致する。
    same_definition_prefix(source, forms, start, end, flat, references, signals,
        first, stop, first_signal, stop_signal, nested, i);
    reveal(flat_body_matches);
    reveal(definitions_before);
    let a = flat[i].form;
    let b = nested[i].definition;
    assert(is_definition_at(source, forms, start, end, a as int)) by {
        reveal(flat_definition_matches);
    };
    assert(is_definition_at(source, forms, start, end, b as int));
    let j = choose|j: int| 0 <= j < nested.len() && (#[trigger] nested[j]).definition == a;
    let k = choose|k: int| 0 <= k < flat.len() && (#[trigger] flat[k]).form == b;
    if j < i {
        assert(flat[j].form == nested[j].definition);
        assert(flat[j].form < a);
    }
    if k < i {
        assert(flat[k].form == nested[k].definition);
        assert(nested[k].definition < b);
    }
    if j > i {
        assert(b < a);
    }
    if k > i {
        assert(a < b);
    }
    assert(a == b);
}

pub(super) proof fn same_body_references(
    source: &str, forms: Seq<Form>, start: int, end: int,
    flat: Seq<BuildDefinition>, references: Seq<ExpressionReference>, signals: Seq<usize>,
    first: int, stop: int, first_signal: int, stop_signal: int, nested: Seq<DefinitionReferences>,
)
    requires
        flat_body_matches(source, forms, start, end, end, flat, references, signals,
            first, stop, first_signal, stop_signal),
        definitions_before(source, forms, start, end, end, nested),
    ensures
        flat.len() == nested.len(),
        forall|i: int| 0 <= i < flat.len() ==> {
            let a = #[trigger] flat[i];
            let b = #[trigger] nested[i];
            &&& a.form == b.definition
            &&& a.expression == b.expression
            &&& first <= a.references.start <= a.references.end <= stop
            &&& references[a.references.start as int..a.references.end as int] == b.references@
        },
{
    let common = if flat.len() < nested.len() { flat.len() } else { nested.len() } as int;
    same_definition_prefix(source, forms, start, end, flat, references, signals,
        first, stop, first_signal, stop_signal, nested, common);
    reveal(flat_body_matches);
    reveal(flat_definition_matches);
    reveal(definitions_before);
    if common < flat.len() {
        let a = flat[common].form;
        assert(is_definition_at(source, forms, start, end, a as int));
        let j = choose|j: int| 0 <= j < nested.len() && (#[trigger] nested[j]).definition == a;
        assert(flat[j].form == a);
        assert(flat[j].form < a);
    }
    if common < nested.len() {
        let b = nested[common].definition;
        assert(is_definition_at(source, forms, start, end, b as int));
        let j = choose|j: int| 0 <= j < flat.len() && (#[trigger] flat[j]).form == b;
        assert(nested[j].definition == b);
        assert(nested[j].definition < b);
    }
    assert forall|i: int| 0 <= i < flat.len() implies {
        let a = #[trigger] flat[i];
        let b = #[trigger] nested[i];
        &&& a.form == b.definition
        &&& a.expression == b.expression
        &&& first <= a.references.start <= a.references.end <= stop
        &&& references[a.references.start as int..a.references.end as int] == b.references@
    } by {
        let a = flat[i];
        let b = nested[i];
        assert(a.form == b.definition);
        assert(a.expression.end == b.expression.end);
        let target = a.form as int + 2;
        let end = a.expression.end as int;
        assert(targets_match(forms, target, end, a.expression.start as int));
        assert(targets_match(forms, target, end, b.expression.start as int));
    };
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
                &mut Vec::new(),
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
            &mut Vec::new(),
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
            &mut Vec::new(),
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
            &mut Vec::new(),
        )
        .unwrap_err();
        assert_eq!(kind, HeaderError::ExpectedExpression);
        assert_eq!(&source[references[0].span.clone()], "first");
        assert_eq!(&source[references[1].span.clone()], "outer");
        assert_eq!(references.len(), 2);
    }
}
