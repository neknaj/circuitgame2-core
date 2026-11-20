//! `concat` の先頭語と、直下の引数が並ぶ構文木範囲を取り出す。

use super::expressions::read_expression_head;
use super::*;

#[cfg(verus_only)]
use super::expression_forest::{
    direct_name_in_signal_index, expression_forest, expression_region, first_expression_children,
    list_child_signals,
};
#[cfg(verus_only)]
use super::expressions::{argument_matches, arguments_match, expression_child_range, list_head_matches, same_expression_head};

verus! {

/// `concat` の直下の引数が、一つ以上の式を含む範囲を占めることを表す。
///
/// 先頭語と引数の位置を表す契約。各引数の文法は厳格解析の契約から得られる。
pub closed spec fn concat_arguments_match(
    source: &str, forms: Seq<Form>, root: int, arguments: Range<usize>,
) -> bool {
    &&& 0 <= root < forms.len()
    &&& forms[root] is List
    &&& root + 2 == arguments.start < arguments.end == forms[root]->List_end <= forms.len()
    &&& argument_matches(forms, root + 1, arguments.end as int, HeaderError::ExpectedReference)
    &&& list_head_matches(source, forms, root + 1, Some(ExpressionHead::Concat))
    &&& {
        let span = form_span(forms[root + 1]);
        &&& is_char_boundary(source.spec_bytes(), span.start as int)
        &&& is_char_boundary(source.spec_bytes(), span.end as int)
    }
}

/// `concat` の先頭語に続く引数列を、構文木上の半開範囲で返す。
///
/// 先頭語と引数全体の範囲を調べ、対応する非空の引数列がなければ `None` を返す。
/// 厳格解析で得た本文と構文木を渡し、各引数を [`next_call_argument`](super::next_call_argument) でたどる。
///
/// # Examples
///
/// 入れ子の `slice` は直下の引数一つとして扱う。
///
/// ```
/// use circuitgame2_syntax::circuit::{concat_argument_range, next_call_argument};
/// use circuitgame2_syntax::parse;
///
/// let source = "(concat lo (slice hi 0 2) 1)";
/// let forms = parse(source).unwrap();
/// let arguments = concat_argument_range(source, &forms, 0).unwrap();
/// let first = next_call_argument(&forms, arguments.clone()).unwrap();
/// let second = next_call_argument(&forms, first.end..arguments.end).unwrap();
/// let third = next_call_argument(&forms, second.end..arguments.end).unwrap();
/// assert_eq!([first, second, third], [2..3, 3..8, 8..9]);
/// ```
pub fn concat_argument_range(source: &str, forms: &[Form], root: usize) -> (result: Option<Range<usize>>)
    ensures forall|range: Range<usize>| #[trigger] concat_arguments_match(source, forms@, root as int, range)
        <==> result == Some(range),
{
    let range = read_concat_argument_range(source, forms, root);
    assert forall|expected: Range<usize>| #[trigger] concat_arguments_match(source, forms@, root as int, expected)
        <==> range == Some(expected) by {
        if concat_arguments_match(source, forms@, root as int, expected) {
            assert(range->Some_0.start == expected.start && range->Some_0.end == expected.end);
        }
    };
    range
}

/// 同じ連接式から得る引数範囲は一意に定まる。
pub proof fn concat_argument_ranges_agree(
    source: &str, forms: Seq<Form>, root: int, left: Range<usize>, right: Range<usize>,
)
    requires concat_arguments_match(source, forms, root, left), concat_arguments_match(source, forms, root, right),
    ensures left == right,
{
}

pub(super) proof fn ordinary_head_excludes_concat(
    source: &str, forms: Seq<Form>, root: int, range: Range<usize>,
)
    requires list_head_matches(source, forms, root + 1, None), concat_arguments_match(source, forms, root, range),
    ensures false,
{
    same_expression_head(source, forms, root + 1, None, Some(ExpressionHead::Concat));
}

fn read_concat_argument_range(source: &str, forms: &[Form], root: usize) -> (result: Option<Range<usize>>)
    ensures
        result matches Some(range) ==> concat_arguments_match(source, forms@, root as int, range),
        (exists|range: Range<usize>| #[trigger] concat_arguments_match(source, forms@, root as int, range)) ==> result.is_some(),
{
    if root >= forms.len() {
        return None;
    }
    let Form::List { end: list_end, .. } = &forms[root] else { return None; };
    let end = *list_end;
    if end > forms.len() || end <= root || end - root <= 2 {
        return None;
    }
    let head = root + 1;
    let Form::Atom { kind: head_kind, span: head_span } = &forms[head] else { return None; };
    if !super::clauses::is_reference(*head_kind)
        || head_span.start >= head_span.end || head_span.end > source.as_bytes().len()
        || !source.is_char_boundary(head_span.start) || !source.is_char_boundary(head_span.end)
    {
        return None;
    }
    let found = read_expression_head(source, &forms[head]);
    if matches!(found, Some(ExpressionHead::Concat)) {
        Some((head + 1)..end)
    } else {
        proof {
            if exists|range: Range<usize>| #[trigger] concat_arguments_match(source, forms@, root as int, range) {
                let range = choose|range: Range<usize>| #[trigger] concat_arguments_match(source, forms@, root as int, range);
                assert(list_head_matches(source, forms@, head as int, found));
                same_expression_head(source, forms@, head as int, found, Some(ExpressionHead::Concat));
            }
        }
        None
    }
}

/// 厳格構文の `concat` の引数範囲は、同じ文法に適合し、直下の式を順にたどれる。
pub proof fn concat_arguments_evidence(
    source: &str, forms: Seq<Form>, root: int, end: int, arguments: Range<usize>,
)
    requires
        concat_arguments_match(source, forms, root, arguments),
        expression_forest(source, forms, root, end),
        root < end <= forms.len(),
        nested_list_indices(forms),
    ensures
        arguments.start == root + 2 < arguments.end == forms[root]->List_end <= end,
        expression_forest(source, forms, arguments.start as int, arguments.end as int),
        expression_region(forms, arguments.start as int, arguments.end as int),
        direct_form_in_range(forms, arguments.start as int, arguments.end as int, arguments.start as int),
        form_region_ends_at(forms, arguments.start as int, arguments.end as int),
{
    first_expression_children(source, forms, root, end);
    let stop = forms[root]->List_end as int;
    let (first, last) = choose|first: int, last: int|
        #[trigger] expression_child_range(source, forms, root, stop, first, last)
        && expression_forest(source, forms, first, last);
    let builtin = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, root + 1, head)
        && arguments_match(forms, root + 2, stop, head, first, last);
    same_expression_head(source, forms, root + 1, builtin, Some(ExpressionHead::Concat));
    super::call_shapes::list_children_region(forms, root, first, last);
    reveal(direct_form_in_range);
}

/// 現在の引数の直後が、列の末尾または次の直接の引数であることを示す。
pub proof fn following_concat_argument(
    source: &str, forms: Seq<Form>, root: int, arguments: Range<usize>, current: usize, next: usize,
)
    requires
        concat_arguments_match(source, forms, root, arguments),
        nested_list_indices(forms),
        direct_form_in_range(forms, arguments.start as int, arguments.end as int, current as int),
        current < next <= arguments.end,
        next == match forms[current as int] {
            Form::List { end, .. } => end as int,
            Form::Atom { .. } => current + 1,
        },
    ensures
        following_direct_form(forms, current as int, next as int),
        next < arguments.end ==> direct_form_in_range(forms, arguments.start as int, arguments.end as int, next as int),
{
    node_end_is_following_direct_form(forms, current as int, next as int);
    reveal(following_direct_form);
    assert(form_region_ends_at(forms, arguments.start as int, arguments.end as int));
}

/// `concat` の直下にある裸の信号名を、同じ定義の信号索引に結び付ける。
pub proof fn indexed_concat_argument_signal(
    source: &str, index: &BuildCircuitIndex, entry: int, definition: int, arguments: Range<usize>, name: usize,
) -> (position: int)
    requires
        build_index_matches(source, *index),
        0 <= entry < index.syntax.entries@.len(), entry < index.entry_ranges@.len(),
        index.entry_ranges@[entry].definitions.start <= definition
            < index.entry_ranges@[entry].definitions.end <= index.definitions@.len(),
        complete_list_indices(index.syntax.forms@), nested_list_indices(index.syntax.forms@),
        concat_arguments_match(source, index.syntax.forms@, index.definitions@[definition].expression.start as int, arguments),
        direct_form_in_range(index.syntax.forms@, arguments.start as int, arguments.end as int, name as int),
        name < index.syntax.forms@.len(),
        index.syntax.forms@[name as int] is Atom && index.syntax.forms@[name as int]->Atom_kind is Name,
    ensures ({
        let row = index.definitions@[definition];
        row.signals.start <= position < row.signals.end <= index.signals@.len() && index.signals@[position] == name
    }),
{
    build_definition_scope_evidence(source, index, entry, definition);
    vstd::std_specs::vec::axiom_spec_len(&index.syntax.forms);
    let row = index.definitions@[definition];
    let forms = index.syntax.forms@;
    let root = row.expression.start as int;
    let end = row.expression.end as int;
    let first = arguments.start as int;
    let last = arguments.end as int;
    super::build::definition_expression_end(forms, row);
    concat_arguments_evidence(source, forms, root, end, arguments);
    assert(expression_child_range(source, forms, root, end, first, last));
    list_child_signals(source, forms, root, end, first, last, ExpressionHead::Concat);
    direct_name_in_signal_index(source, forms, first, last, name);
    let signals = index.signals@[row.signals.start as int..row.signals.end as int];
    let offset = choose|i: int| 0 <= i < signals.len() && signals[i] == name;
    row.signals.start + offset
}

/// 文法に適合した式列が `concat` で始まるなら、その引数範囲を取り出せる。
pub proof fn strict_concat_has_argument_range(source: &str, forms: Seq<Form>, root: int, end: int)
    requires
        expression_forest(source, forms, root, end),
        0 <= root < root + 1 < end <= forms.len(),
        forms[root] is List,
        form_spans_valid(source, forms, source.spec_bytes().len() as int),
        ({
            let span = form_span(forms[root + 1]);
            span.start < span.end <= source.spec_bytes().len()
                && source.spec_bytes()[span.start as int..span.end as int] == "concat".spec_bytes()
        }),
    ensures exists|range: Range<usize>| #[trigger] concat_arguments_match(source, forms, root, range),
{
    first_expression_children(source, forms, root, end);
    let stop = forms[root]->List_end as int;
    let (first, last) = choose|first: int, last: int|
        #[trigger] expression_child_range(source, forms, root, stop, first, last)
        && expression_forest(source, forms, first, last);
    let builtin = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, root + 1, head)
        && arguments_match(forms, root + 2, stop, head, first, last);
    let span = form_span(forms[root + 1]);
    assert(expression_head_spelling(ExpressionHead::Concat).spec_bytes()
        == source.spec_bytes()[span.start as int..span.end as int]);
    assert(builtin == Some(ExpressionHead::Concat));
    reveal(form_spans_valid);
    assert(concat_arguments_match(source, forms, root, first as usize..last as usize));
}

} // verus!
