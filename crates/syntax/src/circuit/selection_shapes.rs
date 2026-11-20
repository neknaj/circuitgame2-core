//! ビット選択式の入力式と数値引数の位置を、平坦な構文木から取り出す。

use super::*;
#[cfg(verus_only)]
use super::expression_forest::{expression_signals_in_order, first_expression_children};

#[cfg(verus_only)]
use super::expressions::{
    after_form, argument_matches, arguments_match, expression_child_range, list_head_matches, same_expression_head,
};
use super::expressions::read_expression_head;

verus! {

/// 開始位置に続く引数の構文木上の添字。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BitSelectionTail {
    /// `bit` の選択数と刻みはそれぞれ1。
    Bit,
    /// `slice` の選択数と、省略可能な刻み。
    Slice {
        /// 選択数を表す自然数アトムの添字。
        count: usize,
        /// 刻みを表す自然数アトムの添字。省略時は1を使う。
        stride: Option<usize>,
    },
}

/// `bit` または `slice` の入力式と数値引数の位置。
#[derive(Debug, Eq, PartialEq)]
pub struct BitSelectionShape {
    /// 入力式を占める構文木上の半開区間。
    pub input: Range<usize>,
    /// 開始位置を表す自然数アトムの添字。
    pub start: usize,
    /// 選択数と刻みの指定。
    pub tail: BitSelectionTail,
}

spec fn readable_expression_head(source: &str, form: Form) -> bool {
    let span = form_span(form);
    &&& span.start < span.end <= source.spec_bytes().len()
    &&& is_char_boundary(source.spec_bytes(), span.start as int)
    &&& is_char_boundary(source.spec_bytes(), span.end as int)
}

/// 選択式の先頭語と引数列が文法に合い、各添字がその位置を指すことを表す。
pub closed spec fn bit_selection_shape_matches(
    source: &str, forms: Seq<Form>, index: int, shape: BitSelectionShape,
) -> bool {
    &&& 0 <= index < forms.len()
    &&& forms[index] is List
    &&& {
        let end = forms[index]->List_end as int;
        let head = match shape.tail { BitSelectionTail::Bit => ExpressionHead::Bit, _ => ExpressionHead::Slice };
        let start = shape.input.end as int;
        &&& argument_matches(forms, index + 1, end, HeaderError::ExpectedReference)
        &&& readable_expression_head(source, forms[index + 1])
        &&& list_head_matches(source, forms, index + 1, Some(head))
        &&& arguments_match(forms, index + 2, end, Some(head), shape.input.start as int, start)
        &&& shape.start == start
        &&& match shape.tail {
            BitSelectionTail::Bit => true,
            BitSelectionTail::Slice { count, stride } =>
                count == start + 1 && (if start + 2 == end { stride.is_none() } else { stride == Some((start + 2) as usize) }),
        }
    }
}

pub(super) proof fn ordinary_head_excludes_selection(source: &str, forms: Seq<Form>, call: int)
    requires list_head_matches(source, forms, call + 1, None),
    ensures !(exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, call, shape)),
{
    if exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, call, shape) {
        let shape = choose|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, call, shape);
        let head = match shape.tail { BitSelectionTail::Bit => ExpressionHead::Bit, _ => ExpressionHead::Slice };
        same_expression_head(source, forms, call + 1, None, Some(head));
    }
}

/// 同じ位置から得たビット選択の構文情報が一致することを示す。
pub proof fn bit_selection_shapes_agree(source: &str, forms: Seq<Form>, index: int, left: BitSelectionShape, right: BitSelectionShape)
    requires
        bit_selection_shape_matches(source, forms, index, left),
        bit_selection_shape_matches(source, forms, index, right),
    ensures left == right,
{
    let lhs = match left.tail { BitSelectionTail::Bit => ExpressionHead::Bit, _ => ExpressionHead::Slice };
    let rhs = match right.tail { BitSelectionTail::Bit => ExpressionHead::Bit, _ => ExpressionHead::Slice };
    same_expression_head(source, forms, index + 1, Some(lhs), Some(rhs));
    assert(left.input == right.input);
}

fn selection_tail(forms: &[Form], first: usize, end: usize, head: ExpressionHead) -> (tail: Option<BitSelectionTail>)
    requires
        first < end <= forms@.len(),
        head is Bit || head is Slice,
    ensures
        tail.is_some() <==> (super::natural_argument_at(forms@, first as int, end as int)
            && (if head is Bit { first + 1 == end }
                else { super::natural_argument_at(forms@, first + 1, end as int)
                    && (first + 2 == end || first + 3 == end && super::natural_argument_at(forms@, first + 2, end as int)) })),
        tail matches Some(found) ==> match found {
            BitSelectionTail::Bit => head is Bit,
            BitSelectionTail::Slice { count, stride } => head is Slice && count == first + 1
                && (if first + 2 == end { stride.is_none() } else { stride == Some((first + 2) as usize) }),
        },
{
    if !matches!(forms[first], Form::Atom { kind: AtomKind::Natural, .. }) {
        return None;
    }
    if matches!(head, ExpressionHead::Bit) {
        return if end - first == 1 { Some(BitSelectionTail::Bit) } else { None };
    }
    let count = first + 1;
    if count == end || !matches!(forms[count], Form::Atom { kind: AtomKind::Natural, .. }) {
        return None;
    }
    if end - first == 2 {
        return Some(BitSelectionTail::Slice { count, stride: None });
    }
    let stride = count + 1;
    if end - first == 3 && matches!(forms[stride], Form::Atom { kind: AtomKind::Natural, .. }) {
        Some(BitSelectionTail::Slice { count, stride: Some(stride) })
    } else {
        None
    }
}

/// 指定したフォームがビット選択式なら、入力式と数値引数の添字を返す。
///
/// `source` と `forms` には同じソースの本文と構文木を渡す。先頭語、引数の配置、
/// 自然数アトムの種別を検査し、対応する局所構造がなければ `None` を返す。
/// 入力式の内容は厳格パーサーで検査する。数値の大きさやビット幅は後段で検査する。
pub fn bit_selection_shape(source: &str, forms: &[Form], index: usize) -> (result: Option<BitSelectionShape>)
    ensures forall|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms@, index as int, shape)
        <==> result == Some(shape),
{
    let found = read_selection_shape(source, forms, index);
    assert forall|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms@, index as int, shape)
        <==> found == Some(shape) by {
        if bit_selection_shape_matches(source, forms@, index as int, shape) {
            bit_selection_shapes_agree(source, forms@, index as int, shape, found->Some_0);
        }
    };
    found
}

fn read_selection_shape(source: &str, forms: &[Form], index: usize) -> (result: Option<BitSelectionShape>)
    ensures
        result matches Some(shape) ==> bit_selection_shape_matches(source, forms@, index as int, shape),
        (exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms@, index as int, shape)) ==> result is Some,
{
    if index >= forms.len() { return None; }
    let Form::List { end: list_end, .. } = &forms[index] else { return None; };
    let end = *list_end;
    if end <= index || end > forms.len() || end - index < 3 { return None; }
    let head_site = index + 1;
    let Form::Atom { kind: head_kind, span: head_span } = &forms[head_site] else { return None; };
    if !super::clauses::is_reference(*head_kind)
        || head_span.start >= head_span.end || head_span.end > source.as_bytes().len()
        || !source.is_char_boundary(head_span.start) || !source.is_char_boundary(head_span.end) {
        return None;
    }
    let head = read_expression_head(source, &forms[head_site]);
    assert(list_head_matches(source, forms@, head_site as int, head));
    let first = index + 2;
    let next = match &forms[first] {
        Form::Atom { .. } => first + 1,
        Form::List { end, .. } => *end,
    };
    assert(next == after_form(forms@, first as int));
    let ghost exists_shape = exists|shape: BitSelectionShape| #[trigger]
        bit_selection_shape_matches(source, forms@, index as int, shape);
    proof {
        if exists_shape {
            let shape = choose|shape: BitSelectionShape| #[trigger]
                bit_selection_shape_matches(source, forms@, index as int, shape);
            let expected = match shape.tail { BitSelectionTail::Bit => ExpressionHead::Bit, _ => ExpressionHead::Slice };
            same_expression_head(source, forms@, head_site as int, head, Some(expected));
            assert(first < next < end);
        }
    }
    let Some(kind @ (ExpressionHead::Bit | ExpressionHead::Slice)) = head else { return None; };
    if first >= next || next >= end { return None; }
    let tail = selection_tail(forms, next, end, kind)?;
    Some(BitSelectionShape { input: first..next, start: next, tail })
}

/// 選択式の入力区間と各自然数アトムが、同じリスト内にあることを示す。
pub proof fn bit_selection_shape_positions(source: &str, forms: Seq<Form>, index: int, shape: BitSelectionShape)
    requires bit_selection_shape_matches(source, forms, index, shape),
    ensures
        0 <= index < forms.len() && forms[index] is List,
        index + 2 == shape.input.start < shape.input.end == shape.start
            < forms[index]->List_end <= forms.len(),
        natural_argument_at(forms, shape.start as int, forms[index]->List_end as int),
        shape.tail matches BitSelectionTail::Slice { count, stride } ==> (
            count == shape.start + 1 && natural_argument_at(forms, count as int, forms[index]->List_end as int)
            && (stride matches Some(at) ==> at == count + 1
                && natural_argument_at(forms, at as int, forms[index]->List_end as int))
        ),
{
}

/// 文法に適合した式列が `bit` または `slice` で始まるなら、その選択式の位置を取り出せる。
pub proof fn strict_bit_selection_has_shape(
    source: &str, forms: Seq<Form>, index: int, end: int,
)
    requires
        expression_forest(source, forms, index, end),
        0 <= index < index + 1 < end <= forms.len(),
        forms[index] is List,
        form_spans_valid(source, forms, source.spec_bytes().len() as int),
        ({
            let span = form_span(forms[index + 1]);
            let word = source.spec_bytes()[span.start as int..span.end as int];
            span.start < span.end <= source.spec_bytes().len()
                && (word == "bit".spec_bytes() || word == "slice".spec_bytes())
        }),
    ensures exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, index, shape),
{
    first_expression_children(source, forms, index, end);
    let stop = forms[index]->List_end as int;
    let (first, last) = choose|first: int, last: int|
        #[trigger] expression_child_range(source, forms, index, stop, first, last)
        && expression_forest(source, forms, first, last);
    let builtin = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, index + 1, head)
        && arguments_match(forms, index + 2, stop, head, first, last);
    let span = form_span(forms[index + 1]);
    let word = source.spec_bytes()[span.start as int..span.end as int];
    let tail = if word == "bit".spec_bytes() {
        assert(expression_head_spelling(ExpressionHead::Bit).spec_bytes() == word);
        assert(builtin == Some(ExpressionHead::Bit));
        BitSelectionTail::Bit
    } else {
        assert(expression_head_spelling(ExpressionHead::Slice).spec_bytes() == word);
        assert(builtin == Some(ExpressionHead::Slice));
        BitSelectionTail::Slice {
            count: (last + 1) as usize,
            stride: if last + 2 == stop { None } else { Some((last + 2) as usize) },
        }
    };
    reveal(form_spans_valid);
    assert(bit_selection_shape_matches(source, forms, index,
        BitSelectionShape { input: first as usize..last as usize, start: last as usize, tail }));
}

/// 選択式が文法に適合した式列の先頭にあれば、その入力式も文法に適合する。
pub proof fn strict_bit_selection_input(
    source: &str, forms: Seq<Form>, index: int, end: int, shape: BitSelectionShape,
)
    requires
        expression_forest(source, forms, index, end),
        index < end <= forms.len(),
        bit_selection_shape_matches(source, forms, index, shape),
    ensures expression_forest(source, forms, shape.input.start as int, shape.input.end as int),
{
    first_expression_children(source, forms, index, end);
    let stop = forms[index]->List_end as int;
    let (first, last) = choose|first: int, last: int|
        #[trigger] expression_child_range(source, forms, index, stop, first, last)
        && expression_forest(source, forms, first, last);
    let candidate = choose|head: Option<ExpressionHead>|
        #[trigger] list_head_matches(source, forms, index + 1, head)
        && arguments_match(forms, index + 2, stop, head, first, last);
    let expected = match shape.tail { BitSelectionTail::Bit => ExpressionHead::Bit, _ => ExpressionHead::Slice };
    same_expression_head(source, forms, index + 1, candidate, Some(expected));
}

/// 入力式が裸の信号名なら、選択式の定義に付く信号索引の先頭がその名を指す。
///
/// 同じ構文木上の位置は後続の行に現れない。
pub proof fn build_selection_input_position(
    source: &str, index: &BuildCircuitIndex, entry: int, definition: int, shape: BitSelectionShape,
)
    requires
        build_index_matches(source, *index),
        0 <= entry < index.syntax.entries@.len(), entry < index.entry_ranges@.len(),
        index.entry_ranges@[entry].definitions.start <= definition
            < index.entry_ranges@[entry].definitions.end <= index.definitions@.len(),
        bit_selection_shape_matches(source, index.syntax.forms@,
            index.definitions@[definition].expression.start as int, shape),
        shape.input.end == shape.input.start + 1,
        index.syntax.forms@[shape.input.start as int] is Atom,
        index.syntax.forms@[shape.input.start as int]->Atom_kind is Name,
    ensures ({
        let frame = index.entry_ranges@[entry].signals;
        let row = index.definitions@[definition];
        &&& frame.start <= row.signals.start < row.signals.end <= frame.end <= index.signals@.len()
        &&& index.signals@[row.signals.start as int] == shape.input.start
        &&& forall|i: int| row.signals.start < i < row.signals.end ==>
            #[trigger] index.signals@[i] > shape.input.start
    }),
{
    build_definition_scope_evidence(source, index, entry, definition);
    vstd::std_specs::vec::axiom_spec_len(&index.syntax.forms);
    let forms = index.syntax.forms@;
    let row = index.definitions@[definition];
    let first = row.expression.start as int;
    let stop = row.expression.end as int;
    first_expression_children(source, forms, first, stop);
    bit_selection_shape_positions(source, forms, first, shape);
    let end = forms[first]->List_end as int;
    assert(expression_child_range(
        source, forms, first, end, shape.input.start as int, shape.input.end as int,
    ));
    super::expression_forest::first_named_child_signal(source, forms, first, stop, shape.input.start);
    expression_signals_in_order(source, forms, first, stop);
    let start = row.signals.start as int;
    let signals = index.signals@[start..row.signals.end as int];
    assert forall|i: int| start < i < row.signals.end implies #[trigger] index.signals@[i] > shape.input.start by {
        assert(signals[0] == shape.input.start);
        assert(signals[i - start] == index.signals@[i]);
    };
}

} // verus!
