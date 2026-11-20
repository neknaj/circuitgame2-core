//! 構造体の表現を操作する式から、入力式と名前の位置を取り出す。

use super::expressions::read_expression_head;
use super::{AtomKind, ExpressionHead, Form};
use core::ops::Range;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::expression_forest::{expression_references, first_cast_reference, first_expression_children};
#[cfg(verus_only)]
use super::expressions::{
    after_form, argument_matches, arguments_match, expression_child_range, list_head_matches, same_expression_head,
};
#[cfg(verus_only)]
use super::{HeaderError, expression_forest, expression_head_spelling, form_span, form_spans_valid, is_char_boundary};
#[cfg(verus_only)]
use super::{ExpressionReference, ExpressionReferenceKind};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 構造体の表現を操作する式の種類と名前の位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructureExpressionKind {
    /// フィールドの値を取り出す。
    Field {
        /// フィールド名のアトムを指す添字。
        name: usize,
    },
    /// 同じ幅のビット列を構造体として扱う。
    As {
        /// 構造体型名のアトムを指す添字。
        target: usize,
    },
    /// 構造体の全ビットを取り出す。
    Raw,
}

/// `field`、`as`、`raw` の入力式と名前の構文位置。
#[derive(Debug, Eq, PartialEq)]
pub struct StructureExpressionShape {
    /// 入力式が占める構文木上の半開区間。
    pub input: Range<usize>,
    /// 専用フォームの種類と名前の位置。
    pub kind: StructureExpressionKind,
}

spec fn expected_head(kind: StructureExpressionKind) -> ExpressionHead {
    match kind {
        StructureExpressionKind::Field { .. } => ExpressionHead::Field,
        StructureExpressionKind::As { .. } => ExpressionHead::As,
        StructureExpressionKind::Raw => ExpressionHead::Raw,
    }
}

spec fn head_is_readable(source: &str, form: Form) -> bool {
    let span = form_span(form);
    &&& span.start < span.end <= source.spec_bytes().len()
    &&& is_char_boundary(source.spec_bytes(), span.start as int)
    &&& is_char_boundary(source.spec_bytes(), span.end as int)
}

/// 入力と名前の添字が、同じ式の文法上の位置に対応することを表す。
pub closed spec fn structure_expression_matches(
    source: &str, forms: Seq<Form>, root: int, shape: StructureExpressionShape,
) -> bool {
    &&& 0 <= root < forms.len()
    &&& forms[root] is List
    &&& {
        let end = forms[root]->List_end as int;
        &&& argument_matches(forms, root + 1, end, HeaderError::ExpectedReference)
        &&& head_is_readable(source, forms[root + 1])
        &&& list_head_matches(source, forms, root + 1, Some(expected_head(shape.kind)))
        &&& arguments_match(forms, root + 2, end, Some(expected_head(shape.kind)),
            shape.input.start as int, shape.input.end as int)
        &&& match shape.kind {
            StructureExpressionKind::Field { name } => name == shape.input.end,
            StructureExpressionKind::As { target } => target == root + 2,
            StructureExpressionKind::Raw => true,
        }
    }
}

proof fn structure_shapes_agree(
    source: &str, forms: Seq<Form>, root: int, left: StructureExpressionShape, right: StructureExpressionShape,
)
    requires structure_expression_matches(source, forms, root, left), structure_expression_matches(source, forms, root, right),
    ensures left == right,
{
    same_expression_head(source, forms, root + 1, Some(expected_head(left.kind)), Some(expected_head(right.kind)));
    assert(left.input == right.input);
}

fn read_structure_shape(source: &str, forms: &[Form], root: usize) -> (result: Option<StructureExpressionShape>)
    ensures
        result matches Some(shape) ==> structure_expression_matches(source, forms@, root as int, shape),
        (exists|shape: StructureExpressionShape| #[trigger] structure_expression_matches(source, forms@, root as int, shape))
            ==> result.is_some(),
{
    if root >= forms.len() { return None; }
    let Form::List { end: list_end, .. } = &forms[root] else { return None; };
    let end = *list_end;
    if end <= root || end > forms.len() || end - root < 3 { return None; }
    let head_at = root + 1;
    let Form::Atom { kind: atom_kind, span: head_span } = &forms[head_at] else { return None; };
    if !super::clauses::is_reference(*atom_kind)
        || head_span.start >= head_span.end || head_span.end > source.as_bytes().len()
        || !source.is_char_boundary(head_span.start) || !source.is_char_boundary(head_span.end) {
        return None;
    }
    let head = read_expression_head(source, &forms[head_at]);
    assert(list_head_matches(source, forms@, head_at as int, head));
    proof {
        if exists|shape: StructureExpressionShape| #[trigger] structure_expression_matches(source, forms@, root as int, shape) {
            let shape = choose|shape: StructureExpressionShape| #[trigger] structure_expression_matches(source, forms@, root as int, shape);
            same_expression_head(source, forms@, head_at as int, head, Some(expected_head(shape.kind)));
        }
    }
    let Some(head @ (ExpressionHead::Field | ExpressionHead::As | ExpressionHead::Raw)) = head else {
        return None;
    };
    let first = root + 2;
    let input_start = if matches!(head, ExpressionHead::As) { first + 1 } else { first };
    if input_start >= end { return None; }
    let input_end = match &forms[input_start] {
        Form::Atom { .. } => input_start + 1,
        Form::List { end: operand_end, .. } => *operand_end,
    };
    assert(input_end == after_form(forms@, input_start as int));
    if input_end <= input_start || input_end > end { return None; }
    let kind = match head {
        ExpressionHead::Field => {
            if end - input_end != 1 || !matches!(&forms[input_end], Form::Atom { kind: AtomKind::Name, .. }) {
                return None;
            }
            StructureExpressionKind::Field { name: input_end }
        },
        ExpressionHead::As => {
            let Form::Atom { kind: type_kind, .. } = forms[first] else { return None; };
            if input_end != end || !super::clauses::is_reference(type_kind) {
                return None;
            }
            StructureExpressionKind::As { target: first }
        },
        ExpressionHead::Raw => {
            if input_end != end { return None; }
            StructureExpressionKind::Raw
        },
        _ => unreachable!(),
    };
    Some(StructureExpressionShape { input: input_start..input_end, kind })
}

/// 指定したフォームから構造体操作の入力式と名前の位置を取り出す。
///
/// `source` と `forms` には同じソースの本文と構文木を渡す。
/// 先頭語と引数の配置が合う場合に位置を返す。入力式の内容は厳格パーサーが検査する。
///
/// # Examples
///
/// 入れ子の場合、返る区間は入力式の部分木全体を含む。
///
/// ```
/// use circuitgame2_syntax::{parse, circuit::{StructureExpressionKind, structure_expression_shape}};
/// let source = "(raw (field (as Packet bus) payload))";
/// let forms = parse(source).unwrap();
/// let raw = structure_expression_shape(source, &forms, 0).unwrap();
/// assert_eq!(raw.kind, StructureExpressionKind::Raw);
/// let field = structure_expression_shape(source, &forms, raw.input.start).unwrap();
/// assert_eq!(field.kind, StructureExpressionKind::Field { name: 8 });
/// let cast = structure_expression_shape(source, &forms, field.input.start).unwrap();
/// assert_eq!(cast.kind, StructureExpressionKind::As { target: 6 });
/// assert_eq!(cast.input, 7..8);
/// ```
pub fn structure_expression_shape(source: &str, forms: &[Form], root: usize) -> (result: Option<StructureExpressionShape>)
    ensures forall|shape: StructureExpressionShape| #[trigger] structure_expression_matches(source, forms@, root as int, shape)
        <==> result == Some(shape),
{
    let found = read_structure_shape(source, forms, root);
    assert forall|shape: StructureExpressionShape| #[trigger] structure_expression_matches(source, forms@, root as int, shape)
        <==> found == Some(shape) by {
        if structure_expression_matches(source, forms@, root as int, shape) {
            structure_shapes_agree(source, forms@, root as int, shape, found->Some_0);
        }
    };
    found
}

/// 抽出した入力式の区間と、名前の添字が指す字句の種別を示す。
pub proof fn structure_expression_positions(
    source: &str, forms: Seq<Form>, root: int, shape: StructureExpressionShape,
)
    requires structure_expression_matches(source, forms, root, shape),
    ensures
        0 <= root < shape.input.start < shape.input.end <= forms.len(),
        shape.input.end == match forms[shape.input.start as int] {
            Form::List { end, .. } => end as int,
            Form::Atom { .. } => shape.input.start + 1,
        },
        match shape.kind {
            StructureExpressionKind::Field { name } => name == shape.input.end && name < forms.len()
                && forms[name as int] is Atom && forms[name as int]->Atom_kind is Name,
            StructureExpressionKind::As { target } => target + 1 == shape.input.start
                && forms[target as int] is Atom && super::reference_atom(forms[target as int]->Atom_kind),
            StructureExpressionKind::Raw => true,
        },
{
}

/// 右辺全体が `as` のとき、構造体の型名が参照列の先頭にあることを示す。
pub proof fn structure_cast_reference(
    source: &str, forms: Seq<Form>, root: int, stop: int, shape: StructureExpressionShape,
)
    requires
        structure_expression_matches(source, forms, root, shape),
        shape.kind is As,
        expression_forest(source, forms, root, stop),
        0 <= root < stop <= forms.len(),
    ensures
        expression_references(source, forms, root, stop).len() > 0,
        ({
            let target = shape.kind->As_target;
            expression_references(source, forms, root, stop)[0] == (ExpressionReference {
                kind: ExpressionReferenceKind::CastType, form: target, span: form_span(forms[target as int]),
            })
        }),
{
    first_expression_children(source, forms, root, stop);
    let end = forms[root]->List_end as int;
    assert(expression_child_range(source, forms, root, end, shape.input.start as int, shape.input.end as int));
    first_cast_reference(source, forms, root, stop, shape.input.start as int, shape.input.end as int);
}

/// 文法に適合する構造体操作から位置を取り出せることと、その入力式が文法に適合することを示す。
pub proof fn strict_structure_expression_has_shape(source: &str, forms: Seq<Form>, root: int, end: int)
    requires
        expression_forest(source, forms, root, end),
        0 <= root < root + 1 < end <= forms.len(),
        forms[root] is List,
        form_spans_valid(source, forms, source.spec_bytes().len() as int),
        ({
            let span = form_span(forms[root + 1]);
            let word = source.spec_bytes()[span.start as int..span.end as int];
            span.start < span.end <= source.spec_bytes().len()
                && (word == "field".spec_bytes() || word == "as".spec_bytes() || word == "raw".spec_bytes())
        }),
    ensures exists|shape: StructureExpressionShape| #[trigger] structure_expression_matches(source, forms, root, shape)
        && expression_forest(source, forms, shape.input.start as int, shape.input.end as int),
{
    first_expression_children(source, forms, root, end);
    let stop = forms[root]->List_end as int;
    let (first, last) = choose|first: int, last: int|
        #[trigger] expression_child_range(source, forms, root, stop, first, last)
        && expression_forest(source, forms, first, last);
    let builtin = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, root + 1, head)
        && arguments_match(forms, root + 2, stop, head, first, last);
    let span = form_span(forms[root + 1]);
    let word = source.spec_bytes()[span.start as int..span.end as int];
    let kind = if word == "field".spec_bytes() {
        assert(expression_head_spelling(ExpressionHead::Field).spec_bytes() == word);
        assert(builtin == Some(ExpressionHead::Field));
        StructureExpressionKind::Field { name: last as usize }
    } else if word == "as".spec_bytes() {
        assert(expression_head_spelling(ExpressionHead::As).spec_bytes() == word);
        assert(builtin == Some(ExpressionHead::As));
        StructureExpressionKind::As { target: (root + 2) as usize }
    } else {
        assert(expression_head_spelling(ExpressionHead::Raw).spec_bytes() == word);
        assert(builtin == Some(ExpressionHead::Raw));
        StructureExpressionKind::Raw
    };
    reveal(form_spans_valid);
    let shape = StructureExpressionShape { input: (first as usize)..(last as usize), kind };
    assert(structure_expression_matches(source, forms, root, shape));
    assert(expression_forest(source, forms, shape.input.start as int, shape.input.end as int));
}

} // verus!
