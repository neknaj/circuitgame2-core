//! 式の並びを検査し、各リストでは子式を後続の式より先に調べる。

use super::expressions::expression_children;
#[cfg(verus_only)]
use super::expressions::{
    after_form, argument_matches, argument_shape_error, arguments_match, expression_child_range, expression_list_error, list_head_matches,
    same_expression_head, same_expression_list_error,
};
use super::*;
#[cfg(verus_only)]
use crate::{bare_atom_kind, sexpr_form_model, syntax_error_evidence, well_formed_sexpr};

verus! {

/// 回路式で共有宣言表を参照する名前の役割。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExpressionReferenceKind {
    /// 通常呼び出しの先頭にある回路名。
    Callee,
    /// `as` が指定する型名。
    CastType,
}

/// 回路式が参照する名前と、元ソース上の位置。
#[derive(Debug, Eq, PartialEq)]
pub struct ExpressionReference {
    /// 呼び出しと型参照のどちらに使うか。
    pub kind: ExpressionReferenceKind,
    /// 元の平坦な構文木で名前のアトムを指す添字。
    pub form: usize,
    /// 名前の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
}

/// 参照が構文木内の名前かパスを指し、範囲の両端が UTF-8 文字境界にあることを表す。
pub open spec fn expression_reference_in_source(
    source: &str, forms: Seq<Form>, item: ExpressionReference,
) -> bool {
    &&& item.form < forms.len()
    &&& forms[item.form as int] is Atom
    &&& reference_atom(forms[item.form as int]->Atom_kind)
    &&& item.span == form_span(forms[item.form as int])
    &&& item.span.start < item.span.end <= source.spec_bytes().len()
    &&& is_char_boundary(source.spec_bytes(), item.span.start as int)
    &&& is_char_boundary(source.spec_bytes(), item.span.end as int)
    &&& bare_atom_kind(source.spec_bytes()[item.span.start as int..item.span.end as int])
        == Some(forms[item.form as int]->Atom_kind)
}

fn indexed_reference(
    _source: &str, forms: &[Form], form: usize, _end: usize, kind: ExpressionReferenceKind,
) -> (item: ExpressionReference)
    requires
        form_spans_valid(_source, forms@, _source.spec_bytes().len() as int),
        argument_matches(forms@, form as int, _end as int, HeaderError::ExpectedReference),
    ensures
        item.kind == kind && item.form == form && item.span == form_span(forms@[form as int]),
        expression_reference_in_source(_source, forms@, item),
{
    proof { reveal(form_spans_valid); }
    ExpressionReference { kind, form, span: form_span_exec(&forms[form]) }
}

spec fn local_reference(
    forms: Seq<Form>, index: int, end: int, builtin: Option<ExpressionHead>,
) -> Seq<ExpressionReference> {
    if 0 <= index && index + 1 < end <= forms.len() && builtin is None {
        seq![ExpressionReference {
            kind: ExpressionReferenceKind::Callee, form: (index + 1) as usize, span: form_span(forms[index + 1]),
        }]
    } else if 0 <= index && index + 2 < end <= forms.len() && builtin == Some(ExpressionHead::As) {
        seq![ExpressionReference {
            kind: ExpressionReferenceKind::CastType, form: (index + 2) as usize, span: form_span(forms[index + 2]),
        }]
    } else {
        Seq::empty()
    }
}

/// 式列の子式を文法に従ってたどったときに現れる参照を、元ソース順で定める。
#[verifier::opaque]
pub closed spec fn expression_references(
    source: &str, forms: Seq<Form>, start: int, stop: int,
) -> Seq<ExpressionReference>
    decreases stop - start,
{
    if !(0 <= start < stop <= forms.len()) {
        Seq::empty()
    } else {
        match forms[start] {
            Form::Atom { .. } => expression_references(source, forms, start + 1, stop),
            Form::List { end, .. } => {
                if start < end <= stop && exists|a: int, b: int| start < a <= b <= end
                    && #[trigger] expression_child_range(source, forms, start, end as int, a, b)
                {
                    let (a, b) = choose|a: int, b: int| start < a <= b <= end
                        && #[trigger] expression_child_range(source, forms, start, end as int, a, b);
                    let builtin = choose|builtin: Option<ExpressionHead>|
                        #[trigger] list_head_matches(source, forms, start + 1, builtin);
                    local_reference(forms, start, end as int, builtin)
                        + expression_references(source, forms, a, b)
                        + expression_references(source, forms, end as int, stop)
                } else {
                    Seq::empty()
                }
            },
        }
    }
}

/// 指定の構文木位置に、専用フォーム以外の呼び出しがあることを表す。
pub closed spec fn ordinary_call_at(source: &str, forms: Seq<Form>, call: int, stop: int) -> bool {
    &&& 0 <= call && call + 1 < stop <= forms.len()
    &&& forms[call] is List
    &&& call + 2 <= forms[call]->List_end <= stop
    &&& argument_matches(forms, call + 1, forms[call]->List_end as int, HeaderError::ExpectedReference)
    &&& list_head_matches(source, forms, call + 1, None)
}

pub(super) proof fn ordinary_call_bounds(source: &str, forms: Seq<Form>, call: int, stop: int)
    requires ordinary_call_at(source, forms, call, stop),
    ensures 0 <= call < forms.len() && forms[call] is List
        && call < stop
        && call + 2 <= forms[call]->List_end <= forms.len()
        && forms[call + 1] is Atom,
{
}

/// 通常呼び出しのリストが指定区間に収まり、ビット選択、構造体式、連接に当たらないことを示す。
pub proof fn ordinary_call_excludes_special_forms(source: &str, forms: Seq<Form>, call: int, stop: int)
    requires ordinary_call_at(source, forms, call, stop),
    ensures
        forms[call] is List && forms[call]->List_end <= stop <= forms.len(),
        !(exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, call, shape)),
        !(exists|shape: StructureExpressionShape| #[trigger] structure_expression_matches(source, forms, call, shape)),
        !(exists|range: Range<usize>| #[trigger] super::concat_arguments::concat_arguments_match(source, forms, call, range)),
{
    super::selection_shapes::ordinary_head_excludes_selection(source, forms, call);
    super::structure_expressions::ordinary_head_excludes_structure(source, forms, call);
    if exists|range: Range<usize>| #[trigger] super::concat_arguments::concat_arguments_match(source, forms, call, range) {
        let range = choose|range: Range<usize>| #[trigger] super::concat_arguments::concat_arguments_match(source, forms, call, range);
        super::concat_arguments::ordinary_head_excludes_concat(source, forms, call, range);
    }
}

/// 通常呼び出しの参照添字は、対応するリストの直後の先頭語を指す。
pub(super) proof fn expression_callee_location(
    source: &str, forms: Seq<Form>, start: int, stop: int, position: int,
)
    requires
        forms.len() <= usize::MAX,
        0 <= position < expression_references(source, forms, start, stop).len(),
        expression_references(source, forms, start, stop)[position].kind is Callee,
    ensures ({
        let call = expression_references(source, forms, start, stop)[position].form - 1;
        &&& 0 <= start <= call && call + 1 < stop <= forms.len()
        &&& forms[call] is List && call + 2 <= forms[call]->List_end <= stop
        &&& ordinary_call_at(source, forms, call, stop)
    }),
    decreases stop - start,
{
    reveal_with_fuel(expression_references, 1);
    assert(0 <= start < stop <= forms.len());
    let refs = expression_references(source, forms, start, stop);
    match forms[start] {
        Form::Atom { .. } => {
            expression_callee_location(source, forms, start + 1, stop, position);
        },
        Form::List { end, .. } => {
            assert(start < end <= stop);
            let (a, b) = choose|a: int, b: int| start < a <= b <= end
                && #[trigger] expression_child_range(source, forms, start, end as int, a, b);
            let head = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, start + 1, head);
            let local = local_reference(forms, start, end as int, head);
            let children = expression_references(source, forms, a, b);
            let siblings = expression_references(source, forms, end as int, stop);
            assert(refs == local + children + siblings);
            if position < local.len() {
                assert(refs[position] == local[position]);
                assert(head is None && refs[position].form == start + 1);
            } else if position < local.len() + children.len() {
                let offset = position - local.len();
                assert(refs[position] == children[offset]);
                expression_callee_location(source, forms, a, b, offset);
            } else {
                let offset = position - local.len() - children.len();
                assert(refs[position] == siblings[offset]);
                expression_callee_location(source, forms, end as int, stop, offset);
            }
        },
    }
}

pub(super) proof fn expression_root_callee(
    source: &str, forms: Seq<Form>, start: int, stop: int,
)
    requires
        0 <= start < stop <= forms.len() <= usize::MAX,
        expression_forest(source, forms, start, stop), after_form(forms, start) == stop,
    ensures ({
        let refs = expression_references(source, forms, start, stop);
        ordinary_call_at(source, forms, start, stop)
            <==> refs.len() > 0 && refs[0].kind is Callee && refs[0].form == start + 1
    }),
{
    let refs = expression_references(source, forms, start, stop);
    if ordinary_call_at(source, forms, start, stop) {
        reveal_with_fuel(expression_forest, 1);
        reveal_with_fuel(expression_references, 1);
        let (a, b) = choose|a: int, b: int| start < a <= b <= stop
            && #[trigger] expression_child_range(source, forms, start, stop, a, b);
        let head = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, start + 1, head);
        same_expression_head(source, forms, start + 1, head, None);
        assert(refs[0] == local_reference(forms, start, stop, head)[0]);
    } else if refs.len() > 0 && refs[0].kind is Callee && refs[0].form == start + 1 {
        expression_callee_location(source, forms, start, stop, 0);
    }
}

/// 各参照の構文木添字は式列の範囲内にあり、重複せず昇順に並ぶ。
pub(super) proof fn expression_references_in_order(source: &str, forms: Seq<Form>, start: int, stop: int)
    requires forms.len() <= usize::MAX,
    ensures ({
        let refs = expression_references(source, forms, start, stop);
        &&& forall|i: int| 0 <= i < refs.len() ==> start <= (#[trigger] refs[i]).form < stop
        &&& forall|i: int, j: int| 0 <= i < j < refs.len() ==>
            (#[trigger] refs[i]).form < (#[trigger] refs[j]).form
    }),
    decreases stop - start,
{
    reveal_with_fuel(expression_references, 1);
    if 0 <= start < stop <= forms.len() {
        match forms[start] {
            Form::Atom { .. } => expression_references_in_order(source, forms, start + 1, stop),
            Form::List { end, .. } => {
                let end = end as int;
                if start < end <= stop && exists|a: int, b: int| start < a <= b <= end
                    && #[trigger] expression_child_range(source, forms, start, end, a, b)
                {
                    let (a, b) = choose|a: int, b: int| start < a <= b <= end
                        && #[trigger] expression_child_range(source, forms, start, end, a, b);
                    let head = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, start + 1, head);
                    let witness = choose|builtin: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, start + 1, builtin)
                        && arguments_match(forms, start + 2, end, builtin, a, b);
                    same_expression_head(source, forms, start + 1, head, witness);
                    let local = local_reference(forms, start, end, head);
                    let children = expression_references(source, forms, a, b);
                    let siblings = expression_references(source, forms, end, stop);
                    let refs = expression_references(source, forms, start, stop);
                    expression_references_in_order(source, forms, a, b);
                    expression_references_in_order(source, forms, end, stop);
                    assert(refs == local + children + siblings);
                    assert(local.len() <= 1);
                    assert forall|i: int| 0 <= i < local.len() implies start <= (#[trigger] local[i]).form < a by {
                        assert(i == 0);
                    };
                    assert forall|i: int| 0 <= i < refs.len() implies start <= (#[trigger] refs[i]).form < stop by {
                        if i < local.len() {
                            assert(refs[i] == local[i]);
                        } else if i < local.len() + children.len() {
                            assert(refs[i] == children[i - local.len()]);
                        } else {
                            assert(refs[i] == siblings[i - local.len() - children.len()]);
                        }
                    };
                    assert forall|i: int, j: int| 0 <= i < j < refs.len() implies
                        (#[trigger] refs[i]).form < (#[trigger] refs[j]).form by {
                        if i < local.len() {
                            assert(refs[i] == local[i]);
                            if j < local.len() + children.len() {
                                assert(refs[j] == children[j - local.len()]);
                            } else {
                                assert(refs[j] == siblings[j - local.len() - children.len()]);
                            }
                        } else if i < local.len() + children.len() {
                            assert(refs[i] == children[i - local.len()]);
                            if j < local.len() + children.len() {
                                assert(refs[j] == children[j - local.len()]);
                            } else {
                                assert(refs[j] == siblings[j - local.len() - children.len()]);
                            }
                        } else {
                            assert(refs[i] == siblings[i - local.len() - children.len()]);
                            assert(refs[j] == siblings[j - local.len() - children.len()]);
                        }
                    };
                }
            },
        }
    }
}

/// 文法上の通常呼び出しが、右辺の参照列に含まれることを示す。
pub(super) proof fn ordinary_call_in_reference_index(
    source: &str, forms: Seq<Form>, start: int, stop: int, call: int, call_limit: int,
)
    requires
        0 <= start <= call < stop <= forms.len() <= usize::MAX,
        expression_forest(source, forms, start, stop),
        ordinary_call_at(source, forms, call, call_limit),
    ensures exists|i: int| 0 <= i < expression_references(source, forms, start, stop).len()
        && (#[trigger] expression_references(source, forms, start, stop)[i]).form == call + 1
        && expression_references(source, forms, start, stop)[i].kind is Callee,
    decreases stop - start,
{
    reveal_with_fuel(expression_references, 1);
    reveal_with_fuel(expression_forest, 1);
    reveal(ordinary_call_at);
    let refs = expression_references(source, forms, start, stop);
    match forms[start] {
        Form::Atom { .. } => ordinary_call_in_reference_index(source, forms, start + 1, stop, call, call_limit),
        Form::List { end, .. } => {
            let end = end as int;
            let (a, b) = choose|a: int, b: int| start < a <= b <= end
                && #[trigger] expression_child_range(source, forms, start, end, a, b);
            let (u, v) = choose|u: int, v: int| start < u <= v <= end
                && #[trigger] expression_child_range(source, forms, start, end, u, v)
                && expression_forest(source, forms, u, v);
            same_child_interval(source, forms, start, end, a, b, u, v);
            let head = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, start + 1, head);
            let local = local_reference(forms, start, end, head);
            let children = expression_references(source, forms, a, b);
            let siblings = expression_references(source, forms, end, stop);
            assert(refs == local + children + siblings);
            if call == start {
                same_expression_head(source, forms, start + 1, head, None);
                assert(refs[0] == local[0]);
            } else if end <= call {
                ordinary_call_in_reference_index(source, forms, end, stop, call, call_limit);
                let i = choose|i: int| 0 <= i < siblings.len() && (#[trigger] siblings[i]).form == call + 1
                    && siblings[i].kind is Callee;
                assert(refs[local.len() + children.len() + i] == siblings[i]);
            } else {
                let witness = choose|builtin: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, start + 1, builtin)
                    && arguments_match(forms, start + 2, end, builtin, a, b);
                assert(forms[call] is List);
                assert(a <= call < b) by {
                    if call == start + 1 {
                        assert(argument_matches(forms, call, end, HeaderError::ExpectedReference));
                    }
                    if call < a {
                        assert(witness == Some(ExpressionHead::As) && call == start + 2);
                        assert(argument_matches(forms, call, end, HeaderError::ExpectedReference));
                    }
                    if b <= call {
                        assert(match witness {
                            Some(ExpressionHead::Field) => argument_matches(forms, call, end, HeaderError::ExpectedName),
                            _ => natural_argument_at(forms, call, end),
                        });
                        reveal(natural_argument_at);
                    }
                };
                ordinary_call_in_reference_index(source, forms, a, b, call, call_limit);
                let i = choose|i: int| 0 <= i < children.len() && (#[trigger] children[i]).form == call + 1
                    && children[i].kind is Callee;
                assert(refs[local.len() + i] == children[i]);
            }
        },
    }
}

#[verifier::opaque]
spec fn pending_references(source: &str, forms: Seq<Form>, pending: Seq<Range<usize>>) -> Seq<ExpressionReference>
    decreases pending.len(),
{
    if pending.len() == 0 { Seq::empty() } else {
        expression_references(source, forms, pending.last().start as int, pending.last().end as int)
            + pending_references(source, forms, pending.drop_last())
    }
}

proof fn list_reference_order(
    source: &str, forms: Seq<Form>, start: int, stop: int, end: int, child_start: int, child_stop: int,
    builtin: Option<ExpressionHead>,
)
    requires
        0 <= start < end <= stop <= forms.len(),
        expression_child_range(source, forms, start, end, child_start, child_stop),
        start < child_start <= child_stop <= end,
        list_head_matches(source, forms, start + 1, builtin),
        forall|i: int, j: int| #[trigger] expression_child_range(source, forms, start, end, i, j)
            ==> i == child_start && j == child_stop,
    ensures
        expression_references(source, forms, start, stop)
            == local_reference(forms, start, end, builtin)
                + expression_references(source, forms, child_start, child_stop)
                + expression_references(source, forms, end, stop),
        expression_signals(source, forms, start, stop)
            == expression_signals(source, forms, child_start, child_stop)
                + expression_signals(source, forms, end, stop),
{
    reveal_with_fuel(expression_references, 1);
    reveal_with_fuel(expression_signals, 1);
    let (i, j) = choose|a: int, b: int| start < a <= b <= end
        && #[trigger] expression_child_range(source, forms, start, end, a, b);
    assert(i == child_start && j == child_stop);
    let witness = choose|builtin: Option<ExpressionHead>|
        #[trigger] list_head_matches(source, forms, start + 1, builtin);
    same_expression_head(source, forms, start + 1, builtin, witness);
}

pub(super) proof fn first_cast_reference(
    source: &str, forms: Seq<Form>, root: int, stop: int, child_start: int, child_stop: int,
)
    requires
        0 <= root && root + 2 < forms[root]->List_end <= stop <= forms.len(),
        expression_child_range(source, forms, root, forms[root]->List_end as int, child_start, child_stop),
        list_head_matches(source, forms, root + 1, Some(ExpressionHead::As)),
    ensures
        expression_references(source, forms, root, stop).len() > 0,
        expression_references(source, forms, root, stop)[0]
            == (ExpressionReference {
                kind: ExpressionReferenceKind::CastType, form: (root + 2) as usize, span: form_span(forms[root + 2]),
            }),
{
    let end = forms[root]->List_end as int;
    assert forall|i: int, j: int| #[trigger] expression_child_range(source, forms, root, end, i, j)
        implies i == child_start && j == child_stop by {
        same_child_interval(source, forms, root, end, child_start, child_stop, i, j);
    };
    list_reference_order(source, forms, root, stop, end, child_start, child_stop, Some(ExpressionHead::As));
}

/// 式の値として参照される無修飾の信号名を、元ソース順の構文木添字で表す。
#[verifier::opaque]
pub closed spec fn expression_signals(source: &str, forms: Seq<Form>, start: int, stop: int) -> Seq<usize>
    decreases stop - start,
{
    if !(0 <= start < stop <= forms.len()) {
        Seq::empty()
    } else {
        match forms[start] {
            Form::Atom { kind, .. } =>
                (if kind is Name { seq![start as usize] } else { Seq::empty() })
                    + expression_signals(source, forms, start + 1, stop),
            Form::List { end, .. } => {
                if start < end <= stop && exists|a: int, b: int| start < a <= b <= end
                    && #[trigger] expression_child_range(source, forms, start, end as int, a, b)
                {
                    let (a, b) = choose|a: int, b: int| start < a <= b <= end
                        && #[trigger] expression_child_range(source, forms, start, end as int, a, b);
                    expression_signals(source, forms, a, b)
                        + expression_signals(source, forms, end as int, stop)
                } else {
                    Seq::empty()
                }
            },
        }
    }
}

pub(super) proof fn bare_signal_index(source: &str, forms: Seq<Form>, first: int, end: int)
    requires
        0 <= first < end <= forms.len() <= usize::MAX, end == first + 1,
        forms[first] is Atom, forms[first]->Atom_kind is Name,
    ensures expression_signals(source, forms, first, end) == seq![first as usize],
{
    reveal_with_fuel(expression_signals, 2);
}

/// リスト単体の信号列は、値を取る子式の信号列に等しい。
pub(super) proof fn list_child_signals(
    source: &str, forms: Seq<Form>, root: int, end: int, first: int, stop: int, head: ExpressionHead,
)
    requires
        root < first <= stop <= end,
        expression_child_range(source, forms, root, end, first, stop),
        list_head_matches(source, forms, root + 1, Some(head)),
    ensures expression_signals(source, forms, root, end) == expression_signals(source, forms, first, stop),
{
    assert forall|i: int, j: int| #[trigger] expression_child_range(source, forms, root, end, i, j)
        implies i == first && j == stop by {
        same_child_interval(source, forms, root, end, first, stop, i, j);
    };
    list_reference_order(source, forms, root, end, end, first, stop, Some(head));
    assert(expression_signals(source, forms, end, end) == Seq::<usize>::empty()) by {
        reveal_with_fuel(expression_signals, 1);
    };
}

pub(super) proof fn direct_name_in_signal_index(
    source: &str, forms: Seq<Form>, first: int, end: int, name: usize,
)
    requires
        forms.len() <= usize::MAX, complete_list_indices(forms),
        expression_region(forms, first, end),
        direct_form_in_range(forms, first, end, name as int),
        forms[name as int] is Atom && forms[name as int]->Atom_kind is Name,
        expression_forest(source, forms, first, end),
    ensures expression_signals(source, forms, first, end).contains(name),
    decreases end - first,
{
    reveal(direct_form_in_range);
    reveal(expression_region);
    reveal(complete_list_indices);
    reveal_with_fuel(expression_signals, 1);
    reveal_with_fuel(expression_forest, 1);
    let signals = expression_signals(source, forms, first, end);
    if first == name {
        assert(signals[0] == name);
    } else {
        let next = after_form(forms, first);
        assert(first < next <= name < end);
        assert(direct_form_in_range(forms, next, end, name as int));
        assert(expression_region(forms, next, end));
        direct_name_in_signal_index(source, forms, next, end, name);
        let suffix = expression_signals(source, forms, next, end);
        let i = choose|i: int| 0 <= i < suffix.len() && suffix[i] == name;
        assert(signals[signals.len() - suffix.len() + i] == name);
    }
}

proof fn same_child_interval(
    source: &str, forms: Seq<Form>, first: int, end: int, a: int, b: int, u: int, v: int,
)
    requires
        expression_child_range(source, forms, first, end, a, b),
        expression_child_range(source, forms, first, end, u, v),
    ensures a == u && b == v, b == end || (a < b && b == after_form(forms, a)),
{
    let left = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, first + 1, head)
        && arguments_match(forms, first + 2, end, head, a, b);
    let right = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, first + 1, head)
        && arguments_match(forms, first + 2, end, head, u, v);
    same_expression_head(source, forms, first + 1, left, right);
}

/// 引数の式区間が裸の信号名だけなら、その添字が信号索引の先頭にあることを示す。
pub(super) proof fn first_named_child_signal(
    source: &str, forms: Seq<Form>, first: int, stop: int, name: usize,
)
    requires
        0 <= first < stop <= forms.len() <= usize::MAX,
        forms[first] is List,
        first < name < name + 1 <= forms[first]->List_end <= stop,
        forms[name as int] is Atom && forms[name as int]->Atom_kind is Name,
        expression_child_range(source, forms, first, forms[first]->List_end as int, name as int, name + 1),
    ensures
        expression_signals(source, forms, first, stop).len() > 0,
        expression_signals(source, forms, first, stop)[0] == name,
{
    reveal_with_fuel(expression_signals, 1);
    let end = forms[first]->List_end as int;
    let (a, b) = choose|a: int, b: int| first < a <= b <= end
        && #[trigger] expression_child_range(source, forms, first, end, a, b);
    same_child_interval(source, forms, first, end, a, b, name as int, name + 1);
    bare_signal_index(source, forms, a, b);
}

pub(super) proof fn call_argument_signal_index(
    source: &str, forms: Seq<Form>, first: int, stop: int, reference: int, name: usize,
)
    requires
        forms.len() <= usize::MAX, complete_list_indices(forms), nested_list_indices(forms),
        expression_region(forms, first, stop), expression_forest(source, forms, first, stop),
        0 <= reference < expression_references(source, forms, first, stop).len(),
        ({
            let indexed = expression_references(source, forms, first, stop)[reference];
            let call = indexed.form - 1;
            &&& indexed.kind is Callee && 0 <= call < forms.len() && forms[call] is List
            &&& direct_form_in_range(forms, call + 2, forms[call]->List_end as int, name as int)
            &&& name < forms.len() && forms[name as int] is Atom && forms[name as int]->Atom_kind is Name
        }),
    ensures expression_signals(source, forms, first, stop).contains(name),
    decreases stop - first,
{
    reveal_with_fuel(expression_references, 1);
    reveal_with_fuel(expression_signals, 1);
    reveal_with_fuel(expression_forest, 1);
    reveal(expression_region);
    let refs = expression_references(source, forms, first, stop);
    let signals = expression_signals(source, forms, first, stop);
    assert(0 <= first < stop <= forms.len());
    match forms[first] {
        Form::Atom { .. } => {
            call_argument_signal_index(source, forms, first + 1, stop, reference, name);
            let tail = expression_signals(source, forms, first + 1, stop);
            let i = choose|i: int| 0 <= i < tail.len() && tail[i] == name;
            assert(signals[signals.len() - tail.len() + i] == name);
        },
        Form::List { end, .. } => {
            let (a, b) = choose|a: int, b: int| first < a <= b <= end
                && #[trigger] expression_child_range(source, forms, first, end as int, a, b);
            let (u, v) = choose|u: int, v: int| first < u <= v <= end
                && #[trigger] expression_child_range(source, forms, first, end as int, u, v)
                && expression_forest(source, forms, u, v);
            let head = choose|head: Option<ExpressionHead>| #[trigger] list_head_matches(source, forms, first + 1, head);
            same_child_interval(source, forms, first, end as int, a, b, u, v);
            child_expression_region(forms, first, end as int, a, b);
            let here = local_reference(forms, first, end as int, head);
            let children = expression_references(source, forms, a, b);
            let child_signals = expression_signals(source, forms, a, b);
            let tail_signals = expression_signals(source, forms, end as int, stop);
            if reference < here.len() {
                assert(refs[reference] == here[reference]);
                assert(head is None && refs[reference].form == first + 1);
                let witness = choose|candidate: Option<ExpressionHead>|
                    #[trigger] list_head_matches(source, forms, first + 1, candidate)
                        && arguments_match(forms, first + 2, end as int, candidate, a, b);
                same_expression_head(source, forms, first + 1, head, witness);
                assert(a == first + 2 && b == end);
                direct_name_in_signal_index(source, forms, a, b, name);
                let i = choose|i: int| 0 <= i < child_signals.len() && child_signals[i] == name;
                assert(signals[i] == name);
            } else if reference < here.len() + children.len() {
                let offset = reference - here.len();
                assert(refs[reference] == children[offset]);
                call_argument_signal_index(source, forms, a, b, offset, name);
                let i = choose|i: int| 0 <= i < child_signals.len() && child_signals[i] == name;
                assert(signals[i] == name);
            } else {
                let offset = reference - here.len() - children.len();
                call_argument_signal_index(source, forms, end as int, stop, offset, name);
                let i = choose|i: int| 0 <= i < tail_signals.len() && tail_signals[i] == name;
                assert(signals[child_signals.len() + i] == name);
            }
        },
    }
}

pub(super) open spec fn signal_indices_in_order(signals: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < signals.len()
        ==> (#[trigger] signals[i]) < (#[trigger] signals[j])
}

pub(super) proof fn expression_signals_in_order(source: &str, forms: Seq<Form>, first: int, stop: int)
    requires forms.len() <= usize::MAX,
    ensures signal_indices_in_order(expression_signals(source, forms, first, stop)),
    decreases stop - first,
{
    reveal_with_fuel(expression_signals, 1);
    if 0 <= first < stop <= forms.len() {
        let whole = expression_signals(source, forms, first, stop);
        match forms[first] {
            Form::Atom { kind, .. } => {
                let tail = expression_signals(source, forms, first + 1, stop);
                expression_signals_in_order(source, forms, first + 1, stop);
                assert forall|i: int, j: int| 0 <= i < j < whole.len()
                    implies (#[trigger] whole[i]) < (#[trigger] whole[j]) by {
                    if kind is Name {
                        if i == 0 {
                            assert(whole[i] == first && whole[j] == tail[j - 1]);
                            expression_signal_evidence(source, forms, first + 1, stop, j - 1);
                        } else {
                            assert(whole[i] == tail[i - 1] && whole[j] == tail[j - 1]);
                        }
                    } else {
                        assert(whole == tail);
                    }
                };
            },
            Form::List { end, .. } => {
                if first < end <= stop && exists|a: int, b: int| first < a <= b <= end
                    && #[trigger] expression_child_range(source, forms, first, end as int, a, b)
                {
                    let (a, b) = choose|a: int, b: int| first < a <= b <= end
                        && #[trigger] expression_child_range(source, forms, first, end as int, a, b);
                    let children = expression_signals(source, forms, a, b);
                    let tail = expression_signals(source, forms, end as int, stop);
                    expression_signals_in_order(source, forms, a, b);
                    expression_signals_in_order(source, forms, end as int, stop);
                    assert forall|i: int, j: int| 0 <= i < j < whole.len()
                        implies (#[trigger] whole[i]) < (#[trigger] whole[j]) by {
                        let cut = children.len();
                        if j < cut {
                            assert(whole[i] == children[i] && whole[j] == children[j]);
                        } else if i >= cut {
                            assert(whole[i] == tail[i - cut] && whole[j] == tail[j - cut]);
                        } else {
                            assert(whole[i] == children[i] && whole[j] == tail[j - cut]);
                            expression_signal_evidence(source, forms, a, b, i);
                            expression_signal_evidence(source, forms, end as int, stop, j - cut);
                        }
                    };
                }
            },
        }
    }
}

pub(super) proof fn expression_signal_evidence(
    source: &str, forms: Seq<Form>, start: int, stop: int, position: int,
)
    requires
        forms.len() <= usize::MAX,
        0 <= position < expression_signals(source, forms, start, stop).len(),
    ensures
        ({
            let index = expression_signals(source, forms, start, stop)[position] as int;
            0 <= start <= index < stop <= forms.len()
                && forms[index] is Atom && forms[index]->Atom_kind is Name
        }),
    decreases stop - start,
{
    reveal_with_fuel(expression_signals, 1);
    assert(0 <= start < stop <= forms.len());
    let result = expression_signals(source, forms, start, stop);
    match forms[start] {
        Form::Atom { kind, .. } => {
            let prefix = if kind is Name { seq![start as usize] } else { Seq::empty() };
            let tail = expression_signals(source, forms, start + 1, stop);
            assert(result == prefix + tail);
            if position >= prefix.len() {
                assert(result[position] == tail[position - prefix.len()]);
                expression_signal_evidence(source, forms, start + 1, stop, position - prefix.len());
            } else {
                assert(kind is Name && position == 0 && result[position] == start);
            }
        },
        Form::List { end, .. } => {
            assert(start < end <= stop);
            let (a, b) = choose|a: int, b: int| start < a <= b <= end
                && #[trigger] expression_child_range(source, forms, start, end as int, a, b);
            let children = expression_signals(source, forms, a, b);
            let tail = expression_signals(source, forms, end as int, stop);
            assert(result == children + tail);
            if position < children.len() {
                assert(result[position] == children[position]);
                expression_signal_evidence(source, forms, a, b, position);
            } else {
                assert(result[position] == tail[position - children.len()]);
                expression_signal_evidence(source, forms, end as int, stop, position - children.len());
            }
        },
    }
}

#[verifier::opaque]
spec fn pending_signals(source: &str, forms: Seq<Form>, pending: Seq<Range<usize>>) -> Seq<usize>
    decreases pending.len(),
{
    if pending.len() == 0 {
        Seq::empty()
    } else {
        expression_signals(source, forms, pending.last().start as int, pending.last().end as int)
            + pending_signals(source, forms, pending.drop_last())
    }
}

/// 半開区間に並ぶ式を回路文法に照らして判定する。
///
/// リストでは、専用引数を除いた子式列と、そのリストの後に続く式列を判定する。
#[verifier::opaque]
pub closed spec fn expression_forest(source: &str, forms: Seq<Form>, start: int, stop: int) -> bool
    decreases stop - start,
{
    &&& 0 <= start <= stop <= forms.len()
    &&& (start == stop || match forms[start] {
        Form::Atom { .. } => expression_atom_at(source, forms[start])
            && expression_forest(source, forms, start + 1, stop),
        Form::List { end, .. } => {
            &&& start < end <= stop
            &&& exists|child_start: int, child_stop: int|
                #[trigger] expression_child_range(source, forms, start, end as int, child_start, child_stop)
                && start < child_start <= child_stop <= end
                && expression_forest(source, forms, child_start, child_stop)
                && expression_forest(source, forms, end as int, stop)
        },
    })
}

/// 文法に適合した式列の先頭がリストなら、専用の引数を除いた子式列も文法に適合する。
pub(super) proof fn first_expression_children(
    source: &str, forms: Seq<Form>, start: int, stop: int,
)
    requires expression_forest(source, forms, start, stop), 0 <= start < stop <= forms.len(), forms[start] is List,
    ensures ({
        let end = forms[start]->List_end as int;
        &&& start < end <= stop
        &&& exists|first: int, last: int|
            #[trigger] expression_child_range(source, forms, start, end, first, last)
                && expression_forest(source, forms, first, last)
    }),
{
    reveal_with_fuel(expression_forest, 1);
}

/// 式列を先頭から検査したときの最初の診断を表す。
///
/// リスト自身の違反を優先し、局所文法に合う場合は子式、後続の式の順に調べる。
#[verifier::opaque]
pub closed spec fn expression_forest_error(
    source: &str, forms: Seq<Form>, start: int, stop: int, error: (HeaderError, Range<usize>),
) -> bool
    decreases stop - start,
{
    &&& 0 <= start < stop <= forms.len()
    &&& match forms[start] {
        Form::Atom { span, .. } => {
            if expression_atom_at(source, forms[start]) {
                expression_forest_error(source, forms, start + 1, stop, error)
            } else {
                error == (HeaderError::ExpectedExpression, span)
            }
        },
        Form::List { span, end } => {
            &&& start < end <= stop
            &&& if exists|i: int, j: int| #[trigger] expression_child_range(source, forms, start, end as int, i, j) {
                exists|i: int, j: int| #[trigger] expression_child_range(source, forms, start, end as int, i, j)
                    && start < i <= j <= end
                    && (expression_forest_error(source, forms, i, j, error)
                        || (expression_forest(source, forms, i, j)
                            && expression_forest_error(source, forms, end as int, stop, error)))
            } else {
                span.end > 0 && expression_list_error(source, forms, start, end as int, (span.end - 1) as usize, error)
            }
        },
    }
}

/// 同じ UTF-8 本文から得たフォーム列では、式の文法判定と最初の診断が一致する。
pub(super) proof fn expression_forest_agrees_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, start: int, stop: int,
    error: (HeaderError, Range<usize>),
)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures
        expression_forest(left, forms, start, stop) == expression_forest(right, forms, start, stop),
        expression_forest_error(left, forms, start, stop, error)
            == expression_forest_error(right, forms, start, stop, error),
    decreases stop - start,
{
    if 0 <= start < stop <= forms.len() {
        match forms[start] {
            Form::Atom { .. } => {
                expression_forest_agrees_on_bytes(left, right, forms, start + 1, stop, error);
            },
            Form::List { span, end } => {
                let next = end as int;
                if start < next <= stop {
                    assert forall|head: Option<ExpressionHead>|
                        #![trigger list_head_matches(left, forms, start + 1, head)]
                        #![trigger list_head_matches(right, forms, start + 1, head)]
                        list_head_matches(left, forms, start + 1, head)
                        == list_head_matches(right, forms, start + 1, head) by {};
                    assert forall|i: int, j: int|
                        #![trigger expression_child_range(left, forms, start, next, i, j)]
                        #![trigger expression_child_range(right, forms, start, next, i, j)]
                        expression_child_range(left, forms, start, next, i, j)
                        == expression_child_range(right, forms, start, next, i, j) by {
                        if expression_child_range(left, forms, start, next, i, j) {
                            let head = choose|head: Option<ExpressionHead>|
                                #[trigger] list_head_matches(left, forms, start + 1, head)
                                && arguments_match(forms, start + 2, next, head, i, j);
                            assert(list_head_matches(right, forms, start + 1, head));
                        }
                        if expression_child_range(right, forms, start, next, i, j) {
                            let head = choose|head: Option<ExpressionHead>|
                                #[trigger] list_head_matches(right, forms, start + 1, head)
                                && arguments_match(forms, start + 2, next, head, i, j);
                            assert(list_head_matches(left, forms, start + 1, head));
                        }
                    };
                    if exists|i: int, j: int| #[trigger] expression_child_range(left, forms, start, next, i, j) {
                        let (a, b) = choose|i: int, j: int|
                            #[trigger] expression_child_range(left, forms, start, next, i, j);
                        expression_forest_agrees_on_bytes(left, right, forms, a, b, error);
                        expression_forest_agrees_on_bytes(left, right, forms, next, stop, error);
                        assert forall|i: int, j: int|
                            #[trigger] expression_child_range(left, forms, start, next, i, j)
                            implies i == a && j == b by {
                            same_child_interval(left, forms, start, next, a, b, i, j);
                        };
                    } else if span.end > 0 {
                        let closing = (span.end - 1) as usize;
                        assert(expression_list_error(left, forms, start, next, closing, error)
                            == expression_list_error(right, forms, start, next, closing, error)) by {
                            if expression_list_error(left, forms, start, next, closing, error)
                                && !expression_list_error(right, forms, start, next, closing, error)
                            {
                                let head = choose|head: Option<ExpressionHead>|
                                    #[trigger] list_head_matches(left, forms, start + 1, head)
                                    && argument_shape_error(forms, start + 2, next, closing, head) == Some(error);
                                assert(list_head_matches(right, forms, start + 1, head));
                            }
                            if expression_list_error(right, forms, start, next, closing, error)
                                && !expression_list_error(left, forms, start, next, closing, error)
                            {
                                let head = choose|head: Option<ExpressionHead>|
                                    #[trigger] list_head_matches(right, forms, start + 1, head)
                                    && argument_shape_error(forms, start + 2, next, closing, head) == Some(error);
                                assert(list_head_matches(left, forms, start + 1, head));
                            }
                        };
                    }
                }
            },
        }
    }
    reveal(expression_forest);
    reveal(expression_forest_error);
}

/// 文法に適合する式列には、式列の診断が成立しない。
pub(super) proof fn expression_forest_match_excludes_error(
    source: &str, forms: Seq<Form>, start: int, stop: int, error: (HeaderError, Range<usize>),
)
    requires expression_forest(source, forms, start, stop),
    ensures !expression_forest_error(source, forms, start, stop, error),
    decreases stop - start,
{
    reveal(expression_forest);
    reveal(expression_forest_error);
    if expression_forest_error(source, forms, start, stop, error) {
        match forms[start] {
            Form::Atom { .. } => {
                expression_forest_match_excludes_error(source, forms, start + 1, stop, error);
            },
            Form::List { end, .. } => {
                let next = end as int;
                let (a, b) = choose|a: int, b: int| start < a <= b <= next
                    && #[trigger] expression_child_range(source, forms, start, next, a, b)
                    && expression_forest(source, forms, a, b);
                let (i, j) = choose|i: int, j: int| start < i <= j <= next
                    && #[trigger] expression_child_range(source, forms, start, next, i, j)
                    && (expression_forest_error(source, forms, i, j, error)
                        || (expression_forest(source, forms, i, j)
                            && expression_forest_error(source, forms, next, stop, error)));
                same_child_interval(source, forms, start, next, a, b, i, j);
                if expression_forest_error(source, forms, i, j, error) {
                    expression_forest_match_excludes_error(source, forms, i, j, error);
                } else {
                    expression_forest_match_excludes_error(source, forms, next, stop, error);
                }
            },
        }
    }
}

/// リスト自身、子式、後続の式の検査順に従うと、式列の診断値は一意に定まる。
pub(super) proof fn expression_forest_errors_agree(
    source: &str, forms: Seq<Form>, start: int, stop: int,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        expression_forest_error(source, forms, start, stop, left),
        expression_forest_error(source, forms, start, stop, right),
    ensures left == right,
    decreases stop - start,
{
    reveal(expression_forest_error);
    match forms[start] {
        Form::Atom { .. } => {
            if expression_atom_at(source, forms[start]) {
                expression_forest_errors_agree(source, forms, start + 1, stop, left, right);
            }
        },
        Form::List { span, end } => {
            let next = end as int;
            if exists|i: int, j: int| #[trigger] expression_child_range(source, forms, start, next, i, j) {
                let (a, b) = choose|a: int, b: int| start < a <= b <= next
                    && #[trigger] expression_child_range(source, forms, start, next, a, b)
                    && (expression_forest_error(source, forms, a, b, left)
                        || (expression_forest(source, forms, a, b)
                            && expression_forest_error(source, forms, next, stop, left)));
                let (i, j) = choose|i: int, j: int| start < i <= j <= next
                    && #[trigger] expression_child_range(source, forms, start, next, i, j)
                    && (expression_forest_error(source, forms, i, j, right)
                        || (expression_forest(source, forms, i, j)
                            && expression_forest_error(source, forms, next, stop, right)));
                same_child_interval(source, forms, start, next, a, b, i, j);
                if expression_forest(source, forms, a, b) {
                    expression_forest_match_excludes_error(source, forms, a, b, left);
                    expression_forest_match_excludes_error(source, forms, a, b, right);
                    expression_forest_errors_agree(source, forms, next, stop, left, right);
                } else {
                    expression_forest_errors_agree(source, forms, a, b, left, right);
                }
            } else {
                same_expression_list_error(source, forms, start, next, (span.end - 1) as usize, left, right);
            }
        },
    }
}

/// 名前、1 ビットを表す 0 と 1、ビット列をアトムとして受理する。
pub(super) open spec fn expression_atom_at(source: &str, form: Form) -> bool {
    match form {
        Form::Atom { kind, span } => {
            &&& span.start < span.end <= source.spec_bytes().len()
            &&& (kind is Name || kind is Binary || kind is Hexadecimal
                || (kind is Natural && {
                    let word = source.spec_bytes()[span.start as int..span.end as int];
                    word == "0".spec_bytes() || word == "1".spec_bytes()
                }))
        },
        _ => false,
    }
}

/// 走査区間に含まれるリストが、区間の外まで延びないことを表す。
#[verifier::opaque]
pub open spec fn expression_region(forms: Seq<Form>, start: int, stop: int) -> bool {
    &&& 0 <= start <= stop <= forms.len()
    &&& forall|i: int| start <= i < stop && #[trigger] forms[i] is List
        ==> forms[i]->List_end <= stop
}

proof fn shrink_expression_region(forms: Seq<Form>, start: int, next: int, stop: int)
    requires expression_region(forms, start, stop), start <= next <= stop,
    ensures expression_region(forms, next, stop),
{
    reveal(expression_region);
}

proof fn child_expression_region(forms: Seq<Form>, index: int, end: int, start: int, stop: int)
    requires
        0 <= index < start <= stop <= end <= forms.len(),
        forms[index] is List && forms[index]->List_end == end,
        stop == end || (start < stop && stop == after_form(forms, start)),
        nested_list_indices(forms),
    ensures expression_region(forms, start, stop),
{
    reveal(expression_region);
    reveal(nested_list_indices);
    assert forall|i: int| start <= i < stop && #[trigger] forms[i] is List
        implies forms[i]->List_end <= stop by {
        if stop == end {
            assert(index < i < end);
        } else if i != start {
            if forms[start] is Atom {
                assert(stop == start + 1);
            } else {
                assert(start < i < forms[start]->List_end);
            }
        }
    };
}

fn read_expression_atom(source: &str, forms: &[Form], index: usize) -> (accepted: bool)
    requires
        index < forms@.len(),
        forms@[index as int] is Atom,
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures accepted == expression_atom_at(source, forms@[index as int]),
{
    let form = &forms[index];
    let Form::Atom { kind: atom_kind, span: atom_span } = form else {
        proof { assert(false); }
        return false;
    };
    proof {
        reveal(form_spans_valid);
        encode_utf8_valid_utf8(source@);
        assert(form_span(*form) == *atom_span);
    }
    let word = source_span(source, atom_span.start, atom_span.end);
    let accepted = expression_atom(*atom_kind, word);
    proof {
        encode_utf8_decode_utf8(word@);
        encode_utf8_decode_utf8("0"@);
        encode_utf8_decode_utf8("1"@);
    }
    accepted
}

spec fn pending_expressions_valid(source: &str, forms: Seq<Form>, pending: Seq<Range<usize>>) -> bool
    decreases pending.len(),
{
    pending.len() == 0 || (expression_forest(source, forms, pending.last().start as int, pending.last().end as int)
        && pending_expressions_valid(source, forms, pending.drop_last()))
}

spec fn expression_work_error(
    source: &str, forms: Seq<Form>, start: int, stop: int, pending: Seq<Range<usize>>,
    error: (HeaderError, Range<usize>),
) -> bool {
    expression_forest_error(source, forms, start, stop, error)
        || (expression_forest(source, forms, start, stop)
            && pending_expressions_error(source, forms, pending, error))
}

spec fn pending_expressions_error(
    source: &str, forms: Seq<Form>, pending: Seq<Range<usize>>, error: (HeaderError, Range<usize>),
) -> bool
    decreases pending.len(),
{
    pending.len() > 0 && {
        let start = pending.last().start as int;
        let stop = pending.last().end as int;
        expression_forest_error(source, forms, start, stop, error)
            || (expression_forest(source, forms, start, stop)
                && pending_expressions_error(source, forms, pending.drop_last(), error))
    }
}

/// 保留区間の合計長を停止性の検査に使う。
spec fn pending_expression_width(pending: Seq<Range<usize>>) -> nat
    decreases pending.len(),
{
    if pending.len() == 0 { 0 }
    else { (pending.last().end - pending.last().start) as nat + pending_expression_width(pending.drop_last()) }
}

/// 入力全体を回路式の列として読み、呼び出し名と型参照を元ソース順で取り出す。
///
/// 各添字は、同じ入力に [`parse`] を適用して得た構文木を指す。
/// 局所信号名、フィールド名、専用フォームの先頭語は参照一覧に含めない。
///
/// # Errors
///
/// 字句や S 式の違反を優先し、入力を構文木にできた場合は式文法の最初の違反を返す。
pub fn index_expression_references(
    source: &str,
) -> (result: Result<Vec<ExpressionReference>, CircuitFormError>)
    ensures expression_source_reference_result(source, result),
{
    let forms = match parse(source) {
        Ok(forms) => forms,
        Err(error) => return Err(CircuitFormError::Syntax(error)),
    };
    let end = forms.len();
    proof { reveal(expression_region); }
    match inspect_expressions(source, forms.as_slice(), 0..end, true) {
        Ok(items) => Ok(items),
        Err((kind, span)) => Err(CircuitFormError::Header { kind, span }),
    }
}

/// 入力全体の式参照索引または最初の診断を、厳格な構文木と式文法に結び付ける。
pub closed spec fn expression_source_reference_result(
    source: &str, result: Result<Vec<ExpressionReference>, CircuitFormError>,
) -> bool {
    match result {
        Err(CircuitFormError::Syntax(error)) =>
            !well_formed_sexpr(source) && syntax_error_evidence(source, error),
        _ => if let Some(forms) = sexpr_form_model(source) {
            let end = forms.len() as int;
            &&& (result.is_ok() <==> expression_forest(source, forms, 0, end))
            &&& match result {
                Ok(items) => items@ == expression_references(source, forms, 0, end)
                    && (forall|i: int| 0 <= i < items@.len()
                        ==> expression_reference_in_source(source, forms, #[trigger] items@[i])),
                Err(CircuitFormError::Header { kind, span }) =>
                    expression_forest_error(source, forms, 0, end, (kind, span)),
                _ => false,
            }
        } else {
            false
        },
    }
}

/// 式列の索引に必要な構文木と元ソースの対応、および走査区間の境界を表す。
pub open spec fn expression_index_region(source: &str, forms: Seq<Form>, roots: Range<usize>) -> bool {
    &&& expression_region(forms, roots.start as int, roots.end as int)
    &&& complete_list_indices(forms)
    &&& nested_list_indices(forms)
    &&& list_source_delimiters(source, forms, false)
    &&& form_spans_valid(source, forms, source.spec_bytes().len() as int)
}

pub(super) fn inspect_expressions(
    source: &str, forms: &[Form], roots: Range<usize>, collect: bool,
) -> (result: Result<Vec<ExpressionReference>, (HeaderError, Range<usize>)>)
    requires expression_index_region(source, forms@, roots),
    ensures
        result.is_ok() <==> expression_forest(source, forms@, roots.start as int, roots.end as int),
        collect ==> (result matches Ok(items) ==> items@ == expression_references(source, forms@, roots.start as int, roots.end as int)
            && (forall|i: int| 0 <= i < items@.len()
                ==> expression_reference_in_source(source, forms@, #[trigger] items@[i]))),
        forall|error: (HeaderError, Range<usize>)| #[trigger] expression_forest_error(
            source, forms@, roots.start as int, roots.end as int, error,
        ) <==> result == Err(error),
{
    let mut references = Vec::new();
    inspect_expressions_into(source, forms, roots, collect, &mut references, false, &mut Vec::new())?;
    Ok(references)
}

/// 式を検査し、収集を指定した場合は参照を既存の配列の末尾に加える。
///
/// # Errors
///
/// 最初の違反を返す。違反より前に加えた参照は配列に残る。
pub(super) fn inspect_expressions_into(
    source: &str, forms: &[Form], roots: Range<usize>, collect: bool,
    references: &mut Vec<ExpressionReference>,
    collect_signals: bool, signals: &mut Vec<usize>,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires expression_index_region(source, forms@, roots),
    ensures
        result.is_ok() <==> expression_forest(source, forms@, roots.start as int, roots.end as int),
        !collect ==> final(references)@ == old(references)@,
        !collect_signals ==> final(signals)@ == old(signals)@,
        final(signals)@.len() >= old(signals)@.len(),
        final(signals)@.take(old(signals)@.len() as int) == old(signals)@,
        collect_signals && result.is_ok() ==>
            final(signals)@ == old(signals)@ + expression_signals(source, forms@, roots.start as int, roots.end as int),
        collect && result.is_ok() ==>
            final(references)@ == old(references)@
                + expression_references(source, forms@, roots.start as int, roots.end as int),
        final(references)@.len() >= old(references)@.len(),
        final(references)@.take(old(references)@.len() as int) == old(references)@,
        forall|i: int| old(references)@.len() <= i < final(references)@.len()
            ==> expression_reference_in_source(source, forms@, #[trigger] final(references)@[i]),
        forall|error: (HeaderError, Range<usize>)| #[trigger] expression_forest_error(
            source, forms@, roots.start as int, roots.end as int, error,
        ) <==> result == Err(error),
{
    let mut sequence = roots.start..roots.end;
    let mut pending: Vec<Range<usize>> = Vec::new();
    let ghost initial = references@;
    let ghost initial_signals = signals@;
    proof {
        reveal(pending_references);
        reveal(pending_signals);
    }
    // 式を処理すると未処理区間の合計長が減る。空区間からの復帰では保留数が減る。
    while sequence.start < sequence.end || pending.len() > 0
        invariant
            initial == old(references)@,
            complete_list_indices(forms@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            expression_region(forms@, sequence.start as int, sequence.end as int),
            forall|i: int| 0 <= i < pending@.len()
                ==> #[trigger] expression_region(forms@, pending@[i].start as int, pending@[i].end as int),
            expression_forest(source, forms@, roots.start as int, roots.end as int)
                == (expression_forest(source, forms@, sequence.start as int, sequence.end as int)
                    && pending_expressions_valid(source, forms@, pending@)),
            forall|error: (HeaderError, Range<usize>)| #[trigger] expression_work_error(
                source, forms@, sequence.start as int, sequence.end as int, pending@, error,
            ) <==> expression_forest_error(source, forms@, roots.start as int, roots.end as int, error),
            collect ==> references@
                + expression_references(source, forms@, sequence.start as int, sequence.end as int)
                + pending_references(source, forms@, pending@)
                =~= initial + expression_references(source, forms@, roots.start as int, roots.end as int),
            !collect ==> references@ == initial,
            initial_signals == old(signals)@,
            !collect_signals ==> signals@ == initial_signals,
            signals@.len() >= initial_signals.len(),
            signals@.take(initial_signals.len() as int) == initial_signals,
            collect_signals ==> signals@
                + expression_signals(source, forms@, sequence.start as int, sequence.end as int)
                + pending_signals(source, forms@, pending@)
                =~= initial_signals + expression_signals(source, forms@, roots.start as int, roots.end as int),
            initial.len() <= references@.len(),
            references@.take(initial.len() as int) == initial,
            forall|i: int| initial.len() <= i < references@.len()
                ==> expression_reference_in_source(source, forms@, #[trigger] references@[i]),
        decreases pending_expression_width(pending@) + sequence.end - sequence.start, pending@.len(),
    {
        let ghost before = pending@;
        let ghost start = sequence.start as int;
        let ghost stop = sequence.end as int;
        let ghost emitted = references@;
        let ghost emitted_signals = signals@;
        proof {
            reveal_with_fuel(expression_forest, 2);
            reveal_with_fuel(expression_forest_error, 2);
            reveal(expression_region);
        }
        if sequence.start == sequence.end {
            assert(expression_references(source, forms@, start, stop) == Seq::empty()) by {
                reveal_with_fuel(expression_references, 1);
            }
            assert(expression_signals(source, forms@, start, stop) == Seq::empty()) by {
                reveal_with_fuel(expression_signals, 1);
            }
            let Some(next) = pending.pop() else {
                proof { assert(false); }
                return Ok(());
            };
            assert(before == pending@.push(next));
            assert(pending_references(source, forms@, before) ==
                expression_references(source, forms@, next.start as int, next.end as int)
                    + pending_references(source, forms@, pending@)) by {
                reveal_with_fuel(pending_references, 1);
            };
            assert(expression_region(forms@, next.start as int, next.end as int));
            assert(before.last() == next && before.drop_last() == pending@);
            assert(pending_expression_width(before)
                == pending_expression_width(pending@) + next.end - next.start);
            assert forall|error: (HeaderError, Range<usize>)| #[trigger] expression_work_error(
                source, forms@, next.start as int, next.end as int, pending@, error,
            ) <==> expression_forest_error(source, forms@, roots.start as int, roots.end as int, error) by {
                assert(expression_work_error(source, forms@, start, stop, before, error)
                    == expression_work_error(source, forms@, next.start as int, next.end as int, pending@, error));
            };
            assert(pending_signals(source, forms@, before) ==
                expression_signals(source, forms@, next.start as int, next.end as int)
                    + pending_signals(source, forms@, pending@)) by {
                reveal_with_fuel(pending_signals, 1);
            }
            sequence = next;
            continue;
        }

        let index = sequence.start;
        match &forms[index] {
            Form::Atom { kind, .. } => {
                if !read_expression_atom(source, forms, index) {
                    let error = (HeaderError::ExpectedExpression, form_span_exec(&forms[index]));
                    assert forall|reported: (HeaderError, Range<usize>)| #[trigger] expression_forest_error(
                        source, forms@, roots.start as int, roots.end as int, reported,
                    ) <==> reported == error by {
                        assert(expression_work_error(source, forms@, start, stop, before, reported) == (reported == error));
                    };
                    return Err(error);
                }
                assert forall|error: (HeaderError, Range<usize>)| #[trigger] expression_work_error(
                    source, forms@, start + 1, stop, before, error,
                ) <==> expression_forest_error(source, forms@, roots.start as int, roots.end as int, error) by {
                    assert(expression_work_error(source, forms@, start, stop, before, error)
                        == expression_work_error(source, forms@, start + 1, stop, before, error));
                };
                proof { shrink_expression_region(forms@, start, start + 1, stop); }
                assert(expression_references(source, forms@, start, stop)
                    == expression_references(source, forms@, start + 1, stop)) by {
                    reveal_with_fuel(expression_references, 1);
                }
                if collect_signals && matches!(kind, AtomKind::Name) {
                    signals.push(index);
                }
                assert(signals@ == if collect_signals && forms@[start]->Atom_kind is Name {
                    emitted_signals.push(index)
                } else { emitted_signals });
                assert(expression_signals(source, forms@, start, stop) ==
                    (if forms@[start]->Atom_kind is Name { seq![index] } else { Seq::empty() })
                        + expression_signals(source, forms@, start + 1, stop)) by {
                    reveal_with_fuel(expression_signals, 1);
                }
                sequence.start += 1;
            }
            Form::List { span, end } => {
                proof {
                    reveal(list_source_delimiters);
                    assert(list_delimited(source.spec_bytes(), forms@[start], false));
                }
                let ghost next = *end as int;
                let (children, builtin) = match expression_children(source, forms, index, *end, span.end - 1) {
                    Ok(parts) => parts,
                    Err(error) => {
                        assert forall|reported: (HeaderError, Range<usize>)| #[trigger] expression_forest_error(
                            source, forms@, roots.start as int, roots.end as int, reported,
                        ) <==> reported == error by {
                            if expression_forest_error(source, forms@, start, stop, reported) {
                                same_expression_list_error(source, forms@, start, next, (span.end - 1) as usize,
                                    error, reported);
                            }
                            assert(expression_work_error(source, forms@, start, stop, before, reported) == (reported == error));
                        };
                        return Err(error);
                    }
                };
                let ghost child_start = children.start as int;
                let ghost child_stop = children.end as int;
                proof {
                    list_reference_order(source, forms@, start, stop, next, child_start, child_stop, builtin);
                }
                if collect {
                    if builtin.is_none() {
                        references.push(indexed_reference(
                            source, forms, index + 1, *end, ExpressionReferenceKind::Callee,
                        ));
                    } else if matches!(builtin, Some(ExpressionHead::As)) {
                        assert(index + 2 < *end);
                        references.push(indexed_reference(
                            source, forms, index + 2, *end, ExpressionReferenceKind::CastType,
                        ));
                    }
                    assert(references@ =~= emitted + local_reference(forms@, start, next, builtin));
                }
                assert(expression_child_range(source, forms@, start, next, child_start, child_stop));
                assert(expression_forest(source, forms@, start, stop) ==
                    (expression_forest(source, forms@, child_start, child_stop)
                        && expression_forest(source, forms@, next, stop))) by {
                    if expression_forest(source, forms@, start, stop) {
                        let (i, j) = choose|i: int, j: int|
                            #[trigger] expression_child_range(source, forms@, start, next, i, j)
                            && start < i <= j <= next
                            && expression_forest(source, forms@, i, j)
                            && expression_forest(source, forms@, next, stop);
                        assert(i == child_start && j == child_stop);
                    }
                };
                proof {
                    child_expression_region(forms@, start, next, child_start, child_stop);
                    shrink_expression_region(forms@, start, next, stop);
                }
                // 親の残りを保留し、子式の診断を後続の式より優先する。
                if *end < sequence.end {
                    pending.push(*end..sequence.end);
                    assert(pending@.last() == (*end..sequence.end) && pending@.drop_last() == before);
                    assert(pending_references(source, forms@, pending@) ==
                        expression_references(source, forms@, next, stop)
                            + pending_references(source, forms@, before)) by {
                        reveal_with_fuel(pending_references, 1);
                    };
                    assert(pending_signals(source, forms@, pending@) ==
                        expression_signals(source, forms@, next, stop) + pending_signals(source, forms@, before)) by {
                        reveal_with_fuel(pending_signals, 1);
                    };
                    assert(pending_expression_width(pending@)
                        == pending_expression_width(before) + stop - next);
                } else {
                    assert(expression_signals(source, forms@, next, stop) == Seq::empty()) by {
                        reveal_with_fuel(expression_signals, 1);
                    };
                    assert(expression_references(source, forms@, next, stop) == Seq::empty()) by {
                        reveal_with_fuel(expression_references, 1);
                    }
                }
                assert forall|error: (HeaderError, Range<usize>)| #[trigger] expression_work_error(
                    source, forms@, child_start, child_stop, pending@, error,
                ) <==> expression_forest_error(source, forms@, roots.start as int, roots.end as int, error) by {
                    if expression_forest_error(source, forms@, start, stop, error) {
                        let (i, j) = choose|i: int, j: int|
                            #[trigger] expression_child_range(source, forms@, start, next, i, j)
                                && start < i <= j <= next
                                && (expression_forest_error(source, forms@, i, j, error)
                                    || (expression_forest(source, forms@, i, j)
                                        && expression_forest_error(source, forms@, next, stop, error)));
                        assert(i == child_start && j == child_stop);
                    }
                    assert(expression_work_error(source, forms@, start, stop, before, error)
                        == expression_work_error(source, forms@, child_start, child_stop, pending@, error));
                };
                sequence = children;
            }
        }
    }
    proof {
        reveal(expression_forest);
        reveal(expression_forest_error);
        reveal(expression_region);
        reveal(expression_references);
        reveal(pending_references);
        reveal(expression_signals);
        reveal(pending_signals);
    }
    assert forall|error: (HeaderError, Range<usize>)|
        !#[trigger] expression_forest_error(source, forms@, roots.start as int, roots.end as int, error) by {
        assert(!expression_work_error(source, forms@, sequence.start as int, sequence.end as int, pending@, error));
    };
    Ok(())
}


} // verus!
