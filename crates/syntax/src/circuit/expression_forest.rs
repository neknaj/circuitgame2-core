//! 式の並びを検査し、各リストでは子式を後続の式より先に調べる。

use super::expressions::expression_children;
#[cfg(verus_only)]
use super::expressions::{
    after_form, argument_matches, expression_child_range, expression_list_error, list_head_matches,
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
{
    reveal_with_fuel(expression_references, 1);
    let (i, j) = choose|a: int, b: int| start < a <= b <= end
        && #[trigger] expression_child_range(source, forms, start, end, a, b);
    assert(i == child_start && j == child_stop);
    let witness = choose|builtin: Option<ExpressionHead>|
        #[trigger] list_head_matches(source, forms, start + 1, builtin);
    same_expression_head(source, forms, start + 1, builtin, witness);
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
                    assert(expression_signals(source, forms@, start, stop)
                        == expression_signals(source, forms@, child_start, child_stop)
                            + expression_signals(source, forms@, next, stop)) by {
                        reveal_with_fuel(expression_signals, 1);
                        let (i, j) = choose|i: int, j: int| start < i <= j <= next
                            && #[trigger] expression_child_range(source, forms@, start, next, i, j);
                        assert(i == child_start && j == child_stop);
                    };
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
