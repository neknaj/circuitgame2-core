//! 式の並びを検査し、各リストでは子式を後続の式より先に調べる。

use super::expressions::expression_children;
#[cfg(verus_only)]
use super::expressions::{
    after_form, expression_child_range, expression_list_error, same_expression_list_error,
};
use super::*;

verus! {

/// 半開区間に並ぶ式を回路文法に照らして判定する。
///
/// リストでは、専用引数を除いた子式列と、そのリストの後に続く式列を判定する。
#[verifier::opaque]
pub(super) open spec fn expression_forest(source: &str, forms: Seq<Form>, start: int, stop: int) -> bool
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
pub(super) open spec fn expression_forest_error(
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
pub(super) open spec fn expression_region(forms: Seq<Form>, start: int, stop: int) -> bool {
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

/// 式列を左から調べ、リストの子式を処理してから後続の式に戻る。
///
/// # Errors
///
/// 有効な式の並びを構成できない場合は、違反の種別と入力上の範囲を返す。
pub(super) fn validate_expressions(
    source: &str, forms: &[Form], roots: Range<usize>,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        expression_region(forms@, roots.start as int, roots.end as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> expression_forest(source, forms@, roots.start as int, roots.end as int),
        forall|error: (HeaderError, Range<usize>)| #[trigger] expression_forest_error(
            source, forms@, roots.start as int, roots.end as int, error,
        ) <==> result == Err(error),
{
    let mut sequence = roots.start..roots.end;
    let mut pending: Vec<Range<usize>> = Vec::new();
    // 式を処理すると未処理区間の合計長が減る。空区間からの復帰では保留数が減る。
    while sequence.start < sequence.end || pending.len() > 0
        invariant
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
        decreases pending_expression_width(pending@) + sequence.end - sequence.start, pending@.len(),
    {
        let ghost before = pending@;
        let ghost start = sequence.start as int;
        let ghost stop = sequence.end as int;
        proof {
            reveal_with_fuel(expression_forest, 2);
            reveal_with_fuel(expression_forest_error, 2);
            reveal(expression_region);
        }
        if sequence.start == sequence.end {
            let Some(next) = pending.pop() else {
                proof { assert(false); }
                return Ok(());
            };
            assert(before == pending@.push(next));
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
            sequence = next;
            continue;
        }

        let index = sequence.start;
        match &forms[index] {
            Form::Atom { .. } => {
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
                sequence.start += 1;
            }
            Form::List { span, end } => {
                proof {
                    reveal(list_source_delimiters);
                    assert(list_delimited(source.spec_bytes(), forms@[start], false));
                }
                let ghost next = *end as int;
                let children = match expression_children(source, forms, index, *end, span.end - 1) {
                    Ok(children) => children,
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
                    assert(pending_expression_width(pending@)
                        == pending_expression_width(before) + stop - next);
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
    }
    assert forall|error: (HeaderError, Range<usize>)|
        !#[trigger] expression_forest_error(source, forms@, roots.start as int, roots.end as int, error) by {
        assert(!expression_work_error(source, forms@, sequence.start as int, sequence.end as int, pending@, error));
    };
    Ok(())
}


} // verus!
