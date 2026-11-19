use super::clauses::{read_named_clause, read_type};
use super::{AtomKind, Clause, Form, Head, HeaderError, check_directive_word, form_span_exec};
use core::ops::Range;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::clauses::enclosing_region_bounds_form;
#[cfg(verus_only)]
use super::{
    direct_form_in_range, directive_argument_error_span, directive_word_at, following_direct_form,
    form_region_ends_at, named_clause_error_span, named_clause_matches,
    node_end_is_following_direct_form, type_error_evidence, type_matches,
};
#[cfg(verus_only)]
use crate::{
    complete_list_indices, form_span, form_spans_valid, list_delimited, list_source_delimiters,
    nested_list_indices,
};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 無修飾名、または名前と型を並べたリストをポートとして認識する関係。
pub open spec fn port_matches(source: &str, forms: Seq<Form>, index: int, limit: int) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& (if forms[index] is List {
        let end = forms[index]->List_end as int;
        &&& end <= limit
        &&& directive_word_at(source, forms, index + 1, end, HeaderError::ExpectedName)
        &&& type_matches(source, forms, index + 2, end, end)
    } else {
        directive_word_at(source, forms, index, limit, HeaderError::ExpectedName)
    })
}

/// ポートの形、名前、型、余分な要素の順で最初の違反を表す。
pub open spec fn port_error_evidence(
    source: &str, forms: Seq<Form>, index: int, limit: int,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& {
        let form = forms[index];
        if form is List {
            let end = form->List_end as int;
            let close = (form_span(form).end - 1) as usize;
            let name = HeaderError::ExpectedName;
            &&& index < end <= limit
            &&& 0 < form_span(form).end <= source.spec_bytes().len()
            &&& source.spec_bytes()[close as int] == 41
            &&& (if directive_word_at(source, forms, index + 1, end, name) {
                type_error_evidence(source, forms, index + 2, end, close, kind, span)
                    || (kind == HeaderError::UnexpectedArgument && exists|after: int|
                        #[trigger] type_matches(source, forms, index + 2, end, after)
                        && after < end && span == form_span(forms[after]))
            } else {
                kind == name && directive_argument_error_span(forms, index + 1, end, close, span)
            })
        } else {
            kind == HeaderError::ExpectedPort
                && !directive_word_at(source, forms, index, limit, HeaderError::ExpectedName)
                && span == form_span(form)
        }
    }
}

fn read_port(source: &str, forms: &[Form], index: usize, _limit: usize)
    -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        index < _limit <= forms@.len(),
        form_region_ends_at(forms@, index as int, _limit as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() == port_matches(source, forms@, index as int, _limit as int),
        match result {
            Ok(after) => index < after <= _limit && following_direct_form(forms@, index as int, after as int),
            Err((kind, span)) => port_error_evidence(source, forms@, index as int, _limit as int, kind, span),
        },
{
    let form = &forms[index];
    let next = match form {
        Form::Atom { kind: AtomKind::Name, .. } => index + 1,
        Form::List { span: list_span, end: list_end } => {
            let end = *list_end;
            proof { enclosing_region_bounds_form(forms@, index as int, index as int, _limit as int); }
            assert(list_delimited(source.spec_bytes(), *form, false)) by {
                reveal(list_source_delimiters);
            };
            let close = list_span.end - 1;
            check_directive_word(source, forms, index + 1, end, close, HeaderError::ExpectedName)?;
            let value = index + 2;
            proof {
                assert(form_region_ends_at(forms@, value as int, end as int)) by {
                    assert(exists|parent: int| 0 <= parent < value
                        && #[trigger] forms@[parent] is List && forms@[parent]->List_end == end);
                };
                enclosing_region_bounds_form(forms@, value as int, value as int, end as int);
            }
            let after_type = read_type(source, forms, value, end, close)?;
            assert(type_matches(source, forms@, value as int, end as int, after_type as int));
            if after_type < end {
                return Err((HeaderError::UnexpectedArgument, form_span_exec(&forms[after_type])));
            }
            end
        }
        _ => return Err((HeaderError::ExpectedPort, form_span_exec(form))),
    };
    proof { node_end_is_following_direct_form(forms@, index as int, next as int); }
    Ok(next)
}

/// 走査済みの直接子がすべてポートであることを表す。
#[verifier::opaque]
pub open spec fn ports_match_before(
    source: &str, forms: Seq<Form>, start: int, limit: int, cursor: int,
) -> bool {
    forall|i: int| #[trigger] direct_form_in_range(forms, start, limit, i) && i < cursor
        ==> port_matches(source, forms, i, limit)
}

/// 入力節は空を許し、出力節はポートを1つ以上要求する。
pub open spec fn ports_clause_matches(
    source: &str, forms: Seq<Form>, index: int, limit: int, after: int, clause: Clause,
) -> bool {
    &&& (clause is In || clause is Out)
    &&& named_clause_matches(source, forms, index, limit, after, clause)
    &&& (clause is Out ==> index + 2 < after)
    &&& ports_match_before(source, forms, index + 2, after, after)
}

/// 節名の誤り、出力ポートの欠落、または最初の不正なポートの診断根拠を表す。
pub open spec fn ports_error_evidence(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize, clause: Clause,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    (kind == HeaderError::ExpectedClause(clause)
        && named_clause_error_span(source, forms, index, limit, closing, clause, span))
    || (exists|end: int| #[trigger] named_clause_matches(source, forms, index, limit, end, clause)
        && ((clause is Out && index + 2 == end && kind == HeaderError::ExpectedPort
            && span.start + 1 == form_span(forms[index]).end && span.end == span.start
            && span.start < source.spec_bytes().len() && source.spec_bytes()[span.start as int] == 41)
        || (exists|i: int| #[trigger] direct_form_in_range(forms, index + 2, end, i)
            && ports_match_before(source, forms, index + 2, end, i)
            && port_error_evidence(source, forms, i, end, kind, span))))
}

proof fn record_port(
    source: &str, forms: Seq<Form>, start: int, index: int, next: int, limit: int,
)
    requires
        index < next <= limit,
        direct_form_in_range(forms, start, limit, index),
        following_direct_form(forms, index, next),
        form_region_ends_at(forms, start, limit),
        ports_match_before(source, forms, start, limit, index),
        port_matches(source, forms, index, limit),
    ensures
        next < limit ==> direct_form_in_range(forms, start, limit, next),
        ports_match_before(source, forms, start, limit, next),
{
    reveal(following_direct_form);
    reveal(ports_match_before);
    assert forall|i: int| #[trigger] direct_form_in_range(forms, start, limit, i) && i < next
        implies port_matches(source, forms, i, limit) by {
        if i > index {
            assert(!direct_form_in_range(forms, start, limit, i));
        }
    };
}

fn read_ports_clause(
    source: &str, forms: &[Form], index: usize, limit: usize, closing: usize, clause: Clause,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        index <= limit <= forms@.len(),
        form_region_ends_at(forms@, index as int, limit as int),
        nested_list_indices(forms@),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
        clause is In || clause is Out,
    ensures
        forall|after: int| #[trigger] ports_clause_matches(
            source, forms@, index as int, limit as int, after, clause)
            <==> (result matches Ok(next) && after == next),
        result matches Ok(after) ==> index + 2 <= after <= limit,
        result matches Err((kind, span)) ==> ports_error_evidence(
            source, forms@, index as int, limit as int, closing, clause, kind, span),
{
    proof { enclosing_region_bounds_form(forms@, index as int, index as int, limit as int); }
    let (end, close) = read_named_clause(source, forms, index, limit, closing, clause)?;
    assert(named_clause_matches(source, forms@, index as int, limit as int, end as int, clause));
    let start = index + 2;
    if matches!(clause, Clause::Out) && start == end {
        return Err((HeaderError::ExpectedPort, close..close));
    }
    let mut cursor = start;
    proof {
        reveal(direct_form_in_range);
        reveal(ports_match_before);
        assert(form_region_ends_at(forms@, start as int, end as int)) by {
            assert(exists|parent: int| 0 <= parent < start
                && #[trigger] forms@[parent] is List && forms@[parent]->List_end == end);
        };
        assert(cursor < end ==> direct_form_in_range(forms@, start as int, end as int, cursor as int));
        assert(ports_match_before(source, forms@, start as int, end as int, cursor as int));
    }
    while cursor < end
        invariant
            start == index + 2,
            start <= cursor <= end <= limit <= forms@.len(),
            clause is In || clause is Out,
            clause is Out ==> start < end,
            named_clause_matches(source, forms@, index as int, limit as int, end as int, clause),
            form_region_ends_at(forms@, start as int, end as int),
            nested_list_indices(forms@),
            complete_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            cursor < end ==> direct_form_in_range(forms@, start as int, end as int, cursor as int),
            ports_match_before(source, forms@, start as int, end as int, cursor as int),
        decreases end - cursor,
    {
        assert(form_region_ends_at(forms@, cursor as int, end as int));
        let next = match read_port(source, forms, cursor, end) {
            Ok(next) => next,
            Err(error) => {
                assert(!ports_match_before(source, forms@, start as int, end as int, end as int)) by {
                    reveal(ports_match_before);
                };
                return Err(error);
            },
        };
        proof { record_port(source, forms@, start as int, cursor as int, next as int, end as int); }
        cursor = next;
    }
    Ok(end)
}

/// 宣言名と入出力節を受理したとき、本体の開始添字を定める。
///
/// `module-part` では宣言名の直後から本体が始まる。
pub open spec fn routine_signature_matches(
    source: &str, forms: Seq<Form>, first: int, limit: int, head: Head, after: int,
) -> bool {
    &&& directive_word_at(source, forms, first, limit, HeaderError::ExpectedName)
    &&& match head {
        Head::ModulePart => after == first + 1,
        Head::Func | Head::Module => exists|out: int|
            #[trigger] ports_clause_matches(source, forms, first + 1, limit, out, Clause::In)
                && ports_clause_matches(source, forms, out, limit, after, Clause::Out),
        _ => false,
    }
}

/// 宣言名、入力節、出力節の順で最初に見つかった違反を表す。
pub open spec fn routine_signature_error_evidence(
    source: &str, forms: Seq<Form>, first: int, limit: int, closing: usize, head: Head,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    let name = HeaderError::ExpectedName;
    if !directive_word_at(source, forms, first, limit, name) {
        kind == name && directive_argument_error_span(forms, first, limit, closing, span)
    } else {
        (head is Func || head is Module)
        && (ports_error_evidence(source, forms, first + 1, limit, closing, Clause::In, kind, span)
            || (exists|out: int| #[trigger] ports_clause_matches(source, forms, first + 1, limit, out, Clause::In)
                && ports_error_evidence(source, forms, out, limit, closing, Clause::Out, kind, span)))
    }
}

pub(super) fn read_routine_signature(
    source: &str, forms: &[Form], first: usize, limit: usize, closing: usize, head: Head,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        first <= limit <= forms@.len(),
        form_region_ends_at(forms@, first as int, limit as int),
        nested_list_indices(forms@),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
        head is Func || head is Module || head is ModulePart,
    ensures
        forall|after: int| #[trigger] routine_signature_matches(
            source, forms@, first as int, limit as int, head, after)
            <==> (result matches Ok(next) && after == next),
        result matches Ok(after) ==> first < after <= limit,
        result matches Err((kind, span)) ==> routine_signature_error_evidence(
            source, forms@, first as int, limit as int, closing, head, kind, span),
{
    check_directive_word(source, forms, first, limit, closing, HeaderError::ExpectedName)?;
    let next = first + 1;
    if matches!(head, Head::ModulePart) {
        return Ok(next);
    }
    let out = read_ports_clause(source, forms, next, limit, closing, Clause::In)?;
    assert(ports_clause_matches(source, forms@, next as int, limit as int, out as int, Clause::In));
    read_ports_clause(source, forms, out, limit, closing, Clause::Out)
}

} // verus!
