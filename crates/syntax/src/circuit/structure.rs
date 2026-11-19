use super::clauses::{read_natural_clause, read_type};
use super::{AtomKind, Clause, Form, HeaderError, check_directive_word, form_span_exec};
use core::ops::Range;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::clause_diagnostics::{
    natural_errors_agree, natural_match_excludes_error, type_after_agrees, type_errors_agree,
    type_match_excludes_error,
};
#[cfg(verus_only)]
use super::clauses::enclosing_region_bounds_form;
#[cfg(verus_only)]
use super::{
    direct_form_in_range, directive_argument_error_span, directive_word_at, following_direct_form,
    form_region_ends_at, natural_clause_error_evidence, natural_clause_matches,
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

/// フィールドを、名前・型・位置指定をこの順に並べたリストとして定める。
pub open spec fn field_matches(source: &str, forms: Seq<Form>, index: int, limit: int) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& forms[index] is List
    &&& {
        let end = forms[index]->List_end as int;
        &&& end <= limit
        &&& directive_word_at(source, forms, index + 1, end, HeaderError::ExpectedName)
        &&& exists|at: int| #[trigger] type_matches(source, forms, index + 2, end, at)
            && natural_clause_matches(source, forms, at, end, end, Clause::At)
    }
}

/// 位置指定の違反、または位置指定の直後にある余分な引数の診断根拠を表す。
pub open spec fn field_offset_error_evidence(
    source: &str, forms: Seq<Form>, at: int, end: int, close: usize,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    natural_clause_error_evidence(source, forms, at, end, close, Clause::At, kind, span)
        || (kind == HeaderError::UnexpectedArgument && exists|after: int|
            #[trigger] natural_clause_matches(source, forms, at, end, after, Clause::At)
            && after < end && span == form_span(forms[after]))
}

/// 不正なフィールドの最初の違反と診断範囲の対応を表す。
pub open spec fn field_error_evidence(
    source: &str, forms: Seq<Form>, index: int, limit: int,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& {
        let field = forms[index];
        if field is List {
            let end = field->List_end as int;
            let close = (form_span(field).end - 1) as usize;
            let name = HeaderError::ExpectedName;
            &&& index < end <= limit
            &&& 0 < form_span(field).end <= source.spec_bytes().len()
            &&& source.spec_bytes()[close as int] == 41
            &&& (if directive_word_at(source, forms, index + 1, end, name) {
                type_error_evidence(source, forms, index + 2, end, close, kind, span)
                    || (exists|at: int| #[trigger] type_matches(source, forms, index + 2, end, at)
                        && field_offset_error_evidence(source, forms, at, end, close, kind, span))
            } else {
                kind == name && directive_argument_error_span(forms, index + 1, end, close, span)
            })
        } else {
            kind == HeaderError::ExpectedList && span == form_span(field)
        }
    }
}

proof fn field_offset_errors_agree(
    source: &str, forms: Seq<Form>, at: int, end: int, close: usize,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        field_offset_error_evidence(source, forms, at, end, close, left.0, left.1),
        field_offset_error_evidence(source, forms, at, end, close, right.0, right.1),
    ensures left == right,
{
    let left_clause =
        natural_clause_error_evidence(source, forms, at, end, close, Clause::At, left.0, left.1);
    let right_clause =
        natural_clause_error_evidence(source, forms, at, end, close, Clause::At, right.0, right.1);
    if left_clause && right_clause {
        natural_errors_agree(source, forms, at, end, close, Clause::At, left, right);
    } else {
        let after = at + 3;
        assert(natural_clause_matches(source, forms, at, end, after, Clause::At)) by {
            if !left_clause {
                let matched = choose|next: int|
                    #[trigger] natural_clause_matches(source, forms, at, end, next, Clause::At)
                    && next < end && left.1 == form_span(forms[next]);
                assert(matched == after);
            } else {
                let matched = choose|next: int|
                    #[trigger] natural_clause_matches(source, forms, at, end, next, Clause::At)
                    && next < end && right.1 == form_span(forms[next]);
                assert(matched == after);
            }
        };
        natural_match_excludes_error(source, forms, at, end, close, Clause::At, after, left);
        natural_match_excludes_error(source, forms, at, end, close, Clause::At, after, right);
        // 位置指定が文法に適合していれば、診断範囲は直後のフォームに限られる。
        assert(left.1 == form_span(forms[after]) && right.1 == form_span(forms[after]));
    }
}

proof fn field_match_excludes_error(
    source: &str, forms: Seq<Form>, index: int, limit: int, error: (HeaderError, Range<usize>),
)
    requires field_matches(source, forms, index, limit),
    ensures !field_error_evidence(source, forms, index, limit, error.0, error.1),
{
    if field_error_evidence(source, forms, index, limit, error.0, error.1) {
        let end = forms[index]->List_end as int;
        let close = (form_span(forms[index]).end - 1) as usize;
        let at = choose|at: int| #[trigger] type_matches(source, forms, index + 2, end, at)
            && natural_clause_matches(source, forms, at, end, end, Clause::At);
        type_match_excludes_error(source, forms, index + 2, end, close, at, error);
        let error_at = choose|at: int| #[trigger] type_matches(source, forms, index + 2, end, at)
            && field_offset_error_evidence(source, forms, at, end, close, error.0, error.1);
        type_after_agrees(source, forms, index + 2, end, at, error_at);
        natural_match_excludes_error(source, forms, at, end, close, Clause::At, end, error);
        let after = choose|after: int|
            #[trigger] natural_clause_matches(source, forms, at, end, after, Clause::At)
            && after < end && error.1 == form_span(forms[after]);
        assert(after == end);
    }
}

proof fn field_errors_agree(
    source: &str, forms: Seq<Form>, index: int, limit: int,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        field_error_evidence(source, forms, index, limit, left.0, left.1),
        field_error_evidence(source, forms, index, limit, right.0, right.1),
    ensures left == right,
{
    let field = forms[index];
    if field is List {
        let end = field->List_end as int;
        let close = (form_span(field).end - 1) as usize;
        if directive_word_at(source, forms, index + 1, end, HeaderError::ExpectedName) {
            let left_type = type_error_evidence(source, forms, index + 2, end, close, left.0, left.1);
            let right_type = type_error_evidence(source, forms, index + 2, end, close, right.0, right.1);
            if left_type && right_type {
                type_errors_agree(source, forms, index + 2, end, close, left, right);
            } else if !left_type {
                let at = choose|at: int| #[trigger] type_matches(source, forms, index + 2, end, at)
                    && field_offset_error_evidence(source, forms, at, end, close, left.0, left.1);
                type_match_excludes_error(source, forms, index + 2, end, close, at, right);
                let other_at = choose|at: int| #[trigger] type_matches(source, forms, index + 2, end, at)
                    && field_offset_error_evidence(source, forms, at, end, close, right.0, right.1);
                type_after_agrees(source, forms, index + 2, end, at, other_at);
                field_offset_errors_agree(source, forms, at, end, close, left, right);
            } else {
                let at = choose|at: int| #[trigger] type_matches(source, forms, index + 2, end, at)
                    && field_offset_error_evidence(source, forms, at, end, close, right.0, right.1);
                type_match_excludes_error(source, forms, index + 2, end, close, at, left);
            }
        }
    }
}

fn read_field(source: &str, forms: &[Form], index: usize, _limit: usize)
    -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        index < _limit <= forms@.len(),
        form_region_ends_at(forms@, index as int, _limit as int),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() == field_matches(source, forms@, index as int, _limit as int),
        match result {
            Ok(after) => forms@[index as int] is List && after == forms@[index as int]->List_end
                && index < after <= _limit && following_direct_form(forms@, index as int, after as int),
            Err((kind, span)) => field_error_evidence(source, forms@, index as int, _limit as int, kind, span),
        },
{
    let field = &forms[index];
    let Form::List { span: list_span, end: end_index } = field else {
        return Err((HeaderError::ExpectedList, form_span_exec(field)));
    };
    let end = *end_index;
    proof { enclosing_region_bounds_form(forms@, index as int, index as int, _limit as int); }
    assert(list_delimited(source.spec_bytes(), *field, false)) by {
        reveal(list_source_delimiters);
    };
    let close = list_span.end - 1;
    let name_index = index + 1;
    if name_index == end {
        return Err((HeaderError::ExpectedName, close..close));
    }
    let name = &forms[name_index];
    if !matches!(name, Form::Atom { kind: AtomKind::Name, .. }) {
        return Err((HeaderError::ExpectedName, form_span_exec(name)));
    }

    let type_index = name_index + 1;
    proof {
        assert(form_region_ends_at(forms@, type_index as int, end as int)) by {
            assert(exists|parent: int| 0 <= parent < type_index
                && #[trigger] forms@[parent] is List && forms@[parent]->List_end == end);
        };
        enclosing_region_bounds_form(forms@, type_index as int, type_index as int, end as int);
    }
    let at = read_type(source, forms, type_index, end, close)?;
    assert(type_matches(source, forms@, type_index as int, end as int, at as int));
    proof { enclosing_region_bounds_form(forms@, type_index as int, at as int, end as int); }

    let next = read_natural_clause(source, forms, at, end, close, Clause::At)?;
    assert(natural_clause_matches(source, forms@, at as int, end as int, next as int, Clause::At));
    if next < end {
        return Err((HeaderError::UnexpectedArgument, form_span_exec(&forms[next])));
    }
    proof { node_end_is_following_direct_form(forms@, index as int, end as int); }
    Ok(end)
}

/// 走査済みの直接フィールドがすべて構文に適合することを表す。
#[verifier::opaque]
pub open spec fn fields_match_before(
    source: &str, forms: Seq<Form>, start: int, limit: int, cursor: int,
) -> bool {
    forall|i: int| #[trigger] direct_form_in_range(forms, start, limit, i) && i < cursor
        ==> field_matches(source, forms, i, limit)
}

/// 構造体の幅指定と、後続する直接フィールド列の構文を定める。
pub open spec fn structure_body_matches(
    source: &str, forms: Seq<Form>, first: int, limit: int,
) -> bool {
    exists|fields: int| #[trigger] natural_clause_matches(source, forms, first, limit, fields, Clause::Width)
        && fields_match_before(source, forms, fields, limit, limit)
}

/// 幅指定か、最初に失敗した直接フィールドの診断根拠を表す。
pub open spec fn structure_body_error_evidence(
    source: &str, forms: Seq<Form>, first: int, limit: int, closing: usize,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    natural_clause_error_evidence(source, forms, first, limit, closing, Clause::Width, kind, span)
    || (exists|fields: int, i: int|
        #[trigger] natural_clause_matches(source, forms, first, limit, fields, Clause::Width)
        && #[trigger] direct_form_in_range(forms, fields, limit, i)
        && fields_match_before(source, forms, fields, limit, i)
        && field_error_evidence(source, forms, i, limit, kind, span))
}

proof fn record_field(
    source: &str, forms: Seq<Form>, start: int, index: int, next: int, limit: int,
)
    requires
        index < next <= limit,
        direct_form_in_range(forms, start, limit, index),
        following_direct_form(forms, index, next),
        form_region_ends_at(forms, start, limit),
        fields_match_before(source, forms, start, limit, index),
        field_matches(source, forms, index, limit),
    ensures
        next < limit ==> direct_form_in_range(forms, start, limit, next),
        fields_match_before(source, forms, start, limit, next),
{
    reveal(following_direct_form);
    reveal(fields_match_before);
    assert forall|i: int| #[trigger] direct_form_in_range(forms, start, limit, i) && i < next
        implies field_matches(source, forms, i, limit) by {
        if i > index {
            assert(!direct_form_in_range(forms, start, limit, i));
        }
    };
}

fn validate_structure_body(
    source: &str, forms: &[Form], first: usize, limit: usize, closing: usize,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        first <= limit <= forms@.len(),
        form_region_ends_at(forms@, first as int, limit as int),
        nested_list_indices(forms@),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
    ensures
        result.is_ok() == structure_body_matches(source, forms@, first as int, limit as int),
        result matches Err((kind, span)) ==>
            structure_body_error_evidence(source, forms@, first as int, limit as int, closing, kind, span),
{
    proof { enclosing_region_bounds_form(forms@, first as int, first as int, limit as int); }
    let start = read_natural_clause(source, forms, first, limit, closing, Clause::Width)?;
    assert(natural_clause_matches(source, forms@, first as int, limit as int, start as int, Clause::Width));
    let mut index = start;
    proof {
        reveal(direct_form_in_range);
        reveal(fields_match_before);
        assert(index < limit ==> direct_form_in_range(forms@, start as int, limit as int, index as int));
        assert(fields_match_before(source, forms@, start as int, limit as int, index as int));
    }
    while index < limit
        invariant
            start <= index <= limit <= forms@.len(),
            natural_clause_matches(source, forms@, first as int, limit as int, start as int, Clause::Width),
            forall|after: int| #[trigger] natural_clause_matches(
                source, forms@, first as int, limit as int, after, Clause::Width) ==> after == start,
            form_region_ends_at(forms@, first as int, limit as int),
            nested_list_indices(forms@),
            complete_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            index < limit ==> direct_form_in_range(forms@, start as int, limit as int, index as int),
            fields_match_before(source, forms@, start as int, limit as int, index as int),
        decreases limit - index,
    {
        assert(form_region_ends_at(forms@, start as int, limit as int));
        assert(form_region_ends_at(forms@, index as int, limit as int));
        let next = match read_field(source, forms, index, limit) {
            Ok(next) => next,
            Err(error) => {
                assert(!fields_match_before(source, forms@, start as int, limit as int, limit as int)) by {
                    reveal(fields_match_before);
                };
                return Err(error);
            }
        };
        proof { record_field(source, forms@, start as int, index as int, next as int, limit as int); }
        index = next;
    }
    Ok(())
}

/// 宣言名、幅指定、フィールド列に従う構造体の引数を表す。
pub open spec fn structure_arguments_match(
    source: &str, forms: Seq<Form>, first: int, limit: int,
) -> bool {
    directive_word_at(source, forms, first, limit, HeaderError::ExpectedName)
        && structure_body_matches(source, forms, first + 1, limit)
}

/// 構造体の宣言名を検査した後、幅指定とフィールド列を順に検査した場合の診断根拠を表す。
pub open spec fn structure_error_evidence(
    source: &str, forms: Seq<Form>, first: int, limit: int, closing: usize,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    if directive_word_at(source, forms, first, limit, HeaderError::ExpectedName) {
        structure_body_error_evidence(source, forms, first + 1, limit, closing, kind, span)
    } else {
        kind == HeaderError::ExpectedName && directive_argument_error_span(forms, first, limit, closing, span)
    }
}

/// 同じ構造体の診断根拠から、最初の違反の種別と範囲が一意に定まることを示す。
pub(super) proof fn structure_errors_agree(
    source: &str, forms: Seq<Form>, first: int, limit: int, closing: usize,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        structure_error_evidence(source, forms, first, limit, closing, left.0, left.1),
        structure_error_evidence(source, forms, first, limit, closing, right.0, right.1),
    ensures left == right,
{
    if directive_word_at(source, forms, first, limit, HeaderError::ExpectedName) {
        let width = first + 1;
        let left_width =
            natural_clause_error_evidence(source, forms, width, limit, closing, Clause::Width, left.0, left.1);
        let right_width =
            natural_clause_error_evidence(source, forms, width, limit, closing, Clause::Width, right.0, right.1);
        if left_width && right_width {
            natural_errors_agree(source, forms, width, limit, closing, Clause::Width, left, right);
        } else if !left_width {
            let (fields, i) = choose|fields: int, i: int|
                #[trigger] natural_clause_matches(source, forms, width, limit, fields, Clause::Width)
                && #[trigger] direct_form_in_range(forms, fields, limit, i)
                && fields_match_before(source, forms, fields, limit, i)
                && field_error_evidence(source, forms, i, limit, left.0, left.1);
            natural_match_excludes_error(source, forms, width, limit, closing, Clause::Width, fields, right);
            let (other_fields, j) = choose|fields: int, j: int|
                #[trigger] natural_clause_matches(source, forms, width, limit, fields, Clause::Width)
                && #[trigger] direct_form_in_range(forms, fields, limit, j)
                && fields_match_before(source, forms, fields, limit, j)
                && field_error_evidence(source, forms, j, limit, right.0, right.1);
            assert(fields == other_fields);
            // 先に失敗したフィールドは、後の違反の根拠では文法に適合する。
            reveal(fields_match_before);
            if i < j {
                assert(field_matches(source, forms, i, limit));
                field_match_excludes_error(source, forms, i, limit, left);
            } else if j < i {
                assert(field_matches(source, forms, j, limit));
                field_match_excludes_error(source, forms, j, limit, right);
            } else {
                field_errors_agree(source, forms, i, limit, left, right);
            }
        } else {
            let (fields, i) = choose|fields: int, i: int|
                #[trigger] natural_clause_matches(source, forms, width, limit, fields, Clause::Width)
                && #[trigger] direct_form_in_range(forms, fields, limit, i)
                && fields_match_before(source, forms, fields, limit, i)
                && field_error_evidence(source, forms, i, limit, right.0, right.1);
            natural_match_excludes_error(source, forms, width, limit, closing, Clause::Width, fields, left);
        }
    }
}

pub(super) fn validate_structure_arguments(
    source: &str, forms: &[Form], first: usize, limit: usize, closing: usize,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        first <= limit <= forms@.len(),
        form_region_ends_at(forms@, first as int, limit as int),
        nested_list_indices(forms@),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
    ensures
        result.is_ok() == structure_arguments_match(source, forms@, first as int, limit as int),
        result matches Err((kind, span)) ==>
            structure_error_evidence(source, forms@, first as int, limit as int, closing, kind, span),
{
    check_directive_word(source, forms, first, limit, closing, HeaderError::ExpectedName)?;
    validate_structure_body(source, forms, first + 1, limit, closing)
}

} // verus!
