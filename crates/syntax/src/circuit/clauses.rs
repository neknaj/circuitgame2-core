use super::{AtomKind, Clause, Form, Head, HeaderError, form_span_exec, source_span};
#[cfg(verus_only)]
use super::{directive_argument_error_span, form_region_ends_at};
#[cfg(verus_only)]
use crate::{
    complete_list_indices, form_span, form_spans_valid, list_delimited, list_source_delimiters,
    nested_list_indices,
};
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{encode_utf8_decode_utf8, encode_utf8_valid_utf8, is_char_boundary};

verus! {

impl Clause {
    fn spelling(self) -> (name: &'static str)
        ensures name@ == clause_spelling(self)@,
    {
        match self {
            Self::In => "in",
            Self::Out => "out",
            Self::Expect => "expect",
            Self::Bits => "bits",
            Self::Width => "width",
            Self::Address => "address",
            Self::Data => "data",
            Self::At => "at",
        }
    }
}

/// 引数をまとめる節が要求する先頭語を定める。
pub open spec fn clause_spelling(clause: Clause) -> &'static str {
    match clause {
        Clause::In => "in",
        Clause::Out => "out",
        Clause::Expect => "expect",
        Clause::Bits => "bits",
        Clause::Width => "width",
        Clause::Address => "address",
        Clause::Data => "data",
        Clause::At => "at",
    }
}

/// 名前アトムの綴りが節の先頭語と一致することを表す。
pub open spec fn clause_word_matches(source: &str, form: Form, clause: Clause) -> bool {
    let span = form_span(form);
    form is Atom && form->Atom_kind == AtomKind::Name
        && source.spec_bytes()[span.start as int..span.end as int] == clause_spelling(clause).spec_bytes()
}

/// 指定の先頭語で始まるリストと、その直後の添字を表す。
pub open spec fn named_clause_matches(
    source: &str, forms: Seq<Form>, index: int, limit: int, after: int, clause: Clause,
) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& forms[index] is List
    &&& index + 1 < after <= limit
    &&& after == forms[index]->List_end
    &&& clause_word_matches(source, forms[index + 1], clause)
}

/// 節が欠けている位置、または節名の検査で最初に違反した要素の範囲を表す。
pub open spec fn named_clause_error_span(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize, clause: Clause, span: Range<usize>,
) -> bool {
    if index == limit {
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41
            && span == (closing..closing)
    } else if 0 <= index < limit <= forms.len() {
        let form = forms[index];
        if form is List {
            let after = form->List_end as int;
            let list_span = form_span(form);
            (after == index + 1 && list_span.end > 0
                && span.start == list_span.end - 1 && span.end == span.start)
            || (index + 1 < after <= limit && !clause_word_matches(source, forms[index + 1], clause)
                && span == form_span(forms[index + 1]))
        } else {
            span == form_span(form)
        }
    } else {
        false
    }
}

/// 指定位置が検査区間に収まり、そこにあるリストも区間を越えないことを表す。
pub open spec fn clause_fits_region(forms: Seq<Form>, index: int, limit: int) -> bool {
    0 <= index <= limit <= forms.len()
        && (index < limit && forms[index] is List ==> forms[index]->List_end <= limit)
}

pub(super) fn read_named_clause(
    source: &str, forms: &[Form], index: usize, limit: usize, closing: usize, clause: Clause,
) -> (result: Result<(usize, usize), (HeaderError, Range<usize>)>)
    requires
        clause_fits_region(forms@, index as int, limit as int),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        forall|after: int| #[trigger] named_clause_matches(source, forms@, index as int, limit as int, after, clause)
            <==> (result matches Ok((end, _)) && after == end),
        match result {
            Ok((_, close)) => close + 1 == form_span(forms@[index as int]).end
                && close < source.spec_bytes().len() && source.spec_bytes()[close as int] == 41,
            Err((kind, span)) => kind == HeaderError::ExpectedClause(clause)
                && named_clause_error_span(source, forms@, index as int, limit as int, closing, clause, span),
        },
{
    let expected = HeaderError::ExpectedClause(clause);
    if index == limit {
        return Err((expected, closing..closing));
    }
    let form = &forms[index];
    let Form::List { span: list_span, end: list_end } = form else {
        return Err((expected, form_span_exec(form)));
    };
    let end = *list_end;
    assert(0 < list_span.end <= source.spec_bytes().len()
        && source.spec_bytes()[list_span.end - 1] == 41) by {
        reveal(list_source_delimiters);
        assert(list_delimited(source.spec_bytes(), *form, false));
        assert(form_span(*form) == *list_span);
    };
    let close = list_span.end - 1;
    if index + 1 == end {
        return Err((expected, close..close));
    }
    let child = &forms[index + 1];
    let Form::Atom { kind: AtomKind::Name, span: word_span } = child else {
        return Err((expected, form_span_exec(child)));
    };
    proof { encode_utf8_valid_utf8(source@); }
    assert(word_span.start < word_span.end <= source.spec_bytes().len()
        && is_char_boundary(source.spec_bytes(), word_span.start as int)
        && is_char_boundary(source.spec_bytes(), word_span.end as int)) by {
        reveal(form_spans_valid);
        assert(form_span(*child) == *word_span);
    };
    let word = source_span(source, word_span.start, word_span.end);
    let spelling = clause.spelling();
    assert(word@ == spelling@ <==> word.spec_bytes() == clause_spelling(clause).spec_bytes()) by {
        encode_utf8_decode_utf8(word@);
        encode_utf8_decode_utf8(spelling@);
    };
    if word == spelling {
        Ok((end, close))
    } else {
        Err((expected, word_span.start..word_span.end))
    }
}

/// 自然数の字句が指定位置にあることを表す。
pub open spec fn natural_argument_at(forms: Seq<Form>, index: int, limit: int) -> bool {
    0 <= index < limit <= forms.len() && forms[index] is Atom && forms[index]->Atom_kind == AtomKind::Natural
}

/// 指定の先頭語と自然数1個を持つ節を表す。自然数の値は用途ごとの範囲検査で扱う。
pub open spec fn natural_clause_matches(
    source: &str, forms: Seq<Form>, index: int, limit: int, after: int, clause: Clause,
) -> bool {
    after == index + 3
        && named_clause_matches(source, forms, index, limit, after, clause)
        && natural_argument_at(forms, index + 2, after)
}

/// 先頭語、自然数の引数、余分な要素の順で最初に見つかった違反を表す。
pub open spec fn natural_clause_error_evidence(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize, clause: Clause,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    (kind == HeaderError::ExpectedClause(clause)
        && named_clause_error_span(source, forms, index, limit, closing, clause, span))
    || (exists|after: int| #[trigger] named_clause_matches(source, forms, index, limit, after, clause)
        && {
            let value = index + 2;
            let close = (form_span(forms[index]).end - 1) as usize;
            (kind == HeaderError::ExpectedNatural && !natural_argument_at(forms, value, after)
                && directive_argument_error_span(forms, value, after, close, span))
            || (kind == HeaderError::UnexpectedArgument && value + 1 < after
                && natural_argument_at(forms, value, after) && span == form_span(forms[value + 1]))
        })
}

pub(super) fn read_natural_clause(
    source: &str, forms: &[Form], index: usize, limit: usize, closing: usize, clause: Clause,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        clause_fits_region(forms@, index as int, limit as int),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        forall|after: int| #[trigger] natural_clause_matches(source, forms@, index as int, limit as int, after, clause)
            <==> result == Ok(after as usize) && 0 <= after <= usize::MAX,
        result matches Err((kind, span)) ==> natural_clause_error_evidence(
            source, forms@, index as int, limit as int, closing, clause, kind, span),
{
    let (end, close) = read_named_clause(source, forms, index, limit, closing, clause)?;
    assert(named_clause_matches(source, forms@, index as int, limit as int, end as int, clause));
    let value = index + 2;
    if value == end {
        return Err((HeaderError::ExpectedNatural, close..close));
    }
    if !matches!(&forms[value], Form::Atom { kind: AtomKind::Natural, .. }) {
        return Err((HeaderError::ExpectedNatural, form_span_exec(&forms[value])));
    }
    let next = value + 1;
    if next < end {
        Err((HeaderError::UnexpectedArgument, form_span_exec(&forms[next])))
    } else {
        Ok(end)
    }
}

/// 名前、相対パス、完全修飾名のいずれかであることを表す。
pub open spec fn reference_atom(kind: AtomKind) -> bool {
    kind is Name || kind is RelativePath || kind is AbsolutePath
}

pub(super) fn is_reference(kind: AtomKind) -> (accepted: bool)
    ensures accepted == reference_atom(kind),
{
    matches!(kind, AtomKind::Name | AtomKind::RelativePath | AtomKind::AbsolutePath)
}

/// 型への参照、または自然数でビット幅を指定する節に続く添字を定める。
pub open spec fn type_matches(source: &str, forms: Seq<Form>, index: int, limit: int, after: int) -> bool {
    &&& 0 <= index < limit <= forms.len()
    &&& ((after == index + 1 && forms[index] is Atom && reference_atom(forms[index]->Atom_kind))
        || natural_clause_matches(source, forms, index, limit, after, Clause::Bits))
}

/// 型指定の欠落、不正な参照、またはビット幅を指定する節の誤りの根拠を表す。
pub open spec fn type_error_evidence(
    source: &str, forms: Seq<Form>, index: int, limit: int, closing: usize,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    if index == limit {
        kind == HeaderError::ExpectedType && span == (closing..closing)
    } else if 0 <= index < limit <= forms.len() {
        let form = forms[index];
        if form is List {
            natural_clause_error_evidence(source, forms, index, limit, closing, Clause::Bits, kind, span)
        } else {
            kind == HeaderError::ExpectedType && form is Atom
                && !reference_atom(form->Atom_kind) && span == form_span(form)
        }
    } else {
        false
    }
}

pub(super) fn read_type(
    source: &str, forms: &[Form], index: usize, limit: usize, closing: usize,
) -> (result: Result<usize, (HeaderError, Range<usize>)>)
    requires
        clause_fits_region(forms@, index as int, limit as int),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        forall|after: int| #[trigger] type_matches(source, forms@, index as int, limit as int, after)
            <==> result == Ok(after as usize) && 0 <= after <= usize::MAX,
        result matches Err((kind, span)) ==>
            type_error_evidence(source, forms@, index as int, limit as int, closing, kind, span),
{
    if index == limit {
        return Err((HeaderError::ExpectedType, closing..closing));
    }
    match &forms[index] {
        Form::Atom { kind: atom_kind, .. }
            if is_reference(*atom_kind) =>
            Ok(index + 1),
        Form::List { .. } => read_natural_clause(source, forms, index, limit, closing, Clause::Bits),
        form => Err((HeaderError::ExpectedType, form_span_exec(form))),
    }
}

/// ラッチの幅指定と、メモリのアドレス幅とデータ型の並びを定める。
pub open spec fn storage_arguments_match(
    source: &str, forms: Seq<Form>, first: int, limit: int, head: Head,
) -> bool {
    match head {
        Head::Latch => natural_clause_matches(source, forms, first, limit, limit, Clause::Width),
        Head::Memory => exists|data: int| #[trigger] natural_clause_matches(
            source, forms, first, limit, data, Clause::Address)
            && named_clause_matches(source, forms, data, limit, limit, Clause::Data)
            && type_matches(source, forms, data + 2, limit, limit),
        _ => false,
    }
}

/// 幅、アドレス幅、データ型の節を順に検査した場合の診断根拠を定める。
pub open spec fn storage_error_evidence(
    source: &str, forms: Seq<Form>, first: int, limit: int, closing: usize, head: Head,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    match head {
        Head::Latch => natural_clause_error_evidence(source, forms, first, limit, closing, Clause::Width, kind, span)
            || (kind == HeaderError::UnexpectedArgument && exists|after: int|
                #[trigger] natural_clause_matches(source, forms, first, limit, after, Clause::Width)
                && after < limit && span == form_span(forms[after])),
        Head::Memory => natural_clause_error_evidence(source, forms, first, limit, closing, Clause::Address, kind, span)
            || (exists|data: int| #[trigger] natural_clause_matches(source, forms, first, limit, data, Clause::Address)
                && ((kind == HeaderError::ExpectedClause(Clause::Data)
                    && named_clause_error_span(source, forms, data, limit, closing, Clause::Data, span))
                || (exists|data_end: int| #[trigger] named_clause_matches(source, forms, data, limit, data_end, Clause::Data)
                    && (type_error_evidence(source, forms, data + 2, data_end,
                            (form_span(forms[data]).end - 1) as usize, kind, span)
                        || (kind == HeaderError::UnexpectedArgument && (
                            (exists|after: int| #[trigger] type_matches(source, forms, data + 2, data_end, after)
                                && after < data_end && span == form_span(forms[after]))
                            || (data_end < limit && type_matches(source, forms, data + 2, data_end, data_end)
                                && span == form_span(forms[data_end])))))))),
        _ => false,
    }
}

proof fn storage_clause_fits(forms: Seq<Form>, first: int, index: int, limit: int)
    requires
        0 <= first <= index <= limit <= forms.len(),
        form_region_ends_at(forms, first, limit),
        nested_list_indices(forms),
        complete_list_indices(forms),
    ensures clause_fits_region(forms, index, limit),
{
    if index < limit && forms[index] is List && limit < forms.len() {
        let parent = choose|parent: int| 0 <= parent < first
            && #[trigger] forms[parent] is List && forms[parent]->List_end == limit;
        reveal(nested_list_indices);
        assert(parent < index < forms[parent]->List_end);
    }
}

pub(super) fn validate_storage_arguments(
    source: &str, forms: &[Form], first: usize, limit: usize, closing: usize, head: Head,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        first <= limit <= forms@.len(),
        form_region_ends_at(forms@, first as int, limit as int),
        nested_list_indices(forms@),
        complete_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        closing < source.spec_bytes().len() && source.spec_bytes()[closing as int] == 41,
        head is Latch || head is Memory,
    ensures
        result.is_ok() == storage_arguments_match(source, forms@, first as int, limit as int, head),
        result matches Err((kind, span)) ==>
            storage_error_evidence(source, forms@, first as int, limit as int, closing, head, kind, span),
{
    proof { storage_clause_fits(forms@, first as int, first as int, limit as int); }
    let after = if matches!(head, Head::Latch) {
        let end = read_natural_clause(source, forms, first, limit, closing, Clause::Width)?;
        assert(natural_clause_matches(source, forms@, first as int, limit as int, end as int, Clause::Width));
        end
    } else {
        let data = read_natural_clause(source, forms, first, limit, closing, Clause::Address)?;
        assert(natural_clause_matches(source, forms@, first as int, limit as int, data as int, Clause::Address));
        proof { storage_clause_fits(forms@, first as int, data as int, limit as int); }
        let (data_end, data_close) = read_named_clause(source, forms, data, limit, closing, Clause::Data)?;
        assert(named_clause_matches(source, forms@, data as int, limit as int, data_end as int, Clause::Data));
        let value = data + 2;
        proof {
            assert(form_region_ends_at(forms@, value as int, data_end as int)) by {
                assert(exists|parent: int| 0 <= parent < value
                    && #[trigger] forms@[parent] is List && forms@[parent]->List_end == data_end);
            };
            storage_clause_fits(forms@, value as int, value as int, data_end as int);
        }
        let next = read_type(source, forms, value, data_end, data_close)?;
        assert(type_matches(source, forms@, value as int, data_end as int, next as int));
        if next < data_end {
            return Err((HeaderError::UnexpectedArgument, form_span_exec(&forms[next])));
        }
        data_end
    };
    if after < limit {
        Err((HeaderError::UnexpectedArgument, form_span_exec(&forms[after])))
    } else {
        Ok(())
    }
}

} // verus!
