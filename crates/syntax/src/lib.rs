#![no_std]

extern crate alloc;

mod atom;
mod boundary;
mod digits;

use crate::boundary::{Boundary, after_ascii, split_at_boundary, split_first_scalar};
use alloc::vec::Vec;
#[cfg(verus_only)]
pub use atom::bare_atom_kind;
use atom::classify;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    encode_utf8_valid_utf8, is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq, is_continuation_byte, length_of_first_scalar, valid_utf8,
    valid_utf8_split,
};

verus! {

#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Form {
    Atom { kind: AtomKind, span: Range<usize> },
    List { span: Range<usize>, end: usize },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AtomKind {
    Name,
    RelativePath,
    AbsolutePath,
    Natural,
    NegativeInteger,
    Binary,
    Hexadecimal,
    String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    InvalidAtom,
    MissingSeparator,
    InvalidEscape { opening: usize },
    UnterminatedString,
    NewlineInString { opening: usize },
    UnexpectedClose,
    UnclosedList { eof: usize },
}

#[derive(Debug, Eq, PartialEq)]
pub struct Error {
    pub kind: ErrorKind,
    pub span: Range<usize>,
}

} // verus!

impl Clone for Error {
    fn clone(&self) -> Self {
        Self {
            kind: self.kind,
            span: self.span.clone(),
        }
    }
}

verus! {

#[derive(Debug, Eq, PartialEq)]
enum SegmentKind {
    Whitespace,
    Comment,
    Open,
    Close,
    Atom(AtomKind),
    Malformed(Error),
}

impl SegmentKind {
    spec fn is_atom(&self) -> bool {
        matches!(self, Self::Atom(_) | Self::Malformed(_))
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Segment {
    kind: SegmentKind,
    span: Range<usize>,
    missing_separator: bool,
}

#[derive(Clone, Copy)]
struct Lexer<'a> {
    cursor: SourceCursor<'a>,
    needs_separator: bool,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> (lexer: Self)
        ensures
            lexer.cursor.source == source,
            lexer.cursor.valid(),
            lexer.cursor.position() == 0,
            !lexer.needs_separator,
    {
        Self {
            cursor: SourceCursor::new(source),
            needs_separator: false,
        }
    }

    fn next_segment(self) -> (step: Option<(Segment, Self)>)
        requires
            self.cursor.valid(),
        ensures
            match step {
                None => self.cursor.position() == self.cursor.source.spec_bytes().len(),
                Some((segment, next)) => {
                    &&& next.cursor.source == self.cursor.source
                    &&& next.cursor.valid()
                    &&& segment.span.start == self.cursor.position()
                    &&& segment.span.start < segment.span.end
                    &&& segment.span.end == next.cursor.position()
                    &&& segment.span.end <= self.cursor.source.spec_bytes().len()
                    &&& is_char_boundary(self.cursor.source.spec_bytes(), segment.span.start as int)
                    &&& is_char_boundary(self.cursor.source.spec_bytes(), segment.span.end as int)
                    &&& (segment.kind is Open ==> segment.span.end == segment.span.start + 1
                        && self.cursor.source.spec_bytes()[segment.span.start as int] == 40)
                    &&& (segment.kind is Close ==> segment.span.end == segment.span.start + 1
                        && self.cursor.source.spec_bytes()[segment.span.start as int] == 41)
                    &&& (segment.kind is Malformed ==> syntax_error_evidence(
                        self.cursor.source, segment.kind->Malformed_0))
                    &&& (segment.kind is Atom ==> form_atom_matches(self.cursor.source,
                        Form::Atom { kind: segment.kind->Atom_0, span: segment.span }))
                    &&& next.needs_separator == segment.kind.is_atom()
                    &&& segment.missing_separator == (self.needs_separator && segment.kind.is_atom())
                },
            },
    {
        let Some((raw, span, cursor)) = self.cursor.advance() else {
            return None;
        };
        let (kind, is_atom) = match raw {
            RawSegment::Whitespace => (SegmentKind::Whitespace, false),
            RawSegment::Comment => (SegmentKind::Comment, false),
            RawSegment::Open => (SegmentKind::Open, false),
            RawSegment::Close => (SegmentKind::Close, false),
            RawSegment::Quoted(error) => (
                match error {
                    Some(error) => SegmentKind::Malformed(error),
                    None => SegmentKind::Atom(AtomKind::String),
                },
                true,
            ),
            RawSegment::Bare(atom) => (
                match classify(atom) {
                    Some(atom) => SegmentKind::Atom(atom),
                    None => SegmentKind::Malformed(Error {
                        kind: ErrorKind::InvalidAtom,
                        span: span.start..span.end,
                    }),
                },
                true,
            ),
        };
        assert(kind is Malformed ==> syntax_error_evidence(self.cursor.source, kind->Malformed_0))
            by { reveal(syntax_error_evidence); reveal(atom_and_close_error_evidence); };
        let missing_separator = self.needs_separator && is_atom;
        Some((
            Segment { kind, span, missing_separator },
            Self { cursor, needs_separator: is_atom },
        ))
    }
}

} // verus!

#[cfg(test)]
impl Iterator for Lexer<'_> {
    type Item = Segment;

    fn next(&mut self) -> Option<Segment> {
        let (segment, next) = self.next_segment()?;
        *self = next;
        Some(segment)
    }
}

verus! {

/// Syntax repairs and their source evidence, in parser processing order.
/// These events describe the parser's recovery. Applying source edits requires
/// resolving their ranges and intent first.
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Repair {
    Skipped {
        span: Range<usize>,
        error: Error,
    },
    InsertedSeparator {
        offset: usize,
    },
    InsertedClose {
        offset: usize,
        opening: Range<usize>,
        list: usize,
    },
}

#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Recovered {
    /// Provisional forest. A repaired list's span includes only source bytes.
    pub forms: Vec<Form>,
    pub repairs: Vec<Repair>,
}

/// Parses all forms in preorder. For a list, `end` is the index after its
/// complete subtree. All source spans are half-open UTF-8 byte ranges.
pub fn parse(source: &str) -> (result: Result<Vec<Form>, Error>)
    ensures
        match result {
            Ok(forms) => complete_list_indices(forms@) && nested_list_indices(forms@)
                && list_source_delimiters(source, forms@, false)
                && form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            Err(error) => syntax_error_evidence(source, error),
        },
{
    match parse_forms(source, false) {
        Ok((forms, _)) => Ok(forms),
        Err(error) => Err(error),
    }
}

/// Recovers S-expressions for editor analysis. Missing closes are inserted at
/// EOF, and unresolved nesting is preserved in the provisional forest.
pub fn parse_recovering(source: &str) -> (result: Recovered)
    ensures
        complete_list_indices(result.forms@),
        nested_list_indices(result.forms@),
        list_source_delimiters(source, result.forms@, true),
        inserted_closes_match(source, result.forms@, result.repairs@),
        repair_input_spans_valid(source, result.repairs@, source.spec_bytes().len() as int),
        form_spans_valid(source, result.forms@, source.spec_bytes().len() as int),
{
    match parse_forms(source, true) {
        Ok((forms, repairs)) => Recovered { forms, repairs },
        Err(_) => unreachable!("recovery handles each syntax error"),
    }
}

spec fn covers(bytes: Seq<u8>, spans: Seq<(int, int)>, end: int) -> bool {
    &&& 0 <= end <= bytes.len()
    &&& (spans.len() == 0 ==> end == 0)
    &&& (spans.len() > 0 ==> spans[spans.len() - 1].1 == end)
    &&& forall|i: int| 0 <= i < spans.len() ==> {
        let span = #[trigger] spans[i];
        &&& 0 <= span.0 < span.1 <= end
        &&& is_char_boundary(bytes, span.0)
        &&& is_char_boundary(bytes, span.1)
        &&& span.0 == if i == 0 { 0 } else { spans[i - 1].1 }
    }
}

spec fn pending_lists(forms: Seq<Form>, open: Seq<usize>) -> bool {
    forall|i: int| 0 <= i < open.len() ==> {
        let index = #[trigger] open[i] as int;
        0 <= index < forms.len() && forms[index] is List && forms[index]->List_end == 0
            && forms[index]->List_span.end == forms[index]->List_span.start + 1
    }
}

pub open spec fn form_span(form: Form) -> Range<usize> {
    match form {
        Form::Atom { span, .. } | Form::List { span, .. } => span,
    }
}

pub open spec fn bare_form_matches(source: &str, form: Form) -> bool {
    match form {
        Form::Atom { kind, span } => kind != AtomKind::String ==> (
            span.start < span.end <= source.spec_bytes().len()
            && bare_atom_kind(source.spec_bytes()[span.start as int..span.end as int]) == Some(kind)
        ),
        Form::List { .. } => true,
    }
}

pub open spec fn form_atom_matches(source: &str, form: Form) -> bool {
    &&& bare_form_matches(source, form)
    &&& match form {
        Form::Atom { kind: AtomKind::String, span } => {
            &&& span.start < span.end <= source.spec_bytes().len()
            &&& quoted_atom(source.spec_bytes()[span.start as int..span.end as int])
        },
        _ => true,
    }
}

#[verifier::opaque]
pub open spec fn form_spans_valid(source: &str, forms: Seq<Form>, consumed: int) -> bool {
    &&& 0 <= consumed <= source.spec_bytes().len()
    &&& forall|i: int| 0 <= i < forms.len() ==> {
        let span = form_span(#[trigger] forms[i]);
        &&& span.start < span.end <= consumed
        &&& is_char_boundary(source.spec_bytes(), span.start as int)
        &&& is_char_boundary(source.spec_bytes(), span.end as int)
        &&& (i > 0 ==> form_span(forms[i - 1]).start < span.start)
        &&& form_atom_matches(source, forms[i])
    }
}

proof fn advance_form_spans(source: &str, forms: Seq<Form>, before: int, after: int)
    requires
        form_spans_valid(source, forms, before),
        before <= after <= source.spec_bytes().len(),
    ensures form_spans_valid(source, forms, after),
{
    reveal(form_spans_valid);
}

proof fn append_form_span(source: &str, forms: Seq<Form>, form: Form, before: int, after: int)
    requires
        form_spans_valid(source, forms, before),
        form_atom_matches(source, form),
        before == form_span(form).start,
        before < form_span(form).end <= after <= source.spec_bytes().len(),
        is_char_boundary(source.spec_bytes(), before),
        is_char_boundary(source.spec_bytes(), form_span(form).end as int),
    ensures form_spans_valid(source, forms.push(form), after),
{
    reveal(form_spans_valid);
    let extended = forms.push(form);
    assert forall|i: int| 0 <= i < extended.len() implies {
        let span = form_span(#[trigger] extended[i]);
        &&& span.start < span.end <= after
        &&& is_char_boundary(source.spec_bytes(), span.start as int)
        &&& is_char_boundary(source.spec_bytes(), span.end as int)
        &&& (i > 0 ==> form_span(extended[i - 1]).start < span.start)
        &&& form_atom_matches(source, extended[i])
    } by {
        if i < forms.len() {
            assert(extended[i] == forms[i]);
        } else if i > 0 {
            assert(extended[i - 1] == forms[i - 1]);
        }
    };
}

proof fn close_form_span(source: &str, forms: Seq<Form>, updated: Seq<Form>, index: int,
    before: int, after: int)
    requires
        form_spans_valid(source, forms, before),
        0 <= index < forms.len(),
        updated.len() == forms.len(),
        before <= after <= source.spec_bytes().len(),
        is_char_boundary(source.spec_bytes(), after),
        updated[index] is List,
        form_span(updated[index]).start == form_span(forms[index]).start,
        form_span(updated[index]).end == after,
        forall|i: int| 0 <= i < forms.len() && i != index ==> #[trigger] updated[i] == forms[i],
    ensures form_spans_valid(source, updated, after),
{
    reveal(form_spans_valid);
    assert forall|i: int| 0 <= i < updated.len() implies {
        let span = form_span(#[trigger] updated[i]);
        &&& span.start < span.end <= after
        &&& is_char_boundary(source.spec_bytes(), span.start as int)
        &&& is_char_boundary(source.spec_bytes(), span.end as int)
        &&& (i > 0 ==> form_span(updated[i - 1]).start < span.start)
        &&& form_atom_matches(source, updated[i])
    } by {
        assert(form_span(updated[i]).start == form_span(forms[i]).start);
        if i > 0 {
            assert(form_span(updated[i - 1]).start == form_span(forms[i - 1]).start);
        }
    };
}

pub open spec fn list_delimited(bytes: Seq<u8>, form: Form, recovering: bool) -> bool {
    match form {
        Form::List { span, end } => {
            &&& span.start < bytes.len()
            &&& bytes[span.start as int] == 40
            &&& (end > 0 ==> 0 < span.end <= bytes.len()
                && (bytes[span.end - 1] == 41 || (recovering && span.end == bytes.len())))
        },
        Form::Atom { .. } => true,
    }
}

#[verifier::opaque]
pub open spec fn list_source_delimiters(source: &str, forms: Seq<Form>, recovering: bool) -> bool {
    forall|i: int| 0 <= i < forms.len()
        ==> list_delimited(source.spec_bytes(), #[trigger] forms[i], recovering)
}

proof fn delimiters_after_append(source: &str, forms: Seq<Form>, form: Form, recovering: bool)
    requires
        list_source_delimiters(source, forms, recovering),
        list_delimited(source.spec_bytes(), form, recovering),
    ensures list_source_delimiters(source, forms.push(form), recovering),
{
    reveal(list_source_delimiters);
    let extended = forms.push(form);
    assert forall|i: int| 0 <= i < extended.len()
        implies list_delimited(source.spec_bytes(), #[trigger] extended[i], recovering) by {
        if i < forms.len() {
            assert(extended[i] == forms[i]);
        }
    };
}

proof fn delimiters_after_close(source: &str, forms: Seq<Form>, updated: Seq<Form>,
    index: int, recovering: bool)
    requires
        list_source_delimiters(source, forms, recovering),
        updated.len() == forms.len(),
        0 <= index < forms.len(),
        forms[index] is List,
        updated[index] is List,
        form_span(updated[index]).start == form_span(forms[index]).start,
        0 < form_span(updated[index]).end <= source.spec_bytes().len(),
        source.spec_bytes()[form_span(updated[index]).end - 1] == 41
            || (recovering && form_span(updated[index]).end == source.spec_bytes().len()),
        forall|i: int| 0 <= i < forms.len() && i != index ==> #[trigger] updated[i] == forms[i],
    ensures list_source_delimiters(source, updated, recovering),
{
    reveal(list_source_delimiters);
    assert forall|i: int| 0 <= i < updated.len()
        implies list_delimited(source.spec_bytes(), #[trigger] updated[i], recovering) by {
        if i != index {
            assert(updated[i] == forms[i]);
        } else {
            assert(list_delimited(source.spec_bytes(), forms[i], recovering));
        }
    };
}

pub open spec fn complete_list_indices(forms: Seq<Form>) -> bool {
    forall|i: int| 0 <= i < forms.len() ==> match #[trigger] forms[i] {
        Form::List { end, .. } => i < end <= forms.len(),
        Form::Atom { .. } => true,
    }
}

spec fn list_indices(forms: Seq<Form>, open: Seq<usize>) -> bool {
    forall|i: int| 0 <= i < forms.len() ==> match #[trigger] forms[i] {
        Form::List { end, .. } => if end == 0 {
            open.contains(i as usize)
        } else {
            i < end <= forms.len()
        },
        Form::Atom { .. } => true,
    }
}

#[verifier::opaque]
pub open spec fn nested_list_indices(forms: Seq<Form>) -> bool {
    forall|i: int, j: int| 0 <= i < j < forms.len()
        && #[trigger] forms[i] is List && #[trigger] forms[j] is List
        && j < forms[i]->List_end
        ==> 0 < forms[j]->List_end <= forms[i]->List_end
}

spec fn open_order(open: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < open.len() ==> #[trigger] open[i] < #[trigger] open[j]
}

proof fn nested_after_append(forms: Seq<Form>, added: Form)
    requires
        nested_list_indices(forms),
        forall|i: int| 0 <= i < forms.len() && #[trigger] forms[i] is List
            ==> forms[i]->List_end <= forms.len(),
    ensures nested_list_indices(forms.push(added)),
{
    reveal(nested_list_indices);
    let extended = forms.push(added);
    assert forall|i: int, j: int| 0 <= i < j < extended.len()
        && #[trigger] extended[i] is List && #[trigger] extended[j] is List
        && j < extended[i]->List_end
        implies 0 < extended[j]->List_end <= extended[i]->List_end by {
        assert(extended[i] == forms[i]);
        assert(j < forms.len());
        assert(extended[j] == forms[j]);
    };
}

proof fn nested_after_close(before: Seq<Form>, after: Seq<Form>, open: Seq<usize>, last: usize)
    requires
        nested_list_indices(before),
        list_indices(before, open),
        open_order(open),
        open.len() > 0,
        last == open[open.len() - 1],
        last < before.len(),
        before[last as int] is List,
        before[last as int]->List_end == 0,
        after.len() == before.len(),
        after[last as int] is List,
        after[last as int]->List_end == after.len(),
        forall|i: int| 0 <= i < before.len() && i != last ==> #[trigger] after[i] == before[i],
    ensures nested_list_indices(after),
{
    reveal(nested_list_indices);
    assert forall|i: int, j: int| 0 <= i < j < after.len()
        && #[trigger] after[i] is List && #[trigger] after[j] is List
        && j < after[i]->List_end
        implies 0 < after[j]->List_end <= after[i]->List_end by {
        if i == last {
            assert(after[j] == before[j]);
            if before[j]->List_end == 0 {
                assert(open.contains(j as usize));
                let at = choose|at: int| 0 <= at < open.len() && open[at] == j as usize;
                assert(at < open.len() - 1);
                assert(open[at] < open[open.len() - 1]);
            }
        } else {
            assert(after[i] == before[i]);
            if j == last {
                assert(0 < before[j]->List_end);
            } else {
                assert(after[j] == before[j]);
            }
        }
    };
}

proof fn indices_after_append(before: Seq<Form>, open: Seq<usize>, form: Form, next: Seq<usize>)
    requires
        list_indices(before, open),
        forall|i: usize| #[trigger] open.contains(i) ==> next.contains(i),
        before.len() < usize::MAX,
        form is List ==> form->List_end == 0 && next.contains(before.len() as usize),
    ensures list_indices(before.push(form), next),
{
    let after = before.push(form);
    assert forall|i: int| 0 <= i < after.len() implies match #[trigger] after[i] {
        Form::List { end, .. } => if end == 0 {
            next.contains(i as usize)
        } else {
            i < end <= after.len()
        },
        Form::Atom { .. } => true,
    } by {
        if i < before.len() {
            assert(after[i] == before[i]);
        }
    };
}

proof fn indices_after_finish(before: Seq<Form>, after: Seq<Form>, open: Seq<usize>,
    shortened: Seq<usize>, last: usize)
    requires
        list_indices(before, open),
        shortened == open[..open.len() - 1],
        open.len() > 0,
        last == open[open.len() - 1],
        last < before.len(),
        after.len() == before.len(),
        after[last as int] is List,
        after[last as int]->List_end == after.len(),
        forall|i: int| 0 <= i < before.len() && i != last ==> #[trigger] after[i] == before[i],
    ensures list_indices(after, shortened),
{
    assert forall|i: int| 0 <= i < after.len() implies match #[trigger] after[i] {
        Form::List { end, .. } => if end == 0 {
            shortened.contains(i as usize)
        } else {
            i < end <= after.len()
        },
        Form::Atom { .. } => true,
    } by {
        if i != last {
            assert(after[i] == before[i]);
            if before[i] is List && before[i]->List_end == 0 {
                assert(open.contains(i as usize));
                let at = choose|at: int| 0 <= at < open.len() && open[at] == i as usize;
                assert(at < shortened.len());
                assert(shortened[at] == i as usize);
            }
        }
    };
}

#[verifier::opaque]
pub open spec fn inserted_closes_match(source: &str, forms: Seq<Form>, repairs: Seq<Repair>) -> bool {
    forall|i: int| 0 <= i < repairs.len() ==> match #[trigger] repairs[i] {
        Repair::InsertedClose { offset, opening, list } => {
            &&& list < forms.len()
            &&& forms[list as int] is List
            &&& forms[list as int]->List_end > 0
            &&& offset == source.spec_bytes().len()
            &&& form_span(forms[list as int]).end == offset
            &&& form_span(forms[list as int]).start == opening.start
            &&& opening.end == opening.start + 1
        },
        _ => true,
    }
}

spec fn no_inserted_closes(repairs: Seq<Repair>) -> bool {
    forall|i: int| 0 <= i < repairs.len() ==> !(#[trigger] repairs[i] is InsertedClose)
}

proof fn no_closes_implies_evidence(source: &str, forms: Seq<Form>, repairs: Seq<Repair>)
    requires no_inserted_closes(repairs),
    ensures inserted_closes_match(source, forms, repairs),
{
    reveal(inserted_closes_match);
}

proof fn record_inserted_close(source: &str, forms: Seq<Form>, updated: Seq<Form>,
    repairs: Seq<Repair>, index: usize, opening: Range<usize>, offset: usize)
    requires
        inserted_closes_match(source, forms, repairs),
        updated.len() == forms.len(),
        index < forms.len(),
        forms[index as int] is List,
        forms[index as int]->List_end == 0,
        updated[index as int] is List,
        updated[index as int]->List_end > 0,
        offset == source.spec_bytes().len(),
        form_span(updated[index as int]).start == opening.start,
        form_span(updated[index as int]).end == offset,
        opening.end == opening.start + 1,
        forall|i: int| 0 <= i < forms.len() && i != index ==> #[trigger] updated[i] == forms[i],
    ensures
        inserted_closes_match(source, updated, repairs.push(Repair::InsertedClose {
            offset, opening, list: index,
        })),
{
    reveal(inserted_closes_match);
    let all = repairs.push(Repair::InsertedClose { offset, opening, list: index });
    assert forall|i: int| 0 <= i < all.len() implies match #[trigger] all[i] {
        Repair::InsertedClose { offset, opening, list } => {
            &&& list < updated.len()
            &&& updated[list as int] is List
            &&& updated[list as int]->List_end > 0
            &&& offset == source.spec_bytes().len()
            &&& form_span(updated[list as int]).end == offset
            &&& form_span(updated[list as int]).start == opening.start
            &&& opening.end == opening.start + 1
        },
        _ => true,
    } by {
        if i < repairs.len() {
            assert(all[i] == repairs[i]);
            if all[i] is InsertedClose {
                let target = all[i]->InsertedClose_list;
                assert(target != index);
                assert(updated[target as int] == forms[target as int]);
            }
        }
    };
}

#[verifier::opaque]
pub open spec fn atom_and_close_error_evidence(source: &str, error: Error) -> bool {
    let bytes = source.spec_bytes();
    match error.kind {
        ErrorKind::InvalidAtom => {
            &&& error.span.start < error.span.end <= bytes.len()
            &&& bare_atom_kind(bytes[error.span.start as int..error.span.end as int]).is_none()
        },
        ErrorKind::UnexpectedClose => {
            &&& error.span.end == error.span.start + 1
            &&& error.span.end <= bytes.len()
            &&& bytes[error.span.start as int] == 41
        },
        _ => true,
    }
}

pub open spec fn string_error_opening(kind: ErrorKind, span: Range<usize>) -> Option<usize> {
    match kind {
        ErrorKind::InvalidEscape { opening } | ErrorKind::NewlineInString { opening } => Some(opening),
        ErrorKind::UnterminatedString => Some(span.start),
        _ => None,
    }
}

pub open spec fn structural_error_location(source: &str, error: Error) -> bool {
    let bytes = source.spec_bytes();
    match error.kind {
        ErrorKind::MissingSeparator => {
            &&& error.span.start == error.span.end
            &&& error.span.start < bytes.len()
            &&& is_char_boundary(bytes, error.span.start as int)
        },
        ErrorKind::UnclosedList { eof } => {
            &&& eof == bytes.len()
            &&& error.span.end == error.span.start + 1 <= eof
            &&& bytes[error.span.start as int] == 40
        },
        _ => true,
    }
}

#[verifier::opaque]
pub open spec fn syntax_error_evidence(source: &str, error: Error) -> bool {
    &&& atom_and_close_error_evidence(source, error)
    &&& structural_error_location(source, error)
    &&& match string_error_opening(error.kind, error.span) {
        Some(opening) => opening < source.spec_bytes().len()
            && string_error_site(source.spec_bytes()[opening as int..], opening as int, error),
        None => true,
    }
}

proof fn parser_error_evidence(source: &str, error: Error)
    requires
        structural_error_location(source, error),
        error.kind is MissingSeparator || error.kind is UnclosedList || (
            error.kind is UnexpectedClose
            && error.span.end == error.span.start + 1
            && error.span.end <= source.spec_bytes().len()
            && source.spec_bytes()[error.span.start as int] == 41
        ),
    ensures syntax_error_evidence(source, error),
{
    reveal(syntax_error_evidence);
    reveal(atom_and_close_error_evidence);
}

pub open spec fn repair_input_span(repair: Repair) -> Option<(int, int)> {
    match repair {
        Repair::Skipped { span, .. } => Some((span.start as int, span.end as int)),
        Repair::InsertedSeparator { offset } => Some((offset as int, offset as int)),
        Repair::InsertedClose { .. } => None,
    }
}

#[verifier::opaque]
pub open spec fn repair_input_spans_valid(source: &str, repairs: Seq<Repair>, consumed: int) -> bool {
    &&& 0 <= consumed <= source.spec_bytes().len()
    &&& forall|i: int| 0 <= i < repairs.len() ==> match repair_input_span(#[trigger] repairs[i]) {
        Some((start, end)) => {
            &&& 0 <= start <= end <= consumed
            &&& (repairs[i] is Skipped ==> start < end
                && syntax_error_evidence(source, repairs[i]->Skipped_error))
            &&& is_char_boundary(source.spec_bytes(), start)
            &&& is_char_boundary(source.spec_bytes(), end)
        },
        None => true,
    }
    &&& forall|i: int, j: int| 0 <= i < j < repairs.len()
        ==> match (repair_input_span(#[trigger] repairs[i]), repair_input_span(#[trigger] repairs[j])) {
            (Some((_, end)), Some((start, _))) => end <= start,
            _ => true,
        }
}

proof fn repair_spans_advance(source: &str, repairs: Seq<Repair>, before: int, after: int)
    requires
        repair_input_spans_valid(source, repairs, before),
        before <= after <= source.spec_bytes().len(),
    ensures repair_input_spans_valid(source, repairs, after),
{
    reveal(repair_input_spans_valid);
}

proof fn repair_spans_append(source: &str, repairs: Seq<Repair>, repair: Repair,
    before: int, after: int)
    requires
        repair_input_spans_valid(source, repairs, before),
        before <= after <= source.spec_bytes().len(),
        match repair_input_span(repair) {
            Some((start, end)) => {
                &&& before <= start <= end <= after
                &&& (repair is Skipped ==> start < end
                    && syntax_error_evidence(source, repair->Skipped_error))
                &&& is_char_boundary(source.spec_bytes(), start)
                &&& is_char_boundary(source.spec_bytes(), end)
            },
            None => true,
        },
    ensures repair_input_spans_valid(source, repairs.push(repair), after),
{
    reveal(repair_input_spans_valid);
    let extended = repairs.push(repair);
    assert forall|i: int| 0 <= i < extended.len() implies match repair_input_span(#[trigger] extended[i]) {
        Some((start, end)) => {
            &&& 0 <= start <= end <= after
            &&& (extended[i] is Skipped ==> start < end
                && syntax_error_evidence(source, extended[i]->Skipped_error))
            &&& is_char_boundary(source.spec_bytes(), start)
            &&& is_char_boundary(source.spec_bytes(), end)
        },
        None => true,
    } by {
        if i < repairs.len() {
            assert(extended[i] == repairs[i]);
        }
    };
    assert forall|i: int, j: int| 0 <= i < j < extended.len()
        implies match (repair_input_span(#[trigger] extended[i]), repair_input_span(#[trigger] extended[j])) {
            (Some((_, end)), Some((start, _))) => end <= start,
            _ => true,
        } by {
        assert(extended[i] == repairs[i]);
        if j < repairs.len() {
            assert(extended[j] == repairs[j]);
        }
    };
}

#[verifier::rlimit(30)]
fn parse_forms(source: &str, recovering: bool) -> (result: Result<(Vec<Form>, Vec<Repair>), Error>)
    ensures
        recovering ==> result.is_ok(),
        match result {
            Ok((forms, repairs)) => inserted_closes_match(source, forms@, repairs@)
                && repair_input_spans_valid(source, repairs@, source.spec_bytes().len() as int)
                && complete_list_indices(forms@) && nested_list_indices(forms@)
                && list_source_delimiters(source, forms@, recovering)
                && form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            Err(error) => syntax_error_evidence(source, error),
        },
{
    let mut forms: Vec<Form> = Vec::new();
    let mut open: Vec<usize> = Vec::new();
    let mut repairs: Vec<Repair> = Vec::new();
    let mut lexer = Lexer::new(source);
    let length = source.as_bytes().len();
    let ghost mut spans: Seq<(int, int)> = Seq::empty();
    proof {
        encode_utf8_valid_utf8(source@);
        reveal(form_spans_valid);
        assert(form_spans_valid(source, forms@, 0));
        reveal(nested_list_indices);
        assert(nested_list_indices(forms@));
        reveal(repair_input_spans_valid);
        assert(repair_input_spans_valid(source, repairs@, 0));
        reveal(list_source_delimiters);
        assert(list_source_delimiters(source, forms@, recovering));
    }

    loop
        invariant
            lexer.cursor.source == source,
            lexer.cursor.valid(),
            length == source.spec_bytes().len(),
            valid_utf8(source.spec_bytes()),
            covers(source.spec_bytes(), spans, lexer.cursor.position()),
            no_inserted_closes(repairs@),
            repair_input_spans_valid(source, repairs@, lexer.cursor.position()),
            form_spans_valid(source, forms@, lexer.cursor.position()),
            pending_lists(forms@, open@),
            list_indices(forms@, open@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, recovering),
            open_order(open@),
        decreases length - lexer.cursor.position(),
    {
        let Some((segment, next)) = lexer.next_segment() else {
            assert(covers(source.spec_bytes(), spans, length as int));
            break;
        };
        let ghost previous_position = lexer.cursor.position();
        let ghost old_forms = forms@;
        let kind = segment.kind;
        let span = segment.span;
        let missing_separator = segment.missing_separator;
        let ghost old_spans = spans;
        proof {
            spans = spans.push((span.start as int, span.end as int));
            assert forall|i: int| 0 <= i < spans.len() implies {
                let part = #[trigger] spans[i];
                &&& 0 <= part.0 < part.1 <= span.end
                &&& is_char_boundary(source.spec_bytes(), part.0)
                &&& is_char_boundary(source.spec_bytes(), part.1)
                &&& part.0 == if i == 0 { 0 } else { spans[i - 1].1 }
            } by {
                if i < old_spans.len() {
                    assert(spans[i] == old_spans[i]);
                }
            };
        }
        lexer = next;
        proof { advance_form_spans(source, forms@, previous_position, lexer.cursor.position()); }
        assert(covers(source.spec_bytes(), spans, lexer.cursor.position()));
        if missing_separator {
            if recovering {
                let repair = Repair::InsertedSeparator { offset: span.start };
                proof { repair_spans_append(source, repairs@, repair, previous_position, previous_position); }
                repairs.push(repair);
            } else {
                let error = Error { kind: ErrorKind::MissingSeparator, span: span.start..span.start };
                proof { parser_error_evidence(source, error); }
                return Err(error);
            }
        }
        let ghost repairs_before_segment = repairs@;
        match kind {
            SegmentKind::Whitespace | SegmentKind::Comment => {}
            SegmentKind::Malformed(error) => {
                if recovering {
                    let repair = Repair::Skipped { span, error };
                    proof { repair_spans_append(source, repairs@, repair, previous_position, lexer.cursor.position()); }
                    repairs.push(repair);
                } else {
                    return Err(error);
                }
            }
            SegmentKind::Open => {
                let ghost before = forms@;
                let ghost previous = open@;
                let index = forms.len();
                let form = Form::List { span, end: 0 };
                let ghost added = form;
                forms.push(form);
                assert(forms.len() == before.len() + 1);
                open.push(index);
                assert(open@[open@.len() - 1] == index);
                assert(exists|j: int| 0 <= j < open@.len() && open@[j] == index);
                assert(open@.contains(index));
                proof {
                    assert forall|value: usize| #[trigger] previous.contains(value)
                        implies open@.contains(value) by {
                        let j = choose|j: int| 0 <= j < previous.len() && previous[j] == value;
                        assert(open@[j] == value);
                    };
                    delimiters_after_append(source, before, added, recovering);
                    nested_after_append(before, added);
                    indices_after_append(before, previous, added, open@);
                    append_form_span(source, old_forms, added, previous_position, lexer.cursor.position());
                }
            }
            SegmentKind::Close => {
                let ghost previous = open@;
                if let Some(index) = open.pop() {
                    let ghost before = forms@;
                    finish_list(&mut forms, index, span.end);
                    proof {
                        delimiters_after_close(source, before, forms@, index as int, recovering);
                        nested_after_close(before, forms@, previous, index);
                        indices_after_finish(before, forms@, previous, open@, index);
                        close_form_span(source, before, forms@, index as int, previous_position, lexer.cursor.position());
                    }
                } else {
                    let error = Error {
                        kind: ErrorKind::UnexpectedClose,
                        span: span.start..span.end,
                    };
                    proof { parser_error_evidence(source, error); }
                    if recovering {
                        let repair = Repair::Skipped { span, error };
                        proof {
                            repair_spans_append(source, repairs@, repair, previous_position, lexer.cursor.position());
                        }
                        repairs.push(repair);
                    } else {
                        return Err(error);
                    }
                }
            }
            SegmentKind::Atom(kind) => {
                let ghost before = forms@;
                let form = Form::Atom { kind, span };
                let ghost added = form;
                forms.push(form);
                assert(forms.len() == before.len() + 1);
                proof {
                    delimiters_after_append(source, before, added, recovering);
                    nested_after_append(before, added);
                    indices_after_append(before, open@, added, open@);
                    append_form_span(source, old_forms, added, previous_position, lexer.cursor.position());
                }
            }
        }
        proof {
            if repairs@ == repairs_before_segment {
                repair_spans_advance(source, repairs@, previous_position, lexer.cursor.position());
            }
        }
    }

    proof { is_char_boundary_start_end_of_seq(source.spec_bytes()); }
    proof { no_closes_implies_evidence(source, forms@, repairs@); }
    while open.len() > 0
        invariant
            length == source.spec_bytes().len(),
            is_char_boundary(source.spec_bytes(), length as int),
            form_spans_valid(source, forms@, length as int),
            inserted_closes_match(source, forms@, repairs@),
            repair_input_spans_valid(source, repairs@, length as int),
            pending_lists(forms@, open@),
            list_indices(forms@, open@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, recovering),
            open_order(open@),
        decreases open@.len(),
    {
        let ghost previous = open@;
        let Some(index) = open.pop() else {
            unreachable!("nonempty list stack");
        };
        let span = match &forms[index] {
            Form::List { span, .. } => span,
            Form::Atom { .. } => unreachable!("only list indices are stacked"),
        };
        if recovering {
            assert(length > 0) by {
                reveal(list_source_delimiters);
                assert(list_delimited(source.spec_bytes(), forms@[index as int], recovering));
            };
            let opening = span.start..span.end;
            let ghost opening_evidence = opening;
            let ghost previous_repairs = repairs@;
            let repair = Repair::InsertedClose { offset: length, opening, list: index };
            proof { repair_spans_append(source, repairs@, repair, length as int, length as int); }
            repairs.push(repair);
            let ghost before = forms@;
            finish_list(&mut forms, index, length);
            proof {
                record_inserted_close(source, before, forms@, previous_repairs, index, opening_evidence, length);
                delimiters_after_close(source, before, forms@, index as int, recovering);
                nested_after_close(before, forms@, previous, index);
                indices_after_finish(before, forms@, previous, open@, index);
                close_form_span(source, before, forms@, index as int, length as int, length as int);
            }
        } else {
            let error = Error { kind: ErrorKind::UnclosedList { eof: length }, span: span.start..span.end };
            proof {
                assert(structural_error_location(source, error)) by {
                    reveal(list_source_delimiters);
                    assert(list_delimited(source.spec_bytes(), forms@[index as int], recovering));
                };
                parser_error_evidence(source, error);
            }
            return Err(error);
        }
    }

    assert(open@.len() == 0);
    let _form_count = forms.len();
    assert(_form_count == forms@.len());
    assert forall|i: int| 0 <= i < forms@.len() implies match #[trigger] forms@[i] {
        Form::List { end, .. } => i < end <= forms@.len(),
        Form::Atom { .. } => true,
    } by {
        assert(i <= usize::MAX);
        assert(!open@.contains(i as usize));
    };
    Ok((forms, repairs))
}

fn finish_list(forms: &mut Vec<Form>, index: usize, offset: usize)
    requires
        index < old(forms)@.len(),
        old(forms)@[index as int] is List,
    ensures
        final(forms)@.len() == old(forms)@.len(),
        match final(forms)@[index as int] {
            Form::List { span, end } => end == old(forms)@.len()
                && span.start == old(forms)@[index as int]->List_span.start
                && span.end == offset,
            Form::Atom { .. } => false,
        },
        forall|i: int| 0 <= i < old(forms)@.len() && i != index
            ==> #[trigger] final(forms)@[i] == old(forms)@[i],
{
    let subtree_end = forms.len();
    let start = match &forms[index] {
        Form::List { span, .. } => span.start,
        Form::Atom { .. } => unreachable!("only list indices are stacked"),
    };
    forms[index] = Form::List { span: start..offset, end: subtree_end };
}

spec fn is_suffix(source: Seq<u8>, suffix: Seq<u8>) -> bool {
    &&& suffix.len() <= source.len()
    &&& suffix =~= source[(source.len() - suffix.len())..]
}

proof fn suffix_transitive(source: Seq<u8>, middle: Seq<u8>, tail: Seq<u8>)
    requires
        is_suffix(source, middle),
        is_suffix(middle, tail),
    ensures
        is_suffix(source, tail),
{
    assert(tail =~= source[(source.len() - tail.len())..]);
}

proof fn suffix_boundary(source: &str, suffix: &str)
    requires
        is_suffix(source.spec_bytes(), suffix.spec_bytes()),
    ensures
        is_char_boundary(source.spec_bytes(),
            source.spec_bytes().len() - suffix.spec_bytes().len()),
{
    let bytes = source.spec_bytes();
    let rest = suffix.spec_bytes();
    let offset = bytes.len() - rest.len();
    encode_utf8_valid_utf8(source@);
    if rest.len() == 0 {
        is_char_boundary_start_end_of_seq(bytes);
    } else {
        encode_utf8_valid_utf8(suffix@);
        reveal_with_fuel(valid_utf8, 2);
        assert(bytes[offset] == rest[0]);
        assert(!is_continuation_byte(rest[0]));
        is_char_boundary_iff_not_is_continuation_byte(bytes, offset);
    }
}

#[derive(Clone, Copy)]
struct SourceCursor<'a> {
    source: &'a str,
    remaining: &'a str,
}

impl<'a> SourceCursor<'a> {
    spec fn valid(self) -> bool {
        is_suffix(self.source.spec_bytes(), self.remaining.spec_bytes())
    }

    spec fn position(self) -> int {
        self.source.spec_bytes().len() - self.remaining.spec_bytes().len()
    }

    fn new(source: &'a str) -> (cursor: Self)
        ensures
            cursor.source == source,
            cursor.valid(),
            cursor.position() == 0,
    {
        Self { source, remaining: source }
    }

    fn advance(self) -> (step: Option<(RawSegment<'a>, Range<usize>, Self)>)
        requires
            self.valid(),
        ensures
            match step {
                None => self.position() == self.source.spec_bytes().len(),
                Some((kind, span, next)) => {
                    &&& next.source == self.source
                    &&& next.valid()
                    &&& span.start == self.position()
                    &&& span.start < span.end
                    &&& span.end == next.position()
                    &&& span.end <= self.source.spec_bytes().len()
                    &&& (kind is Quoted && kind->Quoted_0 is None
                        ==> quoted_atom(self.source.spec_bytes()[span.start as int..span.end as int]))
                    &&& (kind is Quoted && kind->Quoted_0 is Some
                        ==> syntax_error_evidence(self.source, kind->Quoted_0->Some_0))
                    &&& (kind is Bare ==> kind->Bare_0.spec_bytes()
                        =~= self.source.spec_bytes()[span.start as int..span.end as int])
                    &&& (kind is Open ==> span.end == span.start + 1
                        && self.source.spec_bytes()[span.start as int] == 40)
                    &&& (kind is Close ==> span.end == span.start + 1
                        && self.source.spec_bytes()[span.start as int] == 41)
                    &&& is_char_boundary(self.source.spec_bytes(), span.start as int)
                    &&& is_char_boundary(self.source.spec_bytes(), span.end as int)
                },
            },
    {
        let source_length = self.source.as_bytes().len();
        let length = self.remaining.as_bytes().len();
        if length == 0 {
            return None;
        }
        let start = source_length - length;
        let (kind, remaining) = split_segment(self.remaining, start);
        let end = source_length - remaining.as_bytes().len();
        proof {
            suffix_transitive(
                self.source.spec_bytes(), self.remaining.spec_bytes(), remaining.spec_bytes()
            );
            suffix_boundary(self.source, self.remaining);
            suffix_boundary(self.source, remaining);
            if kind is Quoted && kind->Quoted_0 is Some {
                let error = kind->Quoted_0->Some_0;
                assert(syntax_error_evidence(self.source, error)) by {
                    reveal(syntax_error_evidence);
                    reveal(atom_and_close_error_evidence);
                    assert(self.remaining.spec_bytes() =~= self.source.spec_bytes()[start as int..]);
                    assert(string_error_opening(error.kind, error.span) == Some(start));
                };
            }
            if kind is Quoted && kind->Quoted_0 is None {
                assert(self.remaining.spec_bytes()[..(end - start)]
                    =~= self.source.spec_bytes()[start as int..end as int]);
            }
            if kind is Bare {
                assert(kind->Bare_0.spec_bytes() =~= self.remaining.spec_bytes()[..(end - start)]);
                assert(kind->Bare_0.spec_bytes() =~= self.source.spec_bytes()[start as int..end as int]);
            }
        }
        Some((kind, start..end, Self { source: self.source, remaining }))
    }
}

enum RawSegment<'a> {
    Whitespace,
    Comment,
    Open,
    Close,
    Quoted(Option<Error>),
    Bare(&'a str),
}

// 裸のアトムを分類する前に、入力の先頭から字句区間を1つ切り出す。
fn split_segment(input: &str, start: usize) -> (result: (RawSegment<'_>, &str))
    requires
        input.spec_bytes().len() > 0,
        start + input.spec_bytes().len() <= usize::MAX,
    ensures
        is_suffix(input.spec_bytes(), result.1.spec_bytes()),
        result.1.spec_bytes().len() < input.spec_bytes().len(),
        is_char_boundary(input.spec_bytes(), input.spec_bytes().len() - result.1.spec_bytes().len()),
        match result.0 {
            RawSegment::Bare(atom) =>
                atom.spec_bytes() + result.1.spec_bytes() =~= input.spec_bytes(),
            RawSegment::Open => input.spec_bytes()[0] == 40
                && result.1.spec_bytes().len() + 1 == input.spec_bytes().len(),
            RawSegment::Close => input.spec_bytes()[0] == 41
                && result.1.spec_bytes().len() + 1 == input.spec_bytes().len(),
            RawSegment::Quoted(None) => quoted_atom(input.spec_bytes()[..input.spec_bytes().len() - result.1.spec_bytes().len()]),
            RawSegment::Quoted(Some(error)) => string_error_kind(error.kind)
                && string_error_site(input.spec_bytes(), start as int, error),
            _ => true,
        },
{
    let first = input.as_bytes()[0];
    let (kind, remaining) = match first {
        b' ' | b'\t' | b'\r' | b'\n' => (
            RawSegment::Whitespace,
            split_at_boundary(input, Boundary::NonSpace).1,
        ),
        b';' => (RawSegment::Comment, split_at_boundary(input, Boundary::LineEnd).1),
        b'(' => (RawSegment::Open, after_ascii(input)),
        b')' => (RawSegment::Close, after_ascii(input)),
        b'"' => {
            let (remaining, error) = scan_string(input, start);
            (RawSegment::Quoted(error), remaining)
        }
        _ => {
            let (atom, remaining) = split_at_boundary(input, Boundary::AtomEnd);
            (RawSegment::Bare(atom), remaining)
        }
    };
    proof { suffix_boundary(input, remaining); }
    (kind, remaining)
}

spec fn string_error_kind(kind: ErrorKind) -> bool {
    kind is InvalidEscape || kind is NewlineInString || kind is UnterminatedString
}

pub open spec fn string_error_site(bytes: Seq<u8>, start: int, error: Error) -> bool {
    let at = error.span.start - start;
    let end = error.span.end - start;
    &&& bytes.len() > 0 && bytes[0] == 34
    &&& 0 <= at < end <= bytes.len()
    &&& match error.kind {
        ErrorKind::InvalidEscape { opening } => {
            &&& opening == start
            &&& at > 0 && at + 1 < end
            &&& bytes[at] == 92
            &&& bytes[at + 1] != 34 && bytes[at + 1] != 92
            &&& end == at + 1 + length_of_first_scalar(bytes[(at + 1)..])
        },
        ErrorKind::NewlineInString { opening } => {
            &&& opening == start && at > 0
            &&& end == at + 1
            &&& (bytes[at] == 10 || bytes[at] == 13)
        },
        ErrorKind::UnterminatedString => at == 0 && end == bytes.len(),
        _ => false,
    }
}

spec fn string_body_piece(bytes: Seq<u8>) -> bool {
    (forall|i: int| 0 <= i < bytes.len() ==> {
        let byte = #[trigger] bytes[i];
        byte != 34 && byte != 92 && byte != 10 && byte != 13
    })
        || (bytes.len() == 2 && bytes[0] == 92 && (bytes[1] == 34 || bytes[1] == 92))
}

spec fn string_body_pieces(pieces: Seq<Seq<u8>>) -> bool {
    forall|i: int| 0 <= i < pieces.len() ==> string_body_piece(#[trigger] pieces[i])
}

pub closed spec fn quoted_atom(bytes: Seq<u8>) -> bool {
    &&& valid_utf8(bytes)
    &&& bytes.len() >= 2
    &&& bytes[0] == 34
    &&& bytes[bytes.len() - 1] == 34
    &&& exists|pieces: Seq<Seq<u8>>| #[trigger] pieces.flatten() == bytes[1..bytes.len() - 1]
        && string_body_pieces(pieces)
}

proof fn extend_body(bytes: Seq<u8>, pieces: Seq<Seq<u8>>, piece: Seq<u8>, from: int, to: int)
    requires
        1 <= from <= to <= bytes.len(),
        string_body_pieces(pieces),
        pieces.flatten() == bytes[1..from],
        piece == bytes[from..to],
        string_body_piece(piece),
    ensures
        string_body_pieces(pieces.push(piece)),
        pieces.push(piece).flatten() == bytes[1..to],
{
    pieces.lemma_flatten_push(piece);
    assert(pieces.flatten() + piece =~= bytes[1..to]);
}

fn scan_string(input: &str, start: usize) -> (result: (&str, Option<Error>))
    requires
        input.spec_bytes().len() > 0,
        input.spec_bytes()[0] == 34,
        start + input.spec_bytes().len() <= usize::MAX,
    ensures
        is_suffix(input.spec_bytes(), result.0.spec_bytes()),
        result.0.spec_bytes().len() < input.spec_bytes().len(),
        is_char_boundary(input.spec_bytes(), input.spec_bytes().len() - result.0.spec_bytes().len()),
        match result.1 {
            Some(error) => string_error_kind(error.kind)
                && string_error_site(input.spec_bytes(), start as int, error)
                && (error.kind is UnterminatedString ==> result.0.spec_bytes().len() == 0),
            None => quoted_atom(input.spec_bytes()[..input.spec_bytes().len() - result.0.spec_bytes().len()]),
        },
{
    let length = input.as_bytes().len();
    let mut remaining = after_ascii(input);
    let mut error: Option<Error> = None;
    let ghost mut pieces: Seq<Seq<u8>> = Seq::empty();
    assert(pieces.flatten() =~= input.spec_bytes()[1..1]);
    loop
        invariant_except_break
            error.is_none() ==> string_body_pieces(pieces)
                && pieces.flatten() == input.spec_bytes()[1..length - remaining.spec_bytes().len()],
        invariant
            length == input.spec_bytes().len(),
            length > 0,
            input.spec_bytes()[0] == 34,
            start + length <= usize::MAX,
            is_suffix(input.spec_bytes(), remaining.spec_bytes()),
            remaining.spec_bytes().len() < length,
            match error {
                Some(error) => error.kind is InvalidEscape
                    && string_error_site(input.spec_bytes(), start as int, error),
                None => true,
            },
        ensures remaining.spec_bytes().len() == 0,
        decreases remaining.spec_bytes().len(),
    {
        let ghost before = remaining.spec_bytes();
        let (_ordinary, rest) = split_at_boundary(remaining, Boundary::StringSpecial);
        remaining = rest;
        proof {
            if error.is_none() {
                let from = length - before.len();
                let to = length - remaining.spec_bytes().len();
                let piece = _ordinary.spec_bytes();
                assert(piece =~= input.spec_bytes()[from..to]);
                assert(string_body_piece(piece));
                extend_body(input.spec_bytes(), pieces, piece, from, to);
                pieces = pieces.push(piece);
            }
        }
        proof { suffix_transitive(input.spec_bytes(), before, remaining.spec_bytes()); }
        let bytes = remaining.as_bytes();
        let position = start + (length - bytes.len());
        let ghost relative = position - start;
        if bytes.len() == 0 {
            break;
        }
        assert(input.spec_bytes()[relative] == bytes@[0]);
        match bytes[0] {
            b'"' => {
                let tail = after_ascii(remaining);
                proof { suffix_transitive(input.spec_bytes(), remaining.spec_bytes(), tail.spec_bytes()); }
                proof {
                    suffix_boundary(input, tail);
                    if error.is_none() {
                        encode_utf8_valid_utf8(input@);
                        valid_utf8_split(input.spec_bytes(), relative + 1);
                        let literal = input.spec_bytes()[..(relative + 1)];
                        assert(literal[0] == 34 && literal[relative] == 34);
                        assert(pieces.flatten() =~= literal[1..relative]);
                        assert(exists|p: Seq<Seq<u8>>| #[trigger] p.flatten() == literal[1..relative]
                            && string_body_pieces(p));
                        assert(quoted_atom(literal));
                    }
                }
                return (tail, error);
            }
            b'\r' | b'\n' => {
                if error.is_none() {
                    error = Some(Error { kind: ErrorKind::NewlineInString { opening: start }, span: position..position + 1 });
                }
                proof { suffix_boundary(input, remaining); }
                return (remaining, error);
            }
            _ => {
                assert(bytes[0] == b'\\');
                let ghost before_slash = remaining.spec_bytes();
                remaining = after_ascii(remaining);
                proof { suffix_transitive(input.spec_bytes(), before_slash, remaining.spec_bytes()); }
                let escaped_bytes = remaining.as_bytes();
                if escaped_bytes.len() == 0 {
                    break;
                }
                assert(escaped_bytes@ =~= input.spec_bytes()[(relative + 1)..]);
                let escaped = escaped_bytes[0];
                let (scalar, suffix) = split_first_scalar(remaining);
                if !matches!(escaped, b'"' | b'\\') && error.is_none() {
                    let width = scalar.as_bytes().len();
                    error = Some(Error {
                        kind: ErrorKind::InvalidEscape { opening: start },
                        span: position..position + 1 + width,
                    });
                }
                if !matches!(escaped, b'\r' | b'\n') {
                    proof {
                        suffix_transitive(input.spec_bytes(), remaining.spec_bytes(), suffix.spec_bytes());
                        if error.is_none() {
                            assert(escaped == 34 || escaped == 92);
                            assert(scalar.spec_bytes().len() == 1);
                            let piece = input.spec_bytes()[relative..relative + 2];
                            assert(string_body_piece(piece));
                            extend_body(input.spec_bytes(), pieces, piece, relative, relative + 2);
                            pieces = pieces.push(piece);
                        }
                    }
                    remaining = suffix;
                }
            }
        }
    }
    if error.is_none() {
        error = Some(Error {
            kind: ErrorKind::UnterminatedString,
            span: start..start + length,
        });
    }
    proof { suffix_boundary(input, remaining); }
    (remaining, error)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexer_preserves_all_source_and_ignores_parens_inside_malformed_strings() {
        let source = "(a \"日\\q); still inside\" ; comment\r\nb)";
        let segments: Vec<_> = Lexer::new(source).collect();
        let mut offset = 0;
        for segment in &segments {
            assert_eq!(segment.span.start, offset);
            assert!(segment.span.end > offset);
            assert!(source.is_char_boundary(segment.span.end));
            offset = segment.span.end;
        }
        assert_eq!(offset, source.len());
        let malformed = &segments[3];
        assert_eq!(&source[malformed.span.clone()], "\"日\\q); still inside\"");
        let SegmentKind::Malformed(error) = &malformed.kind else {
            panic!("expected malformed string");
        };
        assert_eq!(error.kind, ErrorKind::InvalidEscape { opening: 3 });
        assert_eq!(&source[error.span.clone()], "\\q");
        assert_eq!(
            segments
                .iter()
                .filter(|s| s.kind == SegmentKind::Close)
                .count(),
            1
        );
    }

    #[test]
    fn lexer_leaves_crlf_after_malformed_string_for_trivia() {
        let source = "\"bad\\\r\nb)";
        let segments: Vec<_> = Lexer::new(source).collect();
        assert_eq!(segments[0].span, 0..5);
        assert_eq!(&source[segments[1].span.clone()], "\r\n");
        assert_eq!(segments[2].kind, SegmentKind::Atom(AtomKind::Name));
        assert_eq!(segments[3].kind, SegmentKind::Close);
        assert_eq!(
            parse(source).unwrap_err().kind,
            ErrorKind::InvalidEscape { opening: 0 }
        );
    }

    #[test]
    fn missing_separator_retains_the_intrinsic_error() {
        let source = "a\"\\q\"";
        let segment = Lexer::new(source).nth(1).unwrap();
        assert!(segment.missing_separator);
        assert!(matches!(
            segment.kind,
            SegmentKind::Malformed(Error {
                kind: ErrorKind::InvalidEscape { opening: 1 },
                ..
            })
        ));
        assert_eq!(parse(source).unwrap_err().kind, ErrorKind::MissingSeparator);
    }

    #[test]
    fn whitespace_ends_before_a_multibyte_character() {
        let source = " \t\r\n日";
        let mut lexer = Lexer::new(source);
        let whitespace = lexer.next().unwrap();
        assert_eq!(whitespace.kind, SegmentKind::Whitespace);
        assert_eq!(whitespace.span, 0..4);
        let atom = lexer.next().unwrap();
        assert_eq!(atom.span, 4..source.len());
        assert_eq!(parse(source).unwrap_err().span, atom.span);
    }

    #[test]
    fn parentheses_consume_one_byte_before_multibyte_input() {
        let source = "(日)本";
        let segments: Vec<_> = Lexer::new(source).collect();
        assert_eq!(segments[0].kind, SegmentKind::Open);
        assert_eq!(segments[0].span, 0..1);
        assert_eq!(segments[1].span, 1..4);
        assert_eq!(segments[2].kind, SegmentKind::Close);
        assert_eq!(segments[2].span, 4..5);
        assert_eq!(segments[3].span, 5..8);
    }

    #[test]
    fn string_ordinary_parts_and_escaped_quote_preserve_the_true_end() {
        let source = r#""日); \"本"()"#;
        let segments: Vec<_> = Lexer::new(source).collect();
        assert_eq!(segments.len(), 3);
        assert_eq!(segments[0].kind, SegmentKind::Atom(AtomKind::String));
        assert_eq!(&source[segments[0].span.clone()], r#""日); \"本""#);
        assert_eq!(segments[1].kind, SegmentKind::Open);
        assert_eq!(segments[2].kind, SegmentKind::Close);
    }

    #[test]
    fn malformed_string_keeps_first_error_and_full_scalar_span() {
        let source = "\"\\日\n";
        let segments: Vec<_> = Lexer::new(source).collect();
        assert_eq!(segments[0].span, 0..5);
        assert_eq!(segments[1].kind, SegmentKind::Whitespace);
        let error = parse(source).unwrap_err();
        assert_eq!(error.kind, ErrorKind::InvalidEscape { opening: 0 });
        assert_eq!(error.span, 1..5);
        assert_eq!(
            parse("\"\\").unwrap_err().kind,
            ErrorKind::UnterminatedString
        );
    }

    #[test]
    fn invalid_escape_spans_one_scalar_at_every_utf8_width() {
        for scalar in ['q', 'é', '日', '😀'] {
            let source = alloc::format!("\"\\{scalar}\"()");
            let segments: Vec<_> = Lexer::new(&source).collect();
            let end = 2 + scalar.len_utf8();
            assert_eq!(
                parse(&source).unwrap_err(),
                Error {
                    kind: ErrorKind::InvalidEscape { opening: 0 },
                    span: 1..end,
                }
            );
            assert_eq!(segments[0].span, 0..end + 1);
            assert_eq!(segments[1].kind, SegmentKind::Open);
            assert_eq!(segments[1].span.start, end + 1);
        }
    }
}
