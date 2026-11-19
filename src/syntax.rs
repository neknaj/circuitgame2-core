use crate::boundary::{Boundary, after_ascii, split_at_boundary, split_first_scalar};
#[cfg(verus_only)]
use crate::digits::digit;
use crate::digits::{Radix, matches_digits};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    encode_utf8_valid_utf8, is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq, is_continuation_byte, valid_utf8,
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
            Ok(forms) => complete_list_indices(forms@),
            Err(_) => true,
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
    ensures complete_list_indices(result.forms@),
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
        0 <= index < forms.len() && forms[index] is List
    }
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

#[verifier::rlimit(30)]
fn parse_forms(source: &str, recovering: bool) -> (result: Result<(Vec<Form>, Vec<Repair>), Error>)
    ensures
        recovering ==> result.is_ok(),
        match result {
            Ok((forms, _)) => complete_list_indices(forms@),
            Err(_) => true,
        },
{
    let mut forms: Vec<Form> = Vec::new();
    let mut open: Vec<usize> = Vec::new();
    let mut repairs: Vec<Repair> = Vec::new();
    let mut lexer = Lexer::new(source);
    let length = source.as_bytes().len();
    let ghost mut spans: Seq<(int, int)> = Seq::empty();
    proof { encode_utf8_valid_utf8(source@); }

    loop
        invariant
            lexer.cursor.source == source,
            lexer.cursor.valid(),
            length == source.spec_bytes().len(),
            valid_utf8(source.spec_bytes()),
            covers(source.spec_bytes(), spans, lexer.cursor.position()),
            pending_lists(forms@, open@),
            list_indices(forms@, open@),
        decreases length - lexer.cursor.position(),
    {
        let Some((segment, next)) = lexer.next_segment() else {
            assert(covers(source.spec_bytes(), spans, length as int));
            break;
        };
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
        assert(covers(source.spec_bytes(), spans, lexer.cursor.position()));
        if missing_separator {
            if recovering {
                repairs.push(Repair::InsertedSeparator { offset: span.start });
            } else {
                return Err(Error {
                    kind: ErrorKind::MissingSeparator,
                    span: span.start..span.start,
                });
            }
        }
        match kind {
            SegmentKind::Whitespace | SegmentKind::Comment => {}
            SegmentKind::Malformed(error) => {
                if recovering {
                    repairs.push(Repair::Skipped { span, error });
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
                    indices_after_append(before, previous, added, open@);
                }
            }
            SegmentKind::Close => {
                let ghost previous = open@;
                if let Some(index) = open.pop() {
                    let ghost before = forms@;
                    finish_list(&mut forms, index, span.end);
                    proof { indices_after_finish(before, forms@, previous, open@, index); }
                } else {
                    let error = Error {
                        kind: ErrorKind::UnexpectedClose,
                        span: span.start..span.end,
                    };
                    if recovering {
                        repairs.push(Repair::Skipped { span, error });
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
                proof { indices_after_append(before, open@, added, open@); }
            }
        }
    }

    while open.len() > 0
        invariant
            pending_lists(forms@, open@),
            list_indices(forms@, open@),
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
            repairs.push(Repair::InsertedClose {
                offset: length,
                opening: span.start..span.end,
                list: index,
            });
            let ghost before = forms@;
            finish_list(&mut forms, index, length);
            proof { indices_after_finish(before, forms@, previous, open@, index); }
        } else {
            return Err(Error {
                kind: ErrorKind::UnclosedList { eof: length },
                span: span.start..span.end,
            });
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
                Some((_, span, next)) => {
                    &&& next.source == self.source
                    &&& next.valid()
                    &&& span.start == self.position()
                    &&& span.start < span.end
                    &&& span.end == next.position()
                    &&& span.end <= self.source.spec_bytes().len()
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
            Some(error) => start <= error.span.start < error.span.end
                <= start + input.spec_bytes().len(),
            None => true,
        },
{
    let length = input.as_bytes().len();
    let mut remaining = after_ascii(input);
    let mut error: Option<Error> = None;
    loop
        invariant
            length == input.spec_bytes().len(),
            start + length <= usize::MAX,
            is_suffix(input.spec_bytes(), remaining.spec_bytes()),
            remaining.spec_bytes().len() < length,
            match error {
                Some(error) => start <= error.span.start < error.span.end <= start + length,
                None => true,
            },
        decreases remaining.spec_bytes().len(),
    {
        let ghost before = remaining.spec_bytes();
        remaining = split_at_boundary(remaining, Boundary::StringSpecial).1;
        proof { suffix_transitive(input.spec_bytes(), before, remaining.spec_bytes()); }
        let bytes = remaining.as_bytes();
        let position = start + (length - bytes.len());
        if bytes.len() == 0 {
            break;
        }
        match bytes[0] {
            b'"' => {
                let tail = after_ascii(remaining);
                proof { suffix_transitive(input.spec_bytes(), remaining.spec_bytes(), tail.spec_bytes()); }
                proof { suffix_boundary(input, tail); }
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
                    proof { suffix_transitive(input.spec_bytes(), remaining.spec_bytes(), suffix.spec_bytes()); }
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

verus! {

spec fn digit_sequence(bytes: Seq<u8>, radix: Radix) -> bool {
    &&& bytes.len() > 0
    &&& forall|i: int| 0 <= i < bytes.len() ==> digit(radix, #[trigger] bytes[i])
}

spec fn bare_atom_kind(bytes: Seq<u8>) -> Option<AtomKind> {
    if bytes.len() >= 2 && bytes[0] == 35 && bytes[1] == 98 {
        if digit_sequence(bytes[2..], Radix::Binary) { Some(AtomKind::Binary) } else { None }
    } else if bytes.len() >= 2 && bytes[0] == 35 && bytes[1] == 120 {
        if digit_sequence(bytes[2..], Radix::Hexadecimal) { Some(AtomKind::Hexadecimal) } else { None }
    } else if bytes.len() >= 1 && bytes[0] == 45 {
        if digit_sequence(bytes[1..], Radix::Decimal) { Some(AtomKind::NegativeInteger) } else { None }
    } else if digit_sequence(bytes, Radix::Decimal) {
        Some(AtomKind::Natural)
    } else {
        path_kind(bytes)
    }
}

fn classify(atom: &str) -> (result: Option<AtomKind>)
    ensures result == bare_atom_kind(atom.spec_bytes()),
{
    let bytes = atom.as_bytes();
    if bytes.len() >= 2 && bytes[0] == b'#' && matches!(bytes[1], b'b' | b'x') {
        let tail = after_ascii(after_ascii(atom));
        assert(tail.spec_bytes() =~= bytes@[2..]);
        let (radix, kind) = if bytes[1] == b'b' {
            (Radix::Binary, AtomKind::Binary)
        } else {
            (Radix::Hexadecimal, AtomKind::Hexadecimal)
        };
        if matches_digits(tail.as_bytes(), radix) { Some(kind) } else { None }
    } else if bytes.len() > 0 && bytes[0] == b'-' {
        let tail = after_ascii(atom);
        if matches_digits(tail.as_bytes(), Radix::Decimal) {
            Some(AtomKind::NegativeInteger)
        } else {
            None
        }
    } else if matches_digits(bytes, Radix::Decimal) {
        Some(AtomKind::Natural)
    } else {
        classify_path(atom)
    }
}

spec fn name_start(byte: u8) -> bool {
    65 <= byte <= 90 || 97 <= byte <= 122 || byte == 95
}

spec fn name_continue(byte: u8) -> bool {
    name_start(byte) || 48 <= byte <= 57 || byte == 45
}

spec fn name_component(bytes: Seq<u8>) -> bool {
    &&& bytes.len() > 0
    &&& name_start(bytes[0])
    &&& forall|i: int| 0 < i < bytes.len() ==> name_continue(#[trigger] bytes[i])
}

fn is_name(name: &str) -> (accepted: bool)
    ensures
        accepted == name_component(name.spec_bytes()),
{
    let bytes = name.as_bytes();
    if bytes.len() == 0 || !matches!(bytes[0], b'A'..=b'Z' | b'a'..=b'z' | b'_') {
        return false;
    }
    let mut i = 1;
    while i < bytes.len()
        invariant
            bytes@ == name.spec_bytes(),
            1 <= i <= bytes@.len(),
            name_start(bytes@[0]),
            forall|j: int| 0 < j < i ==> name_continue(#[trigger] bytes@[j]),
        decreases bytes@.len() - i,
    {
        if !matches!(bytes[i], b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' | b'-') {
            assert(!name_continue(bytes@[i as int]));
            assert(!name_component(bytes@));
            return false;
        }
        i += 1;
    }
    true
}

spec fn first_colon(bytes: Seq<u8>, at: int) -> bool {
    &&& 0 <= at <= bytes.len()
    &&& (at < bytes.len() ==> bytes[at] == 58)
    &&& forall|i: int| 0 <= i < at ==> #[trigger] bytes[i] != 58
}

spec fn colon_pair(bytes: Seq<u8>, at: int) -> bool {
    0 <= at && at + 1 < bytes.len() && bytes[at] == 58 && bytes[at + 1] == 58
}

spec fn path_body(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    if exists|at: int| first_colon(bytes, at) {
        let at = choose|at: int| first_colon(bytes, at);
        name_component(bytes[..at]) && (
            at == bytes.len() || (colon_pair(bytes, at) && path_body(bytes[(at + 2)..]))
        )
    } else {
        false
    }
}

proof fn path_body_at(bytes: Seq<u8>, at: int)
    requires
        first_colon(bytes, at),
    ensures
        path_body(bytes) == (name_component(bytes[..at]) && (
            at == bytes.len() || (colon_pair(bytes, at) && path_body(bytes[(at + 2)..]))
        )),
{
    reveal_with_fuel(path_body, 1);
    assert(exists|other: int| first_colon(bytes, other));
    let other = choose|other: int| first_colon(bytes, other);
    if at < other {
        assert(bytes[at] == 58 && bytes[at] != 58);
    } else if other < at {
        assert(bytes[other] == 58 && bytes[other] != 58);
    }
}

fn has_colon_pair(source: &str) -> (pair: bool)
    ensures pair == colon_pair(source.spec_bytes(), 0),
{
    let bytes = source.as_bytes();
    bytes.len() >= 2 && bytes[0] == b':' && bytes[1] == b':'
}

spec fn path_kind(bytes: Seq<u8>) -> Option<AtomKind> {
    if colon_pair(bytes, 0) {
        if path_body(bytes[2..]) { Some(AtomKind::AbsolutePath) } else { None }
    } else if name_component(bytes) {
        Some(AtomKind::Name)
    } else if path_body(bytes) {
        Some(AtomKind::RelativePath)
    } else {
        None
    }
}

fn classify_path(atom: &str) -> (result: Option<AtomKind>)
    ensures result == path_kind(atom.spec_bytes()),
{
    let absolute = has_colon_pair(atom);
    let body = if absolute {
        let after_first = after_ascii(atom);
        let tail = after_ascii(after_first);
        assert(tail.spec_bytes() =~= atom.spec_bytes()[2..]);
        tail
    } else {
        atom
    };
    let mut remaining = body;
    let mut qualified = absolute;
    loop
        invariant
            absolute == colon_pair(atom.spec_bytes(), 0),
            body.spec_bytes() =~= if absolute { atom.spec_bytes()[2..] } else { atom.spec_bytes() },
            path_body(remaining.spec_bytes()) == path_body(body.spec_bytes()),
            !qualified ==> remaining == body,
            qualified && !absolute ==> !name_component(body.spec_bytes()),
        decreases remaining.spec_bytes().len(),
    {
        let (name, separator) = split_at_boundary(remaining, Boundary::Colon);
        let ghost bytes = remaining.spec_bytes();
        let ghost at = name.spec_bytes().len() as int;
        proof {
            assert(name.spec_bytes() =~= bytes[..at]);
            assert(separator.spec_bytes() =~= bytes[at..]);
            assert(first_colon(bytes, at));
            path_body_at(bytes, at);
        }
        if !is_name(name) {
            return None;
        }
        if separator.as_bytes().len() == 0 {
            return Some(if absolute {
                AtomKind::AbsolutePath
            } else if qualified {
                AtomKind::RelativePath
            } else {
                AtomKind::Name
            });
        }
        if !has_colon_pair(separator) {
            return None;
        }
        if !qualified {
            assert(bytes[at] == 58);
            assert(!name_component(body.spec_bytes()));
        }
        let tail = after_ascii(after_ascii(separator));
        assert(tail.spec_bytes() =~= bytes[(at + 2)..]);
        remaining = tail;
        qualified = true;
    }
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
