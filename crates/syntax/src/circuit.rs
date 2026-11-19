use crate::{AtomKind, Error, Form, parse};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Head {
    Using,
    Namespace,
    Use,
    Export,
    Func,
    Module,
    ModulePart,
    Struct,
    Latch,
    Memory,
    Test,
}

} // verus!

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry {
    pub head: Head,
    pub form: usize,
    pub namespace: Option<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CircuitForms {
    pub forms: Vec<Form>,
    pub entries: Vec<Entry>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeaderError {
    ExpectedList,
    ExpectedHead,
    UnknownHead,
    MisplacedHead(Head),
    ExpectedNamespacePath,
    ExpectedNor,
    ExpectedAbsolutePath,
    ExpectedName,
    UnexpectedArgument,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitFormError {
    Syntax(Error),
    Header {
        kind: HeaderError,
        span: Range<usize>,
    },
}

/// Indexes circuit form headers by their position in the S-expression forest.
/// Declaration bodies, expressions, and project-wide rules require further validation.
pub fn index_headers(source: &str) -> Result<CircuitForms, CircuitFormError> {
    let forms = parse(source).map_err(CircuitFormError::Syntax)?;
    let mut entries = Vec::new();
    let mut root = 0;
    while root < forms.len() {
        let (head, end) = read_header(source, &forms, root, false)?;
        entries.push(Entry {
            head,
            form: root,
            namespace: None,
        });
        if head == Head::Namespace {
            let mut item = root + 3;
            while item < end {
                let (head, next) = read_header(source, &forms, item, true)?;
                entries.push(Entry {
                    head,
                    form: item,
                    namespace: Some(root),
                });
                item = next;
            }
        }
        root = end;
    }
    Ok(CircuitForms { forms, entries })
}

fn read_header(
    source: &str,
    forms: &[Form],
    index: usize,
    in_namespace: bool,
) -> Result<(Head, usize), CircuitFormError> {
    let Form::List {
        span: list_span,
        end,
    } = &forms[index]
    else {
        return Err(header_error(HeaderError::ExpectedList, span(&forms[index])));
    };
    let end = *end;
    let head_index = index + 1;
    let argument = head_index + 1;
    let closing = list_span.end - 1;
    let head_span = require_atom(
        forms,
        head_index,
        end,
        closing,
        HeaderError::ExpectedHead,
        |kind| kind == AtomKind::Name,
    )?;
    let Some(head) = recognize_head(&source[head_span.clone()]) else {
        return Err(header_error(HeaderError::UnknownHead, head_span));
    };
    if !head_allowed(head, in_namespace) {
        return Err(header_error(HeaderError::MisplacedHead(head), head_span));
    }
    match head {
        Head::Using => {
            let nor = require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedNor,
                |kind| kind == AtomKind::Name,
            )?;
            if &source[nor.clone()] != "nor" {
                return Err(header_error(HeaderError::ExpectedNor, nor));
            }
            require_end(forms, argument + 1, end)?;
        }
        Head::Namespace => {
            require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedNamespacePath,
                |kind| matches!(kind, AtomKind::Name | AtomKind::RelativePath),
            )?;
        }
        Head::Use => {
            require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedAbsolutePath,
                |kind| kind == AtomKind::AbsolutePath,
            )?;
            require_atom(
                forms,
                argument + 1,
                end,
                closing,
                HeaderError::ExpectedName,
                |kind| kind == AtomKind::Name,
            )?;
            require_end(forms, argument + 2, end)?;
        }
        Head::Export => {
            require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedName,
                |kind| kind == AtomKind::Name,
            )?;
            for item in argument + 1..end {
                require_atom(
                    forms,
                    item,
                    end,
                    closing,
                    HeaderError::ExpectedName,
                    |kind| kind == AtomKind::Name,
                )?;
            }
        }
        _ => {}
    }
    Ok((head, end))
}

fn require_atom(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    expected: HeaderError,
    accepts: impl FnOnce(AtomKind) -> bool,
) -> Result<Range<usize>, CircuitFormError> {
    if index >= end {
        return Err(header_error(expected, closing..closing));
    }
    match &forms[index] {
        Form::Atom { kind, span } if accepts(*kind) => Ok(span.clone()),
        form => Err(header_error(expected, span(form))),
    }
}

fn require_end(forms: &[Form], at: usize, end: usize) -> Result<(), CircuitFormError> {
    if at < end {
        Err(header_error(
            HeaderError::UnexpectedArgument,
            span(&forms[at]),
        ))
    } else {
        Ok(())
    }
}

fn span(form: &Form) -> Range<usize> {
    match form {
        Form::Atom { span, .. } | Form::List { span, .. } => span.clone(),
    }
}

fn header_error(kind: HeaderError, span: Range<usize>) -> CircuitFormError {
    CircuitFormError::Header { kind, span }
}

verus! {

pub open spec fn head_spelling(head: Head) -> &'static str {
    match head {
        Head::Using => "using",
        Head::Namespace => "namespace",
        Head::Use => "use",
        Head::Export => "export",
        Head::Func => "func",
        Head::Module => "module",
        Head::ModulePart => "module-part",
        Head::Struct => "struct",
        Head::Latch => "latch",
        Head::Memory => "memory",
        Head::Test => "test",
    }
}

fn recognize_head(word: &str) -> (head: Option<Head>)
    ensures
        forall|candidate: Head| #[trigger] head_spelling(candidate)@ == word@
            <==> head == Some(candidate),
{
    let head = if word == "using" { Some(Head::Using) }
        else if word == "namespace" { Some(Head::Namespace) }
        else if word == "use" { Some(Head::Use) }
        else if word == "export" { Some(Head::Export) }
        else if word == "func" { Some(Head::Func) }
        else if word == "module" { Some(Head::Module) }
        else if word == "module-part" { Some(Head::ModulePart) }
        else if word == "struct" { Some(Head::Struct) }
        else if word == "latch" { Some(Head::Latch) }
        else if word == "memory" { Some(Head::Memory) }
        else if word == "test" { Some(Head::Test) }
        else { None };
    assert forall|candidate: Head| #[trigger] head_spelling(candidate)@ == word@
        <==> head == Some(candidate) by {
    };
    head
}

pub open spec fn head_in_context(head: Head, in_namespace: bool) -> bool {
    !in_namespace || !(head is Using || head is Namespace)
}

fn head_allowed(head: Head, in_namespace: bool) -> (allowed: bool)
    ensures allowed == head_in_context(head, in_namespace),
{
    !in_namespace || !matches!(head, Head::Using | Head::Namespace)
}

} // verus!
