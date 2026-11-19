use crate::{AtomKind, Error, Form, parse};
use alloc::vec::Vec;
use core::ops::Range;

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
    let head = match &source[head_span.clone()] {
        "using" => Head::Using,
        "namespace" => Head::Namespace,
        "use" => Head::Use,
        "export" => Head::Export,
        "func" => Head::Func,
        "module" => Head::Module,
        "module-part" => Head::ModulePart,
        "struct" => Head::Struct,
        "latch" => Head::Latch,
        "memory" => Head::Memory,
        "test" => Head::Test,
        _ => return Err(header_error(HeaderError::UnknownHead, head_span)),
    };
    if in_namespace && matches!(head, Head::Namespace | Head::Using) {
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
