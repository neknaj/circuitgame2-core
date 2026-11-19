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
    ExpectedReference,
    ExpectedNatural,
    ExpectedPort,
    ExpectedType,
    ExpectedClause(Clause),
    UnexpectedArgument,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Clause {
    In,
    Out,
    Bits,
    Width,
    Address,
    Data,
    At,
}

impl Clause {
    fn spelling(self) -> &'static str {
        match self {
            Self::In => "in",
            Self::Out => "out",
            Self::Bits => "bits",
            Self::Width => "width",
            Self::Address => "address",
            Self::Data => "data",
            Self::At => "at",
        }
    }
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
        Head::Test => {
            require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedReference,
                is_reference,
            )?;
        }
        Head::Func
        | Head::Module
        | Head::ModulePart
        | Head::Struct
        | Head::Latch
        | Head::Memory => {
            require_name(forms, argument, end, closing)?;
            declaration_signature(source, forms, head, argument + 1, end, closing)?;
        }
    }
    Ok((head, end))
}

fn declaration_signature(
    source: &str,
    forms: &[Form],
    head: Head,
    argument: usize,
    end: usize,
    closing: usize,
) -> Result<(), CircuitFormError> {
    match head {
        Head::Func | Head::Module => {
            let out = ports(source, forms, argument, end, closing, Clause::In)?;
            ports(source, forms, out, end, closing, Clause::Out)?;
        }
        Head::Struct | Head::Latch => {
            let mut field = natural_clause(source, forms, argument, end, closing, Clause::Width)?;
            if head == Head::Latch {
                return require_end(forms, field, end);
            }
            while field < end {
                let (field_end, field_close) =
                    list_at(forms, field, end, closing, HeaderError::ExpectedList)?;
                require_name(forms, field + 1, field_end, field_close)?;
                let at = type_at(source, forms, field + 2, field_end, field_close)?;
                let next = natural_clause(source, forms, at, field_end, field_close, Clause::At)?;
                require_end(forms, next, field_end)?;
                field = field_end;
            }
        }
        Head::Memory => {
            let data = natural_clause(source, forms, argument, end, closing, Clause::Address)?;
            let (data_end, data_close) =
                named_clause(source, forms, data, end, closing, Clause::Data)?;
            let next = type_at(source, forms, data + 2, data_end, data_close)?;
            require_end(forms, next, data_end)?;
            require_end(forms, data_end, end)?;
        }
        _ => {}
    }
    Ok(())
}

fn ports(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    clause: Clause,
) -> Result<usize, CircuitFormError> {
    let (port_end, port_close) = named_clause(source, forms, index, end, closing, clause)?;
    let mut port = index + 2;
    if clause == Clause::Out && port == port_end {
        return Err(header_error(
            HeaderError::ExpectedPort,
            port_close..port_close,
        ));
    }
    while port < port_end {
        port = match &forms[port] {
            Form::Atom {
                kind: AtomKind::Name,
                ..
            } => port + 1,
            Form::List { .. } => {
                let (typed_end, typed_close) =
                    list_at(forms, port, port_end, port_close, HeaderError::ExpectedPort)?;
                require_name(forms, port + 1, typed_end, typed_close)?;
                let next = type_at(source, forms, port + 2, typed_end, typed_close)?;
                require_end(forms, next, typed_end)?;
                typed_end
            }
            form => return Err(header_error(HeaderError::ExpectedPort, span(form))),
        };
    }
    Ok(port_end)
}

fn type_at(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<usize, CircuitFormError> {
    if index >= end {
        return Err(header_error(HeaderError::ExpectedType, closing..closing));
    }
    match &forms[index] {
        Form::Atom { kind, .. } if is_reference(*kind) => Ok(index + 1),
        Form::List { .. } => natural_clause(source, forms, index, end, closing, Clause::Bits),
        form => Err(header_error(HeaderError::ExpectedType, span(form))),
    }
}

fn natural_clause(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    clause: Clause,
) -> Result<usize, CircuitFormError> {
    let (clause_end, clause_close) = named_clause(source, forms, index, end, closing, clause)?;
    require_atom(
        forms,
        index + 2,
        clause_end,
        clause_close,
        HeaderError::ExpectedNatural,
        |kind| kind == AtomKind::Natural,
    )?;
    require_end(forms, index + 3, clause_end)?;
    Ok(clause_end)
}

fn named_clause(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    clause: Clause,
) -> Result<(usize, usize), CircuitFormError> {
    let expected = HeaderError::ExpectedClause(clause);
    let (clause_end, clause_close) = list_at(forms, index, end, closing, expected)?;
    let head = require_atom(
        forms,
        index + 1,
        clause_end,
        clause_close,
        expected,
        |kind| kind == AtomKind::Name,
    )?;
    if &source[head.clone()] != clause.spelling() {
        return Err(header_error(expected, head));
    }
    Ok((clause_end, clause_close))
}

fn list_at(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    expected: HeaderError,
) -> Result<(usize, usize), CircuitFormError> {
    if index >= end {
        return Err(header_error(expected, closing..closing));
    }
    match &forms[index] {
        Form::List { span, end } => Ok((*end, span.end - 1)),
        form => Err(header_error(expected, span(form))),
    }
}

fn require_name(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<(), CircuitFormError> {
    require_atom(
        forms,
        index,
        end,
        closing,
        HeaderError::ExpectedName,
        |kind| kind == AtomKind::Name,
    )?;
    Ok(())
}

fn is_reference(kind: AtomKind) -> bool {
    matches!(
        kind,
        AtomKind::Name | AtomKind::RelativePath | AtomKind::AbsolutePath
    )
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
