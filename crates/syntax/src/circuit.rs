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
    ExpectedBodyItem,
    ExpectedTarget,
    ExpectedExpression,
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

/// 回路フォームの宣言位置を構文木の添字で返す。
///
/// 宣言のシグネチャと回路本体の構文を検査する。テスト本体の構文検査、名前解決、型と結線の検査は後続の処理に委ねる。
///
/// # Errors
///
/// 字句、S 式、検査対象の回路フォームに誤りがあれば、元入力の UTF-8 バイト範囲をエラーに含める。
/// 回路フォームに必須の要素がなければ、挿入位置を長さ0の範囲で示す。
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
            let first_body = ports(source, forms, out, end, closing, Clause::Out)?;
            routine_body(source, forms, first_body, end, closing)?;
        }
        Head::ModulePart => routine_body(source, forms, argument, end, closing)?,
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

fn routine_body(
    source: &str,
    forms: &[Form],
    mut item: usize,
    end: usize,
    closing: usize,
) -> Result<(), CircuitFormError> {
    while item < end {
        let (item_end, item_close) =
            list_at(forms, item, end, closing, HeaderError::ExpectedBodyItem)?;
        let head = require_atom(
            forms,
            item + 1,
            item_end,
            item_close,
            HeaderError::ExpectedBodyItem,
            |kind| kind == AtomKind::Name,
        )?;
        let first = item + 2;
        match recognize_body_head(&source[head.clone()]) {
            Some(BodyHead::Expand) => {
                require_atom(
                    forms,
                    first,
                    item_end,
                    item_close,
                    HeaderError::ExpectedReference,
                    is_reference,
                )?;
            }
            Some(BodyHead::Def) => {
                let value = targets(forms, first, item_end, item_close)?;
                let after_value = expression_end(forms, value, item_end, item_close)?;
                require_end(forms, after_value, item_end)?;
                expressions(source, forms, value..after_value)?;
            }
            None => return Err(header_error(HeaderError::ExpectedBodyItem, head)),
        }
        item = item_end;
    }
    Ok(())
}

fn targets(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<usize, CircuitFormError> {
    if index >= end {
        return Err(header_error(HeaderError::ExpectedTarget, closing..closing));
    }
    match &forms[index] {
        Form::Atom {
            kind: AtomKind::Name,
            ..
        } => Ok(index + 1),
        Form::List { span, end } => {
            let closing = span.end - 1;
            let first = index + 1;
            require_name(forms, first, *end, closing)?;
            for name in first + 1..*end {
                require_name(forms, name, *end, closing)?;
            }
            Ok(*end)
        }
        form => Err(header_error(HeaderError::ExpectedTarget, span(form))),
    }
}

fn expression_end(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<usize, CircuitFormError> {
    if index >= end {
        return Err(header_error(
            HeaderError::ExpectedExpression,
            closing..closing,
        ));
    }
    Ok(match &forms[index] {
        Form::Atom { .. } => index + 1,
        Form::List { end, .. } => *end,
    })
}

fn expressions(source: &str, forms: &[Form], roots: Range<usize>) -> Result<(), CircuitFormError> {
    let mut pending = Vec::new();
    pending.push(roots);
    while let Some(mut sequence) = pending.pop() {
        while sequence.start < sequence.end {
            let index = sequence.start;
            match &forms[index] {
                Form::Atom { kind, span } => {
                    if !expression_atom(*kind, &source[span.clone()]) {
                        return Err(header_error(HeaderError::ExpectedExpression, span.clone()));
                    }
                    sequence.start += 1;
                }
                Form::List { span, end } => {
                    let children = expression_children(source, forms, index, *end, span.end - 1)?;
                    if *end < sequence.end {
                        pending.push(*end..sequence.end);
                    }
                    sequence = children;
                }
            }
        }
    }
    Ok(())
}

fn expression_children(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<Range<usize>, CircuitFormError> {
    let head = require_atom(
        forms,
        index + 1,
        end,
        closing,
        HeaderError::ExpectedReference,
        is_reference,
    )?;
    let first = index + 2;
    let builtin = recognize_expression_head(&source[head]);
    match builtin {
        Some(ExpressionHead::As) => {
            require_atom(
                forms,
                first,
                end,
                closing,
                HeaderError::ExpectedReference,
                is_reference,
            )?;
            let value = first + 1;
            let next = expression_end(forms, value, end, closing)?;
            require_end(forms, next, end)?;
            Ok(value..next)
        }
        Some(
            ExpressionHead::Bit
            | ExpressionHead::Slice
            | ExpressionHead::Field
            | ExpressionHead::Raw,
        ) => {
            let next = expression_end(forms, first, end, closing)?;
            let after = match builtin {
                Some(ExpressionHead::Bit) => natural_at(forms, next, end, closing)?,
                Some(ExpressionHead::Slice) => {
                    let length = natural_at(forms, next, end, closing)?;
                    let after_length = natural_at(forms, length, end, closing)?;
                    if after_length < end {
                        natural_at(forms, after_length, end, closing)?
                    } else {
                        after_length
                    }
                }
                Some(ExpressionHead::Field) => {
                    require_name(forms, next, end, closing)?;
                    next + 1
                }
                _ => next,
            };
            require_end(forms, after, end)?;
            Ok(first..next)
        }
        Some(ExpressionHead::Concat) => {
            expression_end(forms, first, end, closing)?;
            Ok(first..end)
        }
        None => Ok(first..end),
    }
}

fn natural_at(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<usize, CircuitFormError> {
    require_atom(
        forms,
        index,
        end,
        closing,
        HeaderError::ExpectedNatural,
        |kind| kind == AtomKind::Natural,
    )?;
    Ok(index + 1)
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
    let next = natural_at(forms, index + 2, clause_end, clause_close)?;
    require_end(forms, next, clause_end)?;
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum BodyHead {
    Def,
    Expand,
}

spec fn body_head_spelling(head: BodyHead) -> &'static str {
    match head {
        BodyHead::Def => "def",
        BodyHead::Expand => "expand",
    }
}

fn recognize_body_head(word: &str) -> (head: Option<BodyHead>)
    ensures
        forall|candidate: BodyHead| #[trigger] body_head_spelling(candidate)@ == word@
            <==> head == Some(candidate),
{
    if word == "def" {
        Some(BodyHead::Def)
    } else if word == "expand" {
        Some(BodyHead::Expand)
    } else {
        None
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExpressionHead {
    Bit,
    Slice,
    Concat,
    Field,
    As,
    Raw,
}

spec fn expression_head_spelling(head: ExpressionHead) -> &'static str {
    match head {
        ExpressionHead::Bit => "bit",
        ExpressionHead::Slice => "slice",
        ExpressionHead::Concat => "concat",
        ExpressionHead::Field => "field",
        ExpressionHead::As => "as",
        ExpressionHead::Raw => "raw",
    }
}

fn recognize_expression_head(word: &str) -> (head: Option<ExpressionHead>)
    ensures
        forall|candidate: ExpressionHead| #[trigger] expression_head_spelling(candidate)@ == word@
            <==> head == Some(candidate),
{
    let head = if word == "bit" { Some(ExpressionHead::Bit) }
        else if word == "slice" { Some(ExpressionHead::Slice) }
        else if word == "concat" { Some(ExpressionHead::Concat) }
        else if word == "field" { Some(ExpressionHead::Field) }
        else if word == "as" { Some(ExpressionHead::As) }
        else if word == "raw" { Some(ExpressionHead::Raw) }
        else { None };
    assert forall|candidate: ExpressionHead|
        #[trigger] expression_head_spelling(candidate)@ == word@
        <==> head == Some(candidate) by {
    };
    head
}

spec fn is_expression_atom(kind: AtomKind, word: &str) -> bool {
    kind is Name || kind is Binary || kind is Hexadecimal
        || (kind is Natural && (word@ == "0"@ || word@ == "1"@))
}

fn expression_atom(kind: AtomKind, word: &str) -> (accepted: bool)
    ensures accepted == is_expression_atom(kind, word),
{
    matches!(kind, AtomKind::Name | AtomKind::Binary | AtomKind::Hexadecimal)
        || (matches!(kind, AtomKind::Natural) && (word == "0" || word == "1"))
}

} // verus!
