//! NCG2M の補助関数本体を、署名から分かる型で検査する。

use alloc::vec::Vec;
use core::ops::Range;
use crate::syntax::{AtomKind, Form};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_span, sexpr_form_model};
use super::data_types::{
    BuiltinDataType, DataType, DataTypeAtom, DefnSignature, SignatureParameter, read_header_signature,
    read_type_value,
};
#[cfg(verus_only)]
use super::data_types::{data_type_matches, signature_matches_header};
use super::defn::{DefnHeaderError, is_name, parse_defn_input, read_type, span_of, tagged};
#[cfg(verus_only)]
use super::defn::{defn_body_site, defn_header_matches, plain_name, tagged_arguments, type_at, usable_forms};
use super::forms::{is_spelling, source_word, subtree_end};
#[cfg(verus_only)]
use super::forms::{spelling, subtree_limit};
use super::integers::{IntegerLiteralError, IntegerType, read_integer_literal};
#[cfg(verus_only)]
use super::integers::{IntegerValue, integer_literal_matches};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 式の構文や型の検査で見つかった違反。
#[derive(Debug, Eq, PartialEq)]
pub enum ExpressionTypeError<'a> {
    /// フォームの直下に必要な個数の引数がないか、余分な引数がある。
    Arguments {
        /// フォーム全体の UTF-8 半開バイト範囲。
        span: Range<usize>,
        /// 必要な引数の個数。
        expected_count: usize,
    },
    /// `defn` の署名注釈以外に現れた `fn` リテラル。その全体の範囲を保持する。
    FunctionLiteral(Range<usize>),
    /// `as-type` の型として読めない。
    Annotation(DefnHeaderError),
    /// 期待型と式の型で `List` の深さが異なる。
    ListDepthMismatch {
        /// 式の UTF-8 半開バイト範囲。
        span: Range<usize>,
        /// 期待型のリストの深さ。
        expected_depth: usize,
        /// 式の型のリストの深さ。
        actual_depth: usize,
    },
    /// 式の型が期待型と一致しない。
    Mismatch {
        /// 式の UTF-8 半開バイト範囲。
        span: Range<usize>,
        /// この位置で要求される型。
        expected: DataType<'a>,
        /// 式の型。
        actual: DataType<'a>,
    },
    /// 十進整数のリテラルが指定された型に収まらない。
    Integer {
        /// リテラルの UTF-8 半開バイト範囲。
        span: Range<usize>,
        /// 整数の読み取りで報告された違反。
        error: IntegerLiteralError,
    },
}

/// 現在の検査で式の型を確定できない理由。
#[derive(Debug, Eq, PartialEq)]
pub enum DeferredExpression {
    /// 後段が扱う式フォームまたはアトム。その式全体の範囲を保持する。
    Form(Range<usize>),
    /// 仮引数の環境で見つからなかった名前。その名前の範囲を保持する。
    Name(Range<usize>),
    /// 仮引数名と真偽値の綴りが重なった式。その名前の範囲を保持する。
    BooleanBinding(Range<usize>),
    /// 実行段階で型名を解決する必要がある式。その式の範囲を保持する。
    StageType(Range<usize>),
}

/// 本体の検査を続けられなかった理由。
#[derive(Debug, Eq, PartialEq)]
pub enum ExpressionCheckFailure<'a> {
    /// 対応している式で確定した構文または型の違反。
    Type(ExpressionTypeError<'a>),
    /// 後段の検査を待つ式または名前。
    Deferred(DeferredExpression),
}

/// 補助関数の署名または本体を検査できなかった最初の理由。
#[derive(Debug, Eq, PartialEq)]
pub enum DefnBodyError<'a> {
    /// 共通 S 式、補助関数の外形、署名のいずれかの違反。
    Header(DefnHeaderError),
    /// 本体で見つかった違反または保留の理由。
    Body(ExpressionCheckFailure<'a>),
}

#[derive(Clone, Copy)]
enum FormTag {
    Annotation,
    Conditional,
    FunctionLiteral,
}

#[derive(Clone, Copy)]
enum Expression {
    Bool,
    Integer { negative: bool },
    Parameter,
    Annotated { annotation: usize, value: usize },
    Conditional { condition: usize, yes: usize, no: usize },
}

#[derive(Clone, Copy)]
struct Request<'a> {
    at: usize,
    expected: DataType<'a>,
}

#[derive(Clone, Copy)]
enum CheckStep<'a> {
    Done,
    One(Request<'a>),
    Three(Request<'a>, Request<'a>, Request<'a>),
}

spec fn keyword(word: Seq<u8>) -> Option<FormTag> {
    if word == "as-type".spec_bytes() { Some(FormTag::Annotation) }
    else if word == "if".spec_bytes() { Some(FormTag::Conditional) }
    else if word == "fn".spec_bytes() { Some(FormTag::FunctionLiteral) }
    else { None }
}

fn read_keyword(word: &str) -> (tag: Option<FormTag>)
    ensures tag == keyword(word.spec_bytes()),
{
    if is_spelling(word, "as-type") { Some(FormTag::Annotation) }
    else if is_spelling(word, "if") { Some(FormTag::Conditional) }
    else if is_spelling(word, "fn") { Some(FormTag::FunctionLiteral) }
    else { None }
}

spec fn bool_word(word: Seq<u8>) -> bool {
    word == "true".spec_bytes() || word == "false".spec_bytes()
}

fn is_bool(word: &str) -> (boolean: bool)
    ensures boolean == bool_word(word.spec_bytes()),
{
    is_spelling(word, "true") || is_spelling(word, "false")
}

spec fn children3(forms: Seq<Form>, at: usize) -> Option<(usize, usize, usize)> {
    let end = subtree_limit(forms, at);
    if !(at + 2 < end <= forms.len()) {
        None
    } else {
        let first = (at + 2) as usize;
        let second = subtree_limit(forms, first);
        if !(first < second < end) {
            None
        } else {
            let third = subtree_limit(forms, second);
            if second < third < end && subtree_limit(forms, third) == end {
                Some((first, second, third))
            } else {
                None
            }
        }
    }
}

fn read_children3(forms: &[Form], at: usize) -> (children: Option<(usize, usize, usize)>)
    requires at < forms@.len(),
    ensures children == children3(forms@, at),
{
    let end = subtree_end(forms, at);
    if end <= at || end - at <= 2 || end > forms.len() { return None; }
    let first = at + 2;
    let second = subtree_end(forms, first);
    if second <= first || second >= end { return None; }
    let third = subtree_end(forms, second);
    if third <= second || third >= end || subtree_end(forms, third) != end {
        return None;
    }
    Some((first, second, third))
}

spec fn shape(source: &str, forms: Seq<Form>, at: usize) -> Result<Expression, ExpressionCheckFailure> {
    let span = form_span(forms[at as int]);
    let deferred = Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span)));
    match forms[at as int] {
        Form::Atom { kind: AtomKind::Natural, .. } => Ok(Expression::Integer { negative: false }),
        Form::Atom { kind: AtomKind::NegativeInteger, .. } => Ok(Expression::Integer { negative: true }),
        Form::Atom { kind: AtomKind::Name, .. } => {
            if bool_word(spelling(source, forms[at as int])) { Ok(Expression::Bool) }
            else { Ok(Expression::Parameter) }
        }
        Form::List { end, .. } if at + 1 < end <= forms.len() && plain_name(forms[at + 1]) =>
            match keyword(spelling(source, forms[at + 1])) {
                Some(FormTag::Annotation) => match tagged_arguments(source, forms, at, "as-type", true) {
                    Some((annotation, value)) => Ok(Expression::Annotated { annotation, value }),
                    None => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Arguments { span, expected_count: 2 })),
                },
                Some(FormTag::Conditional) => match children3(forms, at) {
                    Some((condition, yes, no)) => Ok(Expression::Conditional { condition, yes, no }),
                    None => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Arguments { span, expected_count: 3 })),
                },
                Some(FormTag::FunctionLiteral) =>
                    Err(ExpressionCheckFailure::Type(ExpressionTypeError::FunctionLiteral(span))),
                None => deferred,
            },
        _ => deferred,
    }
}

fn read_shape<'a>(source: &'a str, forms: &[Form], at: usize) -> (result: Result<Expression, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures result == shape(source, forms@, at),
{
    match &forms[at] {
        Form::Atom { kind: AtomKind::Natural, .. } => return Ok(Expression::Integer { negative: false }),
        Form::Atom { kind: AtomKind::NegativeInteger, .. } => return Ok(Expression::Integer { negative: true }),
        Form::Atom { kind: AtomKind::Name, .. } => {
            let word = source_word(source, forms, at);
            return if is_bool(word) { Ok(Expression::Bool) } else { Ok(Expression::Parameter) };
        }
        Form::List { end, .. } => {
            assert(at < *end <= forms@.len());
            let head = at + 1;
            if head < *end && is_name(&forms[head]) {
                match read_keyword(source_word(source, forms, head)) {
                    Some(FormTag::Annotation) => {
                        if let Some((annotation, value)) = tagged(source, forms, at, "as-type", true) {
                            return Ok(Expression::Annotated { annotation, value });
                        }
                        return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Arguments {
                            span: span_of(&forms[at]), expected_count: 2,
                        }));
                    }
                    Some(FormTag::Conditional) => {
                        if let Some((condition, yes, no)) = read_children3(forms, at) {
                            return Ok(Expression::Conditional { condition, yes, no });
                        }
                        return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Arguments {
                            span: span_of(&forms[at]), expected_count: 3,
                        }));
                    }
                    Some(FormTag::FunctionLiteral) => {
                        return Err(ExpressionCheckFailure::Type(ExpressionTypeError::FunctionLiteral(span_of(&forms[at]))));
                    }
                    None => {},
                }
            }
        }
        _ => {},
    }
    Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span_of(&forms[at]))))
}


spec fn parameter_type(parameters: Seq<SignatureParameter>, word: Seq<u8>, from: nat) -> Option<DataType>
    decreases parameters.len() - from,
{
    if from >= parameters.len() {
        None
    } else if parameters[from as int].name.spec_bytes() == word {
        Some(parameters[from as int].ty.ty)
    } else {
        parameter_type(parameters, word, from + 1)
    }
}

fn find_parameter<'a>(parameters: &[SignatureParameter<'a>], word: &str) -> (ty: Option<DataType<'a>>)
    ensures ty == parameter_type(parameters@, word.spec_bytes(), 0),
{
    let mut from = 0;
    while from < parameters.len()
        invariant
            from <= parameters@.len(),
            parameter_type(parameters@, word.spec_bytes(), 0) == parameter_type(parameters@, word.spec_bytes(), from as nat),
        decreases parameters@.len() - from,
    {
        reveal_with_fuel(parameter_type, 2);
        if is_spelling(parameters[from].name, word) {
            return Some(parameters[from].ty.ty);
        }
        from += 1;
    }
    None
}

fn builtin_equal(a: BuiltinDataType, b: BuiltinDataType) -> (equal: bool)
    ensures equal == (a == b),
{
    match (a, b) {
        (BuiltinDataType::Bool, BuiltinDataType::Bool)
        | (BuiltinDataType::Symbol, BuiltinDataType::Symbol)
        | (BuiltinDataType::Syntax, BuiltinDataType::Syntax)
        | (BuiltinDataType::Integer(IntegerType::Nat), BuiltinDataType::Integer(IntegerType::Nat))
        | (BuiltinDataType::Integer(IntegerType::Int), BuiltinDataType::Integer(IntegerType::Int)) => true,
        _ => false,
    }
}

spec fn depth_agrees<'a>(expected: usize, actual: usize, span: Range<usize>)
    -> Result<(), ExpressionCheckFailure<'a>>
{
    if expected == actual {
        Ok(())
    } else {
        Err(ExpressionCheckFailure::Type(ExpressionTypeError::ListDepthMismatch {
            span, expected_depth: expected, actual_depth: actual,
        }))
    }
}

fn check_depth<'a>(expected: usize, actual: usize, span: Range<usize>)
    -> (result: Result<(), ExpressionCheckFailure<'a>>)
    ensures result == depth_agrees(expected, actual, span),
{
    if expected == actual {
        Ok(())
    } else {
        Err(ExpressionCheckFailure::Type(ExpressionTypeError::ListDepthMismatch {
            span, expected_depth: expected, actual_depth: actual,
        }))
    }
}

spec fn types_agree<'a>(expected: DataType<'a>, actual: DataType<'a>, span: Range<usize>)
    -> Result<(), ExpressionCheckFailure<'a>>
{
    match depth_agrees(expected.list_depth, actual.list_depth, span) {
        Err(error) => Err(error),
        Ok(()) => match (expected.atom, actual.atom) {
            (DataTypeAtom::Builtin(a), DataTypeAtom::Builtin(b)) => {
                if a == b { Ok(()) }
                else { Err(ExpressionCheckFailure::Type(ExpressionTypeError::Mismatch { span, expected, actual })) }
            }
            _ => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span))),
        }
    }
}

fn conform<'a>(expected: DataType<'a>, actual: DataType<'a>, span: Range<usize>)
    -> (result: Result<(), ExpressionCheckFailure<'a>>)
    ensures result == types_agree(expected, actual, span),
{
    check_depth(expected.list_depth, actual.list_depth, span.start..span.end)?;
    match (expected.atom, actual.atom) {
        (DataTypeAtom::Builtin(a), DataTypeAtom::Builtin(b)) => {
            if builtin_equal(a, b) {
                Ok(())
            } else {
                Err(ExpressionCheckFailure::Type(ExpressionTypeError::Mismatch { span, expected, actual }))
            }
        }
        _ => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span))),
    }
}

spec fn scalar_type<'a>(builtin: BuiltinDataType) -> DataType<'a> {
    DataType { atom: DataTypeAtom::Builtin(builtin), list_depth: 0 }
}

fn scalar<'a>(builtin: BuiltinDataType) -> (ty: DataType<'a>)
    ensures ty == scalar_type(builtin),
{
    DataType { atom: DataTypeAtom::Builtin(builtin), list_depth: 0 }
}

spec fn literal_integer_type(negative: bool, expected: DataType) -> IntegerType {
    if negative || expected == scalar_type(BuiltinDataType::Integer(IntegerType::Int)) {
        IntegerType::Int
    } else {
        IntegerType::Nat
    }
}

spec fn literal_check<'a>(word: Seq<u8>, ty: IntegerType, span: Range<usize>) -> Result<CheckStep<'a>, ExpressionCheckFailure<'a>> {
    let result = choose|r: Result<IntegerValue, IntegerLiteralError>| integer_literal_matches(word, Some(ty), r);
    match result {
        Ok(_) => Ok(CheckStep::Done),
        Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Integer { span, error })),
    }
}

fn read_integer<'a>(word: &str, ty: IntegerType, span: Range<usize>) -> (result: Result<CheckStep<'a>, ExpressionCheckFailure<'a>>)
    ensures result == literal_check(word.spec_bytes(), ty, span),
{
    match read_integer_literal(word, Some(ty)) {
        Ok(_) => Ok(CheckStep::Done),
        Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Integer { span, error })),
    }
}

spec fn annotation_value<'a>(syntax: super::defn::DataTypeSyntax) -> Option<DataType<'a>> {
    let base = match syntax.name {
        super::defn::DataTypeName::Bool => Some(BuiltinDataType::Bool),
        super::defn::DataTypeName::Nat => Some(BuiltinDataType::Integer(IntegerType::Nat)),
        super::defn::DataTypeName::Int => Some(BuiltinDataType::Integer(IntegerType::Int)),
        super::defn::DataTypeName::Symbol => Some(BuiltinDataType::Symbol),
        super::defn::DataTypeName::Syntax => Some(BuiltinDataType::Syntax),
        super::defn::DataTypeName::Deferred => None,
    };
    match base {
        Some(base) => Some(DataType { atom: DataTypeAtom::Builtin(base), list_depth: syntax.list_depth }),
        None => None,
    }
}

spec fn step_model<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>, request: Request<'a>,
) -> Result<CheckStep<'a>, ExpressionCheckFailure<'a>> {
    let at = request.at;
    let span = form_span(forms[at as int]);
    let expected = request.expected;
    match shape(source, forms, at) {
        Err(error) => Err(error),
        Ok(Expression::Bool) => {
            if parameter_type(parameters, spelling(source, forms[at as int]), 0).is_some() {
                Err(ExpressionCheckFailure::Deferred(DeferredExpression::BooleanBinding(span)))
            } else {
                match types_agree(expected, scalar_type(BuiltinDataType::Bool), span) {
                    Ok(()) => Ok(CheckStep::Done),
                    Err(error) => Err(error),
                }
            }
        },
        Ok(Expression::Parameter) => match parameter_type(parameters, spelling(source, forms[at as int]), 0) {
            Some(actual) => match types_agree(expected, actual, span) {
                Ok(()) => Ok(CheckStep::Done),
                Err(error) => Err(error),
            },
            None => Err(ExpressionCheckFailure::Deferred(DeferredExpression::Name(span))),
        },
        Ok(Expression::Integer { negative }) => {
            let ty = literal_integer_type(negative, expected);
            match types_agree(expected, scalar_type(BuiltinDataType::Integer(ty)), span) {
                Ok(()) => literal_check(spelling(source, forms[at as int]), ty, span),
                Err(error) => Err(error),
            }
        }
        Ok(Expression::Annotated { annotation, value }) =>
            match type_at(source, forms, annotation, annotation, 0) {
                Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Annotation(error))),
                Ok(syntax) => match depth_agrees(expected.list_depth, syntax.list_depth, span) {
                    Err(error) => Err(error),
                    Ok(()) => match annotation_value(syntax) {
                        None => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(syntax.name_span))),
                        Some(actual) => match types_agree(expected, actual, span) {
                            Err(error) => Err(error),
                            Ok(()) => Ok(CheckStep::One(Request { at: value, expected: actual })),
                        },
                    },
                },
            },
        Ok(Expression::Conditional { condition, yes, no }) => Ok(CheckStep::Three(
            Request { at: condition, expected: scalar_type(BuiltinDataType::Bool) },
            Request { at: yes, expected },
            Request { at: no, expected },
        )),
    }
}

spec fn request_inside(forms: Seq<Form>, parent: usize, child: Request) -> bool {
    parent < child.at < forms.len()
        && child.at < subtree_limit(forms, child.at) <= subtree_limit(forms, parent)
}

spec fn step_children_fit(forms: Seq<Form>, at: usize, step: CheckStep) -> bool {
    match step {
        CheckStep::Done => true,
        CheckStep::One(child) => request_inside(forms, at, child),
        CheckStep::Three(cond, yes, no) => request_inside(forms, at, cond) && request_inside(forms, at, yes)
            && request_inside(forms, at, no)
            && subtree_limit(forms, cond.at) <= yes.at && subtree_limit(forms, yes.at) <= no.at,
    }
}

fn read_check_step<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], request: Request<'a>,
) -> (result: Result<CheckStep<'a>, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), request.at < forms@.len(),
    ensures
        result == step_model(source, forms@, parameters@, request),
        result matches Ok(step) ==> step_children_fit(forms@, request.at, step),
{
    let at = request.at;
    let expected = request.expected;
    let expression = read_shape(source, forms, at)?;
    match expression {
        Expression::Bool => {
            let word = source_word(source, forms, at);
            if find_parameter(parameters, word).is_some() {
                return Err(ExpressionCheckFailure::Deferred(DeferredExpression::BooleanBinding(span_of(&forms[at]))));
            }
            conform(expected, scalar(BuiltinDataType::Bool), span_of(&forms[at]))?;
            Ok(CheckStep::Done)
        }
        Expression::Parameter => {
            let word = source_word(source, forms, at);
            let Some(actual) = find_parameter(parameters, word) else {
                return Err(ExpressionCheckFailure::Deferred(DeferredExpression::Name(span_of(&forms[at]))));
            };
            conform(expected, actual, span_of(&forms[at]))?;
            Ok(CheckStep::Done)
        }
        Expression::Integer { negative } => {
            let ty = if negative || (expected.list_depth == 0
                && matches!(expected.atom, DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Int)))) {
                IntegerType::Int
            } else {
                IntegerType::Nat
            };
            conform(expected, scalar(BuiltinDataType::Integer(ty)), span_of(&forms[at]))?;
            read_integer(source_word(source, forms, at), ty, span_of(&forms[at]))
        }
        Expression::Annotated { annotation, value } => {
            let syntax = match read_type(source, forms, annotation) {
                Ok(syntax) => syntax,
                Err(error) => return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Annotation(error))),
            };
            let span = span_of(&forms[at]);
            check_depth(expected.list_depth, syntax.list_depth, span.start..span.end)?;
            let named = read_type_value(source, &syntax);
            if matches!(named.ty.atom, DataTypeAtom::Named(_)) {
                return Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(named.name_span)));
            }
            conform(expected, named.ty, span)?;
            Ok(CheckStep::One(Request { at: value, expected: named.ty }))
        }
        Expression::Conditional { condition, yes, no } => Ok(CheckStep::Three(
            Request { at: condition, expected: scalar(BuiltinDataType::Bool) },
            Request { at: yes, expected },
            Request { at: no, expected },
        )),
    }
}


enum BodyVerdict<'a> {
    Accepted,
    Rejected(ExpressionCheckFailure<'a>),
}

#[verifier::opaque]
spec fn expression_check<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>, request: Request<'a>,
) -> BodyVerdict<'a>
    decreases forms.len() - request.at,
{
    if request.at >= forms.len() {
        BodyVerdict::Rejected(ExpressionCheckFailure::Deferred(DeferredExpression::Form(0..0)))
    } else {
        match step_model(source, forms, parameters, request) {
            Err(error) => BodyVerdict::Rejected(error),
            Ok(step) if !step_children_fit(forms, request.at, step) =>
                BodyVerdict::Rejected(ExpressionCheckFailure::Deferred(DeferredExpression::Form(form_span(forms[request.at as int])))),
            Ok(CheckStep::Done) => BodyVerdict::Accepted,
            Ok(CheckStep::One(child)) => expression_check(source, forms, parameters, child),
            Ok(CheckStep::Three(condition, yes, no)) => {
                match expression_check(source, forms, parameters, condition) {
                    BodyVerdict::Rejected(error) => BodyVerdict::Rejected(error),
                    BodyVerdict::Accepted => match expression_check(source, forms, parameters, yes) {
                        BodyVerdict::Rejected(error) => BodyVerdict::Rejected(error),
                        BodyVerdict::Accepted => expression_check(source, forms, parameters, no),
                    },
                }
            }
        }
    }
}

#[verifier::opaque]
spec fn pending_check<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>, pending: Seq<Request<'a>>,
) -> BodyVerdict<'a>
    decreases pending.len(),
{
    if pending.len() == 0 {
        BodyVerdict::Accepted
    } else {
        match expression_check(source, forms, parameters, pending.last()) {
            BodyVerdict::Rejected(error) => BodyVerdict::Rejected(error),
            BodyVerdict::Accepted => pending_check(source, forms, parameters, pending.drop_last()),
        }
    }
}

spec fn next_requests<'a>(pending: Seq<Request<'a>>, step: CheckStep<'a>) -> Seq<Request<'a>> {
    match step {
        CheckStep::Done => pending,
        CheckStep::One(child) => pending.push(child),
        CheckStep::Three(condition, yes, no) => pending.push(no).push(yes).push(condition),
    }
}

proof fn pending_push<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<SignatureParameter<'a>>, pending: Seq<Request<'a>>, tail: Request<'a>,
)
    ensures pending_check(source, forms, env, pending.push(tail)) == match expression_check(source, forms, env, tail) {
        BodyVerdict::Rejected(error) => BodyVerdict::Rejected(error),
        BodyVerdict::Accepted => pending_check(source, forms, env, pending),
    },
{
    reveal(pending_check);
    assert(pending.push(tail).drop_last() =~= pending);
}

proof fn pending_singleton<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<SignatureParameter<'a>>, request: Request<'a>,
)
    ensures pending_check(source, forms, env, Seq::empty().push(request)) == expression_check(source, forms, env, request),
{
    reveal(pending_check);
    let empty = Seq::<Request<'a>>::empty();
    assert(pending_check(source, forms, env, empty) == BodyVerdict::Accepted);
    pending_push(source, forms, env, empty, request);

}

proof fn popped_error<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<SignatureParameter<'a>>, pending: Seq<Request<'a>>,
    request: Request<'a>, error: ExpressionCheckFailure<'a>,
)
    requires request.at < forms.len(), step_model(source, forms, env, request) == Err(error),
    ensures pending_check(source, forms, env, pending.push(request)) == BodyVerdict::Rejected(error),
{
    reveal(expression_check);
    pending_push(source, forms, env, pending, request);
}

proof fn popped_step<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<SignatureParameter<'a>>, pending: Seq<Request<'a>>,
    request: Request<'a>, step: CheckStep<'a>,
)
    requires request.at < forms.len(), step_children_fit(forms, request.at, step),
        step_model(source, forms, env, request) == Ok(step),
    ensures pending_check(source, forms, env, pending.push(request))
        == pending_check(source, forms, env, next_requests(pending, step)),
{
    reveal(expression_check);
    pending_push(source, forms, env, pending, request);
    match step {
        CheckStep::Done => {},
        CheckStep::One(child) => {
            pending_push(source, forms, env, pending, child);
        }
        CheckStep::Three(condition, yes, no) => {
            pending_push(source, forms, env, pending, no);
            pending_push(source, forms, env, pending.push(no), yes);
            pending_push(source, forms, env, pending.push(no).push(yes), condition);
        }
    }
}

spec fn pending_first(forms: Seq<Form>, pending: Seq<Request>) -> nat {
    if pending.len() == 0 { forms.len() } else { pending.last().at as nat }
}

spec fn requests_ready(forms: Seq<Form>, pending: Seq<Request>) -> bool {
    &&& forall|i: int| 0 <= i < pending.len() ==> {
        let request = #[trigger] pending[i];
        request.at < forms.len() && request.at < subtree_limit(forms, request.at) <= forms.len()
    }
    &&& forall|i: int, j: int| 0 <= i < j < pending.len() ==>
        subtree_limit(forms, (#[trigger] pending[j]).at) <= (#[trigger] pending[i]).at
}

proof fn append_ready<'a>(forms: Seq<Form>, pending: Seq<Request<'a>>, child: Request<'a>)
    requires requests_ready(forms, pending), child.at < subtree_limit(forms, child.at) <= forms.len(),
        forall|i: int| 0 <= i < pending.len() ==> subtree_limit(forms, child.at) <= (#[trigger] pending[i]).at,
    ensures requests_ready(forms, pending.push(child)),
{
    let rows = pending.push(child);
    assert forall|i: int, j: int| 0 <= i < j < rows.len() implies
        subtree_limit(forms, (#[trigger] rows[j]).at) <= (#[trigger] rows[i]).at by {
        if j < pending.len() {
            assert(rows[j] == pending[j]);
        }
    };
}

proof fn step_advances<'a>(forms: Seq<Form>, pending: Seq<Request<'a>>, parent: Request<'a>, step: CheckStep<'a>)
    requires requests_ready(forms, pending.push(parent)), step_children_fit(forms, parent.at, step),
    ensures
        requests_ready(forms, next_requests(pending, step)),
        parent.at < pending_first(forms, next_requests(pending, step)),
{
    let old = pending.push(parent);
    assert forall|i: int| 0 <= i < pending.len() implies
        subtree_limit(forms, parent.at) <= (#[trigger] pending[i]).at by {
        assert(old[i] == pending[i] && old[pending.len() as int] == parent);
    };
    assert(requests_ready(forms, pending)) by {
        assert forall|i: int| 0 <= i < pending.len() implies {
            let child = #[trigger] pending[i];
            child.at < forms.len() && child.at < subtree_limit(forms, child.at) <= forms.len()
        } by {
            assert(pending[i] == old[i]);
        };
        assert forall|i: int, j: int| 0 <= i < j < pending.len() implies
            subtree_limit(forms, (#[trigger] pending[j]).at) <= (#[trigger] pending[i]).at by {
            assert(pending[i] == old[i] && pending[j] == old[j]);
        };
    };
    match step {
        CheckStep::Done => {},
        CheckStep::One(child) => {
            append_ready(forms, pending, child);
        }
        CheckStep::Three(condition, yes, no) => {
            append_ready(forms, pending, no);
            let with_no = pending.push(no);
            assert forall|i: int| 0 <= i < with_no.len() implies
                subtree_limit(forms, yes.at) <= (#[trigger] with_no[i]).at by {
                if i < pending.len() { assert(with_no[i] == pending[i]); }
            };
            append_ready(forms, with_no, yes);
            let with_yes = with_no.push(yes);
            assert forall|i: int| 0 <= i < with_yes.len() implies
                subtree_limit(forms, condition.at) <= (#[trigger] with_yes[i]).at by {
                if i < with_no.len() { assert(with_yes[i] == with_no[i]); }
            };
            append_ready(forms, with_yes, condition);
        }
    }
}

// 検査する式の添字を前進させる。右の分岐から積むことで、条件、左、右の順に調べる。
fn check_body<'a>(
    source: &'a str, forms: &[Form], signature: &DefnSignature<'a>, body: usize,
) -> (result: BodyVerdict<'a>)
    requires usable_forms(source, forms@), body < forms@.len(),
    ensures result == expression_check(source, forms@, signature.parameters@,
        Request { at: body, expected: signature.result_type.ty }),
{
    let start = Request { at: body, expected: signature.result_type.ty };
    let _size = forms.len();
    let _end = subtree_end(forms, body);
    let mut pending = Vec::new();
    pending.push(start);
    let ghost env = signature.parameters@;
    proof {
        assert(complete_list_indices(forms@));
        let root = forms@[body as int];
        if let Form::List { end, .. } = root {
            assert(body < end <= forms@.len());
        }
        assert(body < _end <= _size);
        assert(pending@ =~= Seq::empty().push(start));
        assert(requests_ready(forms@, Seq::empty()));
        append_ready(forms@, Seq::empty(), start);
        pending_singleton(source, forms@, env, start);
    }
    while pending.len() != 0
        invariant
            usable_forms(source, forms@),
            env == signature.parameters@,
            start == (Request { at: body, expected: signature.result_type.ty }),
            requests_ready(forms@, pending@),
            pending_check(source, forms@, env, pending@) == expression_check(source, forms@, env, start),
        decreases forms@.len() - pending_first(forms@, pending@),
    {
        let ghost old = pending@;
        let Some(request) = pending.pop() else { unreachable!() };
        assert(old =~= pending@.push(request));
        let step = match read_check_step(source, forms, &signature.parameters, request) {
            Err(error) => {
                proof { popped_error(source, forms@, env, pending@, request, error); }
                return BodyVerdict::Rejected(error);
            }
            Ok(step) => step,
        };
        proof {
            popped_step(source, forms@, env, pending@, request, step);
            step_advances(forms@, pending@, request, step);
        }
        match step {
            CheckStep::Done => {},
            CheckStep::One(child) => pending.push(child),
            CheckStep::Three(condition, yes, no) => {
                pending.push(no);
                pending.push(yes);
                pending.push(condition);
            }
        }
    }
    proof { reveal(pending_check); }
    BodyVerdict::Accepted
}

spec fn body_witness<'a>(
    source: &'a str, result: Result<DefnSignature<'a>, DefnBodyError<'a>>,
    header: super::defn::DefnHeader, signature: DefnSignature<'a>, forms: Seq<Form>, body: usize,
) -> bool {
    &&& defn_header_matches(source, Ok(header))
    &&& signature_matches_header(source, header, signature)
    &&& sexpr_form_model(source) == Some(forms)
    &&& defn_body_site(source, forms, 0, body)
    &&& match result {
        Ok(checked) => checked == signature && expression_check(source, forms, signature.parameters@,
            Request { at: body, expected: signature.result_type.ty }) == BodyVerdict::Accepted,
        Err(DefnBodyError::Body(error)) => expression_check(source, forms, signature.parameters@,
            Request { at: body, expected: signature.result_type.ty }) == BodyVerdict::Rejected(error),
        Err(DefnBodyError::Header(_)) => false,
    }
}

/// 署名と本体検査の結果が、元の補助関数宣言と式の型規則に対応することを表す。
pub closed spec fn defn_body_matches(
    source: &str, result: Result<DefnSignature, DefnBodyError>,
) -> bool {
    match result {
        Err(DefnBodyError::Header(error)) => defn_header_matches(source, Err(error)),
        _ => exists|header: super::defn::DefnHeader, signature: DefnSignature, forms: Seq<Form>, body: usize|
            #[trigger] body_witness(source, result, header, signature, forms, body),
    }
}

/// 本体の検査を通った署名が、元ソースの補助関数ヘッダーに対応することを示す。
pub proof fn checked_body_signature_origin(source: &str, signature: DefnSignature) -> (header: super::defn::DefnHeader)
    requires defn_body_matches(source, Ok(signature)),
    ensures defn_header_matches(source, Ok(header)), signature_matches_header(source, header, signature),
{
    let (header, projected, forms, body) =
        choose|header: super::defn::DefnHeader, projected: DefnSignature, forms: Seq<Form>, body: usize|
            #[trigger] body_witness(source, Ok(signature), header, projected, forms, body);
    assert(signature == projected);
    header
}

/// 補助関数の本体を、仮引数の型環境と署名の戻り型で検査する。
///
/// 真偽値、十進整数、仮引数の参照、`as-type`、`if` を扱う。`if` は条件、左の分岐、右の分岐の
/// 順に検査する。本体が検査を通れば、元ソースの範囲を持つ署名を返す。
///
/// # Errors
///
/// 検査は最初の診断で止める。対応する式の型・範囲の違反を診断し、後段で扱うフォーム、
/// 仮引数以外の名前、段階固有の型、真偽値と仮引数名の綴りが重なる箇所は保留として返す。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::ncg2m::expression_types::{DefnBodyError, check_defn_body};
///
/// let source = "(defn choose (as-type (Fn (Bool Int) Int) (fn (flag n) (if flag n 0))))";
/// let signature = check_defn_body(source)?;
/// assert_eq!(&source[signature.body_span], "(if flag n 0)");
/// # Ok::<(), DefnBodyError<'_>>(())
/// ```
pub fn check_defn_body(source: &str) -> (result: Result<DefnSignature<'_>, DefnBodyError<'_>>)
    ensures defn_body_matches(source, result),
{
    let (forms, header, body) = match parse_defn_input(source) {
        Ok(input) => input,
        Err(error) => return Err(DefnBodyError::Header(error)),
    };
    let signature = read_header_signature(source, &header);
    let input = forms.as_slice();
    let checked = check_body(source, input, &signature, body);
    assert(input@ == forms@);
    assert(checked == expression_check(source, input@, signature.parameters@, Request {
        at: body, expected: signature.result_type.ty,
    }));
    match checked {
        BodyVerdict::Accepted => {
            assert(expression_check(source, forms@, signature.parameters@, Request {
                at: body, expected: signature.result_type.ty,
            }) == BodyVerdict::Accepted);
            assert(body_witness(source, Ok(signature), header, signature, forms@, body));
            Ok(signature)
        }
        BodyVerdict::Rejected(error) => {
            assert(body_witness(source, Err(DefnBodyError::Body(error)), header, signature, forms@, body));
            Err(DefnBodyError::Body(error))
        }
    }
}

}
