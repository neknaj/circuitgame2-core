//! NCG2M の補助関数本体を、署名から分かる型で検査する。

use alloc::vec::Vec;
use core::ops::Range;
use crate::syntax::{AtomKind, Form};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_span, form_spans_valid, nested_list_indices, sexpr_form_model};
use super::data_types::{
    BuiltinDataType, DataType, DataTypeAtom, DefnSignature, SignatureParameter, read_header_signature,
    read_type_value,
};
#[cfg(verus_only)]
use super::data_types::{data_type_matches, same_defn_signature, signature_matches_header,
    signature_parameter_types_agree, signature_projection_agrees, signature_result_types_agree};
use super::defn::{DefnHeaderError, is_name, parse_defn_input, read_type, span_of, tagged};
#[cfg(verus_only)]
use super::defn::{defn_body_site, defn_body_sites_agree, defn_header_matches, indexed_body_site, plain_name, standalone_header_is_only_root, tagged_arguments, type_at, usable_forms};
use super::file::{MetaItem, MetaItemKind, indexed_meta_body};
#[cfg(verus_only)]
use super::file::{indexed_standalone_header, meta_ast_body_origin, meta_ast_matches, meta_ast_source,
    meta_ast_unique_start, meta_binding_spans_valid, meta_defn_signature_spans, meta_file_matches};
use super::forms::{is_spelling, source_word, subtree_end};
pub use super::let_syntax::LetSyntaxError;
use super::let_syntax::read_let_structure;
#[cfg(verus_only)]
use super::let_syntax::{LocalBinding, let_structure, valid_bindings};
#[cfg(verus_only)]
use super::forms::{spelling, subtree_limit};
use super::integers::{IntegerLiteralError, IntegerType, read_integer_literal};
#[cfg(verus_only)]
use super::integers::{IntegerValue, integer_literal_matches};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

mod macro_body;
pub use macro_body::{CheckedMacroBody, CheckedMacroElement, MacroBodyError, MacroInsertion};
#[cfg(verus_only)]
pub use macro_body::{
    defmacro_body_check, macro_element_origin, macro_insertion_is_typed, macro_insertion_origin,
    macro_parameter_environment,
};
mod fold;
pub(crate) mod named_call;
pub use named_call::DefnBodyCallError;
#[cfg(verus_only)]
pub use named_call::{
    expression_slot, expression_slot_at_root, scalar_call_syntax_at, scalar_evaluator_syntax,
    scalar_syntax_call_arguments, scalar_syntax_form_kind, scalar_syntax_if_children, scalar_syntax_matches_call_arguments,
    scalar_syntax_atom_from_kind, scalar_syntax_if_from_children, scalar_syntax_call_from_arguments,
};
mod local_scopes;
mod typing;
pub use fold::FoldSyntaxError;
use fold::{FoldHeader, FoldKind, read_fold_header};
#[cfg(verus_only)]
use fold::{fold_header, fold_positions};
use local_scopes::{LocalScopes, Scope};
use typing::check_typed_body;
#[cfg(verus_only)]
use typing::typed_body;

#[cfg(verus_only)]
pub use typing::scalar::{local_scalar_fragment, local_scalar_site_is_typed};
#[cfg(verus_only)]
pub use typing::scalar::scalar_atom_at;
#[cfg(verus_only)]
pub(super) use typing::scalar::{scalar_atom_type_origin, scalar_conditional_child_types};

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
    /// スカラー型を要求する位置にリスト式が現れた。式全体の範囲を保持する。
    ListInScalarContext(Range<usize>),
    /// 空のリストの要素型を決めるために型注釈が必要な範囲。
    ListNeedsAnnotation(Range<usize>),
    /// 局所束縛の外形か束縛名に違反がある。
    Let(LetSyntaxError),
    /// 反復式の束縛名に違反がある。
    Fold(FoldSyntaxError),
    /// `fold-list` の入力にリスト型を要求する範囲。
    FoldListInput(Range<usize>),
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
    /// 組み込みの加減乗は `Nat` または `Int` を返す。演算式全体の範囲を保持する。
    ArithmeticResult(Range<usize>),
}

/// 現在の検査で式の型を確定できない理由。
#[derive(Debug, Eq, PartialEq)]
pub enum DeferredExpression {
    /// 後段が扱う式フォームまたはアトム。その式全体の範囲を保持する。
    Form(Range<usize>),
    /// 現在の型環境で見つからなかった名前。その名前の範囲を保持する。
    Name(Range<usize>),
    /// 束縛名と真偽値の綴りが重なった式。その名前の範囲を保持する。
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
    List,
    Let,
    Fold(FoldKind),
}

#[derive(Clone, Copy)]
enum Expression {
    Bool,
    Integer { negative: bool },
    Parameter,
    Annotated { annotation: usize, value: usize },
    Conditional { condition: usize, yes: usize, no: usize },
    List,
    Let,
    Fold(FoldHeader),
}

#[derive(Clone, Copy)]
struct TypeShape {
    builtin: Option<BuiltinDataType>,
    list_depth: usize,
}

#[derive(Clone, Copy)]
struct LocalType<'a> {
    name: &'a str,
    ty: TypeShape,
}

#[cfg(verus_only)]
type TypeBinding = (Seq<u8>, TypeShape);

#[derive(Clone, Copy)]
struct Request {
    at: usize,
    expected: TypeShape,
    list: Option<usize>,
}

#[derive(Clone, Copy)]
enum CheckStep {
    Done,
    One(Request),
    Three(Request, Request, Request),
}

spec fn type_shape(ty: DataType) -> TypeShape {
    TypeShape {
        builtin: match ty.atom {
            DataTypeAtom::Builtin(base) => Some(base),
            DataTypeAtom::Named(_) => None,
        },
        list_depth: ty.list_depth,
    }
}

fn shape_of_type(ty: DataType) -> (shape: TypeShape)
    ensures shape == type_shape(ty),
{
    let builtin = match ty.atom {
        DataTypeAtom::Builtin(base) => Some(base),
        DataTypeAtom::Named(_) => None,
    };
    TypeShape { builtin, list_depth: ty.list_depth }
}

// 本体検査では、段階固有型の解決を保留する。環境は仮引数の綴り、共通型、リストの深さを使う。
spec fn environment_view(parameters: Seq<SignatureParameter>) -> Seq<TypeBinding> {
    parameters.map_values(|parameter: SignatureParameter| (parameter.name.spec_bytes(), type_shape(parameter.ty.ty)))
}

spec fn keyword(word: Seq<u8>) -> Option<FormTag> {
    if word == "as-type".spec_bytes() { Some(FormTag::Annotation) }
    else if word == "if".spec_bytes() { Some(FormTag::Conditional) }
    else if word == "fn".spec_bytes() { Some(FormTag::FunctionLiteral) }
    else if word == "list".spec_bytes() { Some(FormTag::List) }
    else if word == "let".spec_bytes() { Some(FormTag::Let) }
    else if word == "fold-nat".spec_bytes() { Some(FormTag::Fold(FoldKind::Nat)) }
    else if word == "fold-list".spec_bytes() { Some(FormTag::Fold(FoldKind::List)) }
    else { None }
}

fn read_keyword(word: &str) -> (tag: Option<FormTag>)
    ensures tag == keyword(word.spec_bytes()),
{
    if is_spelling(word, "as-type") { Some(FormTag::Annotation) }
    else if is_spelling(word, "if") { Some(FormTag::Conditional) }
    else if is_spelling(word, "fn") { Some(FormTag::FunctionLiteral) }
    else if is_spelling(word, "list") { Some(FormTag::List) }
    else if is_spelling(word, "let") { Some(FormTag::Let) }
    else if is_spelling(word, "fold-nat") { Some(FormTag::Fold(FoldKind::Nat)) }
    else if is_spelling(word, "fold-list") { Some(FormTag::Fold(FoldKind::List)) }
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

/// 元の構文木にある `if` の条件と二つの分岐の位置を表す。
pub closed spec fn conditional_positions(
    source: &str, forms: Seq<Form>, at: usize,
) -> Option<(usize, usize, usize)> {
    if at < forms.len() {
        match forms[at as int] {
            Form::List { end, .. } if at + 1 < end <= forms.len() && plain_name(forms[at + 1])
                && spelling(source, forms[at + 1]) == "if".spec_bytes() =>
                    children3(forms, at),
            _ => None,
        }
    } else {
        None
    }
}

pub(super) proof fn conditional_position_is_list(source: &str, forms: Seq<Form>, at: usize)
    requires conditional_positions(source, forms, at).is_some(),
    ensures at < forms.len() && forms[at as int] is List,
{}

// 型検査と同じ兄弟の境界から、条件と二つの分岐の位置を得る。
pub(super) fn read_conditional_positions(
    source: &str, forms: &[Form], at: usize,
) -> (children: Option<(usize, usize, usize)>)
    requires form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures children == conditional_positions(source, forms@, at),
        children matches Some((condition, yes, no)) ==> at < condition < yes < no < forms@.len(),
{
    let Some(Form::List { end, .. }) = forms.get(at) else { return None; };
    if *end <= at || *end - at <= 1 || *end > forms.len() { return None; }
    let head = at + 1;
    if !is_name(&forms[head]) || !is_spelling(source_word(source, forms, head), "if") {
        return None;
    }
    read_children3(forms, at)
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
                Some(FormTag::List) => Ok(Expression::List),
                Some(FormTag::Let) => Ok(Expression::Let),
                Some(FormTag::Fold(kind)) => match fold_header(source, forms, at, kind) {
                    Ok(header) => Ok(Expression::Fold(header)),
                    Err(error) => Err(error),
                },
                None => deferred,
            },
        _ => deferred,
    }
}

fn read_shape<'a>(source: &'a str, forms: &[Form], at: usize) -> (result: Result<Expression, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures result == shape(source, forms@, at),
        result matches Ok(Expression::Fold(header)) ==> fold_positions(forms@, at, header),
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
                    Some(FormTag::List) => return Ok(Expression::List),
                    Some(FormTag::Let) => return Ok(Expression::Let),
                    Some(FormTag::Fold(kind)) => {
                        let header = read_fold_header(source, forms, at, kind)?;
                        return Ok(Expression::Fold(header));
                    }
                    None => {},
                }
            }
        }
        _ => {},
    }
    Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span_of(&forms[at]))))
}


spec fn parameter_type(parameters: Seq<TypeBinding>, word: Seq<u8>, from: nat) -> Option<TypeShape>
    decreases parameters.len() - from,
{
    if from >= parameters.len() {
        None
    } else if parameters[from as int].0 == word {
        Some(parameters[from as int].1)
    } else {
        parameter_type(parameters, word, from + 1)
    }
}

fn find_parameter(parameters: &[SignatureParameter], word: &str) -> (ty: Option<TypeShape>)
    ensures ty == parameter_type(environment_view(parameters@), word.spec_bytes(), 0),
{
    let mut from = 0;
    while from < parameters.len()
        invariant
            from <= parameters@.len(),
            parameter_type(environment_view(parameters@), word.spec_bytes(), 0) == parameter_type(environment_view(parameters@), word.spec_bytes(), from as nat),
        decreases parameters@.len() - from,
    {
        reveal_with_fuel(parameter_type, 2);
        if is_spelling(parameters[from].name, word) {
            return Some(shape_of_type(parameters[from].ty.ty));
        }
        from += 1;
    }
    None
}

spec fn lexical_view(parameters: Seq<SignatureParameter>, locals: &LocalScopes, scope: Scope) -> Seq<TypeBinding> {
    locals.local_types(scope) + environment_view(parameters)
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

spec fn builtin_type<'a>(builtin: BuiltinDataType, list_depth: usize) -> DataType<'a> {
    DataType { atom: DataTypeAtom::Builtin(builtin), list_depth }
}

fn materialize_builtin<'a>(builtin: BuiltinDataType, list_depth: usize) -> (ty: DataType<'a>)
    ensures ty == builtin_type(builtin, list_depth),
{
    DataType { atom: DataTypeAtom::Builtin(builtin), list_depth }
}

spec fn types_agree<'a>(expected: TypeShape, actual: TypeShape, span: Range<usize>)
    -> Result<(), ExpressionCheckFailure<'a>>
{
    match depth_agrees(expected.list_depth, actual.list_depth, span) {
        Err(error) => Err(error),
        Ok(()) => match (expected.builtin, actual.builtin) {
            (Some(a), Some(b)) => {
                if a == b { Ok(()) }
                else { Err(ExpressionCheckFailure::Type(ExpressionTypeError::Mismatch {
                    span, expected: builtin_type(a, expected.list_depth), actual: builtin_type(b, actual.list_depth),
                })) }
            }
            _ => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span))),
        }
    }
}

fn conform<'a>(expected: TypeShape, actual: TypeShape, span: Range<usize>)
    -> (result: Result<(), ExpressionCheckFailure<'a>>)
    ensures result == types_agree(expected, actual, span),
{
    check_depth(expected.list_depth, actual.list_depth, span.start..span.end)?;
    match (expected.builtin, actual.builtin) {
        (Some(a), Some(b)) => {
            if builtin_equal(a, b) {
                Ok(())
            } else {
                Err(ExpressionCheckFailure::Type(ExpressionTypeError::Mismatch {
                    span,
                    expected: materialize_builtin(a, expected.list_depth),
                    actual: materialize_builtin(b, actual.list_depth),
                }))
            }
        }
        _ => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span))),
    }
}

spec fn scalar_type(builtin: BuiltinDataType) -> TypeShape {
    TypeShape { builtin: Some(builtin), list_depth: 0 }
}

fn scalar(builtin: BuiltinDataType) -> (ty: TypeShape)
    ensures ty == scalar_type(builtin),
{
    TypeShape { builtin: Some(builtin), list_depth: 0 }
}

spec fn literal_integer_type(negative: bool, expected: TypeShape) -> IntegerType {
    if negative || expected == scalar_type(BuiltinDataType::Integer(IntegerType::Int)) {
        IntegerType::Int
    } else {
        IntegerType::Nat
    }
}

spec fn literal_check<'a>(word: Seq<u8>, ty: IntegerType, span: Range<usize>) -> Result<CheckStep, ExpressionCheckFailure<'a>> {
    let result = choose|r: Result<IntegerValue, IntegerLiteralError>| integer_literal_matches(word, Some(ty), r);
    match result {
        Ok(_) => Ok(CheckStep::Done),
        Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Integer { span, error })),
    }
}

fn read_integer<'a>(word: &str, ty: IntegerType, span: Range<usize>) -> (result: Result<CheckStep, ExpressionCheckFailure<'a>>)
    ensures result == literal_check(word.spec_bytes(), ty, span),
{
    match read_integer_literal(word, Some(ty)) {
        Ok(_) => Ok(CheckStep::Done),
        Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Integer { span, error })),
    }
}

spec fn annotation_value(syntax: super::defn::DataTypeSyntax) -> Option<TypeShape> {
    let base = match syntax.name {
        super::defn::DataTypeName::Bool => Some(BuiltinDataType::Bool),
        super::defn::DataTypeName::Nat => Some(BuiltinDataType::Integer(IntegerType::Nat)),
        super::defn::DataTypeName::Int => Some(BuiltinDataType::Integer(IntegerType::Int)),
        super::defn::DataTypeName::Symbol => Some(BuiltinDataType::Symbol),
        super::defn::DataTypeName::Syntax => Some(BuiltinDataType::Syntax),
        super::defn::DataTypeName::Deferred => None,
    };
    match base {
        Some(base) => Some(TypeShape { builtin: Some(base), list_depth: syntax.list_depth }),
        None => None,
    }
}

spec fn list_step<'a>(at: usize, end: usize, expected: TypeShape, span: Range<usize>)
    -> Result<CheckStep, ExpressionCheckFailure<'a>>
{
    if expected.list_depth == 0 {
        Err(ExpressionCheckFailure::Type(ExpressionTypeError::ListInScalarContext(span)))
    } else if at + 2 < end {
        Ok(CheckStep::One(Request {
            at: (at + 2) as usize,
            expected: TypeShape { builtin: expected.builtin, list_depth: (expected.list_depth - 1) as usize },
            list: Some(at),
        }))
    } else if expected.builtin.is_none() {
        Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span)))
    } else {
        Ok(CheckStep::Done)
    }
}

fn read_list_step<'a>(at: usize, end: usize, expected: TypeShape, span: Range<usize>)
    -> (result: Result<CheckStep, ExpressionCheckFailure<'a>>)
    requires at + 1 < end,
    ensures result == list_step(at, end, expected, span),
{
    if expected.list_depth == 0 {
        Err(ExpressionCheckFailure::Type(ExpressionTypeError::ListInScalarContext(span)))
    } else if at + 2 < end {
        Ok(CheckStep::One(Request {
            at: at + 2,
            expected: TypeShape { builtin: expected.builtin, list_depth: expected.list_depth - 1 },
            list: Some(at),
        }))
    } else if expected.builtin.is_none() {
        Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span)))
    } else {
        Ok(CheckStep::Done)
    }
}

spec fn step_model<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<TypeBinding>, request: Request,
) -> Result<CheckStep, ExpressionCheckFailure<'a>> {
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
        Ok(Expression::List) => list_step(at, subtree_limit(forms, at), expected, span),
        Ok(Expression::Let) => match let_structure(source, forms, at) {
            Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Let(error))),
            Ok(_) => Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span))),
        },
        Ok(Expression::Fold(_)) => Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span))),
        Ok(Expression::Annotated { annotation, value }) =>
            match type_at(source, forms, annotation, annotation, 0) {
                Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Annotation(error))),
                Ok(syntax) => match depth_agrees(expected.list_depth, syntax.list_depth, span) {
                    Err(error) => Err(error),
                    Ok(()) => match annotation_value(syntax) {
                        None => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(syntax.name_span))),
                        Some(actual) => match types_agree(expected, actual, span) {
                            Err(error) => Err(error),
                            Ok(()) => Ok(CheckStep::One(Request { at: value, expected: actual, list: None })),
                        },
                    },
                },
            },
        Ok(Expression::Conditional { condition, yes, no }) => Ok(CheckStep::Three(
            Request { at: condition, expected: scalar_type(BuiltinDataType::Bool), list: None },
            Request { at: yes, expected, list: None },
            Request { at: no, expected, list: None },
        )),
    }
}

spec fn request_limit(forms: Seq<Form>, request: Request) -> usize {
    match request.list {
        Some(list) => subtree_limit(forms, list),
        None => subtree_limit(forms, request.at),
    }
}

spec fn request_ready(forms: Seq<Form>, request: Request) -> bool {
    &&& request.at < forms.len()
    &&& request.at < subtree_limit(forms, request.at) <= request_limit(forms, request) <= forms.len()
    &&& request.list matches Some(list) ==> list < request.at && forms[list as int] is List
}

spec fn request_inside(forms: Seq<Form>, parent: usize, child: Request) -> bool {
    parent < child.at && request_ready(forms, child)
        && request_limit(forms, child) <= subtree_limit(forms, parent)
}

spec fn remaining_elements(forms: Seq<Form>, request: Request) -> Option<Request> {
    match request.list {
        Some(list) => {
            let next = subtree_limit(forms, request.at);
            if request.at < next < subtree_limit(forms, list) <= forms.len() {
                Some(Request { at: next, ..request })
            } else {
                None
            }
        }
        None => None,
    }
}

fn read_remaining_elements(forms: &[Form], request: Request) -> (result: Option<Request>)
    requires request_ready(forms@, request), complete_list_indices(forms@), nested_list_indices(forms@),
    ensures
        result == remaining_elements(forms@, request),
        result matches Some(next) ==> request_ready(forms@, next)
            && request.at < next.at && subtree_limit(forms@, request.at) == next.at
            && request_limit(forms@, next) == request_limit(forms@, request),
{
    let list = request.list?;
    let next = subtree_end(forms, request.at);
    let end = subtree_end(forms, list);
    if next < end {
        proof {
            reveal(nested_list_indices);
            assert(next < subtree_limit(forms@, next) <= end);
        }
        Some(Request { at: next, ..request })
    } else {
        None
    }
}

spec fn step_children_fit(forms: Seq<Form>, at: usize, step: CheckStep) -> bool {
    match step {
        CheckStep::Done => true,
        CheckStep::One(child) => request_inside(forms, at, child),
        CheckStep::Three(cond, yes, no) => request_inside(forms, at, cond) && request_inside(forms, at, yes)
            && request_inside(forms, at, no)
            && request_limit(forms, cond) <= yes.at && request_limit(forms, yes) <= no.at,
    }
}

fn read_check_step<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], locals: &LocalScopes<'a>, scope: Scope, request: Request,
) -> (result: Result<CheckStep, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), request.at < forms@.len(), locals.contains(scope),
    ensures
        result == step_model(source, forms@, lexical_view(parameters@, locals, scope), request),
        result matches Ok(step) ==> step_children_fit(forms@, request.at, step),
{
    let at = request.at;
    let expected = request.expected;
    let expression = read_shape(source, forms, at)?;
    match expression {
        Expression::Bool => {
            let word = source_word(source, forms, at);
            if locals.lookup(parameters, scope, word).is_some() {
                return Err(ExpressionCheckFailure::Deferred(DeferredExpression::BooleanBinding(span_of(&forms[at]))));
            }
            conform(expected, scalar(BuiltinDataType::Bool), span_of(&forms[at]))?;
            Ok(CheckStep::Done)
        }
        Expression::Parameter => {
            let word = source_word(source, forms, at);
            let Some(actual) = locals.lookup(parameters, scope, word) else {
                return Err(ExpressionCheckFailure::Deferred(DeferredExpression::Name(span_of(&forms[at]))));
            };
            conform(expected, actual, span_of(&forms[at]))?;
            Ok(CheckStep::Done)
        }
        Expression::Integer { negative } => {
            let ty = if negative || (expected.list_depth == 0
                && matches!(expected.builtin, Some(BuiltinDataType::Integer(IntegerType::Int)))) {
                IntegerType::Int
            } else {
                IntegerType::Nat
            };
            conform(expected, scalar(BuiltinDataType::Integer(ty)), span_of(&forms[at]))?;
            read_integer(source_word(source, forms, at), ty, span_of(&forms[at]))
        }
        Expression::List => {
            let end = subtree_end(forms, at);
            assert(at + 1 < end);
            let result = read_list_step(at, end, expected, span_of(&forms[at]));
            proof {
                reveal(nested_list_indices);
                if let Ok(CheckStep::One(element)) = result {
                    assert(at < element.at < end);
                    assert(forms@[at as int] is List);
                    assert(element.at < subtree_limit(forms@, element.at) <= end);
                }
            }
            result
        }
        Expression::Let => match read_let_structure(source, forms, at) {
            Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Let(error))),
            Ok(_) => Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span_of(&forms[at])))),
        },
        Expression::Fold(_) => Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span_of(&forms[at])))),
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
            let actual = shape_of_type(named.ty);
            conform(expected, actual, span)?;
            Ok(CheckStep::One(Request { at: value, expected: actual, list: None }))
        }
        Expression::Conditional { condition, yes, no } => Ok(CheckStep::Three(
            Request { at: condition, expected: scalar(BuiltinDataType::Bool), list: None },
            Request { at: yes, expected, list: None },
            Request { at: no, expected, list: None },
        )),
    }
}


enum BodyVerdict<'a> {
    Accepted,
    Rejected(ExpressionCheckFailure<'a>),
}

spec fn synthesized_type<'a>(source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize)
    -> Result<TypeShape, ExpressionCheckFailure<'a>>
{
    let span = form_span(forms[at as int]);
    let word = spelling(source, forms[at as int]);
    match shape(source, forms, at) {
        Err(error) => Err(error),
        Ok(Expression::Bool) => {
            if parameter_type(env, word, 0).is_some() {
                Err(ExpressionCheckFailure::Deferred(DeferredExpression::BooleanBinding(span)))
            } else {
                Ok(scalar_type(BuiltinDataType::Bool))
            }
        }
        Ok(Expression::Integer { negative }) => Ok(scalar_type(BuiltinDataType::Integer(
            if negative { IntegerType::Int } else { IntegerType::Nat }
        ))),
        Ok(Expression::Parameter) => match parameter_type(env, word, 0) {
            Some(ty) if ty.builtin.is_some() => Ok(ty),
            Some(_) => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span))),
            None => Err(ExpressionCheckFailure::Deferred(DeferredExpression::Name(span))),
        },
        Ok(Expression::Annotated { annotation, .. }) => match type_at(source, forms, annotation, annotation, 0) {
            Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Annotation(error))),
            Ok(syntax) => match annotation_value(syntax) {
                Some(ty) => Ok(ty),
                None => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(syntax.name_span))),
            },
        },
        Ok(Expression::List) if at + 2 == subtree_limit(forms, at) =>
            Err(ExpressionCheckFailure::Type(ExpressionTypeError::ListNeedsAnnotation(span))),
        _ => Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span))),
    }
}

fn synthesize_type<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], locals: &LocalScopes<'a>, scope: Scope, at: usize,
) -> (result: Result<TypeShape, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), at < forms@.len(), locals.contains(scope),
    ensures result == synthesized_type(source, forms@, lexical_view(parameters@, locals, scope), at),
{
    match read_shape(source, forms, at)? {
        Expression::Bool => {
            if locals.lookup(parameters, scope, source_word(source, forms, at)).is_some() {
                Err(ExpressionCheckFailure::Deferred(DeferredExpression::BooleanBinding(span_of(&forms[at]))))
            } else {
                Ok(scalar(BuiltinDataType::Bool))
            }
        }
        Expression::Integer { negative } => Ok(scalar(BuiltinDataType::Integer(
            if negative { IntegerType::Int } else { IntegerType::Nat }
        ))),
        Expression::Parameter => match locals.lookup(parameters, scope, source_word(source, forms, at)) {
            Some(ty) if ty.builtin.is_some() => Ok(ty),
            Some(_) => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span_of(&forms[at])))),
            None => Err(ExpressionCheckFailure::Deferred(DeferredExpression::Name(span_of(&forms[at])))),
        },
        Expression::Annotated { annotation, .. } => {
            let syntax = match read_type(source, forms, annotation) {
                Ok(syntax) => syntax,
                Err(error) => return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Annotation(error))),
            };
            let named = read_type_value(source, &syntax);
            if matches!(named.ty.atom, DataTypeAtom::Named(_)) {
                Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(named.name_span)))
            } else {
                Ok(shape_of_type(named.ty))
            }
        }
        Expression::List if subtree_end(forms, at) - at == 2 =>
            Err(ExpressionCheckFailure::Type(ExpressionTypeError::ListNeedsAnnotation(span_of(&forms[at])))),
        _ => Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span_of(&forms[at])))),
    }
}

spec fn local_body_check<'a>(source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, expected: TypeShape)
    -> BodyVerdict<'a>
{
    typed_body(source, forms, env, at, expected)
}

fn check_body<'a>(
    source: &'a str, forms: &[Form], signature: &DefnSignature<'a>, body: usize,
) -> (result: BodyVerdict<'a>)
    requires usable_forms(source, forms@), body < forms@.len(),
    ensures result == local_body_check(source, forms@, environment_view(signature.parameters@),
        body, type_shape(signature.result_type.ty)),
{
    check_typed_body(source, forms, &signature.parameters, body, shape_of_type(signature.result_type.ty))
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
        Ok(checked) => checked == signature && local_body_check(source, forms, environment_view(signature.parameters@), body, type_shape(signature.result_type.ty)) == BodyVerdict::Accepted,
        Err(DefnBodyError::Body(error)) => local_body_check(source, forms, environment_view(signature.parameters@), body, type_shape(signature.result_type.ty)) == BodyVerdict::Rejected(error),
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
/// 真偽値、十進整数、局所名の参照、`as-type`、`if`、`list` を扱う。
/// `if` は条件、左の分岐、右の分岐の順に検査する。
/// `list` は期待型の要素型で各要素を左から検査する。空のリストにも同じ期待型を使う。
/// `let` の右辺と本体は、他の式に入れ子にしても同じ規則で検査する。右辺は外側の型環境で
/// 左から検査し、すべて検査できた後に本体へ束縛を導入する。右辺ではリテラル、局所名の参照、
/// `as-type`、`if`、空でない `list` の型を求める。各分岐や各要素の型を個別に求め、一致を確かめる。
/// `fold-nat` の添字は `Nat`、`fold-list` の要素は入力リストの要素型とする。両方の反復で
/// 本体を初期値と同じ型で検査する。反復回数が0の場合も本体を検査する。
/// `fold-list` の入力に空のリストを書く場合は、型注釈で要素型を指定する。
/// 本体が検査を通れば、元ソースの範囲を持つ署名を返す。
///
/// # Errors
///
/// 検査順で最初に見つかった違反、または保留の理由を返す。
/// `let` は束縛列の文法と名前の重複を検査してから、右辺と本体の型を検査する。
/// 反復式は引数の個数、束縛名、入力、初期値、本体の順に検査する。
/// 後段で扱うフォーム、現在の環境に束縛されていない名前、段階固有の型、真偽値と束縛名の
/// 綴りが重なる箇所は保留する。
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
    assert(checked == local_body_check(source, input@, environment_view(signature.parameters@), body, type_shape(signature.result_type.ty)));
    match checked {
        BodyVerdict::Accepted => {
            assert(local_body_check(source, forms@, environment_view(signature.parameters@), body, type_shape(signature.result_type.ty)) == BodyVerdict::Accepted);
            assert(body_witness(source, Ok(signature), header, signature, forms@, body));
            Ok(signature)
        }
        BodyVerdict::Rejected(error) => {
            assert(body_witness(source, Err(DefnBodyError::Body(error)), header, signature, forms@, body));
            Err(DefnBodyError::Body(error))
        }
    }
}


spec fn meta_body_witness<'a>(
    source: &'a str, forms: Seq<Form>, header: super::defn::DefnHeader,
    result: Result<DefnSignature<'a>, ExpressionCheckFailure<'a>>, signature: DefnSignature<'a>,
    root: usize, body: usize,
) -> bool {
    &&& indexed_body_site(source, forms, root, body, header)
    &&& signature_matches_header(source, header, signature)
    &&& match result {
        Ok(checked) => checked == signature && local_body_check(source, forms, environment_view(signature.parameters@), body, type_shape(signature.result_type.ty)) == BodyVerdict::Accepted,
        Err(error) => local_body_check(source, forms, environment_view(signature.parameters@), body, type_shape(signature.result_type.ty)) == BodyVerdict::Rejected(error),
    }
}

pub(crate) closed spec fn meta_defn_check_matches(
    source: &str, forms: Seq<Form>, entries: Seq<MetaItem>, item: usize,
    result: Option<Result<DefnSignature, ExpressionCheckFailure>>,
) -> bool {
    if item >= entries.len() {
        result.is_none()
    } else {
        match entries[item as int].kind {
            MetaItemKind::Defn(header) => result matches Some(checked)
                && (exists|signature: DefnSignature, root: usize, body: usize|
                    #[trigger] meta_body_witness(source, forms, header, checked, signature, root, body)),
            _ => result.is_none(),
        }
    }
}

pub(crate) proof fn meta_defn_check_origin(
    source: &str, forms: Seq<Form>, entries: Seq<MetaItem>, item: usize,
    result: Option<Result<DefnSignature, ExpressionCheckFailure>>,
)
    requires meta_defn_check_matches(source, forms, entries, item, result),
    ensures
        result.is_some() == (item < entries.len() && entries[item as int].kind is Defn),
        result matches Some(Ok(signature)) ==> signature_matches_header(source, entries[item as int].kind->Defn_0, signature),
{
    if let Some(Ok(signature)) = result {
        let header = entries[item as int].kind->Defn_0;
        let (found, root, body) = choose|projected: DefnSignature, root: usize, body: usize|
            #[trigger] meta_body_witness(source, forms, header, Ok(signature), projected, root, body);
        assert(signature == found);
    }
}

pub(crate) fn check_indexed_meta_defn<'a>(
    source: &'a str, forms: &[Form], entries: &[MetaItem], item: usize,
) -> (result: Option<Result<DefnSignature<'a>, ExpressionCheckFailure<'a>>>)
    requires meta_ast_matches(source, forms@, entries@), meta_binding_spans_valid(source, entries@),
    ensures meta_defn_check_matches(source, forms@, entries@, item, result),
{
    if item >= entries.len() {
        return None;
    }
    let MetaItemKind::Defn(header) = &entries[item].kind else { return None; };
    proof { meta_defn_signature_spans(source, entries@, item as int); }
    let body = indexed_meta_body(source, forms, entries, item);
    let signature = read_header_signature(source, header);
    let ghost root = choose|root: usize| #[trigger] indexed_body_site(source, forms@, root, body, *header);
    match check_body(source, forms, &signature, body) {
        BodyVerdict::Accepted => {
            assert(meta_body_witness(source, forms@, *header, Ok(signature), signature, root, body));
            Some(Ok(signature))
        }
        BodyVerdict::Rejected(error) => {
            assert(meta_body_witness(source, forms@, *header, Err(error), signature, root, body));
            Some(Err(error))
        }
    }
}



proof fn signature_environments_agree(left: DefnSignature, right: DefnSignature)
    requires same_defn_signature(left, right),
    ensures
        environment_view(left.parameters@) == environment_view(right.parameters@),
        type_shape(left.result_type.ty) == type_shape(right.result_type.ty),
{
    signature_result_types_agree(left, right);
    let a = environment_view(left.parameters@);
    let b = environment_view(right.parameters@);
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == b[i] by {
        signature_parameter_types_agree(left, right, i);
        assert(a[i] == (left.parameters@[i].name.spec_bytes(), type_shape(left.parameters@[i].ty.ty)));
        assert(b[i] == (right.parameters@[i].name.spec_bytes(), type_shape(right.parameters@[i].ty.ty)));
    };
    assert(a =~= b);
}

/// 検査を通った署名の内容、または本体の診断値全体が一致することを表す。
pub open spec fn same_defn_body_outcome(
    indexed: Result<DefnSignature, ExpressionCheckFailure>, standalone: Result<DefnSignature, DefnBodyError>,
) -> bool {
    match (indexed, standalone) {
        (Ok(left), Ok(right)) => same_defn_signature(left, right),
        (Err(left), Err(DefnBodyError::Body(right))) => left == right,
        _ => false,
    }
}

pub(crate) proof fn indexed_meta_body_agrees_with_standalone(
    source: &str, forms: Seq<Form>, entries: Vec<MetaItem>,
    indexed: Option<Result<DefnSignature, ExpressionCheckFailure>>,
    standalone: Result<DefnSignature, DefnBodyError>,
)
    requires
        meta_ast_matches(source, forms, entries@), meta_file_matches(source, Ok(entries)),
        meta_defn_check_matches(source, forms, entries@, 0, indexed),
        defn_body_matches(source, standalone),
        !(standalone matches Err(DefnBodyError::Header(_))),
    ensures indexed matches Some(result) && same_defn_body_outcome(result, standalone),
{
    let (header, signature, parsed, body) =
        choose|header: super::defn::DefnHeader, signature: DefnSignature, forms: Seq<Form>, body: usize|
            #[trigger] body_witness(source, standalone, header, signature, forms, body);
    assert(sexpr_form_model(source) == Some(forms)) by {
        meta_ast_source(source, forms, entries@);
    };
    assert(parsed == forms);
    indexed_standalone_header(source, forms, entries, header);
    standalone_header_is_only_root(source, forms, header);
    let indexed_header = entries@[0].kind->Defn_0;
    let checked = indexed->Some_0;
    let (located, root, indexed_body) = choose|projected: DefnSignature, root: usize, body: usize|
        #[trigger] meta_body_witness(source, forms, indexed_header, checked, projected, root, body);
    meta_ast_body_origin(source, forms, entries@, 0);
    meta_ast_unique_start(forms, root, 0);
    defn_body_sites_agree(source, forms, 0, body, indexed_body);
    signature_projection_agrees(source, indexed_header, header, located, signature);
    signature_environments_agree(located, signature);
}


}
