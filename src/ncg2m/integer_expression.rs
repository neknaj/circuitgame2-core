//! 十進リテラルと、十進リテラルを引数とする組み込み整数式を扱う。

use core::ops::Range;
use crate::project::read_source_span;
use crate::syntax::{self, AtomKind, Form};
use super::integers::{
    IntegerLiteralError, IntegerOperation, IntegerType, IntegerValue,
    evaluate_int, evaluate_nat, int_to_nat, nat_to_int, read_integer_literal,
};
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid, sexpr_form_model, strict_syntax_rejection, well_formed_sexpr};
#[cfg(verus_only)]
use super::integers::{
    arithmetic_value, int_result_matches, integer_literal_matches, nat_result_matches,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::encode_utf8_decode_utf8;

verus! {

/// 整数式の検査を通過できなかった理由。
#[derive(Debug, Eq, PartialEq)]
pub enum IntegerCheckError {
    /// 共通の字句または S 式解析の違反。
    Syntax(syntax::Error),
    /// この入口で検査する単一の整数式の形に該当しない。
    UnsupportedExpression(Range<usize>),
    /// 式の型が期待型に合わない。範囲は原因の式を指す。
    TypeMismatch {
        /// 元ソース上の半開バイト範囲。
        span: Range<usize>,
        /// 式に要求された整数型。
        expected: IntegerType,
        /// 式に書かれている整数型。
        actual: IntegerType,
    },
    /// リテラルの値が指定された型に収まらない。
    LiteralOutOfRange {
        /// 元ソース上のリテラルの半開バイト範囲。
        span: Range<usize>,
        /// リテラルの整数型。
        ty: IntegerType,
    },
}

/// 検査済みの式を評価した結果が整数型の範囲を越えたことを表す。
#[derive(Debug, Eq, PartialEq)]
pub struct IntegerEvaluationError {
    /// 元ソース上の式全体の半開バイト範囲。
    pub span: Range<usize>,
    /// 演算または変換の結果の型。
    pub ty: IntegerType,
}

#[derive(Clone, Copy)]
struct Literal {
    index: usize,
    negative: bool,
}

#[derive(Clone, Copy)]
enum Builtin {
    Arithmetic(IntegerOperation),
    Convert(IntegerType),
    Annotate,
}

#[derive(Clone, Copy)]
enum Shape {
    Literal(Literal, Option<IntegerType>),
    Arithmetic(IntegerOperation, Literal, Literal),
    Convert(IntegerType, Literal),
}

#[derive(Clone, Copy, Debug)]
enum Instruction {
    Literal(IntegerValue),
    NatArithmetic(IntegerOperation, u64, u64),
    IntArithmetic(IntegerOperation, i64, i64),
    IntToNat(i64),
    NatToInt(u64),
}

/// 検査済みの整数式と、元ソース上のその範囲。
#[derive(Debug)]
pub struct CheckedIntegerExpression {
    span: Range<usize>,
    instruction: Instruction,
}

spec fn spelling(source: &str, form: Form) -> Seq<u8> {
    let span = form_span(form);
    source.spec_bytes()[span.start as int..span.end as int]
}

spec fn literal_model(form: Form, index: usize) -> Option<Literal> {
    match form {
        Form::Atom { kind: AtomKind::Natural, .. } => Some(Literal { index, negative: false }),
        Form::Atom { kind: AtomKind::NegativeInteger, .. } => Some(Literal { index, negative: true }),
        _ => None,
    }
}

spec fn builtin_model(word: Seq<u8>) -> Option<Builtin> {
    if word == "add".spec_bytes() { Some(Builtin::Arithmetic(IntegerOperation::Add)) }
    else if word == "sub".spec_bytes() { Some(Builtin::Arithmetic(IntegerOperation::Sub)) }
    else if word == "mul".spec_bytes() { Some(Builtin::Arithmetic(IntegerOperation::Mul)) }
    else if word == "int-to-nat".spec_bytes() { Some(Builtin::Convert(IntegerType::Nat)) }
    else if word == "nat-to-int".spec_bytes() { Some(Builtin::Convert(IntegerType::Int)) }
    else if word == "as-type".spec_bytes() { Some(Builtin::Annotate) }
    else { None }
}

spec fn type_model(word: Seq<u8>) -> Option<IntegerType> {
    if word == "Nat".spec_bytes() { Some(IntegerType::Nat) }
    else if word == "Int".spec_bytes() { Some(IntegerType::Int) }
    else { None }
}

spec fn shape_model(source: &str, forms: Seq<Form>) -> Option<Shape> {
    if forms.len() == 1 && literal_model(forms[0], 0).is_some() {
        Some(Shape::Literal(literal_model(forms[0], 0)->Some_0, None))
    } else if forms.len() >= 3 && forms[0] is List
        && forms[0]->List_end == forms.len()
        && (forms[1] matches Form::Atom { kind: AtomKind::Name, .. })
    {
        match builtin_model(spelling(source, forms[1])) {
            Some(Builtin::Arithmetic(operation)) if forms.len() == 4 =>
                match (literal_model(forms[2], 2), literal_model(forms[3], 3)) {
                    (Some(left), Some(right)) => Some(Shape::Arithmetic(operation, left, right)),
                    _ => None,
                },
            Some(Builtin::Convert(target)) if forms.len() == 3 =>
                match literal_model(forms[2], 2) {
                    Some(argument) => Some(Shape::Convert(target, argument)),
                    None => None,
                },
            Some(Builtin::Annotate) if forms.len() == 4
                && (forms[2] matches Form::Atom { kind: AtomKind::Name, .. }) =>
                match (type_model(spelling(source, forms[2])), literal_model(forms[3], 3)) {
                    (Some(ty), Some(argument)) => Some(Shape::Literal(argument, Some(ty))),
                    _ => None,
                },
            _ => None,
        }
    } else {
        None
    }
}

fn literal(form: &Form, index: usize) -> (result: Option<Literal>)
    ensures result == literal_model(*form, index),
{
    match form {
        Form::Atom { kind: AtomKind::Natural, .. } => Some(Literal { index, negative: false }),
        Form::Atom { kind: AtomKind::NegativeInteger, .. } => Some(Literal { index, negative: true }),
        _ => None,
    }
}

fn source_word<'a>(source: &'a str, forms: &[Form], index: usize) -> (word: &'a str)
    requires index < forms@.len(), form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures word.spec_bytes() == spelling(source, forms@[index as int]),
{
    let span = match &forms[index] {
        Form::Atom { span, .. } | Form::List { span, .. } => span,
    };
    proof {
        reveal(form_spans_valid);
        assert(*span == form_span(forms@[index as int]));
    }
    read_source_span(source, span.start, span.end)
}

fn is_spelling(word: &str, name: &str) -> (matches: bool)
    ensures matches == (word.spec_bytes() == name.spec_bytes()),
{
    proof {
        encode_utf8_decode_utf8(word@);
        encode_utf8_decode_utf8(name@);
    }
    word == name
}

fn builtin(word: &str) -> (head: Option<Builtin>)
    ensures head == builtin_model(word.spec_bytes()),
{
    if is_spelling(word, "add") { Some(Builtin::Arithmetic(IntegerOperation::Add)) }
    else if is_spelling(word, "sub") { Some(Builtin::Arithmetic(IntegerOperation::Sub)) }
    else if is_spelling(word, "mul") { Some(Builtin::Arithmetic(IntegerOperation::Mul)) }
    else if is_spelling(word, "int-to-nat") { Some(Builtin::Convert(IntegerType::Nat)) }
    else if is_spelling(word, "nat-to-int") { Some(Builtin::Convert(IntegerType::Int)) }
    else if is_spelling(word, "as-type") { Some(Builtin::Annotate) }
    else { None }
}

fn integer_type(word: &str) -> (ty: Option<IntegerType>)
    ensures ty == type_model(word.spec_bytes()),
{
    if is_spelling(word, "Nat") { Some(IntegerType::Nat) }
    else if is_spelling(word, "Int") { Some(IntegerType::Int) }
    else { None }
}

fn expression_shape(source: &str, forms: &[Form]) -> (result: Option<Shape>)
    requires form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures result == shape_model(source, forms@),
{
    if forms.len() == 1 {
        if let Some(leaf) = literal(&forms[0], 0) {
            return Some(Shape::Literal(leaf, None));
        }
    }
    if forms.len() < 3 { return None; }
    let Form::List { end: subtree_end, .. } = &forms[0] else { return None; };
    if *subtree_end != forms.len() || !matches!(forms[1], Form::Atom { kind: AtomKind::Name, .. }) {
        return None;
    }
    match builtin(source_word(source, forms, 1)) {
        Some(Builtin::Arithmetic(operation)) if forms.len() == 4 => {
            let Some(left) = literal(&forms[2], 2) else { return None; };
            let Some(right) = literal(&forms[3], 3) else { return None; };
            Some(Shape::Arithmetic(operation, left, right))
        }
        Some(Builtin::Convert(target)) if forms.len() == 3 => {
            let Some(argument) = literal(&forms[2], 2) else { return None; };
            Some(Shape::Convert(target, argument))
        }
        Some(Builtin::Annotate) if forms.len() == 4
            && matches!(forms[2], Form::Atom { kind: AtomKind::Name, .. }) =>
        {
            let Some(ty) = integer_type(source_word(source, forms, 2)) else { return None; };
            let Some(argument) = literal(&forms[3], 3) else { return None; };
            Some(Shape::Literal(argument, Some(ty)))
        }
        _ => None,
    }
}

fn copy_span(form: &Form) -> (span: Range<usize>)
    ensures span == form_span(*form),
{
    match form {
        Form::Atom { span, .. } | Form::List { span, .. } => span.start..span.end,
    }
}

proof fn literal_results_agree(
    bytes: Seq<u8>, expected: IntegerType, a: Result<IntegerValue, IntegerLiteralError>,
    b: Result<IntegerValue, IntegerLiteralError>,
)
    requires
        integer_literal_matches(bytes, Some(expected), a),
        integer_literal_matches(bytes, Some(expected), b),
    ensures a == b,
{
}

spec fn checked_literal(
    source: &str, form: Form, ty: IntegerType,
) -> Result<IntegerValue, IntegerCheckError> {
    let bytes = spelling(source, form);
    let span = form_span(form);
    let parsed = choose|r: Result<IntegerValue, IntegerLiteralError>| integer_literal_matches(bytes, Some(ty), r);
    match parsed {
        Ok(v) => Ok(v),
        Err(IntegerLiteralError::OutOfRange(range_ty)) =>
            Err(IntegerCheckError::LiteralOutOfRange { span, ty: range_ty }),
        Err(IntegerLiteralError::NegativeLiteralForNat) =>
            Err(IntegerCheckError::TypeMismatch { span, expected: IntegerType::Nat, actual: IntegerType::Int }),
        Err(IntegerLiteralError::InvalidDigits) => Err(IntegerCheckError::UnsupportedExpression(span)),
    }
}

spec fn value_has_type(value: IntegerValue, ty: IntegerType) -> bool {
    match (value, ty) {
        (IntegerValue::Nat(_), IntegerType::Nat) | (IntegerValue::Int(_), IntegerType::Int) => true,
        _ => false,
    }
}

fn check_operand(source: &str, forms: &[Form], at: usize, ty: IntegerType)
    -> (result: Result<IntegerValue, IntegerCheckError>)
    requires at < forms@.len(), form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result == checked_literal(source, forms@[at as int], ty),
        result matches Ok(value) ==> value_has_type(value, ty),
{
    let word = source_word(source, forms, at);
    let read = read_integer_literal(word, Some(ty));
    proof {
        let bytes = spelling(source, forms@[at as int]);
        let model = choose|r: Result<IntegerValue, IntegerLiteralError>| integer_literal_matches(bytes, Some(ty), r);
        literal_results_agree(bytes, ty, read, model);
    }
    match read {
        Ok(value) => Ok(value),
        Err(IntegerLiteralError::OutOfRange(ty)) =>
            Err(IntegerCheckError::LiteralOutOfRange { span: copy_span(&forms[at]), ty }),
        Err(IntegerLiteralError::NegativeLiteralForNat) => Err(IntegerCheckError::TypeMismatch {
            span: copy_span(&forms[at]), expected: IntegerType::Nat, actual: IntegerType::Int,
        }),
        Err(IntegerLiteralError::InvalidDigits) =>
            Err(IntegerCheckError::UnsupportedExpression(copy_span(&forms[at]))),
    }
}

spec fn opposite(ty: IntegerType) -> IntegerType {
    match ty { IntegerType::Nat => IntegerType::Int, IntegerType::Int => IntegerType::Nat }
}

fn other_type(ty: IntegerType) -> (other: IntegerType)
    ensures other == opposite(ty),
{
    match ty { IntegerType::Nat => IntegerType::Int, IntegerType::Int => IntegerType::Nat }
}

spec fn fixed_type(shape: Shape) -> Option<IntegerType> {
    match shape {
        Shape::Literal(_, annotated) => annotated,
        Shape::Convert(target, _) => Some(target),
        _ => None,
    }
}

fn result_annotation(shape: Shape) -> (ty: Option<IntegerType>)
    ensures ty == fixed_type(shape),
{
    match shape {
        Shape::Literal(_, annotated) => annotated,
        Shape::Convert(target, _) => Some(target),
        _ => None,
    }
}

spec fn chosen_type(expected: Option<IntegerType>, any_negative: bool) -> IntegerType {
    match expected {
        Some(ty) => ty,
        None => if any_negative { IntegerType::Int } else { IntegerType::Nat },
    }
}

fn select_type(expected: Option<IntegerType>, any_negative: bool) -> (ty: IntegerType)
    ensures ty == chosen_type(expected, any_negative),
{
    match expected {
        Some(ty) => ty,
        None => if any_negative { IntegerType::Int } else { IntegerType::Nat },
    }
}

spec fn arithmetic_instruction(
    op: IntegerOperation, a: IntegerValue, b: IntegerValue, ty: IntegerType,
) -> Instruction
    recommends value_has_type(a, ty), value_has_type(b, ty),
{
    match (a, b) {
        (IntegerValue::Nat(left), IntegerValue::Nat(right)) => Instruction::NatArithmetic(op, left, right),
        (IntegerValue::Int(left), IntegerValue::Int(right)) => Instruction::IntArithmetic(op, left, right),
        _ => arbitrary(),
    }
}

spec fn conversion_instruction(value: IntegerValue) -> Instruction {
    match value {
        IntegerValue::Nat(n) => Instruction::NatToInt(n),
        IntegerValue::Int(n) => Instruction::IntToNat(n),
    }
}

spec fn instruction_model(source: &str, forms: Seq<Form>, shape: Shape, expected: Option<IntegerType>)
    -> Result<Instruction, IntegerCheckError>
{
    let fixed = fixed_type(shape);
    if fixed.is_some() && expected == Some(opposite(fixed->Some_0)) {
        let actual = fixed->Some_0;
        Err(IntegerCheckError::TypeMismatch {
            span: form_span(forms[0]), expected: opposite(actual), actual,
        })
    } else {
        match shape {
            Shape::Literal(leaf, annotation) => {
                let ty = chosen_type(if annotation.is_some() { annotation } else { expected }, leaf.negative);
                match checked_literal(source, forms[leaf.index as int], ty) {
                    Ok(value) => Ok(Instruction::Literal(value)),
                    Err(error) => Err(error),
                }
            }
            Shape::Arithmetic(op, left, right) => {
                let ty = chosen_type(expected, left.negative || right.negative);
                match checked_literal(source, forms[left.index as int], ty) {
                    Err(error) => Err(error),
                    Ok(a) => match checked_literal(source, forms[right.index as int], ty) {
                        Err(error) => Err(error),
                        Ok(b) => Ok(arithmetic_instruction(op, a, b, ty)),
                    },
                }
            }
            Shape::Convert(target, argument) => match checked_literal(
                source, forms[argument.index as int], opposite(target),
            ) {
                Ok(value) => Ok(conversion_instruction(value)),
                Err(error) => Err(error),
            },
        }
    }
}

proof fn shape_indices(source: &str, forms: Seq<Form>, shape: Shape)
    requires shape_model(source, forms) == Some(shape),
    ensures
        forms.len() > 0,
        match shape {
            Shape::Literal(leaf, _) => leaf.index < forms.len(),
            Shape::Arithmetic(_, left, right) => left.index < forms.len() && right.index < forms.len(),
            Shape::Convert(_, argument) => argument.index < forms.len(),
        },
{
}

fn check_instruction(source: &str, forms: &[Form], shape: Shape, expected: Option<IntegerType>)
    -> (checked: Result<Instruction, IntegerCheckError>)
    requires
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        shape_model(source, forms@) == Some(shape),
    ensures checked == instruction_model(source, forms@, shape, expected),
{
    proof { shape_indices(source, forms@, shape); }
    if let Some(actual) = result_annotation(shape) {
        if matches!((expected, actual),
            (Some(IntegerType::Nat), IntegerType::Int) | (Some(IntegerType::Int), IntegerType::Nat))
        {
            return Err(IntegerCheckError::TypeMismatch {
                span: copy_span(&forms[0]), expected: other_type(actual), actual,
            });
        }
    }
    match shape {
        Shape::Literal(leaf, annotation) => {
            let ty = select_type(if annotation.is_some() { annotation } else { expected }, leaf.negative);
            let value = check_operand(source, forms, leaf.index, ty)?;
            Ok(Instruction::Literal(value))
        }
        Shape::Arithmetic(op, left, right) => {
            let ty = select_type(expected, left.negative || right.negative);
            let a = check_operand(source, forms, left.index, ty)?;
            let b = check_operand(source, forms, right.index, ty)?;
            match (a, b) {
                (IntegerValue::Nat(left), IntegerValue::Nat(right)) => Ok(Instruction::NatArithmetic(op, left, right)),
                (IntegerValue::Int(left), IntegerValue::Int(right)) => Ok(Instruction::IntArithmetic(op, left, right)),
                _ => unreachable!(),
            }
        }
        Shape::Convert(target, argument) => {
            let value = check_operand(source, forms, argument.index, other_type(target))?;
            match value {
                IntegerValue::Nat(n) => Ok(Instruction::NatToInt(n)),
                IntegerValue::Int(n) => Ok(Instruction::IntToNat(n)),
            }
        }
    }
}

/// 共通の構文規則と整数式の型検査に対応する結果を表す。
pub closed spec fn integer_check_matches(
    source: &str, expected: Option<IntegerType>, result: Result<CheckedIntegerExpression, IntegerCheckError>,
) -> bool {
    if well_formed_sexpr(source) {
        sexpr_form_model(source) matches Some(forms) && match shape_model(source, forms) {
            None => result == Err(IntegerCheckError::UnsupportedExpression(0..source.spec_bytes().len() as usize)),
            Some(shape) => match instruction_model(source, forms, shape, expected) {
                Ok(instruction) => result matches Ok(checked)
                    && checked.span == form_span(forms[0]) && checked.instruction == instruction,
                Err(error) => result == Err(error),
            },
        }
    } else {
        result matches Err(IntegerCheckError::Syntax(error)) && strict_syntax_rejection(source, error)
    }
}

/// 単一の整数式を構文と型に照らして検査する。
///
/// 利用者による名前の束縛がない環境を対象とする。
/// 十進リテラル、リテラルを引数とする `add`、`sub`、`mul`、`int-to-nat`、
/// `nat-to-int`、およびリテラルへの `as-type` を受理する。
/// 算術で期待型がなければ、負号付きの引数が一つでもある場合は `Int`、
/// それ以外は `Nat` の署名を選ぶ。
///
/// # Errors
///
/// 共通の字句・構文、対応する式の形、式全体の期待型を順に検査する。
/// 引数のリテラルは左から右へ検査し、最初に失敗した位置を返す。
pub fn check_integer_expression(source: &str, expected: Option<IntegerType>)
    -> (result: Result<CheckedIntegerExpression, IntegerCheckError>)
    ensures integer_check_matches(source, expected, result),
{
    let forms = match syntax::parse(source) {
        Ok(forms) => forms,
        Err(error) => return Err(IntegerCheckError::Syntax(error)),
    };
    let Some(shape) = expression_shape(source, forms.as_slice()) else {
        return Err(IntegerCheckError::UnsupportedExpression(0..source.as_bytes().len()));
    };
    let instruction = check_instruction(source, forms.as_slice(), shape, expected)?;
    proof { shape_indices(source, forms@, shape); }
    Ok(CheckedIntegerExpression { span: copy_span(&forms[0]), instruction })
}

spec fn instruction_meaning(instruction: Instruction) -> (IntegerType, int) {
    match instruction {
        Instruction::Literal(IntegerValue::Nat(n)) => (IntegerType::Nat, n as int),
        Instruction::Literal(IntegerValue::Int(n)) => (IntegerType::Int, n as int),
        Instruction::NatArithmetic(op, a, b) => (IntegerType::Nat, arithmetic_value(op, a as int, b as int)),
        Instruction::IntArithmetic(op, a, b) => (IntegerType::Int, arithmetic_value(op, a as int, b as int)),
        Instruction::IntToNat(n) => (IntegerType::Nat, n as int),
        Instruction::NatToInt(n) => (IntegerType::Int, n as int),
    }
}

/// ソース上の検査済み整数式の型、数学上の値、半開バイト範囲をこの順に返す。
///
/// 演算結果の表現範囲はここでは制限しない。構文・型・リテラルの検査に失敗した場合は `None` とする。
pub closed spec fn integer_expression_meaning(source: &str, expected: Option<IntegerType>)
    -> Option<(IntegerType, int, Range<usize>)>
{
    if !well_formed_sexpr(source) {
        None
    } else {
        match sexpr_form_model(source) {
            Some(forms) => match shape_model(source, forms) {
                Some(shape) => match instruction_model(source, forms, shape, expected) {
                    Ok(instruction) => {
                        let (ty, value) = instruction_meaning(instruction);
                        Some((ty, value, form_span(forms[0])))
                    }
                    Err(_) => None,
                },
                None => None,
            },
            None => None,
        }
    }
}

/// 数学上の値から、型に収まる値または式の範囲付きの評価エラーを定める。
pub open spec fn integer_evaluation_matches(
    ty: IntegerType, value: int, span: Range<usize>, result: Result<IntegerValue, IntegerEvaluationError>,
) -> bool {
    match ty {
        IntegerType::Nat => if 0 <= value <= u64::MAX {
            result matches Ok(IntegerValue::Nat(number)) && number as int == value
        } else {
            result == Err(IntegerEvaluationError { span, ty })
        },
        IntegerType::Int => if i64::MIN <= value <= i64::MAX {
            result matches Ok(IntegerValue::Int(number)) && number as int == value
        } else {
            result == Err(IntegerEvaluationError { span, ty })
        },
    }
}

/// 検査と評価の公開契約をつなぎ、元ソースの数学上の値と評価結果を対応付ける。
pub proof fn integer_check_and_evaluation_agree(
    source: &str, expected: Option<IntegerType>, checked: &CheckedIntegerExpression,
    result: Result<IntegerValue, IntegerEvaluationError>,
)
    requires integer_check_matches(source, expected, Ok(*checked)), checked.evaluation_matches(result),
    ensures integer_expression_meaning(source, expected) matches Some((ty, value, span))
        && integer_evaluation_matches(ty, value, span, result),
{
}

impl CheckedIntegerExpression {
    /// 組み込みの数学上の値または範囲エラーと、評価結果が対応することを表す。
    pub closed spec fn evaluation_matches(&self, result: Result<IntegerValue, IntegerEvaluationError>) -> bool {
        let (ty, value) = instruction_meaning(self.instruction);
        integer_evaluation_matches(ty, value, self.span, result)
    }

    /// 検査済みの式の値を求める。
    ///
    /// # Errors
    ///
    /// 演算または変換の結果が範囲外の場合は、実行した式全体の範囲と結果の型を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::ncg2m::integer_expression::check_integer_expression;
    /// use circuitgame2_core::ncg2m::integers::{IntegerType, IntegerValue};
    ///
    /// let expr = check_integer_expression("(add 1 -2)", None).unwrap();
    /// assert_eq!(expr.evaluate().unwrap(), IntegerValue::Int(-1));
    /// let expr = check_integer_expression("(sub 0 1)", None).unwrap();
    /// let error = expr.evaluate().unwrap_err();
    /// assert_eq!(error.span, 0..9);
    /// assert_eq!(error.ty, IntegerType::Nat);
    /// ```
    pub fn evaluate(&self) -> (result: Result<IntegerValue, IntegerEvaluationError>)
        ensures self.evaluation_matches(result),
    {
        let span = self.span.start..self.span.end;
        match self.instruction {
            Instruction::Literal(value) => Ok(value),
            Instruction::NatArithmetic(op, left, right) => pack_nat(evaluate_nat(op, left, right), span),
            Instruction::IntArithmetic(op, left, right) => pack_int(evaluate_int(op, left, right), span),
            Instruction::IntToNat(n) => pack_nat(int_to_nat(n), span),
            Instruction::NatToInt(n) => pack_int(nat_to_int(n), span),
        }
    }
}

fn pack_nat(read: Result<u64, super::integers::IntegerOutOfRange>, span: Range<usize>)
    -> (result: Result<IntegerValue, IntegerEvaluationError>)
    ensures forall|value: int| #[trigger] nat_result_matches(value, read)
        ==> integer_evaluation_matches(IntegerType::Nat, value, span, result),
{
    match read {
        Ok(value) => Ok(IntegerValue::Nat(value)),
        Err(_) => Err(IntegerEvaluationError { span, ty: IntegerType::Nat }),
    }
}

fn pack_int(read: Result<i64, super::integers::IntegerOutOfRange>, span: Range<usize>)
    -> (result: Result<IntegerValue, IntegerEvaluationError>)
    ensures forall|value: int| #[trigger] int_result_matches(value, read)
        ==> integer_evaluation_matches(IntegerType::Int, value, span, result),
{
    match read {
        Ok(value) => Ok(IntegerValue::Int(value)),
        Err(_) => Err(IntegerEvaluationError { span, ty: IntegerType::Int }),
    }
}

} // verus!
