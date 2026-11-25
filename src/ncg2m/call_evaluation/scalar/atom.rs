//! 型付きの仮引数と、真偽値・整数のアトムを評価する。

use super::*;
use crate::ncg2m::data_types::SignatureParameter;
use crate::ncg2m::defn::span_of;
#[cfg(verus_only)]
use crate::ncg2m::forms::spelling;
use crate::ncg2m::forms::{is_spelling, source_word};
use crate::ncg2m::integers::{IntegerLiteralError, read_integer_literal};
#[cfg(verus_only)]
use crate::ncg2m::integers::integer_literal_matches;
use crate::syntax::{AtomKind, Form};

verus! {

/// 整数リテラルを評価できなかった理由と、リテラルを書いた位置。
#[derive(Debug)]
pub struct ScalarLiteralError<'p, 'a> {
    /// 元のソースと文書版。
    pub source: &'p ProjectSource<'a>,
    /// リテラルの UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 値が表現範囲を越えた場合など、整数の読み取りが失敗した理由。
    pub error: IntegerLiteralError,
}

spec fn scalar_parameter(
    parameters: Seq<SignatureParameter>, values: Seq<ScalarValue>, word: Seq<u8>,
    result: Option<ScalarValue>,
) -> bool {
    match result {
        Some(value) => exists|i: int| 0 <= i < parameters.len()
            && (#[trigger] parameters[i]).name.spec_bytes() == word && values[i] == value
            && (forall|j: int| 0 <= j < i ==> (#[trigger] parameters[j]).name.spec_bytes() != word),
        None => forall|i: int| 0 <= i < parameters.len()
            ==> (#[trigger] parameters[i]).name.spec_bytes() != word,
    }
}

fn read_parameter(
    parameters: &[SignatureParameter<'_>], values: &[ScalarValue], word: &str,
) -> (result: Option<ScalarValue>)
    requires parameters@.len() == values@.len(),
    ensures scalar_parameter(parameters@, values@, word.spec_bytes(), result),
{
    let mut i = 0;
    while i < parameters.len()
        invariant
            i <= parameters@.len() == values@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] parameters@[j]).name.spec_bytes() != word.spec_bytes(),
        decreases parameters@.len() - i,
    {
        if is_spelling(parameters[i].name, word) {
            return Some(values[i]);
        }
        i += 1;
    }
    None
}

spec fn name_atom_result(
    parameters: Seq<SignatureParameter>, values: Seq<ScalarValue>, word: Seq<u8>, expected: DataType,
    result: Option<ScalarValue>,
) -> bool {
    let selected = if word == "true".spec_bytes() { Some(ScalarValue::Bool(true)) }
        else if word == "false".spec_bytes() { Some(ScalarValue::Bool(false)) }
        else {
            choose|value: Option<ScalarValue>| #[trigger] scalar_parameter(parameters, values, word, value)
        };
    result == match selected {
        Some(value) if scalar_fits(value, expected) => Some(value),
        _ => None,
    }
}

proof fn scalar_parameters_agree(
    parameters: Seq<SignatureParameter>, values: Seq<ScalarValue>, word: Seq<u8>,
    first: Option<ScalarValue>, other: Option<ScalarValue>,
)
    requires scalar_parameter(parameters, values, word, first), scalar_parameter(parameters, values, word, other),
    ensures first == other,
{
    if let Some(value) = first {
        let i = choose|i: int| 0 <= i < parameters.len()
            && (#[trigger] parameters[i]).name.spec_bytes() == word && values[i] == value
            && (forall|j: int| 0 <= j < i ==> (#[trigger] parameters[j]).name.spec_bytes() != word);
        if let Some(value2) = other {
            let j = choose|j: int| 0 <= j < parameters.len()
                && (#[trigger] parameters[j]).name.spec_bytes() == word && values[j] == value2
                && (forall|k: int| 0 <= k < j ==> (#[trigger] parameters[k]).name.spec_bytes() != word);
            assert(i == j);
        }
    } else if let Some(value) = other {
        let i = choose|i: int| 0 <= i < parameters.len()
            && (#[trigger] parameters[i]).name.spec_bytes() == word && values[i] == value
            && (forall|j: int| 0 <= j < i ==> (#[trigger] parameters[j]).name.spec_bytes() != word);
        assert(parameters[i].name.spec_bytes() != word);
    }
}

fn read_name_atom(
    parameters: &[SignatureParameter<'_>], values: &[ScalarValue], word: &str, expected: DataType<'_>,
) -> (result: Option<ScalarValue>)
    requires parameters@.len() == values@.len(),
    ensures name_atom_result(parameters@, values@, word.spec_bytes(), expected, result),
{
    let selected = if is_spelling(word, "true") {
        Some(ScalarValue::Bool(true))
    } else if is_spelling(word, "false") {
        Some(ScalarValue::Bool(false))
    } else {
        let found = read_parameter(parameters, values, word);
        proof {
            let model = choose|value: Option<ScalarValue>|
                #[trigger] scalar_parameter(parameters@, values@, word.spec_bytes(), value);
            scalar_parameters_agree(parameters@, values@, word.spec_bytes(), found, model);
        }
        found
    };
    if let Some(value) = selected {
        if scalar_matches(value, expected) { return Some(value); }
    }
    None
}

pub(super) closed spec fn scalar_atom_matches<'p, 'a>(
    frame: &ScalarCallFrame<'p, 'a>, at: usize, expected: DataType<'a>,
    result: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>,
) -> bool {
    let body = frame.body_model();
    if at >= body.forms@.len() {
        result == Ok(None)
    } else {
        let form = body.forms@[at as int];
        let word = spelling(body.source.text_model(), form);
        match form {
            Form::Atom { kind: AtomKind::Natural | AtomKind::NegativeInteger, .. } => {
                if expected.list_depth == 0 && expected.atom is Builtin && expected.atom->Builtin_0 is Integer {
                    let signedness = expected.atom->Builtin_0->Integer_0;
                    match result {
                        Ok(Some(ScalarValue::Integer(value))) => integer_literal_matches(word, Some(signedness), Ok(value)),
                        Err(error) => *error.source == *body.source && error.span == form_span(form)
                            && integer_literal_matches(word, Some(signedness), Err(error.error)),
                        _ => false,
                    }
                } else { result == Ok(None) }
            }
            Form::Atom { kind: AtomKind::Name, .. } => result matches Ok(value)
                && name_atom_result(body.signature.parameters@, frame.parameter_values_model(), word, expected, value),
            _ => result == Ok(None),
        }
    }
}

/// 本体が真偽値、整数、または仮引数のアトムなら、その値または整数診断を定める。
pub closed spec fn atomic_body_matches<'p, 'a>(
    frame: &ScalarCallFrame<'p, 'a>, result: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>,
) -> bool {
    let body = frame.body_model();
    scalar_atom_matches(frame, body.at, body.signature.result_type.ty, result)
}

impl<'p, 'a> ScalarCallFrame<'p, 'a> {
    /// 本体が真偽値、整数、または仮引数のアトムなら評価する。
    ///
    /// 呼び出しや条件式など、アトム以外の本体には `Ok(None)` を返す。
    ///
    /// # Errors
    ///
    /// 整数が宣言された型の表現範囲に収まらない場合は、元のリテラルの範囲と理由を返す。
    pub fn evaluate_atomic_body(&self)
        -> (result: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>)
        ensures atomic_body_matches(self, result),
    {
        self.evaluate_atom(self.body.at, self.body.signature.result_type.ty)
    }

    pub(super) fn evaluate_atom(&self, at: usize, expected: DataType<'a>)
        -> (result: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>)
        ensures scalar_atom_matches(self, at, expected, result),
            result matches Ok(Some(value)) ==> scalar_fits(value, expected),
    {
        proof { use_type_invariant(self); }
        let body = &self.body;
        let source = body.source.text();
        let Some(form) = body.forms.get(at) else { return Ok(None); };
        match form {
            Form::Atom { kind: AtomKind::Natural | AtomKind::NegativeInteger, .. } => {
                if expected.list_depth != 0 { return Ok(None); }
                let DataTypeAtom::Builtin(BuiltinDataType::Integer(signedness)) = expected.atom
                    else { return Ok(None); };
                let word = source_word(source, body.forms, at);
                match read_integer_literal(word, Some(signedness)) {
                    Ok(value) => Ok(Some(ScalarValue::Integer(value))),
                    Err(error) => Err(ScalarLiteralError { source: body.source, span: span_of(form), error }),
                }
            }
            Form::Atom { kind: AtomKind::Name, .. } => Ok(read_name_atom(
                body.signature.parameters.as_slice(), self.values.as_slice(), source_word(source, body.forms, at), expected,
            )),
            _ => Ok(None),
        }
    }
}

}
