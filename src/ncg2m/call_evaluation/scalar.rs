//! 真偽値と整数の引数を、呼び出し先の仮引数に結び付ける。

use alloc::vec::Vec;
use core::ops::Range;
use crate::project::{DefnCallPlan, ProjectSource};
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
use crate::ncg2m::data_types::{BuiltinDataType, DataType, DataTypeAtom, DefnSignature};
use crate::ncg2m::integers::{IntegerType, IntegerValue};
use vstd::prelude::*;
use super::DefnEvaluationBody;

mod atom;
mod invocation;
pub use invocation::{ScalarInvocation, ScalarInvocationError, ScalarInvocationStep, prepare_scalar_invocation};
#[cfg(verus_only)]
pub use invocation::scalar_invocation_applicable;
pub use atom::ScalarLiteralError;
#[cfg(verus_only)]
pub use atom::atomic_body_matches;

verus! {

/// 初段の評価器で扱う真偽値と固定長整数。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScalarValue {
    /// 真偽値。
    Bool(bool),
    /// 自然数または符号付き整数。
    Integer(IntegerValue),
}

impl ScalarValue {
    /// 値に対応する NCG2M の基本型を表す。
    pub open spec fn type_model(self) -> BuiltinDataType {
        match self {
            Self::Bool(_) => BuiltinDataType::Bool,
            Self::Integer(IntegerValue::Nat(_)) => BuiltinDataType::Integer(IntegerType::Nat),
            Self::Integer(IntegerValue::Int(_)) => BuiltinDataType::Integer(IntegerType::Int),
        }
    }

    fn builtin_type(self) -> (ty: BuiltinDataType)
        ensures ty == self.type_model(),
    {
        match self {
            Self::Bool(_) => BuiltinDataType::Bool,
            Self::Integer(IntegerValue::Nat(_)) => BuiltinDataType::Integer(IntegerType::Nat),
            Self::Integer(IntegerValue::Int(_)) => BuiltinDataType::Integer(IntegerType::Int),
        }
    }
}

/// 指定した仮引数の型に、暗黙変換せずに値を束縛できることを表す。
pub open spec fn scalar_fits(value: ScalarValue, ty: DataType) -> bool {
    ty.list_depth == 0 && ty.atom == DataTypeAtom::Builtin(value.type_model())
}

fn scalar_matches(value: ScalarValue, ty: DataType<'_>) -> (matches_type: bool)
    ensures matches_type == scalar_fits(value, ty),
{
    if ty.list_depth != 0 { return false; }
    let DataTypeAtom::Builtin(expected) = ty.atom else { return false; };
    matches!((value.builtin_type(), expected),
        (BuiltinDataType::Bool, BuiltinDataType::Bool)
        | (BuiltinDataType::Integer(IntegerType::Nat), BuiltinDataType::Integer(IntegerType::Nat))
        | (BuiltinDataType::Integer(IntegerType::Int), BuiltinDataType::Integer(IntegerType::Int)))
}

/// 呼び出し先に渡す値を受け取れなかった理由。
#[derive(Debug)]
pub enum ScalarBindingError<'p, 'a> {
    /// 指定した順位の補助関数を計画に見つけられなかった。
    Rank,
    /// 呼び出し先の仮引数の数と、渡された値の数が異なる。
    Arity {
        /// 呼び出し先の宣言を書いたファイルと文書版。
        source: &'p ProjectSource<'a>,
        /// 呼び出し先の宣言全体の UTF-8 半開バイト範囲。
        span: Range<usize>,
        /// 署名が要求する引数の個数。
        expected_count: usize,
        /// 渡された値の個数。
        found_count: usize,
    },
    /// 最初に型が一致しなかった引数。
    Type {
        /// 呼び出し先の宣言を書いたファイルと文書版。
        source: &'p ProjectSource<'a>,
        /// 呼び出し先に書かれた仮引数の型の UTF-8 半開バイト範囲。
        span: Range<usize>,
        /// 署名内での仮引数の位置。
        parameter: usize,
        /// 署名が要求する型。
        expected_type: DataType<'a>,
        /// 渡された値の型。
        found_type: BuiltinDataType,
    },
}

/// 補助関数に入るときの本体と、仮引数だけで構成した新しい環境。
pub struct ScalarCallFrame<'p, 'a> {
    body: DefnEvaluationBody<'p, 'a>,
    values: Vec<ScalarValue>,
}

impl<'p, 'a> ScalarCallFrame<'p, 'a> {
    #[verifier::type_invariant]
    spec fn source_and_values_are_ready(&self) -> bool {
        &&& self.body.at < self.body.forms@.len()
        &&& form_spans_valid(self.body.source.text_model(), self.body.forms@,
            self.body.source.text_model().spec_bytes().len() as int)
        &&& parameters_match(self.body.signature, self.values@)
    }

    /// 呼び出し先の本体と署名を表す。
    pub closed spec fn body_model(&self) -> DefnEvaluationBody<'p, 'a> {
        self.body
    }

    /// 呼び出し先の仮引数に対応する値の列を表す。
    pub closed spec fn parameter_values_model(&self) -> Seq<ScalarValue> {
        self.values@
    }

    /// 元の文書版と構文木上の本体を返す。
    pub fn body(&self) -> (body: &DefnEvaluationBody<'p, 'a>)
        ensures *body == self.body_model(),
    {
        &self.body
    }

    /// 位置順に束縛した仮引数を返す。
    pub fn parameters(&self) -> (values: &[ScalarValue])
        ensures values@ == self.parameter_values_model(),
    {
        self.values.as_slice()
    }
}

/// すべての仮引数に、署名の位置順どおりの型を持つ値が与えられたことを表す。
pub open spec fn parameters_match(signature: DefnSignature, values: Seq<ScalarValue>) -> bool {
    &&& values.len() == signature.parameters@.len()
    &&& forall|i: int| 0 <= i < values.len() ==>
        scalar_fits(#[trigger] values[i], signature.parameters@[i].ty.ty)
}

/// 仮引数の束縛結果と、最初に報告する署名の違反を定める。
pub open spec fn binding_matches<'p, 'a>(
    body: DefnEvaluationBody<'p, 'a>, values: Seq<ScalarValue>,
    result: Result<ScalarCallFrame<'p, 'a>, ScalarBindingError<'p, 'a>>,
) -> bool {
    &&& result.is_ok() <==> parameters_match(body.signature, values)
    &&& match result {
        Ok(frame) => frame.body_model() == body && frame.parameter_values_model() == values,
        Err(ScalarBindingError::Rank) => false,
        Err(ScalarBindingError::Arity { source, span, expected_count, found_count }) => {
            &&& source == body.source && span == body.signature.span
            &&& expected_count == body.signature.parameters@.len() && found_count == values.len() && found_count != expected_count
        }
        Err(ScalarBindingError::Type { source, span, parameter, expected_type, found_type }) => {
            &&& values.len() == body.signature.parameters@.len()
            &&& parameter < values.len()
            &&& source == body.source && span == body.signature.parameters@[parameter as int].ty.span
            &&& expected_type == body.signature.parameters@[parameter as int].ty.ty
            &&& found_type == values[parameter as int].type_model()
            &&& !scalar_fits(values[parameter as int], expected_type)
            &&& forall|i: int| 0 <= i < parameter ==>
                scalar_fits(#[trigger] values[i], body.signature.parameters@[i].ty.ty)
        }
    }
}

fn bind<'p, 'a>(body: DefnEvaluationBody<'p, 'a>, values: Vec<ScalarValue>)
    -> (result: Result<ScalarCallFrame<'p, 'a>, ScalarBindingError<'p, 'a>>)
    requires body.at < body.forms@.len(),
        form_spans_valid(body.source.text_model(), body.forms@, body.source.text_model().spec_bytes().len() as int),
    ensures binding_matches(body, values@, result),
{
    let params = &body.signature.parameters;
    if values.len() != params.len() {
        let span = &body.signature.span;
        return Err(ScalarBindingError::Arity {
            source: body.source, span: span.start..span.end, expected_count: params.len(), found_count: values.len(),
        });
    }
    let mut i = 0;
    while i < values.len()
        invariant
            i <= values@.len() == params@.len(),
            params@ == body.signature.parameters@,
            forall|j: int| 0 <= j < i ==> scalar_fits(#[trigger] values@[j], params@[j].ty.ty),
        decreases values@.len() - i,
    {
        let param = &params[i].ty;
        let value = values[i];
        if !scalar_matches(value, param.ty) {
            return Err(ScalarBindingError::Type {
                source: body.source, span: param.span.start..param.span.end, parameter: i,
                expected_type: param.ty, found_type: value.builtin_type(),
            });
        }
        i += 1;
    }
    Ok(ScalarCallFrame { body, values })
}

/// 指定した順位の本体に対して、仮引数束縛の結果が対応することを表す。
pub open spec fn binding_at_rank_matches<'p, 'a>(
    plan: &DefnCallPlan<'p, 'a>, rank: usize, values: Seq<ScalarValue>,
    result: Result<ScalarCallFrame<'p, 'a>, ScalarBindingError<'p, 'a>>,
) -> bool {
    match result {
        Ok(frame) => {
            let body = frame.body_model();
            &&& plan.body_matches_at_rank(rank, body)
            &&& frame.parameter_values_model() == values
            &&& parameters_match(body.signature, values)
        }
        Err(ScalarBindingError::Rank) => rank >= plan.order_model().len() || !plan.order_nodes_valid()
            || plan.project_model().indexed_defn(plan.order_model()[rank as int].file,
                plan.order_model()[rank as int].item).is_none(),
        Err(error) => {
            let defn = plan.order_model()[rank as int];
            let project = plan.project_model();
            &&& rank < plan.order_model().len()
            &&& defn.file < project.sources_model().len()
            &&& exists|body: DefnEvaluationBody<'p, 'a>| #[trigger] binding_matches(body, values, Err(error))
                && *body.source == project.sources_model()[defn.file as int]
                && project.defn_signature_matches_index(defn.file, defn.item, Some(body.signature))
        },
    }
}

/// 補助関数の本体を元の構文木から取得し、指定した値だけを仮引数に束縛する。
///
/// # Errors
///
/// 順位が範囲外か、引数の個数が合わない場合はエラーを返す。
/// 引数の型が合わない場合は、最初に一致しなかった仮引数の型の範囲を返す。
pub fn bind_scalar_call<'p, 'a>(plan: &DefnCallPlan<'p, 'a>, rank: usize, values: Vec<ScalarValue>)
    -> (result: Result<ScalarCallFrame<'p, 'a>, ScalarBindingError<'p, 'a>>)
    ensures binding_at_rank_matches(plan, rank, values@, result),
{
    let Some(body) = plan.body_at_rank(rank) else { return Err(ScalarBindingError::Rank); };
    bind(body, values)
}

}
