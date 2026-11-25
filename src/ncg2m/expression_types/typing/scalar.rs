//! スカラー評価で扱う構文から、型検査が得た型と束縛を取り出す。

use super::*;

mod declared_progress;
pub(in crate::ncg2m::expression_types) use declared_progress::{accepted_call_has_entry, call_preserves_checked_types};

verus! {

/// 評価器が値を直接求める名前、真偽値、整数のアトムを表す。
pub open spec fn scalar_atom_at(forms: Seq<Form>, at: usize) -> bool {
    at < forms.len() && forms[at as int] matches Form::Atom {
        kind: AtomKind::Name | AtomKind::Natural | AtomKind::NegativeInteger, ..
    }
}

/// 真偽値、整数、仮引数の参照と、それらで構成した条件式を表す。
#[verifier::opaque]
pub open spec fn local_scalar_fragment(source: &str, forms: Seq<Form>, at: usize) -> bool
    decreases forms.len() - at,
{
    scalar_atom_at(forms, at) || match conditional_positions(source, forms, at) {
        Some((condition, yes, no)) if at < condition < yes < no < forms.len() =>
            local_scalar_fragment(source, forms, condition) && local_scalar_fragment(source, forms, yes)
                && local_scalar_fragment(source, forms, no),
        _ => false,
    }
}

/// 元の構文木にある式が、仮引数だけを環境として期待型で検査を通ることを表す。
///
/// 宣言呼び出しの署名を渡さずに型検査する。仮引数の名前と型は元の署名を使う。
pub closed spec fn local_scalar_site_is_typed(
    source: &str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, at: usize, expected: DataType,
) -> bool {
    &&& expected.list_depth == 0
    &&& (expected.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
    &&& typed_body(source, forms, environment_view(parameters), at, type_shape(expected)) == BodyVerdict::Accepted
}

proof fn parameter_type_origin(
    parameters: Seq<SignatureParameter>, word: Seq<u8>, from: nat, ty: TypeShape,
)
    requires parameter_type(environment_view(parameters), word, from) == Some(ty),
    ensures exists|i: int| from <= i < parameters.len()
        && (#[trigger] parameters[i]).name.spec_bytes() == word && type_shape(parameters[i].ty.ty) == ty
        && (forall|j: int| from <= j < i ==> (#[trigger] parameters[j]).name.spec_bytes() != word),
    decreases parameters.len() - from,
{
    let env = environment_view(parameters);
    reveal_with_fuel(parameter_type, 2);
    assert(from < parameters.len());
    assert(env[from as int] == (parameters[from as int].name.spec_bytes(), type_shape(parameters[from as int].ty.ty)));
    if env[from as int].0 != word {
        parameter_type_origin(parameters, word, from + 1, ty);
        let i = choose|i: int| from + 1 <= i < parameters.len()
            && (#[trigger] parameters[i]).name.spec_bytes() == word && type_shape(parameters[i].ty.ty) == ty
            && (forall|j: int| from + 1 <= j < i ==> (#[trigger] parameters[j]).name.spec_bytes() != word);
        assert forall|j: int| from <= j < i implies (#[trigger] parameters[j]).name.spec_bytes() != word by {};
    }
}

pub(in crate::ncg2m) proof fn scalar_atom_type_origin(
    source: &str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, at: usize, expected: DataType,
)
    requires local_scalar_site_is_typed(source, forms, parameters, at, expected),
        scalar_atom_at(forms, at),
    ensures match forms[at as int] {
        Form::Atom { kind: AtomKind::Name, .. } => {
            let word = spelling(source, forms[at as int]);
            if word == "true".spec_bytes() || word == "false".spec_bytes() {
                expected == (DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 })
            } else {
                exists|i: int| 0 <= i < parameters.len()
                    && (#[trigger] parameters[i]).name.spec_bytes() == word && parameters[i].ty.ty == expected
                    && (forall|j: int| 0 <= j < i ==> (#[trigger] parameters[j]).name.spec_bytes() != word)
            }
        },
        _ => expected.atom matches DataTypeAtom::Builtin(BuiltinDataType::Integer(ty)) && expected.list_depth == 0
            && forall|result: Result<IntegerValue, IntegerLiteralError>|
                #[trigger] integer_literal_matches(spelling(source, forms[at as int]), Some(ty), result) ==> result.is_ok(),
    },
{
    reveal(typed_expression);
    let word = spelling(source, forms[at as int]);
    let env = environment_view(parameters);
    let expected_shape = type_shape(expected);
    let request = Request { at, expected: expected_shape, list: None };
    let span = form_span(forms[at as int]);
    assert(step_model(source, forms, env, request).is_ok());
    if forms[at as int] matches Form::Atom { kind: AtomKind::Name, .. } {
        if !bool_word(word) {
            let ty = parameter_type(env, word, 0)->Some_0;
            assert(parameter_type(env, word, 0) == Some(ty));
            assert(ty == expected_shape);
            parameter_type_origin(parameters, word, 0, ty);
            let i = choose|i: int| 0 <= i < parameters.len()
                && (#[trigger] parameters[i]).name.spec_bytes() == word && type_shape(parameters[i].ty.ty) == ty
                && (forall|j: int| 0 <= j < i ==> (#[trigger] parameters[j]).name.spec_bytes() != word);
            assert(parameters[i].ty.ty == expected);
        }
    } else {
        let ty = expected.atom->Builtin_0->Integer_0;
        assert(literal_check(word, ty, span).is_ok());
        assert forall|result: Result<IntegerValue, IntegerLiteralError>|
            #[trigger] integer_literal_matches(word, Some(ty), result) implies result.is_ok() by {
            let chosen = choose|r: Result<IntegerValue, IntegerLiteralError>| integer_literal_matches(word, Some(ty), r);
            assert(chosen == result);
        };
    }
}

pub(in crate::ncg2m::expression_types) proof fn checked_if_keeps_child_types(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, parameters: Seq<SignatureParameter>,
    at: usize, expected: DataType, condition: usize, yes: usize, no: usize,
)
    requires
        typed_body_with_calls(calls, source, forms, environment_view(parameters), at, type_shape(expected))
            == BodyVerdict::Accepted,
        conditional_positions(source, forms, at) == Some((condition, yes, no)),
    ensures
        typed_body_with_calls(calls, source, forms, environment_view(parameters), condition,
            scalar_type(BuiltinDataType::Bool)) == BodyVerdict::Accepted,
        typed_body_with_calls(calls, source, forms, environment_view(parameters), yes, type_shape(expected))
            == BodyVerdict::Accepted,
        typed_body_with_calls(calls, source, forms, environment_view(parameters), no, type_shape(expected))
            == BodyVerdict::Accepted,
{
    reveal(typed_expression);
    let env = environment_view(parameters);
    let ty = type_shape(expected);
    let bool_ty = scalar_type(BuiltinDataType::Bool);
    assert(shape(source, forms, at) == Ok(Expression::Conditional { condition, yes, no }));
    assert(step_model(source, forms, env, Request { at, expected: ty, list: None }) == Ok(CheckStep::Three(
        Request { at: condition, expected: bool_ty, list: None },
        Request { at: yes, expected: ty, list: None },
        Request { at: no, expected: ty, list: None },
    )));
}

pub(in crate::ncg2m) proof fn scalar_conditional_child_types(
    source: &str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, at: usize, expected: DataType,
    condition: usize, yes: usize, no: usize,
)
    requires local_scalar_site_is_typed(source, forms, parameters, at, expected),
        conditional_positions(source, forms, at) == Some((condition, yes, no)),
    ensures
        local_scalar_site_is_typed(source, forms, parameters, condition,
            DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 }),
        local_scalar_site_is_typed(source, forms, parameters, yes, expected),
        local_scalar_site_is_typed(source, forms, parameters, no, expected),
{
    checked_if_keeps_child_types(Seq::empty(), source, forms, parameters, at, expected, condition, yes, no);
}

proof fn local_expression_needs_no_call_types(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, expected: TypeShape,
)
    requires local_scalar_fragment(source, forms, at),
        typed_expression(calls, source, forms, env, Request { at, expected, list: None }, Goal::Check(expected)).is_ok(),
    ensures typed_expression(Seq::empty(), source, forms, env, Request { at, expected, list: None }, Goal::Check(expected)).is_ok(),
    decreases forms.len() - at,
{
    reveal(local_scalar_fragment);
    reveal(typed_expression);
    if scalar_atom_at(forms, at) {
        assert(shape(source, forms, at).is_ok());
        assert(applicable_call(calls, source, forms, at).is_none());
        assert(applicable_call(Seq::empty(), source, forms, at).is_none());
    } else {
        let (condition, yes, no) = conditional_positions(source, forms, at)->Some_0;
        let boolean = scalar_type(BuiltinDataType::Bool);
        assert(at < condition < yes < no < forms.len());
        assert(shape(source, forms, at) == Ok(Expression::Conditional { condition, yes, no }));
        local_expression_needs_no_call_types(calls, source, forms, env, condition, boolean);
        local_expression_needs_no_call_types(calls, source, forms, env, yes, expected);
        local_expression_needs_no_call_types(calls, source, forms, env, no, expected);
    }
}

// 呼び出し表を使わない構文では、同じ環境と期待型の局所型判断を得る。
pub(in crate::ncg2m::expression_types) proof fn checked_local_body_ignores_call_types(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, body: usize,
    checked: DefnSignature, actual: DefnSignature,
)
    requires
        same_defn_signature(checked, actual),
        actual.result_type.ty.list_depth == 0,
        actual.result_type.ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)),
        local_scalar_fragment(source, forms, body),
        typed_body_with_calls(calls, source, forms, environment_view(checked.parameters@),
            body, type_shape(checked.result_type.ty)) == BodyVerdict::Accepted,
    ensures local_scalar_site_is_typed(source, forms, actual.parameters@, body, actual.result_type.ty),
{
    signature_environments_agree(checked, actual);
    let env = environment_view(checked.parameters@);
    let expected = type_shape(checked.result_type.ty);
    local_expression_needs_no_call_types(calls, source, forms, env, body, expected);
}


}
