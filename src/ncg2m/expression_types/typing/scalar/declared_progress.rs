//! 型検査で受理した宣言呼び出しから、署名の戻り型と各引数の型判断を得る。

use super::*;
use super::super::super::named_call::call_signature_types_match;

verus! {

spec fn checked_argument_at(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, env: Seq<TypeBinding>,
    entry: CallTypeEntry, slot: nat,
) -> bool {
    let arg = entry.arguments@[slot as int];
    typed_expression(calls, source, forms, env,
        Request { at: arg.at, expected: arg.expected, list: None }, Goal::Check(arg.expected)).is_ok()
}

proof fn checked_call_arguments_step(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, env: Seq<TypeBinding>, entry: CallTypeEntry, at: nat,
)
    requires canonical_call(forms, entry), at < entry.arguments@.len(),
        typed_call_arguments(calls, source, forms, env, entry, at).is_ok(),
    ensures
        checked_argument_at(calls, source, forms, env, entry, at),
        typed_call_arguments(calls, source, forms, env, entry, at + 1).is_ok(),
{
    let arg = entry.arguments@[at as int];
    assert(entry.at < arg.at < subtree_limit(forms, arg.at) <= subtree_limit(forms, entry.at));
    if at + 1 < entry.arguments@.len() {
        assert(subtree_limit(forms, arg.at) == entry.arguments@[(at + 1) as int].at);
    }
    call_argument_equation(calls, source, forms, env, entry, at);
}

proof fn call_argument_was_checked(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, env: Seq<TypeBinding>,
    entry: CallTypeEntry, next: nat, slot: nat,
)
    requires
        canonical_call(forms, entry), next <= slot < entry.arguments@.len(),
        typed_call_arguments(calls, source, forms, env, entry, next).is_ok(),
    ensures checked_argument_at(calls, source, forms, env, entry, slot),
    decreases slot - next,
{
    checked_call_arguments_step(calls, source, forms, env, entry, next);
    if next < slot {
        call_argument_was_checked(calls, source, forms, env, entry, next + 1, slot);
    }
}

proof fn positioned_entry_is_selected(calls: Seq<CallTypeEntry>, at: usize, index: usize)
    requires call_entries_sorted(calls), index < calls.len(), calls[index as int].at == at,
    ensures call_entry_at(calls, at) == Some(index),
{
    assert(exists|i: usize| i < calls.len() && (#[trigger] calls[i as int]).at == at);
    let chosen = call_entry_at(calls, at)->Some_0;
    assert(chosen < calls.len() && calls[chosen as int].at == at);
    if chosen < index { assert(calls[chosen as int].at < calls[index as int].at); }
    if index < chosen { assert(calls[index as int].at < calls[chosen as int].at); }
}

proof fn typed_named_root_has_typed_declaration(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, env: Seq<TypeBinding>,
    body: usize, index: usize, expected: TypeShape,
)
    requires
        body < forms.len(), applicable_call(calls, source, forms, body) == Some(index),
        typed_expression(calls, source, forms, env, Request { at: body, expected, list: None }, Goal::Check(expected)).is_ok(),
    ensures typed_declared_call(calls, source, forms, env, body, Goal::Check(expected), index).is_ok(),
{
    let request = Request { at: body, expected, list: None };
    named_call_equation(calls, source, forms, env, request, Goal::Check(expected), index);
    assert(remaining_elements(forms, request).is_none());
}

proof fn accepted_declaration_keeps_signature(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, env: Seq<TypeBinding>,
    body: usize, index: usize, expected: TypeShape,
)
    requires
        index < calls.len(), calls[index as int].at == body,
        canonical_call(forms, calls[index as int]),
        typed_declared_call(calls, source, forms, env, body, Goal::Check(expected), index).is_ok(),
    ensures
        calls[index as int].result == expected,
        typed_call_arguments(calls, source, forms, env, calls[index as int], 0).is_ok(),
{
    let entry = calls[index as int];
    if entry.arguments@.len() > 0 {
        assert(entry.arguments@[0].at == body + 2);
    }
    declared_call_equation(calls, source, forms, env, body, Goal::Check(expected), index);
    let actual = typed_declared_call(calls, source, forms, env, body, Goal::Check(expected), index);
    let arguments = typed_call_arguments(calls, source, forms, env, entry, 0);
    let result = declared_call_result(Goal::Check(expected), entry.result, form_span(forms[body as int]));
    assert(result == Ok(expected));
    assert(actual == attach_call_type(arguments, expected));
    if let Err(error) = arguments {
        assert(actual == Err(error));
        assert(false);
    }
    assert(arguments.is_ok());
}

proof fn accepted_call_keeps_signature(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, env: Seq<TypeBinding>,
    body: usize, index: usize, expected: TypeShape,
)
    requires
        call_entries_fit(forms, calls), index < calls.len(), calls[index as int].at == body,
        shape(source, forms, body) == Err(ExpressionCheckFailure::Deferred(
            DeferredExpression::Form(form_span(forms[body as int])),
        )),
        typed_expression(calls, source, forms, env, Request { at: body, expected, list: None }, Goal::Check(expected)).is_ok(),
    ensures
        calls[index as int].result == expected,
        typed_call_arguments(calls, source, forms, env, calls[index as int], 0).is_ok(),
{
    positioned_entry_is_selected(calls, body, index);
    typed_named_root_has_typed_declaration(calls, source, forms, env, body, index, expected);
    accepted_declaration_keeps_signature(calls, source, forms, env, body, index, expected);
}

// 根の宣言呼び出しで確認した型を、元の引数位置と呼び出し先の署名に結び付ける。
pub(in crate::ncg2m::expression_types) proof fn root_call_preserves_checked_types(
    calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>,
    caller: DefnSignature, callee: DefnSignature, body: usize, index: usize,
)
    requires
        call_entries_fit(forms, calls), index < calls.len(),
        calls[index as int].at == body,
        shape(source, forms, body) == Err(ExpressionCheckFailure::Deferred(
            DeferredExpression::Form(form_span(forms[body as int])),
        )),
        call_signature_types_match(calls[index as int], callee),
        typed_body_with_calls(calls, source, forms, environment_view(caller.parameters@),
            body, type_shape(caller.result_type.ty)) == BodyVerdict::Accepted,
    ensures
        type_shape(caller.result_type.ty) == type_shape(callee.result_type.ty),
        forall|slot: int| 0 <= slot < calls[index as int].arguments@.len() ==> {
            let arg = #[trigger] calls[index as int].arguments@[slot];
            let expected = callee.parameters@[slot].ty.ty;
            local_scalar_fragment(source, forms, arg.at) && expected.list_depth == 0
                && (expected.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
                ==> local_scalar_site_is_typed(source, forms, caller.parameters@, arg.at, expected)
        },
{
    let entry = calls[index as int];
    let env = environment_view(caller.parameters@);
    let expected = type_shape(caller.result_type.ty);
    accepted_call_keeps_signature(calls, source, forms, env, body, index, expected);
    assert forall|slot: int| 0 <= slot < entry.arguments@.len() implies {
        let arg = #[trigger] entry.arguments@[slot];
        let ty = callee.parameters@[slot].ty.ty;
        local_scalar_fragment(source, forms, arg.at) && ty.list_depth == 0
            && (ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
            ==> local_scalar_site_is_typed(source, forms, caller.parameters@, arg.at, ty)
    } by {
        call_argument_was_checked(calls, source, forms, env, entry, 0, slot as nat);
        let arg = entry.arguments@[slot];
        let ty = callee.parameters@[slot].ty.ty;
        if local_scalar_fragment(source, forms, arg.at) && ty.list_depth == 0
            && (ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_))) {
            assert(checked_argument_at(calls, source, forms, env, entry, slot as nat));
            local_expression_needs_no_call_types(calls, source, forms, env, arg.at, arg.expected);
        }
    };
}
}
