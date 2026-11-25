//! 期待型がない式の型を求め、最初に見つかった違反や保留を返す。

use super::*;

verus! {

#[derive(Clone, Copy)]
enum InferenceFrame {
    Yes { _at: usize, no: usize },
    No { at: usize, ty: TypeShape },
    List { at: usize, owner: usize, element: Option<TypeShape> },
}

spec fn frame_start(frame: InferenceFrame) -> usize {
    match frame {
        InferenceFrame::Yes { _at: at, .. } | InferenceFrame::No { at, .. } | InferenceFrame::List { at, .. } => at,
    }
}

spec fn frame_limit(forms: Seq<Form>, frame: InferenceFrame) -> usize {
    match frame {
        InferenceFrame::Yes { no, .. } => subtree_limit(forms, no),
        InferenceFrame::No { at, .. } => subtree_limit(forms, at),
        InferenceFrame::List { owner, .. } => subtree_limit(forms, owner),
    }
}

spec fn frame_valid(forms: Seq<Form>, frame: InferenceFrame) -> bool {
    let at = frame_start(frame);
    &&& at < subtree_limit(forms, at) <= frame_limit(forms, frame) <= forms.len()
    &&& match frame {
        InferenceFrame::Yes { no, .. } => subtree_limit(forms, at) <= no < frame_limit(forms, frame),
        InferenceFrame::No { .. } => true,
        InferenceFrame::List { owner, .. } => owner < at && forms[owner as int] is List,
    }
}

spec fn check_at<'a>(source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, expected: TypeShape)
    -> BodyVerdict<'a>
{
    expression_check(source, forms, env, Request { at, expected, list: None })
}

spec fn same_type_at<'a>(forms: Seq<Form>, at: usize, expected: TypeShape, actual: TypeShape)
    -> Result<TypeShape, ExpressionCheckFailure<'a>>
{
    match types_agree(expected, actual, form_span(forms[at as int])) {
        Ok(()) => Ok(expected),
        Err(error) => Err(error),
    }
}

spec fn pending_type<'a>(span: Range<usize>) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span)))
}

spec fn list_type<'a>(element: TypeShape, span: Range<usize>) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    if element.list_depth < usize::MAX {
        Ok(TypeShape { builtin: element.builtin, list_depth: (element.list_depth + 1) as usize })
    } else {
        pending_type(span)
    }
}

#[verifier::opaque]
pub(super) closed spec fn inferred_type<'a>(source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize)
    -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - at, 0nat,
{
    if at >= forms.len() {
        pending_type(0..0)
    } else {
        let span = form_span(forms[at as int]);
        match shape(source, forms, at) {
            Ok(Expression::Conditional { condition, yes, no }) => {
                if !(at < condition < yes < no < forms.len()) {
                    pending_type(span)
                } else {
                    match check_at(source, forms, env, condition, scalar_type(BuiltinDataType::Bool)) {
                        BodyVerdict::Rejected(error) => Err(error),
                        BodyVerdict::Accepted => match inferred_type(source, forms, env, yes) {
                            Err(error) => Err(error),
                            Ok(ty) => match inferred_type(source, forms, env, no) {
                                Err(error) => Err(error),
                                Ok(actual) => same_type_at(forms, no, ty, actual),
                            },
                        },
                    }
                }
            }
            Ok(Expression::List) if at + 2 < subtree_limit(forms, at) <= forms.len() => {
                let first = (at + 2) as usize;
                infer_elements(source, forms, env, at, first, None)
            }
            _ => match synthesized_type(source, forms, env, at) {
                Err(error) => Err(error),
                Ok(ty) => match check_at(source, forms, env, at, ty) {
                    BodyVerdict::Accepted => Ok(ty),
                    BodyVerdict::Rejected(error) => Err(error),
                },
            }
        }
    }
}

#[verifier::opaque]
spec fn infer_elements<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize, earlier: Option<TypeShape>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - at, 1nat,
{
    let end = subtree_limit(forms, owner);
    if !(at < end <= forms.len()) {
        pending_type(form_span(forms[owner as int]))
    } else {
        match inferred_type(source, forms, env, at) {
            Err(error) => Err(error),
            Ok(actual) => extend_list_type(source, forms, env, owner, at, earlier, actual),
        }
    }
}

spec fn extend_list_type<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize,
    at: usize, earlier: Option<TypeShape>, actual: TypeShape,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - at, 0nat,
{
    let end = subtree_limit(forms, owner);
    let agreed = match earlier {
        Some(expected) => same_type_at(forms, at, expected, actual),
        None => Ok(actual),
    };
    match agreed {
        Err(error) => Err(error),
        Ok(ty) => {
            let next = subtree_limit(forms, at);
            if next == end {
                list_type(ty, form_span(forms[owner as int]))
            } else if at < next < end <= forms.len() {
                infer_elements(source, forms, env, owner, next, Some(ty))
            } else {
                pending_type(form_span(forms[owner as int]))
            }
        }
    }
}

spec fn after_frame<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, frame: InferenceFrame,
    result: Result<TypeShape, ExpressionCheckFailure<'a>>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match result {
        Err(error) => Err(error),
        Ok(ty) => match frame {
            InferenceFrame::Yes { no, .. } => match inferred_type(source, forms, env, no) {
                Err(error) => Err(error),
                Ok(actual) => same_type_at(forms, no, ty, actual),
            },
            InferenceFrame::No { at, ty: expected } => same_type_at(forms, at, expected, ty),
            InferenceFrame::List { at, owner, element } => extend_list_type(source, forms, env, owner, at, element, ty),
        }
    }
}

proof fn element_frame_agrees<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize,
    at: usize, earlier: Option<TypeShape>,
)
    requires owner < forms.len(), at < subtree_limit(forms, owner) <= forms.len(),
    ensures infer_elements(source, forms, env, owner, at, earlier)
        == after_frame(source, forms, env, InferenceFrame::List { at, owner, element: earlier },
            inferred_type(source, forms, env, at)),
{
    reveal_with_fuel(inferred_type, 2);
    reveal_with_fuel(infer_elements, 2);
    reveal_with_fuel(extend_list_type, 2);
    let result = inferred_type(source, forms, env, at);
    match result {
        Err(error) => {
            assert(infer_elements(source, forms, env, owner, at, earlier) == Err(error));
        }
        Ok(actual) => {
            assert(infer_elements(source, forms, env, owner, at, earlier)
                == extend_list_type(source, forms, env, owner, at, earlier, actual));
        }
    }
}

proof fn checked_siblings_agree<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize, expected: TypeShape,
)
    requires
        request_ready(forms, Request { at, expected, list: Some(owner) }),
        check_at(source, forms, env, at, expected) == BodyVerdict::Accepted,
        remaining_elements(forms, Request { at, expected, list: Some(owner) }) matches Some(next)
            ==> expression_check(source, forms, env, next) == BodyVerdict::Accepted,
    ensures expression_check(source, forms, env, Request { at, expected, list: Some(owner) }) == BodyVerdict::Accepted,
{
    reveal(expression_check);
    let alone = Request { at, expected, list: None };
    let with_siblings = Request { at, expected, list: Some(owner) };
    assert(request_ready(forms, alone) && remaining_elements(forms, alone).is_none());
    assert(step_model(source, forms, env, alone) == step_model(source, forms, env, with_siblings));
}

proof fn inferred_list_origin<'a>(source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize)
    requires at < forms.len(), shape(source, forms, at) == Ok(Expression::List),
        at + 2 < subtree_limit(forms, at) <= forms.len(),
    ensures inferred_type(source, forms, env, at)
        == infer_elements(source, forms, env, at, (at + 2) as usize, None),
{
    reveal_with_fuel(inferred_type, 2);
    reveal(infer_elements);
    reveal(extend_list_type);
}

proof fn inferred_if_origin<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
    condition: usize, yes: usize, no: usize,
)
    requires at < forms.len(), inferred_type(source, forms, env, at) == Ok(ty),
        shape(source, forms, at) == Ok(Expression::Conditional { condition, yes, no }),
    ensures at < condition < yes < no < forms.len(),
        check_at(source, forms, env, condition, scalar_type(BuiltinDataType::Bool)) == BodyVerdict::Accepted,
        inferred_type(source, forms, env, yes) == Ok(ty),
        inferred_type(source, forms, env, no) == Ok(ty),
{
    reveal_with_fuel(inferred_type, 2);
    let other = inferred_type(source, forms, env, no)->Ok_0;
    assert(same_type_at(forms, no, ty, other) == Ok(ty) && ty == other);
}

pub(super) proof fn inferred_type_checks<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
)
    requires usable_forms(source, forms), at < forms.len(), inferred_type(source, forms, env, at) == Ok(ty),
    ensures expression_check(source, forms, env, Request { at, expected: ty, list: None }) == BodyVerdict::Accepted,
    decreases forms.len() - at, 0nat,
{
    reveal(expression_check);
    let request = Request { at, expected: ty, list: None };
    match shape(source, forms, at) {
        Ok(Expression::Conditional { condition, yes, no }) => {
            inferred_if_origin(source, forms, env, at, ty, condition, yes, no);
            inferred_type_checks(source, forms, env, yes, ty);
            inferred_type_checks(source, forms, env, no, ty);
            let step = step_model(source, forms, env, request)->Ok_0;
            assert(children3(forms, at) == Some((condition, yes, no)));
            assert(step_children_fit(forms, at, step));
        }
        Ok(Expression::List) if at + 2 < subtree_limit(forms, at) <= forms.len() => {
            let first = (at + 2) as usize;
            inferred_list_origin(source, forms, env, at);
            let element = infer_element_type(source, forms, env, at, first, None, ty);
            assert(list_type(element, form_span(forms[at as int])) == Ok(ty));
            inferred_elements_check(source, forms, env, at, first, None, element, ty);
            super::super::forms::child_stays_inside(forms, at, first);
            assert(step_children_fit(forms, at, step_model(source, forms, env, request)->Ok_0));
        }
        _ => { reveal_with_fuel(inferred_type, 2); },
    }
}

proof fn infer_element_type<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize,
    earlier: Option<TypeShape>, list: TypeShape,
) -> (element: TypeShape)
    requires owner < at < subtree_limit(forms, owner) <= forms.len(),
        infer_elements(source, forms, env, owner, at, earlier) == Ok(list),
    ensures
        inferred_type(source, forms, env, at) == Ok(element),
        earlier matches Some(prior) ==> prior == element,
        list_type(element, form_span(forms[owner as int])) == Ok(list),
    decreases forms.len() - at,
{
    reveal_with_fuel(inferred_type, 2);
    reveal_with_fuel(infer_elements, 2);
    reveal_with_fuel(extend_list_type, 2);
    let item = inferred_type(source, forms, env, at)->Ok_0;
    if let Some(expected) = earlier {
        assert(types_agree(expected, item, form_span(forms[at as int])) == Ok(()));
        assert(expected == item);
    }
    let next = subtree_limit(forms, at);
    if next != subtree_limit(forms, owner) {
        assert(at < next < subtree_limit(forms, owner));
        assert(infer_elements(source, forms, env, owner, next, Some(item)) == Ok(list));
        let later = infer_element_type(source, forms, env, owner, next, Some(item), list);
        assert(later == item);
    }
    item
}

proof fn inferred_elements_check<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize,
    earlier: Option<TypeShape>, element: TypeShape, list: TypeShape,
)
    requires usable_forms(source, forms), owner < at < subtree_limit(forms, owner) <= forms.len(),
        forms[owner as int] is List,
        infer_elements(source, forms, env, owner, at, earlier) == Ok(list),
        list_type(element, form_span(forms[owner as int])) == Ok(list),
    ensures expression_check(source, forms, env, Request { at, expected: element, list: Some(owner) })
        == BodyVerdict::Accepted,
    decreases forms.len() - at, 1nat,
{
    reveal_with_fuel(inferred_type, 2);
    reveal_with_fuel(infer_elements, 2);
    reveal_with_fuel(extend_list_type, 2);
    let item = infer_element_type(source, forms, env, owner, at, earlier, list);
    assert(item == element);
    inferred_type_checks(source, forms, env, at, element);
    super::super::forms::child_stays_inside(forms, owner, at);
    let next = subtree_limit(forms, at);
    if next < subtree_limit(forms, owner) {
        assert(infer_elements(source, forms, env, owner, next, Some(element)) == Ok(list));
        inferred_elements_check(source, forms, env, owner, next, Some(element), element, list);
    }
    checked_siblings_agree(source, forms, env, owner, at, element);
}

#[verifier::opaque]
spec fn remaining_type<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, pending: Seq<InferenceFrame>,
    result: Result<TypeShape, ExpressionCheckFailure<'a>>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases pending.len(),
{
    if pending.len() == 0 {
        result
    } else {
        remaining_type(source, forms, env, pending.drop_last(), after_frame(source, forms, env, pending.last(), result))
    }
}

proof fn added_frame<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, pending: Seq<InferenceFrame>, frame: InferenceFrame,
    result: Result<TypeShape, ExpressionCheckFailure<'a>>,
)
    ensures remaining_type(source, forms, env, pending.push(frame), result)
        == remaining_type(source, forms, env, pending, after_frame(source, forms, env, frame, result)),
{
    reveal(remaining_type);
    assert(pending.push(frame).drop_last() =~= pending);
}

proof fn infer_failure<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, pending: Seq<InferenceFrame>, error: ExpressionCheckFailure<'a>,
)
    ensures remaining_type(source, forms, env, pending, Err(error)) == Err(error),
    decreases pending.len(),
{
    reveal(remaining_type);
    if pending.len() > 0 {
        infer_failure(source, forms, env, pending.drop_last(), error);
    }
}

spec fn frames_cover(forms: Seq<Form>, frames: Seq<InferenceFrame>, at: usize) -> bool {
    &&& forall|i: int| 0 <= i < frames.len() ==> {
        let frame = #[trigger] frames[i];
        frame_valid(forms, frame) && frame_start(frame) <= at < subtree_limit(forms, frame_start(frame))
    }
    &&& forall|i: int, j: int| 0 <= i < j < frames.len() ==>
        frame_limit(forms, #[trigger] frames[j]) <= subtree_limit(forms, frame_start(#[trigger] frames[i]))
}

proof fn add_frame_cover(forms: Seq<Form>, frames: Seq<InferenceFrame>, current: usize, frame: InferenceFrame)
    requires frames_cover(forms, frames, current), frame_valid(forms, frame),
        current < forms.len(),
        current <= frame_start(frame) < frame_limit(forms, frame) <= subtree_limit(forms, current),
        complete_list_indices(forms), nested_list_indices(forms),
    ensures frames_cover(forms, frames.push(frame), frame_start(frame)),
{
    let next = frames.push(frame);
    assert forall|i: int| 0 <= i < next.len() implies {
        let f = #[trigger] next[i];
        frame_valid(forms, f) && frame_start(f) <= frame_start(frame) < subtree_limit(forms, frame_start(f))
    } by {
        if i < frames.len() {
            assert(frames[i] == next[i]);
            inside_frame_extent(forms, frames[i], current);
            assert(frame_limit(forms, frame) <= subtree_limit(forms, frame_start(frames[i])));
        }
    };
    assert forall|i:int, j:int| 0 <= i < j < next.len() implies
        frame_limit(forms, #[trigger] next[j]) <= subtree_limit(forms, frame_start(#[trigger] next[i])) by {
        assert(next[i] == frames[i]);
        if j < frames.len() {
            assert(next[j] == frames[j]);
        } else {
            assert(next[j] == frame);
            inside_frame_extent(forms, frames[i], current);
        }
    };
}

proof fn inside_frame_extent(forms: Seq<Form>, frame: InferenceFrame, current: usize)
    requires
        complete_list_indices(forms), nested_list_indices(forms), frame_valid(forms, frame),
        frame_start(frame) <= current < subtree_limit(forms, frame_start(frame)),
    ensures subtree_limit(forms, current) <= subtree_limit(forms, frame_start(frame)),
{
    let owner = frame_start(frame);
    if owner < current {
        assert(forms[owner as int] is List);
        super::super::forms::child_stays_inside(forms, owner, current);
    }
}

proof fn replace_frame_cover(
    forms: Seq<Form>, frames: Seq<InferenceFrame>, current: usize, old: InferenceFrame, next: InferenceFrame,
)
    requires frames_cover(forms, frames.push(old), current), frame_valid(forms, next),
        subtree_limit(forms, frame_start(old)) <= frame_start(next),
        frame_limit(forms, next) <= frame_limit(forms, old),
    ensures frames_cover(forms, frames.push(next), frame_start(next)), current < frame_start(next),
{
    let before = frames.push(old);
    let after = frames.push(next);
    assert(before[frames.len() as int] == old);
    assert forall|i:int| 0 <= i < after.len() implies {
        let f = #[trigger] after[i];
        frame_valid(forms, f) && frame_start(f) <= frame_start(next) < subtree_limit(forms, frame_start(f))
    } by {
        if i < frames.len() {
            assert(after[i] == before[i]);
            assert(frame_limit(forms, old) <= subtree_limit(forms, frame_start(before[i])));
        }
    };
    assert forall|i:int, j:int| 0 <= i < j < after.len() implies
        frame_limit(forms, #[trigger] after[j]) <= subtree_limit(forms, frame_start(#[trigger] after[i])) by {
        assert(after[i] == before[i]);
        if j < frames.len() { assert(after[j] == before[j]); }
    };
}

proof fn remove_frame_cover(forms: Seq<Form>, frames: Seq<InferenceFrame>, current: usize, last: InferenceFrame)
    requires frames_cover(forms, frames.push(last), current),
    ensures frames_cover(forms, frames, current),
{
    let before = frames.push(last);
    assert forall|i:int| 0 <= i < frames.len() implies {
        let frame = #[trigger] frames[i];
        frame_valid(forms, frame) && frame_start(frame) <= current < subtree_limit(forms, frame_start(frame))
    } by {
        assert(frames[i] == before[i]);
    };
    assert forall|i:int, j:int| 0 <= i < j < frames.len() implies
        frame_limit(forms, #[trigger] frames[j]) <= subtree_limit(forms, frame_start(#[trigger] frames[i])) by {
        assert(frames[i] == before[i] && frames[j] == before[j]);
    };
}

#[derive(Clone, Copy)]
enum InferenceStep {
    Type(TypeShape),
    Descend { at: usize, frame: InferenceFrame },
}

spec fn step_result<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>,
    step: Result<InferenceStep, ExpressionCheckFailure<'a>>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match step {
        Err(error) => Err(error),
        Ok(InferenceStep::Type(ty)) => Ok(ty),
        Ok(InferenceStep::Descend { at, frame }) => after_frame(source, forms, env, frame,
            inferred_type(source, forms, env, at)),
    }
}

fn start_inference<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], locals: &[LocalType<'a>], at: usize,
) -> (result: Result<InferenceStep, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures
        step_result(source, forms@, lexical_view(parameters@, locals@), result)
            == inferred_type(source, forms@, lexical_view(parameters@, locals@), at),
        result matches Ok(InferenceStep::Descend { at: child, frame }) ==>
            frame_valid(forms@, frame) && child == frame_start(frame)
                && at < child < frame_limit(forms@, frame) <= subtree_limit(forms@, at),
{
    reveal_with_fuel(inferred_type, 2);
    let ghost env = lexical_view(parameters@, locals@);
    match read_shape(source, forms, at)? {
        Expression::Conditional { condition, yes, no } => {
            assert(children3(forms@, at) == Some((condition, yes, no)));
            let ty = scalar(BuiltinDataType::Bool);
            if let BodyVerdict::Rejected(error) = check_expression(source, forms, parameters, locals, condition, ty) {
                return Err(error);
            }
            let frame = InferenceFrame::Yes { _at: yes, no };
            assert(after_frame(source, forms@, env, frame, inferred_type(source, forms@, env, yes))
                == inferred_type(source, forms@, env, at));
            Ok(InferenceStep::Descend { at: yes, frame })
        }
        Expression::List if subtree_end(forms, at) - at > 2 => {
            let child = at + 2;
            let frame = InferenceFrame::List { at: child, owner: at, element: None };
            proof {
                assert(at < child < subtree_limit(forms@, at) <= forms@.len());
                super::super::forms::child_stays_inside(forms@, at, child);
                reveal(infer_elements);
                reveal(extend_list_type);
                element_frame_agrees(source, forms@, env, at, child, None);
                assert(inferred_type(source, forms@, env, at) == infer_elements(source, forms@, env, at, child, None));
            }
            return Ok(InferenceStep::Descend { at: child, frame });
        }
        _ => {
            let ty = synthesize_type(source, forms, parameters, locals, at)?;
            if let BodyVerdict::Rejected(error) = check_expression(source, forms, parameters, locals, at, ty) {
                Err(error)
            } else {
                Ok(InferenceStep::Type(ty))
            }
        }
    }
}

fn finish_frame<'a>(
    _source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>], _locals: &[LocalType<'a>],
    frame: InferenceFrame, ty: TypeShape,
) -> (result: Result<InferenceStep, ExpressionCheckFailure<'a>>)
    requires usable_forms(_source, forms@), frame_valid(forms@, frame),
    ensures
        step_result(_source, forms@, lexical_view(_parameters@, _locals@), result)
            == after_frame(_source, forms@, lexical_view(_parameters@, _locals@), frame, Ok(ty)),
        result matches Ok(InferenceStep::Descend { at: next, frame: continuation }) ==>
            frame_valid(forms@, continuation) && next == frame_start(continuation)
                && subtree_limit(forms@, frame_start(frame)) <= next
                && frame_limit(forms@, continuation) <= frame_limit(forms@, frame),
{
    let ghost env = lexical_view(_parameters@, _locals@);
    match frame {
        InferenceFrame::Yes { no, .. } =>
            Ok(InferenceStep::Descend { at: no, frame: InferenceFrame::No { at: no, ty } }),
        InferenceFrame::No { at, ty: expected } => {
            conform(expected, ty, span_of(&forms[at]))?;
            Ok(InferenceStep::Type(expected))
        }
        InferenceFrame::List { at, owner, element } => {
            reveal(inferred_type);
            reveal(infer_elements);
            reveal_with_fuel(extend_list_type, 2);
            let element = if let Some(expected) = element {
                conform(expected, ty, span_of(&forms[at]))?;
                expected
            } else {
                ty
            };
            let next = subtree_end(forms, at);
            let limit = subtree_end(forms, owner);
            if next == limit {
                if element.list_depth == usize::MAX {
                    Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span_of(&forms[owner]))))
                } else {
                    Ok(InferenceStep::Type(TypeShape { builtin: element.builtin, list_depth: element.list_depth + 1 }))
                }
            } else {
                let continuation = InferenceFrame::List { at: next, owner, element: Some(element) };
                proof {
                    super::super::forms::child_stays_inside(forms@, owner, next);
                    element_frame_agrees(_source, forms@, env, owner, next, Some(element));
                    assert(after_frame(_source, forms@, env, frame, Ok(ty))
                        == infer_elements(_source, forms@, env, owner, next, Some(element)));
                }
                return Ok(InferenceStep::Descend { at: next, frame: continuation });
            }
        }
    }
}

pub(super) fn infer_type<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], locals: &[LocalType<'a>], root: usize,
) -> (result: Result<TypeShape, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), root < forms@.len(),
    ensures result == inferred_type(source, forms@, lexical_view(parameters@, locals@), root),
{
    let ghost env = lexical_view(parameters@, locals@);
    let mut at = root;
    let mut pending = Vec::<InferenceFrame>::new();
    proof { reveal(remaining_type); }
    loop
        invariant
            usable_forms(source, forms@), env == lexical_view(parameters@, locals@),
            at < forms@.len(), frames_cover(forms@, pending@, at),
            remaining_type(source, forms@, env, pending@, inferred_type(source, forms@, env, at))
                == inferred_type(source, forms@, env, root),
        decreases forms@.len() - at,
    {
        let mut ty = match start_inference(source, forms, parameters, locals, at) {
            Err(error) => {
                proof { infer_failure(source, forms@, env, pending@, error); }
                return Err(error);
            }
            Ok(InferenceStep::Descend { at: next, frame }) => {
                proof {
                    add_frame_cover(forms@, pending@, at, frame);
                    added_frame(source, forms@, env, pending@, frame, inferred_type(source, forms@, env, next));
                }
                pending.push(frame);
                at = next;
                continue;
            }
            Ok(InferenceStep::Type(ty)) => ty,
        };
        // 型が決まった子の結果を使い、次の子に進むか、親の型を確定する。
        let ghost before = at;
        loop
            invariant_except_break
                before == at,
                remaining_type(source, forms@, env, pending@, Ok(ty)) == inferred_type(source, forms@, env, root),
            invariant
                usable_forms(source, forms@), env == lexical_view(parameters@, locals@),
                at < forms@.len(), frames_cover(forms@, pending@, at),
            ensures
                before < at,
                remaining_type(source, forms@, env, pending@, inferred_type(source, forms@, env, at))
                    == inferred_type(source, forms@, env, root),
            decreases pending@.len(),
        {
            let ghost old = pending@;
            let Some(frame) = pending.pop() else {
                proof { reveal(remaining_type); }
                return Ok(ty);
            };
            proof {
                assert(old =~= pending@.push(frame));
                remove_frame_cover(forms@, pending@, at, frame);
                added_frame(source, forms@, env, pending@, frame, Ok(ty));
            }
            match finish_frame(source, forms, parameters, locals, frame, ty) {
                Err(error) => {
                    proof { infer_failure(source, forms@, env, pending@, error); }
                    return Err(error);
                }
                Ok(InferenceStep::Descend { at: next, frame: successor }) => {
                    proof {
                        replace_frame_cover(forms@, pending@, at, frame, successor);
                        added_frame(source, forms@, env, pending@, successor, inferred_type(source, forms@, env, next));
                    }
                    pending.push(successor);
                    at = next;
                    break;
                }
                Ok(InferenceStep::Type(completed)) => ty = completed,
            }
        }
    }
}

}
