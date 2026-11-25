//! 式の位置ごとの型環境を保ちながら、期待型に照らして検査する。

use super::*;

verus! {

spec fn scoped_step_model<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request,
) -> Result<(CheckStep, Seq<TypeBinding>), ExpressionCheckFailure<'a>> {
    if shape(source, forms, request.at) == Ok(Expression::Let) {
        match let_structure(source, forms, request.at) {
            Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Let(error))),
            Ok((rows, body)) => match binding_types(source, forms, env, rows, 0, env) {
                Err(error) => Err(error),
                Ok(extended) => Ok((CheckStep::One(Request {
                    at: body,
                    expected: request.expected,
                    list: None,
                }), extended)),
            },
        }
    } else {
        match step_model(source, forms, env, request) {
            Err(error) => Err(error),
            Ok(step) => Ok((step, env)),
        }
    }
}

#[verifier::opaque]
pub(super) closed spec fn scoped_check<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request,
) -> BodyVerdict<'a>
    decreases forms.len() - request.at,
{
    if !request_ready(forms, request) {
        BodyVerdict::Rejected(ExpressionCheckFailure::Deferred(DeferredExpression::Form(0..0)))
    } else {
        let verdict = match scoped_step_model(source, forms, env, request) {
            Err(error) => BodyVerdict::Rejected(error),
            Ok((step, _)) if !step_children_fit(forms, request.at, step) =>
                BodyVerdict::Rejected(ExpressionCheckFailure::Deferred(DeferredExpression::Form(form_span(forms[request.at as int])))),
            Ok((CheckStep::Done, _)) => BodyVerdict::Accepted,
            Ok((CheckStep::One(child), nested)) => scoped_check(source, forms, nested, child),
            Ok((CheckStep::Three(condition, yes, no), nested)) => {
                match scoped_check(source, forms, nested, condition) {
                    BodyVerdict::Rejected(error) => BodyVerdict::Rejected(error),
                    BodyVerdict::Accepted => match scoped_check(source, forms, nested, yes) {
                        BodyVerdict::Rejected(error) => BodyVerdict::Rejected(error),
                        BodyVerdict::Accepted => scoped_check(source, forms, nested, no),
                    },
                }
            }
        };
        match verdict {
            BodyVerdict::Rejected(error) => BodyVerdict::Rejected(error),
            BodyVerdict::Accepted => match remaining_elements(forms, request) {
                Some(next) => scoped_check(source, forms, env, next),
                None => BodyVerdict::Accepted,
            },
        }
    }
}

proof fn ordinary_check_supports_scopes<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request,
)
    requires expression_check(source, forms, env, request) == BodyVerdict::Accepted,
    ensures scoped_check(source, forms, env, request) == BodyVerdict::Accepted,
    decreases forms.len() - request.at,
{
    reveal(expression_check);
    reveal(scoped_check);
    assert(request_ready(forms, request));
    assert(shape(source, forms, request.at) != Ok(Expression::Let));
    let step = step_model(source, forms, env, request)->Ok_0;
    assert(step_children_fit(forms, request.at, step));
    match step {
        CheckStep::Done => {},
        CheckStep::One(child) => ordinary_check_supports_scopes(source, forms, env, child),
        CheckStep::Three(condition, yes, no) => {
            ordinary_check_supports_scopes(source, forms, env, condition);
            ordinary_check_supports_scopes(source, forms, env, yes);
            ordinary_check_supports_scopes(source, forms, env, no);
        }
    }
    if let Some(next) = remaining_elements(forms, request) {
        ordinary_check_supports_scopes(source, forms, env, next);
    }
}

pub(super) proof fn inferred_type_checks_in_scopes<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
)
    requires usable_forms(source, forms), at < forms.len(), inferred_type(source, forms, env, at) == Ok(ty),
    ensures scoped_check(source, forms, env, Request { at, expected: ty, list: None }) == BodyVerdict::Accepted,
{
    super::inference::inferred_type_checks(source, forms, env, at, ty);
    ordinary_check_supports_scopes(source, forms, env, Request { at, expected: ty, list: None });
}

#[derive(Clone, Copy)]
struct ScopedRequest {
    request: Request,
    scope: Scope,
}

#[cfg(verus_only)]
type CheckAt = (Request, Seq<TypeBinding>);

spec fn request_rows(pending: Seq<ScopedRequest>) -> Seq<Request> {
    pending.map_values(|work: ScopedRequest| work.request)
}

spec fn check_rows(parameters: Seq<SignatureParameter>, locals: &LocalScopes, pending: Seq<ScopedRequest>)
    -> Seq<CheckAt>
{
    pending.map_values(|work: ScopedRequest| (work.request, lexical_view(parameters, locals, work.scope)))
}

spec fn known_scopes(locals: &LocalScopes, pending: Seq<ScopedRequest>) -> bool {
    forall|i: int| 0 <= i < pending.len() ==> locals.contains((#[trigger] pending[i]).scope)
}

#[verifier::opaque]
spec fn pending_scoped<'a>(source: &'a str, forms: Seq<Form>, pending: Seq<CheckAt>) -> BodyVerdict<'a>
    decreases pending.len(),
{
    if pending.len() == 0 {
        BodyVerdict::Accepted
    } else {
        let (request, env) = pending.last();
        match scoped_check(source, forms, env, request) {
            BodyVerdict::Rejected(error) => BodyVerdict::Rejected(error),
            BodyVerdict::Accepted => pending_scoped(source, forms, pending.drop_last()),
        }
    }
}

proof fn pushed_checks<'a>(source: &'a str, forms: Seq<Form>, pending: Seq<CheckAt>, work: CheckAt)
    ensures pending_scoped(source, forms, pending.push(work)) == match scoped_check(source, forms, work.1, work.0) {
        BodyVerdict::Rejected(error) => BodyVerdict::Rejected(error),
        BodyVerdict::Accepted => pending_scoped(source, forms, pending),
    },
{
    reveal(pending_scoped);
    assert(pending.push(work).drop_last() =~= pending);
}

proof fn scoped_rejected<'a>(
    source: &'a str, forms: Seq<Form>, pending: Seq<CheckAt>, work: CheckAt, error: ExpressionCheckFailure<'a>,
)
    requires request_ready(forms, work.0), scoped_step_model(source, forms, work.1, work.0) == Err(error),
    ensures pending_scoped(source, forms, pending.push(work)) == BodyVerdict::Rejected(error),
{
    reveal(scoped_check);
    pushed_checks(source, forms, pending, work);
}

spec fn with_peer_check(pending: Seq<CheckAt>, sibling: Option<Request>, env: Seq<TypeBinding>) -> Seq<CheckAt> {
    match sibling {
        Some(next) => pending.push((next, env)),
        None => pending,
    }
}

spec fn inserted_checks(pending: Seq<CheckAt>, step: CheckStep, env: Seq<TypeBinding>) -> Seq<CheckAt> {
    match step {
        CheckStep::Done => pending,
        CheckStep::One(child) => pending.push((child, env)),
        CheckStep::Three(condition, yes, no) => pending.push((no, env)).push((yes, env)).push((condition, env)),
    }
}

proof fn scoped_step_agrees<'a>(
    source: &'a str, forms: Seq<Form>, pending: Seq<CheckAt>, work: CheckAt,
    step: CheckStep, sibling: Option<Request>, nested: Seq<TypeBinding>,
)
    requires request_ready(forms, work.0), step_children_fit(forms, work.0.at, step),
        scoped_step_model(source, forms, work.1, work.0) == Ok((step, nested)),
        sibling == remaining_elements(forms, work.0),
    ensures pending_scoped(source, forms, pending.push(work))
        == pending_scoped(source, forms, inserted_checks(with_peer_check(pending, sibling, work.1), step, nested)),
{
    reveal(scoped_check);
    pushed_checks(source, forms, pending, work);
    if let Some(next) = sibling {
        pushed_checks(source, forms, pending, (next, work.1));
    }
    let before = with_peer_check(pending, sibling, work.1);
    match step {
        CheckStep::Done => {},
        CheckStep::One(child) => {
            pushed_checks(source, forms, before, (child, nested));
        }
        CheckStep::Three(condition, yes, no) => {
            pushed_checks(source, forms, before, (no, nested));
            pushed_checks(source, forms, before.push((no, nested)), (yes, nested));
            pushed_checks(source, forms, before.push((no, nested)).push((yes, nested)), (condition, nested));
        }
    }
}

proof fn scope_extension_preserves_checks(
    parameters: Seq<SignatureParameter>, old: &LocalScopes, new: &LocalScopes, pending: Seq<ScopedRequest>,
)
    requires known_scopes(old, pending),
        forall|scope: Scope| #[trigger] old.contains(scope) ==> new.contains(scope) && new.local_types(scope) == old.local_types(scope),
    ensures known_scopes(new, pending), check_rows(parameters, old, pending) == check_rows(parameters, new, pending),
{
    assert(check_rows(parameters, old, pending) =~= check_rows(parameters, new, pending));
}

fn read_scoped_step<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>],
    locals: &mut LocalScopes<'a>, work: ScopedRequest,
) -> (result: Result<(CheckStep, Scope), ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), work.request.at < forms@.len(), old(locals).contains(work.scope),
    ensures
        match result {
            Err(error) => scoped_step_model(source, forms@, lexical_view(parameters@, old(locals), work.scope), work.request)
                == Err(error),
            Ok((step, scope)) => final(locals).contains(scope)
                && step_children_fit(forms@, work.request.at, step)
                && scoped_step_model(source, forms@, lexical_view(parameters@, old(locals), work.scope), work.request)
                    == Ok((step, lexical_view(parameters@, final(locals), scope))),
        },
        forall|scope: Scope| #[trigger] old(locals).contains(scope) ==>
            final(locals).contains(scope) && final(locals).local_types(scope) == old(locals).local_types(scope),
{
    let at = work.request.at;
    if !matches!(read_shape(source, forms, at), Ok(Expression::Let)) {
        let step = read_check_step(source, forms, parameters, locals, work.scope, work.request)?;
        return Ok((step, work.scope));
    }
    let header = match read_let_structure(source, forms, at) {
        Ok(header) => header,
        Err(error) => return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Let(error))),
    };
    let extended = read_binding_types(source, forms, parameters, locals,
        work.scope, header.bindings.as_slice(), at, header.body)?;
    proof { super::super::forms::child_stays_inside(forms@, at, header.body); }
    Ok((CheckStep::One(Request { at: header.body, expected: work.request.expected, list: None }), extended))
}

fn push_scoped_work<'a>(
    _parameters: &[SignatureParameter<'a>], _locals: &LocalScopes<'a>, pending: &mut Vec<ScopedRequest>, work: ScopedRequest,
)
    requires known_scopes(_locals, old(pending)@), _locals.contains(work.scope),
    ensures known_scopes(_locals, final(pending)@),
        request_rows(final(pending)@) == request_rows(old(pending)@).push(work.request),
        check_rows(_parameters@, _locals, final(pending)@) == check_rows(_parameters@, _locals, old(pending)@)
            .push((work.request, lexical_view(_parameters@, _locals, work.scope))),
{
    let ghost before = pending@;
    pending.push(work);
    assert(request_rows(pending@) =~= request_rows(before).push(work.request));
    assert(check_rows(_parameters@, _locals, pending@) =~= check_rows(_parameters@, _locals, before)
        .push((work.request, lexical_view(_parameters@, _locals, work.scope))));
}

pub(super) fn check_scoped_expression<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], at: usize, ty: TypeShape,
) -> (result: BodyVerdict<'a>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures result == scoped_check(source, forms@, environment_view(parameters@), Request { at, expected: ty, list: None }),
{
    let mut locals = LocalScopes::new();
    let start = Request { at, expected: ty, list: None };
    let _end = subtree_end(forms, at);
    let _size = forms.len();
    let mut pending = Vec::new();
    push_scoped_work(parameters, &locals, &mut pending, ScopedRequest { request: start, scope: None });
    proof {
        assert(request_rows(Seq::<ScopedRequest>::empty()) =~= Seq::<Request>::empty());
        assert(check_rows(parameters@, &locals, Seq::<ScopedRequest>::empty()) =~= Seq::<CheckAt>::empty());
        assert(lexical_view(parameters@, &locals, None) =~= environment_view(parameters@));
        assert(request_ready(forms@, start)) by {
            assert(complete_list_indices(forms@));
            if let Form::List { end, .. } = forms@[at as int] {
                assert(at < end <= forms@.len());
            }
            assert(at < _end <= _size);
            assert(_end == subtree_limit(forms@, at) && _end == request_limit(forms@, start));
        };
        append_ready(forms@, Seq::empty(), start);
        pushed_checks(source, forms@, Seq::empty(), (start, environment_view(parameters@)));
        reveal(pending_scoped);
    }
    while pending.len() != 0
        invariant
            usable_forms(source, forms@),
            start == (Request { at, expected: ty, list: None }),
            known_scopes(&locals, pending@),
            requests_ready(forms@, request_rows(pending@)),
            pending_scoped(source, forms@, check_rows(parameters@, &locals, pending@))
                == scoped_check(source, forms@, environment_view(parameters@), start),
        decreases forms@.len() - pending_first(forms@, request_rows(pending@)),
    {
        let ghost old_arena = locals;
        let ghost before = pending@;
        let Some(work) = pending.pop() else { unreachable!() };
        let ghost request_stack = request_rows(pending@);
        let ghost checks = check_rows(parameters@, &locals, pending@);
        let ghost env = lexical_view(parameters@, &locals, work.scope);
        proof {
            assert(before =~= pending@.push(work));
            assert(request_rows(before) =~= request_stack.push(work.request));
            assert(check_rows(parameters@, &locals, before) =~= checks.push((work.request, env)));
            assert(pending_scoped(source, forms@, checks.push((work.request, env)))
                == scoped_check(source, forms@, environment_view(parameters@), start));
            assert(known_scopes(&locals, pending@)) by {
                assert forall|i: int| 0 <= i < pending@.len() implies locals.contains((#[trigger] pending@[i]).scope) by {
                    assert(pending@[i] == before[i]);
                };
            };
            assert(locals.contains(work.scope));
        }
        let (step, scope) = match read_scoped_step(source, forms, parameters, &mut locals, work) {
            Err(error) => {
                proof { scoped_rejected(source, forms@, checks, (work.request, env), error); }
                return BodyVerdict::Rejected(error);
            }
            Ok(result) => result,
        };
        let sibling = read_remaining_elements(forms, work.request);
        let ghost nested = lexical_view(parameters@, &locals, scope);
        proof {
            scope_extension_preserves_checks(parameters@, &old_arena, &locals, pending@);
            assert(lexical_view(parameters@, &locals, work.scope) == env);
            scoped_step_agrees(source, forms@, checks, (work.request, env), step, sibling, nested);
            step_advances(forms@, request_stack, work.request, step, sibling);
        }
        // 次の要素は今の環境で検査し、`let` の本体には拡張した環境を渡す。
        if let Some(next) = sibling {
            push_scoped_work(parameters, &locals, &mut pending, ScopedRequest { request: next, scope: work.scope });
        }
        match step {
            CheckStep::Done => {},
            CheckStep::One(child) => {
                push_scoped_work(parameters, &locals, &mut pending, ScopedRequest { request: child, scope });
            }
            CheckStep::Three(condition, yes, no) => {
                push_scoped_work(parameters, &locals, &mut pending, ScopedRequest { request: no, scope });
                push_scoped_work(parameters, &locals, &mut pending, ScopedRequest { request: yes, scope });
                push_scoped_work(parameters, &locals, &mut pending, ScopedRequest { request: condition, scope });
            }
        }
    }
    proof {
        assert(check_rows(parameters@, &locals, pending@) =~= Seq::<CheckAt>::empty());
        reveal(pending_scoped);
    }
    BodyVerdict::Accepted
}

}
