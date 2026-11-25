//! 期待型付きの検査と型合成を、式ごとの型環境で進める。

use super::*;
use super::super::let_syntax::LetHeader;

verus! {

#[derive(Clone, Copy)]
enum Goal {
    Check(TypeShape),
    Infer,
}

spec fn goal_rank(goal: Goal) -> nat {
    match goal { Goal::Check(_) => 0, Goal::Infer => 1 }
}

spec fn unknown_form<'a>(span: Range<usize>) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span)))
}

#[verifier::opaque]
spec fn typed_expression<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, goal: Goal,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - request.at, 2nat, goal_rank(goal),
{
    let at = request.at;
    let span = form_span(forms[at as int]);
    let result = if at >= forms.len() {
        unknown_form(0..0)
    } else if shape(source, forms, at) == Ok(Expression::Let) {
        match let_structure(source, forms, at) {
            Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Let(error))),
            Ok((rows, body)) if at < body < forms.len() => {
                match typed_bindings(source, forms, env, at, body, rows, 0, env) {
                    Err(error) => Err(error),
                    Ok(extended) => {
                        typed_expression(source, forms, extended, Request { at: body, list: None, ..request }, goal)
                    },
                }
            },
            Ok(_) => unknown_form(span),
        }
    } else {
        match goal {
            Goal::Check(expected) => match step_model(source, forms, env, Request { expected, ..request }) {
                Err(error) => Err(error),
                Ok(step) if !step_children_fit(forms, at, step) => unknown_form(span),
                Ok(CheckStep::Done) => Ok(expected),
                Ok(CheckStep::One(child)) => match typed_expression(source, forms, env, child, Goal::Check(child.expected)) {
                    Err(error) => Err(error),
                    Ok(_) => Ok(expected),
                },
                Ok(CheckStep::Three(condition, yes, no)) =>
                    match typed_expression(source, forms, env, condition, Goal::Check(condition.expected)) {
                        Err(error) => Err(error),
                        Ok(_) => match typed_expression(source, forms, env, yes, Goal::Check(yes.expected)) {
                            Err(error) => Err(error),
                            Ok(_) => match typed_expression(source, forms, env, no, Goal::Check(no.expected)) {
                                Err(error) => Err(error),
                                Ok(_) => Ok(expected),
                            },
                        },
                    },
            },
            Goal::Infer => {
                match shape(source, forms, at) {
                    Ok(Expression::Conditional { condition, yes, no }) if at < condition < yes < no < forms.len() => {
                        let boolean = scalar_type(BuiltinDataType::Bool);
                        let cond = Request { at: condition, expected: boolean, list: None };
                        match typed_expression(source, forms, env, cond, Goal::Check(boolean)) {
                            Err(error) => Err(error),
                            Ok(_) => match typed_expression(source, forms, env, Request { at: yes, ..cond }, Goal::Infer) {
                                Err(error) => Err(error),
                                Ok(expected) => compare_inferred_branch(forms, no, expected,
                                    typed_expression(source, forms, env, Request { at: no, ..cond }, Goal::Infer)),
                            },
                        }
                    },
                    Ok(Expression::List) if at + 2 < subtree_limit(forms, at) <= forms.len() =>
                        typed_elements(source, forms, env, at, (at + 2) as usize, None),
                    _ => match synthesized_type(source, forms, env, at) {
                        Err(error) => Err(error),
                        Ok(expected) => typed_expression(source, forms, env, Request { expected, ..request }, Goal::Check(expected)),
                    },
                }
            }
        }
    };
    match result {
        Err(error) => Err(error),
        Ok(ty) => match remaining_elements(forms, request) {
            None => Ok(ty),
            Some(next) => match typed_expression(source, forms, env, next, goal) {
                Err(error) => Err(error),
                Ok(_) => Ok(ty),
            },
        },
    }
}

spec fn typed_bindings<'a>(
    source: &'a str, forms: Seq<Form>, outer: Seq<TypeBinding>,
    owner: usize, body: usize, rows: Seq<LocalBinding>, from: nat, extended: Seq<TypeBinding>,
) -> Result<Seq<TypeBinding>, ExpressionCheckFailure<'a>>
    decreases forms.len() - owner, 1nat, rows.len() - from,
{
    if from >= rows.len() {
        Ok(extended)
    } else {
        let row = rows[from as int];
        if !(owner < row.name < row.value < body <= forms.len()) {
            Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(form_span(forms[owner as int]))))
        } else {
            let expect_unused = scalar_type(BuiltinDataType::Bool);
            let value = Request { at: row.value, expected: expect_unused, list: None };
            match typed_expression(source, forms, outer, value, Goal::Infer) {
                Err(error) => Err(error),
                Ok(ty) => {
                    let name = spelling(source, forms[row.name as int]);
                    typed_bindings(source, forms, outer, owner, body, rows, from + 1, seq![(name, ty)] + extended)
                },
            }
        }
    }
}

spec fn typed_elements<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize, first: Option<TypeShape>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - at, 3nat, 0nat,
{
    let end = subtree_limit(forms, owner);
    if !(owner < at < end <= forms.len()) {
        unknown_form(form_span(forms[owner as int]))
    } else {
        let request = Request { at, expected: scalar_type(BuiltinDataType::Bool), list: None };
        match typed_expression(source, forms, env, request, Goal::Infer) {
            Err(error) => Err(error),
            Ok(actual) => finish_element_model(source, forms, env, owner, at, first, actual),
        }
    }
}

spec fn finish_element_model<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize,
    first: Option<TypeShape>, actual: TypeShape,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - at, 0nat, 0nat,
{
    let end = subtree_limit(forms, owner);
    let element = match first {
        None => Ok(actual),
        Some(expected) => compare_inferred_branch(forms, at, expected, Ok(actual)),
    };
    match element {
        Err(error) => Err(error),
        Ok(ty) => {
            let next = subtree_limit(forms, at);
            if next == end && ty.list_depth < usize::MAX {
                Ok(TypeShape { builtin: ty.builtin, list_depth: (ty.list_depth + 1) as usize })
            } else if at < next < end <= forms.len() {
                typed_elements(source, forms, env, owner, next, Some(ty))
            } else {
                unknown_form(form_span(forms[owner as int]))
            }
        },
    }
}

enum FormPlan {
    Check(CheckStep, TypeShape),
    InferConditional { condition: usize, yes: usize, no: usize },
    InferList { first: usize },
    Let(LetHeader),
}

#[cfg(verus_only)]
enum PlanModel {
    Check(CheckStep, TypeShape),
    InferConditional { condition: usize, yes: usize, no: usize },
    InferList { first: usize },
    Let { rows: Seq<LocalBinding>, body: usize },
}

spec fn project_plan(plan: FormPlan) -> PlanModel {
    match plan {
        FormPlan::Check(step, ty) => PlanModel::Check(step, ty),
        FormPlan::InferConditional { condition, yes, no } => PlanModel::InferConditional { condition, yes, no },
        FormPlan::InferList { first } => PlanModel::InferList { first },
        FormPlan::Let(header) => PlanModel::Let { rows: header.bindings@, body: header.body },
    }
}

spec fn checked_plan<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, ty: TypeShape,
) -> Result<PlanModel, ExpressionCheckFailure<'a>> {
    match step_model(source, forms, env, Request { expected: ty, ..request }) {
        Err(error) => Err(error),
        Ok(step) => Ok(PlanModel::Check(step, ty)),
    }
}

spec fn form_plan<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, goal: Goal,
) -> Result<PlanModel, ExpressionCheckFailure<'a>> {
    let at = request.at;
    match shape(source, forms, at) {
        Err(error) => Err(error),
        Ok(Expression::Let) => match let_structure(source, forms, at) {
            Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Let(error))),
            Ok((rows, body)) => Ok(PlanModel::Let { rows, body }),
        },
        Ok(expr) => match goal {
            Goal::Check(ty) => checked_plan(source, forms, env, request, ty),
            Goal::Infer => match expr {
                Expression::Conditional { condition, yes, no } => Ok(PlanModel::InferConditional { condition, yes, no }),
                Expression::List if at + 2 < subtree_limit(forms, at) =>
                    Ok(PlanModel::InferList { first: (at + 2) as usize }),
                _ => match synthesized_type(source, forms, env, at) {
                    Err(error) => Err(error),
                    Ok(ty) => checked_plan(source, forms, env, request, ty),
                },
            },
        }
    }
}

spec fn planned_children_fit(forms: Seq<Form>, parent: usize, plan: FormPlan) -> bool {
    match plan {
        FormPlan::Let(header) => {
            &&& forms[parent as int] is List
            &&& parent < header.body < subtree_limit(forms, parent) <= forms.len()
            &&& valid_bindings(forms, header.bindings@, parent, header.body)
        }
        FormPlan::Check(step, _) => step_children_fit(forms, parent, step),
        FormPlan::InferList { first } => {
            &&& forms[parent as int] is List
            &&& parent < first < subtree_limit(forms, parent) <= forms.len()
        }
        FormPlan::InferConditional { condition, yes, no } =>
            parent < condition < yes < no < subtree_limit(forms, parent) <= forms.len()
                && subtree_limit(forms, condition) == yes
                && subtree_limit(forms, yes) == no
                && subtree_limit(forms, no) == subtree_limit(forms, parent),
    }
}

fn read_form_plan<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>],
    locals: &LocalScopes<'a>, scope: Scope, request: Request, goal: Goal,
) -> (result: Result<FormPlan, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), request.at < forms@.len(), locals.contains(scope),
    ensures
        (match result { Err(error) => Err(error), Ok(plan) => Ok(project_plan(plan)) })
            == form_plan(source, forms@, lexical_view(parameters@, locals, scope), request, goal),
        result matches Ok(plan) ==> planned_children_fit(forms@, request.at, plan),
{
    let at = request.at;
    let expr = read_shape(source, forms, at)?;
    if matches!(expr, Expression::Let) {
        let header = match read_let_structure(source, forms, at) {
            Ok(header) => header,
            Err(error) => return Err(ExpressionCheckFailure::Type(ExpressionTypeError::Let(error))),
        };
        return Ok(FormPlan::Let(header));
    }
    let ty = match goal {
        Goal::Check(ty) => ty,
        Goal::Infer => match expr {
            Expression::Conditional { condition, yes, no } => {
                assert(children3(forms@, at) == Some((condition, yes, no)));
                return Ok(FormPlan::InferConditional { condition, yes, no });
            }
            Expression::List if subtree_end(forms, at) - at > 2 => {
                return Ok(FormPlan::InferList { first: at + 2 });
            }
            _ => synthesize_type(source, forms, parameters, locals, scope, at)?,
        },
    };
    let step = read_check_step(source, forms, parameters, locals, scope, Request { expected: ty, ..request })?;
    Ok(FormPlan::Check(step, ty))
}

#[derive(Clone, Copy)]
struct Job {
    request: Request,
    goal: Goal,
    scope: Scope,
}

fn check_job(request: Request, scope: Scope) -> (job: Job)
    ensures job == (Job { request, goal: Goal::Check(request.expected), scope }),
{
    Job { request, goal: Goal::Check(request.expected), scope }
}

fn infer_job(at: usize, scope: Scope) -> (job: Job)
    ensures job == (Job {
        request: Request { at, expected: scalar_type(BuiltinDataType::Bool), list: None },
        goal: Goal::Infer, scope,
    }),
{
    Job {
        request: Request { at, expected: scalar(BuiltinDataType::Bool), list: None },
        goal: Goal::Infer,
        scope,
    }
}

enum Await {
    Result(TypeShape),
    Peer(Job),
    CheckedCondition { yes_request: Request, no_request: Request, scope: Scope },
    CheckedYes { no_request: Request, scope: Scope },
    InferredCondition { yes: usize, no: usize, scope: Scope },
    InferredYes { no: usize, scope: Scope },
    InferredNo { no: usize, expected: TypeShape },
    Element { at: usize, owner: usize, element: Option<TypeShape>, scope: Scope },
    Binding { header: LetHeader, binding_owner: Job, index: usize, body_scope: Scope },
}

enum Action {
    Typed(TypeShape),
    Visit(Job, Option<Await>),
}

spec fn job_in_bounds(forms: Seq<Form>, job: Job) -> bool {
    &&& job.request.at < forms.len()
    &&& job.request.list.is_some() ==> request_ready(forms, job.request) && job.goal == Goal::Check(job.request.expected)
}

spec fn wait_in_bounds(forms: Seq<Form>, awaiting: Await) -> bool {
    match awaiting {
        Await::Result(_) => true,
        Await::Peer(job) => job_in_bounds(forms, job),
        Await::CheckedCondition { yes_request: yes, no_request: no, .. } =>
            job_in_bounds(forms, Job { request: yes, goal: Goal::Check(yes.expected), scope: None })
                && job_in_bounds(forms, Job { request: no, goal: Goal::Check(no.expected), scope: None }),
        Await::CheckedYes { no_request: no, .. } =>
            job_in_bounds(forms, Job { request: no, goal: Goal::Check(no.expected), scope: None }),
        Await::InferredCondition { yes, no, .. } => yes < no < forms.len(),
        Await::InferredYes { no, .. } | Await::InferredNo { no, .. } => no < forms.len(),
        Await::Element { at, owner, .. } => owner < at < subtree_limit(forms, at) <= subtree_limit(forms, owner) <= forms.len(),
        Await::Binding { header, binding_owner: owner, index, .. } => {
            &&& index < header.bindings@.len()
            &&& owner.request.at < header.body < forms.len()
            &&& valid_bindings(forms, header.bindings@, owner.request.at, header.body)
        }
    }
}

spec fn wait_has_scopes(locals: &LocalScopes, awaiting: Await) -> bool {
    match awaiting {
        Await::Peer(job) => locals.contains(job.scope),
        Await::CheckedCondition { scope, .. } | Await::CheckedYes { scope, .. }
        | Await::InferredCondition { scope, .. } | Await::InferredYes { scope, .. }
        | Await::Element { scope, .. } => locals.contains(scope),
        Await::Binding { binding_owner, body_scope, .. } =>
            locals.contains(binding_owner.scope) && locals.contains(body_scope),
        _ => true,
    }
}

spec fn action_valid(forms: Seq<Form>, locals: &LocalScopes, action: Action) -> bool {
    match action {
        Action::Typed(_) => true,
        Action::Visit(job, awaiting) => {
            &&& job_in_bounds(forms, job)
            &&& locals.contains(job.scope)
            &&& awaiting matches Some(frame) ==> wait_in_bounds(forms, frame) && wait_has_scopes(locals, frame)
        }
    }
}

spec fn wait_limit(forms: Seq<Form>, waiting: Await, child: Job) -> usize {
    match waiting {
        Await::Result(_) | Await::InferredNo { .. } => request_limit(forms, child.request),
        Await::Peer(next) => request_limit(forms, next.request),
        Await::CheckedCondition { no_request: no, .. } | Await::CheckedYes { no_request: no, .. } => request_limit(forms, no),
        Await::InferredCondition { no, .. } | Await::InferredYes { no, .. } => subtree_limit(forms, no),
        Await::Element { owner, .. } => subtree_limit(forms, owner),
        Await::Binding { header, .. } => subtree_limit(forms, header.body),
    }
}

spec fn wait_follows(forms: Seq<Form>, waiting: Await, child: Job) -> bool {
    let end = request_limit(forms, child.request);
    &&& request_ready(forms, child.request)
    &&& end <= wait_limit(forms, waiting, child) <= forms.len()
    &&& match waiting {
        Await::Result(_) | Await::InferredNo { .. } => true,
        Await::Peer(next) => end <= next.request.at,
        Await::CheckedCondition { yes_request: yes, no_request: no, .. } => end <= yes.at && request_limit(forms, yes) <= no.at,
        Await::CheckedYes { no_request: no, .. } => end <= no.at,
        Await::InferredCondition { yes, no, .. } => end <= yes && subtree_limit(forms, yes) <= no,
        Await::InferredYes { no, .. } => end <= no,
        Await::Element { at, owner, .. } => child.request.at == at && child.request.list.is_none()
            && forms[owner as int] is List,
        Await::Binding { header, index, .. } => index < header.bindings@.len()
            && child.request.at == header.bindings@[index as int].value && child.request.list.is_none(),
    }
}

spec fn action_limit(forms: Seq<Form>, action: Action) -> usize {
    match action {
        Action::Typed(_) => 0,
        Action::Visit(job, pending) => match pending {
            None => request_limit(forms, job.request),
            Some(waiting) => wait_limit(forms, waiting, job),
        },
    }
}

spec fn action_advances(forms: Seq<Form>, action: Action, before: usize) -> bool {
    match action {
        Action::Typed(_) => true,
        Action::Visit(job, pending) => before <= job.request.at
            && request_ready(forms, job.request)
            && (pending matches Some(frame) ==> wait_follows(forms, frame, job)),
    }
}

spec fn job_type<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes, job: Job,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    typed_expression(source, forms, lexical_view(parameters, locals, job.scope), job.request, job.goal)
}

spec fn only_to_result<'a>(
    child: Result<TypeShape, ExpressionCheckFailure<'a>>, expected: TypeShape,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match child {
        Err(error) => Err(error),
        Ok(_) => Ok(expected),
    }
}

spec fn resumed_type<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    frame: Await, ty: TypeShape,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match frame {
        Await::Result(expected) => Ok(expected),
        Await::Peer(job) => job_type(source, forms, parameters, locals, job),
        Await::CheckedCondition { yes_request: yes, no_request: no, scope } => {
            let env = lexical_view(parameters, locals, scope);
            match typed_expression(source, forms, env, yes, Goal::Check(yes.expected)) {
                Err(error) => Err(error),
                Ok(_) => typed_expression(source, forms, env, no, Goal::Check(no.expected)),
            }
        }
        Await::CheckedYes { no_request: no, scope } => {
            typed_expression(source, forms, lexical_view(parameters, locals, scope), no, Goal::Check(no.expected))
        }
        Await::InferredCondition { yes, no, scope } => {
            let env = lexical_view(parameters, locals, scope);
            let yes = Request { at: yes, expected: scalar_type(BuiltinDataType::Bool), list: None };
            let no = Request { at: no, ..yes };
            match typed_expression(source, forms, env, yes, Goal::Infer) {
                Err(error) => Err(error),
                Ok(yes_ty) => compare_inferred_branch(forms, no.at, yes_ty, typed_expression(source, forms, env, no, Goal::Infer)),
            }
        }
        Await::InferredYes { no, scope } => {
            let request = Request { at: no, expected: scalar_type(BuiltinDataType::Bool), list: None };
            let env = lexical_view(parameters, locals, scope);
            compare_inferred_branch(forms, no, ty, typed_expression(source, forms, env, request, Goal::Infer))
        }
        Await::InferredNo { no, expected } => compare_inferred_branch(forms, no, expected, Ok(ty)),
        Await::Element { at, owner, element, scope } => {
            let env = lexical_view(parameters, locals, scope);
            finish_element_model(source, forms, env, owner, at, element, ty)
        }
        Await::Binding { header, binding_owner: owner, index, body_scope } => {
            let binding = header.bindings@[index as int];
            let typed = (spelling(source, forms[binding.name as int]), ty);
            let env = lexical_view(parameters, locals, owner.scope);
            let extended = seq![typed] + lexical_view(parameters, locals, body_scope);
            continue_bindings(source, forms, env, owner, header, (index + 1) as nat, extended)
        }
    }
}

spec fn continue_bindings<'a>(
    source: &'a str, forms: Seq<Form>, outer: Seq<TypeBinding>, owner: Job, header: LetHeader,
    from: nat, extended: Seq<TypeBinding>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match typed_bindings(source, forms, outer, owner.request.at, header.body, header.bindings@, from, extended) {
        Err(error) => Err(error),
        Ok(body_env) => typed_expression(source, forms, body_env, Request { at: header.body, list: None, ..owner.request }, owner.goal),
    }
}

spec fn compare_inferred_branch<'a>(
    forms: Seq<Form>, at: usize, expected: TypeShape, other: Result<TypeShape, ExpressionCheckFailure<'a>>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match other {
        Err(error) => Err(error),
        Ok(actual) => match types_agree(expected, actual, form_span(forms[at as int])) {
            Err(error) => Err(error),
            Ok(()) => Ok(expected),
        },
    }
}

spec fn action_type<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    result: Result<Action, ExpressionCheckFailure<'a>>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match result {
        Err(error) => Err(error),
        Ok(Action::Typed(ty)) => Ok(ty),
        Ok(Action::Visit(job, tail)) => match job_type(source, forms, parameters, locals, job) {
            Err(error) => Err(error),
            Ok(ty) => match tail {
                None => Ok(ty),
                Some(frame) => resumed_type(source, forms, parameters, locals, frame, ty),
            },
        },
    }
}

proof fn checked_answer_is_expected<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, expected: TypeShape, actual: TypeShape,
)
    requires typed_expression(source, forms, env, request, Goal::Check(expected)) == Ok(actual),
    ensures actual == expected,
    decreases forms.len() - request.at,
{
    reveal_with_fuel(typed_expression, 2);
    reveal(typed_bindings);
    if shape(source, forms, request.at) == Ok(Expression::Let) {
        let (rows, body) = let_structure(source, forms, request.at)->Ok_0;
        let extended = typed_bindings(source, forms, env, request.at, body, rows, 0, env)->Ok_0;
        let body_request = Request { at: body, list: None, ..request };
        assert(typed_expression(source, forms, extended, body_request, Goal::Check(expected)) == Ok(actual));
        checked_answer_is_expected(source, forms, extended, body_request, expected, actual);
    }
}

proof fn checked_type_result<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request,
)
    ensures typed_expression(source, forms, env, request, Goal::Check(request.expected))
        == only_to_result(typed_expression(source, forms, env, request, Goal::Check(request.expected)), request.expected),
{
    if let Ok(actual) = typed_expression(source, forms, env, request, Goal::Check(request.expected)) {
        checked_answer_is_expected(source, forms, env, request, request.expected, actual);
    }
}

spec fn ensure_two_checked<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>,
    yes: Request, no: Request, result_ty: TypeShape,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match typed_expression(source, forms, env, yes, Goal::Check(yes.expected)) {
        Err(error) => Err(error),
        Ok(_) => only_to_result(typed_expression(source, forms, env, no, Goal::Check(no.expected)), result_ty),
    }
}

spec fn checked_selections<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, step: CheckStep, ty: TypeShape,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match step {
        CheckStep::Done => Ok(ty),
        CheckStep::One(child) => only_to_result(typed_expression(source, forms, env, child, Goal::Check(child.expected)), ty),
        CheckStep::Three(condition, yes, no) =>
            match typed_expression(source, forms, env, condition, Goal::Check(condition.expected)) {
                Err(error) => Err(error),
                Ok(_) => ensure_two_checked(source, forms, env, yes, no, ty),
            },
    }
}

proof fn plan_check_is_checked<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, goal: Goal, step: CheckStep, ty: TypeShape,
)
    requires request.at < forms.len(), request.list.is_none(), step_children_fit(forms, request.at, step),
        form_plan(source, forms, env, request, goal) == Ok(PlanModel::Check(step, ty)),
    ensures typed_expression(source, forms, env, request, goal) == checked_selections(source, forms, env, step, ty),
        step matches CheckStep::Three(_, _, no) ==> no.expected == ty,
{
    reveal_with_fuel(typed_expression, 3);
    reveal(typed_elements);
    reveal(typed_bindings);
    match goal {
        Goal::Check(expected) => {},
        Goal::Infer => {
            let contextual = Request { expected: ty, ..request };
            assert(synthesized_type(source, forms, env, request.at) == Ok(ty));
            assert(step_model(source, forms, env, contextual) == Ok(step));
            assert(typed_expression(source, forms, env, contextual, Goal::Check(ty))
                == checked_selections(source, forms, env, step, ty));
        }
    }
}

proof fn rejected_plan_has_no_type<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, goal: Goal, error: ExpressionCheckFailure<'a>,
)
    requires request.at < forms.len(), request.list.is_none(),
        form_plan(source, forms, env, request, goal) == Err(error),
    ensures typed_expression(source, forms, env, request, goal) == Err(error),
{
    reveal_with_fuel(typed_expression, 3);
    reveal(typed_bindings);
    reveal(typed_elements);
}

proof fn inferred_condition_plan<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    job: Job, condition: usize, yes: usize, no: usize,
)
    requires
        job.request.at < condition < yes < no < forms.len(), job.request.list.is_none(),
        form_plan(source, forms, lexical_view(parameters, locals, job.scope), job.request, job.goal)
            == Ok(PlanModel::InferConditional { condition, yes, no }),
    ensures job_type(source, forms, parameters, locals, job)
        == action_type(source, forms, parameters, locals, Ok(Action::Visit(
            Job { request: Request { at: condition, expected: scalar_type(BuiltinDataType::Bool), list: None },
                goal: Goal::Check(scalar_type(BuiltinDataType::Bool)), scope: job.scope },
            Some(Await::InferredCondition { yes, no, scope: job.scope }),
        ))),
{
    reveal_with_fuel(typed_expression, 2);
}

proof fn inferred_list_plan<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    job: Job, first: usize,
)
    requires
        job.request.at < first < subtree_limit(forms, job.request.at) <= forms.len(), job.request.list.is_none(),
        form_plan(source, forms, lexical_view(parameters, locals, job.scope), job.request, job.goal)
            == Ok(PlanModel::InferList { first }),
    ensures job_type(source, forms, parameters, locals, job)
        == action_type(source, forms, parameters, locals, Ok(Action::Visit(
            Job { request: Request { at: first, expected: scalar_type(BuiltinDataType::Bool), list: None },
                goal: Goal::Infer, scope: job.scope },
            Some(Await::Element { at: first, owner: job.request.at, element: None, scope: job.scope }),
        ))),
{
    reveal_with_fuel(typed_expression, 2);
    reveal_with_fuel(typed_elements, 2);
    reveal(finish_element_model);
}

proof fn let_plan_type<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    job: Job, header: LetHeader,
)
    requires job.request.at < header.body < forms.len(), job.request.list.is_none(),
        valid_bindings(forms, header.bindings@, job.request.at, header.body),
        form_plan(source, forms, lexical_view(parameters, locals, job.scope), job.request, job.goal)
            == Ok(PlanModel::Let { rows: header.bindings@, body: header.body }),
    ensures job_type(source, forms, parameters, locals, job) ==
        action_type(source, forms, parameters, locals, Ok(
            if header.bindings@.len() == 0 {
                Action::Visit(Job { request: Request { at: header.body, list: None, ..job.request }, ..job }, None)
            } else {
                Action::Visit(Job {
                    request: Request { at: header.bindings@[0].value, expected: scalar_type(BuiltinDataType::Bool), list: None },
                    goal: Goal::Infer, scope: job.scope,
                }, Some(Await::Binding { header, binding_owner: job, index: 0, body_scope: job.scope }))
            }
        )),
{
    reveal_with_fuel(typed_expression, 2);
    reveal_with_fuel(typed_bindings, 2);
    if header.bindings@.len() > 0 {
        assert(job.request.at < header.bindings@[0].name < header.bindings@[0].value < header.body);
    }
}

fn start_action<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], locals: &LocalScopes<'a>, job: Job,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), job_in_bounds(forms@, job), locals.contains(job.scope), job.request.list.is_none(),
    ensures result matches Ok(action) ==> action_valid(forms@, locals, action),
        result matches Ok(action) ==> job.request.at < usize::MAX
            && action_advances(forms@, action, (job.request.at + 1) as usize)
            && action_limit(forms@, action) <= subtree_limit(forms@, job.request.at),
        action_type(source, forms@, parameters@, locals, result) == job_type(source, forms@, parameters@, locals, job),
{
    let req = job.request;
    let _size = forms.len();
    let ghost env = lexical_view(parameters@, locals, job.scope);
    let plan = match read_form_plan(source, forms, parameters, locals, job.scope, req, job.goal) {
        Ok(plan) => plan,
        Err(error) => {
            proof { rejected_plan_has_no_type(source, forms@, env, req, job.goal, error); }
            return Err(error);
        }
    };
    match plan {
        FormPlan::Check(step, ty) => {
            proof { plan_check_is_checked(source, forms@, env, req, job.goal, step, ty); }
            match step {
                CheckStep::Done => Ok(Action::Typed(ty)),
                CheckStep::One(child) => Ok(Action::Visit(check_job(child, job.scope), Some(Await::Result(ty)))),
                CheckStep::Three(condition, yes, no) => {
                    proof { checked_type_result(source, forms@, env, no); }
                    Ok(Action::Visit(check_job(condition, job.scope), Some(Await::CheckedCondition { yes_request: yes, no_request: no, scope: job.scope })))
                }
            }
        }
        FormPlan::InferConditional { condition, yes, no } => {
            proof { inferred_condition_plan(source, forms@, parameters@, locals, job, condition, yes, no); }
            assert(condition < subtree_limit(forms@, condition) == yes);
            assert(yes < subtree_limit(forms@, yes) == no);
            let boolean = scalar(BuiltinDataType::Bool);
            let request = Request { at: condition, expected: boolean, list: None };
            Ok(Action::Visit(check_job(request, job.scope), Some(Await::InferredCondition { yes, no, scope: job.scope })))
        }
        FormPlan::InferList { first } => {
            proof {
                super::super::forms::child_stays_inside(forms@, req.at, first);
                inferred_list_plan(source, forms@, parameters@, locals, job, first);
            }
            Ok(Action::Visit(infer_job(first, job.scope), Some(Await::Element {
                at: first, owner: req.at, element: None, scope: job.scope,
            })))
        }
        FormPlan::Let(header) => {
            proof {
                super::super::forms::child_stays_inside(forms@, req.at, header.body);
                let_plan_type(source, forms@, parameters@, locals, job, header);
            }
            if header.bindings.len() == 0 {
                let body = Job { request: Request { at: header.body, list: None, ..req }, ..job };
                Ok(Action::Visit(body, None))
            } else {
                let row = header.bindings[0];
                Ok(Action::Visit(infer_job(row.value, job.scope), Some(Await::Binding {
                    header, binding_owner: job, index: 0, body_scope: job.scope,
                })))
            }
        }
    }
}


fn accept_element<'a>(
    _source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>], _locals: &LocalScopes<'a>,
    at: usize, owner: usize, element: Option<TypeShape>, scope: Scope, ty: TypeShape, Ghost(child): Ghost<Job>,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires usable_forms(_source, forms@),
        wait_in_bounds(forms@, Await::Element { at, owner, element, scope }),
        wait_has_scopes(_locals, Await::Element { at, owner, element, scope }),
        wait_follows(forms@, Await::Element { at, owner, element, scope }, child),
    ensures result matches Ok(action) ==> action_valid(forms@, _locals, action),
        result matches Ok(action) ==> action_advances(forms@, action, request_limit(forms@, child.request))
            && action_limit(forms@, action) <= wait_limit(forms@, Await::Element { at, owner, element, scope }, child),
        action_type(_source, forms@, _parameters@, _locals, result)
            == resumed_type(_source, forms@, _parameters@, _locals, Await::Element { at, owner, element, scope }, ty),
{
    reveal_with_fuel(typed_expression, 2);
    reveal_with_fuel(typed_elements, 2);
    reveal_with_fuel(finish_element_model, 2);
    let ty = if let Some(expected) = element {
        conform(expected, ty, span_of(&forms[at]))?;
        expected
    } else {
        ty
    };
    let next = subtree_end(forms, at);
    let limit = subtree_end(forms, owner);
    if next < limit {
        proof {
            if forms@[owner as int] is List {
                super::super::forms::child_stays_inside(forms@, owner, next);
            } else {
                assert(limit == owner + 1);
                assert(false);
            }
        }
        Ok(Action::Visit(infer_job(next, scope), Some(Await::Element {
            at: next, owner, element: Some(ty), scope,
        })))
    } else if ty.list_depth == usize::MAX {
        Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(span_of(&forms[owner]))))
    } else {
        Ok(Action::Typed(TypeShape { builtin: ty.builtin, list_depth: ty.list_depth + 1 }))
    }
}

spec fn binding_action(header: LetHeader, owner: Job, index: usize, extended: Scope) -> Action {
    if index + 1 < header.bindings@.len() {
        let next = (index + 1) as usize;
        let child = Job {
            request: Request {
                at: header.bindings@[next as int].value, expected: scalar_type(BuiltinDataType::Bool), list: None,
            },
            goal: Goal::Infer, scope: owner.scope,
        };
        Action::Visit(child, Some(Await::Binding { header, binding_owner: owner, index: next, body_scope: extended }))
    } else {
        Action::Visit(Job { request: Request { at: header.body, list: None, ..owner.request }, scope: extended, ..owner }, None)
    }
}

proof fn binding_action_agrees<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, before: &LocalScopes, after: &LocalScopes,
    header: LetHeader, owner: Job, index: usize, body_scope: Scope, extended: Scope, ty: TypeShape,
)
    requires
        index < header.bindings@.len() <= usize::MAX,
        valid_bindings(forms, header.bindings@, owner.request.at, header.body),
        lexical_view(parameters, after, owner.scope) == lexical_view(parameters, before, owner.scope),
        lexical_view(parameters, after, extended)
            == seq![(spelling(source, forms[header.bindings@[index as int].name as int]), ty)]
                + lexical_view(parameters, before, body_scope),
    ensures
        action_type(source, forms, parameters, after, Ok(binding_action(header, owner, index, extended)))
            == resumed_type(source, forms, parameters, before, Await::Binding { header, binding_owner: owner, index, body_scope }, ty),
{
    let outer = lexical_view(parameters, after, owner.scope);
    let extended_env = lexical_view(parameters, after, extended);
    let from = (index + 1) as nat;
    assert(resumed_type(source, forms, parameters, before, Await::Binding { header, binding_owner: owner, index, body_scope }, ty)
        == continue_bindings(source, forms, outer, owner, header, from, extended_env));
    continue_bindings_unfold(source, forms, outer, owner, header, from, extended_env);
    if from < header.bindings@.len() {
        let next = from as usize;
        let row = header.bindings@[next as int];
        let request = Request { at: row.value, expected: scalar_type(BuiltinDataType::Bool), list: None };
        match typed_expression(source, forms, outer, request, Goal::Infer) {
            Err(error) => {
                assert(action_type(source, forms, parameters, after, Ok(binding_action(header, owner, index, extended)))
                    == Err(error));
            }
            Ok(actual) => {
                assert(action_type(source, forms, parameters, after, Ok(binding_action(header, owner, index, extended)))
                    == resumed_type(source, forms, parameters, after,
                        Await::Binding { header, binding_owner: owner, index: next, body_scope: extended }, actual));
            }
        }
    }
}

proof fn continue_bindings_unfold<'a>(
    source: &'a str, forms: Seq<Form>, outer: Seq<TypeBinding>, owner: Job, header: LetHeader,
    from: nat, extended_env: Seq<TypeBinding>,
)
    requires valid_bindings(forms, header.bindings@, owner.request.at, header.body),
    ensures continue_bindings(source, forms, outer, owner, header, from, extended_env) ==
        if from < header.bindings@.len() {
            let row = header.bindings@[from as int];
            let request = Request { at: row.value, expected: scalar_type(BuiltinDataType::Bool), list: None };
            match typed_expression(source, forms, outer, request, Goal::Infer) {
                Err(error) => Err(error),
                Ok(next_ty) => continue_bindings(source, forms, outer, owner, header, from + 1,
                    seq![(spelling(source, forms[row.name as int]), next_ty)] + extended_env),
            }
        } else {
            typed_expression(source, forms, extended_env,
                Request { at: header.body, list: None, ..owner.request }, owner.goal)
        },
{
    hide(shape);
    hide(step_model);
    reveal_with_fuel(typed_bindings, 2);
    reveal(typed_expression);
    let rows = header.bindings@;
    if from < rows.len() {
        let row = rows[from as int];
        assert(owner.request.at < row.name < row.value < header.body <= forms.len());
        let request = Request { at: row.value, expected: scalar_type(BuiltinDataType::Bool), list: None };
        match typed_expression(source, forms, outer, request, Goal::Infer) {
            Err(error) => {
                assert(typed_bindings(source, forms, outer, owner.request.at, header.body, rows, from, extended_env) == Err(error));
            }
            Ok(next_ty) => {
                let next_env = seq![(spelling(source, forms[row.name as int]), next_ty)] + extended_env;
                assert(typed_bindings(source, forms, outer, owner.request.at, header.body, rows, from, extended_env)
                    == typed_bindings(source, forms, outer, owner.request.at, header.body, rows, from + 1, next_env));
            }
        }
    } else {
        assert(typed_bindings(source, forms, outer, owner.request.at, header.body, rows, from, extended_env) == Ok(extended_env));
    }
}

fn accept_binding<'a>(
    source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>], locals: &mut LocalScopes<'a>,
    header: LetHeader, owner: Job, index: usize, body_scope: Scope, ty: TypeShape, Ghost(child): Ghost<Job>,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@),
        wait_in_bounds(forms@, Await::Binding { header, binding_owner: owner, index, body_scope }),
        wait_has_scopes(old(locals), Await::Binding { header, binding_owner: owner, index, body_scope }),
        wait_follows(forms@, Await::Binding { header, binding_owner: owner, index, body_scope }, child),
    ensures result matches Ok(action) ==> action_valid(forms@, final(locals), action),
        result matches Ok(action) ==> action_advances(forms@, action, request_limit(forms@, child.request))
            && action_limit(forms@, action) <= wait_limit(forms@, Await::Binding { header, binding_owner: owner, index, body_scope }, child),
        action_type(source, forms@, _parameters@, final(locals), result)
            == resumed_type(source, forms@, _parameters@, old(locals), Await::Binding { header, binding_owner: owner, index, body_scope }, ty),
        forall|scope: Scope| #[trigger] old(locals).contains(scope) ==> final(locals).contains(scope)
            && final(locals).local_types(scope) == old(locals).local_types(scope),
{
    let row = header.bindings[index];
    let local = LocalType { name: source_word(source, forms, row.name), ty };
    let ghost outer_env = lexical_view(_parameters@, locals, owner.scope);
    let ghost prior = lexical_view(_parameters@, locals, body_scope);
    let ghost before = *locals;
    // 次の右辺は外側の環境を使い、本体で見える環境にだけ今回の束縛を追加する。
    let new_scope = locals.extend(body_scope, local);
    let count = header.bindings.len();
    assert(lexical_view(_parameters@, locals, owner.scope) == outer_env);
    assert(lexical_view(_parameters@, locals, new_scope) =~= seq![(local.name.spec_bytes(), ty)] + prior);
    proof { binding_action_agrees(source, forms@, _parameters@, &before, locals, header, owner, index, body_scope, new_scope, ty); }
    let _size = forms.len();
    let _end = subtree_end(forms, header.body);
    proof {
        assert(complete_list_indices(forms@));
        if let Form::List { end, .. } = forms@[header.body as int] {
            assert(header.body < end <= _size);
        }
        assert(header.body < _end <= _size);
    }
    let next = index + 1;
    if next < count {
        let next_row = header.bindings[next];
        let value = next_row.value;
        assert(subtree_limit(forms@, row.value) <= next_row.name < value);
        Ok(Action::Visit(infer_job(value, owner.scope), Some(Await::Binding {
            header, binding_owner: owner, index: next, body_scope: new_scope,
        })))
    } else {
        let job = Job { request: Request { at: header.body, list: None, ..owner.request }, scope: new_scope, ..owner };
        Ok(Action::Visit(job, None))
    }
}

fn accept_result<'a>(
    source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>], locals: &mut LocalScopes<'a>, awaiting: Await, ty: TypeShape,
    Ghost(child): Ghost<Job>,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), wait_in_bounds(forms@, awaiting), wait_has_scopes(old(locals), awaiting),
        wait_follows(forms@, awaiting, child),
    ensures result matches Ok(action) ==> action_valid(forms@, final(locals), action),
        result matches Ok(action) ==> action_advances(forms@, action, request_limit(forms@, child.request))
            && action_limit(forms@, action) <= wait_limit(forms@, awaiting, child),
        action_type(source, forms@, _parameters@, final(locals), result)
            == resumed_type(source, forms@, _parameters@, old(locals), awaiting, ty),
        forall|scope: Scope| #[trigger] old(locals).contains(scope) ==> final(locals).contains(scope)
            && final(locals).local_types(scope) == old(locals).local_types(scope),
{
    let _size = forms.len();
    assert(complete_list_indices(forms@) && _size == forms@.len());
    match awaiting {
        Await::Result(expected) => Ok(Action::Typed(expected)),
        Await::Peer(job) => Ok(Action::Visit(job, None)),
        Await::CheckedCondition { yes_request: yes, no_request: no, scope } => {
            Ok(Action::Visit(check_job(yes, scope), Some(Await::CheckedYes { no_request: no, scope })))
        }
        Await::CheckedYes { no_request: no, scope } => Ok(Action::Visit(check_job(no, scope), None)),
        Await::InferredCondition { yes, no, scope } => {
            Ok(Action::Visit(infer_job(yes, scope), Some(Await::InferredYes { no, scope })))
        }
        Await::InferredYes { no, scope } => {
            Ok(Action::Visit(infer_job(no, scope), Some(Await::InferredNo { no, expected: ty })))
        }
        Await::InferredNo { no, expected } => {
            conform(expected, ty, span_of(&forms[no]))?;
            Ok(Action::Typed(expected))
        }
        Await::Element { at, owner, element, scope } =>
            accept_element(source, forms, _parameters, locals, at, owner, element, scope, ty, Ghost(child)),
        Await::Binding { header, binding_owner: owner, index, body_scope } =>
            accept_binding(source, forms, _parameters, locals, header, owner, index, body_scope, ty, Ghost(child)),

    }
}

struct Pending {
    child: Ghost<Job>,
    awaiting: Await,
}

spec fn pending_ranges(forms: Seq<Form>, pending: Seq<Pending>, job: Job) -> bool {
    &&& forall|i: int| 0 <= i < pending.len() ==> {
        let work = #[trigger] pending[i];
        &&& wait_in_bounds(forms, work.awaiting)
        &&& wait_follows(forms, work.awaiting, work.child@)
        &&& work.child@.request.at <= job.request.at
        &&& request_limit(forms, job.request) <= request_limit(forms, work.child@.request)
    }
    &&& forall|i: int, j: int| 0 <= i < j < pending.len() ==> {
        let outer = #[trigger] pending[i];
        let inner = #[trigger] pending[j];
        wait_limit(forms, inner.awaiting, inner.child@) <= request_limit(forms, outer.child@.request)
    }
}

spec fn pending_scopes(locals: &LocalScopes, pending: Seq<Pending>) -> bool {
    forall|i: int| 0 <= i < pending.len() ==> wait_has_scopes(locals, (#[trigger] pending[i]).awaiting)
}

#[verifier::opaque]
spec fn completed_typing<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    pending: Seq<Pending>, result: Result<TypeShape, ExpressionCheckFailure<'a>>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases pending.len(),
{
    match result {
        Err(error) => Err(error),
        Ok(ty) => {
            if pending.len() == 0 {
                Ok(ty)
            } else {
                let work = pending.last();
                completed_typing(source, forms, parameters, locals, pending.drop_last(),
                    resumed_type(source, forms, parameters, locals, work.awaiting, ty))
            }
        }
    }
}

proof fn pushed_pending_agrees<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    pending: Seq<Pending>, work: Pending, result: Result<TypeShape, ExpressionCheckFailure<'a>>,
)
    ensures completed_typing(source, forms, parameters, locals, pending.push(work), result)
        == completed_typing(source, forms, parameters, locals, pending, match result {
            Err(error) => Err(error),
            Ok(ty) => resumed_type(source, forms, parameters, locals, work.awaiting, ty),
        }),
{
    reveal(completed_typing);
    assert(pending.push(work).drop_last() =~= pending);
}

proof fn resume_keeps_earlier_scopes<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, previous: &LocalScopes, locals: &LocalScopes,
    waiting: Await, ty: TypeShape,
)
    requires wait_has_scopes(previous, waiting),
        forall|scope: Scope| #[trigger] previous.contains(scope) ==>
            locals.contains(scope) && locals.local_types(scope) == previous.local_types(scope),
    ensures wait_has_scopes(locals, waiting),
        resumed_type(source, forms, parameters, locals, waiting, ty)
            == resumed_type(source, forms, parameters, previous, waiting, ty),
{
}

proof fn pending_keeps_earlier_scopes<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, previous: &LocalScopes, locals: &LocalScopes,
    pending: Seq<Pending>, result: Result<TypeShape, ExpressionCheckFailure<'a>>,
)
    requires pending_scopes(previous, pending),
        forall|scope: Scope| #[trigger] previous.contains(scope) ==>
            locals.contains(scope) && locals.local_types(scope) == previous.local_types(scope),
    ensures pending_scopes(locals, pending),
        completed_typing(source, forms, parameters, previous, pending, result)
            == completed_typing(source, forms, parameters, locals, pending, result),
    decreases pending.len(),
{
    assert forall|i: int| 0 <= i < pending.len() implies wait_has_scopes(locals, (#[trigger] pending[i]).awaiting) by {
        resume_keeps_earlier_scopes(source, forms, parameters, previous, locals, pending[i].awaiting,
            scalar_type(BuiltinDataType::Bool));
    };
    reveal(completed_typing);
    if pending.len() != 0 {
        if let Ok(ty) = result {
            let last = pending.last();
            resume_keeps_earlier_scopes(source, forms, parameters, previous, locals, last.awaiting, ty);
            let earlier = pending.drop_last();
            assert forall|i:int| 0 <= i < earlier.len() implies wait_has_scopes(previous, (#[trigger] earlier[i]).awaiting) by {
                assert(earlier[i] == pending[i]);
            };
            pending_keeps_earlier_scopes(source, forms, parameters, previous, locals, earlier,
                resumed_type(source, forms, parameters, locals, last.awaiting, ty));
        }
    }
}

proof fn pushed_pending_fits(
    forms: Seq<Form>, locals: &LocalScopes, pending: Seq<Pending>, current: Job, child: Job, frame: Await,
)
    requires pending_ranges(forms, pending, current), pending_scopes(locals, pending),
        current.request.at <= child.request.at,
        wait_in_bounds(forms, frame), wait_follows(forms, frame, child), wait_has_scopes(locals, frame),
        forall|i:int| 0 <= i < pending.len() ==>
            wait_limit(forms, frame, child) <= request_limit(forms, (#[trigger] pending[i]).child@.request),
    ensures pending_ranges(forms, pending.push(Pending { child: Ghost(child), awaiting: frame }), child),
        pending_scopes(locals, pending.push(Pending { child: Ghost(child), awaiting: frame })),
{
    let next = pending.push(Pending { child: Ghost(child), awaiting: frame });
    assert forall|i:int| 0 <= i < next.len() implies {
        let work = #[trigger] next[i];
        &&& wait_in_bounds(forms, work.awaiting)
        &&& wait_follows(forms, work.awaiting, work.child@)
        &&& work.child@.request.at <= child.request.at
        &&& request_limit(forms, child.request) <= request_limit(forms, work.child@.request)
        &&& wait_has_scopes(locals, work.awaiting)
    } by {
        if i < pending.len() { assert(next[i] == pending[i]); }
    };
    assert forall|i:int, j:int| 0 <= i < j < next.len() implies {
        let outer = #[trigger] next[i];
        let inner = #[trigger] next[j];
        wait_limit(forms, inner.awaiting, inner.child@) <= request_limit(forms, outer.child@.request)
    } by {
        assert(next[i] == pending[i]);
        if j < pending.len() { assert(next[j] == pending[j]); }
    };
}

proof fn shrunk_pending_fits(
    forms: Seq<Form>, locals: &LocalScopes, pending: Seq<Pending>, cursor: Job, last: Pending,
)
    requires pending_ranges(forms, pending.push(last), cursor), pending_scopes(locals, pending.push(last)),
    ensures pending_ranges(forms, pending, cursor), pending_scopes(locals, pending),
{
    let old = pending.push(last);
    assert forall|i: int| 0 <= i < pending.len() implies {
        let work = #[trigger] pending[i];
        &&& wait_in_bounds(forms, work.awaiting)
        &&& wait_follows(forms, work.awaiting, work.child@)
        &&& work.child@.request.at <= cursor.request.at
        &&& request_limit(forms, cursor.request) <= request_limit(forms, work.child@.request)
        &&& wait_has_scopes(locals, work.awaiting)
    } by {
        assert(pending[i] == old[i]);
    };
    assert forall|i:int, j:int| 0 <= i < j < pending.len() implies {
        let outer = #[trigger] pending[i];
        let inner = #[trigger] pending[j];
        wait_limit(forms, inner.awaiting, inner.child@) <= request_limit(forms, outer.child@.request)
    } by {
        assert(pending[i] == old[i] && pending[j] == old[j]);
    };
}

proof fn closer_cursor_fits(forms: Seq<Form>, pending: Seq<Pending>, before: Job, after: Job)
    requires pending_ranges(forms, pending, before), before.request.at <= after.request.at,
        forall|i:int| 0 <= i < pending.len() ==>
            request_limit(forms, after.request) <= request_limit(forms, (#[trigger] pending[i]).child@.request),
    ensures pending_ranges(forms, pending, after),
{
}

proof fn advance_after_pop(
    forms: Seq<Form>, pending: Seq<Pending>, current: Job, last: Pending, action: Action,
)
    requires pending_ranges(forms, pending.push(last), current), request_ready(forms, current.request),
        action_advances(forms, action, request_limit(forms, last.child@.request)),
        action_limit(forms, action) <= wait_limit(forms, last.awaiting, last.child@),
    ensures action matches Action::Visit(child, _) ==> {
        &&& current.request.at < child.request.at
        &&& forall|i:int| 0 <= i < pending.len() ==>
            action_limit(forms, action) <= request_limit(forms, (#[trigger] pending[i]).child@.request)
    },
{
    let stack = pending.push(last);
    assert(stack[pending.len() as int] == last);
    if let Action::Visit(child, _) = action {
        assert forall|i:int| 0 <= i < pending.len() implies
            action_limit(forms, action) <= request_limit(forms, (#[trigger] pending[i]).child@.request) by {
            assert(pending[i] == stack[i]);
            assert(wait_limit(forms, last.awaiting, last.child@) <= request_limit(forms, stack[i].child@.request));
        };
    }
}

fn attach_action<'a>(
    _source: &'a str, _forms: &[Form], _parameters: &[SignatureParameter<'a>], _locals: &LocalScopes<'a>,
    pending: &mut Vec<Pending>, _current: Job, child: Job, continuation: Option<Await>,
) -> (result: Job)
    requires
        pending_ranges(_forms@, old(pending)@, _current), pending_scopes(_locals, old(pending)@),
        _current.request.at <= child.request.at,
        action_valid(_forms@, _locals, Action::Visit(child, continuation)),
        action_advances(_forms@, Action::Visit(child, continuation), child.request.at),
        forall|i:int| 0 <= i < old(pending)@.len() ==>
            action_limit(_forms@, Action::Visit(child, continuation)) <= request_limit(_forms@, (#[trigger] old(pending)@[i]).child@.request),
    ensures
        result == child, pending_ranges(_forms@, final(pending)@, result), pending_scopes(_locals, final(pending)@),
        completed_typing(_source, _forms@, _parameters@, _locals, final(pending)@,
            job_type(_source, _forms@, _parameters@, _locals, result))
            == completed_typing(_source, _forms@, _parameters@, _locals, old(pending)@,
                action_type(_source, _forms@, _parameters@, _locals, Ok(Action::Visit(child, continuation)))),
{
    let ghost before = pending@;
    if let Some(awaiting) = continuation {
        proof {
            pushed_pending_fits(_forms@, _locals, pending@, _current, child, awaiting);
            pushed_pending_agrees(_source, _forms@, _parameters@, _locals, pending@,
                Pending { child: Ghost(child), awaiting }, job_type(_source, _forms@, _parameters@, _locals, child));
        }
        pending.push(Pending { child: Ghost(child), awaiting });
    } else {
        proof { closer_cursor_fits(_forms@, pending@, _current, child); }
    }
    child
}

proof fn peer_preserves_typing<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes, work: Job,
)
    requires
        job_in_bounds(forms, work), request_ready(forms, work.request),
    ensures job_type(source, forms, parameters, locals, work) ==
        action_type(source, forms, parameters, locals, Ok(Action::Visit(
            Job { request: Request { list: None, ..work.request }, ..work },
            match remaining_elements(forms, work.request) {
                Some(next) => Some(Await::Peer(Job { request: next, ..work })),
                None => None,
            },
        ))),
{
    reveal_with_fuel(typed_expression, 2);
    reveal(typed_bindings);
    reveal(typed_elements);
    let env = lexical_view(parameters, locals, work.scope);
    if let Some(next) = remaining_elements(forms, work.request) {
        let primary = Request { list: None, ..work.request };
        checked_type_result(source, forms, env, primary);
        checked_type_result(source, forms, env, next);
    }
}

fn type_with_scopes<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], at: usize, expected: TypeShape,
) -> (result: Result<TypeShape, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures result == typed_expression(source, forms@, environment_view(parameters@),
        Request { at, expected, list: None }, Goal::Check(expected)),
{
    let mut locals = LocalScopes::new();
    let mut job = check_job(Request { at, expected, list: None }, None);
    let mut pending = Vec::<Pending>::new();
    let _size = forms.len();
    let _end = subtree_end(forms, at);
    let ghost root = typed_expression(source, forms@, environment_view(parameters@),
        Request { at, expected, list: None }, Goal::Check(expected));
    proof {
        assert(complete_list_indices(forms@));
        assert(at < _end <= _size);
        assert(lexical_view(parameters@, &locals, None) =~= environment_view(parameters@));
        reveal(completed_typing);
    }
    loop
        invariant
            usable_forms(source, forms@), request_ready(forms@, job.request), job_in_bounds(forms@, job),
            locals.contains(job.scope), pending_ranges(forms@, pending@, job), pending_scopes(&locals, pending@),
            root == typed_expression(source, forms@, environment_view(parameters@),
                Request { at, expected, list: None }, Goal::Check(expected)),
            completed_typing(source, forms@, parameters@, &locals, pending@, job_type(source, forms@, parameters@, &locals, job))
                == root,
        decreases forms@.len() - job.request.at,
    {
        let peer = read_remaining_elements(forms, job.request);
        let single = Job { request: Request { list: None, ..job.request }, ..job };
        // 次の要素用に元の環境を保持し、現在の要素の検査から戻ってきたときに使う。
        let after = match peer {
            Some(request) => Some(Await::Peer(check_job(request, job.scope))),
            None => None,
        };
        proof { peer_preserves_typing(source, forms@, parameters@, &locals, job); }
        job = attach_action(source, forms, parameters, &locals, &mut pending, job, single, after);
        let mut ty = match start_action(source, forms, parameters, &locals, job) {
            Err(error) => {
                proof { reveal(completed_typing); }
                return Err(error);
            }
            Ok(Action::Visit(child, waiting)) => {
                job = attach_action(source, forms, parameters, &locals, &mut pending, job, child, waiting);
                continue;
            }
            Ok(Action::Typed(ty)) => ty,
        };
        let ghost before = job.request.at;
        loop
            invariant_except_break
                before == job.request.at,
                completed_typing(source, forms@, parameters@, &locals, pending@, Ok(ty)) == root,
            invariant
                usable_forms(source, forms@), request_ready(forms@, job.request), job_in_bounds(forms@, job),
                locals.contains(job.scope), pending_ranges(forms@, pending@, job), pending_scopes(&locals, pending@),
                root == typed_expression(source, forms@, environment_view(parameters@),
                    Request { at, expected, list: None }, Goal::Check(expected)),
            ensures
                before < job.request.at,
                completed_typing(source, forms@, parameters@, &locals, pending@,
                    job_type(source, forms@, parameters@, &locals, job)) == root,
            decreases pending@.len(),
        {
            let ghost previous = locals;
            let ghost before = pending@;
            let Some(work) = pending.pop() else {
                proof { reveal(completed_typing); }
                return Ok(ty);
            };
            let ghost last = work;
            proof {
                assert(before =~= pending@.push(work));
                pushed_pending_agrees(source, forms@, parameters@, &locals, pending@, work, Ok(ty));
                shrunk_pending_fits(forms@, &locals, pending@, job, work);
            }
            let result = accept_result(source, forms, parameters, &mut locals, work.awaiting, ty, work.child);
            let ghost operation = result;
            proof {
                pending_keeps_earlier_scopes(source, forms@, parameters@, &previous, &locals, pending@,
                    action_type(source, forms@, parameters@, &locals, result));
            }
            match result {
                Err(error) => {
                    proof { reveal(completed_typing); }
                    return Err(error);
                }
                Ok(Action::Visit(child, waiting)) => {
                    proof { advance_after_pop(forms@, pending@, job, last, operation->Ok_0); }
                    job = attach_action(source, forms, parameters, &locals, &mut pending, job, child, waiting);
                    break;
                }
                Ok(Action::Typed(completed)) => ty = completed,
            }
        }
    }
}

pub(super) closed spec fn typed_body<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, expected: TypeShape,
) -> BodyVerdict<'a> {
    match typed_expression(source, forms, env, Request { at, expected, list: None }, Goal::Check(expected)) {
        Ok(_) => BodyVerdict::Accepted,
        Err(error) => BodyVerdict::Rejected(error),
    }
}

pub(super) fn check_typed_body<'a>(
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], at: usize, expected: TypeShape,
) -> (verdict: BodyVerdict<'a>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures verdict == typed_body(source, forms@, environment_view(parameters@), at, expected),
{
    match type_with_scopes(source, forms, parameters, at, expected) {
        Ok(_) => BodyVerdict::Accepted,
        Err(error) => BodyVerdict::Rejected(error),
    }
}

spec fn inferred_request(at: usize) -> Request {
    Request { at, expected: scalar_type(BuiltinDataType::Bool), list: None }
}

pub(super) closed spec fn inferred_as<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
) -> bool {
    typed_expression(source, forms, env, inferred_request(at), Goal::Infer) == Ok(ty)
}

pub(super) proof fn proven_inference_checks_context<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
)
    requires usable_forms(source, forms), at < forms.len(), inferred_as(source, forms, env, at, ty),
    ensures typed_body(source, forms, env, at, ty) == BodyVerdict::Accepted,
{
    verify_inferred_context(source, forms, env, at, ty);
}

proof fn verify_inferred_context<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
)
    requires usable_forms(source, forms), at < forms.len(), inferred_as(source, forms, env, at, ty),
    ensures typed_expression(source, forms, env, Request { at, expected: ty, list: None }, Goal::Check(ty)) == Ok(ty),
    decreases forms.len() - at, 0nat,
{
    match shape(source, forms, at) {
        Ok(Expression::Let) => {
            let (extended, body) = inferred_let_body(source, forms, env, at, ty);
            verify_inferred_context(source, forms, extended, body, ty);
        }
        Ok(Expression::Conditional { condition, yes, no }) => {
            inferred_branches(source, forms, env, at, ty, condition, yes, no);
            verify_inferred_context(source, forms, env, yes, ty);
            verify_inferred_context(source, forms, env, no, ty);
        }
        Ok(Expression::List) if at + 2 < subtree_limit(forms, at) <= forms.len() => {
            let first = (at + 2) as usize;
            inferred_list_elements(source, forms, env, at, ty);
            let element = inferred_element_type(source, forms, env, at, first, None, ty);
            verify_inferred_elements(source, forms, env, at, first, None, element, ty);
            checked_list_uses_elements(source, forms, env, at, element, ty);
        }
        _ => {
            reveal_with_fuel(typed_expression, 2);
        }
    }
}

proof fn inferred_let_body<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
) -> (body: (Seq<TypeBinding>, usize))
    requires at < forms.len(), inferred_as(source, forms, env, at, ty),
        shape(source, forms, at) == Ok(Expression::Let),
    ensures at < body.1 < forms.len(), inferred_as(source, forms, body.0, body.1, ty),
        typed_body(source, forms, env, at, ty) == typed_body(source, forms, body.0, body.1, ty),
        typed_expression(source, forms, env, Request { at, expected: ty, list: None }, Goal::Check(ty))
            == typed_expression(source, forms, body.0, Request { at: body.1, expected: ty, list: None }, Goal::Check(ty)),
{
    reveal_with_fuel(typed_expression, 2);
    reveal(typed_bindings);
    let (rows, body) = let_structure(source, forms, at)->Ok_0;
    let extended = typed_bindings(source, forms, env, at, body, rows, 0, env)->Ok_0;
    (extended, body)
}

proof fn inferred_branches<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape, condition: usize, yes: usize, no: usize,
)
    requires usable_forms(source, forms), at < forms.len(), inferred_as(source, forms, env, at, ty),
        shape(source, forms, at) == Ok(Expression::Conditional { condition, yes, no }),
    ensures
        at < condition < yes < no < forms.len(),
        inferred_as(source, forms, env, yes, ty), inferred_as(source, forms, env, no, ty),
        typed_expression(source, forms, env, Request { at, expected: ty, list: None }, Goal::Check(ty))
            == ensure_two_checked(source, forms, env,
                Request { at: yes, expected: ty, list: None }, Request { at: no, expected: ty, list: None }, ty),
{
    reveal_with_fuel(typed_expression, 2);
    let actual = typed_expression(source, forms, env, inferred_request(no), Goal::Infer)->Ok_0;
    assert(types_agree(ty, actual, form_span(forms[no as int])) == Ok(()) && ty == actual);
    assert(children3(forms, at) == Some((condition, yes, no)));
}

proof fn inferred_list_elements<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
)
    requires at < forms.len(), inferred_as(source, forms, env, at, ty),
        shape(source, forms, at) == Ok(Expression::List),
        at + 2 < subtree_limit(forms, at) <= forms.len(),
    ensures typed_elements(source, forms, env, at, (at + 2) as usize, None) == Ok(ty),
{
    reveal_with_fuel(typed_expression, 2);
    reveal(typed_elements);
    reveal(finish_element_model);
}

proof fn checked_list_uses_elements<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, element: TypeShape, ty: TypeShape,
)
    requires usable_forms(source, forms), at < forms.len(), at + 2 < subtree_limit(forms, at) <= forms.len(),
        shape(source, forms, at) == Ok(Expression::List), element_forms_list(element, ty),
        typed_expression(source, forms, env,
            Request { at: (at + 2) as usize, expected: element, list: Some(at) }, Goal::Check(element)) == Ok(element),
    ensures typed_expression(source, forms, env, Request { at, expected: ty, list: None }, Goal::Check(ty)) == Ok(ty),
{
    reveal(typed_expression);
    let first = (at + 2) as usize;
    super::super::forms::child_stays_inside(forms, at, first);
    let site = Request { at, expected: ty, list: None };
    assert(step_model(source, forms, env, site) == Ok(CheckStep::One(Request {
        at: first, expected: element, list: Some(at),
    })));
    assert(step_children_fit(forms, at, step_model(source, forms, env, site)->Ok_0));
}

spec fn element_forms_list(element: TypeShape, list: TypeShape) -> bool {
    element.list_depth < usize::MAX && list.list_depth == element.list_depth + 1 && list.builtin == element.builtin
}

proof fn inferred_element_type<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize,
    earlier: Option<TypeShape>, list: TypeShape,
) -> (element: TypeShape)
    requires owner < at < subtree_limit(forms, owner) <= forms.len(),
        typed_elements(source, forms, env, owner, at, earlier) == Ok(list),
    ensures inferred_as(source, forms, env, at, element),
        earlier matches Some(first) ==> first == element,
        element_forms_list(element, list),
    decreases forms.len() - at,
{
    reveal_with_fuel(typed_expression, 2);
    reveal_with_fuel(typed_elements, 2);
    reveal_with_fuel(finish_element_model, 2);
    let element = typed_expression(source, forms, env, inferred_request(at), Goal::Infer)->Ok_0;
    if let Some(first) = earlier {
        assert(types_agree(first, element, form_span(forms[at as int])) == Ok(()));
        assert(first == element);
    }
    let next = subtree_limit(forms, at);
    if next != subtree_limit(forms, owner) {
        assert(at < next < subtree_limit(forms, owner));
        assert(typed_elements(source, forms, env, owner, next, Some(element)) == Ok(list));
        let later = inferred_element_type(source, forms, env, owner, next, Some(element), list);
        assert(later == element);
    }
    element
}

proof fn verify_inferred_elements<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize,
    earlier: Option<TypeShape>, element: TypeShape, list: TypeShape,
)
    requires usable_forms(source, forms), owner < at < subtree_limit(forms, owner) <= forms.len(),
        forms[owner as int] is List,
        typed_elements(source, forms, env, owner, at, earlier) == Ok(list),
        element_forms_list(element, list),
    ensures typed_expression(source, forms, env, Request { at, expected: element, list: Some(owner) }, Goal::Check(element))
        == Ok(element),
    decreases forms.len() - at, 1nat,
{
    let item = inferred_element_type(source, forms, env, owner, at, earlier, list);
    assert(item == element);
    verify_inferred_context(source, forms, env, at, element);
    super::super::forms::child_stays_inside(forms, owner, at);
    let next = subtree_limit(forms, at);
    if next < subtree_limit(forms, owner) {
        list_remainder_has_type(source, forms, env, owner, at, earlier, element, list);
        verify_inferred_elements(source, forms, env, owner, next, Some(element), element, list);
    }
    checked_item_with_peers(source, forms, env, owner, at, element);
}

proof fn list_remainder_has_type<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize,
    earlier: Option<TypeShape>, element: TypeShape, list: TypeShape,
)
    requires owner < at < subtree_limit(forms, at) < subtree_limit(forms, owner) <= forms.len(),
        typed_elements(source, forms, env, owner, at, earlier) == Ok(list),
        inferred_as(source, forms, env, at, element), earlier matches Some(first) ==> first == element,
    ensures typed_elements(source, forms, env, owner, subtree_limit(forms, at), Some(element)) == Ok(list),
{
    hide(shape);
    hide(step_model);
    reveal_with_fuel(typed_elements, 2);
    reveal_with_fuel(finish_element_model, 2);
    reveal(typed_expression);
}

proof fn checked_item_with_peers<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize, element: TypeShape,
)
    requires
        request_ready(forms, Request { at, expected: element, list: Some(owner) }),
        typed_expression(source, forms, env, Request { at, expected: element, list: None }, Goal::Check(element)) == Ok(element),
        remaining_elements(forms, Request { at, expected: element, list: Some(owner) }) matches Some(next) ==>
            typed_expression(source, forms, env, next, Goal::Check(element)) == Ok(element),
    ensures typed_expression(source, forms, env, Request { at, expected: element, list: Some(owner) }, Goal::Check(element))
        == Ok(element),
{
    reveal_with_fuel(typed_expression, 2);
    let single = Request { at, expected: element, list: None };
    let peers = Request { at, expected: element, list: Some(owner) };
    assert(step_model(source, forms, env, single) == step_model(source, forms, env, peers));
}

proof fn list_type_rules_have_examples() {
    let source = "(list)";
    let forms = seq![
        Form::List { span: 0usize..6usize, end: 2usize },
        Form::Atom { span: 1usize..5usize, kind: AtomKind::Name },
    ];
    reveal_strlit("(list)");
    reveal_strlit("list");
    reveal_strlit("as-type");
    reveal_strlit("if");
    reveal_strlit("fn");
    vstd::string::is_ascii_spec_bytes(source);
    vstd::string::is_ascii_spec_bytes("list");
    vstd::utf8::encode_utf8_decode_utf8("list"@);
    vstd::utf8::encode_utf8_decode_utf8("as-type"@);
    vstd::utf8::encode_utf8_decode_utf8("if"@);
    vstd::utf8::encode_utf8_decode_utf8("fn"@);
    assert(spelling(source, forms[1]) =~= "list".spec_bytes());
    assert("list".spec_bytes() != "as-type".spec_bytes()
        && "list".spec_bytes() != "if".spec_bytes()
        && "list".spec_bytes() != "fn".spec_bytes());
    assert(keyword(spelling(source, forms[1])) == Some(FormTag::List));
    assert(forms.len() == 2 && forms[0] is List && forms[0]->List_end == 2 && plain_name(forms[1]));
    assert(shape(source, forms, 0) == Ok(Expression::List));
    let env = Seq::<TypeBinding>::empty();
    let list = Request {
        at: 0,
        expected: TypeShape { builtin: Some(BuiltinDataType::Bool), list_depth: 1 },
        list: None,
    };
    let scalar = Request { at: 0, expected: scalar_type(BuiltinDataType::Bool), list: None };
    let error = ExpressionCheckFailure::Type(ExpressionTypeError::ListInScalarContext(0usize..6usize));
    assert(step_model(source, forms, env, list) == Ok(CheckStep::Done));
    assert(step_model(source, forms, env, scalar) == Err(error));
    reveal(typed_expression);
    assert(typed_body(source, forms, env, 0, list.expected) == BodyVerdict::Accepted);
    assert(typed_body(source, forms, env, 0, scalar.expected) == BodyVerdict::Rejected(error));
}

proof fn parallel_binding_has_examples() {
    use super::super::let_syntax::{parallel_let_example_forms, parallel_let_example_layout};
    parallel_let_example_layout();
    let source = "(let ((x true)(y x)) y)";
    let forms = parallel_let_example_forms();
    reveal_strlit("as-type");
    reveal_strlit("if");
    reveal_strlit("fn");
    reveal_strlit("list");
    reveal_strlit("let");
    reveal_strlit("x");
    reveal_strlit("y");
    reveal_strlit("true");
    reveal_strlit("false");
    vstd::utf8::encode_utf8_decode_utf8("as-type"@);
    vstd::utf8::encode_utf8_decode_utf8("if"@);
    vstd::utf8::encode_utf8_decode_utf8("fn"@);
    vstd::utf8::encode_utf8_decode_utf8("list"@);
    vstd::utf8::encode_utf8_decode_utf8("let"@);
    vstd::utf8::encode_utf8_decode_utf8("x"@);
    vstd::utf8::encode_utf8_decode_utf8("y"@);
    vstd::utf8::encode_utf8_decode_utf8("true"@);
    vstd::utf8::encode_utf8_decode_utf8("false"@);
    assert(keyword(spelling(source, forms[1])) == Some(FormTag::Let));
    assert(shape(source, forms, 0) == Ok(Expression::Let));
    assert(shape(source, forms, 5) == Ok(Expression::Bool));
    assert(shape(source, forms, 8) == Ok(Expression::Parameter));
    assert(shape(source, forms, 9) == Ok(Expression::Parameter));
    let boolean = scalar_type(BuiltinDataType::Bool);
    let empty = Seq::<TypeBinding>::empty();
    let outer = seq![("x".spec_bytes(), boolean)];
    let error = ExpressionCheckFailure::Deferred(DeferredExpression::Name(17usize..18usize));
    parallel_binding_example_unfolding(source, forms, boolean, empty, outer, error);
}

proof fn parallel_binding_example_unfolding<'a>(
    source: &'a str, forms: Seq<Form>, boolean: TypeShape, empty: Seq<TypeBinding>, outer: Seq<TypeBinding>,
    error: ExpressionCheckFailure<'a>,
)
    requires
        forms.len() == 10,
        boolean == scalar_type(BuiltinDataType::Bool),
        empty =~= Seq::<TypeBinding>::empty(), outer =~= seq![("x".spec_bytes(), boolean)],
        error == ExpressionCheckFailure::Deferred(DeferredExpression::Name(17usize..18usize)),
        form_span(forms[8]) == (17usize..18usize),
        let_structure(source, forms, 0) == Ok((seq![LocalBinding { name: 4, value: 5 }, LocalBinding { name: 7, value: 8 }], 9)),
        spelling(source, forms[4]) == "x".spec_bytes(), spelling(source, forms[5]) == "true".spec_bytes(),
        spelling(source, forms[7]) == "y".spec_bytes(), spelling(source, forms[8]) == "x".spec_bytes(),
        spelling(source, forms[9]) == "y".spec_bytes(),
        "x".spec_bytes() != "true".spec_bytes(),
        shape(source, forms, 0) == Ok(Expression::Let), shape(source, forms, 5) == Ok(Expression::Bool),
        shape(source, forms, 8) == Ok(Expression::Parameter), shape(source, forms, 9) == Ok(Expression::Parameter),
    ensures
        typed_body(source, forms, empty, 0, boolean) == BodyVerdict::Rejected(error),
        typed_body(source, forms, outer, 0, boolean) == BodyVerdict::Accepted,
{
    reveal_with_fuel(parameter_type, 2);
    inferred_leaf_example(source, forms, empty, 5, Ok(boolean));
    inferred_leaf_example(source, forms, empty, 8, Err(error));
    inferred_leaf_example(source, forms, outer, 5, Ok(boolean));
    inferred_leaf_example(source, forms, outer, 8, Ok(boolean));
    let rows = let_structure(source, forms, 0)->Ok_0.0;
    example_bindings_result(source, forms, empty, rows, Ok(boolean), Err(error));
    example_bindings_result(source, forms, outer, rows, Ok(boolean), Ok(boolean));
    let extended = seq![("y".spec_bytes(), boolean)] + (seq![("x".spec_bytes(), boolean)] + outer);
    let body = Request { at: 9, expected: boolean, list: None };
    assert(step_model(source, forms, extended, body) == Ok(CheckStep::Done));
    assert(typed_bindings(source, forms, outer, 0, 9, rows, 0, outer) == Ok(extended));
    checked_leaf_example(source, forms, extended, body);
    reveal_with_fuel(typed_expression, 2);
    reveal(typed_bindings);
    assert(typed_body(source, forms, outer, 0, boolean) == typed_body(source, forms, extended, 9, boolean));
}

proof fn checked_leaf_example<'a>(source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request)
    requires request.at < forms.len(), request.list.is_none(),
        shape(source, forms, request.at) != Ok(Expression::Let),
        step_model(source, forms, env, request) == Ok(CheckStep::Done),
    ensures typed_expression(source, forms, env, request, Goal::Check(request.expected)) == Ok(request.expected),
{
    reveal(typed_expression);
}

proof fn inferred_leaf_example<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize,
    result: Result<TypeShape, ExpressionCheckFailure<'a>>,
)
    requires
        at < forms.len(),
        shape(source, forms, at) == Ok(Expression::Bool) || shape(source, forms, at) == Ok(Expression::Parameter),
        synthesized_type(source, forms, env, at) == result,
        result matches Ok(ty) ==> step_model(source, forms, env, Request { at, expected: ty, list: None }) == Ok(CheckStep::Done),
    ensures typed_expression(source, forms, env, inferred_request(at), Goal::Infer) == result,
{
    reveal_with_fuel(typed_expression, 2);
}

proof fn example_bindings_result<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, rows: Seq<LocalBinding>,
    first: Result<TypeShape, ExpressionCheckFailure<'a>>, second: Result<TypeShape, ExpressionCheckFailure<'a>>,
)
    requires
        forms.len() == 10,
        rows == seq![LocalBinding { name: 4, value: 5 }, LocalBinding { name: 7, value: 8 }],
        typed_expression(source, forms, env, inferred_request(5), Goal::Infer) == first,
        typed_expression(source, forms, env, inferred_request(8), Goal::Infer) == second,
    ensures typed_bindings(source, forms, env, 0, 9, rows, 0, env) ==
        match first {
            Err(error) => Err(error),
            Ok(left) => match second {
                Err(error) => Err(error),
                Ok(right) => Ok(seq![(spelling(source, forms[7]), right)]
                    + (seq![(spelling(source, forms[4]), left)] + env)),
            },
        },
{
    hide(shape);
    hide(step_model);
    reveal(typed_expression);
    reveal_with_fuel(typed_bindings, 3);
}

}
