//! 期待型付きの検査と型合成を、式ごとの型環境で進める。

use super::*;
use super::super::let_syntax::LetHeader;
use super::fold::checked_fold_item;
#[cfg(verus_only)]
use super::fold::fold_item_type;

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

/// 呼び出し先の署名から渡される、引数位置と期待型。
pub(super) struct CallArgument {
    pub(super) at: usize,
    pub(super) expected: TypeShape,
}

/// 本体を検査する前に確定した、一つの宣言呼び出しの型情報。
pub(super) struct CallTypeEntry {
    pub(super) at: usize,
    pub(super) arguments: Vec<CallArgument>,
    pub(super) result: TypeShape,
}

spec fn call_entry_at(calls: Seq<CallTypeEntry>, at: usize) -> Option<usize> {
    if exists|i: usize| i < calls.len() && (#[trigger] calls[i as int]).at == at {
        Some(choose|i: usize| i < calls.len() && (#[trigger] calls[i as int]).at == at)
    } else { None }
}

pub(super) open spec fn call_entries_sorted(calls: Seq<CallTypeEntry>) -> bool {
    forall|i: int, j: int| 0 <= i < j < calls.len() ==> (#[trigger] calls[i]).at < (#[trigger] calls[j]).at
}

pub(super) open spec fn canonical_call(forms: Seq<Form>, call: CallTypeEntry) -> bool {
    &&& call.at < forms.len()
    &&& forms[call.at as int] is List
    &&& call.at + 2 <= subtree_limit(forms, call.at) <= forms.len()
    &&& if call.arguments@.len() == 0 {
        call.at + 2 == subtree_limit(forms, call.at)
    } else {
        call.arguments@[0].at == call.at + 2
    }
    &&& forall|i: int| 0 <= i < call.arguments@.len() ==> {
        let arg = #[trigger] call.arguments@[i];
        &&& call.at < arg.at < subtree_limit(forms, arg.at) <= subtree_limit(forms, call.at)
        &&& if i + 1 < call.arguments@.len() {
            subtree_limit(forms, arg.at) == call.arguments@[i + 1].at
        } else { subtree_limit(forms, arg.at) == subtree_limit(forms, call.at) }
    }
}

pub(super) open spec fn call_entries_fit(forms: Seq<Form>, calls: Seq<CallTypeEntry>) -> bool {
    call_entries_sorted(calls)
        && forall|i: int| 0 <= i < calls.len() ==> canonical_call(forms, #[trigger] calls[i])
}

fn find_call_entry(calls: &[CallTypeEntry], at: usize) -> (entry: Option<usize>)
    requires call_entries_sorted(calls@),
    ensures entry == call_entry_at(calls@, at),
{
    let mut low = 0;
    let mut high = calls.len();
    while low < high
        invariant call_entries_sorted(calls@), low <= high <= calls@.len(),
            forall|i: int| 0 <= i < low ==> (#[trigger] calls@[i]).at < at,
            forall|i: int| high <= i < calls@.len() ==> at < (#[trigger] calls@[i]).at,
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        let start = calls[mid].at;
        if start == at {
            proof {
                let chosen = call_entry_at(calls@, at)->Some_0;
                assert((exists|i: usize| i < calls@.len() && (#[trigger] calls@[i as int]).at == at));
                if chosen < mid { assert(calls@[chosen as int].at < calls@[mid as int].at); }
                if mid < chosen { assert(calls@[mid as int].at < calls@[chosen as int].at); }
            }
            return Some(mid);
        } else if start < at {
            assert forall|i: int| low <= i <= mid implies (#[trigger] calls@[i]).at < at by {
                if i < mid { assert(calls@[i].at < calls@[mid as int].at); }
            };
            low = mid + 1;
        } else {
            assert forall|i: int| mid <= i < high implies at < (#[trigger] calls@[i]).at by {
                if mid < i { assert(calls@[mid as int].at < calls@[i].at); }
            };
            high = mid;
        }
    }
    None
}

spec fn declared_call_result<'a>(goal: Goal, actual: TypeShape, span: Range<usize>)
    -> Result<TypeShape, ExpressionCheckFailure<'a>>
{
    match goal {
        Goal::Check(expected) => match types_agree(expected, actual, span) {
            Ok(()) => Ok(expected),
            Err(error) => Err(error),
        },
        Goal::Infer if actual.builtin.is_some() => Ok(actual),
        Goal::Infer => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span))),
    }
}

fn call_result_type<'a>(goal: Goal, actual: TypeShape, span: Range<usize>)
    -> (out: Result<TypeShape, ExpressionCheckFailure<'a>>)
    ensures out == declared_call_result(goal, actual, span),
{
    match goal {
        Goal::Check(expected) => {
            conform(expected, actual, span)?;
            Ok(expected)
        },
        Goal::Infer if actual.builtin.is_some() => Ok(actual),
        Goal::Infer => Err(ExpressionCheckFailure::Deferred(DeferredExpression::StageType(span))),
    }
}

spec fn argument_cursor(forms: Seq<Form>, call: CallTypeEntry, i: nat) -> usize {
    if i < call.arguments@.len() { call.arguments@[i as int].at }
    else { subtree_limit(forms, call.at) }
}

#[verifier::opaque]
spec fn typed_call_arguments<'a>(
    calls: Seq<CallTypeEntry>, source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>,
    call: CallTypeEntry, i: nat,
) -> Result<(), ExpressionCheckFailure<'a>>
    decreases forms.len() - argument_cursor(forms, call, i), 3nat, 0nat,
{
    if i >= call.arguments@.len() {
        Ok(())
    } else {
        let arg = call.arguments@[i as int];
        if !(arg.at < argument_cursor(forms, call, i + 1) <= forms.len()) {
            Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(form_span(forms[call.at as int]))))
        } else {
            let request = Request { at: arg.at, expected: arg.expected, list: None };
            match typed_expression(calls, source, forms, env, request, Goal::Check(arg.expected)) {
                Err(error) => Err(error),
                Ok(_) => typed_call_arguments(calls, source, forms, env, call, i + 1),
            }
        }
    }
}

spec fn attach_call_type<'a>(checked: Result<(), ExpressionCheckFailure<'a>>, result: TypeShape)
    -> Result<TypeShape, ExpressionCheckFailure<'a>>
{
    match checked { Ok(()) => Ok(result), Err(error) => Err(error) }
}

spec fn applicable_call(calls: Seq<CallTypeEntry>, source: &str, forms: Seq<Form>, at: usize) -> Option<usize> {
    if shape(source, forms, at) matches Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(_))) {
        call_entry_at(calls, at)
    } else { None }
}

#[verifier::opaque]
spec fn typed_declared_call<'a>(
    calls: Seq<CallTypeEntry>, source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>,
    at: usize, goal: Goal, entry: usize,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - at, 1nat, 0nat,
{
    let call = calls[entry as int];
    let span = form_span(forms[at as int]);
    match declared_call_result(goal, call.result, span) {
        Err(error) => Err(error),
        Ok(ty) => {
            if at < argument_cursor(forms, call, 0) <= forms.len() {
                attach_call_type(typed_call_arguments(calls, source, forms, env, call, 0), ty)
            } else { unknown_form(span) }
        }
    }
}

#[verifier::opaque]
spec fn typed_expression<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, goal: Goal,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - request.at, 2nat, goal_rank(goal),
{
    let at = request.at;
    let span = form_span(forms[at as int]);
    let result = if at >= forms.len() {
        unknown_form(0..0)
    } else if let Some(entry) = applicable_call(calls, source, forms, at) {
        typed_declared_call(calls, source, forms, env, at, goal, entry)
    } else if shape(source, forms, at) == Ok(Expression::Let) {
        match let_structure(source, forms, at) {
            Err(error) => Err(ExpressionCheckFailure::Type(ExpressionTypeError::Let(error))),
            Ok((rows, body)) if at < body < forms.len() => {
                match typed_bindings(calls, source, forms, env, at, body, rows, 0, env) {
                    Err(error) => Err(error),
                    Ok(extended) => {
                        typed_expression(calls, source, forms, extended, Request { at: body, list: None, ..request }, goal)
                    },
                }
            },
            Ok(_) => unknown_form(span),
        }
    } else if let Ok(Expression::Fold(header)) = shape(source, forms, at) {
        typed_fold(calls, source, forms, env, at, header, goal)
    } else {
        match goal {
            Goal::Check(expected) => match step_model(source, forms, env, Request { expected, ..request }) {
                Err(error) => Err(error),
                Ok(step) if !step_children_fit(forms, at, step) => unknown_form(span),
                Ok(CheckStep::Done) => Ok(expected),
                Ok(CheckStep::One(child)) => match typed_expression(calls, source, forms, env, child, Goal::Check(child.expected)) {
                    Err(error) => Err(error),
                    Ok(_) => Ok(expected),
                },
                Ok(CheckStep::Three(condition, yes, no)) =>
                    match typed_expression(calls, source, forms, env, condition, Goal::Check(condition.expected)) {
                        Err(error) => Err(error),
                        Ok(_) => match typed_expression(calls, source, forms, env, yes, Goal::Check(yes.expected)) {
                            Err(error) => Err(error),
                            Ok(_) => match typed_expression(calls, source, forms, env, no, Goal::Check(no.expected)) {
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
                        match typed_expression(calls, source, forms, env, cond, Goal::Check(boolean)) {
                            Err(error) => Err(error),
                            Ok(_) => match typed_expression(calls, source, forms, env, Request { at: yes, ..cond }, Goal::Infer) {
                                Err(error) => Err(error),
                                Ok(expected) => compare_inferred_branch(forms, no, expected,
                                    typed_expression(calls, source, forms, env, Request { at: no, ..cond }, Goal::Infer)),
                            },
                        }
                    },
                    Ok(Expression::List) if at + 2 < subtree_limit(forms, at) <= forms.len() =>
                        typed_elements(calls, source, forms, env, at, (at + 2) as usize, None),
                    _ => match synthesized_type(source, forms, env, at) {
                        Err(error) => Err(error),
                        Ok(expected) => typed_expression(calls, source, forms, env, Request { expected, ..request }, Goal::Check(expected)),
                    },
                }
            }
        }
    };
    match result {
        Err(error) => Err(error),
        Ok(ty) => match remaining_elements(forms, request) {
            None => Ok(ty),
            Some(next) => match typed_expression(calls, source, forms, env, next, goal) {
                Err(error) => Err(error),
                Ok(_) => Ok(ty),
            },
        },
    }
}

spec fn fold_input_request(header: FoldHeader) -> (Request, Goal) {
    match header.kind {
        FoldKind::Nat => {
            let nat_type = scalar_type(BuiltinDataType::Integer(IntegerType::Nat));
            (Request { at: header.input, expected: nat_type, list: None }, Goal::Check(nat_type))
        }
        FoldKind::List => (inferred_request(header.input), Goal::Infer),
    }
}

spec fn fold_initial_request(header: FoldHeader, goal: Goal) -> Request {
    match goal {
        Goal::Check(ty) => Request { at: header.initial, expected: ty, list: None },
        Goal::Infer => inferred_request(header.initial),
    }
}

spec fn fold_environment(
    source: &str, forms: Seq<Form>, env: Seq<TypeBinding>, header: FoldHeader, item: TypeShape, accumulator: TypeShape,
) -> Seq<TypeBinding> {
    seq![(spelling(source, forms[header.accumulator as int]), accumulator)]
        + (seq![(spelling(source, forms[header.item as int]), item)] + env)
}

#[verifier::opaque]
spec fn typed_fold<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, header: FoldHeader, goal: Goal,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - at, 1nat, 0nat,
{
    if fold_positions(forms, at, header) {
        let (input, goal_for_input) = fold_input_request(header);
        match typed_expression(calls, source, forms, env, input, goal_for_input) {
            Err(error) => Err(error),
            Ok(ty) => match fold_item_type(header.kind, ty, form_span(forms[header.input as int])) {
                Err(error) => Err(error),
                Ok(item_type) => match typed_expression(calls, source, forms, env, fold_initial_request(header, goal), goal) {
                    Err(error) => Err(error),
                    Ok(accumulator) => {
                        let body = Request { at: header.body, expected: accumulator, list: None };
                        typed_expression(calls, source, forms, fold_environment(source, forms, env, header, item_type, accumulator),
                            body, Goal::Check(accumulator))
                    }
                },
            },
        }
    } else {
        unknown_form(form_span(forms[at as int]))
    }
}

spec fn typed_bindings<'a>(
    calls: Seq<CallTypeEntry>,
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
            match typed_expression(calls, source, forms, outer, value, Goal::Infer) {
                Err(error) => Err(error),
                Ok(ty) => {
                    let name = spelling(source, forms[row.name as int]);
                    typed_bindings(calls, source, forms, outer, owner, body, rows, from + 1, seq![(name, ty)] + extended)
                },
            }
        }
    }
}

spec fn typed_elements<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, owner: usize, at: usize, first: Option<TypeShape>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>>
    decreases forms.len() - at, 3nat, 0nat,
{
    let end = subtree_limit(forms, owner);
    if !(owner < at < end <= forms.len()) {
        unknown_form(form_span(forms[owner as int]))
    } else {
        let request = Request { at, expected: scalar_type(BuiltinDataType::Bool), list: None };
        match typed_expression(calls, source, forms, env, request, Goal::Infer) {
            Err(error) => Err(error),
            Ok(actual) => finish_element_model(calls, source, forms, env, owner, at, first, actual),
        }
    }
}

spec fn finish_element_model<'a>(
    calls: Seq<CallTypeEntry>,
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
                typed_elements(calls, source, forms, env, owner, next, Some(ty))
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
    Fold(FoldHeader),
}

#[cfg(verus_only)]
enum PlanModel {
    Check(CheckStep, TypeShape),
    InferConditional { condition: usize, yes: usize, no: usize },
    InferList { first: usize },
    Let { rows: Seq<LocalBinding>, body: usize },
    Fold(FoldHeader),
}

spec fn project_plan(plan: FormPlan) -> PlanModel {
    match plan {
        FormPlan::Check(step, ty) => PlanModel::Check(step, ty),
        FormPlan::InferConditional { condition, yes, no } => PlanModel::InferConditional { condition, yes, no },
        FormPlan::InferList { first } => PlanModel::InferList { first },
        FormPlan::Let(header) => PlanModel::Let { rows: header.bindings@, body: header.body },
        FormPlan::Fold(header) => PlanModel::Fold(header),
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
        Ok(Expression::Fold(header)) => Ok(PlanModel::Fold(header)),
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
        FormPlan::Fold(header) => fold_positions(forms, parent, header),
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
    locals: &LocalScopes<'a>, scope: Scope, request: Request, goal: Goal, parsed: Result<Expression, ExpressionCheckFailure<'a>>,
) -> (result: Result<FormPlan, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), request.at < forms@.len(), locals.contains(scope),
        parsed == shape(source, forms@, request.at),
        parsed matches Ok(Expression::Fold(fold)) ==> fold_positions(forms@, request.at, fold),
    ensures
        (match result { Err(error) => Err(error), Ok(plan) => Ok(project_plan(plan)) })
            == form_plan(source, forms@, lexical_view(parameters@, locals, scope), request, goal),
        result matches Ok(plan) ==> planned_children_fit(forms@, request.at, plan),
{
    let at = request.at;
    let expr = parsed?;
    if let Expression::Fold(header) = expr {
        return Ok(FormPlan::Fold(header));
    }
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
    Call { entry: usize, argument: usize, scope: Scope, result: TypeShape },
    Peer(Job),
    CheckedCondition { yes_request: Request, no_request: Request, scope: Scope },
    CheckedYes { no_request: Request, scope: Scope },
    InferredCondition { yes: usize, no: usize, scope: Scope },
    InferredYes { no: usize, scope: Scope },
    InferredNo { no: usize, expected: TypeShape },
    Element { at: usize, owner: usize, element: Option<TypeShape>, scope: Scope },
    Binding { header: LetHeader, binding_owner: Job, index: usize, body_scope: Scope },
    FoldInput { fold: FoldHeader, goal: Goal, scope: Scope },
    FoldInitial { fold: FoldHeader, item_type: TypeShape, scope: Scope },
}

enum Action {
    Typed(TypeShape),
    Visit(Job, Option<Await>),
}

spec fn job_in_bounds(forms: Seq<Form>, job: Job) -> bool {
    &&& job.request.at < forms.len()
    &&& job.request.list.is_some() ==> request_ready(forms, job.request) && job.goal == Goal::Check(job.request.expected)
}

spec fn wait_in_bounds(calls: Seq<CallTypeEntry>, forms: Seq<Form>, awaiting: Await) -> bool {
    match awaiting {
        Await::Result(_) => true,
        Await::Call { entry, argument, .. } => entry < calls.len()
            && canonical_call(forms, calls[entry as int])
            && argument < calls[entry as int].arguments@.len(),
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
        Await::FoldInput { fold, .. } | Await::FoldInitial { fold, .. } => fold_positions(forms, fold._at, fold),
    }
}

spec fn wait_has_scopes(locals: &LocalScopes, awaiting: Await) -> bool {
    match awaiting {
        Await::Call { scope, .. } => locals.contains(scope),
        Await::Peer(job) => locals.contains(job.scope),
        Await::CheckedCondition { scope, .. } | Await::CheckedYes { scope, .. }
        | Await::InferredCondition { scope, .. } | Await::InferredYes { scope, .. }
        | Await::Element { scope, .. } | Await::FoldInput { scope, .. }
        | Await::FoldInitial { scope, .. } => locals.contains(scope),
        Await::Binding { binding_owner, body_scope, .. } =>
            locals.contains(binding_owner.scope) && locals.contains(body_scope),
        _ => true,
    }
}

spec fn action_valid(calls: Seq<CallTypeEntry>, forms: Seq<Form>, locals: &LocalScopes, action: Action) -> bool {
    match action {
        Action::Typed(_) => true,
        Action::Visit(job, awaiting) => {
            &&& job_in_bounds(forms, job)
            &&& locals.contains(job.scope)
            &&& awaiting matches Some(frame) ==> wait_in_bounds(calls, forms, frame) && wait_has_scopes(locals, frame)
        }
    }
}

spec fn wait_limit(calls: Seq<CallTypeEntry>, forms: Seq<Form>, waiting: Await, child: Job) -> usize {
    match waiting {
        Await::Result(_) | Await::InferredNo { .. } => request_limit(forms, child.request),
        Await::Call { entry, .. } => subtree_limit(forms, calls[entry as int].at),
        Await::Peer(next) => request_limit(forms, next.request),
        Await::CheckedCondition { no_request: no, .. } | Await::CheckedYes { no_request: no, .. } => request_limit(forms, no),
        Await::InferredCondition { no, .. } | Await::InferredYes { no, .. } => subtree_limit(forms, no),
        Await::Element { owner, .. } => subtree_limit(forms, owner),
        Await::Binding { header, .. } => subtree_limit(forms, header.body),
        Await::FoldInput { fold, .. } | Await::FoldInitial { fold, .. } => subtree_limit(forms, fold.body),
    }
}

spec fn wait_follows(calls: Seq<CallTypeEntry>, forms: Seq<Form>, waiting: Await, child: Job) -> bool {
    let end = request_limit(forms, child.request);
    &&& request_ready(forms, child.request)
    &&& end <= wait_limit(calls, forms, waiting, child) <= forms.len()
    &&& match waiting {
        Await::Result(_) | Await::InferredNo { .. } => true,
        Await::Call { entry, argument, .. } => {
            let arg = calls[entry as int].arguments@[argument as int];
            child.request.at == arg.at && child.request.list.is_none()
                && child.goal == Goal::Check(arg.expected)
        }
        Await::Peer(next) => end <= next.request.at,
        Await::CheckedCondition { yes_request: yes, no_request: no, .. } => end <= yes.at && request_limit(forms, yes) <= no.at,
        Await::CheckedYes { no_request: no, .. } => end <= no.at,
        Await::InferredCondition { yes, no, .. } => end <= yes && subtree_limit(forms, yes) <= no,
        Await::InferredYes { no, .. } => end <= no,
        Await::Element { at, owner, .. } => child.request.at == at && child.request.list.is_none()
            && forms[owner as int] is List,
        Await::Binding { header, index, .. } => index < header.bindings@.len()
            && child.request.at == header.bindings@[index as int].value && child.request.list.is_none(),
        Await::FoldInput { fold, .. } => child.request.at == fold.input && child.request.list.is_none(),
        Await::FoldInitial { fold, .. } => child.request.at == fold.initial && child.request.list.is_none(),
    }
}

spec fn action_limit(calls: Seq<CallTypeEntry>, forms: Seq<Form>, action: Action) -> usize {
    match action {
        Action::Typed(_) => 0,
        Action::Visit(job, pending) => match pending {
            None => request_limit(forms, job.request),
            Some(waiting) => wait_limit(calls, forms, waiting, job),
        },
    }
}

spec fn action_advances(calls: Seq<CallTypeEntry>, forms: Seq<Form>, action: Action, before: usize) -> bool {
    match action {
        Action::Typed(_) => true,
        Action::Visit(job, pending) => before <= job.request.at
            && request_ready(forms, job.request)
            && (pending matches Some(frame) ==> wait_follows(calls, forms, frame, job)),
    }
}

spec fn job_type<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes, job: Job,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    typed_expression(calls, source, forms, lexical_view(parameters, locals, job.scope), job.request, job.goal)
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
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    frame: Await, ty: TypeShape,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match frame {
        Await::Result(expected) => Ok(expected),
        Await::Call { entry, argument, scope, result } => attach_call_type(
            typed_call_arguments(calls, source, forms, lexical_view(parameters, locals, scope),
                calls[entry as int], (argument + 1) as nat), result),
        Await::Peer(job) => job_type(calls, source, forms, parameters, locals, job),
        Await::CheckedCondition { yes_request: yes, no_request: no, scope } => {
            let env = lexical_view(parameters, locals, scope);
            match typed_expression(calls, source, forms, env, yes, Goal::Check(yes.expected)) {
                Err(error) => Err(error),
                Ok(_) => typed_expression(calls, source, forms, env, no, Goal::Check(no.expected)),
            }
        }
        Await::CheckedYes { no_request: no, scope } => {
            typed_expression(calls, source, forms, lexical_view(parameters, locals, scope), no, Goal::Check(no.expected))
        }
        Await::InferredCondition { yes, no, scope } => {
            let env = lexical_view(parameters, locals, scope);
            let yes = Request { at: yes, expected: scalar_type(BuiltinDataType::Bool), list: None };
            let no = Request { at: no, ..yes };
            match typed_expression(calls, source, forms, env, yes, Goal::Infer) {
                Err(error) => Err(error),
                Ok(yes_ty) => compare_inferred_branch(forms, no.at, yes_ty, typed_expression(calls, source, forms, env, no, Goal::Infer)),
            }
        }
        Await::InferredYes { no, scope } => {
            let request = Request { at: no, expected: scalar_type(BuiltinDataType::Bool), list: None };
            let env = lexical_view(parameters, locals, scope);
            compare_inferred_branch(forms, no, ty, typed_expression(calls, source, forms, env, request, Goal::Infer))
        }
        Await::InferredNo { no, expected } => compare_inferred_branch(forms, no, expected, Ok(ty)),
        Await::Element { at, owner, element, scope } => {
            let env = lexical_view(parameters, locals, scope);
            finish_element_model(calls, source, forms, env, owner, at, element, ty)
        }
        Await::Binding { header, binding_owner: owner, index, body_scope } => {
            let binding = header.bindings@[index as int];
            let typed = (spelling(source, forms[binding.name as int]), ty);
            let env = lexical_view(parameters, locals, owner.scope);
            let extended = seq![typed] + lexical_view(parameters, locals, body_scope);
            continue_bindings(calls, source, forms, env, owner, header, (index + 1) as nat, extended)
        }
        Await::FoldInput { fold, goal, scope } => {
            let env = lexical_view(parameters, locals, scope);
            match fold_item_type(fold.kind, ty, form_span(forms[fold.input as int])) {
                Err(error) => Err(error),
                Ok(item) => match typed_expression(calls, source, forms, env, fold_initial_request(fold, goal), goal) {
                    Err(error) => Err(error),
                    Ok(accumulator) => typed_expression(calls, source, forms,
                        fold_environment(source, forms, env, fold, item, accumulator),
                        Request { at: fold.body, expected: accumulator, list: None }, Goal::Check(accumulator)),
                },
            }
        }
        Await::FoldInitial { fold, item_type, scope } => {
            let env = lexical_view(parameters, locals, scope);
            typed_expression(calls, source, forms, fold_environment(source, forms, env, fold, item_type, ty),
                Request { at: fold.body, expected: ty, list: None }, Goal::Check(ty))
        }
    }
}

spec fn continue_bindings<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, outer: Seq<TypeBinding>, owner: Job, header: LetHeader,
    from: nat, extended: Seq<TypeBinding>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match typed_bindings(calls, source, forms, outer, owner.request.at, header.body, header.bindings@, from, extended) {
        Err(error) => Err(error),
        Ok(body_env) => typed_expression(calls, source, forms, body_env, Request { at: header.body, list: None, ..owner.request }, owner.goal),
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
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    result: Result<Action, ExpressionCheckFailure<'a>>,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match result {
        Err(error) => Err(error),
        Ok(Action::Typed(ty)) => Ok(ty),
        Ok(Action::Visit(job, tail)) => match job_type(calls, source, forms, parameters, locals, job) {
            Err(error) => Err(error),
            Ok(ty) => match tail {
                None => Ok(ty),
                Some(frame) => resumed_type(calls, source, forms, parameters, locals, frame, ty),
            },
        },
    }
}

proof fn named_call_equation<'a>(
    calls: Seq<CallTypeEntry>, source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>,
    request: Request, goal: Goal, entry: usize,
)
    requires request.at < forms.len(), applicable_call(calls, source, forms, request.at) == Some(entry),
    ensures typed_expression(calls, source, forms, env, request, goal)
        == match (typed_declared_call(calls, source, forms, env, request.at, goal, entry), remaining_elements(forms, request)) {
            (Err(error), _) => Err(error),
            (Ok(ty), None) => Ok(ty),
            (Ok(ty), Some(peer)) => match typed_expression(calls, source, forms, env, peer, goal) {
                Err(error) => Err(error),
                Ok(_) => Ok(ty),
            },
        },
{
    reveal_with_fuel(typed_expression, 2);
    reveal_with_fuel(typed_declared_call, 2);
    assert(applicable_call(calls, source, forms, request.at)->Some_0 == entry);
}

proof fn declared_call_equation<'a>(
    calls: Seq<CallTypeEntry>, source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>,
    at: usize, goal: Goal, entry: usize,
)
    requires entry < calls.len(), at < argument_cursor(forms, calls[entry as int], 0) <= forms.len(),
    ensures typed_declared_call(calls, source, forms, env, at, goal, entry)
        == match declared_call_result(goal, calls[entry as int].result, form_span(forms[at as int])) {
            Err(error) => Err(error),
            Ok(ty) => attach_call_type(typed_call_arguments(calls, source, forms, env, calls[entry as int], 0), ty),
        },
{
    reveal_with_fuel(typed_declared_call, 2);
    reveal_with_fuel(typed_call_arguments, 2);
}

proof fn call_argument_equation<'a>(
    calls: Seq<CallTypeEntry>, source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, call: CallTypeEntry, at: nat,
)
    requires
        at >= call.arguments@.len()
            || argument_cursor(forms, call, at) < argument_cursor(forms, call, at + 1) <= forms.len(),
    ensures typed_call_arguments(calls, source, forms, env, call, at) == if at >= call.arguments@.len() {
        Ok(())
    } else {
        let arg = call.arguments@[at as int];
        let request = Request { at: arg.at, expected: arg.expected, list: None };
        match typed_expression(calls, source, forms, env, request, Goal::Check(arg.expected)) {
            Err(error) => Err(error),
            Ok(_) => typed_call_arguments(calls, source, forms, env, call, at + 1),
        }
    },
{
    reveal_with_fuel(typed_call_arguments, 2);
    reveal_with_fuel(typed_expression, 2);
}

proof fn checked_answer_is_expected<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, expected: TypeShape, actual: TypeShape,
)
    requires typed_expression(calls, source, forms, env, request, Goal::Check(expected)) == Ok(actual),
    ensures actual == expected,
    decreases forms.len() - request.at,
{

    if let Some(entry) = applicable_call(calls, source, forms, request.at) {
        assert(request.at < forms.len()) by { reveal_with_fuel(typed_expression, 2); };
        named_call_equation(calls, source, forms, env, request, Goal::Check(expected), entry);
        reveal(typed_declared_call);
        let call = calls[entry as int];
        assert(declared_call_result(Goal::Check(expected), call.result, form_span(forms[request.at as int])) == Ok(expected));
        assert(actual == expected);
    } else {
        reveal_with_fuel(typed_expression, 2);
        reveal(typed_bindings);
        if shape(source, forms, request.at) == Ok(Expression::Let) {
        let (rows, body) = let_structure(source, forms, request.at)->Ok_0;
        let extended = typed_bindings(calls, source, forms, env, request.at, body, rows, 0, env)->Ok_0;
        let body_request = Request { at: body, list: None, ..request };
        assert(typed_expression(calls, source, forms, extended, body_request, Goal::Check(expected)) == Ok(actual));
        checked_answer_is_expected(calls, source, forms, extended, body_request, expected, actual);
    } else if let Ok(Expression::Fold(fold)) = shape(source, forms, request.at) {
        reveal(typed_fold);
        let goal = Goal::Check(expected);
        let initial = fold_initial_request(fold, goal);
        let (input, input_goal) = fold_input_request(fold);
        let input_ty = typed_expression(calls, source, forms, env, input, input_goal)->Ok_0;
        let item = fold_item_type(fold.kind, input_ty, form_span(forms[fold.input as int]))->Ok_0;
        let accumulator = typed_expression(calls, source, forms, env, initial, goal)->Ok_0;
        assert(fold_positions(forms, request.at, fold));
        checked_answer_is_expected(calls, source, forms, env, initial, expected, accumulator);
        checked_answer_is_expected(calls, source, forms, fold_environment(source, forms, env, fold, item, accumulator),
            Request { at: fold.body, expected: accumulator, list: None }, accumulator, actual);
    }
    }
}

proof fn checked_type_result<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request,
)
    ensures typed_expression(calls, source, forms, env, request, Goal::Check(request.expected))
        == only_to_result(typed_expression(calls, source, forms, env, request, Goal::Check(request.expected)), request.expected),
{
    if let Ok(actual) = typed_expression(calls, source, forms, env, request, Goal::Check(request.expected)) {
        checked_answer_is_expected(calls, source, forms, env, request, request.expected, actual);
    }
}

spec fn ensure_two_checked<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>,
    yes: Request, no: Request, result_ty: TypeShape,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match typed_expression(calls, source, forms, env, yes, Goal::Check(yes.expected)) {
        Err(error) => Err(error),
        Ok(_) => only_to_result(typed_expression(calls, source, forms, env, no, Goal::Check(no.expected)), result_ty),
    }
}

spec fn checked_selections<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, step: CheckStep, ty: TypeShape,
) -> Result<TypeShape, ExpressionCheckFailure<'a>> {
    match step {
        CheckStep::Done => Ok(ty),
        CheckStep::One(child) => only_to_result(typed_expression(calls, source, forms, env, child, Goal::Check(child.expected)), ty),
        CheckStep::Three(condition, yes, no) =>
            match typed_expression(calls, source, forms, env, condition, Goal::Check(condition.expected)) {
                Err(error) => Err(error),
                Ok(_) => ensure_two_checked(calls, source, forms, env, yes, no, ty),
            },
    }
}

proof fn plan_check_is_checked<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, goal: Goal, step: CheckStep, ty: TypeShape,
)
    requires request.at < forms.len(), request.list.is_none(), step_children_fit(forms, request.at, step),
        form_plan(source, forms, env, request, goal) == Ok(PlanModel::Check(step, ty)),
    ensures typed_expression(calls, source, forms, env, request, goal) == checked_selections(calls, source, forms, env, step, ty),
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
            assert(typed_expression(calls, source, forms, env, contextual, Goal::Check(ty))
                == checked_selections(calls, source, forms, env, step, ty));
        }
    }
}

proof fn rejected_plan_has_no_type<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request, goal: Goal, error: ExpressionCheckFailure<'a>,
)
    requires applicable_call(calls, source, forms, request.at).is_none(), request.at < forms.len(), request.list.is_none(),
        form_plan(source, forms, env, request, goal) == Err(error),
    ensures typed_expression(calls, source, forms, env, request, goal) == Err(error),
{
    reveal_with_fuel(typed_expression, 3);
    reveal(typed_bindings);
    reveal(typed_elements);
}

proof fn inferred_condition_plan<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    job: Job, condition: usize, yes: usize, no: usize,
)
    requires
        job.request.at < condition < yes < no < forms.len(), job.request.list.is_none(),
        form_plan(source, forms, lexical_view(parameters, locals, job.scope), job.request, job.goal)
            == Ok(PlanModel::InferConditional { condition, yes, no }),
    ensures job_type(calls, source, forms, parameters, locals, job)
        == action_type(calls, source, forms, parameters, locals, Ok(Action::Visit(
            Job { request: Request { at: condition, expected: scalar_type(BuiltinDataType::Bool), list: None },
                goal: Goal::Check(scalar_type(BuiltinDataType::Bool)), scope: job.scope },
            Some(Await::InferredCondition { yes, no, scope: job.scope }),
        ))),
{
    reveal_with_fuel(typed_expression, 2);
}

proof fn inferred_list_plan<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    job: Job, first: usize,
)
    requires
        job.request.at < first < subtree_limit(forms, job.request.at) <= forms.len(), job.request.list.is_none(),
        form_plan(source, forms, lexical_view(parameters, locals, job.scope), job.request, job.goal)
            == Ok(PlanModel::InferList { first }),
    ensures job_type(calls, source, forms, parameters, locals, job)
        == action_type(calls, source, forms, parameters, locals, Ok(Action::Visit(
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
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    job: Job, header: LetHeader,
)
    requires job.request.at < header.body < forms.len(), job.request.list.is_none(),
        valid_bindings(forms, header.bindings@, job.request.at, header.body),
        form_plan(source, forms, lexical_view(parameters, locals, job.scope), job.request, job.goal)
            == Ok(PlanModel::Let { rows: header.bindings@, body: header.body }),
    ensures job_type(calls, source, forms, parameters, locals, job) ==
        action_type(calls, source, forms, parameters, locals, Ok(
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

fn start_fold_action<'a>(
    _calls: &[CallTypeEntry],
    _source: &'a str, _forms: &[Form], _parameters: &[SignatureParameter<'a>], _locals: &LocalScopes<'a>,
    job: Job, fold: FoldHeader,
) -> (result: Action)
    requires usable_forms(_source, _forms@), job.request.list.is_none(), _locals.contains(job.scope),
        fold_positions(_forms@, job.request.at, fold),
        form_plan(_source, _forms@, lexical_view(_parameters@, _locals, job.scope), job.request, job.goal)
            == Ok(PlanModel::Fold(fold)),
    ensures
        action_valid(_calls@, _forms@, _locals, result),
        action_advances(_calls@, _forms@, result, (job.request.at + 1) as usize),
        action_limit(_calls@, _forms@, result) <= subtree_limit(_forms@, job.request.at),
        action_type(_calls@, _source, _forms@, _parameters@, _locals, Ok(result)) == job_type(_calls@, _source, _forms@, _parameters@, _locals, job),
{
    let input = match fold.kind {
        FoldKind::Nat => {
            let nat_type = scalar(BuiltinDataType::Integer(IntegerType::Nat));
            check_job(Request { at: fold.input, expected: nat_type, list: None }, job.scope)
        }
        FoldKind::List => infer_job(fold.input, job.scope),
    };
    reveal_with_fuel(typed_expression, 2);
    reveal_with_fuel(typed_fold, 2);
    Action::Visit(input, Some(Await::FoldInput { fold, goal: job.goal, scope: job.scope }))
}

fn start_call_action<'a>(
    calls: &[CallTypeEntry], _source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>],
    _locals: &LocalScopes<'a>, job: Job, entry: usize,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires
        entry < calls@.len(), canonical_call(forms@, calls@[entry as int]),
        applicable_call(calls@, _source, forms@, job.request.at) == Some(entry),
        job_in_bounds(forms@, job), _locals.contains(job.scope), job.request.list.is_none(),
    ensures
        result matches Ok(action) ==> action_valid(calls@, forms@, _locals, action),
        result matches Ok(action) ==> job.request.at < usize::MAX
            && action_advances(calls@, forms@, action, (job.request.at + 1) as usize)
            && action_limit(calls@, forms@, action) <= subtree_limit(forms@, job.request.at),
        action_type(calls@, _source, forms@, _parameters@, _locals, result)
            == job_type(calls@, _source, forms@, _parameters@, _locals, job),
{
    let call = &calls[entry];
    let ghost env = lexical_view(_parameters@, _locals, job.scope);
    proof {
        assert(call.at == job.request.at);
        assert(job.request.at < argument_cursor(forms@, *call, 0) <= forms@.len());
        assert(remaining_elements(forms@, job.request).is_none());
        named_call_equation(calls@, _source, forms@, env, job.request, job.goal, entry);
        declared_call_equation(calls@, _source, forms@, env, job.request.at, job.goal, entry);
    }
    let ty = call_result_type(job.goal, call.result, span_of(&forms[job.request.at]))?;
    if call.arguments.len() == 0 {
        proof { call_argument_equation(calls@, _source, forms@, env, *call, 0); }
        return Ok(Action::Typed(ty));
    }
    let argument = &call.arguments[0];
    let request = Request { at: argument.at, expected: argument.expected, list: None };
    assert(argument.at < argument_cursor(forms@, *call, 1) <= forms@.len());
    proof { call_argument_equation(calls@, _source, forms@, env, *call, 0); }
    let waiting = Await::Call { entry, argument: 0, scope: job.scope, result: ty };
    Ok(Action::Visit(check_job(request, job.scope), Some(waiting)))
}

fn start_action<'a>(
    calls: &[CallTypeEntry],
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], locals: &LocalScopes<'a>, job: Job,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires call_entries_fit(forms@, calls@), usable_forms(source, forms@), job_in_bounds(forms@, job), locals.contains(job.scope), job.request.list.is_none(),
    ensures result matches Ok(action) ==> action_valid(calls@, forms@, locals, action),
        result matches Ok(action) ==> job.request.at < usize::MAX
            && action_advances(calls@, forms@, action, (job.request.at + 1) as usize)
            && action_limit(calls@, forms@, action) <= subtree_limit(forms@, job.request.at),
        action_type(calls@, source, forms@, parameters@, locals, result) == job_type(calls@, source, forms@, parameters@, locals, job),
{
    let req = job.request;
    let _size = forms.len();
    let ghost env = lexical_view(parameters@, locals, job.scope);
    let parsed = read_shape(source, forms, req.at);
    if matches!(parsed, Err(ExpressionCheckFailure::Deferred(DeferredExpression::Form(_)))) {
        if let Some(entry) = find_call_entry(calls, req.at) {
            assert(canonical_call(forms@, calls@[entry as int]));
            return start_call_action(calls, source, forms, parameters, locals, job, entry);
        }
    }
    assert(applicable_call(calls@, source, forms@, req.at).is_none());
    let plan = match read_form_plan(source, forms, parameters, locals, job.scope, req, job.goal, parsed) {
        Ok(plan) => plan,
        Err(error) => {
            proof { rejected_plan_has_no_type(calls@, source, forms@, env, req, job.goal, error); }
            return Err(error);
        }
    };
    match plan {
        FormPlan::Fold(fold) => Ok(start_fold_action(calls, source, forms, parameters, locals, job, fold)),
        FormPlan::Check(step, ty) => {
            proof { plan_check_is_checked(calls@, source, forms@, env, req, job.goal, step, ty); }
            match step {
                CheckStep::Done => Ok(Action::Typed(ty)),
                CheckStep::One(child) => Ok(Action::Visit(check_job(child, job.scope), Some(Await::Result(ty)))),
                CheckStep::Three(condition, yes, no) => {
                    proof { checked_type_result(calls@, source, forms@, env, no); }
                    Ok(Action::Visit(check_job(condition, job.scope), Some(Await::CheckedCondition { yes_request: yes, no_request: no, scope: job.scope })))
                }
            }
        }
        FormPlan::InferConditional { condition, yes, no } => {
            proof { inferred_condition_plan(calls@, source, forms@, parameters@, locals, job, condition, yes, no); }
            assert(condition < subtree_limit(forms@, condition) == yes);
            assert(yes < subtree_limit(forms@, yes) == no);
            let boolean = scalar(BuiltinDataType::Bool);
            let request = Request { at: condition, expected: boolean, list: None };
            Ok(Action::Visit(check_job(request, job.scope), Some(Await::InferredCondition { yes, no, scope: job.scope })))
        }
        FormPlan::InferList { first } => {
            proof {
                super::super::forms::child_stays_inside(forms@, req.at, first);
                inferred_list_plan(calls@, source, forms@, parameters@, locals, job, first);
            }
            Ok(Action::Visit(infer_job(first, job.scope), Some(Await::Element {
                at: first, owner: req.at, element: None, scope: job.scope,
            })))
        }
        FormPlan::Let(header) => {
            proof {
                super::super::forms::child_stays_inside(forms@, req.at, header.body);
                let_plan_type(calls@, source, forms@, parameters@, locals, job, header);
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

fn accept_fold_input<'a>(
    _calls: &[CallTypeEntry],
    _source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>], _locals: &LocalScopes<'a>,
    fold: FoldHeader, goal: Goal, scope: Scope, ty: TypeShape, Ghost(child): Ghost<Job>,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires usable_forms(_source, forms@), _locals.contains(scope), fold_positions(forms@, fold._at, fold),
        wait_follows(_calls@, forms@, Await::FoldInput { fold, goal, scope }, child),
    ensures result matches Ok(action) ==> action_valid(_calls@, forms@, _locals, action)
        && action_advances(_calls@, forms@, action, request_limit(forms@, child.request))
        && action_limit(_calls@, forms@, action) <= wait_limit(_calls@, forms@, Await::FoldInput { fold, goal, scope }, child),
    action_type(_calls@, _source, forms@, _parameters@, _locals, result)
        == resumed_type(_calls@, _source, forms@, _parameters@, _locals, Await::FoldInput { fold, goal, scope }, ty),
{
    let item_type = checked_fold_item(fold.kind, ty, span_of(&forms[fold.input]))?;
    let seed = match goal {
        Goal::Infer => infer_job(fold.initial, scope),
        Goal::Check(expected) => check_job(Request { at: fold.initial, expected, list: None }, scope),
    };
    Ok(Action::Visit(seed, Some(Await::FoldInitial { fold, item_type, scope })))
}

fn accept_fold_initial<'a>(
    _calls: &[CallTypeEntry],
    source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>], locals: &mut LocalScopes<'a>,
    fold: FoldHeader, item_type: TypeShape, scope: Scope, ty: TypeShape, Ghost(child): Ghost<Job>,
) -> (result: Action)
    requires usable_forms(source, forms@), old(locals).contains(scope), fold_positions(forms@, fold._at, fold),
        wait_follows(_calls@, forms@, Await::FoldInitial { fold, item_type, scope }, child),
    ensures action_valid(_calls@, forms@, final(locals), result)
        && action_advances(_calls@, forms@, result, request_limit(forms@, child.request))
        && action_limit(_calls@, forms@, result) <= wait_limit(_calls@, forms@, Await::FoldInitial { fold, item_type, scope }, child),
    action_type(_calls@, source, forms@, _parameters@, final(locals), Ok(result))
        == resumed_type(_calls@, source, forms@, _parameters@, old(locals), Await::FoldInitial { fold, item_type, scope }, ty),
    forall|older: Scope| #[trigger] old(locals).contains(older) ==> final(locals).contains(older)
        && final(locals).local_types(older) == old(locals).local_types(older),
{
    let item = LocalType { name: source_word(source, forms, fold.item), ty: item_type };
    let accumulator = LocalType { name: source_word(source, forms, fold.accumulator), ty };
    let ghost before = *locals;
    let item_scope = locals.extend(scope, item);
    let ghost intermediate = *locals;
    let body_scope = locals.extend(item_scope, accumulator);
    proof {
        assert forall|older: Scope| #[trigger] before.contains(older) implies
            locals.contains(older) && locals.local_types(older) == before.local_types(older) by {
            assert(intermediate.contains(older));
        };
        assert(lexical_view(_parameters@, locals, body_scope) =~= fold_environment(source, forms@,
            lexical_view(_parameters@, &before, scope), fold, item_type, ty));
    }
    Action::Visit(check_job(Request { at: fold.body, expected: ty, list: None }, body_scope), None)
}


fn accept_element<'a>(
    _calls: &[CallTypeEntry],
    _source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>], _locals: &LocalScopes<'a>,
    at: usize, owner: usize, element: Option<TypeShape>, scope: Scope, ty: TypeShape, Ghost(child): Ghost<Job>,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires usable_forms(_source, forms@),
        wait_in_bounds(_calls@, forms@, Await::Element { at, owner, element, scope }),
        wait_has_scopes(_locals, Await::Element { at, owner, element, scope }),
        wait_follows(_calls@, forms@, Await::Element { at, owner, element, scope }, child),
    ensures result matches Ok(action) ==> action_valid(_calls@, forms@, _locals, action),
        result matches Ok(action) ==> action_advances(_calls@, forms@, action, request_limit(forms@, child.request))
            && action_limit(_calls@, forms@, action) <= wait_limit(_calls@, forms@, Await::Element { at, owner, element, scope }, child),
        action_type(_calls@, _source, forms@, _parameters@, _locals, result)
            == resumed_type(_calls@, _source, forms@, _parameters@, _locals, Await::Element { at, owner, element, scope }, ty),
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
    calls: Seq<CallTypeEntry>,
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
        action_type(calls, source, forms, parameters, after, Ok(binding_action(header, owner, index, extended)))
            == resumed_type(calls, source, forms, parameters, before, Await::Binding { header, binding_owner: owner, index, body_scope }, ty),
{
    let outer = lexical_view(parameters, after, owner.scope);
    let extended_env = lexical_view(parameters, after, extended);
    let from = (index + 1) as nat;
    assert(resumed_type(calls, source, forms, parameters, before, Await::Binding { header, binding_owner: owner, index, body_scope }, ty)
        == continue_bindings(calls, source, forms, outer, owner, header, from, extended_env));
    continue_bindings_unfold(calls, source, forms, outer, owner, header, from, extended_env);
    if from < header.bindings@.len() {
        let next = from as usize;
        let row = header.bindings@[next as int];
        let request = Request { at: row.value, expected: scalar_type(BuiltinDataType::Bool), list: None };
        match typed_expression(calls, source, forms, outer, request, Goal::Infer) {
            Err(error) => {
                assert(action_type(calls, source, forms, parameters, after, Ok(binding_action(header, owner, index, extended)))
                    == Err(error));
            }
            Ok(actual) => {
                assert(action_type(calls, source, forms, parameters, after, Ok(binding_action(header, owner, index, extended)))
                    == resumed_type(calls, source, forms, parameters, after,
                        Await::Binding { header, binding_owner: owner, index: next, body_scope: extended }, actual));
            }
        }
    }
}

proof fn continue_bindings_unfold<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, outer: Seq<TypeBinding>, owner: Job, header: LetHeader,
    from: nat, extended_env: Seq<TypeBinding>,
)
    requires valid_bindings(forms, header.bindings@, owner.request.at, header.body),
    ensures continue_bindings(calls, source, forms, outer, owner, header, from, extended_env) ==
        if from < header.bindings@.len() {
            let row = header.bindings@[from as int];
            let request = Request { at: row.value, expected: scalar_type(BuiltinDataType::Bool), list: None };
            match typed_expression(calls, source, forms, outer, request, Goal::Infer) {
                Err(error) => Err(error),
                Ok(next_ty) => continue_bindings(calls, source, forms, outer, owner, header, from + 1,
                    seq![(spelling(source, forms[row.name as int]), next_ty)] + extended_env),
            }
        } else {
            typed_expression(calls, source, forms, extended_env,
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
        match typed_expression(calls, source, forms, outer, request, Goal::Infer) {
            Err(error) => {
                assert(typed_bindings(calls, source, forms, outer, owner.request.at, header.body, rows, from, extended_env) == Err(error));
            }
            Ok(next_ty) => {
                let next_env = seq![(spelling(source, forms[row.name as int]), next_ty)] + extended_env;
                assert(typed_bindings(calls, source, forms, outer, owner.request.at, header.body, rows, from, extended_env)
                    == typed_bindings(calls, source, forms, outer, owner.request.at, header.body, rows, from + 1, next_env));
            }
        }
    } else {
        assert(typed_bindings(calls, source, forms, outer, owner.request.at, header.body, rows, from, extended_env) == Ok(extended_env));
    }
}

fn accept_binding<'a>(
    _calls: &[CallTypeEntry],
    source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>], locals: &mut LocalScopes<'a>,
    header: LetHeader, owner: Job, index: usize, body_scope: Scope, ty: TypeShape, Ghost(child): Ghost<Job>,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@),
        wait_in_bounds(_calls@, forms@, Await::Binding { header, binding_owner: owner, index, body_scope }),
        wait_has_scopes(old(locals), Await::Binding { header, binding_owner: owner, index, body_scope }),
        wait_follows(_calls@, forms@, Await::Binding { header, binding_owner: owner, index, body_scope }, child),
    ensures result matches Ok(action) ==> action_valid(_calls@, forms@, final(locals), action),
        result matches Ok(action) ==> action_advances(_calls@, forms@, action, request_limit(forms@, child.request))
            && action_limit(_calls@, forms@, action) <= wait_limit(_calls@, forms@, Await::Binding { header, binding_owner: owner, index, body_scope }, child),
        action_type(_calls@, source, forms@, _parameters@, final(locals), result)
            == resumed_type(_calls@, source, forms@, _parameters@, old(locals), Await::Binding { header, binding_owner: owner, index, body_scope }, ty),
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
    proof { binding_action_agrees(_calls@, source, forms@, _parameters@, &before, locals, header, owner, index, body_scope, new_scope, ty); }
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

proof fn continuing_call_type<'a>(
    calls: Seq<CallTypeEntry>, source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>,
    locals: &LocalScopes<'a>, entry: usize, argument: usize, scope: Scope, ty: TypeShape, job: Job,
)
    requires
        entry < calls.len(),
        argument + 1 < calls[entry as int].arguments@.len() <= usize::MAX,
        argument_cursor(forms, calls[entry as int], (argument + 1) as nat)
            < argument_cursor(forms, calls[entry as int], (argument + 2) as nat) <= forms.len(),
        ({
            let arg = calls[entry as int].arguments@[argument + 1];
            job == (Job { request: Request { at: arg.at, expected: arg.expected, list: None },
                goal: Goal::Check(arg.expected), scope })
        }),
    ensures
        action_type(calls, source, forms, parameters, locals, Ok(Action::Visit(job, Some(Await::Call {
            entry, argument: (argument + 1) as usize, scope, result: ty,
        })))) == resumed_type(calls, source, forms, parameters, locals,
            Await::Call { entry, argument, scope, result: ty }, ty),
{
    let call = calls[entry as int];
    let next = (argument + 1) as nat;
    let env = lexical_view(parameters, locals, scope);
    call_argument_equation(calls, source, forms, env, call, next);
    let checked = job_type(calls, source, forms, parameters, locals, job);
    let current = Await::Call { entry, argument, scope, result: ty };
    let waiting = Await::Call { entry, argument: next as usize, scope, result: ty };
    let action = Ok(Action::Visit(job, Some(waiting)));
    match checked {
        Err(error) => {
            assert(typed_call_arguments(calls, source, forms, env, call, next) == Err(error));
            assert(action_type(calls, source, forms, parameters, locals, action) == Err(error));
        }
        Ok(arg_type) => {
            let tail = typed_call_arguments(calls, source, forms, env, call, next + 1);
            let output = attach_call_type(tail, ty);
            assert(typed_call_arguments(calls, source, forms, env, call, next) == tail);
            assert(resumed_type(calls, source, forms, parameters, locals, waiting, arg_type) == output);
            assert(action_type(calls, source, forms, parameters, locals, action) == output);
        }
    }
}

proof fn finished_call_type<'a>(
    calls: Seq<CallTypeEntry>, source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>,
    locals: &LocalScopes<'a>, entry: usize, argument: usize, scope: Scope, ty: TypeShape,
)
    requires entry < calls.len(), argument + 1 == calls[entry as int].arguments@.len(),
    ensures action_type(calls, source, forms, parameters, locals, Ok(Action::Typed(ty)))
        == resumed_type(calls, source, forms, parameters, locals,
            Await::Call { entry, argument, scope, result: ty }, ty),
{
    let env = lexical_view(parameters, locals, scope);
    call_argument_equation(calls, source, forms, env, calls[entry as int], (argument + 1) as nat);
}

proof fn continuing_call_bounds(
    calls: Seq<CallTypeEntry>, forms: Seq<Form>, locals: &LocalScopes, entry: usize, argument: usize,
    scope: Scope, ty: TypeShape, child: Job, job: Job,
)
    requires
        locals.contains(scope),
        wait_in_bounds(calls, forms, Await::Call { entry, argument, scope, result: ty }),
        wait_follows(calls, forms, Await::Call { entry, argument, scope, result: ty }, child),
        argument + 1 < calls[entry as int].arguments@.len() <= usize::MAX,
        ({
            let arg = calls[entry as int].arguments@[argument + 1];
            job == (Job { request: Request { at: arg.at, expected: arg.expected, list: None },
                goal: Goal::Check(arg.expected), scope })
        }),
    ensures ({
        let current = Await::Call { entry, argument, scope, result: ty };
        let waiting = Await::Call { entry, argument: (argument + 1) as usize, scope, result: ty };
        let action = Action::Visit(job, Some(waiting));
        &&& action_valid(calls, forms, locals, action)
        &&& action_advances(calls, forms, action, request_limit(forms, child.request))
        &&& action_limit(calls, forms, action) <= wait_limit(calls, forms, current, child)
        &&& argument_cursor(forms, calls[entry as int], (argument + 1) as nat)
            < argument_cursor(forms, calls[entry as int], (argument + 2) as nat) <= forms.len()
    }),
{
    let call = calls[entry as int];
    let previous = call.arguments@[argument as int];
    let next = (argument + 1) as usize;
    let arg = call.arguments@[next as int];
    let waiting = Await::Call { entry, argument: next, scope, result: ty };
    assert(child.request.at == previous.at && child.request.list.is_none());
    assert(request_limit(forms, child.request) == subtree_limit(forms, previous.at) == arg.at);
    assert(arg.at < argument_cursor(forms, call, (next + 1) as nat) <= forms.len());
    assert(wait_follows(calls, forms, waiting, job));
}

#[verifier::opaque]
spec fn next_call_action_model(calls: Seq<CallTypeEntry>, entry: usize, argument: usize, scope: Scope, ty: TypeShape) -> Action {
    let arguments = calls[entry as int].arguments@;
    let next = argument + 1;
    if next == arguments.len() {
        Action::Typed(ty)
    } else {
        let arg = arguments[next];
        let request = Request { at: arg.at, expected: arg.expected, list: None };
        let job = Job { request, goal: Goal::Check(arg.expected), scope };
        Action::Visit(job, Some(Await::Call { entry, argument: next as usize, scope, result: ty }))
    }
}

proof fn next_call_action_contract<'a>(
    calls: Seq<CallTypeEntry>, source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>,
    locals: &LocalScopes<'a>, entry: usize, argument: usize, scope: Scope, ty: TypeShape, child: Job,
)
    requires
        locals.contains(scope),
        wait_in_bounds(calls, forms, Await::Call { entry, argument, scope, result: ty }),
        wait_follows(calls, forms, Await::Call { entry, argument, scope, result: ty }, child),
        calls[entry as int].arguments@.len() <= usize::MAX,
    ensures ({
        let action = next_call_action_model(calls, entry, argument, scope, ty);
        let current = Await::Call { entry, argument, scope, result: ty };
        &&& action_valid(calls, forms, locals, action)
        &&& action_advances(calls, forms, action, request_limit(forms, child.request))
        &&& action_limit(calls, forms, action) <= wait_limit(calls, forms, current, child)
        &&& action_type(calls, source, forms, parameters, locals, Ok(action))
            == resumed_type(calls, source, forms, parameters, locals, current, ty)
    }),
{
    reveal(next_call_action_model);
    let arguments = calls[entry as int].arguments@;
    let next = argument + 1;
    if next == arguments.len() {
        finished_call_type(calls, source, forms, parameters, locals, entry, argument, scope, ty);
    } else {
        let arg = arguments[next];
        let request = Request { at: arg.at, expected: arg.expected, list: None };
        let job = Job { request, goal: Goal::Check(arg.expected), scope };
        continuing_call_bounds(calls, forms, locals, entry, argument, scope, ty, child, job);
        continuing_call_type(calls, source, forms, parameters, locals, entry, argument, scope, ty, job);
    }
}

fn next_call_argument(calls: &[CallTypeEntry], entry: usize, argument: usize, scope: Scope, ty: TypeShape)
    -> (result: Action)
    requires entry < calls@.len(), argument < calls@[entry as int].arguments@.len(),
    ensures calls@[entry as int].arguments@.len() <= usize::MAX,
        result == next_call_action_model(calls@, entry, argument, scope, ty),
{
    proof { reveal(next_call_action_model); }
    let call = &calls[entry];
    let _length = call.arguments.len();
    let next = argument + 1;
    if next == _length {
        Action::Typed(ty)
    } else {
        let arg = &call.arguments[next];
        let request = Request { at: arg.at, expected: arg.expected, list: None };
        let job = check_job(request, scope);
        let waiting = Await::Call { entry, argument: next, scope, result: ty };
        Action::Visit(job, Some(waiting))
    }
}

fn accept_result<'a>(
    calls: &[CallTypeEntry],
    source: &'a str, forms: &[Form], _parameters: &[SignatureParameter<'a>], locals: &mut LocalScopes<'a>, awaiting: Await, ty: TypeShape,
    Ghost(child): Ghost<Job>,
) -> (result: Result<Action, ExpressionCheckFailure<'a>>)
    requires usable_forms(source, forms@), wait_in_bounds(calls@, forms@, awaiting), wait_has_scopes(old(locals), awaiting),
        wait_follows(calls@, forms@, awaiting, child),
    ensures result matches Ok(action) ==> action_valid(calls@, forms@, final(locals), action),
        result matches Ok(action) ==> action_advances(calls@, forms@, action, request_limit(forms@, child.request))
            && action_limit(calls@, forms@, action) <= wait_limit(calls@, forms@, awaiting, child),
        action_type(calls@, source, forms@, _parameters@, final(locals), result)
            == resumed_type(calls@, source, forms@, _parameters@, old(locals), awaiting, ty),
        forall|scope: Scope| #[trigger] old(locals).contains(scope) ==> final(locals).contains(scope)
            && final(locals).local_types(scope) == old(locals).local_types(scope),
{
    let _size = forms.len();
    assert(complete_list_indices(forms@) && _size == forms@.len());
    match awaiting {
        Await::Result(expected) => Ok(Action::Typed(expected)),
        Await::Call { entry, argument, scope, result } => {
            let action = next_call_argument(calls, entry, argument, scope, result);
            proof {
                next_call_action_contract(calls@, source, forms@, _parameters@, locals, entry, argument, scope, result, child);
            }
            Ok(action)
        }
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
            accept_element(calls, source, forms, _parameters, locals, at, owner, element, scope, ty, Ghost(child)),
        Await::Binding { header, binding_owner: owner, index, body_scope } =>
            accept_binding(calls, source, forms, _parameters, locals, header, owner, index, body_scope, ty, Ghost(child)),
        Await::FoldInput { fold, goal, scope } =>
            accept_fold_input(calls, source, forms, _parameters, locals, fold, goal, scope, ty, Ghost(child)),
        Await::FoldInitial { fold, item_type, scope } =>
            Ok(accept_fold_initial(calls, source, forms, _parameters, locals, fold, item_type, scope, ty, Ghost(child))),

    }
}

struct Pending {
    child: Ghost<Job>,
    awaiting: Await,
}

spec fn pending_ranges(calls: Seq<CallTypeEntry>, forms: Seq<Form>, pending: Seq<Pending>, job: Job) -> bool {
    &&& forall|i: int| 0 <= i < pending.len() ==> {
        let work = #[trigger] pending[i];
        &&& wait_in_bounds(calls, forms, work.awaiting)
        &&& wait_follows(calls, forms, work.awaiting, work.child@)
        &&& work.child@.request.at <= job.request.at
        &&& request_limit(forms, job.request) <= request_limit(forms, work.child@.request)
    }
    &&& forall|i: int, j: int| 0 <= i < j < pending.len() ==> {
        let outer = #[trigger] pending[i];
        let inner = #[trigger] pending[j];
        wait_limit(calls, forms, inner.awaiting, inner.child@) <= request_limit(forms, outer.child@.request)
    }
}

spec fn pending_scopes(locals: &LocalScopes, pending: Seq<Pending>) -> bool {
    forall|i: int| 0 <= i < pending.len() ==> wait_has_scopes(locals, (#[trigger] pending[i]).awaiting)
}

#[verifier::opaque]
spec fn completed_typing<'a>(
    calls: Seq<CallTypeEntry>,
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
                completed_typing(calls, source, forms, parameters, locals, pending.drop_last(),
                    resumed_type(calls, source, forms, parameters, locals, work.awaiting, ty))
            }
        }
    }
}

proof fn pushed_pending_agrees<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes,
    pending: Seq<Pending>, work: Pending, result: Result<TypeShape, ExpressionCheckFailure<'a>>,
)
    ensures completed_typing(calls, source, forms, parameters, locals, pending.push(work), result)
        == completed_typing(calls, source, forms, parameters, locals, pending, match result {
            Err(error) => Err(error),
            Ok(ty) => resumed_type(calls, source, forms, parameters, locals, work.awaiting, ty),
        }),
{
    reveal(completed_typing);
    assert(pending.push(work).drop_last() =~= pending);
}

proof fn resume_keeps_earlier_scopes<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, previous: &LocalScopes, locals: &LocalScopes,
    waiting: Await, ty: TypeShape,
)
    requires wait_has_scopes(previous, waiting),
        forall|scope: Scope| #[trigger] previous.contains(scope) ==>
            locals.contains(scope) && locals.local_types(scope) == previous.local_types(scope),
    ensures wait_has_scopes(locals, waiting),
        resumed_type(calls, source, forms, parameters, locals, waiting, ty)
            == resumed_type(calls, source, forms, parameters, previous, waiting, ty),
{
}

proof fn pending_keeps_earlier_scopes<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, previous: &LocalScopes, locals: &LocalScopes,
    pending: Seq<Pending>, result: Result<TypeShape, ExpressionCheckFailure<'a>>,
)
    requires pending_scopes(previous, pending),
        forall|scope: Scope| #[trigger] previous.contains(scope) ==>
            locals.contains(scope) && locals.local_types(scope) == previous.local_types(scope),
    ensures pending_scopes(locals, pending),
        completed_typing(calls, source, forms, parameters, previous, pending, result)
            == completed_typing(calls, source, forms, parameters, locals, pending, result),
    decreases pending.len(),
{
    assert forall|i: int| 0 <= i < pending.len() implies wait_has_scopes(locals, (#[trigger] pending[i]).awaiting) by {
        resume_keeps_earlier_scopes(calls, source, forms, parameters, previous, locals, pending[i].awaiting,
            scalar_type(BuiltinDataType::Bool));
    };
    reveal(completed_typing);
    if pending.len() != 0 {
        if let Ok(ty) = result {
            let last = pending.last();
            resume_keeps_earlier_scopes(calls, source, forms, parameters, previous, locals, last.awaiting, ty);
            let earlier = pending.drop_last();
            assert forall|i:int| 0 <= i < earlier.len() implies wait_has_scopes(previous, (#[trigger] earlier[i]).awaiting) by {
                assert(earlier[i] == pending[i]);
            };
            pending_keeps_earlier_scopes(calls, source, forms, parameters, previous, locals, earlier,
                resumed_type(calls, source, forms, parameters, locals, last.awaiting, ty));
        }
    }
}

proof fn pushed_pending_fits(
    calls: Seq<CallTypeEntry>,
    forms: Seq<Form>, locals: &LocalScopes, pending: Seq<Pending>, current: Job, child: Job, frame: Await,
)
    requires pending_ranges(calls, forms, pending, current), pending_scopes(locals, pending),
        current.request.at <= child.request.at,
        wait_in_bounds(calls, forms, frame), wait_follows(calls, forms, frame, child), wait_has_scopes(locals, frame),
        forall|i:int| 0 <= i < pending.len() ==>
            wait_limit(calls, forms, frame, child) <= request_limit(forms, (#[trigger] pending[i]).child@.request),
    ensures pending_ranges(calls, forms, pending.push(Pending { child: Ghost(child), awaiting: frame }), child),
        pending_scopes(locals, pending.push(Pending { child: Ghost(child), awaiting: frame })),
{
    let next = pending.push(Pending { child: Ghost(child), awaiting: frame });
    assert forall|i:int| 0 <= i < next.len() implies {
        let work = #[trigger] next[i];
        &&& wait_in_bounds(calls, forms, work.awaiting)
        &&& wait_follows(calls, forms, work.awaiting, work.child@)
        &&& work.child@.request.at <= child.request.at
        &&& request_limit(forms, child.request) <= request_limit(forms, work.child@.request)
        &&& wait_has_scopes(locals, work.awaiting)
    } by {
        if i < pending.len() { assert(next[i] == pending[i]); }
    };
    assert forall|i:int, j:int| 0 <= i < j < next.len() implies {
        let outer = #[trigger] next[i];
        let inner = #[trigger] next[j];
        wait_limit(calls, forms, inner.awaiting, inner.child@) <= request_limit(forms, outer.child@.request)
    } by {
        assert(next[i] == pending[i]);
        if j < pending.len() { assert(next[j] == pending[j]); }
    };
}

proof fn shrunk_pending_fits(
    calls: Seq<CallTypeEntry>,
    forms: Seq<Form>, locals: &LocalScopes, pending: Seq<Pending>, cursor: Job, last: Pending,
)
    requires pending_ranges(calls, forms, pending.push(last), cursor), pending_scopes(locals, pending.push(last)),
    ensures pending_ranges(calls, forms, pending, cursor), pending_scopes(locals, pending),
{
    let old = pending.push(last);
    assert forall|i: int| 0 <= i < pending.len() implies {
        let work = #[trigger] pending[i];
        &&& wait_in_bounds(calls, forms, work.awaiting)
        &&& wait_follows(calls, forms, work.awaiting, work.child@)
        &&& work.child@.request.at <= cursor.request.at
        &&& request_limit(forms, cursor.request) <= request_limit(forms, work.child@.request)
        &&& wait_has_scopes(locals, work.awaiting)
    } by {
        assert(pending[i] == old[i]);
    };
    assert forall|i:int, j:int| 0 <= i < j < pending.len() implies {
        let outer = #[trigger] pending[i];
        let inner = #[trigger] pending[j];
        wait_limit(calls, forms, inner.awaiting, inner.child@) <= request_limit(forms, outer.child@.request)
    } by {
        assert(pending[i] == old[i] && pending[j] == old[j]);
    };
}

proof fn closer_cursor_fits(calls: Seq<CallTypeEntry>, forms: Seq<Form>, pending: Seq<Pending>, before: Job, after: Job)
    requires pending_ranges(calls, forms, pending, before), before.request.at <= after.request.at,
        forall|i:int| 0 <= i < pending.len() ==>
            request_limit(forms, after.request) <= request_limit(forms, (#[trigger] pending[i]).child@.request),
    ensures pending_ranges(calls, forms, pending, after),
{
}

proof fn advance_after_pop(
    calls: Seq<CallTypeEntry>,
    forms: Seq<Form>, pending: Seq<Pending>, current: Job, last: Pending, action: Action,
)
    requires pending_ranges(calls, forms, pending.push(last), current), request_ready(forms, current.request),
        action_advances(calls, forms, action, request_limit(forms, last.child@.request)),
        action_limit(calls, forms, action) <= wait_limit(calls, forms, last.awaiting, last.child@),
    ensures action matches Action::Visit(child, _) ==> {
        &&& current.request.at < child.request.at
        &&& forall|i:int| 0 <= i < pending.len() ==>
            action_limit(calls, forms, action) <= request_limit(forms, (#[trigger] pending[i]).child@.request)
    },
{
    let stack = pending.push(last);
    assert(stack[pending.len() as int] == last);
    if let Action::Visit(child, _) = action {
        assert forall|i:int| 0 <= i < pending.len() implies
            action_limit(calls, forms, action) <= request_limit(forms, (#[trigger] pending[i]).child@.request) by {
            assert(pending[i] == stack[i]);
            assert(wait_limit(calls, forms, last.awaiting, last.child@) <= request_limit(forms, stack[i].child@.request));
        };
    }
}

fn attach_action<'a>(
    _calls: &[CallTypeEntry],
    _source: &'a str, _forms: &[Form], _parameters: &[SignatureParameter<'a>], _locals: &LocalScopes<'a>,
    pending: &mut Vec<Pending>, _current: Job, child: Job, continuation: Option<Await>,
) -> (result: Job)
    requires
        pending_ranges(_calls@, _forms@, old(pending)@, _current), pending_scopes(_locals, old(pending)@),
        _current.request.at <= child.request.at,
        action_valid(_calls@, _forms@, _locals, Action::Visit(child, continuation)),
        action_advances(_calls@, _forms@, Action::Visit(child, continuation), child.request.at),
        forall|i:int| 0 <= i < old(pending)@.len() ==>
            action_limit(_calls@, _forms@, Action::Visit(child, continuation)) <= request_limit(_forms@, (#[trigger] old(pending)@[i]).child@.request),
    ensures
        result == child, pending_ranges(_calls@, _forms@, final(pending)@, result), pending_scopes(_locals, final(pending)@),
        completed_typing(_calls@, _source, _forms@, _parameters@, _locals, final(pending)@,
            job_type(_calls@, _source, _forms@, _parameters@, _locals, result))
            == completed_typing(_calls@, _source, _forms@, _parameters@, _locals, old(pending)@,
                action_type(_calls@, _source, _forms@, _parameters@, _locals, Ok(Action::Visit(child, continuation)))),
{
    let ghost before = pending@;
    if let Some(awaiting) = continuation {
        proof {
            pushed_pending_fits(_calls@, _forms@, _locals, pending@, _current, child, awaiting);
            pushed_pending_agrees(_calls@, _source, _forms@, _parameters@, _locals, pending@,
                Pending { child: Ghost(child), awaiting }, job_type(_calls@, _source, _forms@, _parameters@, _locals, child));
        }
        pending.push(Pending { child: Ghost(child), awaiting });
    } else {
        proof { closer_cursor_fits(_calls@, _forms@, pending@, _current, child); }
    }
    child
}

proof fn peer_preserves_typing<'a>(
    calls: Seq<CallTypeEntry>,
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, locals: &LocalScopes, work: Job,
)
    requires
        job_in_bounds(forms, work), request_ready(forms, work.request),
    ensures job_type(calls, source, forms, parameters, locals, work) ==
        action_type(calls, source, forms, parameters, locals, Ok(Action::Visit(
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
        checked_type_result(calls, source, forms, env, primary);
        checked_type_result(calls, source, forms, env, next);
    }
}

fn type_with_scopes<'a>(
    calls: &[CallTypeEntry],
    source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], at: usize, expected: TypeShape,
) -> (result: Result<TypeShape, ExpressionCheckFailure<'a>>)
    requires call_entries_fit(forms@, calls@), usable_forms(source, forms@), at < forms@.len(),
    ensures result == typed_expression(calls@, source, forms@, environment_view(parameters@),
        Request { at, expected, list: None }, Goal::Check(expected)),
{
    let mut locals = LocalScopes::new();
    let mut job = check_job(Request { at, expected, list: None }, None);
    let mut pending = Vec::<Pending>::new();
    let _size = forms.len();
    let _end = subtree_end(forms, at);
    let ghost root = typed_expression(calls@, source, forms@, environment_view(parameters@),
        Request { at, expected, list: None }, Goal::Check(expected));
    proof {
        assert(complete_list_indices(forms@));
        assert(at < _end <= _size);
        assert(lexical_view(parameters@, &locals, None) =~= environment_view(parameters@));
        reveal(completed_typing);
    }
    loop
        invariant
            call_entries_fit(forms@, calls@), usable_forms(source, forms@), request_ready(forms@, job.request), job_in_bounds(forms@, job),
            locals.contains(job.scope), pending_ranges(calls@, forms@, pending@, job), pending_scopes(&locals, pending@),
            root == typed_expression(calls@, source, forms@, environment_view(parameters@),
                Request { at, expected, list: None }, Goal::Check(expected)),
            completed_typing(calls@, source, forms@, parameters@, &locals, pending@, job_type(calls@, source, forms@, parameters@, &locals, job))
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
        proof { peer_preserves_typing(calls@, source, forms@, parameters@, &locals, job); }
        job = attach_action(calls, source, forms, parameters, &locals, &mut pending, job, single, after);
        let mut ty = match start_action(calls, source, forms, parameters, &locals, job) {
            Err(error) => {
                proof { reveal(completed_typing); }
                return Err(error);
            }
            Ok(Action::Visit(child, waiting)) => {
                job = attach_action(calls, source, forms, parameters, &locals, &mut pending, job, child, waiting);
                continue;
            }
            Ok(Action::Typed(ty)) => ty,
        };
        let ghost before = job.request.at;
        loop
            invariant_except_break
                before == job.request.at,
                completed_typing(calls@, source, forms@, parameters@, &locals, pending@, Ok(ty)) == root,
            invariant
                call_entries_fit(forms@, calls@), usable_forms(source, forms@), request_ready(forms@, job.request), job_in_bounds(forms@, job),
                locals.contains(job.scope), pending_ranges(calls@, forms@, pending@, job), pending_scopes(&locals, pending@),
                root == typed_expression(calls@, source, forms@, environment_view(parameters@),
                    Request { at, expected, list: None }, Goal::Check(expected)),
            ensures
                before < job.request.at,
                completed_typing(calls@, source, forms@, parameters@, &locals, pending@,
                    job_type(calls@, source, forms@, parameters@, &locals, job)) == root,
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
                pushed_pending_agrees(calls@, source, forms@, parameters@, &locals, pending@, work, Ok(ty));
                shrunk_pending_fits(calls@, forms@, &locals, pending@, job, work);
            }
            let result = accept_result(calls, source, forms, parameters, &mut locals, work.awaiting, ty, work.child);
            let ghost operation = result;
            proof {
                pending_keeps_earlier_scopes(calls@, source, forms@, parameters@, &previous, &locals, pending@,
                    action_type(calls@, source, forms@, parameters@, &locals, result));
            }
            match result {
                Err(error) => {
                    proof { reveal(completed_typing); }
                    return Err(error);
                }
                Ok(Action::Visit(child, waiting)) => {
                    proof { advance_after_pop(calls@, forms@, pending@, job, last, operation->Ok_0); }
                    job = attach_action(calls, source, forms, parameters, &locals, &mut pending, job, child, waiting);
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
    match typed_expression(Seq::empty(), source, forms, env, Request { at, expected, list: None }, Goal::Check(expected)) {
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
    let calls: &[CallTypeEntry] = &[];
    assert(calls@ =~= Seq::<CallTypeEntry>::empty());
    match type_with_scopes(calls, source, forms, parameters, at, expected) {
        Ok(_) => BodyVerdict::Accepted,
        Err(error) => BodyVerdict::Rejected(error),
    }
}

/// 解決済みの呼び出し署名を使う本体の型付け。
pub(super) closed spec fn typed_body_with_calls<'a>(
    calls: Seq<CallTypeEntry>, source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, expected: TypeShape,
) -> BodyVerdict<'a> {
    match typed_expression(calls, source, forms, env, Request { at, expected, list: None }, Goal::Check(expected)) {
        Ok(_) => BodyVerdict::Accepted,
        Err(error) => BodyVerdict::Rejected(error),
    }
}

/// 本体を検査し、各呼び出しの引数を署名の期待型で左から調べる。
pub(super) fn check_typed_body_with_calls<'a>(
    calls: &[CallTypeEntry], source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>],
    at: usize, expected: TypeShape,
) -> (verdict: BodyVerdict<'a>)
    requires call_entries_fit(forms@, calls@), usable_forms(source, forms@), at < forms@.len(),
    ensures verdict == typed_body_with_calls(calls@, source, forms@, environment_view(parameters@), at, expected),
{
    match type_with_scopes(calls, source, forms, parameters, at, expected) {
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
    typed_expression(Seq::empty(), source, forms, env, inferred_request(at), Goal::Infer) == Ok(ty)
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
    ensures typed_expression(Seq::empty(), source, forms, env, Request { at, expected: ty, list: None }, Goal::Check(ty)) == Ok(ty),
    decreases forms.len() - at, 0nat,
{
    match shape(source, forms, at) {
        Ok(Expression::Let) => {
            let (extended, body) = inferred_let_body(source, forms, env, at, ty);
            verify_inferred_context(source, forms, extended, body, ty);
        }
        Ok(Expression::Fold(fold)) => {
            inferred_fold_initial(source, forms, env, at, fold, ty);
            verify_inferred_context(source, forms, env, fold.initial, ty);
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

proof fn inferred_fold_initial<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, fold: FoldHeader, ty: TypeShape,
)
    requires at < forms.len(), inferred_as(source, forms, env, at, ty),
        shape(source, forms, at) == Ok(Expression::Fold(fold)),
    ensures at < fold.initial < forms.len(), inferred_as(source, forms, env, fold.initial, ty),
        typed_expression(Seq::empty(), source, forms, env, Request { at: fold.initial, expected: ty, list: None }, Goal::Check(ty)) == Ok(ty)
            ==> typed_expression(Seq::empty(), source, forms, env, Request { at, expected: ty, list: None }, Goal::Check(ty)) == Ok(ty),
{
    reveal_with_fuel(typed_expression, 2);
    reveal_with_fuel(typed_fold, 2);
    let (input, input_goal) = fold_input_request(fold);
    let input_ty = typed_expression(Seq::empty(), source, forms, env, input, input_goal)->Ok_0;
    let item = fold_item_type(fold.kind, input_ty, form_span(forms[fold.input as int]))->Ok_0;
    let accumulator = typed_expression(Seq::empty(), source, forms, env, fold_initial_request(fold, Goal::Infer), Goal::Infer)->Ok_0;
    let body = Request { at: fold.body, expected: accumulator, list: None };
    checked_answer_is_expected(Seq::empty(), source, forms, fold_environment(source, forms, env, fold, item, accumulator), body, accumulator, ty);
}

proof fn inferred_let_body<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
) -> (body: (Seq<TypeBinding>, usize))
    requires at < forms.len(), inferred_as(source, forms, env, at, ty),
        shape(source, forms, at) == Ok(Expression::Let),
    ensures at < body.1 < forms.len(), inferred_as(source, forms, body.0, body.1, ty),
        typed_body(source, forms, env, at, ty) == typed_body(source, forms, body.0, body.1, ty),
        typed_expression(Seq::empty(), source, forms, env, Request { at, expected: ty, list: None }, Goal::Check(ty))
            == typed_expression(Seq::empty(), source, forms, body.0, Request { at: body.1, expected: ty, list: None }, Goal::Check(ty)),
{
    reveal_with_fuel(typed_expression, 2);
    reveal(typed_bindings);
    let (rows, body) = let_structure(source, forms, at)->Ok_0;
    let extended = typed_bindings(Seq::empty(), source, forms, env, at, body, rows, 0, env)->Ok_0;
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
        typed_expression(Seq::empty(), source, forms, env, Request { at, expected: ty, list: None }, Goal::Check(ty))
            == ensure_two_checked(Seq::empty(), source, forms, env,
                Request { at: yes, expected: ty, list: None }, Request { at: no, expected: ty, list: None }, ty),
{
    reveal_with_fuel(typed_expression, 2);
    let actual = typed_expression(Seq::empty(), source, forms, env, inferred_request(no), Goal::Infer)->Ok_0;
    assert(types_agree(ty, actual, form_span(forms[no as int])) == Ok(()) && ty == actual);
    assert(children3(forms, at) == Some((condition, yes, no)));
}

proof fn inferred_list_elements<'a>(
    source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, at: usize, ty: TypeShape,
)
    requires at < forms.len(), inferred_as(source, forms, env, at, ty),
        shape(source, forms, at) == Ok(Expression::List),
        at + 2 < subtree_limit(forms, at) <= forms.len(),
    ensures typed_elements(Seq::empty(), source, forms, env, at, (at + 2) as usize, None) == Ok(ty),
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
        typed_expression(Seq::empty(), source, forms, env,
            Request { at: (at + 2) as usize, expected: element, list: Some(at) }, Goal::Check(element)) == Ok(element),
    ensures typed_expression(Seq::empty(), source, forms, env, Request { at, expected: ty, list: None }, Goal::Check(ty)) == Ok(ty),
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
        typed_elements(Seq::empty(), source, forms, env, owner, at, earlier) == Ok(list),
    ensures inferred_as(source, forms, env, at, element),
        earlier matches Some(first) ==> first == element,
        element_forms_list(element, list),
    decreases forms.len() - at,
{
    reveal_with_fuel(typed_expression, 2);
    reveal_with_fuel(typed_elements, 2);
    reveal_with_fuel(finish_element_model, 2);
    let element = typed_expression(Seq::empty(), source, forms, env, inferred_request(at), Goal::Infer)->Ok_0;
    if let Some(first) = earlier {
        assert(types_agree(first, element, form_span(forms[at as int])) == Ok(()));
        assert(first == element);
    }
    let next = subtree_limit(forms, at);
    if next != subtree_limit(forms, owner) {
        assert(at < next < subtree_limit(forms, owner));
        assert(typed_elements(Seq::empty(), source, forms, env, owner, next, Some(element)) == Ok(list));
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
        typed_elements(Seq::empty(), source, forms, env, owner, at, earlier) == Ok(list),
        element_forms_list(element, list),
    ensures typed_expression(Seq::empty(), source, forms, env, Request { at, expected: element, list: Some(owner) }, Goal::Check(element))
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
        typed_elements(Seq::empty(), source, forms, env, owner, at, earlier) == Ok(list),
        inferred_as(source, forms, env, at, element), earlier matches Some(first) ==> first == element,
    ensures typed_elements(Seq::empty(), source, forms, env, owner, subtree_limit(forms, at), Some(element)) == Ok(list),
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
        typed_expression(Seq::empty(), source, forms, env, Request { at, expected: element, list: None }, Goal::Check(element)) == Ok(element),
        remaining_elements(forms, Request { at, expected: element, list: Some(owner) }) matches Some(next) ==>
            typed_expression(Seq::empty(), source, forms, env, next, Goal::Check(element)) == Ok(element),
    ensures typed_expression(Seq::empty(), source, forms, env, Request { at, expected: element, list: Some(owner) }, Goal::Check(element))
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
    assert(typed_bindings(Seq::empty(), source, forms, outer, 0, 9, rows, 0, outer) == Ok(extended));
    checked_leaf_example(source, forms, extended, body);
    reveal_with_fuel(typed_expression, 2);
    reveal(typed_bindings);
    assert(typed_body(source, forms, outer, 0, boolean) == typed_body(source, forms, extended, 9, boolean));
}

proof fn checked_leaf_example<'a>(source: &'a str, forms: Seq<Form>, env: Seq<TypeBinding>, request: Request)
    requires request.at < forms.len(), request.list.is_none(),
        shape(source, forms, request.at) != Ok(Expression::Let),
        step_model(source, forms, env, request) == Ok(CheckStep::Done),
    ensures typed_expression(Seq::empty(), source, forms, env, request, Goal::Check(request.expected)) == Ok(request.expected),
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
    ensures typed_expression(Seq::empty(), source, forms, env, inferred_request(at), Goal::Infer) == result,
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
        typed_expression(Seq::empty(), source, forms, env, inferred_request(5), Goal::Infer) == first,
        typed_expression(Seq::empty(), source, forms, env, inferred_request(8), Goal::Infer) == second,
    ensures typed_bindings(Seq::empty(), source, forms, env, 0, 9, rows, 0, env) ==
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
