//! 条件式と補助関数の呼び出しを、継続を使って評価する。

use alloc::vec::Vec;
use core::ops::Range;
use super::{
    BuiltinDataType, DataType, DataTypeAtom, DefnCallPlan, IntegerType, PendingScalarArgument,
    ProjectSource, ScalarArguments, ScalarArgumentsStep, ScalarBindingError, ScalarCallFrame,
    ScalarExpression, ScalarExpressionStep, ScalarLiteralError, ScalarValue,
    bind_scalar_call, prepare_scalar_arguments,
};
use super::expression::ScalarCursor;
use crate::ncg2m::defn::span_of;
#[cfg(verus_only)]
use super::{binding_at_rank_matches, prepared_arguments_match, scalar_fits};
#[cfg(verus_only)]
use crate::syntax::form_span;
#[cfg(verus_only)]
use crate::project::{DefnCallEdge, defn_call_arguments};
use vstd::prelude::*;

#[cfg(verus_only)]
pub(super) mod observation;
#[cfg(verus_only)]
pub use observation::{scalar_execution_states_observe_same, scalar_execution_steps_observe_same};
mod slice;
#[cfg(verus_only)]
mod progress;
#[cfg(verus_only)]
mod termination;
#[cfg(verus_only)]
pub use slice::{
    finite_scalar_execution_from_progress, finite_scalar_executions_agree, resumed_scalar_execution_matches, scalar_execution_slice_matches, scalar_execution_terminal_extends,
};

verus! {

type Context<'p, 'a> = (usize, ScalarCallFrame<'p, 'a>, DataType<'a>);

enum Active<'p, 'a> {
    Expression(ScalarExpression<'p, 'a>),
    Lookup { parent: ScalarExpression<'p, 'a>, site: usize },
    Value { frame: ScalarCallFrame<'p, 'a>, value: ScalarValue, _ty: Ghost<DataType<'a>> },
}

impl<'p, 'a> Active<'p, 'a> {
    spec fn context(&self, rank: usize) -> Context<'p, 'a> {
        match self {
            Self::Expression(expr) | Self::Lookup { parent: expr, .. } =>
                (rank, expr.frame_model(), expr.result_type_model()),
            Self::Value { frame, _ty, .. } => (rank, *frame, _ty@),
        }
    }

    spec fn valid(&self, plan: &DefnCallPlan<'p, 'a>, rank: usize) -> bool {
        match self {
            Self::Expression(_) => true,
            Self::Lookup { parent, site } => match plan.calls_model_at_rank(rank) {
                Some(row) => *site <= row.len()
                    && (forall|j: int| 0 <= j < *site ==> (#[trigger] row[j]).at != parent.expression_model().at),
                None => *site == 0,
            },
            Self::Value { value, _ty, .. } => scalar_fits(*value, _ty@),
        }
    }
}

enum Waiting<'plan, 'p, 'a> {
    Argument {
        parent: ScalarCursor<'p, 'a>,
        caller: Ghost<ScalarCallFrame<'p, 'a>>,
        rank: usize,
        pending: PendingScalarArgument<'plan, 'p, 'a>,
    },
    Return {
        parent: ScalarExpression<'p, 'a>,
        rank: usize,
        child: Ghost<Context<'p, 'a>>,
    },
}

impl<'plan, 'p, 'a> Waiting<'plan, 'p, 'a> {
    spec fn input(&self) -> Context<'p, 'a> {
        match self {
            Self::Argument { caller, rank, pending, .. } => {
                let (_, values, body) = pending.model();
                (*rank, caller@, body.signature.parameters@[values.len() as int].ty.ty)
            },
            Self::Return { child, .. } => child@,
        }
    }

    spec fn output(&self) -> Context<'p, 'a> {
        match self {
            Self::Argument { parent, caller, rank, .. } => (*rank, caller@, parent.result_type_model()),
            Self::Return { parent, rank, .. } => (*rank, parent.frame_model(), parent.result_type_model()),
        }
    }

    spec fn valid(&self, plan: &DefnCallPlan<'p, 'a>) -> bool {
        match self {
            Self::Argument { parent, caller, rank, pending } => {
                let (edge, values, body) = pending.model();
                &&& parent.fits(&caller@)
                &&& values.len() < body.signature.parameters@.len()
                &&& call_origin(plan, *rank, &caller@, parent.position_model().at, edge)
                &&& pending.ranks_model().0 == *rank
                &&& pending.ranks_model().1 < *rank
                &&& plan.body_matches_at_rank(pending.ranks_model().1, body)
                &&& parent.position_model().expected == body.signature.result_type.ty
            },
            Self::Return { parent, rank, child } => {
                &&& child@.0 < *rank
                &&& child@.2 == parent.expression_model().expected
            },
        }
    }
}

spec fn call_origin<'p, 'a>(
    plan: &DefnCallPlan<'p, 'a>, rank: usize, caller: &ScalarCallFrame<'p, 'a>, at: usize,
    edge: DefnCallEdge<'p, 'a>,
) -> bool {
    let body = caller.body_model();
    &&& plan.body_matches_at_rank(rank, body)
    &&& edge.at == at
    &&& *edge.call.source == *body.source
    &&& defn_call_arguments(body.forms@, at, edge.arguments@)
}

/// 開始位置、仮引数の環境、呼び出し元の継続を持つ評価状態。
pub struct ScalarExecution<'plan, 'p, 'a> {
    plan: &'plan DefnCallPlan<'p, 'a>,
    rank: usize,
    active: Active<'p, 'a>,
    waiting: Vec<Waiting<'plan, 'p, 'a>>,
    result_type: Ghost<DataType<'a>>,
}

/// 実行枠が終わった時点の値または再開状態。
pub enum ScalarExecutionSlice<'plan, 'p, 'a> {
    /// 実行枠を使い切った。保持した状態から評価を再開できる。
    Suspended(ScalarExecution<'plan, 'p, 'a>),
    /// 最初に指定した補助関数の評価値。
    Complete(ScalarValue),
}

/// 評価を続けられなかった理由。
#[derive(Debug)]
pub enum ScalarExecutionError<'p, 'a> {
    /// 整数リテラルを期待型で評価できなかった。
    Literal(ScalarLiteralError<'p, 'a>),
    /// この評価器が扱う式や型の外にある。
    Deferred {
        /// 評価中のソースと文書バージョン。
        source: &'p ProjectSource<'a>,
        /// 評価を保留したフォームの UTF-8 半開バイト範囲。
        span: Range<usize>,
    },
}

spec fn scalar_type_agrees(left: DataType, right: DataType) -> bool {
    left == right && left.list_depth == 0 && (
        left.atom == DataTypeAtom::Builtin(BuiltinDataType::Bool)
        || left.atom == DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Nat))
        || left.atom == DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Int)))
}

fn same_scalar_type(left: DataType, right: DataType) -> (same: bool)
    ensures same == scalar_type_agrees(left, right),
{
    if left.list_depth != 0 || right.list_depth != 0 { return false; }
    matches!((left.atom, right.atom),
        (DataTypeAtom::Builtin(BuiltinDataType::Bool), DataTypeAtom::Builtin(BuiltinDataType::Bool))
        | (DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Nat)),
            DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Nat)))
        | (DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Int)),
            DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Int))))
}

spec fn context_on(plan: &DefnCallPlan, context: Context) -> bool {
    plan.body_matches_at_rank(context.0, context.1.body_model())
}

spec fn stack_fits<'plan, 'p, 'a>(
    plan: &DefnCallPlan<'p, 'a>, stack: Seq<Waiting<'plan, 'p, 'a>>, output: DataType<'a>,
    current: Context<'p, 'a>,
) -> bool {
    &&& context_on(plan, current)
    &&& if stack.len() == 0 { current.2 == output } else {
        current == stack.last().input() && stack[0].output().2 == output
    }
    &&& forall|i: int| 0 <= i < stack.len() ==> {
        let wait = #[trigger] stack[i];
        &&& wait.valid(plan)
        &&& context_on(plan, wait.output())
        &&& (i > 0 ==> stack[i - 1].input() == wait.output())
    }
}

proof fn append_wait<'plan, 'p, 'a>(
    plan: &DefnCallPlan<'p, 'a>, stack: Seq<Waiting<'plan, 'p, 'a>>, output: DataType<'a>,
    before: Context<'p, 'a>, wait: Waiting<'plan, 'p, 'a>,
)
    requires stack_fits(plan, stack, output, before),
        wait.valid(plan), wait.output() == before,
        context_on(plan, wait.input()),
    ensures stack_fits(plan, stack.push(wait), output, wait.input()),
{
    let next = stack.push(wait);
    assert forall|i: int| 0 <= i < next.len() implies {
        let w = #[trigger] next[i];
        &&& w.valid(plan)
        &&& context_on(plan, w.output())
        &&& (i > 0 ==> next[i - 1].input() == w.output())
    } by {
        if i < stack.len() { assert(next[i] == stack[i]); }
        else { assert(next[i] == wait); }
    };
}

proof fn remove_wait<'plan, 'p, 'a>(
    plan: &DefnCallPlan<'p, 'a>, stack: Seq<Waiting<'plan, 'p, 'a>>, output: DataType<'a>,
    current: Context<'p, 'a>,
)
    requires stack_fits(plan, stack, output, current), stack.len() > 0,
    ensures stack_fits(plan, stack.drop_last(), output, stack.last().output()),
{
    let tail = stack.drop_last();
    let last = stack.last();
    assert(stack[stack.len() - 1] == last);
    assert forall|i: int| 0 <= i < tail.len() implies {
        let w = #[trigger] tail[i];
        &&& w.valid(plan)
        &&& context_on(plan, w.output())
        &&& (i > 0 ==> tail[i - 1].input() == w.output())
    } by { assert(tail[i] == stack[i]); };
}

spec fn entering_call<'plan, 'p, 'a>(
    caller_rank: usize, parent: ScalarExpression<'p, 'a>, edge: DefnCallEdge<'p, 'a>,
    values: Seq<ScalarValue>, target: super::DefnEvaluationBody<'p, 'a>,
    to: usize, stack: Seq<Waiting<'plan, 'p, 'a>>, after: ScalarExecution<'plan, 'p, 'a>,
) -> bool {
    &&& after.waiting@.len() == stack.len() + 1
    &&& after.waiting@.drop_last() == stack
    &&& after.active matches Active::Expression(child) && child.branches_model().len() == 0 && {
        let wait = after.waiting@.last();
        if values.len() < edge.arguments@.len() {
            wait matches Waiting::Argument { parent: resume, caller, rank, pending }
                && resume == parent.cursor_model()
                && caller@ == parent.frame_model() && rank == caller_rank && after.rank == rank
                && pending.model() == (edge, values, target) && pending.ranks_model() == (caller_rank, to)
                && child.frame_model() == parent.frame_model()
                && child.expression_model().at == edge.arguments@[values.len() as int]
                && child.expression_model().expected == target.signature.parameters@[values.len() as int].ty.ty
                && child.result_type_model() == child.expression_model().expected
        } else {
            wait matches Waiting::Return { parent: resume, rank, child: origin }
                && resume == parent && rank == caller_rank && after.rank == to && to < rank
                && origin@ == after.active.context(to)
                && child.frame_model().body_model() == target && child.frame_model().parameter_values_model() == values
                && child.expression_model().at == target.at
                && child.expression_model().expected == target.signature.result_type.ty
                && child.result_type_model() == child.expression_model().expected
        }
    }
}

spec fn next_expression_at<'p, 'a>(
    active: Active<'p, 'a>, ty: DataType<'a>, next: ScalarExpressionStep<'p, 'a>,
) -> bool {
    match (active, next) {
        (Active::Expression(after), ScalarExpressionStep::Continue(expr)) => after == expr,
        (Active::Value { frame, value, _ty: result_ty },
            ScalarExpressionStep::Complete { frame: scope, value: result }) =>
                frame == scope && value == result && result_ty@ == ty,
        (Active::Lookup { parent, site: 0 }, ScalarExpressionStep::NeedsForm(expr)) => parent == expr,
        _ => false,
    }
}

spec fn unresolved_call<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, site: usize, expected: DataType<'a>,
) -> bool {
    exists|args: Option<ScalarArguments<'plan, 'p, 'a>>| #[trigger] prepared_arguments_match(plan, rank, site, args)
        && match args {
            None => true,
            Some(call) => !scalar_type_agrees(expected, call.model().2.signature.result_type.ty),
        }
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    #[verifier::type_invariant]
    spec fn ready(&self) -> bool {
        self.active.valid(self.plan, self.rank) && stack_fits(self.plan, self.waiting@, self.result_type@, self.active.context(self.rank))
    }

    /// 評価を開始した補助関数の戻り値型を表す。
    pub closed spec fn result_type_model(&self) -> DataType<'a> { self.result_type@ }

    /// 指定した関数の本体と仮引数の環境から評価を始めたことを表す。
    pub closed spec fn starts_with(
        &self, plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, frame: ScalarCallFrame<'p, 'a>,
    ) -> bool {
        &&& self.plan == plan && self.rank == rank && self.waiting@.len() == 0
        &&& self.active matches Active::Expression(expr)
            && expr.frame_model() == frame
            && expr.expression_model().at == frame.body_model().at
            && expr.expression_model().expected == frame.body_model().signature.result_type.ty
            && expr.result_type_model() == expr.expression_model().expected
            && expr.branches_model().len() == 0
            && self.result_type_model() == expr.result_type_model()
    }

    /// 指定した順位の補助関数に仮引数を束縛し、評価を開始する。
    ///
    /// # Errors
    ///
    /// 順位、引数の個数、または型が署名に合わないときは束縛の診断を返す。
    pub fn start(plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, values: Vec<ScalarValue>)
        -> (result: Result<Self, ScalarBindingError<'p, 'a>>)
        ensures match result {
            Ok(state) => exists|frame: ScalarCallFrame<'p, 'a>|
                #[trigger] binding_at_rank_matches(plan, rank, values@, Ok(frame))
                    && state.starts_with(plan, rank, frame),
            Err(error) => binding_at_rank_matches(plan, rank, values@, Err(error)),
        },
    {
        let frame = bind_scalar_call(plan, rank, values)?;
        let result_type = Ghost(frame.body_model().signature.result_type.ty);
        let active = Active::Expression(ScalarExpression::start(frame));
        Ok(Self { plan, rank, active, waiting: Vec::new(), result_type })
    }

    fn enter_call(
        plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, parent: ScalarExpression<'p, 'a>,
        args: ScalarArguments<'plan, 'p, 'a>, mut waiting: Vec<Waiting<'plan, 'p, 'a>>, result_type: Ghost<DataType<'a>>,
    ) -> (state: Self)
        requires
            stack_fits(plan, waiting@, result_type@, (rank, parent.frame_model(), parent.result_type_model())),
            call_origin(plan, rank, &parent.frame_model(), parent.expression_model().at, args.model().0),
            args.ranks_model().0 == rank, args.ranks_model().1 < rank,
            plan.body_matches_at_rank(args.ranks_model().1, args.model().2),
            args.model().2.signature.result_type.ty == parent.expression_model().expected,
        ensures state.result_type_model() == result_type@, state.plan == plan,
            entering_call(rank, parent, args.model().0, args.model().1, args.model().2,
                args.ranks_model().1, waiting@, state),
    {
        let ghost before = (rank, parent.frame_model(), parent.result_type_model());
        let ghost stack = waiting@;
        match args.next() {
            ScalarArgumentsStep::Argument(pending) => {
                let (caller, cursor) = parent.into_parts();
                let arg = pending.expression_in(Ghost(caller.body_model().forms@));
                let stored = Waiting::Argument { parent: cursor, caller: Ghost(caller), rank, pending };
                let active = Active::Expression(ScalarExpression::start_at(caller, arg));
                proof { append_wait(plan, stack, result_type@, before, stored); }
                waiting.push(stored);
                assert(waiting@.drop_last() =~= stack);
                Self { plan, rank, active, waiting, result_type }
            },
            ScalarArgumentsStep::Enter { rank: to, frame } => {
                let stored = Waiting::Return { parent, rank,
                    child: Ghost((to, frame, frame.body_model().signature.result_type.ty)),
                };
                let active = Active::Expression(ScalarExpression::start(frame));
                proof { append_wait(plan, stack, result_type@, before, stored); }
                waiting.push(stored);
                assert(waiting@.drop_last() =~= stack);
                Self { plan, rank: to, active, waiting, result_type }
            },
        }
    }

    /// 1ステップで評価する式、継続の変化、または確定する結果を表す。
    pub closed spec fn step_matches(&self,
        step: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    ) -> bool {
        let rank = self.rank;
        let stack = self.waiting@;
        &&& (step matches Ok(ScalarExecutionSlice::Suspended(after)) ==>
            after.plan == self.plan && after.result_type@ == self.result_type@)
        &&& match self.active {
            Active::Expression(expr) => match step {
                Ok(ScalarExecutionSlice::Suspended(after)) => {
                    &&& after.rank == rank && after.waiting@ == stack
                    &&& exists|inner: ScalarExpressionStep<'p, 'a>|
                        #[trigger] expr.expression_step_matches(Ok(inner))
                            && next_expression_at(after.active, expr.result_type_model(), inner)
                },
                Err(ScalarExecutionError::Literal(error)) => expr.expression_step_matches(Err(error)),
                _ => false,
            },
            Active::Lookup { parent, site } => {
                let row = self.plan.calls_model_at_rank(rank);
                let at = parent.expression_model().at;
                let expected = parent.expression_model().expected;
                let body = parent.frame_model().body_model();
                let candidate = row matches Some(edges) && site < edges.len();
                let different = candidate && row->Some_0[site as int].at != at;
                match step {
                    Ok(ScalarExecutionSlice::Suspended(after)) if different =>
                        site < usize::MAX && after.rank == rank && after.waiting@ == stack
                            && after.active == (Active::Lookup { parent, site: (site + 1) as usize }),
                    Ok(ScalarExecutionSlice::Suspended(after)) => candidate
                        && exists|args: ScalarArguments<'plan, 'p, 'a>|
                            #[trigger] prepared_arguments_match(self.plan, rank, site, Some(args))
                            && args.model().0.at == at && scalar_type_agrees(expected, args.model().2.signature.result_type.ty)
                            && entering_call(rank, parent, args.model().0, args.model().1, args.model().2,
                                args.ranks_model().1, stack, after),
                    Err(ScalarExecutionError::Deferred { source, span }) =>
                        *source == *body.source && at < body.forms@.len()
                            && span == form_span(body.forms@[at as int])
                            && (!candidate || (!different && unresolved_call(self.plan, rank, site, expected))),
                    _ => false,
                }
            },
            Active::Value { frame, value, .. } => if stack.len() == 0 {
                step matches Ok(ScalarExecutionSlice::Complete(out)) && out == value
            } else {
                step matches Ok(ScalarExecutionSlice::Suspended(after)) && match stack.last() {
                    Waiting::Argument { parent, caller, pending, rank: from } => {
                        let (edge, values, target) = pending.model();
                        &&& frame == caller@
                        &&& parent.fits(&frame)
                        &&& edge.arguments@.len() == target.signature.parameters@.len()
                        &&& exists|expr: ScalarExpression<'p, 'a>| #[trigger] expr.cursor_model() == parent
                            && expr.frame_model() == frame
                            && entering_call(from, expr, edge, values.push(value), target,
                                pending.ranks_model().1, stack.drop_last(), after)
                    },
                    Waiting::Return { parent, rank: from, .. } => {
                        &&& after.rank == from && after.waiting@ == stack.drop_last()
                        &&& (after.active is Value ==> scalar_fits(value, parent.result_type_model()))
                        &&& exists|inner: ScalarExpressionStep<'p, 'a>| #[trigger] parent.receive_matches(value, inner)
                            && next_expression_at(after.active, parent.result_type_model(), inner)
                    },
                }
            },
        }
    }

    fn step(self) -> (step: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>)
        ensures self.step_matches(step),
        match step {
            Ok(ScalarExecutionSlice::Suspended(state)) => state.result_type_model() == self.result_type_model(),
            Ok(ScalarExecutionSlice::Complete(value)) => scalar_fits(value, self.result_type_model()),
            Err(_) => true,
        },
    {
        proof { use_type_invariant(&self); }
        let ghost previous = self;
        let Self { plan, rank, active, mut waiting, result_type } = self;
        let ghost context = active.context(rank);
        let ghost stack = waiting@;
        let state = match active {
            Active::Expression(expr) => {
                let ty = Ghost(expr.result_type_model());
                let inner = expr.advance();
                match inner {
                    Ok(ScalarExpressionStep::Continue(expr)) =>
                        Self { plan, rank, active: Active::Expression(expr), waiting, result_type },
                    Ok(ScalarExpressionStep::Complete { value, frame }) => {
                        Self { plan, rank, active: Active::Value { frame, value, _ty: ty }, waiting, result_type }
                    }
                    Err(error) => return Err(ScalarExecutionError::Literal(error)),
                    Ok(ScalarExpressionStep::NeedsForm(parent)) =>
                        Self { plan, rank, active: Active::Lookup { parent, site: 0 }, waiting, result_type },
                }
            },
            Active::Lookup { parent, site } => {
                let at = parent.expression().at;
                if let Some(row) = plan.calls_at_rank(rank) {
                    if site < row.len() {
                        let edge = &row[site];
                        if edge.at != at {
                            let active = Active::Lookup { parent, site: site + 1 };
                            return Ok(ScalarExecutionSlice::Suspended(Self { plan, rank, active, waiting, result_type }));
                        }
                        let prepared = prepare_scalar_arguments(plan, rank, site);
                        if let Some(args) = prepared {
                            let expected = parent.expression().expected;
                            if same_scalar_type(expected, args.result_type()) {
                                proof {
                                    assert(args.model().0 == *edge);
                                    assert(plan.order_model()[rank as int] == edge.from);
                                    assert(call_origin(plan, rank, &parent.frame_model(), at, *edge));
                                }
                                let after = Self::enter_call(plan, rank, parent, args, waiting, result_type);
                                assert(previous.step_matches(Ok(ScalarExecutionSlice::Suspended(after))));
                                return Ok(ScalarExecutionSlice::Suspended(after));
                            }
                        }
                        assert(unresolved_call(plan, rank, site, parent.expression_model().expected));
                    }
                }
                let (frame, _) = parent.into_parts();
                let body = frame.body();
                return Err(ScalarExecutionError::Deferred { source: body.source, span: span_of(&body.forms[at]) });
            },
            Active::Value { frame, value, .. } => {
                let Some(resume) = waiting.pop() else { return Ok(ScalarExecutionSlice::Complete(value)); };
                proof {
                    assert(resume == stack.last() && waiting@ =~= stack.drop_last());
                    assert(resume.valid(plan));
                    remove_wait(plan, stack, result_type@, context);
                }
                match resume {
                    Waiting::Argument { parent, rank, pending, .. } => {
                        let Ok(args) = pending.resume(value) else { unreachable!() };
                        let original = ScalarExpression::restore(frame, parent);
                        let after = Self::enter_call(plan, rank, original, args, waiting, result_type);
                        assert(previous.step_matches(Ok(ScalarExecutionSlice::Suspended(after))));
                        after
                    },
                    Waiting::Return { parent, rank, .. } => {
                        let ty = Ghost(parent.result_type_model());
                        let ghost saved = parent;
                        let inner = parent.receive(value);
                        proof { saved.received_value_resumes_branch(value, inner); }
                        let active = match inner {
                            ScalarExpressionStep::Continue(expr) => Active::Expression(expr),
                            ScalarExpressionStep::Complete { frame, value } => Active::Value { frame, value, _ty: ty },
                            ScalarExpressionStep::NeedsForm(_) => unreachable!(),
                        };
                        let after = Self { plan, rank, active, waiting, result_type };
                        assert(previous.step_matches(Ok(ScalarExecutionSlice::Suspended(after))));
                        after
                    },
                }
            },
        };
        Ok(ScalarExecutionSlice::Suspended(state))
    }

}

}
