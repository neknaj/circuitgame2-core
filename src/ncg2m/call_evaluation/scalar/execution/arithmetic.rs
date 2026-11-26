//! 算術式の左右の引数を同じ環境で順に評価する。

use super::*;
use crate::ncg2m::integer_expression::evaluate_checked_arithmetic;
use crate::ncg2m::integers::IntegerValue;
#[cfg(verus_only)]
use crate::ncg2m::integer_expression::{integer_evaluation_matches, integer_value_number, value_has_type};
#[cfg(verus_only)]
use crate::ncg2m::integers::arithmetic_value;
use crate::project::TypedArithmeticSite;
#[cfg(verus_only)]
use crate::project::defn_call_argument_origin;

verus! {

pub(super) struct ArithmeticWait<'p, 'a> {
    pub(super) parent: ScalarCursor<'p, 'a>,
    pub(super) caller: Ghost<ScalarCallFrame<'p, 'a>>,
    pub(super) rank: usize,
    pub(super) site: TypedArithmeticSite,
    pub(super) ty: IntegerType,
    pub(super) left: Option<IntegerValue>,
}

pub(super) open spec fn arithmetic_type<'a>(ty: IntegerType) -> DataType<'a> {
    DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Integer(ty)), list_depth: 0 }
}

pub(super) open spec fn requested_arithmetic_type(expected: DataType) -> Option<IntegerType> {
    match expected.atom {
        DataTypeAtom::Builtin(BuiltinDataType::Integer(ty)) if expected.list_depth == 0 => Some(ty),
        _ => None,
    }
}

pub(super) fn select_arithmetic_type(expected: DataType) -> (ty: Option<IntegerType>)
    ensures ty == requested_arithmetic_type(expected),
{
    if expected.list_depth == 0 {
        if let DataTypeAtom::Builtin(BuiltinDataType::Integer(ty)) = expected.atom {
            return Some(ty);
        }
    }
    None
}

pub(super) fn arithmetic_operand_type<'a>(ty: IntegerType) -> (result: DataType<'a>)
    ensures result == arithmetic_type(ty),
{
    DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Integer(ty)), list_depth: 0 }
}

pub(super) open spec fn arithmetic_origin(
    plan: &DefnCallPlan, rank: usize, frame: ScalarCallFrame, site: TypedArithmeticSite,
) -> bool {
    let body = frame.body_model();
    &&& plan.body_matches_at_rank(rank, body)
    &&& plan.arithmetic_model_at_rank(rank) matches Some(row) && row.contains(site)
    &&& defn_call_arguments(body.forms@, site.at, seq![site.arguments.0, site.arguments.1])
}

impl<'p, 'a> ArithmeticWait<'p, 'a> {
    pub(super) open spec fn input(&self) -> Context<'p, 'a> {
        (self.rank, self.caller@, arithmetic_type(self.ty))
    }

    pub(super) open spec fn output(&self) -> Context<'p, 'a> {
        (self.rank, self.caller@, self.parent.result_type_model())
    }

    pub(super) open spec fn fits(&self, plan: &DefnCallPlan<'p, 'a>) -> bool {
        &&& self.parent.fits(&self.caller@)
        &&& self.parent.position_model().at == self.site.at
        &&& self.parent.position_model().expected == arithmetic_type(self.ty)
        &&& arithmetic_origin(plan, self.rank, self.caller@, self.site)
        &&& self.left matches Some(value) ==> value_has_type(value, self.ty)
    }
}

pub(super) open spec fn starts_operand(
    active: Active, frame: ScalarCallFrame, at: usize, ty: IntegerType,
) -> bool {
    active matches Active::Expression(expr) && {
        &&& expr.frame_model() == frame
        &&& expr.expression_model() == (super::super::ScalarExpressionSite { at, expected: arithmetic_type(ty) })
        &&& expr.result_type_model() == arithmetic_type(ty)
        &&& expr.branches_model().len() == 0
    }
}

pub(super) open spec fn entering_arithmetic(
    rank: usize, parent: ScalarExpression, site: TypedArithmeticSite, ty: IntegerType, stack: Seq<Waiting>,
    after: ScalarExecution,
) -> bool {
    let pending = ArithmeticWait { parent: parent.cursor_model(), caller: Ghost(parent.frame_model()),
        rank, site, ty, left: None };
    &&& after.rank == rank
    &&& after.waiting@ == stack.push(Waiting::Arithmetic(pending))
    &&& starts_operand(after.active, parent.frame_model(), site.arguments.0, ty)
}

#[verifier::opaque]
pub(super) open spec fn arithmetic_step_matches<'plan, 'p, 'a>(
    wait: ArithmeticWait<'p, 'a>, value: ScalarValue, stack: Seq<Waiting<'plan, 'p, 'a>>,
    step: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
) -> bool {
    let frame = wait.caller@;
    let site = wait.site;
    let body = frame.body_model();
    &&& value matches ScalarValue::Integer(right)
    &&& match wait.left {
        None => step matches Ok(ScalarExecutionSlice::Suspended(after)) && {
            let next = ArithmeticWait { left: Some(right), ..wait };
            &&& after.rank == wait.rank
            &&& after.waiting@ == stack.push(Waiting::Arithmetic(next))
            &&& starts_operand(after.active, frame, site.arguments.1, wait.ty)
        },
        Some(left) => {
            let span = form_span(body.forms@[site.at as int]);
            let number = arithmetic_value(site.operation, integer_value_number(left), integer_value_number(right));
            match step {
                Err(ScalarExecutionError::Arithmetic { source, operation, error }) =>
                    *source == *body.source && operation == site.operation
                        && integer_evaluation_matches(wait.ty, number, span, Err(error)),
                Ok(ScalarExecutionSlice::Suspended(after)) => {
                    &&& after.rank == wait.rank && after.waiting@ == stack
                    &&& exists|result: IntegerValue, parent: ScalarExpression<'p, 'a>, inner: ScalarExpressionStep<'p, 'a>|
                        #[trigger] parent.receive_matches(ScalarValue::Integer(result), inner)
                            && parent.frame_model() == frame && parent.cursor_model() == wait.parent
                            && parent.result_type_model() == wait.parent.result_type_model()
                            && integer_evaluation_matches(wait.ty, number, span, Ok(result))
                            && next_expression_at(after.active, parent.result_type_model(), inner)
                },
                _ => false,
            }
        },
    }
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    pub(super) fn enter_arithmetic(
        plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, parent: ScalarExpression<'p, 'a>,
        site: TypedArithmeticSite, ty: IntegerType, mut waiting: Vec<Waiting<'plan, 'p, 'a>>, result_type: Ghost<DataType<'a>>,
    ) -> (after: Self)
        requires
            arithmetic_origin(plan, rank, parent.frame_model(), site),
            parent.expression_model().at == site.at,
            parent.expression_model().expected == arithmetic_type(ty),
            stack_fits(plan, waiting@, result_type@, (rank, parent.frame_model(), parent.result_type_model())),
        ensures
            after.plan == plan, after.result_type@ == result_type@,
            after.root_frame_model() == root_frame(waiting@, parent.frame_model()),
            entering_arithmetic(rank, parent, site, ty, waiting@, after),
    {
        let ghost stack = waiting@;
        let (frame, cursor) = parent.into_parts();
        let pending = ArithmeticWait { parent: cursor, caller: Ghost(frame), rank, site, ty, left: None };
        proof {
            defn_call_argument_origin(frame.body_model().forms@, site.at, seq![site.arguments.0, site.arguments.1], 0);
            assert(pending.fits(plan));
            append_wait(plan, stack, result_type@, pending.output(), Waiting::Arithmetic(pending));
        }
        let expr = ScalarExpression::start_at(frame, super::super::ScalarExpressionSite {
            at: site.arguments.0, expected: arithmetic_operand_type(ty),
        });
        waiting.push(Waiting::Arithmetic(pending));
        Self { plan, rank, active: Active::Expression(expr), waiting, result_type }
    }

    #[verifier::rlimit(12)]
    pub(super) fn resume_arithmetic(
        plan: &'plan DefnCallPlan<'p, 'a>, pending: ArithmeticWait<'p, 'a>, frame: ScalarCallFrame<'p, 'a>,
        value: ScalarValue, mut waiting: Vec<Waiting<'plan, 'p, 'a>>, result_type: Ghost<DataType<'a>>,
    ) -> (step: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>)
        requires
            pending.fits(plan), frame == pending.caller@,
            scalar_fits(value, pending.input().2),
            stack_fits(plan, waiting@, result_type@, pending.output()),
        ensures
            arithmetic_step_matches(pending, value, waiting@, step),
            step matches Ok(ScalarExecutionSlice::Suspended(after)) ==>
                after.plan == plan && after.result_type@ == result_type@
                    && after.root_frame_model() == root_frame(waiting@, frame),
            !(step matches Ok(ScalarExecutionSlice::Complete(_))),
    {
        reveal(arithmetic_step_matches);
        let ghost initial = pending;
        let ghost stack = waiting@;
        let ScalarValue::Integer(value) = value else { unreachable!() };
        let ArithmeticWait { parent, caller, rank, site, ty, left } = pending;
        let active = if let Some(left) = left {
            let body = frame.body();
            proof {
                defn_call_argument_origin(body.forms@, site.at, seq![site.arguments.0, site.arguments.1], 0);
            }
            let source = body.source;
            let result = match evaluate_checked_arithmetic(site.operation, left, value,
                span_of(&body.forms[site.at]), Ghost(ty))
            {
                Ok(integer) => ScalarValue::Integer(integer),
                Err(error) => return Err(ScalarExecutionError::Arithmetic { source, operation: site.operation, error }),
            };
            let outer = ScalarExpression::restore(frame, parent);
            let ty = Ghost(outer.result_type_model());
            let ghost saved = outer;
            let step = outer.receive(result);
            proof { saved.received_value_resumes_branch(result, step); }
            match step {
                ScalarExpressionStep::Continue(expr) => Active::Expression(expr),
                ScalarExpressionStep::Complete { frame, value } => Active::Value { frame, value, _ty: ty },
                ScalarExpressionStep::NeedsForm(_) => unreachable!(),
            }
        } else {
            let right = ArithmeticWait { parent, caller, rank, site, ty, left: Some(value) };
            proof {
                defn_call_argument_origin(frame.body_model().forms@, site.at, seq![site.arguments.0, site.arguments.1], 1);
                assert(right.fits(plan));
                append_wait(plan, stack, result_type@, initial.output(), Waiting::Arithmetic(right));
            }
            let expr = ScalarExpression::start_at(frame, super::super::ScalarExpressionSite {
                at: site.arguments.1, expected: arithmetic_operand_type(ty),
            });
            waiting.push(Waiting::Arithmetic(right));
            Active::Expression(expr)
        };
        Ok(ScalarExecutionSlice::Suspended(Self { plan, rank, active, waiting, result_type }))
    }
}

}
