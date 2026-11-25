//! スカラー評価の遷移を、次の実行位置、継続、値、診断で比較する。

use super::*;
use crate::ncg2m::data_types::{
    same_defn_signature, signature_parameter_types_agree, signature_result_types_agree,
};
use crate::ncg2m::call_evaluation::scalar::expression::observed_expression_steps_agree;
use crate::ncg2m::call_evaluation::scalar::ScalarCondition;
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

pub(in crate::ncg2m::call_evaluation::scalar) open spec fn type_spelling_agrees(left: DataType, right: DataType) -> bool {
    left.list_depth == right.list_depth && match (left.atom, right.atom) {
        (DataTypeAtom::Builtin(a), DataTypeAtom::Builtin(b)) => a == b,
        (DataTypeAtom::Named(a), DataTypeAtom::Named(b)) => a.spec_bytes() == b.spec_bytes(),
        _ => false,
    }
}

pub(in crate::ncg2m::call_evaluation::scalar) open spec fn bodies_agree(left: super::super::DefnEvaluationBody, right: super::super::DefnEvaluationBody) -> bool {
    left == right || (*left.source == *right.source && left.forms@ == right.forms@ && left.at == right.at
        && same_defn_signature(left.signature, right.signature))
}

pub(in crate::ncg2m::call_evaluation::scalar) open spec fn frames_agree(left: ScalarCallFrame, right: ScalarCallFrame) -> bool {
    bodies_agree(left.body_model(), right.body_model())
        && left.parameter_values_model() == right.parameter_values_model()
}

pub(in crate::ncg2m::call_evaluation::scalar) open spec fn condition_parts_agree(
    left: ScalarCondition, right: ScalarCondition,
) -> bool {
    left.positions_model() == right.positions_model()
        && type_spelling_agrees(left.expected_model(), right.expected_model())
}

pub(in crate::ncg2m::call_evaluation::scalar) open spec fn conditions_agree(
    left: Seq<ScalarCondition>, right: Seq<ScalarCondition>,
) -> bool {
    left == right || (left.len() == right.len()
        && forall|i: int| 0 <= i < left.len() ==> condition_parts_agree(#[trigger] left[i], #[trigger] right[i]))
}

pub(in crate::ncg2m::call_evaluation::scalar) open spec fn positions_agree(
    left: super::super::ScalarExpressionSite, right: super::super::ScalarExpressionSite,
) -> bool {
    left.at == right.at && type_spelling_agrees(left.expected, right.expected)
}

pub(in crate::ncg2m::call_evaluation::scalar) open spec fn cursors_agree(left: ScalarCursor, right: ScalarCursor) -> bool {
    positions_agree(left.position_model(), right.position_model())
        && type_spelling_agrees(left.result_type_model(), right.result_type_model())
        && conditions_agree(left.branches_model(), right.branches_model())
}

pub(in crate::ncg2m::call_evaluation::scalar) open spec fn expressions_agree(left: ScalarExpression, right: ScalarExpression) -> bool {
    &&& frames_agree(left.frame_model(), right.frame_model())
    &&& positions_agree(left.expression_model(), right.expression_model())
    &&& type_spelling_agrees(left.result_type_model(), right.result_type_model())
    &&& conditions_agree(left.branches_model(), right.branches_model())
}

spec fn active_agrees(left: Active, right: Active) -> bool {
    left == right || match (left, right) {
        (Active::Expression(a), Active::Expression(b)) => expressions_agree(a, b),
        (Active::Lookup { parent: a, site: first }, Active::Lookup { parent: b, site: second }) =>
            first == second && expressions_agree(a, b),
        (Active::Value { frame: a, value: first, _ty: t }, Active::Value { frame: b, value: second, _ty: u }) =>
            first == second && frames_agree(a, b) && type_spelling_agrees(t@, u@),
        _ => false,
    }
}

spec fn waiting_agrees(left: Waiting, right: Waiting) -> bool {
    left == right || match (left, right) {
        (Waiting::Argument { parent: a, caller: c, rank: first, pending: aa },
            Waiting::Argument { parent: b, caller: d, rank: second, pending: bb }) => {
            let (edge_a, values_a, body_a) = aa.model();
            let (edge_b, values_b, body_b) = bb.model();
            &&& first == second && frames_agree(c@, d@) && cursors_agree(a, b)
            &&& edge_a == edge_b && values_a == values_b && bodies_agree(body_a, body_b)
            &&& aa.ranks_model() == bb.ranks_model()
        },
        (Waiting::Return { parent: a, rank: first, child: aa },
            Waiting::Return { parent: b, rank: second, child: bb }) => {
            let (rank_a, frame_a, ty_a) = aa@;
            let (rank_b, frame_b, ty_b) = bb@;
            &&& first == second && expressions_agree(a, b)
            &&& rank_a == rank_b && frames_agree(frame_a, frame_b)
            &&& type_spelling_agrees(ty_a, ty_b)
        },
        _ => false,
    }
}

spec fn waiting_stack_agrees(left: Seq<Waiting>, right: Seq<Waiting>) -> bool {
    left == right || (left.len() == right.len()
        && forall|i: int| 0 <= i < left.len() ==> waiting_agrees(#[trigger] left[i], #[trigger] right[i]))
}

/// 再開時の順位、評価位置、環境、継続と戻り値型が一致することを表す。
pub closed spec fn scalar_execution_states_observe_same(left: ScalarExecution, right: ScalarExecution) -> bool {
    &&& left.plan == right.plan
    &&& left.rank == right.rank
    &&& type_spelling_agrees(left.result_type@, right.result_type@)
    &&& active_agrees(left.active, right.active)
    &&& waiting_stack_agrees(left.waiting@, right.waiting@)
}

/// 値と診断の出典、または再開時の式、仮引数環境、継続の内容が一致することを表す。
pub open spec fn scalar_execution_steps_observe_same<'plan, 'p, 'a>(
    left: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    right: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
) -> bool {
    match (left, right) {
        (Ok(ScalarExecutionSlice::Complete(a)), Ok(ScalarExecutionSlice::Complete(b))) => a == b,
        (Ok(ScalarExecutionSlice::Suspended(a)), Ok(ScalarExecutionSlice::Suspended(b))) => scalar_execution_states_observe_same(a, b),
        (Err(ScalarExecutionError::Literal(a)), Err(ScalarExecutionError::Literal(b))) =>
            *a.source == *b.source && a.span == b.span && a.error == b.error,
        (Err(ScalarExecutionError::Deferred { source: a, span: left }),
            Err(ScalarExecutionError::Deferred { source: b, span: right })) => *a == *b && left == right,
        _ => false,
    }
}

proof fn expression_outputs_agree(
    first: Active, second: Active, ty_a: DataType, ty_b: DataType,
    left: ScalarExpressionStep, right: ScalarExpressionStep,
)
    requires next_expression_at(first, ty_a, left), next_expression_at(second, ty_b, right),
        type_spelling_agrees(ty_a, ty_b), observed_expression_steps_agree(Ok(left), Ok(right)),
    ensures active_agrees(first, second),
{}

proof fn corresponding_waits_agree(left: Seq<Waiting>, right: Seq<Waiting>, i: int)
    requires waiting_stack_agrees(left, right), 0 <= i < left.len(),
    ensures waiting_agrees(left[i], right[i]),
{
    if left != right { assert(waiting_agrees(left[i], right[i])); }
}

proof fn remaining_waits_agree(left: Seq<Waiting>, right: Seq<Waiting>)
    requires waiting_stack_agrees(left, right), left.len() > 0,
    ensures waiting_stack_agrees(left.drop_last(), right.drop_last()),
{
    let a = left.drop_last();
    let b = right.drop_last();
    assert forall|i: int| 0 <= i < a.len() implies waiting_agrees(#[trigger] a[i], #[trigger] b[i]) by {
        corresponding_waits_agree(left, right, i);
    };
}

proof fn observe_call_entry<'plan, 'p, 'a>(
    rank: usize, parent_a: ScalarExpression<'p, 'a>, parent_b: ScalarExpression<'p, 'a>,
    edge: DefnCallEdge<'p, 'a>, values: Seq<ScalarValue>, to: usize,
    stack_a: Seq<Waiting<'plan, 'p, 'a>>, stack_b: Seq<Waiting<'plan, 'p, 'a>>,
    target_a: super::super::DefnEvaluationBody<'p, 'a>, target_b: super::super::DefnEvaluationBody<'p, 'a>,
    a: ScalarExecution<'plan, 'p, 'a>, b: ScalarExecution<'plan, 'p, 'a>,
)
    requires expressions_agree(parent_a, parent_b), waiting_stack_agrees(stack_a, stack_b),
        bodies_agree(target_a, target_b),
        entering_call(rank, parent_a, edge, values, target_a, to, stack_a, a),
        entering_call(rank, parent_b, edge, values, target_b, to, stack_b, b),
        target_a != target_b && values.len() < edge.arguments@.len() ==>
            values.len() < target_a.signature.parameters@.len()
                && values.len() < target_b.signature.parameters@.len(),
    ensures a.rank == b.rank, active_agrees(a.active, b.active), waiting_stack_agrees(a.waiting@, b.waiting@),
{
    if target_a != target_b {
        signature_result_types_agree(target_a.signature, target_b.signature);
        if values.len() < edge.arguments@.len() {
            signature_parameter_types_agree(target_a.signature, target_b.signature, values.len() as int);
        }
    }
    let tail_a = a.waiting@.last();
    let tail_b = b.waiting@.last();
    if values.len() < edge.arguments@.len() {
        parent_a.restored_cursors_observe_same(parent_b);
    }
    assert(waiting_agrees(tail_a, tail_b));
    assert forall|i: int| 0 <= i < a.waiting@.len()
        implies waiting_agrees(#[trigger] a.waiting@[i], #[trigger] b.waiting@[i]) by {
        if i < stack_a.len() {
            corresponding_waits_agree(stack_a, stack_b, i);
            assert(a.waiting@.drop_last()[i] == stack_a[i] && b.waiting@.drop_last()[i] == stack_b[i]);
        } else {
            assert(a.waiting@[i] == tail_a && b.waiting@[i] == tail_b);
        }
    };
}

proof fn supplied_calls_agree<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, site: usize,
    a: ScalarArguments<'plan, 'p, 'a>, b: ScalarArguments<'plan, 'p, 'a>,
)
    requires prepared_arguments_match(plan, rank, site, Some(a)), prepared_arguments_match(plan, rank, site, Some(b)),
    ensures a.model().0 == b.model().0, a.model().1 == b.model().1, a.ranks_model() == b.ranks_model(),
        bodies_agree(a.model().2, b.model().2),
        type_spelling_agrees(a.model().2.signature.result_type.ty, b.model().2.signature.result_type.ty),
{
    assert(a.model().1 =~= b.model().1);
    plan.bodies_at_rank_agree(a.ranks_model().1, a.model().2, b.model().2);
    signature_result_types_agree(a.model().2.signature, b.model().2.signature);
}


proof fn call_cannot_be_unresolved<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, site: usize, expected: DataType<'a>, other_expected: DataType<'a>,
    prepared: ScalarArguments<'plan, 'p, 'a>,
)
    requires prepared_arguments_match(plan, rank, site, Some(prepared)), type_spelling_agrees(expected, other_expected),
        scalar_type_agrees(expected, prepared.model().2.signature.result_type.ty),
    ensures !unresolved_call(plan, rank, site, other_expected),
{
    if unresolved_call(plan, rank, site, other_expected) {
        let rejected = choose|args: Option<ScalarArguments<'plan, 'p, 'a>>|
            #[trigger] prepared_arguments_match(plan, rank, site, args) && match args {
                None => true,
                Some(call) => !scalar_type_agrees(other_expected, call.model().2.signature.result_type.ty),
            };
        let other = match rejected {
            Some(other) => other,
            None => { assert(false); return; },
        };
        supplied_calls_agree(plan, rank, site, prepared, other);
        assert(scalar_type_agrees(other_expected, other.model().2.signature.result_type.ty));
    }
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 観測が一致する状態から進めると、1ステップ後の再開状態、値、診断の観測も一致する。
    pub proof fn observed_steps_agree(
        &self, other: Self,
        first: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
        second: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires scalar_execution_states_observe_same(*self, other),
            self.step_matches(first), other.step_matches(second),
        ensures scalar_execution_steps_observe_same(first, second),
    {
        reveal(ScalarExecution::step_matches);
        let rank = self.rank;
        let stack_a = self.waiting@;
        let stack_b = other.waiting@;
        match (self.active, other.active) {
            (Active::Expression(a), Active::Expression(b)) => {
                let x = match first {
                    Err(ScalarExecutionError::Literal(error)) => Err(error),
                    Ok(ScalarExecutionSlice::Suspended(after)) => Ok(choose|inner: ScalarExpressionStep<'p, 'a>|
                        #[trigger] a.expression_step_matches(Ok(inner))
                            && next_expression_at(after.active, a.result_type_model(), inner)),
                    _ => { assert(false); return; },
                };
                let y = match second {
                    Err(ScalarExecutionError::Literal(error)) => Err(error),
                    Ok(ScalarExecutionSlice::Suspended(after)) => Ok(choose|inner: ScalarExpressionStep<'p, 'a>|
                        #[trigger] b.expression_step_matches(Ok(inner))
                            && next_expression_at(after.active, b.result_type_model(), inner)),
                    _ => { assert(false); return; },
                };
                a.expression_steps_agree(b, x, y);
                if let (Ok(ScalarExecutionSlice::Suspended(l)), Ok(ScalarExecutionSlice::Suspended(r))) = (first, second) {
                    expression_outputs_agree(l.active, r.active, a.result_type_model(), b.result_type_model(), x->Ok_0, y->Ok_0);
                }
            },
            (Active::Lookup { parent: a, site }, Active::Lookup { parent: b, .. }) => {
                let row = self.plan.calls_model_at_rank(rank);
                let expect_a = a.expression_model().expected;
                let expect_b = b.expression_model().expected;
                let at = a.expression_model().at;
                let candidate = row matches Some(edges) && site < edges.len();
                if candidate && row->Some_0[site as int].at == at {
                    if let Ok(ScalarExecutionSlice::Suspended(x)) = first {
                        let args = choose|args: ScalarArguments<'plan, 'p, 'a>|
                            #[trigger] prepared_arguments_match(self.plan, rank, site, Some(args))
                            && args.model().0.at == at && scalar_type_agrees(expect_a, args.model().2.signature.result_type.ty)
                            && entering_call(rank, a, args.model().0, args.model().1, args.model().2,
                                args.ranks_model().1, stack_a, x);
                        call_cannot_be_unresolved(self.plan, rank, site, expect_a, expect_b, args);
                        let y = match second {
                            Ok(ScalarExecutionSlice::Suspended(after)) => after,
                            _ => { assert(false); return; },
                        };
                        let other_args = choose|args: ScalarArguments<'plan, 'p, 'a>|
                            #[trigger] prepared_arguments_match(self.plan, rank, site, Some(args))
                            && args.model().0.at == at && scalar_type_agrees(expect_b, args.model().2.signature.result_type.ty)
                            && entering_call(rank, b, args.model().0, args.model().1, args.model().2,
                                args.ranks_model().1, stack_b, y);
                        supplied_calls_agree(self.plan, rank, site, args, other_args);
                        observe_call_entry(rank, a, b, args.model().0, args.model().1, args.ranks_model().1,
                            stack_a, stack_b, args.model().2, other_args.model().2, x, y);
                    } else if let Ok(ScalarExecutionSlice::Suspended(y)) = second {
                        let args = choose|args: ScalarArguments<'plan, 'p, 'a>|
                            #[trigger] prepared_arguments_match(self.plan, rank, site, Some(args))
                            && args.model().0.at == at && scalar_type_agrees(expect_b, args.model().2.signature.result_type.ty)
                            && entering_call(rank, b, args.model().0, args.model().1, args.model().2,
                                args.ranks_model().1, stack_b, y);
                        call_cannot_be_unresolved(self.plan, rank, site, expect_b, expect_a, args);
                    }
                }
            },
            (Active::Value { frame: fa, value, .. }, Active::Value { frame: fb, .. }) if stack_a.len() != 0 => {
                let (x, y) = match (first, second) {
                    (Ok(ScalarExecutionSlice::Suspended(x)), Ok(ScalarExecutionSlice::Suspended(y))) => (x, y),
                    _ => { assert(false); return; },
                };
                corresponding_waits_agree(stack_a, stack_b, stack_a.len() - 1);
                remaining_waits_agree(stack_a, stack_b);
                match (stack_a.last(), stack_b.last()) {
                    (Waiting::Argument { parent: a, pending: pa, rank: from, .. },
                        Waiting::Argument { parent: b, pending: pb, .. }) => {
                        let (edge, values, ta) = pa.model();
                        let tb = pb.model().2;
                        let to = pa.ranks_model().1;
                        let args = values.push(value);
                        let ea = choose|expr: ScalarExpression<'p, 'a>|
                            #[trigger] expr.cursor_model() == a && expr.frame_model() == fa
                            && entering_call(from, expr, edge, args, ta, to, stack_a.drop_last(), x);
                        let eb = choose|expr: ScalarExpression<'p, 'a>|
                            #[trigger] expr.cursor_model() == b && expr.frame_model() == fb
                            && entering_call(from, expr, edge, args, tb, to, stack_b.drop_last(), y);
                        ea.restored_expressions_observe_same(eb);
                        observe_call_entry(from, ea, eb, edge, args, to,
                            stack_a.drop_last(), stack_b.drop_last(), ta, tb, x, y);
                    },
                    (Waiting::Return { parent: a, .. }, Waiting::Return { parent: b, .. }) => {
                        let ea = choose|inner: ScalarExpressionStep<'p, 'a>| #[trigger] a.receive_matches(value, inner)
                            && next_expression_at(x.active, a.result_type_model(), inner);
                        let eb = choose|inner: ScalarExpressionStep<'p, 'a>| #[trigger] b.receive_matches(value, inner)
                            && next_expression_at(y.active, b.result_type_model(), inner);
                        a.received_steps_agree(b, value, ea, eb);
                        expression_outputs_agree(x.active, y.active, a.result_type_model(), b.result_type_model(), ea, eb);
                    },
                    _ => { assert(false); }
                }
            },
            _ => {},
        }
    }

    /// 評価状態の観測に反射性があることを示す。
    pub proof fn observations_match_self(&self)
        ensures scalar_execution_states_observe_same(*self, *self),
    {}

    /// 同じ状態からの1ステップは、再開状態、値、診断のいずれか一つを定める。
    pub proof fn steps_are_observationally_deterministic(
        &self,
        first: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
        second: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires self.step_matches(first), self.step_matches(second),
        ensures scalar_execution_steps_observe_same(first, second),
    {
        self.observations_match_self();
        self.observed_steps_agree(*self, first, second);
    }
}

}
