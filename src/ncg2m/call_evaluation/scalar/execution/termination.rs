//! 評価の継続遷移で、待機中の処理を含む残りの仕事量が減ることを示す。

use super::*;
use super::super::termination::{
    expression_work, expression_work_dominates, expression_work_positive, scalar_expression_order, scalar_subexpression_order,
};
use crate::ncg2m::expression_types::named_call::argument_positions_increase;

verus! {

spec fn job_work(rank: usize, at: usize) -> nat {
    expression_work(scalar_expression_order(rank, at))
}

spec fn unstarted_arguments(arguments: Seq<usize>, next: nat) -> Seq<usize> {
    if next < arguments.len() { arguments.subrange(next as int, arguments.len() as int) } else { Seq::empty() }
}

#[verifier::opaque]
spec fn argument_work(rank: usize, arguments: Seq<usize>) -> nat
    decreases arguments.len(),
{
    if arguments.len() == 0 { 0 } else {
        job_work(rank, arguments[0]) + 1 + argument_work(rank, arguments.subrange(1, arguments.len() as int))
    }
}

// 呼び出し元で残った引数、呼び出し先の本体、復帰後の条件分岐をあらかじめ数える。
// 末尾の2は、呼び出し先に入る遷移と呼び出し元に戻る遷移に割り当てる。
spec fn call_work(
    caller_rank: usize, cursor: ScalarCursor, edge: DefnCallEdge, next: nat, to: usize, body: usize,
) -> nat {
    argument_work(caller_rank, unstarted_arguments(edge.arguments@, next))
        + job_work(to, body) + cursor.saved_work_model(caller_rank) + 2
}

spec fn saved_call_work(frame: Waiting) -> nat {
    match frame {
        Waiting::Argument { parent, rank, pending, .. } => {
            let (edge, values, target) = pending.model();
            call_work(rank, parent, edge, values.len() + 1, pending.ranks_model().1, target.at)
        },
        Waiting::Return { parent, rank, .. } => parent.cursor_model().saved_work_model(rank) + 1,
    }
}

#[verifier::opaque]
spec fn waiting_work(stack: Seq<Waiting>) -> nat
    decreases stack.len(),
{
    if stack.len() == 0 { 0 } else { saved_call_work(stack.last()) + waiting_work(stack.drop_last()) }
}

spec fn arguments_in_source_order(arguments: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i && j == i + 1 && j < arguments.len()
        ==> (#[trigger] arguments[i]) < (#[trigger] arguments[j])
}

proof fn ordered_arguments_have_bounded_work(rank: usize, arguments: Seq<usize>)
    requires arguments.len() > 0, arguments_in_source_order(arguments),
    ensures argument_work(rank, arguments) <= 3 * job_work(rank, arguments[0]),
    decreases arguments.len(),
{
    reveal(argument_work);
    let first = arguments[0];
    let rest = arguments.subrange(1, arguments.len() as int);
    expression_work_positive(scalar_expression_order(rank, first));
    assert(argument_work(rank, arguments) == job_work(rank, first) + 1 + argument_work(rank, rest));
    if rest.len() > 0 {
        assert forall|i: int, j: int| 0 <= i && j == i + 1 && j < rest.len()
            implies (#[trigger] rest[i]) < (#[trigger] rest[j]) by {
            assert(rest[i] == arguments[i + 1] && rest[j] == arguments[j + 1]);
            assert(arguments[i + 1] < arguments[j + 1]);
        };
        ordered_arguments_have_bounded_work(rank, rest);
        assert(arguments[0] < arguments[1] && rest[0] == arguments[1]);
        scalar_subexpression_order(rank, first, rank, rest[0]);
        expression_work_dominates(scalar_expression_order(rank, first), scalar_expression_order(rank, rest[0]));
        assert(argument_work(rank, rest) <= 3 * job_work(rank, rest[0]));
        assert(8 * job_work(rank, rest[0]) <= job_work(rank, first));
        assert(argument_work(rank, rest) <= job_work(rank, first));
    } else {
        assert(argument_work(rank, rest) == 0);
    }
    assert(job_work(rank, first) >= 1);
}

proof fn prepared_call_fits_in_expression_work<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, site: usize, parent: ScalarExpression<'p, 'a>,
    args: ScalarArguments<'plan, 'p, 'a>,
)
    requires prepared_arguments_match(plan, rank, site, Some(args)),
        parent.expression_model().at == args.model().0.at,
    ensures call_work(rank, parent.cursor_model(), args.model().0, 0, args.ranks_model().1, args.model().2.at)
        <= parent.expression_work_model(rank),
{
    let (edge, _, target) = args.model();
    let arguments = edge.arguments@;
    let to = args.ranks_model().1;
    let work = scalar_expression_order(rank, edge.at);
    let callee_order = scalar_expression_order(to, target.at);
    prepared_scalar_call_target_reduces_order(plan, rank, site, args);
    expression_work_dominates(work, callee_order);
    expression_work_positive(callee_order);
    parent.expression_work_parts(rank);
    if arguments.len() == 0 {
        reveal(argument_work);
    } else {
        let forms = plan.project_model().functional_forms_model(edge.from.file)->Some_0;
        assert forall|i: int, j: int| 0 <= i && j == i + 1 && j < arguments.len()
            implies (#[trigger] arguments[i]) < (#[trigger] arguments[j]) by {
            argument_positions_increase(forms, edge.at, arguments, i);
        };
        ordered_arguments_have_bounded_work(rank, arguments);
        argument_positions_increase(forms, edge.at, arguments, 0);
        scalar_subexpression_order(rank, edge.at, rank, arguments[0]);
        expression_work_dominates(work, scalar_expression_order(rank, arguments[0]));
        assert(unstarted_arguments(arguments, 0) =~= arguments);
    }
}

proof fn taking_an_argument_reduces_work(rank: usize, arguments: Seq<usize>, next: nat)
    requires next < arguments.len(),
    ensures
        argument_work(rank, unstarted_arguments(arguments, next)) ==
            job_work(rank, arguments[next as int]) + 1 + argument_work(rank, unstarted_arguments(arguments, next + 1)),
{
    reveal(argument_work);
    let remaining = unstarted_arguments(arguments, next);
    assert(remaining[0] == arguments[next as int]);
    assert(remaining.subrange(1, remaining.len() as int) =~= unstarted_arguments(arguments, next + 1));
}

proof fn entering_a_call_reduces_work<'plan, 'p, 'a>(
    rank: usize, parent: ScalarExpression<'p, 'a>, edge: DefnCallEdge<'p, 'a>,
    values: Seq<ScalarValue>, body: super::super::DefnEvaluationBody<'p, 'a>, to: usize,
    stack: Seq<Waiting<'plan, 'p, 'a>>, after: ScalarExecution<'plan, 'p, 'a>,
)
    requires entering_call(rank, parent, edge, values, body, to, stack, after),
    ensures after.remaining_work_model().0 < waiting_work(stack)
        + call_work(rank, parent.cursor_model(), edge, values.len(), to, body.at),
{
    reveal(waiting_work);
    let expr = after.active->Expression_0;
    expr.empty_branch_stack_has_no_work(after.rank);
    if values.len() < edge.arguments@.len() {
        taking_an_argument_reduces_work(rank, edge.arguments@, values.len());
    } else {
        reveal(argument_work);
    }
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 評価中の式、待機中の継続、呼び出し候補の探索に残った仕事を表す。
    pub closed spec fn remaining_work_model(&self) -> (nat, nat) {
        (self.local_work_model().0 + waiting_work(self.waiting@), self.local_work_model().1)
    }

    spec fn local_work_model(&self) -> (nat, nat) {
        let candidates = match self.plan.calls_model_at_rank(self.rank) {
            Some(row) => row.len(),
            None => 0nat,
        };
        match self.active {
            Active::Expression(expr) => (expr.expression_work_model(self.rank), candidates + 1),
            Active::Lookup { parent, site } => (parent.expression_work_model(self.rank), (candidates - site) as nat),
            Active::Value { .. } => (0, 0),
        }
    }

    spec fn continues_in_current_call(&self, after: Self) -> bool {
        !(self.active is Value)
            && self.waiting@ == after.waiting@
            && self.step_matches(Ok(ScalarExecutionSlice::Suspended(after)))
    }

    proof fn current_call_step_reduces_work(&self, after: Self)
        requires self.continues_in_current_call(after),
        ensures {
            let before = self.local_work_model();
            let next = after.local_work_model();
            next.0 < before.0 || (next.0 == before.0 && next.1 < before.1)
        },
    {
        reveal(ScalarExecution::step_matches);
        let rank = self.rank;
        let stack = self.waiting@;
        match self.active {
            Active::Expression(expr) => {
                let inner = choose|inner: ScalarExpressionStep<'p, 'a>| #[trigger] expr.expression_step_matches(Ok(inner))
                    && next_expression_at(after.active, expr.result_type_model(), inner);
                match inner {
                    ScalarExpressionStep::Continue(next) => expr.expression_continuation_reduces_work(rank, next),
                    ScalarExpressionStep::Complete { .. } => expr.expression_has_work(rank),
                    ScalarExpressionStep::NeedsForm(next) => expr.deferred_expression_preserves_work(rank, next),
                }
            },
            Active::Lookup { parent, site } => {
                let row = self.plan.calls_model_at_rank(rank);
                let at = parent.expression_model().at;
                let candidate = row matches Some(edges) && site < edges.len();
                let different = candidate && row->Some_0[site as int].at != at;
                if !different {
                    let expected = parent.expression_model().expected;
                    let args = choose|args: ScalarArguments<'plan, 'p, 'a>|
                        #[trigger] prepared_arguments_match(self.plan, rank, site, Some(args))
                        && args.model().0.at == at && scalar_type_agrees(expected, args.model().2.signature.result_type.ty)
                        && entering_call(rank, parent, args.model().0, args.model().1, args.model().2,
                            args.ranks_model().1, stack, after);
                    assert(after.waiting@.len() == stack.len() + 1);
                    assert(false);
                } else {
                    assert(site < usize::MAX);
                    assert((site + 1) as usize == site + 1);
                    assert(after.rank == rank && after.plan == self.plan);
                    assert(after.active == (Active::Lookup { parent, site: (site + 1) as usize }));
                    assert(self.local_work_model().1 == (row->Some_0.len() - site) as nat);
                    assert(after.local_work_model().1 < self.local_work_model().1);
                }
            },
            Active::Value { .. } => { assert(false); }
        }
    }
    /// 一時停止状態を返すすべての小ステップで、残りの仕事量が辞書式に減る。
    #[verifier::spinoff_prover]
    pub proof fn execution_step_reduces_work(&self, after: Self)
        requires self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures {
            let before = self.remaining_work_model();
            let next = after.remaining_work_model();
            next.0 < before.0 || (next.0 == before.0 && next.1 < before.1)
        },
    {
        reveal(ScalarExecution::step_matches);
        let rank = self.rank;
        let stack = self.waiting@;
        if !(self.active is Value) && stack == after.waiting@ {
            self.current_call_step_reduces_work(after);
        } else {
            match self.active {
                Active::Lookup { parent, site } => {
                    let at = parent.expression_model().at;
                    let expected = parent.expression_model().expected;
                    let args = choose|args: ScalarArguments<'plan, 'p, 'a>|
                        #[trigger] prepared_arguments_match(self.plan, rank, site, Some(args))
                        && args.model().0.at == at && scalar_type_agrees(expected, args.model().2.signature.result_type.ty)
                        && entering_call(rank, parent, args.model().0, args.model().1, args.model().2,
                            args.ranks_model().1, stack, after);
                    prepared_call_fits_in_expression_work(self.plan, rank, site, parent, args);
                    entering_a_call_reduces_work(rank, parent, args.model().0, args.model().1, args.model().2,
                        args.ranks_model().1, stack, after);
                },
                Active::Value { frame, value, .. } => {
                    assert(stack.len() > 0);
                    reveal(waiting_work);
                    match stack.last() {
                        Waiting::Argument { parent, pending, rank: from, .. } => {
                            let (edge, values, target) = pending.model();
                            let to = pending.ranks_model().1;
                            let prefix = values.push(value);
                            let original = choose|expr: ScalarExpression<'p, 'a>| #[trigger] expr.cursor_model() == parent
                                && expr.frame_model() == frame
                                && entering_call(from, expr, edge, prefix, target, to, stack.drop_last(), after);
                            assert(prefix.len() == values.len() + 1);
                            entering_a_call_reduces_work(from, original, edge, prefix, target, to, stack.drop_last(), after);
                        },
                        Waiting::Return { parent, rank: from, .. } => {
                            let inner = choose|inner: ScalarExpressionStep<'p, 'a>| #[trigger] parent.receive_matches(value, inner)
                                && next_expression_at(after.active, parent.result_type_model(), inner);
                            match inner {
                                ScalarExpressionStep::Continue(expr) => parent.received_expression_uses_saved_work(from, value, expr),
                                ScalarExpressionStep::Complete { .. } => {},
                                ScalarExpressionStep::NeedsForm(_) => {
                                    parent.receiving_a_value_resolves_expression(value, inner);
                                    assert(false);
                                },
                            }
                        },
                    }
                },
                Active::Expression(_) => { assert(false); }
            }
        }
    }

}

proof fn prepared_scalar_call_target_reduces_order<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, site: usize, args: ScalarArguments<'plan, 'p, 'a>,
)
    requires prepared_arguments_match(plan, rank, site, Some(args)),
    ensures scalar_expression_order(args.ranks_model().1, args.model().2.at)
        < scalar_expression_order(rank, args.model().0.at),
{
    scalar_subexpression_order(rank, args.model().0.at, args.ranks_model().1, args.model().2.at);
}

}
