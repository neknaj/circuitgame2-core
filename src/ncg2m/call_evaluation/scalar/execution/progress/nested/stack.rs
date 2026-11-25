//! 評価中の式とすべての継続に、元の構文位置と型判断を対応させる。

use super::*;
use super::resume::checked_argument_edge;
use crate::ncg2m::call_evaluation::DefnEvaluationBody;
use crate::ncg2m::call_evaluation::scalar::{ScalarCondition, ScalarExpressionSite};

verus! {

spec fn checked_branch(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, frame: ScalarCallFrame, branch: ScalarCondition,
) -> bool {
    let (at, condition, yes, no) = branch.positions_model();
    let body = frame.body_model();
    &&& plan.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite { at, expected: branch.expected_model() })
    &&& conditional_positions(body.source.text_model(), body.forms@, at) == Some((condition, yes, no))
}

spec fn checked_branches(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, frame: ScalarCallFrame,
    branches: Seq<ScalarCondition>,
) -> bool {
    forall|i: int| 0 <= i < branches.len() ==> checked_branch(aliases, plan, rank, frame, #[trigger] branches[i])
}

spec fn checked_expression(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, expr: ScalarExpression,
) -> bool {
    &&& plan.scalar_site_is_checked(aliases, rank, expr.frame_model().body_model(), expr.expression_model())
    &&& checked_branches(aliases, plan, rank, expr.frame_model(), expr.branches_model())
}

spec fn checked_wait(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, wait: Waiting,
) -> bool {
    match wait {
        Waiting::Argument { parent, caller, rank, .. } => {
            &&& checked_branches(aliases, plan, rank, caller@, parent.branches_model())
            &&& exists|site: usize| #[trigger] checked_argument_edge(aliases, plan, wait, site)
        },
        Waiting::Return { parent, rank, .. } => checked_expression(aliases, plan, rank, parent),
    }
}

spec fn checked_waits(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, waits: Seq<Waiting>,
) -> bool {
    forall|i: int| 0 <= i < waits.len() ==> checked_wait(aliases, plan, #[trigger] waits[i])
}

proof fn preserve_wait_prefix(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, old: Seq<Waiting>, next: Seq<Waiting>, kept: int,
)
    requires
        checked_waits(aliases, plan, old),
        0 <= kept <= old.len() && kept <= next.len() <= kept + 1,
        old.take(kept) == next.take(kept),
        next.len() > kept ==> checked_wait(aliases, plan, next.last()),
    ensures checked_waits(aliases, plan, next),
{
    assert forall|i: int| 0 <= i < next.len() implies checked_wait(aliases, plan, #[trigger] next[i]) by {
        if i < kept {
            assert(old.take(kept)[i] == old[i] && next.take(kept)[i] == next[i]);
        } else {
            assert(next[i] == next.last());
        }
    };
}

proof fn enter_checked_if(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, old: ScalarExpression, next: ScalarExpression,
)
    requires
        checked_expression(aliases, plan, rank, old),
        next.frame_model() == old.frame_model(),
        next.branches_model() == old.branches_model().push(next.branches_model().last()),
        next.branches_model().len() == old.branches_model().len() + 1,
        ({
            let branch = next.branches_model().last();
            let (at, condition, yes, no) = branch.positions_model();
            let body = old.frame_model().body_model();
            &&& at == old.expression_model().at && branch.expected_model() == old.expression_model().expected
            &&& conditional_positions(body.source.text_model(), body.forms@, at) == Some((condition, yes, no))
            &&& next.expression_model() == (ScalarExpressionSite {
                at: condition, expected: DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 },
            })
        }),
    ensures checked_expression(aliases, plan, rank, next),
{
    let frame = old.frame_model();
    let body = frame.body_model();
    let branch = next.branches_model().last();
    let (at, condition, yes, no) = branch.positions_model();
    plan.scalar_condition_sites_are_checked(aliases, rank, body, old.expression_model(), condition, yes, no);
    assert forall|i: int| 0 <= i < next.branches_model().len()
        implies checked_branch(aliases, plan, rank, frame, #[trigger] next.branches_model()[i]) by {
        if i < old.branches_model().len() {
            assert(next.branches_model()[i] == old.branches_model()[i]);
        } else {
            assert(next.branches_model()[i] == branch);
        }
    };
}

proof fn select_checked_if_branch(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, old: ScalarExpression, next: ScalarExpression,
)
    requires
        checked_expression(aliases, plan, rank, old),
        next.frame_model() == old.frame_model(),
        old.branches_model().len() > 0 && next.branches_model() == old.branches_model().drop_last(),
        ({
            let branch = old.branches_model().last();
            &&& next.expression_model().expected == branch.expected_model()
            &&& (next.expression_model().at == branch.positions_model().2
                || next.expression_model().at == branch.positions_model().3)
        }),
    ensures checked_expression(aliases, plan, rank, next),
{
    let frame = old.frame_model();
    let branches = old.branches_model();
    let branch = branches.last();
    let (at, condition, yes, no) = branch.positions_model();
    assert(branches[branches.len() - 1] == branch);
    plan.scalar_condition_sites_are_checked(aliases, rank, frame.body_model(),
        ScalarExpressionSite { at, expected: branch.expected_model() }, condition, yes, no);
    assert forall|i: int| 0 <= i < next.branches_model().len()
        implies checked_branch(aliases, plan, rank, frame, #[trigger] next.branches_model()[i]) by {
        assert(next.branches_model()[i] == branches[i]);
    };
}

#[verifier::spinoff_prover]
proof fn enters_with_checked_frame<'plan, 'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, site: usize,
    parent: ScalarExpression<'p, 'a>, edge: DefnCallEdge<'p, 'a>, values: Seq<ScalarValue>,
    callee: DefnEvaluationBody<'p, 'a>, to: usize,
    stack: Seq<Waiting<'plan, 'p, 'a>>, after: ScalarExecution<'plan, 'p, 'a>,
)
    requires
        defn_call_plan_matches(aliases, plan),
        checked_expression(aliases, plan, rank, parent), checked_waits(aliases, plan, stack),
        scalar_type_agrees(parent.expression_model().expected, callee.signature.result_type.ty),
        plan.calls_model_at_rank(rank) matches Some(row) && site < row.len()
            && row[site as int] == edge && edge.at == parent.expression_model().at,
        plan.order_model().contains(edge.to) && plan.order_model().index_of(edge.to) == to,
        plan.body_matches_at_rank(to, callee),
        entering_call(rank, parent, edge, values, callee, to, stack, after),
        after.plan == plan,
    ensures after.preserves_checked_types(aliases),
{
    reveal(ScalarExecution::preserves_checked_types);
    let child = after.active->Expression_0;
    let waits = after.waiting@;
    let wait = waits.last();
    let body = parent.frame_model().body_model();
    if values.len() < edge.arguments@.len() {
        plan.scalar_call_arguments_are_checked(aliases, rank, body, parent.expression_model(), site, callee);
        parent.restored_cursor_positions_agree();
        assert(checked_argument_edge(aliases, plan, wait, site));
        assert(exists|i: usize| #[trigger] checked_argument_edge(aliases, plan, wait, i));
        assert(plan.calls_model_at_rank(rank)->Some_0[site as int].arguments@[values.len() as int]
            == child.expression_model().at);
    } else {
        plan.scalar_body_site_is_checked(aliases, to, callee);
    }
    assert(waits.take(stack.len() as int) =~= stack);
    assert(stack.take(stack.len() as int) =~= stack);
    preserve_wait_prefix(aliases, plan, stack, waits, stack.len() as int);
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 評価中の式と保留中のすべての式が、同じ呼び出し計画の型判断を保つことを表す。
    ///
    /// 値の型と環境の受け渡しは、実行状態の不変条件と一遷移の仕様で保証する。
    pub closed spec fn preserves_checked_types(&self, aliases: &MixedUseAliases<'_, 'p, 'a>) -> bool {
        &&& checked_waits(aliases, self.plan, self.waiting@)
        &&& match self.active {
            Active::Expression(expr) | Active::Lookup { parent: expr, .. } =>
                checked_expression(aliases, self.plan, self.rank, expr),
            Active::Value { .. } => true,
        }
    }

    /// 型判断を保つ状態から一遷移して一時停止した場合、待機中の継続と次の式の型判断が保たれる。
    pub proof fn suspended_step_preserves_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.preserves_checked_types(aliases),
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.plan_model() == self.plan_model(), after.preserves_checked_types(aliases),
    {
        reveal(ScalarExecution::step_matches);
        match self.active {
            Active::Expression(expr) => self.suspended_expression_keeps_checked_types(aliases, expr, after),
            Active::Lookup { parent, site } => self.suspended_lookup_keeps_checked_types(aliases, parent, site, after),
            Active::Value { value, frame, .. } => self.suspended_return_keeps_checked_types(aliases, value, frame, after),
        }
    }

    #[verifier::spinoff_prover]
    proof fn suspended_expression_keeps_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, expr: ScalarExpression<'p, 'a>, after: Self,
    )
        requires
            self.preserves_checked_types(aliases), self.active == Active::Expression(expr),
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.preserves_checked_types(aliases),
    {
        reveal(ScalarExecution::step_matches);
        let inner = choose|inner: ScalarExpressionStep<'p, 'a>| #[trigger] expr.expression_step_matches(Ok(inner))
            && next_expression_at(after.active, expr.result_type_model(), inner);
        expr.expression_step_tracks_saved_conditions(inner);
        if let ScalarExpressionStep::Continue(child) = inner {
            if child.branches_model().len() > expr.branches_model().len() {
                enter_checked_if(aliases, self.plan, self.rank, expr, child);
            } else {
                select_checked_if_branch(aliases, self.plan, self.rank, expr, child);
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn suspended_lookup_keeps_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, parent: ScalarExpression<'p, 'a>, site: usize, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.preserves_checked_types(aliases),
            self.active == (Active::Lookup { parent, site }),
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.preserves_checked_types(aliases),
    {
        reveal(ScalarExecution::step_matches);
        let row = self.plan.calls_model_at_rank(self.rank);
        if row matches Some(edges) && site < edges.len() && edges[site as int].at != parent.expression_model().at {
            return;
        }
        let args = choose|args: ScalarArguments<'plan, 'p, 'a>|
            #[trigger] prepared_arguments_match(self.plan, self.rank, site, Some(args))
            && args.model().0.at == parent.expression_model().at
            && scalar_type_agrees(parent.expression_model().expected, args.model().2.signature.result_type.ty)
            && entering_call(self.rank, parent, args.model().0, args.model().1, args.model().2,
                args.ranks_model().1, self.waiting@, after);
        let (edge, values, callee) = args.model();
        enters_with_checked_frame(aliases, self.plan, self.rank, site, parent, edge, values, callee,
            args.ranks_model().1, self.waiting@, after);
    }

    #[verifier::spinoff_prover]
    proof fn suspended_return_keeps_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, value: ScalarValue, frame: ScalarCallFrame<'p, 'a>, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.preserves_checked_types(aliases),
            self.active matches Active::Value { frame: scope, value: produced, .. } && scope == frame && produced == value,
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.preserves_checked_types(aliases),
    {
        reveal(ScalarExecution::step_matches);
        let stack = self.waiting@;
        let wait = stack.last();
        let kept = stack.drop_last();
        assert(stack.len() > 0 && stack[stack.len() - 1] == wait);
        assert(checked_wait(aliases, self.plan, wait));
        assert(kept =~= stack.take(stack.len() - 1));
        assert(kept.take(kept.len() as int) =~= kept);
        preserve_wait_prefix(aliases, self.plan, stack, kept, kept.len() as int);
        match wait {
            Waiting::Return { parent, rank, .. } => {
                let inner = choose|inner: ScalarExpressionStep<'p, 'a>|
                    #[trigger] parent.receive_matches(value, inner) && next_expression_at(after.active, parent.result_type_model(), inner);
                parent.received_value_resumes_branch(value, inner);
                if let ScalarExpressionStep::Continue(child) = inner {
                    select_checked_if_branch(aliases, self.plan, rank, parent, child);
                }
            },
            Waiting::Argument { parent: cursor, caller, rank, pending } => {
                let (edge, values, callee) = pending.model();
                let to = pending.ranks_model().1;
                let parent = choose|expr: ScalarExpression<'p, 'a>| #[trigger] expr.cursor_model() == cursor
                    && expr.frame_model() == frame
                    && entering_call(rank, expr, edge, values.push(value), callee, to, kept, after);
                let site = choose|i: usize| #[trigger] checked_argument_edge(aliases, self.plan, wait, i);
                parent.restored_cursor_positions_agree();
                enters_with_checked_frame(aliases, self.plan, rank, site, parent, edge, values.push(value),
                    callee, to, kept, after);
            },
        }
    }

    /// 開始に成功した評価状態には、元の本体の型判断があり、保留中の継続は空である。
    pub proof fn starting_execution_preserves_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize, values: Seq<ScalarValue>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()),
            exists|frame: ScalarCallFrame<'p, 'a>| #[trigger] binding_at_rank_matches(self.plan_model(), rank, values, Ok(frame))
                && self.starts_with(self.plan_model(), rank, frame),
        ensures self.preserves_checked_types(aliases),
    {
        reveal(ScalarExecution::starts_with);
        let frame = choose|frame: ScalarCallFrame<'p, 'a>|
            #[trigger] binding_at_rank_matches(self.plan_model(), rank, values, Ok(frame))
                && self.starts_with(self.plan_model(), rank, frame);
        self.plan.scalar_body_site_is_checked(aliases, rank, frame.body_model());
    }
}

}
