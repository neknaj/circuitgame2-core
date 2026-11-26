//! 評価中の式とすべての継続に、元の構文位置と型判断を対応させる。

use super::*;
use super::resume::checked_argument_edge;
use crate::ncg2m::call_evaluation::DefnEvaluationBody;
use crate::ncg2m::call_evaluation::scalar::{ScalarCondition, ScalarExpressionSite};
use crate::ncg2m::expression_types::{
    scalar_atom_at, scalar_evaluator_syntax, scalar_syntax_form_kind, scalar_syntax_if_children,
    scalar_syntax_matches_call_arguments,
};
use crate::ncg2m::expression_types::named_call::CheckedNamedTarget;

verus! {

spec fn supported_position(plan: &DefnCallPlan, rank: usize, frame: ScalarCallFrame, site: ScalarExpressionSite) -> bool {
    let body = frame.body_model();
    &&& !frame.has_scoped_bindings()
    &&& plan.scalar_fragment_is_closed(rank)
    &&& plan.scalar_fragment_value_type(site.expected)
    &&& scalar_evaluator_syntax(body.source.text_model(), body.forms@, site.at)
}

spec fn checked_branch(
    supported: bool, aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, frame: ScalarCallFrame, branch: ScalarCondition,
) -> bool {
    let (at, condition, yes, no) = branch.positions_model();
    let body = frame.body_model();
    &&& plan.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite { at, expected: branch.expected_model() })
    &&& conditional_positions(body.source.text_model(), body.forms@, at) == Some((condition, yes, no))
    &&& (supported ==> supported_position(plan, rank, frame, ScalarExpressionSite { at, expected: branch.expected_model() }))
}

spec fn checked_branches(
    supported: bool, aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, frame: ScalarCallFrame,
    branches: Seq<ScalarCondition>,
) -> bool {
    forall|i: int| 0 <= i < branches.len() ==> checked_branch(supported, aliases, plan, rank, frame, #[trigger] branches[i])
}

spec fn checked_expression(
    supported: bool, aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, expr: ScalarExpression,
) -> bool {
    &&& plan.scalar_site_is_checked(aliases, rank, expr.frame_model().body_model(), expr.expression_model())
    &&& checked_branches(supported, aliases, plan, rank, expr.frame_model(), expr.branches_model())
    &&& (supported ==> supported_position(plan, rank, expr.frame_model(), expr.expression_model()))
}

spec fn checked_wait(
    supported: bool, aliases: &MixedUseAliases, plan: &DefnCallPlan, wait: Waiting,
) -> bool {
    match wait {
        Waiting::Argument { parent, caller, rank, .. } => {
            &&& checked_branches(supported, aliases, plan, rank, caller@, parent.branches_model())
            &&& (supported ==> supported_position(plan, rank, caller@, parent.position_model()))
            &&& exists|site: usize| #[trigger] checked_argument_edge(aliases, plan, wait, site)
        },
        Waiting::Return { parent, rank, .. } => checked_expression(supported, aliases, plan, rank, parent),
        Waiting::Arithmetic(wait) => {
            let body = wait.caller@.body_model();
            let expected = arithmetic::arithmetic_type(wait.ty);
            let left = ScalarExpressionSite { at: wait.site.arguments.0, expected };
            let right = ScalarExpressionSite { at: wait.site.arguments.1, expected };
            &&& checked_branches(supported, aliases, plan, wait.rank, wait.caller@, wait.parent.branches_model())
            &&& plan.scalar_site_is_checked(aliases, wait.rank, body, wait.parent.position_model())
            &&& plan.scalar_site_is_checked(aliases, wait.rank, body, left)
            &&& plan.scalar_site_is_checked(aliases, wait.rank, body, right)
            &&& (supported ==> supported_position(plan, wait.rank, wait.caller@, wait.parent.position_model())
                && supported_position(plan, wait.rank, wait.caller@, left)
                && supported_position(plan, wait.rank, wait.caller@, right))
        },
    }
}

spec fn checked_waits(
    supported: bool, aliases: &MixedUseAliases, plan: &DefnCallPlan, waits: Seq<Waiting>,
) -> bool {
    forall|i: int| 0 <= i < waits.len() ==> checked_wait(supported, aliases, plan, #[trigger] waits[i])
}

proof fn preserve_wait_prefix(
    supported: bool, aliases: &MixedUseAliases, plan: &DefnCallPlan, old: Seq<Waiting>, next: Seq<Waiting>, kept: int,
)
    requires
        checked_waits(supported, aliases, plan, old),
        0 <= kept <= old.len() && kept <= next.len() <= kept + 1,
        old.take(kept) == next.take(kept),
        next.len() > kept ==> checked_wait(supported, aliases, plan, next.last()),
    ensures checked_waits(supported, aliases, plan, next),
{
    assert forall|i: int| 0 <= i < next.len() implies checked_wait(supported, aliases, plan, #[trigger] next[i]) by {
        if i < kept {
            assert(old.take(kept)[i] == old[i] && next.take(kept)[i] == next[i]);
        } else {
            assert(next[i] == next.last());
        }
    };
}

proof fn enter_checked_if(
    supported: bool, aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, old: ScalarExpression, next: ScalarExpression,
)
    requires
        checked_expression(supported, aliases, plan, rank, old),
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
    ensures checked_expression(supported, aliases, plan, rank, next),
{
    let frame = old.frame_model();
    let body = frame.body_model();
    let branch = next.branches_model().last();
    let (at, condition, yes, no) = branch.positions_model();
    plan.scalar_condition_sites_are_checked(aliases, rank, body, old.expression_model(), condition, yes, no);
    if supported {
        scalar_syntax_if_children(body.source.text_model(), body.forms@, at, condition, yes, no);
    }
    assert forall|i: int| 0 <= i < next.branches_model().len()
        implies checked_branch(supported, aliases, plan, rank, frame, #[trigger] next.branches_model()[i]) by {
        if i < old.branches_model().len() {
            assert(next.branches_model()[i] == old.branches_model()[i]);
        } else {
            assert(next.branches_model()[i] == branch);
        }
    };
}

proof fn select_checked_if_branch(
    supported: bool, aliases: &MixedUseAliases, plan: &DefnCallPlan, rank: usize, old: ScalarExpression, next: ScalarExpression,
)
    requires
        checked_expression(supported, aliases, plan, rank, old),
        next.frame_model() == old.frame_model(),
        old.branches_model().len() > 0 && next.branches_model() == old.branches_model().drop_last(),
        ({
            let branch = old.branches_model().last();
            &&& next.expression_model().expected == branch.expected_model()
            &&& (next.expression_model().at == branch.positions_model().2
                || next.expression_model().at == branch.positions_model().3)
        }),
    ensures checked_expression(supported, aliases, plan, rank, next),
{
    let frame = old.frame_model();
    let branches = old.branches_model();
    let branch = branches.last();
    let (at, condition, yes, no) = branch.positions_model();
    assert(branches[branches.len() - 1] == branch);
    plan.scalar_condition_sites_are_checked(aliases, rank, frame.body_model(),
        ScalarExpressionSite { at, expected: branch.expected_model() }, condition, yes, no);
    if supported {
        let body = frame.body_model();
        scalar_syntax_if_children(body.source.text_model(), body.forms@, at, condition, yes, no);
    }
    assert forall|i: int| 0 <= i < next.branches_model().len()
        implies checked_branch(supported, aliases, plan, rank, frame, #[trigger] next.branches_model()[i]) by {
        assert(next.branches_model()[i] == branches[i]);
    };
}

#[verifier::spinoff_prover]
proof fn enters_with_checked_frame<'plan, 'p, 'a>(
    supported: bool, aliases: &MixedUseAliases<'_, 'p, 'a>, plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, site: usize,
    parent: ScalarExpression<'p, 'a>, edge: DefnCallEdge<'p, 'a>, values: Seq<ScalarValue>,
    callee: DefnEvaluationBody<'p, 'a>, to: usize,
    stack: Seq<Waiting<'plan, 'p, 'a>>, after: ScalarExecution<'plan, 'p, 'a>,
)
    requires
        defn_call_plan_matches(aliases, plan),
        checked_expression(supported, aliases, plan, rank, parent), checked_waits(supported, aliases, plan, stack),
        scalar_type_agrees(parent.expression_model().expected, callee.signature.result_type.ty),
        plan.calls_model_at_rank(rank) matches Some(row) && site < row.len()
            && row[site as int] == edge && edge.at == parent.expression_model().at,
        plan.order_model().contains(edge.to) && plan.order_model().index_of(edge.to) == to,
        plan.body_matches_at_rank(to, callee),
        entering_call(rank, parent, edge, values, callee, to, stack, after),
        after.plan == plan,
    ensures after.state_has_checked_positions(aliases, supported),
{
    reveal(ScalarExecution::state_has_checked_positions);
    let child = after.active->Expression_0;
    let waits = after.waiting@;
    let wait = waits.last();
    let body = parent.frame_model().body_model();
    if supported {
        supported_call_children(aliases, plan, rank, site, parent, to, callee);
    }
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
    preserve_wait_prefix(supported, aliases, plan, stack, waits, stack.len() as int);
}

#[verifier::spinoff_prover]
proof fn supported_call_children<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, plan: &DefnCallPlan<'p, 'a>, rank: usize, site: usize,
    parent: ScalarExpression<'p, 'a>, to: usize, target: DefnEvaluationBody<'p, 'a>,
)
    requires
        defn_call_plan_matches(aliases, plan),
        checked_expression(true, aliases, plan, rank, parent),
        plan.body_matches_at_rank(to, target),
        plan.calls_model_at_rank(rank) matches Some(row) && site < row.len() && {
            let edge = row[site as int];
            &&& edge.at == parent.expression_model().at
            &&& to == plan.order_model().index_of(edge.to)
        },
    ensures
        plan.scalar_fragment_is_closed(to), plan.scalar_fragment_body(to, target),
        forall|i: int| 0 <= i < plan.calls_model_at_rank(rank)->Some_0[site as int].arguments@.len() ==> {
            let body = parent.frame_model().body_model();
            let at = #[trigger] plan.calls_model_at_rank(rank)->Some_0[site as int].arguments@[i];
            scalar_evaluator_syntax(body.source.text_model(), body.forms@, at)
        },
{
    let body = parent.frame_model().body_model();
    let position = parent.expression_model();
    let (ranked, _) = plan.closed_scalar_fragment_callee(rank, site);
    assert(ranked == to);
    plan.closed_scalar_fragment_matches_body(to, target);
    plan.checked_site_has_the_rank_body(aliases, rank, body, position);
    let at = defn_call_plan_site_at_rank(aliases, plan, rank, site);
    let from = plan.order_model()[rank as int];
    assert(at == position.at);
    assert(plan.project_model().functional_forms_model(from.file) == Some(body.forms@));
    assert(body.forms@[at as int] is List);
    assert(conditional_positions(body.source.text_model(), body.forms@, at).is_none());
    scalar_syntax_form_kind(body.source.text_model(), body.forms@, at);
    let edge = plan.calls_model_at_rank(rank)->Some_0[site as int];
    scalar_syntax_matches_call_arguments(body.source.text_model(), body.forms@, at, edge.arguments@);
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 評価中の式と保留中のすべての式が、同じ呼び出し計画の型判断を保つことを表す。
    ///
    /// 値の型と環境の受け渡しは、実行状態の不変条件と一遷移の仕様で保証する。
    pub closed spec fn preserves_checked_types(&self, aliases: &MixedUseAliases<'_, 'p, 'a>) -> bool {
        self.state_has_checked_positions(aliases, false)
    }

    /// 評価中と待機中の式が型判断を保ち、対応構文と呼び出し先の範囲に収まることを表す。
    pub closed spec fn preserves_supported_fragment(&self, aliases: &MixedUseAliases<'_, 'p, 'a>) -> bool {
        self.state_has_checked_positions(aliases, true)
    }

    spec fn has_recorded_arithmetic_lookup(&self) -> bool {
        self.active matches Active::Lookup { parent, site: 0 } && {
            let position = parent.expression_model();
            &&& self.plan.arithmetic_site_model(self.rank, position.at).is_some()
            &&& arithmetic::requested_arithmetic_type(position.expected).is_some()
        }
    }

    spec fn state_has_checked_positions(&self, aliases: &MixedUseAliases<'_, 'p, 'a>, supported: bool) -> bool {
        &&& checked_waits(supported, aliases, self.plan, self.waiting@)
        &&& (supported && self.active is Lookup ==>
            self.searches_checked_scalar_call(aliases) || self.has_recorded_arithmetic_lookup())
        &&& match self.active {
            Active::Expression(expr) | Active::Lookup { parent: expr, .. } =>
                checked_expression(supported, aliases, self.plan, self.rank, expr),
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
        self.suspended_step_keeps_checked_positions(aliases, false, after);
    }

    /// 対応断片の状態を一遷移させて再開状態を得た場合、その全継続が同じ断片に属する。
    pub proof fn suspended_step_preserves_supported_fragment(&self, aliases: &MixedUseAliases<'_, 'p, 'a>, after: Self)
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.preserves_supported_fragment(aliases),
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.plan_model() == self.plan_model(), after.preserves_supported_fragment(aliases),
    {
        self.suspended_step_keeps_checked_positions(aliases, true, after);
    }

    proof fn suspended_step_keeps_checked_positions(&self, aliases: &MixedUseAliases<'_, 'p, 'a>, supported: bool, after: Self)
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.state_has_checked_positions(aliases, supported),
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.plan_model() == self.plan_model(), after.state_has_checked_positions(aliases, supported),
    {
        reveal(ScalarExecution::step_matches);
        match self.active {
            Active::Expression(expr) => self.suspended_expression_keeps_checked_types(aliases, supported, expr, after),
            Active::Lookup { parent, site } => self.suspended_lookup_keeps_checked_types(aliases, supported, parent, site, after),
            Active::Value { value, frame, .. } => self.suspended_return_keeps_checked_types(aliases, supported, value, frame, after),
        }
    }

    #[verifier::spinoff_prover]
    proof fn suspended_expression_keeps_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, supported: bool, expr: ScalarExpression<'p, 'a>, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()),
            self.state_has_checked_positions(aliases, supported), self.active == Active::Expression(expr),
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.state_has_checked_positions(aliases, supported),
    {
        reveal(ScalarExecution::step_matches);
        let inner = choose|inner: ScalarExpressionStep<'p, 'a>| #[trigger] expr.expression_step_matches(Ok(inner))
            && next_expression_at(after.active, expr.result_type_model(), inner);
        expr.expression_step_tracks_saved_conditions(inner);
        if supported && inner is NeedsForm {
            self.supported_expression_starts_checked_lookup(aliases, expr, inner, after);
        }
        if let ScalarExpressionStep::Continue(child) = inner {
            if child.branches_model().len() > expr.branches_model().len() {
                enter_checked_if(supported, aliases, self.plan, self.rank, expr, child);
            } else {
                select_checked_if_branch(supported, aliases, self.plan, self.rank, expr, child);
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn suspended_lookup_keeps_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, supported: bool, parent: ScalarExpression<'p, 'a>, site: usize, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.state_has_checked_positions(aliases, supported),
            self.active == (Active::Lookup { parent, site }),
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.state_has_checked_positions(aliases, supported),
    {
        reveal(ScalarExecution::step_matches);
        if self.has_recorded_arithmetic_lookup() {
            self.suspended_arithmetic_lookup_keeps_checked_types(aliases, supported, parent, after);
            return;
        }
        if supported {
            self.checked_scalar_call_lookup_progress(aliases, Ok(ScalarExecutionSlice::Suspended(after)));
        }
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
        enters_with_checked_frame(supported, aliases, self.plan, self.rank, site, parent, edge, values, callee,
            args.ranks_model().1, self.waiting@, after);
    }

    #[verifier::spinoff_prover]
    proof fn suspended_arithmetic_lookup_keeps_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, supported: bool, parent: ScalarExpression<'p, 'a>, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()),
            self.state_has_checked_positions(aliases, supported),
            self.has_recorded_arithmetic_lookup(), self.active == (Active::Lookup { parent, site: 0 }),
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.state_has_checked_positions(aliases, supported),
    {
        reveal(ScalarExecution::step_matches);
        let frame = parent.frame_model();
        let body = frame.body_model();
        let position = parent.expression_model();
        let selected = self.plan.checked_named_target_at_rank(aliases, self.rank, body, position);
        let (site, ty) = match selected {
            CheckedNamedTarget::Arithmetic(site, ty) => (site, ty),
            _ => { assert(false); return; },
        };
        assert(arithmetic::entering_arithmetic(self.rank, parent, site, ty, self.waiting@, after));
        if supported {
            scalar_syntax_matches_call_arguments(body.source.text_model(), body.forms@, position.at,
                seq![site.arguments.0, site.arguments.1]);
        }
        parent.restored_cursor_positions_agree();
        let old = self.waiting@;
        let waits = after.waiting@;
        assert(checked_wait(supported, aliases, self.plan, waits.last()));
        assert(waits.take(old.len() as int) =~= old);
        assert(old.take(old.len() as int) =~= old);
        preserve_wait_prefix(supported, aliases, self.plan, old, waits, old.len() as int);
    }

    #[verifier::spinoff_prover]
    proof fn suspended_return_keeps_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, supported: bool, value: ScalarValue, frame: ScalarCallFrame<'p, 'a>, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.state_has_checked_positions(aliases, supported),
            self.active matches Active::Value { frame: scope, value: produced, .. } && scope == frame && produced == value,
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.state_has_checked_positions(aliases, supported),
    {
        reveal(ScalarExecution::step_matches);
        let stack = self.waiting@;
        let wait = stack.last();
        let kept = stack.drop_last();
        assert(stack.len() > 0 && stack[stack.len() - 1] == wait);
        assert(checked_wait(supported, aliases, self.plan, wait));
        assert(kept =~= stack.take(stack.len() - 1));
        assert(kept.take(kept.len() as int) =~= kept);
        preserve_wait_prefix(supported, aliases, self.plan, stack, kept, kept.len() as int);
        match wait {
            Waiting::Return { parent, rank, .. } => {
                let inner = choose|inner: ScalarExpressionStep<'p, 'a>|
                    #[trigger] parent.receive_matches(value, inner) && next_expression_at(after.active, parent.result_type_model(), inner);
                parent.received_value_resumes_branch(value, inner);
                if let ScalarExpressionStep::Continue(child) = inner {
                    select_checked_if_branch(supported, aliases, self.plan, rank, parent, child);
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
                enters_with_checked_frame(supported, aliases, self.plan, rank, site, parent, edge, values.push(value),
                    callee, to, kept, after);
            },
            Waiting::Arithmetic(pending) => {
                reveal(arithmetic::arithmetic_step_matches);
                if pending.left.is_none() {
                    assert(checked_wait(supported, aliases, self.plan, after.waiting@.last()));
                    assert(after.waiting@.take(kept.len() as int) =~= kept);
                    preserve_wait_prefix(supported, aliases, self.plan, kept, after.waiting@, kept.len() as int);
                } else {
                    let (result, parent, inner) = choose|result: crate::ncg2m::integers::IntegerValue,
                        parent: ScalarExpression<'p, 'a>, inner: ScalarExpressionStep<'p, 'a>|
                        #[trigger] parent.receive_matches(ScalarValue::Integer(result), inner)
                            && parent.frame_model() == pending.caller@ && parent.cursor_model() == pending.parent
                            && next_expression_at(after.active, parent.result_type_model(), inner);
                    parent.restored_cursor_positions_agree();
                    parent.received_value_resumes_branch(ScalarValue::Integer(result), inner);
                    if let ScalarExpressionStep::Continue(child) = inner {
                        select_checked_if_branch(supported, aliases, self.plan, pending.rank,
                            parent, child);
                    }
                }
            },
        }
    }

    #[verifier::spinoff_prover]
    proof fn supported_expression_starts_checked_lookup(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, expr: ScalarExpression<'p, 'a>,
        inner: ScalarExpressionStep<'p, 'a>, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()),
            self.active == Active::Expression(expr), self.state_has_checked_positions(aliases, true),
            inner is NeedsForm, expr.expression_step_matches(Ok(inner)),
            next_expression_at(after.active, expr.result_type_model(), inner),
            self.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.searches_checked_scalar_call(aliases) || after.has_recorded_arithmetic_lookup(),
    {
        reveal(ScalarExecution::step_matches);
        let frame = expr.frame_model();
        let body = frame.body_model();
        let position = expr.expression_model();
        let source = body.source.text_model();
        if scalar_atom_at(body.forms@, position.at) {
            self.plan.checked_atom_keeps_local_type(aliases, self.rank, body, position);
            expr.checked_atom_does_not_request_form(inner);
            assert(false);
        }
        if let Some((condition, yes, no)) = conditional_positions(source, body.forms@, position.at) {
            expr.an_if_starts_with_its_condition(condition, yes, no, Ok(inner));
            assert(false);
        }
        scalar_syntax_form_kind(source, body.forms@, position.at);
        self.plan.checked_site_has_the_rank_body(aliases, self.rank, body, position);
        self.plan.closed_scalar_fragment_matches_body(self.rank, body);
        self.plan.supported_call_is_body_expression(aliases, self.rank, body, position);
        let target = self.plan.checked_named_target_at_rank(aliases, self.rank, body, position);
        match target {
            CheckedNamedTarget::Declaration(_) => {
                assert(self.plan.scalar_site_has_declared_edge(self.rank, position.at));
                let candidate = self.plan.checked_call_site_at_rank(aliases, self.rank, body, position);
                assert(self.evaluates_indexed_scalar_call(aliases, candidate));
                self.checked_call_expression_starts_lookup(aliases, candidate, Ok(ScalarExecutionSlice::Suspended(after)));
            },
            CheckedNamedTarget::Arithmetic(_, _) => {
                expr.expression_step_tracks_saved_conditions(inner);
                let lookup = inner->NeedsForm_0;
                assert(expr.expression_model() == lookup.expression_model());
                assert(after.active == (Active::Lookup { parent: lookup, site: 0 }));
                assert(after.has_recorded_arithmetic_lookup());
            },
        }
    }

    /// 対応する順位から実際に開始した状態では、全継続について断片の条件が成り立つ。
    pub proof fn starting_execution_preserves_supported_fragment(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize, values: Seq<ScalarValue>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.plan_model().scalar_fragment_is_closed(rank),
            exists|frame: ScalarCallFrame<'p, 'a>| #[trigger] binding_at_rank_matches(self.plan_model(), rank, values, Ok(frame))
                && self.starts_with(self.plan_model(), rank, frame),
        ensures self.preserves_supported_fragment(aliases),
    {
        reveal(ScalarExecution::starts_with);
        let frame = choose|frame: ScalarCallFrame<'p, 'a>|
            #[trigger] binding_at_rank_matches(self.plan_model(), rank, values, Ok(frame))
                && self.starts_with(self.plan_model(), rank, frame);
        self.plan.scalar_body_site_is_checked(aliases, rank, frame.body_model());
        self.plan.closed_scalar_fragment_matches_body(rank, frame.body_model());
    }

    /// 対応する実行状態を進めると、未対応フォームの診断を返さない。
    pub proof fn supported_step_does_not_defer(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.preserves_supported_fragment(aliases),
            self.step_matches(result),
        ensures !(result matches Err(ScalarExecutionError::Deferred { .. })),
    {
        reveal(ScalarExecution::step_matches);
        if self.active is Lookup && !self.has_recorded_arithmetic_lookup() {
            self.checked_scalar_call_lookup_progress(aliases, result);
        } else if self.active is Value && self.waiting@.len() > 0 && self.waiting@.last() is Arithmetic {
            reveal(arithmetic::arithmetic_step_matches);
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
