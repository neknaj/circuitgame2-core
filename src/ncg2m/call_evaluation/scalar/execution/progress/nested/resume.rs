//! 引数の値を受け取り、元の型判断に従って呼び出しを進める。

use super::*;

verus! {

pub(super) open spec fn checked_argument_edge(
    aliases: &MixedUseAliases, plan: &DefnCallPlan, wait: Waiting, site: usize,
) -> bool {
    wait matches Waiting::Argument { parent, caller, rank, pending } && {
        let (edge, _, callee) = pending.model();
        let body = caller@.body_model();
        let position = parent.position_model();
        let order = plan.order_model();
        &&& plan.scalar_site_is_checked(aliases, rank, body, position)
        &&& scalar_type_agrees(position.expected, callee.signature.result_type.ty)
        &&& plan.calls_model_at_rank(rank) matches Some(row)
            && site < row.len() && row[site as int] == edge && edge.at == position.at
        &&& order.contains(edge.to) && order.index_of(edge.to) == pending.ranks_model().1
        &&& plan.body_matches_at_rank(pending.ranks_model().1, callee)
    }
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 最後に積んだ引数継続が、元の式の型判断と対応する辺を保持することを表す。
    pub closed spec fn latest_argument_is_checked(&self, aliases: &MixedUseAliases<'_, 'p, 'a>) -> bool {
        self.waiting@.len() > 0 && self.waiting@.last() is Argument ==>
            exists|site: usize| #[trigger] checked_argument_edge(aliases, self.plan, self.waiting@.last(), site)
    }

    pub(super) proof fn latest_argument_keeps_call_site(&self, aliases: &MixedUseAliases<'_, 'p, 'a>, site: usize)
        requires checked_argument_edge(aliases, self.plan, self.waiting@.last(), site),
        ensures self.latest_argument_is_checked(aliases),
    {
        assert(exists|i: usize| #[trigger] checked_argument_edge(aliases, self.plan, self.waiting@.last(), i));
    }

    pub(super) proof fn latest_continuation_waits_for_return(&self, aliases: &MixedUseAliases<'_, 'p, 'a>)
        requires self.waiting@.last() is Return,
        ensures self.latest_argument_is_checked(aliases),
    {}

    /// 評価済みの値を、型検査済みの呼び出しの引数として受け取る状態を表す。
    pub closed spec fn returns_checked_argument(&self, aliases: &MixedUseAliases<'_, 'p, 'a>) -> bool {
        &&& self.active is Value
        &&& self.waiting@.len() > 0 && self.waiting@.last() is Argument
        &&& self.latest_argument_is_checked(aliases)
    }

    /// 引数の値を受け取ると、同じ環境で次の引数を評価するか、呼び出し先の本体に進む。
    #[verifier::spinoff_prover]
    pub proof fn checked_argument_resumes_call(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.returns_checked_argument(aliases),
            self.step_matches(result),
        ensures result matches Ok(ScalarExecutionSlice::Suspended(after))
            && after.evaluates_checked_expression(aliases) && after.latest_argument_is_checked(aliases),
    {
        reveal(ScalarExecution::step_matches);
        let waits = self.waiting@;
        let wait = waits.last();
        let (cursor, caller, rank, pending) = match wait {
            Waiting::Argument { parent, caller, rank, pending } => (parent, caller, rank, pending),
            _ => { assert(false); return; },
        };
        let (frame, value) = match self.active {
            Active::Value { frame, value, .. } => (frame, value),
            _ => { assert(false); return; },
        };
        let after = match result {
            Ok(ScalarExecutionSlice::Suspended(after)) => after,
            _ => { assert(false); return; },
        };
        let (edge, values, callee) = pending.model();
        let to = pending.ranks_model().1;
        let expr = choose|expr: ScalarExpression<'p, 'a>| #[trigger] expr.cursor_model() == cursor
            && expr.frame_model() == frame
            && entering_call(rank, expr, edge, values.push(value), callee, to, waits.drop_last(), after);
        assert(frame == caller@);
        let site = choose|i: usize| #[trigger] checked_argument_edge(aliases, self.plan, wait, i);
        expr.restored_cursor_positions_agree();
        if values.len() + 1 < edge.arguments@.len() {
            assert(site < self.plan.calls_model_at_rank(rank)->Some_0.len());
            self.plan.scalar_call_arguments_are_checked(aliases, rank, frame.body_model(), cursor.position_model(),
                site, callee);
            assert(self.plan.calls_model_at_rank(rank)->Some_0[site as int].arguments@[values.len() as int + 1]
                == edge.arguments@[values.len() as int + 1]);
            after.latest_argument_keeps_call_site(aliases, site);
        } else {
            self.plan.scalar_body_site_is_checked(aliases, to, callee);
            after.latest_continuation_waits_for_return(aliases);
        }
    }
}

}
