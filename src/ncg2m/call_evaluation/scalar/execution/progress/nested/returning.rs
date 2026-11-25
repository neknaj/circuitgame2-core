//! 呼び出し先の値を受け取り、元の環境で式の評価を再開する。

use super::*;
use crate::ncg2m::call_evaluation::scalar::ScalarExpressionSite;

verus! {

spec fn last_condition_is_checked(
    plan: &DefnCallPlan, aliases: &MixedUseAliases, rank: usize, parent: ScalarExpression,
) -> bool {
    parent.branches_model().len() > 0 ==> {
        let branch = parent.branches_model().last();
        let (at, condition, yes, no) = branch.positions_model();
        let body = parent.frame_model().body_model();
        &&& plan.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite {
            at, expected: branch.expected_model(),
        })
        &&& conditional_positions(body.source.text_model(), body.forms@, at) == Some((condition, yes, no))
    }
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 現在の環境で、最後に保存した条件式の型判断が成り立つことを表す。
    pub closed spec fn saves_checked_condition(&self, aliases: &MixedUseAliases<'_, 'p, 'a>) -> bool {
        match self.active {
            Active::Expression(parent) | Active::Lookup { parent, .. } =>
                last_condition_is_checked(self.plan, aliases, self.rank, parent),
            Active::Value { .. } => false,
        }
    }

    pub(super) proof fn condition_entry_saves_checked_position(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, original: ScalarExpression<'p, 'a>,
    )
        requires self.active matches Active::Expression(child) && {
            let branch = child.branches_model().last();
            let body = original.frame_model().body_model();
            &&& child.branches_model().len() > 0
            &&& child.frame_model() == original.frame_model()
            &&& branch.positions_model().0 == original.expression_model().at
            &&& branch.expected_model() == original.expression_model().expected
            &&& conditional_positions(body.source.text_model(), body.forms@, original.expression_model().at)
                == Some((branch.positions_model().1, branch.positions_model().2, branch.positions_model().3))
            &&& self.plan.scalar_site_is_checked(aliases, self.rank, body, original.expression_model())
        },
        ensures self.saves_checked_condition(aliases),
    {}

    /// 呼び出し先の値を待つ元の式と、保留中の条件式に型判断があることを表す。
    pub closed spec fn returns_checked_call(&self, aliases: &MixedUseAliases<'_, 'p, 'a>) -> bool {
        &&& self.active is Value
        &&& self.waiting@.len() > 0
        &&& self.waiting@.last() matches Waiting::Return { parent, rank, .. }
            && self.plan.scalar_site_is_checked(aliases, rank, parent.frame_model().body_model(), parent.expression_model())
            && last_condition_is_checked(self.plan, aliases, rank, parent)
    }

    /// 呼び出し元の同じ環境で、受け取った値を返すか、選択した型検査済みの分岐に進むことを表す。
    pub closed spec fn restores_checked_caller(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, after: Self,
    ) -> bool {
        &&& self.returns_checked_call(aliases)
        &&& {
            let parent = self.waiting@.last()->Return_parent;
            let value = self.active->Value_value;
            &&& after.plan == self.plan && after.rank == self.waiting@.last()->Return_rank
            &&& after.waiting@ == self.waiting@.drop_last()
            &&& match after.active {
                Active::Value { frame, value: out, _ty } =>
                    parent.branches_model().len() == 0 && frame == parent.frame_model() && out == value
                        && _ty@ == parent.result_type_model() && scalar_fits(out, _ty@),
                Active::Expression(child) => {
                    let branch = parent.branches_model().last();
                    &&& parent.branches_model().len() > 0 && value is Bool
                    &&& child.frame_model() == parent.frame_model()
                    &&& child.branches_model() == parent.branches_model().drop_last()
                    &&& child.expression_model().at
                        == if value->Bool_0 { branch.positions_model().2 } else { branch.positions_model().3 }
                    &&& child.expression_model().expected == branch.expected_model()
                    &&& after.evaluates_checked_expression(aliases)
                },
                _ => false,
            }
        }
    }

    /// 呼び出し先が値を返したら、元の仮引数環境を復元し、その値を元の式に渡す。
    #[verifier::spinoff_prover]
    pub proof fn checked_return_resumes_caller(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires self.returns_checked_call(aliases), self.step_matches(result),
        ensures result matches Ok(ScalarExecutionSlice::Suspended(after)) && self.restores_checked_caller(aliases, after),
    {
        reveal(ScalarExecution::step_matches);
        let after = result->Ok_0->Suspended_0;
        let waits = self.waiting@;
        let wait = waits.last();
        let (parent, from, value) = (wait->Return_parent, wait->Return_rank, self.active->Value_value);
        let inner = choose|inner: ScalarExpressionStep<'p, 'a>| #[trigger] parent.receive_matches(value, inner)
            && next_expression_at(after.active, parent.result_type_model(), inner);
        parent.received_value_resumes_branch(value, inner);
        if parent.branches_model().len() > 0 {
            let branch = parent.branches_model().last();
            let (at, condition, yes, no) = branch.positions_model();
            let body = parent.frame_model().body_model();
            self.plan.scalar_condition_sites_are_checked(aliases, from, body,
                ScalarExpressionSite { at, expected: branch.expected_model() }, condition, yes, no);
        }
    }
}

}
