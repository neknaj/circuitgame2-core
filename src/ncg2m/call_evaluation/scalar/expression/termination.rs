//! 条件付きの評価を続けると、条件と分岐に残った仕事が減ることを示す。

use super::*;
use super::super::condition::conditional_children_follow_parent;
use super::super::termination::{
    expression_work, expression_work_dominates, expression_work_positive, scalar_expression_order, scalar_subexpression_order,
};

verus! {

spec fn branch_work(rank: usize, branch: ScalarCondition) -> nat {
    let (_, _, yes, no) = branch.positions_model();
    expression_work(scalar_expression_order(rank, yes)) + expression_work(scalar_expression_order(rank, no))
}

#[verifier::opaque]
spec fn saved_branches_work(rank: usize, branches: Seq<ScalarCondition>) -> nat
    decreases branches.len(),
{
    if branches.len() == 0 {
        0
    } else {
        branch_work(rank, branches.last()) + saved_branches_work(rank, branches.drop_last())
    }
}

impl<'p, 'a> ScalarCursor<'p, 'a> {
    pub(in crate::ncg2m::call_evaluation::scalar) closed spec fn saved_work_model(&self, rank: usize) -> nat {
        saved_branches_work(rank, self.branches_model())
    }
}

impl<'p, 'a> ScalarExpression<'p, 'a> {
    /// 現在の式と、条件の結果を待つ分岐に残った評価の仕事量を表す。
    pub closed spec fn expression_work_model(&self, rank: usize) -> nat {
        expression_work(scalar_expression_order(rank, self.expression_model().at))
            + saved_branches_work(rank, self.branches_model())
    }

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn expression_work_parts(&self, rank: usize)
        ensures self.expression_work_model(rank) == expression_work(scalar_expression_order(rank, self.expression_model().at))
            + self.cursor_model().saved_work_model(rank),
    {}

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn empty_branch_stack_has_no_work(&self, rank: usize)
        requires self.branches_model().len() == 0,
        ensures self.expression_work_model(rank) == expression_work(scalar_expression_order(rank, self.expression_model().at)),
    {
        reveal(saved_branches_work);
    }

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn received_expression_uses_saved_work(
        &self, rank: usize, value: ScalarValue, after: Self,
    )
        requires self.receive_matches(value, ScalarExpressionStep::Continue(after)),
        ensures after.expression_work_model(rank) <= self.cursor_model().saved_work_model(rank),
    {
        reveal(ScalarExpression::receive_matches);
        reveal(saved_branches_work);
    }

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn receiving_a_value_resolves_expression(
        &self, value: ScalarValue, step: ScalarExpressionStep,
    )
        requires self.receive_matches(value, step),
        ensures !(step is NeedsForm),
    {
        reveal(ScalarExpression::receive_matches);
    }

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn expression_has_work(&self, rank: usize)
        ensures self.expression_work_model(rank) > 0,
    {
        expression_work_positive(scalar_expression_order(rank, self.expression_model().at));
    }

    #[verifier::spinoff_prover]
    pub(in crate::ncg2m::call_evaluation::scalar) proof fn expression_continuation_reduces_work(&self, rank: usize, after: Self)
        requires self.expression_step_matches(Ok(ScalarExpressionStep::Continue(after))),
        ensures after.expression_work_model(rank) < self.expression_work_model(rank),
    {
        reveal(ScalarExpression::expression_step_matches);
        let site = self.expression_model();
        let current = scalar_expression_order(rank, site.at);
        let before = self.branches_model();
        let pending = after.branches_model();
        if self.condition_entry_matches(after) {
            let branch = pending.last();
            let (_, condition, yes, no) = branch.positions_model();
            conditional_children_follow_parent(self.frame_model().body_model(), site, branch);
            scalar_subexpression_order(rank, site.at, rank, condition);
            scalar_subexpression_order(rank, site.at, rank, yes);
            scalar_subexpression_order(rank, site.at, rank, no);
            expression_work_dominates(current, scalar_expression_order(rank, condition));
            expression_work_dominates(current, scalar_expression_order(rank, yes));
            expression_work_dominates(current, scalar_expression_order(rank, no));
            expression_work_positive(current);
            assert(pending.drop_last() =~= before);
            reveal(saved_branches_work);
        } else {
            let frame = self.frame_model();
            let next = Ok(ScalarExpressionStep::Continue(after));
            let atom = choose|atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>|
                #[trigger] scalar_atom_matches(&frame, site.at, site.expected, atom)
                    && self.atom_transition_matches(atom, next);
            assert(atom matches Ok(Some(_)));
            let value = atom->Ok_0->Some_0;
            self.received_value_reduces_work(rank, value, after);
        }
    }

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn deferred_expression_preserves_work(
        &self, rank: usize, after: Self,
    )
        requires self.expression_step_matches(Ok(ScalarExpressionStep::NeedsForm(after))),
        ensures after.expression_work_model(rank) == self.expression_work_model(rank),
    {
        reveal(ScalarExpression::expression_step_matches);
        reveal(ScalarExpression::receive_matches);
        let frame = self.frame_model();
        let site = self.expression_model();
        let next = Ok(ScalarExpressionStep::NeedsForm(after));
        let atom = choose|atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>|
            #[trigger] scalar_atom_matches(&frame, site.at, site.expected, atom)
                && self.atom_transition_matches(atom, next);
        assert(atom == Ok(None));
    }

    proof fn received_value_reduces_work(&self, rank: usize, value: ScalarValue, after: Self)
        requires self.receive_matches(value, ScalarExpressionStep::Continue(after)),
        ensures after.expression_work_model(rank) < self.expression_work_model(rank),
    {
        reveal(ScalarExpression::receive_matches);
        reveal(saved_branches_work);
        expression_work_positive(scalar_expression_order(rank, self.expression_model().at));
    }
}

}
