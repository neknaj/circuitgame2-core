//! 型検査を通ったアトムと条件式の評価を、元の部分式と仮引数環境に結び付ける。

use super::*;
use super::super::atom::{a_list_has_no_scalar_atom, typed_atom_yields_value};
use super::super::condition::{conditional_children_follow_parent, conditional_match_has_positions};
use crate::ncg2m::expression_types::{
    conditional_positions, local_scalar_fragment, local_scalar_site_is_typed, scalar_atom_at, scalar_conditional_child_types,
};

verus! {

impl<'p, 'a> ScalarCallFrame<'p, 'a> {
    /// この環境の元の構文木上で、指定した局所スカラー式が型検査を通ることを表す。
    pub open spec fn has_locally_checked_site(&self, site: ScalarExpressionSite<'a>) -> bool {
        let body = self.body_model();
        let source = body.source.text_model();
        &&& !self.has_fold_bindings()
        &&& local_scalar_fragment(source, body.forms@, site.at)
        &&& local_scalar_site_is_typed(source, body.forms@, body.signature.parameters@, site.at, site.expected)
    }
}

proof fn checked_conditional_children(
    frame: ScalarCallFrame, site: ScalarExpressionSite, branch: ScalarCondition,
)
    requires frame.has_locally_checked_site(site), scalar_condition_matches(frame.body_model(), site, Some(branch)),
    ensures
        branch.positions_model().0 == site.at, branch.expected_model() == site.expected,
        branch_in_bounds(branch, frame.body_model().forms@.len()),
        frame.has_locally_checked_site(ScalarExpressionSite { at: branch.positions_model().1, expected: boolean_type() }),
        frame.has_locally_checked_site(ScalarExpressionSite { at: branch.positions_model().2, expected: site.expected }),
        frame.has_locally_checked_site(ScalarExpressionSite { at: branch.positions_model().3, expected: site.expected }),
{
    reveal(local_scalar_fragment);
    let body = frame.body_model();
    let source = body.source.text_model();
    let (_, condition, yes, no) = branch.positions_model();
    conditional_match_has_positions(body, site, Some(branch));
    conditional_children_follow_parent(body, site, branch);
    assert(!scalar_atom_at(body.forms@, site.at));
    scalar_conditional_child_types(source, body.forms@, body.signature.parameters@, site.at, site.expected, condition, yes, no);
}

impl<'p, 'a> ScalarExpression<'p, 'a> {
    pub(in crate::ncg2m::call_evaluation::scalar) proof fn declared_call_requests_lookup(
        &self, result: Result<ScalarExpressionStep<'p, 'a>, ScalarLiteralError<'p, 'a>>,
    )
        requires self.expression_step_matches(result), {
            let body = self.frame_model().body_model();
            let site = self.expression_model();
            &&& site.at < body.forms@.len() && body.forms@[site.at as int] is List
            &&& conditional_positions(body.source.text_model(), body.forms@, site.at).is_none()
        },
        ensures result matches Ok(ScalarExpressionStep::NeedsForm(next)) && expression_positions_agree(*self, next),
    {
        reveal(ScalarExpression::expression_step_matches);
        let frame = self.frame_model();
        let body = frame.body_model();
        let site = self.expression_model();
        if let Ok(ScalarExpressionStep::Continue(next)) = result {
            if self.condition_entry_matches(next) {
                conditional_match_has_positions(body, site, Some(next.branches_model().last()));
                assert(false);
            }
        }
        let atom = choose|atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>|
            #[trigger] scalar_atom_matches(&frame, site.at, site.expected, atom)
                && self.atom_transition_matches(atom, result);
        a_list_has_no_scalar_atom(&frame, site.at, site.expected, atom);
    }

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn an_if_starts_with_its_condition(
        &self, condition: usize, yes: usize, no: usize,
        result: Result<ScalarExpressionStep<'p, 'a>, ScalarLiteralError<'p, 'a>>,
    )
        requires self.expression_step_matches(result), {
            let body = self.frame_model().body_model();
            conditional_positions(body.source.text_model(), body.forms@, self.expression_model().at)
                == Some((condition, yes, no))
        },
        ensures result matches Ok(ScalarExpressionStep::Continue(next))
            && next.frame_model() == self.frame_model()
            && next.branches_model().len() == self.branches_model().len() + 1
            && next.branches_model().last().positions_model() == (self.expression_model().at, condition, yes, no)
            && next.branches_model().last().expected_model() == self.expression_model().expected
            && next.expression_model() == (ScalarExpressionSite {
                at: condition, expected: DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 },
            }),
    {
        reveal(ScalarExpression::expression_step_matches);
        let body = self.frame_model().body_model();
        let site = self.expression_model();
        if scalar_condition_matches(body, site, None) {
            conditional_match_has_positions(body, site, None);
            assert(false);
        }
        let next = result->Ok_0->Continue_0;
        let branch = next.branches_model().last();
        conditional_match_has_positions(body, site, Some(branch));
        conditional_children_follow_parent(body, site, branch);
    }

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn restored_cursor_positions_agree(&self)
        ensures self.expression_model() == self.cursor_model().position_model(),
            self.branches_model() == self.cursor_model().branches_model(),
    {}

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn received_value_resumes_branch(
        &self, value: ScalarValue, step: ScalarExpressionStep<'p, 'a>,
    )
        requires self.receive_matches(value, step),
        ensures
            if self.branches_model().len() == 0 {
                step matches ScalarExpressionStep::Complete { value: out, frame }
                    && out == value && frame == self.frame_model()
            } else {
                let branch = self.branches_model().last();
                &&& value is Bool
                &&& step matches ScalarExpressionStep::Continue(after)
                    && after.frame_model() == self.frame_model()
                    && after.branches_model() == self.branches_model().drop_last()
                    && after.expression_model().expected == branch.expected_model()
                    && after.expression_model().at ==
                        if value->Bool_0 { branch.positions_model().2 } else { branch.positions_model().3 }
            },
    {}

    // 待機中の条件が増える場合と、条件の値を受け取って分岐に進む場合を区別する。
    #[verifier::spinoff_prover]
    pub(in crate::ncg2m::call_evaluation::scalar) proof fn expression_step_tracks_saved_conditions(
        &self, step: ScalarExpressionStep<'p, 'a>,
    )
        requires self.expression_step_matches(Ok(step)),
        ensures match step {
            ScalarExpressionStep::Continue(after) => {
                let before = self.branches_model();
                let next = after.branches_model();
                let body = self.frame_model().body_model();
                &&& after.frame_model() == self.frame_model()
                &&& if next.len() > before.len() {
                    let branch = next.last();
                    &&& next == before.push(branch)
                    &&& after.expression_model().at == branch.positions_model().1
                    &&& after.expression_model().expected == (DataType {
                        atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0,
                    })
                    &&& branch.positions_model().0 == self.expression_model().at
                    &&& branch.expected_model() == self.expression_model().expected
                    &&& conditional_positions(body.source.text_model(), body.forms@, self.expression_model().at)
                        == Some((branch.positions_model().1, branch.positions_model().2, branch.positions_model().3))
                } else {
                    let branch = before.last();
                    &&& before.len() > 0 && next == before.drop_last()
                    &&& after.expression_model().expected == branch.expected_model()
                    &&& (after.expression_model().at == branch.positions_model().2
                        || after.expression_model().at == branch.positions_model().3)
                }
            },
            ScalarExpressionStep::NeedsForm(after) => expression_positions_agree(*self, after),
            ScalarExpressionStep::Complete { .. } => true,
        },
    {
        reveal(ScalarExpression::expression_step_matches);
        let frame = self.frame_model();
        let site = self.expression_model();
        if let ScalarExpressionStep::Continue(after) = step {
            if self.condition_entry_matches(after) {
                let before = self.branches_model();
                let next = after.branches_model();
                let branch = next.last();
                conditional_match_has_positions(frame.body_model(), site, Some(branch));
                conditional_children_follow_parent(frame.body_model(), site, branch);
                assert(next =~= before.push(branch));
                return;
            }
        }
        let atom = choose|atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>|
            #[trigger] scalar_atom_matches(&frame, site.at, site.expected, atom)
            && self.atom_transition_matches(atom, Ok(step));
        match atom {
            Ok(Some(value)) => self.received_value_resumes_branch(value, step),
            _ => {},
        }
    }

    pub(in crate::ncg2m::call_evaluation::scalar) proof fn checked_atom_does_not_request_form(
        &self, step: ScalarExpressionStep<'p, 'a>,
    )
        requires
            self.expression_step_matches(Ok(step)),
            ({
                let frame = self.frame_model();
                let body = frame.body_model();
                let site = self.expression_model();
                &&& !frame.has_fold_bindings()
                &&& scalar_atom_at(body.forms@, site.at)
                &&& local_scalar_site_is_typed(body.source.text_model(), body.forms@, body.signature.parameters@,
                    site.at, site.expected)
                &&& parameters_match(body.signature, frame.parameter_values_model())
            }),
        ensures !(step is NeedsForm),
    {
        if step is NeedsForm {
            reveal(ScalarExpression::expression_step_matches);
            let frame = self.frame_model();
            let site = self.expression_model();
            let atom = choose|atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>|
                #[trigger] scalar_atom_matches(&frame, site.at, site.expected, atom) && self.atom_transition_matches(atom, Ok(step));
            typed_atom_yields_value(&frame, site.at, site.expected, atom);
            self.received_value_resumes_branch(atom->Ok_0->Some_0, step);
        }
    }

    /// 評価中の式と保留中の条件式が、同じ仮引数環境で型検査を通った局所スカラー式であることを表す。
    pub closed spec fn is_locally_checked(&self) -> bool {
        let frame = self.frame_model();
        let branches = self.branches_model();
        &&& self.positions_fit()
        &&& parameters_match(frame.body_model().signature, frame.parameter_values_model())
        &&& frame.has_locally_checked_site(self.expression_model())
        &&& forall|i: int| 0 <= i < branches.len() ==> {
            let branch = #[trigger] branches[i];
            frame.has_locally_checked_site(ScalarExpressionSite { at: branch.positions_model().0, expected: branch.expected_model() })
        }
    }

    pub(super) proof fn starts_at_locally_checked_site(&self)
        requires
            self.positions_fit(), self.branches_model().len() == 0,
            self.frame_model().has_locally_checked_site(self.expression_model()),
            parameters_match(self.frame_model().body_model().signature, self.frame_model().parameter_values_model()),
        ensures self.is_locally_checked(),
    {}

    /// 型検査を通ったアトムと条件式は、値を返すか、同じ環境で型検査済みの部分式に進む。
    #[verifier::spinoff_prover]
    pub proof fn locally_checked_step_progress(
        &self, result: Result<ScalarExpressionStep<'p, 'a>, ScalarLiteralError<'p, 'a>>,
    )
        requires self.is_locally_checked(), self.expression_step_matches(result),
        ensures match result {
            Ok(ScalarExpressionStep::Continue(after)) =>
                after.is_locally_checked() && after.frame_model() == self.frame_model(),
            Ok(ScalarExpressionStep::Complete { value, frame }) =>
                scalar_fits(value, self.result_type_model()) && frame == self.frame_model(),
            _ => false,
        },
    {
        reveal(ScalarExpression::expression_step_matches);
        let frame = self.frame_model();
        let site = self.expression_model();
        if let Ok(ScalarExpressionStep::Continue(after)) = result {
            if self.condition_entry_matches(after) {
                self.locally_checked_enters_condition(after);
                return;
            }
        }
        let body = frame.body_model();
        conditional_match_has_positions(body, site, None);
        reveal(local_scalar_fragment);
        assert(scalar_atom_at(body.forms@, site.at));
        let atom = choose|atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>|
            #[trigger] scalar_atom_matches(&frame, site.at, site.expected, atom)
                && self.atom_transition_matches(atom, result);
        typed_atom_yields_value(&frame, site.at, site.expected, atom);
        let value = atom->Ok_0->Some_0;
        self.locally_checked_receives_value(value, result->Ok_0);
    }

    proof fn locally_checked_enters_condition(&self, after: Self)
        requires self.is_locally_checked(), self.condition_entry_matches(after),
        ensures after.is_locally_checked(),
    {
        let frame = self.frame_model();
        let branches = after.branches_model();
        let branch = branches.last();
        let site = self.expression_model();
        checked_conditional_children(frame, site, branch);
        let before = self.branches_model();
        assert(branches.len() == before.len() + 1);
        assert(branches[before.len() as int] == branch);
        let body = frame.body_model();
        assert(after.expression_model().at < body.forms@.len());
        assert(after.expression_model().expected == boolean_type());
        assert(after.cursor.origin@ == frame);
        assert forall|i: int| 0 <= i < branches.len() implies {
            let saved = #[trigger] branches[i];
            &&& branch_in_bounds(saved, body.forms@.len())
            &&& scalar_condition_matches(body, ScalarExpressionSite {
                at: saved.positions_model().0, expected: saved.expected_model(),
            }, Some(saved))
            &&& saved.expected_model() == if i == 0 { after.result_type_model() } else { boolean_type() }
        } by {
            if i < before.len() { assert(branches[i] == before[i]); }
            else {
                assert(branches[i] == branch);
                assert(i == before.len());
            }
        };
        assert(after.positions_fit());
        assert forall|i: int| 0 <= i < branches.len() implies {
            let saved = #[trigger] branches[i];
            frame.has_locally_checked_site(ScalarExpressionSite { at: saved.positions_model().0, expected: saved.expected_model() })
        } by {
            if i < before.len() { assert(branches[i] == before[i]); }
            else { assert(branches[i] == branch); }
        };
    }

    proof fn locally_checked_receives_value(&self, value: ScalarValue, result: ScalarExpressionStep<'p, 'a>)
        requires self.is_locally_checked(), scalar_fits(value, self.expression_model().expected), self.receive_matches(value, result),
        ensures match result {
            ScalarExpressionStep::Continue(after) => after.is_locally_checked() && after.frame_model() == self.frame_model(),
            ScalarExpressionStep::Complete { value, frame } => scalar_fits(value, self.result_type_model()) && frame == self.frame_model(),
            _ => false,
        },
    {
        let frame = self.frame_model();
        let before = self.branches_model();
        if before.len() > 0 {
            let branch = before.last();
            let site = ScalarExpressionSite { at: branch.positions_model().0, expected: branch.expected_model() };
            assert(scalar_condition_matches(frame.body_model(), site, Some(branch)));
            checked_conditional_children(frame, site, branch);
            let after = result->Continue_0;
            let saved = after.branches_model();
            assert forall|i: int| 0 <= i < saved.len() implies {
                let pending = #[trigger] saved[i];
                frame.has_locally_checked_site(ScalarExpressionSite { at: pending.positions_model().0, expected: pending.expected_model() })
            } by {
                assert(saved[i] == before[i]);
            };
        }
    }
}

}
