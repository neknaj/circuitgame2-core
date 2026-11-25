//! 対応する断片の呼び出しを、実行枠における探索と部分式評価に結び付ける。

use super::*;
use crate::ncg2m::expression_types::{
    scalar_atom_at, scalar_evaluator_syntax, scalar_syntax_form_kind, scalar_syntax_matches_call_arguments,
};

verus! {

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 評価または呼び出しの探索を行う式が対応範囲にあり、呼び出し先の本体まで断片が閉じていることを表す。
    pub closed spec fn evaluates_supported_subexpression(&self) -> bool {
        match self.active {
            Active::Expression(expr) | Active::Lookup { parent: expr, .. } => {
                let body = expr.frame_model().body_model();
                let position = expr.expression_model();
                &&& self.plan.scalar_fragment_is_closed(self.rank)
                &&& self.plan.scalar_fragment_value_type(position.expected)
                &&& scalar_evaluator_syntax(body.source.text_model(), body.forms@, position.at)
            },
            Active::Value { .. } => false,
        }
    }

    /// 対応する順位から開始した評価は、元の本体の対応する式から始まる。
    pub proof fn starts_with_supported_scalar_body(&self, rank: usize, frame: ScalarCallFrame<'p, 'a>)
        requires
            self.starts_with(self.plan_model(), rank, frame),
            self.plan_model().body_matches_at_rank(rank, frame.body_model()),
            self.plan_model().scalar_fragment_is_closed(rank),
        ensures self.evaluates_supported_subexpression(),
    {
        reveal(ScalarExecution::starts_with);
        self.plan.closed_scalar_fragment_matches_body(rank, frame.body_model());
    }

    /// 対応する本体直下の宣言呼び出しは、一つの実行枠で同じ断片内の探索へ進む。
    pub proof fn supported_root_call_slice(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize, frame: ScalarCallFrame<'p, 'a>,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()),
            self.starts_with(self.plan_model(), rank, frame),
            self.plan_model().body_matches_at_rank(rank, frame.body_model()),
            self.plan_model().scalar_fragment_is_closed(rank),
            scalar_call_syntax_at(frame.body_model().source.text_model(), frame.body_model().forms@, frame.body_model().at),
            scalar_execution_slice_matches(*self, 1, result),
        ensures result matches Ok(ScalarExecutionSlice::Suspended(after))
            && after.searches_checked_scalar_call(aliases) && after.evaluates_supported_subexpression(),
    {
        self.starts_with_supported_scalar_body(rank, frame);
        self.plan.closed_scalar_fragment_matches_body(rank, frame.body_model());
        self.one_step_slice_matches(result);
        self.checked_root_call_starts_lookup(aliases, rank, frame, result);
        reveal(ScalarExecution::starts_with);
        reveal(ScalarExecution::step_matches);
        let expr = self.active->Expression_0;
        let after = result->Ok_0->Suspended_0;
        let inner = choose|inner: ScalarExpressionStep<'p, 'a>| #[trigger] expr.expression_step_matches(Ok(inner))
            && next_expression_at(after.active, expr.result_type_model(), inner);
        expr.expression_step_tracks_saved_conditions(inner);
    }

    /// 対応する型付き呼び出しの探索は、一つの実行枠で探索を続けるか対応する部分式へ進む。
    #[verifier::spinoff_prover]
    pub proof fn supported_scalar_lookup_slice(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()),
            self.searches_checked_scalar_call(aliases), self.evaluates_supported_subexpression(),
            scalar_execution_slice_matches(*self, 1, result),
        ensures result matches Ok(ScalarExecutionSlice::Suspended(after))
            && (after.searches_checked_scalar_call(aliases) || after.evaluates_checked_expression(aliases))
            && after.evaluates_supported_subexpression(),
    {
        self.one_step_slice_matches(result);
        self.checked_scalar_call_lookup_progress(aliases, result);
        reveal(ScalarExecution::step_matches);
        reveal(ScalarExecution::searches_checked_scalar_call);
        let after = result->Ok_0->Suspended_0;
        let parent = self.active->Lookup_parent;
        let site = self.active->Lookup_site;
        let position = parent.expression_model();
        let body = parent.frame_model().body_model();
        let row = self.plan.calls_model_at_rank(self.rank)->Some_0;
        let found = choose|found: int| site <= found < row.len() && (#[trigger] row[found]).at == position.at;
        assert(site <= found < row.len());
        if row[site as int].at != position.at { return; }
        let args = choose|args: ScalarArguments<'plan, 'p, 'a>|
            #[trigger] prepared_arguments_match(self.plan, self.rank, site, Some(args))
            && args.model().0.at == position.at
            && scalar_type_agrees(position.expected, args.model().2.signature.result_type.ty)
            && entering_call(self.rank, parent, args.model().0, args.model().1, args.model().2,
                args.ranks_model().1, self.waiting@, after);
        let (edge, _, target) = args.model();
        let (to, _) = self.plan.closed_scalar_fragment_callee(self.rank, site);
        self.plan.closed_scalar_fragment_matches_body(to, target);
        if edge.arguments@.len() == 0 {
            assert(after.rank == to);
        } else {
            self.plan.checked_site_has_the_rank_body(aliases, self.rank, body, position);
            let at = defn_call_plan_site_at_rank(aliases, self.plan, self.rank, site);
            let from = self.plan.order_model()[self.rank as int];
            assert(at == position.at);
            assert(self.plan.project_model().functional_forms_model(from.file) == Some(body.forms@));
            assert(body.forms@[at as int] is List);
            assert(conditional_positions(body.source.text_model(), body.forms@, at).is_none());
            scalar_syntax_form_kind(body.source.text_model(), body.forms@, position.at);
            assert(!scalar_atom_at(body.forms@, position.at));
            scalar_syntax_matches_call_arguments(body.source.text_model(), body.forms@, position.at, edge.arguments@);
            assert(scalar_evaluator_syntax(body.source.text_model(), body.forms@, edge.arguments@[0]));
        }
    }
}

}
