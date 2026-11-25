//! 呼び出しの探索から、同じ型検査を根拠に引数や呼び出し先の本体へ進む。

use super::*;
use crate::ncg2m::expression_types::conditional_positions;

mod resume;
mod returning;
mod stack;

verus! {

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 評価中の式が元の仮引数環境と期待型で検査を通ったことを表す。
    pub closed spec fn evaluates_checked_expression(&self, aliases: &MixedUseAliases<'_, 'p, 'a>) -> bool {
        self.active matches Active::Expression(expr)
            && self.plan.scalar_site_is_checked(aliases, self.rank, expr.frame_model().body_model(), expr.expression_model())
    }

    /// 型検査を通ったスカラー呼び出しの辺が、探索位置以降にあることを表す。
    pub closed spec fn searches_checked_scalar_call(&self, aliases: &MixedUseAliases<'_, 'p, 'a>) -> bool {
        self.active matches Active::Lookup { parent, site } && {
            let body = parent.frame_model().body_model();
            let position = parent.expression_model();
            &&& self.plan.scalar_site_is_checked(aliases, self.rank, body, position)
            &&& position.expected.list_depth == 0
            &&& (position.expected.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
            &&& self.plan.calls_model_at_rank(self.rank) matches Some(row)
                && exists|found: int| site <= found < row.len() && (#[trigger] row[found]).at == position.at
        }
    }

    /// 評価中のスカラー式に指定した呼び出しの辺が対応することを表す。
    pub closed spec fn evaluates_indexed_scalar_call(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, candidate: usize,
    ) -> bool {
        &&& self.evaluates_checked_expression(aliases)
        &&& self.active matches Active::Expression(expr) && {
            let position = expr.expression_model();
            &&& position.expected.list_depth == 0
            &&& (position.expected.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
            &&& self.plan.calls_model_at_rank(self.rank) matches Some(row) && candidate < row.len()
                && row[candidate as int].at == position.at
        }
    }

    /// 型検査済みの式に対応する宣言呼び出しの探索を、同じ仮引数環境で始める。
    pub proof fn checked_call_expression_starts_lookup(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, candidate: usize,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.evaluates_indexed_scalar_call(aliases, candidate),
            self.step_matches(result),
        ensures result matches Ok(ScalarExecutionSlice::Suspended(after))
            && after.searches_checked_scalar_call(aliases),
    {
        let expr = self.active->Expression_0;
        self.plan.checked_site_has_the_rank_body(aliases, self.rank, expr.frame_model().body_model(), expr.expression_model());
        self.expression_dispatches_to_indexed_call(aliases, candidate, result);
        let row = self.plan.calls_model_at_rank(self.rank)->Some_0;
        assert(exists|found: int| 0 <= found < row.len() && (#[trigger] row[found]).at == expr.expression_model().at);
    }

    /// 本体直下の呼び出しの探索状態から、その位置を本体の戻り型で検査したことを示す。
    pub proof fn scalar_root_search_is_checked(&self, aliases: &MixedUseAliases<'_, 'p, 'a>)
        requires defn_call_plan_matches(aliases, self.plan_model()), self.searches_scalar_root_call(),
        ensures self.searches_checked_scalar_call(aliases),
    {
        reveal(ScalarExecution::searches_scalar_root_call);
        let parent = self.active->Lookup_parent;
        self.plan.scalar_body_site_is_checked(aliases, self.rank, parent.frame_model().body_model());
    }

    /// 型検査済みの呼び出しを探し、辺が見つかったら型検査済みの式の評価へ進む。
    #[verifier::spinoff_prover]
    pub proof fn checked_scalar_call_lookup_progress(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.searches_checked_scalar_call(aliases),
            self.step_matches(result),
        ensures result matches Ok(ScalarExecutionSlice::Suspended(after))
            && (after.searches_checked_scalar_call(aliases)
                || (after.evaluates_checked_expression(aliases) && after.latest_argument_is_checked(aliases))),
    {
        reveal(ScalarExecution::step_matches);
        let site = self.active->Lookup_site;
        let parent = self.active->Lookup_parent;
        let body = parent.frame_model().body_model();
        let position = parent.expression_model();
        let row = self.plan.calls_model_at_rank(self.rank)->Some_0;
        let found = choose|found: int| site <= found < row.len() && (#[trigger] row[found]).at == position.at;
        let edge = row[site as int];
        if edge.at != position.at {
            assert(site + 1 <= found);
        } else {
            match result {
                Ok(ScalarExecutionSlice::Suspended(after)) => {
                    let args = choose|args: ScalarArguments<'plan, 'p, 'a>|
                        #[trigger] prepared_arguments_match(self.plan, self.rank, site, Some(args))
                        && args.model().0.at == position.at
                        && scalar_type_agrees(position.expected, args.model().2.signature.result_type.ty)
                        && entering_call(self.rank, parent, args.model().0, args.model().1, args.model().2,
                            args.ranks_model().1, self.waiting@, after);
                    self.selected_call_enters_checked_expression(aliases, args, after);
                },
                Err(_) => {
                    let args = choose|args: Option<ScalarArguments<'plan, 'p, 'a>>|
                        #[trigger] prepared_arguments_match(self.plan, self.rank, site, args)
                            && match args {
                                None => true,
                                Some(call) => !scalar_type_agrees(position.expected, call.model().2.signature.result_type.ty),
                            };
                    assert(args.is_some());
                    self.plan.scalar_call_arguments_are_checked(aliases, self.rank, body, position, site, args->Some_0.model().2);
                    assert(false);
                },
                _ => { assert(false); },
            }
        }
    }

    /// 評価する位置に条件式があることを表す。
    pub closed spec fn evaluates_if(&self) -> bool {
        self.active matches Active::Expression(expr) && {
            let body = expr.frame_model().body_model();
            conditional_positions(body.source.text_model(), body.forms@, expr.expression_model().at).is_some()
        }
    }

    /// 型検査済みの条件式を進めると、同じ環境で真偽値の条件を評価し始める。
    #[verifier::spinoff_prover]
    pub proof fn checked_if_starts_with_checked_condition(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires self.evaluates_checked_expression(aliases), self.evaluates_if(), self.step_matches(result),
        ensures result matches Ok(ScalarExecutionSlice::Suspended(after)) && after.evaluates_checked_expression(aliases)
            && after.saves_checked_condition(aliases),
    {
        reveal(ScalarExecution::step_matches);
        let expr = self.active->Expression_0;
        let body = expr.frame_model().body_model();
        let position = expr.expression_model();
        let (condition, yes, no) = conditional_positions(body.source.text_model(), body.forms@, position.at)->Some_0;
        match result {
            Ok(ScalarExecutionSlice::Suspended(after)) => {
                let inner = choose|inner: ScalarExpressionStep<'p, 'a>| #[trigger] expr.expression_step_matches(Ok(inner))
                    && next_expression_at(after.active, expr.result_type_model(), inner);
                expr.an_if_starts_with_its_condition(condition, yes, no, Ok(inner));
                self.plan.scalar_condition_sites_are_checked(aliases, self.rank, body, position, condition, yes, no);
                after.condition_entry_saves_checked_position(aliases, expr);
            },
            Err(ScalarExecutionError::Literal(error)) => {
                expr.an_if_starts_with_its_condition(condition, yes, no, Err(error));
                assert(false);
            },
            _ => { assert(false); },
        }
    }

    proof fn selected_call_enters_checked_expression(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, args: ScalarArguments<'plan, 'p, 'a>, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.searches_checked_scalar_call(aliases),
            prepared_arguments_match(self.plan, self.rank, self.active->Lookup_site, Some(args)),
            args.model().0.at == self.active->Lookup_parent.expression_model().at,
            scalar_type_agrees(self.active->Lookup_parent.expression_model().expected, args.model().2.signature.result_type.ty),
            entering_call(self.rank, self.active->Lookup_parent, args.model().0, args.model().1, args.model().2,
                args.ranks_model().1, self.waiting@, after),
            after.plan == self.plan,
        ensures after.evaluates_checked_expression(aliases), after.latest_argument_is_checked(aliases),
    {
        let parent = self.active->Lookup_parent;
        let body = parent.frame_model().body_model();
        let site = self.active->Lookup_site;
        let (edge, _, callee) = args.model();
        if edge.arguments@.len() == 0 {
            self.plan.scalar_body_site_is_checked(aliases, args.ranks_model().1, callee);
            after.latest_continuation_waits_for_return(aliases);
        } else {
            self.plan.scalar_call_arguments_are_checked(aliases, self.rank, body, parent.expression_model(), site, callee);
            parent.restored_cursor_positions_agree();
            after.latest_argument_keeps_call_site(aliases, site);
        }
    }
}

}
