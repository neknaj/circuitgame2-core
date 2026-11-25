//! 型検査済みの宣言呼び出しを探す遷移に、元の本体と署名の証拠を使う。

use super::*;
use crate::project::{MixedUseAliases, defn_call_plan_matches, defn_call_plan_root_scalar_call};

verus! {

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// この評価が参照する補助関数の型検査済み計画を表す。
    pub closed spec fn plan_model(&self) -> &'plan DefnCallPlan<'p, 'a> { self.plan }

    /// 評価中の式に対応する呼び出しの辺を探していることを表す。
    pub closed spec fn is_looking_up_call(&self) -> bool { self.active is Lookup }

    /// 評価中の関数の本体がスカラーを返す宣言呼び出しで、その辺が探索位置以降にあることを表す。
    pub closed spec fn searches_scalar_root_call(&self) -> bool {
        self.active matches Active::Lookup { parent, site } && {
            let body = parent.frame_model().body_model();
            let ty = body.signature.result_type.ty;
            &&& self.plan.body_matches_at_rank(self.rank, body)
            &&& parent.expression_model().at == body.at
            &&& parent.expression_model().expected == ty
            &&& ty.list_depth == 0
            &&& (ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
            &&& self.plan.calls_model_at_rank(self.rank) matches Some(row)
                && exists|found: int| site <= found < row.len() && (#[trigger] row[found]).at == body.at
        }
    }

    /// 型検査済みの本体呼び出しを探すか、その引数または呼び出し先の本体の評価を始める。
    #[verifier::spinoff_prover]
    pub proof fn scalar_root_call_lookup_progress(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires defn_call_plan_matches(aliases, self.plan_model()), self.searches_scalar_root_call(), self.step_matches(result),
        ensures result matches Ok(ScalarExecutionSlice::Suspended(after))
            && (!after.is_looking_up_call() || after.searches_scalar_root_call()),
    {
        reveal(ScalarExecution::step_matches);
        let site = self.active->Lookup_site;
        let parent = self.active->Lookup_parent;
        let body = parent.frame_model().body_model();
        let row = self.plan.calls_model_at_rank(self.rank)->Some_0;
        let found = choose|found: int| site <= found < row.len() && (#[trigger] row[found]).at == body.at;
        let edge = row[site as int];
        if edge.at != body.at {
            assert(site + 1 <= found);
        } else if result is Err {
            let expected = body.signature.result_type.ty;
            let args = choose|args: Option<ScalarArguments<'plan, 'p, 'a>>|
                #[trigger] prepared_arguments_match(self.plan, self.rank, site, args)
                    && match args {
                        None => true,
                        Some(call) => !scalar_type_agrees(expected, call.model().2.signature.result_type.ty),
                    };
            assert(args.is_some());
            let call = args->Some_0;
            defn_call_plan_root_scalar_call(aliases, self.plan, self.rank, site, body, call.model().2);
            assert(false);
        }
    }
}

}
