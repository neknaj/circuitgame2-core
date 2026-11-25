//! 計画が保持する型検査で、本体の式と呼び出し時の部分式に付けた型を取り出す。

use super::*;
use crate::ncg2m::call_evaluation::scalar::ScalarExpressionSite;
use crate::ncg2m::data_types::{BuiltinDataType, DataType, DataTypeAtom};
use crate::ncg2m::expression_types::{conditional_positions, expression_slot, scalar_call_syntax_at};
use crate::ncg2m::expression_types::named_call::{
    defn_checked_call_arguments, defn_checked_call_has_edge, defn_checked_expression_site, defn_checked_if_child_sites, defn_checked_site_at_body_root,
};

verus! {

impl<'p, 'a> DefnCallPlan<'p, 'a> {
    /// 元の本体の仮引数環境で、指定した期待型により式が型検査を通ることを表す。
    pub closed spec fn scalar_site_is_checked(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, site: ScalarExpressionSite<'a>,
    ) -> bool {
        &&& self.body_matches_at_rank(rank, body)
        &&& self.calls_model_at_rank(rank) matches Some(row)
            && defn_checked_expression_site(aliases, self.order_model()[rank as int], row, body, site.at, site.expected)
    }

    pub(crate) proof fn checked_site_has_the_rank_body(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, site: ScalarExpressionSite<'a>,
    )
        requires self.scalar_site_is_checked(aliases, rank, body, site),
        ensures self.body_matches_at_rank(rank, body),
    {}

    /// 計画から得た本体を、元の署名の戻り型で検査したことを示す。
    pub proof fn scalar_body_site_is_checked(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize, body: DefnEvaluationBody<'p, 'a>,
    )
        requires defn_call_plan_matches(aliases, self), self.body_matches_at_rank(rank, body),
        ensures self.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite {
            at: body.at, expected: body.signature.result_type.ty,
        }),
    {
        defn_call_plan_edge_order(aliases, self, rank);
        let row = self.calls_model_at_rank(rank)->Some_0;
        defn_checked_site_at_body_root(aliases, self.order_model()[rank as int], row, body);
    }

    /// 型検査を通った `if` の条件は真偽値であり、両分岐の期待型は親の期待型に一致する。
    pub proof fn scalar_condition_sites_are_checked(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize, body: DefnEvaluationBody<'p, 'a>,
        site: ScalarExpressionSite<'a>, condition: usize, yes: usize, no: usize,
    )
        requires
            self.scalar_site_is_checked(aliases, rank, body, site),
            conditional_positions(body.source.text_model(), body.forms@, site.at) == Some((condition, yes, no)),
        ensures
            self.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite {
                at: condition, expected: DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 },
            }),
            self.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite { at: yes, expected: site.expected }),
            self.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite { at: no, expected: site.expected }),
    {
        let row = self.calls_model_at_rank(rank)->Some_0;
        defn_checked_if_child_sites(aliases, self.order_model()[rank as int], row, body, site.at,
            site.expected, condition, yes, no);
    }

    /// 型検査済みの宣言呼び出しの、元の構文位置と呼び出し先の順位を計画から得る。
    pub proof fn checked_call_site_at_rank(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, position: ScalarExpressionSite<'a>,
    ) -> (site: usize)
        requires
            defn_call_plan_matches(aliases, self), self.scalar_site_is_checked(aliases, rank, body, position),
            expression_slot(body.source.text_model(), body.forms@, body.at, position.at),
            scalar_call_syntax_at(body.source.text_model(), body.forms@, position.at),
        ensures self.calls_model_at_rank(rank) matches Some(row) && site < row.len() && {
            let edge = row[site as int];
            let order = self.order_model();
            &&& edge.at == position.at
            &&& edge.from == order[rank as int]
            &&& *edge.call.source == *body.source
            &&& edge.call.span == form_span(body.forms@[position.at as int])
            &&& edge.call.head == form_span(body.forms@[position.at + 1])
            &&& defn_call_arguments(body.forms@, position.at, edge.arguments@)
            &&& order.contains(edge.to)
            &&& order.index_of(edge.to) < rank
        },
    {
        defn_call_plan_edge_order(aliases, self, rank);
        let row = self.calls_model_at_rank(rank)->Some_0;
        let decl = self.order_model()[rank as int];
        let site = defn_checked_call_has_edge(aliases, decl, row, body, position.at, position.expected);
        let storage = self.edges@[self.order@[rank as int] as int];
        assert(storage.len() == row.len());
        let site = site as usize;
        let at = defn_call_plan_site_at_rank(aliases, self, rank, site);
        assert(at == position.at);
        site
    }

    /// 型検査済みの宣言呼び出しについて、戻り型の一致と呼び出し元の環境における引数の型判断を示す。
    pub proof fn scalar_call_arguments_are_checked(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize, body: DefnEvaluationBody<'p, 'a>,
        site: ScalarExpressionSite<'a>, candidate: usize, callee: DefnEvaluationBody<'p, 'a>,
    )
        requires
            defn_call_plan_matches(aliases, self), self.scalar_site_is_checked(aliases, rank, body, site),
            site.expected.list_depth == 0,
            site.expected.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)),
            self.calls_model_at_rank(rank) matches Some(row) && candidate < row.len() && {
                let edge = row[candidate as int];
                &&& edge.at == site.at
                &&& self.order_model().contains(edge.to)
                &&& self.body_matches_at_rank(self.order_model().index_of(edge.to) as usize, callee)
            },
        ensures
            site.expected == callee.signature.result_type.ty,
            self.calls_model_at_rank(rank)->Some_0[candidate as int].arguments@.len() == callee.signature.parameters@.len(),
            forall|slot: int| 0 <= slot < callee.signature.parameters@.len() ==>
                self.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite {
                    at: #[trigger] self.calls_model_at_rank(rank)->Some_0[candidate as int].arguments@[slot],
                    expected: callee.signature.parameters@[slot].ty.ty,
                }),
    {
        defn_call_plan_edge_order(aliases, self, rank);
        let row = self.calls_model_at_rank(rank)->Some_0;
        let edge = row[candidate as int];
        let order = self.order_model();
        assert(order[order.index_of(edge.to)] == edge.to);
        defn_checked_call_arguments(aliases, self.order_model()[rank as int], row, candidate, body, site.expected, callee);
    }
}

}
