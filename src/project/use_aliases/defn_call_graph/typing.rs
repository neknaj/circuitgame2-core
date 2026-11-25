//! 計画が保持する型検査で、本体の式と呼び出し時の部分式に付けた型を取り出す。

use super::*;
use crate::ncg2m::call_evaluation::scalar::ScalarExpressionSite;
use crate::ncg2m::data_types::{BuiltinDataType, DataType, DataTypeAtom};
use crate::ncg2m::expression_types::{conditional_positions, expression_slot, local_scalar_site_is_typed, scalar_atom_at, scalar_call_syntax_at, scalar_evaluator_syntax};
use crate::ncg2m::expression_types::named_call::{
    CheckedNamedTarget, checked_atom_uses_only_parameters, checked_body_scalar_position, recorded_edge_has_call_syntax,
    defn_checked_call_arguments, defn_checked_call_target, defn_checked_expression_site,
    defn_checked_if_child_sites, defn_checked_site_at_body_root,
};

mod scalar_closure;

verus! {

impl<'p, 'a> DefnCallPlan<'p, 'a> {
    /// 元の本体の仮引数環境で、指定した期待型により式が型検査を通ることを表す。
    pub closed spec fn scalar_site_is_checked(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, site: ScalarExpressionSite<'a>,
    ) -> bool {
        &&& self.body_matches_at_rank(rank, body)
        &&& self.calls_model_at_rank(rank) matches Some(row)
            && self.arithmetic_model_at_rank(rank) matches Some(arithmetic)
            && defn_checked_expression_site(aliases, self.order_model()[rank as int], row, arithmetic,
                body, site.at, site.expected)
    }

    pub(crate) proof fn checked_site_has_the_rank_body(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, site: ScalarExpressionSite<'a>,
    )
        requires self.scalar_site_is_checked(aliases, rank, body, site),
        ensures self.body_matches_at_rank(rank, body),
    {}

    pub(crate) proof fn supported_call_is_body_expression(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, site: ScalarExpressionSite<'a>,
    )
        requires
            self.scalar_site_is_checked(aliases, rank, body, site),
            scalar_evaluator_syntax(body.source.text_model(), body.forms@, body.at),
            scalar_call_syntax_at(body.source.text_model(), body.forms@, site.at),
        ensures expression_slot(body.source.text_model(), body.forms@, body.at, site.at),
    {
        let row = self.calls_model_at_rank(rank)->Some_0;
        checked_body_scalar_position(aliases, self.order_model()[rank as int], row, self.arithmetic_model_at_rank(rank)->Some_0, body, site.at, site.expected);
    }

    pub(crate) proof fn checked_atom_keeps_local_type(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, site: ScalarExpressionSite<'a>,
    )
        requires
            self.scalar_site_is_checked(aliases, rank, body, site), scalar_atom_at(body.forms@, site.at),
            self.scalar_fragment_value_type(site.expected),
        ensures local_scalar_site_is_typed(body.source.text_model(), body.forms@, body.signature.parameters@, site.at, site.expected),
    {
        let row = self.calls_model_at_rank(rank)->Some_0;
        checked_atom_uses_only_parameters(aliases, self.order_model()[rank as int], row, self.arithmetic_model_at_rank(rank)->Some_0, body, site.at, site.expected);
    }

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
        body_sites_are_covered_at_rank(aliases, self, rank);
        let row = self.calls_model_at_rank(rank)->Some_0;
        defn_checked_site_at_body_root(aliases, self.order_model()[rank as int], row, self.arithmetic_model_at_rank(rank)->Some_0, body);
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
        defn_checked_if_child_sites(aliases, self.order_model()[rank as int], row, self.arithmetic_model_at_rank(rank)->Some_0, body, site.at,
            site.expected, condition, yes, no);
    }

    /// 呼び出し計画の辺は、元の本体にある宣言呼び出しの構文に対応する。
    pub proof fn recorded_call_at_rank_has_syntax(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, site: usize,
    )
        requires
            defn_call_plan_matches(aliases, self), self.body_matches_at_rank(rank, body),
            self.calls_model_at_rank(rank) matches Some(row) && site < row.len(),
        ensures scalar_call_syntax_at(body.source.text_model(), body.forms@,
            self.calls_model_at_rank(rank)->Some_0[site as int].at),
    {
        defn_call_plan_edge_order(aliases, self, rank);
        body_sites_are_covered_at_rank(aliases, self, rank);
        let row = self.calls_model_at_rank(rank)->Some_0;
        recorded_edge_has_call_syntax(aliases, self.order_model()[rank as int], row, self.arithmetic_model_at_rank(rank)->Some_0, body, site);
    }

    /// 指定した本体の式位置に、宣言への呼び出しがあることを表す。
    pub open spec fn scalar_site_has_declared_edge(&self, rank: usize, at: usize) -> bool {
        self.calls_model_at_rank(rank) matches Some(row)
            && exists|i: int| 0 <= i < row.len() && (#[trigger] row[i]).at == at
    }

    /// 型検査済みの名前付きフォームで、選択した宣言または組み込みの型判断を取り出す。
    pub(crate) proof fn checked_named_target_at_rank(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, position: ScalarExpressionSite<'a>,
    ) -> (selected: CheckedNamedTarget)
        requires
            defn_call_plan_matches(aliases, self), self.scalar_site_is_checked(aliases, rank, body, position),
            (expression_slot(body.source.text_model(), body.forms@, body.at, position.at)
                && scalar_call_syntax_at(body.source.text_model(), body.forms@, position.at))
                || self.arithmetic_site_model(rank, position.at).is_some(),
        ensures match selected {
            CheckedNamedTarget::Declaration(site) => {
                &&& self.calls_model_at_rank(rank) matches Some(row) && 0 <= site < row.len() && row[site].at == position.at
                &&& self.arithmetic_site_model(rank, position.at).is_none()
            },
            CheckedNamedTarget::Arithmetic(site, ty) => {
                &&& site.at == position.at
                &&& self.arithmetic_site_model(rank, position.at) == Some(site)
                &&& !self.scalar_site_has_declared_edge(rank, position.at)
                &&& scalar_call_syntax_at(body.source.text_model(), body.forms@, position.at)
                &&& position.expected.list_depth == 0
                &&& position.expected.atom == DataTypeAtom::Builtin(BuiltinDataType::Integer(ty))
                &&& defn_call_arguments(body.forms@, position.at, seq![site.arguments.0, site.arguments.1])
                &&& self.scalar_site_is_checked(aliases, rank, body,
                    ScalarExpressionSite { at: site.arguments.0, expected: position.expected })
                &&& self.scalar_site_is_checked(aliases, rank, body,
                    ScalarExpressionSite { at: site.arguments.1, expected: position.expected })
            },
        },
    {
        body_sites_are_covered_at_rank(aliases, self, rank);
        reveal(DefnCallPlan::arithmetic_site_model);
        let row = self.calls_model_at_rank(rank)->Some_0;
        let arithmetic = self.arithmetic_model_at_rank(rank)->Some_0;
        let selected = defn_checked_call_target(aliases, self.order_model()[rank as int], row, arithmetic,
            body, position.at, position.expected);
        if let CheckedNamedTarget::Arithmetic(site, _) = selected {
            let at = position.at;
            let actual = choose|i: int| 0 <= i < arithmetic.len() && (#[trigger] arithmetic[i]) == site;
            let stored = choose|i: int| 0 <= i < arithmetic.len() && (#[trigger] arithmetic[i]).at == at;
            if actual < stored { assert(arithmetic[actual].at < arithmetic[stored].at); }
            if stored < actual { assert(arithmetic[stored].at < arithmetic[actual].at); }
            assert(stored == actual);
        }
        selected
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
            self.scalar_site_has_declared_edge(rank, position.at),
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
        let site = choose|i: int| 0 <= i < row.len() && (#[trigger] row[i]).at == position.at;
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
        defn_checked_call_arguments(aliases, self.order_model()[rank as int], row, self.arithmetic_model_at_rank(rank)->Some_0, candidate, body, site.expected, callee);
    }
}

}
