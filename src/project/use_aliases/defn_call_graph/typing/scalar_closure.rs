//! スカラー評価器が扱う構文を、到達する補助関数の本体まで確認する。

use super::*;
use crate::ncg2m::data_types::{signature_parameter_types_agree, signature_result_types_agree};
use crate::ncg2m::expression_types::{scalar_evaluator_syntax, scalar_syntax_matches_call_arguments};

verus! {

impl<'p, 'a> DefnCallPlan<'p, 'a> {
    /// 本体の構文と、仮引数および戻り値の型をスカラー評価器で扱えることを表す。
    pub open spec fn scalar_fragment_body(&self, rank: usize, body: DefnEvaluationBody<'p, 'a>) -> bool {
        &&& self.body_matches_at_rank(rank, body)
        &&& scalar_evaluator_syntax(body.source.text_model(), body.forms@, body.at)
        &&& self.scalar_fragment_value_type(body.signature.result_type.ty)
        &&& forall|i: int| 0 <= i < body.signature.parameters@.len() ==>
            self.scalar_fragment_value_type((#[trigger] body.signature.parameters@[i]).ty.ty)
    }

    /// 評価環境に保持できる真偽値と固定幅整数の型を表す。
    pub open spec fn scalar_fragment_value_type(&self, ty: DataType) -> bool {
        ty.list_depth == 0
            && (ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
    }

    /// 指定した順位の集合が対応する本体だけを含み、その集合内で全呼び出し先が収まることを表す。
    pub open spec fn scalar_fragment_ranks_are_closed(&self, ranks: Set<usize>) -> bool {
        forall|rank: usize| #[trigger] ranks.contains(rank) ==> {
            &&& exists|body: DefnEvaluationBody<'p, 'a>| #[trigger] self.scalar_fragment_body(rank, body)
            &&& self.calls_model_at_rank(rank) matches Some(row) && {
                let order = self.order_model();
                forall|i: int| 0 <= i < row.len() ==> {
                    let edge = #[trigger] row[i];
                    &&& order.contains(edge.to)
                    &&& 0 <= order.index_of(edge.to) < rank
                    &&& ranks.contains(order.index_of(edge.to) as usize)
                }
            }
        }
    }

    /// 指定した順位の本体と、そこから到達するすべての補助関数が対応する断片に属することを表す。
    ///
    /// 条件式の両方の分岐を調べるため、実行時に選ばれない分岐の呼び出しも対象に含む。
    pub closed spec fn scalar_fragment_is_closed(&self, rank: usize) -> bool {
        exists|ranks: Set<usize>| ranks.contains(rank) && #[trigger] self.scalar_fragment_ranks_are_closed(ranks)
    }

    /// すべての呼び出し先を含む対応済みの順位集合から、指定した順位の対応を示す。
    pub proof fn scalar_fragment_is_closed_over(&self, rank: usize, ranks: Set<usize>)
        requires ranks.contains(rank), self.scalar_fragment_ranks_are_closed(ranks),
        ensures self.scalar_fragment_is_closed(rank),
    {}

    /// 呼び出しを持たない対応済みの本体は、その順位だけで閉じている。
    pub proof fn scalar_fragment_without_calls_is_closed(&self, rank: usize, body: DefnEvaluationBody<'p, 'a>)
        requires self.scalar_fragment_body(rank, body),
            self.calls_model_at_rank(rank) matches Some(row) && row.len() == 0,
        ensures self.scalar_fragment_is_closed(rank),
    {
        let ranks = Set::empty().insert(rank);
        assert forall|k: usize| #[trigger] ranks.contains(k) implies {
            &&& exists|origin: DefnEvaluationBody<'p, 'a>| #[trigger] self.scalar_fragment_body(k, origin)
            &&& self.calls_model_at_rank(k) matches Some(row) && {
                let order = self.order_model();
                forall|i: int| 0 <= i < row.len() ==> {
                    let edge = #[trigger] row[i];
                    &&& order.contains(edge.to)
                    &&& 0 <= order.index_of(edge.to) < k
                    &&& ranks.contains(order.index_of(edge.to) as usize)
                }
            }
        } by { assert(k == rank); };
        self.scalar_fragment_is_closed_over(rank, ranks);
    }

    /// 対応する順位について、同じ順位から得た実際の本体にも構文と型の判断が成り立つ。
    pub proof fn closed_scalar_fragment_matches_body(&self, rank: usize, body: DefnEvaluationBody<'p, 'a>)
        requires self.scalar_fragment_is_closed(rank), self.body_matches_at_rank(rank, body),
        ensures self.scalar_fragment_body(rank, body),
    {
        let ranks = choose|ranks: Set<usize>| ranks.contains(rank) && #[trigger] self.scalar_fragment_ranks_are_closed(ranks);
        let origin = choose|origin: DefnEvaluationBody<'p, 'a>| #[trigger] self.scalar_fragment_body(rank, origin);
        self.bodies_at_rank_agree(rank, origin, body);
        signature_result_types_agree(origin.signature, body.signature);
        assert forall|i: int| 0 <= i < body.signature.parameters@.len()
            implies self.scalar_fragment_value_type((#[trigger] body.signature.parameters@[i]).ty.ty) by {
            signature_parameter_types_agree(origin.signature, body.signature, i);
            assert(origin.signature.parameters@[i].ty.ty == body.signature.parameters@[i].ty.ty);
        };
    }

    /// 対応する本体内の呼び出し先の順位と、同じ断片に属する元の本体を取り出す。
    pub proof fn closed_scalar_fragment_callee(&self, rank: usize, site: usize)
        -> (callee: (usize, DefnEvaluationBody<'p, 'a>))
        requires
            self.scalar_fragment_is_closed(rank),
            self.calls_model_at_rank(rank) matches Some(row) && site < row.len(),
        ensures
            callee.0 < rank,
            self.order_model().contains(self.calls_model_at_rank(rank)->Some_0[site as int].to),
            self.order_model().index_of(self.calls_model_at_rank(rank)->Some_0[site as int].to) == callee.0,
            self.scalar_fragment_body(callee.0, callee.1),
            self.scalar_fragment_is_closed(callee.0),
    {
        let ranks = choose|ranks: Set<usize>| ranks.contains(rank) && #[trigger] self.scalar_fragment_ranks_are_closed(ranks);
        let row = self.calls_model_at_rank(rank)->Some_0;
        let edge = row[site as int];
        let to = self.order_model().index_of(edge.to) as usize;
        assert(ranks.contains(to));
        self.scalar_fragment_is_closed_over(to, ranks);
        let body = choose|body: DefnEvaluationBody<'p, 'a>| #[trigger] self.scalar_fragment_body(to, body);
        (to, body)
    }

    /// 対応する宣言呼び出しから、同じ型検査で確定した実引数と呼び出し先の本体を取り出す。
    #[verifier::spinoff_prover]
    pub proof fn closed_scalar_call_has_checked_parts(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, rank: usize,
        body: DefnEvaluationBody<'p, 'a>, position: ScalarExpressionSite<'a>,
    ) -> (parts: (usize, usize, DefnEvaluationBody<'p, 'a>))
        requires
            defn_call_plan_matches(aliases, self), self.scalar_fragment_is_closed(rank),
            self.scalar_site_is_checked(aliases, rank, body, position), self.scalar_fragment_value_type(position.expected),
            scalar_evaluator_syntax(body.source.text_model(), body.forms@, position.at),
            expression_slot(body.source.text_model(), body.forms@, body.at, position.at),
            scalar_call_syntax_at(body.source.text_model(), body.forms@, position.at),
            self.scalar_site_has_declared_edge(rank, position.at),
        ensures self.calls_model_at_rank(rank) matches Some(row) && parts.0 < row.len() && {
            let edge = row[parts.0 as int];
            let target = parts.2;
            &&& edge.at == position.at
            &&& self.order_model().index_of(edge.to) == parts.1
            &&& parts.1 < rank
            &&& self.scalar_fragment_body(parts.1, target)
            &&& self.scalar_fragment_is_closed(parts.1)
            &&& target.signature.result_type.ty == position.expected
            &&& edge.arguments@.len() == target.signature.parameters@.len()
            &&& forall|i: int| 0 <= i < edge.arguments@.len() ==> {
                let at = #[trigger] edge.arguments@[i];
                let ty = target.signature.parameters@[i].ty.ty;
                &&& self.scalar_fragment_value_type(ty)
                &&& scalar_evaluator_syntax(body.source.text_model(), body.forms@, at)
                &&& self.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite { at, expected: ty })
            }
        },
    {
        let site = self.checked_call_site_at_rank(aliases, rank, body, position);
        let (to, target) = self.closed_scalar_fragment_callee(rank, site);
        let edge = self.calls_model_at_rank(rank)->Some_0[site as int];
        self.scalar_call_arguments_are_checked(aliases, rank, body, position, site, target);
        scalar_syntax_matches_call_arguments(body.source.text_model(), body.forms@, position.at, edge.arguments@);
        assert forall|i: int| 0 <= i < edge.arguments@.len() implies {
            let at = #[trigger] edge.arguments@[i];
            let ty = target.signature.parameters@[i].ty.ty;
            &&& self.scalar_fragment_value_type(ty)
            &&& scalar_evaluator_syntax(body.source.text_model(), body.forms@, at)
            &&& self.scalar_site_is_checked(aliases, rank, body, ScalarExpressionSite { at, expected: ty })
        } by {
            assert(self.scalar_fragment_value_type(target.signature.parameters@[i].ty.ty));
        };
        (site, to, target)
    }
}

}
