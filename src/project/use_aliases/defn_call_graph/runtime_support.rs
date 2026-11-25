//! 型検査済み計画から元の本体を取得し、スカラー評価器の対応範囲を調べる。

use super::*;
use crate::ncg2m::data_types::{BuiltinDataType, DataType, DataTypeAtom};
use crate::ncg2m::expression_types::named_call::check_scalar_body_syntax;

verus! {

spec fn marked(scope: Seq<bool>, rank: usize) -> bool {
    rank < scope.len() && scope[rank as int]
}

proof fn marked_ranks(scope: Seq<bool>) -> (ranks: Set<usize>)
    ensures forall|rank: usize| #[trigger] ranks.contains(rank) == marked(scope, rank),
{
    let numbers = Seq::new(scope.len(), |i: int| i as usize);
    let all = numbers.to_set();
    let ranks = all.filter(|rank: usize| marked(scope, rank));
    assert forall|rank: usize| #[trigger] ranks.contains(rank) == marked(scope, rank) by {
        if marked(scope, rank) {
            assert(numbers[rank as int] == rank);
            assert(numbers.contains(rank));
            assert(all.contains(rank));
        }
    };
    ranks
}

spec fn marked_superset(before: Seq<bool>, after: Seq<bool>) -> bool {
    before.len() == after.len()
        && forall|rank: usize| #[trigger] marked(before, rank) ==> marked(after, rank)
}

spec fn already_verified(plan: &DefnCallPlan, scope: Seq<bool>, first: usize) -> bool {
    forall|rank: usize| rank >= first && #[trigger] marked(scope, rank) ==> {
        &&& exists|body: DefnEvaluationBody| #[trigger] plan.scalar_fragment_body(rank, body)
        &&& plan.calls_model_at_rank(rank) matches Some(row) && {
            let order = plan.order_model();
            forall|i: int| 0 <= i < row.len() ==> {
                let edge = #[trigger] row[i];
                &&& order.contains(edge.to)
                &&& 0 <= order.index_of(edge.to) < rank
                &&& marked(scope, order.index_of(edge.to) as usize)
            }
        }
    }
}

spec fn marks_are_necessary(plan: &DefnCallPlan, root: usize, scope: Seq<bool>) -> bool {
    plan.scalar_fragment_is_closed(root) ==>
        forall|rank: usize| #[trigger] marked(scope, rank) ==> plan.scalar_fragment_is_closed(rank)
}

proof fn marking_preserves_verified_frontier(
    plan: &DefnCallPlan, before: Seq<bool>, after: Seq<bool>, first: usize,
)
    requires already_verified(plan, before, first), marked_superset(before, after),
        forall|rank: int| first <= rank < before.len() ==> before[rank] == #[trigger] after[rank],
    ensures already_verified(plan, after, first),
{
    assert forall|rank: usize| rank >= first && #[trigger] marked(after, rank) implies {
        &&& exists|body: DefnEvaluationBody| #[trigger] plan.scalar_fragment_body(rank, body)
        &&& plan.calls_model_at_rank(rank) matches Some(row) && {
            let order = plan.order_model();
            forall|i: int| 0 <= i < row.len() ==> {
                let edge = #[trigger] row[i];
                &&& order.contains(edge.to)
                &&& 0 <= order.index_of(edge.to) < rank
                &&& marked(after, order.index_of(edge.to) as usize)
            }
        }
    } by {
        assert(marked(before, rank));
        let row = plan.calls_model_at_rank(rank)->Some_0;
        assert forall|site: int| 0 <= site < row.len() implies
            marked(after, plan.order_model().index_of((#[trigger] row[site]).to) as usize) by {
            assert(marked(before, plan.order_model().index_of(row[site].to) as usize));
        };
    };
}

impl<'p, 'a> DefnCallPlan<'p, 'a> {
    fn check_scalar_value_type(&self, ty: DataType) -> (supported: bool)
        ensures supported == self.scalar_fragment_value_type(ty),
    {
        ty.list_depth == 0
            && matches!(ty.atom, DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
    }

    fn check_body_signature(&self, signature: &crate::ncg2m::data_types::DefnSignature) -> (supported: bool)
        ensures supported == (self.scalar_fragment_value_type(signature.result_type.ty)
            && forall|i: int| 0 <= i < signature.parameters@.len()
                ==> self.scalar_fragment_value_type((#[trigger] signature.parameters@[i]).ty.ty)),
    {
        if !self.check_scalar_value_type(signature.result_type.ty) { return false; }
        let mut next = 0;
        while next < signature.parameters.len()
            invariant
                next <= signature.parameters@.len(),
                self.scalar_fragment_value_type(signature.result_type.ty),
                forall|i: int| 0 <= i < next
                    ==> self.scalar_fragment_value_type((#[trigger] signature.parameters@[i]).ty.ty),
            decreases signature.parameters@.len() - next,
        {
            if !self.check_scalar_value_type(signature.parameters[next].ty.ty) { return false; }
            next += 1;
        }
        true
    }

    /// 指定した順位の本体と署名を、スカラー評価器で扱えるか調べる。
    ///
    /// 順位の範囲外なら `None` を返す。本体の構文と仮引数・戻り値の型を調べる。
    /// 呼び出し先の本体は、それぞれの順位で調べる。
    pub fn scalar_body_support_at_rank(&self, rank: usize) -> (supported: Option<bool>)
        ensures
            supported.is_some() == (rank < self.order_model().len()),
            supported matches Some(ok) ==> exists|body: DefnEvaluationBody<'p, 'a>|
                #[trigger] self.body_matches_at_rank(rank, body) && ok == self.scalar_fragment_body(rank, body),
    {
        let body = self.body_at_rank(rank)?;
        let signature_fits = self.check_body_signature(&body.signature);
        proof { body.source.text_model_is_text(); }
        let fits = signature_fits && check_scalar_body_syntax(body.source.text(), body.forms, body.at);
        assert(self.body_matches_at_rank(rank, body) && fits == self.scalar_fragment_body(rank, body));
        assert(exists|origin: DefnEvaluationBody<'p, 'a>| #[trigger] self.body_matches_at_rank(rank, origin)
            && fits == self.scalar_fragment_body(rank, origin));
        Some(fits)
    }
    // 順位は呼び出しの辺を下るたびに減る。処理済みの順位を再び調べる必要はない。
    fn mark_scalar_callees(&self, _root: usize, rank: usize, marks: &mut Vec<bool>)
        requires
            rank < self.order_model().len(), marked(old(marks)@, rank), marks_are_necessary(self, _root, old(marks)@),
        ensures
            marked_superset(old(marks)@, final(marks)@),
            marks_are_necessary(self, _root, final(marks)@),
            forall|i: int| rank <= i < old(marks)@.len() ==> old(marks)@[i] == #[trigger] final(marks)@[i],
            self.calls_model_at_rank(rank) matches Some(row) && {
                let order = self.order_model();
                forall|i: int| 0 <= i < row.len() ==> {
                    let edge = #[trigger] row[i];
                    &&& order.contains(edge.to)
                    &&& 0 <= order.index_of(edge.to) < rank
                    &&& marked(final(marks)@, order.index_of(edge.to) as usize)
                }
            },
    {
        proof {
            use_type_invariant(self);
            reveal(anchored_arguments);
            let node = self.order@[rank as int];
            assert(node < self.edges@.len());
            assert(self.order_model() == self.order@.map_values(|i: usize| self.vertices@[i as int]));
        }
        let Some(row) = self.calls_at_rank(rank) else { unreachable!() };
        let ghost origin = marks@;
        let ghost order = self.order_model();
        let ghost node = self.order@[rank as int] as int;
        let mut site = 0;
        while site < row.len()
            invariant
                self.indexes_are_valid(),
                self.calls_model_at_rank(rank) == Some(row@),
                row@ == self.edges@[node]@, self.ranks@[node] == rank,
                order == self.order_model(),
                order == self.order@.map_values(|i: usize| self.vertices@[i as int]),
                0 <= node < self.edges@.len(),
                marked(origin, rank), marked(marks@, rank),
                marked_superset(origin, marks@), marks_are_necessary(self, _root, marks@),
                forall|i: int| rank <= i < origin.len() ==> origin[i] == #[trigger] marks@[i],
                site <= row@.len(),
                forall|i: int| 0 <= i < site ==> {
                    let edge = #[trigger] row@[i];
                    &&& order.contains(edge.to)
                    &&& 0 <= order.index_of(edge.to) < rank
                    &&& marked(marks@, order.index_of(edge.to) as usize)
                },
            decreases row@.len() - site,
        {
            let edge = &row[site];
            proof {
                reveal(ordered_edges);
                assert(*edge == self.edges@[node]@[site as int]);
                assert(order.contains(edge.to) && order.index_of(edge.to) < rank);
            }
            let Some(target) = self.rank_of(edge.to) else { unreachable!() };
            let ghost before = marks@;
            marks.set(target, true);
            proof {
                if self.scalar_fragment_is_closed(_root) {
                    assert(self.scalar_fragment_is_closed(rank));
                    let callee = self.closed_scalar_fragment_callee(rank, site);
                    assert(callee.0 == target);
                }
                assert forall|i: usize| #[trigger] marked(marks@, i) && i != target
                    implies marked(before, i) by { assert(before[i as int] == marks@[i as int]); };
                assert forall|i: usize| #[trigger] marked(before, i) implies marked(marks@, i) by {
                    if i != target { assert(before[i as int] == marks@[i as int]); }
                };
                assert(marked_superset(origin, marks@));
                assert(marks_are_necessary(self, _root, marks@));
            }
            site += 1;
        }
    }

    /// 選んだ順位から到達する補助関数の構文と署名を、スカラー評価器で扱えるかを調べる。
    ///
    /// 順位の範囲外なら `None`、到達する本体に非対応の構文や型があれば `Some(false)` を返す。
    /// 対応する場合は、同じ計画、順位、署名に合う実引数を
    /// [`crate::ncg2m::call_evaluation::scalar::ScalarExecution::start`] に渡し、正の実行枠で評価を進められる。
    pub fn scalar_fragment_support_at_rank(&self, rank: usize) -> (supported: Option<bool>)
        ensures supported.is_some() == (rank < self.order_model().len()),
            supported matches Some(ok) ==> ok == self.scalar_fragment_is_closed(rank),
    {
        if rank >= self.len() { return None; }
        let mut scope: Vec<bool> = Vec::new();
        while scope.len() <= rank
            invariant rank < self.order_model().len() <= usize::MAX,
                scope@.len() <= rank + 1,
                forall|i: int| 0 <= i < scope@.len() ==> !(#[trigger] scope@[i]),
            decreases rank + 1 - scope@.len(),
        {
            scope.push(false);
        }
        scope.set(rank, true);
        let mut cursor = rank + 1;
        while cursor > 0
            invariant
                cursor <= rank + 1 <= self.order_model().len(), scope@.len() == rank + 1,
                marked(scope@, rank), marks_are_necessary(self, rank, scope@),
                already_verified(self, scope@, cursor),
            decreases cursor,
        {
            let current = cursor - 1;
            if scope[current] {
                let Some(ok) = self.scalar_body_support_at_rank(current) else { unreachable!() };
                proof {
                    assert(marked(scope@, current));
                    if !ok && self.scalar_fragment_is_closed(rank) {
                        assert(self.scalar_fragment_is_closed(current));
                        let body = choose|body: DefnEvaluationBody<'p, 'a>|
                            #[trigger] self.body_matches_at_rank(current, body) && ok == self.scalar_fragment_body(current, body);
                        self.closed_scalar_fragment_matches_body(current, body);
                        assert(false);
                    }
                }
                if !ok { return Some(false); }
                let ghost before = scope@;
                self.mark_scalar_callees(rank, current, &mut scope);
                proof {
                    marking_preserves_verified_frontier(self, before, scope@, cursor);
                    assert(already_verified(self, scope@, current));
                }
            } else {
                assert(already_verified(self, scope@, current));
            }
            cursor = current;
        }
        proof {
            let included = marked_ranks(scope@);
            assert(already_verified(self, scope@, 0));
            assert(self.scalar_fragment_ranks_are_closed(included));
            self.scalar_fragment_is_closed_over(rank, included);
        }
        Some(true)
    }

}

}
