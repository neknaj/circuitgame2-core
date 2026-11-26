//! 自然数反復の回数、累積値、次に本体を評価する位置を保持する。

use super::DefnEvaluationBody;
use crate::ncg2m::expression_types::{NatFoldTerms, read_nat_fold_terms};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::nat_fold_terms_match;
use crate::project::DefnCallPlan;
use vstd::prelude::*;

verus! {

/// 型検査済みの関数本体から自然数反復の式と束縛名の位置を取り出す。
///
/// 計画に順位がない場合と、本体の根が `fold-nat` でない場合は `None` を返す。
/// 本体の構文木と文書版を再利用する。
pub fn planned_nat_fold<'p, 'a>(plan: &DefnCallPlan<'p, 'a>, rank: usize)
    -> (fold: Option<(DefnEvaluationBody<'p, 'a>, NatFoldTerms)>)
    ensures
        fold matches Some((body, terms)) ==>
            plan.body_matches_at_rank(rank, body)
            && nat_fold_terms_match(body.source.text_model(), body.forms@, body.at, Some(terms))
            && body.at < terms.count < terms.initial < terms.index_binding
                < terms.accumulator_binding < terms.body < body.forms@.len(),
        fold is None ==> forall|body: DefnEvaluationBody<'p, 'a>|
            #[trigger] plan.body_matches_at_rank(rank, body) ==>
                nat_fold_terms_match(body.source.text_model(), body.forms@, body.at, None),
{
    let Some(body) = plan.body_at_rank(rank) else {
        return None;
    };
    let source = body.source.text();
    match read_nat_fold_terms(source, body.forms, body.at) {
        Some(terms) => Some((body, terms)),
        None => {
            assert forall|other: DefnEvaluationBody<'p, 'a>| #[trigger] plan.body_matches_at_rank(rank, other)
                implies nat_fold_terms_match(other.source.text_model(), other.forms@, other.at, None)
                by {
                    plan.bodies_at_rank_agree(rank, body, other);
                }
            None
        },
    }
}

/// 回数と初期値を評価した後の `fold-nat` の継続。
///
/// 反復中も当初の回数は固定する。累積値の型は本体を評価する側で決める。
pub struct NatFold<Value> {
    count: u64,
    index: u64,
    accumulator: Value,
}

/// 次の反復を実行するか、反復の結果を返す。
pub enum NatFoldNext<Value> {
    /// 指定された添字と累積値を束縛して本体を評価する。
    Evaluate(NatFoldIteration<Value>),
    /// 反復が終了し、最後の累積値が得られた。
    Complete(Value),
}

/// 本体の値を待つ一回の反復。
///
/// 次の値はこの反復を消費して渡す。添字の再指定は不要である。
pub struct NatFoldIteration<Value> {
    fold: NatFold<Value>,
}

impl<Value> NatFold<Value> {
    /// 回数、次の添字、現在の累積値を表す。
    pub closed spec fn model(&self) -> (u64, u64, Value) {
        (self.count, self.index, self.accumulator)
    }

    #[verifier::type_invariant]
    spec fn fits(&self) -> bool {
        self.index <= self.count
    }

    /// 左から評価した回数と初期値を受け取り、添字0から開始する。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::ncg2m::call_evaluation::nat_fold::{NatFold, NatFoldNext};
    ///
    /// assert!(matches!(NatFold::start(0, 7).next(), NatFoldNext::Complete(7)));
    /// let NatFoldNext::Evaluate(first) = NatFold::start(1, 7).next() else {
    ///     unreachable!();
    /// };
    /// assert_eq!((first.index(), *first.accumulator()), (0, 7));
    /// let next = first.receive::<()>(Ok(5)).unwrap();
    /// assert!(matches!(next.next(), NatFoldNext::Complete(5)));
    /// ```
    pub fn start(count: u64, initial: Value) -> (fold: Self)
        ensures fold.model() == (count, 0u64, initial),
    {
        Self { count, index: 0, accumulator: initial }
    }

    /// 次の本体の評価を要求する。回数が0なら初期値を返す。
    pub fn next(self) -> (next: NatFoldNext<Value>)
        ensures match next {
            NatFoldNext::Evaluate(iteration) => iteration.model() == self.model()
                && self.model().1 < self.model().0,
            NatFoldNext::Complete(value) => self.model().1 == self.model().0
                && value == self.model().2,
        },
    {
        proof { use_type_invariant(&self); }
        if self.index < self.count {
            NatFoldNext::Evaluate(NatFoldIteration { fold: self })
        } else {
            NatFoldNext::Complete(self.accumulator)
        }
    }
}

impl<Value> NatFoldIteration<Value> {
    /// 当初の回数、本体に渡す添字と累積値を表す。
    pub closed spec fn model(&self) -> (u64, u64, Value) { self.fold.model() }

    #[verifier::type_invariant]
    spec fn pending(&self) -> bool {
        self.fold.index < self.fold.count
    }

    /// 本体に束縛する添字。
    pub fn index(&self) -> (index: u64)
        ensures index == self.model().1,
    {
        self.fold.index
    }

    /// 本体に束縛する累積値。
    pub fn accumulator(&self) -> (accumulator: &Value)
        ensures *accumulator == self.model().2,
    {
        &self.fold.accumulator
    }

    /// 本体が返した値で累積値を更新する。
    ///
    /// # Errors
    ///
    /// 本体が失敗した場合はその診断を返す。次の反復は進まない。
    pub fn receive<Error>(self, result: Result<Value, Error>) -> (next: Result<NatFold<Value>, Error>)
        ensures match result {
            Ok(value) => next matches Ok(fold) && fold.model() == (
                self.model().0, (self.model().1 + 1) as u64, value,
            ) && self.model().1 < self.model().0,
            Err(error) => next == Err(error),
        },
    {
        proof { use_type_invariant(&self); }
        let value = result?;
        Ok(NatFold { count: self.fold.count, index: self.fold.index + 1, accumulator: value })
    }
}

/// 添字 `start` から、各反復の本体に添字と直前の値を渡して得る累積値列。
///
/// 先頭は実行前の累積値である。続く各要素は成功した本体一回分の結果を表す。
pub open spec fn fold_nat_values<Value, Error>(
    body: spec_fn(u64, Value) -> Result<Value, Error>, start: nat, count: nat, values: Seq<Value>,
) -> bool {
    &&& values.len() > 0
    &&& start + values.len() - 1 <= count <= u64::MAX
    &&& forall|i: int| 0 <= i < values.len() - 1 ==>
        #[trigger] body((start + i) as u64, values[i]) == Ok(values[i + 1])
}

/// 連続する部分列をつなぐと、実行枠を分けずに進めた場合の累積値列になる。
pub proof fn fold_nat_values_compose<Value, Error>(
    body: spec_fn(u64, Value) -> Result<Value, Error>, start: nat, count: nat,
    first: Seq<Value>, second: Seq<Value>,
)
    requires fold_nat_values(body, start, count, first),
        fold_nat_values(body, (start + first.len() - 1) as nat, count, second),
        first.last() == second[0],
    ensures fold_nat_values(body, start, count, first + second.skip(1)),
{
    let joined = first + second.skip(1);
    assert forall|i: int| 0 <= i < joined.len() - 1 implies
        #[trigger] body((start + i) as u64, joined[i]) == Ok(joined[i + 1]) by {
        if i + 1 < first.len() {
            assert(joined[i] == first[i]);
            assert(joined[i + 1] == first[i + 1]);
        } else {
            let j = i - first.len() + 1;
            assert(0 <= j < second.len() - 1);
            assert(joined[i] == second[j]) by {
                if j == 0 {
                    assert(i == first.len() - 1);
                }
            }
            assert(joined[i + 1] == second[j + 1]);
            assert((start + i) as u64 == ((start + first.len() - 1) as nat + j) as u64);
        }
    }
}

/// 本体の評価結果が規則に従うとき、一回進めた実際の継続を累積値列の末尾につなぐ。
pub proof fn fold_nat_receive_extends_values<Value, Error>(
    body: spec_fn(u64, Value) -> Result<Value, Error>, start: nat, values: Seq<Value>,
    before: NatFoldIteration<Value>, after: NatFold<Value>,
)
    requires
        fold_nat_values(body, start, before.model().0 as nat, values),
        before.model().1 == start + values.len() - 1,
        before.model().2 == values.last(),
        before.model().1 < before.model().0,
        body(before.model().1, before.model().2) == Ok(after.model().2),
        after.model().0 == before.model().0,
        after.model().1 == before.model().1 + 1,
    ensures
        fold_nat_values(body, start, after.model().0 as nat, values.push(after.model().2)),
        after.model().1 == start + values.push(after.model().2).len() - 1,
{
    let second = seq![before.model().2, after.model().2];
    assert(fold_nat_values(body, (start + values.len() - 1) as nat, after.model().0 as nat, second));
    fold_nat_values_compose(body, start, after.model().0 as nat, values, second);
    assert(values.push(after.model().2) =~= values + second.skip(1));
}

} // verus!
