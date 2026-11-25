//! 条件の位置を取り出し、真偽値を受け取って実行する分岐を選ぶ。

use super::{BuiltinDataType, DataType, DataTypeAtom, ScalarCallFrame};
use crate::ncg2m::expression_types::read_conditional_positions;
#[cfg(verus_only)]
use crate::ncg2m::expression_types::conditional_positions;
#[cfg(verus_only)]
use super::DefnEvaluationBody;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::execution::observation::{bodies_agree, condition_parts_agree, positions_agree};

verus! {

/// 元の構文木で、決められた型を期待して評価する式。
#[derive(Clone, Copy)]
pub struct ScalarExpressionSite<'a> {
    /// 元の構文木における式の添字。
    pub at: usize,
    /// この位置で要求される型。
    pub expected: DataType<'a>,
}

/// `if` の条件の値が得られるまで、二つの分岐と結果の期待型を保持する。
pub struct ScalarCondition<'a> {
    at: usize,
    condition: usize,
    yes: usize,
    no: usize,
    expected: DataType<'a>,
}

/// 条件待ちの継続が、元の構文木にある `if` の部分式を指すことを表す。
pub closed spec fn scalar_condition_matches<'p, 'a>(
    body: DefnEvaluationBody<'p, 'a>, site: ScalarExpressionSite<'a>, next: Option<ScalarCondition<'a>>,
) -> bool {
    let positions = conditional_positions(body.source.text_model(), body.forms@, site.at);
    match next {
        Some(next) => positions matches Some((condition, yes, no))
            && next.positions_model() == (site.at, condition, yes, no)
            && site.at < condition < yes < no < body.forms@.len()
            && next.expected_model() == site.expected,
        None => positions.is_none(),
    }
}

pub(super) proof fn conditional_results_observe_same(
    a: DefnEvaluationBody, b: DefnEvaluationBody, site_a: ScalarExpressionSite, site_b: ScalarExpressionSite,
    first: Option<ScalarCondition>, second: Option<ScalarCondition>,
)
    requires bodies_agree(a, b), positions_agree(site_a, site_b),
        scalar_condition_matches(a, site_a, first), scalar_condition_matches(b, site_b, second),
    ensures match (first, second) {
        (Some(left), Some(right)) => condition_parts_agree(left, right),
        (None, None) => true,
        _ => false,
    },
{
    assert(a.forms@ == b.forms@ && *a.source == *b.source && site_a.at == site_b.at);
}

impl<'a> ScalarCondition<'a> {
    /// この継続を作った元の `if`、条件、二つの分岐の順に添字を表す。
    pub closed spec fn positions_model(&self) -> (usize, usize, usize, usize) {
        (self.at, self.condition, self.yes, self.no)
    }

    /// 選択する分岐に要求する型を表す。
    pub closed spec fn expected_model(&self) -> DataType<'a> { self.expected }

    /// 先に評価する条件の位置と、その期待型を返す。
    pub fn condition(&self) -> (site: ScalarExpressionSite<'a>)
        ensures site.at == self.positions_model().1,
            site.expected == (DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 }),
    {
        ScalarExpressionSite {
            at: self.condition,
            expected: DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 },
        }
    }

    /// 条件の値で分岐を一つ選び、`if` 全体の期待型を選んだ側に引き継ぐ。
    pub fn select(self, condition: bool) -> (site: ScalarExpressionSite<'a>)
        ensures site.at == if condition { self.positions_model().2 } else { self.positions_model().3 },
            site.expected == self.expected_model(),
    {
        ScalarExpressionSite { at: if condition { self.yes } else { self.no }, expected: self.expected }
    }
}

impl<'p, 'a> ScalarCallFrame<'p, 'a> {
    /// 評価位置に `if` があれば、条件を先に評価するための継続を返す。
    ///
    /// 位置はこのフレームの元の構文木に対する添字である。
    /// 式が `if` でない場合や添字が範囲外の場合は `None` を返す。
    pub fn condition_at(&self, site: ScalarExpressionSite<'a>) -> (next: Option<ScalarCondition<'a>>)
        ensures scalar_condition_matches(self.body_model(), site, next),
            next matches Some(next) ==> {
                let (at, condition, yes, no) = next.positions_model();
                &&& at == site.at
                &&& at < condition < yes < no < self.body_model().forms@.len()
                &&& next.expected_model() == site.expected
            },
    {
        proof { use_type_invariant(self); }
        let body = self.body();
        let (condition, yes, no) = read_conditional_positions(body.source.text(), body.forms, site.at)?;
        Some(ScalarCondition { at: site.at, condition, yes, no, expected: site.expected })
    }
}

}
