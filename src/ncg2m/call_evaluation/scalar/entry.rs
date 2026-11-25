//! 選んだ補助関数をスカラー評価器で扱えるか調べ、評価の開始に備える。

use super::*;
use crate::project::DefnPosition;

verus! {

/// スカラー評価の入口を選べなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScalarEntryError {
    /// 指定した宣言位置が呼び出し計画に含まれない。
    UnknownDefinition,
    /// 本体または到達する補助関数に、評価器が扱えない構文や型がある。
    UnsupportedFragment,
}

/// スカラー評価器が扱えることを確かめた補助関数。
///
/// 選択した宣言の計画を借用する。同じ入口から、実引数を変えて複数回の評価を開始できる。
pub struct ScalarEntry<'plan, 'p, 'a> {
    plan: &'plan DefnCallPlan<'p, 'a>,
    rank: usize,
}

impl<'plan, 'p, 'a> ScalarEntry<'plan, 'p, 'a> {
    #[verifier::type_invariant]
    spec fn checked(&self) -> bool {
        let position = self.plan.order_model()[self.rank as int];
        &&& self.plan.order_nodes_valid()
        &&& self.rank < self.plan.order_model().len()
        &&& self.plan.project_model().indexed_defn(position.file, position.item).is_some()
        &&& self.plan.scalar_fragment_is_closed(self.rank)
    }

    /// 入口を選んだ呼び出し計画。
    pub closed spec fn plan_model(&self) -> &'plan DefnCallPlan<'p, 'a> {
        self.plan
    }

    /// 呼び出し計画における入口の順位。
    pub closed spec fn rank_model(&self) -> usize {
        self.rank
    }

    /// 呼び出し計画における入口の順位を返す。
    pub fn rank(&self) -> (rank: usize)
        ensures rank == self.rank_model(),
    {
        self.rank
    }

    /// 入口の仮引数に値を束縛し、新しい評価を開始する。
    ///
    /// # Errors
    ///
    /// 実引数の個数や型が署名に合わない場合は、束縛の診断を返す。
    pub fn start(&self, values: Vec<ScalarValue>)
        -> (result: Result<ScalarExecution<'plan, 'p, 'a>, ScalarBindingError<'p, 'a>>)
        ensures
            self.plan_model().scalar_fragment_is_closed(self.rank_model()),
            !(result matches Err(ScalarBindingError::Rank)),
            match result {
                Ok(state) => {
                    &&& state.plan_model() == self.plan_model()
                    &&& exists|frame: ScalarCallFrame<'p, 'a>|
                        #[trigger] binding_at_rank_matches(self.plan_model(), self.rank_model(), values@, Ok(frame))
                            && state.starts_with(self.plan_model(), self.rank_model(), frame)
                },
                Err(error) => binding_at_rank_matches(self.plan_model(), self.rank_model(), values@, Err(error)),
            },
    {
        proof { use_type_invariant(self); }
        let ghost arguments = values@;
        let result = ScalarExecution::start(self.plan, self.rank, values);
        proof {
            assert(self.plan_model() == self.plan && self.rank_model() == self.rank);
            if let Ok(state) = &result {
                let frame = choose|frame: ScalarCallFrame<'p, 'a>|
                    #[trigger] binding_at_rank_matches(self.plan, self.rank, arguments, Ok(frame))
                        && state.starts_with(self.plan, self.rank, frame);
                assert(binding_at_rank_matches(self.plan_model(), self.rank_model(), arguments, Ok(frame)));
                assert(state.starts_with(self.plan_model(), self.rank_model(), frame));
            }
        }
        result
    }
}

/// 呼び出し計画内の宣言位置を選び、対応するスカラー評価の入口を用意する。
///
/// 宣言位置は、この計画と同じプロジェクトから取得する。条件式の両分岐と、
/// そこから到達する補助関数も検査する。
///
/// # Errors
///
/// 宣言が計画になければ [`ScalarEntryError::UnknownDefinition`]、到達する本体に
/// 非対応の構文や型があれば [`ScalarEntryError::UnsupportedFragment`] を返す。
pub fn prepare_scalar_entry<'plan, 'p, 'a>(plan: &'plan DefnCallPlan<'p, 'a>, position: DefnPosition)
    -> (result: Result<ScalarEntry<'plan, 'p, 'a>, ScalarEntryError>)
    ensures
        match result {
            Ok(entry) => {
                &&& plan.order_model().contains(position)
                &&& entry.plan_model() == plan
                &&& entry.rank_model() == plan.order_model().index_of(position)
                &&& plan.scalar_fragment_is_closed(entry.rank_model())
            },
            Err(ScalarEntryError::UnknownDefinition) => !plan.order_model().contains(position),
            Err(ScalarEntryError::UnsupportedFragment) => plan.order_model().contains(position)
                && !plan.scalar_fragment_is_closed(plan.order_model().index_of(position) as usize),
        },
{
    let Some(rank) = plan.rank_of(position) else { return Err(ScalarEntryError::UnknownDefinition); };
    let Some(supported) = plan.scalar_fragment_support_at_rank(rank) else { unreachable!() };
    if !supported { return Err(ScalarEntryError::UnsupportedFragment); }
    Ok(ScalarEntry { plan, rank })
}

}
