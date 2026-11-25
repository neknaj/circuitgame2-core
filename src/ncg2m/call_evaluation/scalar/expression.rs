//! スカラー式の条件評価と分岐選択を途中から再開する。

use super::{
    BuiltinDataType, DataType, DataTypeAtom, ScalarCallFrame, ScalarCondition,
    ScalarExpressionSite, ScalarLiteralError, ScalarValue,
};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use super::{scalar_condition_matches, scalar_fits};
#[cfg(verus_only)]
use super::atom::scalar_atom_matches;

verus! {

/// 実行中の補助関数と、値を待つ条件式を保持する。
pub struct ScalarExpression<'p, 'a> {
    frame: ScalarCallFrame<'p, 'a>,
    next: ScalarExpressionSite<'a>,
    branches: Vec<ScalarCondition<'a>>,
}

/// スカラー式の評価を一つ進めた結果。
pub enum ScalarExpressionStep<'p, 'a> {
    /// 次に評価する条件または選んだ分岐が決まった。
    Continue(ScalarExpression<'p, 'a>),
    /// 本体の値が得られた。
    Complete(ScalarValue),
    /// アトムや条件式以外のフォームを評価する必要がある。
    NeedsForm(ScalarExpression<'p, 'a>),
}

spec fn boolean_type<'a>() -> DataType<'a> {
    DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 }
}

spec fn branch_in_bounds(branch: ScalarCondition, length: nat) -> bool {
    let (at, condition, yes, no) = branch.positions_model();
    at < condition < yes < no < length
}

impl<'p, 'a> ScalarExpression<'p, 'a> {
    #[verifier::type_invariant]
    spec fn positions_fit(&self) -> bool {
        let branches = self.branches@;
        let body = self.frame.body_model();
        &&& self.next.at < body.forms@.len()
        &&& self.next.expected == if branches.len() == 0 { body.signature.result_type.ty } else { boolean_type() }
        &&& forall|i: int| 0 <= i < branches.len() ==> {
            let branch = #[trigger] branches[i];
            &&& branch_in_bounds(branch, body.forms@.len())
            &&& branch.expected_model() == if i == 0 { body.signature.result_type.ty } else { boolean_type() }
        }
    }

    /// 条件や分岐を置いた、元の本体と仮引数の環境を表す。
    pub closed spec fn frame_model(&self) -> ScalarCallFrame<'p, 'a> { self.frame }

    /// 現在評価する位置と、値に求める型を表す。
    pub closed spec fn expression_model(&self) -> ScalarExpressionSite<'a> { self.next }

    /// 条件の値を待つ継続を、深さの浅い側から表す。
    pub closed spec fn branches_model(&self) -> Seq<ScalarCondition<'a>> { self.branches@ }

    /// 型付きの本体を評価する。開始時には条件を待つ継続を持たない。
    pub fn start(frame: ScalarCallFrame<'p, 'a>) -> (state: Self)
        ensures state.frame_model() == frame,
            state.expression_model().at == frame.body_model().at,
            state.expression_model().expected == frame.body_model().signature.result_type.ty,
            state.branches_model().len() == 0,
    {
        proof { use_type_invariant(&frame); }
        let body = frame.body();
        let next = ScalarExpressionSite { at: body.at, expected: body.signature.result_type.ty };
        Self { frame, next, branches: Vec::new() }
    }

    /// 元の構文木で、次に評価する式を返す。
    pub fn expression(&self) -> (site: ScalarExpressionSite<'a>)
        ensures site == self.expression_model(),
    {
        self.next
    }

    /// 条件を先に評価し、その値が得られたら選んだ分岐に移る。
    ///
    /// 条件式やアトム以外のフォームは、その位置で状態を返す。実行時の整数診断は元の
    /// 文書と式の範囲を保つ。
    ///
    /// # Errors
    ///
    /// 評価した整数リテラルが期待型の表現範囲を超えたときなどに返す。
    pub fn advance(self) -> (step: Result<ScalarExpressionStep<'p, 'a>, ScalarLiteralError<'p, 'a>>)
        ensures self.expression_step_matches(step),
            step matches Ok(ScalarExpressionStep::Complete(value)) ==>
                scalar_fits(value, self.frame_model().body_model().signature.result_type.ty),
    {
        proof { use_type_invariant(&self); }
        let ghost previous = self;
        let Self { frame, next, mut branches } = self;
        if let Some(branch) = frame.condition_at(next) {
            let condition = branch.condition();
            branches.push(branch);
            assert(branches@.take(previous.branches_model().len() as int) =~= previous.branches_model());
            let result = Ok(ScalarExpressionStep::Continue(Self { frame, next: condition, branches }));
            assert(previous.expression_step_matches(result));
            return result;
        }
        let value = match frame.evaluate_atom(next.at, next.expected) {
            Ok(Some(value)) => value,
            Ok(None) => return Ok(ScalarExpressionStep::NeedsForm(Self { frame, next, branches })),
            Err(error) => return Err(error),
        };
        if let Some(branch) = branches.pop() {
            let ScalarValue::Bool(condition) = value else { unreachable!() };
            let selected = branch.select(condition);
            let after = Self { frame, next: selected, branches };
            let result = Ok(ScalarExpressionStep::Continue(after));
            proof {
                assert(previous.branches_model().last() == branch);
                assert(after.branches_model() =~= previous.branches_model().drop_last());
                assert(previous.expression_step_matches(result));
            }
            result
        } else {
            Ok(ScalarExpressionStep::Complete(value))
        }
    }

    /// 条件に降りる、選んだ分岐へ移る、または値・元の診断を返す遷移を表す。
    pub closed spec fn expression_step_matches(
        &self, result: Result<ScalarExpressionStep<'p, 'a>, ScalarLiteralError<'p, 'a>>,
    ) -> bool {
        let frame = self.frame_model();
        let before = self.expression_model();
        let body = frame.body_model();
        let branches = self.branches_model();
        let condition_transition = match result {
            Ok(ScalarExpressionStep::Continue(after)) => {
                let pending = after.branches_model();
                &&& pending.len() == branches.len() + 1
                &&& pending.take(branches.len() as int) == branches
                &&& scalar_condition_matches(body, before, Some(pending.last()))
                &&& after.frame_model() == frame
                &&& after.expression_model().at == pending.last().positions_model().1
                &&& after.expression_model().expected == boolean_type()
            },
            _ => false,
        };
        condition_transition || (scalar_condition_matches(body, before, None) && match result {
            Ok(ScalarExpressionStep::Continue(after)) => {
                let last = branches.last();
                let at = after.expression_model().at;
                &&& branches.len() > 0
                &&& after.frame_model() == frame
                &&& after.branches_model() == branches.drop_last()
                &&& after.expression_model().expected == last.expected_model()
                &&& ((at == last.positions_model().2
                    && scalar_atom_matches(&frame, before.at, before.expected, Ok(Some(ScalarValue::Bool(true)))))
                    || (at == last.positions_model().3
                    && scalar_atom_matches(&frame, before.at, before.expected, Ok(Some(ScalarValue::Bool(false))))))
            },
            Ok(ScalarExpressionStep::Complete(value)) => branches.len() == 0
                && scalar_atom_matches(&frame, before.at, before.expected, Ok(Some(value))),
            Ok(ScalarExpressionStep::NeedsForm(after)) => after.frame_model() == frame
                && after.expression_model() == before && after.branches_model() == branches
                && scalar_atom_matches(&frame, before.at, before.expected, Ok(None)),
            Err(error) => scalar_atom_matches(&frame, before.at, before.expected, Err(error)),
        })
    }
}

}
