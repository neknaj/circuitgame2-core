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
    cursor: ScalarCursor<'p, 'a>,
}

// 呼び出し中に保存する式の位置。仮引数の環境はアクティブな側だけが保持する。
pub(super) struct ScalarCursor<'p, 'a> {
    next: ScalarExpressionSite<'a>,
    branches: Vec<ScalarCondition<'a>>,
    result_type: DataType<'a>,
    origin: Ghost<ScalarCallFrame<'p, 'a>>,
}

/// スカラー式の評価を一つ進めた結果。
pub enum ScalarExpressionStep<'p, 'a> {
    /// 次に評価する条件または選んだ分岐が決まった。
    Continue(ScalarExpression<'p, 'a>),
    /// 式の値が得られ、評価に使った環境を返せる。
    Complete {
        /// 式が返した値。
        value: ScalarValue,
        /// 式が参照した仮引数の環境。
        frame: ScalarCallFrame<'p, 'a>,
    },
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

impl<'p, 'a> ScalarCursor<'p, 'a> {
    pub(super) closed spec fn position_model(&self) -> ScalarExpressionSite<'a> { self.next }

    pub(super) closed spec fn result_type_model(&self) -> DataType<'a> { self.result_type }

    pub(super) closed spec fn fits(&self, frame: &ScalarCallFrame<'p, 'a>) -> bool {
        let body = frame.body_model();
        &&& self.origin@ == *frame
        &&& self.next.at < body.forms@.len()
        &&& self.next.expected == if self.branches@.len() == 0 { self.result_type } else { boolean_type() }
        &&& forall|i: int| 0 <= i < self.branches@.len() ==> {
            let branch = #[trigger] self.branches@[i];
            &&& branch_in_bounds(branch, body.forms@.len())
            &&& scalar_condition_matches(body, ScalarExpressionSite {
                at: branch.positions_model().0, expected: branch.expected_model(),
            }, Some(branch))
            &&& branch.expected_model() == if i == 0 { self.result_type } else { boolean_type() }
        }
    }
}

impl<'p, 'a> ScalarExpression<'p, 'a> {
    #[verifier::type_invariant]
    spec fn positions_fit(&self) -> bool {
        self.cursor.fits(&self.frame)
    }

    pub(super) closed spec fn cursor_model(&self) -> ScalarCursor<'p, 'a> { self.cursor }

    /// 式の値が満たす型を表す。
    pub closed spec fn result_type_model(&self) -> DataType<'a> { self.cursor.result_type }

    /// 条件や分岐を置いた、元の本体と仮引数の環境を表す。
    pub closed spec fn frame_model(&self) -> ScalarCallFrame<'p, 'a> { self.frame }

    /// 現在評価する位置と、値に求める型を表す。
    pub closed spec fn expression_model(&self) -> ScalarExpressionSite<'a> { self.cursor.next }

    /// 条件の値を待つ継続を、深さの浅い側から表す。
    pub closed spec fn branches_model(&self) -> Seq<ScalarCondition<'a>> { self.cursor.branches@ }

    /// 型付きの本体を評価する。開始時には条件を待つ継続を持たない。
    pub fn start(frame: ScalarCallFrame<'p, 'a>) -> (state: Self)
        ensures state.frame_model() == frame,
            state.expression_model().at == frame.body_model().at,
            state.expression_model().expected == frame.body_model().signature.result_type.ty,
            state.branches_model().len() == 0,
            state.result_type_model() == frame.body_model().signature.result_type.ty,
    {
        proof { use_type_invariant(&frame); }
        let body = frame.body();
        let next = ScalarExpressionSite { at: body.at, expected: body.signature.result_type.ty };
        Self::start_at(frame, next)
    }

    pub(super) fn start_at(frame: ScalarCallFrame<'p, 'a>, site: ScalarExpressionSite<'a>)
        -> (state: Self)
        requires site.at < frame.body_model().forms@.len(),
        ensures state.frame_model() == frame, state.expression_model() == site,
            state.result_type_model() == site.expected, state.branches_model().len() == 0,
    {
        let origin = Ghost(frame);
        Self { frame, cursor: ScalarCursor { next: site, branches: Vec::new(), result_type: site.expected, origin } }
    }

    pub(super) fn into_parts(self) -> (parts: (ScalarCallFrame<'p, 'a>, ScalarCursor<'p, 'a>))
        ensures
            parts == (self.frame_model(), self.cursor_model()),
            parts.1.fits(&parts.0),
            parts.1.position_model() == self.expression_model(),
            parts.1.result_type_model() == self.result_type_model(),
    {
        proof { use_type_invariant(&self); }
        (self.frame, self.cursor)
    }

    pub(super) fn restore(frame: ScalarCallFrame<'p, 'a>, cursor: ScalarCursor<'p, 'a>) -> (state: Self)
        requires cursor.fits(&frame),
        ensures state.frame_model() == frame, state.cursor_model() == cursor,
            state.expression_model() == cursor.position_model(),
            state.result_type_model() == cursor.result_type_model(),
    {
        Self { frame, cursor }
    }

    /// 元の構文木で、次に評価する式を返す。
    pub fn expression(&self) -> (site: ScalarExpressionSite<'a>)
        ensures site == self.expression_model(),
    {
        self.cursor.next
    }

    pub(super) closed spec fn receive_matches(
        &self, value: ScalarValue, step: ScalarExpressionStep<'p, 'a>,
    ) -> bool {
        let branches = self.branches_model();
        let frame = self.frame_model();
        if branches.len() == 0 {
            step matches ScalarExpressionStep::Complete { value: completed, frame: entered }
                && completed == value && entered == frame
        } else {
            let last = branches.last();
            match (step, value) {
                (ScalarExpressionStep::Continue(after), ScalarValue::Bool(condition)) =>
                    after.frame_model() == frame
                    && after.result_type_model() == self.result_type_model()
                    && after.branches_model() == branches.drop_last()
                    && after.expression_model().expected == last.expected_model()
                    && after.expression_model().at == (if condition { last.positions_model().2 } else { last.positions_model().3 }),
                _ => false,
            }
        }
    }

    pub(super) fn receive(self, value: ScalarValue) -> (step: ScalarExpressionStep<'p, 'a>)
        requires scalar_fits(value, self.expression_model().expected),
        ensures self.receive_matches(value, step),
            match step {
                ScalarExpressionStep::Complete { value, frame } =>
                    scalar_fits(value, self.result_type_model()) && frame == self.frame_model(),
                ScalarExpressionStep::Continue(after) =>
                    after.frame_model() == self.frame_model() && after.result_type_model() == self.result_type_model(),
                ScalarExpressionStep::NeedsForm(_) => false,
            },
    {
        proof { use_type_invariant(&self); }
        let ghost previous = self;
        let Self { frame, cursor: ScalarCursor { mut branches, result_type, origin, .. } } = self;
        if let Some(branch) = branches.pop() {
            let ScalarValue::Bool(condition) = value else { unreachable!() };
            let next = branch.select(condition);
            assert(previous.branches_model().last() == branch);
            assert(branches@ =~= previous.branches_model().drop_last());
            ScalarExpressionStep::Continue(Self { frame, cursor: ScalarCursor { next, branches, result_type, origin } })
        } else {
            ScalarExpressionStep::Complete { value, frame }
        }
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
            step matches Ok(ScalarExpressionStep::Complete { value, frame }) ==>
                scalar_fits(value, self.result_type_model()) && frame == self.frame_model(),
    {
        proof { use_type_invariant(&self); }
        let ghost previous = self;
        let (frame, ScalarCursor { next, mut branches, result_type, origin }) = self.into_parts();
        if let Some(branch) = frame.condition_at(next) {
            let condition = branch.condition();
            branches.push(branch);
            assert(branches@.take(previous.branches_model().len() as int) =~= previous.branches_model());
            let result = Ok(ScalarExpressionStep::Continue(Self { frame, cursor: ScalarCursor { next: condition, branches, result_type, origin } }));
            assert(previous.expression_step_matches(result));
            return result;
        }
        let value = match frame.evaluate_atom(next.at, next.expected) {
            Ok(Some(value)) => value,
            Ok(None) => return Ok(ScalarExpressionStep::NeedsForm(Self { frame, cursor: ScalarCursor { next, branches, result_type, origin } })),
            Err(error) => return Err(error),
        };
        let at = Self::restore(frame, ScalarCursor { next, branches, result_type, origin });
        let step = at.receive(value);
        assert(previous.receive_matches(value, step));
        Ok(step)
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
                &&& after.result_type_model() == self.result_type_model()
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
                &&& after.result_type_model() == self.result_type_model()
                &&& after.branches_model() == branches.drop_last()
                &&& after.expression_model().expected == last.expected_model()
                &&& ((at == last.positions_model().2
                    && scalar_atom_matches(&frame, before.at, before.expected, Ok(Some(ScalarValue::Bool(true)))))
                    || (at == last.positions_model().3
                    && scalar_atom_matches(&frame, before.at, before.expected, Ok(Some(ScalarValue::Bool(false))))))
            },
            Ok(ScalarExpressionStep::Complete { value, frame: entered }) => branches.len() == 0
                && entered == frame && scalar_atom_matches(&frame, before.at, before.expected, Ok(Some(value))),
            Ok(ScalarExpressionStep::NeedsForm(after)) => after.frame_model() == frame
                && after.result_type_model() == self.result_type_model()
                && after.expression_model() == before && after.branches_model() == branches
                && scalar_atom_matches(&frame, before.at, before.expected, Ok(None)),
            Err(error) => scalar_atom_matches(&frame, before.at, before.expected, Err(error)),
        })
    }
}

}
