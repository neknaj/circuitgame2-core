//! スカラー式の条件評価と分岐選択を途中から再開する。

use super::{
    DataType, ScalarCallFrame, ScalarCondition,
    ScalarExpressionSite, ScalarLiteralError, ScalarValue,
};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use super::{BuiltinDataType, DataTypeAtom, scalar_condition_matches, scalar_fits};
#[cfg(verus_only)]
use super::atom::{scalar_atom_matches, scalar_atoms_observe_same};
#[cfg(verus_only)]
use super::condition::conditional_results_observe_same;
#[cfg(verus_only)]
use super::execution::observation::{
    condition_parts_agree, conditions_agree, cursors_agree, expressions_agree, frames_agree, positions_agree,
    type_spelling_agrees,
};

#[cfg(verus_only)]
mod progress;
#[cfg(verus_only)]
mod termination;

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

    pub(super) closed spec fn branches_model(&self) -> Seq<ScalarCondition<'a>> { self.branches@ }

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
            frame.has_locally_checked_site(ScalarExpressionSite {
                at: frame.body_model().at, expected: frame.body_model().signature.result_type.ty,
            }) ==> state.is_locally_checked(),
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
            frame.has_locally_checked_site(site) ==> state.is_locally_checked(),
    {
        proof { use_type_invariant(&frame); }
        let origin = Ghost(frame);
        let state = Self { frame, cursor: ScalarCursor { next: site, branches: Vec::new(), result_type: site.expected, origin } };
        proof {
            if frame.has_locally_checked_site(site) {
                state.starts_at_locally_checked_site();
            }
        }
        state
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
            site.at < self.frame_model().body_model().forms@.len(),
    {
        proof { use_type_invariant(self); }
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
                    && after.cursor.origin@ == self.cursor.origin@
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
            match step {
                Ok(ScalarExpressionStep::Continue(after)) => {
                    &&& after.frame_model() == self.frame_model()
                    &&& after.result_type_model() == self.result_type_model()
                },
                Ok(ScalarExpressionStep::Complete { value, frame }) =>
                    scalar_fits(value, self.result_type_model()) && frame == self.frame_model(),
                Ok(ScalarExpressionStep::NeedsForm(after)) => {
                    &&& after.frame_model() == self.frame_model()
                    &&& after.result_type_model() == self.result_type_model()
                    &&& after.expression_model() == self.expression_model()
                },
                Err(_) => true,
            },
    {
        proof {
            use_type_invariant(&self);
            reveal(ScalarExpression::expression_step_matches);
        }
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

    spec fn condition_entry_matches(&self, after: Self) -> bool {
        let pending = after.branches_model();
        let branches = self.branches_model();
        &&& pending.len() == branches.len() + 1
        &&& pending.take(branches.len() as int) == branches
        &&& scalar_condition_matches(self.frame_model().body_model(), self.expression_model(), Some(pending.last()))
        &&& after.frame_model() == self.frame_model()
        &&& after.cursor.origin@ == self.cursor.origin@
        &&& after.result_type_model() == self.result_type_model()
        &&& after.expression_model().at == pending.last().positions_model().1
        &&& after.expression_model().expected == boolean_type()
    }

    spec fn atom_transition_matches(
        &self, atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>,
        step: Result<ScalarExpressionStep<'p, 'a>, ScalarLiteralError<'p, 'a>>,
    ) -> bool {
        match atom {
            Ok(Some(value)) => step matches Ok(next) && self.receive_matches(value, next),
            Ok(None) => step matches Ok(ScalarExpressionStep::NeedsForm(after)) && expression_positions_agree(*self, after),
            Err(error) => step == Err(error),
        }
    }

    /// 条件に降りる、選んだ分岐へ移る、または値・元の診断を返す遷移を表す。
    #[verifier::opaque]
    pub closed spec fn expression_step_matches(
        &self, result: Result<ScalarExpressionStep<'p, 'a>, ScalarLiteralError<'p, 'a>>,
    ) -> bool {
        let frame = self.frame_model();
        let before = self.expression_model();
        let body = frame.body_model();
        ||| (result matches Ok(ScalarExpressionStep::Continue(after)) && self.condition_entry_matches(after))
        ||| (scalar_condition_matches(body, before, None)
            && exists|atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>|
                #[trigger] scalar_atom_matches(&frame, before.at, before.expected, atom)
                    && self.atom_transition_matches(atom, result))
    }

    pub(super) proof fn restored_cursors_observe_same(&self, other: Self)
        requires expressions_agree(*self, other),
        ensures cursors_agree(self.cursor_model(), other.cursor_model()),
    {}

    pub(super) proof fn restored_expressions_observe_same(&self, other: Self)
        requires frames_agree(self.frame_model(), other.frame_model()), cursors_agree(self.cursor_model(), other.cursor_model()),
        ensures expressions_agree(*self, other),
    {}

    pub(super) proof fn received_steps_agree(
        &self, other: Self, value: ScalarValue, first: ScalarExpressionStep<'p, 'a>, second: ScalarExpressionStep<'p, 'a>,
    )
        requires expressions_agree(*self, other),
            self.receive_matches(value, first), other.receive_matches(value, second),
        ensures observed_expression_steps_agree(Ok(first), Ok(second)),
    {
        let a = self.branches_model();
        let b = other.branches_model();
        if a.len() > 0 {
            corresponding_conditions_agree(a, b, a.len() - 1);
            assert(conditions_agree(a.drop_last(), b.drop_last())) by {
                let left = a.drop_last();
                let right = b.drop_last();
                assert forall|i: int| 0 <= i < left.len()
                    implies condition_parts_agree(#[trigger] left[i], #[trigger] right[i]) by {
                    corresponding_conditions_agree(a, b, i);
                };
            };
        }
    }

    pub(super) proof fn expression_steps_agree(
        &self, other: Self,
        first: Result<ScalarExpressionStep<'p, 'a>, ScalarLiteralError<'p, 'a>>,
        second: Result<ScalarExpressionStep<'p, 'a>, ScalarLiteralError<'p, 'a>>,
    )
        requires expressions_agree(*self, other),
            self.expression_step_matches(first), other.expression_step_matches(second),
        ensures observed_expression_steps_agree(first, second),
    {
        reveal(ScalarExpression::expression_step_matches);
        let frame_a = self.frame_model();
        let frame_b = other.frame_model();
        let site_a = self.expression_model();
        let site_b = other.expression_model();
        let body_a = frame_a.body_model();
        let body_b = frame_b.body_model();
        let left_entry = match first {
            Ok(ScalarExpressionStep::Continue(after)) if self.condition_entry_matches(after) => Some(after),
            _ => None,
        };
        let right_entry = match second {
            Ok(ScalarExpressionStep::Continue(after)) if other.condition_entry_matches(after) => Some(after),
            _ => None,
        };
        if let Some(left) = left_entry {
            let condition = Some(left.branches_model().last());
            if let Some(right) = right_entry {
                conditional_results_observe_same(body_a, body_b, site_a, site_b, condition, Some(right.branches_model().last()));
                let a = self.branches_model();
                let b = other.branches_model();
                let left = left.branches_model();
                let right = right.branches_model();
                assert forall|i: int| 0 <= i < left.len() implies condition_parts_agree(#[trigger] left[i], #[trigger] right[i]) by {
                    if i < a.len() {
                        corresponding_conditions_agree(a, b, i);
                        assert(left.take(a.len() as int)[i] == a[i] && right.take(b.len() as int)[i] == b[i]);
                    } else {
                        assert(left[i] == left.last() && right[i] == right.last());
                    }
                };
            } else {
                conditional_results_observe_same(body_a, body_b, site_a, site_b, condition, None);
            }
        } else if let Some(right) = right_entry {
            conditional_results_observe_same(body_a, body_b, site_a, site_b, None, Some(right.branches_model().last()));
        } else {
            let a = choose|atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>|
                #[trigger] scalar_atom_matches(&frame_a, site_a.at, site_a.expected, atom)
                    && self.atom_transition_matches(atom, first);
            let b = choose|atom: Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>>|
                #[trigger] scalar_atom_matches(&frame_b, site_b.at, site_b.expected, atom)
                    && other.atom_transition_matches(atom, second);
            scalar_atoms_observe_same(&frame_a, &frame_b, site_a.at, site_a.expected, site_b.expected, a, b);
            if let Ok(Some(value)) = a {
                self.received_steps_agree(other, value, first->Ok_0, second->Ok_0);
            }
        }
    }
}

proof fn corresponding_conditions_agree(left: Seq<ScalarCondition>, right: Seq<ScalarCondition>, i: int)
    requires conditions_agree(left, right), 0 <= i < left.len(),
    ensures condition_parts_agree(left[i], right[i]),
{
    if left != right {
        assert(0 <= i < right.len());
        assert(condition_parts_agree(left[i], right[i]));
    }
}

pub(super) open spec fn expression_positions_agree(left: ScalarExpression, right: ScalarExpression) -> bool {
    &&& left.frame_model() == right.frame_model()
    &&& left.expression_model() == right.expression_model()
    &&& left.branches_model() == right.branches_model()
    &&& left.result_type_model() == right.result_type_model()
}

pub(super) open spec fn literal_errors_agree(left: ScalarLiteralError, right: ScalarLiteralError) -> bool {
    *left.source == *right.source && left.span == right.span && left.error == right.error
}

pub(super) open spec fn observed_expression_steps_agree(
    first: Result<ScalarExpressionStep, ScalarLiteralError>,
    second: Result<ScalarExpressionStep, ScalarLiteralError>,
) -> bool {
    match (first, second) {
        (Ok(ScalarExpressionStep::Continue(left)), Ok(ScalarExpressionStep::Continue(right)))
        | (Ok(ScalarExpressionStep::NeedsForm(left)), Ok(ScalarExpressionStep::NeedsForm(right))) =>
            expressions_agree(left, right),
        (Ok(ScalarExpressionStep::Complete { frame: left, value: a }),
            Ok(ScalarExpressionStep::Complete { frame: right, value: b })) => frames_agree(left, right) && a == b,
        (Err(left), Err(right)) => literal_errors_agree(left, right),
        _ => false,
    }
}

}
