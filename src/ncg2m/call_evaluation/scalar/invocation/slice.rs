//! 準備済みの呼び出しを、続きから実行できる枠に区切る。

use core::num::NonZeroUsize;
#[cfg(verus_only)]
use super::{invocation_errors_agree, invocation_states_agree, invocation_steps_agree};
use super::{ScalarCallFrame, ScalarInvocation, ScalarInvocationError, ScalarInvocationStep};
use vstd::prelude::*;

verus! {

/// 実行枠の終了時点での、呼び出しの進み具合。
pub enum ScalarInvocationSlice<'plan, 'p, 'a> {
    /// 呼び出し先へ移る前の再開用の状態。
    Suspended(ScalarInvocation<'plan, 'p, 'a>),
    /// 全引数がそろい、呼び出し先の本体の評価を始められる。
    Enter {
        /// 呼び出し先の順位。
        rank: usize,
        /// 呼び出し先の本体と仮引数の環境。
        frame: ScalarCallFrame<'p, 'a>,
    },
}

#[verifier::opaque]
spec fn invocation_path<'plan, 'p, 'a>(
    start: ScalarInvocation<'plan, 'p, 'a>, path: Seq<ScalarInvocation<'plan, 'p, 'a>>,
) -> bool {
    &&& path.len() > 0
    &&& path[0] == start
    &&& forall|i: int, j: int| 0 <= i && j == i + 1 && j < path.len() ==>
        (#[trigger] path[i]).advance_matches(Ok(ScalarInvocationStep::Continue(#[trigger] path[j])))
}

spec fn invocation_slice_path<'plan, 'p, 'a>(
    start: ScalarInvocation<'plan, 'p, 'a>, fuel: nat, path: Seq<ScalarInvocation<'plan, 'p, 'a>>,
    result: Result<ScalarInvocationSlice<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>,
) -> bool {
    &&& invocation_path(start, path)
    &&& match result {
        Ok(ScalarInvocationSlice::Suspended(state)) => path.len() == fuel + 1 && path.last() == state,
        Ok(ScalarInvocationSlice::Enter { rank, frame }) => path.len() <= fuel
            && path.last().advance_matches(Ok(ScalarInvocationStep::Enter { rank, frame })),
        Err(error) => path.len() <= fuel && path.last().advance_matches(Err(error)),
    }
}

/// 実行枠が、元の呼び出しから指定回数まで進んだ結果を表す。
pub closed spec fn invocation_slice_matches<'plan, 'p, 'a>(
    start: ScalarInvocation<'plan, 'p, 'a>, fuel: nat,
    result: Result<ScalarInvocationSlice<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>,
) -> bool {
    exists|path: Seq<ScalarInvocation<'plan, 'p, 'a>>|
        #[trigger] invocation_slice_path(start, fuel, path, result)
}

proof fn invocation_path_extend<'plan, 'p, 'a>(
    start: ScalarInvocation<'plan, 'p, 'a>, path: Seq<ScalarInvocation<'plan, 'p, 'a>>,
    next: ScalarInvocation<'plan, 'p, 'a>,
)
    requires invocation_path(start, path),
        path.last().advance_matches(Ok(ScalarInvocationStep::Continue(next))),
    ensures invocation_path(start, path.push(next)),
{
    reveal(invocation_path);
    let extended = path.push(next);
    assert forall|i: int, j: int| 0 <= i && j == i + 1 && j < extended.len()
        implies (#[trigger] extended[i]).advance_matches(Ok(ScalarInvocationStep::Continue(#[trigger] extended[j]))) by {
        if j < path.len() { assert(path[i].advance_matches(Ok(ScalarInvocationStep::Continue(path[j])))); }
        else { assert(extended[i] == path.last() && extended[j] == next); }
    };
}

impl<'plan, 'p, 'a> ScalarInvocation<'plan, 'p, 'a> {
    /// 指定した正の回数を上限に引数評価を進め、次の本体か再開用の状態を返す。
    ///
    /// 一つの遷移は引数一つの評価か、全引数を受け取った呼び出し先への移動に当たる。
    ///
    /// # Errors
    ///
    /// 最初に評価できなかった引数の元位置と理由を返す。
    pub fn run_slice(self, fuel: NonZeroUsize)
        -> (result: Result<ScalarInvocationSlice<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>)
        ensures invocation_slice_matches(self, fuel@ as nat, result),
    {
        let budget = fuel.get();
        let mut remaining = budget;
        let ghost start = self;
        let mut current = self;
        let ghost mut path = seq![current];
        assert(invocation_path(start, path)) by { reveal(invocation_path); };
        while remaining > 0
            invariant
                remaining <= budget == fuel@,
                start == self,
                invocation_path(start, path),
                path.len() == budget - remaining + 1,
                path.last() == current,
            decreases remaining,
        {
            match current.advance() {
                Ok(ScalarInvocationStep::Continue(next)) => {
                    proof {
                        invocation_path_extend(start, path, next);
                        path = path.push(next);
                    }
                    current = next;
                    remaining -= 1;
                }
                Ok(ScalarInvocationStep::Enter { rank, frame }) => {
                    let result = Ok(ScalarInvocationSlice::Enter { rank, frame });
                    assert(invocation_slice_path(start, fuel@ as nat, path, result));
                    assert(invocation_slice_matches(start, fuel@ as nat, result));
                    return result;
                }
                Err(error) => {
                    let result = Err(error);
                    assert(invocation_slice_path(start, fuel@ as nat, path, result));
                    assert(invocation_slice_matches(start, fuel@ as nat, result));
                    return result;
                }
            }
        }
        let result = Ok(ScalarInvocationSlice::Suspended(current));
        assert(invocation_slice_path(start, budget as nat, path, result));
        result
    }
}

/// 保留した呼び出しを次の枠で再開した結果が、両方の枠を合わせた遷移列に対応することを示す。
pub proof fn resumed_invocation_slices_match<'plan, 'p, 'a>(
    start: ScalarInvocation<'plan, 'p, 'a>, first_fuel: nat,
    suspended: ScalarInvocation<'plan, 'p, 'a>, next_fuel: nat,
    result: Result<ScalarInvocationSlice<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>,
)
    requires
        invocation_slice_matches(start, first_fuel, Ok(ScalarInvocationSlice::Suspended(suspended))),
        invocation_slice_matches(suspended, next_fuel, result),
    ensures invocation_slice_matches(start, first_fuel + next_fuel, result),
{
    let left = choose|path: Seq<ScalarInvocation<'plan, 'p, 'a>>|
        #[trigger] invocation_slice_path(start, first_fuel, path, Ok(ScalarInvocationSlice::Suspended(suspended)));
    let right = choose|path: Seq<ScalarInvocation<'plan, 'p, 'a>>|
        #[trigger] invocation_slice_path(suspended, next_fuel, path, result);
    reveal(invocation_path);
    let joined = left + right.subrange(1, right.len() as int);
    assert(joined[0] == start && joined.last() == right.last());
    assert forall|i: int, j: int| 0 <= i && j == i + 1 && j < joined.len()
        implies (#[trigger] joined[i]).advance_matches(Ok(ScalarInvocationStep::Continue(#[trigger] joined[j]))) by {
        if j < left.len() {
            assert(left[i].advance_matches(Ok(ScalarInvocationStep::Continue(left[j]))));
        } else {
            let right_index = j - left.len() + 1;
            assert(joined[j] == right[right_index]);
            if j == left.len() {
                assert(joined[i] == left.last());
                assert(left.last() == suspended && suspended == right[0]);
            } else {
                assert(joined[i] == right[right_index - 1]);
            }
            assert(right[right_index - 1].advance_matches(Ok(ScalarInvocationStep::Continue(right[right_index]))));
        }
    };
    assert(invocation_path(start, joined));
    assert(invocation_slice_path(start, first_fuel + next_fuel, joined, result));
}


/// 呼び出し先への移動か診断に達した結果は、実行枠を広げても変わらない。
pub proof fn invocation_terminal_slice_extends<'plan, 'p, 'a>(
    start: ScalarInvocation<'plan, 'p, 'a>, fuel: nat, extra: nat,
    result: Result<ScalarInvocationSlice<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>,
)
    requires invocation_slice_matches(start, fuel, result),
        !(result matches Ok(ScalarInvocationSlice::Suspended(_))),
    ensures invocation_slice_matches(start, fuel + extra, result),
{
    let path = choose|path: Seq<ScalarInvocation<'plan, 'p, 'a>>|
        #[trigger] invocation_slice_path(start, fuel, path, result);
    assert(invocation_slice_path(start, fuel + extra, path, result));
}

/// 二つの枠の実行結果が、再開時の状態、進入先の環境、または最初の診断まで一致する。
pub open spec fn invocation_slice_results_agree(
    first: Result<ScalarInvocationSlice, ScalarInvocationError>,
    second: Result<ScalarInvocationSlice, ScalarInvocationError>,
) -> bool {
    match (first, second) {
        (Ok(ScalarInvocationSlice::Suspended(a)), Ok(ScalarInvocationSlice::Suspended(b))) =>
            invocation_states_agree(a, b),
        (Ok(ScalarInvocationSlice::Enter { rank: a, frame: left }),
            Ok(ScalarInvocationSlice::Enter { rank: b, frame: right })) =>
            a == b && left.body_model() == right.body_model()
                && left.parameter_values_model() == right.parameter_values_model(),
        (Err(a), Err(b)) => invocation_errors_agree(a, b),
        _ => false,
    }
}

spec fn terminal_step<'plan, 'p, 'a>(
    result: Result<ScalarInvocationSlice<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>,
) -> Result<ScalarInvocationStep<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>> {
    match result {
        Ok(ScalarInvocationSlice::Enter { rank, frame }) => Ok(ScalarInvocationStep::Enter { rank, frame }),
        Ok(ScalarInvocationSlice::Suspended(state)) => Ok(ScalarInvocationStep::Continue(state)),
        Err(error) => Err(error),
    }
}

proof fn invocation_prefix_agrees(
    start: ScalarInvocation, left: Seq<ScalarInvocation>, right: Seq<ScalarInvocation>, i: int,
)
    requires invocation_path(start, left), invocation_path(start, right),
        0 <= i < left.len(), i < right.len(),
    ensures invocation_states_agree(left[i], right[i]),
    decreases i,
{
    reveal(invocation_path);
    if i > 0 {
        invocation_prefix_agrees(start, left, right, i - 1);
        let a = Ok(ScalarInvocationStep::Continue(left[i]));
        let b = Ok(ScalarInvocationStep::Continue(right[i]));
        assert(left[i - 1].advance_matches(a) && right[i - 1].advance_matches(b));
        invocation_steps_agree(left[i - 1], right[i - 1], a, b);
    }
}

proof fn invocation_paths_same_length(
    start: ScalarInvocation, fuel: nat, left: Seq<ScalarInvocation>, right: Seq<ScalarInvocation>,
    first: Result<ScalarInvocationSlice, ScalarInvocationError>,
    second: Result<ScalarInvocationSlice, ScalarInvocationError>,
)
    requires invocation_slice_path(start, fuel, left, first), invocation_slice_path(start, fuel, right, second),
        left.len() <= right.len(),
    ensures left.len() == right.len(),
{
    reveal(invocation_path);
    if left.len() < right.len() {
        let i = left.len() - 1;
        invocation_prefix_agrees(start, left, right, i);
        assert(!(first matches Ok(ScalarInvocationSlice::Suspended(_))));
        let a = terminal_step(first);
        let b = Ok(ScalarInvocationStep::Continue(right[i + 1]));
        assert(left[i].advance_matches(a) && right[i].advance_matches(b));
        invocation_steps_agree(left[i], right[i], a, b);
    }
}

/// 同じ再開状態に同じ実行枠を与えると、実行結果は一意に定まる。
pub proof fn invocation_slice_is_deterministic<'plan, 'p, 'a>(
    start: ScalarInvocation<'plan, 'p, 'a>, fuel: nat,
    first: Result<ScalarInvocationSlice<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>,
    second: Result<ScalarInvocationSlice<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>,
)
    requires invocation_slice_matches(start, fuel, first), invocation_slice_matches(start, fuel, second),
    ensures invocation_slice_results_agree(first, second),
{
    let left = choose|path: Seq<ScalarInvocation<'plan, 'p, 'a>>|
        #[trigger] invocation_slice_path(start, fuel, path, first);
    let right = choose|path: Seq<ScalarInvocation<'plan, 'p, 'a>>|
        #[trigger] invocation_slice_path(start, fuel, path, second);
    reveal(invocation_path);
    if left.len() <= right.len() {
        invocation_paths_same_length(start, fuel, left, right, first, second);
    } else {
        invocation_paths_same_length(start, fuel, right, left, second, first);
    }
    invocation_prefix_agrees(start, left, right, left.len() - 1);
    if left.len() <= fuel {
        invocation_steps_agree(left.last(), right.last(), terminal_step(first), terminal_step(second));
    }
}

}
