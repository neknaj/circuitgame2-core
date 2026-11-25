//! 実行枠で評価を区切り、保存した継続から再開する。

use core::num::NonZeroUsize;
use super::{ScalarExecution, ScalarExecutionError, ScalarExecutionSlice};
#[cfg(verus_only)]
use super::super::scalar_fits;
#[cfg(verus_only)]
use crate::project::{MixedUseAliases, defn_call_plan_matches};
#[cfg(verus_only)]
use super::{scalar_execution_states_observe_same, scalar_execution_steps_observe_same};
use vstd::prelude::*;

verus! {

// 評価が続いた状態だけを保持する。値や診断は最後の遷移で確定する。
#[verifier::opaque]
spec fn execution_path(start: ScalarExecution, path: Seq<ScalarExecution>) -> bool {
    &&& path.len() > 0
    &&& path[0] == start
    &&& forall|i: int, j: int| 0 <= i && j == i + 1 && j < path.len() ==>
        (#[trigger] path[i]).step_matches(Ok(ScalarExecutionSlice::Suspended(#[trigger] path[j])))
}

spec fn execution_path_result<'plan, 'p, 'a>(
    start: ScalarExecution<'plan, 'p, 'a>, fuel: nat, path: Seq<ScalarExecution<'plan, 'p, 'a>>,
    result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
) -> bool {
    &&& execution_path(start, path)
    &&& match result {
        Ok(ScalarExecutionSlice::Suspended(state)) => path.len() == fuel + 1 && path.last() == state,
        _ => path.len() <= fuel && path.last().step_matches(result),
    }
}

/// 実行枠の結果が、指定した回数までの評価遷移に対応することを表す。
pub closed spec fn scalar_execution_slice_matches<'plan, 'p, 'a>(
    start: ScalarExecution<'plan, 'p, 'a>, fuel: nat,
    result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
) -> bool {
    exists|path: Seq<ScalarExecution<'plan, 'p, 'a>>| #[trigger] execution_path_result(start, fuel, path, result)
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 実行枠を使い切ったとき、再開状態の全継続が元の型判断を保つことを示す。
    pub proof fn suspended_slice_preserves_checked_types(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, fuel: nat, after: Self,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()),
            self.preserves_checked_types(aliases),
            scalar_execution_slice_matches(*self, fuel, Ok(ScalarExecutionSlice::Suspended(after))),
        ensures self.plan_model() == after.plan_model(), after.preserves_checked_types(aliases),
    {
        let result = Ok(ScalarExecutionSlice::Suspended(after));
        let path = choose|path: Seq<ScalarExecution<'plan, 'p, 'a>>|
            #[trigger] execution_path_result(*self, fuel, path, result);
        reveal(execution_path);
        checked_types_at_step(false, aliases, *self, path, path.len() - 1);
    }

    /// 対応断片の実行枠は、値、整数の診断、または同じ断片の再開状態を返す。
    pub proof fn supported_slice_does_not_defer(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, fuel: nat,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.preserves_supported_fragment(aliases),
            scalar_execution_slice_matches(*self, fuel, result),
        ensures match result {
            Ok(ScalarExecutionSlice::Suspended(after)) =>
                after.plan_model() == self.plan_model() && after.preserves_supported_fragment(aliases),
            Ok(ScalarExecutionSlice::Complete(_)) | Err(ScalarExecutionError::Literal(_)) => true,
            Err(ScalarExecutionError::Deferred { .. }) => false,
        },
    {
        let path = choose|path: Seq<ScalarExecution<'plan, 'p, 'a>>|
            #[trigger] execution_path_result(*self, fuel, path, result);
        reveal(execution_path);
        checked_types_at_step(true, aliases, *self, path, path.len() - 1);
        let last = path.last();
        assert(last == path[path.len() - 1]);
        if !(result matches Ok(ScalarExecutionSlice::Suspended(_))) {
            last.supported_step_does_not_defer(aliases, result);
        }
    }

    /// 一時停止した実行枠では、使った予算の分だけ残りの一時停止遷移の上限が減る。
    pub proof fn suspended_slice_consumes_continuation_bound(&self, fuel: nat, after: Self)
        requires scalar_execution_slice_matches(*self, fuel, Ok(ScalarExecutionSlice::Suspended(after))),
        ensures after.remaining_continuations_bound() + fuel <= self.remaining_continuations_bound(),
    {
        let result = Ok(ScalarExecutionSlice::Suspended(after));
        let path = choose|path: Seq<ScalarExecution<'plan, 'p, 'a>>|
            #[trigger] execution_path_result(*self, fuel, path, result);
        reveal(execution_path);
        continuation_bound_after_steps(*self, path, path.len() - 1);
        assert(path[path.len() - 1] == after);
    }

    /// 対応断片の実行は、残りの一時停止回数の上限を超える予算で値か整数の診断を返す。
    ///
    /// 複数の正の実行枠を使う場合は、[resumed_scalar_execution_matches] で予算を合成できる。
    pub proof fn supported_slice_finishes_by_continuation_bound(
        &self, aliases: &MixedUseAliases<'_, 'p, 'a>, fuel: nat,
        result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires
            defn_call_plan_matches(aliases, self.plan_model()), self.preserves_supported_fragment(aliases),
            self.remaining_continuations_bound() < fuel,
            scalar_execution_slice_matches(*self, fuel, result),
        ensures (result matches Ok(ScalarExecutionSlice::Complete(_))) || (result matches Err(ScalarExecutionError::Literal(_))),
    {
        self.supported_slice_does_not_defer(aliases, fuel, result);
        if let Ok(ScalarExecutionSlice::Suspended(after)) = result {
            self.suspended_slice_consumes_continuation_bound(fuel, after);
            assert(false);
        }
    }

    /// 一時停止した回数の上限に最後の一遷移を足せば、既に得た終端の結果まで届く。
    pub proof fn terminal_slice_fits_continuation_bound(
        &self, fuel: nat, result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires scalar_execution_slice_matches(*self, fuel, result),
            !(result matches Ok(ScalarExecutionSlice::Suspended(_))),
        ensures scalar_execution_slice_matches(*self, self.remaining_continuations_bound() + 1, result),
    {
        let path = choose|path: Seq<ScalarExecution<'plan, 'p, 'a>>|
            #[trigger] execution_path_result(*self, fuel, path, result);
        reveal(execution_path);
        continuation_bound_after_steps(*self, path, path.len() - 1);
        assert(path.len() <= self.remaining_continuations_bound() + 1);
        assert(execution_path_result(*self, self.remaining_continuations_bound() + 1, path, result));
    }

    /// 予算が一つの実行枠の結果から、実装が行った一遷移を取り出す。
    pub proof fn one_step_slice_matches(
        &self, result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    )
        requires scalar_execution_slice_matches(*self, 1, result),
        ensures self.step_matches(result),
    {
        let path = choose|path: Seq<ScalarExecution<'plan, 'p, 'a>>|
            #[trigger] execution_path_result(*self, 1, path, result);
        reveal(execution_path);
        if let Ok(ScalarExecutionSlice::Suspended(next)) = result {
            assert(path.len() == 2);
            assert(path[0] == *self && path[1] == next);
            assert(path[0].step_matches(Ok(ScalarExecutionSlice::Suspended(path[1]))));
        } else {
            assert(path.len() == 1 && path.last() == *self);
        }
    }
}

// 正の実行枠を繰り返し与えたとき、途中で中断しなければ実際の評価が終端に達することを示す。
#[cfg(verus_only)]
#[allow(dead_code)]
#[verifier::spinoff_prover]
fn run_supported_slices_until_terminal<'plan, 'p, 'a>(
    start: ScalarExecution<'plan, 'p, 'a>, fuel: NonZeroUsize, Ghost(aliases): Ghost<&MixedUseAliases<'_, 'p, 'a>>,
) -> (result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>)
    requires defn_call_plan_matches(aliases, start.plan_model()), start.preserves_supported_fragment(aliases),
    ensures
        (result matches Ok(ScalarExecutionSlice::Complete(_))) || (result matches Err(ScalarExecutionError::Literal(_))),
        scalar_execution_slice_matches(start, start.remaining_continuations_bound() + 1, result),
{
    let mut state = start;
    let ghost mut spent: nat = 0;
    loop
        invariant
            0 < fuel@,
            state.plan_model() == start.plan_model(),
            defn_call_plan_matches(aliases, state.plan_model()),
            state.preserves_supported_fragment(aliases),
            spent == 0 ==> state == start,
            spent > 0 ==> scalar_execution_slice_matches(start, spent, Ok(ScalarExecutionSlice::Suspended(state))),
        decreases state.remaining_continuations_bound(),
    {
        let ghost before = state;
        let result = state.run_slice(fuel);
        let ghost budget = spent + fuel@ as nat;
        proof {
            before.supported_slice_does_not_defer(aliases, fuel@ as nat, result);
            if spent > 0 {
                resumed_scalar_execution_matches(start, spent, before, fuel@ as nat, result);
            }
            assert(scalar_execution_slice_matches(start, budget, result));
        }
        match result {
            Ok(ScalarExecutionSlice::Suspended(after)) => {
                proof {
                    before.suspended_slice_consumes_continuation_bound(fuel@ as nat, after);
                    spent = budget;
                }
                state = after;
            },
            terminal => {
                proof { start.terminal_slice_fits_continuation_bound(budget, terminal); }
                return terminal;
            },
        }
    }
}

proof fn continuation_bound_after_steps(start: ScalarExecution, path: Seq<ScalarExecution>, step: int)
    requires execution_path(start, path), 0 <= step < path.len(),
    ensures path[step].remaining_continuations_bound() + step <= start.remaining_continuations_bound(),
    decreases step,
{
    reveal(execution_path);
    if step > 0 {
        continuation_bound_after_steps(start, path, step - 1);
        let previous = path[step - 1];
        let next = path[step];
        assert(previous.step_matches(Ok(ScalarExecutionSlice::Suspended(next))));
        previous.execution_step_reduces_continuation_bound(next);
    }
}

proof fn checked_types_at_step<'plan, 'p, 'a>(
    supported: bool, aliases: &MixedUseAliases<'_, 'p, 'a>, start: ScalarExecution<'plan, 'p, 'a>,
    path: Seq<ScalarExecution<'plan, 'p, 'a>>, i: int,
)
    requires
        execution_path(start, path), 0 <= i < path.len(),
        defn_call_plan_matches(aliases, start.plan_model()),
        if supported { start.preserves_supported_fragment(aliases) } else { start.preserves_checked_types(aliases) },
    ensures
        path[i].plan_model() == start.plan_model(),
        if supported { path[i].preserves_supported_fragment(aliases) } else { path[i].preserves_checked_types(aliases) },
    decreases i,
{
    reveal(execution_path);
    if i > 0 {
        checked_types_at_step(supported, aliases, start, path, i - 1);
        let previous = path[i - 1];
        let next = path[i];
        assert(previous.step_matches(Ok(ScalarExecutionSlice::Suspended(next))));
        if supported {
            previous.suspended_step_preserves_supported_fragment(aliases, next);
        } else {
            previous.suspended_step_preserves_checked_types(aliases, next);
        }
    }
}

proof fn append_execution_step(
    start: ScalarExecution, path: Seq<ScalarExecution>, next: ScalarExecution,
)
    requires execution_path(start, path), path.last().step_matches(Ok(ScalarExecutionSlice::Suspended(next))),
    ensures execution_path(start, path.push(next)),
{
    reveal(execution_path);
    let extended = path.push(next);
    assert forall|i: int, j: int| 0 <= i && j == i + 1 && j < extended.len()
        implies (#[trigger] extended[i]).step_matches(Ok(ScalarExecutionSlice::Suspended(#[trigger] extended[j]))) by {
        if j < path.len() { assert(path[i].step_matches(Ok(ScalarExecutionSlice::Suspended(path[j])))); }
        else { assert(extended[i] == path.last() && extended[j] == next); }
    };
}

/// 途中で区切って再開した処理を、二つの実行枠を合わせた評価に対応させる。
pub proof fn resumed_scalar_execution_matches<'plan, 'p, 'a>(
    start: ScalarExecution<'plan, 'p, 'a>, first: nat,
    suspended: ScalarExecution<'plan, 'p, 'a>, next: nat,
    result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
)
    requires
        scalar_execution_slice_matches(start, first, Ok(ScalarExecutionSlice::Suspended(suspended))),
        scalar_execution_slice_matches(suspended, next, result),
    ensures scalar_execution_slice_matches(start, first + next, result),
{
    let a = choose|path: Seq<ScalarExecution>| #[trigger] execution_path_result(
        start, first, path, Ok(ScalarExecutionSlice::Suspended(suspended)));
    let b = choose|path: Seq<ScalarExecution>| #[trigger] execution_path_result(suspended, next, path, result);
    reveal(execution_path);
    let joined = a + b.subrange(1, b.len() as int);
    assert(joined[0] == start && joined.last() == b.last());
    assert forall|i: int, j: int| 0 <= i && j == i + 1 && j < joined.len()
        implies (#[trigger] joined[i]).step_matches(Ok(ScalarExecutionSlice::Suspended(#[trigger] joined[j]))) by {
        if j < a.len() {
            assert(a[i].step_matches(Ok(ScalarExecutionSlice::Suspended(a[j]))));
        } else {
            let index = j - a.len() + 1;
            assert(joined[j] == b[index]);
            if j == a.len() {
                assert(joined[i] == a.last());
                assert(a.last() == suspended && suspended == b[0]);
            } else {
                assert(joined[i] == b[index - 1]);
            }
            assert(b[index - 1].step_matches(Ok(ScalarExecutionSlice::Suspended(b[index]))));
        }
    };
    assert(execution_path(start, joined));
    assert(execution_path_result(start, first + next, joined, result));
}

/// 次の遷移が存在し、評価を続ける先も条件を満たす状態から、有限の評価軌跡を構成する。
///
/// `admissible` は評価の途中で保つ条件を表す。値、診断、未対応フォームを返した時点で軌跡が終わる。
pub proof fn finite_scalar_execution_from_progress<'plan, 'p, 'a>(
    start: ScalarExecution<'plan, 'p, 'a>,
    admissible: spec_fn(ScalarExecution<'plan, 'p, 'a>) -> bool,
)
    requires admissible(start),
        forall|state: ScalarExecution<'plan, 'p, 'a>| #[trigger] admissible(state) ==>
            exists|result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>|
                #[trigger] state.step_matches(result) && match result {
                    Ok(ScalarExecutionSlice::Suspended(next)) => admissible(next),
                    _ => true,
                },
    ensures exists|fuel: nat, result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>|
        #[trigger] scalar_execution_slice_matches(start, fuel, result)
            && !(result matches Ok(ScalarExecutionSlice::Suspended(_))),
    decreases start.remaining_work_model().0, start.remaining_work_model().1,
{
    let step = choose|result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>|
        #[trigger] start.step_matches(result) && match result {
            Ok(ScalarExecutionSlice::Suspended(next)) => admissible(next),
            _ => true,
        };
    let initial = seq![start];
    reveal(execution_path);
    assert(execution_path(start, initial));
    match step {
        Ok(ScalarExecutionSlice::Suspended(next)) => {
            start.execution_step_reduces_work(next);
            finite_scalar_execution_from_progress(next, admissible);
            let (fuel, result) = choose|fuel: nat, result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>|
                #[trigger] scalar_execution_slice_matches(next, fuel, result)
                    && !(result matches Ok(ScalarExecutionSlice::Suspended(_)));
            append_execution_step(start, initial, next);
            assert(execution_path_result(start, 1, initial.push(next), step));
            assert(scalar_execution_slice_matches(start, 1, step));
            resumed_scalar_execution_matches(start, 1, next, fuel, result);
        },
        _ => {
            assert(execution_path_result(start, 1, initial, step));
            assert(scalar_execution_slice_matches(start, 1, step));
        },
    }
}

/// 値や診断が確定した実行枠は、枠を広げても同じ結果に対応する。
pub proof fn scalar_execution_terminal_extends<'plan, 'p, 'a>(
    start: ScalarExecution<'plan, 'p, 'a>, fuel: nat, extra: nat,
    result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
)
    requires scalar_execution_slice_matches(start, fuel, result),
        !(result matches Ok(ScalarExecutionSlice::Suspended(_))),
    ensures scalar_execution_slice_matches(start, fuel + extra, result),
{
    let path = choose|path: Seq<ScalarExecution>| #[trigger] execution_path_result(start, fuel, path, result);
    assert(execution_path_result(start, fuel + extra, path, result));
}

proof fn observations_agree_along_paths(
    start_a: ScalarExecution, start_b: ScalarExecution,
    a: Seq<ScalarExecution>, b: Seq<ScalarExecution>, i: int,
)
    requires scalar_execution_states_observe_same(start_a, start_b),
        execution_path(start_a, a), execution_path(start_b, b), 0 <= i < a.len(), i < b.len(),
    ensures scalar_execution_states_observe_same(a[i], b[i]),
    decreases i,
{
    reveal(execution_path);
    if i > 0 {
        observations_agree_along_paths(start_a, start_b, a, b, i - 1);
        let step_a = Ok(ScalarExecutionSlice::Suspended(a[i]));
        let step_b = Ok(ScalarExecutionSlice::Suspended(b[i]));
        assert(a[i - 1].step_matches(step_a) && b[i - 1].step_matches(step_b));
        a[i - 1].observed_steps_agree(b[i - 1], step_a, step_b);
    }
}

/// 観測が一致する二つの初期状態について、完了までの有限な評価軌跡がそれぞれあれば、
/// 終端の値または診断は一致する。実行枠は異なっていてもよい。
pub proof fn finite_scalar_executions_agree<'plan, 'p, 'a>(
    start_a: ScalarExecution<'plan, 'p, 'a>, start_b: ScalarExecution<'plan, 'p, 'a>,
    fuel_a: nat, fuel_b: nat,
    result_a: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
    result_b: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>,
)
    requires
        scalar_execution_states_observe_same(start_a, start_b),
        scalar_execution_slice_matches(start_a, fuel_a, result_a),
        scalar_execution_slice_matches(start_b, fuel_b, result_b),
        !(result_a matches Ok(ScalarExecutionSlice::Suspended(_))),
        !(result_b matches Ok(ScalarExecutionSlice::Suspended(_))),
    ensures scalar_execution_steps_observe_same(result_a, result_b),
{
    let a = choose|path: Seq<ScalarExecution>| #[trigger] execution_path_result(start_a, fuel_a, path, result_a);
    let b = choose|path: Seq<ScalarExecution>| #[trigger] execution_path_result(start_b, fuel_b, path, result_b);
    reveal(execution_path);
    if a.len() < b.len() {
        let i = a.len() - 1;
        observations_agree_along_paths(start_a, start_b, a, b, i);
        let step = Ok(ScalarExecutionSlice::Suspended(b[i + 1]));
        assert(b[i].step_matches(step));
        a[i].observed_steps_agree(b[i], result_a, step);
    } else if b.len() < a.len() {
        let i = b.len() - 1;
        observations_agree_along_paths(start_a, start_b, a, b, i);
        let step = Ok(ScalarExecutionSlice::Suspended(a[i + 1]));
        assert(a[i].step_matches(step));
        a[i].observed_steps_agree(b[i], step, result_b);
    } else {
        let i = a.len() - 1;
        observations_agree_along_paths(start_a, start_b, a, b, i);
        a[i].observed_steps_agree(b[i], result_a, result_b);
    }
}

impl<'plan, 'p, 'a> ScalarExecution<'plan, 'p, 'a> {
    /// 途中の継続を保ち、指定した正の回数まで評価を進める。
    ///
    /// 真偽値と固定長整数のアトム、`if`、補助関数への呼び出しを評価できる。
    ///
    /// # Errors
    ///
    /// 評価した式の整数診断、または評価対象外のフォームや型を元の位置とともに返す。
    pub fn run_slice(self, fuel: NonZeroUsize)
        -> (step: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>)
        ensures scalar_execution_slice_matches(self, fuel@ as nat, step),
            match step {
                Ok(ScalarExecutionSlice::Suspended(state)) => state.result_type_model() == self.result_type_model(),
                Ok(ScalarExecutionSlice::Complete(value)) => scalar_fits(value, self.result_type_model()),
                Err(_) => true,
            },
    {
        let budget = fuel.get();
        let mut remaining = budget;
        let ghost start = self;
        let mut state = self;
        let ghost mut path = seq![state];
        assert(execution_path(start, path)) by { reveal(execution_path); };
        while remaining != 0
            invariant
                remaining <= budget == fuel@,
                start == self,
                state.result_type_model() == self.result_type_model(),
                path.len() == budget - remaining + 1,
                path.last() == state,
                execution_path(start, path),
            decreases remaining,
        {
            match state.step() {
                Ok(ScalarExecutionSlice::Suspended(next)) => {
                    proof {
                        append_execution_step(start, path, next);
                        path = path.push(next);
                    }
                    state = next;
                },
                Ok(ScalarExecutionSlice::Complete(value)) => {
                    let result = Ok(ScalarExecutionSlice::Complete(value));
                    assert(execution_path_result(start, fuel@ as nat, path, result));
                    assert(scalar_execution_slice_matches(start, fuel@ as nat, result));
                    return result;
                },
                Err(error) => {
                    let result = Err(error);
                    assert(execution_path_result(start, fuel@ as nat, path, result));
                    assert(scalar_execution_slice_matches(start, fuel@ as nat, result));
                    return result;
                },
            }
            remaining -= 1;
        }
        let result = Ok(ScalarExecutionSlice::Suspended(state));
        assert(execution_path_result(start, fuel@ as nat, path, result));
        result
    }
}

}
