//! 実行枠で評価を区切り、保存した継続から再開する。

use core::num::NonZeroUsize;
use super::{ScalarExecution, ScalarExecutionError, ScalarExecutionSlice};
#[cfg(verus_only)]
use super::super::scalar_fits;
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
