//! 呼び出し順位と構文木の添字から、評価する式の順序と仕事量を定める。

use vstd::arithmetic::mul::lemma_mul_inequality;
use vstd::prelude::*;

verus! {

/// 呼び出し順位を優先し、同じ順位では後ろの式ほど小さくなる自然数を返す。
pub(super) open spec fn scalar_expression_order(rank: usize, at: usize) -> nat {
    let width = usize::MAX as nat + 1;
    rank as nat * width + (usize::MAX as nat - at as nat) as nat
}

/// 同じ本体の部分式や、順位の低い呼び出し先に進むと、式の順序が厳密に減る。
pub(super) proof fn scalar_subexpression_order(parent_rank: usize, parent: usize, child_rank: usize, child: usize)
    requires child_rank < parent_rank || (child_rank == parent_rank && parent < child),
    ensures scalar_expression_order(child_rank, child) < scalar_expression_order(parent_rank, parent),
{
    if child_rank < parent_rank {
        let width = usize::MAX as int + 1;
        let from = parent_rank as int;
        let to = child_rank as int;
        lemma_mul_inequality(to + 1, from, width);
        assert((to + 1) * width == to * width + width) by (nonlinear_arith);
    }
}

// 順序の小さい式とその継続を複数処理できるよう、順序が一つ上がるごとに仕事量を8倍にする。
#[verifier::opaque]
pub(super) open spec fn expression_work(order: nat) -> nat
    decreases order,
{
    if order == 0 { 1 } else { 8 * expression_work((order - 1) as nat) }
}

pub(super) proof fn expression_work_positive(order: nat)
    ensures expression_work(order) > 0,
    decreases order,
{
    reveal(expression_work);
    if order > 0 { expression_work_positive((order - 1) as nat); }
}

pub(super) proof fn expression_work_dominates(parent: nat, child: nat)
    requires child < parent,
    ensures 8 * expression_work(child) <= expression_work(parent),
    decreases parent,
{
    reveal(expression_work);
    if child + 1 < parent {
        expression_work_dominates((parent - 1) as nat, child);
    }
}

}
