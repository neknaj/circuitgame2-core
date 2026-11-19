//! `concat` の各引数の幅を足し、連接したビット列に必要な幅を求める。

use vstd::prelude::*;

verus! {

/// 連接するビット列の幅を計算できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConcatWidthError {
    /// 連接するビット列が一つもない。
    Empty,
    /// 幅が 0 のビット列がある。
    ZeroWidth {
        /// 幅が 0 の引数の添字。先頭から 0 で数える。
        argument: usize,
    },
    /// 引数を順に加えた幅が、指定の上限を超えた。
    LimitExceeded {
        /// 加えた時点で初めて上限を超えた引数の添字。
        argument: usize,
        /// その引数までを含む幅。
        width: u128,
        /// 呼び出し側が指定した幅の上限。
        limit: u64,
    },
}

/// 先頭から指定数の幅を数学上の整数で合計する。
/// 引数を低位側から置くため、合計は次の引数を置く位置にもなる。
#[verifier::opaque]
pub closed spec fn concat_prefix_width(widths: Seq<u64>, count: nat) -> int
    recommends count <= widths.len(),
    decreases count,
{
    if count == 0 { 0 }
    else { concat_prefix_width(widths, (count - 1) as nat) + widths[count - 1] }
}

#[verifier::opaque]
spec fn within_limit(widths: Seq<u64>, count: int, limit: u64) -> bool {
    &&& 0 <= count <= widths.len()
    &&& forall|i: int| 0 <= i < count <= widths.len() ==>
        0 < #[trigger] widths[i] && concat_prefix_width(widths, (i + 1) as nat) <= limit
}

/// 幅の合計または最初に失敗した引数が、入力の幅と上限に対応することを表す。
pub closed spec fn concat_width_matches(
    widths: Seq<u64>, limit: u64, result: Result<u64, ConcatWidthError>,
) -> bool {
    if widths.len() == 0 {
        result == Err(ConcatWidthError::Empty)
    } else {
        match result {
            Ok(width) => within_limit(widths, widths.len() as int, limit)
                && width == concat_prefix_width(widths, widths.len()),
            Err(ConcatWidthError::ZeroWidth { argument }) =>
                argument < widths.len() && within_limit(widths, argument as int, limit)
                    && widths[argument as int] == 0,
            Err(ConcatWidthError::LimitExceeded { argument, width, limit: bound }) =>
                argument < widths.len() && within_limit(widths, argument as int, limit)
                    && widths[argument as int] > 0 && bound == limit
                    && width == concat_prefix_width(widths, (argument + 1) as nat) && width > limit,
            Err(ConcatWidthError::Empty) => false,
        }
    }
}

/// 連接するビット列の幅を、引数順に加えた合計を返す。
///
/// 各引数の幅を先に確定し、合計を連接式の期待幅と照合するときに使う。
///
/// # Errors
///
/// 引数がなければ空のエラーを返す。各引数では、幅が 0 かどうかを確認してから幅を加える。
/// 合計が最初に上限を超えた引数と、その時点の合計を返す。
pub fn check_concat_width(widths: &[u64], max_width: u64) -> (result: Result<u64, ConcatWidthError>)
    ensures
        concat_width_matches(widths@, max_width, result),
        result matches Ok(width) ==> 0 < width <= max_width,
{
    if widths.len() == 0 { return Err(ConcatWidthError::Empty); }
    let mut argument = 0;
    let mut sum = 0u64;
    proof { reveal(within_limit); reveal_with_fuel(concat_prefix_width, 1); }
    while argument < widths.len()
        invariant
            0 < widths@.len(),
            within_limit(widths@, argument as int, max_width),
            argument <= widths@.len(), sum <= max_width,
            argument > 0 ==> 0 < sum,
            sum == concat_prefix_width(widths@, argument as nat),
        decreases widths@.len() - argument,
    {
        let width = widths[argument];
        if width == 0 { return Err(ConcatWidthError::ZeroWidth { argument }); }
        let next = sum as u128 + width as u128;
        assert(next == concat_prefix_width(widths@, (argument + 1) as nat)) by {
            reveal_with_fuel(concat_prefix_width, 1);
        };
        if next > max_width as u128 {
            return Err(ConcatWidthError::LimitExceeded { argument, width: next, limit: max_width });
        }
        proof {
            reveal(within_limit);
            assert forall|i: int| 0 <= i <= argument
                implies 0 < #[trigger] widths@[i] && concat_prefix_width(widths@, (i + 1) as nat) <= max_width by {
                if i < argument {
                    assert(0 < widths@[i] && concat_prefix_width(widths@, (i + 1) as nat) <= max_width);
                }
            };
        }
        sum = next as u64;
        argument += 1;
    }
    Ok(sum)
}

} // verus!
