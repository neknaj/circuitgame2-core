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

/// 型を確定した連接式の合計幅に関する違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConcatResultWidthError {
    /// 引数がない、幅が0の引数がある、または加算途中の幅が `u64` の範囲を超えた。
    Arguments(ConcatWidthError),
    /// 合計幅が出力側の期待幅と異なる。
    Mismatch {
        /// 出力側が要求した幅。
        expected: u64,
        /// 各引数の幅を足した値。
        actual: u64,
    },
    /// 合計幅が設定上限を超える。
    ConfiguredLimit {
        /// 処理に設定された上限。
        limit: u64,
        /// 各引数の幅を足した値。
        actual: u64,
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

/// 合計幅を求め、期待幅、設定上限の順に照合することを表す。
pub closed spec fn concat_result_width_matches(
    widths: Seq<u64>, expected: Option<u64>, limit: u64, result: Result<u64, ConcatResultWidthError>,
) -> bool {
    match result {
        Err(ConcatResultWidthError::Arguments(error)) => concat_width_matches(widths, u64::MAX, Err(error)),
        _ => {
            let total = concat_prefix_width(widths, widths.len());
            &&& 0 < total <= u64::MAX
            &&& concat_width_matches(widths, u64::MAX, Ok(total as u64))
            &&& match expected {
                Some(w) if w != total => result == Err(ConcatResultWidthError::Mismatch { expected: w, actual: total as u64 }),
                _ if total > limit => result == Err(ConcatResultWidthError::ConfiguredLimit { limit, actual: total as u64 }),
                _ => result == Ok(total as u64),
            }
        },
    }
}

/// 同じ引数と上限からは、合計幅または最初の違反が一意に定まる。
pub proof fn concat_width_results_agree(
    widths: Seq<u64>, limit: u64, left: Result<u64, ConcatWidthError>, right: Result<u64, ConcatWidthError>,
)
    requires concat_width_matches(widths, limit, left), concat_width_matches(widths, limit, right),
    ensures left == right,
{
    if widths.len() > 0 {
        let a = concat_width_valid_prefix(widths, limit, left);
        let b = concat_width_valid_prefix(widths, limit, right);
        reveal(within_limit);
        if a < b {
            assert(0 < widths[a] && concat_prefix_width(widths, (a + 1) as nat) <= limit);
            assert(false);
        } else if b < a {
            assert(0 < widths[b] && concat_prefix_width(widths, (b + 1) as nat) <= limit);
            assert(false);
        }
    }
}

proof fn concat_width_valid_prefix(
    widths: Seq<u64>, limit: u64, result: Result<u64, ConcatWidthError>,
) -> (count: int)
    requires widths.len() > 0, concat_width_matches(widths, limit, result),
    ensures
        within_limit(widths, count, limit),
        match result {
            Ok(_) => count == widths.len(),
            Err(ConcatWidthError::ZeroWidth { argument }) => count == argument < widths.len()
                && widths[count] == 0,
            Err(ConcatWidthError::LimitExceeded { argument, .. }) => count == argument < widths.len()
                && widths[count] > 0 && concat_prefix_width(widths, (count + 1) as nat) > limit,
            Err(ConcatWidthError::Empty) => false,
        },
{
    match result {
        Ok(_) => widths.len() as int,
        Err(ConcatWidthError::ZeroWidth { argument }) | Err(ConcatWidthError::LimitExceeded { argument, .. }) => argument as int,
        Err(ConcatWidthError::Empty) => 0,
    }
}

/// 期待幅を含む条件が同じなら、連接の合計幅または診断も一致する。
pub proof fn concat_result_widths_agree(
    widths: Seq<u64>, expected: Option<u64>, limit: u64,
    left: Result<u64, ConcatResultWidthError>, right: Result<u64, ConcatResultWidthError>,
)
    requires
        concat_result_width_matches(widths, expected, limit, left),
        concat_result_width_matches(widths, expected, limit, right),
    ensures left == right,
{
    let sum = concat_prefix_width(widths, widths.len()) as u64;
    let l = if let Err(ConcatResultWidthError::Arguments(error)) = left { Err(error) } else { Ok(sum) };
    let r = if let Err(ConcatResultWidthError::Arguments(error)) = right { Err(error) } else { Ok(sum) };
    concat_width_results_agree(widths, u64::MAX, l, r);
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

/// 各引数の幅を足し、連接式の期待幅と設定上限を照合する。
///
/// `expected` は連接全体の幅を指定する。個々の引数の幅は、呼び出す前に確定させる。
///
/// # Errors
///
/// 引数の幅と合計幅の表現範囲は [`check_concat_width`] と同じ順で検査する。
/// 合計幅が求まったら、期待幅との一致を調べ、その後で設定上限を検査する。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::project::{ConcatResultWidthError, check_concat_result_width};
///
/// assert_eq!(check_concat_result_width(&[2, 3], Some(5), 8), Ok(5));
/// assert_eq!(
///     check_concat_result_width(&[2, 3], Some(4), 4),
///     Err(ConcatResultWidthError::Mismatch { expected: 4, actual: 5 }),
/// );
/// ```
pub fn check_concat_result_width(
    widths: &[u64], expected: Option<u64>, limit: u64,
) -> (result: Result<u64, ConcatResultWidthError>)
    ensures
        concat_result_width_matches(widths@, expected, limit, result),
        result matches Ok(width) ==> 0 < width <= limit && width == concat_prefix_width(widths@, widths@.len()),
        result matches Ok(width) ==> expected matches Some(requested) ==> width == requested,
        result matches Err(ConcatResultWidthError::Mismatch { expected: requested, actual })
            ==> expected == Some(requested) && requested != actual,
{
    let actual = match check_concat_width(widths, u64::MAX) {
        Ok(actual) => actual,
        Err(error) => return Err(ConcatResultWidthError::Arguments(error)),
    };
    if let Some(expected) = expected {
        if expected != actual {
            return Err(ConcatResultWidthError::Mismatch { expected, actual });
        }
    }
    if actual > limit {
        Err(ConcatResultWidthError::ConfiguredLimit { limit, actual })
    } else {
        Ok(actual)
    }
}

} // verus!
