//! ビット列から選択するすべての位置が、入力の幅に収まることを確認する。

#[cfg(verus_only)]
use vstd::arithmetic::mul::lemma_mul_inequality;
use vstd::prelude::*;

verus! {

/// `bit` または `slice` で指定した選択の違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BitSelectionError {
    /// 選択数が 0 である。
    ZeroCount,
    /// 刻みが 0 である。
    ZeroStride,
    /// 選択する最後の位置が、入力のビット列の範囲を越えている。
    Outside {
        /// 指定した開始位置。
        start: u64,
        /// 選択する最後の位置。`u64` に収まらない位置も表す。
        last: u128,
        /// 入力のビット幅。
        input_width: u64,
    },
}

/// 選択が有効なら末尾位置を返し、違反があればその理由を返すことを表す。
pub open spec fn bit_selection_matches(
    input_width: u64, start: u64, count: u64, stride: u64, result: Result<u64, BitSelectionError>,
) -> bool {
    let last = start + (count - 1) * stride;
    if count == 0 {
        result == Err(BitSelectionError::ZeroCount)
    } else if stride == 0 {
        result == Err(BitSelectionError::ZeroStride)
    } else if last >= input_width {
        result matches Err(BitSelectionError::Outside { start: first, last: end, input_width: width })
            && first == start && end == last && width == input_width
    } else {
        result matches Ok(end) && end == last
    }
}

/// 検査に通った選択の任意の要素について、元の添字が入力の幅に収まることを示す。
pub proof fn selected_bit_in_range(
    input_width: u64, start: u64, count: u64, stride: u64, last: u64, element: int,
)
    requires
        bit_selection_matches(input_width, start, count, stride, Ok(last)),
        0 <= element < count,
    ensures 0 <= start + element * stride <= last < input_width,
{
    lemma_mul_inequality(element, count - 1, stride as int);
    lemma_mul_inequality(0, element, stride as int);
}

/// 開始位置、選択数、刻みから最後に選択するビットの添字を求める。
///
/// 添字は 0 から数える。`bit` では選択数と刻みに 1 を指定する。`slice` で刻みを省略した場合も 1 を使う。
///
/// # Errors
///
/// 選択数、刻み、選択範囲の順に検査して、最初の違反を返す。
pub fn check_bit_selection(
    input_width: u64, start: u64, count: u64, stride: u64,
) -> (result: Result<u64, BitSelectionError>)
    ensures
        bit_selection_matches(input_width, start, count, stride, result),
        result matches Ok(last) ==> start <= last < input_width && 0 < count && 0 < stride,
{
    if count == 0 {
        return Err(BitSelectionError::ZeroCount);
    }
    if stride == 0 {
        return Err(BitSelectionError::ZeroStride);
    }
    let steps = (count - 1) as u128;
    proof {
        // 末尾は最大で u64::MAX の二乗なので、範囲外の値も u128 で計算できる。
        lemma_mul_inequality(steps as int, u64::MAX as int - 1, stride as int);
        lemma_mul_inequality(stride as int, u64::MAX as int, u64::MAX as int - 1);
        lemma_mul_inequality(0, steps as int, stride as int);
        assert(steps * stride + start <= (u64::MAX as int - 1) * u64::MAX + u64::MAX);
    }
    let last = steps * stride as u128 + start as u128;
    if last >= input_width as u128 {
        Err(BitSelectionError::Outside { start, last, input_width })
    } else {
        Ok(last as u64)
    }
}

} // verus!
