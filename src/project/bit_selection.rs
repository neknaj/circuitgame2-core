//! ビット選択の範囲を検査し、選択順に値や配線を取り出す。

use alloc::vec::Vec;
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

/// 開始位置から刻み幅ずつ進み、指定個数の要素を取り出す。
pub open spec fn selected_bits_values<T>(input: Seq<T>, start: u64, count: nat, stride: u64) -> Seq<T> {
    Seq::new(count, |i: int| input[start + i * stride])
}

proof fn append_selected_bit_value<T>(input: Seq<T>, start: u64, stride: u64, previous: Seq<T>, value: T)
    requires
        previous == selected_bits_values(input, start, previous.len(), stride),
        0 <= start + previous.len() * stride < input.len(),
        value == input[start + previous.len() * stride],
    ensures previous.push(value) == selected_bits_values(input, start, previous.len() + 1, stride),
{
    let next = previous.push(value);
    let expected = selected_bits_values(input, start, previous.len() + 1, stride);
    assert forall|i: int| 0 <= i < next.len() implies (#[trigger] next[i]) == (#[trigger] expected[i]) by {
        assert(expected[i] == input[start + i * stride]);
        if i < previous.len() {
            assert(next[i] == previous[i]);
        } else {
            assert(i == previous.len());
            assert(next[i] == value);
        }
    };
    assert(next =~= expected);
}

/// 選択した要素列、または最初に検出した違反を表す。
pub open spec fn selected_bits_match<T>(
    input: Seq<T>, start: u64, count: u64, stride: u64, result: Result<Vec<T>, BitSelectionError>,
) -> bool {
    &&& input.len() <= u64::MAX
    &&& match result {
        Err(error) => bit_selection_matches(input.len() as u64, start, count, stride, Err(error)),
        Ok(values) => {
            &&& exists|last: u64| #[trigger] bit_selection_matches(input.len() as u64, start, count, stride, Ok(last))
            &&& values@.len() == count
            &&& values@ == selected_bits_values(input, start, count as nat, stride)
        },
    }
}

/// 指定した位置を、開始位置から刻みの順に取り出す。
///
/// 入力と結果の先頭は、どちらもそれぞれのビット列の最下位に対応する。
/// 要素をビット値にすれば評価に、配線にすればネットリストの生成に使える。
///
/// # Errors
///
/// [`check_bit_selection`] と同じ順に選択数、刻み、範囲を検査する。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::project::{BitSelectionError, select_bits};
///
/// let input = [true, false, false, true, true, true];
/// assert_eq!(select_bits(&input, 1, 3, 2), Ok(vec![false, true, true]));
/// assert_eq!(select_bits(&input, 1, 4, 2), Err(BitSelectionError::Outside {
///     start: 1, last: 7, input_width: 6,
/// }));
/// ```
pub fn select_bits<T: Copy>(
    input: &[T], start: u64, count: u64, stride: u64,
) -> (result: Result<Vec<T>, BitSelectionError>)
    ensures selected_bits_match(input@, start, count, stride, result),
{
    let input_len = input.len();
    let width = input_len as u64;
    let _last = match check_bit_selection(width, start, count, stride) {
        Ok(last) => last,
        Err(error) => return Err(error),
    };

    let mut selected = Vec::new();
    assert(selected@ =~= selected_bits_values(input@, start, 0, stride));
    let mut i: u64 = 0;
    while i < count
        invariant
            width == input@.len(),
            input_len == input@.len(),
            bit_selection_matches(width, start, count, stride, Ok(_last)),
            i == selected@.len() <= count,
            selected@ == selected_bits_values(input@, start, i as nat, stride),
        decreases count - i,
    {
        proof { selected_bit_in_range(width, start, count, stride, _last, i as int); }
        let offset = start + i * stride;
        assert(offset < input_len && offset == start + i * stride);
        let index = offset as usize;
        let value = input[index];
        proof { append_selected_bit_value(input@, start, stride, selected@, value); }
        selected.push(value);
        i += 1;
    }
    assert(exists|end: u64| #[trigger] bit_selection_matches(width, start, count, stride, Ok(end)));
    Ok(selected)
}

} // verus!
