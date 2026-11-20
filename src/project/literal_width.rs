//! 回路式の定数を、期待幅と実行環境の幅上限に照らして検査する。

use crate::syntax::bit_literal_size;
#[cfg(verus_only)]
use crate::syntax::{BitLiteralSize, bit_literal_size_matches};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 回路の定数にビット幅を与えられなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CircuitLiteralWidthError {
    /// 元の字句が回路の定数の形に従わない。
    InvalidLiteral,
    /// 期待幅が 0 である。
    ZeroWidth,
    /// 1 ビット固定の `0` または `1` に異なる期待幅が指定された。
    FixedBitWidth {
        /// 利用箇所が要求する幅。
        expected: u64,
    },
    /// 二進または十六進の値が期待幅に収まらない。
    DoesNotFit {
        /// 利用箇所が要求する幅。
        expected: u64,
        /// 値を表すのに必要なビット数。
        required: u128,
    },
    /// 定数に割り当てる幅が、呼び出し側の指定した上限を超えた。
    LimitExceeded {
        /// 定数に割り当てようとした幅。
        width: u128,
        /// 呼び出し側が指定した幅の上限。
        limit: u64,
    },
}

spec fn fixed_bit(bytes: Seq<u8>) -> bool {
    &&& bytes.len() == 1
    &&& (bytes[0] == b'0' || bytes[0] == b'1')
}

spec fn width_for(
    fixed: bool, written: u128, required: u128, expected: Option<u64>, limit: u64,
    result: Result<u64, CircuitLiteralWidthError>,
) -> bool {
    let width = if let Some(expected) = expected { expected as u128 } else { written };
    if width == 0 {
        result == Err(CircuitLiteralWidthError::ZeroWidth)
    } else if fixed && width != 1 {
        result == Err(CircuitLiteralWidthError::FixedBitWidth { expected: width as u64 })
    } else if required > width {
        result == Err(CircuitLiteralWidthError::DoesNotFit { expected: width as u64, required })
    } else if width > limit {
        result == Err(CircuitLiteralWidthError::LimitExceeded { width, limit })
    } else {
        result matches Ok(actual) && actual == width
    }
}

/// 字句の形と値の必要ビット数から、利用できる幅または最初の違反を定める。
pub closed spec fn circuit_literal_width_matches(
    bytes: Seq<u8>, expected: Option<u64>, limit: u64, result: Result<u64, CircuitLiteralWidthError>,
) -> bool {
    if fixed_bit(bytes) {
        width_for(true, 1, 1, expected, limit, result)
    } else if bit_literal_size_matches(bytes, None) {
        result == Err(CircuitLiteralWidthError::InvalidLiteral)
    } else {
        exists|size: BitLiteralSize| #[trigger] bit_literal_size_matches(bytes, Some(size))
            && width_for(false, size.written_bits, size.required_bits, expected, limit, result)
    }
}

pub(super) proof fn fixed_bit_literal_width(
    bytes: Seq<u8>, expected: Option<u64>, limit: u64, width: u64,
)
    requires
        bytes == "0".spec_bytes() || bytes == "1".spec_bytes(),
        circuit_literal_width_matches(bytes, expected, limit, Ok(width)),
    ensures width == 1,
{
    reveal_strlit("0");
    reveal_strlit("1");
    let word = if bytes == "0".spec_bytes() { "0" } else { "1" };
    assert(vstd::string::is_ascii(word)) by {
        assert forall|i: int| 0 <= i < word@.len() implies #[trigger] word@[i] as int <= 127 by {
            assert(i == 0);
        };
    };
    vstd::string::is_ascii_spec_bytes(word);
    assert(fixed_bit(bytes));
}

fn apply_width(
    fixed: bool, written: u128, required: u128,
    expected: Option<u64>, limit: u64,
) -> (result: Result<u64, CircuitLiteralWidthError>)
    requires required <= written, fixed ==> written == 1 && required == 1,
    ensures
        width_for(fixed, written, required, expected, limit, result),
        result matches Ok(width) ==> 0 < width <= limit && (expected.is_none() || expected == Some(width)),
{
    let width = match expected {
        Some(bits) => bits as u128,
        None => written,
    };
    if width == 0 {
        return Err(CircuitLiteralWidthError::ZeroWidth);
    }
    if let Some(expected) = expected {
        if fixed && expected != 1 {
            return Err(CircuitLiteralWidthError::FixedBitWidth { expected });
        }
        if required > width {
            return Err(CircuitLiteralWidthError::DoesNotFit { expected, required });
        }
    }
    if width > limit as u128 {
        return Err(CircuitLiteralWidthError::LimitExceeded { width, limit });
    }
    Ok(width as u64)
}

/// 回路の定数一つを、期待幅に照らして検査し、割り当てるビット幅を返す。
///
/// `0` と `1` は 1 ビット。二進・十六進のリテラルは、期待幅があればその幅で表せる値を受理する。
/// 期待幅がなければ、二進の各桁を 1 ビット、十六進の各桁を 4 ビットと数える。
///
/// # Errors
///
/// 字句の違反、期待幅 0、固定幅の不一致、値が期待幅に収まらない場合、幅の上限超過の順に検査する。
pub fn check_circuit_literal_width(
    word: &str, expected: Option<u64>, max_width: u64,
) -> (result: Result<u64, CircuitLiteralWidthError>)
    ensures
        circuit_literal_width_matches(word.spec_bytes(), expected, max_width, result),
        result matches Ok(width) ==> 0 < width <= max_width,
        result matches Ok(width) ==> expected.is_none() || expected == Some(width),
{
    let bytes = word.as_bytes();
    if bytes.len() == 1 && matches!(bytes[0], b'0' | b'1') {
        return apply_width(true, 1, 1, expected, max_width);
    }
    let Some(size) = bit_literal_size(word) else {
        return Err(CircuitLiteralWidthError::InvalidLiteral);
    };
    let result = apply_width(false, size.written_bits, size.required_bits, expected, max_width);
    assert(circuit_literal_width_matches(word.spec_bytes(), expected, max_width, result)) by {
        assert(bit_literal_size_matches(word.spec_bytes(), Some(size)));
    };
    result
}

} // verus!
