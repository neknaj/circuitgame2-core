//! NCG2M の十進リテラルと整数の組み込みを評価する。

use crate::syntax::{NaturalRangeError, read_natural_u64};
#[cfg(verus_only)]
use crate::syntax::decimal_natural_value;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    encode_utf8_valid_utf8, is_char_boundary, length_of_first_scalar, valid_utf8,
};

verus! {

/// NCG2M の整数の型。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntegerType {
    /// 符号なし 64 ビットの自然数。
    Nat,
    /// 符号付き 64 ビットの整数。
    Int,
}

/// 期待型を考慮して読み取った十進リテラルの値。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntegerValue {
    /// `Nat` の値。
    Nat(u64),
    /// `Int` の値。
    Int(i64),
}

/// 十進リテラルを読み取れなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntegerLiteralError {
    /// ASCII の十進数字が必要な位置に別の文字があるか、数字がない。
    InvalidDigits,
    /// 期待型が `Nat` の位置に、負号の付いた十進リテラルがある。
    NegativeLiteralForNat,
    /// リテラルの値が、選ばれた型の表現範囲を越える。
    OutOfRange(IntegerType),
}

/// 加減乗の組み込み。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntegerOperation {
    /// `add`。二つの引数の和。
    Add,
    /// `sub`。第 1 引数から第 2 引数を引いた差。
    Sub,
    /// `mul`。二つの引数の積。
    Mul,
}

/// 組み込みの結果が戻り値の型の範囲を越えたことを表す。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IntegerOutOfRange;

/// 数学上の整数に対する組み込みの結果を定める。
pub open spec fn arithmetic_value(operation: IntegerOperation, left: int, right: int) -> int {
    match operation {
        IntegerOperation::Add => left + right,
        IntegerOperation::Sub => left - right,
        IntegerOperation::Mul => left * right,
    }
}

/// 数学上の値から `Nat` の実行結果を定める。
pub open spec fn nat_result_matches(value: int, result: Result<u64, IntegerOutOfRange>) -> bool {
    if 0 <= value <= u64::MAX {
        result matches Ok(read) && read as int == value
    } else {
        result == Err(IntegerOutOfRange)
    }
}

/// 数学上の値から `Int` の実行結果を定める。
pub open spec fn int_result_matches(value: int, result: Result<i64, IntegerOutOfRange>) -> bool {
    if i64::MIN <= value <= i64::MAX {
        result matches Ok(read) && read as int == value
    } else {
        result == Err(IntegerOutOfRange)
    }
}

/// 十進リテラルの形、期待型、数学上の値から変換結果を定める。
pub open spec fn integer_literal_matches(
    bytes: Seq<u8>, expected: Option<IntegerType>, result: Result<IntegerValue, IntegerLiteralError>,
) -> bool {
    let negative = bytes.len() > 0 && bytes[0] == b'-';
    let magnitude = if negative { decimal_natural_value(bytes[1..]) } else {
        decimal_natural_value(bytes)
    };
    match magnitude {
        None => result == Err(IntegerLiteralError::InvalidDigits),
        Some(magnitude) => {
            let value = if negative { -magnitude } else { magnitude };
            if negative && expected == Some(IntegerType::Nat) {
                result == Err(IntegerLiteralError::NegativeLiteralForNat)
            } else if negative || expected == Some(IntegerType::Int) {
                if i64::MIN <= value <= i64::MAX {
                    result matches Ok(IntegerValue::Int(read)) && read as int == value
                } else {
                    result == Err(IntegerLiteralError::OutOfRange(IntegerType::Int))
                }
            } else if 0 <= value <= u64::MAX {
                result matches Ok(IntegerValue::Nat(read)) && read as int == value
            } else {
                result == Err(IntegerLiteralError::OutOfRange(IntegerType::Nat))
            }
        }
    }
}

/// 十進リテラルを期待型に従って読み取る。
///
/// 負号があるときは `Int` とする。負号がなく期待型が未定なら `Nat` とする。
/// 十進数字の先頭に 0 を置ける。負号付きの `-0` は `Int` の 0 を表す。
///
/// # Errors
///
/// 数字列の形、期待型、値の範囲の順に検査する。負号があり期待型が `Nat` の場合は
/// [`IntegerLiteralError::NegativeLiteralForNat`] を返す。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::ncg2m::integers::{
///     IntegerLiteralError, IntegerType, IntegerValue, read_integer_literal,
/// };
///
/// assert_eq!(read_integer_literal("7", None)?, IntegerValue::Nat(7));
/// assert_eq!(read_integer_literal("7", Some(IntegerType::Int))?, IntegerValue::Int(7));
/// assert_eq!(
///     read_integer_literal("-9223372036854775808", None)?,
///     IntegerValue::Int(i64::MIN),
/// );
/// assert_eq!(
///     read_integer_literal("-9223372036854775809", None),
///     Err(IntegerLiteralError::OutOfRange(IntegerType::Int)),
/// );
/// # Ok::<(), IntegerLiteralError>(())
/// ```
pub fn read_integer_literal(
    word: &str, expected: Option<IntegerType>,
) -> (result: Result<IntegerValue, IntegerLiteralError>)
    ensures integer_literal_matches(word.spec_bytes(), expected, result),
{
    let bytes = word.as_bytes();
    let negative = bytes.len() > 0 && bytes[0] == b'-';
    let digits = if negative {
        proof {
            encode_utf8_valid_utf8(word@);
            reveal_with_fuel(valid_utf8, 2);
            assert(length_of_first_scalar(bytes@) == 1);
            reveal_with_fuel(is_char_boundary, 2);
            assert(is_char_boundary(bytes@, 1));
        }
        word.split_at(1).1
    } else {
        word
    };
    let magnitude = read_natural_u64(digits);
    if matches!(magnitude, Err(NaturalRangeError::InvalidDigits)) {
        return Err(IntegerLiteralError::InvalidDigits);
    }
    if negative && matches!(expected, Some(IntegerType::Nat)) {
        return Err(IntegerLiteralError::NegativeLiteralForNat);
    }
    let ty = if negative || matches!(expected, Some(IntegerType::Int)) {
        IntegerType::Int
    } else {
        IntegerType::Nat
    };
    let Ok(magnitude) = magnitude else { return Err(IntegerLiteralError::OutOfRange(ty)); };
    if matches!(ty, IntegerType::Nat) {
        return Ok(IntegerValue::Nat(magnitude));
    }
    if negative && magnitude == (i64::MAX as u64) + 1 {
        // 最小値の絶対値は `i64` の正の範囲に収まらない。
        return Ok(IntegerValue::Int(i64::MIN));
    }
    if magnitude > i64::MAX as u64 {
        return Err(IntegerLiteralError::OutOfRange(IntegerType::Int));
    }
    let signed = magnitude as i64;
    Ok(IntegerValue::Int(if negative { -signed } else { signed }))
}

/// `Nat` どうしの加算、減算、乗算を行う。
///
/// # Errors
///
/// 結果が負になるか、符号なし 64 ビットの最大値を越える場合に
/// [`IntegerOutOfRange`] を返す。
pub fn evaluate_nat(
    operation: IntegerOperation, left: u64, right: u64,
) -> (result: Result<u64, IntegerOutOfRange>)
    ensures nat_result_matches(arithmetic_value(operation, left as int, right as int), result),
{
    let value = match operation {
        IntegerOperation::Add => left.checked_add(right),
        IntegerOperation::Sub => left.checked_sub(right),
        IntegerOperation::Mul => left.checked_mul(right),
    };
    match value { Some(value) => Ok(value), None => Err(IntegerOutOfRange) }
}

/// `Int` どうしの加算、減算、乗算を行う。
///
/// # Errors
///
/// 結果が符号付き 64 ビットの範囲を越える場合に [`IntegerOutOfRange`] を返す。
pub fn evaluate_int(
    operation: IntegerOperation, left: i64, right: i64,
) -> (result: Result<i64, IntegerOutOfRange>)
    ensures int_result_matches(arithmetic_value(operation, left as int, right as int), result),
{
    let value = match operation {
        IntegerOperation::Add => left.checked_add(right),
        IntegerOperation::Sub => left.checked_sub(right),
        IntegerOperation::Mul => left.checked_mul(right),
    };
    match value { Some(value) => Ok(value), None => Err(IntegerOutOfRange) }
}

/// 組み込み `int-to-nat`。同じ値を `Nat` で表す。
///
/// # Errors
///
/// 入力が負なら [`IntegerOutOfRange`] を返す。
pub fn int_to_nat(value: i64) -> (result: Result<u64, IntegerOutOfRange>)
    ensures nat_result_matches(value as int, result),
{
    if value < 0 { Err(IntegerOutOfRange) } else { Ok(value as u64) }
}

/// 組み込み `nat-to-int`。同じ値を `Int` で表す。
///
/// # Errors
///
/// 入力が符号付き 64 ビットの最大値を越える場合は [`IntegerOutOfRange`] を返す。
pub fn nat_to_int(value: u64) -> (result: Result<i64, IntegerOutOfRange>)
    ensures int_result_matches(value as int, result),
{
    if value > i64::MAX as u64 { Err(IntegerOutOfRange) } else { Ok(value as i64) }
}

proof fn integer_range_examples() {
    assert(nat_result_matches(arithmetic_value(IntegerOperation::Sub, 0, 1), Err(IntegerOutOfRange)));
    assert(int_result_matches(arithmetic_value(IntegerOperation::Mul, i64::MIN as int, -1), Err(IntegerOutOfRange)));
    assert(int_result_matches(arithmetic_value(IntegerOperation::Add, i64::MIN as int, 0), Ok(i64::MIN)));
}

} // verus!
