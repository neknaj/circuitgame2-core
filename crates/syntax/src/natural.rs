//! 自然数の字句を、値の範囲を確認しながら機械整数に変換する。

#[cfg(verus_only)]
use crate::digits::digit;
use crate::digits::{Radix, matches_digits};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 自然数の字句を `u64` に変換できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NaturalRangeError {
    /// ASCII の十進数字が一桁以上並ぶ字句を要求する。
    InvalidDigits,
    /// 十進数として表す値が `u64::MAX` を超えている。
    OutOfRange,
}

pub(crate) open spec fn natural_digits(bytes: Seq<u8>) -> bool {
    bytes.len() > 0 && forall|i: int| 0 <= i < bytes.len() ==> digit(Radix::Decimal, #[trigger] bytes[i])
}

spec fn decimal_prefix(bytes: Seq<u8>, count: nat) -> int
    decreases count,
{
    if count == 0 { 0 } else {
        decimal_prefix(bytes, (count - 1) as nat) * 10 + (bytes[count - 1] as int - b'0' as int)
    }
}

/// 十進数字の列が表す数学上の値を、桁数による上限なしで定める。
pub closed spec fn decimal_natural_value(bytes: Seq<u8>) -> Option<int> {
    if natural_digits(bytes) { Some(decimal_prefix(bytes, bytes.len())) } else { None }
}

pub(crate) proof fn digits_admit_value(bytes: Seq<u8>)
    requires natural_digits(bytes),
    ensures decimal_natural_value(bytes).is_some(),
{
}

/// 字句の形と数学上の値に対応する変換結果を定める。
pub open spec fn natural_u64_matches(bytes: Seq<u8>, result: Result<u64, NaturalRangeError>) -> bool {
    match decimal_natural_value(bytes) {
        None => result == Err(NaturalRangeError::InvalidDigits),
        Some(value) => if value > u64::MAX {
            result == Err(NaturalRangeError::OutOfRange)
        } else {
            result matches Ok(natural) && natural as int == value
        },
    }
}

proof fn decimal_step(bytes: Seq<u8>, at: nat)
    requires at < bytes.len(),
    ensures decimal_prefix(bytes, at + 1) == 10 * decimal_prefix(bytes, at) + bytes[at as int] as int - b'0' as int,
{
    reveal_with_fuel(decimal_prefix, 2);
}

proof fn decimal_prefix_only_grows(bytes: Seq<u8>, first: nat, last: nat)
    requires
        natural_digits(bytes), first <= last <= bytes.len(),
        0 <= decimal_prefix(bytes, first),
    ensures decimal_prefix(bytes, first) <= decimal_prefix(bytes, last),
    decreases last - first,
{
    if last > first {
        decimal_prefix_only_grows(bytes, first, (last - 1) as nat);
        decimal_step(bytes, (last - 1) as nat);
        assert(digit(Radix::Decimal, bytes[last - 1]));
    }
}

/// ASCII の十進数字列を `u64` に変換する。
///
/// 先頭の 0 を許す。例えば `"0001"` は `1` を返す。
///
/// # Errors
///
/// 数字列の形が正しくなければ [`NaturalRangeError::InvalidDigits`] を返す。
/// 数字列が表す値が `u64` に収まらなければ [`NaturalRangeError::OutOfRange`] を返す。
pub fn read_natural_u64(word: &str) -> (result: Result<u64, NaturalRangeError>)
    ensures natural_u64_matches(word.spec_bytes(), result),
{
    let bytes = word.as_bytes();
    if !matches_digits(bytes, Radix::Decimal) {
        return Err(NaturalRangeError::InvalidDigits);
    }
    let mut value = 0u64;
    let mut at = 0;
    assert(decimal_prefix(bytes@, 0) == 0);
    while at < bytes.len()
        invariant
            bytes@ == word.spec_bytes(),
            natural_digits(bytes@),
            at <= bytes@.len(),
            value as int == decimal_prefix(bytes@, at as nat),
        decreases bytes@.len() - at,
    {
        let byte = bytes[at];
        let decimal = (byte - b'0') as u64;
        proof { decimal_step(bytes@, at as nat); }
        let Some(prefix) = value.checked_mul(10) else {
            proof { decimal_prefix_only_grows(bytes@, (at + 1) as nat, bytes@.len()); }
            return Err(NaturalRangeError::OutOfRange);
        };
        let Some(next) = prefix.checked_add(decimal) else {
            proof { decimal_prefix_only_grows(bytes@, (at + 1) as nat, bytes@.len()); }
            return Err(NaturalRangeError::OutOfRange);
        };
        value = next;
        at += 1;
    }
    Ok(value)
}

} // verus!
