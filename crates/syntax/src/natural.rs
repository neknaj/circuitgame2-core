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

/// 十進数字列を読み進める状態。
///
/// 元の字句を借りて保持する。各ステップは十進数字を最大一桁だけ消費する。
pub struct NaturalReader<'a> {
    bytes: &'a [u8],
    at: usize,
    value: Option<u64>,
}

/// 十進数字列を一歩読んだ結果。
pub enum NaturalReadStep<'a> {
    /// 字句の末尾まで読み、値を確定した。
    Done(u64),
    /// 次の桁または字句の末尾から読み取りを続ける。
    Continue(NaturalReader<'a>),
}

impl<'a> NaturalReader<'a> {
    /// 読み取る元の字句をバイト列で表す。
    pub closed spec fn bytes_model(&self) -> Seq<u8> { self.bytes@ }

    /// 次に読むバイトの位置を表す。
    pub closed spec fn position_model(&self) -> usize { self.at }

    /// オーバーフローした接頭辞は `None` で表す。
    pub closed spec fn prefix_model(&self) -> Option<u64> { self.value }

    /// 読み終えた範囲が十進数字で、保持する値がその接頭辞に対応することを表す。
    pub closed spec fn valid(&self) -> bool {
        let bytes = self.bytes_model();
        let at = self.position_model() as int;
        let value = decimal_prefix(bytes, at as nat);
        &&& at <= bytes.len()
        &&& forall|i: int| 0 <= i < at ==> digit(Radix::Decimal, #[trigger] bytes[i])
        &&& match self.prefix_model() {
            Some(natural) => natural as int == value,
            None => value > u64::MAX,
        }
    }

    #[verifier::type_invariant]
    spec fn invariant(&self) -> bool { self.valid() }

    /// 字句の先頭から十進数字の読み取りを始める。
    pub fn new(word: &'a str) -> (reader: Self)
        ensures reader.valid(), reader.bytes_model() == word.spec_bytes(),
            reader.position_model() == 0, reader.prefix_model() == Some(0),
    {
        let bytes = word.as_bytes();
        assert(decimal_prefix(bytes@, 0) == 0);
        Self { bytes, at: 0, value: Some(0) }
    }

    /// 十進数字を一桁読み、末尾の場合は値を確定する。
    ///
    /// # Errors
    ///
    /// 空の字句や十進数字以外のバイトに達した場合は `InvalidDigits` を返す。
    /// 十進数字のみで値が `u64` を超える場合は、末尾で `OutOfRange` を返す。
    pub fn step(self) -> (result: Result<NaturalReadStep<'a>, NaturalRangeError>)
        ensures natural_read_step_matches(&self, result),
    {
        proof { use_type_invariant(&self); }
        let (bytes, at, value) = (self.bytes, self.at, self.value);
        if at == bytes.len() {
            reveal(decimal_natural_value);
            return if at == 0 { Err(NaturalRangeError::InvalidDigits) }
                else if let Some(natural) = value { Ok(NaturalReadStep::Done(natural)) }
                else { Err(NaturalRangeError::OutOfRange) };
        }

        let byte = bytes[at];
        if byte < b'0' || byte > b'9' {
            reveal(decimal_natural_value);
            return Err(NaturalRangeError::InvalidDigits);
        }

        let decimal = (byte - b'0') as u64;
        proof { decimal_step(bytes@, at as nat); }
        let next = match value {
            Some(natural) => match natural.checked_mul(10) {
                Some(tens) => tens.checked_add(decimal),
                None => None,
            },
            None => None,
        };
        Ok(NaturalReadStep::Continue(Self { bytes, at: at + 1, value: next }))
    }
}

/// 一歩の結果と、終端で確定する数学上の十進値の関係を表す。
pub open spec fn natural_read_step_matches(
    previous: &NaturalReader, result: Result<NaturalReadStep, NaturalRangeError>,
) -> bool {
    let bytes = previous.bytes_model();
    let at = previous.position_model() as int;
    &&& previous.valid()
    &&& if at < bytes.len() && b'0' <= bytes[at] <= b'9' {
        result matches Ok(NaturalReadStep::Continue(next))
            && next.valid() && next.bytes_model() == bytes && next.position_model() == at + 1
    } else {
        match result {
            Ok(NaturalReadStep::Done(value)) => at == bytes.len() && natural_u64_matches(bytes, Ok(value)),
            Err(error) => natural_u64_matches(bytes, Err(error)),
            _ => false,
        }
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
