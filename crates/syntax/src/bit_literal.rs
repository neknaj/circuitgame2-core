//! ビット列リテラルの表記幅と、値を表すのに必要なビット数を求める。

use crate::{AtomKind, atom::classify};
#[cfg(verus_only)]
use crate::bare_atom_kind;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 二進または十六進リテラルのビット数。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BitLiteralSize {
    /// 全桁を数えた幅。先頭の 0 も含む。
    pub written_bits: u128,
    /// 最上位の 1 から最下位までのビット数。値が 0 なら 0。
    pub required_bits: u128,
}

spec fn first_significant(bytes: Seq<u8>, at: int) -> bool {
    &&& 2 <= at <= bytes.len()
    &&& forall|i: int| 2 <= i < at ==> #[trigger] bytes[i] == b'0'
    &&& at < bytes.len() ==> bytes[at] != b'0'
}

spec fn leading_digit_bits(byte: u8) -> nat {
    if byte == b'0' { 0 }
    else if byte == b'1' { 1 }
    else if byte <= b'3' && b'2' <= byte { 2 }
    else if byte <= b'7' && b'4' <= byte { 3 }
    else { 4 }
}

/// ビット列リテラルの有無とビット数が、元の字句に対応することを表す。
pub closed spec fn bit_literal_size_matches(bytes: Seq<u8>, result: Option<BitLiteralSize>) -> bool {
    let kind = bare_atom_kind(bytes);
    if kind == Some(AtomKind::Binary) || kind == Some(AtomKind::Hexadecimal) {
        let unit = if kind == Some(AtomKind::Binary) { 1int } else { 4int };
        result matches Some(size)
            && size.written_bits == unit * (bytes.len() - 2)
            && exists|first: int| #[trigger] first_significant(bytes, first)
                && size.required_bits == (if first == bytes.len() { 0 }
                    else { unit * (bytes.len() - first - 1) + leading_digit_bits(bytes[first]) })
    } else {
        result is None
    }
}

fn first_nonzero(bytes: &[u8]) -> (at: usize)
    requires 2 <= bytes@.len(),
    ensures first_significant(bytes@, at as int),
{
    let mut at = 2;
    while at < bytes.len()
        invariant
            2 <= at <= bytes@.len(),
            forall|i: int| 2 <= i < at ==> #[trigger] bytes@[i] == b'0',
        decreases bytes@.len() - at,
    {
        if bytes[at] != b'0' {
            return at;
        }
        at += 1;
    }
    at
}

fn digit_bits(byte: u8) -> (width: u128)
    ensures width == leading_digit_bits(byte),
{
    match byte {
        b'0' => 0,
        b'1' => 1,
        b'2'..=b'3' => 2,
        b'4'..=b'7' => 3,
        _ => 4,
    }
}

/// `#b` または `#x` で始まるリテラルの表記幅と必要ビット数を返す。
///
/// 例えば `#x01` の表記幅は 8、必要ビット数は 1。字句の規則に合うビット列以外は `None`。
/// 数字列を機械整数に変換しないので、長いリテラルも元の桁から数えられる。
pub fn bit_literal_size(word: &str) -> (result: Option<BitLiteralSize>)
    ensures
        bit_literal_size_matches(word.spec_bytes(), result),
        result.is_none() <==> bit_literal_size_matches(word.spec_bytes(), None),
        result matches Some(size) ==> 0 < size.written_bits && size.required_bits <= size.written_bits,
{
    let kind = classify(word);
    let unit: u128 = match kind {
        Some(AtomKind::Binary) => 1,
        Some(AtomKind::Hexadecimal) => 4,
        _ => return None,
    };
    let bytes = word.as_bytes();
    proof { crate::atom::bit_atom_has_digits(bytes@, kind); }
    let first = first_nonzero(bytes);
    // 全桁が十六進でも、入力のバイト数の 4 倍は u128 に収まる。
    assert(bytes.len() <= u64::MAX);
    let written_bits = ((bytes.len() - 2) as u128) * unit;
    let required_bits = if first == bytes.len() {
        0
    } else {
        let high = digit_bits(bytes[first]);
        assert(high <= unit);
        ((bytes.len() - first - 1) as u128) * unit + high
    };
    assert(required_bits <= written_bits);
    Some(BitLiteralSize { written_bits, required_bits })
}

} // verus!
