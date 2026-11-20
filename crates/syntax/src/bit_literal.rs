//! ビット列リテラルの表記幅と、値を表すのに必要なビット数を求める。

use crate::{AtomKind, atom::classify};
#[cfg(verus_only)]
use crate::bare_atom_kind;
#[cfg(verus_only)]
use crate::digits::{Radix, digit};
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

/// 字句を検査した二進または十六進のリテラル。桁は元の文字列から借りる。
#[derive(Clone, Copy, Debug)]
pub struct BitLiteral<'a> {
    word: &'a str,
    unit: u64,
}

spec fn digit_unit(bytes: Seq<u8>) -> int {
    match bare_atom_kind(bytes) {
        Some(AtomKind::Binary) => 1,
        Some(AtomKind::Hexadecimal) => 4,
        _ => 0,
    }
}

spec fn digit_value(byte: u8) -> int {
    if byte <= b'9' { byte - b'0' }
    else if byte <= b'F' { byte - b'A' + 10 }
    else { byte - b'a' + 10 }
}

spec fn bit_in_digit(byte: u8, offset: int) -> bool {
    let place = if offset == 0 { 1int }
        else if offset == 1 { 2int }
        else if offset == 2 { 4int }
        else { 8int };
    (digit_value(byte) / place) % 2 == 1
}

/// 元の字句の低位から数えたビットを表す。表記幅を超える位置は 0 とする。
pub closed spec fn bit_literal_value_at(bytes: Seq<u8>, bit: nat) -> bool {
    let unit = digit_unit(bytes);
    if unit == 0 || (bit as int) / unit >= bytes.len() - 2 {
        false
    } else {
        bit_in_digit(bytes[bytes.len() - 1 - (bit as int) / unit], (bit as int) % unit)
    }
}

impl<'a> BitLiteral<'a> {
    /// 検査した元のリテラルを表す。
    pub closed spec fn word_model(&self) -> &'a str { self.word }

    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        (self.unit == 1 || self.unit == 4) && self.unit == digit_unit(self.word.spec_bytes())
    }

    /// 最下位を 0 としてビットを読む。表記幅より上のビットは `false`。
    ///
    /// 字句の検査は [`read_bit_literal`] で済んでいるため、指定位置の桁だけを調べる。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_syntax::read_bit_literal;
    /// let literal = read_bit_literal("#xAf").unwrap();
    /// assert_eq!([literal.bit(0), literal.bit(4), literal.bit(7), literal.bit(8)],
    ///            [true, false, true, false]);
    /// ```
    pub fn bit(&self, index: u64) -> (value: bool)
        ensures value == bit_literal_value_at(self.word_model().spec_bytes(), index as nat),
    {
        proof { use_type_invariant(self); }
        let bytes = self.word.as_bytes();
        proof { crate::atom::bit_atom_has_digits(bytes@, bare_atom_kind(bytes@)); }
        assert(bytes.len() <= u64::MAX);
        let from_end = index / self.unit;
        if from_end >= (bytes.len() - 2) as u64 {
            return false;
        }
        let at = bytes.len() - 1 - from_end as usize;
        let byte = bytes[at];
        let value = if byte <= b'9' { byte - b'0' }
            else if byte <= b'F' { byte - b'A' + 10 }
            else { byte - b'a' + 10 };
        let offset = index % self.unit;
        assert(offset <= 3);
        let place = match offset { 0 => 1, 1 => 2, 2 => 4, _ => 8 };
        (value / place) % 2 == 1
    }
}

/// 二進・十六進リテラルを検査し、元の字句を借りる。字句が無効なら `None`。
pub fn read_bit_literal(word: &str) -> (result: Option<BitLiteral<'_>>)
    ensures
        result.is_some() <==> (bare_atom_kind(word.spec_bytes()) == Some(AtomKind::Binary)
            || bare_atom_kind(word.spec_bytes()) == Some(AtomKind::Hexadecimal)),
        result matches Some(literal) ==> literal.word_model() == word,
{
    let unit = match classify(word) {
        Some(AtomKind::Binary) => 1,
        Some(AtomKind::Hexadecimal) => 4,
        _ => return None,
    };
    Some(BitLiteral { word, unit })
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

proof fn high_digit_bit_is_zero(byte: u8, offset: int)
    requires digit(Radix::Hexadecimal, byte), leading_digit_bits(byte) <= offset < 4,
    ensures !bit_in_digit(byte, offset),
{
    if offset == 0 {
        assert(byte == b'0');
    } else if offset == 1 {
        assert(0 <= digit_value(byte) < 2);
    } else if offset == 2 {
        assert(0 <= digit_value(byte) < 4);
    } else {
        assert(0 <= digit_value(byte) < 8);
    }
}

proof fn leading_digit_bit_is_one(byte: u8)
    requires digit(Radix::Hexadecimal, byte), byte != b'0',
    ensures bit_in_digit(byte, leading_digit_bits(byte) - 1),
{
    let width = leading_digit_bits(byte);
    if width == 1 {
        assert(digit_value(byte) == 1);
    } else if width == 2 {
        assert(2 <= digit_value(byte) < 4);
    } else if width == 3 {
        assert(4 <= digit_value(byte) < 8);
    } else {
        assert(8 <= digit_value(byte) < 16);
    }
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

/// 表記の桁数で、そのリテラルの値をすべて表せることを示す。
pub proof fn bit_literal_required_width_fits_spelling(bytes: Seq<u8>, size: BitLiteralSize)
    requires bit_literal_size_matches(bytes, Some(size)),
    ensures bytes.len() > 2, 0 < size.written_bits, size.required_bits <= size.written_bits,
{
    let kind = bare_atom_kind(bytes);
    crate::atom::bit_atom_has_digits(bytes, kind);
    let unit = digit_unit(bytes);
    let first = choose|first: int| #[trigger] first_significant(bytes, first)
        && size.required_bits == (if first == bytes.len() { 0 }
            else { unit * (bytes.len() - first - 1) + leading_digit_bits(bytes[first]) });
    if first < bytes.len() && unit == 1 {
        assert(bytes[first] == b'1');
    }
}

/// 二進・十六進の字句は、接頭辞の後に少なくとも一桁を持つ。
pub proof fn bit_literal_kind_has_digits(bytes: Seq<u8>)
    requires bare_atom_kind(bytes) == Some(AtomKind::Binary) || bare_atom_kind(bytes) == Some(AtomKind::Hexadecimal),
    ensures bytes.len() > 2,
{
    crate::atom::bit_atom_has_digits(bytes, bare_atom_kind(bytes));
}

/// 必要ビット数以上の位置には 1 がないことを示す。
pub proof fn bit_literal_high_bits_are_zero(bytes: Seq<u8>, size: BitLiteralSize, bit: nat)
    requires bit_literal_size_matches(bytes, Some(size)), size.required_bits <= bit,
    ensures !bit_literal_value_at(bytes, bit),
{
    let kind = bare_atom_kind(bytes);
    crate::atom::bit_atom_has_digits(bytes, kind);
    let unit = digit_unit(bytes);
    let bit = bit as int;
    let from_end = bit / unit;
    if from_end < bytes.len() - 2 {
        let first = choose|first: int| #[trigger] first_significant(bytes, first)
            && size.required_bits == (if first == bytes.len() { 0 }
                else { unit * (bytes.len() - first - 1) + leading_digit_bits(bytes[first]) });
        let at = bytes.len() - 1 - from_end;
        let offset = bit % unit;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bit, unit);
        vstd::arithmetic::div_mod::lemma_mod_bound(bit, unit);
        if at < first {
            assert(bytes[at] == b'0');
        } else {
            assert(first < bytes.len());
            if unit == 1 {
                assert(offset == 0);
            } else {
                assert(unit == 4);
            }
            assert(at == first) by (nonlinear_arith)
                requires 0 < unit, 0 <= offset < unit, at >= first,
                    bit == unit * (bytes.len() - at - 1) + offset,
                    unit * (bytes.len() - first - 1) + leading_digit_bits(bytes[first]) <= bit,
            ;
            high_digit_bit_is_zero(bytes[at], offset);
        }
    }
}

/// 値が 0 でなければ、必要ビット数の最後の位置に 1 があることを示す。
pub proof fn bit_literal_top_bit_is_one(bytes: Seq<u8>, size: BitLiteralSize)
    requires bit_literal_size_matches(bytes, Some(size)), size.required_bits > 0,
    ensures bit_literal_value_at(bytes, (size.required_bits - 1) as nat),
{
    let kind = bare_atom_kind(bytes);
    crate::atom::bit_atom_has_digits(bytes, kind);
    let unit = digit_unit(bytes);
    let first = choose|first: int| #[trigger] first_significant(bytes, first)
        && size.required_bits == (if first == bytes.len() { 0 }
            else { unit * (bytes.len() - first - 1) + leading_digit_bits(bytes[first]) });
    let byte = bytes[first];
    let offset = leading_digit_bits(byte) - 1;
    let from_end = bytes.len() - first - 1;
    let bit = size.required_bits - 1;
    assert(0 <= offset < unit) by {
        if unit == 1 { assert(byte == b'1'); }
    };
    assert(bit == from_end * unit + offset);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(bit, unit, from_end, offset);
    leading_digit_bit_is_one(byte);
}

/// 同じ字句の表記幅は基数と先頭の 0 を含む桁数から決まる。
pub proof fn bit_literal_written_widths_agree(bytes: Seq<u8>, left: BitLiteralSize, right: BitLiteralSize)
    requires bit_literal_size_matches(bytes, Some(left)), bit_literal_size_matches(bytes, Some(right)),
    ensures left.written_bits == right.written_bits,
{
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
    let Some(literal) = read_bit_literal(word) else { return None; };
    proof {
        use_type_invariant(&literal);
        assert(literal.unit == 1 || literal.unit == 4);
        assert(literal.unit == digit_unit(word.spec_bytes()));
    }
    let unit = literal.unit as u128;
    let bytes = word.as_bytes();
    proof { crate::atom::bit_atom_has_digits(bytes@, bare_atom_kind(bytes@)); }
    let first = first_nonzero(bytes);
    // 全桁が十六進でも、入力のバイト数の 4 倍は u128 に収まる。
    assert(bytes.len() <= u64::MAX);
    assert(unit == 1 || unit == 4);
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
