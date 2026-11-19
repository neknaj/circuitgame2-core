use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    encode_utf8_valid_utf8, is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq, is_continuation_byte, length_of_first_scalar,
    pop_first_scalar, valid_utf8,
};

verus! {

#[derive(Clone, Copy)]
pub(crate) enum Boundary {
    NonSpace,
    LineEnd,
    AtomEnd,
    Colon,
    StringSpecial,
}

pub(crate) open spec fn whitespace(byte: u8) -> bool {
    byte == 32 || byte == 9 || byte == 10 || byte == 13
}

pub(crate) open spec fn stops(mode: Boundary, byte: u8) -> bool {
    match mode {
        Boundary::NonSpace => !whitespace(byte),
        Boundary::LineEnd => byte == 10 || byte == 13,
        Boundary::AtomEnd => whitespace(byte) || byte == 59 || byte == 40
            || byte == 41 || byte == 34,
        Boundary::Colon => byte == 58,
        Boundary::StringSpecial => byte == 34 || byte == 92 || byte == 10 || byte == 13,
    }
}

/// 指定した境界に初めて達するバイト位置を返す。
///
/// 該当する位置がなければ、入力スライスの長さを返す。
pub(crate) fn first_boundary(bytes: &[u8], mode: Boundary) -> (end: usize)
    ensures
        end <= bytes@.len(),
        end < bytes@.len() ==> stops(mode, bytes@[end as int]),
        forall|j: int| 0 <= j < end ==> !stops(mode, #[trigger] bytes@[j]),
{
    let mut i = 0;
    while i < bytes.len()
        invariant
            i <= bytes@.len(),
            forall|j: int| 0 <= j < i ==> !stops(mode, #[trigger] bytes@[j]),
        decreases bytes@.len() - i,
    {
        let byte = bytes[i];
        let space = matches!(byte, b' ' | b'\t' | b'\r' | b'\n');
        let stop = match mode {
            Boundary::NonSpace => !space,
            Boundary::LineEnd => matches!(byte, b'\r' | b'\n'),
            Boundary::AtomEnd => space || matches!(byte, b';' | b'(' | b')' | b'"'),
            Boundary::Colon => byte == b':',
            Boundary::StringSpecial => matches!(byte, b'"' | b'\\' | b'\r' | b'\n'),
        };
        assert(stop == stops(mode, bytes@[i as int]));
        if stop {
            return i;
        }
        i += 1;
    }
    i
}

proof fn ascii_prefix_boundary(bytes: Seq<u8>, end: int)
    requires
        valid_utf8(bytes),
        0 <= end <= bytes.len(),
        forall|i: int| 0 <= i < end ==> #[trigger] bytes[i] < 128,
    ensures
        is_char_boundary(bytes, end),
    decreases end,
{
    if end > 0 {
        assert(bytes[0] < 128);
        assert(length_of_first_scalar(bytes) == 1);
        let rest = pop_first_scalar(bytes);
        reveal_with_fuel(valid_utf8, 2);
        assert forall|i: int| 0 <= i < end - 1 implies #[trigger] rest[i] < 128 by {
            assert(rest[i] == bytes[i + 1]);
        }
        ascii_prefix_boundary(rest, end - 1);
    }
    reveal_with_fuel(is_char_boundary, 2);
}

/// 最初の境界で入力を切り分ける。
///
/// 後半は境界のバイトから始まる。境界がなければ後半は空になる。
pub(crate) fn split_at_boundary(source: &str, mode: Boundary) -> (parts: (&str, &str))
    ensures
        parts.0.spec_bytes() + parts.1.spec_bytes() =~= source.spec_bytes(),
        parts.1.spec_bytes().len() > 0 ==> stops(mode, parts.1.spec_bytes()[0]),
        forall|j: int| 0 <= j < parts.0.spec_bytes().len()
            ==> !stops(mode, #[trigger] parts.0.spec_bytes()[j]),
        is_char_boundary(source.spec_bytes(), parts.0.spec_bytes().len() as int),
{
    let input = source.as_bytes();
    let end = first_boundary(input, mode);
    proof {
        let bytes = source.spec_bytes();
        encode_utf8_valid_utf8(source@);
        if matches!(mode, Boundary::NonSpace) {
            assert forall|i: int| 0 <= i < end implies #[trigger] bytes[i] < 128 by {
                assert(!stops(mode, bytes[i]));
            }
            ascii_prefix_boundary(bytes, end as int);
        } else if end < bytes.len() {
            assert(bytes[end as int] < 128);
            assert(!is_continuation_byte(bytes[end as int]));
            is_char_boundary_iff_not_is_continuation_byte(bytes, end as int);
        } else {
            assert(end == bytes.len());
            is_char_boundary_start_end_of_seq(bytes);
        }
        assert(is_char_boundary(bytes, end as int));
    }
    let parts = source.split_at(end);
    assert(parts.0.spec_bytes().len() == end);
    parts
}

/// 先頭の ASCII 1バイトを消費し、直後から始まる接尾辞を返す。
pub(crate) fn after_ascii(source: &str) -> (suffix: &str)
    requires
        source.spec_bytes().len() > 0,
        source.spec_bytes()[0] < 128,
    ensures
        suffix.spec_bytes() =~= source.spec_bytes()[1..],
        is_char_boundary(source.spec_bytes(), 1),
{
    proof {
        encode_utf8_valid_utf8(source@);
        ascii_prefix_boundary(source.spec_bytes(), 1);
    }
    source.split_at(1).1
}

/// 空でない UTF-8 文字列を、先頭の Unicode スカラー値を表す部分と残りに分ける。
pub(crate) fn split_first_scalar(source: &str) -> (parts: (&str, &str))
    requires
        source.spec_bytes().len() > 0,
    ensures
        0 < parts.0.spec_bytes().len() <= 4,
        parts.0.spec_bytes().len() == length_of_first_scalar(source.spec_bytes()),
        parts.0.spec_bytes() + parts.1.spec_bytes() =~= source.spec_bytes(),
        is_char_boundary(source.spec_bytes(), parts.0.spec_bytes().len() as int),
{
    let lead = source.as_bytes()[0];
    let width = if lead < 0x80 {
        1
    } else if lead < 0xe0 {
        2
    } else if lead < 0xf0 {
        3
    } else {
        4
    };
    proof {
        let bytes = source.spec_bytes();
        encode_utf8_valid_utf8(source@);
        reveal_with_fuel(valid_utf8, 2);
        assert(width == length_of_first_scalar(bytes));
        reveal_with_fuel(is_char_boundary, 2);
        assert(is_char_boundary(bytes, width as int));
    }
    let parts = source.split_at(width);
    assert(parts.0.spec_bytes().len() == width);
    parts
}

} // verus!
