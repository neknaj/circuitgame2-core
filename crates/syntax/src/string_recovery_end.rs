//! 開き引用符に続く入力のうち、回復時に文字列として消費する範囲を定める。

use vstd::prelude::*;
use vstd::utf8::{
    is_leading_byte_width_1, is_leading_byte_width_2, is_leading_byte_width_3,
    length_of_first_scalar, valid_first_scalar,
};

verus! {

pub(super) open spec fn recovery_scalar_width(lead: u8) -> int {
    if is_leading_byte_width_1(lead) {
        1
    } else if is_leading_byte_width_2(lead) {
        2
    } else if is_leading_byte_width_3(lead) {
        3
    } else {
        4
    }
}

pub(super) proof fn recovery_scalar_width_matches(bytes: Seq<u8>)
    requires 0 < bytes.len(), valid_first_scalar(bytes),
    ensures recovery_scalar_width(bytes[0]) == length_of_first_scalar(bytes),
{
}

/// 未エスケープの閉じ引用符は含め、CR と LF は次の字句に残す。
///
/// バックスラッシュに続くスカラー値は、エスケープとして無効でも文字列の一部とする。
/// 直後が CR、LF、入力末尾の場合は、バックスラッシュの直後で終わる。
pub(super) closed spec fn string_recovery_end_from(bytes: Seq<u8>, at: int) -> int
    decreases bytes.len() - at,
{
    if at < 0 || bytes.len() <= at {
        bytes.len() as int
    } else {
        match bytes[at] {
            b'"' => at + 1,
            b'\r' | b'\n' => at,
            b'\\' => {
                let next = at + 1;
                if next == bytes.len() || bytes[next] == b'\r' || bytes[next] == b'\n' {
                    next
                } else {
                    let after = next + recovery_scalar_width(bytes[next]);
                    if after <= bytes.len() {
                        string_recovery_end_from(bytes, after)
                    } else {
                        bytes.len() as int
                    }
                }
            },
            _ => string_recovery_end_from(bytes, at + 1),
        }
    }
}

pub(super) proof fn string_recovery_end_at_stop(bytes: Seq<u8>, at: int)
    requires 0 <= at <= bytes.len(),
        at == bytes.len() || bytes[at] == b'"' || bytes[at] == b'\r' || bytes[at] == b'\n',
    ensures string_recovery_end_from(bytes, at) == if at < bytes.len() && bytes[at] == b'"' { at + 1 } else { at },
{
}

pub(super) proof fn string_recovery_end_after_escape(bytes: Seq<u8>, slash: int, after: int)
    requires
        0 <= slash < after <= bytes.len(),
        bytes[slash] == b'\\',
        ({
            let next = slash + 1;
            if next == bytes.len() || bytes[next] == b'\r' || bytes[next] == b'\n' {
                after == next
            } else {
                after == next + recovery_scalar_width(bytes[next])
            }
        }),
    ensures string_recovery_end_from(bytes, slash) == string_recovery_end_from(bytes, after),
{
}

/// 引用符、バックスラッシュ、改行のない区間をまとめて進めても、回復終端は変わらない。
pub(super) proof fn skip_ordinary_string_bytes(bytes: Seq<u8>, from: int, to: int)
    requires
        0 <= from <= to <= bytes.len(),
        forall|i: int| from <= i < to ==> {
            let byte = #[trigger] bytes[i];
            byte != b'"' && byte != b'\\' && byte != b'\r' && byte != b'\n'
        },
    ensures string_recovery_end_from(bytes, from) == string_recovery_end_from(bytes, to),
    decreases to - from,
{
    if from < to {
        reveal(string_recovery_end_from);
        skip_ordinary_string_bytes(bytes, from + 1, to);
        assert(string_recovery_end_from(bytes, from) == string_recovery_end_from(bytes, from + 1));
    }
}

proof fn string_recovery_end_examples() {
    // 無効なエスケープの「日」は3バイトであり、続く右括弧も閉じ引用符まで文字列に含まれる。
    assert(string_recovery_end_from(seq![b'"', b'\\', 0xe6u8, 0x97u8, 0xa5u8, b')', b'"', b')'], 1) == 7)
        by (compute);
    assert(string_recovery_end_from(seq![b'"', b'\\', b'\r', b'\n', b')'], 1) == 2) by (compute);
    assert(string_recovery_end_from(seq![b'"', b'\\', b'"', b')'], 1) == 4) by (compute);
}

} // verus!
