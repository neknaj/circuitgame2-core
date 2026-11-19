//! 文字列の先頭から規則に従って読み進めたとき、最初に起きる違反を定める。

use super::{Boundary, Error, ErrorKind, boundary, quoted_prefix::quoted_body, string_error_site};
use vstd::prelude::*;

verus! {

/// 違反が生じた位置と診断範囲の対応を表す。末尾の単独のバックスラッシュでは、
/// 文字列本体をその直前まで読み、診断は開き引用符から入力末尾までを指す。
pub(super) open spec fn first_error_matches_stop(bytes: Seq<u8>, opening: int, stop: int, error: Error) -> bool {
    match error.kind {
        ErrorKind::InvalidEscape { .. } | ErrorKind::NewlineInString { .. } => stop == error.span.start - opening,
        ErrorKind::UnterminatedString => stop == bytes.len()
            || (0 <= stop < bytes.len() && stop + 1 == bytes.len() && bytes[stop] == 92),
        _ => false,
    }
}

pub(super) closed spec fn first_string_error(bytes: Seq<u8>, opening: int, error: Error) -> bool {
    string_error_site(bytes, opening, error)
        && exists|stop: int| 1 <= stop <= bytes.len() && #[trigger] quoted_body(bytes, 1, stop)
            && first_error_matches_stop(bytes, opening, stop, error)
}

pub(super) proof fn record_first_string_error(bytes: Seq<u8>, opening: int, stop: int, error: Error)
    requires
        1 <= stop <= bytes.len(),
        quoted_body(bytes, 1, stop),
        string_error_site(bytes, opening, error),
        first_error_matches_stop(bytes, opening, stop, error),
    ensures first_string_error(bytes, opening, error),
{
}

spec fn invalid_body_stop(bytes: Seq<u8>, stop: int) -> bool {
    stop == bytes.len() || (0 <= stop < bytes.len() && (
        bytes[stop] == 10 || bytes[stop] == 13 || (bytes[stop] == 92
            && (stop + 1 == bytes.len() || (bytes[stop + 1] != 34 && bytes[stop + 1] != 92)))
    ))
}

proof fn error_stop_is_invalid(bytes: Seq<u8>, opening: int, stop: int, error: Error)
    requires
        1 <= stop <= bytes.len(),
        string_error_site(bytes, opening, error),
        first_error_matches_stop(bytes, opening, stop, error),
    ensures invalid_body_stop(bytes, stop),
{
}

proof fn invalid_body_stops_agree(bytes: Seq<u8>, from: int, left: int, right: int)
    requires
        1 <= from <= left <= bytes.len(),
        from <= right <= bytes.len(),
        quoted_body(bytes, from, left),
        quoted_body(bytes, from, right),
        invalid_body_stop(bytes, left),
        invalid_body_stop(bytes, right),
    ensures left == right,
    decreases left - from,
{
    reveal(quoted_body);
    if from < left && from < right {
        let width: int = if bytes[from] == 92 { 2 } else { 1 };
        invalid_body_stops_agree(bytes, from + width, left, right);
    } else if left != right {
        // 先に止まる候補の位置を、もう一方の妥当な本体が通過することはできない。
        assert(from < bytes.len());
        if bytes[from] == 92 {
            assert(from + 1 < bytes.len() && (bytes[from + 1] == 34 || bytes[from + 1] == 92));
        } else {
            assert(!boundary::stops(Boundary::StringSpecial, bytes[from]));
            assert(bytes[from] != 10 && bytes[from] != 13);
        }
        assert(!invalid_body_stop(bytes, from));
    }
}

/// 最初に壊れた位置と、その位置のバイト列から、種別・主範囲・開き引用符の位置を一意に決める。
pub(super) proof fn first_string_errors_agree(bytes: Seq<u8>, opening: int, a: Error, b: Error)
    requires first_string_error(bytes, opening, a), first_string_error(bytes, opening, b),
    ensures a == b,
{
    let left = choose|stop: int| 1 <= stop <= bytes.len() && #[trigger] quoted_body(bytes, 1, stop)
        && first_error_matches_stop(bytes, opening, stop, a);
    let right = choose|stop: int| 1 <= stop <= bytes.len() && #[trigger] quoted_body(bytes, 1, stop)
        && first_error_matches_stop(bytes, opening, stop, b);
    error_stop_is_invalid(bytes, opening, left, a);
    error_stop_is_invalid(bytes, opening, right, b);
    invalid_body_stops_agree(bytes, 1, left, right);
    assert(a.kind == b.kind);
    assert(a.span.start == b.span.start && a.span.end == b.span.end);
}

} // verus!
