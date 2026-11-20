use crate::AtomKind;
use crate::boundary::{Boundary, after_ascii, split_at_boundary};
#[cfg(verus_only)]
use crate::digits::digit;
use crate::digits::{Radix, matches_digits};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{encode_utf8_decode_utf8, encode_utf8_valid_utf8, is_char_boundary_iff_not_is_continuation_byte};

verus! {

spec fn digit_sequence(bytes: Seq<u8>, radix: Radix) -> bool {
    &&& bytes.len() > 0
    &&& forall|i: int| 0 <= i < bytes.len() ==> digit(radix, #[trigger] bytes[i])
}

pub closed spec fn bare_atom_kind(bytes: Seq<u8>) -> Option<AtomKind> {
    if bytes.len() >= 2 && bytes[0] == 35 && bytes[1] == 98 {
        if digit_sequence(bytes[2..], Radix::Binary) { Some(AtomKind::Binary) } else { None }
    } else if bytes.len() >= 2 && bytes[0] == 35 && bytes[1] == 120 {
        if digit_sequence(bytes[2..], Radix::Hexadecimal) { Some(AtomKind::Hexadecimal) } else { None }
    } else if bytes.len() >= 1 && bytes[0] == 45 {
        if digit_sequence(bytes[1..], Radix::Decimal) { Some(AtomKind::NegativeInteger) } else { None }
    } else if digit_sequence(bytes, Radix::Decimal) {
        Some(AtomKind::Natural)
    } else {
        path_kind(bytes)
    }
}

/// 自然数として分類されたアトムが十進の値を持つことを示す。
pub proof fn natural_atom_has_value(bytes: Seq<u8>)
    requires bare_atom_kind(bytes) == Some(AtomKind::Natural),
    ensures crate::decimal_natural_value(bytes).is_some(),
{
    crate::natural::digits_admit_value(bytes);
}

pub(crate) proof fn bit_atom_has_digits(bytes: Seq<u8>, kind: Option<AtomKind>)
    requires
        kind == bare_atom_kind(bytes),
        kind == Some(AtomKind::Binary) || kind == Some(AtomKind::Hexadecimal),
    ensures
        bytes.len() > 2,
        kind == Some(AtomKind::Binary) ==> forall|i: int| 2 <= i < bytes.len()
            ==> #[trigger] bytes[i] == b'0' || bytes[i] == b'1',
{
    if kind == Some(AtomKind::Binary) {
        assert forall|i: int| 2 <= i < bytes.len() implies #[trigger] bytes[i] == b'0' || bytes[i] == b'1' by {
            assert(bytes[2..][i - 2] == bytes[i]);
        };
    }
}

pub(crate) fn classify(atom: &str) -> (result: Option<AtomKind>)
    ensures
        result == bare_atom_kind(atom.spec_bytes()),
        result != Some(AtomKind::String),
{
    let bytes = atom.as_bytes();
    if bytes.len() >= 2 && bytes[0] == b'#' && matches!(bytes[1], b'b' | b'x') {
        let tail = after_ascii(after_ascii(atom));
        assert(tail.spec_bytes() =~= bytes@[2..]);
        let (radix, kind) = if bytes[1] == b'b' {
            (Radix::Binary, AtomKind::Binary)
        } else {
            (Radix::Hexadecimal, AtomKind::Hexadecimal)
        };
        if matches_digits(tail.as_bytes(), radix) { Some(kind) } else { None }
    } else if bytes.len() > 0 && bytes[0] == b'-' {
        let tail = after_ascii(atom);
        if matches_digits(tail.as_bytes(), Radix::Decimal) {
            Some(AtomKind::NegativeInteger)
        } else {
            None
        }
    } else if matches_digits(bytes, Radix::Decimal) {
        Some(AtomKind::Natural)
    } else {
        classify_path(atom)
    }
}

spec fn name_start(byte: u8) -> bool {
    65 <= byte <= 90 || 97 <= byte <= 122 || byte == 95
}

spec fn name_continue(byte: u8) -> bool {
    name_start(byte) || 48 <= byte <= 57 || byte == 45
}

spec fn name_component(bytes: Seq<u8>) -> bool {
    &&& bytes.len() > 0
    &&& name_start(bytes[0])
    &&& forall|i: int| 0 < i < bytes.len() ==> name_continue(#[trigger] bytes[i])
}

fn is_name(name: &str) -> (accepted: bool)
    ensures
        accepted == name_component(name.spec_bytes()),
{
    let bytes = name.as_bytes();
    if bytes.len() == 0 || !matches!(bytes[0], b'A'..=b'Z' | b'a'..=b'z' | b'_') {
        return false;
    }
    let mut i = 1;
    while i < bytes.len()
        invariant
            bytes@ == name.spec_bytes(),
            1 <= i <= bytes@.len(),
            name_start(bytes@[0]),
            forall|j: int| 0 < j < i ==> name_continue(#[trigger] bytes@[j]),
        decreases bytes@.len() - i,
    {
        if !matches!(bytes[i], b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' | b'-') {
            assert(!name_continue(bytes@[i as int]));
            assert(!name_component(bytes@));
            return false;
        }
        i += 1;
    }
    true
}

spec fn first_colon(bytes: Seq<u8>, at: int) -> bool {
    &&& 0 <= at <= bytes.len()
    &&& (at < bytes.len() ==> bytes[at] == 58)
    &&& forall|i: int| 0 <= i < at ==> #[trigger] bytes[i] != 58
}

spec fn colon_pair(bytes: Seq<u8>, at: int) -> bool {
    0 <= at && at + 1 < bytes.len() && bytes[at] == 58 && bytes[at + 1] == 58
}

spec fn path_body(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    if exists|at: int| first_colon(bytes, at) {
        let at = choose|at: int| first_colon(bytes, at);
        name_component(bytes[..at]) && (
            at == bytes.len() || (colon_pair(bytes, at) && path_body(bytes[(at + 2)..]))
        )
    } else {
        false
    }
}

proof fn path_body_at(bytes: Seq<u8>, at: int)
    requires
        first_colon(bytes, at),
    ensures
        path_body(bytes) == (name_component(bytes[..at]) && (
            at == bytes.len() || (colon_pair(bytes, at) && path_body(bytes[(at + 2)..]))
        )),
{
    reveal_with_fuel(path_body, 1);
    assert(exists|other: int| first_colon(bytes, other));
    let other = choose|other: int| first_colon(bytes, other);
    if at < other {
        assert(bytes[at] == 58 && bytes[at] != 58);
    } else if other < at {
        assert(bytes[other] == 58 && bytes[other] != 58);
    }
}

fn has_colon_pair(source: &str) -> (pair: bool)
    ensures pair == colon_pair(source.spec_bytes(), 0),
{
    let bytes = source.as_bytes();
    bytes.len() >= 2 && bytes[0] == b':' && bytes[1] == b':'
}

spec fn path_kind(bytes: Seq<u8>) -> Option<AtomKind> {
    if colon_pair(bytes, 0) {
        if path_body(bytes[2..]) { Some(AtomKind::AbsolutePath) } else { None }
    } else if name_component(bytes) {
        Some(AtomKind::Name)
    } else if path_body(bytes) {
        Some(AtomKind::RelativePath)
    } else {
        None
    }
}

fn classify_path(atom: &str) -> (result: Option<AtomKind>)
    ensures result == path_kind(atom.spec_bytes()),
{
    let absolute = has_colon_pair(atom);
    let body = if absolute {
        let after_first = after_ascii(atom);
        let tail = after_ascii(after_first);
        assert(tail.spec_bytes() =~= atom.spec_bytes()[2..]);
        tail
    } else {
        atom
    };
    let mut remaining = body;
    let mut qualified = absolute;
    loop
        invariant
            absolute == colon_pair(atom.spec_bytes(), 0),
            body.spec_bytes() =~= if absolute { atom.spec_bytes()[2..] } else { atom.spec_bytes() },
            path_body(remaining.spec_bytes()) == path_body(body.spec_bytes()),
            !qualified ==> remaining == body,
            qualified && !absolute ==> !name_component(body.spec_bytes()),
        decreases remaining.spec_bytes().len(),
    {
        let (name, separator) = split_at_boundary(remaining, Boundary::Colon);
        let ghost bytes = remaining.spec_bytes();
        let ghost at = name.spec_bytes().len() as int;
        proof {
            assert(name.spec_bytes() =~= bytes[..at]);
            assert(separator.spec_bytes() =~= bytes[at..]);
            assert(first_colon(bytes, at));
            path_body_at(bytes, at);
        }
        if !is_name(name) {
            return None;
        }
        if separator.as_bytes().len() == 0 {
            return Some(if absolute {
                AtomKind::AbsolutePath
            } else if qualified {
                AtomKind::RelativePath
            } else {
                AtomKind::Name
            });
        }
        if !has_colon_pair(separator) {
            return None;
        }
        if !qualified {
            assert(bytes[at] == 58);
            assert(!name_component(body.spec_bytes()));
        }
        let tail = after_ascii(after_ascii(separator));
        assert(tail.spec_bytes() =~= bytes[(at + 2)..]);
        remaining = tail;
        qualified = true;
    }
}

/// 親パスと末尾の名前が、完全修飾名の元のバイト列を復元することを表す。
pub closed spec fn absolute_path_parts(path: &str, parent: Option<&str>, name: &str) -> bool {
    &&& bare_atom_kind(path.spec_bytes()) == Some(AtomKind::AbsolutePath)
    &&& body_path_parts(path.spec_bytes().skip(2), parent, name)
}

spec fn body_path_parts(bytes: Seq<u8>, parent: Option<&str>, name: &str) -> bool {
    &&& name_component(name.spec_bytes())
    &&& match parent {
        None => name.spec_bytes() == bytes,
        Some(parent) => {
            let prefix = parent.spec_bytes();
            let separator = prefix.len();
            &&& prefix.len() > 0
            &&& separator + 2 < bytes.len()
            &&& prefix == bytes.take(separator as int)
            &&& colon_pair(bytes, separator as int)
            &&& name.spec_bytes() == bytes.skip((separator + 2) as int)
        },
    }
}

/// 先頭の名前と残りの成分が、相対パスの元のバイト列を復元することを表す。
pub closed spec fn relative_path_parts(path: &str, head: &str, middle: Option<&str>, name: &str) -> bool {
    let bytes = path.spec_bytes();
    let at = head.spec_bytes().len() as int;
    &&& bare_atom_kind(bytes) == Some(AtomKind::RelativePath)
    &&& name_component(head.spec_bytes())
    &&& head.spec_bytes() == bytes.take(at)
    &&& colon_pair(bytes, at)
    &&& body_path_parts(bytes.skip(at + 2), middle, name)
}

proof fn component_has_no_colon(bytes: Seq<u8>, at: int)
    requires name_component(bytes), 0 <= at < bytes.len(),
    ensures bytes[at] != b':',
{
}

proof fn body_path_parts_agree(
    bytes: Seq<u8>, left_parent: Option<&str>, left: &str, right_parent: Option<&str>, right: &str,
)
    requires body_path_parts(bytes, left_parent, left), body_path_parts(bytes, right_parent, right),
    ensures left@ == right@,
        match (left_parent, right_parent) {
            (Some(a), Some(b)) => a@ == b@,
            (None, None) => true,
            _ => false,
        },
{
    match (left_parent, right_parent) {
        (Some(a), Some(b)) => {
            let i = a.spec_bytes().len() as int;
            let j = b.spec_bytes().len() as int;
            // 短い親パスを選ぶと、末尾の名前に後続の区切り記号が残る。
            if i < j {
                component_has_no_colon(left.spec_bytes(), j - i - 1);
                assert(left.spec_bytes()[j - i - 1] == bytes[j + 1]);
            } else if j < i {
                component_has_no_colon(right.spec_bytes(), i - j - 1);
                assert(right.spec_bytes()[i - j - 1] == bytes[i + 1]);
            }
            encode_utf8_decode_utf8(a@);
            encode_utf8_decode_utf8(b@);
        },
        (Some(a), None) => component_has_no_colon(right.spec_bytes(), a.spec_bytes().len() as int),
        (None, Some(b)) => component_has_no_colon(left.spec_bytes(), b.spec_bytes().len() as int),
        (None, None) => {},
    }
    encode_utf8_decode_utf8(left@);
    encode_utf8_decode_utf8(right@);
}

/// 同じ完全修飾名から切り出した親パスと末尾の名前は、文字列の内容が一致する。
pub proof fn absolute_path_parts_agree(
    left_path: &str, left_parent: Option<&str>, left: &str,
    right_path: &str, right_parent: Option<&str>, right: &str,
)
    requires
        left_path@ == right_path@,
        absolute_path_parts(left_path, left_parent, left),
        absolute_path_parts(right_path, right_parent, right),
    ensures left@ == right@,
        match (left_parent, right_parent) {
            (Some(a), Some(b)) => a@ == b@,
            (None, None) => true,
            _ => false,
        },
{
    body_path_parts_agree(left_path.spec_bytes().skip(2), left_parent, left, right_parent, right);
}

/// 同じ相対パスを分解した先頭の名前、中間のパス、末尾の名前は内容が一致する。
pub proof fn relative_path_parts_agree(
    left_path: &str, left_head: &str, left_middle: Option<&str>, left: &str,
    right_path: &str, right_head: &str, right_middle: Option<&str>, right: &str,
)
    requires
        left_path@ == right_path@,
        relative_path_parts(left_path, left_head, left_middle, left),
        relative_path_parts(right_path, right_head, right_middle, right),
    ensures left_head@ == right_head@, left@ == right@,
        match (left_middle, right_middle) {
            (Some(a), Some(b)) => a@ == b@,
            (None, None) => true,
            _ => false,
        },
{
    let i = left_head.spec_bytes().len() as int;
    let j = right_head.spec_bytes().len() as int;
    let bytes = left_path.spec_bytes();
    if i < j {
        component_has_no_colon(right_head.spec_bytes(), i);
        assert(right_head.spec_bytes()[i] == bytes[i]);
    } else if j < i {
        component_has_no_colon(left_head.spec_bytes(), j);
        assert(left_head.spec_bytes()[j] == bytes[j]);
    }
    encode_utf8_decode_utf8(left_head@);
    encode_utf8_decode_utf8(right_head@);
    body_path_parts_agree(bytes.skip(i + 2), left_middle, left, right_middle, right);
}

spec fn last_colon_at(bytes: Seq<u8>, at: int) -> bool {
    &&& -1 <= at < bytes.len()
    &&& (at >= 0 ==> bytes[at] == b':')
    &&& forall|later: int| at < later < bytes.len() ==> #[trigger] bytes[later] != b':'
}

fn last_colon(bytes: &[u8]) -> (found: Option<usize>)
    ensures last_colon_at(bytes@, if let Some(index) = found { index as int } else { -1 }),
{
    let mut cursor = bytes.len();
    while cursor > 0
        invariant
            cursor <= bytes@.len(),
            forall|i: int| cursor <= i < bytes@.len() ==> #[trigger] bytes@[i] != b':',
        decreases cursor,
    {
        cursor -= 1;
        if bytes[cursor] == b':' {
            return Some(cursor);
        }
    }
    None
}

proof fn last_path_component(bytes: Seq<u8>, last: int)
    requires path_body(bytes), last_colon_at(bytes, last),
    ensures
        if last < 0 {
            name_component(bytes)
        } else {
            0 < last - 1 && colon_pair(bytes, last - 1)
                && name_component(bytes.skip(last + 1))
        },
    decreases bytes.len(),
{
    reveal_with_fuel(path_body, 1);
    let first = choose|first: int| first_colon(bytes, first);
    path_body_at(bytes, first);
    if first == bytes.len() {
        assert(last == -1);
        assert(bytes.take(first) =~= bytes);
    } else {
        assert(first + 1 <= last);
        assert(first > 0);
        let tail = bytes.skip(first + 2);
        assert(tail =~= bytes[(first + 2)..]);
        let at = last - first - 2;
        assert(last_colon_at(tail, at)) by {
            assert forall|i: int| at < i < tail.len() implies #[trigger] tail[i] != b':' by {
                assert(tail[i] == bytes[i + first + 2]);
            };
        };
        last_path_component(tail, at);
        if at < 0 {
            assert(last == first + 1);
        } else {
            assert(colon_pair(bytes, last - 1));
            assert(tail.skip(at + 1) =~= bytes.skip(last + 1));
        }
    }
}

/// 完全修飾名を、先頭の `::` を除いた親パスと末尾の名前に分ける。
///
/// ルート直下の名前には親パスがない。字句規則に従う完全修飾名を受理する。
pub fn split_absolute_path(path: &str) -> (result: Option<(Option<&str>, &str)>)
    ensures
        result.is_some() == (bare_atom_kind(path.spec_bytes()) == Some(AtomKind::AbsolutePath)),
        result matches Some((parent, name)) ==> absolute_path_parts(path, parent, name),
{
    if !matches!(classify(path), Some(AtomKind::AbsolutePath)) {
        return None;
    }
    assert(colon_pair(path.spec_bytes(), 0));
    let body = after_ascii(after_ascii(path));
    assert(body.spec_bytes() =~= path.spec_bytes().skip(2));
    Some(split_path_body(body))
}

/// 相対パスを、先頭の名前、中間のパス、末尾の名前に分ける。
///
/// 成分が二つの場合、中間のパスは `None`。すべて元入力の部分文字列である。
pub fn split_relative_path(path: &str) -> (result: Option<(&str, Option<&str>, &str)>)
    ensures
        result.is_some() == (bare_atom_kind(path.spec_bytes()) == Some(AtomKind::RelativePath)),
        result matches Some((head, middle, name)) ==> relative_path_parts(path, head, middle, name),
{
    if !matches!(classify(path), Some(AtomKind::RelativePath)) {
        return None;
    }
    let (head, separator) = split_at_boundary(path, Boundary::Colon);
    let ghost bytes = path.spec_bytes();
    let ghost at = head.spec_bytes().len() as int;
    proof {
        assert(head.spec_bytes() =~= bytes.take(at));
        assert(separator.spec_bytes() =~= bytes.skip(at));
        assert(first_colon(bytes, at));
        path_body_at(bytes, at);
        assert(!name_component(bytes));
        assert(colon_pair(bytes, at));
    }
    let tail = after_ascii(after_ascii(separator));
    assert(tail.spec_bytes() =~= bytes.skip(at + 2));
    let (middle, name) = split_path_body(tail);
    Some((head, middle, name))
}

fn split_path_body(body: &str) -> (parts: (Option<&str>, &str))
    requires path_body(body.spec_bytes()),
    ensures body_path_parts(body.spec_bytes(), parts.0, parts.1),
{
    let Some(last) = last_colon(body.as_bytes()) else {
        proof { last_path_component(body.spec_bytes(), -1); }
        return (None, body);
    };
    proof { last_path_component(body.spec_bytes(), last as int); }
    let separator = last - 1;
    proof {
        encode_utf8_valid_utf8(body@);
        is_char_boundary_iff_not_is_continuation_byte(body.spec_bytes(), separator as int);
    }
    let (parent, tail) = body.split_at(separator);
    let name = after_ascii(after_ascii(tail));
    assert(body_path_parts(body.spec_bytes(), Some(parent), name)) by {
        let offset = separator as int;
        assert(parent.spec_bytes().len() == offset);
        assert(name.spec_bytes() =~= body.spec_bytes().skip(last + 1));
        assert(name_component(name.spec_bytes()));
        assert(parent.spec_bytes() =~= body.spec_bytes().take(offset));
    };
    (Some(parent), name)
}

} // verus!
