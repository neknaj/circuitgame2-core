//! 宣言と名前空間の照合に使う名前を扱う。

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    encode_utf8_decode_utf8, encode_utf8_valid_utf8, is_char_boundary,
    is_char_boundary_iff_not_is_continuation_byte, is_char_boundary_start_end_of_seq,
};

verus! {

/// 名前空間のパスと、その直下にある名前を照合するキー。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NameKey<'a> {
    /// ルートから親名前空間までのパス。ルート直下では `None`。
    pub parent: Option<&'a str>,
    /// 修飾を含まない名前。
    pub name: &'a str,
}

pub open spec fn key_view(key: NameKey) -> (Option<Seq<char>>, Seq<char>) {
    (match key.parent {
        Some(parent) => Some(parent@),
        None => None,
    }, key.name@)
}

pub open spec fn key_bytes(key: NameKey) -> (Option<Seq<u8>>, Seq<u8>) {
    (match key.parent {
        Some(parent) => Some(parent.spec_bytes()),
        None => None,
    }, key.name.spec_bytes())
}

pub(super) proof fn key_views_agree(left: NameKey, right: NameKey)
    ensures
        (key_view(left) == key_view(right)) <==> (key_bytes(left) == key_bytes(right)),
{
    encode_utf8_decode_utf8(left.name@);
    encode_utf8_decode_utf8(right.name@);
    if let (Some(l), Some(r)) = (left.parent, right.parent) {
        encode_utf8_decode_utf8(l@);
        encode_utf8_decode_utf8(r@);
    }
}

impl NameKey<'_> {
    /// 名前空間と名前が一致することを確かめる。
    pub fn same_name(self, other: NameKey) -> (same: bool)
        ensures
            same == (key_view(self) == key_view(other)),
            same == (key_bytes(self) == key_bytes(other)),
    {
        proof { key_views_agree(self, other); }
        if self.name != other.name {
            return false;
        }
        match (self.parent, other.parent) {
            (None, None) => true,
            (Some(left), Some(right)) => left == right,
            _ => false,
        }
    }

    /// 親の名前空間をそろえ、宣言名の先頭を文字列と照合する。
    pub(super) fn matches_name_prefix(self, prefix: NameKey) -> (matches: bool)
        ensures matches == ({
            let actual = key_bytes(self);
            let wanted = key_bytes(prefix);
            &&& actual.0 == wanted.0
            &&& wanted.1.len() <= actual.1.len()
            &&& actual.1.take(wanted.1.len() as int) == wanted.1
        }),
    {
        let actual_parent = NameKey { parent: self.parent, name: "" };
        let wanted_parent = NameKey { parent: prefix.parent, name: "" };
        actual_parent.same_name(wanted_parent)
            && has_bytes_at(self.name.as_bytes(), 0, prefix.name.as_bytes())
    }
}

pub(super) proof fn namespace_component_agrees_on_bytes(
    left_path: &str, right_path: &str, left: NameKey, right: NameKey, lo: int, hi: int,
)
    requires left_path.spec_bytes() == right_path.spec_bytes(), key_bytes(left) == key_bytes(right),
    ensures namespace_component(left_path, left, lo, hi) == namespace_component(right_path, right, lo, hi),
{}

spec fn bytes_at(bytes: Seq<u8>, at: int, expected: Seq<u8>) -> bool {
    0 <= at <= at + expected.len() <= bytes.len()
        && bytes[at..at + expected.len()] == expected
}

fn has_bytes_at(bytes: &[u8], at: usize, expected: &[u8]) -> (found: bool)
    ensures found == bytes_at(bytes@, at as int, expected@),
{
    if at > bytes.len() || expected.len() > bytes.len() - at {
        return false;
    }
    let mut index = 0;
    while index < expected.len()
        invariant
            at + expected.len() <= bytes.len(),
            index <= expected.len(),
            forall|i: int| 0 <= i < index ==> #[trigger] expected@[i] == bytes@[at + i],
        decreases expected.len() - index,
    {
        if bytes[at + index] != expected[index] {
            assert(bytes@[at as int..at + expected.len()][index as int] == bytes@[at + index]);
            return false;
        }
        index += 1;
    }
    assert(bytes@[at as int..at + expected.len()] =~= expected@);
    true
}

/// パスがキーに対応する名前空間を導入する場合、その成分の相対バイト範囲を定める。
pub closed spec fn namespace_component(path: &str, key: NameKey, start: int, end: int) -> bool {
    let bytes = path.spec_bytes();
    let separator = seq![b':', b':'];
    &&& match key.parent {
        None => start == 0,
        Some(parent) => parent.spec_bytes().len() > 0
            && bytes_at(bytes, 0, parent.spec_bytes())
            && bytes_at(bytes, parent.spec_bytes().len() as int, separator)
            && start == parent.spec_bytes().len() + 2,
    }
    &&& key.name.spec_bytes().len() > 0 && !key.name.spec_bytes().contains(b':')
    &&& bytes_at(bytes, start, key.name.spec_bytes())
    &&& end == start + key.name.spec_bytes().len()
    &&& (end == bytes.len() || bytes_at(bytes, end, separator))
}

/// 内容が同じキーは、同じパス内の成分範囲に対応する。
pub(super) proof fn namespace_components_agree(path: &str, left: NameKey, right: NameKey, start: int, end: int)
    requires key_view(left) == key_view(right), namespace_component(path, left, start, end),
    ensures namespace_component(path, right, start, end),
{
    key_views_agree(left, right);
}

/// 同じキーに対応する名前空間成分の開始位置と終了位置が一致する。
pub(super) proof fn namespace_component_bounds_agree(
    path: &str, key: NameKey, left_start: int, left_end: int, right_start: int, right_end: int,
)
    requires
        namespace_component(path, key, left_start, left_end),
        namespace_component(path, key, right_start, right_end),
    ensures left_start == right_start, left_end == right_end,
{
}

pub(super) open spec fn full_name_bytes(key: NameKey) -> Seq<u8> {
    let (parent, name) = key_bytes(key);
    match parent {
        None => name,
        Some(parent) => parent + seq![b':', b':'] + name,
    }
}

pub(super) open spec fn component_ends_at(bytes: Seq<u8>, end: int) -> bool {
    0 < end <= bytes.len() && (end == bytes.len()
        || (end + 1 < bytes.len() && bytes[end] == b':' && bytes[end + 1] == b':'))
}

pub(super) proof fn namespace_component_prefix(path: &str, key: NameKey, start: int, end: int)
    requires namespace_component(path, key, start, end),
    ensures
        component_ends_at(path.spec_bytes(), end),
        full_name_bytes(key) == path.spec_bytes().take(end),
{
    reveal(namespace_component);
    let bytes = path.spec_bytes();
    match key.parent {
        None => {
            assert(bytes.take(end) =~= key.name.spec_bytes());
        },
        Some(parent) => {
            let (prefix, name) = (parent.spec_bytes(), key.name.spec_bytes());
            let separator = seq![b':', b':'];
            assert(bytes[prefix.len() as int..start] == separator);
            assert(bytes.take(end) =~= prefix + separator + name);
        }
    }
    if end != bytes.len() {
        assert(bytes[end] == b':' && bytes[end + 1] == b':');
    }
}

pub(super) proof fn component_source_boundaries(
    source: &str, path: &str, key: NameKey, base: int, limit: int, lo: int, hi: int,
)
    requires
        namespace_component(path, key, lo, hi),
        0 <= base < limit <= source.spec_bytes().len(),
        source.spec_bytes()[base..limit] == path.spec_bytes(),
        is_char_boundary(source.spec_bytes(), limit),
    ensures
        0 <= base + lo < base + hi <= limit,
        is_char_boundary(source.spec_bytes(), base + lo),
        is_char_boundary(source.spec_bytes(), base + hi),
{
    let source_bytes = source.spec_bytes();
    let path_bytes = path.spec_bytes();
    let name_bytes = key.name.spec_bytes();
    encode_utf8_valid_utf8(source@);
    encode_utf8_valid_utf8(key.name@);
    is_char_boundary_start_end_of_seq(name_bytes);
    is_char_boundary_iff_not_is_continuation_byte(name_bytes, 0);
    assert(source_bytes[base + lo] == path_bytes[lo]);
    assert(path_bytes[lo] == name_bytes[0]);
    is_char_boundary_iff_not_is_continuation_byte(source_bytes, base + lo);
    if base + hi < limit {
        assert(path_bytes[hi] == b':');
        assert(source_bytes[base + hi] == path_bytes[hi]);
        is_char_boundary_iff_not_is_continuation_byte(source_bytes, base + hi);
    }
}

fn has_colon(bytes: &[u8]) -> (found: bool)
    ensures found == bytes@.contains(b':'),
{
    let mut index = 0;
    while index < bytes.len()
        invariant
            index <= bytes.len(),
            forall|i: int| 0 <= i < index ==> #[trigger] bytes@[i] != b':',
        decreases bytes.len() - index,
    {
        if bytes[index] == b':' {
            return true;
        }
        index += 1;
    }
    false
}

/// パス自身とその中間の名前空間から、キーが指す成分を探す。
///
/// 戻り値は `path` の先頭から数えた UTF-8 バイト範囲の両端。
pub(super) fn match_namespace_component(path: &str, key: NameKey)
    -> (found: Option<(usize, usize)>)
    ensures
        forall|start: int, end: int| #[trigger] namespace_component(path, key, start, end)
            <==> (found matches Some((lo, hi)) && start == lo && end == hi),
        found.is_some() <==> (exists|lo: int, hi: int| #[trigger] namespace_component(path, key, lo, hi)),
        found matches Some((lo, hi)) ==> lo < hi <= path.spec_bytes().len()
            && namespace_component(path, key, lo as int, hi as int),
{
    let bytes = path.as_bytes();
    let separator_bytes = [b':', b':'];
    let separator = separator_bytes.as_slice();
    assert(separator@ =~= seq![b':', b':']);
    let start = match key.parent {
        None => 0,
        Some(parent) => {
            let prefix = parent.as_bytes();
            if prefix.len() == 0 || !has_bytes_at(bytes, 0, prefix)
                || !has_bytes_at(bytes, prefix.len(), separator) {
                return None;
            }
            prefix.len() + 2
        }
    };
    let name = key.name.as_bytes();
    if name.len() == 0 || has_colon(name) || !has_bytes_at(bytes, start, name) {
        return None;
    }
    let end = start + name.len();
    if end == bytes.len() || has_bytes_at(bytes, end, separator) {
        assert(namespace_component(path, key, start as int, end as int));
        Some((start, end))
    } else {
        None
    }
}

} // verus!
