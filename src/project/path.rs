//! 仮想相対パスを成分列に正規化する。

use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    encode_utf8_decode_utf8, encode_utf8_valid_utf8, is_char_boundary,
    is_char_boundary_iff_not_is_continuation_byte, is_char_boundary_start_end_of_seq,
    is_continuation_byte, length_of_first_scalar,
};

verus! {

/// 仮想相対パスを正規化できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PathError {
    /// プロジェクトルートを基準とする相対パスが必要である。
    Absolute,
    /// パスの区切りには `/` が必要である。
    Backslash,
    /// `..` がプロジェクトルートを越える。
    EscapesRoot,
    /// 正規化したパスに成分がない。
    Empty,
}

/// パスの拡張子で指定されるソース言語。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceKind {
    /// `.ncg2` の回路記述。
    Circuit,
    /// `.ncg2m` の純粋関数型ソース。
    Functional,
}

/// プロジェクトルートからの正規化済み仮想相対パス。
#[derive(Debug, Eq, PartialEq)]
pub struct VirtualPath<'a> {
    components: Vec<&'a str>,
}

pub open spec fn component_bytes(parts: Seq<&str>) -> Seq<Seq<u8>> {
    Seq::new(parts.len(), |i: int| parts[i].spec_bytes())
}

spec fn ascii_letter(byte: u8) -> bool {
    b'a' <= byte <= b'z' || b'A' <= byte <= b'Z'
}

spec fn drive_prefix(bytes: Seq<u8>) -> bool {
    bytes.len() >= 2 && ascii_letter(bytes[0]) && bytes[1] == b':'
}

/// 空成分、ドット成分、区切り、先頭のドライブ指定を含まない成分列を表す。
pub closed spec fn canonical_components(parts: Seq<Seq<u8>>) -> bool {
    &&& parts.len() > 0
    &&& !drive_prefix(parts[0])
    &&& forall|i: int| 0 <= i < parts.len() ==> {
        let part = #[trigger] parts[i];
        &&& part.len() > 0
        &&& part != seq![b'.'] && part != seq![b'.', b'.']
        &&& !part.contains(b'/') && !part.contains(b'\\')
    }
}

spec fn separator_at(bytes: Seq<u8>, at: int) -> int
    decreases bytes.len() - at,
{
    if at < 0 || at >= bytes.len() { bytes.len() as int }
    else if bytes[at] == b'/' { at }
    else { separator_at(bytes, at + 1) }
}

spec fn reduce_component(stack: Seq<Seq<u8>>, part: Seq<u8>) -> Result<Seq<Seq<u8>>, PathError> {
    if part.contains(b'\\') { Err(PathError::Backslash) }
    else if part.len() == 0 || part == seq![b'.'] { Ok(stack) }
    else if part == seq![b'.', b'.'] {
        if stack.len() == 0 { Err(PathError::EscapesRoot) }
        else { Ok(stack.drop_last()) }
    } else if stack.len() == 0 && drive_prefix(part) {
        Err(PathError::Absolute)
    } else {
        Ok(stack.push(part))
    }
}

#[verifier::opaque]
spec fn reduce_path(bytes: Seq<u8>, stack: Seq<Seq<u8>>) -> Result<Seq<Seq<u8>>, PathError>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        if stack.len() == 0 { Err(PathError::Empty) } else { Ok(stack) }
    } else {
        let slash = separator_at(bytes, 0);
        if 0 <= slash <= bytes.len() {
            let rest = if slash == bytes.len() { slash } else { slash + 1 };
            match reduce_component(stack, bytes.take(slash)) {
                Ok(next) => reduce_path(bytes.skip(rest), next),
                Err(error) => Err(error),
            }
        } else {
            Err(PathError::Empty)
        }
    }
}

/// 入力を `/` で区切り、正規化した成分列または最初のパス違反を定める。
pub closed spec fn normalized_path(path: &str) -> Result<Seq<Seq<u8>>, PathError> {
    let bytes = path.spec_bytes();
    if bytes.len() > 0 && bytes[0] == b'/' { Err(PathError::Absolute) }
    else { reduce_path(bytes, Seq::empty()) }
}

fn read_component(path: &str) -> (split: (&str, &str, bool))
    requires path.spec_bytes().len() > 0,
    ensures
        0 <= separator_at(path.spec_bytes(), 0) <= path.spec_bytes().len(),
        split.0.spec_bytes() == path.spec_bytes().take(separator_at(path.spec_bytes(), 0)),
        split.1.spec_bytes() == path.spec_bytes().skip(if separator_at(path.spec_bytes(), 0) == path.spec_bytes().len() {
            path.spec_bytes().len() as int
        } else { separator_at(path.spec_bytes(), 0) + 1 }),
        split.1.spec_bytes().len() < path.spec_bytes().len(),
        !split.0.spec_bytes().contains(b'/'),
        split.2 == split.0.spec_bytes().contains(b'\\'),
{
    let bytes = path.as_bytes();
    let mut cursor = 0;
    let mut backslash = false;
    while cursor < bytes.len() && bytes[cursor] != b'/'
        invariant
            bytes@ == path.spec_bytes(),
            cursor <= bytes.len(),
            separator_at(bytes@, cursor as int) == separator_at(bytes@, 0),
            forall|i: int| 0 <= i < cursor ==> #[trigger] bytes@[i] != b'/',
            backslash == (exists|i: int| 0 <= i < cursor && #[trigger] bytes@[i] == b'\\'),
        decreases bytes.len() - cursor,
    {
        if bytes[cursor] == b'\\' {
            backslash = true;
        }
        cursor += 1;
    }
    assert(separator_at(bytes@, cursor as int) == cursor);
    proof {
        encode_utf8_valid_utf8(path@);
        if cursor < bytes.len() {
            assert(!is_continuation_byte(bytes@[cursor as int]));
            is_char_boundary_iff_not_is_continuation_byte(bytes@, cursor as int);
        } else {
            is_char_boundary_start_end_of_seq(bytes@);
        }
    }
    let (component, tail) = path.split_at(cursor);
    let rest = if cursor < bytes.len() {
        proof {
            encode_utf8_valid_utf8(tail@);
            assert(tail.spec_bytes()[0] == b'/');
            assert(length_of_first_scalar(tail.spec_bytes()) == 1);
            reveal_with_fuel(is_char_boundary, 2);
        }
        tail.split_at(1).1
    } else {
        tail
    };
    assert(component.spec_bytes() =~= bytes@.take(cursor as int));
    assert(backslash == component.spec_bytes().contains(b'\\')) by {
        let word = component.spec_bytes();
        if backslash {
            let i = choose|i: int| 0 <= i < cursor && #[trigger] bytes@[i] == b'\\';
            assert(word[i] == b'\\');
        } else if word.contains(b'\\') {
            let i = choose|i: int| 0 <= i < word.len() && #[trigger] word[i] == b'\\';
            assert(bytes@[i] == b'\\');
        }
    };
    assert(rest.spec_bytes() =~= bytes@.skip(if cursor < bytes.len() { cursor + 1 } else { cursor as int }));
    (component, rest, backslash)
}

fn has_drive_prefix(part: &str) -> (found: bool)
    ensures found == drive_prefix(part.spec_bytes()),
{
    let bytes = part.as_bytes();
    if bytes.len() < 2 {
        false
    } else {
        let first = bytes[0];
        ((b'a' <= first && first <= b'z') || (b'A' <= first && first <= b'Z')) && bytes[1] == b':'
    }
}

impl<'a> VirtualPath<'a> {
    /// 正規化した識別子を、元ソースと同じ UTF-8 バイトの成分列で表す。
    pub closed spec fn components_model(&self) -> Seq<Seq<u8>> {
        component_bytes(self.components@)
    }

    /// ルートからファイルまでの成分を順に返す。
    pub fn components(&self) -> (parts: &[&'a str])
        ensures component_bytes(parts@) == self.components_model(),
    {
        self.components.as_slice()
    }

    pub(super) fn copy_for_diagnostic(&self) -> (copied: VirtualPath<'a>)
        ensures copied.components_model() == self.components_model(),
    {
        let parts = self.components();
        let mut components = Vec::new();
        let mut index = 0;
        while index < parts.len()
            invariant
                index <= parts@.len(),
                components@ == parts@.take(index as int),
            decreases parts.len() - index,
        {
            components.push(parts[index]);
            index += 1;
            assert(components@ =~= parts@.take(index as int));
        }
        assert(components@ =~= parts@);
        VirtualPath { components }
    }

    /// 同じプロジェクト内のファイルを指すか、正規化後の成分を照合する。
    pub fn same_file(&self, other: &VirtualPath) -> (same: bool)
        ensures same == (self.components_model() == other.components_model()),
    {
        let left = self.components();
        let right = other.components();
        if left.len() != right.len() {
            return false;
        }
        let mut index = 0;
        while index < left.len()
            invariant
                left.len() == right.len(),
                index <= left.len(),
                component_bytes(left@) == self.components_model(),
                component_bytes(right@) == other.components_model(),
                forall|i: int| 0 <= i < index ==>
                    (#[trigger] left@[i]).spec_bytes() == (#[trigger] right@[i]).spec_bytes(),
            decreases left.len() - index,
        {
            let left_part = left[index];
            let right_part = right[index];
            proof {
                encode_utf8_decode_utf8(left_part@);
                encode_utf8_decode_utf8(right_part@);
            }
            if left_part != right_part {
                assert(self.components_model()[index as int] != other.components_model()[index as int]);
                return false;
            }
            index += 1;
        }
        assert(self.components_model() =~= other.components_model());
        true
    }
}

/// 仮想パスをプロジェクトルートからの成分列に正規化する。
///
/// 連続する区切りや末尾の区切りが作る空成分は除く。
/// 各成分の文字の並びはそのまま保ち、大文字と小文字を区別する。
///
/// # Errors
///
/// 絶対パス、先頭のドライブ指定、バックスラッシュ、ルートを越える `..`、空となるパスを拒否する。
pub fn normalize_path(path: &str) -> (result: Result<VirtualPath<'_>, PathError>)
    ensures
        match result {
            Ok(normalized) => normalized_path(path) == Ok(normalized.components_model())
                && canonical_components(normalized.components_model()),
            Err(error) => normalized_path(path) == Err(error),
        },
{
    let input = path.as_bytes();
    if input.len() > 0 && input[0] == b'/' {
        return Err(PathError::Absolute);
    }
    let mut remaining = path;
    let mut components: Vec<&str> = Vec::new();
    assert(component_bytes(components@) =~= Seq::<Seq<u8>>::empty());
    while remaining.as_bytes().len() > 0
        invariant
            normalized_path(path) == reduce_path(remaining.spec_bytes(), component_bytes(components@)),
            components@.len() > 0 ==> canonical_components(component_bytes(components@)),
        decreases remaining.spec_bytes().len(),
    {
        let (part, rest, backslash) = read_component(remaining);
        let bytes = part.as_bytes();
        let ghost before = component_bytes(components@);
        proof { reveal(reduce_path); }
        if backslash {
            return Err(PathError::Backslash);
        }
        if bytes.len() == 0 || (bytes.len() == 1 && bytes[0] == b'.') {
            assert(bytes@.len() == 0 || bytes@ =~= seq![b'.']);
        } else if bytes.len() == 2 && bytes[0] == b'.' && bytes[1] == b'.' {
            assert(bytes@ =~= seq![b'.', b'.']);
            if components.pop().is_none() {
                return Err(PathError::EscapesRoot);
            }
            assert(component_bytes(components@) =~= before.drop_last());
        } else {
            if components.len() == 0 && has_drive_prefix(part) {
                return Err(PathError::Absolute);
            }
            components.push(part);
            assert(component_bytes(components@) =~= before.push(part.spec_bytes()));
        }
        remaining = rest;
    }
    proof { reveal(reduce_path); }
    if components.len() == 0 {
        Err(PathError::Empty)
    } else {
        Ok(VirtualPath { components })
    }
}

spec fn suffix_of(word: Seq<u8>, suffix: Seq<u8>) -> bool {
    word.len() > suffix.len() && word.skip((word.len() - suffix.len()) as int) == suffix
}

/// 最後の成分の拡張子からソース言語を定める。
pub closed spec fn source_kind_of(parts: Seq<Seq<u8>>) -> Option<SourceKind> {
    if parts.len() == 0 { None }
    else if suffix_of(parts.last(), ".ncg2".spec_bytes()) { Some(SourceKind::Circuit) }
    else if suffix_of(parts.last(), ".ncg2m".spec_bytes()) { Some(SourceKind::Functional) }
    else { None }
}

fn has_suffix(word: &str, extension: &str) -> (found: bool)
    ensures found == suffix_of(word.spec_bytes(), extension.spec_bytes()),
{
    let word_bytes = word.as_bytes();
    let ext_bytes = extension.as_bytes();
    if word_bytes.len() <= ext_bytes.len() {
        return false;
    }
    let start = word_bytes.len() - ext_bytes.len();
    let mut index = 0;
    while index < ext_bytes.len()
        invariant
            word_bytes@ == word.spec_bytes(),
            ext_bytes@ == extension.spec_bytes(),
            start > 0,
            start + ext_bytes.len() == word_bytes.len(),
            index <= ext_bytes.len(),
            forall|i: int| 0 <= i < index ==> #[trigger] ext_bytes@[i] == word_bytes@[start + i],
        decreases ext_bytes.len() - index,
    {
        if ext_bytes[index] != word_bytes[start + index] {
            assert(word_bytes@.skip(start as int)[index as int] == word_bytes@[start + index]);
            assert(word_bytes@.skip(start as int) != ext_bytes@);
            return false;
        }
        index += 1;
    }
    assert(word_bytes@.skip(start as int) =~= ext_bytes@);
    true
}

impl VirtualPath<'_> {
    /// 最終成分に対応するソース言語を返す。拡張子の前には名前が必要である。
    pub fn source_kind(&self) -> (kind: Option<SourceKind>)
        ensures kind == source_kind_of(self.components_model()),
    {
        if self.components.len() == 0 {
            return None;
        }
        let name = self.components[self.components.len() - 1];
        if has_suffix(name, ".ncg2") {
            Some(SourceKind::Circuit)
        } else if has_suffix(name, ".ncg2m") {
            Some(SourceKind::Functional)
        } else {
            None
        }
    }
}

} // verus!
