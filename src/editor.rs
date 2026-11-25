//! エディタから受け取った UTF-8 ソースの置換を検査する。

mod lines;
pub use lines::{LineBounds, LineIndex, PositionEncoding, TextPosition};

use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{encode_utf8_valid_utf8, is_char_boundary, valid_utf8, valid_utf8_concat};

verus! {

/// ソースの置換を適用できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceEditError {
    /// 始点が終点より後ろにある。
    ReversedRange,
    /// 終点が元ソースの末尾を越えている。
    OutsideSource,
    /// 置換の端点が UTF-8 の文字境界にない。
    InsideCharacter {
        /// 文字の途中にある元ソース上のバイト位置。
        offset: usize,
    },
    /// 置換後のバイト数が `isize::MAX` を超える。
    SourceTooLong,
}

/// 一つの置換から得た UTF-8 テキスト。
#[derive(Debug)]
pub struct EditedSource {
    bytes: Vec<u8>,
}

impl EditedSource {
    #[verifier::type_invariant]
    spec fn text_is_utf8(&self) -> bool {
        valid_utf8(self.bytes@)
    }

    /// 置換後のテキストを UTF-8 バイト列として表す。
    pub closed spec fn bytes_model(&self) -> Seq<u8> {
        self.bytes@
    }

    /// 置換後のテキストを借用する。
    pub fn as_str(&self) -> (source: &str)
        ensures source.spec_bytes() == self.bytes_model(),
    {
        proof { use_type_invariant(self); }
        // SAFETY: 構築時に検証した UTF-8 バイト列を保持し、変更できる参照は公開しない。
        unsafe { str::from_utf8_unchecked(self.bytes.as_slice()) }
    }
}

/// 置換の失敗条件とその検査順。
pub open spec fn source_edit_error(
    source: &str, range: Range<usize>, replacement: &str,
) -> Option<SourceEditError> {
    let bytes = source.spec_bytes();
    let start = range.start as int;
    let end = range.end as int;
    if start > end {
        Some(SourceEditError::ReversedRange)
    } else if end > bytes.len() {
        Some(SourceEditError::OutsideSource)
    } else if !is_char_boundary(bytes, start) {
        Some(SourceEditError::InsideCharacter { offset: range.start })
    } else if !is_char_boundary(bytes, end) {
        Some(SourceEditError::InsideCharacter { offset: range.end })
    } else if start + bytes.len() - end + replacement.spec_bytes().len() > isize::MAX {
        Some(SourceEditError::SourceTooLong)
    } else {
        None
    }
}

/// 元の接頭部、置換テキスト、元の接尾部を順に並べた結果と、置換できない場合の診断を定める。
pub open spec fn source_edit_matches(
    source: &str, range: Range<usize>, replacement: &str, result: Result<EditedSource, SourceEditError>,
) -> bool {
    match source_edit_error(source, range, replacement) {
        Some(error) => result == Err(error),
        None => result matches Ok(text)
            && text.bytes_model() == source.spec_bytes()[..range.start]
                + replacement.spec_bytes() + source.spec_bytes()[range.end..],
    }
}

/// 置換後の本文を構成する、検査済みの三つの区間。
pub struct SourceEditParts<'a> {
    /// 置換開始位置より前の元の本文。
    pub prefix: &'a str,
    /// 挿入するテキスト。
    pub replacement: &'a str,
    /// 置換終了位置から始まる元の本文。
    pub suffix: &'a str,
    /// 三つの区間を連結したときの UTF-8 バイト数。
    pub byte_len: usize,
}

/// 検査済みの区間が元の指定と同じ本文を構成することを表す。
pub open spec fn source_edit_parts_match(
    source: &str, range: Range<usize>, replacement: &str,
    result: Result<SourceEditParts, SourceEditError>,
) -> bool {
    match source_edit_error(source, range, replacement) {
        Some(error) => result == Err(error),
        None => result matches Ok(parts)
            && parts.prefix.spec_bytes() == source.spec_bytes()[..range.start]
            && parts.replacement == replacement
            && parts.suffix.spec_bytes() == source.spec_bytes()[range.end..]
            && parts.byte_len == parts.prefix.spec_bytes().len() + parts.replacement.spec_bytes().len()
                + parts.suffix.spec_bytes().len()
            && parts.byte_len <= isize::MAX,
    }
}

/// 置換範囲を検査し、本文を構築するための借用とバイト数を返す。
///
/// # Errors
///
/// 範囲の順序、ソースの末尾、始点と終点の文字境界、置換後のバイト数の順に検査する。
pub fn prepare_source_edit<'a>(
    source: &'a str, range: Range<usize>, replacement: &'a str,
) -> (result: Result<SourceEditParts<'a>, SourceEditError>)
    ensures source_edit_parts_match(source, range, replacement, result),
{
    if range.start > range.end {
        return Err(SourceEditError::ReversedRange);
    }
    let length = source.as_bytes().len();
    if range.end > length {
        return Err(SourceEditError::OutsideSource);
    }
    if !source.is_char_boundary(range.start) {
        return Err(SourceEditError::InsideCharacter { offset: range.start });
    }
    if !source.is_char_boundary(range.end) {
        return Err(SourceEditError::InsideCharacter { offset: range.end });
    }
    let kept = length - (range.end - range.start);
    let limit = isize::MAX as usize;
    let inserted = replacement.as_bytes().len();
    if kept > limit || inserted > limit - kept {
        return Err(SourceEditError::SourceTooLong);
    }

    let (prefix, _) = source.split_at(range.start);
    let (_, suffix) = source.split_at(range.end);
    Ok(SourceEditParts { prefix, replacement, suffix, byte_len: kept + inserted })
}

fn append_bytes(target: &mut Vec<u8>, bytes: &[u8])
    requires old(target)@.len() + bytes@.len() <= isize::MAX,
    ensures final(target)@ == old(target)@ + bytes@,
{
    target.extend_from_slice(bytes);
    assert(target@ =~= old(target)@ + bytes@);
}

/// 元ソースの UTF-8 半開バイト範囲を置換し、新しいテキストを返す。
///
/// 始点と終点が等しい範囲には挿入できる。元ソースの範囲外と文字の途中への指定は拒否する。
///
/// # Errors
///
/// 範囲の順序、ソースの末尾、始点と終点の文字境界、置換後のバイト数の順に検査する。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::editor::{SourceEditError, apply_source_edit};
///
/// let edited = apply_source_edit("aあz", 1..4, "β")?;
/// assert_eq!(edited.as_str(), "aβz");
/// assert!(matches!(apply_source_edit("aあz", 2..4, "β"),
///     Err(SourceEditError::InsideCharacter { offset: 2 })));
/// # Ok::<(), SourceEditError>(())
/// ```
pub fn apply_source_edit(source: &str, range: Range<usize>, replacement: &str)
    -> (result: Result<EditedSource, SourceEditError>)
    ensures source_edit_matches(source, range, replacement, result),
{
    let parts = match prepare_source_edit(source, range, replacement) {
        Ok(parts) => parts,
        Err(error) => return Err(error),
    };
    let mut bytes = Vec::with_capacity(parts.byte_len);
    append_bytes(&mut bytes, parts.prefix.as_bytes());
    append_bytes(&mut bytes, parts.replacement.as_bytes());
    append_bytes(&mut bytes, parts.suffix.as_bytes());
    proof {
        encode_utf8_valid_utf8(parts.prefix@);
        encode_utf8_valid_utf8(parts.replacement@);
        encode_utf8_valid_utf8(parts.suffix@);
        valid_utf8_concat(parts.prefix.spec_bytes(), parts.replacement.spec_bytes());
        valid_utf8_concat(parts.prefix.spec_bytes() + parts.replacement.spec_bytes(), parts.suffix.spec_bytes());
    }
    Ok(EditedSource { bytes })
}

} // verus!
