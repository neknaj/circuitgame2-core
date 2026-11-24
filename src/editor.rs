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

/// 元の接頭部、置換テキスト、元の接尾部を順に並べた結果と、置換できない場合の診断を定める。
pub open spec fn source_edit_matches(
    source: &str, range: Range<usize>, replacement: &str, result: Result<EditedSource, SourceEditError>,
) -> bool {
    let bytes = source.spec_bytes();
    let start = range.start as int;
    let end = range.end as int;
    let inserted = replacement.spec_bytes();
    if start > end {
        result == Err(SourceEditError::ReversedRange)
    } else if end > bytes.len() {
        result == Err(SourceEditError::OutsideSource)
    } else if !is_char_boundary(bytes, start) {
        result == Err(SourceEditError::InsideCharacter { offset: range.start })
    } else if !is_char_boundary(bytes, end) {
        result == Err(SourceEditError::InsideCharacter { offset: range.end })
    } else if start + bytes.len() - end + inserted.len() > isize::MAX {
        result == Err(SourceEditError::SourceTooLong)
    } else {
        result matches Ok(text) && text.bytes_model() == bytes[..start] + inserted + bytes[end..]
    }
}

fn append_bytes(target: &mut Vec<u8>, bytes: &[u8])
    ensures final(target)@ == old(target)@ + bytes@,
{
    let ghost prefix = target@;
    let mut index = 0;
    while index < bytes.len()
        invariant
            index <= bytes@.len(),
            target@ == prefix + bytes@.take(index as int),
        decreases bytes@.len() - index,
    {
        target.push(bytes[index]);
        assert(bytes@.take(index as int).push(bytes@[index as int]) =~= bytes@.take(index + 1));
        index += 1;
    }
    assert(bytes@.take(bytes@.len() as int) =~= bytes@);
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
    let inserted = replacement.as_bytes();
    if kept > limit || inserted.len() > limit - kept {
        return Err(SourceEditError::SourceTooLong);
    }

    let (prefix, _) = source.split_at(range.start);
    let (_, suffix) = source.split_at(range.end);
    // 追記時の容量拡張を避けるため、置換後の長さで先に確保する。
    let mut bytes = Vec::with_capacity(kept + inserted.len());
    append_bytes(&mut bytes, prefix.as_bytes());
    append_bytes(&mut bytes, inserted);
    append_bytes(&mut bytes, suffix.as_bytes());
    proof {
        encode_utf8_valid_utf8(prefix@);
        encode_utf8_valid_utf8(replacement@);
        encode_utf8_valid_utf8(suffix@);
        valid_utf8_concat(prefix.spec_bytes(), replacement.spec_bytes());
        valid_utf8_concat(prefix.spec_bytes() + replacement.spec_bytes(), suffix.spec_bytes());
        assert(bytes@ =~= source.spec_bytes()[..range.start] + replacement.spec_bytes() + source.spec_bytes()[range.end..]);
    }
    Ok(EditedSource { bytes })
}

} // verus!
