//! エディタの行番号を、UTF-8 ソース上の行の境界に対応付ける。

use alloc::vec::Vec;
use vstd::prelude::*;

#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    char_is_scalar, decode_utf8, decode_utf8_encode_utf8, encode_scalar, encode_utf8,
    encode_utf8_first_scalar, encode_utf8_valid_utf8, has_width_1_encoding, has_width_2_encoding,
    has_width_3_encoding, is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq, is_continuation_byte, length_of_first_scalar,
    pop_first_scalar, valid_utf8, valid_utf8_split,
};

verus! {

/// 改行を除いた一行分の UTF-8 半開バイト範囲。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LineBounds {
    /// 行頭のバイト位置。
    pub start: usize,
    /// 改行の直前または文書の末尾。
    pub end: usize,
}

/// 行内の列を数える単位。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PositionEncoding {
    /// UTF-8 のコード単位（バイト）。
    Utf8,
    /// UTF-16 のコード単位。補助平面の文字は 2 単位を使う。
    Utf16,
    /// UTF-32 のコード単位（Unicode スカラー値）。
    Utf32,
}

/// いずれも 0 から数える文書内の位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TextPosition {
    /// 改行で区切られた行の番号。
    pub line: usize,
    /// 指定した符号化方式のコード単位で測った列。
    pub column: usize,
}

/// UTF-8 のスナップショットと、改行の先頭バイト位置。
pub struct LineIndex<'a> {
    source: &'a str,
    breaks: Vec<usize>,
}

/// CRLF の LF を除き、CR と LF をそれぞれ改行の先頭とする。
pub open spec fn line_break_at(bytes: Seq<u8>, at: int) -> bool {
    &&& 0 <= at < bytes.len()
    &&& (bytes[at] == 13 || bytes[at] == 10 && (at == 0 || bytes[at - 1] != 13))
}

spec fn covered_breaks(bytes: Seq<u8>, breaks: Seq<usize>, scanned: nat) -> bool {
    &&& scanned <= bytes.len()
    &&& forall|i: int| 0 <= i < breaks.len() ==>
        (#[trigger] breaks[i]) < scanned && line_break_at(bytes, breaks[i] as int)
    &&& forall|i: int, j: int| 0 <= i < j < breaks.len() ==>
        (#[trigger] breaks[i]) < (#[trigger] breaks[j])
    &&& forall|at: int| 0 <= at < scanned && #[trigger] line_break_at(bytes, at)
        ==> exists|i: int| 0 <= i < breaks.len() && (#[trigger] breaks[i]) == at
}

spec fn after_break(bytes: Seq<u8>, offset: int) -> int {
    if bytes[offset] == 13 && offset + 1 < bytes.len() && bytes[offset + 1] == 10 {
        offset + 2
    } else {
        offset + 1
    }
}

spec fn counted_byte(bytes: Seq<u8>, at: int, encoding: PositionEncoding) -> nat {
    if matches!(encoding, PositionEncoding::Utf8)
        || !is_continuation_byte(bytes[at])
        || matches!(encoding, PositionEncoding::Utf16) && at > 0 && bytes[at - 1] >= 0xf0
    { 1 } else { 0 }
}

fn count_byte(bytes: &[u8], at: usize, encoding: PositionEncoding) -> (units: usize)
    requires at < bytes@.len(),
    ensures units == counted_byte(bytes@, at as int, encoding), units <= 1,
{
    let byte = bytes[at];
    // UTF-16 は 4 バイト文字の先頭とその直後を 1 単位ずつ数える。
    if matches!(encoding, PositionEncoding::Utf8) || byte < 0x80 || byte > 0xbf
        || matches!(encoding, PositionEncoding::Utf16) && at > 0 && bytes[at - 1] >= 0xf0
    { 1 } else { 0 }
}

spec fn column_units(bytes: Seq<u8>, start: int, end: int, encoding: PositionEncoding) -> nat
    recommends 0 <= start <= end <= bytes.len(),
    decreases end - start,
{
    if end <= start { 0 } else {
        column_units(bytes, start, end - 1, encoding) + counted_byte(bytes, end - 1, encoding)
    }
}

proof fn later_column(bytes: Seq<u8>, start: int, first: int, last: int, encoding: PositionEncoding)
    requires 0 <= start <= first <= last <= bytes.len(),
    ensures
        column_units(bytes, start, first, encoding) <= column_units(bytes, start, last, encoding),
        first < last && counted_byte(bytes, first, encoding) > 0 ==>
            column_units(bytes, start, first, encoding) < column_units(bytes, start, last, encoding),
    decreases last - first,
{
    if first < last {
        reveal_with_fuel(column_units, 2);
        later_column(bytes, start, first, last - 1, encoding);
    }
}

proof fn distinct_columns(bytes: Seq<u8>, start: int, first: int, last: int, encoding: PositionEncoding)
    requires valid_utf8(bytes), 0 <= start <= first < last <= bytes.len(), is_char_boundary(bytes, first),
    ensures column_units(bytes, start, first, encoding) < column_units(bytes, start, last, encoding),
{
    is_char_boundary_iff_not_is_continuation_byte(bytes, first);
    later_column(bytes, start, first, last, encoding);
}

spec fn scalar_width(ch: char, encoding: PositionEncoding) -> nat {
    match encoding {
        PositionEncoding::Utf8 => encode_scalar(ch as u32).len(),
        PositionEncoding::Utf16 => if ch as u32 > 0xffff { 2 } else { 1 },
        PositionEncoding::Utf32 => 1,
    }
}

spec fn scalar_units(chars: Seq<char>, encoding: PositionEncoding) -> nat
    decreases chars.len(),
{
    if chars.len() == 0 { 0 } else {
        scalar_width(chars[0], encoding) + scalar_units(chars.drop_first(), encoding)
    }
}

proof fn column_split(bytes: Seq<u8>, start: int, mid: int, end: int, encoding: PositionEncoding)
    requires 0 <= start <= mid <= end <= bytes.len(),
    ensures column_units(bytes, start, end, encoding)
        == column_units(bytes, start, mid, encoding) + column_units(bytes, mid, end, encoding),
    decreases end - mid,
{
    if mid < end {
        reveal_with_fuel(column_units, 2);
        column_split(bytes, start, mid, end - 1, encoding);
    }
}

proof fn encoded_scalar_units(bytes: Seq<u8>, start: int, end: int, ch: char, encoding: PositionEncoding)
    requires
        0 <= start <= end <= bytes.len(),
        bytes.subrange(start, end) == encode_scalar(ch as u32),
    ensures column_units(bytes, start, end, encoding) == scalar_width(ch, encoding),
{
    char_is_scalar(ch);
    let value = ch as u32;
    let chars = seq![ch];
    let encoded = bytes.subrange(start, end);
    assert(encode_utf8(chars) =~= encoded) by { reveal_with_fuel(encode_utf8, 3); }
    encode_utf8_first_scalar(chars);
    assert(bytes[start] == encoded[0]);
    reveal_with_fuel(column_units, 6);
    if has_width_1_encoding(value) {
        assert(end == start + 1);
    } else if has_width_2_encoding(value) {
        assert(end == start + 2);
        assert(bytes[start + 1] == encoded[1]);
    } else if has_width_3_encoding(value) {
        assert(end == start + 3);
        assert(bytes[start + 1] == encoded[1] && bytes[start + 2] == encoded[2]);
    } else {
        assert(end == start + 4);
        assert(bytes[start + 1] == encoded[1] && bytes[start + 2] == encoded[2] && bytes[start + 3] == encoded[3]);
    }
}

proof fn encoded_columns(bytes: Seq<u8>, start: int, end: int, chars: Seq<char>, encoding: PositionEncoding)
    requires 0 <= start <= end <= bytes.len(), bytes.subrange(start, end) == encode_utf8(chars),
    ensures column_units(bytes, start, end, encoding) == scalar_units(chars, encoding),
    decreases chars.len(),
{
    reveal_with_fuel(encode_utf8, 2);
    if chars.len() > 0 {
        let head = encode_scalar(chars[0] as u32);
        let rest = chars.drop_first();
        let tail = encode_utf8(rest);
        let span = bytes.subrange(start, end);
        assert(span == head + tail);
        assert(span.len() == end - start);
        assert((head + tail).len() == head.len() + tail.len());
        let mid = start + head.len();
        assert(start <= mid <= end);
        assert(bytes.subrange(start, mid) =~= head);
        assert forall|index: int| 0 <= index < tail.len() implies
            #[trigger] bytes.subrange(mid, end)[index] == tail[index] by {
            assert(span[head.len() + index] == (head + tail)[head.len() + index]);
            assert(span[head.len() + index] == bytes[mid + index]);
        };
        assert(bytes.subrange(mid, end) =~= tail);
        encoded_scalar_units(bytes, start, mid, chars[0], encoding);
        encoded_columns(bytes, mid, end, rest, encoding);
        column_split(bytes, start, mid, end, encoding);
    } else {
        assert(bytes.subrange(start, end).len() == end - start);
        assert(start == end);
    }
}

proof fn boundary_after_ascii(bytes: Seq<u8>, at: int)
    requires valid_utf8(bytes), 0 <= at < bytes.len(), bytes[at] <= 0x7f,
    ensures is_char_boundary(bytes, at + 1),
    decreases bytes.len(),
{
    reveal_with_fuel(valid_utf8, 2);
    reveal_with_fuel(is_char_boundary, 2);
    let width = length_of_first_scalar(bytes);
    let tail = pop_first_scalar(bytes);
    if at < width {
        assert(at == 0 && width == 1);
    } else {
        assert(bytes[at] == tail[at - width]);
        boundary_after_ascii(tail, at - width);
    }
}

proof fn unicode_span(bytes: Seq<u8>, start: int, end: int, encoding: PositionEncoding)
    requires
        valid_utf8(bytes), 0 <= start <= end <= bytes.len(),
        is_char_boundary(bytes, start), is_char_boundary(bytes, end),
    ensures column_units(bytes, start, end, encoding)
        == scalar_units(decode_utf8(bytes.subrange(start, end)), encoding),
{
    valid_utf8_split(bytes, end);
    let prefix = bytes.take(end);
    assert(prefix =~= bytes.subrange(0, end));
    if start < end {
        is_char_boundary_iff_not_is_continuation_byte(bytes, start);
        assert(prefix[start] == bytes[start]);
        is_char_boundary_iff_not_is_continuation_byte(prefix, start);
    } else {
        is_char_boundary_start_end_of_seq(prefix);
    }
    valid_utf8_split(prefix, start);
    let span = bytes.subrange(start, end);
    assert(span =~= prefix.subrange(start, end));
    decode_utf8_encode_utf8(span);
    encoded_columns(bytes, start, end, decode_utf8(span), encoding);
}

spec fn within_line(bytes: Seq<u8>, line: LineBounds, offset: int) -> bool {
    &&& line.start <= offset <= line.end
    &&& is_char_boundary(bytes, offset)
}

spec fn offset_matches(
    bytes: Seq<u8>, line: LineBounds, column: usize, encoding: PositionEncoding, offset: int,
) -> bool {
    &&& within_line(bytes, line, offset)
    &&& (column_units(bytes, line.start as int, offset, encoding) == column
        || offset == line.end && column_units(bytes, line.start as int, offset, encoding) < column)
}

fn scan_column(source: &str, start: usize, end: usize, encoding: PositionEncoding) -> (column: usize)
    requires start <= end <= source.spec_bytes().len(),
    ensures column == column_units(source.spec_bytes(), start as int, end as int, encoding),
{
    let bytes = source.as_bytes();
    let mut at = start;
    let mut units = 0usize;
    while at < end
        invariant
            bytes@ == source.spec_bytes(),
            start <= at <= end <= bytes@.len(),
            units == column_units(bytes@, start as int, at as int, encoding),
            units <= at - start,
        decreases end - at,
    {
        assert(column_units(bytes@, start as int, at + 1, encoding)
            == units + counted_byte(bytes@, at as int, encoding));
        units += count_byte(bytes, at, encoding);
        at += 1;
    }
    units
}

impl<'a> LineIndex<'a> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        covered_breaks(self.source.spec_bytes(), self.breaks@, self.source.spec_bytes().len())
    }

    /// 索引を作った時点のテキストを表す。
    pub closed spec fn bytes_model(&self) -> Seq<u8> { self.source.spec_bytes() }

    /// ソースにある改行の先頭位置を文書順に並べる。
    pub closed spec fn breaks_model(&self) -> Seq<usize> { self.breaks@ }

    /// 索引にすべての改行が一度ずつ、バイト位置の昇順で含まれることを表す。
    pub closed spec fn line_index_matches(&self, source: &str) -> bool {
        self.bytes_model() == source.spec_bytes()
            && covered_breaks(self.bytes_model(), self.breaks_model(), self.bytes_model().len())
    }

    /// CRLF、CR、LF の改行位置から索引を作る。
    pub fn new(source: &'a str) -> (index: Self)
        ensures index.line_index_matches(source),
    {
        let bytes = source.as_bytes();
        let mut breaks = Vec::new();
        let mut at = 0usize;
        while at < bytes.len()
            invariant
                bytes@ == source.spec_bytes(),
                covered_breaks(bytes@, breaks@, at as nat),
            decreases bytes@.len() - at,
        {
            let ghost previous = breaks@;
            let byte = bytes[at];
            if byte == b'\r' || byte == b'\n' && (at == 0 || bytes[at - 1] != b'\r') {
                assert(line_break_at(bytes@, at as int));
                breaks.push(at);
            } else {
                assert(!line_break_at(bytes@, at as int));
            }
            proof {
                assert forall|cursor: int| 0 <= cursor < at + 1 && #[trigger] line_break_at(bytes@, cursor)
                    implies exists|i: int| 0 <= i < breaks@.len() && (#[trigger] breaks@[i]) == cursor by {
                    if cursor == at {
                        assert(breaks@[previous.len() as int] == cursor);
                    } else {
                        let i = choose|i: int| 0 <= i < previous.len() && (#[trigger] previous[i]) == cursor;
                        assert(breaks@[i] == cursor);
                    }
                };
            }
            at += 1;
        }
        Self { source, breaks }
    }

    /// 行頭と行末を、隣り合う改行または文書の境界から定める。
    pub closed spec fn line_bounds_match(&self, number: usize, bounds: Option<LineBounds>) -> bool {
        match bounds {
            Some(line) => {
                &&& number <= self.breaks_model().len()
                &&& line.start == if number == 0 { 0 } else {
                    after_break(self.bytes_model(), self.breaks_model()[number - 1] as int)
                }
                &&& line.end == if number == self.breaks_model().len() { self.bytes_model().len() as int }
                    else { self.breaks_model()[number as int] as int }
                &&& line.start <= line.end <= self.bytes_model().len()
            },
            None => number > self.breaks_model().len(),
        }
    }

    spec fn modeled_line(&self, number: usize) -> LineBounds {
        let bytes = self.bytes_model();
        let breaks = self.breaks_model();
        let start = if number == 0 { 0 } else { after_break(bytes, breaks[number - 1] as int) };
        let end = if number == breaks.len() { bytes.len() as int } else { breaks[number as int] as int };
        LineBounds { start: start as usize, end: end as usize }
    }

    /// 0 から数えた行番号に対応するバイト範囲を返す。
    ///
    /// 空の文書にも行 0 がある。末尾が改行なら、その後に空行がある。
    /// 行番号が範囲外の場合は `None` を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::editor::{LineBounds, LineIndex};
    ///
    /// let lines = LineIndex::new("漢\r\n\n");
    /// assert_eq!(lines.line(0), Some(LineBounds { start: 0, end: 3 }));
    /// assert_eq!(lines.line(1), Some(LineBounds { start: 5, end: 5 }));
    /// assert_eq!(lines.line(2), Some(LineBounds { start: 6, end: 6 }));
    /// assert_eq!(lines.line(3), None);
    /// ```
    pub fn line(&self, number: usize) -> (bounds: Option<LineBounds>)
        ensures self.line_bounds_match(number, bounds),
    {
        proof { use_type_invariant(self); }
        if number > self.breaks.len() { return None; }
        let bytes = self.source.as_bytes();
        let end = if number == self.breaks.len() { bytes.len() } else { self.breaks[number] };
        let start = if number == 0 {
            0
        } else {
            let last = self.breaks[number - 1];
            if bytes[last] == b'\r' && last + 1 < bytes.len() && bytes[last + 1] == b'\n' {
                assert(number < self.breaks@.len() ==> end != last + 1);
                last + 2
            } else {
                last + 1
            }
        };
        Some(LineBounds { start, end })
    }

    proof fn end_is_boundary(&self, number: usize, line: LineBounds)
        requires self.valid(), self.line_bounds_match(number, Some(line)),
        ensures is_char_boundary(self.bytes_model(), line.end as int),
    {
        let bytes = self.bytes_model();
        encode_utf8_valid_utf8(self.source@);
        assert(valid_utf8(bytes));
        if number == self.breaks_model().len() {
            is_char_boundary_start_end_of_seq(bytes);
        } else {
            let at = self.breaks_model()[number as int] as int;
            assert(line_break_at(bytes, at));
            is_char_boundary_iff_not_is_continuation_byte(bytes, at);
            assert(!is_continuation_byte(bytes[at]));
        }
    }

    proof fn start_is_boundary(&self, number: usize, line: LineBounds)
        requires self.valid(), self.line_bounds_match(number, Some(line)),
        ensures is_char_boundary(self.bytes_model(), line.start as int),
    {
        let bytes = self.bytes_model();
        encode_utf8_valid_utf8(self.source@);
        if number == 0 {
            is_char_boundary_start_end_of_seq(bytes);
        } else {
            let at = self.breaks_model()[number - 1] as int;
            assert(line_break_at(bytes, at));
            assert(bytes[line.start - 1] <= 0x7f);
            boundary_after_ascii(bytes, line.start - 1);
        }
    }

    /// 指定位置を、必要なら行末に丸めて UTF-8 バイト位置に対応付ける。
    pub closed spec fn position_to_byte_matches(
        &self, position: TextPosition, encoding: PositionEncoding, result: Option<usize>,
    ) -> bool {
        match result {
            Some(offset) => exists|line: LineBounds| {
                &&& #[trigger] self.line_bounds_match(position.line, Some(line))
                &&& offset_matches(self.bytes_model(), line, position.column, encoding, offset as int)
            },
            None => forall|line: LineBounds, offset: int|
                #[trigger] self.line_bounds_match(position.line, Some(line)) ==>
                    !(#[trigger] offset_matches(self.bytes_model(), line, position.column, encoding, offset)),
        }
    }

    /// 行・列から UTF-8 のバイト位置を求める。
    ///
    /// 行末を越える列は行末に丸める。存在しない行、UTF-8 の文字や
    /// UTF-16 のサロゲートペアの途中を指す場合は `None` を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::editor::{LineIndex, PositionEncoding, TextPosition};
    ///
    /// let lines = LineIndex::new("a漢😀\r\n");
    /// let position = |column| TextPosition { line: 0, column };
    /// assert_eq!(lines.position_to_byte(position(2), PositionEncoding::Utf16), Some(4));
    /// assert_eq!(lines.position_to_byte(position(3), PositionEncoding::Utf16), None);
    /// assert_eq!(lines.position_to_byte(position(9), PositionEncoding::Utf16), Some(8));
    /// assert_eq!(lines.byte_to_position(8, PositionEncoding::Utf8), Some(position(8)));
    /// assert_eq!(lines.byte_to_position(8, PositionEncoding::Utf32), Some(position(3)));
    /// assert_eq!(lines.byte_to_position(9, PositionEncoding::Utf16), None);
    /// assert_eq!(lines.byte_to_position(10, PositionEncoding::Utf16),
    ///     Some(TextPosition { line: 1, column: 0 }));
    /// ```
    pub fn position_to_byte(&self, position: TextPosition, encoding: PositionEncoding)
        -> (result: Option<usize>)
        ensures self.position_to_byte_matches(position, encoding, result),
    {
        let Some(line) = self.line(position.line) else { return None; };
        let bytes = self.source.as_bytes();
        let mut at = line.start;
        let mut units = 0usize;
        while at < line.end
            invariant
                bytes@ == self.bytes_model(),
                self.line_bounds_match(position.line, Some(line)),
                line.start <= at <= line.end <= bytes@.len(),
                units == column_units(bytes@, line.start as int, at as int, encoding),
                units <= at - line.start,
                forall|prior: int| line.start <= prior < at && #[trigger] is_char_boundary(bytes@, prior) ==>
                    column_units(bytes@, line.start as int, prior, encoding) != position.column,
            decreases line.end - at,
        {
            if units == position.column && self.source.is_char_boundary(at) {
                assert(offset_matches(bytes@, line, position.column, encoding, at as int));
                return Some(at);
            }
            assert(forall|prior: int| line.start <= prior < at + 1 && #[trigger] is_char_boundary(bytes@, prior) ==>
                column_units(bytes@, line.start as int, prior, encoding) != position.column);
            assert(column_units(bytes@, line.start as int, at + 1, encoding)
                == units + counted_byte(bytes@, at as int, encoding));
            units += count_byte(bytes, at, encoding);
            at += 1;
        }
        if units <= position.column {
            proof {
                use_type_invariant(self);
                self.end_is_boundary(position.line, line);
            }
            assert(offset_matches(bytes@, line, position.column, encoding, line.end as int));
            Some(line.end)
        } else {
            assert forall|other: LineBounds, offset: int|
                #[trigger] self.line_bounds_match(position.line, Some(other)) implies
                    !(#[trigger] offset_matches(bytes@, other, position.column, encoding, offset)) by {
                assert(other == line);
                if line.start <= offset < line.end && is_char_boundary(bytes@, offset) {
                    assert(column_units(bytes@, line.start as int, offset, encoding) != position.column);
                }
            };
            None
        }
    }

    spec fn cut_at(&self, offset: usize, line: usize) -> bool {
        &&& line <= self.breaks_model().len()
        &&& forall|i: int| 0 <= i < line ==> (#[trigger] self.breaks_model()[i]) < offset
        &&& forall|i: int| line <= i < self.breaks_model().len() ==> (#[trigger] self.breaks_model()[i]) >= offset
    }

    fn line_candidate(&self, offset: usize) -> (line: usize)
        ensures self.cut_at(offset, line),
    {
        proof { use_type_invariant(self); }
        let mut lo = 0;
        let mut hi = self.breaks.len();
        while lo < hi
            invariant
                self.valid(),
                lo <= hi <= self.breaks@.len(),
                forall|i: int| 0 <= i < lo ==> (#[trigger] self.breaks@[i]) < offset,
                forall|i: int| hi <= i < self.breaks@.len() ==> (#[trigger] self.breaks@[i]) >= offset,
            decreases hi - lo,
        {
            let middle = lo + (hi - lo) / 2;
            if self.breaks[middle] < offset {
                assert(forall|i: int| 0 <= i < middle + 1 ==> (#[trigger] self.breaks@[i]) < offset);
                lo = middle + 1;
            } else {
                assert(forall|i: int| middle <= i < self.breaks@.len() ==> (#[trigger] self.breaks@[i]) >= offset);
                hi = middle;
            }
        }
        lo
    }

    proof fn exact_line_is_candidate(&self, offset: usize, number: usize, line: LineBounds, candidate: usize)
        requires
            self.cut_at(offset, candidate),
            self.line_bounds_match(number, Some(line)),
            line.start <= offset <= line.end,
        ensures number == candidate,
    {
        let breaks = self.breaks_model();
        if number < candidate {
            assert(breaks[number as int] < offset);
        } else if number > candidate {
            assert(breaks[number - 1] >= offset);
        }
    }

    /// バイト位置と、丸めを行う前の正確な行・列の対応を表す。
    pub closed spec fn byte_to_position_matches(
        &self, offset: usize, encoding: PositionEncoding, result: Option<TextPosition>,
    ) -> bool {
        let bytes = self.bytes_model();
        match result {
            Some(position) => self.exact_position_at(offset, encoding, position, self.modeled_line(position.line)),
            None => forall|number: usize, line: LineBounds|
                #[trigger] self.line_bounds_match(number, Some(line)) ==> !within_line(bytes, line, offset as int),
        }
    }

    spec fn exact_position_at(
        &self, offset: usize, encoding: PositionEncoding, position: TextPosition, line: LineBounds,
    ) -> bool {
        &&& self.line_bounds_match(position.line, Some(line))
        &&& within_line(self.bytes_model(), line, offset as int)
        &&& position.column == column_units(self.bytes_model(), line.start as int, offset as int, encoding)
    }

    /// UTF-8 のバイト位置から行・列を求める。
    ///
    /// 文書の範囲外、UTF-8 文字の途中、または CRLF の CR と LF の間は `None` を返す。
    pub fn byte_to_position(&self, offset: usize, encoding: PositionEncoding)
        -> (result: Option<TextPosition>)
        ensures self.byte_to_position_matches(offset, encoding, result),
    {
        let number = self.line_candidate(offset);
        let Some(line) = self.line(number) else { return None; };
        if offset < line.start || offset > line.end || !self.source.is_char_boundary(offset) {
            assert forall|other_number: usize, other: LineBounds|
                #[trigger] self.line_bounds_match(other_number, Some(other)) implies
                    !within_line(self.bytes_model(), other, offset as int) by {
                if within_line(self.bytes_model(), other, offset as int) {
                    self.exact_line_is_candidate(offset, other_number, other, number);
                    assert(other == line);
                }
            };
            return None;
        }
        let column = scan_column(self.source, line.start, offset, encoding);
        let position = TextPosition { line: number, column };
        assert(line == self.modeled_line(number));
        Some(position)
    }

    proof fn same_line_at_offset(
        &self, offset: usize, first: usize, first_bounds: LineBounds, second: usize, second_bounds: LineBounds,
    )
        requires
            self.valid(),
            self.line_bounds_match(first, Some(first_bounds)),
            self.line_bounds_match(second, Some(second_bounds)),
            first_bounds.start <= offset <= first_bounds.end,
            second_bounds.start <= offset <= second_bounds.end,
        ensures first == second,
    {
        let breaks = self.breaks_model();
        if first < second {
            assert(breaks[first as int] <= breaks[second - 1]);
        } else if second < first {
            assert(breaks[second as int] <= breaks[first - 1]);
        }
    }

    /// バイト位置を行・列に変換できる場合、逆変換は元のバイト位置を返す。
    pub proof fn byte_roundtrip(
        &self, offset: usize, position: TextPosition, encoding: PositionEncoding, result: Option<usize>,
    )
        requires
            self.byte_to_position_matches(offset, encoding, Some(position)),
            self.position_to_byte_matches(position, encoding, result),
        ensures result == Some(offset),
    {
        let bytes = self.bytes_model();
        let line = self.modeled_line(position.line);
        assert(offset_matches(bytes, line, position.column, encoding, offset as int));
        if let Some(actual) = result {
            let witness = choose|witness: LineBounds| {
                &&& #[trigger] self.line_bounds_match(position.line, Some(witness))
                &&& offset_matches(bytes, witness, position.column, encoding, actual as int)
            };
            assert(witness == line);
            encode_utf8_valid_utf8(self.source@);
            if actual < offset {
                distinct_columns(bytes, line.start as int, actual as int, offset as int, encoding);
            } else if offset < actual {
                distinct_columns(bytes, line.start as int, offset as int, actual as int, encoding);
            }
        }
    }

    /// 一行分の内容を指定した符号化の単位で数える。
    pub closed spec fn line_width_model(&self, line: LineBounds, encoding: PositionEncoding) -> nat
        recommends line.start <= line.end <= self.bytes_model().len(),
    {
        column_units(self.bytes_model(), line.start as int, line.end as int, encoding)
    }

    /// 行頭からの列を、元ソースの Unicode スカラー値で測る。
    pub closed spec fn unicode_column_model(&self, line: LineBounds, offset: usize, encoding: PositionEncoding) -> nat
        recommends line.start <= offset <= line.end <= self.bytes_model().len(),
    {
        scalar_units(decode_utf8(self.bytes_model().subrange(line.start as int, offset as int)), encoding)
    }

    /// 変換した列が、UTF-8・UTF-16・UTF-32 それぞれの Unicode コード単位数に等しいことを示す。
    pub proof fn position_counts_unicode(
        &self, source: &str, offset: usize, position: TextPosition, encoding: PositionEncoding,
    )
        requires self.line_index_matches(source), self.byte_to_position_matches(offset, encoding, Some(position)),
        ensures exists|line: LineBounds| {
            &&& #[trigger] self.line_bounds_match(position.line, Some(line))
            &&& position.column == self.unicode_column_model(line, offset, encoding)
        },
    {
        let bytes = self.bytes_model();
        let line = self.modeled_line(position.line);
        encode_utf8_valid_utf8(self.source@);
        self.start_is_boundary(position.line, line);
        unicode_span(bytes, line.start as int, offset as int, encoding);
        assert(position.column == self.unicode_column_model(line, offset, encoding));
    }

    /// 行・列をバイト位置に変換できる場合、逆変換は行末への丸めを反映した位置を返す。
    pub proof fn position_roundtrip(
        &self, source: &str, position: TextPosition, encoding: PositionEncoding, offset: usize, result: Option<TextPosition>,
    )
        requires
            self.line_index_matches(source),
            self.position_to_byte_matches(position, encoding, Some(offset)),
            self.byte_to_position_matches(offset, encoding, result),
        ensures
            result matches Some(normalized) && {
                &&& normalized.line == position.line
                &&& exists|line: LineBounds| {
                    &&& #[trigger] self.line_bounds_match(position.line, Some(line))
                    &&& normalized.column == if position.column <= self.line_width_model(line, encoding) {
                        position.column as nat
                    } else {
                        self.line_width_model(line, encoding)
                    }
                }
            },
    {
        let bytes = self.bytes_model();
        let line = choose|line: LineBounds| {
            &&& #[trigger] self.line_bounds_match(position.line, Some(line))
            &&& offset_matches(bytes, line, position.column, encoding, offset as int)
        };
        assert(within_line(bytes, line, offset as int));
        if let Some(normalized) = result {
            let witness = self.modeled_line(normalized.line);
            self.same_line_at_offset(offset, position.line, line, normalized.line, witness);
            assert(witness == line);
            later_column(bytes, line.start as int, offset as int, line.end as int, encoding);
            assert(normalized.column == if position.column <= column_units(bytes, line.start as int, line.end as int, encoding) {
                position.column as nat
            } else {
                column_units(bytes, line.start as int, line.end as int, encoding)
            });
        }
    }
}

} // verus!
