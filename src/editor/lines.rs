//! エディタの行番号を、UTF-8 ソース上の行の境界に対応付ける。

use alloc::vec::Vec;
use vstd::prelude::*;

#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 改行を除いた一行分の UTF-8 半開バイト範囲。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LineBounds {
    /// 行頭のバイト位置。
    pub start: usize,
    /// 改行の直前または文書の末尾。
    pub end: usize,
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
}

} // verus!
