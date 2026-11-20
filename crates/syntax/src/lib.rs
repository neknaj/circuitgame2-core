//! NCG2 ソースを字句と構文木に分ける。
//!
//! 厳格な S 式解析には [`parse`]、エディタ向けの回復解析には [`parse_recovering`] を使う。
//! 回路フォームの構文検査には [`circuit`] を使う。

#![no_std]

extern crate alloc;

mod atom;
mod bit_literal;
mod boundary;
pub mod circuit;
mod digits;
mod natural;
pub use bit_literal::{BitLiteral, BitLiteralSize, bit_literal_size, read_bit_literal};
#[cfg(verus_only)]
pub use bit_literal::{
    bit_literal_high_bits_are_zero, bit_literal_required_width_fits_spelling, bit_literal_size_matches, bit_literal_top_bit_is_one,
    bit_literal_value_at, bit_literal_written_widths_agree,
};
#[cfg(verus_only)]
pub use atom::natural_atom_has_value;
pub use natural::{NaturalRangeError, read_natural_u64};
#[cfg(verus_only)]
pub use natural::{decimal_natural_value, natural_u64_matches};
#[cfg(verus_only)]
mod form_model;
#[cfg(verus_only)]
pub use form_model::{sexpr_form_model, sexpr_models_agree_on_bytes};
#[cfg(verus_only)]
mod lexical;
#[cfg(verus_only)]
mod strict_error;
#[cfg(verus_only)]
mod strict_string_error;
#[cfg(verus_only)]
mod string_recovery_end;
#[cfg(verus_only)]
pub use strict_error::{strict_syntax_rejection, strict_token_errors_agree};
#[cfg(verus_only)]
pub use lexical::{
    InputDerivation, Lexeme, LexemeKind, input_lexeme_valid, lexeme_at, sexpr_input_derivation,
    well_formed_sexpr,
};
#[cfg(verus_only)]
mod projection;
#[cfg(verus_only)]
pub use projection::{forest_terminals, significant_pieces};
#[cfg(verus_only)]
mod quoted_prefix;
#[cfg(verus_only)]
pub use quoted_prefix::quoted_prefix_at;
#[cfg(verus_only)]
use quoted_prefix::{
    advance_quoted_prefixes_over_ordinary, escape_at_quoted_prefixes, initialize_quoted_prefixes,
    quoted_prefix_starts_with_quote, quoted_prefixes_viable, quoted_stop,
};
#[cfg(verus_only)]
use strict_string_error::{first_string_error, first_string_errors_agree, record_first_string_error};
#[cfg(verus_only)]
use string_recovery_end::{
    recovery_scalar_width, recovery_scalar_width_matches, skip_ordinary_string_bytes, string_recovery_end_from,
    string_recovery_end_after_escape, string_recovery_end_at_stop,
};

use crate::boundary::{Boundary, after_ascii, split_at_boundary, split_first_scalar};
use alloc::vec::Vec;
use atom::classify;
#[cfg(verus_only)]
pub use atom::{absolute_path_parts, absolute_path_parts_agree, bare_atom_kind, relative_path_parts, relative_path_parts_agree};
pub use atom::{split_absolute_path, split_relative_path};
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    encode_utf8_valid_utf8, is_char_boundary, is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_start_end_of_seq, is_continuation_byte, length_of_first_scalar, valid_utf8,
    valid_first_scalar, valid_utf8_split,
};

verus! {

/// 平坦な構文木のアトムまたはリストを表す。
///
/// `span` は元入力に対する半開バイト範囲である。開始位置と終了位置は UTF-8 の文字境界にある。
/// リストの `end` は、その部分木を過ぎた最初の添字である。
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Form {
    /// リストの子またはトップレベルに現れる一つの字句。
    Atom {
        /// 字句の分類。文字列のエスケープは元入力に残る。
        kind: AtomKind,
        /// アトム全体の範囲。文字列では引用符も含む。
        span: Range<usize>,
    },
    /// 開き括弧と子の部分木を持つ要素。
    List {
        /// 元入力上の開き括弧から閉じ括弧の直後まで。閉じ括弧を補った場合は元入力の末尾まで。
        span: Range<usize>,
        /// 同じ構文木の配列で部分木が終わる位置。末尾の部分木では配列の長さに等しい。
        end: usize,
    },
}

/// 字句文法で認識したアトムの種別。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AtomKind {
    /// 修飾子を含まない名前。
    Name,
    /// `::` で複数の名前をつないだ相対パス。
    RelativePath,
    /// 先頭に `::` を持つ完全修飾名。
    AbsolutePath,
    /// 十進数字の列。先頭にゼロを置ける。
    Natural,
    /// 先頭に `-` を持つ十進整数。
    NegativeInteger,
    /// `#b` に続く二進ビット列。
    Binary,
    /// `#x` に続く十六進ビット列。
    Hexadecimal,
    /// 二重引用符で囲んだ文字列。
    String,
}

/// 字句解析と S 式解析のエラー種別。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    /// トークン全体がどのアトムにも該当しない。
    InvalidAtom,
    /// 隣り合うアトムの間に区切りがない。主範囲は区切りを挿入する位置を指す。
    MissingSeparator,
    /// 文字列内に許されないエスケープがある。主範囲はバックスラッシュと直後の文字を含む。
    InvalidEscape {
        /// 開き引用符のバイト位置。
        opening: usize,
    },
    /// 入力末尾までに閉じ引用符がない。
    UnterminatedString,
    /// 閉じ引用符の前に CR または LF がある。
    NewlineInString {
        /// 開き引用符のバイト位置。
        opening: usize,
    },
    /// 対応する開き括弧がない閉じ括弧がある。
    UnexpectedClose,
    /// 入力末尾に達してもリストが閉じていない。主範囲は開き括弧を指す。
    UnclosedList {
        /// 閉じ括弧を補える入力末尾のバイト位置。
        eof: usize,
    },
}

/// 構文エラーと元入力上の主範囲。
#[derive(Debug, Eq, PartialEq)]
pub struct Error {
    /// 誤りの種別と、その説明に必要な関連位置。
    pub kind: ErrorKind,
    /// UTF-8 の半開バイト範囲。挿入位置を示す場合は長さ0となる。
    pub span: Range<usize>,
}

} // verus!

impl Clone for Error {
    fn clone(&self) -> Self {
        Self {
            kind: self.kind,
            span: self.span.clone(),
        }
    }
}

verus! {

#[derive(Debug, Eq, PartialEq)]
enum SegmentKind {
    Whitespace,
    Comment,
    Open,
    Close,
    Atom(AtomKind),
    Malformed(Error),
}

impl SegmentKind {
    spec fn is_atom(&self) -> bool {
        matches!(self, Self::Atom(_) | Self::Malformed(_))
    }
}

#[cfg(verus_only)]
spec fn segment_lexeme(kind: SegmentKind) -> Option<LexemeKind> {
    match kind {
        SegmentKind::Whitespace => Some(LexemeKind::Whitespace),
        SegmentKind::Comment => Some(LexemeKind::Comment),
        SegmentKind::Open => Some(LexemeKind::Open),
        SegmentKind::Close => Some(LexemeKind::Close),
        SegmentKind::Atom(kind) => Some(LexemeKind::Atom(kind)),
        SegmentKind::Malformed(_) => None,
    }
}

#[cfg(verus_only)]
#[verifier::opaque]
spec fn lexical_step_agrees(bytes: Seq<u8>, start: int, end: int, observed: Option<LexemeKind>) -> bool {
    &&& (observed is Some ==> lexeme_at(bytes, start, end, observed->Some_0))
    &&& forall|expected_end: int, expected: LexemeKind|
        #[trigger] lexeme_at(bytes, start, expected_end, expected)
            ==> end == expected_end && observed == Some(expected)
}

/// 不正な字句の診断と、字句解析で読み飛ばす範囲との対応を表す。
#[verifier::opaque]
spec fn malformed_segment_matches(bytes: Seq<u8>, span: Range<usize>, error: Error) -> bool {
    let start = span.start as int;
    let end = span.end as int;
    &&& 0 <= start < end <= bytes.len()
    &&& if error.kind is InvalidAtom {
        &&& span == error.span
        &&& bare_atom_extent(bytes, start, end)
        &&& bare_atom_kind(bytes[start..end]).is_none()
    } else {
        &&& bytes[start] == b'"'
        &&& first_string_error(bytes[start..], start, error)
        &&& end == start + string_recovery_end_from(bytes[start..], 1)
    }
}

/// 同じ開始位置から読み飛ばす範囲と、その診断は一意に定まる。
proof fn malformed_segments_agree(bytes: Seq<u8>, a: Range<usize>, b: Range<usize>, left: Error, right: Error)
    requires a.start == b.start, malformed_segment_matches(bytes, a, left), malformed_segment_matches(bytes, b, right),
    ensures a == b, left == right,
{
    reveal(malformed_segment_matches);
    reveal(bare_atom_extent);
    let start = a.start as int;
    if left.kind is InvalidAtom {
        assert(!bare_atom_delimiter(bytes[start]));
        if a.end < b.end {
            assert(!bare_atom_delimiter(bytes[a.end as int]));
        } else if b.end < a.end {
            assert(!bare_atom_delimiter(bytes[b.end as int]));
        }
    } else {
        if right.kind is InvalidAtom {
            assert(!bare_atom_delimiter(bytes[start]));
        }
        first_string_errors_agree(bytes[start..], start, left, right);
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Segment {
    kind: SegmentKind,
    span: Range<usize>,
    missing_separator: bool,
}

/// 指定した位置と直前の区切り状態から、正常または不正な一字句を読む規則を表す。
#[verifier::opaque]
spec fn recovery_segment_at(bytes: Seq<u8>, start: int, needs_separator: bool, segment: Segment) -> bool {
    let span = segment.span;
    &&& 0 <= start == span.start < span.end <= bytes.len()
    &&& is_char_boundary(bytes, start)
    &&& is_char_boundary(bytes, span.end as int)
    &&& lexical_step_agrees(bytes, start, span.end as int, segment_lexeme(segment.kind))
    &&& (segment.kind matches SegmentKind::Malformed(error) ==> malformed_segment_matches(bytes, span, error))
    &&& segment.missing_separator == (needs_separator && segment.kind.is_atom())
}

/// 同じバイト列の同じ位置と区切り状態から読む字句は、終端と診断を含めて一致する。
proof fn recovery_segments_agree(bytes: Seq<u8>, start: int, needs_separator: bool, left: Segment, right: Segment)
    requires
        recovery_segment_at(bytes, start, needs_separator, left),
        recovery_segment_at(bytes, start, needs_separator, right),
    ensures left == right,
{
    reveal(recovery_segment_at);
    reveal(lexical_step_agrees);
    match (left.kind, right.kind) {
        (SegmentKind::Malformed(a), SegmentKind::Malformed(b)) =>
            malformed_segments_agree(bytes, left.span, right.span, a, b),
        _ => {
            // 正常な字句が成立すれば、両方の根拠が同じ正常字句を選ぶ。
            let a = segment_lexeme(left.kind);
            let b = segment_lexeme(right.kind);
            if a is Some {
                assert(lexeme_at(bytes, start, left.span.end as int, a->Some_0));
            } else {
                assert(lexeme_at(bytes, start, right.span.end as int, b->Some_0));
            }
        },
    }
}

#[derive(Clone, Copy)]
struct Lexer<'a> {
    cursor: SourceCursor<'a>,
    needs_separator: bool,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> (lexer: Self)
        ensures
            lexer.cursor.source == source,
            lexer.cursor.valid(),
            lexer.cursor.position() == 0,
            !lexer.needs_separator,
    {
        Self {
            cursor: SourceCursor::new(source),
            needs_separator: false,
        }
    }

    fn next_segment(self) -> (step: Option<(Segment, Self)>)
        requires
            self.cursor.valid(),
        ensures
            match step {
                None => self.cursor.position() == self.cursor.source.spec_bytes().len(),
                Some((segment, next)) => {
                    &&& next.cursor.source == self.cursor.source
                    &&& next.cursor.valid()
                    &&& segment.span.start == self.cursor.position()
                    &&& segment.span.start < segment.span.end
                    &&& segment.span.end == next.cursor.position()
                    &&& segment.span.end <= self.cursor.source.spec_bytes().len()
                    &&& lexical_step_agrees(self.cursor.source.spec_bytes(), self.cursor.position(),
                        segment.span.end as int, segment_lexeme(segment.kind))
                    &&& is_char_boundary(self.cursor.source.spec_bytes(), segment.span.start as int)
                    &&& is_char_boundary(self.cursor.source.spec_bytes(), segment.span.end as int)
                    &&& (segment.kind is Whitespace || segment.kind is Comment ==> trivia_extent(
                        self.cursor.source.spec_bytes(), segment.span.start as int, segment.span.end as int,
                        segment.kind is Comment))
                    &&& (segment.kind is Open ==> segment.span.end == segment.span.start + 1
                        && self.cursor.source.spec_bytes()[segment.span.start as int] == 40)
                    &&& (segment.kind is Close ==> segment.span.end == segment.span.start + 1
                        && self.cursor.source.spec_bytes()[segment.span.start as int] == 41)
                    &&& (segment.kind is Malformed ==> syntax_error_evidence(
                        self.cursor.source, segment.kind->Malformed_0)
                        && (segment.kind->Malformed_0.kind is InvalidAtom
                            || string_error_kind(segment.kind->Malformed_0.kind))
                        && strict_error::malformed_atom_extent(self.cursor.source.spec_bytes(),
                            segment.span.start as int, segment.kind->Malformed_0)
                        && malformed_segment_matches(self.cursor.source.spec_bytes(), segment.span, segment.kind->Malformed_0))
                    &&& (segment.kind is Atom ==> form_atom_matches(self.cursor.source,
                        Form::Atom { kind: segment.kind->Atom_0, span: segment.span }))
                    &&& next.needs_separator == segment.kind.is_atom()
                    &&& segment.missing_separator == (self.needs_separator && segment.kind.is_atom())
                    &&& recovery_segment_at(self.cursor.source.spec_bytes(), self.cursor.position(),
                        self.needs_separator, segment)
                },
            },
    {
        let Some((raw, span, cursor)) = self.cursor.advance() else {
            return None;
        };
        let ghost raw_segment = raw;
        let (kind, is_atom) = match raw {
            RawSegment::Whitespace => (SegmentKind::Whitespace, false),
            RawSegment::Comment => (SegmentKind::Comment, false),
            RawSegment::Open => (SegmentKind::Open, false),
            RawSegment::Close => (SegmentKind::Close, false),
            RawSegment::Quoted(error) => (
                match error {
                    Some(error) => SegmentKind::Malformed(error),
                    None => SegmentKind::Atom(AtomKind::String),
                },
                true,
            ),
            RawSegment::Bare(atom) => (
                match classify(atom) {
                    Some(atom) => SegmentKind::Atom(atom),
                    None => SegmentKind::Malformed(Error {
                        kind: ErrorKind::InvalidAtom,
                        span: span.start..span.end,
                    }),
                },
                true,
            ),
        };
        assert(kind is Malformed ==> syntax_error_evidence(self.cursor.source, kind->Malformed_0))
            by { reveal(syntax_error_evidence); reveal(atom_and_close_error_evidence); };
        assert(kind is Malformed ==> strict_error::malformed_atom_extent(
            self.cursor.source.spec_bytes(), span.start as int, kind->Malformed_0)) by {
            reveal(strict_error::malformed_atom_extent);
        };
        assert(kind is Malformed ==> malformed_segment_matches(self.cursor.source.spec_bytes(), span, kind->Malformed_0)) by {
            reveal(malformed_segment_matches);
        };
        proof {
            assert(segment_lexeme(kind) is Some ==> lexeme_at(
                self.cursor.source.spec_bytes(), span.start as int,
                span.end as int, segment_lexeme(kind)->Some_0)) by {
                reveal(lexeme_at);
                match raw_segment {
                    RawSegment::Bare(atom) => {
                        assert(atom.spec_bytes() =~= self.cursor.source.spec_bytes()[
                            span.start as int..span.end as int]);
                    }
                    _ => {}
                }
            };
            assert forall|end: int, expected: LexemeKind|
                #[trigger] lexeme_at(self.cursor.source.spec_bytes(), self.cursor.position(), end, expected)
                implies span.end == end && segment_lexeme(kind) == Some(expected) by {
                let bytes = self.cursor.source.spec_bytes();
                let start = self.cursor.position();
                lexical::lexical_extent_facts(bytes, start, end, expected);
                match raw_segment {
                    RawSegment::Whitespace => {
                        lexical::raw_trivia_matches(bytes, start, span.end as int, end, expected, false);
                    }
                    RawSegment::Comment => {
                        lexical::raw_trivia_matches(bytes, start, span.end as int, end, expected, true);
                    }
                    RawSegment::Open => {
                        assert(expected == LexemeKind::Open);
                    }
                    RawSegment::Close => {
                        assert(expected == LexemeKind::Close);
                    }
                    RawSegment::Quoted(_) => {
                        assert(expected == LexemeKind::Atom(AtomKind::String));
                        reveal(lexeme_at);
                        reveal(quoted_prefix_at);
                        let relative_close = end - start - 1;
                        let remaining = self.cursor.remaining.spec_bytes();
                        assert(remaining[..relative_close + 1] =~= bytes[start..end]);
                        assert(quoted_prefix_at(remaining, relative_close));
                        assert(raw_segment->Quoted_0 is None);
                        assert(segment_lexeme(kind) == Some(expected));
                    }
                    RawSegment::Bare(atom) => {
                        let expected_kind = lexical::raw_bare_matches(
                            bytes, start, span.end as int, end, expected);
                        assert(atom.spec_bytes() =~= bytes[start..end]);
                        assert(bare_atom_kind(atom.spec_bytes()) == Some(expected_kind));
                        assert(segment_lexeme(kind) == Some(expected));
                    }
                }
            };
            assert(lexical_step_agrees(self.cursor.source.spec_bytes(), self.cursor.position(),
                span.end as int, segment_lexeme(kind))) by {
                reveal(lexical_step_agrees);
            };
        }
        let missing_separator = self.needs_separator && is_atom;
        let segment = Segment { kind, span, missing_separator };
        assert(recovery_segment_at(self.cursor.source.spec_bytes(), self.cursor.position(),
            self.needs_separator, segment)) by {
            reveal(recovery_segment_at);
        };
        Some((segment, Self { cursor, needs_separator: is_atom }))
    }
}

} // verus!

#[cfg(test)]
impl Iterator for Lexer<'_> {
    type Item = Segment;

    fn next(&mut self) -> Option<Segment> {
        let (segment, next) = self.next_segment()?;
        *self = next;
        Some(segment)
    }
}

verus! {

/// 回復解析が行った操作と、その根拠となる元入力の位置を表す。
///
/// 操作の記録は解析順に並ぶ。元入力を編集する場合は、記録された範囲と各操作の意味を確認する。
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Repair {
    /// 不正な入力を読み飛ばした。
    Skipped {
        /// 読み飛ばした元入力の半開バイト範囲。
        span: Range<usize>,
        /// 読み飛ばす根拠となった構文エラー。
        error: Error,
    },
    /// アトム間に区切りがあるものとして解析を続けた。
    InsertedSeparator {
        /// 補完位置を示す元入力のバイト位置。
        offset: usize,
    },
    /// 入力末尾でリストを閉じたものとして構文木を作った。
    InsertedClose {
        /// 閉じ括弧の合成位置。入力のバイト長に等しい。
        offset: usize,
        /// 対応する開き括弧の半開バイト範囲。
        opening: Range<usize>,
        /// 閉じ括弧を補ったリストを指す、[`Recovered::forms`] 内の添字。
        list: usize,
    },
}

/// 回復解析で得た構文木と修復記録を保持する。
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Recovered {
    /// 回復した構文木を先行順に並べる。
    ///
    /// 修復した箇所を含む構文は暫定である。合成した閉じ括弧は元入力の範囲を占めない。
    pub forms: Vec<Form>,
    /// 入力の読み飛ばしや欠落の補完を解析順に並べる。
    pub repairs: Vec<Repair>,
    /// 深さ 0 で読み始め、修復を挟まず元入力の閉じ括弧で閉じたリストの範囲。
    ///
    /// UTF-8 の半開バイト範囲を元入力順に並べる。アトムと補完されたリストは含まない。
    pub original_lists: Vec<Range<usize>>,
}

/// 入力全体を厳格に解析し、S 式の構文木を先行順で返す。
///
/// リストでは、リスト自身の要素に続いて子の部分木が並ぶ。範囲と添字の意味は [`Form`] を参照する。
///
/// # Errors
///
/// 不正な字句、アトム間の区切り不足、対応する括弧の欠落や余分な閉じ括弧を検出すると、
/// 元入力上の範囲とエラー種別を返す。
///
/// # Examples
///
/// ```
/// use circuitgame2_syntax::{Form, parse};
///
/// let forms = parse("(using nor)")?;
/// assert!(matches!(&forms[0], Form::List { end: 3, .. }));
/// # Ok::<(), circuitgame2_syntax::Error>(())
/// ```
pub fn parse(source: &str) -> (result: Result<Vec<Form>, Error>)
    ensures
        well_formed_sexpr(source) == result.is_ok(),
        match result {
            Ok(forms) => complete_list_indices(forms@) && nested_list_indices(forms@)
                && list_source_delimiters(source, forms@, false)
                && form_spans_valid(source, forms@, source.spec_bytes().len() as int)
                && strict_source_covered(source, forms@)
                && strict_sexpr_derivation(source, forms@)
                && sexpr_form_model(source) == Some(forms@),
            Err(error) => syntax_error_evidence(source, error) && strict_syntax_rejection(source, error),
        },
{
    match parse_forms(source, false) {
        Ok((forms, _, _)) => {
            proof { derive_strict_forest(source, forms@); }
            Ok(forms)
        }
        Err(error) => Err(error),
    }
}

/// エディタ向けに構文エラーから回復し、得られた S 式の構文木と修復記録を返す。
///
/// 閉じ括弧が欠けたリストは入力末尾で閉じたものとし、合成位置と開き括弧の範囲を記録する。
/// 読み飛ばした入力と補った区切りも記録する。妥当な入力では [`parse`] と同じ構文木を返し、修復記録は空になる。
///
/// # Examples
///
/// ```
/// use circuitgame2_syntax::{Repair, parse_recovering};
///
/// let result = parse_recovering("(using");
/// assert!(matches!(&result.repairs[..], [Repair::InsertedClose { offset: 6, .. }]));
/// ```
pub fn parse_recovering(source: &str) -> (result: Recovered)
    ensures
        well_formed_sexpr(source) ==> result.repairs@.len() == 0
            && sexpr_form_model(source) == Some(result.forms@),
        complete_list_indices(result.forms@),
        nested_list_indices(result.forms@),
        list_source_delimiters(source, result.forms@, true),
        inserted_closes_match(source, result.forms@, result.repairs@),
        repair_input_spans_valid(source, result.repairs@, source.spec_bytes().len() as int),
        form_spans_valid(source, result.forms@, source.spec_bytes().len() as int),
        original_list_ranges(source, result.original_lists@, result.repairs@, source.spec_bytes().len() as int),
{
    match parse_forms(source, true) {
        Ok((forms, repairs, original_lists)) => Recovered { forms, repairs, original_lists },
        Err(_) => unreachable!("recovery handles each syntax error"),
    }
}

pub open spec fn covers(bytes: Seq<u8>, spans: Seq<(int, int)>, end: int) -> bool {
    &&& 0 <= end <= bytes.len()
    &&& (spans.len() == 0 ==> end == 0)
    &&& (spans.len() > 0 ==> spans[spans.len() - 1].1 == end)
    &&& forall|i: int| 0 <= i < spans.len() ==> {
        let span = #[trigger] spans[i];
        &&& 0 <= span.0 < span.1 <= end
        &&& is_char_boundary(bytes, span.0)
        &&& is_char_boundary(bytes, span.1)
        &&& span.0 == if i == 0 { 0 } else { spans[i - 1].1 }
    }
}

pub open spec fn first_form_piece(form: Form) -> (int, int) {
    let span = form_span(form);
    (span.start as int, if form is List { span.start + 1 } else { span.end as int })
}

pub open spec fn list_close_piece(form: Form) -> (int, int) {
    let end = form_span(form).end as int;
    (end - 1, end)
}

pub open spec fn form_represents_piece(form: Form, piece: (int, int)) -> bool {
    piece == first_form_piece(form)
        || (form is List && form->List_end != 0
            && form_span(form).start + 1 < form_span(form).end
            && piece == list_close_piece(form))
}

pub open spec fn parsed_piece(source: &str, forms: Seq<Form>, piece: (int, int)) -> bool {
    trivia_extent(source.spec_bytes(), piece.0, piece.1, false)
        || trivia_extent(source.spec_bytes(), piece.0, piece.1, true)
        || exists|i: int| 0 <= i < forms.len()
            && form_represents_piece(#[trigger] forms[i], piece)
}

#[verifier::opaque]
pub open spec fn pieces_represented(source: &str, forms: Seq<Form>, pieces: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < pieces.len() ==> parsed_piece(source, forms, #[trigger] pieces[i])
}

pub open spec fn form_pieces_present(form: Form, pieces: Seq<(int, int)>) -> bool {
    &&& pieces.contains(first_form_piece(form))
    &&& (form is List && form->List_end != 0 ==> {
        &&& form_span(form).start + 1 < form_span(form).end
        &&& pieces.contains(list_close_piece(form))
    })
}

#[verifier::opaque]
pub open spec fn all_form_pieces_present(forms: Seq<Form>, pieces: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < forms.len() ==> form_pieces_present(#[trigger] forms[i], pieces)
}

pub open spec fn closed_list(form: Form) -> bool {
    form is List && form->List_end != 0
}

#[verifier::opaque]
pub open spec fn distinct_list_closes(forms: Seq<Form>) -> bool {
    forall|i: int, j: int| 0 <= i < j < forms.len()
        && #[trigger] closed_list(forms[i]) && #[trigger] closed_list(forms[j])
        ==> form_span(forms[i]).end != form_span(forms[j]).end
}

pub open spec fn preorder_range_pair(earlier: Form, later: Form, later_index: int) -> bool {
    let first = form_span(earlier);
    let second = form_span(later);
    &&& first.start < second.start
    &&& match earlier {
        Form::Atom { .. } => {
            if later is Atom { first.end < second.start } else { first.end <= second.start }
        },
        Form::List { end, .. } => {
            if end == 0 {
                true
            } else if later_index < end {
                second.end < first.end
            } else {
                first.end <= second.start
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn strict_preorder_ranges(forms: Seq<Form>) -> bool {
    forall|i: int, j: int| 0 <= i < j < forms.len()
        ==> preorder_range_pair(#[trigger] forms[i], #[trigger] forms[j], j)
}

#[verifier::opaque]
spec fn atoms_end_before(forms: Seq<Form>, position: int) -> bool {
    forall|i: int| 0 <= i < forms.len() && #[trigger] forms[i] is Atom
        ==> form_span(forms[i]).end < position
}

proof fn atoms_stay_behind_cursor(
    source: &str, before: Seq<Form>, after: Seq<Form>, previous: int, next: int,
)
    requires
        form_spans_valid(source, before, previous),
        previous < next,
        forall|i: int| 0 <= i < after.len() && #[trigger] after[i] is Atom
            ==> i < before.len() && after[i] == before[i],
    ensures atoms_end_before(after, next),
{
    reveal(form_spans_valid);
    reveal(atoms_end_before);
    assert forall|i: int| 0 <= i < after.len() && #[trigger] after[i] is Atom
        implies form_span(after[i]).end < next by {
        assert(after[i] == before[i]);
        assert(form_span(before[i]).end <= previous);
    };
}

proof fn append_preserves_preorder_ranges(
    source: &str, forms: Seq<Form>, added: Form, before: int,
)
    requires
        strict_preorder_ranges(forms),
        form_spans_valid(source, forms, before),
        complete_or_pending_ends_in_bounds(forms),
        form_span(added).start == before,
        added is Atom ==> atoms_end_before(forms, before),
    ensures strict_preorder_ranges(forms.push(added)),
{
    reveal(strict_preorder_ranges);
    reveal(form_spans_valid);
    reveal(atoms_end_before);
    let extended = forms.push(added);
    assert forall|i: int, j: int| 0 <= i < j < extended.len()
        implies preorder_range_pair(#[trigger] extended[i], #[trigger] extended[j], j) by {
        assert(extended[i] == forms[i]);
        if j < forms.len() {
            assert(extended[j] == forms[j]);
        } else {
            assert(extended[j] == added);
            assert(form_span(forms[i]).start < form_span(forms[i]).end <= before);
        }
    };
}

spec fn complete_or_pending_ends_in_bounds(forms: Seq<Form>) -> bool {
    forall|i: int| 0 <= i < forms.len() && #[trigger] forms[i] is List
        ==> forms[i]->List_end <= forms.len()
}

proof fn close_preserves_preorder_ranges(
    source: &str, before: Seq<Form>, after: Seq<Form>, closed: int, position: int,
)
    requires
        strict_preorder_ranges(before),
        nested_list_indices(before),
        form_spans_valid(source, before, position),
        0 <= closed < before.len() == after.len(),
        before[closed] is List && before[closed]->List_end == 0,
        after[closed] is List && after[closed]->List_end == after.len(),
        form_span(after[closed]).start == form_span(before[closed]).start,
        position < form_span(after[closed]).end,
        forall|i: int| 0 <= i < before.len() && i != closed
            ==> #[trigger] after[i] == before[i],
    ensures strict_preorder_ranges(after),
{
    reveal(strict_preorder_ranges);
    reveal(form_spans_valid);
    reveal(nested_list_indices);
    assert forall|i: int, j: int| 0 <= i < j < after.len()
        implies preorder_range_pair(#[trigger] after[i], #[trigger] after[j], j) by {
        assert(preorder_range_pair(before[i], before[j], j));
        if i == closed {
            assert(after[j] == before[j]);
            assert(form_span(before[j]).end <= position);
        } else if j == closed {
            assert(after[i] == before[i]);
            if closed_list(before[i]) {
                assert(before[i]->List_end <= closed);
            }
        } else {
            assert(after[i] == before[i] && after[j] == before[j]);
        }
    };
}

proof fn preorder_ranges_have_distinct_closes(source: &str, forms: Seq<Form>, consumed: int)
    requires
        strict_preorder_ranges(forms),
        form_spans_valid(source, forms, consumed),
    ensures distinct_list_closes(forms),
{
    reveal(strict_preorder_ranges);
    reveal(distinct_list_closes);
    reveal(form_spans_valid);
    assert forall|i: int, j: int| 0 <= i < j < forms.len()
        && #[trigger] closed_list(forms[i]) && #[trigger] closed_list(forms[j])
        implies form_span(forms[i]).end != form_span(forms[j]).end by {
        assert(preorder_range_pair(forms[i], forms[j], j));
        assert(form_span(forms[j]).start < form_span(forms[j]).end);
    };
}

#[verifier::opaque]
pub open spec fn strict_source_covered(source: &str, forms: Seq<Form>) -> bool {
    &&& distinct_list_closes(forms)
    &&& strict_preorder_ranges(forms)
    &&& exists|pieces: Seq<(int, int)>| covers(source.spec_bytes(), pieces, source.spec_bytes().len() as int)
        && #[trigger] pieces_represented(source, forms, pieces)
        && all_form_pieces_present(forms, pieces)
}

proof fn source_coverage_from_pieces(source: &str, forms: Seq<Form>, pieces: Seq<(int, int)>)
    requires
        covers(source.spec_bytes(), pieces, source.spec_bytes().len() as int),
        pieces_represented(source, forms, pieces),
        all_form_pieces_present(forms, pieces),
        distinct_list_closes(forms),
        strict_preorder_ranges(forms),
    ensures strict_source_covered(source, forms),
{
    reveal(strict_source_covered);
}

proof fn append_represented_piece(
    source: &str, forms: Seq<Form>, pieces: Seq<(int, int)>, piece: (int, int),
)
    requires pieces_represented(source, forms, pieces), parsed_piece(source, forms, piece),
    ensures pieces_represented(source, forms, pieces.push(piece)),
{
    reveal(pieces_represented);
    let extended = pieces.push(piece);
    assert forall|i: int| 0 <= i < extended.len()
        implies parsed_piece(source, forms, #[trigger] extended[i]) by {
        if i < pieces.len() {
            assert(extended[i] == pieces[i]);
        }
    };
}

proof fn preserve_represented_pieces(
    source: &str, before: Seq<Form>, after: Seq<Form>, pieces: Seq<(int, int)>,
)
    requires
        pieces_represented(source, before, pieces),
        before.len() <= after.len(),
        forall|i: int, piece: (int, int)| 0 <= i < before.len()
            && #[trigger] form_represents_piece(before[i], piece)
            ==> form_represents_piece(after[i], piece),
    ensures pieces_represented(source, after, pieces),
{
    reveal(pieces_represented);
    assert forall|i: int| 0 <= i < pieces.len()
        implies parsed_piece(source, after, #[trigger] pieces[i]) by {
        let piece = pieces[i];
        assert(parsed_piece(source, before, piece));
        if !trivia_extent(source.spec_bytes(), piece.0, piece.1, false)
            && !trivia_extent(source.spec_bytes(), piece.0, piece.1, true)
        {
            let witness = choose|j: int| 0 <= j < before.len()
                && form_represents_piece(#[trigger] before[j], piece);
            assert(form_represents_piece(before[witness], piece));
            assert(form_represents_piece(after[witness], piece));
        }
    };
}

proof fn appended_form_preserves_pieces(
    source: &str, forms: Seq<Form>, added: Form, pieces: Seq<(int, int)>,
)
    requires pieces_represented(source, forms, pieces),
    ensures pieces_represented(source, forms.push(added), pieces),
{
    preserve_represented_pieces(source, forms, forms.push(added), pieces);
}

proof fn closed_form_preserves_pieces(
    source: &str, before: Seq<Form>, after: Seq<Form>, closed: int, pieces: Seq<(int, int)>,
)
    requires
        pieces_represented(source, before, pieces),
        before.len() == after.len(),
        0 <= closed < before.len(),
        before[closed] is List && before[closed]->List_end == 0,
        after[closed] is List && after[closed]->List_span.start == before[closed]->List_span.start,
        forall|i: int| 0 <= i < before.len() && i != closed
            ==> #[trigger] after[i] == before[i],
    ensures pieces_represented(source, after, pieces),
{
    assert forall|i: int, piece: (int, int)| 0 <= i < before.len()
        && #[trigger] form_represents_piece(before[i], piece)
        implies form_represents_piece(after[i], piece) by {
        if i == closed {
            assert(piece == (before[i]->List_span.start as int, before[i]->List_span.start + 1));
        } else {
            assert(after[i] == before[i]);
        }
    };
    preserve_represented_pieces(source, before, after, pieces);
}

proof fn piece_membership_preserved(pieces: Seq<(int, int)>, piece: (int, int))
    ensures
        forall|old: (int, int)| #[trigger] pieces.contains(old) ==> pieces.push(piece).contains(old),
        pieces.push(piece).contains(piece),
{
    let extended = pieces.push(piece);
    assert(extended[pieces.len() as int] == piece);
    assert forall|old: (int, int)| #[trigger] pieces.contains(old)
        implies extended.contains(old) by {
        let i = choose|i: int| 0 <= i < pieces.len() && pieces[i] == old;
        assert(extended[i] == old);
    };
}

proof fn form_pieces_preserved(
    forms: Seq<Form>, after: Seq<Form>, pieces: Seq<(int, int)>, piece: (int, int),
)
    requires
        all_form_pieces_present(forms, pieces),
        forall|i: int| 0 <= i < after.len()
            && (i >= forms.len() || #[trigger] after[i] != forms[i])
            ==> form_pieces_present(after[i], pieces.push(piece)),
    ensures all_form_pieces_present(after, pieces.push(piece)),
{
    reveal(all_form_pieces_present);
    piece_membership_preserved(pieces, piece);
    assert forall|i: int| 0 <= i < after.len()
        implies form_pieces_present(#[trigger] after[i], pieces.push(piece)) by {
        if i < forms.len() && after[i] == forms[i] {
            assert(form_pieces_present(forms[i], pieces));
        }
    };
}

proof fn add_form_pieces(forms: Seq<Form>, added: Form, pieces: Seq<(int, int)>, piece: (int, int))
    requires
        all_form_pieces_present(forms, pieces),
        first_form_piece(added) == piece,
        added is List ==> added->List_end == 0,
    ensures all_form_pieces_present(forms.push(added), pieces.push(piece)),
{
    piece_membership_preserved(pieces, piece);
    let after = forms.push(added);
    assert(after[forms.len() as int] == added);
    form_pieces_preserved(forms, after, pieces, piece);
}

proof fn close_form_pieces(
    before: Seq<Form>, after: Seq<Form>, closed: int, pieces: Seq<(int, int)>, piece: (int, int),
)
    requires
        all_form_pieces_present(before, pieces),
        before.len() == after.len(),
        0 <= closed < before.len(),
        before[closed] is List && after[closed] is List,
        first_form_piece(before[closed]) == first_form_piece(after[closed]),
        form_span(after[closed]).start + 1 < form_span(after[closed]).end,
        list_close_piece(after[closed]) == piece,
        forall|i: int| 0 <= i < before.len() && i != closed
            ==> #[trigger] after[i] == before[i],
    ensures all_form_pieces_present(after, pieces.push(piece)),
{
    reveal(all_form_pieces_present);
    piece_membership_preserved(pieces, piece);
    assert(form_pieces_present(before[closed], pieces));
    assert(form_pieces_present(after[closed], pieces.push(piece)));
    form_pieces_preserved(before, after, pieces, piece);
}

spec fn pending_lists(forms: Seq<Form>, open: Seq<usize>) -> bool {
    forall|i: int| 0 <= i < open.len() ==> {
        let index = #[trigger] open[i] as int;
        0 <= index < forms.len() && forms[index] is List && forms[index]->List_end == 0
            && forms[index]->List_span.end == forms[index]->List_span.start + 1
    }
}

pub open spec fn form_span(form: Form) -> Range<usize> {
    match form {
        Form::Atom { span, .. } | Form::List { span, .. } => span,
    }
}

pub open spec fn bare_atom_delimiter(byte: u8) -> bool {
    byte == 32 || byte == 9 || byte == 10 || byte == 13 || byte == 59
        || byte == 40 || byte == 41 || byte == 34
}

#[verifier::opaque]
pub open spec fn bare_atom_extent(bytes: Seq<u8>, start: int, end: int) -> bool {
    &&& 0 <= start < end <= bytes.len()
    &&& forall|i: int| start <= i < end ==> !bare_atom_delimiter(#[trigger] bytes[i])
    &&& (end < bytes.len() ==> bare_atom_delimiter(bytes[end]))
}

pub open spec fn trivia_byte(byte: u8, comment: bool) -> bool {
    if comment {
        byte != 10 && byte != 13
    } else {
        byte == 32 || byte == 9 || byte == 10 || byte == 13
    }
}

#[verifier::opaque]
pub open spec fn trivia_extent(bytes: Seq<u8>, start: int, end: int, comment: bool) -> bool {
    &&& 0 <= start < end <= bytes.len()
    &&& (comment ==> bytes[start] == 59)
    &&& forall|i: int| start <= i < end ==> trivia_byte(#[trigger] bytes[i], comment)
    &&& (end < bytes.len() ==> !trivia_byte(bytes[end], comment))
}

proof fn lift_trivia_extent(bytes: Seq<u8>, suffix: Seq<u8>, start: int, end: int, comment: bool)
    requires
        0 <= start < end <= bytes.len(),
        suffix == bytes[start..],
        trivia_extent(suffix, 0, end - start, comment),
    ensures trivia_extent(bytes, start, end, comment),
{
    reveal(trivia_extent);
    assert(bytes[start] == suffix[0]);
    assert forall|i: int| start <= i < end implies trivia_byte(#[trigger] bytes[i], comment) by {
        assert(bytes[i] == suffix[i - start]);
    };
    if end < bytes.len() {
        assert(bytes[end] == suffix[end - start]);
    }
}

fn split_trivia(input: &str, comment: bool) -> (remaining: &str)
    requires
        input.spec_bytes().len() > 0,
        if comment { input.spec_bytes()[0] == 59 } else { trivia_byte(input.spec_bytes()[0], false) },
    ensures
        is_suffix(input.spec_bytes(), remaining.spec_bytes()),
        trivia_extent(input.spec_bytes(), 0, input.spec_bytes().len() - remaining.spec_bytes().len(), comment),
        remaining.spec_bytes().len() < input.spec_bytes().len(),
{
    let (_trivia, remaining) = split_at_boundary(input,
        if comment { Boundary::LineEnd } else { Boundary::NonSpace });
    proof {
        reveal(trivia_extent);
        let bytes = input.spec_bytes();
        let end = _trivia.spec_bytes().len() as int;
        assert(end > 0);
        assert forall|i: int| 0 <= i < end implies trivia_byte(#[trigger] bytes[i], comment) by {
            assert(bytes[i] == _trivia.spec_bytes()[i]);
        };
        if end < bytes.len() {
            assert(bytes[end] == remaining.spec_bytes()[0]);
        }
    }
    remaining
}

proof fn lift_bare_extent(bytes: Seq<u8>, suffix: Seq<u8>, start: int, end: int)
    requires
        0 <= start < end <= bytes.len(),
        suffix == bytes[start..],
        bare_atom_extent(suffix, 0, end - start),
    ensures bare_atom_extent(bytes, start, end),
{
    reveal(bare_atom_extent);
    assert forall|i: int| start <= i < end implies !bare_atom_delimiter(#[trigger] bytes[i]) by {
        assert(bytes[i] == suffix[i - start]);
    };
    if end < bytes.len() {
        assert(bytes[end] == suffix[end - start]);
    }
}

pub open spec fn bare_form_matches(source: &str, form: Form) -> bool {
    match form {
        Form::Atom { kind, span } => kind != AtomKind::String ==> (
            bare_atom_extent(source.spec_bytes(), span.start as int, span.end as int)
            && bare_atom_kind(source.spec_bytes()[span.start as int..span.end as int]) == Some(kind)
        ),
        Form::List { .. } => true,
    }
}

pub open spec fn form_atom_matches(source: &str, form: Form) -> bool {
    &&& bare_form_matches(source, form)
    &&& match form {
        Form::Atom { kind: AtomKind::String, span } => {
            &&& span.start < span.end <= source.spec_bytes().len()
            &&& quoted_atom(source.spec_bytes()[span.start as int..span.end as int])
        },
        _ => true,
    }
}

#[verifier::opaque]
pub open spec fn form_spans_valid(source: &str, forms: Seq<Form>, consumed: int) -> bool {
    &&& 0 <= consumed <= source.spec_bytes().len()
    &&& forall|i: int| 0 <= i < forms.len() ==> {
        let span = form_span(#[trigger] forms[i]);
        &&& span.start < span.end <= consumed
        &&& is_char_boundary(source.spec_bytes(), span.start as int)
        &&& is_char_boundary(source.spec_bytes(), span.end as int)
        &&& (i > 0 ==> form_span(forms[i - 1]).start < span.start)
        &&& form_atom_matches(source, forms[i])
    }
}

proof fn advance_form_spans(source: &str, forms: Seq<Form>, before: int, after: int)
    requires
        form_spans_valid(source, forms, before),
        before <= after <= source.spec_bytes().len(),
    ensures form_spans_valid(source, forms, after),
{
    reveal(form_spans_valid);
}

proof fn append_form_span(source: &str, forms: Seq<Form>, form: Form, before: int, after: int)
    requires
        form_spans_valid(source, forms, before),
        form_atom_matches(source, form),
        before == form_span(form).start,
        before < form_span(form).end <= after <= source.spec_bytes().len(),
        is_char_boundary(source.spec_bytes(), before),
        is_char_boundary(source.spec_bytes(), form_span(form).end as int),
    ensures form_spans_valid(source, forms.push(form), after),
{
    reveal(form_spans_valid);
    let extended = forms.push(form);
    assert forall|i: int| 0 <= i < extended.len() implies {
        let span = form_span(#[trigger] extended[i]);
        &&& span.start < span.end <= after
        &&& is_char_boundary(source.spec_bytes(), span.start as int)
        &&& is_char_boundary(source.spec_bytes(), span.end as int)
        &&& (i > 0 ==> form_span(extended[i - 1]).start < span.start)
        &&& form_atom_matches(source, extended[i])
    } by {
        if i < forms.len() {
            assert(extended[i] == forms[i]);
        } else if i > 0 {
            assert(extended[i - 1] == forms[i - 1]);
        }
    };
}

proof fn close_form_span(source: &str, forms: Seq<Form>, updated: Seq<Form>, index: int,
    before: int, after: int)
    requires
        form_spans_valid(source, forms, before),
        0 <= index < forms.len(),
        updated.len() == forms.len(),
        before <= after <= source.spec_bytes().len(),
        is_char_boundary(source.spec_bytes(), after),
        updated[index] is List,
        form_span(updated[index]).start == form_span(forms[index]).start,
        form_span(updated[index]).end == after,
        forall|i: int| 0 <= i < forms.len() && i != index ==> #[trigger] updated[i] == forms[i],
    ensures form_spans_valid(source, updated, after),
{
    reveal(form_spans_valid);
    assert forall|i: int| 0 <= i < updated.len() implies {
        let span = form_span(#[trigger] updated[i]);
        &&& span.start < span.end <= after
        &&& is_char_boundary(source.spec_bytes(), span.start as int)
        &&& is_char_boundary(source.spec_bytes(), span.end as int)
        &&& (i > 0 ==> form_span(updated[i - 1]).start < span.start)
        &&& form_atom_matches(source, updated[i])
    } by {
        assert(form_span(updated[i]).start == form_span(forms[i]).start);
        if i > 0 {
            assert(form_span(updated[i - 1]).start == form_span(forms[i - 1]).start);
        }
    };
}

pub open spec fn list_delimited(bytes: Seq<u8>, form: Form, recovering: bool) -> bool {
    match form {
        Form::List { span, end } => {
            &&& span.start < bytes.len()
            &&& bytes[span.start as int] == 40
            &&& (end > 0 ==> 0 < span.end <= bytes.len()
                && (bytes[span.end - 1] == 41 || (recovering && span.end == bytes.len())))
        },
        Form::Atom { .. } => true,
    }
}

#[verifier::opaque]
pub open spec fn list_source_delimiters(source: &str, forms: Seq<Form>, recovering: bool) -> bool {
    forall|i: int| 0 <= i < forms.len()
        ==> list_delimited(source.spec_bytes(), #[trigger] forms[i], recovering)
}

proof fn delimiters_after_append(source: &str, forms: Seq<Form>, form: Form, recovering: bool)
    requires
        list_source_delimiters(source, forms, recovering),
        list_delimited(source.spec_bytes(), form, recovering),
    ensures list_source_delimiters(source, forms.push(form), recovering),
{
    reveal(list_source_delimiters);
    let extended = forms.push(form);
    assert forall|i: int| 0 <= i < extended.len()
        implies list_delimited(source.spec_bytes(), #[trigger] extended[i], recovering) by {
        if i < forms.len() {
            assert(extended[i] == forms[i]);
        }
    };
}

proof fn delimiters_after_close(source: &str, forms: Seq<Form>, updated: Seq<Form>,
    index: int, recovering: bool)
    requires
        list_source_delimiters(source, forms, recovering),
        updated.len() == forms.len(),
        0 <= index < forms.len(),
        forms[index] is List,
        updated[index] is List,
        form_span(updated[index]).start == form_span(forms[index]).start,
        0 < form_span(updated[index]).end <= source.spec_bytes().len(),
        source.spec_bytes()[form_span(updated[index]).end - 1] == 41
            || (recovering && form_span(updated[index]).end == source.spec_bytes().len()),
        forall|i: int| 0 <= i < forms.len() && i != index ==> #[trigger] updated[i] == forms[i],
    ensures list_source_delimiters(source, updated, recovering),
{
    reveal(list_source_delimiters);
    assert forall|i: int| 0 <= i < updated.len()
        implies list_delimited(source.spec_bytes(), #[trigger] updated[i], recovering) by {
        if i != index {
            assert(updated[i] == forms[i]);
        } else {
            assert(list_delimited(source.spec_bytes(), forms[i], recovering));
        }
    };
}

pub open spec fn complete_list_indices(forms: Seq<Form>) -> bool {
    forall|i: int| 0 <= i < forms.len() ==> match #[trigger] forms[i] {
        Form::List { end, .. } => i < end <= forms.len(),
        Form::Atom { .. } => true,
    }
}

spec fn list_indices(forms: Seq<Form>, open: Seq<usize>) -> bool {
    forall|i: int| 0 <= i < forms.len() ==> match #[trigger] forms[i] {
        Form::List { end, .. } => if end == 0 {
            open.contains(i as usize)
        } else {
            i < end <= forms.len()
        },
        Form::Atom { .. } => true,
    }
}

#[verifier::opaque]
pub open spec fn nested_list_indices(forms: Seq<Form>) -> bool {
    forall|i: int, j: int| 0 <= i < j < forms.len()
        && #[trigger] forms[i] is List && #[trigger] forms[j] is List
        && j < forms[i]->List_end
        ==> 0 < forms[j]->List_end <= forms[i]->List_end
}

#[verifier::opaque]
pub open spec fn sexpr_forest(
    source: &str, forms: Seq<Form>, pieces: Seq<(int, int)>,
    first: int, limit: int, lower: int, upper: int,
) -> bool
    decreases limit - first,
{
    &&& 0 <= first <= limit <= forms.len()
    &&& 0 <= lower <= upper <= source.spec_bytes().len()
    &&& (first < limit ==> {
        let form = forms[first];
        let span = form_span(form);
        &&& lower <= span.start < span.end <= upper
        &&& form_pieces_present(form, pieces)
        &&& match form {
            Form::Atom { .. } => form_atom_matches(source, form)
                && sexpr_forest(source, forms, pieces, first + 1, limit, span.end as int, upper),
            Form::List { end, .. } => {
                &&& first < end <= limit
                &&& span.start + 1 < span.end
                &&& source.spec_bytes()[span.start as int] == 40
                &&& source.spec_bytes()[span.end - 1] == 41
                &&& sexpr_forest(source, forms, pieces, first + 1, end as int,
                    span.start + 1, span.end - 1)
                &&& sexpr_forest(source, forms, pieces, end as int, limit, span.end as int, upper)
            },
        }
    })
}

#[verifier::opaque]
spec fn forest_region(
    forms: Seq<Form>, first: int, limit: int, lower: int, upper: int,
) -> bool {
    forall|index: int| first <= index < limit ==> {
        let form = #[trigger] forms[index];
        &&& lower <= form_span(form).start
        &&& form_span(form).end <= upper
        &&& (form is List ==> form->List_end <= limit)
    }
}

proof fn derive_forest_region(
    source: &str, forms: Seq<Form>, pieces: Seq<(int, int)>,
    first: int, limit: int, lower: int, upper: int,
)
    requires
        0 <= first <= limit <= forms.len(),
        0 <= lower <= upper <= source.spec_bytes().len(),
        forest_region(forms, first, limit, lower, upper),
        complete_list_indices(forms),
        nested_list_indices(forms),
        strict_preorder_ranges(forms),
        all_form_pieces_present(forms, pieces),
        list_source_delimiters(source, forms, false),
        form_spans_valid(source, forms, source.spec_bytes().len() as int),
    ensures sexpr_forest(source, forms, pieces, first, limit, lower, upper),
    decreases limit - first,
{
    reveal(sexpr_forest);
    if first == limit {
        return;
    }
    reveal(forest_region);
    reveal(all_form_pieces_present);
    reveal(form_spans_valid);
    reveal(list_source_delimiters);
    reveal(strict_preorder_ranges);
    reveal(nested_list_indices);
    let form = forms[first];
    let span = form_span(form);
    assert(lower <= span.start < span.end <= upper);
    assert(form_pieces_present(form, pieces));
    let after = match form {
        Form::Atom { .. } => first + 1,
        Form::List { end, .. } => {
            assert(first < end <= limit);
            assert(list_delimited(source.spec_bytes(), form, false));
            assert(span.start + 1 < span.end);
            assert(forest_region(forms, first + 1, end as int, span.start + 1, span.end - 1)) by {
                assert forall|i: int| first + 1 <= i < end implies {
                    let child = #[trigger] forms[i];
                    &&& span.start + 1 <= form_span(child).start
                    &&& form_span(child).end <= span.end - 1
                    &&& (child is List ==> child->List_end <= end)
                } by {
                    assert(preorder_range_pair(form, forms[i], i));
                };
            };
            derive_forest_region(source, forms, pieces, first + 1, end as int, span.start + 1, span.end - 1);
            end as int
        },
    };
    assert(forest_region(forms, after, limit, span.end as int, upper)) by {
        assert forall|i: int| after <= i < limit implies {
            let sibling = #[trigger] forms[i];
            &&& span.end <= form_span(sibling).start
            &&& form_span(sibling).end <= upper
            &&& (sibling is List ==> sibling->List_end <= limit)
        } by {
            assert(preorder_range_pair(form, forms[i], i));
        };
    };
    derive_forest_region(source, forms, pieces, after, limit, span.end as int, upper);
}

#[verifier::opaque]
pub open spec fn strict_sexpr_derivation(source: &str, forms: Seq<Form>) -> bool {
    &&& strict_preorder_ranges(forms)
    &&& exists|pieces: Seq<(int, int)>|
        covers(source.spec_bytes(), pieces, source.spec_bytes().len() as int)
        && #[trigger] pieces_represented(source, forms, pieces)
        && sexpr_forest(source, forms, pieces, 0, forms.len() as int, 0, source.spec_bytes().len() as int)
        && significant_pieces(source, pieces) == forest_terminals(forms, 0, forms.len() as int)
}

proof fn derive_strict_forest(source: &str, forms: Seq<Form>)
    requires
        complete_list_indices(forms),
        nested_list_indices(forms),
        list_source_delimiters(source, forms, false),
        form_spans_valid(source, forms, source.spec_bytes().len() as int),
        strict_source_covered(source, forms),
    ensures strict_sexpr_derivation(source, forms),
{
    reveal(strict_source_covered);
    reveal(strict_sexpr_derivation);
    reveal(form_spans_valid);
    reveal(forest_region);
    let upper = source.spec_bytes().len() as int;
    let pieces = choose|pieces: Seq<(int, int)>| covers(source.spec_bytes(), pieces, upper)
        && #[trigger] pieces_represented(source, forms, pieces)
        && all_form_pieces_present(forms, pieces);
    derive_forest_region(source, forms, pieces, 0, forms.len() as int, 0, upper);
    projection::derive_projection(source, forms, pieces);
}

spec fn open_order(open: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < open.len() ==> #[trigger] open[i] < #[trigger] open[j]
}

proof fn nested_after_append(forms: Seq<Form>, added: Form)
    requires
        nested_list_indices(forms),
        forall|i: int| 0 <= i < forms.len() && #[trigger] forms[i] is List
            ==> forms[i]->List_end <= forms.len(),
    ensures nested_list_indices(forms.push(added)),
{
    reveal(nested_list_indices);
    let extended = forms.push(added);
    assert forall|i: int, j: int| 0 <= i < j < extended.len()
        && #[trigger] extended[i] is List && #[trigger] extended[j] is List
        && j < extended[i]->List_end
        implies 0 < extended[j]->List_end <= extended[i]->List_end by {
        assert(extended[i] == forms[i]);
        assert(j < forms.len());
        assert(extended[j] == forms[j]);
    };
}

proof fn nested_after_close(before: Seq<Form>, after: Seq<Form>, open: Seq<usize>, last: usize)
    requires
        nested_list_indices(before),
        list_indices(before, open),
        open_order(open),
        open.len() > 0,
        last == open[open.len() - 1],
        last < before.len(),
        before[last as int] is List,
        before[last as int]->List_end == 0,
        after.len() == before.len(),
        after[last as int] is List,
        after[last as int]->List_end == after.len(),
        forall|i: int| 0 <= i < before.len() && i != last ==> #[trigger] after[i] == before[i],
    ensures nested_list_indices(after),
{
    reveal(nested_list_indices);
    assert forall|i: int, j: int| 0 <= i < j < after.len()
        && #[trigger] after[i] is List && #[trigger] after[j] is List
        && j < after[i]->List_end
        implies 0 < after[j]->List_end <= after[i]->List_end by {
        if i == last {
            assert(after[j] == before[j]);
            if before[j]->List_end == 0 {
                assert(open.contains(j as usize));
                let at = choose|at: int| 0 <= at < open.len() && open[at] == j as usize;
                assert(at < open.len() - 1);
                assert(open[at] < open[open.len() - 1]);
            }
        } else {
            assert(after[i] == before[i]);
            if j == last {
                assert(0 < before[j]->List_end);
            } else {
                assert(after[j] == before[j]);
            }
        }
    };
}

proof fn indices_after_append(before: Seq<Form>, open: Seq<usize>, form: Form, next: Seq<usize>)
    requires
        list_indices(before, open),
        forall|i: usize| #[trigger] open.contains(i) ==> next.contains(i),
        before.len() < usize::MAX,
        form is List ==> form->List_end == 0 && next.contains(before.len() as usize),
    ensures list_indices(before.push(form), next),
{
    let after = before.push(form);
    assert forall|i: int| 0 <= i < after.len() implies match #[trigger] after[i] {
        Form::List { end, .. } => if end == 0 {
            next.contains(i as usize)
        } else {
            i < end <= after.len()
        },
        Form::Atom { .. } => true,
    } by {
        if i < before.len() {
            assert(after[i] == before[i]);
        }
    };
}

proof fn indices_after_finish(before: Seq<Form>, after: Seq<Form>, open: Seq<usize>,
    shortened: Seq<usize>, last: usize)
    requires
        list_indices(before, open),
        shortened == open[..open.len() - 1],
        open.len() > 0,
        last == open[open.len() - 1],
        last < before.len(),
        after.len() == before.len(),
        after[last as int] is List,
        after[last as int]->List_end == after.len(),
        forall|i: int| 0 <= i < before.len() && i != last ==> #[trigger] after[i] == before[i],
    ensures list_indices(after, shortened),
{
    assert forall|i: int| 0 <= i < after.len() implies match #[trigger] after[i] {
        Form::List { end, .. } => if end == 0 {
            shortened.contains(i as usize)
        } else {
            i < end <= after.len()
        },
        Form::Atom { .. } => true,
    } by {
        if i != last {
            assert(after[i] == before[i]);
            if before[i] is List && before[i]->List_end == 0 {
                assert(open.contains(i as usize));
                let at = choose|at: int| 0 <= at < open.len() && open[at] == i as usize;
                assert(at < shortened.len());
                assert(shortened[at] == i as usize);
            }
        }
    };
}

#[verifier::opaque]
pub open spec fn inserted_closes_match(source: &str, forms: Seq<Form>, repairs: Seq<Repair>) -> bool {
    forall|i: int| 0 <= i < repairs.len() ==> match #[trigger] repairs[i] {
        Repair::InsertedClose { offset, opening, list } => {
            &&& list < forms.len()
            &&& forms[list as int] is List
            &&& forms[list as int]->List_end > 0
            &&& offset == source.spec_bytes().len()
            &&& form_span(forms[list as int]).end == offset
            &&& form_span(forms[list as int]).start == opening.start
            &&& opening.end == opening.start + 1
        },
        _ => true,
    }
}

spec fn no_inserted_closes(repairs: Seq<Repair>) -> bool {
    forall|i: int| 0 <= i < repairs.len() ==> !(#[trigger] repairs[i] is InsertedClose)
}

proof fn no_closes_implies_evidence(source: &str, forms: Seq<Form>, repairs: Seq<Repair>)
    requires no_inserted_closes(repairs),
    ensures inserted_closes_match(source, forms, repairs),
{
    reveal(inserted_closes_match);
}

proof fn record_inserted_close(source: &str, forms: Seq<Form>, updated: Seq<Form>,
    repairs: Seq<Repair>, index: usize, opening: Range<usize>, offset: usize)
    requires
        inserted_closes_match(source, forms, repairs),
        updated.len() == forms.len(),
        index < forms.len(),
        forms[index as int] is List,
        forms[index as int]->List_end == 0,
        updated[index as int] is List,
        updated[index as int]->List_end > 0,
        offset == source.spec_bytes().len(),
        form_span(updated[index as int]).start == opening.start,
        form_span(updated[index as int]).end == offset,
        opening.end == opening.start + 1,
        forall|i: int| 0 <= i < forms.len() && i != index ==> #[trigger] updated[i] == forms[i],
    ensures
        inserted_closes_match(source, updated, repairs.push(Repair::InsertedClose {
            offset, opening, list: index,
        })),
{
    reveal(inserted_closes_match);
    let all = repairs.push(Repair::InsertedClose { offset, opening, list: index });
    assert forall|i: int| 0 <= i < all.len() implies match #[trigger] all[i] {
        Repair::InsertedClose { offset, opening, list } => {
            &&& list < updated.len()
            &&& updated[list as int] is List
            &&& updated[list as int]->List_end > 0
            &&& offset == source.spec_bytes().len()
            &&& form_span(updated[list as int]).end == offset
            &&& form_span(updated[list as int]).start == opening.start
            &&& opening.end == opening.start + 1
        },
        _ => true,
    } by {
        if i < repairs.len() {
            assert(all[i] == repairs[i]);
            if all[i] is InsertedClose {
                let target = all[i]->InsertedClose_list;
                assert(target != index);
                assert(updated[target as int] == forms[target as int]);
            }
        }
    };
}

#[verifier::opaque]
pub open spec fn atom_and_close_error_evidence(source: &str, error: Error) -> bool {
    let bytes = source.spec_bytes();
    match error.kind {
        ErrorKind::InvalidAtom => {
            &&& bare_atom_extent(bytes, error.span.start as int, error.span.end as int)
            &&& bare_atom_kind(bytes[error.span.start as int..error.span.end as int]).is_none()
        },
        ErrorKind::UnexpectedClose => {
            &&& error.span.end == error.span.start + 1
            &&& error.span.end <= bytes.len()
            &&& bytes[error.span.start as int] == 41
        },
        _ => true,
    }
}

pub open spec fn string_error_opening(kind: ErrorKind, span: Range<usize>) -> Option<usize> {
    match kind {
        ErrorKind::InvalidEscape { opening } | ErrorKind::NewlineInString { opening } => Some(opening),
        ErrorKind::UnterminatedString => Some(span.start),
        _ => None,
    }
}

pub open spec fn structural_error_location(source: &str, error: Error) -> bool {
    let bytes = source.spec_bytes();
    match error.kind {
        ErrorKind::MissingSeparator => {
            &&& error.span.start == error.span.end
            &&& error.span.start < bytes.len()
            &&& is_char_boundary(bytes, error.span.start as int)
        },
        ErrorKind::UnclosedList { eof } => {
            &&& eof == bytes.len()
            &&& error.span.end == error.span.start + 1 <= eof
            &&& bytes[error.span.start as int] == 40
        },
        _ => true,
    }
}

#[verifier::opaque]
pub open spec fn syntax_error_evidence(source: &str, error: Error) -> bool {
    &&& atom_and_close_error_evidence(source, error)
    &&& structural_error_location(source, error)
    &&& match string_error_opening(error.kind, error.span) {
        Some(opening) => opening < source.spec_bytes().len()
            && string_error_site(source.spec_bytes()[opening as int..], opening as int, error),
        None => true,
    }
}

proof fn parser_error_evidence(source: &str, error: Error)
    requires
        structural_error_location(source, error),
        error.kind is MissingSeparator || error.kind is UnclosedList || (
            error.kind is UnexpectedClose
            && error.span.end == error.span.start + 1
            && error.span.end <= source.spec_bytes().len()
            && source.spec_bytes()[error.span.start as int] == 41
        ),
    ensures syntax_error_evidence(source, error),
{
    reveal(syntax_error_evidence);
    reveal(atom_and_close_error_evidence);
}

pub open spec fn repair_input_span(repair: Repair) -> Option<(int, int)> {
    match repair {
        Repair::Skipped { span, .. } => Some((span.start as int, span.end as int)),
        Repair::InsertedSeparator { offset } => Some((offset as int, offset as int)),
        Repair::InsertedClose { .. } => None,
    }
}

#[verifier::opaque]
pub open spec fn repair_input_spans_valid(source: &str, repairs: Seq<Repair>, consumed: int) -> bool {
    &&& 0 <= consumed <= source.spec_bytes().len()
    &&& forall|i: int| 0 <= i < repairs.len() ==> match repair_input_span(#[trigger] repairs[i]) {
        Some((start, end)) => {
            &&& 0 <= start <= end <= consumed
            &&& (repairs[i] is Skipped ==> start < end
                && syntax_error_evidence(source, repairs[i]->Skipped_error))
            &&& is_char_boundary(source.spec_bytes(), start)
            &&& is_char_boundary(source.spec_bytes(), end)
        },
        None => true,
    }
    &&& forall|i: int, j: int| 0 <= i < j < repairs.len()
        ==> match (repair_input_span(#[trigger] repairs[i]), repair_input_span(#[trigger] repairs[j])) {
            (Some((_, end)), Some((start, _))) => end <= start,
            _ => true,
        }
}

proof fn repair_spans_advance(source: &str, repairs: Seq<Repair>, before: int, after: int)
    requires
        repair_input_spans_valid(source, repairs, before),
        before <= after <= source.spec_bytes().len(),
    ensures repair_input_spans_valid(source, repairs, after),
{
    reveal(repair_input_spans_valid);
}

proof fn repair_spans_append(source: &str, repairs: Seq<Repair>, repair: Repair,
    before: int, after: int)
    requires
        repair_input_spans_valid(source, repairs, before),
        before <= after <= source.spec_bytes().len(),
        match repair_input_span(repair) {
            Some((start, end)) => {
                &&& before <= start <= end <= after
                &&& (repair is Skipped ==> start < end
                    && syntax_error_evidence(source, repair->Skipped_error))
                &&& is_char_boundary(source.spec_bytes(), start)
                &&& is_char_boundary(source.spec_bytes(), end)
            },
            None => true,
        },
    ensures repair_input_spans_valid(source, repairs.push(repair), after),
{
    reveal(repair_input_spans_valid);
    let extended = repairs.push(repair);
    assert forall|i: int| 0 <= i < extended.len() implies match repair_input_span(#[trigger] extended[i]) {
        Some((start, end)) => {
            &&& 0 <= start <= end <= after
            &&& (extended[i] is Skipped ==> start < end
                && syntax_error_evidence(source, extended[i]->Skipped_error))
            &&& is_char_boundary(source.spec_bytes(), start)
            &&& is_char_boundary(source.spec_bytes(), end)
        },
        None => true,
    } by {
        if i < repairs.len() {
            assert(extended[i] == repairs[i]);
        }
    };
    assert forall|i: int, j: int| 0 <= i < j < extended.len()
        implies match (repair_input_span(#[trigger] extended[i]), repair_input_span(#[trigger] extended[j])) {
            (Some((_, end)), Some((start, _))) => end <= start,
            _ => true,
        } by {
        assert(extended[i] == repairs[i]);
        if j < repairs.len() {
            assert(extended[j] == repairs[j]);
        }
    };
}

#[verifier::opaque]
spec fn strict_prefix_evidence(
    source: &str, forms: Seq<Form>, spans: Seq<(int, int)>, pos: int, needs_separator: bool,
) -> bool {
    &&& pieces_represented(source, forms, spans)
    &&& all_form_pieces_present(forms, spans)
    &&& strict_preorder_ranges(forms)
    &&& (!needs_separator ==> atoms_end_before(forms, pos))
}

proof fn strict_prefix_add_trivia(
    source: &str, forms: Seq<Form>, spans: Seq<(int, int)>, piece: (int, int), needs_separator: bool,
)
    requires
        strict_prefix_evidence(source, forms, spans, piece.0, needs_separator),
        form_spans_valid(source, forms, piece.0),
        piece.0 < piece.1,
        trivia_extent(source.spec_bytes(), piece.0, piece.1, false)
            || trivia_extent(source.spec_bytes(), piece.0, piece.1, true),
    ensures strict_prefix_evidence(source, forms, spans.push(piece), piece.1, false),
{
    reveal(strict_prefix_evidence);
    assert(parsed_piece(source, forms, piece));
    append_represented_piece(source, forms, spans, piece);
    form_pieces_preserved(forms, forms, spans, piece);
    atoms_stay_behind_cursor(source, forms, forms, piece.0, piece.1);
}

proof fn strict_prefix_add_form(
    source: &str, before: Seq<Form>, added: Form, spans: Seq<(int, int)>,
    piece: (int, int), needed_separator: bool,
)
    requires
        strict_prefix_evidence(source, before, spans, piece.0, needed_separator),
        form_spans_valid(source, before, piece.0),
        complete_or_pending_ends_in_bounds(before),
        first_form_piece(added) == piece && piece.0 < piece.1,
        added is List ==> added->List_end == 0,
        added is Atom ==> !needed_separator,
    ensures strict_prefix_evidence(source, before.push(added), spans.push(piece), piece.1, added is Atom),
{
    reveal(strict_prefix_evidence);
    let after = before.push(added);
    appended_form_preserves_pieces(source, before, added, spans);
    add_form_pieces(before, added, spans, piece);
    append_preserves_preorder_ranges(source, before, added, piece.0);
    if added is List {
        atoms_stay_behind_cursor(source, before, after, piece.0, piece.1);
    }
    assert(parsed_piece(source, after, piece)) by {
        assert(form_represents_piece(after[before.len() as int], piece));
    };
    append_represented_piece(source, after, spans, piece);
}

proof fn strict_prefix_close_list(
    source: &str, before: Seq<Form>, after: Seq<Form>, spans: Seq<(int, int)>,
    closed: int, piece: (int, int), needed_separator: bool,
)
    requires
        strict_prefix_evidence(source, before, spans, piece.0, needed_separator),
        form_spans_valid(source, before, piece.0),
        nested_list_indices(before),
        0 <= closed < before.len() == after.len(),
        before[closed] is List && before[closed]->List_end == 0,
        after[closed] is List && after[closed]->List_end == after.len(),
        form_span(before[closed]).end == form_span(before[closed]).start + 1,
        form_span(after[closed]).start == form_span(before[closed]).start,
        piece == list_close_piece(after[closed]),
        forall|i: int| 0 <= i < before.len() && i != closed
            ==> #[trigger] after[i] == before[i],
    ensures strict_prefix_evidence(source, after, spans.push(piece), piece.1, false),
{
    reveal(strict_prefix_evidence);
    assert(form_span(before[closed]).end <= piece.0) by {
        reveal(form_spans_valid);
    };
    closed_form_preserves_pieces(source, before, after, closed, spans);
    close_form_pieces(before, after, closed, spans, piece);
    close_preserves_preorder_ranges(source, before, after, closed, piece.0);
    atoms_stay_behind_cursor(source, before, after, piece.0, piece.1);
    assert(parsed_piece(source, after, piece)) by {
        assert(form_represents_piece(after[closed], piece));
    };
    append_represented_piece(source, after, spans, piece);
}

#[cfg(verus_only)]
spec fn segment_parenthesis_delta(kind: SegmentKind) -> int {
    match kind {
        SegmentKind::Open => 1,
        SegmentKind::Close => -1,
        _ => 0,
    }
}

#[cfg(verus_only)]
proof fn follow_input_derivation(
    bytes: Seq<u8>, witness: InputDerivation, i: int, position: int,
    needs_separator: bool, depth: int, segment: Segment, next_needs_separator: bool,
) -> (lexeme: Lexeme)
    requires
        lexical::input_progress(bytes, witness, i, position, needs_separator, depth),
        position == segment.span.start < segment.span.end <= bytes.len(),
        lexical_step_agrees(bytes, position, segment.span.end as int, segment_lexeme(segment.kind)),
        segment.missing_separator == (needs_separator && segment.kind.is_atom()),
        next_needs_separator == segment.kind.is_atom(),
    ensures
        0 <= i < witness.lexemes.len(),
        lexeme == witness.lexemes[i],
        lexeme.start == segment.span.start && lexeme.end == segment.span.end,
        segment_lexeme(segment.kind) == Some(lexeme.kind),
        !(segment.kind is Malformed),
        !segment.missing_separator,
        segment.kind is Close ==> depth > 0,
        lexical::input_progress(bytes, witness, i + 1, segment.span.end as int, next_needs_separator,
            depth + segment_parenthesis_delta(segment.kind)),
{
    let lexeme = lexical::input_next(bytes, witness, i, position, needs_separator, depth);
    reveal(lexical_step_agrees);
    assert(segment_lexeme(segment.kind) == Some(lexeme.kind));
    assert(segment.kind.is_atom() == (lexeme.kind is Atom));
    assert(segment_parenthesis_delta(segment.kind) == lexical::parenthesis_delta(lexeme.kind));
    lexeme
}

#[cfg(verus_only)]
proof fn record_input_segment(
    bytes: Seq<u8>, prefix: InputDerivation, segment: Segment,
    needed_separator: bool, old_depth: int, next_needs_separator: bool, new_depth: int,
) -> (next: InputDerivation)
    requires
        lexical::scanned_input_prefix(bytes, prefix, segment.span.start as int, needed_separator, old_depth),
        lexical_step_agrees(bytes, segment.span.start as int, segment.span.end as int, segment_lexeme(segment.kind)),
        !(segment.kind is Malformed),
        !segment.missing_separator,
        segment.missing_separator == (needed_separator && segment.kind.is_atom()),
        next_needs_separator == segment.kind.is_atom(),
        new_depth == old_depth + segment_parenthesis_delta(segment.kind),
        new_depth >= 0,
    ensures
        lexical::scanned_input_prefix(bytes, next, segment.span.end as int, next_needs_separator, new_depth),
        next.lexemes == prefix.lexemes.push(Lexeme {
            start: segment.span.start as int, end: segment.span.end as int, kind: segment_lexeme(segment.kind)->Some_0,
        }),
{
    reveal(lexical_step_agrees);
    let observed = segment_lexeme(segment.kind);
    assert(observed is Some);
    let kind = observed->Some_0;
    assert(segment.kind.is_atom() == (kind is Atom));
    assert(segment_parenthesis_delta(segment.kind) == lexical::parenthesis_delta(kind));
    lexical::record_scanned_input(bytes, prefix,
        Lexeme { start: segment.span.start as int, end: segment.span.end as int, kind },
        needed_separator, old_depth)
}

proof fn initialize_parse_invariants(
    source: &str, forms: Seq<Form>, spans: Seq<(int, int)>, repairs: Seq<Repair>, recovering: bool,
)
    requires forms.len() == 0, spans.len() == 0, repairs.len() == 0,
    ensures
        valid_utf8(source.spec_bytes()),
        form_spans_valid(source, forms, 0),
        strict_prefix_evidence(source, forms, spans, 0, false),
        nested_list_indices(forms),
        repair_input_spans_valid(source, repairs, 0),
        list_source_delimiters(source, forms, recovering),
{
    encode_utf8_valid_utf8(source@);
    reveal(form_spans_valid);
    assert(form_spans_valid(source, forms, 0));
    reveal(pieces_represented);
    assert(pieces_represented(source, forms, spans));
    reveal(all_form_pieces_present);
    assert(all_form_pieces_present(forms, spans));
    reveal(strict_preorder_ranges);
    assert(strict_preorder_ranges(forms));
    reveal(atoms_end_before);
    assert(atoms_end_before(forms, 0));
    reveal(strict_prefix_evidence);
    assert(strict_prefix_evidence(source, forms, spans, 0, false));
    reveal(nested_list_indices);
    assert(nested_list_indices(forms));
    reveal(repair_input_spans_valid);
    assert(repair_input_spans_valid(source, repairs, 0));
    reveal(list_source_delimiters);
    assert(list_source_delimiters(source, forms, recovering));
}

spec fn completed_original_list(source: &str, span: Range<usize>, consumed: int) -> bool {
    let bytes = source.spec_bytes();
    &&& span.start + 1 < span.end <= consumed <= bytes.len()
    &&& bytes[span.start as int] == b'(' && bytes[span.end - 1] == b')'
    &&& is_char_boundary(bytes, span.start as int) && is_char_boundary(bytes, span.end as int)
}

spec fn repair_precedes(repair: Repair, start: int) -> bool {
    match repair_input_span(repair) { Some((_, end)) => end <= start, None => true }
}

/// 確定したリストの範囲が元入力の括弧を含み、互いに重ならないことを表す。
///
/// 各範囲の内部には、読み飛ばした元入力の範囲や補った区切りの位置がない。
pub closed spec fn original_list_ranges(
    source: &str, lists: Seq<Range<usize>>, repairs: Seq<Repair>, consumed: int,
) -> bool {
    &&& forall|i: int| 0 <= i < lists.len() ==> completed_original_list(source, #[trigger] lists[i], consumed)
    &&& forall|i: int, j: int| 0 <= i < j < lists.len() ==> (#[trigger] lists[i]).end <= (#[trigger] lists[j]).start
    &&& forall|i: int, j: int| 0 <= i < lists.len() && 0 <= j < repairs.len() ==> {
        let list = #[trigger] lists[i];
        match repair_input_span(#[trigger] repairs[j]) {
            Some((start, end)) => end <= list.start || list.end <= start,
            None => true,
        }
    }
}

proof fn advance_original_lists(
    source: &str, lists: Seq<Range<usize>>, repairs: Seq<Repair>, after: Seq<Repair>, before: int, consumed: int,
)
    requires
        original_list_ranges(source, lists, repairs, before),
        before <= consumed <= source.spec_bytes().len(),
        repairs.is_prefix_of(after),
        forall|i: int| repairs.len() <= i < after.len() ==>
            match repair_input_span(#[trigger] after[i]) { Some((start, _)) => before <= start, None => true },
    ensures original_list_ranges(source, lists, after, consumed),
{
    reveal(original_list_ranges);
    assert forall|i: int, j: int| 0 <= i < lists.len() && 0 <= j < after.len() implies {
        let list = #[trigger] lists[i];
        match repair_input_span(#[trigger] after[j]) {
            Some((start, end)) => end <= list.start || list.end <= start,
            None => true,
        }
    } by {
        if j < repairs.len() {
            assert(after[j] == repairs[j]);
        } else {
            assert(lists[i].end <= before);
        }
    };
}

proof fn append_original_list(
    source: &str, lists: Seq<Range<usize>>, repairs: Seq<Repair>, span: Range<usize>, consumed: int,
)
    requires
        original_list_ranges(source, lists, repairs, consumed),
        completed_original_list(source, span, consumed),
        forall|i: int| 0 <= i < lists.len() ==> (#[trigger] lists[i]).end <= span.start,
        forall|i: int| 0 <= i < repairs.len() ==> repair_precedes(#[trigger] repairs[i], span.start as int),
    ensures original_list_ranges(source, lists.push(span), repairs, consumed),
{
    reveal(original_list_ranges);
    let updated = lists.push(span);
    assert forall|i: int, j: int| 0 <= i < updated.len() && 0 <= j < repairs.len() implies {
        let list = #[trigger] updated[i];
        match repair_input_span(#[trigger] repairs[j]) {
            Some((start, end)) => end <= list.start || list.end <= start,
            None => true,
        }
    } by {
        if i < lists.len() { assert(updated[i] == lists[i]); }
    };
}

#[verifier::rlimit(55)]
fn parse_forms(source: &str, recovering: bool) -> (result: Result<(Vec<Form>, Vec<Repair>, Vec<Range<usize>>), Error>)
    ensures
        recovering || well_formed_sexpr(source) ==> result.is_ok(),
        !recovering && result.is_ok() ==> well_formed_sexpr(source),
        match result {
            Ok((forms, repairs, original_lists)) => inserted_closes_match(source, forms@, repairs@)
                && repair_input_spans_valid(source, repairs@, source.spec_bytes().len() as int)
                && complete_list_indices(forms@) && nested_list_indices(forms@)
                && list_source_delimiters(source, forms@, recovering)
                && form_spans_valid(source, forms@, source.spec_bytes().len() as int)
                && original_list_ranges(source, original_lists@, repairs@, source.spec_bytes().len() as int)
                && (!recovering ==> strict_source_covered(source, forms@))
                && (well_formed_sexpr(source) ==> repairs@.len() == 0
                    && sexpr_form_model(source) == Some(forms@)),
            Err(error) => syntax_error_evidence(source, error) && strict_syntax_rejection(source, error),
        },
{
    let mut forms: Vec<Form> = Vec::new();
    let mut open: Vec<usize> = Vec::new();
    let mut repairs: Vec<Repair> = Vec::new();
    let mut original_lists: Vec<Range<usize>> = Vec::new();
    let mut root: Option<(usize, usize)> = None;
    let mut lexer = Lexer::new(source);
    let length = source.as_bytes().len();
    let ghost mut spans: Seq<(int, int)> = Seq::empty();
    let ghost derivation;
    let ghost mut input_prefix;
    proof {
        input_prefix = lexical::empty_scanned_input(source.spec_bytes());
        form_model::model_starts(input_prefix.lexemes, forms@, open@);
        derivation = lexical::choose_input_derivation(source);
        if derivation is Some {
            lexical::input_starts(source.spec_bytes(), derivation->Some_0);
            form_model::model_starts(derivation->Some_0.lexemes, forms@, open@);
        }

        initialize_parse_invariants(source, forms@, spans, repairs@, recovering);
        reveal(original_list_ranges);
    }

    loop
        invariant
            derivation.is_some() == well_formed_sexpr(source),
            derivation == lexical::chosen_input_derivation(source),
            derivation is Some ==> repairs@.len() == 0 && form_model::model_matches(
                derivation->Some_0.lexemes, spans.len() as int, forms@, open@),
            derivation is Some ==> lexical::input_progress(source.spec_bytes(),
                derivation->Some_0, spans.len() as int, lexer.cursor.position(),
                lexer.needs_separator, open@.len() as int),
            lexer.cursor.source == source,
            lexer.cursor.valid(),
            length == source.spec_bytes().len(),
            valid_utf8(source.spec_bytes()),
            covers(source.spec_bytes(), spans, lexer.cursor.position()),
            !recovering ==> strict_prefix_evidence(source, forms@, spans,
                lexer.cursor.position(), lexer.needs_separator),
            !recovering ==> lexical::scanned_input_prefix(source.spec_bytes(), input_prefix,
                lexer.cursor.position(), lexer.needs_separator, open@.len() as int),
            !recovering ==> form_model::model_matches(input_prefix.lexemes, input_prefix.lexemes.len() as int, forms@, open@),
            no_inserted_closes(repairs@),
            repair_input_spans_valid(source, repairs@, lexer.cursor.position()),
            form_spans_valid(source, forms@, lexer.cursor.position()),
            pending_lists(forms@, open@),
            list_indices(forms@, open@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, recovering),
            open_order(open@),
            original_list_ranges(source, original_lists@, repairs@, lexer.cursor.position()),
            root matches Some((start, checkpoint)) ==> {
                &&& start < lexer.cursor.position()
                &&& source.spec_bytes()[start as int] == b'('
                &&& is_char_boundary(source.spec_bytes(), start as int)
                &&& checkpoint <= repairs@.len()
                &&& forall|i: int| 0 <= i < checkpoint ==> repair_precedes(#[trigger] repairs@[i], start as int)
                &&& forall|i: int| 0 <= i < original_lists@.len() ==> (#[trigger] original_lists@[i]).end <= start
            },
        ensures
            valid_utf8(source.spec_bytes()),
            form_spans_valid(source, forms@, length as int),
            repair_input_spans_valid(source, repairs@, length as int),
            !recovering ==> strict_source_covered(source, forms@),
            !recovering ==> lexical::scanned_input_prefix(source.spec_bytes(), input_prefix,
                length as int, lexer.needs_separator, open@.len() as int),
            !recovering ==> form_model::model_matches(input_prefix.lexemes, input_prefix.lexemes.len() as int, forms@, open@),
            well_formed_sexpr(source) ==> open@.len() == 0 && repairs@.len() == 0
                && sexpr_form_model(source) == Some(forms@),
            !recovering && open@.len() == 0 ==> well_formed_sexpr(source),
            original_list_ranges(source, original_lists@, repairs@, length as int),
        decreases length - lexer.cursor.position(),
    {
        let Some((segment, next)) = lexer.next_segment() else {
            proof {
                if derivation is Some {
                    lexical::input_ends(source.spec_bytes(), derivation->Some_0,
                        spans.len() as int, lexer.needs_separator, open@.len() as int);
                    form_model::model_finishes(source, derivation->Some_0, forms@, open@);
                }
                if !recovering {
                    if open@.len() == 0 {
                        lexical::seal_scanned_input(source, input_prefix, lexer.needs_separator);
                    }
                    reveal(strict_prefix_evidence);
                    preorder_ranges_have_distinct_closes(source, forms@, length as int);
                    source_coverage_from_pieces(source, forms@, spans);
                }
            }
            break;
        };
        let ghost expected;
        proof {
            expected = if derivation is Some {
                Some(follow_input_derivation(source.spec_bytes(), derivation->Some_0, spans.len() as int,
                    lexer.cursor.position(), lexer.needs_separator, open@.len() as int,
                    segment, next.needs_separator))
            } else if !recovering {
                match segment_lexeme(segment.kind) {
                    Some(kind) => Some(Lexeme { start: segment.span.start as int, end: segment.span.end as int, kind }),
                    None => None,
                }
            } else {
                None
            };
        }
        let ghost old_open = open@;
        let ghost previous_open = old_open.len();
        let ghost scanned_segment = segment;
        let ghost previous_position = lexer.cursor.position();
        let ghost repairs_before = repairs@;
        let ghost old_forms = forms@;
        let ghost previous_needs_separator = lexer.needs_separator;
        let kind = segment.kind;
        let span = segment.span;
        let missing_separator = segment.missing_separator;
        let ghost old_spans = spans;
        let ghost piece = (span.start as int, span.end as int);
        proof {
            spans = spans.push(piece);
            assert forall|i: int| 0 <= i < spans.len() implies {
                let part = #[trigger] spans[i];
                &&& 0 <= part.0 < part.1 <= span.end
                &&& is_char_boundary(source.spec_bytes(), part.0)
                &&& is_char_boundary(source.spec_bytes(), part.1)
                &&& part.0 == if i == 0 { 0 } else { spans[i - 1].1 }
            } by {
                if i < old_spans.len() {
                    assert(spans[i] == old_spans[i]);
                }
            };
        }
        lexer = next;
        proof { advance_form_spans(source, forms@, previous_position, lexer.cursor.position()); }
        assert(covers(source.spec_bytes(), spans, lexer.cursor.position()));
        if missing_separator {
            if recovering {
                let repair = Repair::InsertedSeparator { offset: span.start };
                proof { repair_spans_append(source, repairs@, repair, previous_position, previous_position); }
                repairs.push(repair);
            } else {
                let error = Error { kind: ErrorKind::MissingSeparator, span: span.start..span.start };
                proof {
                    parser_error_evidence(source, error);
                    reveal(lexical_step_agrees);
                    assert forall|end: int, candidate: LexemeKind|
                        #[trigger] lexeme_at(source.spec_bytes(), previous_position, end, candidate)
                        implies candidate is Atom by {
                        assert(segment_lexeme(kind) == Some(candidate));
                    };
                    strict_error::record_missing_separator(source, error, input_prefix, previous_open as int);
                }
                return Err(error);
            }
        }
        let ghost repairs_before_segment = repairs@;
        let ghost previous_lists = original_lists@;
        proof {
            advance_original_lists(source, previous_lists, repairs_before, repairs@,
                previous_position, previous_position);
            advance_original_lists(source, previous_lists, repairs@, repairs@,
                previous_position, lexer.cursor.position());
        }
        match kind {
            SegmentKind::Whitespace | SegmentKind::Comment => {
                proof {
                    if expected is Some {
                        assert(form_model::apply_lexeme(old_forms, old_open, expected->Some_0)
                            == (forms@, open@)) by { reveal(form_model::apply_lexeme); };
                    }
                    if !recovering {
                        strict_prefix_add_trivia(source, forms@, old_spans, piece, previous_needs_separator);
                    }
                }
            }
            SegmentKind::Malformed(error) => {
                if recovering {
                    let repair = Repair::Skipped { span, error };
                    proof { repair_spans_append(source, repairs@, repair, previous_position, lexer.cursor.position()); }
                    repairs.push(repair);
                    proof {
                        advance_original_lists(source, original_lists@, repairs_before_segment, repairs@,
                            previous_position, lexer.cursor.position());
                    }
                } else {
                    proof {
                        reveal(lexical_step_agrees);
                        strict_error::record_malformed_atom(source, error, input_prefix, previous_position, previous_open as int);
                    }
                    return Err(error);
                }
            }
            SegmentKind::Open => {
                if recovering && open.len() == 0 {
                    proof {
                        reveal(original_list_ranges);
                        reveal(repair_input_spans_valid);
                        assert(span.start == previous_position);
                        assert forall|i: int| 0 <= i < original_lists@.len()
                            implies (#[trigger] original_lists@[i]).end <= span.start by {
                            assert(completed_original_list(source, original_lists@[i], previous_position));
                        };
                        assert forall|i: int| 0 <= i < repairs@.len()
                            implies repair_precedes(#[trigger] repairs@[i], span.start as int) by {};
                    }
                    root = Some((span.start, repairs.len()));
                }
                let ghost before = forms@;
                let ghost previous = open@;
                let index = forms.len();
                let form = Form::List { span, end: 0 };
                let ghost added = form;
                forms.push(form);
                assert(forms.len() == before.len() + 1);
                open.push(index);
                assert(open@[open@.len() - 1] == index);
                assert(exists|j: int| 0 <= j < open@.len() && open@[j] == index);
                assert(open@.contains(index));
                proof {
                    assert forall|value: usize| #[trigger] previous.contains(value)
                        implies open@.contains(value) by {
                        let j = choose|j: int| 0 <= j < previous.len() && previous[j] == value;
                        assert(open@[j] == value);
                    };
                    delimiters_after_append(source, before, added, recovering);
                    nested_after_append(before, added);
                    indices_after_append(before, previous, added, open@);
                    append_form_span(source, old_forms, added, previous_position, lexer.cursor.position());
                    if expected is Some {
                        assert(form_model::apply_lexeme(old_forms, old_open, expected->Some_0)
                            == (forms@, open@)) by { reveal(form_model::apply_lexeme); };
                    }
                    if !recovering {
                        assert(complete_or_pending_ends_in_bounds(before));
                        strict_prefix_add_form(source, before, added, old_spans, piece, previous_needs_separator);
                    }
                }
            }
            SegmentKind::Close => {
                let ghost previous = open@;
                if let Some(index) = open.pop() {
                    let ghost before = forms@;
                    finish_list(&mut forms, index, span.end);
                    if recovering && open.len() == 0 {
                        if let Some((start, checkpoint)) = root {
                            if repairs.len() == checkpoint {
                                let confirmed = start..span.end;
                                proof {
                                    append_original_list(source, original_lists@, repairs@, confirmed,
                                        lexer.cursor.position());
                                }
                                original_lists.push(confirmed);
                            }
                        }
                        root = None;
                    }
                    proof {
                        delimiters_after_close(source, before, forms@, index as int, recovering);
                        nested_after_close(before, forms@, previous, index);
                        indices_after_finish(before, forms@, previous, open@, index);
                        close_form_span(source, before, forms@, index as int, previous_position, lexer.cursor.position());
                        if expected is Some {
                            assert(index == old_open.last());
                            assert(forms@ =~= before.update(index as int, forms@[index as int]));
                            assert(form_model::apply_lexeme(old_forms, old_open, expected->Some_0)
                                == (forms@, open@)) by { reveal(form_model::apply_lexeme); };
                        }
                        if !recovering {
                            strict_prefix_close_list(source, before, forms@, old_spans,
                                index as int, piece, previous_needs_separator);
                        }
                    }
                } else {
                    let error = Error {
                        kind: ErrorKind::UnexpectedClose,
                        span: span.start..span.end,
                    };
                    proof { parser_error_evidence(source, error); }
                    if recovering {
                        let repair = Repair::Skipped { span, error };
                        proof {
                            repair_spans_append(source, repairs@, repair, previous_position, lexer.cursor.position());
                        }
                        repairs.push(repair);
                        proof {
                            advance_original_lists(source, original_lists@, repairs_before_segment, repairs@,
                                previous_position, lexer.cursor.position());
                        }
                    } else {
                        proof { strict_error::record_unexpected_close(source, error, input_prefix, previous_needs_separator); }
                        return Err(error);
                    }
                }
            }
            SegmentKind::Atom(kind) => {
                let ghost before = forms@;
                let form = Form::Atom { kind, span };
                let ghost added = form;
                forms.push(form);
                assert(forms.len() == before.len() + 1);
                proof {
                    delimiters_after_append(source, before, added, recovering);
                    nested_after_append(before, added);
                    indices_after_append(before, open@, added, open@);
                    append_form_span(source, old_forms, added, previous_position, lexer.cursor.position());
                    if expected is Some {
                        assert(form_model::apply_lexeme(old_forms, old_open, expected->Some_0)
                            == (forms@, open@)) by { reveal(form_model::apply_lexeme); };
                    }
                    if !recovering {
                        assert(complete_or_pending_ends_in_bounds(before));
                        strict_prefix_add_form(source, before, added, old_spans, piece, previous_needs_separator);
                    }
                }
            }
        }
        proof {
            if derivation is Some {
                assert(expected is Some);
                form_model::model_advances(derivation->Some_0.lexemes, old_spans.len() as int,
                    old_forms, old_open, forms@, open@);
            }
            if derivation is Some || !recovering {
                assert(open@.len() == previous_open + segment_parenthesis_delta(scanned_segment.kind));
            }
            if !recovering {
                assert(expected is Some);
                form_model::model_appends(input_prefix.lexemes, expected->Some_0, old_forms, old_open, forms@, open@);
                input_prefix = record_input_segment(source.spec_bytes(), input_prefix, scanned_segment,
                    previous_needs_separator, previous_open as int, lexer.needs_separator, open@.len() as int);
            }
            if repairs@ == repairs_before_segment {
                repair_spans_advance(source, repairs@, previous_position, lexer.cursor.position());
            }
        }
    }

    proof { is_char_boundary_start_end_of_seq(source.spec_bytes()); }
    proof { no_closes_implies_evidence(source, forms@, repairs@); }
    while open.len() > 0
        invariant
            !recovering ==> strict_source_covered(source, forms@),
            !recovering ==> lexical::scanned_input_prefix(source.spec_bytes(), input_prefix,
                length as int, lexer.needs_separator, open@.len() as int),
            !recovering ==> form_model::model_matches(input_prefix.lexemes, input_prefix.lexemes.len() as int, forms@, open@),
            well_formed_sexpr(source) ==> open@.len() == 0 && repairs@.len() == 0
                && sexpr_form_model(source) == Some(forms@),
            !recovering && open@.len() == 0 ==> well_formed_sexpr(source),
            length == source.spec_bytes().len(),
            valid_utf8(source.spec_bytes()),
            is_char_boundary(source.spec_bytes(), length as int),
            form_spans_valid(source, forms@, length as int),
            inserted_closes_match(source, forms@, repairs@),
            repair_input_spans_valid(source, repairs@, length as int),
            pending_lists(forms@, open@),
            list_indices(forms@, open@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, recovering),
            open_order(open@),
            original_list_ranges(source, original_lists@, repairs@, length as int),
        decreases open@.len(),
    {
        let ghost previous = open@;
        let Some(index) = open.pop() else {
            unreachable!("nonempty list stack");
        };
        let span = match &forms[index] {
            Form::List { span, .. } => span,
            Form::Atom { .. } => unreachable!("only list indices are stacked"),
        };
        if recovering {
            assert(length > 0) by {
                reveal(list_source_delimiters);
                assert(list_delimited(source.spec_bytes(), forms@[index as int], recovering));
            };
            let opening = span.start..span.end;
            let ghost opening_evidence = opening;
            let ghost previous_repairs = repairs@;
            let repair = Repair::InsertedClose { offset: length, opening, list: index };
            proof { repair_spans_append(source, repairs@, repair, length as int, length as int); }
            repairs.push(repair);
            proof { advance_original_lists(source, original_lists@, previous_repairs, repairs@, length as int, length as int); }
            let ghost before = forms@;
            finish_list(&mut forms, index, length);
            proof {
                record_inserted_close(source, before, forms@, previous_repairs, index, opening_evidence, length);
                delimiters_after_close(source, before, forms@, index as int, recovering);
                nested_after_close(before, forms@, previous, index);
                indices_after_finish(before, forms@, previous, open@, index);
                close_form_span(source, before, forms@, index as int, length as int, length as int);
            }
        } else {
            let error = Error { kind: ErrorKind::UnclosedList { eof: length }, span: span.start..span.end };
            proof {
                assert(structural_error_location(source, error)) by {
                    reveal(list_source_delimiters);
                    assert(list_delimited(source.spec_bytes(), forms@[index as int], recovering));
                };
                parser_error_evidence(source, error);
                assert(index == previous.last());
                strict_error::record_unclosed_list(source, error, input_prefix, lexer.needs_separator, forms@, previous);
            }
            return Err(error);
        }
    }

    assert(open@.len() == 0);
    let _form_count = forms.len();
    assert(_form_count == forms@.len());
    assert forall|i: int| 0 <= i < forms@.len() implies match #[trigger] forms@[i] {
        Form::List { end, .. } => i < end <= forms@.len(),
        Form::Atom { .. } => true,
    } by {
        assert(i <= usize::MAX);
        assert(!open@.contains(i as usize));
    };
    Ok((forms, repairs, original_lists))
}

fn finish_list(forms: &mut Vec<Form>, index: usize, offset: usize)
    requires
        index < old(forms)@.len(),
        old(forms)@[index as int] is List,
    ensures
        final(forms)@.len() == old(forms)@.len(),
        match final(forms)@[index as int] {
            Form::List { span, end } => end == old(forms)@.len()
                && span.start == old(forms)@[index as int]->List_span.start
                && span.end == offset,
            Form::Atom { .. } => false,
        },
        forall|i: int| 0 <= i < old(forms)@.len() && i != index
            ==> #[trigger] final(forms)@[i] == old(forms)@[i],
{
    let subtree_end = forms.len();
    let start = match &forms[index] {
        Form::List { span, .. } => span.start,
        Form::Atom { .. } => unreachable!("only list indices are stacked"),
    };
    forms[index] = Form::List { span: start..offset, end: subtree_end };
}

spec fn is_suffix(source: Seq<u8>, suffix: Seq<u8>) -> bool {
    &&& suffix.len() <= source.len()
    &&& suffix =~= source[(source.len() - suffix.len())..]
}

proof fn suffix_transitive(source: Seq<u8>, middle: Seq<u8>, tail: Seq<u8>)
    requires
        is_suffix(source, middle),
        is_suffix(middle, tail),
    ensures
        is_suffix(source, tail),
{
    assert(tail =~= source[(source.len() - tail.len())..]);
}

proof fn suffix_boundary(source: &str, suffix: &str)
    requires
        is_suffix(source.spec_bytes(), suffix.spec_bytes()),
    ensures
        is_char_boundary(source.spec_bytes(),
            source.spec_bytes().len() - suffix.spec_bytes().len()),
{
    let bytes = source.spec_bytes();
    let rest = suffix.spec_bytes();
    let offset = bytes.len() - rest.len();
    encode_utf8_valid_utf8(source@);
    if rest.len() == 0 {
        is_char_boundary_start_end_of_seq(bytes);
    } else {
        encode_utf8_valid_utf8(suffix@);
        reveal_with_fuel(valid_utf8, 2);
        assert(bytes[offset] == rest[0]);
        assert(!is_continuation_byte(rest[0]));
        is_char_boundary_iff_not_is_continuation_byte(bytes, offset);
    }
}

#[derive(Clone, Copy)]
struct SourceCursor<'a> {
    source: &'a str,
    remaining: &'a str,
}

impl<'a> SourceCursor<'a> {
    spec fn valid(self) -> bool {
        is_suffix(self.source.spec_bytes(), self.remaining.spec_bytes())
    }

    spec fn position(self) -> int {
        self.source.spec_bytes().len() - self.remaining.spec_bytes().len()
    }

    fn new(source: &'a str) -> (cursor: Self)
        ensures
            cursor.source == source,
            cursor.valid(),
            cursor.position() == 0,
    {
        Self { source, remaining: source }
    }

    fn advance(self) -> (step: Option<(RawSegment<'a>, Range<usize>, Self)>)
        requires
            self.valid(),
        ensures
            match step {
                None => self.position() == self.source.spec_bytes().len(),
                Some((kind, span, next)) => {
                    &&& next.source == self.source
                    &&& next.valid()
                    &&& span.start == self.position()
                    &&& span.start < span.end
                    &&& span.end == next.position()
                    &&& span.end <= self.source.spec_bytes().len()
                    &&& (forall|close: int| #[trigger] quoted_prefix_at(self.remaining.spec_bytes(), close)
                        ==> kind is Quoted && kind->Quoted_0 is None && span.end == span.start + close + 1)
                    &&& (kind is Quoted ==> self.source.spec_bytes()[span.start as int] == 34)
                    &&& (kind is Quoted && kind->Quoted_0 is None
                        ==> quoted_atom(self.source.spec_bytes()[span.start as int..span.end as int]))
                    &&& (kind is Quoted && kind->Quoted_0 is Some
                        ==> syntax_error_evidence(self.source, kind->Quoted_0->Some_0)
                            && string_error_kind(kind->Quoted_0->Some_0.kind)
                            && first_string_error(self.source.spec_bytes()[span.start as int..],
                                span.start as int, kind->Quoted_0->Some_0)
                            && span.end == span.start
                                + string_recovery_end_from(self.source.spec_bytes()[span.start as int..], 1))
                    &&& (kind is Bare ==> kind->Bare_0.spec_bytes()
                        =~= self.source.spec_bytes()[span.start as int..span.end as int]
                        && bare_atom_extent(self.source.spec_bytes(), span.start as int, span.end as int))
                    &&& (kind is Whitespace || kind is Comment ==> trivia_extent(
                        self.source.spec_bytes(), span.start as int, span.end as int, kind is Comment))
                    &&& (kind is Open ==> span.end == span.start + 1
                        && self.source.spec_bytes()[span.start as int] == 40)
                    &&& (kind is Close ==> span.end == span.start + 1
                        && self.source.spec_bytes()[span.start as int] == 41)
                    &&& is_char_boundary(self.source.spec_bytes(), span.start as int)
                    &&& is_char_boundary(self.source.spec_bytes(), span.end as int)
                },
            },
    {
        let source_length = self.source.as_bytes().len();
        let length = self.remaining.as_bytes().len();
        if length == 0 {
            return None;
        }
        let start = source_length - length;
        let (kind, remaining) = split_segment(self.remaining, start);
        let end = source_length - remaining.as_bytes().len();
        proof {
            suffix_transitive(
                self.source.spec_bytes(), self.remaining.spec_bytes(), remaining.spec_bytes()
            );
            suffix_boundary(self.source, self.remaining);
            suffix_boundary(self.source, remaining);
            assert forall|close: int| #[trigger] quoted_prefix_at(self.remaining.spec_bytes(), close)
                implies kind is Quoted && kind->Quoted_0 is None && end == start + close + 1 by {
                reveal(quoted_prefix_at);
                assert(remaining.spec_bytes() == self.remaining.spec_bytes()[(close + 1)..]);
                assert(remaining.spec_bytes().len() == length - (close + 1));
            };
            if kind is Quoted && kind->Quoted_0 is Some {
                let error = kind->Quoted_0->Some_0;
                assert(syntax_error_evidence(self.source, error)) by {
                    reveal(syntax_error_evidence);
                    reveal(atom_and_close_error_evidence);
                    assert(self.remaining.spec_bytes() =~= self.source.spec_bytes()[start as int..]);
                    assert(string_error_opening(error.kind, error.span) == Some(start));
                };
            }
            if kind is Quoted && kind->Quoted_0 is None {
                assert(self.remaining.spec_bytes()[..(end - start)]
                    =~= self.source.spec_bytes()[start as int..end as int]);
            }
            if kind is Whitespace || kind is Comment {
                lift_trivia_extent(self.source.spec_bytes(), self.remaining.spec_bytes(),
                    start as int, end as int, kind is Comment);
            }
            if kind is Bare {
                assert(kind->Bare_0.spec_bytes() =~= self.remaining.spec_bytes()[..(end - start)]);
                assert(kind->Bare_0.spec_bytes() =~= self.source.spec_bytes()[start as int..end as int]);
                lift_bare_extent(self.source.spec_bytes(), self.remaining.spec_bytes(), start as int, end as int);
            }
        }
        Some((kind, start..end, Self { source: self.source, remaining }))
    }
}

enum RawSegment<'a> {
    Whitespace,
    Comment,
    Open,
    Close,
    Quoted(Option<Error>),
    Bare(&'a str),
}

fn split_segment(input: &str, start: usize) -> (result: (RawSegment<'_>, &str))
    requires
        input.spec_bytes().len() > 0,
        start + input.spec_bytes().len() <= usize::MAX,
    ensures
        forall|close: int| #[trigger] quoted_prefix_at(input.spec_bytes(), close)
            ==> result.0 is Quoted && result.0->Quoted_0 is None
                && result.1.spec_bytes() == input.spec_bytes()[(close + 1)..],
        result.0 is Quoted ==> input.spec_bytes()[0] == 34,
        is_suffix(input.spec_bytes(), result.1.spec_bytes()),
        result.1.spec_bytes().len() < input.spec_bytes().len(),
        is_char_boundary(input.spec_bytes(), input.spec_bytes().len() - result.1.spec_bytes().len()),
        match result.0 {
            RawSegment::Bare(atom) =>
                atom.spec_bytes() + result.1.spec_bytes() =~= input.spec_bytes()
                && bare_atom_extent(input.spec_bytes(), 0, atom.spec_bytes().len() as int),
            RawSegment::Whitespace | RawSegment::Comment => trivia_extent(input.spec_bytes(),
                0, input.spec_bytes().len() - result.1.spec_bytes().len(), result.0 is Comment),
            RawSegment::Open => input.spec_bytes()[0] == 40
                && result.1.spec_bytes().len() + 1 == input.spec_bytes().len(),
            RawSegment::Close => input.spec_bytes()[0] == 41
                && result.1.spec_bytes().len() + 1 == input.spec_bytes().len(),
            RawSegment::Quoted(None) => quoted_atom(input.spec_bytes()[..input.spec_bytes().len() - result.1.spec_bytes().len()]),
            RawSegment::Quoted(Some(error)) => string_error_kind(error.kind)
                && string_error_site(input.spec_bytes(), start as int, error)
                && first_string_error(input.spec_bytes(), start as int, error)
                && string_recovery_end_from(input.spec_bytes(), 1) == input.spec_bytes().len() - result.1.spec_bytes().len(),
        },
{
    let first = input.as_bytes()[0];
    proof { quoted_prefix_starts_with_quote(input.spec_bytes()); }
    let (kind, remaining) = match first {
        b' ' | b'\t' | b'\r' | b'\n' => (
            RawSegment::Whitespace,
            split_trivia(input, false),
        ),
        b';' => (RawSegment::Comment, split_trivia(input, true)),
        b'(' => (RawSegment::Open, after_ascii(input)),
        b')' => (RawSegment::Close, after_ascii(input)),
        b'"' => {
            // 「診断と補完の仕様」のエラー回復に従い、不正な文字列内の括弧を同期点にしない。
            let (remaining, error) = scan_string(input, start);
            (RawSegment::Quoted(error), remaining)
        }
        _ => {
            let (atom, remaining) = split_at_boundary(input, Boundary::AtomEnd);
            proof {
                reveal(bare_atom_extent);
                let bytes = input.spec_bytes();
                let end = atom.spec_bytes().len() as int;
                assert(end > 0);
                assert forall|i: int| 0 <= i < end implies !bare_atom_delimiter(#[trigger] bytes[i]) by {
                    assert(bytes[i] == atom.spec_bytes()[i]);
                };
                if end < bytes.len() {
                    assert(bytes[end] == remaining.spec_bytes()[0]);
                }
                assert(bare_atom_extent(bytes, 0, end));
            }
            (RawSegment::Bare(atom), remaining)
        }
    };
    proof { suffix_boundary(input, remaining); }
    (kind, remaining)
}

spec fn string_error_kind(kind: ErrorKind) -> bool {
    kind is InvalidEscape || kind is NewlineInString || kind is UnterminatedString
}

pub open spec fn string_error_site(bytes: Seq<u8>, start: int, error: Error) -> bool {
    let at = error.span.start - start;
    let end = error.span.end - start;
    &&& bytes.len() > 0 && bytes[0] == 34
    &&& 0 <= at < end <= bytes.len()
    &&& match error.kind {
        ErrorKind::InvalidEscape { opening } => {
            &&& opening == start
            &&& at > 0 && at + 1 < end
            &&& bytes[at] == 92
            &&& bytes[at + 1] != 34 && bytes[at + 1] != 92
            &&& end == at + 1 + length_of_first_scalar(bytes[(at + 1)..])
        },
        ErrorKind::NewlineInString { opening } => {
            &&& opening == start && at > 0
            &&& end == at + 1
            &&& (bytes[at] == 10 || bytes[at] == 13)
        },
        ErrorKind::UnterminatedString => at == 0 && end == bytes.len(),
        _ => false,
    }
}

spec fn string_body_piece(bytes: Seq<u8>) -> bool {
    (forall|i: int| 0 <= i < bytes.len() ==> {
        let byte = #[trigger] bytes[i];
        byte != 34 && byte != 92 && byte != 10 && byte != 13
    })
        || (bytes.len() == 2 && bytes[0] == 92 && (bytes[1] == 34 || bytes[1] == 92))
}

spec fn string_body_pieces(pieces: Seq<Seq<u8>>) -> bool {
    forall|i: int| 0 <= i < pieces.len() ==> string_body_piece(#[trigger] pieces[i])
}

pub closed spec fn quoted_atom(bytes: Seq<u8>) -> bool {
    &&& valid_utf8(bytes)
    &&& bytes.len() >= 2
    &&& bytes[0] == 34
    &&& bytes[bytes.len() - 1] == 34
    &&& exists|pieces: Seq<Seq<u8>>| #[trigger] pieces.flatten() == bytes[1..bytes.len() - 1]
        && string_body_pieces(pieces)
}

proof fn extend_body(bytes: Seq<u8>, pieces: Seq<Seq<u8>>, piece: Seq<u8>, from: int, to: int)
    requires
        1 <= from <= to <= bytes.len(),
        string_body_pieces(pieces),
        pieces.flatten() == bytes[1..from],
        piece == bytes[from..to],
        string_body_piece(piece),
    ensures
        string_body_pieces(pieces.push(piece)),
        pieces.push(piece).flatten() == bytes[1..to],
{
    pieces.lemma_flatten_push(piece);
    assert(pieces.flatten() + piece =~= bytes[1..to]);
}

fn scan_string(input: &str, start: usize) -> (result: (&str, Option<Error>))
    requires
        input.spec_bytes().len() > 0,
        input.spec_bytes()[0] == 34,
        start + input.spec_bytes().len() <= usize::MAX,
    ensures
        forall|close: int| #[trigger] quoted_prefix_at(input.spec_bytes(), close)
            ==> result.1.is_none() && result.0.spec_bytes() == input.spec_bytes()[(close + 1)..],
        is_suffix(input.spec_bytes(), result.0.spec_bytes()),
        result.0.spec_bytes().len() < input.spec_bytes().len(),
        is_char_boundary(input.spec_bytes(), input.spec_bytes().len() - result.0.spec_bytes().len()),
        string_recovery_end_from(input.spec_bytes(), 1) == input.spec_bytes().len() - result.0.spec_bytes().len(),
        match result.1 {
            Some(error) => string_error_kind(error.kind)
                && string_error_site(input.spec_bytes(), start as int, error)
                && first_string_error(input.spec_bytes(), start as int, error)
                && (error.kind is UnterminatedString ==> result.0.spec_bytes().len() == 0),
            None => quoted_atom(input.spec_bytes()[..input.spec_bytes().len() - result.0.spec_bytes().len()]),
        },
{
    let length = input.as_bytes().len();
    let mut remaining = after_ascii(input);
    let mut error: Option<Error> = None;
    let ghost mut pieces: Seq<Seq<u8>> = Seq::empty();
    let ghost mut eof_stop = 1int;
    assert(pieces.flatten() =~= input.spec_bytes()[1..1]);
    proof {
        initialize_quoted_prefixes(input.spec_bytes());
        assert(input.spec_bytes().len() - remaining.spec_bytes().len() == 1);
    }
    loop
        invariant_except_break
            quoted_prefixes_viable(input.spec_bytes(),
                length - remaining.spec_bytes().len(), error.is_none()),
            error.is_none() ==> string_body_pieces(pieces)
                && pieces.flatten() == input.spec_bytes()[1..length - remaining.spec_bytes().len()],
        invariant
            length == input.spec_bytes().len(),
            length > 0,
            input.spec_bytes()[0] == 34,
            start + length <= usize::MAX,
            is_suffix(input.spec_bytes(), remaining.spec_bytes()),
            remaining.spec_bytes().len() < length,
            string_recovery_end_from(input.spec_bytes(), 1)
                == string_recovery_end_from(input.spec_bytes(), length - remaining.spec_bytes().len()),
            match error {
                Some(error) => error.kind is InvalidEscape
                    && string_error_site(input.spec_bytes(), start as int, error)
                    && first_string_error(input.spec_bytes(), start as int, error),
                None => true,
            },
        ensures
            remaining.spec_bytes().len() == 0,
            string_recovery_end_from(input.spec_bytes(), 1) == length,
            forall|close: int| !#[trigger] quoted_prefix_at(input.spec_bytes(), close),
            error.is_none() ==> 1 <= eof_stop <= length
                && (eof_stop == length || (eof_stop + 1 == length && input.spec_bytes()[eof_stop] == 92))
                && quoted_prefix::quoted_body(input.spec_bytes(), 1, eof_stop),
        decreases remaining.spec_bytes().len(),
    {
        let ghost before = remaining.spec_bytes();
        let (_ordinary, rest) = split_at_boundary(remaining, Boundary::StringSpecial);
        remaining = rest;
        proof {
            let from = length - before.len();
            let to = length - remaining.spec_bytes().len();
            let piece = _ordinary.spec_bytes();
            assert(piece =~= input.spec_bytes()[from..to]);
            assert forall|i: int| from <= i < to
                implies !boundary::stops(Boundary::StringSpecial, #[trigger] input.spec_bytes()[i]) by {
                assert(input.spec_bytes()[i] == piece[i - from]);
            };
            advance_quoted_prefixes_over_ordinary(input.spec_bytes(), from, to, error.is_none());
            skip_ordinary_string_bytes(input.spec_bytes(), from, to);
            if error.is_none() {
                assert(string_body_piece(piece));
                extend_body(input.spec_bytes(), pieces, piece, from, to);
                pieces = pieces.push(piece);
            }
        }
        proof { suffix_transitive(input.spec_bytes(), before, remaining.spec_bytes()); }
        let bytes = remaining.as_bytes();
        let position = start + (length - bytes.len());
        let ghost relative = position - start;
        if bytes.len() == 0 {
            proof {
                quoted_stop(input.spec_bytes(), relative, error.is_none());
                string_recovery_end_at_stop(input.spec_bytes(), relative);
                if error.is_none() {
                    eof_stop = relative;
                    quoted_prefix::derive_quoted_body(input.spec_bytes(), 1, eof_stop, pieces);
                }
            }
            break;
        }
        assert(input.spec_bytes()[relative] == bytes@[0]);
        match bytes[0] {
            b'"' => {
                let tail = after_ascii(remaining);
                proof { suffix_transitive(input.spec_bytes(), remaining.spec_bytes(), tail.spec_bytes()); }
                proof {
                    quoted_stop(input.spec_bytes(), relative, error.is_none());
                    suffix_boundary(input, tail);
                    string_recovery_end_at_stop(input.spec_bytes(), relative);
                    if error.is_none() {
                        encode_utf8_valid_utf8(input@);
                        valid_utf8_split(input.spec_bytes(), relative + 1);
                        let literal = input.spec_bytes()[..(relative + 1)];
                        assert(literal[0] == 34 && literal[relative] == 34);
                        assert(pieces.flatten() =~= literal[1..relative]);
                        assert(exists|p: Seq<Seq<u8>>| #[trigger] p.flatten() == literal[1..relative]
                            && string_body_pieces(p));
                        assert(quoted_atom(literal));
                    }
                }
                return (tail, error);
            }
            b'\r' | b'\n' => {
                proof {
                    quoted_stop(input.spec_bytes(), relative, error.is_none());
                    string_recovery_end_at_stop(input.spec_bytes(), relative);
                }
                if error.is_none() {
                    error = Some(Error { kind: ErrorKind::NewlineInString { opening: start }, span: position..position + 1 });
                    proof {
                        quoted_prefix::derive_quoted_body(input.spec_bytes(), 1, relative, pieces);
                        record_first_string_error(input.spec_bytes(), start as int, relative, error->Some_0);
                    }
                }
                proof { suffix_boundary(input, remaining); }
                return (remaining, error);
            }
            _ => {
                assert(bytes[0] == b'\\');
                let ghost before_slash = remaining.spec_bytes();
                let ghost clean = error.is_none();
                proof { escape_at_quoted_prefixes(input.spec_bytes(), relative, clean); }
                remaining = after_ascii(remaining);
                proof { suffix_transitive(input.spec_bytes(), before_slash, remaining.spec_bytes()); }
                let ghost escaped_text = remaining;
                let escaped_bytes = remaining.as_bytes();
                if escaped_bytes.len() == 0 {
                    proof {
                        assert(relative + 1 == length);
                        string_recovery_end_after_escape(input.spec_bytes(), relative, length as int);
                        string_recovery_end_at_stop(input.spec_bytes(), length as int);
                        if clean {
                            eof_stop = relative;
                            quoted_prefix::derive_quoted_body(input.spec_bytes(), 1, eof_stop, pieces);
                        }
                    }
                    break;
                }
                assert(escaped_bytes@ =~= input.spec_bytes()[(relative + 1)..]);
                let escaped = escaped_bytes[0];
                let (scalar, suffix) = split_first_scalar(remaining);
                if !matches!(escaped, b'"' | b'\\') && error.is_none() {
                    let width = scalar.as_bytes().len();
                    error = Some(Error {
                        kind: ErrorKind::InvalidEscape { opening: start },
                        span: position..position + 1 + width,
                    });
                    proof {
                        quoted_prefix::derive_quoted_body(input.spec_bytes(), 1, relative, pieces);
                        record_first_string_error(input.spec_bytes(), start as int, relative, error->Some_0);
                    }
                }
                if !matches!(escaped, b'\r' | b'\n') {
                    proof {
                        suffix_transitive(input.spec_bytes(), remaining.spec_bytes(), suffix.spec_bytes());
                        if error.is_none() {
                            assert(escaped == 34 || escaped == 92);
                            assert(scalar.spec_bytes().len() == 1);
                            let piece = input.spec_bytes()[relative..relative + 2];
                            assert(string_body_piece(piece));
                            extend_body(input.spec_bytes(), pieces, piece, relative, relative + 2);
                            pieces = pieces.push(piece);
                        }
                    }
                    remaining = suffix;
                }
                proof {
                    let next = length - remaining.spec_bytes().len();
                    if escaped != b'\r' && escaped != b'\n' {
                        let escaped_suffix = input.spec_bytes()[(relative + 1)..];
                        encode_utf8_valid_utf8(escaped_text@);
                        assert(valid_first_scalar(escaped_suffix)) by { reveal_with_fuel(valid_utf8, 2); };
                        recovery_scalar_width_matches(escaped_suffix);
                        assert(next == relative + 1 + recovery_scalar_width(input.spec_bytes()[relative + 1]));
                    }
                    string_recovery_end_after_escape(input.spec_bytes(), relative, next);
                    if escaped == 34 || escaped == 92 {
                        assert(length - remaining.spec_bytes().len() == relative + 2);
                        assert(error.is_none() == clean);
                    } else {
                        reveal(quoted_prefixes_viable);
                        assert forall|close: int| !#[trigger] quoted_prefix_at(input.spec_bytes(), close) by {
                            if quoted_prefix_at(input.spec_bytes(), close) {
                                assert(input.spec_bytes()[relative + 1] == 34
                                    || input.spec_bytes()[relative + 1] == 92);
                            }
                        };
                    }
                }
            }
        }
    }
    if error.is_none() {
        error = Some(Error {
            kind: ErrorKind::UnterminatedString,
            span: start..start + length,
        });
        proof { record_first_string_error(input.spec_bytes(), start as int, eof_stop, error->Some_0); }
    }
    proof { suffix_boundary(input, remaining); }
    (remaining, error)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexer_preserves_all_source_and_ignores_parens_inside_malformed_strings() {
        let source = "(a \"日\\q); still inside\" ; comment\r\nb)";
        let segments: Vec<_> = Lexer::new(source).collect();
        let mut offset = 0;
        for segment in &segments {
            assert_eq!(segment.span.start, offset);
            assert!(segment.span.end > offset);
            assert!(source.is_char_boundary(segment.span.end));
            offset = segment.span.end;
        }
        assert_eq!(offset, source.len());
        let malformed = &segments[3];
        assert_eq!(&source[malformed.span.clone()], "\"日\\q); still inside\"");
        let SegmentKind::Malformed(error) = &malformed.kind else {
            panic!("expected malformed string");
        };
        assert_eq!(error.kind, ErrorKind::InvalidEscape { opening: 3 });
        assert_eq!(&source[error.span.clone()], "\\q");
        assert_eq!(
            segments
                .iter()
                .filter(|s| s.kind == SegmentKind::Close)
                .count(),
            1
        );
    }

    #[test]
    fn lexer_leaves_crlf_after_malformed_string_for_trivia() {
        let source = "\"bad\\\r\nb)";
        let segments: Vec<_> = Lexer::new(source).collect();
        assert_eq!(segments[0].span, 0..5);
        assert_eq!(&source[segments[1].span.clone()], "\r\n");
        assert_eq!(segments[2].kind, SegmentKind::Atom(AtomKind::Name));
        assert_eq!(segments[3].kind, SegmentKind::Close);
        assert_eq!(
            parse(source).unwrap_err().kind,
            ErrorKind::InvalidEscape { opening: 0 }
        );
    }

    #[test]
    fn missing_separator_retains_the_intrinsic_error() {
        let source = "a\"\\q\"";
        let segment = Lexer::new(source).nth(1).unwrap();
        assert!(segment.missing_separator);
        assert!(matches!(
            segment.kind,
            SegmentKind::Malformed(Error {
                kind: ErrorKind::InvalidEscape { opening: 1 },
                ..
            })
        ));
        assert_eq!(parse(source).unwrap_err().kind, ErrorKind::MissingSeparator);
    }

    #[test]
    fn whitespace_ends_before_a_multibyte_character() {
        let source = " \t\r\n日";
        let mut lexer = Lexer::new(source);
        let whitespace = lexer.next().unwrap();
        assert_eq!(whitespace.kind, SegmentKind::Whitespace);
        assert_eq!(whitespace.span, 0..4);
        let atom = lexer.next().unwrap();
        assert_eq!(atom.span, 4..source.len());
        assert_eq!(parse(source).unwrap_err().span, atom.span);
    }

    #[test]
    fn parentheses_consume_one_byte_before_multibyte_input() {
        let source = "(日)本";
        let segments: Vec<_> = Lexer::new(source).collect();
        assert_eq!(segments[0].kind, SegmentKind::Open);
        assert_eq!(segments[0].span, 0..1);
        assert_eq!(segments[1].span, 1..4);
        assert_eq!(segments[2].kind, SegmentKind::Close);
        assert_eq!(segments[2].span, 4..5);
        assert_eq!(segments[3].span, 5..8);
    }

    #[test]
    fn string_atoms_end_at_the_unescaped_quote() {
        for literal in [r#""""#, r#""日); \"本""#, r#""\\\"""#] {
            let source = alloc::format!("{literal}()");
            let segments: Vec<_> = Lexer::new(&source).collect();
            assert_eq!(segments.len(), 3, "{source:?}");
            assert_eq!(segments[0].kind, SegmentKind::Atom(AtomKind::String));
            assert_eq!(segments[0].span, 0..literal.len());
            assert_eq!(&source[segments[0].span.clone()], literal);
            assert_eq!(segments[1].kind, SegmentKind::Open);
            assert_eq!(segments[2].kind, SegmentKind::Close);
        }
    }

    #[test]
    fn malformed_string_keeps_first_error_and_full_scalar_span() {
        let source = "\"\\日\n";
        let segments: Vec<_> = Lexer::new(source).collect();
        assert_eq!(segments[0].span, 0..5);
        assert_eq!(segments[1].kind, SegmentKind::Whitespace);
        let error = parse(source).unwrap_err();
        assert_eq!(error.kind, ErrorKind::InvalidEscape { opening: 0 });
        assert_eq!(error.span, 1..5);
        assert_eq!(
            parse("\"\\").unwrap_err().kind,
            ErrorKind::UnterminatedString
        );
    }

    #[test]
    fn invalid_escape_spans_one_scalar_at_every_utf8_width() {
        for scalar in ['q', 'é', '日', '😀'] {
            let source = alloc::format!("\"\\{scalar}\"()");
            let segments: Vec<_> = Lexer::new(&source).collect();
            let end = 2 + scalar.len_utf8();
            assert_eq!(
                parse(&source).unwrap_err(),
                Error {
                    kind: ErrorKind::InvalidEscape { opening: 0 },
                    span: 1..end,
                }
            );
            assert_eq!(segments[0].span, 0..end + 1);
            assert_eq!(segments[1].kind, SegmentKind::Open);
            assert_eq!(segments[1].span.start, end + 1);
        }
    }

    #[test]
    fn line_comment_stops_before_crlf() {
        let source = ";日\r\n (a)";
        let mut lexer = Lexer::new(source);
        let comment = lexer.next().unwrap();
        assert_eq!(comment.kind, SegmentKind::Comment);
        assert_eq!(&source[comment.span], ";日");
        let whitespace = lexer.next().unwrap();
        assert_eq!(whitespace.kind, SegmentKind::Whitespace);
        assert_eq!(&source[whitespace.span], "\r\n ");
        assert_eq!(lexer.next().unwrap().kind, SegmentKind::Open);
    }
}
