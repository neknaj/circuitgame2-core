//! 共通の S 式字句を保ち、空白と改行を整える。

use alloc::string::String;
use vstd::prelude::*;
use super::{Error, Lexer, SegmentKind, boundary::source_span, parse};
#[cfg(verus_only)]
use super::{InputDerivation, follow_input_derivation, lexical};
#[cfg(verus_only)]
use crate::LexemeKind;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::{encode_scalar, encode_utf8, encode_utf8_concat, encode_utf8_push}};

#[cfg(verus_only)]
mod proof;

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::seq_lib::group_seq_properties};

#[derive(Clone, Copy)]
enum Piece {
    Open,
    Close,
    Comment,
    Atom,
}

#[derive(Clone, Copy)]
enum Gap {
    Empty,
    Space,
    Line,
}

spec fn piece_kind(kind: LexemeKind) -> Piece {
    match kind {
        LexemeKind::Open => Piece::Open,
        LexemeKind::Close => Piece::Close,
        LexemeKind::Comment => Piece::Comment,
        _ => Piece::Atom,
    }
}

spec fn gap_layout(previous: Option<Piece>, current: Piece, line_break: bool, depth: int) -> Gap {
    if previous is None {
        Gap::Empty
    } else if matches!(previous, Some(Piece::Comment)) || line_break
        || (depth == 0 && !matches!(current, Piece::Comment)) {
        Gap::Line
    } else if matches!(current, Piece::Comment) {
        Gap::Space
    } else if matches!(previous, Some(Piece::Open)) || matches!(current, Piece::Close) {
        Gap::Empty
    } else {
        Gap::Space
    }
}

fn layout_gap(previous: Option<Piece>, current: Piece, line_break: bool, depth: usize) -> (gap: Gap)
    ensures gap == gap_layout(previous, current, line_break, depth as int),
{
    if previous.is_none() {
        Gap::Empty
    } else if matches!(previous, Some(Piece::Comment)) || line_break
        || (depth == 0 && !matches!(current, Piece::Comment)) {
        Gap::Line
    } else if matches!(current, Piece::Comment) {
        Gap::Space
    } else if matches!(previous, Some(Piece::Open)) || matches!(current, Piece::Close) {
        Gap::Empty
    } else {
        Gap::Space
    }
}

spec fn indentation(depth: int) -> Seq<u8> {
    Seq::new((2 * depth) as nat, |_: int| b' ')
}

spec fn gap_bytes(gap: Gap, current: Piece, depth: int) -> Seq<u8> {
    match gap {
        Gap::Empty => Seq::empty(),
        Gap::Space => seq![b' '],
        Gap::Line => seq![b'\n'] + indentation(if current == Piece::Close { depth - 1 } else { depth }),
    }
}

spec fn has_break(bytes: Seq<u8>) -> bool {
    bytes.contains(b'\r') || bytes.contains(b'\n')
}

fn contains_break(bytes: &[u8]) -> (result: bool)
    ensures result == has_break(bytes@),
{
    let mut index = 0;
    while index < bytes.len()
        invariant index <= bytes@.len(), !has_break(bytes@.take(index as int)),
        decreases bytes@.len() - index,
    {
        if bytes[index] == b'\r' || bytes[index] == b'\n' {
            assert(bytes@.contains(bytes@[index as int]));
            return true;
        }
        assert(bytes@.take(index as int + 1) =~= bytes@.take(index as int).push(bytes@[index as int]));
        index += 1;
    }
    assert(bytes@.take(index as int) =~= bytes@);
    false
}

spec fn previous_piece(input: InputDerivation, index: int) -> Option<int>
    decreases index,
{
    if index <= 0 {
        None
    } else if input.lexemes[index - 1].kind is Whitespace {
        previous_piece(input, index - 1)
    } else {
        Some(index - 1)
    }
}

spec fn previous_kind(input: InputDerivation, index: int) -> Option<Piece> {
    match previous_piece(input, index) {
        Some(prev) => Some(piece_kind(input.lexemes[prev].kind)),
        None => None,
    }
}

spec fn previous_end(input: InputDerivation, index: int) -> int {
    match previous_piece(input, index) {
        Some(prev) => input.lexemes[prev].end,
        None => 0,
    }
}

spec fn formatted_gap(bytes: Seq<u8>, input: InputDerivation, index: int) -> Seq<u8> {
    let piece = input.lexemes[index];
    let kind = piece_kind(piece.kind);
    let depth = input.depths[index];
    let line_break = has_break(bytes[previous_end(input, index)..piece.start]);
    gap_bytes(gap_layout(previous_kind(input, index), kind, line_break, depth), kind, depth)
}

#[verifier::opaque]
spec fn formatted_prefix(bytes: Seq<u8>, input: InputDerivation, index: int) -> Seq<u8>
    decreases index,
{
    if index <= 0 {
        Seq::empty()
    } else {
        let prefix = formatted_prefix(bytes, input, index - 1);
        let piece = input.lexemes[index - 1];
        if piece.kind is Whitespace { prefix }
        else { prefix + formatted_gap(bytes, input, index - 1) + bytes[piece.start..piece.end] }
    }
}

/// 入力の字句導出で決まる整形後のバイト列を表す。
///
/// 文字列、コメント、括弧など空白以外の各字句を順に出力する。字句の間では元の改行を保ち、
/// トップレベルの式を別行に置く。行頭には深さ1につき2個の空白を置く。末尾は LF とし、
/// 空白以外の字句がない場合は空にする。
pub closed spec fn formatted_bytes(source: &str) -> Option<Seq<u8>> {
    formatted_from_bytes(source.spec_bytes())
}

spec fn formatted_from_bytes(bytes: Seq<u8>) -> Option<Seq<u8>> {
    match lexical::chosen_input_derivation_bytes(bytes) {
        None => None,
        Some(input) => {
            let total = input.lexemes.len() as int;
            Some(formatted_prefix(bytes, input, total)
                + if previous_piece(input, total) is None { Seq::empty() } else { seq![b'\n'] })
        },
    }
}

/// 空白字句を除き、各字句の種類と UTF-8 の表記を入力順に並べる。
///
/// 字句または S 式が不正なら `None` を返す。
pub closed spec fn formatting_lexemes(source: &str) -> Option<Seq<(LexemeKind, Seq<u8>)>> {
    proof::formatting_lexemes_bytes(source.spec_bytes())
}

/// 整形前後の字句が元の表記と並びを保ち、出力がもう一度整形しても同じになることを表す。
pub closed spec fn formatted_preserves(source: &str, output: Seq<u8>) -> bool {
    let original_lexemes = proof::formatting_lexemes_bytes(source.spec_bytes());
    &&& original_lexemes is Some
    &&& proof::formatting_lexemes_bytes(output) == original_lexemes
    &&& formatted_from_bytes(output) == Some(output)
}

/// 整形結果の UTF-8 文字列は同じ字句を持ち、再整形で変わらない。
pub proof fn formatted_output_is_stable(source: &str, output: &str)
    requires formatted_preserves(source, output.spec_bytes()),
    ensures
        formatting_lexemes(source) is Some,
        formatting_lexemes(source) == formatting_lexemes(output),
        formatted_bytes(output) == Some(output.spec_bytes()),
{
}

fn append(output: &mut String, text: &str)
    ensures encode_utf8(final(output)@) == encode_utf8(old(output)@) + text.spec_bytes(),
{
    proof { encode_utf8_concat(output@, text@); }
    output.push_str(text);
}

fn append_layout_byte(output: &mut String, character: char)
    requires character == ' ' || character == '\n',
    ensures encode_utf8(final(output)@) == encode_utf8(old(output)@) + seq![character as u8],
{
    proof {
        encode_utf8_push(output@, character);
        if character == ' ' {
            assert((32u32 & 127u32) as u8 == 32u8) by (bit_vector);
            assert(encode_scalar(b' ' as u32) =~= seq![b' ']);
        } else {
            assert((10u32 & 127u32) as u8 == 10u8) by (bit_vector);
            assert(encode_scalar(b'\n' as u32) =~= seq![b'\n']);
        }
    }
    output.push(character);
}

fn append_gap(output: &mut String, gap: Gap, current: Piece, depth: usize)
    requires current == Piece::Close ==> depth > 0,
    ensures encode_utf8(final(output)@) == encode_utf8(old(output)@) + gap_bytes(gap, current, depth as int),
{
    match gap {
        Gap::Empty => {},
        Gap::Space => append_layout_byte(output, ' '),
        Gap::Line => {
            let indent = if matches!(current, Piece::Close) { depth - 1 } else { depth };
            let ghost before = encode_utf8(output@);
            append_layout_byte(output, '\n');
            let ghost start = encode_utf8(output@);
            let mut i = 0;
            assert(indentation(0) =~= Seq::<u8>::empty());
            while i < indent
                invariant i <= indent, encode_utf8(output@) == start + indentation(i as int),
                decreases indent - i,
            {
                append_layout_byte(output, ' ');
                append_layout_byte(output, ' ');
                assert(indentation((i + 1) as int) =~= indentation(i as int) + seq![b' ', b' ']);
                i += 1;
            }
            assert(start == before + seq![b'\n']);
            assert(encode_utf8(output@) =~= before + gap_bytes(gap, current, depth as int));
        },
    }
}

/// NCG2 と NCG2M が共有する S 式の空白を整える。
///
/// コメントと文字列を含む空白以外の字句は、入力の UTF-8 表記をそのまま保つ。
///
/// # Errors
///
/// 字句または S 式が不正な場合は、厳格な S 式解析と同じ位置と種別のエラーを返す。
pub fn format_sexpr(source: &str) -> (result: Result<String, Error>)
    ensures match result {
        Ok(text) => formatted_bytes(source) == Some(encode_utf8(text@))
            && formatted_preserves(source, encode_utf8(text@)),
        Err(error) => formatted_bytes(source).is_none() && super::strict_syntax_rejection(source, error),
    },
{
    if let Err(error) = parse(source) {
        proof {
            lexical::choose_input_derivation(source);
            reveal(lexical::chosen_input_derivation);
        }
        return Err(error);
    }
    let mut lexer = Lexer::new(source);
    let mut output = String::new();
    let mut previous: Option<Piece> = None;
    let mut line_break = false;
    let mut depth: usize = 0;
    let ghost input;
    let ghost mut index: int = 0;
    let bytes = source.as_bytes();
    proof {
        let derivation = lexical::choose_input_derivation(source);
        input = derivation->Some_0;
        lexical::input_starts(source.spec_bytes(), input);
        reveal(formatted_prefix);
        assert(encode_utf8(output@) == Seq::<u8>::empty());
    }
    loop
        invariant
            lexical::chosen_input_derivation(source) == Some(input),
            bytes@ == source.spec_bytes(),
            lexer.cursor.source == source, lexer.cursor.valid(),
            depth <= lexer.cursor.position(),
            lexical::input_progress(bytes@, input, index, lexer.cursor.position(), lexer.needs_separator, depth as int),
            previous == previous_kind(input, index),
            0 <= previous_end(input, index) <= lexer.cursor.position(),
            line_break == has_break(bytes@[previous_end(input, index)..lexer.cursor.position()]),
            encode_utf8(output@) == formatted_prefix(bytes@, input, index),
        decreases bytes.len() - lexer.cursor.position(),
    {
        let Some((segment, next)) = lexer.next_segment() else {
            proof {
                lexical::input_ends(bytes@, input, index, lexer.needs_separator, depth as int);
            }
            if previous.is_some() {
                append_layout_byte(&mut output, '\n');
            }
            proof {
                reveal(lexical::chosen_input_derivation);
                proof::formatting_is_stable(source, encode_utf8(output@));
            }
            return Ok(output);
        };
        let ghost lexeme;
        proof {
            lexeme = follow_input_derivation(bytes@, input, index, lexer.cursor.position(),
                lexer.needs_separator, depth as int, segment, next.needs_separator);
        }
        let piece = match segment.kind {
            SegmentKind::Whitespace => {
                let whitespace = &bytes[segment.span.start..segment.span.end];
                let extends_line = contains_break(whitespace);
                proof {
                    assert(bytes@[previous_end(input, index)..lexeme.end]
                        =~= bytes@[previous_end(input, index)..lexeme.start] + whitespace@);
                    reveal(formatted_prefix);
                    assert(formatted_prefix(bytes@, input, index + 1) == formatted_prefix(bytes@, input, index));
                }
                line_break = line_break || extends_line;
                lexer = next;
                proof { index = index + 1; }
                continue;
            },
            SegmentKind::Open => Piece::Open,
            SegmentKind::Close => Piece::Close,
            SegmentKind::Comment => Piece::Comment,
            SegmentKind::Atom(_) => Piece::Atom,
            SegmentKind::Malformed(_) => unreachable!(),
        };
        let ghost before = encode_utf8(output@);
        let gap = layout_gap(previous, piece, line_break, depth);
        append_gap(&mut output, gap, piece, depth);
        let text = source_span(source, segment.span.start, segment.span.end);
        append(&mut output, text);
        proof {
            reveal(formatted_prefix);
            reveal(lexical::input_progress);
            assert(piece == piece_kind(lexeme.kind));
            assert(depth == input.depths[index]);
            assert(text.spec_bytes() == bytes@[lexeme.start..lexeme.end]);
            assert(gap_bytes(gap, piece, depth as int) == formatted_gap(bytes@, input, index));
            assert(encode_utf8(output@) =~= before + formatted_gap(bytes@, input, index) + bytes@[lexeme.start..lexeme.end]);
            assert(encode_utf8(output@) == formatted_prefix(bytes@, input, index + 1));
        }
        if matches!(piece, Piece::Open) { depth += 1; }
        if matches!(piece, Piece::Close) { depth -= 1; }
        previous = Some(piece);
        line_break = false;
        lexer = next;
        proof { index = index + 1; }
    }
}

} // verus!
