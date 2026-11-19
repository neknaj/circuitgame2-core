//! 厳格解析が最初に入力を拒否する位置を定める。

use super::lexical::{input_lexeme_valid, lexeme_at, lexemes_agree, scanned_input_prefix};
use super::{Error, ErrorKind, InputDerivation, Lexeme, LexemeKind, bare_atom_delimiter,
    bare_atom_extent, structural_error_location};
use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

pub(super) open spec fn malformed_atom_extent(bytes: Seq<u8>, at: int, error: Error) -> bool {
    if error.kind is InvalidAtom {
        error.span.start == at && bare_atom_extent(bytes, at, error.span.end as int)
    } else {
        bytes[at] == 34
    }
}

spec fn rejection_at(bytes: Seq<u8>, at: int, needs_separator: bool, depth: int, error: Error) -> bool {
    let no_lexeme = forall|end: int, kind: LexemeKind| !#[trigger] lexeme_at(bytes, at, end, kind);
    match error.kind {
        ErrorKind::UnexpectedClose => depth == 0 && error.span.start == at
            && lexeme_at(bytes, at, error.span.end as int, LexemeKind::Close),
        ErrorKind::UnclosedList { eof } => at == bytes.len() == eof && depth > 0,
        ErrorKind::MissingSeparator => 0 <= at < bytes.len() && needs_separator && error.span.start == at
            && (forall|end: int, kind: LexemeKind| #[trigger] lexeme_at(bytes, at, end, kind) ==> kind is Atom),
        _ => 0 <= at < bytes.len() && !needs_separator && no_lexeme && malformed_atom_extent(bytes, at, error),
    }
}

/// 厳格解析が診断を選ぶまでに受理した字句と、その直後の拒否条件を表す。
///
/// 未閉鎖リストの開き位置と文字列内部の違反には、別途 `syntax_error_evidence` が根拠を与える。
pub closed spec fn strict_syntax_rejection(source: &str, error: Error) -> bool {
    let bytes = source.spec_bytes();
    exists|prefix: InputDerivation, at: int, needs_separator: bool, depth: int|
        #[trigger] scanned_input_prefix(bytes, prefix, at, needs_separator, depth)
        && rejection_at(bytes, at, needs_separator, depth, error)
}

pub(super) proof fn record_unexpected_close(
    source: &str, error: Error, prefix: InputDerivation, needs_separator: bool,
)
    requires
        error.kind is UnexpectedClose,
        error.span.end == error.span.start + 1 <= source.spec_bytes().len(),
        source.spec_bytes()[error.span.start as int] == 41,
        scanned_input_prefix(source.spec_bytes(), prefix, error.span.start as int, needs_separator, 0),
    ensures strict_syntax_rejection(source, error),
{
    reveal(lexeme_at);
    assert(rejection_at(source.spec_bytes(), error.span.start as int, needs_separator, 0, error));
}

pub(super) proof fn record_missing_separator(
    source: &str, error: Error, prefix: InputDerivation, depth: int,
)
    requires
        error.kind is MissingSeparator,
        error.span.start < source.spec_bytes().len(),
        scanned_input_prefix(source.spec_bytes(), prefix, error.span.start as int, true, depth),
        forall|end: int, kind: LexemeKind| #[trigger] lexeme_at(source.spec_bytes(), error.span.start as int, end, kind)
            ==> kind is Atom,
    ensures strict_syntax_rejection(source, error),
{
    assert(rejection_at(source.spec_bytes(), error.span.start as int, true, depth, error));
}

pub(super) proof fn record_malformed_atom(
    source: &str, error: Error, prefix: InputDerivation, at: int, depth: int,
)
    requires
        !(error.kind is UnexpectedClose || error.kind is UnclosedList || error.kind is MissingSeparator),
        0 <= at < source.spec_bytes().len(),
        scanned_input_prefix(source.spec_bytes(), prefix, at, false, depth),
        forall|end: int, kind: LexemeKind| !#[trigger] lexeme_at(source.spec_bytes(), at, end, kind),
        malformed_atom_extent(source.spec_bytes(), at, error),
    ensures strict_syntax_rejection(source, error),
{
    assert(rejection_at(source.spec_bytes(), at, false, depth, error));
}

pub(super) proof fn record_unclosed_list(
    source: &str, error: Error, prefix: InputDerivation, needs_separator: bool, depth: int,
)
    requires
        error.kind matches ErrorKind::UnclosedList { eof } && eof == source.spec_bytes().len(),
        depth > 0,
        scanned_input_prefix(source.spec_bytes(), prefix, source.spec_bytes().len() as int, needs_separator, depth),
    ensures strict_syntax_rejection(source, error),
{
    assert(rejection_at(source.spec_bytes(), source.spec_bytes().len() as int, needs_separator, depth, error));
}

proof fn preceding_lexemes_agree(bytes: Seq<u8>, a: InputDerivation, b: InputDerivation, count: int)
    requires
        0 <= count <= a.lexemes.len(), count <= b.lexemes.len(),
        a.depths.len() == a.lexemes.len() + 1, b.depths.len() == b.lexemes.len() + 1,
        a.depths[0] == 0, b.depths[0] == 0,
        forall|i: int| 0 <= i < count ==> #[trigger] input_lexeme_valid(bytes, a, i),
        forall|i: int| 0 <= i < count ==> #[trigger] input_lexeme_valid(bytes, b, i),
    ensures
        count > 0 ==> a.lexemes[count - 1] == b.lexemes[count - 1],
        a.depths[count] == b.depths[count],
    decreases count,
{
    if count > 0 {
        let i = count - 1;
        preceding_lexemes_agree(bytes, a, b, i);
        assert(input_lexeme_valid(bytes, a, i));
        assert(input_lexeme_valid(bytes, b, i));
        reveal(input_lexeme_valid);
        lexemes_agree(bytes, a.lexemes[i], b.lexemes[i]);
    }
}

proof fn rejected_prefix_cannot_be_shorter(
    bytes: Seq<u8>, a: InputDerivation, a_stop: int, a_separator: bool, a_depth: int, error: Error,
    b: InputDerivation, b_stop: int, b_separator: bool, b_depth: int,
)
    requires
        scanned_input_prefix(bytes, a, a_stop, a_separator, a_depth),
        scanned_input_prefix(bytes, b, b_stop, b_separator, b_depth),
        rejection_at(bytes, a_stop, a_separator, a_depth, error),
    ensures a.lexemes.len() >= b.lexemes.len(),
{
    reveal(scanned_input_prefix);
    let count = a.lexemes.len() as int;
    if count < b.lexemes.len() {
        preceding_lexemes_agree(bytes, a, b, count);
        assert(input_lexeme_valid(bytes, b, count));
        reveal(input_lexeme_valid);
        let next = b.lexemes[count];
        assert(next.start == a_stop);
        if error.kind is UnexpectedClose {
            let close = Lexeme { start: a_stop, end: error.span.end as int, kind: LexemeKind::Close };
            lexemes_agree(bytes, close, next);
            assert(b.depths[count + 1] == -1);
        } else if error.kind is UnclosedList {
            reveal(lexeme_at);
            assert(a_stop < bytes.len());
        } else if error.kind is MissingSeparator {
            assert(next.kind is Atom && count > 0 && b.lexemes[count - 1].kind is Atom);
        } else {
            assert(!lexeme_at(bytes, a_stop, next.end, next.kind));
        }
    }
}

proof fn bare_extents_agree(bytes: Seq<u8>, start: int, a_end: int, b_end: int)
    requires bare_atom_extent(bytes, start, a_end), bare_atom_extent(bytes, start, b_end),
    ensures a_end == b_end,
{
    reveal(bare_atom_extent);
    if a_end < b_end {
        assert(!bare_atom_delimiter(bytes[a_end]));
    }
    if b_end < a_end {
        assert(!bare_atom_delimiter(bytes[b_end]));
    }
}

/// 厳格解析の一方が余分な閉じ括弧、区切りの欠落、不正な裸のアトムのいずれかを報告した場合、
/// 同じ入力の他方でもエラー値が一致する。
pub proof fn strict_token_errors_agree(source: &str, left: Error, right: Error)
    requires strict_syntax_rejection(source, left), strict_syntax_rejection(source, right),
        structural_error_location(source, left), structural_error_location(source, right),
        left.kind is UnexpectedClose || left.kind is MissingSeparator || left.kind is InvalidAtom,
    ensures left == right,
{
    let bytes = source.spec_bytes();
    let (a, a_stop, a_separator, a_depth) = choose|prefix: InputDerivation, at: int, needs_separator: bool, depth: int|
        #[trigger] scanned_input_prefix(bytes, prefix, at, needs_separator, depth)
            && rejection_at(bytes, at, needs_separator, depth, left);
    let (b, b_stop, b_separator, b_depth) = choose|prefix: InputDerivation, at: int, needs_separator: bool, depth: int|
        #[trigger] scanned_input_prefix(bytes, prefix, at, needs_separator, depth)
            && rejection_at(bytes, at, needs_separator, depth, right);
    rejected_prefix_cannot_be_shorter(bytes, a, a_stop, a_separator, a_depth, left, b, b_stop, b_separator, b_depth);
    rejected_prefix_cannot_be_shorter(bytes, b, b_stop, b_separator, b_depth, right, a, a_stop, a_separator, a_depth);
    reveal(scanned_input_prefix);
    preceding_lexemes_agree(bytes, a, b, a.lexemes.len() as int);
    assert(a_stop == b_stop);
    assert(a_separator == b_separator);
    if left.kind is UnexpectedClose {
        assert(lexeme_at(bytes, a_stop, left.span.end as int, LexemeKind::Close));
        assert(right.kind is UnexpectedClose) by { reveal(lexeme_at); };
        reveal(lexeme_at);
    } else if left.kind is MissingSeparator {
        if right.kind is UnexpectedClose {
            assert(lexeme_at(bytes, a_stop, right.span.end as int, LexemeKind::Close));
            assert(LexemeKind::Close is Atom);
        }
        assert(right.kind is MissingSeparator);
    } else {
        assert(right.kind is InvalidAtom) by { reveal(bare_atom_extent); };
        bare_extents_agree(bytes, a_stop, left.span.end as int, right.span.end as int);
    }
}

} // verus!
