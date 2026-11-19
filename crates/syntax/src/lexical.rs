use super::{
    AtomKind, bare_atom_delimiter, bare_atom_extent, bare_atom_kind, quoted_atom, trivia_byte,
    trivia_extent,
};
use vstd::prelude::*;

verus! {

pub enum LexemeKind {
    Whitespace,
    Comment,
    Open,
    Close,
    Atom(AtomKind),
}

#[verifier::opaque]
pub open spec fn lexeme_at(bytes: Seq<u8>, start: int, end: int, kind: LexemeKind) -> bool {
    &&& 0 <= start < end <= bytes.len()
    &&& match kind {
        LexemeKind::Whitespace => trivia_extent(bytes, start, end, false),
        LexemeKind::Comment => trivia_extent(bytes, start, end, true),
        LexemeKind::Open => end == start + 1 && bytes[start] == 40,
        LexemeKind::Close => end == start + 1 && bytes[start] == 41,
        LexemeKind::Atom(AtomKind::String) => quoted_atom(bytes[start..end]),
        LexemeKind::Atom(kind) => bare_atom_extent(bytes, start, end)
            && bare_atom_kind(bytes[start..end]) == Some(kind),
    }
}

pub(super) proof fn lexical_extent_facts(bytes: Seq<u8>, start: int, end: int, kind: LexemeKind)
    requires lexeme_at(bytes, start, end, kind),
    ensures
        0 <= start < end <= bytes.len(),
        match kind {
            LexemeKind::Whitespace => trivia_byte(bytes[start], false),
            LexemeKind::Comment => bytes[start] == 59,
            LexemeKind::Open => bytes[start] == 40 && end == start + 1,
            LexemeKind::Close => bytes[start] == 41 && end == start + 1,
            LexemeKind::Atom(AtomKind::String) => bytes[start] == 34,
            LexemeKind::Atom(_) => !bare_atom_delimiter(bytes[start]),
        },
{
    reveal(lexeme_at);
    reveal(trivia_extent);
    reveal(bare_atom_extent);
    if kind == LexemeKind::Atom(AtomKind::String) {
        reveal(quoted_atom);
        assert(bytes[start..end][0] == bytes[start]);
    }
}

pub(super) proof fn raw_trivia_matches(
    bytes: Seq<u8>, start: int, actual: int, expected: int, kind: LexemeKind, comment: bool,
)
    requires
        trivia_extent(bytes, start, actual, comment),
        lexeme_at(bytes, start, expected, kind),
    ensures
        actual == expected,
        kind == if comment { LexemeKind::Comment } else { LexemeKind::Whitespace },
{
    lexical_extent_facts(bytes, start, expected, kind);
    reveal(trivia_extent);
    assert(if comment { bytes[start] == 59 } else { trivia_byte(bytes[start], false) });
    assert(kind == if comment { LexemeKind::Comment } else { LexemeKind::Whitespace });
    reveal(lexeme_at);
    if actual < expected {
        assert(trivia_byte(bytes[actual], comment));
        assert(!trivia_byte(bytes[actual], comment));
    }
    if expected < actual {
        assert(trivia_byte(bytes[expected], comment));
        assert(!trivia_byte(bytes[expected], comment));
    }
}

pub(super) proof fn raw_bare_matches(
    bytes: Seq<u8>, start: int, actual: int, expected: int, kind: LexemeKind,
) -> (atom: AtomKind)
    requires
        bare_atom_extent(bytes, start, actual),
        lexeme_at(bytes, start, expected, kind),
    ensures
        actual == expected,
        kind == LexemeKind::Atom(atom),
        bare_atom_kind(bytes[start..expected]) == Some(atom),
{
    lexical_extent_facts(bytes, start, expected, kind);
    reveal(bare_atom_extent);
    assert(!bare_atom_delimiter(bytes[start]));
    assert(kind is Atom && kind->Atom_0 != AtomKind::String);
    reveal(lexeme_at);
    if actual < expected {
        assert(bare_atom_delimiter(bytes[actual]));
        assert(!bare_atom_delimiter(bytes[actual]));
    }
    if expected < actual {
        assert(bare_atom_delimiter(bytes[expected]));
        assert(!bare_atom_delimiter(bytes[expected]));
    }
    kind->Atom_0
}

} // verus!
