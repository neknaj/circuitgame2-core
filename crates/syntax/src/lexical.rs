use super::{
    AtomKind, bare_atom_delimiter, bare_atom_extent, bare_atom_kind, quoted_atom, trivia_byte,
    trivia_extent,
};
use super::quoted_prefix::{
    initialize_quoted_prefixes, quoted_body, quoted_prefix_at, quoted_prefixes_viable,
};
use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;

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

pub ghost struct Lexeme {
    pub start: int,
    pub end: int,
    pub kind: LexemeKind,
}

// 両候補を同じエスケープ規則でたどると、先に閉じる引用符をもう一方の本文に含められない。
proof fn quoted_closes_agree(bytes: Seq<u8>, from: int, first: int, second: int)
    requires
        0 <= from <= first < bytes.len(),
        from <= second < bytes.len(),
        bytes[first] == 34, bytes[second] == 34,
        quoted_body(bytes, from, first), quoted_body(bytes, from, second),
    ensures first == second,
    decreases first - from,
{
    reveal(quoted_body);
    if from == first || from == second {
        assert(bytes[from] == 34);
        assert(super::boundary::stops(super::Boundary::StringSpecial, bytes[from]));
        assert(from == first && from == second);
    } else {
        let next = if bytes[from] == 92 { from + 2 } else { from + 1 };
        quoted_closes_agree(bytes, next, first, second);
    }
}

/// 同じ開始位置で字句規則を満たす字句は、種別と終了位置が一致する。
pub(super) proof fn lexemes_agree(bytes: Seq<u8>, a: Lexeme, b: Lexeme)
    requires
        a.start == b.start,
        lexeme_at(bytes, a.start, a.end, a.kind),
        lexeme_at(bytes, b.start, b.end, b.kind),
    ensures a == b,
{
    let start = a.start;
    lexical_extent_facts(bytes, start, a.end, a.kind);
    lexical_extent_facts(bytes, start, b.end, b.kind);
    reveal(lexeme_at);
    if a.kind is Whitespace || a.kind is Comment {
        raw_trivia_matches(bytes, start, a.end, b.end, b.kind, a.kind is Comment);
    } else if a.kind is Open || a.kind is Close {
        assert(a.kind == b.kind);
    } else if a.kind == LexemeKind::Atom(AtomKind::String) {
        assert(b.kind == a.kind);
        let remaining = bytes[start..];
        let first = a.end - start - 1;
        let second = b.end - start - 1;
        reveal(quoted_prefix_at);
        reveal(quoted_atom);
        assert(remaining[..first + 1] =~= bytes[start..a.end]);
        assert(remaining[..second + 1] =~= bytes[start..b.end]);
        assert(quoted_prefix_at(remaining, first));
        assert(quoted_prefix_at(remaining, second));
        initialize_quoted_prefixes(remaining);
        reveal(quoted_prefixes_viable);
        quoted_closes_agree(remaining, 1, first, second);
    } else {
        raw_bare_matches(bytes, start, a.end, b.end, b.kind);
    }
}

pub ghost struct InputDerivation {
    pub lexemes: Seq<Lexeme>,
    pub depths: Seq<int>,
}

pub open spec fn parenthesis_delta(kind: LexemeKind) -> int {
    match kind {
        LexemeKind::Open => 1,
        LexemeKind::Close => -1,
        _ => 0,
    }
}

#[verifier::opaque]
pub open spec fn input_lexeme_valid(bytes: Seq<u8>, witness: InputDerivation, i: int) -> bool {
    let lexeme = witness.lexemes[i];
    &&& lexeme_at(bytes, lexeme.start, lexeme.end, lexeme.kind)
    &&& lexeme.start == if i == 0 { 0 } else { witness.lexemes[i - 1].end }
    &&& (i > 0 && lexeme.kind is Atom ==> !(witness.lexemes[i - 1].kind is Atom))
    &&& witness.depths[i + 1] == witness.depths[i] + parenthesis_delta(lexeme.kind)
    &&& witness.depths[i + 1] >= 0
}

#[verifier::opaque]
pub open spec fn sexpr_input_derivation(bytes: Seq<u8>, witness: InputDerivation) -> bool {
    let lexemes = witness.lexemes;
    let depths = witness.depths;
    &&& depths.len() == lexemes.len() + 1
    &&& depths[0] == 0
    &&& depths[lexemes.len() as int] == 0
    &&& (lexemes.len() == 0 ==> bytes.len() == 0)
    &&& (lexemes.len() > 0 ==> lexemes[lexemes.len() - 1].end == bytes.len())
    &&& forall|i: int| 0 <= i < lexemes.len() ==> #[trigger] input_lexeme_valid(bytes, witness, i)
}

/// 括弧と字句の規則に従う導出が存在することを表す。
#[verifier::opaque]
pub open spec fn well_formed_sexpr_bytes(bytes: Seq<u8>) -> bool {
    exists|witness: InputDerivation| #[trigger] sexpr_input_derivation(bytes, witness)
}

#[verifier::opaque]
pub open spec fn well_formed_sexpr(source: &str) -> bool {
    well_formed_sexpr_bytes(source.spec_bytes())
}

/// バイト列から、字句と括弧の規則に従う導出を選ぶ。
#[verifier::opaque]
pub open spec fn chosen_input_derivation_bytes(bytes: Seq<u8>) -> Option<InputDerivation> {
    if well_formed_sexpr_bytes(bytes) {
        Some(choose|witness: InputDerivation| #[trigger] sexpr_input_derivation(bytes, witness))
    } else {
        None
    }
}

#[verifier::opaque]
pub open spec fn chosen_input_derivation(source: &str) -> Option<InputDerivation> {
    chosen_input_derivation_bytes(source.spec_bytes())
}

pub(super) proof fn choose_input_derivation(source: &str) -> (witness: Option<InputDerivation>)
    ensures
        witness == chosen_input_derivation(source),
        witness.is_some() == well_formed_sexpr(source),
        witness is Some ==> sexpr_input_derivation(source.spec_bytes(), witness->Some_0),
{
    reveal(well_formed_sexpr);
    reveal(well_formed_sexpr_bytes);
    reveal(chosen_input_derivation);
    reveal(chosen_input_derivation_bytes);
    chosen_input_derivation(source)
}

#[verifier::opaque]
pub(super) open spec fn input_progress(
    bytes: Seq<u8>, witness: InputDerivation, i: int, position: int, needs_separator: bool, depth: int,
) -> bool {
    let lexemes = witness.lexemes;
    &&& sexpr_input_derivation(bytes, witness)
    &&& 0 <= i <= lexemes.len()
    &&& position == if i < lexemes.len() { lexemes[i].start } else { bytes.len() as int }
    &&& needs_separator == (i > 0 && lexemes[i - 1].kind is Atom)
    &&& depth == witness.depths[i]
}

pub(super) proof fn input_starts(bytes: Seq<u8>, witness: InputDerivation)
    requires sexpr_input_derivation(bytes, witness),
    ensures input_progress(bytes, witness, 0, 0, false, 0),
{
    reveal(input_progress);
    reveal(sexpr_input_derivation);
    if witness.lexemes.len() == 0 {
        assert(bytes.len() == 0);
    } else {
        assert(input_lexeme_valid(bytes, witness, 0));
        reveal(input_lexeme_valid);
        assert(witness.lexemes[0].start == 0);
    }
}

pub(super) proof fn input_ends(
    bytes: Seq<u8>, witness: InputDerivation, i: int, needs_separator: bool, depth: int,
)
    requires input_progress(bytes, witness, i, bytes.len() as int, needs_separator, depth),
    ensures depth == 0, i == witness.lexemes.len(),
{
    reveal(input_progress);
    reveal(sexpr_input_derivation);
    if i < witness.lexemes.len() {
        let lexeme = witness.lexemes[i];
        assert(input_lexeme_valid(bytes, witness, i));
        reveal(input_lexeme_valid);
        assert(lexeme_at(bytes, lexeme.start, lexeme.end, lexeme.kind));
        reveal(lexeme_at);
    }
}

pub(super) proof fn input_next(
    bytes: Seq<u8>, witness: InputDerivation, i: int, position: int, needs_separator: bool, depth: int,
) -> (lexeme: Lexeme)
    requires
        input_progress(bytes, witness, i, position, needs_separator, depth),
        position < bytes.len(),
    ensures
        0 <= i < witness.lexemes.len(),
        lexeme == witness.lexemes[i],
        lexeme.start == position,
        lexeme_at(bytes, lexeme.start, lexeme.end, lexeme.kind),
        !(needs_separator && lexeme.kind is Atom),
        lexeme.kind is Close ==> depth > 0,
        input_progress(bytes, witness, i + 1, lexeme.end, lexeme.kind is Atom,
            depth + parenthesis_delta(lexeme.kind)),
{
    reveal(input_progress);
    reveal(sexpr_input_derivation);
    let lexeme = witness.lexemes[i];
    assert(input_lexeme_valid(bytes, witness, i));
    reveal(input_lexeme_valid);
    if i + 1 < witness.lexemes.len() {
        assert(input_lexeme_valid(bytes, witness, i + 1));
        assert(witness.lexemes[i + 1].start == lexeme.end);
    } else {
        assert(lexeme.end == bytes.len());
    }
    lexeme
}

#[verifier::opaque]
pub(super) open spec fn scanned_input_prefix(
    bytes: Seq<u8>, prefix: InputDerivation, position: int, needs_separator: bool, depth: int,
) -> bool {
    let count = prefix.lexemes.len() as int;
    &&& prefix.depths.len() == count + 1
    &&& prefix.depths[0] == 0
    &&& prefix.depths[count] == depth
    &&& position == if count == 0 { 0 } else { prefix.lexemes[count - 1].end }
    &&& needs_separator == (count > 0 && prefix.lexemes[count - 1].kind is Atom)
    &&& forall|i: int| 0 <= i < count ==> #[trigger] input_lexeme_valid(bytes, prefix, i)
}

pub(super) proof fn empty_scanned_input(bytes: Seq<u8>) -> (prefix: InputDerivation)
    ensures scanned_input_prefix(bytes, prefix, 0, false, 0), prefix.lexemes.len() == 0,
{
    reveal(scanned_input_prefix);
    InputDerivation { lexemes: Seq::empty(), depths: seq![0int] }
}

pub(super) proof fn record_scanned_input(
    bytes: Seq<u8>, prefix: InputDerivation, lexeme: Lexeme, needed_separator: bool, old_depth: int,
) -> (next: InputDerivation)
    requires
        scanned_input_prefix(bytes, prefix, lexeme.start, needed_separator, old_depth),
        lexeme_at(bytes, lexeme.start, lexeme.end, lexeme.kind),
        !(needed_separator && lexeme.kind is Atom),
        0 <= old_depth + parenthesis_delta(lexeme.kind),
    ensures
        scanned_input_prefix(bytes, next, lexeme.end, lexeme.kind is Atom,
            old_depth + parenthesis_delta(lexeme.kind)),
        next.lexemes == prefix.lexemes.push(lexeme),
{
    reveal(scanned_input_prefix);
    let count = prefix.lexemes.len() as int;
    let new_depth = old_depth + parenthesis_delta(lexeme.kind);
    let next = InputDerivation { lexemes: prefix.lexemes.push(lexeme), depths: prefix.depths.push(new_depth) };
    assert forall|i: int| 0 <= i < next.lexemes.len()
        implies #[trigger] input_lexeme_valid(bytes, next, i) by {
        if i < count {
            assert(input_lexeme_valid(bytes, prefix, i));
            assert(next.lexemes[i] == prefix.lexemes[i]);
            if i > 0 {
                assert(next.lexemes[i - 1] == prefix.lexemes[i - 1]);
            }
            assert(next.depths[i] == prefix.depths[i] && next.depths[i + 1] == prefix.depths[i + 1]);
            reveal(input_lexeme_valid);
        } else {
            reveal(input_lexeme_valid);
        }
    };
    next
}

pub(super) proof fn seal_scanned_input(source: &str, prefix: InputDerivation, needs_separator: bool)
    requires scanned_input_prefix(source.spec_bytes(), prefix,
        source.spec_bytes().len() as int, needs_separator, 0),
    ensures well_formed_sexpr(source),
{
    reveal(scanned_input_prefix);
    reveal(sexpr_input_derivation);
    reveal(well_formed_sexpr);
    reveal(well_formed_sexpr_bytes);
    assert(sexpr_input_derivation(source.spec_bytes(), prefix));
}

} // verus!
