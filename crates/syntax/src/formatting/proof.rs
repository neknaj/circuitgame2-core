//! 整形済みの字句導出を構成し、表記の保存と冪等性を示す。

use super::*;
use crate::{Lexeme, bare_atom_delimiter, bare_atom_extent, lexeme_at, quoted_atom, trivia_byte, trivia_extent};
use crate::lexical::{
    chosen_input_derivation_bytes, empty_scanned_input, input_lexeme_valid, lexemes_agree,
    parenthesis_delta, record_scanned_input, scanned_input_prefix, sexpr_input_derivation, well_formed_sexpr_bytes,
};

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::seq_lib::group_seq_properties};

proof fn take_index<T>(left: Seq<T>, right: Seq<T>, count: int, index: int)
    requires 0 <= index < count <= left.len(), count <= right.len(),
        left.take(count) == right.take(count),
    ensures left[index] == right[index],
{
    vstd::seq_lib::lemma_seq_take_index(left, count, index);
    vstd::seq_lib::lemma_seq_take_index(right, count, index);
    assert(left.take(count)[index] == right.take(count)[index]);
}

// 既存区間より後ろに文字を足す場合、末尾字句の停止条件だけを確認する。
proof fn retain_lexeme(before: Seq<u8>, after: Seq<u8>, piece: Lexeme)
    requires
        before.len() <= after.len(), before == after.take(before.len() as int),
        lexeme_at(before, piece.start, piece.end, piece.kind),
        piece.end == before.len() < after.len() ==> match piece.kind {
            LexemeKind::Atom(kind) => kind == crate::AtomKind::String || bare_atom_delimiter(after[piece.end]),
            LexemeKind::Comment => !trivia_byte(after[piece.end], true),
            LexemeKind::Whitespace => !trivia_byte(after[piece.end], false),
            _ => true,
        },
    ensures lexeme_at(after, piece.start, piece.end, piece.kind),
{
    reveal(lexeme_at);
    reveal(trivia_extent);
    reveal(bare_atom_extent);
    assert(before.take(before.len() as int) =~= before);
    vstd::seq_lib::subrange_of_matching_take(before, after, piece.start, piece.end, before.len() as int);
    if piece.end < before.len() {
        take_index(before, after, before.len() as int, piece.end);
    }
    assert forall|i: int| piece.start <= i < piece.end implies #[trigger] after[i] == before[i] by {
        take_index(before, after, before.len() as int, i);
    };
    if piece.kind is Comment || piece.kind is Whitespace {
        let comment = piece.kind is Comment;
        assert(after[piece.start] == before[piece.start]);
        assert forall|i: int| piece.start <= i < piece.end
            implies trivia_byte(#[trigger] after[i], comment) by {
            assert(after[i] == before[i]);
        };
        assert(trivia_extent(after, piece.start, piece.end, comment));
    } else if piece.kind is Atom && piece.kind->Atom_0 != crate::AtomKind::String {
        assert forall|i: int| piece.start <= i < piece.end
            implies !bare_atom_delimiter(#[trigger] after[i]) by {
            assert(after[i] == before[i]);
        };
        assert(bare_atom_extent(after, piece.start, piece.end));
    } else if piece.kind is Open || piece.kind is Close {
        assert(after[piece.start] == before[piece.start]);
    }
}

proof fn retain_prefix(before: Seq<u8>, after: Seq<u8>, prefix: InputDerivation, depth: int, atom: bool)
    requires
        before.len() <= after.len(), before == after.take(before.len() as int),
        scanned_input_prefix(before, prefix, before.len() as int, atom, depth),
        prefix.lexemes.len() > 0 && before.len() < after.len() ==> {
            let end = before.len() as int;
            match prefix.lexemes.last().kind {
                LexemeKind::Atom(kind) => kind == crate::AtomKind::String || bare_atom_delimiter(after[end]),
                LexemeKind::Comment => !trivia_byte(after[end], true),
                LexemeKind::Whitespace => !trivia_byte(after[end], false),
                _ => true,
            }
        },
    ensures scanned_input_prefix(after, prefix, before.len() as int, atom, depth),
{
    reveal(scanned_input_prefix);
    assert forall|i: int| 0 <= i < prefix.lexemes.len()
        implies #[trigger] input_lexeme_valid(after, prefix, i) by {
        assert(input_lexeme_valid(before, prefix, i));
        reveal(input_lexeme_valid);
        let piece = prefix.lexemes[i];
        if i + 1 < prefix.lexemes.len() {
            assert(input_lexeme_valid(before, prefix, i + 1));
            lexical::lexical_extent_facts(before, prefix.lexemes[i + 1].start, prefix.lexemes[i + 1].end,
                prefix.lexemes[i + 1].kind);
            assert(piece.end < before.len());
        }
        retain_lexeme(before, after, piece);
    };
}

proof fn copy_lexeme_at_end(original: Seq<u8>, piece: Lexeme, output: Seq<u8>, start: int) -> (placed: Lexeme)
    requires
        !(piece.kind is Whitespace), 0 <= piece.start < piece.end <= original.len(),
        lexeme_at(original, piece.start, piece.end, piece.kind),
        0 <= start < output.len(),
        output[start..] == original[piece.start..piece.end],
    ensures
        placed == (Lexeme { start, end: output.len() as int, kind: piece.kind }),
        lexeme_at(output, placed.start, placed.end, placed.kind),
{
    reveal(lexeme_at);
    reveal(trivia_extent);
    reveal(bare_atom_extent);
    assert(output[start..].len() == output.len() - start) by {
        vstd::seq_lib::lemma_seq_skip_len(output, start);
    };
    assert(original[piece.start..piece.end].len() == piece.end - piece.start) by {
        vstd::seq::lemma_seq_subrange_len(original, piece.start, piece.end);
    };
    assert(output.len() - start == piece.end - piece.start);
    assert forall|i: int| start <= i < output.len()
        implies #[trigger] output[i] == original[piece.start + (i - start)] by {
        let offset = i - start;
        assert(0 <= offset < piece.end - piece.start);
        assert(output[start..][offset] == output[i]);
        assert(original[piece.start..piece.end][offset] == original[piece.start + offset]);
        assert(output[start..][offset] == original[piece.start..piece.end][offset]);
    };
    if piece.kind is Comment {
        assert(output[start] == b';');
        assert forall|i: int| start <= i < output.len() implies trivia_byte(#[trigger] output[i], true) by {
            let source = piece.start + (i - start);
            assert(piece.start <= source < piece.end);
            assert(output[i] == original[source]);
            assert(trivia_byte(original[source], true));
        };
        assert(trivia_extent(output, start, output.len() as int, true));
    } else if piece.kind is Atom && piece.kind->Atom_0 != crate::AtomKind::String {
        assert forall|i: int| start <= i < output.len() implies !bare_atom_delimiter(#[trigger] output[i]) by {
            let source = piece.start + (i - start);
            assert(piece.start <= source < piece.end);
            assert(output[i] == original[source]);
            assert(!bare_atom_delimiter(original[source]));
        };
        assert(bare_atom_extent(output, start, output.len() as int));
    } else if piece.kind is Open || piece.kind is Close {
        assert(output.len() == start + 1);
        assert(output[start] == original[piece.start]);
    }
    Lexeme { start, end: output.len() as int, kind: piece.kind }
}

proof fn gap_facts(gap: Gap, kind: Piece, depth: int)
    ensures {
        let bytes = gap_bytes(gap, kind, depth);
        &&& bytes.len() == 0 <==> gap == Gap::Empty
        &&& forall|i: int| 0 <= i < bytes.len() ==> trivia_byte(#[trigger] bytes[i], false)
        &&& gap == Gap::Line ==> bytes[0] == b'\n'
        &&& has_break(bytes) == (gap == Gap::Line)
    },
{
    let bytes = gap_bytes(gap, kind, depth);
    assert forall|i: int| 0 <= i < bytes.len() implies
        (#[trigger] bytes[i]) == b' ' || (gap == Gap::Line && i == 0 && bytes[i] == b'\n') by {};
}

proof fn append_piece(
    original: Seq<u8>, piece: Lexeme, depth: int, before: Seq<u8>, prefix: InputDerivation, line: bool,
) -> (next: InputDerivation)
    requires
        lexeme_at(original, piece.start, piece.end, piece.kind), !(piece.kind is Whitespace),
        0 <= depth, 0 <= depth + parenthesis_delta(piece.kind),
        scanned_input_prefix(before, prefix, before.len() as int, prefix.lexemes.len() > 0 && prefix.lexemes.last().kind is Atom, depth),
        prefix.lexemes.len() > 0 ==> !(prefix.lexemes.last().kind is Whitespace),
    ensures {
        let prev = if prefix.lexemes.len() == 0 { None } else { Some(piece_kind(prefix.lexemes.last().kind)) };
        let gap = gap_bytes(gap_layout(prev, piece_kind(piece.kind), line, depth), piece_kind(piece.kind), depth);
        let next_bytes = before + gap + original[piece.start..piece.end];
        let placed = Lexeme { start: (before.len() + gap.len()) as int, end: next_bytes.len() as int, kind: piece.kind };
        let whitespace = Lexeme { start: before.len() as int, end: placed.start, kind: LexemeKind::Whitespace };
        &&& next.lexemes == (if gap.len() == 0 { prefix.lexemes } else { prefix.lexemes.push(whitespace) }).push(placed)
        &&& next.depths == (if gap.len() == 0 { prefix.depths } else { prefix.depths.push(depth) })
            .push(depth + parenthesis_delta(placed.kind))
        &&& scanned_input_prefix(next_bytes, next, next_bytes.len() as int, placed.kind is Atom,
            depth + parenthesis_delta(placed.kind))
    },
{
    let kind = piece_kind(piece.kind);
    let prev = if prefix.lexemes.len() == 0 { None } else { Some(piece_kind(prefix.lexemes.last().kind)) };
    let layout = gap_layout(prev, kind, line, depth);
    let gap = gap_bytes(layout, kind, depth);
    let rest = original[piece.start..piece.end];
    let output = before + gap + rest;
    let boundary = before.len() as int;
    let start = boundary + gap.len();
    lexical::lexical_extent_facts(original, piece.start, piece.end, piece.kind);
    assert(output[start..] =~= rest);
    let placed = copy_lexeme_at_end(original, piece, output, start);
    lexical::lexical_extent_facts(output, placed.start, placed.end, placed.kind);
    gap_facts(layout, kind, depth);
    assert(before =~= output.take(boundary));
    if gap.len() > 0 {
        assert(output[boundary] == gap[0]);
        if prev == Some(Piece::Comment) {
            assert(layout == Gap::Line && !trivia_byte(output[boundary], true));
        }
        assert(bare_atom_delimiter(output[boundary]));
        retain_prefix(before, output, prefix, depth, prefix.lexemes.len() > 0 && prefix.lexemes.last().kind is Atom);
        let whitespace = Lexeme { start: boundary, end: start, kind: LexemeKind::Whitespace };
        assert(lexeme_at(output, boundary, start, LexemeKind::Whitespace)) by {
            reveal(lexeme_at);
            reveal(trivia_extent);
            assert(!trivia_byte(output[start], false));
            assert(output[boundary..start] =~= gap);
        };
        let separated = record_scanned_input(output, prefix, whitespace,
            prefix.lexemes.len() > 0 && prefix.lexemes.last().kind is Atom, depth);
        record_scanned_input(output, separated, placed, false, depth)
    } else {
        assert(prev is None || prev == Some(Piece::Open) || kind == Piece::Close);
        assert(!(prefix.lexemes.len() > 0 && prefix.lexemes.last().kind is Atom && placed.kind is Atom));
        retain_prefix(before, output, prefix, depth, prefix.lexemes.len() > 0 && prefix.lexemes.last().kind is Atom);
        record_scanned_input(output, prefix, placed, prefix.lexemes.len() > 0 && prefix.lexemes.last().kind is Atom, depth)
    }
}

spec fn spelling(bytes: Seq<u8>, lexemes: Seq<Lexeme>, count: int) -> Seq<(LexemeKind, Seq<u8>)>
    decreases count,
{
    if count <= 0 {
        Seq::empty()
    } else {
        let previous = spelling(bytes, lexemes, count - 1);
        let current = lexemes[count - 1];
        if current.kind is Whitespace { previous }
        else { previous.push((current.kind, bytes[current.start..current.end])) }
    }
}

pub(super) closed spec fn formatting_lexemes_bytes(bytes: Seq<u8>) -> Option<Seq<(LexemeKind, Seq<u8>)>> {
    match chosen_input_derivation_bytes(bytes) {
        Some(input) => Some(spelling(bytes, input.lexemes, input.lexemes.len() as int)),
        None => None,
    }
}

proof fn same_previous(left: InputDerivation, right: InputDerivation, count: int)
    requires
        0 <= count <= left.lexemes.len(), count <= right.lexemes.len(),
        left.lexemes.take(count) == right.lexemes.take(count),
    ensures
        previous_piece(left, count) == previous_piece(right, count),
        previous_kind(left, count) == previous_kind(right, count),
        previous_end(left, count) == previous_end(right, count),
        previous_piece(left, count) matches Some(i) ==> 0 <= i < count,
    decreases count,
{
    if count > 0 && left.lexemes[count - 1].kind is Whitespace {
        take_index(left.lexemes, right.lexemes, count, count - 1);
        assert(left.lexemes.take(count - 1) =~= right.lexemes.take(count - 1));
        same_previous(left, right, count - 1);
    }
    if count > 0 && !(left.lexemes[count - 1].kind is Whitespace) {
        take_index(left.lexemes, right.lexemes, count, count - 1);
    }
    if let Some(i) = previous_piece(left, count) {
        take_index(left.lexemes, right.lexemes, count, i);
    }
}

// 接頭辞内で使う字句・深さ・空白の範囲が同じなら、後ろを足しても整形済み接頭辞は変わらない。
proof fn prefix_unchanged(before: Seq<u8>, after: Seq<u8>, left: InputDerivation, right: InputDerivation, count: int)
    requires
        0 <= count <= left.lexemes.len(), count <= right.lexemes.len(),
        left.lexemes.take(count) == right.lexemes.take(count),
        left.depths.take(count) == right.depths.take(count),
        count <= left.depths.len(), count <= right.depths.len(),
        before.len() <= after.len(), before == after.take(before.len() as int),
        forall|i: int| 0 <= i < count ==> 0 <= (#[trigger] left.lexemes[i]).start <= left.lexemes[i].end <= before.len(),
        forall|i: int| 0 <= i < count ==> 0 <= #[trigger] previous_end(left, i) <= left.lexemes[i].start,
    ensures
        formatted_prefix(before, left, count) == formatted_prefix(after, right, count),
        spelling(before, left.lexemes, count) == spelling(after, right.lexemes, count),
    decreases count,
{
    reveal(formatted_prefix);
    if count > 0 {
        let index = count - 1;
        assert(left.lexemes.take(index) =~= right.lexemes.take(index));
        assert(left.depths.take(index) =~= right.depths.take(index));
        prefix_unchanged(before, after, left, right, index);
        same_previous(left, right, index);
        take_index(left.lexemes, right.lexemes, count, index);
        take_index(left.depths, right.depths, count, index);
        let piece = left.lexemes[index];
        assert(before.take(before.len() as int) =~= before);
        vstd::seq_lib::subrange_of_matching_take(before, after, piece.start, piece.end, before.len() as int);
        vstd::seq_lib::subrange_of_matching_take(before, after, previous_end(left, index), piece.start, before.len() as int);
    }
}

proof fn prefix_piece_ranges(bytes: Seq<u8>, prefix: InputDerivation, depth: int, atom: bool)
    requires scanned_input_prefix(bytes, prefix, bytes.len() as int, atom, depth),
    ensures
        prefix.depths.len() == prefix.lexemes.len() + 1,
        prefix.depths.last() == depth,
        forall|i: int| 0 <= i < prefix.lexemes.len() ==>
            0 <= (#[trigger] prefix.lexemes[i]).start < prefix.lexemes[i].end <= bytes.len(),
        forall|i: int| 0 <= i < prefix.lexemes.len() ==>
            0 <= #[trigger] previous_end(prefix, i) <= prefix.lexemes[i].start,
{
    reveal(scanned_input_prefix);
    assert forall|i: int| 0 <= i < prefix.lexemes.len() implies
        0 <= (#[trigger] prefix.lexemes[i]).start < prefix.lexemes[i].end <= bytes.len() by {
        assert(input_lexeme_valid(bytes, prefix, i));
        reveal(input_lexeme_valid);
        let p = prefix.lexemes[i];
        lexical::lexical_extent_facts(bytes, p.start, p.end, p.kind);
    };
    assert forall|i: int| 0 <= i < prefix.lexemes.len() implies
        0 <= #[trigger] previous_end(prefix, i) <= prefix.lexemes[i].start by {
        if let Some(prev) = previous_piece(prefix, i) {
            assert(0 <= prev < i) by { same_previous(prefix, prefix, i); };
            earlier_piece_ends_before(bytes, prefix, prev, i);
        }
    };
}

proof fn earlier_piece_ends_before(bytes: Seq<u8>, prefix: InputDerivation, earlier: int, later: int)
    requires
        0 <= earlier < later < prefix.lexemes.len(),
        forall|i: int| 0 <= i < prefix.lexemes.len() ==> #[trigger] input_lexeme_valid(bytes, prefix, i),
    ensures prefix.lexemes[earlier].end <= prefix.lexemes[later].start,
    decreases later - earlier,
{
    assert(input_lexeme_valid(bytes, prefix, later));
    reveal(input_lexeme_valid);
    if later > earlier + 1 {
        earlier_piece_ends_before(bytes, prefix, earlier, later - 1);
        assert(input_lexeme_valid(bytes, prefix, later - 1));
        lexical::lexical_extent_facts(bytes, prefix.lexemes[later - 1].start,
            prefix.lexemes[later - 1].end, prefix.lexemes[later - 1].kind);
    }
}

proof fn normalized_gap_repeats(previous: Option<Piece>, current: Piece, old_break: bool, depth: int)
    ensures {
        let gap = gap_layout(previous, current, old_break, depth);
        gap_layout(previous, current, has_break(gap_bytes(gap, current, depth)), depth) == gap
    },
{
    gap_facts(gap_layout(previous, current, old_break, depth), current, depth);
}

// 原文の先頭から字句を一つずつ加え、整形済み接頭辞にも同じ字句導出が存在することを示す。
#[verifier::rlimit(45)]
proof fn derive_formatted_prefix(original: Seq<u8>, input: InputDerivation, count: int) -> (made: InputDerivation)
    requires
        sexpr_input_derivation(original, input),
        0 <= count <= input.lexemes.len(),
    ensures {
        let bytes = formatted_prefix(original, input, count);
        let n = made.lexemes.len() as int;
        &&& scanned_input_prefix(bytes, made, bytes.len() as int, n > 0 && made.lexemes.last().kind is Atom,
            input.depths[count])
        &&& (n > 0 ==> !(made.lexemes.last().kind is Whitespace))
        &&& previous_kind(input, count) == previous_kind(made, n)
        &&& spelling(original, input.lexemes, count) == spelling(bytes, made.lexemes, n)
        &&& formatted_prefix(bytes, made, n) == bytes
    },
    decreases count,
{
    reveal(formatted_prefix);
    if count == 0 {
        reveal(sexpr_input_derivation);
        return empty_scanned_input(Seq::empty());
    }
    let index = count - 1;
    let piece = input.lexemes[index];
    assert(input_lexeme_valid(original, input, index)) by { reveal(sexpr_input_derivation); };
    assert(input.depths[index] >= 0) by {
        reveal(sexpr_input_derivation);
        reveal(input_lexeme_valid);
        if index > 0 { assert(input_lexeme_valid(original, input, index - 1)); }
    };
    reveal(input_lexeme_valid);
    let previous = derive_formatted_prefix(original, input, index);
    if piece.kind is Whitespace {
        return previous;
    }
    let depth = input.depths[index];
    let kind = piece_kind(piece.kind);
    let before = formatted_prefix(original, input, index);
    let old_count = previous.lexemes.len() as int;
    let prev = previous_kind(input, index);
    let old_break = has_break(original[previous_end(input, index)..piece.start]);
    let layout = gap_layout(prev, kind, old_break, depth);
    let gap = gap_bytes(layout, kind, depth);
    let after = before + gap + original[piece.start..piece.end];
    assert(if old_count == 0 { prev is None } else { prev == Some(piece_kind(previous.lexemes.last().kind)) });
    let result = append_piece(original, piece, depth, before, previous, old_break);
    let prior = (result.lexemes.len() - 1) as int;
    let last = result.lexemes[prior];
    let info = previous.lexemes.len() > 0 && previous.lexemes.last().kind is Atom;
    prefix_piece_ranges(before, previous, depth, info);
    prefix_piece_ranges(after, result, input.depths[count], last.kind is Atom);
    reveal(scanned_input_prefix);
    assert(result.lexemes.take(old_count) =~= previous.lexemes);
    assert(result.depths.take(old_count) =~= previous.depths.take(old_count));
    assert(before =~= after.take(before.len() as int));
    prefix_unchanged(before, after, previous, result, old_count);
    assert(formatted_prefix(after, result, prior) == before);
    assert(spelling(after, result.lexemes, prior) == spelling(before, previous.lexemes, old_count));
    same_previous(previous, result, old_count);
    assert(previous_kind(result, prior) == prev);
    assert(previous_end(result, prior) == before.len());
    assert(after[before.len() as int..last.start] =~= gap);
    normalized_gap_repeats(prev, kind, old_break, depth);
    assert(result.depths[prior] == depth);
    assert(formatted_gap(after, result, prior) == gap);
    assert(after[last.start..last.end] =~= original[piece.start..piece.end]);
    result
}

proof fn same_prefix_depths(left: InputDerivation, right: InputDerivation, count: int)
    requires
        0 <= count <= left.lexemes.len(), count <= right.lexemes.len(),
        left.depths.len() == left.lexemes.len() + 1, right.depths.len() == right.lexemes.len() + 1,
        left.depths[0] == 0, right.depths[0] == 0,
        left.lexemes.take(count) == right.lexemes.take(count),
        forall|i: int| 0 <= i < count ==> #[trigger] left.depths[i + 1] == left.depths[i] + parenthesis_delta(left.lexemes[i].kind),
        forall|i: int| 0 <= i < count ==> #[trigger] right.depths[i + 1] == right.depths[i] + parenthesis_delta(right.lexemes[i].kind),
    ensures
        left.depths[count] == right.depths[count],
        left.depths.take(count) == right.depths.take(count),
    decreases count,
{
    if count > 0 {
        assert(left.lexemes.take(count - 1) =~= right.lexemes.take(count - 1));
        same_prefix_depths(left, right, count - 1);
        take_index(left.lexemes, right.lexemes, count, count - 1);
        assert(left.depths[(count - 1) + 1] == left.depths[count - 1] + parenthesis_delta(left.lexemes[count - 1].kind));
        assert(left.depths[count] == left.depths[count - 1] + parenthesis_delta(left.lexemes[count - 1].kind));
        assert(right.depths[count] == right.depths[count - 1] + parenthesis_delta(right.lexemes[count - 1].kind));
        assert(left.depths.take(count) =~= right.depths.take(count));
    }
}

proof fn unique_prefix(bytes: Seq<u8>, left: InputDerivation, right: InputDerivation, count: int)
    requires
        sexpr_input_derivation(bytes, left), sexpr_input_derivation(bytes, right),
        0 <= count <= left.lexemes.len(), count <= right.lexemes.len(),
    ensures left.lexemes.take(count) == right.lexemes.take(count),
    decreases count,
{
    if count > 0 {
        let i = count - 1;
        unique_prefix(bytes, left, right, i);
        reveal(sexpr_input_derivation);
        assert(input_lexeme_valid(bytes, left, i) && input_lexeme_valid(bytes, right, i));
        reveal(input_lexeme_valid);
        if i > 0 { take_index(left.lexemes, right.lexemes, i, i - 1); }
        lexemes_agree(bytes, left.lexemes[i], right.lexemes[i]);
        assert(left.lexemes.take(count) =~= right.lexemes.take(count));
    }
}

proof fn derivations_agree(bytes: Seq<u8>, left: InputDerivation, right: InputDerivation)
    requires sexpr_input_derivation(bytes, left), sexpr_input_derivation(bytes, right),
    ensures left == right,
{
    let n = if left.lexemes.len() < right.lexemes.len() { left.lexemes.len() } else { right.lexemes.len() } as int;
    unique_prefix(bytes, left, right, n);
    reveal(sexpr_input_derivation);
    if n < right.lexemes.len() {
        assert(input_lexeme_valid(bytes, right, n));
        reveal(input_lexeme_valid);
        let current = right.lexemes[n];
        lexical::lexical_extent_facts(bytes, current.start, current.end, current.kind);
        assert(false);
    }
    if n < left.lexemes.len() {
        assert(input_lexeme_valid(bytes, left, n));
        reveal(input_lexeme_valid);
        let current = left.lexemes[n];
        lexical::lexical_extent_facts(bytes, current.start, current.end, current.kind);
        assert(false);
    }
    assert(left.lexemes =~= right.lexemes);
    assert forall|i: int| 0 <= i < n implies
        #[trigger] left.depths[i + 1] == left.depths[i] + parenthesis_delta(left.lexemes[i].kind) by {
        assert(input_lexeme_valid(bytes, left, i));
        reveal(input_lexeme_valid);
    };
    assert forall|i: int| 0 <= i < n implies
        #[trigger] right.depths[i + 1] == right.depths[i] + parenthesis_delta(right.lexemes[i].kind) by {
        assert(input_lexeme_valid(bytes, right, i));
        reveal(input_lexeme_valid);
    };
    same_prefix_depths(left, right, n);
    assert forall|i: int| 0 <= i < left.depths.len()
        implies (#[trigger] left.depths[i]) == right.depths[i] by {
        if i < n { take_index(left.depths, right.depths, n, i); }
        else { assert(i == n); }
    };
    assert(left.depths =~= right.depths);
}

pub(super) proof fn formatting_is_stable(source: &str, output: Seq<u8>)
    requires formatted_bytes(source) == Some(output),
    ensures formatted_preserves(source, output),
{
    let original = source.spec_bytes();
    let selected = lexical::choose_input_derivation(source);
    let input = selected->Some_0;
    reveal(lexical::chosen_input_derivation);
    let count = input.lexemes.len() as int;
    let prefix = derive_formatted_prefix(original, input, count);
    let n = prefix.lexemes.len() as int;
    let before = formatted_prefix(original, input, count);
    reveal(sexpr_input_derivation);
    reveal(scanned_input_prefix);
    let complete = if n == 0 {
        assert(previous_kind(input, count) is None);
        assert(before == Seq::<u8>::empty());
        prefix
    } else {
        assert(output == before + seq![b'\n']);
        assert(before =~= output.take(before.len() as int));
        let atom = prefix.lexemes.last().kind is Atom;
        retain_prefix(before, output, prefix, 0, atom);
        let terminator = Lexeme { start: before.len() as int, end: output.len() as int, kind: LexemeKind::Whitespace };
        reveal(lexeme_at);
        reveal(trivia_extent);
        assert(lexeme_at(output, terminator.start, terminator.end, terminator.kind));
        let complete = record_scanned_input(output, prefix, terminator, atom, 0);
        assert(complete.lexemes.take(n) =~= prefix.lexemes);
        assert(complete.depths.take(n) =~= prefix.depths.take(n));
        prefix_piece_ranges(before, prefix, 0, atom);
        prefix_unchanged(before, output, prefix, complete, n);
        same_previous(prefix, complete, n);
        reveal(formatted_prefix);
        complete
    };
    assert(sexpr_input_derivation(output, complete));
    reveal(well_formed_sexpr_bytes);
    reveal(chosen_input_derivation_bytes);
    let chosen = chosen_input_derivation_bytes(output)->Some_0;
    derivations_agree(output, complete, chosen);
}

} // verus!
