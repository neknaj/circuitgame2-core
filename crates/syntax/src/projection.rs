use super::{
    Form, bare_atom_delimiter, bare_atom_extent, covers, first_form_piece, form_represents_piece,
    list_close_piece, parsed_piece, pieces_represented, quoted_atom, sexpr_forest, trivia_byte,
    trivia_extent,
};
use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

pub open spec fn forest_terminals(forms: Seq<Form>, first: int, limit: int) -> Seq<(int, int)>
    decreases limit - first,
{
    if 0 <= first < limit <= forms.len() {
        let form = forms[first];
        match form {
            Form::Atom { .. } => seq![first_form_piece(form)]
                + forest_terminals(forms, first + 1, limit),
            Form::List { end, .. } => if first < end <= limit {
                seq![first_form_piece(form)]
                    + forest_terminals(forms, first + 1, end as int)
                    + seq![list_close_piece(form)]
                    + forest_terminals(forms, end as int, limit)
            } else {
                Seq::empty()
            },
        }
    } else {
        Seq::empty()
    }
}

pub open spec fn is_significant(source: &str, piece: (int, int)) -> bool {
    !trivia_extent(source.spec_bytes(), piece.0, piece.1, false)
        && !trivia_extent(source.spec_bytes(), piece.0, piece.1, true)
}

proof fn terminal_start_is_significant(source: &str, piece: (int, int))
    requires
        source.spec_bytes()[piece.0] != 59,
        !trivia_byte(source.spec_bytes()[piece.0], false),
    ensures is_significant(source, piece),
{
    reveal(trivia_extent);
}

pub open spec fn significant_pieces(source: &str, pieces: Seq<(int, int)>) -> Seq<(int, int)> {
    pieces.filter(|piece: (int, int)| is_significant(source, piece))
}

spec fn sorted(pieces: Seq<(int, int)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < pieces.len() ==> (#[trigger] pieces[i]).0 < (#[trigger] pieces[j]).0
}

spec fn inside(pieces: Seq<(int, int)>, lower: int, upper: int) -> bool {
    forall|i: int| 0 <= i < pieces.len() ==> {
        let piece = #[trigger] pieces[i];
        lower <= piece.0 < piece.1 <= upper
    }
}

proof fn concatenate(left: Seq<(int, int)>, right: Seq<(int, int)>, lower: int, split: int, upper: int)
    requires
        sorted(left), sorted(right),
        inside(left, lower, split), inside(right, split, upper),
        lower <= split <= upper,
    ensures sorted(left + right), inside(left + right, lower, upper),
{
    let both = left + right;
    assert forall|i: int| 0 <= i < both.len() implies {
        let piece = #[trigger] both[i];
        lower <= piece.0 < piece.1 <= upper
    } by {
        if i < left.len() {
            assert(both[i] == left[i]);
        } else {
            assert(both[i] == right[i - left.len()]);
        }
    };
    assert forall|i: int, j: int| 0 <= i < j < both.len()
        implies (#[trigger] both[i]).0 < (#[trigger] both[j]).0 by {
        if j < left.len() {
            assert(both[i] == left[i] && both[j] == left[j]);
        } else if i >= left.len() {
            assert(both[i] == right[i - left.len()] && both[j] == right[j - left.len()]);
        } else {
            assert(both[i] == left[i] && both[j] == right[j - left.len()]);
        }
    };
}

proof fn terminal_evidence(
    source: &str, forms: Seq<Form>, pieces: Seq<(int, int)>,
    first: int, limit: int, lower: int, upper: int,
)
    requires sexpr_forest(source, forms, pieces, first, limit, lower, upper),
    ensures
        sorted(forest_terminals(forms, first, limit)),
        inside(forest_terminals(forms, first, limit), lower, upper),
        forall|piece: (int, int)| #[trigger] forest_terminals(forms, first, limit).contains(piece)
            ==> pieces.contains(piece) && is_significant(source, piece),
        forall|i: int, piece: (int, int)| first <= i < limit
            && #[trigger] form_represents_piece(forms[i], piece)
            ==> forest_terminals(forms, first, limit).contains(piece),
    decreases limit - first,
{
    reveal(sexpr_forest);
    if first == limit {
        return;
    }
    let form = forms[first];
    let start_piece = first_form_piece(form);
    let start = start_piece.0;
    let finish = super::form_span(form).end as int;
    let leading = seq![start_piece];
    let (initial, after) = match form {
        Form::Atom { kind, .. } => {
            if kind == super::AtomKind::String {
                reveal(quoted_atom);
                let quoted = source.spec_bytes()[start..finish];
                assert(quoted[0] == 34);
                assert(source.spec_bytes()[start] == 34);
            } else {
                reveal(bare_atom_extent);
                assert(!bare_atom_delimiter(source.spec_bytes()[start]));
            }
            terminal_start_is_significant(source, start_piece);
            (leading, first + 1)
        }
        Form::List { end, .. } => {
            let close = list_close_piece(form);
            let closing = seq![close];
            let children = forest_terminals(forms, first + 1, end as int);
            terminal_evidence(source, forms, pieces, first + 1, end as int, start + 1, finish - 1);
            concatenate(leading, children, lower, start + 1, finish - 1);
            concatenate(leading + children, closing, lower, finish - 1, finish);
            terminal_start_is_significant(source, start_piece);
            terminal_start_is_significant(source, close);
            (leading + children + closing, end as int)
        }
    };
    terminal_evidence(source, forms, pieces, after, limit, finish, upper);
    let tail = forest_terminals(forms, after, limit);
    concatenate(initial, tail, lower, finish, upper);
    assert(forest_terminals(forms, first, limit) == initial + tail);
    assert forall|piece: (int, int)| #[trigger] (initial + tail).contains(piece)
        implies pieces.contains(piece) && is_significant(source, piece) by {
        assert(initial.contains(piece) || tail.contains(piece));
        match form {
            Form::Atom { .. } => {
                assert(initial.contains(piece) ==> piece == start_piece);
            }
            Form::List { end, .. } => {
                let children = forest_terminals(forms, first + 1, end as int);
                let close = list_close_piece(form);
                assert(initial.contains(piece)
                    ==> piece == start_piece || children.contains(piece) || piece == close);
            }
        }
    };
    assert forall|i: int, piece: (int, int)| first <= i < limit
        && #[trigger] form_represents_piece(forms[i], piece)
        implies (initial + tail).contains(piece) by {
        if i == first {
            assert(piece == start_piece || (form is List && piece == list_close_piece(form)));
        } else if i < after {
            assert(form is List);
            assert(forest_terminals(forms, first + 1, after).contains(piece));
        } else {
            assert(tail.contains(piece));
        }
    };
}

#[verifier::opaque]
spec fn adjacent_starts_increase(pieces: Seq<(int, int)>) -> bool {
    forall|j: int| 0 < j < pieces.len()
        ==> (#[trigger] pieces[j - 1]).0 < (#[trigger] pieces[j]).0
}

proof fn order_from_adjacent_starts(pieces: Seq<(int, int)>, i: int, j: int)
    requires adjacent_starts_increase(pieces), 0 <= i < j < pieces.len(),
    ensures pieces[i].0 < pieces[j].0,
    decreases j - i,
{
    assert(pieces[j - 1].0 < pieces[j].0) by {
        reveal(adjacent_starts_increase);
    };
    if i < j - 1 {
        order_from_adjacent_starts(pieces, i, j - 1);
    }
}

proof fn covered_ranges_are_sorted(bytes: Seq<u8>, pieces: Seq<(int, int)>, end: int)
    requires covers(bytes, pieces, end),
    ensures sorted(pieces),
{
    assert(adjacent_starts_increase(pieces)) by {
        reveal(adjacent_starts_increase);
        assert forall|j: int| 0 < j < pieces.len()
            implies (#[trigger] pieces[j - 1]).0 < (#[trigger] pieces[j]).0 by {
            assert(pieces[j - 1].0 < pieces[j - 1].1 == pieces[j].0);
        };
    };
    assert forall|i: int, j: int| 0 <= i < j < pieces.len()
        implies (#[trigger] pieces[i]).0 < (#[trigger] pieces[j]).0 by {
        order_from_adjacent_starts(pieces, i, j);
    };
}

proof fn filter_sorted(source: &str, pieces: Seq<(int, int)>)
    requires sorted(pieces),
    ensures sorted(significant_pieces(source, pieces)),
    decreases pieces.len(),
{
    if pieces.len() == 0 {
        return;
    }
    let pred = |piece: (int, int)| is_significant(source, piece);
    let first = pieces[0];
    let tail = pieces.drop_first();
    assert(pieces =~= seq![first] + tail);
    assert(sorted(tail)) by {
        assert forall|i: int, j: int| 0 <= i < j < tail.len()
            implies (#[trigger] tail[i]).0 < (#[trigger] tail[j]).0 by {
            assert(tail[i] == pieces[i + 1] && tail[j] == pieces[j + 1]);
        };
    };
    filter_sorted(source, tail);
    tail.lemma_filter_prepend(first, pred);
    let filtered_tail = significant_pieces(source, tail);
    let filtered = significant_pieces(source, pieces);
    if pred(first) {
        assert forall|i: int, j: int| 0 <= i < j < filtered.len()
            implies (#[trigger] filtered[i]).0 < (#[trigger] filtered[j]).0 by {
            if i == 0 {
                let piece = filtered_tail[j - 1];
                assert(filtered_tail.contains(piece));
                tail.lemma_filter_contains_rev(pred, piece);
                let index = choose|k: int| 0 <= k < tail.len() && tail[k] == piece;
                assert(pieces[index + 1] == piece);
            } else {
                assert(filtered[i] == filtered_tail[i - 1] && filtered[j] == filtered_tail[j - 1]);
            }
        };
    }
}

proof fn same_sorted_ranges(left: Seq<(int, int)>, right: Seq<(int, int)>)
    requires
        sorted(left), sorted(right),
        forall|piece: (int, int)| #![trigger left.contains(piece)] #![trigger right.contains(piece)]
            left.contains(piece) <==> right.contains(piece),
    ensures left == right,
    decreases left.len(),
{
    if left.len() == 0 || right.len() == 0 {
        if left.len() != 0 {
            assert(left.contains(left[0]));
            assert(right.contains(left[0]));
        }
        if right.len() != 0 {
            assert(right.contains(right[0]));
            assert(left.contains(right[0]));
        }
        assert(left =~= right);
        return;
    }
    let a = left[0];
    let b = right[0];
    assert(left.contains(a) && right.contains(b));
    assert(right.contains(a) && left.contains(b));
    let ai = choose|i: int| 0 <= i < right.len() && right[i] == a;
    let bi = choose|i: int| 0 <= i < left.len() && left[i] == b;
    if ai > 0 {
        assert(b.0 < a.0);
    }
    if bi > 0 {
        assert(a.0 < b.0);
    }
    assert(ai == 0 && bi == 0);
    assert(a == b);
    let left_tail = left.drop_first();
    let right_tail = right.drop_first();
    assert(sorted(left_tail) && sorted(right_tail)) by {
        assert forall|i: int, j: int| 0 <= i < j < left_tail.len()
            implies (#[trigger] left_tail[i]).0 < (#[trigger] left_tail[j]).0 by {
            assert(left_tail[i] == left[i + 1] && left_tail[j] == left[j + 1]);
        };
        assert forall|i: int, j: int| 0 <= i < j < right_tail.len()
            implies (#[trigger] right_tail[i]).0 < (#[trigger] right_tail[j]).0 by {
            assert(right_tail[i] == right[i + 1] && right_tail[j] == right[j + 1]);
        };
    };
    assert forall|piece: (int, int)| #![trigger left_tail.contains(piece)] #![trigger right_tail.contains(piece)]
        left_tail.contains(piece) <==> right_tail.contains(piece) by {
        assert(left =~= seq![a] + left_tail);
        assert(right =~= seq![a] + right_tail);
        assert(!left_tail.contains(a) && !right_tail.contains(a)) by {
            if left_tail.contains(a) {
                let i = choose|i: int| 0 <= i < left_tail.len() && left_tail[i] == a;
                assert(left[i + 1] == a);
            }
            if right_tail.contains(a) {
                let i = choose|i: int| 0 <= i < right_tail.len() && right_tail[i] == a;
                assert(right[i + 1] == a);
            }
        };
        assert(left.contains(piece) == right.contains(piece));
    };
    same_sorted_ranges(left_tail, right_tail);
    assert(left =~= right);
}

pub(super) proof fn derive_projection(source: &str, forms: Seq<Form>, pieces: Seq<(int, int)>)
    requires
        covers(source.spec_bytes(), pieces, source.spec_bytes().len() as int),
        pieces_represented(source, forms, pieces),
        sexpr_forest(source, forms, pieces, 0, forms.len() as int, 0, source.spec_bytes().len() as int),
    ensures significant_pieces(source, pieces) == forest_terminals(forms, 0, forms.len() as int),
{
    let end = source.spec_bytes().len() as int;
    let pred = |piece: (int, int)| is_significant(source, piece);
    let filtered = significant_pieces(source, pieces);
    let terminals = forest_terminals(forms, 0, forms.len() as int);
    covered_ranges_are_sorted(source.spec_bytes(), pieces, end);
    filter_sorted(source, pieces);
    terminal_evidence(source, forms, pieces, 0, forms.len() as int, 0, end);
    reveal(pieces_represented);
    assert forall|piece: (int, int)| #![trigger filtered.contains(piece)] #![trigger terminals.contains(piece)]
        filtered.contains(piece) <==> terminals.contains(piece) by {
        if filtered.contains(piece) {
            pieces.lemma_filter_contains_rev(pred, piece);
            let index = choose|i: int| 0 <= i < filtered.len() && filtered[i] == piece;
            pieces.lemma_filter_pred(pred, index);
            let original = choose|i: int| 0 <= i < pieces.len() && pieces[i] == piece;
            assert(parsed_piece(source, forms, pieces[original]));
            let owner = choose|i: int| 0 <= i < forms.len() && form_represents_piece(#[trigger] forms[i], piece);
            assert(form_represents_piece(forms[owner], piece));
        }
        if terminals.contains(piece) {
            let index = choose|i: int| 0 <= i < pieces.len() && pieces[i] == piece;
            pieces.lemma_filter_contains(pred, index);
        }
    };
    same_sorted_ranges(filtered, terminals);
}

} // verus!
