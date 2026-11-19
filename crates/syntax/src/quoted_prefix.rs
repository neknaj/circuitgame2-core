use super::{Boundary, boundary, quoted_atom, string_body_piece, string_body_pieces};
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub(super) open spec fn quoted_body(bytes: Seq<u8>, from: int, until: int) -> bool
    decreases until - from,
{
    &&& 0 <= from <= until <= bytes.len()
    &&& (from < until ==> {
        if bytes[from] == 92 {
            &&& from + 1 < until
            &&& (bytes[from + 1] == 34 || bytes[from + 1] == 92)
            &&& quoted_body(bytes, from + 2, until)
        } else {
            &&& !boundary::stops(Boundary::StringSpecial, bytes[from])
            &&& quoted_body(bytes, from + 1, until)
        }
    })
}

proof fn prepend_ordinary_body(bytes: Seq<u8>, from: int, next: int, until: int)
    requires
        0 <= from <= next <= until <= bytes.len(),
        quoted_body(bytes, next, until),
        forall|i: int| from <= i < next ==> !boundary::stops(Boundary::StringSpecial, #[trigger] bytes[i]),
    ensures quoted_body(bytes, from, until),
    decreases next - from,
{
    if from < next {
        prepend_ordinary_body(bytes, from + 1, next, until);
        reveal(quoted_body);
    }
}

proof fn derive_quoted_body(bytes: Seq<u8>, from: int, until: int, pieces: Seq<Seq<u8>>)
    requires
        0 <= from <= until <= bytes.len(),
        string_body_pieces(pieces),
        pieces.flatten() == bytes[from..until],
    ensures quoted_body(bytes, from, until),
    decreases pieces.len(),
{
    if pieces.len() == 0 {
        assert(pieces.flatten().len() == 0);
        reveal(quoted_body);
    } else {
        let head = pieces[0];
        let remaining = pieces.drop_first();
        let next = from + head.len();
        assert(pieces =~= seq![head] + remaining);
        vstd::seq_lib::lemma_flatten_concat(seq![head], remaining);
        assert(seq![head].flatten() == head);
        let flat = pieces.flatten();
        let tail = remaining.flatten();
        assert(flat == head + tail);
        assert(from <= next <= until);
        assert(head =~= bytes[from..next]);
        assert(tail.len() == until - next);
        assert forall|i: int| 0 <= i < tail.len() implies #[trigger] tail[i] == bytes[next + i] by {
            assert(tail[i] == flat[head.len() + i]);
            assert(flat[head.len() + i] == bytes[from + head.len() + i]);
        };
        assert(tail =~= bytes[next..until]);
        assert forall|i: int| 0 <= i < remaining.len()
            implies string_body_piece(#[trigger] remaining[i]) by {
            assert(remaining[i] == pieces[i + 1]);
        };
        derive_quoted_body(bytes, next, until, remaining);
        assert(string_body_piece(head));
        if head.len() > 0 && head[0] == 92 {
            assert(head.len() == 2 && (head[1] == 34 || head[1] == 92));
            assert(bytes[from] == head[0] && bytes[from + 1] == head[1]);
            reveal(quoted_body);
        } else {
            assert forall|i: int| from <= i < next
                implies !boundary::stops(Boundary::StringSpecial, #[trigger] bytes[i]) by {
                assert(bytes[i] == head[i - from]);
            };
            prepend_ordinary_body(bytes, from, next, until);
        }
    }
}

#[verifier::opaque]
pub open spec fn quoted_prefix_at(bytes: Seq<u8>, close: int) -> bool {
    1 <= close < bytes.len() && quoted_atom(bytes[..close + 1])
}

pub(super) proof fn quoted_prefix_starts_with_quote(bytes: Seq<u8>)
    ensures forall|close: int| #[trigger] quoted_prefix_at(bytes, close) ==> bytes[0] == 34,
{
    reveal(quoted_prefix_at);
    reveal(quoted_atom);
    assert forall|close: int| #[trigger] quoted_prefix_at(bytes, close) implies bytes[0] == 34 by {
        assert(bytes[..close + 1][0] == bytes[0]);
    };
}

#[verifier::opaque]
pub(super) open spec fn quoted_prefixes_viable(bytes: Seq<u8>, pos: int, clean: bool) -> bool {
    forall|close: int| #[trigger] quoted_prefix_at(bytes, close)
        ==> clean && pos <= close < bytes.len() && bytes[close] == 34 && quoted_body(bytes, pos, close)
}

pub(super) proof fn initialize_quoted_prefixes(bytes: Seq<u8>)
    ensures quoted_prefixes_viable(bytes, 1, true),
{
    reveal(quoted_prefixes_viable);
    assert forall|close: int| #[trigger] quoted_prefix_at(bytes, close)
        implies 1 <= close < bytes.len() && bytes[close] == 34 && quoted_body(bytes, 1, close) by {
        reveal(quoted_prefix_at);
        let literal = bytes[..close + 1];
        reveal(quoted_atom);
        assert(literal[close] == bytes[close]);
        assert(literal[1..close] =~= bytes[1..close]);
        let pieces = choose|pieces: Seq<Seq<u8>>| #[trigger] pieces.flatten() == literal[1..close]
            && string_body_pieces(pieces);
        derive_quoted_body(bytes, 1, close, pieces);
    };
}

proof fn advance_ordinary_prefix(bytes: Seq<u8>, from: int, next: int, until: int)
    requires
        0 <= from <= next <= until <= bytes.len(),
        quoted_body(bytes, from, until),
        forall|i: int| from <= i < next ==> !boundary::stops(Boundary::StringSpecial, #[trigger] bytes[i]),
    ensures quoted_body(bytes, next, until),
    decreases next - from,
{
    if from < next {
        assert(quoted_body(bytes, from + 1, until)) by {
            reveal(quoted_body);
        };
        advance_ordinary_prefix(bytes, from + 1, next, until);
    }
}

pub(super) proof fn advance_quoted_prefixes_over_ordinary(bytes: Seq<u8>, from: int, next: int, clean: bool)
    requires
        0 <= from <= next <= bytes.len(),
        quoted_prefixes_viable(bytes, from, clean),
        forall|i: int| from <= i < next ==> !boundary::stops(Boundary::StringSpecial, #[trigger] bytes[i]),
    ensures quoted_prefixes_viable(bytes, next, clean),
{
    reveal(quoted_prefixes_viable);
    assert forall|close: int| #[trigger] quoted_prefix_at(bytes, close)
        implies clean && next <= close < bytes.len() && bytes[close] == 34 && quoted_body(bytes, next, close) by {
        assert(from <= close && bytes[close] == 34);
        assert(next <= close);
        advance_ordinary_prefix(bytes, from, next, close);
    };
}

pub(super) proof fn quoted_stop(bytes: Seq<u8>, pos: int, clean: bool)
    requires
        0 <= pos <= bytes.len(),
        quoted_prefixes_viable(bytes, pos, clean),
        pos < bytes.len() ==> bytes[pos] == 34 || bytes[pos] == 10 || bytes[pos] == 13,
    ensures
        forall|close: int| #[trigger] quoted_prefix_at(bytes, close)
            ==> clean && pos == close && pos < bytes.len() && bytes[pos] == 34,
{
    reveal(quoted_prefixes_viable);
    assert forall|close: int| #[trigger] quoted_prefix_at(bytes, close)
        implies clean && pos == close && pos < bytes.len() && bytes[pos] == 34 by {
        assert(pos <= close && bytes[close] == 34);
        if pos < close {
            reveal(quoted_body);
            assert(!boundary::stops(Boundary::StringSpecial, bytes[pos]));
        }
    };
}

pub(super) proof fn escape_at_quoted_prefixes(bytes: Seq<u8>, pos: int, clean: bool)
    requires
        0 <= pos < bytes.len(),
        bytes[pos] == 92,
        quoted_prefixes_viable(bytes, pos, clean),
    ensures
        forall|close: int| #[trigger] quoted_prefix_at(bytes, close) ==> {
            &&& clean
            &&& pos + 1 < close < bytes.len()
            &&& (bytes[pos + 1] == 34 || bytes[pos + 1] == 92)
        },
        quoted_prefixes_viable(bytes, pos + 2, clean),
{
    reveal(quoted_prefixes_viable);
    assert forall|close: int| #[trigger] quoted_prefix_at(bytes, close) implies {
        &&& clean
        &&& pos + 1 < close < bytes.len()
        &&& (bytes[pos + 1] == 34 || bytes[pos + 1] == 92)
        &&& quoted_body(bytes, pos + 2, close)
    } by {
        assert(pos < close);
        reveal(quoted_body);
        assert(quoted_body(bytes, pos, close));
    };
}

} // verus!
