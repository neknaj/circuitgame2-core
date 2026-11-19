use crate::AtomKind;
use crate::boundary::{Boundary, after_ascii, split_at_boundary};
#[cfg(verus_only)]
use crate::digits::digit;
use crate::digits::{Radix, matches_digits};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

spec fn digit_sequence(bytes: Seq<u8>, radix: Radix) -> bool {
    &&& bytes.len() > 0
    &&& forall|i: int| 0 <= i < bytes.len() ==> digit(radix, #[trigger] bytes[i])
}

pub closed spec fn bare_atom_kind(bytes: Seq<u8>) -> Option<AtomKind> {
    if bytes.len() >= 2 && bytes[0] == 35 && bytes[1] == 98 {
        if digit_sequence(bytes[2..], Radix::Binary) { Some(AtomKind::Binary) } else { None }
    } else if bytes.len() >= 2 && bytes[0] == 35 && bytes[1] == 120 {
        if digit_sequence(bytes[2..], Radix::Hexadecimal) { Some(AtomKind::Hexadecimal) } else { None }
    } else if bytes.len() >= 1 && bytes[0] == 45 {
        if digit_sequence(bytes[1..], Radix::Decimal) { Some(AtomKind::NegativeInteger) } else { None }
    } else if digit_sequence(bytes, Radix::Decimal) {
        Some(AtomKind::Natural)
    } else {
        path_kind(bytes)
    }
}

pub(crate) fn classify(atom: &str) -> (result: Option<AtomKind>)
    ensures result == bare_atom_kind(atom.spec_bytes()),
{
    let bytes = atom.as_bytes();
    if bytes.len() >= 2 && bytes[0] == b'#' && matches!(bytes[1], b'b' | b'x') {
        let tail = after_ascii(after_ascii(atom));
        assert(tail.spec_bytes() =~= bytes@[2..]);
        let (radix, kind) = if bytes[1] == b'b' {
            (Radix::Binary, AtomKind::Binary)
        } else {
            (Radix::Hexadecimal, AtomKind::Hexadecimal)
        };
        if matches_digits(tail.as_bytes(), radix) { Some(kind) } else { None }
    } else if bytes.len() > 0 && bytes[0] == b'-' {
        let tail = after_ascii(atom);
        if matches_digits(tail.as_bytes(), Radix::Decimal) {
            Some(AtomKind::NegativeInteger)
        } else {
            None
        }
    } else if matches_digits(bytes, Radix::Decimal) {
        Some(AtomKind::Natural)
    } else {
        classify_path(atom)
    }
}

spec fn name_start(byte: u8) -> bool {
    65 <= byte <= 90 || 97 <= byte <= 122 || byte == 95
}

spec fn name_continue(byte: u8) -> bool {
    name_start(byte) || 48 <= byte <= 57 || byte == 45
}

spec fn name_component(bytes: Seq<u8>) -> bool {
    &&& bytes.len() > 0
    &&& name_start(bytes[0])
    &&& forall|i: int| 0 < i < bytes.len() ==> name_continue(#[trigger] bytes[i])
}

fn is_name(name: &str) -> (accepted: bool)
    ensures
        accepted == name_component(name.spec_bytes()),
{
    let bytes = name.as_bytes();
    if bytes.len() == 0 || !matches!(bytes[0], b'A'..=b'Z' | b'a'..=b'z' | b'_') {
        return false;
    }
    let mut i = 1;
    while i < bytes.len()
        invariant
            bytes@ == name.spec_bytes(),
            1 <= i <= bytes@.len(),
            name_start(bytes@[0]),
            forall|j: int| 0 < j < i ==> name_continue(#[trigger] bytes@[j]),
        decreases bytes@.len() - i,
    {
        if !matches!(bytes[i], b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' | b'-') {
            assert(!name_continue(bytes@[i as int]));
            assert(!name_component(bytes@));
            return false;
        }
        i += 1;
    }
    true
}

spec fn first_colon(bytes: Seq<u8>, at: int) -> bool {
    &&& 0 <= at <= bytes.len()
    &&& (at < bytes.len() ==> bytes[at] == 58)
    &&& forall|i: int| 0 <= i < at ==> #[trigger] bytes[i] != 58
}

spec fn colon_pair(bytes: Seq<u8>, at: int) -> bool {
    0 <= at && at + 1 < bytes.len() && bytes[at] == 58 && bytes[at + 1] == 58
}

spec fn path_body(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    if exists|at: int| first_colon(bytes, at) {
        let at = choose|at: int| first_colon(bytes, at);
        name_component(bytes[..at]) && (
            at == bytes.len() || (colon_pair(bytes, at) && path_body(bytes[(at + 2)..]))
        )
    } else {
        false
    }
}

proof fn path_body_at(bytes: Seq<u8>, at: int)
    requires
        first_colon(bytes, at),
    ensures
        path_body(bytes) == (name_component(bytes[..at]) && (
            at == bytes.len() || (colon_pair(bytes, at) && path_body(bytes[(at + 2)..]))
        )),
{
    reveal_with_fuel(path_body, 1);
    assert(exists|other: int| first_colon(bytes, other));
    let other = choose|other: int| first_colon(bytes, other);
    if at < other {
        assert(bytes[at] == 58 && bytes[at] != 58);
    } else if other < at {
        assert(bytes[other] == 58 && bytes[other] != 58);
    }
}

fn has_colon_pair(source: &str) -> (pair: bool)
    ensures pair == colon_pair(source.spec_bytes(), 0),
{
    let bytes = source.as_bytes();
    bytes.len() >= 2 && bytes[0] == b':' && bytes[1] == b':'
}

spec fn path_kind(bytes: Seq<u8>) -> Option<AtomKind> {
    if colon_pair(bytes, 0) {
        if path_body(bytes[2..]) { Some(AtomKind::AbsolutePath) } else { None }
    } else if name_component(bytes) {
        Some(AtomKind::Name)
    } else if path_body(bytes) {
        Some(AtomKind::RelativePath)
    } else {
        None
    }
}

fn classify_path(atom: &str) -> (result: Option<AtomKind>)
    ensures result == path_kind(atom.spec_bytes()),
{
    let absolute = has_colon_pair(atom);
    let body = if absolute {
        let after_first = after_ascii(atom);
        let tail = after_ascii(after_first);
        assert(tail.spec_bytes() =~= atom.spec_bytes()[2..]);
        tail
    } else {
        atom
    };
    let mut remaining = body;
    let mut qualified = absolute;
    loop
        invariant
            absolute == colon_pair(atom.spec_bytes(), 0),
            body.spec_bytes() =~= if absolute { atom.spec_bytes()[2..] } else { atom.spec_bytes() },
            path_body(remaining.spec_bytes()) == path_body(body.spec_bytes()),
            !qualified ==> remaining == body,
            qualified && !absolute ==> !name_component(body.spec_bytes()),
        decreases remaining.spec_bytes().len(),
    {
        let (name, separator) = split_at_boundary(remaining, Boundary::Colon);
        let ghost bytes = remaining.spec_bytes();
        let ghost at = name.spec_bytes().len() as int;
        proof {
            assert(name.spec_bytes() =~= bytes[..at]);
            assert(separator.spec_bytes() =~= bytes[at..]);
            assert(first_colon(bytes, at));
            path_body_at(bytes, at);
        }
        if !is_name(name) {
            return None;
        }
        if separator.as_bytes().len() == 0 {
            return Some(if absolute {
                AtomKind::AbsolutePath
            } else if qualified {
                AtomKind::RelativePath
            } else {
                AtomKind::Name
            });
        }
        if !has_colon_pair(separator) {
            return None;
        }
        if !qualified {
            assert(bytes[at] == 58);
            assert(!name_component(body.spec_bytes()));
        }
        let tail = after_ascii(after_ascii(separator));
        assert(tail.spec_bytes() =~= bytes[(at + 2)..]);
        remaining = tail;
        qualified = true;
    }
}

} // verus!
