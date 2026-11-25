//! 平坦な構文木を走査し、評価器が扱える式の構文かを調べる。

use super::*;
#[cfg(verus_only)]
use super::super::body::{call_argument_intervals, call_arguments_from_intervals};
use alloc::vec::Vec;

verus! {

#[derive(Clone, Copy)]
struct Forest {
    first: usize,
    end: usize,
}

#[verifier::opaque]
spec fn supported_forest(source: &str, forms: Seq<Form>, first: usize, end: usize) -> bool
    decreases end - first,
{
    if first == end { true } else if first < end <= forms.len() {
        let next = subtree_limit(forms, first);
        first < next <= end && scalar_evaluator_syntax(source, forms, first)
            && supported_forest(source, forms, next, end)
    } else { false }
}

proof fn supported_argument_suffix(
    source: &str, forms: Seq<Form>, owner: usize, args: Seq<usize>, i: int,
)
    requires
        defn_call_arguments(forms, owner, args), 0 <= i <= args.len(),
        forall|j: int| i <= j < args.len() ==> scalar_evaluator_syntax(source, forms, #[trigger] args[j]),
    ensures supported_forest(source, forms,
        if i < args.len() { args[i] } else { subtree_limit(forms, owner) }, subtree_limit(forms, owner)),
    decreases args.len() - i,
{
    reveal(supported_forest);
    if i < args.len() {
        call_argument_intervals(forms, owner, args, i);
        supported_argument_suffix(source, forms, owner, args, i + 1);
    }
}

proof fn supported_forest_argument_positions(
    source: &str, forms: Seq<Form>, first: usize, end: usize,
) -> (arguments: Seq<usize>)
    requires first <= end <= forms.len(), supported_forest(source, forms, first, end),
    ensures
        if arguments.len() == 0 { first == end } else { arguments[0] == first },
        forall|i: int| 0 <= i < arguments.len() ==> {
            let child = #[trigger] arguments[i];
            &&& first <= child < subtree_limit(forms, child) <= end
            &&& scalar_evaluator_syntax(source, forms, child)
            &&& if i + 1 < arguments.len() { subtree_limit(forms, child) == arguments[i + 1] }
                else { subtree_limit(forms, child) == end }
        },
    decreases end - first,
{
    reveal(supported_forest);
    if first == end { return Seq::empty(); }
    let next = subtree_limit(forms, first);
    let rest = supported_forest_argument_positions(source, forms, next, end);
    let args = seq![first] + rest;
    assert forall|i: int| 0 <= i < args.len() implies {
        let child = #[trigger] args[i];
        &&& first <= child < subtree_limit(forms, child) <= end
        &&& scalar_evaluator_syntax(source, forms, child)
        &&& if i + 1 < args.len() { subtree_limit(forms, child) == args[i + 1] }
            else { subtree_limit(forms, child) == end }
    } by {
        if i > 0 {
            assert(args[i] == rest[i - 1]);
            if i + 1 < args.len() { assert(args[i + 1] == rest[i]); }
        } else if rest.len() > 0 {
            assert(args[1] == rest[0]);
        }
    };
    args
}

#[verifier::spinoff_prover]
proof fn call_support_matches_forest(source: &str, forms: Seq<Form>, at: usize)
    requires scalar_call_syntax_at(source, forms, at),
    ensures scalar_evaluator_syntax(source, forms, at)
        == supported_forest(source, forms, (at + 2) as usize, subtree_limit(forms, at)),
{
    declared_call_syntax_uses_signature(source, forms, at);
    let first = (at + 2) as usize;
    let end = subtree_limit(forms, at);
    if scalar_evaluator_syntax(source, forms, at) {
        let args = scalar_syntax_call_arguments(source, forms, at);
        call_argument_intervals(forms, at, args, 0);
        supported_argument_suffix(source, forms, at, args, 0);
    }
    if supported_forest(source, forms, first, end) {
        let args = supported_forest_argument_positions(source, forms, first, end);
        call_arguments_from_intervals(forms, at, args);
        scalar_syntax_call_from_arguments(source, forms, at, args);
    }
}

#[verifier::spinoff_prover]
proof fn if_support_matches_forest(
    source: &str, forms: Seq<Form>, at: usize, condition: usize, yes: usize, no: usize,
)
    requires conditional_positions(source, forms, at) == Some((condition, yes, no)),
    ensures scalar_evaluator_syntax(source, forms, at)
        == supported_forest(source, forms, (at + 2) as usize, subtree_limit(forms, at)),
{
    reveal(conditional_positions);
    assert(children3(forms, at) == Some((condition, yes, no)));
    let end = subtree_limit(forms, at);
    reveal_with_fuel(supported_forest, 4);
    assert(supported_forest(source, forms, condition, end)
        == (scalar_evaluator_syntax(source, forms, condition)
            && scalar_evaluator_syntax(source, forms, yes) && scalar_evaluator_syntax(source, forms, no)));
    if scalar_evaluator_syntax(source, forms, at) {
        scalar_syntax_if_children(source, forms, at, condition, yes, no);
    }
    if supported_forest(source, forms, condition, end) {
        scalar_syntax_if_from_children(source, forms, at, condition, yes, no);
    }
}

fn read_supported_children(source: &str, forms: &[Form], at: usize) -> (children: Option<Forest>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures
        children.is_none() ==> !scalar_evaluator_syntax(source, forms@, at),
        children matches Some(children) ==> {
            &&& at < children.first <= children.end == subtree_limit(forms@, at) <= forms@.len()
            &&& scalar_evaluator_syntax(source, forms@, at) == supported_forest(source, forms@, children.first, children.end)
        },
{
    if matches!(&forms[at], Form::Atom { kind: AtomKind::Name | AtomKind::Natural | AtomKind::NegativeInteger, .. }) {
        proof {
            scalar_syntax_atom_from_kind(source, forms@, at);
            reveal(supported_forest);
        }
        return Some(Forest { first: at + 1, end: at + 1 });
    }
    if let Some((condition, _yes, _no)) = read_conditional_positions(source, forms, at) {
        proof { if_support_matches_forest(source, forms@, at, condition, _yes, _no); }
        return Some(Forest { first: condition, end: subtree_end(forms, at) });
    }
    if let Some((head, end, _)) = read_named_head(source, forms, at) {
        proof {
            assert(scalar_call_syntax_at(source, forms@, at));
            call_support_matches_forest(source, forms@, at);
        }
        return Some(Forest { first: head + 1, end });
    }
    proof {
        if scalar_evaluator_syntax(source, forms@, at) {
            scalar_syntax_form_kind(source, forms@, at);
            assert(false);
        }
    }
    None
}

spec fn frontier_fits(forms: Seq<Form>, frontier: Seq<Forest>) -> bool {
    forall|i: int| 0 <= i < frontier.len() ==> {
        let part = #[trigger] frontier[i];
        part.first < part.end <= forms.len()
    }
}

spec fn frontier_is_supported(source: &str, forms: Seq<Form>, frontier: Seq<Forest>) -> bool {
    forall|i: int| 0 <= i < frontier.len() ==> {
        let part = #[trigger] frontier[i];
        supported_forest(source, forms, part.first, part.end)
    }
}

#[verifier::opaque]
spec fn frontier_width(frontier: Seq<Forest>) -> nat
    decreases frontier.len(),
{
    if frontier.len() == 0 {
        0
    } else {
        let last = frontier.last();
        (last.end - last.first) as nat + frontier_width(frontier.drop_last())
    }
}

proof fn frontier_last(source: &str, forms: Seq<Form>, before: Seq<Forest>, after: Seq<Forest>, part: Forest)
    requires before == after.push(part),
    ensures
        frontier_fits(forms, before) == (frontier_fits(forms, after) && part.first < part.end <= forms.len()),
        frontier_is_supported(source, forms, before)
            == (frontier_is_supported(source, forms, after) && supported_forest(source, forms, part.first, part.end)),
        frontier_width(before) == frontier_width(after) + (part.end - part.first) as nat,
{
    reveal(frontier_width);
    assert(before.drop_last() =~= after);
    assert(before.last() == part);
    if frontier_fits(forms, before) {
        assert(frontier_fits(forms, after)) by {
            assert forall|i: int| 0 <= i < after.len() implies (#[trigger] after[i]).first < after[i].end <= forms.len() by {
                assert(after[i] == before[i]);
            };
        };
    }
    if frontier_is_supported(source, forms, before) {
        assert(frontier_is_supported(source, forms, after)) by {
            assert forall|i: int| 0 <= i < after.len() implies supported_forest(
                source, forms, (#[trigger] after[i]).first, after[i].end,
            ) by { assert(after[i] == before[i]); };
        };
    }
    if frontier_fits(forms, after) && part.first < part.end <= forms.len() {
        assert forall|i: int| 0 <= i < before.len() implies (#[trigger] before[i]).first < before[i].end <= forms.len() by {
            if i < after.len() { assert(before[i] == after[i]); }
            else { assert(before[i] == part); }
        };
    }
    if frontier_is_supported(source, forms, after) && supported_forest(source, forms, part.first, part.end) {
        assert forall|i: int| 0 <= i < before.len() implies supported_forest(
            source, forms, (#[trigger] before[i]).first, before[i].end,
        ) by {
            if i < after.len() { assert(before[i] == after[i]); }
            else { assert(before[i] == part); }
        };
    }
}

fn keep_forest(
    frontier: &mut Vec<Forest>, part: Forest, Ghost(source): Ghost<&str>, Ghost(forms): Ghost<Seq<Form>>,
)
    requires frontier_fits(forms, old(frontier)@), part.first <= part.end <= forms.len(),
    ensures
        frontier_fits(forms, final(frontier)@),
        frontier_is_supported(source, forms, final(frontier)@)
            == (frontier_is_supported(source, forms, old(frontier)@) && supported_forest(source, forms, part.first, part.end)),
        frontier_width(final(frontier)@) == frontier_width(old(frontier)@) + (part.end - part.first) as nat,
{
    let ghost before = frontier@;
    if part.first < part.end {
        frontier.push(part);
        proof { frontier_last(source, forms, frontier@, before, part); }
    } else {
        reveal(supported_forest);
    }
}

/// 保持した構文木で、本体がスカラー評価器の対応構文に属するかを調べる。
///
/// 対応する構文を調べる。名前の解決先、引数の型、整数の表現範囲は型検査と評価器が扱う。
pub(crate) fn check_scalar_body_syntax(source: &str, forms: &[Form], root: usize) -> (supported: bool)
    requires
        complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        root < forms@.len(),
    ensures supported == scalar_evaluator_syntax(source, forms@, root),
{
    let limit = subtree_end(forms, root);
    let _length = forms.len();
    proof {
        match forms@[root as int] {
            Form::Atom { .. } => { assert(limit == root + 1 <= _length); },
            Form::List { end, .. } => { assert(root < end <= _length && limit == end); },
        }
    }
    let mut frontier = Vec::new();
    keep_forest(&mut frontier, Forest { first: root, end: limit }, Ghost(source), Ghost(forms@));
    proof {
        reveal_with_fuel(supported_forest, 2);
        assert(root < limit <= forms@.len());
        assert(supported_forest(source, forms@, root, limit) == scalar_evaluator_syntax(source, forms@, root));
    }
    while !frontier.is_empty()
        invariant
            usable_forms(source, forms@),
            frontier_fits(forms@, frontier@),
            frontier_is_supported(source, forms@, frontier@) == scalar_evaluator_syntax(source, forms@, root),
        decreases frontier_width(frontier@),
    {
        let ghost before = frontier@;
        let Some(part) = frontier.pop() else { unreachable!() };
        proof {
            assert(before =~= frontier@.push(part));
            frontier_last(source, forms@, before, frontier@, part);
            reveal(supported_forest);
        }
        let next = subtree_end(forms, part.first);
        if next > part.end { return false; }
        let Some(children) = read_supported_children(source, forms, part.first) else { return false; };
        keep_forest(&mut frontier, Forest { first: next, end: part.end }, Ghost(source), Ghost(forms@));
        keep_forest(&mut frontier, children, Ghost(source), Ghost(forms@));
        assert(frontier_width(frontier@) < frontier_width(before));
    }
    true
}


}
