//! 構文木の指定位置が、本体の式としてたどれる位置にあるかを調べる。

use super::*;
use crate::ncg2m::let_syntax::LetHeader;
#[cfg(verus_only)]
use crate::ncg2m::let_syntax::LocalBinding;

mod coverage;
#[cfg(verus_only)]
mod supported;
#[cfg(verus_only)]
pub(in crate::ncg2m::expression_types) use supported::list_in_supported_body_is_expression_slot;
pub(in crate::ncg2m) use coverage::mark_expression_slots;
#[cfg(verus_only)]
pub(in crate::ncg2m) use coverage::slot_marked;

verus! {

spec fn contains(forms: Seq<Form>, child: usize, at: usize) -> bool {
    child <= at < forms.len() && at < subtree_limit(forms, child)
}

fn contains_at(forms: &[Form], child: usize, at: usize) -> (found: bool)
    ensures found == contains(forms@, child, at),
{
    if child > at || at >= forms.len() { return false; }
    at < subtree_end(forms, child)
}

spec fn argument_containing(forms: Seq<Form>, first: usize, end: usize, at: usize) -> Option<usize>
    decreases end - first,
{
    if first >= end || end > forms.len() || at < first || at >= end {
        None
    } else {
        let next = subtree_limit(forms, first);
        if !(first < next <= end) { None }
        else if at < next { Some(first) }
        else { argument_containing(forms, next, end, at) }
    }
}

fn pick_argument(forms: &[Form], _owner: usize, first: usize, end: usize, at: usize) -> (next: Option<usize>)
    requires complete_list_indices(forms@), nested_list_indices(forms@),
        _owner < first <= end <= forms@.len(), forms@[_owner as int] is List,
        subtree_limit(forms@, _owner) == end,
    ensures next == argument_containing(forms@, first, end, at),
{
    if at < first || at >= end { return None; }
    let mut current = first;
    while current < end
        invariant complete_list_indices(forms@), nested_list_indices(forms@),
            _owner < first <= current <= end <= forms@.len(),
            forms@[_owner as int] is List, subtree_limit(forms@, _owner) == end,
            current <= at < end,
            argument_containing(forms@, current, end, at) == argument_containing(forms@, first, end, at),
        decreases end - current,
    {
        proof { super::super::super::forms::child_stays_inside(forms@, _owner, current); }
        let limit = subtree_end(forms, current);
        if at < limit { return Some(current); }
        current = limit;
    }
    None
}

spec fn binding_containing(
    forms: Seq<Form>, bindings: Seq<LocalBinding>, at: usize, start: nat,
) -> Option<usize>
    decreases bindings.len() - start,
{
    if start >= bindings.len() {
        None
    } else {
        let value = bindings[start as int].value;
        if contains(forms, value, at) { Some(value) }
        else { binding_containing(forms, bindings, at, start + 1) }
    }
}

fn pick_let(forms: &[Form], header: &LetHeader, at: usize) -> (child: Option<usize>)
    ensures child == if contains(forms@, header.body, at) { Some(header.body) }
        else { binding_containing(forms@, header.bindings@, at, 0) },
{
    if contains_at(forms, header.body, at) { return Some(header.body); }
    let mut i = 0;
    while i < header.bindings.len()
        invariant i <= header.bindings@.len(), !contains(forms@, header.body, at),
            binding_containing(forms@, header.bindings@, at, i as nat)
                == binding_containing(forms@, header.bindings@, at, 0),
        decreases header.bindings@.len() - i,
    {
        let value = header.bindings[i].value;
        if contains_at(forms, value, at) {
            assert(binding_containing(forms@, header.bindings@, at, i as nat) == Some(value));
            return Some(value);
        }
        i += 1;
    }
    None
}

spec fn first_containing(forms: Seq<Form>, at: usize, one: usize, two: usize, three: usize) -> Option<usize> {
    if contains(forms, one, at) { Some(one) }
    else if contains(forms, two, at) { Some(two) }
    else if contains(forms, three, at) { Some(three) }
    else { None }
}

fn pick_three(forms: &[Form], at: usize, one: usize, two: usize, three: usize) -> (child: Option<usize>)
    ensures child == first_containing(forms@, at, one, two, three),
{
    if contains_at(forms, one, at) { Some(one) }
    else if contains_at(forms, two, at) { Some(two) }
    else if contains_at(forms, three, at) { Some(three) }
    else { None }
}

spec fn expression_child(source: &str, forms: Seq<Form>, owner: usize, at: usize) -> Option<usize> {
    if owner >= forms.len() {
        None
    } else {
        match shape(source, forms, owner) {
            Ok(Expression::Annotated { value, .. }) =>
                if contains(forms, value, at) { Some(value) } else { None },
            Ok(Expression::Conditional { condition, yes, no }) =>
                first_containing(forms, at, condition, yes, no),
            Ok(Expression::Fold(header)) => first_containing(forms, at, header.input, header.initial, header.body),
            Ok(Expression::Let) => match let_structure(source, forms, owner) {
                Ok((_, body)) if contains(forms, body, at) => Some(body),
                Ok((rows, _)) => binding_containing(forms, rows, at, 0),
                Err(_) => None,
            },
            Ok(Expression::List) => argument_containing(forms, (owner + 2) as usize, subtree_limit(forms, owner), at),
            _ if named_call_head(source, forms, owner) =>
                argument_containing(forms, (owner + 2) as usize, subtree_limit(forms, owner), at),
            _ => None,
        }
    }
}

fn read_expression_child(source: &str, forms: &[Form], owner: usize, at: usize) -> (child: Option<usize>)
    requires usable_forms(source, forms@), owner < forms@.len(),
    ensures child == expression_child(source, forms@, owner, at),
{
    match read_shape(source, forms, owner) {
        Ok(Expression::Annotated { value, .. }) =>
            if contains_at(forms, value, at) { Some(value) } else { None },
        Ok(Expression::Conditional { condition, yes, no }) => pick_three(forms, at, condition, yes, no),
        Ok(Expression::Fold(header)) => pick_three(forms, at, header.input, header.initial, header.body),
        Ok(Expression::Let) => match read_let_structure(source, forms, owner) {
            Ok(header) => pick_let(forms, &header, at),
            Err(_) => None,
        },
        Ok(Expression::List) => {
            let Form::List { end: list_end, .. } = &forms[owner] else { unreachable!() };
            let _length = forms.len();
            assert(owner + 2 <= *list_end <= _length);
            pick_argument(forms, owner, owner + 2, *list_end, at)
        }
        _ => match read_named_head(source, forms, owner) {
            Some((head, end, _)) => pick_argument(forms, owner, head + 1, end, at),
            None => None,
        }
    }
}

/// 本体の根から式の位置だけをたどって到達できることを表す。
///
/// 型注釈、束縛名、構文テンプレートの内部は式としてたどらない。
pub closed spec fn expression_slot(source: &str, forms: Seq<Form>, root: usize, at: usize) -> bool
    decreases at - root,
{
    if root > at || at >= forms.len() {
        false
    } else if root == at {
        true
    } else {
        match expression_child(source, forms, root, at) {
            Some(next) if root < next <= at => expression_slot(source, forms, next, at),
            _ => false,
        }
    }
}

/// 本体の根は式の位置である。
pub proof fn expression_slot_at_root(source: &str, forms: Seq<Form>, root: usize)
    requires root < forms.len(),
    ensures expression_slot(source, forms, root, root),
{}

pub(in crate::ncg2m) proof fn expression_slot_bounds(source: &str, forms: Seq<Form>, root: usize, at: usize)
    requires expression_slot(source, forms, root, at),
    ensures root <= at < forms.len(),
{}

/// 型検査がたどる式の位置を、本体の根から確認する。
pub(in crate::ncg2m) fn is_expression_slot(source: &str, forms: &[Form], root: usize, at: usize) -> (found: bool)
    requires usable_forms(source, forms@),
    ensures found == expression_slot(source, forms@, root, at),
{
    if root > at || at >= forms.len() { return false; }
    let mut current = root;
    while current < at
        invariant usable_forms(source, forms@), root <= current <= at < forms@.len(),
            expression_slot(source, forms@, root, at) == expression_slot(source, forms@, current, at),
        decreases at - current,
    {
        let Some(next) = read_expression_child(source, forms, current, at) else { return false; };
        if current >= next || next > at { return false; }
        current = next;
    }
    true
}

}
