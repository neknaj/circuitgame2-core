//! 本体の構文木を前から一度たどり、式として到達できる位置を記録する。

use super::*;

verus! {

spec fn child_bounds(forms: Seq<Form>, root: usize, children: Seq<usize>) -> bool {
    forall|i: int| 0 <= i < children.len() ==> root < #[trigger] children[i] < subtree_limit(forms, root)
}

spec fn covers_expression_children(source: &str, forms: Seq<Form>, root: usize, children: Seq<usize>) -> bool {
    forall|at: usize| #[trigger] expression_child(source, forms, root, at) matches Some(child)
        ==> children.contains(child)
}

fn argument_slots(forms: &[Form], _owner: usize, first: usize, end: usize) -> (children: Vec<usize>)
    requires
        complete_list_indices(forms@), nested_list_indices(forms@),
        _owner < first <= end <= forms@.len(), forms@[_owner as int] is List, subtree_limit(forms@, _owner) == end,
    ensures
        child_bounds(forms@, _owner, children@),
        forall|at: usize| #[trigger] argument_containing(forms@, first, end, at) matches Some(child)
            ==> children@.contains(child),
{
    let mut children = Vec::<usize>::new();
    let mut next = first;
    while next < end
        invariant
            complete_list_indices(forms@), nested_list_indices(forms@),
            _owner < first <= next <= end <= forms@.len(),
            forms@[_owner as int] is List, subtree_limit(forms@, _owner) == end,
            child_bounds(forms@, _owner, children@),
            forall|at: usize| #[trigger] argument_containing(forms@, first, end, at) matches Some(child)
                ==> children@.contains(child) || argument_containing(forms@, next, end, at) == Some(child),
        decreases end - next,
    {
        let ghost previous = children@;
        proof { super::super::super::super::forms::child_stays_inside(forms@, _owner, next); }
        let limit = subtree_end(forms, next);
        children.push(next);
        proof {
            assert forall|at: usize| #[trigger] argument_containing(forms@, first, end, at).is_some()
                implies ({
                    let child = argument_containing(forms@, first, end, at)->Some_0;
                    children@.contains(child) || argument_containing(forms@, limit, end, at) == Some(child)
                }) by {
                if let Some(wanted) = argument_containing(forms@, first, end, at) {
                    if previous.contains(wanted) {
                        let index = choose|i: int| 0 <= i < previous.len() && (#[trigger] previous[i]) == wanted;
                        assert(children@[index] == wanted);
                    } else {
                        assert(argument_containing(forms@, next, end, at) == Some(wanted));
                        if at < limit {
                            assert(wanted == next);
                            assert(children@[previous.len() as int] == wanted);
                        }
                    }
                }
            };
        }
        next = limit;
    }
    children
}

proof fn binding_slot_in_header(
    forms: Seq<Form>, bindings: Seq<LocalBinding>, at: usize, from: nat, child: usize,
)
    requires binding_containing(forms, bindings, at, from) == Some(child),
    ensures exists|i: int| from <= i < bindings.len() && (#[trigger] bindings[i]).value == child,
    decreases bindings.len() - from,
{
    assert(from < bindings.len());
    if !contains(forms, bindings[from as int].value, at) {
        binding_slot_in_header(forms, bindings, at, from + 1, child);
    }
}

fn let_slots(_forms: &[Form], _owner: usize, header: &LetHeader) -> (children: Vec<usize>)
    requires
        _owner < header.body < subtree_limit(_forms@, _owner),
        valid_bindings(_forms@, header.bindings@, _owner, header.body),
    ensures
        child_bounds(_forms@, _owner, children@),
        children@.contains(header.body),
        forall|at: usize| #[trigger] binding_containing(_forms@, header.bindings@, at, 0) matches Some(child)
            ==> children@.contains(child),
{
    let mut children = Vec::<usize>::new();
    let mut i = 0;
    while i < header.bindings.len()
        invariant
            _owner < header.body < subtree_limit(_forms@, _owner),
            valid_bindings(_forms@, header.bindings@, _owner, header.body),
            i == children@.len() <= header.bindings@.len(),
            child_bounds(_forms@, _owner, children@),
            forall|j: int| 0 <= j < i ==> #[trigger] children@[j] == header.bindings@[j].value,
        decreases header.bindings@.len() - i,
    {
        children.push(header.bindings[i].value);
        i += 1;
    }
    let ghost bindings = children@;
    children.push(header.body);
    proof {
        assert(children@[bindings.len() as int] == header.body);
        assert forall|at: usize| #[trigger] binding_containing(_forms@, header.bindings@, at, 0).is_some()
            implies children@.contains(binding_containing(_forms@, header.bindings@, at, 0)->Some_0) by {
            let child = binding_containing(_forms@, header.bindings@, at, 0)->Some_0;
            binding_slot_in_header(_forms@, header.bindings@, at, 0, child);
            let i = choose|i: int| 0 <= i < header.bindings@.len() && (#[trigger] header.bindings@[i]).value == child;
            assert(children@[i] == bindings[i] == child);
        };
    }
    children
}

fn read_slot_children(source: &str, forms: &[Form], owner: usize) -> (children: Vec<usize>)
    requires usable_forms(source, forms@), owner < forms@.len(),
    ensures child_bounds(forms@, owner, children@), covers_expression_children(source, forms@, owner, children@),
{
    match read_shape(source, forms, owner) {
        Ok(Expression::Annotated { annotation: _annotation, value }) => {
            proof { assert(tagged_arguments(source, forms@, owner, "as-type", true) == Some((_annotation, value))); }
            let mut children = Vec::new();
            children.push(value);
            assert(covers_expression_children(source, forms@, owner, children@)) by {
                assert forall|at: usize| #[trigger] expression_child(source, forms@, owner, at).is_some()
                    implies children@.contains(expression_child(source, forms@, owner, at)->Some_0) by {
                    assert(expression_child(source, forms@, owner, at) == Some(value));
                    assert(children@[0] == value);
                };
            };
            children
        }
        Ok(Expression::Conditional { condition, yes, no }) => {
            proof { assert(children3(forms@, owner) == Some((condition, yes, no))); }
            let children = three_slots(forms, owner, condition, yes, no);
            proof { cover_three(source, forms@, owner, children@, condition, yes, no); }
            children
        }
        Ok(Expression::Fold(header)) => {
            let children = three_slots(forms, owner, header.input, header.initial, header.body);
            proof { cover_three(source, forms@, owner, children@, header.input, header.initial, header.body); }
            children
        }
        Ok(Expression::Let) => match read_let_structure(source, forms, owner) {
            Ok(header) => {
                let children = let_slots(forms, owner, &header);
                assert(covers_expression_children(source, forms@, owner, children@)) by {
                    assert forall|at: usize| #[trigger] expression_child(source, forms@, owner, at).is_some()
                        implies children@.contains(expression_child(source, forms@, owner, at)->Some_0) by {
                        if !contains(forms@, header.body, at) {
                            assert(expression_child(source, forms@, owner, at) ==
                                binding_containing(forms@, header.bindings@, at, 0));
                        }
                    };
                };
                children
            }
            Err(_) => Vec::new(),
        },
        Ok(Expression::List) => {
            let Form::List { end, .. } = &forms[owner] else { unreachable!() };
            let _length = forms.len();
            assert(owner + 2 <= *end <= _length);
            let children = argument_slots(forms, owner, owner + 2, *end);
            proof { cover_arguments(source, forms@, owner, children@); }
            children
        }
        _ => match read_named_head(source, forms, owner) {
            Some((head, end, _)) => {
                let children = argument_slots(forms, owner, head + 1, end);
                proof { cover_arguments(source, forms@, owner, children@); }
                children
            }
            None => Vec::new(),
        },
    }
}

proof fn cover_three(
    source: &str, forms: Seq<Form>, owner: usize, children: Seq<usize>, first: usize, second: usize, third: usize,
)
    requires
        (shape(source, forms, owner) == Ok(Expression::Conditional { condition: first, yes: second, no: third })
            || (shape(source, forms, owner) matches Ok(Expression::Fold(header))
                && header.input == first && header.initial == second && header.body == third)),
        children == seq![first, second, third],
    ensures covers_expression_children(source, forms, owner, children),
{
    assert forall|at: usize| #[trigger] expression_child(source, forms, owner, at).is_some()
        implies children.contains(expression_child(source, forms, owner, at)->Some_0) by {
        let child = expression_child(source, forms, owner, at)->Some_0;
        assert(first_containing(forms, at, first, second, third) == Some(child));
        if child == first { assert(children[0] == child); }
        else if child == second { assert(children[1] == child); }
        else { assert(children[2] == child); }
    };
}

proof fn cover_arguments(source: &str, forms: Seq<Form>, owner: usize, children: Seq<usize>)
    requires
        (shape(source, forms, owner) == Ok(Expression::List)
            || (named_call_head(source, forms, owner)
                && !(shape(source, forms, owner) matches Ok(Expression::Annotated { .. }))
                && !(shape(source, forms, owner) matches Ok(Expression::Conditional { .. }))
                && !(shape(source, forms, owner) matches Ok(Expression::Fold(_)))
                && shape(source, forms, owner) != Ok(Expression::Let))),
        forall|at: usize| #[trigger] argument_containing(forms, (owner + 2) as usize, subtree_limit(forms, owner), at)
            matches Some(child) ==> children.contains(child),
    ensures covers_expression_children(source, forms, owner, children),
{
    assert forall|at: usize| #[trigger] expression_child(source, forms, owner, at).is_some()
        implies children.contains(expression_child(source, forms, owner, at)->Some_0) by {
        assert(expression_child(source, forms, owner, at)
            == argument_containing(forms, (owner + 2) as usize, subtree_limit(forms, owner), at));
    };
}

fn three_slots(_forms: &[Form], _owner: usize, first: usize, second: usize, third: usize) -> (children: Vec<usize>)
    requires _owner < first < second < third < subtree_limit(_forms@, _owner),
    ensures children@ == seq![first, second, third], child_bounds(_forms@, _owner, children@),
{
    let mut children = Vec::new();
    children.push(first);
    children.push(second);
    children.push(third);
    children
}

pub(in crate::ncg2m) open spec fn slot_marked(mask: Seq<bool>, root: usize, at: usize) -> bool {
    root <= at < root + mask.len() && mask[at - root]
}

#[verifier::opaque]
spec fn slot_frontier(source: &str, forms: Seq<Form>, mask: Seq<bool>, root: usize, next: usize) -> bool {
    forall|at: usize| #[trigger] expression_slot(source, forms, root, at) && !slot_marked(mask, root, at)
        ==> exists|pending: usize| next <= pending < root + mask.len()
            && #[trigger] slot_marked(mask, root, pending)
            && #[trigger] expression_slot(source, forms, pending, at)
}

spec fn preserved_marks(before: Seq<bool>, after: Seq<bool>) -> bool {
    &&& before.len() == after.len()
    &&& forall|i: int| 0 <= i < before.len() && #[trigger] before[i] ==> after[i]
}

proof fn next_expression_on_path(source: &str, forms: Seq<Form>, parent: usize, target: usize)
    -> (next: usize)
    requires expression_slot(source, forms, parent, target), parent != target,
    ensures
        parent < next,
        expression_child(source, forms, parent, target) == Some(next),
        expression_slot(source, forms, next, target),
{
    expression_child(source, forms, parent, target)->Some_0
}

proof fn advance_slot_frontier(
    source: &str, forms: Seq<Form>, before: Seq<bool>, after: Seq<bool>, root: usize, cursor: usize,
)
    requires
        cursor < usize::MAX,
        slot_frontier(source, forms, before, root, cursor),
        preserved_marks(before, after),
        forall|at: usize| slot_marked(before, root, cursor)
            ==> match #[trigger] expression_child(source, forms, cursor, at) {
                Some(child) => slot_marked(after, root, child),
                None => true,
            },
    ensures slot_frontier(source, forms, after, root, (cursor + 1) as usize),
{
    reveal(slot_frontier);
    assert forall|at: usize| #[trigger] expression_slot(source, forms, root, at) && !slot_marked(after, root, at)
        implies exists|pending: usize| cursor + 1 <= pending < root + after.len()
            && #[trigger] slot_marked(after, root, pending)
            && #[trigger] expression_slot(source, forms, pending, at) by {
        assert(!slot_marked(before, root, at));
        let pending = choose|pending: usize| cursor <= pending < root + before.len()
            && #[trigger] slot_marked(before, root, pending)
            && #[trigger] expression_slot(source, forms, pending, at);
        assert(slot_marked(after, root, pending));
        if pending == cursor {
            assert(pending != at);
            let child = next_expression_on_path(source, forms, pending, at);
            assert(slot_marked(after, root, child));
        }
    };
}

fn mark_children(
    _forms: &[Form], root: usize, _owner: usize, children: &[usize], mask: &mut Vec<bool>,
)
    requires
        root <= _owner < subtree_limit(_forms@, _owner) <= root + old(mask)@.len(),
        child_bounds(_forms@, _owner, children@),
    ensures
        preserved_marks(old(mask)@, final(mask)@),
        forall|child: usize| #[trigger] children@.contains(child)
            ==> slot_marked(final(mask)@, root, child),
{
    let mut i = 0;
    while i < children.len()
        invariant
            root <= _owner < subtree_limit(_forms@, _owner) <= root + old(mask)@.len(),
            child_bounds(_forms@, _owner, children@),
            i <= children@.len(),
            preserved_marks(old(mask)@, mask@),
            forall|j: int| 0 <= j < i ==> slot_marked(mask@, root, #[trigger] children@[j]),
        decreases children@.len() - i,
    {
        let child = children[i];
        assert(_owner < child < subtree_limit(_forms@, _owner));
        let ghost previous = mask@;
        mask.set(child - root, true);
        proof {
            assert forall|j: int| 0 <= j < i implies slot_marked(mask@, root, #[trigger] children@[j]) by {
                assert(slot_marked(previous, root, children@[j]));
            };
        }
        i += 1;
    }
    proof {
        assert forall|child: usize| #[trigger] children@.contains(child) implies slot_marked(mask@, root, child) by {
            let j = choose|j: int| 0 <= j < children@.len() && (#[trigger] children@[j]) == child;
            assert(slot_marked(mask@, root, children@[j]));
        };
    }
}

/// 型検査の結果とは独立に、本体からたどれる式の位置をすべて記録する。
pub(in crate::ncg2m) fn mark_expression_slots(source: &str, forms: &[Form], root: usize) -> (mask: Vec<bool>)
    requires usable_forms(source, forms@), root < forms@.len(),
    ensures
        mask@.len() == subtree_limit(forms@, root) - root,
        forall|at: usize| #[trigger] expression_slot(source, forms@, root, at) ==> slot_marked(mask@, root, at),
{
    let _length = forms.len();
    let end = subtree_end(forms, root);
    proof {
        match forms@[root as int] {
            Form::List { end: stop, .. } => assert(root < stop == end <= forms@.len()),
            Form::Atom { .. } => assert(end == root + 1 <= forms@.len()),
        }
    }
    let mut mask = Vec::<bool>::new();
    mask.push(true);
    while mask.len() < end - root
        invariant
            root < end <= forms@.len(),
            1 <= mask@.len() <= end - root,
            mask@[0],
        decreases end - root - mask@.len(),
    {
        mask.push(false);
    }

    let mut cursor = root;
    assert(slot_frontier(source, forms@, mask@, root, cursor)) by {
        reveal(slot_frontier);
        assert(slot_marked(mask@, root, root));
        assert forall|at: usize| #[trigger] expression_slot(source, forms@, root, at) && !slot_marked(mask@, root, at)
            implies exists|pending: usize| cursor <= pending < root + mask@.len()
                && #[trigger] slot_marked(mask@, root, pending)
                && #[trigger] expression_slot(source, forms@, pending, at) by {
            assert(cursor == root && root < root + mask@.len());
        };
    };
    while cursor < end
        invariant
            usable_forms(source, forms@),
            root <= cursor <= end <= forms@.len(),
            end == subtree_limit(forms@, root),
            mask@.len() == end - root,
            slot_frontier(source, forms@, mask@, root, cursor),
        decreases end - cursor,
    {
        let ghost before = mask@;
        if mask[cursor - root] {
            let children = read_slot_children(source, forms, cursor);
            proof {
                if root < cursor {
                    assert(forms@[root as int] is List);
                    super::super::super::super::forms::child_stays_inside(forms@, root, cursor);
                }
                assert(cursor < subtree_limit(forms@, cursor) <= end);
            }
            mark_children(forms, root, cursor, children.as_slice(), &mut mask);
            assert forall|at: usize| #[trigger] expression_child(source, forms@, cursor, at).is_some()
                implies slot_marked(mask@, root, expression_child(source, forms@, cursor, at)->Some_0) by {
                assert(covers_expression_children(source, forms@, cursor, children@));
            };
        }
        proof { advance_slot_frontier(source, forms@, before, mask@, root, cursor); }
        cursor += 1;
    }
    assert forall|at: usize| #[trigger] expression_slot(source, forms@, root, at)
        implies slot_marked(mask@, root, at) by {
        reveal(slot_frontier);
    };
    mask
}
}
