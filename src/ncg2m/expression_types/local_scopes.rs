//! 局所束縛を追加し、外側の環境への参照を保持する。

use super::*;

verus! {

pub(super) type Scope = Option<usize>;

#[derive(Clone, Copy)]
struct Entry<'a> {
    parent: Scope,
    local: LocalType<'a>,
}

pub(super) struct LocalScopes<'a> {
    entries: Vec<Entry<'a>>,
}

spec fn scope_in_bounds(size: nat, scope: Scope) -> bool {
    scope matches Some(index) ==> index < size
}

spec fn scope_rank(scope: Scope) -> nat {
    match scope {
        Some(index) => index as nat + 1,
        None => 0,
    }
}

#[verifier::opaque]
spec fn scope_types(entries: Seq<Entry>, scope: Scope) -> Seq<TypeBinding>
    decreases scope_rank(scope),
{
    match scope {
        Some(index) if index < entries.len() && scope_in_bounds(index as nat, entries[index as int].parent) => {
            let entry = entries[index as int];
            seq![(entry.local.name.spec_bytes(), entry.local.ty)] + scope_types(entries, entry.parent)
        }
        _ => Seq::empty(),
    }
}

proof fn scope_types_preserved(entries: Seq<Entry>, new: Entry, scope: Scope)
    requires scope_in_bounds(entries.len(), scope),
    ensures scope_types(entries, scope) == scope_types(entries.push(new), scope),
    decreases scope_rank(scope),
{
    reveal(scope_types);
    if let Some(index) = scope {
        let after = entries.push(new);
        assert(after[index as int] == entries[index as int]);
        if scope_in_bounds(index as nat, entries[index as int].parent) {
            let parent = entries[index as int].parent;
            scope_types_preserved(entries, new, parent);
        }
    }
}

spec fn search_local(env: Seq<TypeBinding>, name: Seq<u8>) -> Option<TypeShape> {
    parameter_type(env, name, 0)
}

proof fn concatenated_lookup(front: Seq<TypeBinding>, after: Seq<TypeBinding>, name: Seq<u8>, at: nat)
    requires at <= front.len(),
    ensures parameter_type(front + after, name, at)
        == match parameter_type(front, name, at) {
            Some(ty) => Some(ty),
            None => parameter_type(after, name, 0),
        },
    decreases front.len() - at,
{
    reveal_with_fuel(parameter_type, 2);
    if at == front.len() {
        suffix_lookup(front, after, name, 0);
    } else if front[at as int].0 != name {
        concatenated_lookup(front, after, name, at + 1);
    }
}

proof fn suffix_lookup(front: Seq<TypeBinding>, after: Seq<TypeBinding>, name: Seq<u8>, at: nat)
    ensures parameter_type(front + after, name, front.len() + at) == parameter_type(after, name, at),
    decreases after.len() - at,
{
    reveal_with_fuel(parameter_type, 2);
    if at < after.len() && after[at as int].0 != name {
        suffix_lookup(front, after, name, at + 1);
    }
}

impl<'a> LocalScopes<'a> {
    spec fn entries_ready(&self) -> bool {
        forall|i: int| 0 <= i < self.entries@.len() ==> scope_in_bounds(i as nat, (#[trigger] self.entries@[i]).parent)
    }

    pub(super) closed spec fn contains(&self, scope: Scope) -> bool {
        self.entries_ready() && scope_in_bounds(self.entries@.len(), scope)
    }

    pub(super) closed spec fn local_types(&self, scope: Scope) -> Seq<TypeBinding> {
        scope_types(self.entries@, scope)
    }

    pub(super) fn new() -> (scopes: Self)
        ensures scopes.contains(None), scopes.local_types(None) == Seq::<TypeBinding>::empty(),
    {
        proof { reveal(scope_types); }
        Self { entries: Vec::new() }
    }

    pub(super) fn extend(&mut self, parent: Scope, local: LocalType<'a>) -> (scope: Scope)
        requires old(self).contains(parent),
        ensures
            final(self).contains(scope),
            final(self).local_types(scope) == seq![(local.name.spec_bytes(), local.ty)] + old(self).local_types(parent),
            forall|old_scope: Scope| #[trigger] old(self).contains(old_scope) ==> {
                final(self).contains(old_scope)
                    && final(self).local_types(old_scope) == old(self).local_types(old_scope)
            },
    {
        let old_count = self.entries.len();
        let ghost before = self.entries@;
        let entry = Entry { parent, local };
        self.entries.push(entry);
        proof {
            reveal(scope_types);
            assert forall|i: int| 0 <= i < self.entries@.len() implies
                scope_in_bounds(i as nat, (#[trigger] self.entries@[i]).parent) by {
                if i < before.len() { assert(self.entries@[i] == before[i]); }
            };
            assert forall|old_scope: Scope| #[trigger] old(self).contains(old_scope) implies {
                self.contains(old_scope) && self.local_types(old_scope) == old(self).local_types(old_scope)
            } by {
                scope_types_preserved(before, entry, old_scope);
            };
        }
        Some(old_count)
    }

    fn find_local(&self, scope: Scope, word: &str) -> (result: Option<TypeShape>)
        requires self.contains(scope),
        ensures result == search_local(self.local_types(scope), word.spec_bytes()),
    {
        let mut current = scope;
        loop
            invariant
                self.entries_ready(), self.contains(current),
                search_local(self.local_types(scope), word.spec_bytes())
                    == search_local(self.local_types(current), word.spec_bytes()),
            decreases scope_rank(current),
        {
            reveal(scope_types);
            let Some(index) = current else { return None; };
            let entry = self.entries[index];
            if is_spelling(entry.local.name, word) {
                return Some(entry.local.ty);
            }
            proof {
                suffix_lookup(
                    seq![(entry.local.name.spec_bytes(), entry.local.ty)],
                    self.local_types(entry.parent), word.spec_bytes(), 0,
                );
            }
            current = entry.parent;
        }
    }

    pub(super) fn lookup(&self, parameters: &[SignatureParameter<'a>], scope: Scope, word: &str)
        -> (result: Option<TypeShape>)
        requires self.contains(scope),
        ensures result == parameter_type(self.local_types(scope) + environment_view(parameters@), word.spec_bytes(), 0),
    {
        proof {
            concatenated_lookup(self.local_types(scope), environment_view(parameters@), word.spec_bytes(), 0);
        }
        if let Some(ty) = self.find_local(scope, word) {
            Some(ty)
        } else {
            find_parameter(parameters, word)
        }
    }
}

}
