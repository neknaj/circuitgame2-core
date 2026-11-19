//! ファイルと名前空間ブロックごとに、別名を最初に指定した `use` を索引に載せる。

use crate::project::declarations::path_index::PathIndex;
use alloc::collections::BTreeMap;
#[cfg(verus_only)]
use vstd::laws_cmp::obeys_cmp;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

type Scope = (usize, Option<usize>);
type Terminal = (Scope, usize);

pub(super) struct AliasIndex {
    paths: PathIndex,
    first_uses: BTreeMap<Terminal, usize>,
    bindings: Ghost<Map<(Scope, Seq<u8>), usize>>,
}

// 同じ綴りを複数のスコープで共有しても、最初の指定はスコープごとに記録する。
spec fn first_uses_match(
    paths: Seq<Seq<u8>>, first_uses: Map<Terminal, usize>, bindings: Map<(Scope, Seq<u8>), usize>,
) -> bool {
    &&& forall|terminal: Terminal| #[trigger] first_uses.contains_key(terminal) ==> {
        let (scope, node) = terminal;
        &&& node < paths.len()
        &&& bindings.contains_key((scope, paths[node as int]))
        &&& bindings[(scope, paths[node as int])] == first_uses[terminal]
    }
    &&& forall|key: (Scope, Seq<u8>)| #[trigger] bindings.contains_key(key) ==>
        exists|node: usize| #[trigger] first_uses.contains_key((key.0, node))
            && node < paths.len() && paths[node as int] == key.1
}

proof fn extend_paths(
    before: Seq<Seq<u8>>, after: Seq<Seq<u8>>, first_uses: Map<Terminal, usize>,
    bindings: Map<(Scope, Seq<u8>), usize>,
)
    requires before.is_prefix_of(after), first_uses_match(before, first_uses, bindings),
    ensures first_uses_match(after, first_uses, bindings),
{
    assert forall|key: (Scope, Seq<u8>)| #[trigger] bindings.contains_key(key) implies
        exists|node: usize| #[trigger] first_uses.contains_key((key.0, node))
            && node < after.len() && after[node as int] == key.1 by {
        let node = choose|node: usize| #[trigger] first_uses.contains_key((key.0, node))
            && node < before.len() && before[node as int] == key.1;
        assert(after[node as int] == before[node as int]);
    };
}

impl AliasIndex {
    pub(super) closed spec fn bindings(&self) -> Map<(Scope, Seq<u8>), usize> {
        self.bindings@
    }

    pub(super) closed spec fn valid(&self) -> bool {
        self.paths.valid() && first_uses_match(self.paths.paths(), self.first_uses@, self.bindings@)
    }

    pub(super) fn new() -> (index: Self)
        ensures index.valid(), index.bindings() == Map::<(Scope, Seq<u8>), usize>::empty(),
    {
        let paths = PathIndex::new();
        let first_uses = BTreeMap::new();
        Self { paths, first_uses, bindings: Ghost(Map::empty()) }
    }

    proof fn terminal_binding(&self, scope: Scope, word: Seq<u8>, node: usize)
        requires self.valid(), node < self.paths.paths().len(), self.paths.paths()[node as int] == word,
        ensures
            self.first_uses@.contains_key((scope, node)) == self.bindings().contains_key((scope, word)),
            self.first_uses@.contains_key((scope, node)) ==>
                self.first_uses@[(scope, node)] == self.bindings()[(scope, word)],
    {
        if self.bindings().contains_key((scope, word)) {
            let other = choose|other: usize| #[trigger] self.first_uses@.contains_key((scope, other))
                && other < self.paths.paths().len() && self.paths.paths()[other as int] == word;
            self.paths.same_path(other as int, node as int);
        }
    }

    /// 指定したファイルとブロックで、その別名を最初に指定した添字を返す。
    pub(super) fn lookup(&self, scope: Scope, word: &str) -> (result: Option<usize>)
        requires self.valid(),
        ensures result == if self.bindings().contains_key((scope, word.spec_bytes())) {
            Some(self.bindings()[(scope, word.spec_bytes())])
        } else { None },
    {
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<Terminal>());
            self.paths.empty_root();
        }
        let Some(node) = self.paths.follow(0, word.as_bytes()) else {
            proof {
                let bytes = word.spec_bytes();
                if self.bindings().contains_key((scope, bytes)) {
                    let node = choose|node: usize| #[trigger] self.first_uses@.contains_key((scope, node))
                        && node < self.paths.paths().len() && self.paths.paths()[node as int] == bytes;
                    assert(bytes.is_prefix_of(self.paths.paths()[node as int]));
                    assert(false);
                }
            }
            return None;
        };
        proof { self.terminal_binding(scope, word.spec_bytes(), node); }
        match self.first_uses.get(&(scope, node)) {
            Some(rank) => Some(*rank),
            None => None,
        }
    }

    /// 未登録の別名を追加する。登録済みなら最初の指定を返す。
    ///
    /// `Some(None)` は新規登録、`Some(Some(first))` は登録済み、`None` は節点の添字の枯渇を示す。
    pub(super) fn insert_if_absent(&mut self, scope: Scope, word: &str, at: usize) -> (result: Option<Option<usize>>)
        requires old(self).valid(),
        ensures final(self).valid(), match result {
            None => final(self).bindings() == old(self).bindings(),
            Some(previous) => {
                let key = (scope, word.spec_bytes());
                &&& previous == if old(self).bindings().contains_key(key) {
                    Some(old(self).bindings()[key])
                } else { None }
                &&& final(self).bindings() == if previous.is_none() {
                    old(self).bindings().insert(key, at)
                } else { old(self).bindings() }
            },
        },
    {
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<Terminal>());
            self.paths.empty_root();
        }
        let ghost paths_before = self.paths.paths();
        let node = self.paths.extend_bytes(0, word.as_bytes());
        proof { extend_paths(paths_before, self.paths.paths(), self.first_uses@, self.bindings@); }
        let node = node?;
        proof { self.terminal_binding(scope, word.spec_bytes(), node); }
        let terminal = (scope, node);
        if let Some(previous) = self.first_uses.get(&terminal) {
            return Some(Some(*previous));
        }
        let ghost prior_first = self.first_uses@;
        let ghost prior_bindings = self.bindings@;
        let ghost key = (scope, word.spec_bytes());
        let _ = self.first_uses.insert(terminal, at);
        self.bindings = Ghost(prior_bindings.insert(key, at));
        assert forall|other: Terminal| #[trigger] self.first_uses@.contains_key(other) implies {
            let (other_scope, other_node) = other;
            &&& other_node < self.paths.paths().len()
            &&& self.bindings@.contains_key((other_scope, self.paths.paths()[other_node as int]))
            &&& self.bindings@[(other_scope, self.paths.paths()[other_node as int])] == self.first_uses@[other]
        } by {
            if other != terminal {
                assert(prior_first.contains_key(other));
                self.paths.same_path(other.1 as int, node as int);
            }
        };
        assert forall|other: (Scope, Seq<u8>)| #[trigger] self.bindings@.contains_key(other) implies
            exists|id: usize| #[trigger] self.first_uses@.contains_key((other.0, id))
                && id < self.paths.paths().len() && self.paths.paths()[id as int] == other.1 by {
            if other == key {
                assert(self.first_uses@.contains_key(terminal));
            } else {
                assert(prior_bindings.contains_key(other));
                let id = choose|id: usize| #[trigger] prior_first.contains_key((other.0, id))
                    && id < self.paths.paths().len() && self.paths.paths()[id as int] == other.1;
                assert(self.first_uses@.contains_key((other.0, id)));
            }
        };
        Some(None)
    }
}

} // verus!
