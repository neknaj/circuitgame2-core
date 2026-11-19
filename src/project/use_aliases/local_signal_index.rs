//! 関数内の名前と駆動元を対応づける索引。

use super::OutputDriver;
use crate::project::declarations::path_index::PathIndex;
use alloc::collections::BTreeMap;
#[cfg(verus_only)]
use vstd::laws_cmp::obeys_cmp;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

pub(super) struct LocalSignalIndex {
    paths: PathIndex,
    drivers: BTreeMap<usize, OutputDriver>,
    bindings: Ghost<Map<Seq<u8>, OutputDriver>>,
}

// 駆動元を登録した終端だけを束縛とみなす。接頭辞を通過しただけでは束縛は生じない。
spec fn drivers_match(
    paths: Seq<Seq<u8>>, drivers: Map<usize, OutputDriver>, bindings: Map<Seq<u8>, OutputDriver>,
) -> bool {
    &&& forall|node: usize| #[trigger] drivers.contains_key(node) ==> {
        &&& node < paths.len()
        &&& bindings.contains_key(paths[node as int])
        &&& bindings[paths[node as int]] == drivers[node]
    }
    &&& forall|word: Seq<u8>| #[trigger] bindings.contains_key(word) ==>
        exists|node: usize| #[trigger] drivers.contains_key(node) && node < paths.len()
            && paths[node as int] == word
}

proof fn extend_paths(
    before: Seq<Seq<u8>>, after: Seq<Seq<u8>>, drivers: Map<usize, OutputDriver>,
    bindings: Map<Seq<u8>, OutputDriver>,
)
    requires before.is_prefix_of(after), drivers_match(before, drivers, bindings),
    ensures drivers_match(after, drivers, bindings),
{
    assert forall|word: Seq<u8>| #[trigger] bindings.contains_key(word) implies
        exists|node: usize| #[trigger] drivers.contains_key(node) && node < after.len()
            && after[node as int] == word by {
        let node = choose|node: usize| #[trigger] drivers.contains_key(node) && node < before.len()
            && before[node as int] == word;
        assert(after[node as int] == before[node as int]);
    };
}

impl LocalSignalIndex {
    pub(super) closed spec fn bindings(&self) -> Map<Seq<u8>, OutputDriver> {
        self.bindings@
    }

    pub(super) closed spec fn valid(&self) -> bool {
        self.paths.valid() && drivers_match(self.paths.paths(), self.drivers@, self.bindings@)
    }

    pub(super) fn new() -> (index: Self)
        ensures index.valid(), index.bindings() == Map::<Seq<u8>, OutputDriver>::empty(),
    {
        let paths = PathIndex::new();
        let drivers = BTreeMap::new();
        Self { paths, drivers, bindings: Ghost(Map::empty()) }
    }

    // 同じ名前に対応する終端が複数存在しないことを使い、抽象的な束縛と節点の駆動元を対応づける。
    proof fn terminal_binding(&self, word: Seq<u8>, node: usize)
        requires self.valid(), node < self.paths.paths().len(), self.paths.paths()[node as int] == word,
        ensures self.drivers@.contains_key(node) == self.bindings().contains_key(word),
            self.drivers@.contains_key(node) ==> self.drivers@[node] == self.bindings()[word],
    {
        if self.bindings().contains_key(word) {
            let other = choose|other: usize| #[trigger] self.drivers@.contains_key(other)
                && other < self.paths.paths().len() && self.paths.paths()[other as int] == word;
            self.paths.same_path(other as int, node as int);
        }
    }

    /// 名前と完全に一致する束縛を返す。
    pub(super) fn lookup(&self, word: &str) -> (result: Option<OutputDriver>)
        requires self.valid(),
        ensures result == if self.bindings().contains_key(word.spec_bytes()) {
            Some(self.bindings()[word.spec_bytes()])
        } else { None },
    {
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<usize>());
            self.paths.empty_root();
        }
        let Some(node) = self.paths.follow(0, word.as_bytes()) else {
            proof {
                if self.bindings().contains_key(word.spec_bytes()) {
                    let node = choose|node: usize| #[trigger] self.drivers@.contains_key(node)
                        && node < self.paths.paths().len() && self.paths.paths()[node as int] == word.spec_bytes();
                    assert(word.spec_bytes().is_prefix_of(self.paths.paths()[node as int]));
                    assert(false);
                }
            }
            return None;
        };
        proof { self.terminal_binding(word.spec_bytes(), node); }
        match self.drivers.get(&node) {
            Some(driver) => Some(*driver),
            None => None,
        }
    }

    /// 新しい名前を登録する。登録済みの名前には、先に登録した駆動元を返す。
    /// `Some(None)` は登録成功、`Some(Some(driver))` は登録済み、`None` は節点の添字の枯渇を表す。
    pub(super) fn insert_if_absent(&mut self, word: &str, value: OutputDriver)
        -> (result: Option<Option<OutputDriver>>)
        requires old(self).valid(),
        ensures final(self).valid(), match result {
            None => final(self).bindings() == old(self).bindings(),
            Some(previous) => {
                &&& previous == if old(self).bindings().contains_key(word.spec_bytes()) {
                    Some(old(self).bindings()[word.spec_bytes()])
                } else { None }
                &&& final(self).bindings() == if previous.is_none() {
                    old(self).bindings().insert(word.spec_bytes(), value)
                } else { old(self).bindings() }
            },
        },
    {
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<usize>());
            self.paths.empty_root();
        }
        let ghost paths_before = self.paths.paths();
        let node = self.paths.extend_bytes(0, word.as_bytes());
        proof { extend_paths(paths_before, self.paths.paths(), self.drivers@, self.bindings@); }
        let node = node?;
        proof { self.terminal_binding(word.spec_bytes(), node); }
        if let Some(previous) = self.drivers.get(&node) {
            return Some(Some(*previous));
        }
        let ghost prior_drivers = self.drivers@;
        let ghost prior_bindings = self.bindings@;
        let ghost bytes = word.spec_bytes();
        let _ = self.drivers.insert(node, value);
        self.bindings = Ghost(prior_bindings.insert(bytes, value));
        assert forall|other: usize| #[trigger] self.drivers@.contains_key(other) implies {
            &&& other < self.paths.paths().len()
            &&& self.bindings@.contains_key(self.paths.paths()[other as int])
            &&& self.bindings@[self.paths.paths()[other as int]] == self.drivers@[other]
        } by {
            if other != node {
                assert(prior_drivers.contains_key(other));
                self.paths.same_path(other as int, node as int);
            }
        };
        assert forall|key: Seq<u8>| #[trigger] self.bindings@.contains_key(key) implies
            exists|other: usize| #[trigger] self.drivers@.contains_key(other)
                && other < self.paths.paths().len() && self.paths.paths()[other as int] == key by {
            if key == bytes {
                assert(self.drivers@.contains_key(node));
            } else {
                assert(prior_bindings.contains_key(key));
                let other = choose|other: usize| #[trigger] prior_drivers.contains_key(other)
                    && other < self.paths.paths().len() && self.paths.paths()[other as int] == key;
                assert(self.drivers@.contains_key(other));
            }
        };
        Some(None)
    }
}

} // verus!
