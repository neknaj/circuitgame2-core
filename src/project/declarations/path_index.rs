//! 完全修飾名のバイト列を共有し、名前の接頭辞に添字を割り当てる。

use super::super::name_keys::NameKey;
#[cfg(verus_only)]
use super::super::name_keys::{component_ends_at, full_name_bytes};
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
#[cfg(verus_only)]
use vstd::laws_cmp::obeys_cmp;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

type Edge = (usize, u8);

pub(in crate::project) struct PathIndex {
    edges: BTreeMap<Edge, usize>,
    next: usize,
    paths: Ghost<Seq<Seq<u8>>>,
    parents: Ghost<Seq<Edge>>,
}

// BTreeMap の検索・挿入と整数の比較には、固定版 vstd の標準ライブラリ契約を使う。
impl PathIndex {
    pub(in crate::project) closed spec fn paths(&self) -> Seq<Seq<u8>> {
        self.paths@
    }

    pub(in crate::project) closed spec fn valid(&self) -> bool {
        &&& self.next == self.paths@.len()
        &&& self.parents@.len() == self.paths@.len()
        &&& self.next >= 1
        &&& self.paths@[0] == Seq::<u8>::empty()
        &&& forall|i: int, j: int| 0 <= i < j < self.paths@.len()
            ==> (#[trigger] self.paths@[i]) != (#[trigger] self.paths@[j])
        &&& forall|parent: usize, byte: u8| {
            #[trigger] self.edges@.contains_key((parent, byte)) ==> {
                let child = self.edges@[(parent, byte)];
                &&& parent < child < self.next
                &&& self.paths@[child as int] == self.paths@[parent as int].push(byte)
            }
        }
        &&& forall|i: int| 1 <= i < self.paths@.len() ==> {
            let edge = #[trigger] self.parents@[i];
            self.edges@.contains_key(edge) && self.edges@[edge] == i
        }
    }

    pub(in crate::project) fn new() -> (index: Self)
        ensures index.valid(), index.paths() == seq![Seq::<u8>::empty()],
    {
        let ghost initial = seq![Seq::<u8>::empty()];
        let ghost root_parent = seq![(0usize, 0u8)];
        Self { edges: BTreeMap::new(), next: 1, paths: Ghost(initial), parents: Ghost(root_parent) }
    }

    pub(in crate::project) proof fn same_path(&self, first: int, second: int)
        requires self.valid(), 0 <= first < self.paths().len(), 0 <= second < self.paths().len(),
        ensures self.paths()[first] == self.paths()[second] <==> first == second,
    {
        reveal(PathIndex::valid);
    }

    pub(in crate::project) proof fn empty_root(&self)
        requires self.valid(),
        ensures self.paths().len() >= 1, self.paths()[0] == Seq::<u8>::empty(),
    {
        reveal(PathIndex::valid);
    }

    proof fn missing_edge(&self, parent: usize, byte: u8)
        requires self.valid(), parent < self.paths().len(), !self.edges@.contains_key((parent, byte)),
        ensures forall|i: int| 0 <= i < self.paths().len() ==>
            (#[trigger] self.paths()[i]) != self.paths()[parent as int].push(byte),
    {
        reveal(PathIndex::valid);
        let path = self.paths()[parent as int].push(byte);
        assert forall|i: int| 0 <= i < self.paths().len() implies (#[trigger] self.paths()[i]) != path by {
            if i == 0 {
                assert(path.len() > 0);
            } else if self.paths()[i] == path {
                let (p, b) = self.parents@[i];
                assert(self.edges@.contains_key((p, b)) && self.edges@[(p, b)] == i);
                assert(self.paths()[i] == self.paths()[p as int].push(b));
                assert(path[path.len() as int - 1] == b);
                assert(path[path.len() as int - 1] == byte);
                assert(self.paths()[p as int].len() == self.paths()[parent as int].len());
                assert forall|k: int| 0 <= k < self.paths()[p as int].len()
                    implies self.paths()[p as int][k] == self.paths()[parent as int][k] by {
                    assert(path[k] == self.paths()[p as int][k]);
                    assert(path[k] == self.paths()[parent as int][k]);
                };
                assert(self.paths()[p as int] =~= self.paths()[parent as int]);
                self.same_path(p as int, parent as int);
                assert(p == parent && b == byte);
            }
        };
    }

    proof fn prefix_node(&self, node: int, len: int) -> (prefix: int)
        requires self.valid(), 0 <= node < self.paths().len(), 0 <= len <= self.paths()[node].len(),
        ensures 0 <= prefix < self.paths().len(), self.paths()[prefix] == self.paths()[node].take(len),
        decreases node,
    {
        reveal(PathIndex::valid);
        if len == self.paths()[node].len() {
            assert(self.paths()[node].take(len) =~= self.paths()[node]);
            node
        } else {
            assert(node != 0);
            let (p, b) = self.parents@[node];
            assert(self.edges@.contains_key((p, b)) && self.edges@[(p, b)] == node);
            assert(self.paths()[node] == self.paths()[p as int].push(b));
            assert(self.paths()[node].take(len) =~= self.paths()[p as int].take(len));
            self.prefix_node(p as int, len)
        }
    }

    pub(in crate::project) fn follow(&self, parent: usize, bytes: &[u8]) -> (result: Option<usize>)
        requires self.valid(), parent < self.paths().len(),
        ensures
            result matches Some(node) ==> node < self.paths().len()
                && self.paths()[node as int] == self.paths()[parent as int] + bytes@,
            result.is_none() ==> forall|i: int| 0 <= i < self.paths().len()
                ==> !(self.paths()[parent as int] + bytes@).is_prefix_of(#[trigger] self.paths()[i]),
    {
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            reveal(PathIndex::valid);
            assert(obeys_cmp::<Edge>());
        }
        let mut node = parent;
        let mut at = 0;
        assert(bytes@.take(0) =~= Seq::<u8>::empty());
        while at < bytes.len()
            invariant
                self.valid(), parent < self.paths().len(), node < self.paths().len(),
                at <= bytes@.len(),
                self.paths()[node as int] == self.paths()[parent as int] + bytes@.take(at as int),
                obeys_cmp::<Edge>(),
            decreases bytes@.len() - at,
        {
            let byte = bytes[at];
            let edge = (node, byte);
            let ghost part = self.paths()[node as int].push(byte);
            assert(bytes@.take(at as int).push(bytes@[at as int]) =~= bytes@.take(at + 1));
            assert(part =~= self.paths()[parent as int] + bytes@.take(at + 1));
            let Some(next) = self.edges.get(&edge) else {
                proof {
                    self.missing_edge(node, byte);
                    assert forall|i: int| 0 <= i < self.paths().len() implies
                        !(self.paths()[parent as int] + bytes@).is_prefix_of(#[trigger] self.paths()[i]) by {
                        if (self.paths()[parent as int] + bytes@).is_prefix_of(self.paths()[i]) {
                            let p = self.prefix_node(i, part.len() as int);
                            assert(self.paths()[i].take(part.len() as int) =~= part);
                            assert(self.paths()[p] != part);
                        }
                    };
                }
                return None;
            };
            node = *next;
            at += 1;
        }
        assert(bytes@.take(at as int) =~= bytes@);
        Some(node)
    }

    pub(super) fn find(&self, key: NameKey) -> (result: Option<usize>)
        requires self.valid(),
        ensures
            result matches Some(node) ==> node < self.paths().len() && self.paths()[node as int] == full_name_bytes(key),
            result.is_none() ==> forall|i: int| 0 <= i < self.paths().len() ==> (#[trigger] self.paths()[i]) != full_name_bytes(key),
    {
        proof { reveal(PathIndex::valid); }
        let prefix = if let Some(parent) = key.parent {
            let parent_node = self.follow(0, parent.as_bytes())?;
            let separator = [b':', b':'];
            assert(separator@ =~= seq![b':', b':']);
            self.follow(parent_node, separator.as_slice())?
        } else {
            0
        };
        self.follow(prefix, key.name.as_bytes())
    }

    // 接頭辞を延ばすたびに最長で一つ添字を追加する。空きが尽きた場合は呼び出し側で扱う。
    pub(super) fn extend(&mut self, parent: usize, byte: u8) -> (child: Option<usize>)
        requires old(self).valid(), parent < old(self).paths().len(),
        ensures
            final(self).valid(),
            old(self).paths().is_prefix_of(final(self).paths()),
            child matches Some(child) ==> child < final(self).paths().len()
                && final(self).paths()[child as int] == old(self).paths()[parent as int].push(byte),
            child.is_none() ==> final(self).paths() == old(self).paths()
                && final(self).paths().len() == usize::MAX,
    {
        let edge = (parent, byte);
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            reveal(PathIndex::valid);
            assert(obeys_cmp::<Edge>());
        }
        if let Some(child) = self.edges.get(&edge) {
            return Some(*child);
        }
        if self.next == usize::MAX {
            return None;
        }
        let child = self.next;
        let ghost old_paths = self.paths@;
        let ghost old_edges = self.edges@;
        let ghost old_parents = self.parents@;
        let ghost path = old_paths[parent as int].push(byte);
        proof { self.missing_edge(parent, byte); }
        let _ = self.edges.insert(edge, child);
        self.next = child + 1;
        self.paths = Ghost(old_paths.push(path));
        self.parents = Ghost(old_parents.push(edge));
        assert forall|i: int| 1 <= i < self.paths@.len() implies {
            let current = #[trigger] self.parents@[i];
            self.edges@.contains_key(current) && self.edges@[current] == i
        } by {
            if i == child {
                assert(self.edges@.contains_key(edge) && self.edges@[edge] == child);
            } else {
                let previous = old_parents[i];
                assert(old_edges.contains_key(previous) && old_edges[previous] == i);
                assert(previous != edge);
                assert(self.edges@.contains_key(previous) && self.edges@[previous] == i);
            }
        };
        assert forall|i: int, j: int| 0 <= i < j < self.paths@.len()
            implies (#[trigger] self.paths@[i]) != (#[trigger] self.paths@[j]) by {
            assert(self.paths@[i] == old_paths[i]);
            if j == child {
                assert(old_paths[i] != path);
            } else {
                assert(self.paths@[j] == old_paths[j]);
            }
        };
        Some(child)
    }

    pub(in crate::project) fn extend_bytes(&mut self, parent: usize, bytes: &[u8]) -> (child: Option<usize>)
        requires old(self).valid(), parent < old(self).paths().len(),
        ensures
            final(self).valid(),
            old(self).paths().is_prefix_of(final(self).paths()),
            child matches Some(child) ==> child < final(self).paths().len()
                && final(self).paths()[child as int] == old(self).paths()[parent as int] + bytes@,
            child.is_none() ==> final(self).paths().len() == usize::MAX,
    {
        let ghost initial = self.paths();
        let mut node = parent;
        let mut at = 0;
        let mut exhausted = false;
        assert(bytes@.take(0) =~= Seq::<u8>::empty());
        while at < bytes.len() && !exhausted
            invariant
                self.valid(),
                initial == old(self).paths(),
                initial.is_prefix_of(self.paths()),
                exhausted ==> self.paths().len() == usize::MAX,
                parent < initial.len(),
                node < self.paths().len(),
                at <= bytes@.len(),
                self.paths()[node as int] == initial[parent as int] + bytes@.take(at as int),
            decreases bytes@.len() - at, if exhausted { 0int } else { 1int },
        {
            match self.extend(node, bytes[at]) {
                Some(next) => {
                    assert(bytes@.take(at as int).push(bytes@[at as int]) =~= bytes@.take(at + 1));
                    node = next;
                    at += 1;
                },
                None => {
                    exhausted = true;
                },
            }
        }
        if exhausted {
            None
        } else {
            assert(bytes@.take(at as int) =~= bytes@);
            Some(node)
        }
    }

    pub(super) fn declaration(&mut self, key: NameKey) -> (node: Option<usize>)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            node matches Some(node) ==> old(self).paths().is_prefix_of(final(self).paths())
                && node < final(self).paths().len()
                && final(self).paths()[node as int] == full_name_bytes(key),
    {
        let ghost initial = self.paths();
        let prefix = if let Some(parent) = key.parent {
            let parent_node = self.extend_bytes(0, parent.as_bytes())?;
            let separator = [b':', b':'];
            let node = self.extend_bytes(parent_node, separator.as_slice())?;
            assert(separator@ =~= seq![b':', b':']);
            node
        } else {
            0
        };
        proof { reveal(PathIndex::valid); }
        assert(initial.is_prefix_of(self.paths()));
        let node = self.extend_bytes(prefix, key.name.as_bytes())?;
        assert(self.paths()[node as int] =~= full_name_bytes(key));
        Some(node)
    }

    pub(super) fn namespace(&mut self, bytes: &[u8]) -> (nodes: Option<Vec<usize>>)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            nodes matches Some(nodes) ==> {
                &&& old(self).paths().is_prefix_of(final(self).paths())
                &&& forall|i: int| 0 <= i < nodes@.len() ==> #[trigger] nodes@[i] < final(self).paths().len()
                &&& forall|end: int| #[trigger] component_ends_at(bytes@, end) ==>
                    exists|i: int| 0 <= i < nodes@.len()
                        && final(self).paths()[(#[trigger] nodes@[i]) as int] == bytes@.take(end)
            },
    {
        let ghost initial = self.paths();
        let mut nodes: Vec<usize> = Vec::new();
        let mut node = 0;
        let mut at = 0;
        assert(bytes@.take(0) =~= Seq::<u8>::empty());
        while at < bytes.len()
            invariant
                self.valid(),
                initial.is_prefix_of(self.paths()),
                node < self.paths().len(),
                at <= bytes@.len(),
                self.paths()[node as int] == bytes@.take(at as int),
                forall|i: int| 0 <= i < nodes@.len() ==> #[trigger] nodes@[i] < self.paths().len(),
                forall|end: int| end <= at && #[trigger] component_ends_at(bytes@, end) ==>
                    exists|i: int| 0 <= i < nodes@.len()
                        && self.paths()[(#[trigger] nodes@[i]) as int] == bytes@.take(end),
            decreases bytes@.len() - at,
        {
            let ghost previous_paths = self.paths();
            let ghost previous_nodes = nodes@;
            node = self.extend(node, bytes[at])?;
            assert(bytes@.take(at as int).push(bytes@[at as int]) =~= bytes@.take(at + 1));
            at += 1;
            if at == bytes.len() || (bytes.len() - at >= 2 && bytes[at] == b':' && bytes[at + 1] == b':') {
                assert(component_ends_at(bytes@, at as int));
                nodes.push(node);
            } else {
                assert(!component_ends_at(bytes@, at as int));
            }
            assert forall|end: int| end <= at && #[trigger] component_ends_at(bytes@, end) implies
                exists|i: int| 0 <= i < nodes@.len()
                    && self.paths()[(#[trigger] nodes@[i]) as int] == bytes@.take(end) by {
                if end == at {
                    assert(nodes@[nodes@.len() - 1] == node);
                } else {
                    let i = choose|i: int| 0 <= i < previous_nodes.len()
                        && previous_paths[(#[trigger] previous_nodes[i]) as int] == bytes@.take(end);
                    assert(nodes@[i] == previous_nodes[i]);
                    assert(self.paths()[nodes@[i] as int] == previous_paths[previous_nodes[i] as int]);
                }
            };
        }
        Some(nodes)
    }
}

} // verus!
