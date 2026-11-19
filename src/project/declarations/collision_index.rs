//! 宣言と名前空間の索引から、出現順で最初の衝突候補を探す。

use super::path_index::PathIndex;
use super::{Occurrence, key_of};
#[cfg(verus_only)]
use super::{before, conflicts, form_key};
#[cfg(verus_only)]
use crate::project::name_keys::{
    NameKey, full_name_bytes, key_views_agree, namespace_component, namespace_component_prefix,
};
use crate::syntax::circuit::Head;
#[cfg(verus_only)]
use crate::syntax::circuit::NamedForm;
use alloc::collections::BTreeMap;
use core::cmp::min;
use vstd::prelude::*;

verus! {

spec fn indexed_path(paths: Seq<Seq<u8>>, ids: Set<usize>, path: Seq<u8>) -> bool {
    exists|id: usize| #[trigger] ids.contains(id) && id < paths.len() && paths[id as int] == path
}

proof fn record_indexed_path(paths: Seq<Seq<u8>>, ids: Set<usize>, id: usize, path: Seq<u8>)
    requires ids.contains(id), id < paths.len(), paths[id as int] == path,
    ensures indexed_path(paths, ids, path),
{
}

spec fn binding_indexed(
    form: NamedForm, paths: Seq<Seq<u8>>, declarations: Set<usize>, namespaces: Set<usize>,
) -> bool {
    if form.head is Namespace {
        forall|key: NameKey, lo: int, hi: int|
            #[trigger] namespace_component(form.name.word, key, lo, hi) ==>
                indexed_path(paths, namespaces, full_name_bytes(key))
    } else {
        indexed_path(paths, declarations, full_name_bytes(form_key(form)))
    }
}

proof fn keep_indexed(
    form: NamedForm, old_paths: Seq<Seq<u8>>, paths: Seq<Seq<u8>>,
    old_decls: Set<usize>, decls: Set<usize>, old_ns: Set<usize>, ns: Set<usize>,
)
    requires
        old_paths.is_prefix_of(paths), old_decls.subset_of(decls), old_ns.subset_of(ns),
        binding_indexed(form, old_paths, old_decls, old_ns),
    ensures binding_indexed(form, paths, decls, ns),
{
    if form.head is Namespace {
        assert forall|key: NameKey, lo: int, hi: int|
            #[trigger] namespace_component(form.name.word, key, lo, hi) implies
                indexed_path(paths, ns, full_name_bytes(key)) by {
            let name = full_name_bytes(key);
            let id = choose|id: usize| #[trigger] old_ns.contains(id) && id < old_paths.len()
                && old_paths[id as int] == name;
            assert(ns.contains(id) && paths[id as int] == name);
        };
    } else {
        let name = full_name_bytes(form_key(form));
        let id = choose|id: usize| #[trigger] old_decls.contains(id) && id < old_paths.len()
            && old_paths[id as int] == name;
        assert(decls.contains(id) && paths[id as int] == name);
    }
}

proof fn indexed_paths_conflict(
    index: &PathIndex, left: NamedForm, right: NamedForm, decls: Set<usize>, ns: Set<usize>,
    new_decls: Set<usize>, new_ns: Set<usize>,
)
    requires
        index.valid(),
        binding_indexed(left, index.paths(), decls, ns),
        binding_indexed(right, index.paths(), new_decls, new_ns),
        decls.disjoint(new_decls), ns.disjoint(new_decls), decls.disjoint(new_ns),
    ensures !conflicts(left, right),
{
    let paths = index.paths();
    if conflicts(left, right) {
        let (first_keys, second_keys, path) = if left.head is Namespace {
            let key = form_key(right);
            let (_lo, _hi) = choose|lo: int, hi: int|
                #[trigger] namespace_component(left.name.word, key, lo, hi);
            assert(indexed_path(paths, ns, full_name_bytes(key)));
            (ns, new_decls, full_name_bytes(key))
        } else if right.head is Namespace {
            let key = form_key(left);
            let (_lo, _hi) = choose|lo: int, hi: int|
                #[trigger] namespace_component(right.name.word, key, lo, hi);
            assert(indexed_path(paths, new_ns, full_name_bytes(key)));
            (decls, new_ns, full_name_bytes(key))
        } else {
            key_views_agree(form_key(left), form_key(right));
            (decls, new_decls, full_name_bytes(form_key(left)))
        };
        let first = choose|id: usize| #[trigger] first_keys.contains(id) && id < paths.len() && paths[id as int] == path;
        let second = choose|id: usize| #[trigger] second_keys.contains(id) && id < paths.len() && paths[id as int] == path;
        index.same_path(first as int, second as int);
        assert(first != second);
    }
}

spec fn before_rank(map: Map<usize, usize>, stop: int) -> Set<usize> {
    map.dom().filter(|id: usize| map[id] < stop)
}

spec fn keeps_earliest(old: Map<usize, usize>, new: Map<usize, usize>) -> bool {
    forall|id: usize| #[trigger] old.contains_key(id) ==> new.contains_key(id) && new[id] <= old[id]
}

proof fn earlier_entries_remain(old: Map<usize, usize>, new: Map<usize, usize>, stop: int)
    requires keeps_earliest(old, new),
    ensures before_rank(old, stop).subset_of(before_rank(new, stop)),
{
    assert forall|id: usize| #[trigger] before_rank(old, stop).contains(id)
        implies before_rank(new, stop).contains(id) by {
        assert(old.contains_key(id) && old[id] < stop);
    };
}

// 固定版 vstd の BTreeMap の検索契約に従い、未登録の名前には末尾の添字を使う。
fn earliest(map: &BTreeMap<usize, usize>, id: usize, end: usize) -> (rank: usize)
    ensures rank == if map@.contains_key(id) { map@[id] } else { end },
{
    match map.get(&id) {
        Some(rank) => *rank,
        None => end,
    }
}

fn record_earliest(map: &mut BTreeMap<usize, usize>, id: usize, rank: usize)
    ensures final(map)@ == old(map)@.insert(id, rank),
{
    assert(vstd::laws_cmp::obeys_cmp::<usize>());
    map.insert(id, rank);
}

pub(super) open spec fn no_pair_before(items: Seq<Occurrence>, start: int, stop_left: int, stop_right: int) -> bool {
    forall|i: int, j: int| start <= i < j < items.len() && before(i, j, stop_left, stop_right)
        ==> !conflicts(*(#[trigger] items[i]).form, *(#[trigger] items[j]).form)
}

// 後ろから走査し、各キーについて処理済みの範囲で最初の添字を保持する。
// 索引は候補を絞り、呼び出し側は既存の判定でその候補の種類と範囲を確定する。
pub(super) fn first_candidate(items: &[Occurrence]) -> (result: Result<Option<(usize, usize)>, ()>)
    ensures
        match result {
            Ok(Some((left, right))) => left < right < items@.len()
                && no_pair_before(items@, 0, left as int, right as int),
            Ok(None) => no_pair_before(items@, 0, items@.len() as int, items@.len() as int),
            Err(()) => true,
        },
{
    let mut index = PathIndex::new();
    let mut declarations: BTreeMap<usize, usize> = BTreeMap::new();
    let mut namespaces: BTreeMap<usize, usize> = BTreeMap::new();
    let count = items.len();
    let mut at = count;
    let mut best_left = count;
    let mut best_right = count;
    while at > 0
        invariant
            index.valid(),
            at <= count == items@.len(),
            at <= best_left <= count,
            if best_left == count { best_right == count } else { best_left < best_right < count },
            no_pair_before(items@, at as int, best_left as int, best_right as int),
            forall|id: usize| #[trigger] declarations@.contains_key(id) ==> at <= declarations@[id] < count,
            forall|id: usize| #[trigger] namespaces@.contains_key(id) ==> at <= namespaces@[id] < count,
            forall|i: int| at <= i < count
                ==> binding_indexed(*(#[trigger] items@[i]).form, index.paths(),
                    before_rank(declarations@, i + 1), before_rank(namespaces@, i + 1)),
        decreases at,
    {
        let left = at - 1;
        let item = items[left];
        let ghost previous_paths = index.paths();
        let ghost before_decls = declarations@;
        let ghost before_ns = namespaces@;
        let (right, Ghost(added_decls), Ghost(added_ns)) = if matches!(item.form.head, Head::Namespace) {
            let bytes = item.form.name.word.as_bytes();
            let nodes = index.namespace(bytes).ok_or(())?;
            let mut right = count;
            let mut pos = 0;
            let ghost all = nodes@.to_set();
            while pos < nodes.len()
                invariant
                    pos <= nodes@.len(),
                    left + 1 == at <= count,
                    at <= right <= count,
                    forall|p: int| 0 <= p < pos ==> namespaces@.contains_key(#[trigger] nodes@[p])
                        && namespaces@[nodes@[p]] == left,
                    forall|p: int| 0 <= p < pos && declarations@.contains_key(#[trigger] nodes@[p])
                        ==> right <= declarations@[nodes@[p]],
                    forall|id: usize| #[trigger] namespaces@.contains_key(id) ==> left <= namespaces@[id] < count,
                    forall|id: usize| #[trigger] declarations@.contains_key(id) ==> at <= declarations@[id] < count,
                    keeps_earliest(before_ns, namespaces@),
                decreases nodes@.len() - pos,
            {
                let node = nodes[pos];
                right = min(right, earliest(&declarations, node, count));
                let ghost previous = namespaces@;
                record_earliest(&mut namespaces, node, left);
                assert forall|id: usize| #[trigger] namespaces@.contains_key(id)
                    implies left <= namespaces@[id] < count by {
                    if id == node {
                        assert(namespaces@[id] == left);
                    } else {
                        assert(previous.contains_key(id) && namespaces@[id] == previous[id]);
                        assert(left <= previous[id] < count);
                    }
                };
                pos += 1;
            }
            proof {
                nodes@.to_set_ensures();
                assert forall|key: NameKey, lo: int, hi: int|
                    #[trigger] namespace_component(item.form.name.word, key, lo, hi) implies
                        indexed_path(index.paths(), all, full_name_bytes(key)) by {
                    namespace_component_prefix(item.form.name.word, key, lo, hi);
                    let p = choose|p: int| 0 <= p < nodes@.len() && index.paths()[(#[trigger] nodes@[p]) as int] == bytes@.take(hi);
                    record_indexed_path(index.paths(), all, nodes@[p], full_name_bytes(key));
                };
                assert forall|id: usize| #[trigger] all.contains(id) implies
                    before_rank(namespaces@, at as int).contains(id)
                        && !before_rank(before_decls, right as int).contains(id) by {
                    let p = choose|p: int| 0 <= p < nodes@.len() && #[trigger] nodes@[p] == id;
                };
            }
            (right, Ghost(Set::<usize>::empty()), Ghost(all))
        } else {
            let node = index.declaration(key_of(item.form)).ok_or(())?;
            let right = min(earliest(&declarations, node, count), earliest(&namespaces, node, count));
            record_earliest(&mut declarations, node, left);
            let ghost only = set![node];
            proof {
                record_indexed_path(index.paths(), only, node, full_name_bytes(form_key(*item.form)));
            }
            (right, Ghost(only), Ghost(Set::<usize>::empty()))
        };
        proof {
            assert(binding_indexed(*item.form, index.paths(), added_decls, added_ns));
            assert(before_rank(before_decls, right as int).disjoint(added_decls));
            assert(before_rank(before_ns, right as int).disjoint(added_decls));
            assert(before_rank(before_decls, right as int).disjoint(added_ns));
            assert forall|j: int| at <= j < right implies
                !conflicts(*item.form, *(#[trigger] items@[j]).form) by {
                keep_indexed(*items@[j].form, previous_paths, index.paths(),
                    before_rank(before_decls, j + 1), before_rank(before_decls, right as int),
                    before_rank(before_ns, j + 1), before_rank(before_ns, right as int));
                indexed_paths_conflict(&index, *item.form, *items@[j].form, added_decls, added_ns,
                    before_rank(before_decls, right as int), before_rank(before_ns, right as int));
            };
            assert forall|i: int| left <= i < count implies
                binding_indexed(*(#[trigger] items@[i]).form, index.paths(),
                    before_rank(declarations@, i + 1), before_rank(namespaces@, i + 1)) by {
                if i == left {
                    keep_indexed(*item.form, index.paths(), index.paths(), added_decls,
                        before_rank(declarations@, i + 1), added_ns, before_rank(namespaces@, i + 1));
                } else {
                    earlier_entries_remain(before_decls, declarations@, i + 1);
                    earlier_entries_remain(before_ns, namespaces@, i + 1);
                    keep_indexed(*items@[i].form, previous_paths, index.paths(),
                        before_rank(before_decls, i + 1), before_rank(declarations@, i + 1),
                        before_rank(before_ns, i + 1), before_rank(namespaces@, i + 1));
                }
            };
        }
        if right < count {
            best_left = left;
            best_right = right;
        }
        at = left;
    }
    if best_left == count { Ok(None) } else { Ok(Some((best_left, best_right))) }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::first_candidate;
    use crate::project::declarations::read_occurrences;
    use crate::project::{SourceSnapshot, parse_circuit_project};

    #[test]
    fn finds_the_first_candidate_without_the_reference_scan() {
        for (text, expected) in [
            ("(namespace a::b) (namespace a::b) (namespace a::c)", None),
            (
                "(namespace a::b) (namespace a (struct b (width 1))) (struct a (width 1))",
                Some((0, 2)),
            ),
            (
                "(struct a (width 1)) (struct b (width 1)) (struct b (width 1)) (struct a (width 1))",
                Some((0, 3)),
            ),
        ] {
            let project = parse_circuit_project(&[SourceSnapshot {
                path: "main.ncg2",
                revision: 1,
                text,
            }])
            .unwrap();
            let items = read_occurrences(&project);
            assert_eq!(first_candidate(&items), Ok(expected), "{text}");
        }
    }
}
