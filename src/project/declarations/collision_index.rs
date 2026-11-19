//! 宣言と名前空間の索引から、全組比較が不要なソース集合を判定する。

use super::path_index::PathIndex;
use super::{Occurrence, key_of};
#[cfg(verus_only)]
use super::{conflicts, form_key};
#[cfg(verus_only)]
use crate::project::name_keys::{
    NameKey, full_name_bytes, key_views_agree, namespace_component, namespace_component_prefix,
};
use crate::syntax::circuit::Head;
#[cfg(verus_only)]
use crate::syntax::circuit::NamedForm;
use alloc::collections::BTreeSet;
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

// 索引を使って衝突のないことを示す。候補が見つかれば、呼び出し側が出現順の診断を確定する。
// 出現した添字の有無は、固定版 vstd の BTreeSet の検索・挿入の契約で示す。
pub(super) fn no_indexed_conflicts(items: &[Occurrence]) -> (clear: bool)
    ensures clear ==> forall|i: int, j: int| 0 <= i < j < items@.len()
        ==> !conflicts(*(#[trigger] items@[i]).form, *(#[trigger] items@[j]).form),
{
    let mut index = PathIndex::new();
    let mut declarations: BTreeSet<usize> = BTreeSet::new();
    let mut namespaces: BTreeSet<usize> = BTreeSet::new();
    let mut at = 0;
    while at < items.len()
        invariant
            index.valid(),
            at <= items@.len(),
            forall|i: int| 0 <= i < at
                ==> binding_indexed(*(#[trigger] items@[i]).form, index.paths(), declarations@, namespaces@),
            forall|i: int, j: int| 0 <= i < j < at ==> !conflicts(*(#[trigger] items@[i]).form, *(#[trigger] items@[j]).form),
        decreases items@.len() - at,
    {
        let item = items[at];
        let ghost previous_paths = index.paths();
        let ghost before_decls = declarations@;
        let ghost before_ns = namespaces@;
        let (Ghost(added_decls), Ghost(added_ns)) = if matches!(item.form.head, Head::Namespace) {
            let bytes = item.form.name.word.as_bytes();
            let Some(nodes) = index.namespace(bytes) else { return false; };
            let mut pos = 0;
            let ghost all = nodes@.to_set();
            while pos < nodes.len()
                invariant
                    pos <= nodes@.len(),
                    forall|p: int| 0 <= p < pos ==> namespaces@.contains(#[trigger] nodes@[p])
                        && !declarations@.contains(nodes@[p]),
                    before_ns.subset_of(namespaces@),
                decreases nodes@.len() - pos,
            {
                let node = nodes[pos];
                if declarations.contains(&node) {
                    return false;
                }
                namespaces.insert(node);
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
                assert forall|id: usize| #[trigger] all.contains(id) implies namespaces@.contains(id) && !declarations@.contains(id) by {
                    let p = choose|p: int| 0 <= p < nodes@.len() && #[trigger] nodes@[p] == id;
                };
            }
            (Ghost(Set::<usize>::empty()), Ghost(all))
        } else {
            let Some(node) = index.declaration(key_of(item.form)) else { return false; };
            if declarations.contains(&node) || namespaces.contains(&node) {
                return false;
            }
            declarations.insert(node);
            let ghost only = set![node];
            proof {
                record_indexed_path(index.paths(), only, node, full_name_bytes(form_key(*item.form)));
            }
            (Ghost(only), Ghost(Set::<usize>::empty()))
        };
        proof {
            assert(binding_indexed(*item.form, index.paths(), added_decls, added_ns));
            assert(before_decls.disjoint(added_decls) && before_ns.disjoint(added_decls) && before_decls.disjoint(added_ns));
            assert forall|i: int| 0 <= i <= at implies
                binding_indexed(*(#[trigger] items@[i]).form, index.paths(), declarations@, namespaces@) by {
                if i == at {
                    keep_indexed(*item.form, index.paths(), index.paths(), added_decls, declarations@, added_ns, namespaces@);
                } else {
                    keep_indexed(*items@[i].form, previous_paths, index.paths(), before_decls, declarations@, before_ns, namespaces@);
                }
            };
            assert forall|i: int| 0 <= i < at implies !conflicts(*(#[trigger] items@[i]).form, *item.form) by {
                keep_indexed(*items@[i].form, previous_paths, index.paths(), before_decls, before_decls, before_ns, before_ns);
                indexed_paths_conflict(&index, *items@[i].form, *item.form, before_decls, before_ns, added_decls, added_ns);
            };
        }
        at += 1;
    }
    true
}

} // verus!
