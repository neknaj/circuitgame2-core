//! 回路と NCG2M の宣言を同じ完全修飾名で照合する。

use alloc::vec::Vec;
use core::ops::Range;
use crate::ncg2m::file::{MetaItem, MetaItemKind};
#[cfg(verus_only)]
use crate::ncg2m::file::{meta_binding_span_evidence, meta_binding_spans_valid};
use crate::project::{NameKey, ParsedProjectSources, ProjectSource, ProjectSourceIndex, read_source_span};
#[cfg(verus_only)]
use crate::project::{
    circuits::{name_in_source, parsed_name_span},
    name_keys::{key_bytes, key_view, key_views_agree, namespace_component, namespace_component_agrees_on_bytes},
    source_indexes::project_source_index_evidence,
};
use crate::syntax::circuit::{Head, NameSite, NamedBuildCircuit};
#[cfg(verus_only)]
use crate::syntax::circuit::NamedForm;
use super::{LocatedName, NameConflict, NameConflictKind, defines_binding, key_of, namespace_key_location};
#[cfg(verus_only)]
use super::{before, form_key, location_in_source, named_binding};
use super::collision_index::{BindingKey, CollisionItem, LookupIndex, find_binding, search_conflicts};
#[cfg(verus_only)]
use super::collision_index::{binding_keys_conflict, binding_lookup_matches, namespace_binding_matches, no_pair_before};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 言語をまたいで照合する独立宣言の種類。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProjectDeclarationKind {
    /// 回路の関数、モジュール、構造体、ラッチ、メモリの独立宣言。
    Circuit(Head),
    /// NCG2M の補助関数宣言。
    Defn,
    /// NCG2M のマクロ定義。
    Defmacro,
}

/// 完全修飾名で特定した宣言。
#[derive(Debug)]
pub struct ProjectDeclaration<'p, 'a> {
    /// 宣言の元ファイルと名前の範囲。
    pub name: LocatedName<'p, 'a>,
    /// 宣言の種類。
    pub kind: ProjectDeclarationKind,
    /// 解析済みソース列で対象ファイルを指す添字。
    pub file: usize,
    /// 回路の名前列または NCG2M のフォーム列で元の項目を指す添字。
    pub item: usize,
}

/// 両言語の独立宣言と名前空間を収めた索引。
pub struct MixedDeclarationTable<'p, 'a> {
    sites: Vec<Site<'p, 'a>>,
    lookup: Option<LookupIndex>,
}

#[derive(Clone, Copy, Debug)]
struct Site<'p, 'a> {
    file: usize,
    item: usize,
    source: &'p ProjectSource<'a>,
    binding: BindingKey<'a>,
    kind: Option<ProjectDeclarationKind>,
    start: usize,
    end: usize,
}

impl<'a> CollisionItem<'a> for Site<'_, 'a> {
    closed spec fn binding_model(&self) -> BindingKey<'a> { self.binding }

    fn binding_key(&self) -> (key: BindingKey<'a>) { self.binding }
}

spec fn kind_tag(head: Head) -> Option<ProjectDeclarationKind> {
    if head is Namespace { None } else { Some(ProjectDeclarationKind::Circuit(head)) }
}

spec fn span_bytes(text: &str, span: Range<usize>) -> Seq<u8> {
    text.spec_bytes()[span.start as int..span.end as int]
}

spec fn meta_site_kind(item: MetaItemKind) -> Option<(Option<ProjectDeclarationKind>, Range<usize>)> {
    match item {
        MetaItemKind::Namespace { path } => Some((None, path)),
        MetaItemKind::Defn(header) => Some((Some(ProjectDeclarationKind::Defn), header.name_span)),
        MetaItemKind::Defmacro { name, .. } => Some((Some(ProjectDeclarationKind::Defmacro), name)),
        _ => None,
    }
}

fn meta_site_span(item: &MetaItemKind) -> (site: Option<(Option<ProjectDeclarationKind>, Range<usize>)>)
    ensures site == meta_site_kind(*item),
{
    match item {
        MetaItemKind::Namespace { path } => Some((None, path.start..path.end)),
        MetaItemKind::Defn(header) => Some((Some(ProjectDeclarationKind::Defn), header.name_span.start..header.name_span.end)),
        MetaItemKind::Defmacro { name, .. } => Some((Some(ProjectDeclarationKind::Defmacro), name.start..name.end)),
        _ => None,
    }
}

#[cfg(verus_only)]
type SiteModel = (Option<ProjectDeclarationKind>, Range<usize>, (Option<Seq<u8>>, Seq<u8>));

spec fn circuit_site_model(form: NamedForm) -> Option<SiteModel> {
    if named_binding(form.head) {
        Some((kind_tag(form.head), form.name.span, key_bytes(form_key(form))))
    } else {
        None
    }
}

spec fn meta_site_model(text: &str, item: MetaItem) -> Option<SiteModel> {
    match meta_site_kind(item.kind) {
        Some((kind, span)) => {
            let parent = match item.namespace {
                Some(path) => Some(span_bytes(text, path)),
                None => None,
            };
            Some((kind, span, (parent, span_bytes(text, span))))
        }
        None => None,
    }
}

spec fn index_count(index: ProjectSourceIndex) -> nat {
    match index {
        ProjectSourceIndex::Circuit(circuit) => circuit.names@.len(),
        ProjectSourceIndex::Functional(items) => items@.len(),
    }
}

fn index_len(index: &ProjectSourceIndex) -> (len: usize)
    ensures len == index_count(*index),
{
    match index {
        ProjectSourceIndex::Circuit(circuit) => circuit.names.len(),
        ProjectSourceIndex::Functional(items) => items.len(),
    }
}

spec fn expected_site(project: &ParsedProjectSources, file: int, item: int) -> Option<SiteModel> {
    let indexes = project.indexes_model();
    if 0 <= file < indexes.len() && 0 <= item < index_count(indexes[file]) {
        match indexes[file] {
            ProjectSourceIndex::Circuit(circuit) => circuit_site_model(circuit.names@[item]),
            ProjectSourceIndex::Functional(items) => meta_site_model(project.sources_model()[file].text, items@[item]),
        }
    } else {
        None
    }
}

spec fn site_matches(site: Site, model: SiteModel) -> bool {
    &&& site.kind == model.0
    &&& site.start == model.1.start && site.end == model.1.end
    &&& key_bytes(site.binding.key) == model.2
    &&& site.binding.namespace == site.kind.is_none()
    &&& name_in_source(site.source.text, NameSite { word: site.binding.key.name, span: site.start..site.end })
}

spec fn source_site(project: &ParsedProjectSources, site: Site) -> bool {
    &&& site.file < project.sources_model().len()
    &&& *site.source == project.sources_model()[site.file as int]
    &&& expected_site(project, site.file as int, site.item as int) matches Some(model) && site_matches(site, model)
}

fn circuit_site<'p, 'a>(
    source: &'p ProjectSource<'a>, circuit: &NamedBuildCircuit<'a>, file: usize, item: usize,
) -> (site: Option<Site<'p, 'a>>)
    requires crate::project::parsed_circuit_matches(*source, *circuit), item < circuit.names@.len(),
    ensures site.is_some() == circuit_site_model(circuit.names@[item as int]).is_some(),
        site matches Some(site) ==> site.file == file && site.item == item && *site.source == *source
            && site_matches(site, circuit_site_model(circuit.names@[item as int])->Some_0),
{
    let form = &circuit.names[item];
    if !defines_binding(form.head) {
        return None;
    }
    proof { parsed_name_span(*source, *circuit, item as int); }
    let namespace = matches!(form.head, Head::Namespace);
    Some(Site {
        source, file, item, binding: BindingKey { key: key_of(form), namespace },
        kind: if namespace { None } else { Some(ProjectDeclarationKind::Circuit(form.head)) },
        start: form.name.span.start, end: form.name.span.end,
    })
}

fn meta_site<'p, 'a>(
    source: &'p ProjectSource<'a>, entries: &[MetaItem], file: usize, item: usize,
) -> (site: Option<Site<'p, 'a>>)
    requires item < entries@.len(), meta_binding_spans_valid(source.text, entries@),
    ensures site.is_some() == meta_site_model(source.text, entries@[item as int]).is_some(),
        site matches Some(site) ==> site.file == file && site.item == item && *site.source == *source
            && site_matches(site, meta_site_model(source.text, entries@[item as int])->Some_0),
{
    let entry = &entries[item];
    let (kind, span) = meta_site_span(&entry.kind)?;
    proof { meta_binding_span_evidence(source.text, entries@, item as int); }
    let name = read_source_span(source.text, span.start, span.end);
    let parent = match &entry.namespace {
        Some(path) => Some(read_source_span(source.text, path.start, path.end)),
        None => None,
    };
    Some(Site {
        source, file, item, binding: BindingKey { key: NameKey { parent, name }, namespace: kind.is_none() },
        kind, start: span.start, end: span.end,
    })
}

fn read_site<'p, 'a>(
    project: &'p ParsedProjectSources<'a>, file: usize, item: usize,
) -> (site: Option<Site<'p, 'a>>)
    requires
        project.has_source_indexes(),
        file < project.indexes_model().len(),
        item < index_count(project.indexes_model()[file as int]),
    ensures site.is_some() == expected_site(project, file as int, item as int).is_some(),
        site matches Some(site) ==> source_site(project, site) && site.file == file && site.item == item,
{
    let source = &project.sources()[file];
    let index = &project.indexes()[file];
    proof { project_source_index_evidence(*source, *index); }
    match index {
        ProjectSourceIndex::Circuit(circuit) => circuit_site(source, circuit, file, item),
        ProjectSourceIndex::Functional(entries) => meta_site(source, entries, file, item),
    }
}


spec fn selected_site(project: &ParsedProjectSources, file: int, item: int) -> bool {
    expected_site(project, file, item).is_some()
}

#[verifier::opaque]
spec fn sites_before(project: &ParsedProjectSources, sites: Seq<Site>, file: int, item: int) -> bool {
    &&& forall|at: int| 0 <= at < sites.len() ==> {
        let site = #[trigger] sites[at];
        source_site(project, site) && before(site.file as int, site.item as int, file, item)
    }
    &&& forall|f: int, n: int| #[trigger] selected_site(project, f, n) && before(f, n, file, item)
        ==> exists|at: int| 0 <= at < sites.len() && (#[trigger] sites[at]).file == f && sites[at].item == n
    &&& forall|i: int, j: int| 0 <= i < j < sites.len() ==> {
        let a = #[trigger] sites[i];
        let b = #[trigger] sites[j];
        before(a.file as int, a.item as int, b.file as int, b.item as int)
    }
}

proof fn append_site(
    project: &ParsedProjectSources, sites: Seq<Site>, file: int, item: int, picked: Option<Site>,
)
    requires sites_before(project, sites, file, item),
        match picked {
            Some(site) => source_site(project, site) && site.file == file && site.item == item,
            None => !selected_site(project, file, item),
        },
    ensures sites_before(project, if let Some(site) = picked { sites.push(site) } else { sites }, file, item + 1),
{
    reveal(sites_before);
    let next = if let Some(site) = picked { sites.push(site) } else { sites };
    assert forall|f: int, n: int| #[trigger] selected_site(project, f, n) && before(f, n, file, item + 1)
        implies exists|at: int| 0 <= at < next.len() && (#[trigger] next[at]).file == f && next[at].item == n by {
        if before(f, n, file, item) {
            let at = choose|at: int| 0 <= at < sites.len() && (#[trigger] sites[at]).file == f && sites[at].item == n;
            assert(next[at] == sites[at]);
        } else {
            assert(f == file && n == item);
            assert(picked is Some);
            assert(next[sites.len() as int] == picked->Some_0);
        }
    };
}

proof fn advance_site_file(project: &ParsedProjectSources, sites: Seq<Site>, file: int, count: int)
    requires
        0 <= file < project.indexes_model().len(),
        count == index_count(project.indexes_model()[file]),
        sites_before(project, sites, file, count),
    ensures sites_before(project, sites, file + 1, 0),
{
    reveal(sites_before);
    assert forall|f: int, n: int| #[trigger] selected_site(project, f, n) && before(f, n, file + 1, 0)
        implies before(f, n, file, count) by {};
}

spec fn remaining_sites(project: &ParsedProjectSources, file: int, item: int) -> int {
    let indexes = project.indexes_model();
    if 0 <= file < indexes.len() { index_count(indexes[file]) - item } else { 0 }
}

fn read_sites<'p, 'a>(project: &'p ParsedProjectSources<'a>) -> (sites: Vec<Site<'p, 'a>>)
    ensures sites_before(project, sites@, project.indexes_model().len() as int, 0),
{
    let indexes = project.indexes();
    let mut sites = Vec::new();
    let mut file = 0;
    let mut item = 0;
    assert(sites_before(project, sites@, 0, 0)) by { reveal(sites_before); }
    while file < indexes.len()
        invariant
            project.has_source_indexes(), indexes@ == project.indexes_model(),
            file <= indexes@.len(),
            file < indexes@.len() ==> item <= index_count(indexes@[file as int]),
            file == indexes@.len() ==> item == 0,
            sites_before(project, sites@, file as int, item as int),
        decreases indexes@.len() - file, remaining_sites(project, file as int, item as int),
    {
        if item == index_len(&indexes[file]) {
            proof { advance_site_file(project, sites@, file as int, item as int); }
            file += 1;
            item = 0;
            continue;
        }
        let selected = read_site(project, file, item);
        proof { append_site(project, sites@, file as int, item as int, selected); }
        if let Some(site) = selected {
            sites.push(site);
        }
        item += 1;
    }
    sites
}

spec fn full_sites(project: &ParsedProjectSources, sites: Seq<Site>) -> bool {
    sites_before(project, sites, project.indexes_model().len() as int, 0)
}

spec fn position_of(site: Site, location: LocatedName) -> bool {
    *site.source == *location.source && location.span == (site.start..site.end) && location_in_source(location)
}

spec fn namespace_position(site: Site, key: NameKey, location: LocatedName) -> bool {
    *site.source == *location.source && location_in_source(location)
        && (exists|lo: int, hi: int| #[trigger] namespace_component(site.binding.key.name, key, lo, hi)
            && location.span.start == site.start + lo && location.span.end == site.start + hi)
}

spec fn site_is_readable(site: Site) -> bool {
    site.binding.namespace == site.kind.is_none()
        && name_in_source(site.source.text, NameSite { word: site.binding.key.name, span: site.start..site.end })
}

fn site_location<'p, 'a>(site: Site<'p, 'a>) -> (location: LocatedName<'p, 'a>)
    requires site_is_readable(site),
    ensures position_of(site, location),
{
    LocatedName { source: site.source, span: site.start..site.end }
}

fn site_namespace<'p, 'a>(site: Site<'p, 'a>, key: NameKey) -> (location: Option<LocatedName<'p, 'a>>)
    requires site_is_readable(site),
    ensures
        location.is_some() == (exists|lo: int, hi: int| #[trigger] namespace_component(site.binding.key.name, key, lo, hi)),
        location matches Some(value) ==> namespace_position(site, key, value),
{
    let name = NameSite { word: site.binding.key.name, span: site.start..site.end };
    namespace_key_location(site.source, &name, key)
}

spec fn site_conflict(left: Site, right: Site, error: NameConflict) -> bool {
    if left.binding.namespace {
        !right.binding.namespace && error.kind is DeclarationAndNamespace
            && namespace_position(left, right.binding.key, error.first) && position_of(right, error.second)
    } else if right.binding.namespace {
        error.kind is DeclarationAndNamespace
            && position_of(left, error.first) && namespace_position(right, left.binding.key, error.second)
    } else {
        error.kind is DuplicateDeclaration && key_view(left.binding.key) == key_view(right.binding.key)
            && position_of(left, error.first) && position_of(right, error.second)
    }
}

fn make_conflict<'p, 'a>(left: Site<'p, 'a>, right: Site<'p, 'a>) -> (error: NameConflict<'p, 'a>)
    requires site_is_readable(left), site_is_readable(right), binding_keys_conflict(left.binding, right.binding),
    ensures site_conflict(left, right, error),
{
    if left.binding.namespace {
        let Some(first) = site_namespace(left, right.binding.key) else { unreachable!() };
        NameConflict {
            kind: NameConflictKind::DeclarationAndNamespace,
            first, second: site_location(right),
        }
    } else if right.binding.namespace {
        let Some(second) = site_namespace(right, left.binding.key) else { unreachable!() };
        NameConflict {
            kind: NameConflictKind::DeclarationAndNamespace,
            first: site_location(left), second,
        }
    } else {
        NameConflict {
            kind: NameConflictKind::DuplicateDeclaration,
            first: site_location(left), second: site_location(right),
        }
    }
}


spec fn site_before(left: Site, right: Site) -> bool {
    before(left.file as int, left.item as int, right.file as int, right.item as int)
}

spec fn pair_before(a: Site, b: Site, left: Site, right: Site) -> bool {
    site_before(a, left) || (a.file == left.file && a.item == left.item && site_before(b, right))
}

/// 完全修飾名で重複する独立宣言または、独立宣言と名前空間の組があることを表す。
pub closed spec fn mixed_project_names_conflict(project: &ParsedProjectSources) -> bool {
    exists|left: Site, right: Site| #[trigger] source_site(project, left)
        && #[trigger] source_site(project, right) && site_before(left, right)
        && binding_keys_conflict(left.binding, right.binding)
}

/// 元ソース順で最初の衝突と、その二つの出現箇所に診断が対応することを表す。
pub closed spec fn mixed_name_conflict_evidence(project: &ParsedProjectSources, error: NameConflict) -> bool {
    exists|left: Site, right: Site| #[trigger] source_site(project, left)
        && #[trigger] source_site(project, right) && site_before(left, right)
        && site_conflict(left, right, error)
        && (forall|a: Site, b: Site| #[trigger] source_site(project, a)
            && #[trigger] source_site(project, b) && site_before(a, b)
            && pair_before(a, b, left, right) ==> !binding_keys_conflict(a.binding, b.binding))
}

/// 索引が、両言語の宣言と名前空間を正規化済みソース順で保持することを表す。
pub closed spec fn mixed_declaration_table_matches(project: &ParsedProjectSources, table: MixedDeclarationTable) -> bool {
    full_sites(project, table.sites@)
}

proof fn find_site_rank(project: &ParsedProjectSources, sites: Seq<Site>, site: Site) -> (rank: int)
    requires full_sites(project, sites), source_site(project, site),
    ensures 0 <= rank < sites.len(), sites[rank].file == site.file, sites[rank].item == site.item,
        key_bytes(sites[rank].binding.key) == key_bytes(site.binding.key),
        sites[rank].binding.namespace == site.binding.namespace,
{
    reveal(sites_before);
    assert(selected_site(project, site.file as int, site.item as int));
    let rank = choose|at: int| 0 <= at < sites.len() && (#[trigger] sites[at]).file == site.file
        && sites[at].item == site.item;
    assert(source_site(project, sites[rank]));
    rank
}

proof fn namespace_path_keeps_key(
    path: &str, other: &str, key: NameKey, target: NameKey,
)
    requires path.spec_bytes() == other.spec_bytes(), key_bytes(key) == key_bytes(target),
    ensures namespace_binding_matches(path, key) == namespace_binding_matches(other, target),
{
    if exists|lo: int, hi: int| #[trigger] namespace_component(path, key, lo, hi) {
        let (lo, hi) = choose|lo: int, hi: int| #[trigger] namespace_component(path, key, lo, hi);
        namespace_component_agrees_on_bytes(path, other, key, target, lo, hi);
        assert(exists|lo: int, hi: int| #[trigger] namespace_component(other, target, lo, hi));
    }
    if exists|lo: int, hi: int| #[trigger] namespace_component(other, target, lo, hi) {
        let (lo, hi) = choose|lo: int, hi: int| #[trigger] namespace_component(other, target, lo, hi);
        namespace_component_agrees_on_bytes(path, other, key, target, lo, hi);
        assert(exists|lo: int, hi: int| #[trigger] namespace_component(path, key, lo, hi));
    }
}

proof fn collision_keeps_keys(left: BindingKey, right: BindingKey, a: BindingKey, b: BindingKey)
    requires key_bytes(left.key) == key_bytes(a.key), key_bytes(right.key) == key_bytes(b.key),
        left.namespace == a.namespace, right.namespace == b.namespace,
    ensures binding_keys_conflict(left, right) == binding_keys_conflict(a, b),
{
    if left.namespace && !right.namespace {
        namespace_path_keeps_key(left.key.name, a.key.name, right.key, b.key);
    } else if right.namespace && !left.namespace {
        namespace_path_keeps_key(right.key.name, b.key.name, left.key, a.key);
    } else {
        key_views_agree(left.key, a.key);
        key_views_agree(right.key, b.key);
    }
}

proof fn ordered_site_ranks(
    project: &ParsedProjectSources, sites: Seq<Site>, a: Site, b: Site,
) -> (ranks: (int, int))
    requires full_sites(project, sites), source_site(project, a), source_site(project, b), site_before(a, b),
    ensures
        0 <= ranks.0 < ranks.1 < sites.len(),
        sites[ranks.0].file == a.file && sites[ranks.0].item == a.item,
        sites[ranks.1].file == b.file && sites[ranks.1].item == b.item,
        binding_keys_conflict(sites[ranks.0].binding, sites[ranks.1].binding)
            == binding_keys_conflict(a.binding, b.binding),
{
    reveal(sites_before);
    let i = find_site_rank(project, sites, a);
    let j = find_site_rank(project, sites, b);
    if j < i { assert(site_before(sites[j], sites[i])); }
    collision_keeps_keys(sites[i].binding, sites[j].binding, a.binding, b.binding);
    (i, j)
}

proof fn no_source_conflict(project: &ParsedProjectSources, sites: Seq<Site>)
    requires full_sites(project, sites), no_pair_before(sites, 0, sites.len() as int, sites.len() as int),
    ensures !mixed_project_names_conflict(project),
{
    if mixed_project_names_conflict(project) {
        let (a, b) = choose|a: Site, b: Site| #[trigger] source_site(project, a)
            && #[trigger] source_site(project, b) && site_before(a, b)
            && binding_keys_conflict(a.binding, b.binding);
        let (i, j) = ordered_site_ranks(project, sites, a, b);
        assert(!binding_keys_conflict(sites[i].binding, sites[j].binding));
    }
}

proof fn first_source_conflict(project: &ParsedProjectSources, sites: Seq<Site>, i: int, j: int, error: NameConflict)
    requires full_sites(project, sites), 0 <= i < j < sites.len(), no_pair_before(sites, 0, i, j),
        site_conflict(sites[i], sites[j], error), binding_keys_conflict(sites[i].binding, sites[j].binding),
    ensures mixed_project_names_conflict(project), mixed_name_conflict_evidence(project, error),
{
    reveal(sites_before);
    let left = sites[i];
    let right = sites[j];
    assert(source_site(project, left) && source_site(project, right) && site_before(left, right));
    assert forall|a: Site, b: Site| #[trigger] source_site(project, a)
        && #[trigger] source_site(project, b) && site_before(a, b) && pair_before(a, b, left, right)
        implies !binding_keys_conflict(a.binding, b.binding) by {
        let (f, n) = ordered_site_ranks(project, sites, a, b);
        if f > i { assert(site_before(left, sites[f])); }
        if f == i && n > j { assert(site_before(right, sites[n])); }
        assert(before(f, n, i, j));
    };
}


proof fn choose_conflict_sites<'p, 'a>(project: &'p ParsedProjectSources<'a>, error: NameConflict<'p, 'a>)
    -> (pair: (Site<'p, 'a>, Site<'p, 'a>))
    requires mixed_name_conflict_evidence(project, error),
    ensures
        source_site(project, pair.0), source_site(project, pair.1),
        site_before(pair.0, pair.1), site_conflict(pair.0, pair.1, error),
        binding_keys_conflict(pair.0.binding, pair.1.binding),
        forall|a: Site, b: Site| #[trigger] source_site(project, a)
            && #[trigger] source_site(project, b) && site_before(a, b)
            && pair_before(a, b, pair.0, pair.1) ==> !binding_keys_conflict(a.binding, b.binding),
{
    let (left, right) = choose|left: Site, right: Site| #[trigger] source_site(project, left)
        && #[trigger] source_site(project, right) && site_before(left, right)
        && site_conflict(left, right, error)
        && (forall|a: Site, b: Site| #[trigger] source_site(project, a)
            && #[trigger] source_site(project, b) && site_before(a, b)
            && pair_before(a, b, left, right) ==> !binding_keys_conflict(a.binding, b.binding));
    if left.binding.namespace {
        let key = right.binding.key;
        let path = left.binding.key.name;
        let (lo, hi) = choose|lo: int, hi: int| #[trigger] namespace_component(path, key, lo, hi)
            && error.first.span.start == left.start + lo && error.first.span.end == left.start + hi;
        assert(namespace_binding_matches(path, key));
    } else if right.binding.namespace {
        let key = left.binding.key;
        let path = right.binding.key.name;
        let (lo, hi) = choose|lo: int, hi: int| #[trigger] namespace_component(path, key, lo, hi)
            && error.second.span.start == right.start + lo && error.second.span.end == right.start + hi;
        assert(namespace_binding_matches(path, key));
    }
    (left, right)
}

proof fn sites_at_same_item_agree(project: &ParsedProjectSources, left: Site, right: Site)
    requires source_site(project, left), source_site(project, right),
        left.file == right.file, left.item == right.item,
    ensures
        *left.source == *right.source, left.start == right.start, left.end == right.end,
        key_bytes(left.binding.key) == key_bytes(right.binding.key),
        left.binding.namespace == right.binding.namespace,
{}

proof fn namespace_positions_agree(
    left: Site, right: Site, key: NameKey, other: NameKey, a: LocatedName, b: LocatedName,
)
    requires
        namespace_position(left, key, a), namespace_position(right, other, b),
        *left.source == *right.source, left.start == right.start,
        left.binding.key.name.spec_bytes() == right.binding.key.name.spec_bytes(),
        key_bytes(key) == key_bytes(other),
    ensures a == b,
{
    let (lo, hi) = choose|lo: int, hi: int| #[trigger] namespace_component(left.binding.key.name, key, lo, hi)
        && a.span.start == left.start + lo && a.span.end == left.start + hi;
    let (i, j) = choose|i: int, j: int| #[trigger] namespace_component(right.binding.key.name, other, i, j)
        && b.span.start == right.start + i && b.span.end == right.start + j;
    namespace_component_agrees_on_bytes(right.binding.key.name, left.binding.key.name, other, key, i, j);
    crate::project::name_keys::namespace_component_bounds_agree(left.binding.key.name, key, lo, hi, i, j);
}

/// 同じ索引入力の衝突診断は、種別と両方のファイル識別子・文書バージョン・範囲が一致する。
pub proof fn mixed_name_conflicts_agree(project: &ParsedProjectSources, a: NameConflict, b: NameConflict)
    requires mixed_name_conflict_evidence(project, a), mixed_name_conflict_evidence(project, b),
    ensures a.kind == b.kind, a.first == b.first, a.second == b.second,
{
    let (a_left, a_right) = choose_conflict_sites(project, a);
    let (b_left, b_right) = choose_conflict_sites(project, b);
    if pair_before(a_left, a_right, b_left, b_right) {
        assert(!binding_keys_conflict(a_left.binding, a_right.binding));
    }
    if pair_before(b_left, b_right, a_left, a_right) {
        assert(!binding_keys_conflict(b_left.binding, b_right.binding));
    }
    sites_at_same_item_agree(project, a_left, b_left);
    sites_at_same_item_agree(project, a_right, b_right);
    if a_left.binding.namespace {
        namespace_positions_agree(a_left, b_left, a_right.binding.key, b_right.binding.key, a.first, b.first);
    } else if a_right.binding.namespace {
        namespace_positions_agree(a_right, b_right, a_left.binding.key, b_left.binding.key, a.second, b.second);
    }
}

/// 名前で見つけた宣言の位置と種別が、元ファイルの言語別索引に対応することを示す。
pub proof fn mixed_declaration_origin(
    project: &ParsedProjectSources, table: &MixedDeclarationTable, key: NameKey, declaration: ProjectDeclaration,
)
    requires mixed_declaration_table_matches(project, *table), table.declaration_at(key, declaration),
    ensures
        declaration.file < project.sources_model().len(),
        declaration.file < project.indexes_model().len(),
        *declaration.name.source == project.sources_model()[declaration.file as int],
        location_in_source(declaration.name),
        match project.indexes_model()[declaration.file as int] {
            ProjectSourceIndex::Circuit(circuit) =>
                declaration.item < circuit.names@.len() && {
                    let form = circuit.names@[declaration.item as int];
                    declaration.kind == ProjectDeclarationKind::Circuit(form.head) && declaration.name.span == form.name.span
                },
            ProjectSourceIndex::Functional(items) =>
                declaration.item < items@.len() && match items@[declaration.item as int].kind {
                    MetaItemKind::Defn(header) =>
                        declaration.kind is Defn && declaration.name.span == header.name_span,
                    MetaItemKind::Defmacro { name, .. } =>
                        declaration.kind is Defmacro && declaration.name.span == name,
                    _ => false,
                },
        },
{
    reveal(sites_before);
    let i = choose|i: int| 0 <= i < table.sites@.len() && {
        let site = #[trigger] table.sites@[i];
        &&& binding_lookup_matches(site.binding, key, false)
        &&& position_of(site, declaration.name)
        &&& site.kind == Some(declaration.kind)
        &&& site.file == declaration.file && site.item == declaration.item
    };
    assert(source_site(project, table.sites@[i]));
}

impl<'p, 'a> MixedDeclarationTable<'p, 'a> {
    #[verifier::type_invariant]
    spec fn sites_valid(&self) -> bool {
        &&& self.lookup matches Some(index) ==> index.matches(self.sites@)
        &&& forall|i: int| 0 <= i < self.sites@.len() ==> site_is_readable(#[trigger] self.sites@[i])
    }

    /// 指定のキーに対応する宣言が索引にあることを表す。
    pub closed spec fn declares(&self, key: NameKey) -> bool {
        exists|i: int| 0 <= i < self.sites@.len()
            && binding_lookup_matches((#[trigger] self.sites@[i]).binding, key, false)
    }

    /// 宣言の種類と位置が、索引内の指定された名前に対応することを表す。
    pub closed spec fn declaration_at(&self, key: NameKey, declaration: ProjectDeclaration) -> bool {
        exists|i: int| 0 <= i < self.sites@.len() && {
            let site = #[trigger] self.sites@[i];
            &&& binding_lookup_matches(site.binding, key, false)
            &&& position_of(site, declaration.name)
            &&& site.kind == Some(declaration.kind)
            &&& site.file == declaration.file && site.item == declaration.item
        }
    }

    /// 完全修飾名に対応する独立宣言を探す。
    pub fn declaration(&self, key: NameKey) -> (result: Option<ProjectDeclaration<'p, 'a>>)
        ensures result.is_some() == self.declares(key),
            result matches Some(value) ==> self.declaration_at(key, value) && location_in_source(value.name),
    {
        proof { use_type_invariant(self); }
        let rank = find_binding(self.lookup.as_ref(), &self.sites, key, false)?;
        let site = self.sites[rank];
        let Some(kind) = site.kind else { unreachable!() };
        Some(ProjectDeclaration {
            name: site_location(site), kind, file: site.file, item: site.item,
        })
    }

    /// 指定のキーに対応する名前空間が索引にあることを表す。
    pub closed spec fn has_namespace(&self, key: NameKey) -> bool {
        exists|i: int| 0 <= i < self.sites@.len()
            && binding_lookup_matches((#[trigger] self.sites@[i]).binding, key, true)
    }

    /// 範囲が指定された名前空間の最初の導入箇所に対応することを表す。
    pub closed spec fn first_namespace_at(&self, key: NameKey, location: LocatedName) -> bool {
        exists|i: int| 0 <= i < self.sites@.len() && {
            let site = #[trigger] self.sites@[i];
            &&& binding_lookup_matches(site.binding, key, true)
            &&& namespace_position(site, key, location)
            &&& forall|j: int| 0 <= j < i ==> !binding_lookup_matches((#[trigger] self.sites@[j]).binding, key, true)
        }
    }

    /// 明示された名前空間やパスの中間にある名前空間を探し、最初の導入箇所を返す。
    pub fn namespace(&self, key: NameKey) -> (result: Option<LocatedName<'p, 'a>>)
        ensures result.is_some() == self.has_namespace(key),
            result matches Some(location) ==> self.first_namespace_at(key, location) && location_in_source(location),
    {
        proof { use_type_invariant(self); }
        let rank = find_binding(self.lookup.as_ref(), &self.sites, key, true)?;
        site_namespace(self.sites[rank], key)
    }
}

/// 回路と NCG2M の独立宣言と名前空間を、同じ完全修飾名の規則で索引にする。
///
/// # Errors
///
/// 独立宣言の重複や名前空間との衝突があれば、両方の出現箇所を返す。複数あれば先行箇所の順、
/// 先行箇所が同じときは後続箇所の順で選ぶ。出現順はソースの初出順とファイル内の記述順で決まる。
pub fn index_mixed_declarations<'p, 'a>(project: &'p ParsedProjectSources<'a>)
    -> (result: Result<MixedDeclarationTable<'p, 'a>, NameConflict<'p, 'a>>)
    ensures result.is_ok() == !mixed_project_names_conflict(project),
        match result {
            Ok(table) => mixed_declaration_table_matches(project, table),
            Err(error) => mixed_name_conflict_evidence(project, error),
        },
{
    let sites = read_sites(project);
    match search_conflicts(&sites) {
        Ok(lookup) => {
            proof {
                no_source_conflict(project, sites@);
                reveal(sites_before);
                assert forall|rank: int| 0 <= rank < sites@.len()
                    implies site_is_readable(#[trigger] sites@[rank]) by {
                    assert(source_site(project, sites@[rank]));
                };
            }
            Ok(MixedDeclarationTable { sites, lookup })
        }
        Err((left, right)) => {
            proof {
                reveal(sites_before);
                assert(source_site(project, sites@[left as int]) && source_site(project, sites@[right as int]));
            }
            let error = make_conflict(sites[left], sites[right]);
            proof { first_source_conflict(project, sites@, left as int, right as int, error); }
            Err(error)
        }
    }
}

}

impl core::fmt::Debug for MixedDeclarationTable<'_, '_> {
    fn fmt(&self, output: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        output.debug_struct("MixedDeclarationTable").field("sites", &self.sites).finish()
    }
}
