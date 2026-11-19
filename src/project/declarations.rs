//! 名前空間の導入箇所と独立宣言を集め、完全修飾名の衝突を検査する。

#[cfg(verus_only)]
use super::circuits::{name_in_source, parsed_name_span};
use super::name_keys::match_namespace_component;
#[cfg(verus_only)]
use super::name_keys::{component_source_boundaries, key_view, namespace_component};
#[cfg(verus_only)]
use super::parsed_circuit_matches;
use super::{CircuitProject, NameKey, ProjectSource};
use crate::syntax::circuit::{Head, NamedForm};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::is_char_boundary;

verus! {

/// 名前の出現箇所と、所属するファイル。
#[derive(Debug)]
pub struct LocatedName<'p, 'a> {
    /// 正規化されたファイル識別子と文書バージョンを持つソース。
    pub source: &'p ProjectSource<'a>,
    /// 名前の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
}

#[derive(Clone, Copy, Debug)]
struct Occurrence<'p, 'a> {
    _file: usize,
    _index: usize,
    source: &'p ProjectSource<'a>,
    form: &'p NamedForm<'a>,
}

/// 完全修飾名が重複した理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NameConflictKind {
    /// 同じ完全修飾名を持つ独立宣言が二つある。
    DuplicateDeclaration,
    /// 独立宣言と子名前空間が同じ完全修飾名を持つ。
    DeclarationAndNamespace,
}

/// 完全修飾名の衝突と、衝突に関わった二つの出現箇所。
#[derive(Debug)]
pub struct NameConflict<'p, 'a> {
    /// 衝突の種類。
    pub kind: NameConflictKind,
    /// 先に調べた出現箇所。
    pub first: LocatedName<'p, 'a>,
    /// 後で調べた出現箇所。
    pub second: LocatedName<'p, 'a>,
}

/// 共有名前空間に属する独立宣言と、名前空間の導入箇所。
#[derive(Debug)]
pub struct DeclarationTable<'p, 'a> {
    occurrences: Vec<Occurrence<'p, 'a>>,
}

spec fn named_binding(head: Head) -> bool {
    head is Namespace || head is Func || head is Module || head is Struct || head is Latch || head is Memory
}

fn defines_binding(head: Head) -> (binding: bool)
    ensures binding == named_binding(head),
{
    matches!(head, Head::Namespace | Head::Func | Head::Module | Head::Struct | Head::Latch | Head::Memory)
}

/// 独立宣言の所属名前空間と名前から照合キーを定める。
pub open spec fn form_key(form: NamedForm) -> NameKey {
    NameKey { parent: if let Some(parent) = form.namespace { Some(parent.word) } else { None }, name: form.name.word }
}

pub(super) fn key_of<'a>(form: &NamedForm<'a>) -> (key: NameKey<'a>)
    ensures key == form_key(*form),
{
    let parent = if let Some(path) = &form.namespace {
        Some(path.word)
    } else {
        None
    };
    NameKey { parent, name: form.name.word }
}

spec fn before(file: int, index: int, later_file: int, later_index: int) -> bool {
    file < later_file || (file == later_file && index < later_index)
}

spec fn binding_at(project: &CircuitProject, file: int, index: int) -> bool {
    let circuits = project.circuits_model();
    &&& 0 <= file < circuits.len()
    &&& 0 <= index < circuits[file].names@.len()
    &&& named_binding(circuits[file].names@[index].head)
}

spec fn occurrence_matches(project: &CircuitProject, item: Occurrence) -> bool {
    let file = item._file as int;
    let index = item._index as int;
    &&& binding_at(project, file, index)
    &&& file < project.sources_model().len()
    &&& *item.source == project.sources_model()[file]
    &&& *item.form == project.circuits_model()[file].names@[index]
    &&& name_in_source(item.source.text, item.form.name)
}

#[verifier::opaque]
spec fn occurrences_before(
    project: &CircuitProject, items: Seq<Occurrence>, file: int, index: int,
) -> bool {
    &&& forall|at: int| 0 <= at < items.len() ==> {
        let item = #[trigger] items[at];
        occurrence_matches(project, item) && before(item._file as int, item._index as int, file, index)
    }
    &&& forall|f: int, n: int| #[trigger] binding_at(project, f, n) && before(f, n, file, index)
        ==> exists|at: int| 0 <= at < items.len() && (#[trigger] items[at])._file == f && items[at]._index == n
    &&& forall|i: int, j: int| 0 <= i < j < items.len() ==> {
        let left = #[trigger] items[i];
        let right = #[trigger] items[j];
        before(left._file as int, left._index as int, right._file as int, right._index as int)
    }
}

proof fn advance_occurrences(
    project: &CircuitProject, items: Seq<Occurrence>, file: int, index: int, picked: Option<Occurrence>,
)
    requires
        occurrences_before(project, items, file, index),
        match picked {
            Some(item) => occurrence_matches(project, item) && item._file == file && item._index == index,
            None => !binding_at(project, file, index),
        },
    ensures
        occurrences_before(project,
            if let Some(item) = picked { items.push(item) } else { items }, file, index + 1),
{
    reveal(occurrences_before);
    let next = if let Some(item) = picked { items.push(item) } else { items };
    assert forall|f: int, n: int| #[trigger] binding_at(project, f, n) && before(f, n, file, index + 1)
        implies exists|at: int| 0 <= at < next.len() && (#[trigger] next[at])._file == f && next[at]._index == n by {
        if before(f, n, file, index) {
            let at = choose|at: int| 0 <= at < items.len() && (#[trigger] items[at])._file == f && items[at]._index == n;
            assert(next[at] == items[at]);
        } else {
            assert(f == file && n == index);
            assert(picked is Some);
            assert(next[items.len() as int] == picked->Some_0);
        }
    };
}

proof fn advance_file(project: &CircuitProject, items: Seq<Occurrence>, file: int, count: int)
    requires
        0 <= file < project.circuits_model().len(),
        count == project.circuits_model()[file].names@.len(),
        occurrences_before(project, items, file, count),
    ensures occurrences_before(project, items, file + 1, 0),
{
    reveal(occurrences_before);
    assert forall|f: int, n: int| #[trigger] binding_at(project, f, n) && before(f, n, file + 1, 0)
        implies before(f, n, file, count) by {};
}

spec fn remaining_names(project: &CircuitProject, file: int, index: int) -> int {
    let circuits = project.circuits_model();
    if 0 <= file < circuits.len() { circuits[file].names@.len() - index } else { 0 }
}

fn read_occurrences<'p, 'a>(project: &'p CircuitProject<'a>) -> (items: Vec<Occurrence<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures occurrences_before(project, items@, project.circuits_model().len() as int, 0),
{
    let sources = project.sources();
    let circuits = project.circuits();
    let mut items: Vec<Occurrence> = Vec::new();
    let mut file = 0;
    let mut index = 0;
    assert(occurrences_before(project, items@, 0, 0)) by { reveal(occurrences_before); }
    while file < circuits.len()
        invariant
            project.has_parsed_sources(),
            sources@ == project.sources_model(),
            circuits@ == project.circuits_model(),
            file <= circuits@.len(),
            file < circuits@.len() ==> index <= circuits@[file as int].names@.len(),
            file == circuits@.len() ==> index == 0,
            occurrences_before(project, items@, file as int, index as int),
        decreases circuits@.len() - file, remaining_names(project, file as int, index as int),
    {
        let parsed = &circuits[file];
        if index == parsed.names.len() {
            proof { advance_file(project, items@, file as int, index as int); }
            file += 1;
            index = 0;
            continue;
        }
        let form = &parsed.names[index];
        let picked = if defines_binding(form.head) {
            let source = &sources[file];
            proof {
                assert(parsed_circuit_matches(*source, *parsed));
                parsed_name_span(*source, *parsed, index as int);
            }
            Some(Occurrence { _file: file, _index: index, source, form })
        } else {
            None
        };
        proof { advance_occurrences(project, items@, file as int, index as int, picked); }
        if let Some(item) = picked {
            items.push(item);
        }
        index += 1;
    }
    items
}

spec fn portion_matches(form: NamedForm, key: NameKey, span: Range<usize>) -> bool {
    exists|lo: int, hi: int| #[trigger] namespace_component(form.name.word, key, lo, hi)
        && span.start == form.name.span.start + lo && span.end == form.name.span.start + hi
}

spec fn conflicts(left: NamedForm, right: NamedForm) -> bool {
    if left.head is Namespace && right.head is Namespace {
        false
    } else if left.head is Namespace {
        exists|lo: int, hi: int| #[trigger] namespace_component(left.name.word, form_key(right), lo, hi)
    } else if right.head is Namespace {
        exists|lo: int, hi: int| #[trigger] namespace_component(right.name.word, form_key(left), lo, hi)
    } else {
        key_view(form_key(left)) == key_view(form_key(right))
    }
}

/// 範囲の両端が、示されたソースの UTF-8 文字境界にあることを表す。
pub closed spec fn location_in_source(location: LocatedName) -> bool {
    let bytes = location.source.text.spec_bytes();
    &&& location.span.start < location.span.end <= bytes.len()
    &&& is_char_boundary(bytes, location.span.start as int)
    &&& is_char_boundary(bytes, location.span.end as int)
}

spec fn conflict_at(left: Occurrence, right: Occurrence, error: NameConflict) -> bool {
    &&& location_in_source(error.first) && location_in_source(error.second)
    &&& *error.first.source == *left.source && *error.second.source == *right.source
    &&& if left.form.head is Namespace {
        &&& !(right.form.head is Namespace)
        &&& error.kind is DeclarationAndNamespace
        &&& portion_matches(*left.form, form_key(*right.form), error.first.span)
        &&& error.second.span == right.form.name.span
    } else if right.form.head is Namespace {
        &&& error.kind is DeclarationAndNamespace
        &&& error.first.span == left.form.name.span
        &&& portion_matches(*right.form, form_key(*left.form), error.second.span)
    } else {
        &&& error.kind is DuplicateDeclaration
        &&& key_view(form_key(*left.form)) == key_view(form_key(*right.form))
        &&& error.first.span == left.form.name.span && error.second.span == right.form.name.span
    }
}

/// 独立宣言が重複するか、独立宣言と子名前空間が衝突することを表す。
pub closed spec fn project_names_conflict(project: &CircuitProject) -> bool {
    exists|f: int, n: int, g: int, m: int| #[trigger] binding_at(project, f, n)
        && #[trigger] binding_at(project, g, m) && (f != g || n != m)
        && conflicts(project.circuits_model()[f].names@[n], project.circuits_model()[g].names@[m])
}

/// 衝突の種類と、同じ名前を導入した二つの異なる出現箇所の根拠を表す。
pub closed spec fn name_conflict_evidence(project: &CircuitProject, error: NameConflict) -> bool {
    exists|left: Occurrence, right: Occurrence| #[trigger] occurrence_matches(project, left)
        && #[trigger] occurrence_matches(project, right)
        && before(left._file as int, left._index as int, right._file as int, right._index as int)
        && conflict_at(left, right, error)
}

/// 表が、解析したプロジェクトの名前空間と独立宣言の出現箇所に対応することを表す。
pub closed spec fn declaration_table_matches(project: &CircuitProject, table: DeclarationTable) -> bool {
    occurrences_before(project, table.occurrences@, project.circuits_model().len() as int, 0)
}

/// プロジェクトに完全修飾名で特定できる独立宣言があることを表す。
pub closed spec fn project_declares(project: &CircuitProject, key: NameKey) -> bool {
    exists|file: int, index: int| #[trigger] binding_at(project, file, index)
        && {
            let form = project.circuits_model()[file].names@[index];
            !(form.head is Namespace) && key_view(form_key(form)) == key_view(key)
        }
}

pub(super) proof fn declaration_location_evidence(
    table: &DeclarationTable, key: NameKey, source: &ProjectSource, form: &NamedForm,
)
    requires table.well_formed(), table.declaration_at(key, source, form),
    ensures location_in_source(LocatedName { source, span: form.name.span }),
{
    let items = table.occurrences@;
    let i = choose|i: int| 0 <= i < items.len() && {
        let item = #[trigger] items[i];
        &&& !(item.form.head is Namespace)
        &&& *item.source == *source && *item.form == *form
        &&& key_view(form_key(*item.form)) == key_view(key)
    };
    assert(name_in_source(items[i].source.text, items[i].form.name));
}

pub(super) proof fn declaration_key_evidence(
    table: &DeclarationTable, key: NameKey, source: &ProjectSource, form: &NamedForm,
)
    requires table.declaration_at(key, source, form),
    ensures key_view(form_key(*form)) == key_view(key),
{
}

pub(super) proof fn declaration_key_equivalence(project: &CircuitProject, left: NameKey, right: NameKey)
    requires key_view(left) == key_view(right),
    ensures project_declares(project, left) <==> project_declares(project, right),
{
}

pub(super) proof fn located_name_evidence(location: LocatedName)
    requires
        location.span.start < location.span.end <= location.source.text.spec_bytes().len(),
        is_char_boundary(location.source.text.spec_bytes(), location.span.start as int),
        is_char_boundary(location.source.text.spec_bytes(), location.span.end as int),
    ensures location_in_source(location),
{
}

pub(super) proof fn declaration_lookup_agrees(
    project: &CircuitProject, table: &DeclarationTable, key: NameKey,
)
    requires declaration_table_matches(project, *table),
    ensures
        project_declares(project, key) <==>
            exists|source: &ProjectSource, form: &NamedForm| #[trigger] table.declaration_at(key, source, form),
{
    let items = table.occurrences@;
    reveal(occurrences_before);
    if project_declares(project, key) {
        let (file, index) = choose|file: int, index: int| #[trigger] binding_at(project, file, index)
            && {
                let form = project.circuits_model()[file].names@[index];
                !(form.head is Namespace) && key_view(form_key(form)) == key_view(key)
            };
        let i = choose|i: int| 0 <= i < items.len() && (#[trigger] items[i])._file == file && items[i]._index == index;
        let item = items[i];
        assert(table.declaration_at(key, item.source, item.form));
    } else if exists|source: &ProjectSource, form: &NamedForm| #[trigger] table.declaration_at(key, source, form) {
        let (source, form) = choose|source: &ProjectSource, form: &NamedForm| #[trigger] table.declaration_at(key, source, form);
        let i = choose|i: int| 0 <= i < items.len()
            && {
                let item = #[trigger] items[i];
                !(item.form.head is Namespace) && *item.source == *source && *item.form == *form
                    && key_view(form_key(*item.form)) == key_view(key)
            };
        assert(occurrence_matches(project, items[i]));
        assert(project_declares(project, key));
    }
}

fn namespace_location<'p, 'a>(
    item: Occurrence<'p, 'a>, key: NameKey,
) -> (location: Option<LocatedName<'p, 'a>>)
    requires name_in_source(item.source.text, item.form.name),
    ensures
        location.is_some() <==> (exists|lo: int, hi: int| #[trigger] namespace_component(item.form.name.word, key, lo, hi)),
        location matches Some(location) ==> *location.source == *item.source
            && portion_matches(*item.form, key, location.span) && location_in_source(location),
{
    let (lo, hi) = match_namespace_component(item.form.name.word, key)?;
    let start = item.form.name.span.start;
    assert(namespace_component(item.form.name.word, key, lo as int, hi as int));
    proof {
        component_source_boundaries(item.source.text, item.form.name.word, key,
            start as int, item.form.name.span.end as int, lo as int, hi as int);
    }
    Some(LocatedName { source: item.source, span: start + lo..start + hi })
}

fn name_location<'p, 'a>(item: Occurrence<'p, 'a>) -> (location: LocatedName<'p, 'a>)
    requires name_in_source(item.source.text, item.form.name),
    ensures *location.source == *item.source && location.span == item.form.name.span && location_in_source(location),
{
    let span = &item.form.name.span;
    LocatedName { source: item.source, span: span.start..span.end }
}

fn check_pair<'p, 'a>(left: Occurrence<'p, 'a>, right: Occurrence<'p, 'a>) -> (error: Option<NameConflict<'p, 'a>>)
    requires
        name_in_source(left.source.text, left.form.name),
        name_in_source(right.source.text, right.form.name),
    ensures
        error.is_some() == conflicts(*left.form, *right.form),
        error matches Some(error) ==> conflict_at(left, right, error),
{
    match (left.form.head, right.form.head) {
        (Head::Namespace, Head::Namespace) => None,
        (Head::Namespace, _) => {
            let first = namespace_location(left, key_of(right.form))?;
            Some(NameConflict { kind: NameConflictKind::DeclarationAndNamespace, first, second: name_location(right) })
        },
        (_, Head::Namespace) => {
            let second = namespace_location(right, key_of(left.form))?;
            Some(NameConflict { kind: NameConflictKind::DeclarationAndNamespace, first: name_location(left), second })
        },
        _ => {
            if key_of(left.form).same_name(key_of(right.form)) {
                Some(NameConflict {
                    kind: NameConflictKind::DuplicateDeclaration,
                    first: name_location(left), second: name_location(right),
                })
            } else {
                None
            }
        },
    }
}

proof fn record_conflict(
    project: &CircuitProject, items: Seq<Occurrence>, left: int, right: int, error: NameConflict,
)
    requires
        occurrences_before(project, items, project.circuits_model().len() as int, 0),
        0 <= left < right < items.len(),
        conflict_at(items[left], items[right], error),
    ensures project_names_conflict(project), name_conflict_evidence(project, error),
{
    reveal(occurrences_before);
    let l = items[left];
    let r = items[right];
    assert(occurrence_matches(project, l) && occurrence_matches(project, r));
    assert(before(l._file as int, l._index as int, r._file as int, r._index as int));
    assert(conflicts(*l.form, *r.form));
}

proof fn rule_out_conflicts(project: &CircuitProject, items: Seq<Occurrence>)
    requires
        occurrences_before(project, items, project.circuits_model().len() as int, 0),
        forall|i: int, j: int| 0 <= i < j < items.len() ==> !conflicts(*(#[trigger] items[i]).form, *(#[trigger] items[j]).form),
    ensures !project_names_conflict(project),
{
    reveal(occurrences_before);
    if project_names_conflict(project) {
        let (f, n, g, m) = choose|f: int, n: int, g: int, m: int| #[trigger] binding_at(project, f, n)
            && #[trigger] binding_at(project, g, m) && (f != g || n != m)
            && conflicts(project.circuits_model()[f].names@[n], project.circuits_model()[g].names@[m]);
        let left = choose|i: int| 0 <= i < items.len() && (#[trigger] items[i])._file == f && items[i]._index == n;
        let right = choose|j: int| 0 <= j < items.len() && (#[trigger] items[j])._file == g && items[j]._index == m;
        assert(left != right);
        assert(occurrence_matches(project, items[left]));
        assert(occurrence_matches(project, items[right]));
        if right < left {
            assert(conflicts(*items[right].form, *items[left].form) == conflicts(*items[left].form, *items[right].form));
        }
    }
}

impl<'p, 'a> DeclarationTable<'p, 'a> {
    /// 保持している名前とその範囲が、元ソースの字句に対応することを表す。
    pub closed spec fn well_formed(&self) -> bool {
        forall|i: int| 0 <= i < self.occurrences@.len() ==> {
            let item = #[trigger] self.occurrences@[i];
            name_in_source(item.source.text, item.form.name)
        }
    }

    /// 独立宣言が属するファイルと、名前索引の項目との対応を表す。
    pub closed spec fn declaration_at(&self, key: NameKey, source: &ProjectSource, form: &NamedForm) -> bool {
        &&& key_view(form_key(*form)) == key_view(key)
        &&& exists|i: int| 0 <= i < self.occurrences@.len()
            && {
                let item = #[trigger] self.occurrences@[i];
                &&& !(item.form.head is Namespace)
                &&& *item.source == *source && *item.form == *form
            }
    }

    /// 完全修飾名で独立宣言を探し、ファイルと名前索引の項目を返す。
    pub fn declaration(&self, key: NameKey) -> (result: Option<(&'p ProjectSource<'a>, &'p NamedForm<'a>)>)
        ensures
            result matches Some((source, form)) ==> self.declaration_at(key, source, form),
            result.is_none() ==> forall|source: &ProjectSource, form: &NamedForm|
                !#[trigger] self.declaration_at(key, source, form),
    {
        let mut index = 0;
        while index < self.occurrences.len()
            invariant
                index <= self.occurrences@.len(),
                forall|i: int| 0 <= i < index ==> {
                    let item = #[trigger] self.occurrences@[i];
                    item.form.head is Namespace || key_view(form_key(*item.form)) != key_view(key)
                },
            decreases self.occurrences@.len() - index,
        {
            let item = self.occurrences[index];
            if !matches!(item.form.head, Head::Namespace) && key_of(item.form).same_name(key) {
                assert(self.declaration_at(key, item.source, item.form));
                return Some((item.source, item.form));
            }
            index += 1;
        }
        None
    }

    /// 名前空間を導入した成分の範囲と、そのファイルを表す。
    pub closed spec fn namespace_at(&self, key: NameKey, location: LocatedName) -> bool {
        exists|i: int| 0 <= i < self.occurrences@.len()
            && {
                let item = #[trigger] self.occurrences@[i];
                &&& item.form.head is Namespace
                &&& *item.source == *location.source
                &&& portion_matches(*item.form, key, location.span)
            }
    }

    /// 明示された名前空間と中間の名前空間を探し、最初の導入箇所を返す。
    pub fn namespace(&self, key: NameKey) -> (result: Option<LocatedName<'p, 'a>>)
        requires self.well_formed(),
        ensures
            result matches Some(location) ==> self.namespace_at(key, location) && location_in_source(location),
            result.is_none() ==> forall|location: LocatedName| !#[trigger] self.namespace_at(key, location),
    {
        let mut index = 0;
        while index < self.occurrences.len()
            invariant
                self.well_formed(),
                index <= self.occurrences@.len(),
                forall|i: int| 0 <= i < index ==> {
                    let item = #[trigger] self.occurrences@[i];
                    item.form.head is Namespace ==> !(exists|lo: int, hi: int|
                        #[trigger] namespace_component(item.form.name.word, key, lo, hi))
                },
            decreases self.occurrences@.len() - index,
        {
            let item = self.occurrences[index];
            if matches!(item.form.head, Head::Namespace) {
                if let Some(location) = namespace_location(item, key) {
                    assert(self.namespace_at(key, location));
                    return Some(location);
                }
            }
            index += 1;
        }
        None
    }
}

/// 回路プロジェクトの名前空間と独立宣言を索引にする。
///
/// # Errors
///
/// 重複宣言や子名前空間との衝突があれば、同じ名前を導入した二つの出現箇所を返す。
pub fn index_declarations<'p, 'a>(
    project: &'p CircuitProject<'a>,
) -> (result: Result<DeclarationTable<'p, 'a>, NameConflict<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures
        result.is_ok() <==> !project_names_conflict(project),
        match result {
            Ok(table) => declaration_table_matches(project, table) && table.well_formed(),
            Err(error) => name_conflict_evidence(project, error),
        },
{
    let items = read_occurrences(project);
    let mut left = 0;
    let mut right = 1;
    while left < items.len()
        invariant
            occurrences_before(project, items@, project.circuits_model().len() as int, 0),
            left <= items@.len(),
            right <= items@.len() + 1,
            left < items@.len() ==> left < right,
            forall|i: int, j: int| 0 <= i < j < items@.len() && before(i, j, left as int, right as int)
                ==> !conflicts(*(#[trigger] items@[i]).form, *(#[trigger] items@[j]).form),
        decreases items@.len() - left, items@.len() + 1 - right,
    {
        if right >= items.len() {
            left += 1;
            right = if left < items.len() { left + 1 } else { left };
            continue;
        }
        proof { reveal(occurrences_before); }
        if let Some(error) = check_pair(items[left], items[right]) {
            proof { record_conflict(project, items@, left as int, right as int, error); }
            return Err(error);
        }
        right += 1;
    }
    proof {
        rule_out_conflicts(project, items@);
        reveal(occurrences_before);
    }
    Ok(DeclarationTable { occurrences: items })
}

} // verus!
