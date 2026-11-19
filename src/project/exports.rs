//! 共有宣言表に公開指定を適用する。

#[cfg(verus_only)]
use super::circuits::parsed_index_evidence;
use super::circuits::read_indexed_atom;
#[cfg(verus_only)]
use super::declarations::{
    declaration_key_equivalence, declaration_lookup_agrees, located_name_evidence,
};
#[cfg(verus_only)]
use super::name_keys::{key_bytes, key_views_agree};
use super::{
    CircuitProject, DeclarationTable, LocatedName, NameConflict, NameKey, ProjectSource,
    index_declarations,
};
#[cfg(verus_only)]
use super::{
    declaration_table_matches, location_in_source, name_conflict_evidence, parsed_circuit_matches,
    project_declares, project_names_conflict,
};
use crate::syntax::Form;
use crate::syntax::circuit::Head;
#[cfg(verus_only)]
use crate::syntax::circuit::export_entry_evidence;
#[cfg(verus_only)]
use crate::syntax::form_span;
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 共有宣言表に公開指定を適用できなかった理由。
#[derive(Debug)]
pub enum ExportError<'p, 'a> {
    /// 宣言表を作るときに見つかった名前の衝突。
    Conflict(NameConflict<'p, 'a>),
    /// 指定された名前を持つ独立宣言が、同じ名前空間に存在しない。
    MissingDeclaration(LocatedName<'p, 'a>),
}

/// 共有宣言表と、公開された宣言の集合。
#[derive(Debug)]
pub struct ExportTable<'p, 'a> {
    declarations: DeclarationTable<'p, 'a>,
    names: Vec<NameKey<'a>>,
}

#[derive(Debug)]
struct ExportSite<'p, 'a> {
    _file: usize,
    _entry: usize,
    _arg: usize,
    source: &'p ProjectSource<'a>,
    key: NameKey<'a>,
    span: Range<usize>,
}

spec fn before(f: int, e: int, a: int, file: int, entry: int, arg: int) -> bool {
    f < file || (f == file && (e < entry || (e == entry && a < arg)))
}

spec fn export_at(project: &CircuitProject, file: int, entry: int, arg: int) -> bool {
    let circuits = project.circuits_model();
    &&& 0 <= file < circuits.len()
    &&& 0 <= entry < circuits[file].syntax.entries@.len()
    &&& {
        let parsed = circuits[file];
        let item = parsed.syntax.entries@[entry];
        let root = item.form as int;
        &&& item.head is Export
        &&& 0 <= root < parsed.syntax.forms@.len()
        &&& parsed.syntax.forms@[root] is List
        &&& 0 <= arg
        &&& root + 2 + arg < parsed.syntax.forms@[root]->List_end <= parsed.syntax.forms@.len()
    }
}

spec fn export_key(project: &CircuitProject, file: int, entry: int, arg: int, key: NameKey) -> bool {
    &&& export_at(project, file, entry, arg)
    &&& file < project.sources_model().len()
    &&& {
        let source = project.sources_model()[file].text.spec_bytes();
        let parsed = project.circuits_model()[file];
        let item = parsed.syntax.entries@[entry];
        let span = form_span(parsed.syntax.forms@[item.form + 2 + arg]);
        &&& key.name.spec_bytes() == source[span.start as int..span.end as int]
        &&& match (item.namespace, key.parent) {
            (None, None) => true,
            (Some(parent), Some(path)) => {
                &&& parent + 2 < parsed.syntax.forms@.len()
                &&& {
                    let span = form_span(parsed.syntax.forms@[parent + 2]);
                    path.spec_bytes() == source[span.start as int..span.end as int]
                }
            },
            _ => false,
        }
    }
}

spec fn site_matches(project: &CircuitProject, site: ExportSite) -> bool {
    let f = site._file as int;
    let e = site._entry as int;
    let a = site._arg as int;
    &&& export_key(project, f, e, a, site.key)
    &&& *site.source == project.sources_model()[f]
    &&& {
        let parsed = project.circuits_model()[f];
        let item = parsed.syntax.entries@[e];
        &&& site.span == form_span(parsed.syntax.forms@[item.form + 2 + a])
        &&& location_in_source(LocatedName { source: site.source, span: site.span })
    }
}

#[verifier::opaque]
spec fn sites_before(project: &CircuitProject, sites: Seq<ExportSite>, file: int, entry: int, arg: int) -> bool {
    &&& forall|i: int| 0 <= i < sites.len() ==> {
        let site = #[trigger] sites[i];
        &&& site_matches(project, site)
        &&& before(site._file as int, site._entry as int, site._arg as int, file, entry, arg)
    }
    &&& forall|f: int, e: int, a: int| #[trigger] export_at(project, f, e, a) && before(f, e, a, file, entry, arg)
        ==> exists|i: int| 0 <= i < sites.len()
            && (#[trigger] sites[i])._file == f && sites[i]._entry == e && sites[i]._arg == a
    &&& forall|i: int, j: int| 0 <= i < j < sites.len() ==> {
        let l = #[trigger] sites[i];
        let r = #[trigger] sites[j];
        before(l._file as int, l._entry as int, l._arg as int, r._file as int, r._entry as int, r._arg as int)
    }
}

proof fn save_site(project: &CircuitProject, sites: Seq<ExportSite>, site: ExportSite, file: int, entry: int, arg: int)
    requires
        sites_before(project, sites, file, entry, arg),
        site_matches(project, site),
        site._file == file && site._entry == entry && site._arg == arg,
    ensures sites_before(project, sites.push(site), file, entry, arg + 1),
{
    reveal(sites_before);
    let next = sites.push(site);
    assert forall|f: int, e: int, a: int| #[trigger] export_at(project, f, e, a) && before(f, e, a, file, entry, arg + 1)
        implies exists|i: int| 0 <= i < next.len()
            && (#[trigger] next[i])._file == f && next[i]._entry == e && next[i]._arg == a by {
        if before(f, e, a, file, entry, arg) {
            let i = choose|i: int| 0 <= i < sites.len()
                && (#[trigger] sites[i])._file == f && sites[i]._entry == e && sites[i]._arg == a;
            assert(next[i] == sites[i]);
        } else {
            assert(next[sites.len() as int] == site);
        }
    };
}

proof fn next_entry(project: &CircuitProject, sites: Seq<ExportSite>, file: int, entry: int, arg: int)
    requires
        sites_before(project, sites, file, entry, arg),
        forall|a: int| #[trigger] export_at(project, file, entry, a) ==> a < arg,
    ensures sites_before(project, sites, file, entry + 1, 0),
{
    reveal(sites_before);
    assert forall|f: int, e: int, a: int| #[trigger] export_at(project, f, e, a) && before(f, e, a, file, entry + 1, 0)
        implies before(f, e, a, file, entry, arg) by {};
}

proof fn next_file(project: &CircuitProject, sites: Seq<ExportSite>, file: int, entry: int)
    requires
        0 <= file < project.circuits_model().len(),
        entry == project.circuits_model()[file].syntax.entries@.len(),
        sites_before(project, sites, file, entry, 0),
    ensures sites_before(project, sites, file + 1, 0, 0),
{
    reveal(sites_before);
    assert forall|f: int, e: int, a: int| #[trigger] export_at(project, f, e, a) && before(f, e, a, file + 1, 0, 0)
        implies before(f, e, a, file, entry, 0) by {};
}

spec fn left_in_entry(project: &CircuitProject, file: int, entry: int, arg: int) -> nat {
    let circuits = project.circuits_model();
    if 0 <= file < circuits.len() && 0 <= entry < circuits[file].syntax.entries@.len() {
        let item = circuits[file].syntax.entries@[entry];
        let forms = circuits[file].syntax.forms@;
        if item.head is Export && item.form < forms.len() && forms[item.form as int] is List {
            (forms[item.form as int]->List_end - item.form - 2 - arg) as nat
        } else { 0 }
    } else { 0 }
}

fn read_exports<'p, 'a>(project: &'p CircuitProject<'a>) -> (sites: Vec<ExportSite<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures sites_before(project, sites@, project.circuits_model().len() as int, 0, 0),
{
    let circuits = project.circuits();
    let sources = project.sources();
    let mut sites = Vec::new();
    let mut file = 0;
    let mut entry = 0;
    let mut arg = 0;
    assert(sites_before(project, sites@, 0, 0, 0)) by { reveal(sites_before); }
    while file < circuits.len()
        invariant
            project.has_parsed_sources(),
            sources@ == project.sources_model(),
            circuits@ == project.circuits_model(),
            file <= circuits@.len(),
            file < circuits@.len() ==> entry <= circuits@[file as int].syntax.entries@.len(),
            file == circuits@.len() ==> entry == 0 && arg == 0,
            arg > 0 ==> export_at(project, file as int, entry as int, arg - 1),
            sites_before(project, sites@, file as int, entry as int, arg as int),
        decreases circuits@.len() - file,
            if file < circuits@.len() { circuits@[file as int].syntax.entries@.len() - entry } else { 0 },
            left_in_entry(project, file as int, entry as int, arg as int),
    {
        let parsed = &circuits[file];
        let source = &sources[file];
        let entries = &parsed.syntax.entries;
        if entry == entries.len() {
            proof { next_file(project, sites@, file as int, entry as int); }
            file += 1;
            entry = 0;
            arg = 0;
            continue;
        }
        let item = &entries[entry];
        if !matches!(item.head, Head::Export) {
            proof { next_entry(project, sites@, file as int, entry as int, arg as int); }
            entry += 1;
            arg = 0;
            continue;
        }
        let forms = &parsed.syntax.forms;
        proof {
            assert(parsed_circuit_matches(*source, *parsed));
            parsed_index_evidence(*source, *parsed);
            export_entry_evidence(source.text, forms@, entries@, entry as int);
        }
        let Form::List { end: stop, .. } = &forms[item.form] else {
            proof { assert(false); }
            return sites;
        };
        let position = item.form + 2 + arg;
        if position == *stop {
            proof { next_entry(project, sites@, file as int, entry as int, arg as int); }
            entry += 1;
            arg = 0;
            continue;
        }
        let parent = if let Some(parent) = item.namespace {
            assert(entries@[entry as int].namespace == Some(parent));
            let _length = forms.len();
            assert(parent + 2 < _length);
            Some(read_indexed_atom(source.text, forms, parent + 2).0)
        } else {
            None
        };
        let (name, span) = read_indexed_atom(source.text, forms, position);
        let site = ExportSite { _file: file, _entry: entry, _arg: arg, source, key: NameKey { parent, name }, span };
        proof {
            located_name_evidence(LocatedName { source, span: site.span });
            save_site(project, sites@, site, file as int, entry as int, arg as int);
        }
        sites.push(site);
        arg += 1;
    }
    sites
}

spec fn published(names: Seq<NameKey>, key: NameKey) -> bool {
    exists|i: int| 0 <= i < names.len() && key_bytes(#[trigger] names[i]) == key_bytes(key)
}

fn is_published_in(names: &[NameKey], key: NameKey) -> (found: bool)
    ensures found == published(names@, key),
{
    let mut i = 0;
    while i < names.len()
        invariant
            i <= names@.len(),
            forall|j: int| 0 <= j < i ==> key_bytes(#[trigger] names@[j]) != key_bytes(key),
        decreases names@.len() - i,
    {
        if names[i].same_name(key) {
            return true;
        }
        i += 1;
    }
    false
}

spec fn indicated(project: &CircuitProject, key: NameKey) -> bool {
    exists|f: int, e: int, a: int| #[trigger] export_key(project, f, e, a, key)
}

proof fn export_spelling_determines_key(
    project: &CircuitProject, f: int, e: int, a: int, left: NameKey, right: NameKey,
)
    requires export_key(project, f, e, a, left), export_key(project, f, e, a, right),
    ensures key_bytes(left) == key_bytes(right),
{
}

proof fn relocate_key(project: &CircuitProject, f: int, e: int, a: int, left: NameKey, right: NameKey)
    requires export_key(project, f, e, a, left), key_bytes(left) == key_bytes(right),
    ensures export_key(project, f, e, a, right),
{
}

proof fn publication_matches_requests(project: &CircuitProject, sites: Seq<ExportSite>, names: Seq<NameKey>)
    requires
        sites_before(project, sites, project.circuits_model().len() as int, 0, 0),
        forall|i: int| 0 <= i < sites.len() ==> #[trigger] published(names, sites[i].key),
        forall|i: int| 0 <= i < names.len() ==> #[trigger] indicated(project, names[i]),
    ensures forall|key: NameKey| #[trigger] published(names, key) <==> indicated(project, key),
{
    reveal(sites_before);
    assert forall|key: NameKey| #[trigger] published(names, key) <==> indicated(project, key) by {
        if published(names, key) {
            let i = choose|i: int| 0 <= i < names.len() && key_bytes(#[trigger] names[i]) == key_bytes(key);
            assert(indicated(project, names[i]));
            let (f, e, a) = choose|f: int, e: int, a: int| #[trigger] export_key(project, f, e, a, names[i]);
            relocate_key(project, f, e, a, names[i], key);
        }
        if indicated(project, key) {
            let (f, e, a) = choose|f: int, e: int, a: int| #[trigger] export_key(project, f, e, a, key);
            let i = choose|i: int| 0 <= i < sites.len()
                && (#[trigger] sites[i])._file == f && sites[i]._entry == e && sites[i]._arg == a;
            assert(site_matches(project, sites[i]));
            export_spelling_determines_key(project, f, e, a, sites[i].key, key);
            assert(published(names, sites[i].key));
        }
    };
}

spec fn declarations_before_site(project: &CircuitProject, site: ExportSite) -> bool {
    forall|f: int, e: int, a: int, key: NameKey| #[trigger] export_key(project, f, e, a, key)
        && before(f, e, a, site._file as int, site._entry as int, site._arg as int)
        ==> project_declares(project, key)
}

proof fn earlier_exports_resolve(project: &CircuitProject, sites: Seq<ExportSite>, index: int)
    requires
        sites_before(project, sites, project.circuits_model().len() as int, 0, 0),
        0 <= index < sites.len(),
        forall|i: int| 0 <= i < index ==> #[trigger] project_declares(project, sites[i].key),
    ensures declarations_before_site(project, sites[index]),
{
    reveal(sites_before);
    let current = sites[index];
    assert forall|f: int, e: int, a: int, key: NameKey| #[trigger] export_key(project, f, e, a, key)
        && before(f, e, a, current._file as int, current._entry as int, current._arg as int)
        implies project_declares(project, key) by {
        assert(site_matches(project, current));
        let i = choose|i: int| 0 <= i < sites.len()
            && (#[trigger] sites[i])._file == f && sites[i]._entry == e && sites[i]._arg == a;
        let earlier = sites[i];
        assert(i < index);
        assert(site_matches(project, earlier));
        export_spelling_determines_key(project, f, e, a, earlier.key, key);
        key_views_agree(earlier.key, key);
        declaration_key_equivalence(project, earlier.key, key);
        assert(project_declares(project, earlier.key));
    };
}

/// 公開指定がすべて、同じ名前空間にある独立宣言を指すことを表す。
pub closed spec fn project_exports_valid(project: &CircuitProject) -> bool {
    forall|key: NameKey| #[trigger] indicated(project, key) ==> project_declares(project, key)
}

/// 公開指定の診断を、宣言表の衝突または未解決の公開名に結び付ける。
pub closed spec fn export_error_evidence(project: &CircuitProject, error: ExportError) -> bool {
    match error {
        ExportError::Conflict(conflict) => name_conflict_evidence(project, conflict),
        ExportError::MissingDeclaration(location) => !project_names_conflict(project)
            && (exists|site: ExportSite| #[trigger] site_matches(project, site)
                && *site.source == *location.source && site.span == location.span
                && !project_declares(project, site.key) && declarations_before_site(project, site)),
    }
}

/// 各宣言の公開状態が、元の公開指定と一致することを表す。
pub closed spec fn export_table_matches(project: &CircuitProject, table: ExportTable) -> bool {
    &&& !project_names_conflict(project)
    &&& project_exports_valid(project)
    &&& declaration_table_matches(project, table.declarations)
    &&& table.declarations.well_formed()
    &&& forall|i: int, j: int| 0 <= i < j < table.names@.len() ==>
        key_bytes(#[trigger] table.names@[i]) != key_bytes(#[trigger] table.names@[j])
    &&& forall|key: NameKey| #[trigger] published(table.names@, key) <==> indicated(project, key)
}

pub(super) proof fn exports_use_project_declarations(project: &CircuitProject, table: ExportTable)
    requires export_table_matches(project, table),
    ensures declaration_table_matches(project, table.declarations_model()), !project_names_conflict(project),
{
}

impl<'p, 'a> ExportTable<'p, 'a> {
    /// 完全修飾名で指定した独立宣言が公開されていることを表す。
    pub closed spec fn publishes(&self, key: NameKey) -> bool {
        published(self.names@, key)
    }

    /// 完全修飾名で指定した独立宣言が公開されているかを返す。
    pub fn is_public(&self, key: NameKey) -> (found: bool)
        ensures found == self.publishes(key),
    {
        is_published_in(&self.names, key)
    }

    /// 名前解決に使った共有宣言表を返す。
    pub fn declarations(&self) -> (decls: &DeclarationTable<'p, 'a>)
        ensures *decls == self.declarations_model(),
    {
        &self.declarations
    }

    /// 名前解決に使った共有宣言表を表す。
    pub closed spec fn declarations_model(&self) -> DeclarationTable<'p, 'a> {
        self.declarations
    }
}

/// 共有宣言表を作り、各名前空間の公開指定を適用する。同じ宣言への指定は一件にまとめる。
///
/// # Errors
///
/// 宣言の衝突があればその診断を返す。公開先の独立宣言が同じ名前空間にない場合は、指定された名前の範囲を返す。
pub fn index_exports<'p, 'a>(
    project: &'p CircuitProject<'a>,
) -> (result: Result<ExportTable<'p, 'a>, ExportError<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures
        result.is_ok() <==> !project_names_conflict(project) && project_exports_valid(project),
        match result {
            Ok(table) => export_table_matches(project, table) && table.declarations_model().well_formed(),
            Err(error) => export_error_evidence(project, error),
        },
{
    let declarations = match index_declarations(project) {
        Ok(table) => table,
        Err(error) => return Err(ExportError::Conflict(error)),
    };
    let sites = read_exports(project);
    let mut names = Vec::new();
    let mut index = 0;
    while index < sites.len()
        invariant
            index <= sites@.len(),
            !project_names_conflict(project),
            declaration_table_matches(project, declarations),
            declarations.well_formed(),
            sites_before(project, sites@, project.circuits_model().len() as int, 0, 0),
            forall|i: int| 0 <= i < index ==> #[trigger] published(names@, sites@[i].key),
            forall|i: int| 0 <= i < index ==> #[trigger] project_declares(project, sites@[i].key),
            forall|i: int| 0 <= i < names@.len() ==> #[trigger] indicated(project, names@[i])
                && project_declares(project, names@[i]),
            forall|i: int, j: int| 0 <= i < j < names@.len() ==>
                key_bytes(#[trigger] names@[i]) != key_bytes(#[trigger] names@[j]),
        decreases sites@.len() - index,
    {
        let site = &sites[index];
        proof {
            reveal(sites_before);
            assert(site_matches(project, *site));
            assert(indicated(project, site.key));
            declaration_lookup_agrees(project, &declarations, site.key);
        }
        if declarations.declaration(site.key).is_none() {
            assert(!project_exports_valid(project));
            proof { earlier_exports_resolve(project, sites@, index as int); }
            let span = site.span.start..site.span.end;
            return Err(ExportError::MissingDeclaration(LocatedName { source: site.source, span }));
        }
        assert(project_declares(project, site.key));
        let ghost previous = names@;
        if !is_published_in(&names, site.key) {
            names.push(site.key);
            assert(names@[previous.len() as int] == site.key);
        }
        assert forall|i: int| 0 <= i < names@.len() implies #[trigger] indicated(project, names@[i])
            && project_declares(project, names@[i]) by {
            if i < previous.len() {
                assert(names@[i] == previous[i]);
                assert(indicated(project, previous[i]));
            }
        };
        assert(published(names@, site.key));
        assert forall|i: int| 0 <= i < index + 1 implies #[trigger] published(names@, sites@[i].key) by {
            if i < index {
                assert(published(previous, sites@[i].key));
                let j = choose|j: int| 0 <= j < previous.len() && key_bytes(#[trigger] previous[j]) == key_bytes(sites@[i].key);
                assert(names@[j] == previous[j]);
            }
        };
        index += 1;
    }
    proof {
        publication_matches_requests(project, sites@, names@);
        assert forall|key: NameKey| #[trigger] indicated(project, key) implies project_declares(project, key) by {
            assert(published(names@, key));
            let i = choose|i: int| 0 <= i < names@.len() && key_bytes(#[trigger] names@[i]) == key_bytes(key);
            assert(published(names@, names@[i]));
            assert(indicated(project, names@[i]));
            assert(project_declares(project, names@[i]));
            key_views_agree(names@[i], key);
            declaration_key_equivalence(project, names@[i], key);
        };
    }
    Ok(ExportTable { declarations, names })
}

} // verus!
