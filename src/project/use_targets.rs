//! 厳格索引にある別名指定を読み取り、参照先を解決する。

use super::circuits::read_indexed_atom;
#[cfg(verus_only)]
use super::circuits::{parsed_index_evidence, parsed_name_span};
#[cfg(verus_only)]
use super::declarations::located_name_evidence;
use super::{
    AbsoluteResolutionError, AbsoluteTarget, CircuitProject, ExportError, ExportTable, LocatedName,
    ProjectSource, index_exports,
};
#[cfg(verus_only)]
use super::{
    absolute_resolution_evidence, export_error_evidence, export_table_matches, location_in_source,
    parsed_circuit_matches, declaration_table_matches, project_names_conflict,
};
use crate::syntax::circuit::{Head, NameSite, NamedBuildCircuit};
#[cfg(verus_only)]
use crate::syntax::circuit::{name_site_matches, use_entry_evidence};
#[cfg(verus_only)]
use crate::syntax::{AtomKind, bare_atom_kind, form_span};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 別名を指定した場所と、その引数の字句。
#[derive(Debug)]
pub struct UseSite<'p, 'a> {
    /// 別名を指定したファイル。
    pub source: &'p ProjectSource<'a>,
    /// 所属する名前空間ブロックの構文木上の添字。ファイルの直下では `None`。
    pub block: Option<usize>,
    /// 参照元の名前空間パス。可視性の判定に使う。
    pub namespace: Option<&'a str>,
    /// 対象の完全修飾名と範囲。
    pub reference: NameSite<'a>,
    /// 別名と範囲。
    pub alias: NameSite<'a>,
}

/// 別名を指定した場所と、完全修飾名が指す対象。
#[derive(Debug)]
pub struct ResolvedUse<'p, 'a> {
    /// 別名を指定した場所。
    pub site: UseSite<'p, 'a>,
    /// 解決した宣言または名前空間。
    pub target: AbsoluteTarget<'p, 'a, 'a>,
    pub(super) _file: usize,
    pub(super) _entry: usize,
}

impl<'p, 'a> ResolvedUse<'p, 'a> {
    /// 索引を借りずに返せる診断に、指定位置と参照先を写す。
    pub(super) fn copy_for_diagnostic(&self) -> (copy: Self)
        ensures copy == *self,
    {
        let site = &self.site;
        let target = match &self.target {
            AbsoluteTarget::Declaration { source, form } => AbsoluteTarget::Declaration { source, form },
            AbsoluteTarget::Namespace { key, introduced_at } => AbsoluteTarget::Namespace {
                key: *key,
                introduced_at: LocatedName {
                    source: introduced_at.source,
                    span: introduced_at.span.start..introduced_at.span.end,
                },
            },
        };
        let reference = NameSite { word: site.reference.word, span: site.reference.span.start..site.reference.span.end };
        let alias = NameSite { word: site.alias.word, span: site.alias.span.start..site.alias.span.end };
        let site = UseSite { source: site.source, block: site.block, namespace: site.namespace, reference, alias };
        Self { site, target, _file: self._file, _entry: self._entry }
    }
}

/// 参照先を解決した別名指定の一覧と、解決に使った公開表。
#[derive(Debug)]
pub struct UseTargets<'p, 'a> {
    project: &'p CircuitProject<'a>,
    exports: ExportTable<'p, 'a>,
    directives: Vec<ResolvedUse<'p, 'a>>,
}

/// 別名指定の参照先を解決できなかった理由。
#[derive(Debug)]
pub enum UseTargetError<'p, 'a> {
    /// 共有宣言表または公開表を作る際の診断。
    Export(ExportError<'p, 'a>),
    /// 完全修飾名が指す宣言や名前空間が見つからない。
    Missing(UseSite<'p, 'a>),
    /// 完全修飾名が指す宣言は別の名前空間にあり、公開されていない。
    Private {
        /// 別名を指定した場所と参照先の範囲。
        site: UseSite<'p, 'a>,
        /// 非公開の宣言の名前を指す範囲。
        declaration: LocatedName<'p, 'a>,
    },
}

spec fn is_use(project: &CircuitProject, file: int, index: int) -> bool {
    let circuits = project.circuits_model();
    &&& 0 <= file < circuits.len()
    &&& 0 <= index < circuits[file].syntax.entries@.len()
    &&& circuits[file].syntax.entries@[index].head is Use
}

spec fn before(file: int, index: int, stop_file: int, stop_index: int) -> bool {
    file < stop_file || (file == stop_file && index < stop_index)
}

spec fn atom_site(source: &ProjectSource, site: NameSite) -> bool {
    &&& location_in_source(LocatedName { source, span: site.span })
    &&& site.word.spec_bytes() == source.text.spec_bytes()[site.span.start as int..site.span.end as int]
}

spec fn indexed_site(source: &ProjectSource, parsed: &NamedBuildCircuit, index: int, site: UseSite) -> bool {
    &&& 0 <= index < parsed.syntax.entries@.len()
    &&& {
        let item = parsed.syntax.entries@[index];
        let forms = parsed.syntax.forms@;
        &&& item.head is Use
        &&& item.form + 3 < forms.len()
        &&& *site.source == *source && site.block == item.namespace
        &&& atom_site(source, site.reference)
        &&& atom_site(source, site.alias)
        &&& site.reference.span == form_span(forms[item.form + 2])
        &&& site.alias.span == form_span(forms[item.form + 3])
        &&& bare_atom_kind(site.reference.word.spec_bytes()) == Some(AtomKind::AbsolutePath)
        &&& bare_atom_kind(site.alias.word.spec_bytes()) == Some(AtomKind::Name)
        &&& match (item.namespace, site.namespace) {
            (None, None) => true,
            (Some(parent), Some(path)) => {
                &&& parent + 2 < forms.len()
                &&& {
                    let span = form_span(forms[parent + 2]);
                    &&& path.spec_bytes() == source.text.spec_bytes()[span.start as int..span.end as int]
                }
            },
            _ => false,
        }
    }
}

spec fn site_at(project: &CircuitProject, file: int, index: int, site: UseSite) -> bool {
    &&& is_use(project, file, index)
    &&& file < project.sources_model().len()
    &&& indexed_site(&project.sources_model()[file], &project.circuits_model()[file], index, site)
}

spec fn resolved_at(project: &CircuitProject, exports: &ExportTable, item: ResolvedUse) -> bool {
    &&& site_at(project, item._file as int, item._entry as int, item.site)
    &&& absolute_resolution_evidence(exports, item.site.reference.word, item.site.namespace, Ok(item.target))
}

#[verifier::opaque]
spec fn resolved_before(
    project: &CircuitProject, exports: &ExportTable, items: Seq<ResolvedUse>, stop_file: int, stop_index: int,
) -> bool {
    &&& forall|j: int| 0 <= j < items.len() ==> {
        let item = #[trigger] items[j];
        resolved_at(project, exports, item)
            && before(item._file as int, item._entry as int, stop_file, stop_index)
    }
    &&& forall|file: int, index: int| #[trigger] is_use(project, file, index) && before(file, index, stop_file, stop_index)
        ==> exists|j: int| 0 <= j < items.len() && (#[trigger] items[j])._file == file && items[j]._entry == index
    &&& forall|i: int, j: int| 0 <= i < j < items.len() ==> {
        let left = #[trigger] items[i];
        let right = #[trigger] items[j];
        before(left._file as int, left._entry as int, right._file as int, right._entry as int)
    }
}

proof fn record_use(
    project: &CircuitProject, exports: &ExportTable, items: Seq<ResolvedUse>,
    file: int, index: int, picked: Option<ResolvedUse>,
)
    requires
        resolved_before(project, exports, items, file, index),
        match picked {
            Some(item) => resolved_at(project, exports, item) && item._file == file && item._entry == index,
            None => !is_use(project, file, index),
        },
    ensures
        resolved_before(project, exports,
            if let Some(item) = picked { items.push(item) } else { items }, file, index + 1),
{
    reveal(resolved_before);
    let next = if let Some(item) = picked { items.push(item) } else { items };
    assert forall|f: int, i: int| #[trigger] is_use(project, f, i) && before(f, i, file, index + 1)
        implies exists|j: int| 0 <= j < next.len()
            && (#[trigger] next[j])._file == f && next[j]._entry == i by {
        if before(f, i, file, index) {
            let j = choose|j: int| 0 <= j < items.len() && (#[trigger] items[j])._file == f && items[j]._entry == i;
            assert(next[j] == items[j]);
        } else {
            assert(f == file && i == index);
            assert(picked is Some);
            assert(next[items.len() as int] == picked->Some_0);
        }
    };
}

proof fn finish_file(
    project: &CircuitProject, exports: &ExportTable, items: Seq<ResolvedUse>, file: int, index: int,
)
    requires
        0 <= file < project.circuits_model().len(),
        index == project.circuits_model()[file].syntax.entries@.len(),
        resolved_before(project, exports, items, file, index),
    ensures resolved_before(project, exports, items, file + 1, 0),
{
    reveal(resolved_before);
    assert forall|f: int, i: int| #[trigger] is_use(project, f, i) && before(f, i, file + 1, 0)
        implies before(f, i, file, index) by {};
}

fn read_use<'p, 'a>(
    source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit, index: usize,
) -> (site: UseSite<'p, 'a>)
    requires
        parsed_circuit_matches(*source, *parsed),
        index < parsed.syntax.entries@.len(),
        parsed.syntax.entries@[index as int].head is Use,
    ensures indexed_site(source, parsed, index as int, site),
{
    let item = &parsed.syntax.entries[index];
    let forms = &parsed.syntax.forms;
    proof {
        parsed_index_evidence(*source, *parsed);
        use_entry_evidence(source.text, forms@, parsed.syntax.entries@, index as int);
    }
    let _length = forms.len();
    assert(item.form + 3 < _length);
    let (reference_word, reference_span) = read_indexed_atom(source.text, forms, item.form + 2);
    let (alias_word, alias_span) = read_indexed_atom(source.text, forms, item.form + 3);
    let namespace = if let Some(parent) = item.namespace {
        assert(parent + 2 < _length);
        Some(read_indexed_atom(source.text, forms, parent + 2).0)
    } else {
        None
    };
    let reference = NameSite { word: reference_word, span: reference_span };
    let alias = NameSite { word: alias_word, span: alias_span };
    proof {
        located_name_evidence(LocatedName { source, span: reference.span });
        located_name_evidence(LocatedName { source, span: alias.span });
    }
    UseSite { source, block: item.namespace, namespace, reference, alias }
}

/// 解決結果が、厳格索引の全 `use` と出現順に対応することを表す。
pub closed spec fn use_targets_match(project: &CircuitProject, targets: UseTargets) -> bool {
    *targets.project == *project
        && export_table_matches(project, targets.exports)
        && resolved_before(project, &targets.exports, targets.directives@, project.circuits_model().len() as int, 0)
}

pub(super) proof fn resolved_use_evidence(
    targets: &UseTargets, index: int, namespace: Option<&str>,
)
    requires
        targets.covers_project(),
        0 <= index < targets.directives_model().len(),
        ({
            let item = targets.directives_model()[index];
            let circuits = targets.project_model().circuits_model();
            &&& item._file < circuits.len()
            &&& match (item.site.block, namespace) {
                (None, None) => true,
                (Some(form), Some(path)) => {
                    let names = circuits[item._file as int].names@;
                    exists|i: int| 0 <= i < names.len() && (#[trigger] names[i]).form == form
                        && names[i].name.word == path
                },
                _ => false,
            }
        }),
    ensures
        ({
            let item = targets.directives_model()[index];
            let from = item.site.namespace;
            (match (namespace, from) {
                (None, None) => true,
                (Some(left), Some(right)) => left.spec_bytes() == right.spec_bytes(),
                _ => false,
            }) && absolute_resolution_evidence(&targets.exports_model(),
                item.site.reference.word, from, Ok(item.target))
        }),
{
    let item = targets.directives@[index];
    let file = item._file as int;
    let project = targets.project;
    reveal(resolved_before);
    assert(resolved_at(project, &targets.exports, item));
    if let Some(form) = item.site.block {
        let parsed = project.circuits_model()[file];
        let source = project.sources_model()[file];
        let names = parsed.names@;
        let path = namespace->Some_0;
        let i = choose|i: int| 0 <= i < names.len() && (#[trigger] names[i]).form == form
            && names[i].name.word == path;
        parsed_name_span(source, parsed, i);
        reveal(name_site_matches);
    }
}

spec fn rejection(
    project: &CircuitProject, site: UseSite, error: AbsoluteResolutionError,
) -> bool {
    exists|file: int, index: int, exports: &ExportTable, prefix: Seq<ResolvedUse>|
        #![trigger site_at(project, file, index, site), resolved_before(project, exports, prefix, file, index)]
        site_at(project, file, index, site)
        && export_table_matches(project, *exports)
        && resolved_before(project, exports, prefix, file, index)
        && absolute_resolution_evidence(exports, site.reference.word, site.namespace, Err(error))
}

/// 診断が、公開表の作成または最初に解決できなかった参照先に対応することを表す。
pub closed spec fn use_target_error_evidence(project: &CircuitProject, error: UseTargetError) -> bool {
    match error {
        UseTargetError::Export(error) => export_error_evidence(project, error),
        UseTargetError::Missing(site) => rejection(project, site, AbsoluteResolutionError::Missing),
        UseTargetError::Private { site, declaration } =>
            rejection(project, site, AbsoluteResolutionError::Private(declaration)),
    }
}

impl<'p, 'a> UseTargets<'p, 'a> {
    /// 参照位置の特定に使う構文済みプロジェクトを返す。
    pub(super) fn project(&self) -> (project: &'p CircuitProject<'a>)
        ensures *project == self.project_model(),
            self.covers_project() ==> project.has_parsed_sources(),
    {
        self.project
    }

    pub(super) closed spec fn project_model(&self) -> CircuitProject<'a> {
        *self.project
    }

    /// 全 `use` が、構文済みプロジェクトにある指定と対応することを表す。
    pub closed spec fn covers_project(&self) -> bool {
        self.project.has_parsed_sources() && use_targets_match(self.project, *self)
    }

    pub(super) proof fn declarations_cover_project(&self)
        requires self.covers_project(),
        ensures declaration_table_matches(&self.project_model(), self.exports_model().declarations_model()),
            !project_names_conflict(&self.project_model()),
    {
        super::exports::exports_use_project_declarations(self.project, self.exports);
    }

    /// 解決に使った公開表を返す。
    pub fn exports(&self) -> (exports: &ExportTable<'p, 'a>)
        ensures *exports == self.exports_model(),
    {
        &self.exports
    }

    /// 解決に使った公開表を表す。
    pub closed spec fn exports_model(&self) -> ExportTable<'p, 'a> {
        self.exports
    }

    /// 解決済みの別名指定を出現順に返す。
    ///
    /// 同じ別名を指定した箇所も、後続の衝突検査と警告のために保持する。
    pub fn directives(&self) -> (directives: &[ResolvedUse<'p, 'a>])
        ensures directives@ == self.directives_model(),
    {
        self.directives.as_slice()
    }

    /// 解決済みの別名指定の列を表す。
    pub closed spec fn directives_model(&self) -> Seq<ResolvedUse<'p, 'a>> {
        self.directives@
    }
}

/// 宣言と公開を検査し、各 `use` の参照先を出現順に解決する。
///
/// # Errors
///
/// 宣言や公開指定の違反に続いて、最初に解決できなかった参照先の診断を返す。
/// 非公開の場合は、対応する宣言の名前を関連範囲として返す。
pub fn index_use_targets<'p, 'a>(
    project: &'p CircuitProject<'a>,
) -> (result: Result<UseTargets<'p, 'a>, UseTargetError<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures
        match result {
            Ok(targets) => use_targets_match(project, targets)
                && targets.exports_model().declarations_model().well_formed()
                && targets.covers_project(),
            Err(error) => use_target_error_evidence(project, error),
        },
{
    let exports = match index_exports(project) {
        Ok(exports) => exports,
        Err(error) => return Err(UseTargetError::Export(error)),
    };
    let sources = project.sources();
    let circuits = project.circuits();
    let mut directives: Vec<ResolvedUse> = Vec::new();
    let mut file = 0;
    let mut index = 0;
    assert(resolved_before(project, &exports, directives@, 0, 0)) by { reveal(resolved_before); }
    while file < circuits.len()
        invariant
            project.has_parsed_sources(),
            export_table_matches(project, exports),
            exports.declarations_model().well_formed(),
            sources@ == project.sources_model(),
            circuits@ == project.circuits_model(),
            file <= circuits@.len(),
            file < circuits@.len() ==> index <= circuits@[file as int].syntax.entries@.len(),
            file == circuits@.len() ==> index == 0,
            resolved_before(project, &exports, directives@, file as int, index as int),
        decreases circuits@.len() - file,
            if file < circuits@.len() { circuits@[file as int].syntax.entries@.len() - index } else { 0 },
    {
        let parsed = &circuits[file];
        if index == parsed.syntax.entries.len() {
            proof { finish_file(project, &exports, directives@, file as int, index as int); }
            file += 1;
            index = 0;
            continue;
        }
        if matches!(parsed.syntax.entries[index].head, Head::Use) {
            let site = read_use(&sources[file], parsed, index);
            assert(site_at(project, file as int, index as int, site));
            let target = match exports.resolve_absolute(site.reference.word, site.namespace) {
                Ok(target) => target,
                Err(AbsoluteResolutionError::Missing) => {
                    assert(rejection(project, site, AbsoluteResolutionError::Missing));
                    return Err(UseTargetError::Missing(site));
                }
                Err(AbsoluteResolutionError::Private(declaration)) => {
                    assert(rejection(project, site, AbsoluteResolutionError::Private(declaration)));
                    return Err(UseTargetError::Private { site, declaration });
                }
                Err(AbsoluteResolutionError::InvalidPath) => {
                    proof { assert(false); }
                    unreachable!();
                }
            };
            let item = ResolvedUse { site, target, _file: file, _entry: index };
            proof { record_use(project, &exports, directives@, file as int, index as int, Some(item)); }
            directives.push(item);
        } else {
            proof { record_use(project, &exports, directives@, file as int, index as int, None); }
        }
        index += 1;
    }
    Ok(UseTargets { project, exports, directives })
}

} // verus!
