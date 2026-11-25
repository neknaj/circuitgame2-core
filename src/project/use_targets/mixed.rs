//! 両言語の別名指定を読み、指定元の名前空間から参照先を解決する。

use super::{UseSite, UseTargetError, read_use};
#[cfg(verus_only)]
use super::{atom_site, before, indexed_site};
use crate::ncg2m::file::MetaItemKind;
#[cfg(verus_only)]
use crate::ncg2m::file::{meta_binding_span_evidence, meta_use_span_evidence};
use crate::project::{
    AbsoluteResolutionError, MixedAbsoluteTarget, MixedExportTable, ParsedProjectSources,
    ProjectSourceIndex, index_mixed_exports, read_source_span,
};
#[cfg(verus_only)]
use crate::project::{
    LocatedName, location_in_source, mixed_absolute_resolution_evidence, mixed_export_error_evidence, mixed_export_table_matches,
    declarations::located_name_evidence, source_indexes::{directive_entry_count, project_source_index_evidence},
};
use crate::project::source_indexes::count_directive_entries;
use crate::syntax::circuit::{Head, NameSite};
#[cfg(verus_only)]
use crate::syntax::{AtomKind, bare_atom_kind, form_span};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 混在プロジェクトで参照先を解決した別名指定。
#[derive(Debug)]
pub struct MixedResolvedUse<'p, 'a> {
    /// 指定元のファイル、所属ブロックと引数の位置。
    pub site: UseSite<'p, 'a>,
    /// 参照先の独立宣言または名前空間。
    pub target: MixedAbsoluteTarget<'p, 'a, 'a>,
    /// 正規化済みソースの初出順に付けたファイル添字。
    pub file: usize,
    /// 言語別の構文索引における指示フォームの添字。
    pub entry: usize,
}

/// 両言語を対象に、参照先を解決した別名指定の一覧。
#[derive(Debug)]
pub struct MixedUseTargets<'p, 'a> {
    project: &'p ParsedProjectSources<'a>,
    exports: MixedExportTable<'p, 'a>,
    directives: Vec<MixedResolvedUse<'p, 'a>>,
}

/// 言語別の構文索引で指定した添字が別名指定を指すことを表す。
pub closed spec fn indexed_mixed_use_at(project: &ParsedProjectSources, file: int, entry: int) -> bool {
    let indexes = project.indexes_model();
    &&& 0 <= file < indexes.len()
    &&& 0 <= entry < directive_entry_count(indexes[file])
    &&& match indexes[file] {
        ProjectSourceIndex::Circuit(parsed) => parsed.syntax.entries@[entry].head is Use,
        ProjectSourceIndex::Functional(items) => items@[entry].kind is Use,
    }
}

/// 別名指定の範囲、字句と所属ブロックが、言語別の構文索引に対応することを表す。
pub closed spec fn mixed_use_site_at(project: &ParsedProjectSources, file: int, entry: int, site: UseSite) -> bool {
    &&& indexed_mixed_use_at(project, file, entry)
    &&& *site.source == project.sources_model()[file]
    &&& bare_atom_kind(site.reference.word.spec_bytes()) == Some(AtomKind::AbsolutePath)
    &&& bare_atom_kind(site.alias.word.spec_bytes()) == Some(AtomKind::Name)
    &&& match project.indexes_model()[file] {
        ProjectSourceIndex::Circuit(parsed) => indexed_site(site.source, &parsed, entry, site),
        ProjectSourceIndex::Functional(items) => {
            let item = items@[entry];
            &&& site.reference.span == item.kind->Use_target
            &&& site.alias.span == item.kind->Use_alias
            &&& atom_site(site.source, site.reference)
            &&& atom_site(site.source, site.alias)
            &&& match (item.namespace, site.namespace, site.block) {
                (None, None, None) => true,
                (Some(span), Some(path), Some(block)) => block == span.start && path.spec_bytes()
                    == site.source.text.spec_bytes()[span.start as int..span.end as int],
                _ => false,
            }
        },
    }
}

fn read_site<'p, 'a>(project: &'p ParsedProjectSources<'a>, file: usize, entry: usize)
    -> (site: Option<UseSite<'p, 'a>>)
    requires project.has_source_indexes(), file < project.indexes_model().len(),
        entry < directive_entry_count(project.indexes_model()[file as int]),
    ensures site.is_some() == indexed_mixed_use_at(project, file as int, entry as int),
        site matches Some(site) ==> mixed_use_site_at(project, file as int, entry as int, site),
{
    let source = &project.sources()[file];
    let index = &project.indexes()[file];
    proof { project_source_index_evidence(*source, *index); }
    match index {
        ProjectSourceIndex::Circuit(parsed) => {
            if !matches!(parsed.syntax.entries[entry].head, Head::Use) {
                return None;
            }
            let site = read_use(source, parsed, entry);
            proof { reveal(indexed_site); }
            Some(site)
        }
        ProjectSourceIndex::Functional(items) => {
            let item = &items[entry];
            let MetaItemKind::Use { target: target_span, alias: alias_span } = &item.kind else { return None };
            proof {
                meta_binding_span_evidence(source.text, items@, entry as int);
                meta_use_span_evidence(source.text, items@, entry as int);
            }
            let (namespace, block) = match &item.namespace {
                Some(path) => (Some(read_source_span(source.text, path.start, path.end)), Some(path.start)),
                None => (None, None),
            };
            let reference = NameSite {
                word: read_source_span(source.text, target_span.start, target_span.end),
                span: target_span.start..target_span.end,
            };
            let alias = NameSite {
                word: read_source_span(source.text, alias_span.start, alias_span.end),
                span: alias_span.start..alias_span.end,
            };
            proof {
                located_name_evidence(LocatedName { source, span: reference.span });
                located_name_evidence(LocatedName { source, span: alias.span });
            }
            Some(UseSite { source, block, namespace, reference, alias })
        }
    }
}

spec fn resolved_at(project: &ParsedProjectSources, exports: &MixedExportTable, item: MixedResolvedUse) -> bool {
    mixed_use_site_at(project, item.file as int, item.entry as int, item.site)
        && mixed_absolute_resolution_evidence(exports, item.site.reference.word, item.site.namespace, Ok(item.target))
}

#[verifier::opaque]
spec fn resolved_before(
    project: &ParsedProjectSources, exports: &MixedExportTable, items: Seq<MixedResolvedUse>,
    file: int, entry: int,
) -> bool {
    &&& forall|j: int| 0 <= j < items.len() ==> {
        let item = #[trigger] items[j];
        resolved_at(project, exports, item) && before(item.file as int, item.entry as int, file, entry)
    }
    &&& forall|f: int, e: int| #[trigger] indexed_mixed_use_at(project, f, e) && before(f, e, file, entry)
        ==> exists|j: int| 0 <= j < items.len() && (#[trigger] items[j]).file == f && items[j].entry == e
    &&& forall|i: int, j: int| 0 <= i < j < items.len() ==> {
        let first = #[trigger] items[i];
        let second = #[trigger] items[j];
        before(first.file as int, first.entry as int, second.file as int, second.entry as int)
    }
}

proof fn record_use(
    project: &ParsedProjectSources, exports: &MixedExportTable, items: Seq<MixedResolvedUse>,
    file: int, entry: int, picked: Option<MixedResolvedUse>,
)
    requires resolved_before(project, exports, items, file, entry),
        match picked {
            Some(item) => resolved_at(project, exports, item) && item.file == file && item.entry == entry,
            None => !indexed_mixed_use_at(project, file, entry),
        },
    ensures resolved_before(project, exports,
        if let Some(item) = picked { items.push(item) } else { items }, file, entry + 1),
{
    reveal(resolved_before);
    let next = if let Some(item) = picked { items.push(item) } else { items };
    assert forall|f: int, e: int| #[trigger] indexed_mixed_use_at(project, f, e) && before(f, e, file, entry + 1)
        implies exists|j: int| 0 <= j < next.len()
            && (#[trigger] next[j]).file == f && next[j].entry == e by {
        if before(f, e, file, entry) {
            let j = choose|j: int| 0 <= j < items.len() && (#[trigger] items[j]).file == f && items[j].entry == e;
            assert(next[j] == items[j]);
        } else {
            assert(f == file && e == entry);
            assert(picked is Some);
            assert(next[items.len() as int] == picked->Some_0);
        }
    };
}

proof fn finish_file(
    project: &ParsedProjectSources, exports: &MixedExportTable, items: Seq<MixedResolvedUse>,
    file: int, entry: int,
)
    requires entry == directive_entry_count(project.indexes_model()[file]),
        resolved_before(project, exports, items, file, entry),
    ensures resolved_before(project, exports, items, file + 1, 0),
{
    reveal(resolved_before);
    assert forall|f: int, e: int| #[trigger] indexed_mixed_use_at(project, f, e) && before(f, e, file + 1, 0)
        implies before(f, e, file, entry) by {};
}

/// 解決結果が、両言語の元の索引にある別名指定と順序どおりに対応することを表す。
pub closed spec fn mixed_use_targets_match(project: &ParsedProjectSources, targets: MixedUseTargets) -> bool {
    *targets.project == *project && project.has_source_indexes() && mixed_export_table_matches(project, targets.exports)
        && resolved_before(project, &targets.exports, targets.directives@, project.indexes_model().len() as int, 0)
}

spec fn first_rejection(
    project: &ParsedProjectSources, exports: &MixedExportTable, site: UseSite, error: AbsoluteResolutionError,
) -> bool {
    &&& mixed_export_table_matches(project, *exports)
    &&& mixed_absolute_resolution_evidence(exports, site.reference.word, site.namespace, Err(error))
    &&& exists|file: int, entry: int| #[trigger] mixed_use_site_at(project, file, entry, site)
        && forall|f: int, e: int| #[trigger] indexed_mixed_use_at(project, f, e) && before(f, e, file, entry)
            ==> exists|item: MixedResolvedUse| #[trigger] resolved_at(project, exports, item)
                && item.file == f && item.entry == e
}

proof fn rejection_from_prefix(
    project: &ParsedProjectSources, exports: &MixedExportTable, items: Seq<MixedResolvedUse>,
    file: int, entry: int, site: UseSite, error: AbsoluteResolutionError,
)
    requires mixed_export_table_matches(project, *exports), mixed_use_site_at(project, file, entry, site),
        mixed_absolute_resolution_evidence(exports, site.reference.word, site.namespace, Err(error)),
        resolved_before(project, exports, items, file, entry),
    ensures first_rejection(project, exports, site, error),
{
    reveal(resolved_before);
    assert forall|f: int, e: int| #[trigger] indexed_mixed_use_at(project, f, e) && before(f, e, file, entry)
        implies exists|item: MixedResolvedUse| #[trigger] resolved_at(project, exports, item)
            && item.file == f && item.entry == e by {
        let j = choose|j: int| 0 <= j < items.len() && (#[trigger] items[j]).file == f && items[j].entry == e;
        assert(resolved_at(project, exports, items[j]));
    };
}

/// 診断が公開表のエラー、または最初に解決できない別名指定に対応することを表す。
pub closed spec fn mixed_use_target_error_matches(project: &ParsedProjectSources, error: UseTargetError) -> bool {
    match error {
        UseTargetError::Export(error) => mixed_export_error_evidence(project, error),
        UseTargetError::Missing(site) => exists|exports: MixedExportTable|
            first_rejection(project, &exports, site, AbsoluteResolutionError::Missing),
        UseTargetError::Private { site, declaration } => exists|exports: MixedExportTable|
            first_rejection(project, &exports, site, AbsoluteResolutionError::Private(declaration)),
    }
}

impl<'p, 'a> MixedUseTargets<'p, 'a> {
    /// 別名を指定した解析済みプロジェクトを返す。
    pub fn project(&self) -> (project: &'p ParsedProjectSources<'a>)
        ensures *project == self.project_model(),
    {
        self.project
    }

    /// 別名の解決に使った解析済みプロジェクトを表す。
    pub closed spec fn project_model(&self) -> ParsedProjectSources<'a> {
        *self.project
    }

    /// 一覧の別名指定が、元ファイルの指示とその参照先に対応することを示す。
    pub proof fn directive_origin(&self, rank: int)
        requires mixed_use_targets_match(&self.project_model(), *self), 0 <= rank < self.directives_model().len(),
        ensures {
            let row = self.directives_model()[rank];
            &&& row.file < self.project_model().sources_model().len()
            &&& *row.site.source == self.project_model().sources_model()[row.file as int]
            &&& mixed_use_site_at(&self.project_model(), row.file as int, row.entry as int, row.site)
            &&& location_in_source(LocatedName { source: row.site.source, span: row.site.reference.span })
            &&& location_in_source(LocatedName { source: row.site.source, span: row.site.alias.span })
            &&& row.site.reference.word.spec_bytes() == row.site.source.text_model().spec_bytes()[
                row.site.reference.span.start as int..row.site.reference.span.end as int]
            &&& row.site.alias.word.spec_bytes() == row.site.source.text_model().spec_bytes()[
                row.site.alias.span.start as int..row.site.alias.span.end as int]
            &&& match self.project_model().indexes_model()[row.file as int] {
                ProjectSourceIndex::Circuit(parsed) => {
                    let entry = parsed.syntax.entries@[row.entry as int];
                    let forms = parsed.syntax.forms@;
                    &&& entry.head is Use
                    &&& row.site.block == entry.namespace
                    &&& row.site.reference.span == form_span(forms[entry.form + 2])
                    &&& row.site.alias.span == form_span(forms[entry.form + 3])
                    &&& match (entry.namespace, row.site.namespace) {
                        (None, None) => true,
                        (Some(root), Some(path)) => {
                            let span = form_span(forms[root + 2]);
                            path.spec_bytes() == row.site.source.text_model().spec_bytes()[span.start as int..span.end as int]
                        },
                        _ => false,
                    }
                },
                ProjectSourceIndex::Functional(items) => {
                    let item = items@[row.entry as int];
                    &&& item.kind is Use
                    &&& match (item.namespace, row.site.namespace, row.site.block) {
                        (None, None, None) => true,
                        (Some(span), Some(path), Some(block)) => block == span.start
                            && path.spec_bytes() == row.site.source.text_model().spec_bytes()[span.start as int..span.end as int],
                        _ => false,
                    }
                    &&& row.site.reference.span == item.kind->Use_target
                    &&& row.site.alias.span == item.kind->Use_alias
                },
            }
            &&& mixed_absolute_resolution_evidence(&self.exports_model(), row.site.reference.word, row.site.namespace,
                Ok(row.target))
        },
    {
        reveal(resolved_before);
        assert(resolved_at(self.project, &self.exports, self.directives@[rank]));
        reveal(indexed_site);
        reveal(atom_site);
        self.directives@[rank].site.source.text_model_is_text();
    }

    /// 構文索引上の別名指定に対応する行が、解決済み一覧に一件あることを示す。
    pub proof fn directive_rank(&self, file: int, entry: int) -> (rank: int)
        requires mixed_use_targets_match(&self.project_model(), *self),
            indexed_mixed_use_at(&self.project_model(), file, entry),
        ensures
            0 <= rank < self.directives_model().len(),
            self.directives_model()[rank].file == file && self.directives_model()[rank].entry == entry,
            forall|i: int| 0 <= i < self.directives_model().len()
                && (#[trigger] self.directives_model()[i]).file == file
                && self.directives_model()[i].entry == entry ==> i == rank,
    {
        reveal(resolved_before);
        let items = self.directives_model();
        let rank = choose|i: int| 0 <= i < items.len() && (#[trigger] items[i]).file == file && items[i].entry == entry;
        assert forall|i: int| 0 <= i < items.len() && (#[trigger] items[i]).file == file
            && items[i].entry == entry implies i == rank by {
            if i < rank { assert(before(file, entry, file, entry)); }
            if rank < i { assert(before(file, entry, file, entry)); }
        };
        rank
    }

    /// 別名指定を、ソースの初出順とファイル内の記述順で返す。
    pub fn directives(&self) -> (directives: &[MixedResolvedUse<'p, 'a>])
        ensures directives@ == self.directives_model(),
    {
        self.directives.as_slice()
    }

    /// 参照先を解決した別名指定を元の順序で表す。
    pub closed spec fn directives_model(&self) -> Seq<MixedResolvedUse<'p, 'a>> {
        self.directives@
    }

    /// 別名の参照先を解決した混在プロジェクトの公開表を返す。
    pub fn exports(&self) -> (exports: &MixedExportTable<'p, 'a>)
        ensures *exports == self.exports_model(),
    {
        &self.exports
    }

    /// 別名の参照先を解決した公開表を表す。
    pub closed spec fn exports_model(&self) -> MixedExportTable<'p, 'a> {
        self.exports
    }
}

/// 両言語の `use` が指定する完全修飾名を、各指示の所属名前空間から解決する。
///
/// 解決結果は所属ファイルとブロックの位置を保持する。別名同士や直接宣言との衝突は後段で検査する。
///
/// # Errors
///
/// 宣言の衝突と公開指定のエラーを先に検査する。別名の参照先が見つからないか非公開なら、
/// ソースの初出順とファイル内の記述順で最初の違反を返す。
///
/// # Examples
///
/// 名前空間の同じ名前を使った二つのブロックでも、別名を指定したブロックは区別できる。
///
/// ```
/// use circuitgame2_core::project::{SourceSnapshot, index_mixed_use_targets, parse_project_sources};
///
/// let sources = [
///     SourceSnapshot { path: "gates.ncg2", revision: 7,
///         text: "(namespace gates (struct Bit (width 1)) (export Bit))" },
///     SourceSnapshot { path: "consumer.ncg2m", revision: 9,
///         text: "(namespace app (use ::gates::Bit T)) (namespace app (use ::gates::Bit T))" },
/// ];
/// let project = parse_project_sources(&sources).unwrap();
/// let targets = index_mixed_use_targets(&project).unwrap();
/// let [first, second] = targets.directives() else { panic!() };
/// assert_eq!(first.site.namespace, Some("app"));
/// assert_eq!(first.site.namespace, second.site.namespace);
/// assert_ne!(first.site.block, second.site.block);
/// ```
pub fn index_mixed_use_targets<'p, 'a>(project: &'p ParsedProjectSources<'a>)
    -> (result: Result<MixedUseTargets<'p, 'a>, UseTargetError<'p, 'a>>)
    ensures match result {
        Ok(targets) => mixed_use_targets_match(project, targets),
        Err(error) => mixed_use_target_error_matches(project, error),
    },
{
    let exports = match index_mixed_exports(project) {
        Ok(table) => table,
        Err(error) => return Err(UseTargetError::Export(error)),
    };
    let indexes = project.indexes();
    let mut directives = Vec::new();
    let mut file = 0;
    assert(resolved_before(project, &exports, directives@, 0, 0)) by { reveal(resolved_before); }
    while file < indexes.len()
        invariant indexes@ == project.indexes_model(), project.has_source_indexes(), file <= indexes@.len(),
            mixed_export_table_matches(project, exports), resolved_before(project, &exports, directives@, file as int, 0),
        decreases indexes@.len() - file,
    {
        let entries = count_directive_entries(&indexes[file]);
        let mut entry = 0;
        while entry < entries
            invariant indexes@ == project.indexes_model(), project.has_source_indexes(),
                file < indexes@.len(), entry <= entries == directive_entry_count(indexes@[file as int]),
                mixed_export_table_matches(project, exports),
                resolved_before(project, &exports, directives@, file as int, entry as int),
            decreases entries - entry,
        {
            if let Some(site) = read_site(project, file, entry) {
                let target = match exports.resolve_absolute(site.reference.word, site.namespace) {
                    Ok(target) => target,
                    Err(error) => {
                        proof {
                            rejection_from_prefix(project, &exports, directives@, file as int, entry as int, site, error);
                        }
                        return Err(match error {
                            AbsoluteResolutionError::Missing => UseTargetError::Missing(site),
                            AbsoluteResolutionError::Private(declaration) => UseTargetError::Private { site, declaration },
                            AbsoluteResolutionError::InvalidPath => unreachable!(),
                        });
                    }
                };
                let item = MixedResolvedUse { site, target, file, entry };
                proof { record_use(project, &exports, directives@, file as int, entry as int, Some(item)); }
                directives.push(item);
            } else {
                proof { record_use(project, &exports, directives@, file as int, entry as int, None); }
            }
            entry += 1;
        }
        proof { finish_file(project, &exports, directives@, file as int, entry as int); }
        file += 1;
    }
    Ok(MixedUseTargets { project, exports, directives })
}

}
