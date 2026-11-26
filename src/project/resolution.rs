//! 完全修飾名を共有宣言表と公開表に照合する。

use super::declarations::key_of;
#[cfg(verus_only)]
use super::declarations::{
    declaration_key_evidence, declaration_location_evidence, declaration_sites_agree,
    declaration_table_matches, form_key, project_names_conflict, same_declaration_key,
};
#[cfg(verus_only)]
use super::{
    CircuitProject, ParsedProjectSources, location_in_source, mixed_declarations_agree,
    mixed_export_table_matches, exports::mixed_exports_use_project_declarations,
};
#[cfg(verus_only)]
use super::name_keys::key_view;
use super::{
    DeclarationTable, ExportTable, LocatedName, MixedExportTable, NameKey, ProjectDeclaration, ProjectSource,
};
#[cfg(verus_only)]
use crate::syntax::{AtomKind, absolute_path_parts, bare_atom_kind};
use crate::syntax::{circuit::NamedForm, split_absolute_path};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 完全修飾名が指す独立宣言または名前空間。
#[derive(Debug)]
pub enum AbsoluteTarget<'p, 'a, 'q> {
    /// 回路や型などの独立宣言。
    Declaration {
        /// 宣言が属するファイル。
        source: &'p ProjectSource<'a>,
        /// 宣言の名前とフォームの位置。
        form: &'p NamedForm<'a>,
    },
    /// 明示された名前空間またはパスの中間にある名前空間。
    Namespace {
        /// 名前空間を識別する完全修飾名の成分。
        key: NameKey<'q>,
        /// 名前空間を導入した箇所の一つ。
        introduced_at: LocatedName<'p, 'a>,
    },
}

/// 対象の種別と完全修飾名から、同じ共有宣言表での同一性を定める。
pub open spec fn same_target(left: AbsoluteTarget, right: AbsoluteTarget) -> bool {
    match (left, right) {
        (AbsoluteTarget::Declaration { form: left, .. }, AbsoluteTarget::Declaration { form: right, .. }) =>
            key_view(form_key(*left)) == key_view(form_key(*right)),
        (AbsoluteTarget::Namespace { key: left, .. }, AbsoluteTarget::Namespace { key: right, .. }) =>
            key_view(left) == key_view(right),
        _ => false,
    }
}

impl AbsoluteTarget<'_, '_, '_> {
    /// 同じ共有宣言表から得た二つの対象が、一つの宣言または名前空間を指すかを返す。
    pub fn is_same_target(&self, other: &AbsoluteTarget) -> (same: bool)
        ensures same == same_target(*self, *other),
    {
        match (self, other) {
            (Self::Declaration { form: left, .. }, AbsoluteTarget::Declaration { form: right, .. }) =>
                key_of(left).same_name(key_of(right)),
            (Self::Namespace { key: left, .. }, AbsoluteTarget::Namespace { key: right, .. }) =>
                left.same_name(*right),
            _ => false,
        }
    }
}

/// 完全修飾名を解決できなかった理由。
#[derive(Debug)]
pub enum AbsoluteResolutionError<'p, 'a> {
    /// 参照の綴りが完全修飾名の字句規則に従わない。
    InvalidPath,
    /// この名前を持つ宣言や名前空間が存在しない。
    Missing,
    /// 宣言が別の名前空間にあり、公開されていない。
    Private(LocatedName<'p, 'a>),
}

/// 指定したキーの候補と、参照元から独立宣言が見えるかを記録する。
///
/// 候補がない場合も観測値に含める。名前空間の場合は、最初に導入した箇所を保持する。
#[derive(Debug)]
pub struct AbsoluteLookup<'p, 'a, 'q> {
    target: Option<AbsoluteTarget<'p, 'a, 'q>>,
    visible: bool,
}

impl<'p, 'a, 'q> AbsoluteLookup<'p, 'a, 'q> {
    /// 宣言表で選んだ候補を表す。候補がなければ `None`。
    pub closed spec fn target_model(&self) -> Option<AbsoluteTarget<'p, 'a, 'q>> { self.target }

    /// 独立宣言が参照元から見えることを表す。名前空間と候補の不在では偽。
    pub closed spec fn visible_model(&self) -> bool { self.visible }

    /// 観測値から決まる解決結果と診断の範囲を表す。
    pub open spec fn resolution_model(&self) -> Result<AbsoluteTarget<'p, 'a, 'q>, AbsoluteResolutionError<'p, 'a>> {
        match self.target_model() {
            Some(target @ AbsoluteTarget::Declaration { source, form }) =>
                if self.visible_model() { Ok(target) }
                else { Err(AbsoluteResolutionError::Private(LocatedName { source, span: form.name.span })) },
            Some(target @ AbsoluteTarget::Namespace { .. }) => Ok(target),
            None => Err(AbsoluteResolutionError::Missing),
        }
    }

    /// 共有宣言表で選んだ候補を借りる。候補がなければ `None`。
    pub fn target(&self) -> (result: Option<&AbsoluteTarget<'p, 'a, 'q>>)
        ensures (match result { Some(target) => Some(*target), None => None }) == self.target_model(),
    {
        match &self.target {
            Some(target) => Some(target),
            None => None,
        }
    }

    /// 候補が独立宣言であり、参照元から見えることを返す。
    pub fn is_visible_declaration(&self) -> (result: bool)
        ensures result == self.visible_model(),
    {
        self.visible
    }

    /// 観測値から解決結果を返す。
    ///
    /// # Errors
    ///
    /// 候補がなければ不在を、見えない宣言なら宣言名の元範囲とともに非公開を返す。
    pub fn into_resolution(self) -> (result: Result<AbsoluteTarget<'p, 'a, 'q>, AbsoluteResolutionError<'p, 'a>>)
        ensures result == self.resolution_model(),
    {
        match self.target {
            Some(AbsoluteTarget::Declaration { source, form }) if !self.visible => {
                let span = &form.name.span;
                Err(AbsoluteResolutionError::Private(LocatedName { source, span: span.start..span.end }))
            },
            Some(target) => Ok(target),
            None => Err(AbsoluteResolutionError::Missing),
        }
    }
}

/// 宣言が参照元と同じ名前空間に属するか、公開されていることを表す。
pub open spec fn declaration_visible_from(table: &ExportTable, key: NameKey, from: Option<&str>) -> bool {
    key_view(key) == key_view(NameKey { parent: from, name: key.name })
        || table.publishes(key)
}

/// 共有宣言表にキーに対応する独立宣言があることを表す。
pub open spec fn declaration_exists(table: &DeclarationTable, key: NameKey) -> bool {
    exists|source: &ProjectSource, form: &NamedForm|
        #[trigger] table.declaration_at(key, source, form)
}

/// 指定した名前空間の直下で、キーに対応する宣言または名前空間の有無を表す。
pub open spec fn direct_target_matches(
    table: &DeclarationTable, key: NameKey, result: Option<AbsoluteTarget>,
) -> bool {
    match result {
        Some(AbsoluteTarget::Declaration { source, form }) =>
            table.declaration_at(key, source, form)
                && location_in_source(LocatedName { source, span: form.name.span }),
        Some(AbsoluteTarget::Namespace { key: observed, introduced_at }) =>
            observed == key && !declaration_exists(table, key)
                && table.namespace_at(key, introduced_at) && location_in_source(introduced_at),
        None => !declaration_exists(table, key)
            && (forall|location: LocatedName| !#[trigger] table.namespace_at(key, location)),
    }
}

pub(super) proof fn direct_targets_agree(
    table: &DeclarationTable, key: NameKey, left: Option<AbsoluteTarget>, right: Option<AbsoluteTarget>,
)
    requires direct_target_matches(table, key, left), direct_target_matches(table, key, right),
    ensures match (left, right) {
        (Some(left), Some(right)) => same_target(left, right),
        (None, None) => true,
        _ => false,
    },
{
    if let Some(AbsoluteTarget::Declaration { source, form }) = left {
        declaration_key_evidence(table, key, source, form);
        assert(declaration_exists(table, key));
    }
    if let Some(AbsoluteTarget::Declaration { source, form }) = right {
        declaration_key_evidence(table, key, source, form);
        assert(declaration_exists(table, key));
    }
}

/// 直接束縛の結果と、子名前空間を最初に導入した箇所との対応を表す。
pub open spec fn selected_direct_target_matches(
    table: &DeclarationTable, key: NameKey, result: Option<AbsoluteTarget>,
) -> bool {
    &&& direct_target_matches(table, key, result)
    &&& result matches Some(AbsoluteTarget::Namespace { introduced_at, .. }) ==>
        table.first_namespace_at(key, introduced_at)
}

/// 衝突のない宣言表では、直接束縛の対象と出現位置が一意に定まる。
pub(super) proof fn selected_direct_targets_agree(
    project: &CircuitProject, table: &DeclarationTable, key: NameKey,
    left: Option<AbsoluteTarget>, right: Option<AbsoluteTarget>,
)
    requires
        declaration_table_matches(project, *table),
        !project_names_conflict(project),
        selected_direct_target_matches(table, key, left),
        selected_direct_target_matches(table, key, right),
    ensures left == right,
{
    direct_targets_agree(table, key, left, right);
    match (left, right) {
        (
            Some(AbsoluteTarget::Declaration { source: a, form: b }),
            Some(AbsoluteTarget::Declaration { source: c, form: d }),
        ) => declaration_sites_agree(project, table, key, a, b, c, d),
        (
            Some(AbsoluteTarget::Namespace { introduced_at: a, .. }),
            Some(AbsoluteTarget::Namespace { introduced_at: b, .. }),
        ) => table.first_namespace_sites_agree(key, a, b),
        _ => {},
    }
}

impl<'p, 'a> DeclarationTable<'p, 'a> {
    /// 名前空間の直下にある独立宣言または子名前空間を、指定した名前で探す。
    ///
    /// 中間の名前空間も対象に含める。子名前空間を導入した箇所が複数あれば、最初の箇所を返す。
    pub fn direct_target<'q>(&self, key: NameKey<'q>) -> (result: Option<AbsoluteTarget<'p, 'a, 'q>>)
        requires self.well_formed(),
        ensures
            direct_target_matches(self, key, result),
            selected_direct_target_matches(self, key, result),
    {
        if let Some((source, form)) = self.declaration(key) {
            proof { declaration_location_evidence(self, key, source, form); }
            Some(AbsoluteTarget::Declaration { source, form })
        } else if let Some(introduced_at) = self.namespace(key) {
            Some(AbsoluteTarget::Namespace { key, introduced_at })
        } else {
            None
        }
    }
}

/// 完全修飾名の成分と参照元に対して、解決結果または診断の根拠を定める。
pub open spec fn has_resolution(
    table: &ExportTable, key: NameKey, from: Option<&str>,
    result: Result<AbsoluteTarget, AbsoluteResolutionError>,
) -> bool {
    let declarations = table.declarations_model();
    match result {
        Ok(target @ AbsoluteTarget::Declaration { .. }) =>
            direct_target_matches(&declarations, key, Some(target)) && declaration_visible_from(table, key, from),
        Ok(target @ AbsoluteTarget::Namespace { .. }) =>
            selected_direct_target_matches(&declarations, key, Some(target)),
        Err(AbsoluteResolutionError::Private(location)) =>
            !declaration_visible_from(table, key, from) && location_in_source(location)
                && (exists|form: &NamedForm| #[trigger] declarations.declaration_at(key, location.source, form)
                    && location.span == form.name.span),
        Err(AbsoluteResolutionError::Missing) => direct_target_matches(&declarations, key, None),
        Err(AbsoluteResolutionError::InvalidPath) => false,
    }
}

spec fn resolved_candidate<'p, 'a, 'q>(
    table: &ExportTable<'p, 'a>, key: NameKey<'q>, from: Option<&str>,
    candidate: Option<AbsoluteTarget<'p, 'a, 'q>>,
) -> Result<AbsoluteTarget<'p, 'a, 'q>, AbsoluteResolutionError<'p, 'a>> {
    match candidate {
        Some(target @ AbsoluteTarget::Declaration { source, form }) =>
            if declaration_visible_from(table, key, from) { Ok(target) }
            else { Err(AbsoluteResolutionError::Private(LocatedName { source, span: form.name.span })) },
        Some(target @ AbsoluteTarget::Namespace { .. }) => Ok(target),
        None => Err(AbsoluteResolutionError::Missing),
    }
}

proof fn recover_resolution_candidate<'p, 'a, 'q>(
    table: &ExportTable<'p, 'a>, key: NameKey<'q>, from: Option<&str>,
    result: Result<AbsoluteTarget<'p, 'a, 'q>, AbsoluteResolutionError<'p, 'a>>,
) -> (candidate: Option<AbsoluteTarget<'p, 'a, 'q>>)
    requires has_resolution(table, key, from, result),
    ensures selected_direct_target_matches(&table.declarations_model(), key, candidate),
        result == resolved_candidate(table, key, from, candidate),
{
    match result {
        Ok(target) => Some(target),
        Err(AbsoluteResolutionError::Private(location)) => {
            let declarations = &table.declarations_model();
            let form = choose|form: &'p NamedForm<'a>|
                #[trigger] declarations.declaration_at(key, location.source, form)
                && location.span == form.name.span;
            Some(AbsoluteTarget::Declaration { source: location.source, form })
        },
        Err(AbsoluteResolutionError::Missing) => None,
        Err(AbsoluteResolutionError::InvalidPath) => { assert(false); None },
    }
}

// 完全修飾キーは文字列の内容で照合する。名前空間の候補だけキーを付け替える。
proof fn transfer_selected_candidate<'p, 'a, 'q>(
    table: &DeclarationTable<'p, 'a>, from: NameKey, to: NameKey<'q>, candidate: Option<AbsoluteTarget<'p, 'a, '_>>,
) -> (out: Option<AbsoluteTarget<'p, 'a, 'q>>)
    requires key_view(from) == key_view(to), selected_direct_target_matches(table, from, candidate),
    ensures selected_direct_target_matches(table, to, out),
        out == match candidate {
            Some(AbsoluteTarget::Namespace { introduced_at, .. }) =>
                Some(AbsoluteTarget::Namespace { key: to, introduced_at }),
            Some(AbsoluteTarget::Declaration { source, form }) => Some(AbsoluteTarget::Declaration { source, form }),
            None => None,
        },
{
    match candidate {
        Some(AbsoluteTarget::Declaration { source, form }) => {
            same_declaration_key(table, from, to, source, form);
            Some(AbsoluteTarget::Declaration { source, form })
        },
        _ => {
            if declaration_exists(table, to) {
                let (source, form) = choose|source: &ProjectSource, form: &NamedForm|
                    #[trigger] table.declaration_at(to, source, form);
                same_declaration_key(table, to, from, source, form);
                assert(declaration_exists(table, from));
            }
            match candidate {
                Some(AbsoluteTarget::Namespace { introduced_at, .. }) => {
                    table.same_namespace_key(from, to, introduced_at);
                    table.same_first_namespace_key(from, to, introduced_at);
                    Some(AbsoluteTarget::Namespace { key: to, introduced_at })
                },
                _ => {
                    assert forall|location: LocatedName| !#[trigger] table.namespace_at(to, location) by {
                        if table.namespace_at(to, location) {
                            table.same_namespace_key(to, from, location);
                        }
                    };
                    None
                },
            }
        },
    }
}

// 候補の不在、非公開、最初の名前空間位置まで、同じキーで同じ解決結果を得る。
pub(super) proof fn key_resolutions_agree(
    project: &CircuitProject, table: &ExportTable, left_key: NameKey, right_key: NameKey, from: Option<&str>,
    left: Result<AbsoluteTarget, AbsoluteResolutionError>, right: Result<AbsoluteTarget, AbsoluteResolutionError>,
)
    requires
        declaration_table_matches(project, table.declarations_model()), !project_names_conflict(project),
        key_view(left_key) == key_view(right_key),
        has_resolution(table, left_key, from, left), has_resolution(table, right_key, from, right),
    ensures left == right || (left matches Ok(AbsoluteTarget::Namespace { introduced_at: a, .. })
        && right matches Ok(AbsoluteTarget::Namespace { introduced_at: b, .. }) && a == b),
{
    let declarations = &table.declarations_model();
    let a = recover_resolution_candidate(table, left_key, from, left);
    let b = recover_resolution_candidate(table, right_key, from, right);
    let moved = transfer_selected_candidate(declarations, right_key, left_key, b);
    selected_direct_targets_agree(project, declarations, left_key, a, moved);
    table.same_publication_key(left_key, right_key);
}

/// 完全修飾名の解決結果を、字句規則、共有宣言表、公開表に結び付ける。
pub open spec fn absolute_resolution_evidence(
    table: &ExportTable, path: &str, from: Option<&str>,
    result: Result<AbsoluteTarget, AbsoluteResolutionError>,
) -> bool {
    if result matches Err(AbsoluteResolutionError::InvalidPath) {
        bare_atom_kind(path.spec_bytes()) != Some(AtomKind::AbsolutePath)
    } else {
        exists|key: NameKey| #[trigger] absolute_path_parts(path, key.parent, key.name)
            && has_resolution(table, key, from, result)
    }
}

pub(super) proof fn absolute_declaration_evidence(
    table: &ExportTable, path: &str, from: Option<&str>, source: &ProjectSource, form: &NamedForm,
)
    requires absolute_resolution_evidence(table, path, from, Ok(AbsoluteTarget::Declaration { source, form })),
    ensures table.declarations_model().declaration_at(form_key(*form), source, form),
{
    let target = Ok(AbsoluteTarget::Declaration { source, form });
    let key = choose|key: NameKey| #[trigger] absolute_path_parts(path, key.parent, key.name)
        && has_resolution(table, key, from, target);
    declaration_key_evidence(&table.declarations_model(), key, source, form);
}

impl<'p, 'a> ExportTable<'p, 'a> {
    /// 参照元の名前空間から、完全修飾名が指す宣言または名前空間を解決する。
    ///
    /// `from` は参照元の名前空間パスを先頭の `::` を除いた形で渡す。ルート直下は `None` で表す。
    /// 参照元と異なる名前空間の宣言には公開指定が必要である。名前空間のパスは参照元を問わず解決できる。
    ///
    /// # Errors
    ///
    /// 不正な綴り、対象の欠落、非公開の宣言を区別する。
    /// 非公開の場合は宣言の名前を指す元ソース上の範囲を返す。
    pub fn resolve_absolute<'q>(&self, path: &'q str, from: Option<&str>)
        -> (result: Result<AbsoluteTarget<'p, 'a, 'q>, AbsoluteResolutionError<'p, 'a>>)
        requires self.declarations_model().well_formed(),
        ensures absolute_resolution_evidence(self, path, from, result),
    {
        let Some((parent, name)) = split_absolute_path(path) else {
            return Err(AbsoluteResolutionError::InvalidPath);
        };
        let key = NameKey { parent, name };
        assert(absolute_path_parts(path, key.parent, key.name));
        self.resolve_key(key, from)
    }

    /// 一つのキーについて、候補の有無と参照元からの可視性を観測する。
    ///
    /// `from` は先頭の `::` を除いた参照元の名前空間で、ルート直下では `None`。
    pub fn observe_absolute_key<'q>(&self, key: NameKey<'q>, from: Option<&str>)
        -> (lookup: AbsoluteLookup<'p, 'a, 'q>)
        requires self.declarations_model().well_formed(),
        ensures
            selected_direct_target_matches(&self.declarations_model(), key, lookup.target_model()),
            lookup.visible_model() == (lookup.target_model() matches Some(AbsoluteTarget::Declaration { .. })
                && declaration_visible_from(self, key, from)),
            has_resolution(self, key, from, lookup.resolution_model()),
    {
        let target = self.declarations().direct_target(key);
        let visible = matches!(target, Some(AbsoluteTarget::Declaration { .. }))
            && (key.same_name(NameKey { parent: from, name: key.name }) || self.is_public(key));
        proof {
            if let Some(AbsoluteTarget::Declaration { source, form }) = target {
                if !visible {
                    let location = LocatedName { source, span: form.name.span };
                    assert(exists|candidate: &NamedForm|
                        #[trigger] self.declarations_model().declaration_at(key, location.source, candidate)
                            && location.span == candidate.name.span);
                }
            }
        }
        AbsoluteLookup { target, visible }
    }

    /// 宣言表のキーを解決し、参照元から末尾の宣言が見えることを確かめる。
    pub(super) fn resolve_key<'q>(&self, key: NameKey<'q>, from: Option<&str>)
        -> (result: Result<AbsoluteTarget<'p, 'a, 'q>, AbsoluteResolutionError<'p, 'a>>)
        requires self.declarations_model().well_formed(),
        ensures has_resolution(self, key, from, result),
            exists|lookup: AbsoluteLookup<'p, 'a, 'q>|
                #[trigger] lookup.resolution_model() == result
                && selected_direct_target_matches(&self.declarations_model(), key, lookup.target_model())
                && lookup.visible_model() == (lookup.target_model() matches Some(AbsoluteTarget::Declaration { .. })
                    && declaration_visible_from(self, key, from)),
    {
        let lookup = self.observe_absolute_key(key, from);
        let ghost observed = lookup;
        let result = lookup.into_resolution();
        assert(observed.resolution_model() == result);
        result
    }
}



/// 混在プロジェクトの完全修飾名が指す対象。
#[derive(Debug)]
pub enum MixedAbsoluteTarget<'p, 'a, 'q> {
    /// 回路または NCG2M の独立宣言。
    Declaration(ProjectDeclaration<'p, 'a>),
    /// 明示された名前空間またはパスの途中にある名前空間。
    Namespace {
        /// 名前空間を識別する完全修飾名の成分。
        key: NameKey<'q>,
        /// 元の記述順で、名前空間を最初に導入した箇所。
        introduced_at: LocatedName<'p, 'a>,
    },
}

/// 指定した名前空間から、その独立宣言が見えることを表す。
pub open spec fn mixed_declaration_visible_from(table: &MixedExportTable, key: NameKey, from: Option<&str>) -> bool {
    key_view(key) == key_view(NameKey { parent: from, name: key.name }) || table.publishes(key)
}

/// 指定の名前と参照元に対する解決結果を表す。
pub open spec fn mixed_key_resolution(
    table: &MixedExportTable, key: NameKey, from: Option<&str>,
    result: Result<MixedAbsoluteTarget, AbsoluteResolutionError>,
) -> bool {
    let declarations = table.declarations_model();
    let visible = mixed_declaration_visible_from(table, key, from);
    match result {
        Ok(MixedAbsoluteTarget::Declaration(declaration)) =>
            declarations.declaration_at(key, declaration) && visible && location_in_source(declaration.name),
        Ok(MixedAbsoluteTarget::Namespace { key: observed, introduced_at }) =>
            observed == key && !declarations.declares(key)
                && declarations.first_namespace_at(key, introduced_at) && location_in_source(introduced_at),
        Err(AbsoluteResolutionError::Private(location)) => !visible && location_in_source(location)
            && (exists|declaration: ProjectDeclaration| #[trigger] declarations.declaration_at(key, declaration)
                && declaration.name == location),
        Err(AbsoluteResolutionError::Missing) => !declarations.declares(key) && !declarations.has_namespace(key),
        Err(AbsoluteResolutionError::InvalidPath) => false,
    }
}

/// 完全修飾名の解決が、字句、共有宣言表、公開範囲に従うことを表す。
pub open spec fn mixed_absolute_resolution_evidence(
    table: &MixedExportTable, path: &str, from: Option<&str>,
    result: Result<MixedAbsoluteTarget, AbsoluteResolutionError>,
) -> bool {
    if result matches Err(AbsoluteResolutionError::InvalidPath) {
        bare_atom_kind(path.spec_bytes()) != Some(AtomKind::AbsolutePath)
    } else {
        exists|key: NameKey| #[trigger] absolute_path_parts(path, key.parent, key.name)
            && mixed_key_resolution(table, key, from, result)
    }
}


/// 同じ混在宣言表で得た二つの結果が、同じ宣言または名前空間を指すことを表す。
pub open spec fn same_mixed_target(left: MixedAbsoluteTarget, right: MixedAbsoluteTarget) -> bool {
    match (left, right) {
        (MixedAbsoluteTarget::Declaration(a), MixedAbsoluteTarget::Declaration(b)) =>
            a.file == b.file && a.item == b.item,
        (MixedAbsoluteTarget::Namespace { key: a, .. }, MixedAbsoluteTarget::Namespace { key: b, .. }) =>
            key_view(a) == key_view(b),
        _ => false,
    }
}

impl MixedAbsoluteTarget<'_, '_, '_> {
    /// 同じ混在宣言表で解決した二つの名前が、同じ対象を指すかを返す。
    pub(in crate::project) fn is_same_target(&self, other: &MixedAbsoluteTarget) -> (same: bool)
        ensures same == same_mixed_target(*self, *other),
    {
        match (self, other) {
            (Self::Declaration(a), MixedAbsoluteTarget::Declaration(b)) =>
                a.file == b.file && a.item == b.item,
            (Self::Namespace { key: a, .. }, MixedAbsoluteTarget::Namespace { key: b, .. }) =>
                a.same_name(*b),
            _ => false,
        }
    }
}

pub(in crate::project) open spec fn mixed_direct_target_matches(
    table: &MixedExportTable, key: NameKey, target: Option<MixedAbsoluteTarget>,
) -> bool {
    match target {
        Some(found) => mixed_key_resolution(table, key, key.parent, Ok(found)),
        None => mixed_key_resolution(table, key, key.parent, Err(AbsoluteResolutionError::Missing)),
    }
}

pub(in crate::project) proof fn mixed_direct_targets_agree(
    project: &ParsedProjectSources, table: &MixedExportTable, key: NameKey,
    left: Option<MixedAbsoluteTarget>, right: Option<MixedAbsoluteTarget>,
)
    requires mixed_export_table_matches(project, *table),
        mixed_direct_target_matches(table, key, left), mixed_direct_target_matches(table, key, right),
    ensures left == right,
{
    mixed_exports_use_project_declarations(project, table);
    let declarations = table.declarations_model();
    if let Some(MixedAbsoluteTarget::Declaration(a)) = left {
        declarations.declaration_at_exists(key, a);
        assert(right matches Some(MixedAbsoluteTarget::Declaration(_)));
        let b = right->Some_0->Declaration_0;
        mixed_declarations_agree(project, &declarations, key, a, b);
    } else if let Some(MixedAbsoluteTarget::Declaration(b)) = right {
        declarations.declaration_at_exists(key, b);
        assert(false);
    }
    if let Some(MixedAbsoluteTarget::Namespace { introduced_at: a, .. }) = left {
        declarations.namespace_at_exists(key, a);
        assert(right matches Some(MixedAbsoluteTarget::Namespace { .. }));
        let b = right->Some_0->Namespace_introduced_at;
        declarations.namespace_origins_agree(key, a, b);
    } else if let Some(MixedAbsoluteTarget::Namespace { introduced_at: b, .. }) = right {
        declarations.namespace_at_exists(key, b);
        assert(false);
    }
}

impl<'p, 'a> MixedExportTable<'p, 'a> {
    /// 混在プロジェクトの完全修飾名を、参照元の名前空間から解決する。
    ///
    /// `from` に参照元の名前空間パスを先頭の `::` を除いて渡す。ルート直下は `None` で表す。
    /// 別の名前空間の独立宣言は公開されていれば参照できる。名前空間は参照元を問わず解決できる。
    ///
    /// # Errors
    ///
    /// 完全修飾名として不正な綴り、対象の欠落、非公開の宣言を区別する。
    /// 非公開の場合は元の宣言名の範囲を返す。
    pub fn resolve_absolute<'q>(&self, path: &'q str, from: Option<&str>)
        -> (result: Result<MixedAbsoluteTarget<'p, 'a, 'q>, AbsoluteResolutionError<'p, 'a>>)
        ensures mixed_absolute_resolution_evidence(self, path, from, result),
    {
        let Some((parent, name)) = split_absolute_path(path) else {
            return Err(AbsoluteResolutionError::InvalidPath);
        };
        let key = NameKey { parent, name };
        assert(absolute_path_parts(path, key.parent, key.name));
        self.resolve_mixed_key(key, from)
    }

    // 別名との衝突検査では、同じ名前空間の直下を公開状態に関わらず参照する。
    pub(in crate::project) fn mixed_direct_target<'q>(&self, key: NameKey<'q>)
        -> (target: Option<MixedAbsoluteTarget<'p, 'a, 'q>>)
        ensures mixed_direct_target_matches(self, key, target),
    {
        match self.resolve_mixed_key(key, key.parent) {
            Ok(target) => Some(target),
            Err(AbsoluteResolutionError::Missing) => None,
            Err(_) => unreachable!(),
        }
    }

    pub(in crate::project) fn resolve_mixed_key<'q>(&self, key: NameKey<'q>, from: Option<&str>)
        -> (result: Result<MixedAbsoluteTarget<'p, 'a, 'q>, AbsoluteResolutionError<'p, 'a>>)
        ensures mixed_key_resolution(self, key, from, result),
    {
        let declarations = self.declarations();
        if let Some(declaration) = declarations.declaration(key) {
            if key.same_name(NameKey { parent: from, name: key.name }) || self.is_public(key) {
                return Ok(MixedAbsoluteTarget::Declaration(declaration));
            }
            return Err(AbsoluteResolutionError::Private(declaration.name));
        }
        if let Some(introduced_at) = declarations.namespace(key) {
            return Ok(MixedAbsoluteTarget::Namespace { key, introduced_at });
        }
        Err(AbsoluteResolutionError::Missing)
    }
}

} // verus!
