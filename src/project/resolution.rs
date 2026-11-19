//! 完全修飾名を共有宣言表と公開表に照合する。

use super::declarations::key_of;
#[cfg(verus_only)]
use super::declarations::{
    declaration_key_evidence, declaration_location_evidence, declaration_sites_agree,
    declaration_table_matches, form_key, project_names_conflict,
};
#[cfg(verus_only)]
use super::{CircuitProject, location_in_source};
#[cfg(verus_only)]
use super::name_keys::key_view;
use super::{DeclarationTable, ExportTable, LocatedName, NameKey, ProjectSource};
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
            direct_target_matches(&declarations, key, Some(target)),
        Err(AbsoluteResolutionError::Private(location)) =>
            !declaration_visible_from(table, key, from) && location_in_source(location)
                && (exists|form: &NamedForm| #[trigger] declarations.declaration_at(key, location.source, form)
                    && location.span == form.name.span),
        Err(AbsoluteResolutionError::Missing) => direct_target_matches(&declarations, key, None),
        Err(AbsoluteResolutionError::InvalidPath) => false,
    }
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

    /// 宣言表のキーを解決し、参照元から末尾の宣言が見えることを確かめる。
    pub(super) fn resolve_key<'q>(&self, key: NameKey<'q>, from: Option<&str>)
        -> (result: Result<AbsoluteTarget<'p, 'a, 'q>, AbsoluteResolutionError<'p, 'a>>)
        requires self.declarations_model().well_formed(),
        ensures has_resolution(self, key, from, result),
    {
        match self.declarations().direct_target(key) {
            Some(target @ AbsoluteTarget::Declaration { source, form }) => {
                if key.same_name(NameKey { parent: from, name: key.name }) || self.is_public(key) {
                    Ok(target)
                } else {
                    let span = &form.name.span;
                    Err(AbsoluteResolutionError::Private(LocatedName { source, span: span.start..span.end }))
                }
            }
            Some(target @ AbsoluteTarget::Namespace { .. }) => Ok(target),
            None => Err(AbsoluteResolutionError::Missing),
        }
    }
}

} // verus!
