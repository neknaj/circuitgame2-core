//! 完全修飾名を共有宣言表と公開表に照合する。

#[cfg(verus_only)]
use super::declarations::declaration_location_evidence;
#[cfg(verus_only)]
use super::location_in_source;
#[cfg(verus_only)]
use super::name_keys::key_view;
use super::{ExportTable, LocatedName, NameKey, ProjectSource};
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
pub open spec fn declaration_exists(table: &ExportTable, key: NameKey) -> bool {
    exists|source: &ProjectSource, form: &NamedForm|
        #[trigger] table.declarations_model().declaration_at(key, source, form)
}

/// 完全修飾名の成分と参照元に対して、解決結果または診断の根拠を定める。
pub open spec fn has_resolution(
    table: &ExportTable, key: NameKey, from: Option<&str>,
    result: Result<AbsoluteTarget, AbsoluteResolutionError>,
) -> bool {
    let declarations = table.declarations_model();
    match result {
        Ok(AbsoluteTarget::Declaration { source, form }) =>
            declarations.declaration_at(key, source, form) && declaration_visible_from(table, key, from),
        Ok(AbsoluteTarget::Namespace { key: observed, introduced_at }) =>
            observed == key && !declaration_exists(table, key)
                && declarations.namespace_at(key, introduced_at) && location_in_source(introduced_at),
        Err(AbsoluteResolutionError::Private(location)) =>
            !declaration_visible_from(table, key, from) && location_in_source(location)
                && (exists|form: &NamedForm| #[trigger] declarations.declaration_at(key, location.source, form)
                    && location.span == form.name.span),
        Err(AbsoluteResolutionError::Missing) =>
            !declaration_exists(table, key)
                && (forall|location: LocatedName| !#[trigger] declarations.namespace_at(key, location)),
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
        let declarations = self.declarations();
        if let Some((source, form)) = declarations.declaration(key) {
            if key.same_name(NameKey { parent: from, name }) || self.is_public(key) {
                return Ok(AbsoluteTarget::Declaration { source, form });
            }
            proof { declaration_location_evidence(declarations, key, source, form); }
            let span = &form.name.span;
            return Err(AbsoluteResolutionError::Private(LocatedName { source, span: span.start..span.end }));
        }
        if let Some(introduced_at) = declarations.namespace(key) {
            Ok(AbsoluteTarget::Namespace { key, introduced_at })
        } else {
            Err(AbsoluteResolutionError::Missing)
        }
    }
}

} // verus!
