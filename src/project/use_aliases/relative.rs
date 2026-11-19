//! 相対パスの先頭をスコープで解決し、残りを共有宣言表で検索する。

use super::{ReferenceScopeError, UnqualifiedTarget, UseAliases};
#[cfg(verus_only)]
use crate::project::ExportTable;
#[cfg(verus_only)]
use crate::project::resolution::has_resolution;
use crate::project::{
    AbsoluteResolutionError, AbsoluteTarget, LocatedName, NameKey, ProjectSource,
};
use crate::syntax::circuit::NamedForm;
use crate::syntax::split_relative_path;
#[cfg(verus_only)]
use crate::syntax::{AtomKind, bare_atom_kind, relative_path_parts};
use alloc::string::String;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 相対パスが指す元の宣言または名前空間。
#[derive(Debug)]
pub enum RelativeTarget<'p, 'a, 'q> {
    /// 共有宣言表の独立宣言。
    Declaration {
        /// 宣言のあるファイルと文書版。
        source: &'p ProjectSource<'a>,
        /// 宣言の種別、名前、元ソース上の位置。
        form: &'p NamedForm<'a>,
    },
    /// 明示された名前空間またはパスの中間にある名前空間。
    Namespace {
        /// ルートから親名前空間までのパス。先頭の `::` は含まない。
        parent: String,
        /// 相対パスから借用する末尾の名前。
        name: &'q str,
        /// 対象を導入した箇所の一つ。
        introduced_at: LocatedName<'p, 'a>,
    },
}

/// 相対パスを解決できなかった理由。
#[derive(Debug)]
pub enum RelativeResolutionError<'p, 'a> {
    /// 指定したファイルまたは名前空間ブロックが見つからない。
    Scope(ReferenceScopeError),
    /// 入力が相対パスの字句規則に従わない。
    InvalidPath,
    /// 先頭の名前に対応する直接の束縛または別名がない。
    MissingHead,
    /// 先頭の名前が独立宣言を指すため、その先をたどれない。
    DeclarationHead {
        /// 先頭の名前が指す宣言のファイルと文書版。
        source: &'p ProjectSource<'a>,
        /// 宣言の名前と元ソース上の位置。
        form: &'p NamedForm<'a>,
    },
    /// 先頭が指す名前空間から残りのパスをたどった先に、対象がない。
    Missing,
    /// 末尾の宣言が別の名前空間にあり、公開されていない。
    Private(LocatedName<'p, 'a>),
}

spec fn parent_spelling(head: NameKey, middle: Option<&str>) -> Seq<char> {
    let separator = "::"@;
    let base = if let Some(parent) = head.parent { parent@ + separator + head.name@ } else { head.name@ };
    if let Some(middle) = middle { base + separator + middle@ } else { base }
}

fn destination_parent(head: NameKey, middle: Option<&str>) -> (parent: String)
    ensures parent@ == parent_spelling(head, middle),
{
    let mut path = String::new();
    if let Some(parent) = head.parent {
        path.push_str(parent);
        path.push_str("::");
    }
    path.push_str(head.name);
    if let Some(middle) = middle {
        path.push_str("::");
        path.push_str(middle);
    }
    path
}

spec fn tail_matches(
    table: &ExportTable, head: NameKey, middle: Option<&str>, name: &str, from: Option<&str>,
    result: Result<RelativeTarget, RelativeResolutionError>,
) -> bool {
    let spelling = parent_spelling(head, middle);
    exists|parent: &str| #[trigger] parent@ == spelling && {
        let key = NameKey { parent: Some(parent), name };
        match result {
            Ok(RelativeTarget::Declaration { source, form }) =>
                has_resolution(table, key, from, Ok(AbsoluteTarget::Declaration { source, form })),
            Ok(RelativeTarget::Namespace { parent: path, name: observed, introduced_at }) =>
                path@ == spelling && observed == name
                    && has_resolution(table, key, from, Ok(AbsoluteTarget::Namespace { key, introduced_at })),
            Err(RelativeResolutionError::Missing) =>
                has_resolution(table, key, from, Err(AbsoluteResolutionError::Missing)),
            Err(RelativeResolutionError::Private(location)) =>
                has_resolution(table, key, from, Err(AbsoluteResolutionError::Private(location))),
            _ => false,
        }
    }
}

spec fn path_outcome(
    table: &ExportTable, from: Option<&str>, binding: Option<UnqualifiedTarget>, middle: Option<&str>, name: &str,
    result: Result<RelativeTarget, RelativeResolutionError>,
) -> bool {
    match binding {
        None => result is Err && result->Err_0 is MissingHead,
        Some(binding) => {
            let target = match binding {
                UnqualifiedTarget::Direct(target) => target,
                UnqualifiedTarget::Alias(directive) => directive.target,
            };
            match target {
                AbsoluteTarget::Declaration { source, form } =>
                    result == Err(RelativeResolutionError::DeclarationHead { source, form }),
                AbsoluteTarget::Namespace { key, .. } => tail_matches(table, key, middle, name, from, result),
            }
        },
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) proof fn relative_requires_valid_input(
        &self, file: usize, block: Option<usize>, path: &str, from: Option<&str>,
        found: Result<RelativeTarget, RelativeResolutionError>,
    )
        requires
            self.scope_matches(file, block, Ok(from)),
            bare_atom_kind(path.spec_bytes()) == Some(AtomKind::RelativePath),
            self.relative_resolution_matches(file, block, path, found),
        ensures !matches!(found, Err(RelativeResolutionError::Scope(_) | RelativeResolutionError::InvalidPath)),
    {
        if let Err(RelativeResolutionError::Scope(error)) = found {
            assert(self.scope_matches(file, block, Err(error)));
        }
    }

    /// 相対パスの結果が、参照元の束縛、元の名前空間、共有宣言表、公開条件に対応することを表す。
    pub closed spec fn relative_resolution_matches(
        &self, file: usize, block: Option<usize>, path: &str,
        result: Result<RelativeTarget, RelativeResolutionError>,
    ) -> bool {
        match result {
            Err(RelativeResolutionError::Scope(error)) => self.scope_matches(file, block, Err(error)),
            Err(RelativeResolutionError::InvalidPath) => bare_atom_kind(path.spec_bytes()) != Some(AtomKind::RelativePath)
                && (exists|from: Option<&str>| #[trigger] self.scope_matches(file, block, Ok(from))),
            _ => exists|head: &str, middle: Option<&str>, name: &str, from: Option<&str>, binding: Option<UnqualifiedTarget>|
                #![trigger relative_path_parts(path, head, middle, name), self.unqualified_binding_matches(file, block, head, from, binding)]
                relative_path_parts(path, head, middle, name)
                && self.scope_matches(file, block, Ok(from))
                && self.unqualified_binding_matches(file, block, head, from, binding)
                && path_outcome(&self.targets.exports_model(), from, binding, middle, name, result),
        }
    }

    /// 相対パスを、指定したファイルとブロックから解決する。
    ///
    /// `file` と `block` は [`Self::resolve_unqualified`] と同じ添字を使う。
    /// 先頭の成分が指す名前空間の実パスに残りをつなぎ、末尾の宣言が参照元から見えるかを検査する。
    ///
    /// # Errors
    ///
    /// 無効なスコープ、字句違反、先頭の束縛の不在、宣言を指す先頭、参照先の不在と非公開を区別する。
    /// 参照元のスコープを、相対パスの綴りより先に検査する。
    pub fn resolve_relative<'q>(
        &'q self, file: usize, block: Option<usize>, path: &'q str,
    ) -> (result: Result<RelativeTarget<'p, 'a, 'q>, RelativeResolutionError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.relative_resolution_matches(file, block, path, result),
    {
        let from = match self.scope_namespace(file, block) {
            Ok(from) => from,
            Err(error) => return Err(RelativeResolutionError::Scope(error)),
        };
        let Some((head, middle, name)) = split_relative_path(path) else {
            return Err(RelativeResolutionError::InvalidPath);
        };
        let binding = self.lookup_in_scope(file, block, from, head);
        let ghost selection = binding;
        let Some(binding) = binding else {
            assert(self.unqualified_binding_matches(file, block, head, from, selection));
            return Err(RelativeResolutionError::MissingHead);
        };
        let target = match &binding {
            UnqualifiedTarget::Alias(directive) => &directive.target,
            UnqualifiedTarget::Direct(target) => target,
        };
        let head_key = match target {
            AbsoluteTarget::Declaration { source, form } =>
                return Err(RelativeResolutionError::DeclarationHead { source, form }),
            AbsoluteTarget::Namespace { key, .. } => *key,
        };
        let parent = destination_parent(head_key, middle);
        let key = NameKey { parent: Some(parent.as_str()), name };
        let result = match self.targets.exports().resolve_key(key, from) {
            Ok(AbsoluteTarget::Declaration { source, form }) => Ok(RelativeTarget::Declaration { source, form }),
            Ok(AbsoluteTarget::Namespace { introduced_at, .. }) =>
                Ok(RelativeTarget::Namespace { parent, name, introduced_at }),
            Err(AbsoluteResolutionError::Missing) => Err(RelativeResolutionError::Missing),
            Err(AbsoluteResolutionError::Private(location)) => Err(RelativeResolutionError::Private(location)),
            Err(AbsoluteResolutionError::InvalidPath) => {
                proof { assert(false); }
                unreachable!();
            }
        };
        assert(tail_matches(&self.targets.exports_model(), head_key, middle, name, from, result));
        result
    }
}

} // verus!
