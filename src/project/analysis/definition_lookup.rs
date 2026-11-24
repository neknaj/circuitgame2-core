//! 確定した名前解決の結果から、参照位置が指す宣言を選ぶ。

use super::{DefinitionAnalysis, UseAliasReport};
use crate::project::{
    AbsoluteTarget, DefinitionBinding, IndexedDefinitionBinding, LocatedName, ResolvedUse,
    UseTargets, VirtualPath,
};
use vstd::prelude::*;

verus! {

spec fn definition_at<'p, 'a>(
    item: &IndexedDefinitionBinding<'p, 'a>, file: &VirtualPath, offset: usize,
) -> Option<LocatedName<'p, 'a>> {
    let resolved = &item.resolved;
    if resolved.site.source.id.components_model() != file.components_model()
        || !(resolved.site.name.span.start <= offset < resolved.site.name.span.end)
    {
        None
    } else {
        match resolved.binding {
            DefinitionBinding::Declaration { source, form } =>
                Some(LocatedName { source, span: form.name.span }),
            DefinitionBinding::Nor => None,
        }
    }
}

spec fn alias_at<'p, 'a>(item: &ResolvedUse<'p, 'a>, file: &VirtualPath, offset: usize)
    -> Option<LocatedName<'p, 'a>>
{
    let reference = item.site.reference.span;
    let alias = item.site.alias.span;
    if item.site.source.id.components_model() != file.components_model()
        || !(reference.start <= offset < reference.end || alias.start <= offset < alias.end)
    {
        None
    } else {
        match item.target {
            AbsoluteTarget::Declaration { source, form } =>
                Some(LocatedName { source, span: form.name.span }),
            AbsoluteTarget::Namespace { introduced_at, .. } => Some(introduced_at),
        }
    }
}

impl<'p, 'a> UseTargets<'p, 'a> {
    /// 対象ファイルの参照位置を含む最初の `use` が指す宣言を表す。
    pub closed spec fn alias_location_matches(
        &self, file: &VirtualPath, offset: usize, location: Option<LocatedName>,
    ) -> bool {
        let uses = self.directives_model();
        match location {
            Some(_) => exists|i: int| {
                &&& 0 <= i < uses.len() && alias_at(&(#[trigger] uses[i]), file, offset) == location
                &&& forall|j: int| 0 <= j < i ==> alias_at(&(#[trigger] uses[j]), file, offset).is_none()
            },
            None => forall|i: int| 0 <= i < uses.len() ==> alias_at(&(#[trigger] uses[i]), file, offset).is_none(),
        }
    }

    /// `use` の参照先または別名を指すバイト位置から、解決済みの宣言位置を返す。
    ///
    /// 指定位置を含む `use` がない場合は `None` を返す。
    /// 別名同士の衝突は [`crate::project::check_use_aliases`] で検査する。
    pub fn alias_location(
        &self, file: &VirtualPath, offset: usize,
    ) -> (location: Option<LocatedName<'p, 'a>>)
        ensures self.alias_location_matches(file, offset, location),
    {
        let uses = self.directives();
        let mut i = 0usize;
        while i < uses.len()
            invariant
                uses@ == self.directives_model(),
                i <= uses@.len(),
                forall|j: int| 0 <= j < i ==> alias_at(&(#[trigger] uses@[j]), file, offset).is_none(),
            decreases uses@.len() - i,
        {
            let item = &uses[i];
            let site = &item.site;
            if site.source.id.same_file(file)
                && (site.reference.span.start <= offset && offset < site.reference.span.end
                    || site.alias.span.start <= offset && offset < site.alias.span.end)
            {
                let location = match &item.target {
                    AbsoluteTarget::Declaration { source, form } => LocatedName {
                        source: *source, span: form.name.span.start..form.name.span.end,
                    },
                    AbsoluteTarget::Namespace { introduced_at, .. } => LocatedName {
                        source: introduced_at.source, span: introduced_at.span.start..introduced_at.span.end,
                    },
                };
                assert(alias_at(&uses@[i as int], file, offset) == Some(location));
                return Some(location);
            }
            assert(alias_at(&uses@[i as int], file, offset).is_none());
            i += 1;
        }
        None
    }
}

impl<'p, 'a> UseAliasReport<'p, 'a> {
    /// 対象ファイルの参照位置を含む最初の `use` が指す宣言を表す。
    pub closed spec fn alias_location_matches(
        &self, file: &VirtualPath, offset: usize, location: Option<LocatedName>,
    ) -> bool {
        self.targets.alias_location_matches(file, offset, location)
    }

    /// `use` の参照先または別名を指すバイト位置から、解決済みの宣言位置を返す。
    ///
    /// 指定位置を含む `use` がない場合は `None` を返す。
    pub fn alias_location(
        &self, file: &VirtualPath, offset: usize,
    ) -> (location: Option<LocatedName<'p, 'a>>)
        ensures self.alias_location_matches(file, offset, location),
    {
        self.targets.alias_location(file, offset)
    }
}

impl<'p, 'a> DefinitionAnalysis<'p, 'a> {
    /// 解決済みの参照を先に調べ、そこになければ `use` に対応する宣言を選ぶ。
    pub closed spec fn definition_location_matches(
        &self, file: &VirtualPath, offset: usize, location: Option<LocatedName>,
    ) -> bool {
        let defs = self.definitions@;
        ||| location.is_some() && exists|i: int| {
            &&& 0 <= i < defs.len() && definition_at(&(#[trigger] defs[i]), file, offset) == location
            &&& forall|j: int| 0 <= j < i ==> definition_at(&(#[trigger] defs[j]), file, offset).is_none()
        }
        ||| (forall|j: int| 0 <= j < defs.len() ==> definition_at(&(#[trigger] defs[j]), file, offset).is_none())
            && self.aliases.alias_location_matches(file, offset, location)
    }

    /// 参照位置から、コンパイラが選んだ宣言名の範囲を返す。
    ///
    /// 対象ファイルの UTF-8 バイト位置を受け取る。基底ゲートなど、対応する宣言のない位置は `None`。
    pub fn definition_location(
        &self, file: &VirtualPath, offset: usize,
    ) -> (location: Option<LocatedName<'p, 'a>>)
        ensures self.definition_location_matches(file, offset, location),
    {
        let mut i = 0usize;
        while i < self.definitions.len()
            invariant
                i <= self.definitions@.len(),
                forall|j: int| 0 <= j < i ==> definition_at(&(#[trigger] self.definitions@[j]), file, offset).is_none(),
            decreases self.definitions@.len() - i,
        {
            let item = &self.definitions[i];
            let resolved = &item.resolved;
            if resolved.site.source.id.same_file(file)
                && resolved.site.name.span.start <= offset && offset < resolved.site.name.span.end
            {
                if let DefinitionBinding::Declaration { source, form } = &resolved.binding {
                    let location = LocatedName { source: *source, span: form.name.span.start..form.name.span.end };
                    assert(definition_at(&self.definitions@[i as int], file, offset) == Some(location));
                    return Some(location);
                }
            }
            assert(definition_at(&self.definitions@[i as int], file, offset).is_none());
            i += 1;
        }
        self.aliases.alias_location(file, offset)
    }
}

} // verus!
