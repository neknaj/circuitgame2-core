//! 補助関数の宣言位置を起点に、NCG2M の呼び出し先を名前で解決する。

use super::MixedUseAliases;
use super::relative::destination_parent;
#[cfg(verus_only)]
use super::relative::parent_spelling;
use crate::project::{
    AbsoluteResolutionError, LocatedName, MixedAbsoluteTarget, NameKey,
    ProjectDeclaration, ProjectDeclarationKind,
};
use crate::project::source_indexes::DefnScope;
#[cfg(verus_only)]
use crate::project::{
    MixedExportTable, mixed_absolute_resolution_evidence, mixed_declaration_origin, mixed_use_targets_match, mixed_key_resolution,
    exports::mixed_exports_use_project_declarations,
    resolution::mixed_direct_target_matches,
};
use crate::syntax::{AtomKind, classify_bare_atom, split_relative_path};
#[cfg(verus_only)]
use crate::syntax::{absolute_path_parts, bare_atom_kind, relative_path_parts};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 補助関数の呼び出し位置で名前を解決した結果。
#[derive(Debug)]
pub enum ResolvedDefnName<'p, 'a> {
    /// 共通宣言表にある NCG2M の補助関数。
    Declaration(ProjectDeclaration<'p, 'a>),
    /// 現在の名前空間に宣言や別名がない無修飾名。段階に応じた組み込みの探索に渡す。
    StageName,
}

/// 呼び出し先の名前を解決できなかった理由。
#[derive(Debug)]
pub enum DefnNameError<'p, 'a> {
    /// 参照元として指定した項目が補助関数宣言に当たらない。
    Caller,
    /// 呼び出し先として使える名前の字句規則に合わない。
    InvalidName,
    /// 完全修飾名または相対パスが指す対象が存在しない。
    Missing,
    /// 相対パスの先頭に対応する名前空間または別名がない。
    MissingHead,
    /// 相対パスの先頭が独立宣言を指すため、その先をたどれない。
    DeclarationHead(ProjectDeclaration<'p, 'a>),
    /// 末尾の参照先が別の名前空間にあり、公開されていない。
    Private(LocatedName<'p, 'a>),
    /// 補助関数以外の独立宣言を指定した。
    WrongDeclaration(ProjectDeclaration<'p, 'a>),
    /// 補助関数を指定する位置で名前空間を指定した。
    Namespace(LocatedName<'p, 'a>),
}

spec fn call_target_result(
    absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>,
    result: Result<ResolvedDefnName, DefnNameError>,
) -> bool {
    match absolute {
        Ok(MixedAbsoluteTarget::Declaration(declaration)) => {
            if declaration.kind is Defn {
                result == Ok(ResolvedDefnName::Declaration(declaration))
            } else {
                result == Err(DefnNameError::WrongDeclaration(declaration))
            }
        }
        Ok(MixedAbsoluteTarget::Namespace { introduced_at, .. }) =>
            result == Err(DefnNameError::Namespace(introduced_at)),
        Err(AbsoluteResolutionError::Missing) => result == Err(DefnNameError::Missing),
        Err(AbsoluteResolutionError::Private(location)) => result == Err(DefnNameError::Private(location)),
        Err(AbsoluteResolutionError::InvalidPath) => result == Err(DefnNameError::InvalidName),
    }
}

fn call_target<'p, 'a>(
    absolute: Result<MixedAbsoluteTarget<'p, 'a, '_>, AbsoluteResolutionError<'p, 'a>>,
) -> (result: Result<ResolvedDefnName<'p, 'a>, DefnNameError<'p, 'a>>)
    ensures call_target_result(absolute, result),
{
    match absolute {
        Ok(MixedAbsoluteTarget::Declaration(declaration)) => {
            if matches!(declaration.kind, ProjectDeclarationKind::Defn) {
                Ok(ResolvedDefnName::Declaration(declaration))
            } else {
                Err(DefnNameError::WrongDeclaration(declaration))
            }
        }
        Ok(MixedAbsoluteTarget::Namespace { introduced_at, .. }) => Err(DefnNameError::Namespace(introduced_at)),
        Err(AbsoluteResolutionError::Missing) => Err(DefnNameError::Missing),
        Err(AbsoluteResolutionError::Private(location)) => Err(DefnNameError::Private(location)),
        Err(AbsoluteResolutionError::InvalidPath) => Err(DefnNameError::InvalidName),
    }
}

fn copy_location<'p, 'a>(location: &LocatedName<'p, 'a>) -> (out: LocatedName<'p, 'a>)
    ensures out == *location,
{
    LocatedName { source: location.source, span: location.span.start..location.span.end }
}

fn copy_target<'p, 'a, 'q>(target: &MixedAbsoluteTarget<'p, 'a, 'q>) -> (out: MixedAbsoluteTarget<'p, 'a, 'q>)
    ensures out == *target,
{
    match target {
        MixedAbsoluteTarget::Declaration(d) => MixedAbsoluteTarget::Declaration(ProjectDeclaration {
            name: copy_location(&d.name), kind: d.kind, file: d.file, item: d.item,
        }),
        MixedAbsoluteTarget::Namespace { key, introduced_at } =>
            MixedAbsoluteTarget::Namespace { key: *key, introduced_at: copy_location(introduced_at) },
    }
}

spec fn scoped_binding(
    aliases: &MixedUseAliases, file: usize, scope: DefnScope, word: &str, binding: Option<MixedAbsoluteTarget>,
) -> bool {
    let targets = aliases.targets_model();
    let rows = targets.directives_model();
    if aliases.first_alias_matches(file, scope.block, word, None) {
        mixed_direct_target_matches(&targets.exports_model(), NameKey { parent: scope.namespace, name: word }, binding)
    } else {
        exists|i: usize| #[trigger] aliases.first_alias_matches(file, scope.block, word, Some(i))
            && i < rows.len() && binding == Some(rows[i as int].target)
    }
}

spec fn plain_result(binding: Option<MixedAbsoluteTarget>, result: Result<ResolvedDefnName, DefnNameError>) -> bool {
    match binding {
        Some(target) => call_target_result(Ok(target), result),
        None => result == Ok(ResolvedDefnName::StageName),
    }
}

spec fn qualified_tail(
    exports: &MixedExportTable, from: Option<&str>, binding: Option<MixedAbsoluteTarget>,
    middle: Option<&str>, name: &str, result: Result<ResolvedDefnName, DefnNameError>,
) -> bool {
    match binding {
        None => result == Err(DefnNameError::MissingHead),
        Some(MixedAbsoluteTarget::Declaration(declaration)) =>
            result == Err(DefnNameError::DeclarationHead(declaration)),
        Some(MixedAbsoluteTarget::Namespace { key, .. }) =>
            exists|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                parent@ == parent_spelling(key, middle)
                && #[trigger] mixed_key_resolution(exports, NameKey { parent: Some(parent), name }, from, absolute)
                && call_target_result(absolute, result),
    }
}

/// 呼び出し先の選択と診断が、元の補助関数の所属と混在宣言表の名前解決規則に従うことを表す。
pub closed spec fn defn_name_resolution(
    aliases: &MixedUseAliases, file: usize, item: usize, name: &str,
    result: Result<ResolvedDefnName, DefnNameError>,
) -> bool {
    let targets = aliases.targets_model();
    let project = targets.project_model();
    if project.indexed_defn(file, item).is_none() {
        result == Err(DefnNameError::Caller)
    } else {
        exists|scope: DefnScope| #[trigger] project.defn_scope_matches(file, item, Some(scope))
            && name_in_scope(aliases, file, name, scope, result)
    }
}

spec fn name_in_scope(
    aliases: &MixedUseAliases, file: usize, name: &str, scope: DefnScope,
    result: Result<ResolvedDefnName, DefnNameError>,
) -> bool {
    let exports = aliases.targets_model().exports_model();
    match bare_atom_kind(name.spec_bytes()) {
        Some(AtomKind::AbsolutePath) =>
            exists|absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                #[trigger] mixed_absolute_resolution_evidence(&exports, name, scope.namespace, absolute)
                && call_target_result(absolute, result),
        Some(AtomKind::Name) => exists|binding: Option<MixedAbsoluteTarget>|
            #[trigger] scoped_binding(aliases, file, scope, name, binding) && plain_result(binding, result),
        Some(AtomKind::RelativePath) =>
            exists|head: &str, middle: Option<&str>, last: &str, binding: Option<MixedAbsoluteTarget>|
                #[trigger] relative_path_parts(name, head, middle, last)
                && #[trigger] scoped_binding(aliases, file, scope, head, binding)
                && qualified_tail(&exports, scope.namespace, binding, middle, last, result),
        _ => result == Err(DefnNameError::InvalidName),
    }
}

proof fn absolute_name_declares(
    exports: &MixedExportTable, name: &str, from: Option<&str>,
    declaration: ProjectDeclaration,
)
    requires mixed_absolute_resolution_evidence(exports, name, from, Ok(MixedAbsoluteTarget::Declaration(declaration))),
    ensures exists|key: NameKey| #[trigger] exports.declarations_model().declaration_at(key, declaration),
{
    let key = choose|key: NameKey| #[trigger] absolute_path_parts(name, key.parent, key.name)
        && mixed_key_resolution(exports, key, from, Ok(MixedAbsoluteTarget::Declaration(declaration)));
    assert(exports.declarations_model().declaration_at(key, declaration));
}

/// 解決した宣言が元ソースの補助関数であり、その索引から署名を取得できることを示す。
pub proof fn resolved_defn_name_origin(
    aliases: &MixedUseAliases, file: usize, item: usize, name: &str, declaration: ProjectDeclaration,
)
    requires
        defn_name_resolution(aliases, file, item, name, Ok(ResolvedDefnName::Declaration(declaration))),
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
    ensures
        declaration.kind is Defn,
        aliases.targets_model().project_model().indexed_defn(declaration.file, declaration.item).is_some(),
        declaration.file < aliases.targets_model().project_model().sources_model().len(),
        *declaration.name.source == aliases.targets_model().project_model().sources_model()[declaration.file as int],
{
    let targets = aliases.targets_model();
    let project = targets.project_model();
    let exports = targets.exports_model();
    let result = Ok(ResolvedDefnName::Declaration(declaration));
    let scope = choose|scope: DefnScope| #[trigger] project.defn_scope_matches(file, item, Some(scope))
        && name_in_scope(aliases, file, name, scope, result);
    let declarations = exports.declarations_model();
    match bare_atom_kind(name.spec_bytes()) {
        Some(AtomKind::AbsolutePath) => {
            let absolute = choose|absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                #[trigger] mixed_absolute_resolution_evidence(&exports, name, scope.namespace, absolute)
                && call_target_result(absolute, result);
            assert(absolute == Ok(MixedAbsoluteTarget::Declaration(declaration)));
            absolute_name_declares(&exports, name, scope.namespace, declaration);
        }
        Some(AtomKind::Name) => {
            let binding = choose|binding: Option<MixedAbsoluteTarget>|
                #[trigger] scoped_binding(aliases, file, scope, name, binding) && plain_result(binding, result);
            assert(binding == Some(MixedAbsoluteTarget::Declaration(declaration)));
            if aliases.first_alias_matches(file, scope.block, name, None) {
                let key = NameKey { parent: scope.namespace, name };
                assert(declarations.declaration_at(key, declaration));
            } else {
                let rows = targets.directives_model();
                let i = choose|i: usize| #[trigger] aliases.first_alias_matches(file, scope.block, name, Some(i))
                    && i < rows.len() && binding == Some(rows[i as int].target);
                targets.directive_origin(i as int);
                let row = rows[i as int];
                absolute_name_declares(&exports, row.site.reference.word, row.site.namespace, declaration);
            }
        }
        Some(AtomKind::RelativePath) => {
            let (head, middle, last, binding) = choose|head: &str, middle: Option<&str>, last: &str, binding: Option<MixedAbsoluteTarget>|
                #[trigger] relative_path_parts(name, head, middle, last)
                && #[trigger] scoped_binding(aliases, file, scope, head, binding)
                && qualified_tail(&exports, scope.namespace, binding, middle, last, result);
            let key = binding->Some_0->Namespace_key;
            let (parent, absolute) = choose|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                parent@ == parent_spelling(key, middle)
                && #[trigger] mixed_key_resolution(&exports, NameKey { parent: Some(parent), name: last }, scope.namespace, absolute)
                && call_target_result(absolute, result);
            assert(absolute == Ok(MixedAbsoluteTarget::Declaration(declaration)));
            assert(declarations.declaration_at(NameKey { parent: Some(parent), name: last }, declaration));
        }
        _ => assert(false),
    }
    let key = choose|key: NameKey| #[trigger] declarations.declaration_at(key, declaration);
    targets.mixed_use_exports_match(&project);
    mixed_exports_use_project_declarations(&project, &exports);
    mixed_declaration_origin(&project, &declarations, key, declaration);
    project.indexed_defn_kind(declaration.file, declaration.item);
}

/// 組み込みの探索に進めるのは、無修飾名に別名も直接束縛もない場合であることを示す。
pub proof fn stage_name_has_no_binding<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize, name: &str,
) -> (scope: (Option<usize>, Option<&'a str>))
    requires defn_name_resolution(aliases, file, item, name, Ok(ResolvedDefnName::StageName)),
    ensures
        bare_atom_kind(name.spec_bytes()) == Some(AtomKind::Name),
        aliases.first_alias_matches(file, scope.0, name, None),
        !aliases.targets_model().exports_model().declarations_model().declares(NameKey { parent: scope.1, name }),
        !aliases.targets_model().exports_model().declarations_model().has_namespace(NameKey { parent: scope.1, name }),
{
    let project = aliases.targets_model().project_model();
    let result = Ok(ResolvedDefnName::StageName);
    let scope = choose|scope: DefnScope| #[trigger] project.defn_scope_matches(file, item, Some(scope))
        && name_in_scope(aliases, file, name, scope, result);
    let exports = aliases.targets_model().exports_model();
    match bare_atom_kind(name.spec_bytes()) {
        Some(AtomKind::AbsolutePath) => {
            let absolute = choose|absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                #[trigger] mixed_absolute_resolution_evidence(&exports, name, scope.namespace, absolute)
                && call_target_result(absolute, result);
            assert(false);
        }
        Some(AtomKind::RelativePath) => {
            let (head, middle, last, binding) = choose|head: &str, middle: Option<&str>, last: &str, binding: Option<MixedAbsoluteTarget>|
                #[trigger] relative_path_parts(name, head, middle, last)
                && #[trigger] scoped_binding(aliases, file, scope, head, binding)
                && qualified_tail(&exports, scope.namespace, binding, middle, last, result);
            assert(binding->Some_0 is Namespace);
            let key = binding->Some_0->Namespace_key;
            let (parent, absolute) = choose|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                parent@ == parent_spelling(key, middle)
                && #[trigger] mixed_key_resolution(&exports, NameKey { parent: Some(parent), name: last }, scope.namespace, absolute)
                && call_target_result(absolute, result);
            assert(false);
        }
        Some(AtomKind::Name) => {
            let binding = choose|binding: Option<MixedAbsoluteTarget>|
                #[trigger] scoped_binding(aliases, file, scope, name, binding) && plain_result(binding, result);
            assert(binding.is_none());
            assert(aliases.first_alias_matches(file, scope.block, name, None)) by {
                if !aliases.first_alias_matches(file, scope.block, name, None) {
                    let rows = aliases.targets_model().directives_model();
                    let i = choose|i: usize| #[trigger] aliases.first_alias_matches(file, scope.block, name, Some(i))
                        && i < rows.len() && binding == Some(rows[i as int].target);
                }
            };
        }
        _ => assert(false),
    }
    (scope.block, scope.namespace)
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    fn binding_for_call<'q>(&'q self, file: usize, scope: DefnScope<'a>, word: &'q str)
        -> (binding: Option<MixedAbsoluteTarget<'p, 'a, 'q>>)
        ensures scoped_binding(self, file, scope, word, binding),
    {
        let targets = self.targets();
        let rows = targets.directives();
        let rank = self.first_alias(file, scope.block, word);
        proof { self.first_alias_origin(file, scope.block, word, rank); }
        if let Some(i) = rank {
            let target = copy_target(&rows[i].target);
            assert(!self.first_alias_matches(file, scope.block, word, None)) by {
                if self.first_alias_matches(file, scope.block, word, None) {
                    self.first_alias_origin(file, scope.block, word, None);
                }
            };
            Some(target)
        } else {
            targets.exports().mixed_direct_target(NameKey { parent: scope.namespace, name: word })
        }
    }

    fn relative_call(
        &self, file: usize, scope: DefnScope<'a>, path: &str,
    ) -> (result: Result<ResolvedDefnName<'p, 'a>, DefnNameError<'p, 'a>>)
        requires bare_atom_kind(path.spec_bytes()) == Some(AtomKind::RelativePath),
        ensures
            exists|head: &str, middle: Option<&str>, last: &str, binding: Option<MixedAbsoluteTarget>|
                #[trigger] relative_path_parts(path, head, middle, last)
                && #[trigger] scoped_binding(self, file, scope, head, binding)
                && qualified_tail(&self.targets_model().exports_model(), scope.namespace, binding, middle, last, result),
    {
        let Some((head, middle, last)) = split_relative_path(path) else { unreachable!() };
        let binding = self.binding_for_call(file, scope, head);
        let ghost selected = binding;
        match binding {
            None => Err(DefnNameError::MissingHead),
            Some(MixedAbsoluteTarget::Declaration(declaration)) => Err(DefnNameError::DeclarationHead(declaration)),
            Some(MixedAbsoluteTarget::Namespace { key, .. }) => {
                let exports = self.targets().exports();
                let parent = destination_parent(key, middle);
                let tail = NameKey { parent: Some(parent.as_str()), name: last };
                let absolute = exports.resolve_mixed_key(tail, scope.namespace);
                let outcome = call_target(absolute);
                assert(qualified_tail(&self.targets_model().exports_model(), scope.namespace, selected, middle, last, outcome));
                outcome
            }
        }
    }

    /// 補助関数の宣言位置から、呼び出し名を解決する。
    ///
    /// 完全修飾名と相対パスは、参照元の名前空間を基準に公開範囲を検査する。
    /// 無修飾名は元のファイルとブロック内の別名、または同じ名前空間の宣言を調べる。
    /// 束縛がなければ、参照元の段階で使える組み込みを探索するための結果を返す。
    ///
    /// # Errors
    ///
    /// 参照元が補助関数宣言であることを先に検査する。名前の字句違反、修飾先の不在・非公開、
    /// 補助関数以外の対象を区別する。対象が存在する診断では、元の宣言または名前空間の範囲を返す。
    ///
    /// # Examples
    ///
    /// 完全修飾名、宣言の別名、名前空間の別名は、同じ補助関数を指せる。
    /// 別名は宣言を書いたブロックの中で使う。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     DefnNameError, ResolvedDefnName, SourceSnapshot, check_mixed_use_aliases,
    ///     index_mixed_use_targets, parse_project_sources,
    /// };
    ///
    /// let library = "(namespace lib
    ///     (defn ready (as-type (Fn () Bool) (fn () true)))
    ///     (defn hidden (as-type (Fn () Bool) (fn () false)))
    ///     (export ready))";
    /// let application = "(namespace app
    ///     (use ::lib l) (use ::lib::ready f)
    ///     (defn caller (as-type (Fn () Bool) (fn () (f)))))
    ///     (namespace app (defn other (as-type (Fn () Bool) (fn () true))))";
    /// let inputs = [
    ///     SourceSnapshot { path: "lib.ncg2m", revision: 5, text: library },
    ///     SourceSnapshot { path: "app.ncg2m", revision: 7, text: application },
    /// ];
    /// let project = parse_project_sources(&inputs).unwrap();
    /// let uses = index_mixed_use_targets(&project).unwrap();
    /// let aliases = check_mixed_use_aliases(&uses).unwrap();
    /// for name in ["::lib::ready", "l::ready", "f"] {
    ///     let ResolvedDefnName::Declaration(target) = aliases.resolve_defn_name(1, 3, name).unwrap()
    ///         else { panic!() };
    ///     assert_eq!(&library[target.name.span], "ready");
    /// }
    /// assert!(matches!(aliases.resolve_defn_name(1, 3, "l::hidden"), Err(DefnNameError::Private(_))));
    /// assert!(matches!(aliases.resolve_defn_name(1, 5, "f"), Ok(ResolvedDefnName::StageName)));
    /// ```
    pub fn resolve_defn_name(&self, file: usize, item: usize, name: &str)
        -> (result: Result<ResolvedDefnName<'p, 'a>, DefnNameError<'p, 'a>>)
        ensures defn_name_resolution(self, file, item, name, result),
    {
        let targets = self.targets();
        let project = targets.project();
        let Some(scope) = project.defn_scope(file, item) else {
            proof { project.defn_scope_is_indexed(file, item, None); }
            return Err(DefnNameError::Caller);
        };
        proof { project.defn_scope_is_indexed(file, item, Some(scope)); }
        let kind = classify_bare_atom(name);
        let outcome = match kind {
            Some(AtomKind::AbsolutePath) => call_target(targets.exports().resolve_absolute(name, scope.namespace)),
            Some(AtomKind::RelativePath) => self.relative_call(file, scope, name),
            Some(AtomKind::Name) => match self.binding_for_call(file, scope, name) {
                Some(target) => call_target(Ok(target)),
                None => Ok(ResolvedDefnName::StageName),
            },
            _ => Err(DefnNameError::InvalidName),
        };
        assert(defn_name_resolution(self, file, item, name, outcome));
        outcome
    }
}

}
