//! 混在ソース集合の厳格索引から、関数の呼び出し位置を確定する。

use super::{MixedUseAliases, definitions::DefinitionReferenceSite, find_namespace, relative::destination_parent};
#[cfg(verus_only)]
use super::{defn_name::scoped_binding, is_namespace_block, relative::parent_spelling};
use crate::project::circuits::read_indexed_atom;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::project::source_indexes::{project_source_index_evidence, project_source_index_matches};
use crate::project::source_indexes::DefnScope;
use crate::project::{AbsoluteResolutionError, LocatedName, MixedAbsoluteTarget, NameKey, ParsedProjectSources,
    ProjectDeclaration, ProjectDeclarationKind, ProjectSourceIndex};
#[cfg(verus_only)]
use crate::project::{mixed_absolute_resolution_evidence, mixed_key_resolution};
use crate::syntax::{AtomKind, classify_bare_atom, split_relative_path};
#[cfg(verus_only)]
use crate::syntax::{bare_atom_kind, relative_path_parts};
use crate::syntax::circuit::{ExpressionReferenceKind, Head, NameSite};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    NamedBuildCircuit, build_definition_scope_evidence, build_entry_ranges_evidence, expression_reference_in_source,
    namespace_name_evidence, reference_atom,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::is_char_boundary};

verus! {

/// `func` の呼び出し名が指す対象。
#[derive(Debug)]
pub enum MixedFuncCallee<'p, 'a> {
    /// 混在宣言表にある回路関数。
    Function(ProjectDeclaration<'p, 'a>),
    /// 同じスコープに束縛がないときに選ぶ基底ゲート。
    Nor,
}

/// `func` の呼び出し名を解決できなかった理由。
#[derive(Debug)]
pub enum MixedFuncCalleeError<'p, 'a> {
    /// スコープに呼び出し先が見つからない。
    Missing,
    /// 相対パスの先頭に対応する名前空間または別名がない。
    MissingPrefix,
    /// 相対パスの先頭が宣言を指すため、その内側をたどれない。
    DeclarationPrefix(ProjectDeclaration<'p, 'a>),
    /// 別の名前空間にある非公開宣言の位置。
    Private(LocatedName<'p, 'a>),
    /// 呼び出し名が名前空間を指す。値はその名前空間の宣言位置。
    Namespace(LocatedName<'p, 'a>),
    /// 回路関数以外の宣言が選ばれた。
    WrongDeclaration(ProjectDeclaration<'p, 'a>),
}

spec fn qualified_func_target(
    outcome: Result<MixedAbsoluteTarget, AbsoluteResolutionError>,
    result: Result<MixedFuncCallee, MixedFuncCalleeError>,
) -> bool {
    match outcome {
        Ok(MixedAbsoluteTarget::Declaration(declaration)) => {
            if declaration.kind == ProjectDeclarationKind::Circuit(Head::Func) {
                result == Ok(MixedFuncCallee::Function(declaration))
            } else {
                result == Err(MixedFuncCalleeError::WrongDeclaration(declaration))
            }
        },
        Ok(MixedAbsoluteTarget::Namespace { introduced_at, .. }) =>
            result == Err(MixedFuncCalleeError::Namespace(introduced_at)),
        Err(AbsoluteResolutionError::Private(location)) => result == Err(MixedFuncCalleeError::Private(location)),
        Err(_) => result == Err(MixedFuncCalleeError::Missing),
    }
}

fn checked_func_target<'p, 'a>(outcome: Result<MixedAbsoluteTarget<'p, 'a, '_>, AbsoluteResolutionError<'p, 'a>>)
    -> (result: Result<MixedFuncCallee<'p, 'a>, MixedFuncCalleeError<'p, 'a>>)
    ensures qualified_func_target(outcome, result),
{
    match outcome {
        Ok(MixedAbsoluteTarget::Declaration(declaration)) => {
            if matches!(declaration.kind, ProjectDeclarationKind::Circuit(Head::Func)) {
                Ok(MixedFuncCallee::Function(declaration))
            } else { Err(MixedFuncCalleeError::WrongDeclaration(declaration)) }
        },
        Ok(MixedAbsoluteTarget::Namespace { introduced_at, .. }) => Err(MixedFuncCalleeError::Namespace(introduced_at)),
        Err(AbsoluteResolutionError::Private(site)) => Err(MixedFuncCalleeError::Private(site)),
        Err(_) => Err(MixedFuncCalleeError::Missing),
    }
}

/// 元の呼び出し位置と、そのスコープでの名前解決結果。
#[derive(Debug)]
pub struct MixedFuncCalleeResolution<'p, 'a> {
    /// 呼び出し名の範囲、参照元の文書版、名前空間ブロック。
    pub site: DefinitionReferenceSite<'p, 'a>,
    /// 解決した回路関数、基底ゲート、または名前解決の違反。
    pub target: Result<MixedFuncCallee<'p, 'a>, MixedFuncCalleeError<'p, 'a>>,
}

spec fn unqualified_func_target(
    word: &str, binding: Option<MixedAbsoluteTarget>,
    result: Result<MixedFuncCallee, MixedFuncCalleeError>,
) -> bool {
    match binding {
        Some(target) => qualified_func_target(Ok(target), result),
        None => if word@ == "nor"@ {
            result == Ok(MixedFuncCallee::Nor)
        } else {
            result == Err(MixedFuncCalleeError::Missing)
        },
    }
}

spec fn func_target_in_scope(
    aliases: &MixedUseAliases, file: usize, scope: DefnScope, word: &str,
    result: Result<MixedFuncCallee, MixedFuncCalleeError>,
) -> bool {
    let exports = aliases.targets_model().exports_model();
    match bare_atom_kind(word.spec_bytes()) {
        Some(AtomKind::Name) => exists|binding: Option<MixedAbsoluteTarget>|
            #[trigger] scoped_binding(aliases, file, scope, word, binding)
                && unqualified_func_target(word, binding, result),
        Some(AtomKind::AbsolutePath) => exists|absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
            #[trigger] mixed_absolute_resolution_evidence(&exports, word, scope.namespace, absolute)
                && qualified_func_target(absolute, result),
        Some(AtomKind::RelativePath) => exists|head: &str, middle: Option<&str>, last: &str, binding: Option<MixedAbsoluteTarget>|
            #[trigger] relative_path_parts(word, head, middle, last)
                && #[trigger] scoped_binding(aliases, file, scope, head, binding)
                && match binding {
                    None => result == Err(MixedFuncCalleeError::MissingPrefix),
                    Some(MixedAbsoluteTarget::Declaration(declaration)) => result == Err(MixedFuncCalleeError::DeclarationPrefix(declaration)),
                    Some(MixedAbsoluteTarget::Namespace { key, .. }) =>
                        exists|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                            parent@ == parent_spelling(key, middle)
                                && #[trigger] mixed_key_resolution(&exports, NameKey { parent: Some(parent), name: last }, scope.namespace, absolute)
                                && qualified_func_target(absolute, result),
                },
        _ => false,
    }
}

spec fn func_scope_path(parsed: &NamedBuildCircuit, block: Option<usize>, namespace: Option<&str>) -> bool {
    match block {
        None => namespace.is_none(),
        Some(block) => exists|i: int| 0 <= i < parsed.names@.len()
            && #[trigger] is_namespace_block(parsed.names@[i], block)
            && namespace == Some(parsed.names@[i].name.word),
    }
}

impl<'a> ParsedProjectSources<'a> {
    /// 指定した定義内参照が `func` 本体の呼び出し名であることを表す。
    pub open spec fn has_func_callee(&self, file: usize, entry: usize, definition: usize, reference: usize) -> bool {
        &&& file < self.sources_model().len()
        &&& file < self.indexes_model().len()
        &&& self.indexes_model()[file as int] matches ProjectSourceIndex::Circuit(parsed)
        &&& entry < parsed.syntax.entries@.len()
        &&& entry < parsed.entry_ranges@.len()
        &&& parsed.syntax.entries@[entry as int].head is Func
        &&& {
            let definitions = parsed.entry_ranges@[entry as int].definitions;
            let index = definitions.start + definition;
            &&& index < definitions.end
            &&& index < parsed.definitions@.len()
            &&& {
                let references = parsed.definitions@[index].references;
                let at = references.start + reference;
                &&& at < references.end
                &&& at < parsed.references@.len()
                &&& parsed.references@[at].kind is Callee
            }
        }
    }

    /// 混在ソース集合のファイル番号で、`func` 本体の呼び出し名を取り出す。
    ///
    /// `entry` はファイル内の構文項目、`definition` は項目内の定義、`reference` は定義内の参照の添字。
    /// 範囲外の添字や `func` の呼び出し名を指さない添字には `None` を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{ProjectSourceIndex, SourceSnapshot, parse_project_sources};
    /// use circuitgame2_core::syntax::circuit::Head;
    ///
    /// let circuit = "; 猫\n(namespace app (func gate (in a) (out z) (def z (nor a a))))";
    /// let project = parse_project_sources(&[
    ///     SourceSnapshot { path: "tools.ncg2m", revision: 1, text: "" },
    ///     SourceSnapshot { path: "board.ncg2", revision: 7, text: circuit },
    /// ]).unwrap();
    /// let ProjectSourceIndex::Circuit(index) = &project.indexes()[1] else { panic!() };
    /// let entry = index.syntax.entries.iter().position(|item| item.head == Head::Func).unwrap();
    /// let site = project.func_callee_site(1, entry, 0, 0).unwrap();
    /// assert_eq!(&circuit[site.name.span], "nor");
    /// assert_eq!(site.source.revision, 7);
    /// assert_eq!(site.block, Some(0));
    /// assert!(project.func_callee_site(0, entry, 0, 0).is_none());
    /// ```
    pub fn func_callee_site(&self, file: usize, entry: usize, definition: usize, reference: usize)
        -> (result: Option<DefinitionReferenceSite<'_, 'a>>)
        ensures
            result.is_some() <==> self.has_func_callee(file, entry, definition, reference),
            result matches Some(site) ==> {
                let parsed = self.indexes_model()[file as int]->Circuit_0;
                let item = parsed.syntax.entries@[entry as int];
                let def = parsed.entry_ranges@[entry as int].definitions.start + definition;
                let reference_at = parsed.definitions@[def].references.start + reference;
                let indexed = parsed.references@[reference_at];
                &&& *site.source == self.sources_model()[file as int]
                &&& site.owner is Func && site.role is Callee && site.block == item.namespace
                &&& site.name.span == indexed.span
                &&& (bare_atom_kind(site.name.word.spec_bytes()) matches Some(kind) && reference_atom(kind))
                &&& (site.block matches Some(block) ==> exists|i: int| 0 <= i < parsed.names@.len() && {
                    let named = #[trigger] parsed.names@[i];
                    named.head is Namespace && named.form == block && named.block.is_none()
                })
                &&& {
                    let bytes = site.source.text_model().spec_bytes();
                    let start = site.name.span.start as int;
                    let end = site.name.span.end as int;
                    &&& 0 <= start < end <= bytes.len()
                    &&& is_char_boundary(bytes, start) && is_char_boundary(bytes, end)
                    &&& bytes[start..end] == site.name.word.spec_bytes()
                }
            },
    {
        let sources = self.sources();
        let indexes = self.indexes();
        if file >= sources.len() { return None; }
        let index = &indexes[file];
        let ProjectSourceIndex::Circuit(parsed) = index else { return None; };
        if entry >= parsed.syntax.entries.len() || entry >= parsed.entry_ranges.len() { return None; }
        let item = &parsed.syntax.entries[entry];
        if !matches!(item.head, Head::Func) { return None; }
        let source = &sources[file];
        let ghost model = parsed.build_model();
        proof {
            assert(project_source_index_matches(*source, *index));
            project_source_index_evidence(*source, *index);
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, entry as int);
        }
        let definitions = &parsed.entry_ranges[entry].definitions;
        if definition >= definitions.end - definitions.start { return None; }
        let def = definitions.start + definition;
        let references = &parsed.definitions[def].references;
        proof { build_definition_scope_evidence(source.text, &model, entry as int, def as int); }
        if reference >= references.end - references.start { return None; }
        let indexed = &parsed.references[references.start + reference];
        if !matches!(indexed.kind, ExpressionReferenceKind::Callee) { return None; }
        proof {
            source.text_model_is_text();
            assert(expression_reference_in_source(source.text, parsed.syntax.forms@, *indexed));
            if let Some(block) = item.namespace {
                namespace_name_evidence(source.text, parsed.syntax.forms@, parsed.syntax.entries@,
                    parsed.names@, item.form as int, block);
                let i = choose|i: int| 0 <= i < parsed.names@.len() && (#[trigger] parsed.names@[i]).form == block
                    && parsed.names@[i].head is Namespace && parsed.names@[i].block is None;
                assert(is_namespace_block(parsed.names@[i], block));
            }
        }
        let (word, span) = read_indexed_atom(source.text, &parsed.syntax.forms, indexed.form);
        Some(DefinitionReferenceSite {
            source,
            name: NameSite { word, span },
            role: indexed.kind,
            owner: item.head,
            block: item.namespace,
        })
    }
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// 混在ソース集合の `func` 本体から、呼び出し名を解決する。
    ///
    /// 無修飾名は呼び出し元のブロックの別名、同じ名前空間の宣言の順に探す。
    /// 束縛のない無修飾の `nor` は基底ゲートを指す。範囲外の添字や別用途の参照には `None` を返す。
    /// 相対パスは現在のスコープで先頭の名前を解決する。修飾名の末尾は共通宣言表を参照し、公開範囲を検査する。
    /// 基底宣言の件数はプロジェクト全体の検査で扱う。
    ///
    /// # Errors
    ///
    /// 参照先が見つからないか、参照先が回路関数でない場合は、元の呼び出し範囲と理由を返す。
    ///
    /// # Examples
    ///
    /// 別名 `nor` はそのブロックで優先する。同じ名前空間でも、別ブロックにある `nor` は基底ゲートを指す。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     MixedFuncCallee, MixedFuncCalleeError, ProjectSourceIndex, SourceSnapshot,
    ///     check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources,
    /// };
    /// use circuitgame2_core::syntax::circuit::Head;
    ///
    /// let circuit = "(using nor)
    ///     (namespace app
    ///         (use ::lib::ready nor)
    ///         (use ::lib tools)
    ///         (func first (in a) (out z) (def z (nor a a)))
    ///         (func relative (in a) (out z) (def z (tools::ready a a))))
    ///     (namespace app
    ///         (func second (in a) (out z) (def z (nor a a)))
    ///         (func absolute (in a) (out z) (def z (::nor a a))))";
    /// let meta = "(namespace lib (export ready) (defn ready (as-type (Fn () Bool) (fn () true))))";
    /// let project = parse_project_sources(&[
    ///     SourceSnapshot { path: "lib.ncg2m", revision: 2, text: meta },
    ///     SourceSnapshot { path: "board.ncg2", revision: 7, text: circuit },
    /// ]).unwrap();
    /// let targets = index_mixed_use_targets(&project).unwrap();
    /// let aliases = check_mixed_use_aliases(&targets).unwrap();
    /// let ProjectSourceIndex::Circuit(index) = &project.indexes()[1] else { panic!() };
    /// let mut functions = index.syntax.entries.iter().enumerate()
    ///     .filter(|(_, item)| item.head == Head::Func);
    /// let first = functions.next().unwrap().0;
    /// let relative = functions.next().unwrap().0;
    /// let second = functions.next().unwrap().0;
    /// let absolute = functions.next().unwrap().0;
    /// let result = aliases.resolve_mixed_func_callee(1, first, 0, 0).unwrap();
    /// let Err(MixedFuncCalleeError::WrongDeclaration(target)) = result.target else { panic!() };
    /// assert_eq!(&circuit[result.site.name.span], "nor");
    /// assert_eq!(&meta[target.name.span], "ready");
    /// assert!(matches!(aliases.resolve_mixed_func_callee(1, second, 0, 0).unwrap().target,
    ///     Ok(MixedFuncCallee::Nor)));
    /// assert!(matches!(aliases.resolve_mixed_func_callee(1, relative, 0, 0).unwrap().target,
    ///     Err(MixedFuncCalleeError::WrongDeclaration(_))));
    /// assert!(matches!(aliases.resolve_mixed_func_callee(1, absolute, 0, 0).unwrap().target,
    ///     Err(MixedFuncCalleeError::Missing)));
    /// ```
    pub fn resolve_mixed_func_callee(&self, file: usize, entry: usize, definition: usize, reference: usize)
        -> (result: Option<MixedFuncCalleeResolution<'p, 'a>>)
        ensures
            result.is_some() <==> self.targets_model().project_model().has_func_callee(file, entry, definition, reference),
            self.mixed_func_callee_matches(file, entry, definition, reference, result),
    {
        let project = self.targets().project();
        let Some(site) = project.func_callee_site(file, entry, definition, reference) else { return None; };
        let word = site.name.word;
        let indexes = project.indexes();
        let ProjectSourceIndex::Circuit(parsed) = &indexes[file] else {
            proof { assert(false); }
            unreachable!()
        };
        let namespace = if let Some(block) = site.block {
            let name = find_namespace(parsed, block);
            proof { assert(name.is_some()); }
            name
        } else { None };
        let scope = DefnScope { block: site.block, namespace };
        let exports = self.targets().exports();
        let target = match classify_bare_atom(word) {
            Some(AtomKind::Name) => {
                let binding = self.binding_for_call(file, scope, word);
                let ghost selected = binding;
                let result = match binding {
                    Some(target) => checked_func_target(Ok(target)),
                    None if word == "nor" => Ok(MixedFuncCallee::Nor),
                    None => Err(MixedFuncCalleeError::Missing),
                };
                assert(unqualified_func_target(word, selected, result));
                result
            },
            Some(AtomKind::AbsolutePath) => {
                let absolute = exports.resolve_absolute(word, namespace);
                checked_func_target(absolute)
            },
            Some(AtomKind::RelativePath) => {
                let Some((head, middle, last)) = split_relative_path(word) else {
                    proof { assert(false); }
                    unreachable!()
                };
                let binding = self.binding_for_call(file, scope, head);
                let ghost selected = binding;
                let result = match binding {
                    None => Err(MixedFuncCalleeError::MissingPrefix),
                    Some(MixedAbsoluteTarget::Declaration(declaration)) => Err(MixedFuncCalleeError::DeclarationPrefix(declaration)),
                    Some(MixedAbsoluteTarget::Namespace { key, .. }) => {
                        let parent = destination_parent(key, middle);
                        let path = NameKey { parent: Some(parent.as_str()), name: last };
                        let absolute = exports.resolve_mixed_key(path, namespace);
                        let result = checked_func_target(absolute);
                        assert(func_target_in_scope(self, file, scope, word, result));
                        result
                    },
                };
                assert(scoped_binding(self, file, scope, head, selected));
                result
            },
            _ => { proof { assert(false); } unreachable!() },
        };
        assert(func_target_in_scope(self, file, scope, word, target));
        Some(MixedFuncCalleeResolution { site, target })
    }

    /// 呼び出しの結果が元の索引位置と同じスコープの束縛に対応することを表す。
    pub closed spec fn mixed_func_callee_matches(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        result: Option<MixedFuncCalleeResolution>,
    ) -> bool {
        let project = self.targets_model().project_model();
        if !project.has_func_callee(file, entry, definition, reference) {
            result.is_none()
        } else {
            let parsed = project.indexes_model()[file as int]->Circuit_0;
            let item = parsed.syntax.entries@[entry as int];
            let def = parsed.entry_ranges@[entry as int].definitions.start + definition;
            let indexed = parsed.references@[parsed.definitions@[def].references.start + reference];
            let source = &project.sources_model()[file as int];
            let text = source.text_model().spec_bytes();
            let bytes = text[indexed.span.start as int..indexed.span.end as int];
            result matches Some(resolved) && {
                let site = resolved.site;
                &&& *site.source == *source && site.name.span == indexed.span && site.name.word.spec_bytes() == bytes
                &&& site.owner is Func && site.role is Callee && site.block == item.namespace
                &&& exists|namespace: Option<&str>| {
                    &&& func_scope_path(&parsed, site.block, namespace)
                    &&& #[trigger] func_target_in_scope(self, file, DefnScope { block: site.block, namespace }, site.name.word, resolved.target)
                }
            }
        }
    }

    /// 基底 NOR が無修飾の `nor` で、参照元に同名の束縛がないことを示す。
    #[verifier::spinoff_prover]
    pub proof fn mixed_nor_has_no_binding(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        resolved: MixedFuncCalleeResolution<'p, 'a>,
    ) -> (namespace: Option<&'a str>)
        requires
            self.mixed_func_callee_matches(file, entry, definition, reference, Some(resolved)),
            resolved.target matches Ok(MixedFuncCallee::Nor),
        ensures
            resolved.site.name.word@ == "nor"@,
            bare_atom_kind(resolved.site.name.word.spec_bytes()) == Some(AtomKind::Name),
            match resolved.site.block {
                None => namespace.is_none(),
                Some(block) => {
                    let parsed = self.targets_model().project_model().indexes_model()[file as int]->Circuit_0;
                    exists|i: int| 0 <= i < parsed.names@.len() && {
                        let named = #[trigger] parsed.names@[i];
                        named.head is Namespace && named.form == block && named.block.is_none()
                            && namespace == Some(named.name.word)
                    }
                },
            },
            self.first_alias_matches(file, resolved.site.block, resolved.site.name.word, None),
            !self.targets_model().exports_model().declarations_model().declares(NameKey { parent: namespace, name: resolved.site.name.word }),
            !self.targets_model().exports_model().declarations_model().has_namespace(NameKey { parent: namespace, name: resolved.site.name.word }),
    {
        let site = resolved.site;
        let word = site.name.word;
        let parsed = self.targets_model().project_model().indexes_model()[file as int]->Circuit_0;
        let namespace = choose|namespace: Option<&str>|
            func_scope_path(&parsed, site.block, namespace)
                && #[trigger] func_target_in_scope(self, file, DefnScope { block: site.block, namespace }, word, resolved.target);
        let scope = DefnScope { block: site.block, namespace };
        match bare_atom_kind(word.spec_bytes()) {
            Some(AtomKind::Name) => {
                let binding = choose|binding: Option<MixedAbsoluteTarget>|
                    #[trigger] scoped_binding(self, file, scope, word, binding)
                        && unqualified_func_target(word, binding, resolved.target);
                assert(binding.is_none());
                if !self.first_alias_matches(file, site.block, word, None) {
                    let rows = self.targets_model().directives_model();
                    let i = choose|i: usize| #[trigger] self.first_alias_matches(file, site.block, word, Some(i))
                        && i < rows.len() && binding == Some(rows[i as int].target);
                    assert(false);
                }
            },
            Some(AtomKind::AbsolutePath) => {
                let absolute = choose|absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                    #[trigger] mixed_absolute_resolution_evidence(&self.targets_model().exports_model(), word, namespace, absolute)
                        && qualified_func_target(absolute, resolved.target);
                assert(false);
            },
            Some(AtomKind::RelativePath) => {
                // 修飾名は共有宣言表で解決する。
                assert(false);
            },
            _ => assert(false),
        }
        namespace
    }
}

} // verus!
