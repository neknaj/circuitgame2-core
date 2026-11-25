//! 混在ソース集合の厳格索引から、関数の呼び出し位置を確定する。

use super::{MixedUseAliases, definitions::DefinitionReferenceSite, find_namespace};
#[cfg(verus_only)]
use super::{defn_name::scoped_binding, is_namespace_block};
use crate::project::circuits::read_indexed_atom;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::project::source_indexes::{project_source_index_evidence, project_source_index_matches};
use crate::project::source_indexes::DefnScope;
use crate::project::{LocatedName, MixedAbsoluteTarget, ParsedProjectSources, ProjectDeclaration, ProjectDeclarationKind, ProjectSourceIndex};
use crate::syntax::{AtomKind, classify_bare_atom};
#[cfg(verus_only)]
use crate::syntax::bare_atom_kind;
use crate::syntax::circuit::{ExpressionReferenceKind, Head, NameSite};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    build_definition_scope_evidence, build_entry_ranges_evidence, expression_reference_in_source, namespace_name_evidence,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::is_char_boundary};

verus! {

/// `func` の無修飾の呼び出し名が指す対象。
#[derive(Debug)]
pub enum MixedFuncCallee<'p, 'a> {
    /// 混在宣言表にある回路関数。
    Function(ProjectDeclaration<'p, 'a>),
    /// 同じスコープに束縛がないときに選ぶ基底ゲート。
    Nor,
}

/// `func` の無修飾の呼び出し名を解決できなかった理由。
#[derive(Debug)]
pub enum MixedFuncCalleeError<'p, 'a> {
    /// スコープに呼び出し先が見つからない。
    Missing,
    /// 呼び出し名が名前空間を指す。値はその名前空間の宣言位置。
    Namespace(LocatedName<'p, 'a>),
    /// 回路関数以外の宣言が選ばれた。
    WrongDeclaration(ProjectDeclaration<'p, 'a>),
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
        Some(MixedAbsoluteTarget::Declaration(declaration)) => {
            if declaration.kind == ProjectDeclarationKind::Circuit(Head::Func) {
                result == Ok(MixedFuncCallee::Function(declaration))
            } else {
                result == Err(MixedFuncCalleeError::WrongDeclaration(declaration))
            }
        },
        Some(MixedAbsoluteTarget::Namespace { introduced_at, .. }) =>
            result == Err(MixedFuncCalleeError::Namespace(introduced_at)),
        None => if word@ == "nor"@ {
            result == Ok(MixedFuncCallee::Nor)
        } else {
            result == Err(MixedFuncCalleeError::Missing)
        },
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
    /// 混在ソース集合の `func` 本体から、無修飾の呼び出し名を解決する。
    ///
    /// 呼び出し元のブロックで別名を探し、なければ同じ名前空間の宣言を探す。
    /// 束縛のない `nor` は基底ゲートを指す。範囲外の添字、別用途の参照、修飾名には `None` を返す。
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
    ///     (namespace app (use ::lib::ready nor) (func first (in a) (out z) (def z (nor a a))))
    ///     (namespace app (func second (in a) (out z) (def z (nor a a))))";
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
    /// let second = functions.next().unwrap().0;
    /// let result = aliases.resolve_unqualified_func_callee(1, first, 0, 0).unwrap();
    /// let Err(MixedFuncCalleeError::WrongDeclaration(target)) = result.target else { panic!() };
    /// assert_eq!(&circuit[result.site.name.span], "nor");
    /// assert_eq!(&meta[target.name.span], "ready");
    /// assert!(matches!(aliases.resolve_unqualified_func_callee(1, second, 0, 0).unwrap().target,
    ///     Ok(MixedFuncCallee::Nor)));
    /// ```
    pub fn resolve_unqualified_func_callee(&self, file: usize, entry: usize, definition: usize, reference: usize)
        -> (result: Option<MixedFuncCalleeResolution<'p, 'a>>)
        ensures self.unqualified_func_callee_matches(file, entry, definition, reference, result),
    {
        let project = self.targets().project();
        let Some(site) = project.func_callee_site(file, entry, definition, reference) else { return None; };
        let word = site.name.word;
        if !matches!(classify_bare_atom(word), Some(AtomKind::Name)) { return None; }
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
        let binding = self.binding_for_call(file, scope, word);
        let ghost selected = binding;
        let target = match binding {
            Some(MixedAbsoluteTarget::Declaration(declaration)) => {
                if matches!(declaration.kind, ProjectDeclarationKind::Circuit(Head::Func)) {
                    Ok(MixedFuncCallee::Function(declaration))
                } else { Err(MixedFuncCalleeError::WrongDeclaration(declaration)) }
            },
            Some(MixedAbsoluteTarget::Namespace { introduced_at, .. }) => Err(MixedFuncCalleeError::Namespace(introduced_at)),
            None if word == "nor" => Ok(MixedFuncCallee::Nor),
            None => Err(MixedFuncCalleeError::Missing),
        };
        assert(unqualified_func_target(word, selected, target));
        Some(MixedFuncCalleeResolution { site, target })
    }

    /// 無修飾の呼び出しの結果が元の索引位置と同じスコープの束縛に対応することを表す。
    pub closed spec fn unqualified_func_callee_matches(
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
            if bare_atom_kind(bytes) != Some(AtomKind::Name) {
                result.is_none()
            } else {
                result matches Some(resolved) && {
                    let site = resolved.site;
                    &&& *site.source == *source && site.name.span == indexed.span && site.name.word.spec_bytes() == bytes
                    &&& site.owner is Func && site.role is Callee && site.block == item.namespace
                    &&& exists|namespace: Option<&str>, binding: Option<MixedAbsoluteTarget>| {
                        &&& match site.block {
                            None => namespace.is_none(),
                            Some(block) => exists|i: int| 0 <= i < parsed.names@.len()
                                && #[trigger] is_namespace_block(parsed.names@[i], block)
                                && namespace == Some(parsed.names@[i].name.word),
                        }
                        &&& #[trigger] scoped_binding(self, file, DefnScope { block: site.block, namespace }, site.name.word, binding)
                        &&& unqualified_func_target(site.name.word, binding, resolved.target)
                    }
                }
            }
        }
    }
}

} // verus!
