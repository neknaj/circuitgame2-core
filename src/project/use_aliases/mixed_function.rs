//! 混在ソース集合の厳格索引から、関数の呼び出し位置を確定する。

mod typed;
pub use typed::{MixedFuncDriverError, MixedTypedSignatureError};

use super::{MixedUseAliases, call_arity::{FuncCallArity, FuncCallTarget}, definitions::DefinitionReferenceSite,
    find_namespace, relative::destination_parent};
#[cfg(verus_only)]
use super::{defn_name::{absolute_name_declares, scoped_binding}, is_namespace_block, relative::parent_spelling};
use crate::project::circuits::read_indexed_atom;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::project::source_indexes::{project_source_index_evidence, project_source_index_matches};
use crate::project::source_indexes::DefnScope;
use crate::project::{AbsoluteResolutionError, LocatedName, MixedAbsoluteTarget, NameKey, ParsedProjectSources,
    ProjectDeclaration, ProjectDeclarationKind, ProjectSourceIndex};
#[cfg(verus_only)]
use crate::project::{exports::mixed_exports_use_project_declarations, mixed_absolute_resolution_evidence,
    mixed_declaration_origin, mixed_key_resolution, mixed_use_targets_match};
use crate::syntax::{AtomKind, classify_bare_atom, split_relative_path};
#[cfg(verus_only)]
use crate::syntax::{bare_atom_kind, relative_path_parts};
use crate::syntax::circuit::{CallShape, ExpressionReferenceKind, Head, NameSite, indexed_call_shape, named_build_entry, routine_arity};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    NamedBuildCircuit, build_definition_scope_evidence, build_entry_ranges_evidence, call_shape_matches,
    expression_reference_in_source, namespace_name_evidence, reference_atom, routine_arity_matches,
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

/// 混在プロジェクトで、回路の参照が必要な宣言を指さなかった理由。
#[derive(Debug)]
pub enum MixedFuncCalleeError<'p, 'a> {
    /// スコープに参照先が見つからない。
    Missing,
    /// 相対パスの先頭に対応する名前空間または別名がない。
    MissingPrefix,
    /// 相対パスの先頭が宣言を指すため、その内側をたどれない。
    DeclarationPrefix(ProjectDeclaration<'p, 'a>),
    /// 別の名前空間にある非公開宣言の位置。
    Private(LocatedName<'p, 'a>),
    /// 参照名が名前空間を指す。値はその名前空間の宣言位置。
    Namespace(LocatedName<'p, 'a>),
    /// 使用箇所が要求する種別と異なる宣言が選ばれた。
    WrongDeclaration(ProjectDeclaration<'p, 'a>),
}

spec fn scoped_absolute_result(
    absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>,
    expected: Head, result: Result<Option<ProjectDeclaration>, MixedFuncCalleeError>,
) -> bool {
    match absolute {
        Ok(MixedAbsoluteTarget::Declaration(declaration)) => {
            if declaration.kind == ProjectDeclarationKind::Circuit(expected) {
                result == Ok(Some(declaration))
            } else {
                result == Err(MixedFuncCalleeError::WrongDeclaration(declaration))
            }
        },
        Ok(MixedAbsoluteTarget::Namespace { introduced_at, .. }) => result == Err(MixedFuncCalleeError::Namespace(introduced_at)),
        Err(AbsoluteResolutionError::Private(location)) => result == Err(MixedFuncCalleeError::Private(location)),
        Err(_) => result == Err(MixedFuncCalleeError::Missing),
    }
}

fn checked_scoped_target<'p, 'a>(absolute: Result<MixedAbsoluteTarget<'p, 'a, '_>, AbsoluteResolutionError<'p, 'a>>, expected: Head)
    -> (result: Result<Option<ProjectDeclaration<'p, 'a>>, MixedFuncCalleeError<'p, 'a>>)
    requires expected is Func || expected is Struct,
    ensures scoped_absolute_result(absolute, expected, result),
{
    match absolute {
        Ok(MixedAbsoluteTarget::Declaration(declaration)) => match (declaration.kind, expected) {
            (ProjectDeclarationKind::Circuit(Head::Func), Head::Func)
                | (ProjectDeclarationKind::Circuit(Head::Struct), Head::Struct) => Ok(Some(declaration)),
            _ => Err(MixedFuncCalleeError::WrongDeclaration(declaration)),
        },
        Ok(MixedAbsoluteTarget::Namespace { introduced_at, .. }) => Err(MixedFuncCalleeError::Namespace(introduced_at)),
        Err(AbsoluteResolutionError::Private(location)) => Err(MixedFuncCalleeError::Private(location)),
        Err(_) => Err(MixedFuncCalleeError::Missing),
    }
}

spec fn scoped_circuit_name_matches(
    aliases: &MixedUseAliases, file: usize, scope: DefnScope, word: &str, expected: Head,
    result: Result<Option<ProjectDeclaration>, MixedFuncCalleeError>,
) -> bool {
    let exports = aliases.targets_model().exports_model();
    match bare_atom_kind(word.spec_bytes()) {
        Some(AtomKind::Name) => exists|binding: Option<MixedAbsoluteTarget>|
            #[trigger] scoped_binding(aliases, file, scope, word, binding)
                && match binding {
                    None => result == Ok(None),
                    Some(target) => scoped_absolute_result(Ok(target), expected, result),
                },
        Some(AtomKind::AbsolutePath) => exists|absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
            #[trigger] mixed_absolute_resolution_evidence(&exports, word, scope.namespace, absolute)
                && scoped_absolute_result(absolute, expected, result),
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
                                && scoped_absolute_result(absolute, expected, result),
                },
        _ => false,
    }
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

spec fn func_result<'p, 'a>(word: &str, binding: Result<Option<ProjectDeclaration<'p, 'a>>, MixedFuncCalleeError<'p, 'a>>)
    -> Result<MixedFuncCallee<'p, 'a>, MixedFuncCalleeError<'p, 'a>>
{
    match binding {
        Ok(Some(declaration)) => Ok(MixedFuncCallee::Function(declaration)),
        Ok(None) if word@ == "nor"@ => Ok(MixedFuncCallee::Nor),
        Ok(None) => Err(MixedFuncCalleeError::Missing),
        Err(error) => Err(error),
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

/// 混在プロジェクトの関数呼び出しで名前を解決できなかった理由と元の位置。
#[derive(Debug)]
pub struct MixedFuncCallError<'p, 'a> {
    /// 呼び出し名の範囲と元の文書版。
    pub site: DefinitionReferenceSite<'p, 'a>,
    /// 参照先を選べなかった理由。
    pub reason: MixedFuncCalleeError<'p, 'a>,
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

#[verifier::spinoff_prover]
proof fn function_result_follows_scope(
    aliases: &MixedUseAliases, file: usize, scope: DefnScope, word: &str,
    selected: Result<Option<ProjectDeclaration>, MixedFuncCalleeError>,
)
    requires scoped_circuit_name_matches(aliases, file, scope, word, Head::Func, selected),
    ensures func_target_in_scope(aliases, file, scope, word, func_result(word, selected)),
{
    let exports = aliases.targets_model().exports_model();
    let result = func_result(word, selected);
    match bare_atom_kind(word.spec_bytes()) {
        Some(AtomKind::Name) => {
            let binding = choose|binding: Option<MixedAbsoluteTarget>|
                #[trigger] scoped_binding(aliases, file, scope, word, binding)
                    && match binding {
                        None => selected == Ok(None),
                        Some(target) => scoped_absolute_result(Ok(target), Head::Func, selected),
                    };
            assert(unqualified_func_target(word, binding, result));
        },
        Some(AtomKind::AbsolutePath) => {
            let absolute = choose|absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                #[trigger] mixed_absolute_resolution_evidence(&exports, word, scope.namespace, absolute)
                    && scoped_absolute_result(absolute, Head::Func, selected);
            assert(qualified_func_target(absolute, result));
        },
        Some(AtomKind::RelativePath) => {
            let (head, middle, last, binding) = choose|head: &str, middle: Option<&str>, last: &str, binding: Option<MixedAbsoluteTarget>|
                #[trigger] relative_path_parts(word, head, middle, last)
                    && #[trigger] scoped_binding(aliases, file, scope, head, binding)
                    && match binding {
                        None => selected == Err(MixedFuncCalleeError::MissingPrefix),
                        Some(MixedAbsoluteTarget::Declaration(declaration)) =>
                            selected == Err(MixedFuncCalleeError::DeclarationPrefix(declaration)),
                        Some(MixedAbsoluteTarget::Namespace { key, .. }) =>
                            exists|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                                parent@ == parent_spelling(key, middle)
                                    && #[trigger] mixed_key_resolution(&exports, NameKey { parent: Some(parent), name: last }, scope.namespace, absolute)
                                    && scoped_absolute_result(absolute, Head::Func, selected),
                    };
            if let Some(MixedAbsoluteTarget::Namespace { key, .. }) = binding {
                let (parent, absolute) = choose|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                    parent@ == parent_spelling(key, middle)
                        && #[trigger] mixed_key_resolution(&exports, NameKey { parent: Some(parent), name: last }, scope.namespace, absolute)
                        && scoped_absolute_result(absolute, Head::Func, selected);
                assert(qualified_func_target(absolute, result));
            }
        },
        _ => assert(false),
    }
}

spec fn selected_func_arity_matches(project: &ParsedProjectSources, target: MixedFuncCallee, found: FuncCallTarget) -> bool {
    match (target, found) {
        (MixedFuncCallee::Nor, FuncCallTarget::Nor) => true,
        (MixedFuncCallee::Function(selected), FuncCallTarget::Function { arity, declaration, file, entry }) => {
            &&& file == selected.file && declaration == selected.name
            &&& file < project.indexes_model().len()
            &&& project.indexes_model()[file as int] matches ProjectSourceIndex::Circuit(parsed)
            &&& entry < parsed.syntax.entries@.len() && selected.item < parsed.names@.len()
            &&& parsed.syntax.entries@[entry as int].head is Func
            &&& parsed.syntax.entries@[entry as int].form == parsed.names@[selected.item as int].form
            &&& routine_arity_matches(declaration.source.text_model(), &parsed.syntax, entry as int, Some(arity))
        },
        _ => false,
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

    spec fn indexed_func_shape_matches(&self, file: usize, entry: usize, definition: usize, reference: usize, call: CallShape) -> bool {
        let parsed = self.indexes_model()[file as int]->Circuit_0;
        let def = parsed.entry_ranges@[entry as int].definitions.start + definition;
        let row = parsed.definitions@[def];
        let indexed = parsed.references@[row.references.start + reference];
        &&& self.has_func_callee(file, entry, definition, reference)
        &&& call_shape_matches(self.sources_model()[file as int].text_model(), parsed.syntax.forms@, row, indexed, Some(call))
    }

    fn indexed_func_shape(&self, file: usize, entry: usize, definition: usize, reference: usize) -> (call: CallShape)
        requires self.has_func_callee(file, entry, definition, reference),
        ensures self.indexed_func_shape_matches(file, entry, definition, reference, call),
    {
        let source = &self.sources()[file];
        let index = &self.indexes()[file];
        let ProjectSourceIndex::Circuit(parsed) = index else {
            proof { assert(false); }
            unreachable!()
        };
        let ghost model = parsed.build_model();
        proof {
            source.text_model_is_text();
            project_source_index_evidence(*source, *index);
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, entry as int);
        }
        let def = parsed.entry_ranges[entry].definitions.start + definition;
        let row = &parsed.definitions[def];
        proof { build_definition_scope_evidence(source.text, &model, entry as int, def as int); }
        let shape = indexed_call_shape(source.text, &parsed.syntax.forms, row, &parsed.references, row.references.start + reference);
        let Some(call) = shape else { proof { assert(false); } unreachable!() };
        call
    }
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// 関数の呼び出し名を解決し、直接の実引数数と参照先の入出力ポート数を返す。
    ///
    /// 添字は [`Self::resolve_mixed_func_callee`] と同じ。対象の呼び出しがない場合は `None` を返す。
    /// 入出力の型は後段で検査する。
    ///
    /// # Errors
    ///
    /// 名前解決の違反には呼び出し名の範囲が付く。参照先が特定できた場合は、その位置も返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     FuncArityError, FuncCallTarget, ProjectSourceIndex, SourceSnapshot, check_mixed_use_aliases,
    ///     index_mixed_use_targets, parse_project_sources,
    /// };
    ///
    /// let circuit = "(using nor)
    ///     (func invert (in x) (out y) (def y (nor x x)))
    ///     (func caller (in a) (out z) (def z (::invert (nor a a))))
    ///     (func bad (in a) (out z) (def z (::invert a a)))";
    /// let project = parse_project_sources(&[
    ///     SourceSnapshot { path: "helpers.ncg2m", revision: 1, text: "" },
    ///     SourceSnapshot { path: "design.ncg2", revision: 3, text: circuit },
    /// ]).unwrap();
    /// let targets = index_mixed_use_targets(&project).unwrap();
    /// let aliases = check_mixed_use_aliases(&targets).unwrap();
    /// let ProjectSourceIndex::Circuit(index) = &project.indexes()[1] else { panic!() };
    /// let caller = index.names.iter().find(|site| site.name.word == "caller").unwrap();
    /// let entry = index.syntax.entries.iter().position(|item| item.form == caller.form).unwrap();
    /// let call = aliases.resolve_mixed_func_call_arity(1, entry, 0, 0).unwrap().unwrap()
    ///     .check_input_count().unwrap();
    /// let FuncCallTarget::Function { arity, declaration, file, .. } = call.target else { panic!() };
    /// assert_eq!(&circuit[declaration.span], "invert");
    /// assert_eq!((file, arity.inputs, arity.outputs), (1, 1, 1));
    /// assert_eq!(call.call.arguments, 1);
    /// assert_eq!(&circuit[call.call.span], "(::invert (nor a a))");
    /// let nested = aliases.resolve_mixed_func_call_arity(1, entry, 0, 1).unwrap().unwrap();
    /// assert!(matches!(nested.target, FuncCallTarget::Nor));
    /// assert_eq!(nested.call.arguments, 2);
    /// let bad = index.names.iter().find(|site| site.name.word == "bad").unwrap();
    /// let entry = index.syntax.entries.iter().position(|item| item.form == bad.form).unwrap();
    /// let wrong = aliases.resolve_mixed_func_call_arity(1, entry, 0, 0).unwrap().unwrap();
    /// let Err(FuncArityError::ArgumentCount { call, expected, actual, .. }) = wrong.check_input_count()
    ///     else { panic!() };
    /// assert_eq!((expected, actual), (1, 2));
    /// assert_eq!(&circuit[call.span], "(::invert a a)");
    /// ```
    pub fn resolve_mixed_func_call_arity(&self, file: usize, entry: usize, definition: usize, reference: usize)
        -> (result: Option<Result<FuncCallArity<'p, 'a>, MixedFuncCallError<'p, 'a>>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures
            result.is_some() <==> self.targets_model().project_model().has_func_callee(file, entry, definition, reference),
            self.mixed_func_call_arity_matches(file, entry, definition, reference, result),
    {
        let Some(resolved) = self.resolve_mixed_func_callee(file, entry, definition, reference) else { return None; };
        let ghost named = resolved;
        let MixedFuncCalleeResolution { site, target } = resolved;
        let project = self.targets().project();
        let selected = match target {
            Ok(selected) => selected,
            Err(reason) => return Some(Err(MixedFuncCallError { site, reason })),
        };
        let call = project.indexed_func_shape(file, entry, definition, reference);
        let ghost before = selected;
        let target = match selected {
            MixedFuncCallee::Nor => FuncCallTarget::Nor,
            MixedFuncCallee::Function(declaration) => {
                proof { self.mixed_function_callee_origin(file, entry, definition, reference, named, declaration); }
                let index = &project.indexes()[declaration.file];
                let ProjectSourceIndex::Circuit(parsed) = index else { proof { assert(false); } unreachable!() };
                let source = declaration.name.source;
                proof {
                    source.text_model_is_text();
                    project_source_index_evidence(*source, *index);
                    parsed_index_evidence(*source, *parsed);
                }
                let entry = named_build_entry(source.text, parsed, declaration.item);
                let Some(arity) = routine_arity(source.text, &parsed.syntax, entry) else { proof { assert(false); } unreachable!() };
                FuncCallTarget::Function { arity, declaration: declaration.name, file: declaration.file, entry }
            },
        };
        assert(selected_func_arity_matches(project, before, target));
        Some(Ok(FuncCallArity { source: site.source, call, target }))
    }

    /// 個数が元の呼び出し構文と名前解決で選ばれた宣言の署名に対応することを表す。
    pub closed spec fn mixed_func_call_arity_matches(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        result: Option<Result<FuncCallArity, MixedFuncCallError>>,
    ) -> bool {
        let project = self.targets_model().project_model();
        match result {
            None => !project.has_func_callee(file, entry, definition, reference),
            Some(Err(error)) => self.mixed_func_callee_matches(file, entry, definition, reference,
                Some(MixedFuncCalleeResolution { site: error.site, target: Err(error.reason) })),
            Some(Ok(call)) => project.indexed_func_shape_matches(file, entry, definition, reference, call.call)
                && exists|resolved: MixedFuncCalleeResolution| {
                    &&& #[trigger] self.mixed_func_callee_matches(file, entry, definition, reference, Some(resolved))
                    &&& *call.source == *resolved.site.source
                    &&& resolved.target matches Ok(target)
                    &&& selected_func_arity_matches(&project, target, call.target)
                },
        }
    }

    /// 実引数数とポート数が由来する、呼び出し元と宣言先の厳格索引を示す。
    #[verifier::spinoff_prover]
    pub proof fn mixed_func_call_arity_origin(
        &self, file: usize, entry: usize, definition: usize, reference: usize, call: FuncCallArity<'p, 'a>,
    )
        requires
            self.mixed_func_call_arity_matches(file, entry, definition, reference, Some(Ok(call))),
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures ({
            let project = self.targets_model().project_model();
            &&& project.has_func_callee(file, entry, definition, reference)
            &&& *call.source == project.sources_model()[file as int]
            &&& {
                let parsed = project.indexes_model()[file as int]->Circuit_0;
                let def = parsed.entry_ranges@[entry as int].definitions.start + definition;
                let row = parsed.definitions@[def];
                let indexed = parsed.references@[row.references.start + reference];
                call_shape_matches(call.source.text_model(), parsed.syntax.forms@, row, indexed, Some(call.call))
            }
            &&& call.target matches FuncCallTarget::Function { arity, declaration, file: target_file, entry: target_entry }
                ==> {
                    &&& target_file < project.sources_model().len()
                    &&& *declaration.source == project.sources_model()[target_file as int]
                    &&& project.indexes_model()[target_file as int] matches ProjectSourceIndex::Circuit(parsed)
                    &&& target_entry < parsed.syntax.entries@.len()
                    &&& parsed.syntax.entries@[target_entry as int].head is Func
                    &&& routine_arity_matches(declaration.source.text_model(), &parsed.syntax, target_entry as int, Some(arity))
                    &&& exists|i: int| 0 <= i < parsed.names@.len() && {
                        let named = #[trigger] parsed.names@[i];
                        &&& named.head is Func
                        &&& named.form == parsed.syntax.entries@[target_entry as int].form
                        &&& named.name.span == declaration.span
                    }
                }
        }),
    {
        let resolved = choose|resolved: MixedFuncCalleeResolution| {
            &&& #[trigger] self.mixed_func_callee_matches(file, entry, definition, reference, Some(resolved))
            &&& *call.source == *resolved.site.source
            &&& resolved.target matches Ok(target)
            &&& selected_func_arity_matches(&self.targets_model().project_model(), target, call.target)
        };
        if let FuncCallTarget::Function { .. } = call.target {
            self.mixed_function_callee_origin(file, entry, definition, reference, resolved, resolved.target->Ok_0->Function_0);
        }
    }

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
        let binding = self.resolve_scoped_circuit_name(file, scope, word, Head::Func);
        proof { function_result_follows_scope(self, file, scope, word, binding); }
        let target = match binding {
            Ok(Some(declaration)) => Ok(MixedFuncCallee::Function(declaration)),
            Ok(None) if word == "nor" => Ok(MixedFuncCallee::Nor),
            Ok(None) => Err(MixedFuncCalleeError::Missing),
            Err(error) => Err(error),
        };
        Some(MixedFuncCalleeResolution { site, target })
    }

    // 名前の探索と公開範囲は呼び出し名と型名で共用する。
    fn resolve_scoped_circuit_name(&self, file: usize, scope: DefnScope<'a>, word: &str, expected: Head)
        -> (result: Result<Option<ProjectDeclaration<'p, 'a>>, MixedFuncCalleeError<'p, 'a>>)
        requires
            bare_atom_kind(word.spec_bytes()) matches Some(kind) && reference_atom(kind),
            expected is Func || expected is Struct,
        ensures scoped_circuit_name_matches(self, file, scope, word, expected, result),
    {
        let exports = self.targets().exports();
        match classify_bare_atom(word) {
            Some(AtomKind::Name) => {
                let binding = self.binding_for_call(file, scope, word);
                match binding {
                    Some(target) => checked_scoped_target(Ok(target), expected),
                    None => Ok(None),
                }
            },
            Some(AtomKind::AbsolutePath) => {
                let absolute = exports.resolve_absolute(word, scope.namespace);
                checked_scoped_target(absolute, expected)
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
                        let absolute = exports.resolve_mixed_key(path, scope.namespace);
                        let result = checked_scoped_target(absolute, expected);
                        assert(scoped_circuit_name_matches(self, file, scope, word, expected, result));
                        result
                    },
                };
                assert(scoped_binding(self, file, scope, head, selected));
                result
            },
            _ => { proof { assert(false); } unreachable!() },
        }
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

    /// 解決した関数が同じソース集合の宣言を指し、宣言名が厳格索引にあることを示す。
    #[verifier::spinoff_prover]
    pub proof fn mixed_function_callee_origin(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        resolved: MixedFuncCalleeResolution<'p, 'a>, declaration: ProjectDeclaration<'p, 'a>,
    )
        requires
            self.mixed_func_callee_matches(file, entry, definition, reference, Some(resolved)),
            resolved.target == Ok(MixedFuncCallee::Function(declaration)),
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures
            declaration.kind == ProjectDeclarationKind::Circuit(Head::Func),
            ({
                let project = self.targets_model().project_model();
                &&& declaration.file < project.sources_model().len()
                &&& declaration.file < project.indexes_model().len()
                &&& *declaration.name.source == project.sources_model()[declaration.file as int]
                &&& project.indexes_model()[declaration.file as int] matches ProjectSourceIndex::Circuit(circuit)
                &&& declaration.item < circuit.names@.len()
                &&& circuit.names@[declaration.item as int].head is Func
                &&& declaration.name.span == circuit.names@[declaration.item as int].name.span
            }),
    {
        let targets = self.targets_model();
        let project = targets.project_model();
        let exports = targets.exports_model();
        let declarations = exports.declarations_model();
        let site = resolved.site;
        let word = site.name.word;
        let parsed = project.indexes_model()[file as int]->Circuit_0;
        let namespace = choose|namespace: Option<&str>| func_scope_path(&parsed, site.block, namespace)
            && #[trigger] func_target_in_scope(self, file, DefnScope { block: site.block, namespace }, word, resolved.target);
        let scope = DefnScope { block: site.block, namespace };
        let target = Ok(MixedAbsoluteTarget::Declaration(declaration));
        match bare_atom_kind(word.spec_bytes()) {
            Some(AtomKind::Name) => {
                let binding = choose|binding: Option<MixedAbsoluteTarget>|
                    #[trigger] scoped_binding(self, file, scope, word, binding)
                        && unqualified_func_target(word, binding, resolved.target);
                assert(binding == Some(MixedAbsoluteTarget::Declaration(declaration)));
                if self.first_alias_matches(file, site.block, word, None) {
                    assert(declarations.declaration_at(NameKey { parent: namespace, name: word }, declaration));
                } else {
                    let rows = targets.directives_model();
                    let rank = choose|rank: usize| #[trigger] self.first_alias_matches(file, site.block, word, Some(rank))
                        && rank < rows.len() && binding == Some(rows[rank as int].target);
                    targets.directive_origin(rank as int);
                    let row = rows[rank as int];
                    absolute_name_declares(&exports, row.site.reference.word, row.site.namespace, declaration);
                }
            },
            Some(AtomKind::AbsolutePath) => {
                let absolute = choose|absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                    #[trigger] mixed_absolute_resolution_evidence(&exports, word, namespace, absolute)
                        && qualified_func_target(absolute, resolved.target);
                assert(absolute == target);
                absolute_name_declares(&exports, word, namespace, declaration);
            },
            Some(AtomKind::RelativePath) => {
                let (head, middle, last, binding) = choose|head: &str, middle: Option<&str>, last: &str, binding: Option<MixedAbsoluteTarget>|
                    #[trigger] relative_path_parts(word, head, middle, last)
                        && #[trigger] scoped_binding(self, file, scope, head, binding)
                        && match binding {
                            Some(MixedAbsoluteTarget::Namespace { key, .. }) =>
                                exists|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                                    parent@ == parent_spelling(key, middle)
                                        && #[trigger] mixed_key_resolution(&exports, NameKey { parent: Some(parent), name: last }, namespace, absolute)
                                        && qualified_func_target(absolute, resolved.target),
                            _ => false,
                        };
                let key = binding->Some_0->Namespace_key;
                let (parent, absolute) = choose|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                    parent@ == parent_spelling(key, middle)
                        && #[trigger] mixed_key_resolution(&exports, NameKey { parent: Some(parent), name: last }, namespace, absolute)
                        && qualified_func_target(absolute, resolved.target);
                assert(absolute == target);
                assert(declarations.declaration_at(NameKey { parent: Some(parent), name: last }, declaration));
            },
            _ => assert(false),
        }
        let key = choose|key: NameKey| #[trigger] declarations.declaration_at(key, declaration);
        targets.mixed_use_exports_match(&project);
        mixed_exports_use_project_declarations(&project, &exports);
        mixed_declaration_origin(&project, &declarations, key, declaration);
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
