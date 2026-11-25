//! 回路本体の所属からマクロ名を解決し、元の定義を取り出す。

use core::ops::Range;

use super::{MixedUseAliases, find_namespace};
use crate::ncg2m::file::MetaItemKind;
#[cfg(verus_only)]
use crate::ncg2m::{defn::readable_span, file::meta_macro_span_evidence};
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
use crate::project::source_indexes::DefnScope;
#[cfg(verus_only)]
use crate::project::source_indexes::project_source_index_evidence;
use crate::project::{
    MixedFuncCalleeError, ProjectDeclaration, ProjectDeclarationKind, ProjectSourceIndex,
};
#[cfg(verus_only)]
use crate::project::{ParsedProjectSources, exports::mixed_exports_use_project_declarations, location_in_source, mixed_declaration_origin, mixed_use_targets_match};
use crate::syntax::{AtomKind, classify_bare_atom};
use crate::syntax::circuit::Head;
#[cfg(verus_only)]
use super::{is_namespace_block, mixed_function::{func_scope_path, scoped_circuit_name_matches, scoped_declaration_key}};
#[cfg(verus_only)]
use crate::syntax::bare_atom_kind;
#[cfg(verus_only)]
use crate::syntax::circuit::{indexed_entry_evidence, namespace_name_evidence, reference_atom};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 解決したマクロの元の宣言と、ソース集合に保持した索引範囲。
#[derive(Debug)]
pub struct ResolvedDefmacro<'p, 'a> {
    /// NCG2M の宣言位置、文書版、ファイルと項目の添字。
    pub declaration: ProjectDeclaration<'p, 'a>,
    /// 宣言順の仮引数名。それぞれ元ファイルの UTF-8 半開バイト範囲。
    pub parameters: &'p [Range<usize>],
    /// マクロ本体の S 式1個を含む元ファイルの UTF-8 半開バイト範囲。
    pub body: &'p Range<usize>,
}

/// 回路本体に書いたマクロ名を解決できない理由。
#[derive(Debug)]
pub enum DefmacroNameError<'p, 'a> {
    /// ファイル・項目の組が、展開を許す回路本体を指さない。
    Caller,
    /// マクロ名の字句が無修飾名、完全修飾名、相対パスのいずれにも当てはまらない。
    InvalidName,
    /// 指定したスコープで名前を引いた結果。宣言、名前空間、非公開の位置を保持する。
    Reference(MixedFuncCalleeError<'p, 'a>),
}

/// 指定した索引位置に展開を置ける種類の回路本体がある。
pub open spec fn has_macro_caller(project: &ParsedProjectSources, file: usize, entry: usize) -> bool {
    &&& file < project.indexes_model().len()
    &&& project.indexes_model()[file as int] matches ProjectSourceIndex::Circuit(parsed)
        && entry < parsed.syntax.entries@.len() && {
            let head = parsed.syntax.entries@[entry as int].head;
            head is Func || head is Module || head is ModulePart
        }
}

/// 宣言の出典と種別が、混在プロジェクトの元の索引にある。
pub closed spec fn macro_reference_declaration(project: &ParsedProjectSources, declaration: ProjectDeclaration) -> bool {
    &&& declaration.file < project.sources_model().len()
    &&& declaration.file < project.indexes_model().len()
    &&& *declaration.name.source == project.sources_model()[declaration.file as int]
    &&& location_in_source(declaration.name)
    &&& match project.indexes_model()[declaration.file as int] {
        ProjectSourceIndex::Circuit(circuit) =>
            declaration.item < circuit.names@.len() && {
                let form = circuit.names@[declaration.item as int];
                declaration.kind == ProjectDeclarationKind::Circuit(form.head)
                    && declaration.name.span == form.name.span
            },
        ProjectSourceIndex::Functional(items) =>
            declaration.item < items@.len() && match items@[declaration.item as int].kind {
                MetaItemKind::Defn(header) =>
                    declaration.kind is Defn && declaration.name.span == header.name_span,
                MetaItemKind::Defmacro { name, .. } =>
                    declaration.kind is Defmacro && declaration.name.span == name,
                _ => false,
            },
    }
}

/// 解決結果のマクロ名、仮引数、本体が同じ宣言の索引に対応する。
pub open spec fn indexed_defmacro(project: &ParsedProjectSources, definition: ResolvedDefmacro) -> bool {
    let declaration = definition.declaration;
    &&& declaration.kind is Defmacro
    &&& macro_reference_declaration(project, declaration)
    &&& defmacro_ranges_readable(definition)
    &&& project.indexes_model()[declaration.file as int] matches ProjectSourceIndex::Functional(items)
        && declaration.item < items@.len()
        && (items@[declaration.item as int].kind matches MetaItemKind::Defmacro { name, parameters, body }
            && declaration.name.span == name && definition.parameters@ == parameters@ && *definition.body == body)
}

/// 仮引数と本体の範囲が、元の文書から読み出せる UTF-8 文字境界にある。
pub open spec fn defmacro_ranges_readable(definition: ResolvedDefmacro) -> bool {
    let source = definition.declaration.name.source.text_model();
    &&& readable_span(source, *definition.body)
    &&& forall|i: int| 0 <= i < definition.parameters@.len() ==>
        readable_span(source, #[trigger] definition.parameters@[i])
}

spec fn macro_result_matches(
    project: &ParsedProjectSources, selection: Result<Option<ProjectDeclaration>, MixedFuncCalleeError>,
    result: Result<ResolvedDefmacro, DefmacroNameError>,
) -> bool {
    match selection {
        Ok(Some(declaration)) =>
            result matches Ok(definition) && definition.declaration == declaration && indexed_defmacro(project, definition),
        Ok(None) => result == Err(DefmacroNameError::Reference(MixedFuncCalleeError::Missing)),
        Err(error) => {
            &&& result == Err(DefmacroNameError::Reference(error))
            &&& error matches MixedFuncCalleeError::WrongDeclaration(declaration) ==>
                !(declaration.kind is Defmacro) && macro_reference_declaration(project, declaration)
        },
    }
}

/// 参照元の回路本体のスコープで選んだ宣言、または診断の根拠を表す。
pub closed spec fn defmacro_name_resolution(
    aliases: &MixedUseAliases, file: usize, entry: usize, word: &str,
    result: Result<ResolvedDefmacro, DefmacroNameError>,
) -> bool {
    let project = aliases.targets_model().project_model();
    if !has_macro_caller(&project, file, entry) {
        result == Err(DefmacroNameError::Caller)
    } else if !(bare_atom_kind(word.spec_bytes()) matches Some(kind) && reference_atom(kind)) {
        result == Err(DefmacroNameError::InvalidName)
    } else {
        let parsed = project.indexes_model()[file as int]->Circuit_0;
        let block = parsed.syntax.entries@[entry as int].namespace;
        exists|namespace: Option<&str>, selection: Result<Option<ProjectDeclaration>, MixedFuncCalleeError>|
            func_scope_path(&parsed, block, namespace)
                && #[trigger] scoped_circuit_name_matches(aliases, file, DefnScope { block, namespace },
                    word, ProjectDeclarationKind::Defmacro, selection)
                && macro_result_matches(&project, selection, result)
    }
}

#[verifier::spinoff_prover]
proof fn selected_declaration_origin(
    aliases: &MixedUseAliases, file: usize, scope: DefnScope, word: &str,
    selected: Result<Option<ProjectDeclaration>, MixedFuncCalleeError>, declaration: ProjectDeclaration,
)
    requires
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
        scoped_circuit_name_matches(aliases, file, scope, word, ProjectDeclarationKind::Defmacro, selected),
        selected == Ok(Some(declaration)) || selected == Err(MixedFuncCalleeError::WrongDeclaration(declaration)),
    ensures
        (declaration.kind is Defmacro) <==> selected == Ok(Some(declaration)),
        macro_reference_declaration(&aliases.targets_model().project_model(), declaration),
{
    let targets = aliases.targets_model();
    let project = targets.project_model();
    let exports = targets.exports_model();
    let declarations = exports.declarations_model();
    let key = scoped_declaration_key(aliases, file, scope, word, ProjectDeclarationKind::Defmacro, declaration, selected);
    targets.mixed_use_exports_match(&project);
    mixed_exports_use_project_declarations(&project, &exports);
    mixed_declaration_origin(&project, &declarations, key, declaration);
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// 回路本体の位置からマクロ名を解決し、仮引数と本体の索引範囲を返す。
    ///
    /// `entry` は回路フォームの索引項目を指す。`func`、`module`、`module-part`
    /// の所属から名前空間と別名スコープを求める。`word` には元の展開フォームの
    /// マクロ名を渡す。`module-part` の別名はその本体があるブロックから引く。
    ///
    /// # Errors
    ///
    /// 回路本体の位置、名前の字句、スコープでの名前解決の順に検査する。
    /// 別の種別の宣言が見つかった場合は、その宣言の位置と種別を返す。
    pub fn resolve_defmacro_name(&self, file: usize, entry: usize, word: &str)
        -> (result: Result<ResolvedDefmacro<'p, 'a>, DefmacroNameError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures
            defmacro_name_resolution(self, file, entry, word, result),
            result matches Ok(definition) ==> indexed_defmacro(&self.targets_model().project_model(), definition),
            result matches Err(DefmacroNameError::Reference(MixedFuncCalleeError::WrongDeclaration(declaration))) ==>
                !(declaration.kind is Defmacro)
                && macro_reference_declaration(&self.targets_model().project_model(), declaration),
    {
        let project = self.targets().project();
        let indexes = project.indexes();
        if file >= indexes.len() { return Err(DefmacroNameError::Caller); }
        let ProjectSourceIndex::Circuit(parsed) = &indexes[file] else { return Err(DefmacroNameError::Caller); };
        if entry >= parsed.syntax.entries.len() { return Err(DefmacroNameError::Caller); }
        let owner = &parsed.syntax.entries[entry];
        if !matches!(owner.head, Head::Func | Head::Module | Head::ModulePart) {
            return Err(DefmacroNameError::Caller);
        }
        assert(has_macro_caller(project, file, entry));
        if !matches!(classify_bare_atom(word), Some(AtomKind::Name | AtomKind::AbsolutePath | AtomKind::RelativePath)) {
            return Err(DefmacroNameError::InvalidName);
        }
        let namespace = if let Some(block) = owner.namespace {
            proof {
                let source = project.sources_model()[file as int];
                project_source_index_evidence(source, indexes@[file as int]);
                parsed_index_evidence(source, *parsed);
                source.text_model_is_text();
                indexed_entry_evidence(source.text_model(), parsed.syntax.forms@, parsed.syntax.entries@, entry as int);
                namespace_name_evidence(source.text_model(), parsed.syntax.forms@, parsed.syntax.entries@,
                    parsed.names@, owner.form as int, block);
                let i = choose|i: int| 0 <= i < parsed.names@.len() && (#[trigger] parsed.names@[i]).form == block
                    && parsed.names@[i].head is Namespace && parsed.names@[i].block is None;
                assert(is_namespace_block(parsed.names@[i], block));
            }
            find_namespace(parsed, block)
        } else { None };
        assert(func_scope_path(parsed, owner.namespace, namespace));
        let scope = DefnScope { block: owner.namespace, namespace };
        let selection = self.resolve_scoped_circuit_name(file, scope, word, ProjectDeclarationKind::Defmacro);
        let ghost chosen = selection;
        let outcome = match selection {
            Ok(Some(declaration)) => {
                proof {
                    selected_declaration_origin(self, file, scope, word, chosen, declaration);
                    reveal(macro_reference_declaration);
                    let index = indexes@[declaration.file as int];
                    let source = project.sources_model()[declaration.file as int];
                    project_source_index_evidence(source, index);
                    source.text_model_is_text();
                    meta_macro_span_evidence(source.text_model(), index->Functional_0@, declaration.item as int);
                }
                let ProjectSourceIndex::Functional(items) = &indexes[declaration.file] else { unreachable!() };
                let MetaItemKind::Defmacro { parameters, body, .. } = &items[declaration.item].kind else { unreachable!() };
                Ok(ResolvedDefmacro { declaration, parameters: parameters.as_slice(), body })
            },
            Ok(None) => Err(DefmacroNameError::Reference(MixedFuncCalleeError::Missing)),
            Err(error) => {
                proof {
                    if let MixedFuncCalleeError::WrongDeclaration(declaration) = &error {
                        selected_declaration_origin(self, file, scope, word, chosen, *declaration);
                    }
                }
                Err(DefmacroNameError::Reference(error))
            },
        };
        assert(macro_result_matches(project, chosen, outcome));
        assert(defmacro_name_resolution(self, file, entry, word, outcome));
        outcome
    }
}

} // verus!
