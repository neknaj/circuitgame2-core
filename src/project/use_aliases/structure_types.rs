//! 構造体フィールドの型名を、フィールドを含む宣言のスコープで解決する。

mod index;
mod cast_reference;
mod expression;
mod port_type;
pub use expression::StructureExpressionTypeError;
pub(super) use expression::StructureExpressionContext;
#[cfg(verus_only)]
pub(super) use expression::CheckedStructureExpression;
pub use index::{
    ResolvedStructureEntry, ResolvedStructures, StructureIndexError, StructureLayout, StructureLayoutError,
    StructureLayoutField, StructureLayouts, StructurePlacementError, StructureTypeError, StructureTypeReference, StructureOperation, StructureOperationError, TypedStructureOperation,
};

use super::definitions::{ReferenceRequest, ReferenceUse};
use super::{DefinitionBinding, DefinitionReferenceReason, UseAliases};
#[cfg(verus_only)]
use super::ResolvedPortType;
use crate::project::circuits::read_indexed_atom;
use crate::project::declarations::key_of;
use crate::project::{
    DeclaredField, DeclaredFieldType, LocatedName, ProjectSource, StructureNumberError,
    check_structure_declaration,
};
use crate::syntax::Form;
use crate::syntax::circuit::{NamedForm, named_build_entry};
use alloc::vec::Vec;
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::project::circuits::{parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::project::declarations::{declaration_location_evidence, form_key, located_name_evidence};
#[cfg(verus_only)]
use crate::project::structure_declarations::checked_structure_fields;
#[cfg(verus_only)]
use crate::project::{StructureDeclaration, location_in_source, structure_declaration_result};
#[cfg(verus_only)]
use crate::syntax::circuit::{indexed_entry_evidence, named_forms_match, namespace_name_evidence, reference_atom};
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 構造体の宣言をプロジェクト内で識別する。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StructurePosition {
    /// 正規化済みソース一覧の添字。
    pub file: usize,
    /// ファイルの厳格索引にある構造体宣言の添字。
    pub entry: usize,
}

/// フィールドのビット列型または解決済みの構造体型。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructureFieldType {
    /// 宣言で指定されたビット列の幅。
    Bits(u64),
    /// 宣言で識別する構造体型。
    Struct(StructurePosition),
}

/// 元の宣言の構文位置と、解決済みの型を持つフィールド。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResolvedStructureField {
    /// 元の宣言にある位置、型指定、ビットオフセット。
    pub declared: DeclaredField,
    /// フィールドの型。
    pub ty: StructureFieldType,
}

/// 総幅と各フィールドの型を持つ構造体宣言。
#[derive(Debug, Eq, PartialEq)]
pub struct ResolvedStructure {
    /// 宣言で指定された総幅。
    pub width: u64,
    /// 元の宣言順に並ぶフィールド。
    pub fields: Vec<ResolvedStructureField>,
}

/// 構造体宣言の数値またはフィールドの型参照に関する診断。
#[derive(Debug)]
pub enum StructureResolutionError<'p, 'a> {
    /// 幅またはオフセットが使えない。
    Number(StructureNumberError<'p, 'a>),
    /// フィールドに書いた型名を解決できない。
    TypeReference {
        /// 解決できなかった型名の元ソース範囲。
        reference: LocatedName<'p, 'a>,
        /// 名前解決の結果と、該当する関連箇所。
        reason: DefinitionReferenceReason<'p, 'a>,
    },
}

struct StructureScope<'p, 'a> {
    file: usize,
    block: Option<usize>,
    namespace: Option<&'a str>,
    source: &'p ProjectSource<'a>,
    forms: &'p [Form],
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn structure_scope_matches(&self, file: usize, entry: usize, scope: &StructureScope) -> bool {
        let project = self.targets.project_model();
        &&& scope.file == file < project.circuits_model().len()
        &&& file < project.sources_model().len()
        &&& *scope.source == project.sources_model()[file as int]
        &&& {
            let syntax = project.circuits_model()[file as int].syntax;
            &&& entry < syntax.entries@.len()
            &&& scope.forms@ == syntax.forms@
            &&& scope.block == syntax.entries@[entry as int].namespace
            &&& self.scope_matches(file, scope.block, Ok(scope.namespace))
        }
    }

    spec fn structure_type_binding(&self, scope: &StructureScope, at: usize, binding: Result<DefinitionBinding, DefinitionReferenceReason>) -> bool {
        let span = form_span(scope.forms@[at as int]);
        &&& at < scope.forms@.len()
        &&& scope.forms@[at as int] is Atom
        &&& exists|word: &str| word.spec_bytes() == scope.source.text.spec_bytes()[span.start as int..span.end as int]
            && #[trigger] self.binding_evidence(scope.file,
                ReferenceRequest { block: scope.block, word, role: ReferenceUse::StructType }, scope.namespace,
                scope.forms@[at as int]->Atom_kind, binding)
    }

    pub(super) open spec fn is_structure_position(&self, position: StructurePosition) -> bool {
        let circuits = self.targets.project_model().circuits_model();
        &&& position.file < circuits.len()
        &&& position.entry < circuits[position.file as int].syntax.entries@.len()
        &&& circuits[position.file as int].syntax.entries@[position.entry as int].head is Struct
    }

    pub(super) closed spec fn structure_position_matches(&self, position: StructurePosition, binding: DefinitionBinding) -> bool {
        let project = self.targets.project_model();
        &&& binding matches DefinitionBinding::Declaration { source, form }
        &&& self.is_structure_position(position)
        &&& position.file < project.sources_model().len()
        &&& *source == project.sources_model()[position.file as int]
        &&& project.circuits_model()[position.file as int].syntax.entries@[position.entry as int].form == form.form
    }

    /// 構造体の宣言位置と、ポート型が保持する宣言の対応を表す。
    pub closed spec fn structure_port_type_matches(
        &self, position: StructurePosition, result: Option<ResolvedPortType>,
    ) -> bool {
        match result {
            Some(ResolvedPortType::Struct { source, form }) => {
                let parsed = self.targets.project_model().circuits_model()[position.file as int];
                &&& self.declared_port_type(ResolvedPortType::Struct { source, form })
                &&& self.structure_position_matches(position, DefinitionBinding::Declaration { source, form })
                &&& (exists|i: int| 0 <= i < parsed.names@.len() && (#[trigger] parsed.names@[i]) == *form)
            },
            None => !self.is_structure_position(position),
            _ => false,
        }
    }

    pub(super) proof fn structure_port_type_resolved(&self, position: StructurePosition, result: Option<ResolvedPortType>)
        requires
            self.can_resolve(),
            self.structure_port_type_matches(position, result),
        ensures
            result.is_some() <==> self.is_structure_position(position),
            result matches Some(port) ==> port is Struct && self.declared_port_type(port),
            result matches Some(ResolvedPortType::Struct { source, form }) ==>
                location_in_source(LocatedName { source, span: form.name.span }),
    {
        if let Some(ResolvedPortType::Struct { source, form }) = result {
            self.targets.declarations_cover_project();
            declaration_location_evidence(&self.targets.exports_model().declarations_model(), form_key(*form), source, form);
        }
    }

    /// 同じ宣言位置で得られるポート型は、元の宣言とそのソースを一意に指す。
    pub proof fn structure_port_types_agree(
        &self, position: StructurePosition, left: Option<ResolvedPortType>, right: Option<ResolvedPortType>,
    )
        requires
            self.can_resolve(),
            self.structure_port_type_matches(position, left),
            self.structure_port_type_matches(position, right),
        ensures left == right,
    {
        if let (Some(ResolvedPortType::Struct { source: x, form: a }),
            Some(ResolvedPortType::Struct { source: y, form: b })) = (left, right)
        {
            let project = self.targets.project_model();
            let parsed = project.circuits_model()[position.file as int];
            self.targets.parsed_project_model();
            parsed_index_evidence(*x, parsed);
            reveal(named_forms_match);
            let i = choose|i: int| 0 <= i < parsed.names@.len() && (#[trigger] parsed.names@[i]) == *a;
            let j = choose|j: int| 0 <= j < parsed.names@.len() && (#[trigger] parsed.names@[j]) == *b;
            if i < j { assert(parsed.names@[i].form < parsed.names@[j].form); }
            if j < i { assert(parsed.names@[j].form < parsed.names@[i].form); }
            assert(i == j && *x == *y);
        }
    }

    /// 解決済みの構造体宣言を、同じプロジェクトの配置表で使う位置に変換する。
    pub(super) fn resolved_structure_position(
        &self, source: &ProjectSource<'a>, declaration: &NamedForm<'a>,
    ) -> (position: StructurePosition)
        requires
            self.can_resolve(),
            declaration.head is Struct,
            self.targets.exports_model().declarations_model().declaration_at(form_key(*declaration), source, declaration),
        ensures
            self.is_structure_position(position),
            self.structure_position_matches(position, DefinitionBinding::Declaration { source, form: declaration }),
            self.structure_port_type_matches(position, Some(ResolvedPortType::Struct { source, form: declaration })),
    {
        proof { self.targets.declarations_cover_project(); }
        let project = self.targets.project();
        let table = self.targets.exports().declarations();
        let (file, name) = table.selected_declaration_position(key_of(declaration),
            Ghost(*project), Ghost(*source), Ghost(*declaration));
        let parsed = &project.circuits()[file];
        proof {
            assert(parsed_circuit_matches(*source, *parsed));
            parsed_index_evidence(*source, *parsed);
        }
        let entry = named_build_entry(source.text, parsed, name);
        let position = StructurePosition { file, entry };
        proof {
            assert(exists|i: int| 0 <= i < parsed.names@.len()
                && (#[trigger] parsed.names@[i]) == *declaration) by {
                assert(parsed.names@[name as int] == *declaration);
            };
        }
        position
    }

    spec fn structure_field_matches(&self, scope: &StructureScope, declared: DeclaredField, field: ResolvedStructureField) -> bool {
        &&& field.declared == declared
        &&& match (declared.ty, field.ty) {
            (DeclaredFieldType::Bits(width), StructureFieldType::Bits(resolved)) => resolved == width,
            (DeclaredFieldType::Named { form }, StructureFieldType::Struct(target)) =>
                exists|binding: DefinitionBinding| #[trigger] self.structure_type_binding(scope, form, Ok(binding))
                    && self.structure_position_matches(target, binding),
            _ => false,
        }
    }

    spec fn structure_field_error(&self, scope: &StructureScope, declared: DeclaredField, error: StructureResolutionError) -> bool {
        &&& declared.ty matches DeclaredFieldType::Named { form }
        &&& error matches StructureResolutionError::TypeReference { reference, reason }
        &&& *reference.source == *scope.source
        &&& location_in_source(reference)
        &&& reference.span == form_span(scope.forms@[form as int])
        &&& self.structure_type_binding(scope, form, Err(reason))
    }

    fn resolve_structure_field(
        &self, scope: &StructureScope<'p, 'a>, field: DeclaredField,
    ) -> (result: Result<ResolvedStructureField, StructureResolutionError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.scope_matches(scope.file, scope.block, Ok(scope.namespace)),
            form_spans_valid(scope.source.text, scope.forms@, scope.source.text.spec_bytes().len() as int),
            field.ty matches DeclaredFieldType::Named { form } ==> form < scope.forms@.len()
                && scope.forms@[form as int] is Atom && reference_atom(scope.forms@[form as int]->Atom_kind),
        ensures match result {
            Ok(resolved) => self.structure_field_matches(scope, field, resolved),
            Err(error) => self.structure_field_error(scope, field, error),
        },
    {
        let ty = match field.ty {
            DeclaredFieldType::Bits(width) => StructureFieldType::Bits(width),
            DeclaredFieldType::Named { form: atom } => {
                let (word, span) = read_indexed_atom(scope.source.text, scope.forms, atom);
                let Form::Atom { kind: atom_kind, .. } = scope.forms[atom] else { unreachable!() };
                let request = ReferenceRequest { block: scope.block, word, role: ReferenceUse::StructType };
                let binding = match self.resolve_scoped_binding(scope.file, &request, scope.namespace, atom_kind) {
                    Ok(binding) => binding,
                    Err(reason) => {
                        let reference = LocatedName { source: scope.source, span };
                        proof { located_name_evidence(reference); }
                        assert(self.structure_type_binding(scope, atom, Err(reason)));
                        return Err(StructureResolutionError::TypeReference { reference, reason });
                    },
                };
                assert(self.structure_type_binding(scope, atom, Ok(binding)));
                proof { self.struct_binding_is_struct(scope.file, request, scope.namespace, atom_kind, binding); }
                let DefinitionBinding::Declaration { source: declaration_source, form: declaration } = binding else { unreachable!() };
                proof {
                    self.binding_declaration_origin(scope.file, request, scope.namespace, atom_kind, declaration_source, declaration);
                }
                let target = self.resolved_structure_position(declaration_source, declaration);
                assert(self.structure_position_matches(target, binding));
                StructureFieldType::Struct(target)
            },
        };
        Ok(ResolvedStructureField { declared: field, ty })
    }

    spec fn resolved_structure_fields(
        &self, scope: &StructureScope, fields: Seq<DeclaredField>, resolved: Seq<ResolvedStructureField>,
    ) -> bool {
        &&& resolved.len() <= fields.len()
        &&& forall|i: int| 0 <= i < resolved.len() ==>
            self.structure_field_matches(scope, fields[i], #[trigger] resolved[i])
    }

    spec fn structure_after_numbers(
        &self, scope: &StructureScope, declaration: StructureDeclaration,
        result: Result<Option<ResolvedStructure>, StructureResolutionError>,
    ) -> bool {
        match result {
            Ok(Some(resolved)) => resolved.width == declaration.width
                && resolved.fields@.len() == declaration.fields@.len()
                && self.resolved_structure_fields(scope, declaration.fields@, resolved.fields@),
            Err(error) => exists|prefix: Seq<ResolvedStructureField>| {
                let i = prefix.len() as int;
                i < declaration.fields@.len()
                    && #[trigger] self.resolved_structure_fields(scope, declaration.fields@, prefix)
                    && self.structure_field_error(scope, declaration.fields@[i], error)
            },
            Ok(None) => false,
        }
    }

    /// 構造体の各フィールド型と、宣言元スコープでの解決結果との対応を表す。
    pub closed spec fn structure_resolution_matches(
        &self, file: usize, entry: usize, limit: u64, result: Result<Option<ResolvedStructure>, StructureResolutionError>,
    ) -> bool {
        let project = &self.targets.project_model();
        match result {
            Ok(None) => structure_declaration_result(project, file as int, entry as int, limit, Ok(None)),
            Err(StructureResolutionError::Number(error)) =>
                structure_declaration_result(project, file as int, entry as int, limit, Err(error)),
            _ => exists|scope: StructureScope, declaration: StructureDeclaration|
                #[trigger] self.structure_scope_matches(file, entry, &scope)
                    && #[trigger] structure_declaration_result(project, file as int, entry as int, limit, Ok(Some(declaration)))
                    && self.structure_after_numbers(&scope, declaration, result),
        }
    }

    /// 構造体の各フィールド型を宣言元のスコープで解決する。
    ///
    /// 対象外のファイルや索引項目は `Ok(None)` を返す。`limit` は宣言幅の上限を指定する。
    /// フィールドの配置と構造体型をたどる循環は後段で検査する。
    ///
    /// # Examples
    ///
    /// 別ファイルの公開型に付けた別名から、元の宣言を特定する。
    ///
    /// ```
    /// use circuitgame2_core::{
    ///     project::{SourceSnapshot, StructureFieldType, StructurePosition, check_use_aliases,
    ///         index_use_targets, parse_circuit_project},
    ///     syntax::circuit::Head,
    /// };
    /// let project = parse_circuit_project(&[
    ///     SourceSnapshot { path: "app.ncg2", revision: 1,
    ///         text: "(namespace app (use ::lib::Word imported)
    ///             (struct Pair (width 16) (high imported (at 8)) (low (bits 8) (at 0))))" },
    ///     SourceSnapshot { path: "lib.ncg2", revision: 1,
    ///         text: "(namespace lib (struct Word (width 8)) (export Word))" },
    /// ]).unwrap();
    /// let entry = |file: usize| project.circuits()[file].syntax.entries.iter()
    ///     .position(|item| item.head == Head::Struct).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let pair = aliases.resolve_structure_fields(0, entry(0), 16).unwrap().unwrap();
    /// assert_eq!(pair.fields[0].ty, StructureFieldType::Struct(StructurePosition { file: 1, entry: entry(1) }));
    /// assert_eq!(pair.fields[1].ty, StructureFieldType::Bits(8));
    /// ```
    ///
    /// # Errors
    ///
    /// 数値の違反を先に確認する。続いてフィールドを宣言順に調べ、最初に解決できなかった型名を返す。
    pub fn resolve_structure_fields(
        &self, file: usize, entry: usize, limit: u64,
    ) -> (result: Result<Option<ResolvedStructure>, StructureResolutionError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.structure_resolution_matches(file, entry, limit, result),
    {
        let project = self.targets.project();
        let declaration = match check_structure_declaration(project, file, entry, limit) {
            Ok(Some(declaration)) => declaration,
            Ok(None) => return Ok(None),
            Err(error) => return Err(StructureResolutionError::Number(error)),
        };
        proof { checked_structure_fields(project, file, entry, limit, declaration); }

        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let owner = &parsed.syntax.entries[entry];
        proof {
            assert(parsed_circuit_matches(*source, *parsed));
            parsed_index_evidence(*source, *parsed);
            indexed_entry_evidence(source.text, parsed.syntax.forms@, parsed.syntax.entries@, entry as int);
            if let Some(parent) = owner.namespace {
                namespace_name_evidence(source.text, parsed.syntax.forms@, parsed.syntax.entries@,
                    parsed.names@, owner.form as int, parent);
                let i = choose|i: int| 0 <= i < parsed.names@.len() && (#[trigger] parsed.names@[i]).form == parent
                    && parsed.names@[i].head is Namespace && parsed.names@[i].block is None;
                assert(super::is_namespace_block(parsed.names@[i], parent));
            }
        }
        let Ok(namespace) = self.scope_namespace(file, owner.namespace) else { unreachable!() };
        let scope = StructureScope { file, block: owner.namespace, namespace, source, forms: parsed.syntax.forms.as_slice() };
        assert(self.structure_scope_matches(file, entry, &scope));
        let mut fields = Vec::new();
        let mut i = 0;
        while i < declaration.fields.len()
            invariant
                self.can_resolve(),
                project.has_parsed_sources(),
                *project == self.targets.project_model(),
                file < project.circuits_model().len(),
                scope.forms@ == project.circuits_model()[file as int].syntax.forms@,
                i == fields@.len() <= declaration.fields@.len(),
                self.structure_scope_matches(file, entry, &scope),
                structure_declaration_result(project, file as int, entry as int, limit, Ok(Some(declaration))),
                form_spans_valid(scope.source.text, scope.forms@, scope.source.text.spec_bytes().len() as int),
                self.resolved_structure_fields(&scope, declaration.fields@, fields@),
            decreases declaration.fields@.len() - i,
        {
            proof { checked_structure_fields(project, file, entry, limit, declaration); }
            let field = declaration.fields[i];
            assert(field == declaration.fields@[i as int]);
            assert(field.ty matches DeclaredFieldType::Named { form } ==> form < scope.forms@.len()
                && scope.forms@[form as int] is Atom && reference_atom(scope.forms@[form as int]->Atom_kind));
            let resolved = match self.resolve_structure_field(&scope, field) {
                Ok(resolved) => resolved,
                Err(error) => {
                    assert(error is TypeReference);
                    assert(self.structure_after_numbers(&scope, declaration, Err(error)));
                    assert(self.structure_resolution_matches(file, entry, limit, Err(error)));
                    return Err(error);
                },
            };
            fields.push(resolved);
            i += 1;
        }
        let result = Ok(Some(ResolvedStructure { width: declaration.width, fields }));
        assert(self.structure_after_numbers(&scope, declaration, result));
        result
    }
}

} // verus!
