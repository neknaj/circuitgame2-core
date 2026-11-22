//! モジュール本体の呼び出し先を、呼び出し元の断片にある別名で解決する。

mod ports;
pub use ports::{ModuleCallPorts, ModuleCallPortsError};
mod inputs;
pub use inputs::{ModuleCallInputs, ModuleCallInputsError};

use super::{DefinitionBinding, DefinitionPosition, DefinitionReferenceError, TypedRoutineSignature, TypedSignatureError, UseAliases};
#[cfg(verus_only)]
use super::ResolvedDefinitionReference;
use crate::project::{LocatedName, ModuleBodyPosition, ProjectSource};
#[cfg(verus_only)]
use crate::project::{circuits::parsed_index_evidence, declarations::located_name_evidence, location_in_source};
use crate::syntax::circuit::{CallShape, Head, indexed_call_shape};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence, call_arguments_match, call_shape_matches, indexed_call_arguments};
use vstd::prelude::*;

verus! {

/// モジュールの右辺で名前解決した呼び出し先。
#[derive(Debug)]
pub enum ModuleCallTarget<'p, 'a> {
    /// 基底 NOR。1ビット入力を2本受け取り、1ビット出力を1本返す。
    Nor,
    /// `func` または `module` の宣言と型付き署名。
    Routine {
        /// 参照先のファイルと厳格索引の位置。
        position: ModuleBodyPosition,
        /// 参照先の宣言名を含む範囲。
        declaration: LocatedName<'p, 'a>,
        /// 宣言のスコープで型名を解決した入出力。
        signature: TypedRoutineSignature<'p, 'a>,
    },
    /// 名前解決したラッチまたはメモリ。状態素子の検査は後段で行う。
    StateElement {
        /// ラッチまたはメモリの宣言種別。
        head: Head,
        /// 参照先のファイルと厳格索引の位置。
        position: ModuleBodyPosition,
        /// 参照先の宣言名を含む範囲。
        declaration: LocatedName<'p, 'a>,
    },
}

/// 呼び出し元の構文位置と名前解決した参照先。
#[derive(Debug)]
pub struct ModuleCallSignature<'p, 'a> {
    /// 呼び出しを書いたファイルと文書版。
    pub source: &'p ProjectSource<'a>,
    /// 呼び出しを表すリストの位置、範囲、実引数数。
    pub call: CallShape,
    /// 宣言の位置と署名、または基底ゲート。
    pub target: ModuleCallTarget<'p, 'a>,
}

/// 呼び出しの名前解決または参照先の署名の診断。
#[derive(Debug)]
pub enum ModuleCallSignatureError<'p, 'a> {
    /// 呼び出し先の名前を参照元で解決できなかった。
    Reference(DefinitionReferenceError<'p, 'a>),
    /// 参照先の入出力を検査できなかった。
    Signature {
        /// 呼び出し名の元のソース範囲。
        reference: LocatedName<'p, 'a>,
        /// 参照先の宣言名の範囲。
        declaration: LocatedName<'p, 'a>,
        /// 署名の検査で見つかった違反。
        reason: TypedSignatureError<'p, 'a>,
    },
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn module_call_at(&self, at: DefinitionPosition) -> bool {
        let parsed = self.targets.project_model().circuits_model()[at.file as int];
        let def = parsed.entry_ranges@[at.entry as int].definitions.start + at.definition;
        let head = parsed.syntax.entries@[at.entry as int].head;
        &&& self.position_exists(at.file, at.entry, at.definition, at.reference)
        &&& at.entry < parsed.syntax.entries@.len() && (head is Module || head is ModulePart)
        &&& parsed.references@[parsed.definitions@[def].references.start + at.reference].kind is Callee
    }

    spec fn module_callee_position(
        &self, binding: DefinitionBinding, position: ModuleBodyPosition, declaration: LocatedName,
    ) -> bool {
        let project = self.targets.project_model();
        let circuits = project.circuits_model();
        &&& binding matches DefinitionBinding::Declaration { source, form }
        &&& position.file < circuits.len() && position.file < project.sources_model().len()
        &&& *source == project.sources_model()[position.file as int]
        &&& position.entry < circuits[position.file as int].syntax.entries@.len()
        &&& {
            let entry = circuits[position.file as int].syntax.entries@[position.entry as int];
            &&& entry.form == form.form && entry.head == form.head
            &&& *declaration.source == *source && declaration.span == form.name.span
            &&& location_in_source(declaration)
        }
    }

    spec fn module_callee_matches(&self, binding: DefinitionBinding, max_width: u64, target: ModuleCallTarget) -> bool {
        match target {
            ModuleCallTarget::Nor => binding is Nor,
            ModuleCallTarget::Routine { position, declaration, signature } =>
                self.module_callee_position(binding, position, declaration)
                && (binding->Declaration_form.head is Func || binding->Declaration_form.head is Module)
                && self.typed_signature_evidence(position.file, position.entry, max_width, Ok(Some(signature))),
            ModuleCallTarget::StateElement { head, position, declaration } =>
                self.module_callee_position(binding, position, declaration)
                && head == binding->Declaration_form.head && (head is Latch || head is Memory),
        }
    }

    /// 呼び出し元の構文、断片の別名による解決結果、参照先の型を対応付ける。
    pub closed spec fn module_call_signature_result(
        &self, at: DefinitionPosition, max_width: u64,
        result: Result<Option<ModuleCallSignature>, ModuleCallSignatureError>,
    ) -> bool {
        if !self.module_call_at(at) {
            result == Ok(None)
        } else {
            match result {
                Ok(Some(signature)) => {
                    let project = self.targets.project_model();
                    let source = &project.sources_model()[at.file as int];
                    let parsed = &project.circuits_model()[at.file as int];
                    let row = parsed.definitions@[parsed.entry_ranges@[at.entry as int].definitions.start + at.definition];
                    let indexed = parsed.references@[row.references.start + at.reference];
                    &&& *signature.source == *source
                    &&& location_in_source(LocatedName { source: signature.source, span: signature.call.span })
                    &&& signature.call.form + 1 == indexed.form
                    &&& call_shape_matches(source.text, parsed.syntax.forms@, row, indexed, Some(signature.call))
                    &&& call_arguments_match(parsed.syntax.forms@, signature.call)
                    &&& exists|resolved: ResolvedDefinitionReference|
                        #[trigger] self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, Ok(resolved))
                        && self.module_callee_matches(resolved.binding, max_width, signature.target)
                },
                Err(ModuleCallSignatureError::Reference(error)) => !(error is UnknownPosition)
                    && self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, Err(error)),
                Err(ModuleCallSignatureError::Signature { reference, declaration, reason }) =>
                    exists|resolved: ResolvedDefinitionReference, position: ModuleBodyPosition|
                        #[trigger] self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, Ok(resolved))
                        && #[trigger] self.typed_signature_evidence(position.file, position.entry, max_width, Err(reason))
                        && self.module_callee_position(resolved.binding, position, declaration)
                        && (resolved.binding->Declaration_form.head is Func || resolved.binding->Declaration_form.head is Module)
                        && *reference.source == *resolved.site.source && reference.span == resolved.site.name.span
                        && location_in_source(reference),
                Ok(None) => false,
            }
        }
    }

    /// 型検査で使う実引数の位置と、名前解決済みのポート署名を取り出す。
    pub(super) proof fn module_call_site_evidence(
        &self, at: DefinitionPosition, max_width: u64, signature: ModuleCallSignature,
    )
        requires self.module_call_signature_result(at, max_width, Ok(Some(signature))),
        ensures
            self.position_exists(at.file, at.entry, at.definition, at.reference),
            location_in_source(LocatedName { source: signature.source, span: signature.call.span }),
            ({
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[at.file as int];
                let row = parsed.definitions@[parsed.entry_ranges@[at.entry as int].definitions.start + at.definition];
                let indexed = parsed.references@[row.references.start + at.reference];
                &&& *signature.source == project.sources_model()[at.file as int]
                &&& signature.call.form + 1 == indexed.form
                &&& call_shape_matches(signature.source.text, parsed.syntax.forms@, row, indexed, Some(signature.call))
                &&& call_arguments_match(parsed.syntax.forms@, signature.call)
            }),
            signature.target matches ModuleCallTarget::Routine { position, signature: ports, .. } ==>
                self.typed_signature_evidence(position.file, position.entry, max_width, Ok(Some(ports))),
    {
        let resolved = choose|resolved: ResolvedDefinitionReference|
            #[trigger] self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, Ok(resolved))
                && self.module_callee_matches(resolved.binding, max_width, signature.target);
    }

    /// `module` または `module-part` の右辺にある呼び出しを、その断片のスコープで解決する。
    ///
    /// `at` はこのプロジェクトを厳格解析した結果の添字を指す。範囲外の添字、
    /// モジュール本体以外の項目、型名の参照には `None` を返す。
    /// `max_width` は参照先のポート宣言を検査する際のビット幅上限で、基底 NOR の署名は固定幅である。
    /// 実引数とポート型の照合は後段で行う。
    ///
    /// # Errors
    ///
    /// 呼び出し先の名前解決、次いで参照先の署名を検査し、最初の違反を返す。
    pub fn resolve_module_call_signature(&self, at: DefinitionPosition, max_width: u64)
        -> (result: Result<Option<ModuleCallSignature<'p, 'a>>, ModuleCallSignatureError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_call_signature_result(at, max_width, result),
    {
        let project = self.targets.project();
        let circuits = project.circuits();
        if at.file >= circuits.len() { return Ok(None); }
        let parsed = &circuits[at.file];
        if at.entry >= parsed.syntax.entries.len()
            || !matches!(parsed.syntax.entries[at.entry].head, Head::Module | Head::ModulePart) {
            return Ok(None);
        }
        let source = &project.sources()[at.file];
        let ghost model = parsed.build_model();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, at.entry as int);
        }
        let defs = &parsed.entry_ranges[at.entry].definitions;
        if at.definition >= defs.end - defs.start { return Ok(None); }
        let def = defs.start + at.definition;
        proof { build_definition_scope_evidence(source.text, &model, at.entry as int, def as int); }
        let row = &parsed.definitions[def];
        if at.reference >= row.references.end - row.references.start { return Ok(None); }
        let reference = row.references.start + at.reference;
        let Some(call) = indexed_call_shape(source.text, parsed.syntax.forms.as_slice(), row,
            parsed.references.as_slice(), reference) else { return Ok(None); };
        proof {
            located_name_evidence(LocatedName { source, span: call.span });
            indexed_call_arguments(source.text, parsed.syntax.forms@, *row, parsed.references@[reference as int], call);
        }
        assert(self.module_call_at(at));
        let resolved = match self.resolve_definition_reference(at.file, at.entry, at.definition, at.reference) {
            Ok(resolved) => resolved,
            Err(error) => {
                proof {
                    if error is UnknownPosition {
                        self.valid_position_is_not_unknown(at.file, at.entry, at.definition, at.reference);
                    }
                }
                return Err(ModuleCallSignatureError::Reference(error));
            },
        };
        let target = match resolved.binding {
            DefinitionBinding::Nor => ModuleCallTarget::Nor,
            DefinitionBinding::Declaration { source: origin, form } => {
                proof { self.resolved_definition_declaration(at.file, at.entry, at.definition, at.reference, resolved, origin, form); }
                let (file, entry) = self.indexed_declaration_position(origin, form);
                let position = ModuleBodyPosition { file, entry };
                let declaration = LocatedName { source: origin, span: form.name.span.start..form.name.span.end };
                assert(self.module_callee_position(resolved.binding, position, declaration));
                if matches!(form.head, Head::Latch | Head::Memory) {
                    ModuleCallTarget::StateElement { head: form.head, position, declaration }
                } else {
                    let signature = match self.resolve_routine_signature(file, entry, max_width) {
                        Ok(Some(signature)) => signature,
                        Ok(None) => {
                            proof {
                                self.typed_signature_skips_non_routines(file, entry, max_width);
                                assert(false);
                            }
                            unreachable!()
                        },
                        Err(reason) => {
                            let name = resolved.site.name;
                            let reference = LocatedName { source: resolved.site.source, span: name.span.start..name.span.end };
                            proof {
                                self.resolved_reference_location(at.file, at.entry, at.definition, at.reference, resolved);
                                located_name_evidence(reference);
                            }
                            return Err(ModuleCallSignatureError::Signature { reference, declaration, reason });
                        },
                    };
                    ModuleCallTarget::Routine { position, declaration, signature }
                }
            },
        };
        assert(self.module_callee_matches(resolved.binding, max_width, target));
        Ok(Some(ModuleCallSignature { source, call, target }))
    }
}

} // verus!
