//! 呼び出しを名前解決し、参照先の宣言から必要な入出力数を求める。

mod checks;
mod inputs;
mod outputs;
mod typed;
pub use checks::FuncArityError;
pub use inputs::{CallInputError, CallInputReason, CheckedCallInputs, FuncCallInputsError};
pub use outputs::{FuncCallOutputError, FuncCallOutputTypes};
pub use typed::{CallPortType, FuncCallSignature, FuncCallSignatureError, TypedFuncCall};

use super::{DefinitionBinding, DefinitionReferenceError, ResolvedDefinitionReference, UseAliases};
#[cfg(verus_only)]
use super::{DefinitionPosition, FunctionCallSite};
#[cfg(verus_only)]
use crate::project::circuits::{parsed_index_evidence, parsed_circuit_matches};
use crate::project::declarations::key_of;
#[cfg(verus_only)]
use crate::project::declarations::{declaration_location_evidence, located_name_evidence};
use crate::project::{LocatedName, ProjectSource};
#[cfg(verus_only)]
use crate::project::{CircuitProject, location_in_source};
use crate::syntax::circuit::{
    CallShape, Head, RoutineArity, indexed_call_shape, named_build_entry, routine_arity,
};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    build_definition_scope_evidence, build_entry_ranges_evidence, call_arguments_match, call_shape_matches,
    indexed_call_arguments, routine_arity_matches,
};
use vstd::prelude::*;

verus! {

/// 組み合わせ回路の呼び出し先と、その入出力数の根拠。
#[derive(Debug)]
pub enum FuncCallTarget<'p, 'a> {
    /// 名前解決で選ばれた基底 NOR。入力は 2 ポート、出力は 1 ポート。
    Nor,
    /// 名前解決で選ばれた関数の署名。
    Function {
        /// 宣言の入出力ポート数。
        arity: RoutineArity,
        /// 宣言のソースと関数名の範囲。
        declaration: LocatedName<'p, 'a>,
        /// 正規化して集約したプロジェクトのソース一覧の添字。
        file: usize,
        /// 宣言を含むファイルの厳格索引の添字。
        entry: usize,
    },
}

impl FuncCallTarget<'_, '_> {
    /// 名前解決で選んだ参照先の入出力数を表す。
    pub open spec fn port_counts(&self) -> RoutineArity {
        match self {
            FuncCallTarget::Nor => RoutineArity { inputs: 2, outputs: 1 },
            FuncCallTarget::Function { arity, .. } => *arity,
        }
    }

    /// 呼び出し先が受け取る入力と返す出力のポート数を返す。
    pub fn ports(&self) -> (ports: RoutineArity)
        ensures ports == self.port_counts(),
    {
        match self {
            Self::Nor => RoutineArity { inputs: 2, outputs: 1 },
            Self::Function { arity, .. } => *arity,
        }
    }
}

/// 呼び出し元の構文と、名前解決で選ばれた参照先。
#[derive(Debug)]
pub struct FuncCallArity<'p, 'a> {
    /// 呼び出し元のファイルと文書版。
    pub source: &'p ProjectSource<'a>,
    /// 呼び出し全体の UTF-8 半開バイト範囲と、直接の引数数。
    pub call: CallShape,
    /// 呼び出しが解決された関数または基底 NOR。
    pub target: FuncCallTarget<'p, 'a>,
}

spec fn target_ports_match(project: &CircuitProject, resolved: ResolvedDefinitionReference, target: FuncCallTarget) -> bool {
    match (resolved.binding, target) {
        (DefinitionBinding::Nor, FuncCallTarget::Nor) => true,
        (DefinitionBinding::Declaration { source, form }, FuncCallTarget::Function { arity, declaration, file, entry }) => {
            let circuits = project.circuits_model();
            &&& file < circuits.len() && file < project.sources_model().len() && entry < circuits[file as int].syntax.entries@.len()
            &&& *source == project.sources_model()[file as int]
            &&& circuits[file as int].syntax.entries@[entry as int].head is Func
            &&& circuits[file as int].syntax.entries@[entry as int].form == form.form
            &&& form.head is Func
            &&& *declaration.source == *source && declaration.span == form.name.span
            &&& location_in_source(declaration)
            &&& routine_arity_matches(source.text, &circuits[file as int].syntax, entry as int, Some(arity))
        },
        _ => false,
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) open spec fn func_call_at(&self, file: usize, entry: usize, definition: usize, reference: usize) -> bool {
        let parsed = self.targets.project_model().circuits_model()[file as int];
        let def = parsed.entry_ranges@[entry as int].definitions.start + definition;
        let indexed = parsed.references@[parsed.definitions@[def].references.start + reference];
        self.position_exists(file, entry, definition, reference)
            && entry < parsed.syntax.entries@.len()
            && parsed.syntax.entries@[entry as int].head is Func && indexed.kind is Callee
    }

    pub(super) open spec fn func_position_matches(
        &self, binding: DefinitionBinding, position: Option<(usize, usize)>,
    ) -> bool {
        match binding {
            DefinitionBinding::Nor => position.is_none(),
            DefinitionBinding::Declaration { source, form } => {
                &&& position matches Some((file, entry))
                &&& {
                    let project = self.targets.project_model();
                    let circuits = project.circuits_model();
                    &&& file < circuits.len() && file < project.sources_model().len()
                    &&& *source == project.sources_model()[file as int]
                    &&& entry < circuits[file as int].syntax.entries@.len()
                    &&& circuits[file as int].syntax.entries@[entry as int].head is Func
                    &&& circuits[file as int].syntax.entries@[entry as int].form == form.form
                    &&& form.head is Func
                    &&& location_in_source(LocatedName { source, span: form.name.span })
                }
            },
        }
    }

    /// 解決済みの呼び出し先を、関数宣言のファイルと索引項目で示す。
    pub(super) fn resolved_func_position(
        &self, Ghost(caller): Ghost<(usize, usize, usize, usize)>,
        resolved: &ResolvedDefinitionReference<'p, 'a>,
    ) -> (position: Option<(usize, usize)>)
        requires
            self.can_resolve(),
            self.func_call_at(caller.0, caller.1, caller.2, caller.3),
            self.definition_resolution_evidence(caller.0, caller.1, caller.2, caller.3, Ok(*resolved)),
        ensures self.func_position_matches(resolved.binding, position),
    {
        let (source, form) = match resolved.binding {
            DefinitionBinding::Declaration { source, form } => (source, form),
            DefinitionBinding::Nor => return None,
        };
        let project = self.targets.project();
        proof {
            self.resolved_func_declaration(caller.0, caller.1, caller.2, caller.3, *resolved, source, form);
            self.targets.declarations_cover_project();
        }
        let table = self.targets.exports().declarations();
        let key = key_of(form);
        let (file, name) = table.selected_declaration_position(key,
            Ghost(*project), Ghost(*source), Ghost(*form));
        proof { declaration_location_evidence(table, key, source, form); }
        let circuit = &project.circuits()[file];
        proof {
            assert(parsed_circuit_matches(*source, *circuit));
            parsed_index_evidence(*source, *circuit);
        }
        Some((file, named_build_entry(source.text, circuit, name)))
    }

    /// 結果が、同じ右辺の呼び出しと名前解決で選んだ署名に対応することを表す。
    pub closed spec fn func_call_arity_evidence(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        result: Result<Option<FuncCallArity>, DefinitionReferenceError>,
    ) -> bool {
        if !self.func_call_at(file, entry, definition, reference) {
            result == Ok(None)
        } else {
            let project = self.targets.project_model();
            let source = &project.sources_model()[file as int];
            let parsed = project.circuits_model()[file as int];
            let row = parsed.definitions@[parsed.entry_ranges@[entry as int].definitions.start + definition];
            let indexed = parsed.references@[row.references.start + reference];
            match result {
                Ok(Some(call)) =>
                    *call.source == *source
                        && call.call.form + 1 == indexed.form
                        && location_in_source(LocatedName { source: call.source, span: call.call.span })
                        && call_shape_matches(source.text, parsed.syntax.forms@, row, indexed, Some(call.call))
                        && call_arguments_match(parsed.syntax.forms@, call.call)
                        && exists|resolved: ResolvedDefinitionReference|
                            #[trigger] self.definition_resolution_evidence(file, entry, definition, reference, Ok(resolved))
                                && target_ports_match(&project, resolved, call.target),
                Err(error) => !(error is UnknownPosition)
                    && self.definition_resolution_evidence(file, entry, definition, reference, Err(error)),
                Ok(None) => false,
            }
        }
    }

    /// 解決済みの関数呼び出しから、展開順の定理に使う参照位置を得る。
    pub proof fn expansion_site_for_call(
        &self, at: DefinitionPosition, call: FuncCallArity<'p, 'a>,
    ) -> (site: FunctionCallSite<'p, 'a>)
        requires
            self.func_call_arity_evidence(at.file, at.entry, at.definition, at.reference, Ok(Some(call))),
            call.target is Function,
        ensures
            self.expansion_call_in_source(site), site.position == at,
            call.target matches FuncCallTarget::Function { file, entry, .. } && site.target == (file, entry),
    {
        let project = self.targets.project_model();
        let resolved = choose|resolved: ResolvedDefinitionReference|
            #[trigger] self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, Ok(resolved))
                && target_ports_match(&project, resolved, call.target);
        let file = call.target->Function_file;
        let entry = call.target->Function_entry;
        assert(self.func_position_matches(resolved.binding, Some((file, entry))));
        self.expansion_site_for_binding(at, (file, entry), resolved)
    }

    /// `func` の右辺にある通常呼び出しを解決し、実引数数と参照先の入出力数を返す。
    ///
    /// `file` は集約後のソース一覧、`entry` はファイルの厳格索引を指す。
    /// `definition` は索引項目内、`reference` はその定義内の相対添字。
    /// 範囲外の添字、関数以外の項目、型名の参照には `None` を返す。
    ///
    /// # Errors
    ///
    /// 呼び出し名の解決に失敗した場合は、参照名の範囲と、非公開などの理由を返す。
    pub fn resolve_func_call_arity(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
    ) -> (result: Result<Option<FuncCallArity<'p, 'a>>, DefinitionReferenceError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_call_arity_evidence(file, entry, definition, reference, result),
    {
        let project = self.targets.project();
        let circuits = project.circuits();
        if file >= circuits.len() { return Ok(None); }
        let parsed = &circuits[file];
        if entry >= parsed.syntax.entries.len() || !matches!(parsed.syntax.entries[entry].head, Head::Func) {
            return Ok(None);
        }
        let source = &project.sources()[file];
        let ghost model = parsed.build_model();
        proof {
            assert(parsed_circuit_matches(*source, *parsed));
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, entry as int);
        }
        let defs = &parsed.entry_ranges[entry].definitions;
        if definition >= defs.end - defs.start { return Ok(None); }
        let def = defs.start + definition;
        proof { build_definition_scope_evidence(source.text, &model, entry as int, def as int); }
        let row = &parsed.definitions[def];
        if reference >= row.references.end - row.references.start { return Ok(None); }
        let position = row.references.start + reference;
        let shape = indexed_call_shape(source.text, parsed.syntax.forms.as_slice(), row, parsed.references.as_slice(), position);
        let Some(call) = shape else { return Ok(None); };
        proof {
            located_name_evidence(LocatedName { source, span: call.span });
            indexed_call_arguments(source.text, parsed.syntax.forms@, *row, parsed.references@[position as int], call);
        }
        assert(self.func_call_at(file, entry, definition, reference));
        let resolved = match self.resolve_definition_reference(file, entry, definition, reference) {
            Ok(resolved) => resolved,
            Err(error) => {
                proof {
                    if error is UnknownPosition {
                        self.valid_position_is_not_unknown(file, entry, definition, reference);
                    }
                }
                return Err(error);
            },
        };
        let ghost resolution = resolved;
        let position = self.resolved_func_position(Ghost((file, entry, definition, reference)), &resolved);
        let target = match resolved.binding {
            DefinitionBinding::Nor => FuncCallTarget::Nor,
            DefinitionBinding::Declaration { source, form } => {
                let Some((target_file, target_entry)) = position else {
                    proof { assert(false); }
                    unreachable!()
                };
                let target_circuit = &circuits[target_file];
                proof {
                    assert(parsed_circuit_matches(*source, *target_circuit));
                    parsed_index_evidence(*source, *target_circuit);
                }
                let Some(arity) = routine_arity(source.text, &target_circuit.syntax, target_entry) else {
                    proof { assert(false); }
                    unreachable!()
                };
                let declaration = LocatedName { source, span: form.name.span.start..form.name.span.end };
                FuncCallTarget::Function { arity, declaration, file: target_file, entry: target_entry }
            },
        };
        assert(target_ports_match(project, resolution, target));
        Ok(Some(FuncCallArity { source, call, target }))
    }
}

} // verus!
