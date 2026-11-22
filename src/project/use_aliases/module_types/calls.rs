//! 呼び出しの信号引数を、元の断片の束縛とモジュールの型表から検査する。

use super::{ModuleOutputTypes, ModuleOutputTypesError, UseAliases, aliases::lookup_member, selections::read_bound_type};
use crate::project::{DefinitionPosition, ModuleBodyPosition, ModuleCallInputs, ModuleCallInputsError, ModuleCallPorts, SignalType};
#[cfg(verus_only)]
use super::selections::bound_type;
#[cfg(verus_only)]
use crate::project::circuits::{parsed_circuit_matches, parsed_index_evidence};
use crate::syntax::{AtomKind, Form, circuit::indexed_call_signal};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence, call_argument_positions,
    call_argument_position_bounds, call_argument_position_is_direct};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// モジュールの型表を使って呼び出しを検査するときに見つかった違反。
#[derive(Debug)]
pub enum ModuleInferredCallError<'p, 'a> {
    /// 配線、型の伝播、式や出力の検査に見つかった違反。
    Module(ModuleOutputTypesError<'p, 'a>),
    /// 参照先の署名、入出力数、または実引数の違反。
    Call(ModuleCallInputsError<'p, 'a>),
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn inferred_argument_at(
        &self, module: &ModuleOutputTypes, at: DefinitionPosition, member: usize, ports: &ModuleCallPorts,
        index: int, ty: Option<SignalType>,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = project.circuits_model()[at.file as int];
        let frame = parsed.entry_ranges@[at.entry as int];
        let row = parsed.definitions@[frame.definitions.start + at.definition];
        let arguments = ports.arguments@;
        let form = arguments[index];
        let wiring = &module.expressions.typed.sources.roots.wiring;
        &&& 0 <= index < arguments.len() && form < parsed.syntax.forms@.len()
        &&& if parsed.syntax.forms@[form as int] is Atom && parsed.syntax.forms@[form as int]->Atom_kind is Name {
            exists|position: int| row.signals.start <= position < row.signals.end
                && (#[trigger] parsed.signals@[position]) == form
                && {
                    let slot = position - frame.signals.start;
                    let bound = wiring.signals@[member as int]@[slot];
                    &&& 0 <= slot < wiring.signals@[member as int]@.len()
                    &&& bound.form == form
                    &&& ty == bound_type(&module.expressions.typed, module.expressions.types@, bound.driver)
                }
        } else { ty.is_none() }
    }

    #[verifier::opaque]
    spec fn inferred_arguments_prefix(
        &self, module: &ModuleOutputTypes, at: DefinitionPosition, member: usize, ports: &ModuleCallPorts,
        types: Seq<Option<SignalType>>,
    ) -> bool {
        &&& types.len() <= ports.arguments@.len()
        &&& forall|i: int| 0 <= i < types.len() ==>
            self.inferred_argument_at(module, at, member, ports, i, #[trigger] types[i])
    }

    fn infer_call_arguments(&self, _owner: ModuleBodyPosition, limit: u64, module: &ModuleOutputTypes<'p, 'a>,
        at: DefinitionPosition, member: usize, ports: &ModuleCallPorts<'p, 'a>,
    ) -> (types: Vec<Option<SignalType<'p, 'a>>>)
        requires
            self.can_resolve(), self.module_output_types_result(_owner, limit, Ok(Some(*module))),
            self.module_call_ports_result(at, limit, Ok(Some(*ports))),
            ({
                let members = module.expressions.typed.sources.roots.wiring.drivers.body.members@;
                member < members.len() && members[member as int] == (ModuleBodyPosition { file: at.file, entry: at.entry })
            }),
        ensures types@.len() == ports.arguments@.len(), self.inferred_arguments_prefix(module, at, member, ports, types@),
    {
        let expressions = &module.expressions;
        let typed = &expressions.typed;
        let wiring = &typed.sources.roots.wiring;
        proof {
            self.module_output_types_evidence(_owner, limit, *module);
            self.module_selections_evidence(_owner, limit, *expressions);
            self.module_call_ports_evidence(at, limit, *ports);
            self.module_call_site_evidence(at, limit, ports.signature);
        }
        let project = self.targets.project();
        let source = &project.sources()[at.file];
        let parsed = &project.circuits()[at.file];
        let ghost model = parsed.build_model();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, at.entry as int);
        }
        let frame = &parsed.entry_ranges[at.entry];
        let definition = frame.definitions.start + at.definition;
        proof { build_definition_scope_evidence(source.text, &model, at.entry as int, definition as int); }
        let row = &parsed.definitions[definition];
        let reference = row.references.start + at.reference;
        let forms = parsed.syntax.forms.as_slice();
        let arguments = ports.arguments.as_slice();
        let mut types = Vec::new();
        let mut i = 0;
        assert(self.inferred_arguments_prefix(module, at, member, ports, types@)) by { reveal(UseAliases::inferred_arguments_prefix); };
        while i < arguments.len()
            invariant
                self.can_resolve(), *project == self.targets.project_model(),
                self.module_wiring_result(_owner, limit, Ok(Some(*wiring))), *wiring == module.expressions.typed.sources.roots.wiring,
                *typed == module.expressions.typed, *expressions == module.expressions,
                expressions.types@.len() == wiring.drivers.definitions@.len(),
                member < wiring.drivers.body.members@.len(),
                wiring.drivers.body.members@[member as int] == (ModuleBodyPosition { file: at.file, entry: at.entry }),
                at.file < project.sources_model().len(), at.file < project.circuits_model().len(),
                *source == project.sources_model()[at.file as int], *parsed == project.circuits_model()[at.file as int],
                parsed_circuit_matches(*source, *parsed), model == parsed.build_model(),
                at.entry < parsed.entry_ranges@.len(), at.entry < parsed.syntax.entries@.len(),
                *frame == parsed.entry_ranges@[at.entry as int],
                definition == frame.definitions.start + at.definition,
                frame.definitions.start <= definition < frame.definitions.end <= parsed.definitions@.len(),
                *row == parsed.definitions@[definition as int],
                row.references.start <= reference < row.references.end <= parsed.references@.len(),
                reference == row.references.start + at.reference,
                self.module_call_signature_result(at, limit, Ok(Some(ports.signature))),
                forms@ == parsed.syntax.forms@, arguments@ == ports.arguments@,
                call_argument_positions(forms@, ports.signature.call, arguments@),
                i == types@.len() <= arguments@.len(),
                self.inferred_arguments_prefix(module, at, member, ports, types@),
            decreases arguments@.len() - i,
        {
            proof {
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &model, at.entry as int, definition as int);
                self.module_call_site_evidence(at, limit, ports.signature);
                call_argument_position_bounds(forms@, ports.signature.call, arguments@, i as int);
            }
            let form = arguments[i];
            let ty = if matches!(forms[form], Form::Atom { kind: AtomKind::Name, .. }) {
                proof { call_argument_position_is_direct(forms@, ports.signature.call, arguments@, i as int); }
                let position = indexed_call_signal(source.text, forms, row, parsed.references.as_slice(), reference,
                    &ports.signature.call, parsed.signals.as_slice(), form);
                proof { self.module_signal_index_item(_owner, limit, *wiring, member as int, position as int); }
                let binding = &wiring.signals[member][position - frame.signals.start];
                let value = read_bound_type(typed, expressions.types.as_slice(), binding.driver);
                assert(self.inferred_argument_at(module, at, member, ports, i as int, value));
                value
            } else { None };
            assert(self.inferred_argument_at(module, at, member, ports, i as int, ty));
            let ghost prior = types@;
            types.push(ty);
            assert(self.inferred_arguments_prefix(module, at, member, ports, types@)) by {
                reveal(UseAliases::inferred_arguments_prefix);
                assert forall|j: int| 0 <= j < types@.len() implies
                    self.inferred_argument_at(module, at, member, ports, j, #[trigger] types@[j]) by {
                    if j < i { assert(types@[j] == prior[j]); }
                };
            };
            i += 1;
        }
        types
    }

    spec fn inferred_call(
        &self, module: &ModuleOutputTypes, at: DefinitionPosition, limit: u64,
        result: Result<Option<ModuleCallInputs>, ModuleCallInputsError>,
    ) -> bool {
        let members = module.expressions.typed.sources.roots.wiring.drivers.body.members@;
        let owner = ModuleBodyPosition { file: at.file, entry: at.entry };
        if !members.contains(owner) { result == Ok(None) } else {
            match result {
                Ok(None) => self.module_call_ports_result(at, limit, Ok(None)),
                Err(ModuleCallInputsError::Ports(error)) => self.module_call_ports_result(at, limit, Err(error)),
                _ => exists|ports: ModuleCallPorts, known: Seq<Option<SignalType>>, member: usize|
                    #[trigger] self.module_call_ports_result(at, limit, Ok(Some(ports)))
                    && member < members.len() && members[member as int] == owner
                    && #[trigger] self.inferred_arguments_prefix(module, at, member, &ports, known)
                    && known.len() == ports.arguments@.len()
                    && self.module_inputs_from_plan_match(at, limit, &ports, known, result),
            }
        }
    }

    fn check_inferred_call_in_module(
        &self, owner: ModuleBodyPosition, module: &ModuleOutputTypes<'p, 'a>, at: DefinitionPosition, limit: u64,
    ) -> (result: Result<Option<ModuleCallInputs<'p, 'a>>, ModuleCallInputsError<'p, 'a>>)
        requires self.can_resolve(), self.module_output_types_result(owner, limit, Ok(Some(*module))),
        ensures self.inferred_call(module, at, limit, result),
    {
        let members = module.expressions.typed.sources.roots.wiring.drivers.body.members.as_slice();
        let Some(member) = lookup_member(members, ModuleBodyPosition { file: at.file, entry: at.entry }) else {
            return Ok(None);
        };
        let ports = match self.check_module_call_ports(at, limit) {
            Ok(Some(ports)) => ports,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleCallInputsError::Ports(error)),
        };
        let known = self.infer_call_arguments(owner, limit, module, at, member, &ports);
        let ghost plan = ports;
        let result = match self.check_module_inputs_from_plan(at, limit, ports, known.as_slice()) {
            Ok(checked) => Ok(Some(checked)),
            Err(error) => Err(error),
        };
        assert(!(result matches Err(ModuleCallInputsError::Ports(_))));
        assert(self.inferred_arguments_prefix(module, at, member, &plan, known@));
        assert(self.module_inputs_from_plan_match(at, limit, &plan, known@, result));
        assert(self.inferred_call(module, at, limit, result));
        result
    }

    /// 実引数の照合結果と、型表および元の断片の束縛との対応を表す。
    pub closed spec fn module_inferred_call_result(&self, owner: ModuleBodyPosition, at: DefinitionPosition, limit: u64,
        result: Result<Option<ModuleCallInputs>, ModuleInferredCallError>) -> bool {
        match result {
            Err(ModuleInferredCallError::Module(error)) => self.module_output_types_result(owner, limit, Err(error)),
            _ => (result == Ok(None) && self.module_output_types_result(owner, limit, Ok(None)))
                || exists|module: ModuleOutputTypes| #[trigger] self.module_output_types_result(owner, limit, Ok(Some(module)))
                    && self.inferred_call(&module, at, limit, match result {
                        Ok(call) => Ok(call), Err(ModuleInferredCallError::Call(error)) => Err(error), _ => Ok(None),
                    }),
        }
    }

    /// 指定した呼び出しの実引数を、モジュールの型表と参照先の署名で検査する。
    ///
    /// 直接の信号名は元の断片の束縛から型を得る。リテラルは入力ポートの型で検査する。
    /// 型が未確定の信号と子式は保留する。指定した位置がモジュール内の呼び出しを指さなければ
    /// `None` を返す。
    ///
    /// # Errors
    ///
    /// モジュールの配線と式を検査した後、参照先の署名、入出力数、直接引数の順に違反を返す。
    pub fn check_module_call_with_inferred_types(&self, owner: ModuleBodyPosition, at: DefinitionPosition, limit: u64)
        -> (result: Result<Option<ModuleCallInputs<'p, 'a>>, ModuleInferredCallError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_inferred_call_result(owner, at, limit, result),
    {
        let module = match self.check_module_output_types(owner, limit) {
            Ok(Some(module)) => module,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleInferredCallError::Module(error)),
        };
        match self.check_inferred_call_in_module(owner, &module, at, limit) {
            Ok(checked) => Ok(checked),
            Err(error) => Err(ModuleInferredCallError::Call(error)),
        }
    }
}

} // verus!
