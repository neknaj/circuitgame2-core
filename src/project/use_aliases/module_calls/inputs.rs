//! 明示定数と判明済みの実引数の型を、呼び出し先の入力ポート型に照合する。

use super::{ModuleCallPorts, ModuleCallPortsError, UseAliases};
#[cfg(verus_only)]
use super::ModuleCallTarget;
use crate::project::{CallInputReason, DefinitionPosition, LocatedName, PortDirection, ResolvedPortType, SignalType};
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::{CallPortType, circuits::{is_form_location, parsed_index_evidence}};
use crate::project::use_aliases::{call_arity::check_leaf, function_atoms::{copy_location, copy_signal_type}};
#[cfg(verus_only)]
use crate::project::use_aliases::call_arity::{checked_nor_literal_width, leaf_result};
use crate::syntax::Form;
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_spans_valid, nested_list_indices, circuit::{
    call_argument_position_bounds, call_argument_positions,
}};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 呼び出しの引数ごとに、検査で得た型とその根拠を持つ。
#[derive(Debug)]
pub struct ModuleCallInputs<'p, 'a> {
    /// 名前解決した署名と、入力ポートごとの元の構文位置。
    pub ports: ModuleCallPorts<'p, 'a>,
    /// 入力ポート順の型。供給された型もソースから読める定数もない箇所は `None`。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

/// 呼び出し先の解決や引数の照合で見つかった違反。
#[derive(Debug)]
pub enum ModuleCallInputsError<'p, 'a> {
    /// 名前解決、署名または入出力数の診断。
    Ports(ModuleCallPortsError<'p, 'a>),
    /// 渡された型の要素数が直接の引数数と異なる。
    TypeCount {
        /// 呼び出しが持つ直接の引数数。
        expected_count: usize,
        /// 呼び出し側が渡した型情報の要素数。
        supplied: usize,
    },
    /// 先頭から数えて最初に検査に失敗した引数。
    Argument {
        /// 入力ポートと引数の添字。先頭は0。
        index: usize,
        /// 引数式全体の元のソース範囲。
        argument: LocatedName<'p, 'a>,
        /// 入力ポートの要求型。
        expected: ResolvedPortType<'p, 'a>,
        /// 要求型の注釈。基底 NOR の場合は `None`。
        required_at: Option<LocatedName<'p, 'a>>,
        /// 不一致やリテラル幅の違反の理由。
        reason: CallInputReason<'p, 'a>,
    },
}

spec fn argument_type(
    forms: Seq<Form>, ports: &ModuleCallPorts, limit: u64, at: usize, actual: Option<SignalType>,
    result: Result<Option<SignalType>, CallInputReason>,
) -> bool {
    let root = ports.arguments@[at as int];
    &&& at < ports.arguments@.len() && root < forms.len()
    &&& exists|port: CallPortType| #[trigger] ports.signature.target.port_matches(PortDirection::Input, at, Some(port))
        && leaf_result(ports.signature.source, forms[root as int], &port, actual, limit, result)
}

#[verifier::opaque]
spec fn valid_input_prefix(
    forms: Seq<Form>, ports: &ModuleCallPorts, limit: u64, known: Seq<Option<SignalType>>, prefix: Seq<Option<SignalType>>,
) -> bool {
    &&& prefix.len() <= known.len() == ports.arguments@.len()
    &&& forall|i: int| 0 <= i < prefix.len() ==>
        argument_type(forms, ports, limit, i as usize, known[i], Ok(#[trigger] prefix[i]))
}

spec fn input_error(
    forms: Seq<Form>, ports: &ModuleCallPorts, limit: u64, known: Seq<Option<SignalType>>, error: ModuleCallInputsError,
) -> bool {
    match error {
        ModuleCallInputsError::TypeCount { expected_count, supplied } => expected_count == ports.arguments@.len()
            && supplied == known.len() && expected_count != supplied,
        ModuleCallInputsError::Argument { index, argument, expected, required_at, reason } => {
            let source = ports.signature.source;
            let root = ports.arguments@[index as int];
            &&& index < ports.arguments@.len() && root < forms.len()
            &&& is_form_location(source, forms[root as int], argument)
            &&& exists|before: Seq<Option<SignalType>>, port: CallPortType|
                #[trigger] valid_input_prefix(forms, ports, limit, known, before) && before.len() == index
                && #[trigger] ports.signature.target.port_matches(PortDirection::Input, index, Some(port))
                && expected == port.ty && required_at == match port.annotation {
                    Some(annotation) => Some(*annotation), None => None,
                }
                && leaf_result(source, forms[root as int], &port, known[index as int], limit, Err(reason))
        },
        ModuleCallInputsError::Ports(_) => false,
    }
}

spec fn checked_input_types(
    forms: Seq<Form>, ports: &ModuleCallPorts, limit: u64, known: Seq<Option<SignalType>>,
    result: Result<Vec<Option<SignalType>>, ModuleCallInputsError>,
) -> bool {
    match result {
        Ok(types) => types@.len() == ports.arguments@.len() && valid_input_prefix(forms, ports, limit, known, types@),
        Err(error) => input_error(forms, ports, limit, known, error),
    }
}

fn check_inputs<'p, 'a>(
    forms: &[Form], ports: &ModuleCallPorts<'p, 'a>, limit: u64, known: &[Option<SignalType<'p, 'a>>],
) -> (result: Result<Vec<Option<SignalType<'p, 'a>>>, ModuleCallInputsError<'p, 'a>>)
    requires
        call_argument_positions(forms@, ports.signature.call, ports.arguments@),
        complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(ports.signature.source.text, forms@, ports.signature.source.text.spec_bytes().len() as int),
        match ports.signature.target {
            ModuleCallTarget::Nor => ports.arguments@.len() == 2,
            ModuleCallTarget::Routine { signature, .. } => ports.arguments@.len() == signature.inputs@.len(),
            ModuleCallTarget::StateElement { .. } => false,
        },
    ensures checked_input_types(forms@, ports, limit, known@, result),
{
    let count = ports.arguments.len();
    if known.len() != count {
        return Err(ModuleCallInputsError::TypeCount { expected_count: count, supplied: known.len() });
    }
    let source = ports.signature.source;
    let mut types = Vec::new();
    let mut i = 0;
    assert(valid_input_prefix(forms@, ports, limit, known@, types@)) by { reveal(valid_input_prefix); };
    while i < count
        invariant
            count == ports.arguments@.len() == known@.len(), i == types@.len() <= count,
            *source == *ports.signature.source,
            call_argument_positions(forms@, ports.signature.call, ports.arguments@),
            complete_list_indices(forms@), nested_list_indices(forms@),
            form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
            match ports.signature.target {
                ModuleCallTarget::Nor => count == 2,
                ModuleCallTarget::Routine { signature, .. } => count == signature.inputs@.len(),
                ModuleCallTarget::StateElement { .. } => false,
            },
            valid_input_prefix(forms@, ports, limit, known@, types@),
        decreases count - i,
    {
        proof { call_argument_position_bounds(forms@, ports.signature.call, ports.arguments@, i as int); }
        let root = ports.arguments[i];
        let Some(port) = ports.signature.target.port(PortDirection::Input, i) else {
            proof { assert(false); }
            unreachable!()
        };
        let ty = copy_signal_type(&known[i]);
        let checked = check_leaf(source, forms, root, &port, ty, limit);
        let accepted = match checked {
            Ok(accepted) => accepted,
            Err(reason) => {
                let argument = form_location(source, forms, root);
                let required_at = match port.annotation {
                    Some(annotation) => Some(copy_location(annotation)), None => None,
                };
                let error = ModuleCallInputsError::Argument { index: i, argument, expected: port.ty, required_at, reason };
                assert(input_error(forms@, ports, limit, known@, error));
                return Err(error);
            },
        };
        assert(argument_type(forms@, ports, limit, i, known@[i as int], Ok(accepted)));
        let ghost prior = types@;
        types.push(accepted);
        assert(valid_input_prefix(forms@, ports, limit, known@, types@)) by {
            reveal(valid_input_prefix);
            assert forall|j: int| 0 <= j < types@.len() implies
                argument_type(forms@, ports, limit, j as usize, known@[j], Ok(#[trigger] types@[j])) by {
                if j < i { assert(types@[j] == prior[j]); }
            };
        };
        i += 1;
    }
    Ok(types)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(in crate::project::use_aliases) closed spec fn module_nor_literals_fit(
        &self, at: DefinitionPosition, limit: u64, checked: &ModuleCallInputs,
    ) -> bool {
        let forms = self.targets.project_model().circuits_model()[at.file as int].syntax.forms@;
        let source = checked.ports.signature.source.text;
        forall|i: int| 0 <= i < checked.ports.arguments@.len() ==> {
            let root = #[trigger] checked.ports.arguments@[i];
            let form = forms[root as int];
            let span = crate::syntax::form_span(form);
            form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal) ==>
                crate::project::circuit_literal_width_matches(source.spec_bytes()[span.start as int..span.end as int],
                    Some(1), limit, Ok(1))
        }
    }

    /// 検査結果から、NOR に渡した各二進・十六進リテラルの幅の根拠を取り出す。
    pub(in crate::project::use_aliases) proof fn checked_module_nor_literals(
        &self, at: DefinitionPosition, limit: u64, ports: &ModuleCallPorts, known: Seq<Option<SignalType>>, checked: &ModuleCallInputs,
    )
        requires self.module_inputs_from_plan_match(at, limit, ports, known, Ok(Some(*checked))),
            ports.signature.target is Nor,
        ensures self.module_nor_literals_fit(at, limit, checked),
    {
        let forms = self.targets.project_model().circuits_model()[at.file as int].syntax.forms@;
        let source = ports.signature.source;
        assert(checked.ports == *ports);
        vstd::std_specs::vec::axiom_spec_len(&ports.arguments);
        reveal(argument_type);
        reveal(valid_input_prefix);
        assert forall|i: int| 0 <= i < ports.arguments@.len() implies {
            let root = #[trigger] ports.arguments@[i];
            let form = forms[root as int];
            let span = crate::syntax::form_span(form);
            form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal) ==>
                crate::project::circuit_literal_width_matches(source.text.spec_bytes()[span.start as int..span.end as int],
                    Some(1), limit, Ok(1))
        } by {
            let root = ports.arguments@[i];
            let form = forms[root as int];
            if form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal) {
                let typed = checked.types@[i];
                let index = i as usize;
                assert(index as int == i);
                assert(argument_type(forms, ports, limit, index, known[i], Ok(typed)));
                assert(exists|port: CallPortType|
                    #[trigger] ports.signature.target.port_matches(PortDirection::Input, index, Some(port))
                    && leaf_result(source, form, &port, known[i], limit, Ok(typed)));
                let port = choose|port: CallPortType|
                    #[trigger] ports.signature.target.port_matches(PortDirection::Input, index, Some(port))
                    && leaf_result(source, form, &port, known[i], limit, Ok(typed));
                ports.signature.target.nor_input_width(index, port);
                checked_nor_literal_width(source, form, &port, known[i], limit, typed);
            }
        };
    }

    /// 実引数の構文位置から、NOR の入力幅を照合した結果を取り出す。
    pub(in crate::project::use_aliases) proof fn module_nor_literal_item(
        &self, at: DefinitionPosition, limit: u64, checked: &ModuleCallInputs, i: int,
    )
        requires self.module_nor_literals_fit(at, limit, checked), 0 <= i < checked.ports.arguments@.len(),
        ensures ({
            let source = checked.ports.signature.source.text;
            let forms = self.targets.project_model().circuits_model()[at.file as int].syntax.forms@;
            let form = forms[checked.ports.arguments@[i] as int];
            let span = crate::syntax::form_span(form);
            form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal) ==>
                crate::project::circuit_literal_width_matches(source.spec_bytes()[span.start as int..span.end as int],
                    Some(1), limit, Ok(1))
        }),
    {
    }

    /// 照合で返す入出力計画は、照合に渡した計画と同じである。
    pub(in crate::project::use_aliases) proof fn module_inputs_plan_identity(
        &self, at: DefinitionPosition, limit: u64, ports: &ModuleCallPorts, known: Seq<Option<SignalType>>, checked: ModuleCallInputs,
    )
        requires self.module_inputs_from_plan_match(at, limit, ports, known, Ok(Some(checked))),
        ensures checked.ports == *ports,
    {
    }

    pub(in crate::project::use_aliases) closed spec fn module_inputs_from_plan_match(
        &self, at: DefinitionPosition, max_width: u64, ports: &ModuleCallPorts, known: Seq<Option<SignalType>>,
        result: Result<Option<ModuleCallInputs>, ModuleCallInputsError>,
    ) -> bool {
        let forms = self.targets.project_model().circuits_model()[at.file as int].syntax.forms@;
        match result {
            Ok(Some(checked)) => checked.ports == *ports
                && checked_input_types(forms, ports, max_width, known, Ok(checked.types)),
            Err(error) => checked_input_types(forms, ports, max_width, known, Err(error)),
            Ok(None) => false,
        }
    }

    /// 入出力数を検査済みの署名に、直接の引数の型を照合する。
    pub(in crate::project::use_aliases) fn check_module_inputs_from_plan(
        &self, at: DefinitionPosition, max_width: u64, ports: ModuleCallPorts<'p, 'a>, known: &[Option<SignalType<'p, 'a>>],
    ) -> (result: Result<ModuleCallInputs<'p, 'a>, ModuleCallInputsError<'p, 'a>>)
        requires self.can_resolve(), self.module_call_ports_result(at, max_width, Ok(Some(ports))),
        ensures
            self.module_inputs_from_plan_match(at, max_width, &ports, known@, match result {
                Ok(checked) => Ok(Some(checked)), Err(error) => Err(error),
            }),
            self.module_call_inputs_result(at, max_width, known@, match result {
                Ok(checked) => Ok(Some(checked)), Err(error) => Err(error),
            }),
            !(result matches Err(ModuleCallInputsError::Ports(_))),
            known@.len() == ports.arguments@.len() ==> !(result matches Err(ModuleCallInputsError::TypeCount { .. })),
    {
        proof {
            self.module_call_ports_evidence(at, max_width, ports);
            self.module_call_site_evidence(at, max_width, ports.signature);
        }
        let project = self.targets.project();
        let parsed = &project.circuits()[at.file];
        proof { parsed_index_evidence(*ports.signature.source, *parsed); }
        let forms = parsed.syntax.forms.as_slice();
        let types = check_inputs(forms, &ports, max_width, known)?;
        Ok(ModuleCallInputs { ports, types })
    }

    /// 照合結果を元の呼び出し、供給された型、引数順の診断に対応付ける。
    pub closed spec fn module_call_inputs_result(
        &self, at: DefinitionPosition, max_width: u64, known: Seq<Option<SignalType>>,
        result: Result<Option<ModuleCallInputs>, ModuleCallInputsError>,
    ) -> bool {
        let forms = self.targets.project_model().circuits_model()[at.file as int].syntax.forms@;
        match result {
            Ok(None) => self.module_call_ports_result(at, max_width, Ok(None)),
            Ok(Some(checked)) => self.module_call_ports_result(at, max_width, Ok(Some(checked.ports)))
                && checked_input_types(forms, &checked.ports, max_width, known, Ok(checked.types)),
            Err(ModuleCallInputsError::Ports(error)) => self.module_call_ports_result(at, max_width, Err(error)),
            Err(error) => exists|ports: ModuleCallPorts| #[trigger] self.module_call_ports_result(at, max_width, Ok(Some(ports)))
                && checked_input_types(forms, &ports, max_width, known, Err(error)),
        }
    }

    /// モジュール呼び出しの定数と、呼び出し側が与えた引数型を入力ポートと照合する。
    ///
    /// `at` が指す呼び出しの直接引数と同じ順で `known` を渡す。定数の型はソースから求める。
    /// 信号と子式は、型情報が `None` なら保留する。与えられた型とその出典は、
    /// 呼び出し側の型推論結果として受け取り、出典の範囲と文書版は再検査しない。
    ///
    /// # Errors
    ///
    /// 名前解決と入出力数、型情報の件数、先頭からの引数の順に検査して最初の違反を返す。
    pub fn check_module_call_inputs(&self, at: DefinitionPosition, max_width: u64, known: &[Option<SignalType<'p, 'a>>])
        -> (result: Result<Option<ModuleCallInputs<'p, 'a>>, ModuleCallInputsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_call_inputs_result(at, max_width, known@, result),
    {
        let ports = match self.check_module_call_ports(at, max_width) {
            Ok(Some(ports)) => ports,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleCallInputsError::Ports(error)),
        };
        let checked = self.check_module_inputs_from_plan(at, max_width, ports, known)?;
        Ok(Some(checked))
    }
}

} // verus!
