//! 実引数のルートにある通常呼び出しから出力型を得る。

use super::{DefinitionPosition, SignalType, UseAliases};
use crate::project::{LocatedName, PortDirection, ProjectSource};
use crate::syntax::circuit::{BuildDefinition, NamedBuildCircuit, callee_reference_at_form};
use crate::project::use_aliases::function_atoms::copy_location;
#[cfg(verus_only)]
use super::super::direct_output_type;
#[cfg(verus_only)]
use crate::syntax::circuit::definition_call_index;
use vstd::prelude::*;

verus! {

spec fn callee_at(row: &BuildDefinition, parsed: &NamedBuildCircuit, form: usize, reference: int) -> bool {
    &&& row.references.start <= reference < row.references.end <= parsed.references@.len()
    &&& parsed.references@[reference].form == form + 1
    &&& parsed.references@[reference].kind is Callee
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) closed spec fn nested_argument_type(
        &self, at: DefinitionPosition, limit: u64, form: usize, ty: Option<SignalType>,
    ) -> bool {
        let parsed = self.targets.project_model().circuits_model()[at.file as int];
        let row = &parsed.definitions@[parsed.entry_ranges@[at.entry as int].definitions.start + at.definition];
        if !(exists|reference: int| #[trigger] callee_at(row, &parsed, form, reference)) {
            ty.is_none()
        } else {
            exists|reference: int, plan: Result<Option<crate::project::ModuleCallPorts>, crate::project::ModuleCallPortsError>|
                #![trigger callee_at(row, &parsed, form, reference), self.module_call_ports_result(
                    DefinitionPosition { reference: (reference - row.references.start) as usize, ..at }, limit, plan)]
                callee_at(row, &parsed, form, reference)
                && self.module_call_ports_result(
                    DefinitionPosition { reference: (reference - row.references.start) as usize, ..at }, limit, plan)
                && match plan {
                    Ok(Some(ports)) => ports.signature.call.form == form
                        && (ty matches Some(value) && direct_output_type(&ports, 0, value)),
                    Err(_) => ty.is_none(),
                    Ok(None) => false,
                }
        }
    }

    /// 子の署名と入出力数が妥当なら、出力ポートの型を親の検査に渡す。
    /// 子に違反があれば型は未確定となる。全件検査では、その子を検査する順番で診断する。
    pub(super) fn read_nested_argument_type(
        &self, at: DefinitionPosition, limit: u64, source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>,
        row: &BuildDefinition, form: usize,
    ) -> (ty: Option<SignalType<'p, 'a>>)
        requires
            self.can_resolve(), self.module_call_at(at),
            *source == self.targets.project_model().sources_model()[at.file as int],
            *parsed == self.targets.project_model().circuits_model()[at.file as int],
            *row == parsed.definitions@[parsed.entry_ranges@[at.entry as int].definitions.start + at.definition],
            definition_call_index(source.text, parsed.syntax.forms@, *row, parsed.references@),
            row.references.end <= parsed.references@.len(),
            row.expression.start < form < row.expression.end,
        ensures self.nested_argument_type(at, limit, form, ty),
            ty matches Some(value) ==> crate::project::location_in_source(value.origin),
    {
        let refs = parsed.references.as_slice();
        let Some(reference) = callee_reference_at_form(source.text, parsed.syntax.forms.as_slice(), row, refs, form) else {
            return None;
        };
        assert(callee_at(row, parsed, form, reference as int));
        let child = DefinitionPosition { reference: reference - row.references.start, ..at };
        assert(self.module_call_at(child));
        let checked = self.check_module_call_ports(child, limit);
        let ghost plan = checked;
        let ports = match checked {
            Ok(Some(ports)) => ports,
            Err(_) => {
                assert(self.nested_argument_type(at, limit, form, None));
                return None;
            },
            Ok(None) => {
                proof { self.module_call_ports_present(child, limit); }
                unreachable!()
            },
        };
        proof {
            self.module_call_ports_evidence(child, limit, ports);
            self.module_call_site_evidence(child, limit, ports.signature);
            assert(ports.signature.call.form == form);
        }
        let Some(port) = ports.signature.target.port(PortDirection::Output, 0) else {
            proof { assert(false); }
            unreachable!()
        };
        proof { self.module_call_port_location(child, limit, ports.signature, PortDirection::Output, 0, port); }
        let origin = match port.annotation {
            Some(annotation) => copy_location(annotation),
            None => LocatedName { source: ports.signature.source, span: ports.signature.call.span.start..ports.signature.call.span.end },
        };
        let value = SignalType { ty: port.ty, origin };
        assert(direct_output_type(&ports, 0, value));
        assert(self.module_call_ports_result(child, limit, plan));
        assert(self.nested_argument_type(at, limit, form, Some(value)));
        Some(value)
    }
}

} // verus!
