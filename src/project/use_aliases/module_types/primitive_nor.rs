//! 単一ビットの基底 NOR を、フィードバックを保ったまま tick 用の配線に変換する。

use super::{ModuleCalls, ModuleCallsError, UseAliases, copy_location};
use crate::netlist::{ClockedNor, NorGate, NorNetlist, Wire};
use crate::project::{LocatedName, ModuleBodyPosition, ModuleCallTarget, ModuleWiring, OutputDriver, ResolvedPortType,
    TypedPort, circuits::{form_location, read_indexed_atom}};
use crate::syntax::{AtomKind, Form, circuit::indexed_call_signal, read_bit_literal};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::netlist::{clocked_wiring_from_endpoints, output_ports_available, wire_available};
#[cfg(verus_only)]
use crate::project::circuits::{is_form_location, parsed_index_evidence};
#[cfg(verus_only)]
use crate::syntax::{bit_literal_value_at, form_span, circuit::{build_definition_scope_evidence,
    build_entry_ranges_evidence, call_argument_position_bounds, call_argument_position_is_direct}};
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::encode_utf8_decode_utf8};

verus! {

/// 単一ビットの基底 NOR を変換する段階の診断。
#[derive(Debug)]
pub enum PrimitiveModuleError<'p, 'a> {
    /// モジュールの型検査または呼び出しの違反。
    Module(ModuleCallsError<'p, 'a>),
    /// 現在の変換対象に含まれないポート型。
    Port(LocatedName<'p, 'a>),
    /// 現在の変換対象に含まれない定義の右辺。
    Definition(LocatedName<'p, 'a>),
    /// 現在の変換対象に含まれない実引数。
    Argument(LocatedName<'p, 'a>),
}

spec fn one_bit_ports(ports: Seq<TypedPort>, end: int) -> bool {
    &&& 0 <= end <= ports.len()
    &&& forall|i: int| 0 <= i < end ==> (#[trigger] ports[i]).ty == ResolvedPortType::Bits(1)
}

spec fn first_unsupported_port(ports: Seq<TypedPort>, site: LocatedName) -> bool {
    exists|i: int| 0 <= i < ports.len() && one_bit_ports(ports, i)
        && (#[trigger] ports[i]).ty != ResolvedPortType::Bits(1) && ports[i].annotation == site
}

fn unsupported_port(ports: &[TypedPort]) -> (bad: Option<usize>)
    ensures match bad {
        None => one_bit_ports(ports@, ports@.len() as int),
        Some(i) => i < ports@.len() && one_bit_ports(ports@, i as int) && ports@[i as int].ty != ResolvedPortType::Bits(1),
    },
{
    let mut i = 0;
    while i < ports.len()
        invariant one_bit_ports(ports@, i as int),
        decreases ports@.len() - i,
    {
        if !matches!(ports[i].ty, ResolvedPortType::Bits(1)) { return Some(i); }
        i += 1;
    }
    None
}

spec fn driver_wire(driver: OutputDriver) -> Wire {
    match driver {
        OutputDriver::Input(i) => Wire::Input(i),
        OutputDriver::Definition(i) => Wire::Gate(i),
    }
}

fn map_driver(driver: OutputDriver) -> (wire: Wire)
    ensures wire == driver_wire(driver),
{
    match driver {
        OutputDriver::Input(i) => Wire::Input(i),
        OutputDriver::Definition(i) => Wire::Gate(i),
    }
}

spec fn literal_bit(source: &str, form: Form, bit: bool) -> bool {
    let span = form_span(form);
    let bytes = source.spec_bytes()[span.start as int..span.end as int];
    &&& form is Atom
    &&& match form->Atom_kind {
        AtomKind::Natural => bytes == if bit { "1".spec_bytes() } else { "0".spec_bytes() },
        AtomKind::Binary | AtomKind::Hexadecimal => bit == bit_literal_value_at(bytes, 0),
        _ => false,
    }
}

spec fn literal_value_fits(source: &str, form: Form) -> bool {
    let span = form_span(form);
    let bytes = source.spec_bytes()[span.start as int..span.end as int];
    form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal) ==>
        forall|i: nat| i >= 1 ==> !#[trigger] bit_literal_value_at(bytes, i)
}

fn read_literal_bit(source: &str, forms: &[Form], root: usize) -> (bit: Option<bool>)
    requires root < forms@.len(), crate::syntax::form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        bit matches Some(value) ==> literal_bit(source, forms@[root as int], value),
        ({
            let form = forms@[root as int];
            let span = form_span(form);
            bit.is_some() && form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal)
                ==> source.spec_bytes()[span.start as int..span.end as int].len() > 2
        }),
        bit.is_none() ==> !(exists|value: bool| literal_bit(source, forms@[root as int], value)),
{
    match forms[root] {
        Form::Atom { kind: AtomKind::Natural, .. } => {
            let (word, _) = read_indexed_atom(source, forms, root);
            proof {
                encode_utf8_decode_utf8(word@);
                encode_utf8_decode_utf8("0"@);
                encode_utf8_decode_utf8("1"@);
            }
            if word == "0" { return Some(false); }
            if word == "1" { return Some(true); }
            assert(word.spec_bytes() != "0".spec_bytes() && word.spec_bytes() != "1".spec_bytes());
            None
        },
        Form::Atom { kind: AtomKind::Binary | AtomKind::Hexadecimal, .. } => {
            let (word, _) = read_indexed_atom(source, forms, root);
            proof { crate::syntax::bit_literal_kind_has_digits(word.spec_bytes()); }
            let Some(literal) = read_bit_literal(word) else {
                proof { assert(false); }
                unreachable!()
            };
            Some(literal.bit(0))
        },
        _ => None,
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn primitive_operand_matches(&self, checked: &ModuleCalls, index: int, arg: int, wire: Wire) -> bool {
        let call = checked.calls@[index];
        let wiring = &checked.module.expressions.typed.sources.roots.wiring;
        let parsed = self.targets.project_model().circuits_model()[call.at.file as int];
        let frame = parsed.entry_ranges@[call.at.entry as int];
        let definition = parsed.definitions@[frame.definitions.start + call.at.definition];
        let root = call.inputs.ports.arguments@[arg];
        let form = parsed.syntax.forms@[root as int];
        if form is Atom && form->Atom_kind is Name {
            exists|position: int| definition.signals.start <= position < definition.signals.end
                && (#[trigger] parsed.signals@[position]) == root && {
                    let bound = wiring.signals@[call.member as int]@[position - frame.signals.start];
                    &&& bound.form == root
                    &&& wire == driver_wire(bound.driver)
                }
        } else {
            wire matches Wire::Constant(value) && literal_bit(call.inputs.ports.signature.source.text, form, value)
                && literal_value_fits(call.inputs.ports.signature.source.text, form)
        }
    }

    spec fn primitive_definition_supported(&self, checked: &ModuleCalls, index: int) -> bool {
        let call = checked.calls@[index];
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        let driver = drivers.definitions@[index];
        let origin = drivers.origins@[index];
        let parsed = self.targets.project_model().circuits_model()[origin.file as int];
        let frame = parsed.entry_ranges@[origin.entry as int];
        &&& index < checked.calls@.len()
        &&& origin.file == call.at.file && origin.entry == call.at.entry
        &&& driver.definition == frame.definitions.start + call.at.definition
        &&& driver.result_index == 0 && call.at.reference == 0
        &&& call.inputs.ports.signature.call.form == parsed.definitions@[driver.definition as int].expression.start
        &&& call.inputs.ports.signature.target is Nor
    }

    spec fn primitive_gate_matches(&self, checked: &ModuleCalls, index: int, gate: NorGate) -> bool {
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        &&& self.primitive_definition_supported(checked, index)
        &&& self.primitive_operand_matches(checked, index, 0, gate.left)
        &&& self.primitive_operand_matches(checked, index, 1, gate.right)
        &&& wire_available(gate.left, drivers.signature.inputs@.len(), drivers.definitions@.len())
        &&& wire_available(gate.right, drivers.signature.inputs@.len(), drivers.definitions@.len())
    }

    spec fn primitive_argument_error(&self, checked: &ModuleCalls, index: int, arg: int, site: LocatedName) -> bool {
        let call = checked.calls@[index];
        let source = call.inputs.ports.signature.source;
        let parsed = self.targets.project_model().circuits_model()[call.at.file as int];
        let form = parsed.syntax.forms@[call.inputs.ports.arguments@[arg] as int];
        &&& is_form_location(source, form, site)
        &&& !(form is Atom && form->Atom_kind is Name)
        &&& !(exists|value: bool| literal_bit(source.text, form, value))
    }

    spec fn primitive_gate_error(&self, checked: &ModuleCalls, index: int, error: PrimitiveModuleError) -> bool {
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        let origin = drivers.origins@[index];
        let project = self.targets.project_model();
        match error {
            PrimitiveModuleError::Definition(site) => {
                let parsed = project.circuits_model()[origin.file as int];
                let root = parsed.definitions@[drivers.definitions@[index].definition as int].expression.start;
                &&& !self.primitive_definition_supported(checked, index)
                &&& is_form_location(&project.sources_model()[origin.file as int], parsed.syntax.forms@[root as int], site)
            },
            PrimitiveModuleError::Argument(site) => self.primitive_definition_supported(checked, index) && (
                self.primitive_argument_error(checked, index, 0, site)
                || (exists|wire: Wire| self.primitive_operand_matches(checked, index, 0, wire))
                    && self.primitive_argument_error(checked, index, 1, site)),
            _ => false,
        }
    }

    fn primitive_operand(&self, _owner: ModuleBodyPosition, _limit: u64, checked: &ModuleCalls<'p, 'a>,
        index: usize, arg: usize,
    ) -> (wire: Result<Wire, PrimitiveModuleError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(_owner, _limit, Ok(Some(*checked))),
            index < checked.calls@.len(), arg < checked.calls@[index as int].inputs.ports.arguments@.len(),
            checked.calls@[index as int].inputs.ports.signature.target is Nor,
        ensures
            wire matches Ok(value) ==> self.primitive_operand_matches(checked, index as int, arg as int, value)
                && ({
                    let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
                    wire_available(value, drivers.signature.inputs@.len(), drivers.definitions@.len())
                }),
            wire matches Err(PrimitiveModuleError::Argument(site)) ==>
                self.primitive_argument_error(checked, index as int, arg as int, site),
            wire.is_err() ==> wire matches Err(PrimitiveModuleError::Argument(_)),
    {
        let call = &checked.calls[index];
        let ghost at = call.at;
        let ports = &call.inputs.ports;
        let wiring = &checked.module.expressions.typed.sources.roots.wiring;
        proof {
            self.module_calls_type_evidence(_owner, _limit, checked);
            self.module_output_types_evidence(_owner, _limit, checked.module);
            self.module_selections_evidence(_owner, _limit, checked.module.expressions);
            self.module_calls_item_evidence(_owner, _limit, checked, index as int);
            self.module_call_ports_evidence(at, _limit, *ports);
            self.module_call_site_evidence(at, _limit, ports.signature);
        }
        let project = self.targets.project();
        let source = ports.signature.source;
        let parsed = &project.circuits()[call.at.file];
        let ghost model = parsed.build_model();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, at.entry as int);
        }
        let frame = &parsed.entry_ranges[call.at.entry];
        let definition = frame.definitions.start + call.at.definition;
        let row = &parsed.definitions[definition];
        let forms = parsed.syntax.forms.as_slice();
        let root = ports.arguments[arg];
        proof {
            build_definition_scope_evidence(source.text, &model, at.entry as int, definition as int);
            call_argument_position_bounds(forms@, ports.signature.call, ports.arguments@, arg as int);
        }
        if matches!(forms[root], Form::Atom { kind: AtomKind::Name, .. }) {
            proof { call_argument_position_is_direct(forms@, ports.signature.call, ports.arguments@, arg as int); }
            let reference = row.references.start + call.at.reference;
            let position = indexed_call_signal(source.text, forms, row, parsed.references.as_slice(), reference,
                &ports.signature.call, parsed.signals.as_slice(), root);
            proof { self.module_signal_index_item(_owner, _limit, *wiring, call.member as int, position as int); }
            let bound = &wiring.signals[call.member][position - frame.signals.start];
            Ok(map_driver(bound.driver))
        } else if let Some(bit) = read_literal_bit(source.text, forms, root) {
            proof {
                let form = forms@[root as int];
                if form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal) {
                    self.module_nor_literal_item(at, _limit, &call.inputs, arg as int);
                    let span = form_span(form);
                    let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
                    crate::project::literal_width::circuit_bit_literal_boundary(bytes, Some(1), _limit, Ok(1));
                }
            }
            Ok(Wire::Constant(bit))
        } else {
            Err(PrimitiveModuleError::Argument(form_location(source, forms, root)))
        }
    }

    fn lower_primitive_gate(&self, _owner: ModuleBodyPosition, _limit: u64, checked: &ModuleCalls<'p, 'a>, index: usize)
        -> (gate: Result<NorGate, PrimitiveModuleError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(_owner, _limit, Ok(Some(*checked))),
            index < checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len(),
        ensures match gate {
            Ok(gate) => self.primitive_gate_matches(checked, index as int, gate),
            Err(error) => self.primitive_gate_error(checked, index as int, error),
        },
    {
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(_owner, _limit, checked);
            self.module_output_types_evidence(_owner, _limit, checked.module);
            self.module_selections_evidence(_owner, _limit, checked.module.expressions);
            self.module_driver_sites(_owner, _limit, *drivers, index as int);
        }
        let origin = drivers.origins[index];
        let driver = &drivers.definitions[index];
        let project = self.targets.project();
        let source = &project.sources()[origin.file];
        let parsed = &project.circuits()[origin.file];
        let ghost model = parsed.build_model();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, origin.entry as int);
            build_definition_scope_evidence(source.text, &model, origin.entry as int, driver.definition as int);
        }
        let row = &parsed.definitions[driver.definition];
        let frame = &parsed.entry_ranges[origin.entry];
        let local = driver.definition - frame.definitions.start;
        if index >= checked.calls.len() {
            return Err(PrimitiveModuleError::Definition(form_location(source, parsed.syntax.forms.as_slice(), row.expression.start)));
        }
        let call = &checked.calls[index];
        if call.at.file != origin.file || call.at.entry != origin.entry || call.at.definition != local
            || call.at.reference != 0 || driver.result_index != 0
            || call.inputs.ports.signature.call.form != row.expression.start
            || !matches!(call.inputs.ports.signature.target, ModuleCallTarget::Nor)
        {
            return Err(PrimitiveModuleError::Definition(form_location(source, parsed.syntax.forms.as_slice(), row.expression.start)));
        }
        proof {
            self.module_calls_item_evidence(_owner, _limit, checked, index as int);
            self.module_call_ports_evidence(call.at, _limit, call.inputs.ports);
        }
        let left = self.primitive_operand(_owner, _limit, checked, index, 0)?;
        let right = self.primitive_operand(_owner, _limit, checked, index, 1)?;
        Ok(NorGate { left, right })
    }

    #[verifier::opaque]
    spec fn primitive_gate_prefix(&self, checked: &ModuleCalls, gates: Seq<NorGate>) -> bool {
        &&& gates.len() <= checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < gates.len() ==> self.primitive_gate_matches(checked, i, #[trigger] gates[i])
    }

    spec fn primitive_lowering_error(&self, checked: &ModuleCalls, error: PrimitiveModuleError) -> bool {
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        let inputs = drivers.signature.inputs@;
        let outputs = drivers.signature.outputs@;
        let valid_inputs = one_bit_ports(inputs, inputs.len() as int);
        match error {
            PrimitiveModuleError::Port(site) => first_unsupported_port(inputs, site)
                || valid_inputs && first_unsupported_port(outputs, site),
            PrimitiveModuleError::Definition(_) | PrimitiveModuleError::Argument(_) =>
                valid_inputs && one_bit_ports(outputs, outputs.len() as int)
                    && exists|prefix: Seq<NorGate>| #[trigger] self.primitive_gate_prefix(checked, prefix)
                        && prefix.len() < drivers.definitions@.len()
                        && self.primitive_gate_error(checked, prefix.len() as int, error),
            PrimitiveModuleError::Module(_) => false,
        }
    }

    /// 変換の成功結果と、検査済みソースの定義・ポート順・配線の対応を表す。
    pub closed spec fn primitive_module_result(&self, owner: ModuleBodyPosition, limit: u64,
        result: Result<Option<ClockedNor>, PrimitiveModuleError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_calls_result(owner, limit, Ok(None)),
            Err(PrimitiveModuleError::Module(error)) => self.module_calls_result(owner, limit, Err(error)),
            Err(error) => exists|checked: ModuleCalls|
                #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
                && self.primitive_lowering_error(&checked, error),
            Ok(Some(circuit)) => exists|checked: ModuleCalls|
                #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked))) && {
                    let netlist = circuit.netlist_model();
                    let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
                    &&& one_bit_ports(drivers.signature.inputs@, drivers.signature.inputs@.len() as int)
                    &&& one_bit_ports(drivers.signature.outputs@, drivers.signature.outputs@.len() as int)
                    &&& netlist.input_count == drivers.signature.inputs@.len()
                    &&& netlist.gates@.len() == drivers.definitions@.len()
                    &&& self.primitive_gate_prefix(&checked, netlist.gates@)
                    &&& netlist.outputs@.len() == drivers.outputs@.len()
                    &&& forall|i: int| 0 <= i < netlist.outputs@.len() ==>
                        (#[trigger] netlist.outputs@[i]) == driver_wire(drivers.outputs@[i])
                },
        }
    }

    /// 単一ビットの入出力と基底 NOR からなるモジュールを tick 実行用に変換する。
    ///
    /// 定義ごとにゲートを一つ置き、信号名と1ビットの定数を入力配線に変換する。
    /// 全断片の定義に先に番号を割り当てるため、前方参照と自己参照を扱える。
    /// 指定位置にモジュールがなければ `None` を返す。
    ///
    /// # Errors
    ///
    /// モジュールの検査を先に行い、続いて対応できない型や式の元ソース位置を返す。
    pub fn lower_primitive_module(&self, owner: ModuleBodyPosition, limit: u64)
        -> (result: Result<Option<ClockedNor>, PrimitiveModuleError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.primitive_module_result(owner, limit, result),
    {
        let checked = match self.check_module_calls(owner, limit) {
            Ok(Some(checked)) => checked,
            Ok(None) => return Ok(None),
            Err(error) => return Err(PrimitiveModuleError::Module(error)),
        };
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, limit, &checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, checked.module.expressions);
        }
        let inputs = drivers.signature.inputs.as_slice();
        let output_ports = drivers.signature.outputs.as_slice();
        if let Some(i) = unsupported_port(inputs) {
            let site = copy_location(&inputs[i].annotation);
            assert(first_unsupported_port(inputs@, site));
            assert(self.primitive_lowering_error(&checked, PrimitiveModuleError::Port(site)));
            return Err(PrimitiveModuleError::Port(site));
        }
        if let Some(i) = unsupported_port(output_ports) {
            let site = copy_location(&output_ports[i].annotation);
            assert(first_unsupported_port(output_ports@, site));
            assert(self.primitive_lowering_error(&checked, PrimitiveModuleError::Port(site)));
            return Err(PrimitiveModuleError::Port(site));
        }
        let n = drivers.definitions.len();
        let mut gates = Vec::with_capacity(n);
        let mut i = 0;
        assert(self.primitive_gate_prefix(&checked, gates@)) by { reveal(UseAliases::primitive_gate_prefix); };
        while i < n
            invariant
                self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(checked))),
                *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
                inputs@ == drivers.signature.inputs@, output_ports@ == drivers.signature.outputs@,
                one_bit_ports(inputs@, inputs@.len() as int), one_bit_ports(output_ports@, output_ports@.len() as int),
                n == drivers.definitions@.len(), i == gates@.len() <= n,
                self.primitive_gate_prefix(&checked, gates@),
            decreases n - i,
        {
            let gate = match self.lower_primitive_gate(owner, limit, &checked, i) {
                Ok(gate) => gate,
                Err(error) => {
                    assert(self.primitive_lowering_error(&checked, error));
                    return Err(error);
                },
            };
            let ghost prior = gates@;
            gates.push(gate);
            assert(self.primitive_gate_prefix(&checked, gates@)) by {
                reveal(UseAliases::primitive_gate_prefix);
                assert forall|j: int| 0 <= j < gates@.len() implies
                    self.primitive_gate_matches(&checked, j, #[trigger] gates@[j]) by {
                    if j < i { assert(gates@[j] == prior[j]); }
                };
            };
            i += 1;
        }
        let mut outputs = Vec::with_capacity(drivers.outputs.len());
        let mut o = 0;
        while o < drivers.outputs.len()
            invariant
                self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
                n == drivers.definitions@.len(),
                o == outputs@.len() <= drivers.outputs@.len(),
                output_ports_available(outputs@, drivers.signature.inputs@.len(), n as nat, o as int),
                forall|j: int| 0 <= j < outputs@.len() ==> (#[trigger] outputs@[j]) == driver_wire(drivers.outputs@[j]),
            decreases drivers.outputs@.len() - o,
        {
            proof { self.module_output_driver(owner, limit, *drivers, o as int); }
            let wire = map_driver(drivers.outputs[o]);
            let ghost prior = outputs@;
            outputs.push(wire);
            assert forall|j: int| 0 <= j < outputs@.len() implies
                (#[trigger] outputs@[j]) == driver_wire(drivers.outputs@[j])
                    && wire_available(outputs@[j], drivers.signature.inputs@.len(), n as nat) by {
                if j < o { assert(outputs@[j] == prior[j]); }
            };
            o += 1;
        }
        let netlist = NorNetlist { input_count: inputs.len(), gates, outputs };
        proof {
            reveal(UseAliases::primitive_gate_prefix);
            clocked_wiring_from_endpoints(&netlist);
        }
        let outcome = ClockedNor::check(netlist);
        match outcome {
            Ok(circuit) => Ok(Some(circuit)),
            Err(_) => {
                proof { assert(false); }
                unreachable!()
            },
        }
    }
}

} // verus!
