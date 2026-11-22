//! 検査済みの親モジュールから子回路の配置と実引数の配線を求める。

mod hierarchy;

use super::{ModuleCalls, ModuleCallsError, PrimitiveModuleError, UseAliases, copy_location};
use super::clocked_plan::{ClockedPlanError, ClockedWireDriver, clocked_reserve, clocked_resolve};
use super::primitive_nor::{read_literal_bit, unsupported_port};
#[cfg(verus_only)]
use super::primitive_nor::{PrimitiveOperand, literal_bit, literal_value_fits};
use crate::project::use_aliases::function_drivers::name_location;
use crate::netlist::{ClockedInstanceError, ClockedNor, ClockedNorError, NorGate, NorNetlist, Wire};
use crate::project::{LocatedName, ModuleBodyPosition, ModuleCallTarget, OutputDriver,
    circuits::{form_location, read_indexed_atom}};
use crate::syntax::{AtomKind, Form, circuit::indexed_call_signal, read_bit_literal};
use alloc::{vec, vec::Vec};
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::netlist::{instance_gates_at, instance_gates_in_extension};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence,
    call_argument_position_bounds, call_argument_position_is_direct};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 親子のモジュールを tick 実行用に組み立てるときの診断。
#[derive(Debug)]
pub enum ClockedModuleError<'p, 'a> {
    /// 親モジュールの型や呼び出しの違反。
    Parent(ModuleCallsError<'p, 'a>),
    /// 子モジュールを展開できなかった。
    Child {
        /// 親モジュールの呼び出し箇所。
        call: LocatedName<'p, 'a>,
        /// 子モジュールのソースに対応する診断。
        reason: PrimitiveModuleError<'p, 'a>,
    },
    /// 現在の変換対象に含まれない型、回路呼び出し、または式。
    Unsupported(LocatedName<'p, 'a>),
    /// ゲート数の上限を超える呼び出し箇所。
    Capacity(LocatedName<'p, 'a>),
    /// 遅延のない配線だけで閉じる循環。順番は配線をたどる向き。
    AliasCycle(Vec<LocatedName<'p, 'a>>),
    /// モジュール宣言間の再帰を構成する呼び出し。末尾の参照先は先頭の呼び出し元に戻る。
    Recursion(Vec<LocatedName<'p, 'a>>),
    /// 配線の組み立て中に見つかった違反と、そのインスタンスの位置。
    Instance(LocatedName<'p, 'a>, ClockedInstanceError),
    /// 親回路全体の検査で見つかった配線の違反。
    Netlist(ClockedNorError),
}

struct SourceInstance<'s, 'p, 'a> {
    template: &'s ClockedNor,
    arguments: Vec<ClockedWireDriver>,
    output_sites: Vec<LocatedName<'p, 'a>>,
    site: LocatedName<'p, 'a>,
}

spec fn edge_templates_ready(edges: Seq<Option<usize>>, templates: Seq<Option<ClockedNor>>) -> bool {
    forall|i: int| 0 <= i < edges.len() ==>
        ((#[trigger] edges[i]) matches Some(child) ==> child < templates.len() && templates[child as int].is_some())
}

spec fn instance_counts_match(instances: Seq<SourceInstance>, counts: Seq<usize>) -> bool {
    &&& instances.len() == counts.len()
    &&& forall|i: int| 0 <= i < instances.len() ==> {
        let model = (#[trigger] instances[i]).template.netlist_model();
        &&& counts[i] == model.gates@.len()
        &&& instances[i].arguments@.len() == model.input_count
        &&& instances[i].output_sites@.len() == model.outputs@.len()
    }
}

spec fn symbolic_output(driver: OutputDriver) -> ClockedWireDriver {
    match driver {
        OutputDriver::Input(port) => ClockedWireDriver::Terminal(Wire::Input(port)),
        OutputDriver::Definition(slot) => ClockedWireDriver::Alias(slot),
    }
}

fn symbolic_driver(driver: OutputDriver) -> (wire: ClockedWireDriver)
    ensures wire == symbolic_output(driver),
{
    match driver {
        OutputDriver::Input(port) => ClockedWireDriver::Terminal(Wire::Input(port)),
        OutputDriver::Definition(definition) => ClockedWireDriver::Alias(definition),
    }
}

spec fn resolved_driver(driver: ClockedWireDriver, wires: Seq<Wire>) -> Option<Wire> {
    match driver {
        ClockedWireDriver::Terminal(wire) => Some(wire),
        ClockedWireDriver::Alias(slot) if slot < wires.len() => Some(wires[slot as int]),
        _ => None,
    }
}

fn resolve_driver(driver: ClockedWireDriver, wires: &[Wire]) -> (wire: Option<Wire>)
    ensures wire == resolved_driver(driver, wires@),
{
    match driver {
        ClockedWireDriver::Terminal(wire) => Some(wire),
        ClockedWireDriver::Alias(target) => {
            if target < wires.len() { Some(wires[target]) } else { None }
        },
    }
}

fn builtin_instance() -> (result: Result<ClockedNor, ClockedNorError>) {
    ClockedNor::check(NorNetlist {
        input_count: 2,
        gates: vec![NorGate { left: Wire::Input(0), right: Wire::Input(1) }],
        outputs: vec![Wire::Gate(0)],
    })
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn source_argument_matches(&self, checked: &ModuleCalls, index: int, arg: int, driver: ClockedWireDriver) -> bool {
        exists|operand: PrimitiveOperand| #[trigger] self.primitive_operand_resolves(checked, index, arg, operand)
            && driver == match operand {
                PrimitiveOperand::Driver(output) => symbolic_output(output),
                PrimitiveOperand::Literal(bit) => ClockedWireDriver::Terminal(Wire::Constant(bit)),
            }
    }

    spec fn source_arguments_match(&self, checked: &ModuleCalls, index: int, arguments: Seq<ClockedWireDriver>) -> bool {
        &&& arguments.len() == checked.calls@[index].inputs.ports.arguments@.len()
        &&& forall|arg: int| 0 <= arg < arguments.len() ==>
            self.source_argument_matches(checked, index, arg, #[trigger] arguments[arg])
    }

    spec fn instance_matches_source_call(&self, checked: &ModuleCalls, index: int, instance: SourceInstance,
        edge: Option<usize>, templates: Seq<Option<ClockedNor>>, builtin: &ClockedNor) -> bool
    {
        &&& self.source_arguments_match(checked, index, instance.arguments@)
        &&& match checked.calls@[index].inputs.ports.signature.target {
            ModuleCallTarget::Nor => *instance.template == *builtin,
            ModuleCallTarget::Routine { .. } => edge matches Some(child) && child < templates.len()
                && templates[child as int] == Some(*instance.template),
            ModuleCallTarget::StateElement { .. } => false,
        }
    }

    spec fn instances_match_source_calls(&self, checked: &ModuleCalls, instances: Seq<SourceInstance>,
        edges: Seq<Option<usize>>, templates: Seq<Option<ClockedNor>>, builtin: &ClockedNor) -> bool
    {
        &&& instances.len() <= checked.calls@.len() == edges.len()
        &&& forall|i: int| 0 <= i < instances.len() ==> #[trigger]
            self.instance_matches_source_call(checked, i, instances[i], edges[i], templates, builtin)
    }

    spec fn clocked_checked_assembly_matches(&self, checked: &ModuleCalls, edges: Seq<Option<usize>>,
        templates: Seq<Option<ClockedNor>>, builtin: &ClockedNor, netlist: NorNetlist) -> bool
    {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        exists|instances: Seq<SourceInstance>, counts: Seq<usize>|
            #![trigger self.instances_match_source_calls(checked, instances, edges, templates, builtin),
                source_assembly_matches(instances, counts, drivers.signature.inputs@.len() as usize, drivers.outputs@, netlist)]
            instances.len() == checked.calls@.len()
            && self.instances_match_source_calls(checked, instances, edges, templates, builtin)
            && source_assembly_matches(instances, counts, drivers.signature.inputs@.len() as usize, drivers.outputs@, netlist)
    }

    fn source_driver_location(&self, _owner: ModuleBodyPosition, _limit: u64, drivers: &crate::project::ModuleDrivers<'p, 'a>, index: usize)
        -> (site: LocatedName<'p, 'a>)
        requires self.can_resolve(), self.module_drivers_result(_owner, _limit, Ok(Some(*drivers))),
            index < drivers.definitions@.len(),
        ensures
            crate::project::location_in_source(site),
            site.span == drivers.definitions@[index as int].name.span,
            *site.source == self.targets.project_model().sources_model()[drivers.origins@[index as int].file as int],
    {
        proof { self.module_driver_sites(_owner, _limit, *drivers, index as int); }
        let position = drivers.origins[index];
        let source = &self.targets.project().sources()[position.file];
        name_location(source, &drivers.definitions[index].name)
    }

    fn clocked_source_argument(&self, _owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls<'p, 'a>,
        index: usize, arg: usize,
    ) -> (driver: Result<ClockedWireDriver, LocatedName<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(_owner, limit, Ok(Some(*checked))),
            index < checked.calls@.len(), arg < checked.calls@[index as int].inputs.ports.arguments@.len(),
        ensures driver matches Ok(wire) ==> self.source_argument_matches(checked, index as int, arg as int, wire),
    {
        let call = &checked.calls[index];
        let ports = &call.inputs.ports;
        let ghost at = call.at;
        let wiring = &checked.module.expressions.typed.sources.roots.wiring;
        proof {
            self.module_calls_type_evidence(_owner, limit, checked);
            self.module_output_types_evidence(_owner, limit, checked.module);
            self.module_selections_evidence(_owner, limit, checked.module.expressions);
            self.module_calls_item_evidence(_owner, limit, checked, index as int);
            self.module_call_ports_evidence(at, limit, *ports);
            self.module_call_site_evidence(at, limit, ports.signature);
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
            proof { self.module_signal_index_item(_owner, limit, *wiring, call.member as int, position as int); }
            let driver = wiring.signals[call.member][position - frame.signals.start].driver;
            assert(self.primitive_name_resolves(checked, index as int, root, position as int, PrimitiveOperand::Driver(driver)));
            assert(self.primitive_operand_resolves(checked, index as int, arg as int, PrimitiveOperand::Driver(driver)));
            return Ok(symbolic_driver(driver));
        }
        if matches!(forms[root], Form::Atom { kind: AtomKind::Natural, .. }) {
            if let Some(bit) = read_literal_bit(source.text, forms, root) {
                assert(self.primitive_operand_resolves(checked, index as int, arg as int, PrimitiveOperand::Literal(bit)));
                return Ok(ClockedWireDriver::Terminal(Wire::Constant(bit)));
            }
        } else if matches!(forms[root], Form::Atom { kind: AtomKind::Binary | AtomKind::Hexadecimal, .. }) {
            let (word, _) = read_indexed_atom(source.text, forms, root);
            if let Some(literal) = read_bit_literal(word) {
                if let Ok(_) = crate::project::check_circuit_literal_width(word, Some(1), limit) {
                    proof { crate::syntax::bit_literal_kind_has_digits(word.spec_bytes()); }
                    let bit = literal.bit(0);
                    assert(literal_bit(source.text, forms@[root as int], bit) && literal_value_fits(source.text, forms@[root as int]));
                    assert(self.primitive_operand_resolves(checked, index as int, arg as int, PrimitiveOperand::Literal(bit)));
                    return Ok(ClockedWireDriver::Terminal(Wire::Constant(bit)));
                }
            }
        }
        Err(form_location(source, forms, root))
    }

    fn prepare_module_instances<'s>(&self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls<'p, 'a>,
        edges: &[Option<usize>], templates: &'s [Option<ClockedNor>], builtin: &'s ClockedNor,
    ) -> (result: Result<(Vec<SourceInstance<'s, 'p, 'a>>, Vec<usize>), ClockedModuleError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            edges@.len() == checked.calls@.len(), edge_templates_ready(edges@, templates@),
        ensures
            result matches Ok((instances, counts)) ==> instance_counts_match(instances@, counts@)
                && instances@.len() == checked.calls@.len()
                && self.instances_match_source_calls(checked, instances@, edges@, templates@, builtin),
            !(result matches Err(ClockedModuleError::Parent(_))),
    {
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, limit, checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, checked.module.expressions);
        }
        let project = self.targets.project();
        let mut counts = Vec::new();
        let mut instances = Vec::new();
        let mut index = 0;
        let mut driver = 0;
        while index < checked.calls.len()
            invariant
                self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
                self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
                *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
                *project == self.targets.project_model(),
                edges@.len() == checked.calls@.len(), edge_templates_ready(edges@, templates@),
                index <= checked.calls@.len(), index == counts@.len() == instances@.len(),
                instance_counts_match(instances@, counts@),
                self.instances_match_source_calls(checked, instances@, edges@, templates@, builtin),
                driver <= drivers.definitions@.len(),
            decreases checked.calls@.len() - index,
        {
            let call = &checked.calls[index];
            let signature = &call.inputs.ports.signature;
            let site = LocatedName { source: signature.source, span: signature.call.span.start..signature.call.span.end };
            proof {
                self.module_calls_item_evidence(owner, limit, checked, index as int);
                self.module_call_ports_evidence(call.at, limit, call.inputs.ports);
                self.module_call_site_evidence(call.at, limit, *signature);
            }
            let parsed = &project.circuits()[call.at.file];
            let frame = &parsed.entry_ranges[call.at.entry];
            let indexed_definition = frame.definitions.start + call.at.definition;
            if driver < drivers.definitions.len() {
                proof { self.module_driver_sites(owner, limit, *drivers, driver as int); }
                let origin = drivers.origins[driver];
                if origin.file != call.at.file || origin.entry != call.at.entry
                    || drivers.definitions[driver].definition != indexed_definition
                {
                    return Err(ClockedModuleError::Unsupported(self.source_driver_location(owner, limit, drivers, driver)));
                }
            }
            if call.at.reference != 0 || parsed.definitions[indexed_definition].expression.start != signature.call.form {
                return Err(ClockedModuleError::Unsupported(site));
            }
            let template = match &signature.target {
                ModuleCallTarget::Nor => builtin,
                ModuleCallTarget::Routine { signature: typed, .. } => {
                    if unsupported_port(typed.inputs.as_slice()).is_some() || unsupported_port(typed.outputs.as_slice()).is_some() {
                        return Err(ClockedModuleError::Unsupported(site));
                    }
                    let Some(child) = edges[index] else { return Err(ClockedModuleError::Unsupported(site)); };
                    templates[child].as_ref().unwrap()
                },
                ModuleCallTarget::StateElement { .. } => return Err(ClockedModuleError::Unsupported(site)),
            };
            let netlist = template.checked_netlist();
            if call.inputs.ports.arguments.len() != netlist.input_count {
                return Err(ClockedModuleError::Unsupported(site));
            }
            let mut output_sites = Vec::new();
            let mut output = 0;
            while output < netlist.outputs.len()
                invariant
                    self.can_resolve(), self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
                    driver <= drivers.definitions@.len(),
                    output == output_sites@.len() <= netlist.outputs@.len(),
                decreases netlist.outputs@.len() - output,
            {
                if driver >= drivers.definitions.len() { return Err(ClockedModuleError::Unsupported(site)); }
                proof { self.module_driver_sites(owner, limit, *drivers, driver as int); }
                let row = &drivers.definitions[driver];
                let origin = drivers.origins[driver];
                if origin.file != call.at.file || origin.entry != call.at.entry || row.definition != indexed_definition
                    || row.result_index != output
                {
                    return Err(ClockedModuleError::Unsupported(self.source_driver_location(owner, limit, drivers, driver)));
                }
                output_sites.push(self.source_driver_location(owner, limit, drivers, driver));
                driver += 1;
                output += 1;
            }
            let mut arguments: Vec<ClockedWireDriver> = Vec::new();
            let mut arg = 0;
            while arg < call.inputs.ports.arguments.len()
                invariant self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
                    index < checked.calls@.len(), *call == checked.calls@[index as int],
                    arg == arguments@.len() <= call.inputs.ports.arguments@.len(),
                    forall|k: int| 0 <= k < arg ==>
                        self.source_argument_matches(checked, index as int, k, #[trigger] arguments@[k]),
                decreases call.inputs.ports.arguments@.len() - arg,
            {
                let value = match self.clocked_source_argument(owner, limit, checked, index, arg) {
                    Ok(value) => value,
                    Err(location) => return Err(ClockedModuleError::Unsupported(location)),
                };
                let ghost before = arguments@;
                arguments.push(value);
                assert forall|k: int| 0 <= k < arguments@.len() implies
                    self.source_argument_matches(checked, index as int, k, #[trigger] arguments@[k]) by {
                    if k < arg { assert(arguments@[k] == before[k]); }
                };
                arg += 1;
            }
            let ghost before_instances = instances@;
            let ghost before_counts = counts@;
            counts.push(netlist.gates.len());
            instances.push(SourceInstance { template, arguments, output_sites, site });
            assert forall|j: int| 0 <= j < instances@.len() implies {
                let model = (#[trigger] instances@[j]).template.netlist_model();
                &&& counts@[j] == model.gates@.len()
                &&& instances@[j].arguments@.len() == model.input_count
                &&& instances@[j].output_sites@.len() == model.outputs@.len()
            } by {
                if j < index { assert(instances@[j] == before_instances[j] && counts@[j] == before_counts[j]); }
            };
            assert(self.instance_matches_source_call(checked, index as int, instances@[index as int],
                edges@[index as int], templates@, builtin));
            assert forall|j: int| 0 <= j < instances@.len() implies #[trigger]
                self.instance_matches_source_call(checked, j, instances@[j], edges@[j], templates@, builtin) by {
                if j < index {
                    assert(instances@[j] == before_instances[j]);
                    assert(self.instance_matches_source_call(checked, j, before_instances[j], edges@[j], templates@, builtin));
                }
            };
            index += 1;
        }
        if driver < drivers.definitions.len() {
            return Err(ClockedModuleError::Unsupported(self.source_driver_location(owner, limit, drivers, driver)));
        }
        Ok((instances, counts))
    }

    fn lower_checked_module(&self, owner: ModuleBodyPosition, width_limit: u64, gate_limit: usize, checked: &ModuleCalls<'p, 'a>,
        edges: &[Option<usize>], templates: &[Option<ClockedNor>], builtin: &ClockedNor,
    ) -> (result: Result<ClockedNor, ClockedModuleError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, width_limit, Ok(Some(*checked))),
            edges@.len() == checked.calls@.len(), edge_templates_ready(edges@, templates@),
        ensures
            !(result matches Err(ClockedModuleError::Parent(_))),
            result matches Ok(circuit) ==> circuit.netlist_model().gates@.len() <= gate_limit
                && crate::netlist::clocked_wiring_valid(&circuit.netlist_model())
                && self.clocked_module_ports_match(owner, width_limit, &circuit.netlist_model())
                && self.clocked_checked_assembly_matches(checked, edges@, templates@, builtin, circuit.netlist_model()),
    {
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, width_limit, checked);
            self.module_output_types_evidence(owner, width_limit, checked.module);
            self.module_selections_evidence(owner, width_limit, checked.module.expressions);
            self.module_output_driver(owner, width_limit, *drivers, 0);
        }
        let inputs = drivers.signature.inputs.as_slice();
        let outputs = drivers.signature.outputs.as_slice();
        if let Some(i) = unsupported_port(inputs) { return Err(ClockedModuleError::Unsupported(copy_location(&inputs[i].annotation))); }
        if let Some(i) = unsupported_port(outputs) { return Err(ClockedModuleError::Unsupported(copy_location(&outputs[i].annotation))); }
        let (instances, counts) = self.prepare_module_instances(owner, width_limit, checked, edges, templates, builtin)?;
        let circuit = assemble_source_instances(&instances, &counts, inputs.len(), &drivers.outputs, gate_limit)?;
        assert(instances@.len() == checked.calls@.len());
        assert(self.clocked_checked_assembly_matches(checked, edges@, templates@, builtin, circuit.netlist_model())) by {
            let input_count = checked.module.expressions.typed.sources.roots.wiring.drivers.signature.inputs@.len() as usize;
            assert(input_count == inputs.len());
            assert(self.instances_match_source_calls(checked, instances@, edges@, templates@, builtin));
            assert(source_assembly_matches(instances@, counts@, input_count, drivers.outputs@, circuit.netlist_model()));
        };
        Ok(circuit)
    }

    /// 変換後の入出力ビット数が、検査済みの親モジュールのポート宣言と対応する。
    pub closed spec fn clocked_module_ports_match(&self, owner: ModuleBodyPosition, limit: u64, netlist: &NorNetlist) -> bool {
        exists|checked: ModuleCalls| #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked))) && {
            let signature = checked.module.expressions.typed.sources.roots.wiring.drivers.signature;
            &&& netlist.input_count == signature.inputs@.len()
            &&& netlist.outputs@.len() == signature.outputs@.len()
            &&& super::primitive_nor::one_bit_ports(signature.inputs@, signature.inputs@.len() as int)
            &&& super::primitive_nor::one_bit_ports(signature.outputs@, signature.outputs@.len() as int)
        }
    }
}

spec fn resolved_arguments(instance: SourceInstance, wires: Seq<Wire>) -> Seq<Wire> {
    Seq::new(instance.arguments@.len(), |i: int| resolved_driver(instance.arguments@[i], wires)->Some_0)
}

spec fn arguments_valid(instance: SourceInstance, wires: Seq<Wire>) -> bool {
    forall|i: int| 0 <= i < instance.arguments@.len() ==>
        resolved_driver(#[trigger] instance.arguments@[i], wires).is_some()
}

// 各インスタンスの実引数と、割り当てたゲート区間の配線が対応する。
spec fn instance_assembled(instance: SourceInstance, base: usize, wires: Seq<Wire>, gates: Seq<NorGate>) -> bool {
    arguments_valid(instance, wires)
        && instance_gates_at(instance.template.netlist_model().gates@, resolved_arguments(instance, wires), base, gates)
}

spec fn assembled_gate_prefix(instances: Seq<SourceInstance>, regions: Seq<core::ops::Range<usize>>,
    wires: Seq<Wire>, gates: Seq<NorGate>, end: int) -> bool
{
    &&& 0 <= end <= instances.len() == regions.len()
    &&& forall|i: int| 0 <= i < end ==> #[trigger] instance_assembled(instances[i], regions[i].start, wires, gates)
}

proof fn extend_assembled_gate_prefix(instances: Seq<SourceInstance>, regions: Seq<core::ops::Range<usize>>,
    wires: Seq<Wire>, before: Seq<NorGate>, after: Seq<NorGate>, added: int)
    requires
        0 <= added < instances.len(),
        assembled_gate_prefix(instances, regions, wires, before, added),
        before.len() <= after.len(), after.take(before.len() as int) == before,
        instance_assembled(instances[added], regions[added].start, wires, after),
    ensures assembled_gate_prefix(instances, regions, wires, after, added + 1),
{
    assert forall|i: int| 0 <= i < added + 1 implies
        #[trigger] instance_assembled(instances[i], regions[i].start, wires, after) by {
        if i < added {
            let instance = instances[i];
            assert(instance_assembled(instance, regions[i].start, wires, before));
            instance_gates_in_extension(instance.template.netlist_model().gates@, resolved_arguments(instance, wires),
                regions[i].start, before, after);
        }
    };
}

spec fn child_output_driver(output: Wire, arguments: Seq<ClockedWireDriver>, gate_base: usize) -> ClockedWireDriver {
    match output {
        Wire::Input(i) => arguments[i as int],
        Wire::Constant(bit) => ClockedWireDriver::Terminal(Wire::Constant(bit)),
        Wire::Gate(i) => ClockedWireDriver::Terminal(Wire::Gate((gate_base + i) as usize)),
    }
}

spec fn child_output_count(instance: SourceInstance) -> nat {
    instance.template.netlist_model().outputs@.len()
}

// 出力番号は、呼び出し順に各インスタンスの出力ポートを並べて決める。
spec fn child_drivers_match(instances: Seq<SourceInstance>, regions: Seq<core::ops::Range<usize>>,
    offsets: Seq<nat>, drivers: Seq<ClockedWireDriver>) -> bool
{
    &&& offsets.len() <= instances.len() == regions.len()
    &&& drivers.len() == if offsets.len() == 0 { 0 }
        else { offsets.last() + child_output_count(instances[offsets.len() - 1]) }
    &&& forall|i: int| 0 <= i < offsets.len() ==> {
        let base = #[trigger] offsets[i];
        let child = instances[i];
        let outputs = child.template.netlist_model().outputs@;
        &&& base == if i == 0 { 0 } else { offsets[i - 1] + child_output_count(instances[i - 1]) }
        &&& base + outputs.len() <= drivers.len()
        &&& forall|j: int| 0 <= j < outputs.len() ==> (#[trigger] drivers[base + j])
            == child_output_driver(outputs[j], child.arguments@, regions[i].start)
    }
}

spec fn assembled_outputs(drivers: Seq<OutputDriver>, wires: Seq<Wire>, outputs: Seq<Wire>) -> bool {
    forall|i: int| 0 <= i < outputs.len() ==> Some(#[trigger] outputs[i]) == resolved_driver(symbolic_output(drivers[i]), wires)
}

spec fn source_assembly_matches(instances: Seq<SourceInstance>, counts: Seq<usize>, inputs: usize,
    output_drivers: Seq<OutputDriver>, netlist: NorNetlist) -> bool
{
    &&& instance_counts_match(instances, counts)
    &&& netlist.input_count == inputs && netlist.outputs@.len() == output_drivers.len()
    &&& netlist.gates@.len() <= usize::MAX
    &&& exists|regions: Seq<core::ops::Range<usize>>, offsets: Seq<nat>, drivers: Seq<ClockedWireDriver>, wires: Seq<Wire>|
        #![trigger child_drivers_match(instances, regions, offsets, drivers), super::clocked_plan::clocked_wires_match(drivers, wires)]
        super::clocked_plan::clocked_regions_cover(counts, regions, netlist.gates@.len() as usize)
        && offsets.len() == instances.len()
        && child_drivers_match(instances, regions, offsets, drivers)
        && super::clocked_plan::clocked_wires_match(drivers, wires)
        && assembled_gate_prefix(instances, regions, wires, netlist.gates@, instances.len() as int)
        && assembled_outputs(output_drivers, wires, netlist.outputs@)
}

fn resolve_instance_arguments<'p, 'a>(instance: &SourceInstance<'_, 'p, 'a>, wires: &[Wire])
    -> (result: Result<Vec<Wire>, ClockedModuleError<'p, 'a>>)
    ensures
        result matches Ok(arguments) ==> arguments@ == resolved_arguments(*instance, wires@) && arguments_valid(*instance, wires@),
        !(result matches Err(ClockedModuleError::Parent(_))),
{
    let mut arguments: Vec<Wire> = Vec::new();
    let mut j = 0;
    while j < instance.arguments.len()
        invariant j == arguments@.len() <= instance.arguments@.len(),
            forall|k: int| 0 <= k < j ==>
                Some(#[trigger] arguments@[k]) == resolved_driver(instance.arguments@[k], wires@),
        decreases instance.arguments@.len() - j,
    {
        let Some(wire) = resolve_driver(instance.arguments[j], wires) else {
            return Err(ClockedModuleError::Unsupported(copy_location(&instance.site)));
        };
        let ghost before = arguments@;
        arguments.push(wire);
        assert forall|k: int| 0 <= k < arguments@.len() implies
            Some(#[trigger] arguments@[k]) == resolved_driver(instance.arguments@[k], wires@) by {
            if k < j { assert(arguments@[k] == before[k]); }
        };
        j += 1;
    }
    assert forall|k: int| 0 <= k < instance.arguments@.len() implies
        resolved_driver(#[trigger] instance.arguments@[k], wires@).is_some() by {
        assert(Some(arguments@[k]) == resolved_driver(instance.arguments@[k], wires@));
    };
    assert(arguments@ =~= resolved_arguments(*instance, wires@));
    Ok(arguments)
}

fn assemble_source_instances<'p, 'a>(instances: &[SourceInstance<'_, 'p, 'a>], counts: &[usize], inputs: usize,
    output_drivers: &[OutputDriver], limit: usize,
) -> (result: Result<ClockedNor, ClockedModuleError<'p, 'a>>)
    requires instance_counts_match(instances@, counts@),
    ensures
        result matches Ok(circuit) ==> circuit.netlist_model().input_count == inputs
            && circuit.netlist_model().outputs@.len() == output_drivers@.len()
            && circuit.netlist_model().gates@.len() <= limit
            && crate::netlist::clocked_wiring_valid(&circuit.netlist_model())
            && source_assembly_matches(instances@, counts@, inputs, output_drivers@, circuit.netlist_model()),
        !(result matches Err(ClockedModuleError::Parent(_))),
{
    let (regions, total) = match clocked_reserve(counts, limit) {
        Ok(plan) => plan,
        Err(i) => return Err(ClockedModuleError::Capacity(copy_location(&instances[i].site))),
    };
    let mut drivers: Vec<ClockedWireDriver> = Vec::new();
    let mut sites = Vec::new();
    let ghost mut offsets = Seq::<nat>::empty();
    let mut i = 0;
    while i < instances.len()
        invariant i <= instances@.len(), regions@.len() == instances@.len(), drivers@.len() == sites@.len(),
            instance_counts_match(instances@, counts@),
            super::clocked_plan::clocked_regions_cover(counts@, regions@, total),
            offsets.len() == i, child_drivers_match(instances@, regions@, offsets, drivers@),
        decreases instances@.len() - i,
    {
        let instance = &instances[i];
        let netlist = instance.template.checked_netlist();
        let region = &regions[i];
        let ghost prefix = drivers@;
        let ghost base = prefix.len();
        let ghost outputs = netlist.outputs@;
        let mut j = 0;
        while j < netlist.outputs.len()
            invariant j <= netlist.outputs@.len() == instance.output_sites@.len(), drivers@.len() == sites@.len(),
                region.start <= region.end <= total, crate::netlist::clocked_wiring_valid(netlist),
                netlist.outputs@ == outputs, drivers@.len() == base + j, drivers@.take(base as int) == prefix,
                forall|k: int| 0 <= k < j ==> (#[trigger] drivers@[base + k])
                    == child_output_driver(outputs[k], instance.arguments@, region.start),
            decreases netlist.outputs@.len() - j,
        {
            let driver = match netlist.outputs[j] {
                Wire::Input(arg) => {
                    if arg >= instance.arguments.len() {
                        return Err(ClockedModuleError::Unsupported(copy_location(&instance.site)));
                    }
                    instance.arguments[arg]
                },
                Wire::Constant(bit) => ClockedWireDriver::Terminal(Wire::Constant(bit)),
                Wire::Gate(gate) => {
                    if gate >= region.end - region.start {
                        return Err(ClockedModuleError::Unsupported(copy_location(&instance.site)));
                    }
                    ClockedWireDriver::Terminal(Wire::Gate(region.start + gate))
                },
            };
            let ghost before = drivers@;
            drivers.push(driver);
            assert(drivers@.take(base as int) =~= prefix);
            assert forall|k: int| 0 <= k <= j implies (#[trigger] drivers@[base + k])
                == child_output_driver(outputs[k], instance.arguments@, region.start) by {
                if k < j { assert(drivers@[base + k] == before[base + k]); }
            };
            sites.push(copy_location(&instance.output_sites[j]));
            j += 1;
        }
        proof {
            let prior_offsets = offsets;
            offsets = offsets.push(base);
            assert forall|k: int| 0 <= k < offsets.len() implies {
                let start = #[trigger] offsets[k];
                let child = instances@[k];
                let child_outputs = child.template.netlist_model().outputs@;
                &&& start == if k == 0 { 0 } else { offsets[k - 1] + child_output_count(instances@[k - 1]) }
                &&& start + child_outputs.len() <= drivers@.len()
                &&& forall|l: int| 0 <= l < child_outputs.len() ==> (#[trigger] drivers@[start + l])
                    == child_output_driver(child_outputs[l], child.arguments@, regions@[k].start)
            } by {
                if k > 0 { assert(offsets[k - 1] == prior_offsets[k - 1]); }
                if k < i {
                    let start = offsets[k];
                    let child = instances@[k];
                    let child_outputs = child.template.netlist_model().outputs@;
                    assert(start == prior_offsets[k]);
                    assert forall|l: int| 0 <= l < child_outputs.len() implies (#[trigger] drivers@[start + l])
                        == child_output_driver(child_outputs[l], child.arguments@, regions@[k].start) by {
                        assert(drivers@[start + l] == prefix[start + l]);
                    };
                }
            };
        }
        i += 1;
    }
    let wires = match clocked_resolve(drivers.as_slice(), inputs, total) {
        Ok(wires) => wires,
        Err(ClockedPlanError::AliasCycle(cycle)) => {
            let mut path = Vec::new();
            let mut i = 0;
            while i < cycle.len()
                invariant i <= cycle@.len(), sites@.len() == drivers@.len(),
                    forall|j: int| 0 <= j < cycle@.len() ==> #[trigger] cycle@[j] < drivers@.len(),
                decreases cycle@.len() - i,
            {
                let slot = cycle[i];
                path.push(copy_location(&sites[slot]));
                i += 1;
            }
            return Err(ClockedModuleError::AliasCycle(path));
        },
        Err(ClockedPlanError::Wire(index)) => {
            return Err(ClockedModuleError::Unsupported(copy_location(&sites[index])));
        },
        Err(ClockedPlanError::GateCapacity(_)) => {
            proof { assert(false); }
            unreachable!()
        },
    };
    let mut gates = Vec::new();
    let mut i = 0;
    while i < instances.len()
        invariant i <= instances@.len(), gates@.len() <= total,
            instance_counts_match(instances@, counts@),
            super::clocked_plan::clocked_regions_cover(counts@, regions@, total),
            gates@.len() == if i == 0 { 0usize } else { regions@[i - 1].end },
            assembled_gate_prefix(instances@, regions@, wires@, gates@, i as int),
        decreases instances@.len() - i,
    {
        let instance = &instances[i];
        let arguments = resolve_instance_arguments(instance, &wires)?;
        let ghost before = gates@;
        assert(before.len() == regions@[i as int].start);
        if let Err(error) = instance.template.append_instance(&mut gates, &arguments, inputs, total) {
            return Err(ClockedModuleError::Instance(copy_location(&instance.site), error));
        }
        proof { extend_assembled_gate_prefix(instances@, regions@, wires@, before, gates@, i as int); }
        i += 1;
    }
    let mut outputs: Vec<Wire> = Vec::new();
    assert(gates@.len() == total);
    let mut i = 0;
    while i < output_drivers.len()
        invariant i == outputs@.len() <= output_drivers@.len(), assembled_outputs(output_drivers@, wires@, outputs@),
        decreases output_drivers@.len() - i,
    {
        let Some(wire) = resolve_driver(symbolic_driver(output_drivers[i]), &wires) else {
            return Err(ClockedModuleError::Netlist(ClockedNorError::Output { output: i }));
        };
        let ghost before = outputs@;
        outputs.push(wire);
        assert forall|k: int| 0 <= k < outputs@.len() implies
            Some(#[trigger] outputs@[k]) == resolved_driver(symbolic_output(output_drivers@[k]), wires@) by {
            if k < i { assert(outputs@[k] == before[k]); }
        };
        i += 1;
    }
    let netlist = NorNetlist { input_count: inputs, gates, outputs };
    proof {
        assert(source_assembly_matches(instances@, counts@, inputs, output_drivers@, netlist)) by {
            assert(super::clocked_plan::clocked_regions_cover(counts@, regions@, netlist.gates@.len() as usize));
            assert(child_drivers_match(instances@, regions@, offsets, drivers@));
            assert(super::clocked_plan::clocked_wires_match(drivers@, wires@));
        };
    }
    match ClockedNor::check(netlist) {
        Ok(circuit) => Ok(circuit),
        Err(error) => Err(ClockedModuleError::Netlist(error)),
    }
}

} // verus!
