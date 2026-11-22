//! 検査済みの親モジュールから子回路の配置と実引数の配線を求める。

use super::{ModuleCalls, ModuleCallsError, PrimitiveModuleError, UseAliases, copy_location};
use super::clocked_plan::{ClockedPlanError, ClockedWireDriver, clocked_reserve, clocked_resolve};
use super::primitive_nor::unsupported_port;
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
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence,
    call_argument_position_bounds, call_argument_position_is_direct};

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
    /// 配線の組み立て中に見つかった違反と、そのインスタンスの位置。
    Instance(LocatedName<'p, 'a>, ClockedInstanceError),
    /// 親回路全体の検査で見つかった配線の違反。
    Netlist(ClockedNorError),
}

struct SourceInstance<'p, 'a> {
    template: ClockedNor,
    arguments: Vec<ClockedWireDriver>,
    output_sites: Vec<LocatedName<'p, 'a>>,
    site: LocatedName<'p, 'a>,
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

fn symbolic_driver(driver: OutputDriver) -> (wire: ClockedWireDriver) {
    match driver {
        OutputDriver::Input(port) => ClockedWireDriver::Terminal(Wire::Input(port)),
        OutputDriver::Definition(definition) => ClockedWireDriver::Alias(definition),
    }
}

fn resolve_driver(driver: ClockedWireDriver, wires: &[Wire]) -> (wire: Option<Wire>) {
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
            return Ok(symbolic_driver(wiring.signals[call.member][position - frame.signals.start].driver));
        }
        if matches!(forms[root], Form::Atom { kind: AtomKind::Natural | AtomKind::Binary | AtomKind::Hexadecimal, .. }) {
            let (word, _) = read_indexed_atom(source.text, forms, root);
            if word == "0" { return Ok(ClockedWireDriver::Terminal(Wire::Constant(false))); }
            if word == "1" { return Ok(ClockedWireDriver::Terminal(Wire::Constant(true))); }
            if let Some(literal) = read_bit_literal(word) {
                if crate::project::check_circuit_literal_width(word, Some(1), limit).is_ok() {
                    return Ok(ClockedWireDriver::Terminal(Wire::Constant(literal.bit(0))));
                }
            }
        }
        Err(form_location(source, forms, root))
    }

    fn prepare_module_instances(&self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls<'p, 'a>)
        -> (result: Result<(Vec<SourceInstance<'p, 'a>>, Vec<usize>), ClockedModuleError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
        ensures
            result matches Ok((instances, counts)) ==> instance_counts_match(instances@, counts@),
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
                index <= checked.calls@.len(), index == counts@.len() == instances@.len(),
                instance_counts_match(instances@, counts@),
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
                ModuleCallTarget::Nor => match builtin_instance() {
                    Ok(circuit) => circuit,
                    Err(error) => return Err(ClockedModuleError::Netlist(error)),
                },
                ModuleCallTarget::Routine { position, signature: typed, .. } => {
                    if unsupported_port(typed.inputs.as_slice()).is_some() || unsupported_port(typed.outputs.as_slice()).is_some() {
                        return Err(ClockedModuleError::Unsupported(site));
                    }
                    match self.lower_primitive_module(*position, limit) {
                        Ok(Some(template)) => template,
                        Ok(None) => return Err(ClockedModuleError::Unsupported(site)),
                        Err(reason) => return Err(ClockedModuleError::Child { call: site, reason }),
                    }
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
            let mut arguments = Vec::new();
            let mut arg = 0;
            while arg < call.inputs.ports.arguments.len()
                invariant self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
                    index < checked.calls@.len(), *call == checked.calls@[index as int],
                    arg == arguments@.len() <= call.inputs.ports.arguments@.len(),
                decreases call.inputs.ports.arguments@.len() - arg,
            {
                let value = match self.clocked_source_argument(owner, limit, checked, index, arg) {
                    Ok(value) => value,
                    Err(location) => return Err(ClockedModuleError::Unsupported(location)),
                };
                arguments.push(value);
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
            index += 1;
        }
        if driver < drivers.definitions.len() {
            return Err(ClockedModuleError::Unsupported(self.source_driver_location(owner, limit, drivers, driver)));
        }
        Ok((instances, counts))
    }

    /// 親モジュールと、直接呼び出す基底 NOR モジュールをソースから変換する。
    ///
    /// 入出力は単一ビットで、親の各定義は信号名または定数を直接渡す呼び出しとする。
    /// 指定位置にモジュールがなければ `None` を返す。
    ///
    /// # Errors
    ///
    /// 親と子の型や呼び出しの違反、ゲート数の上限、直結の循環を報告する。
    pub fn lower_clocked_module(&self, owner: ModuleBodyPosition, width_limit: u64, gate_limit: usize)
        -> (result: Result<Option<ClockedNor>, ClockedModuleError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            result == Ok(None) ==> self.module_calls_result(owner, width_limit, Ok(None)),
            result matches Err(ClockedModuleError::Parent(error)) ==>
                self.module_calls_result(owner, width_limit, Err(error)),
            result matches Ok(Some(circuit)) ==> circuit.netlist_model().gates@.len() <= gate_limit
                && crate::netlist::clocked_wiring_valid(&circuit.netlist_model())
                && self.clocked_module_ports_match(owner, width_limit, &circuit.netlist_model()),
    {
        let checked = match self.check_module_calls(owner, width_limit) {
            Ok(Some(checked)) => checked,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ClockedModuleError::Parent(error)),
        };
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, width_limit, &checked);
            self.module_output_types_evidence(owner, width_limit, checked.module);
            self.module_selections_evidence(owner, width_limit, checked.module.expressions);
            self.module_output_driver(owner, width_limit, *drivers, 0);
        }
        let inputs = drivers.signature.inputs.as_slice();
        let outputs = drivers.signature.outputs.as_slice();
        if let Some(i) = unsupported_port(inputs) { return Err(ClockedModuleError::Unsupported(copy_location(&inputs[i].annotation))); }
        if let Some(i) = unsupported_port(outputs) { return Err(ClockedModuleError::Unsupported(copy_location(&outputs[i].annotation))); }
        let (instances, counts) = self.prepare_module_instances(owner, width_limit, &checked)?;
        match assemble_source_instances(&instances, &counts, inputs.len(), &drivers.outputs, gate_limit) {
            Ok(circuit) => Ok(Some(circuit)),
            Err(error) => Err(error),
        }
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

fn assemble_source_instances<'p, 'a>(instances: &[SourceInstance<'p, 'a>], counts: &[usize], inputs: usize,
    output_drivers: &[OutputDriver], limit: usize,
) -> (result: Result<ClockedNor, ClockedModuleError<'p, 'a>>)
    requires instance_counts_match(instances@, counts@),
    ensures
        result matches Ok(circuit) ==> circuit.netlist_model().input_count == inputs
            && circuit.netlist_model().outputs@.len() == output_drivers@.len()
            && circuit.netlist_model().gates@.len() <= limit
            && crate::netlist::clocked_wiring_valid(&circuit.netlist_model()),
        !(result matches Err(ClockedModuleError::Parent(_))),
{
    let (regions, total) = match clocked_reserve(counts, limit) {
        Ok(plan) => plan,
        Err(i) => return Err(ClockedModuleError::Capacity(copy_location(&instances[i].site))),
    };
    let mut drivers = Vec::new();
    let mut sites = Vec::new();
    let mut i = 0;
    while i < instances.len()
        invariant i <= instances@.len(), regions@.len() == instances@.len(), drivers@.len() == sites@.len(),
            instance_counts_match(instances@, counts@),
            super::clocked_plan::clocked_regions_cover(counts@, regions@, total),
        decreases instances@.len() - i,
    {
        let instance = &instances[i];
        let netlist = instance.template.checked_netlist();
        let region = &regions[i];
        let mut j = 0;
        while j < netlist.outputs.len()
            invariant j <= netlist.outputs@.len() == instance.output_sites@.len(), drivers@.len() == sites@.len(),
                region.start <= region.end <= total, crate::netlist::clocked_wiring_valid(netlist),
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
            drivers.push(driver);
            sites.push(copy_location(&instance.output_sites[j]));
            j += 1;
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
        decreases instances@.len() - i,
    {
        let instance = &instances[i];
        let mut arguments = Vec::new();
        let mut j = 0;
        while j < instance.arguments.len()
            invariant j <= instance.arguments@.len(),
            decreases instance.arguments@.len() - j,
        {
            let Some(wire) = resolve_driver(instance.arguments[j], &wires) else {
                return Err(ClockedModuleError::Unsupported(copy_location(&instance.site)));
            };
            arguments.push(wire);
            j += 1;
        }
        if let Err(error) = instance.template.append_instance(&mut gates, &arguments, inputs, total) {
            return Err(ClockedModuleError::Instance(copy_location(&instance.site), error));
        }
        i += 1;
    }
    let mut outputs = Vec::new();
    assert(gates@.len() == total);
    let mut i = 0;
    while i < output_drivers.len()
        invariant i == outputs@.len() <= output_drivers@.len(),
        decreases output_drivers@.len() - i,
    {
        let Some(wire) = resolve_driver(symbolic_driver(output_drivers[i]), &wires) else {
            return Err(ClockedModuleError::Netlist(ClockedNorError::Output { output: i }));
        };
        outputs.push(wire);
        i += 1;
    }
    match ClockedNor::check(NorNetlist { input_count: inputs, gates, outputs }) {
        Ok(circuit) => Ok(circuit),
        Err(error) => Err(ClockedModuleError::Netlist(error)),
    }
}

} // verus!
