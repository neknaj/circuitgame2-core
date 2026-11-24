//! 呼び出しと公開出力が読む配線を解決し、tick 実行用の VM を初期化する。

use super::{ClockedEndpointError, ClockedModuleEndpoints, ModuleBodyPosition, ModuleCalls, UseAliases};
use crate::netlist::{ClockedNor, ClockedNorError, ClockedStorageInputs, ClockedVm, ClockedVmError,
    NorGate, NorNetlist, PortBitLayout, Wire};
use crate::project::{ClockedArgumentWiringError, ClockedWireDriver, LocatedName};
use crate::project::use_aliases::module_types::clocked_source::resolve_driver;
#[cfg(verus_only)]
use crate::project::use_aliases::module_types::clocked_source::resolved_driver;
#[cfg(verus_only)]
use crate::netlist::clocked_vm_result;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 型の幅、配線の配置、ゲート数、状態メモリに適用する上限。
#[derive(Clone, Copy, Debug)]
pub struct ClockedModuleVmLimits {
    /// ソースの型検査に渡すビット幅の上限。
    pub width: u64,
    /// 入力、出力、定義、増補入力それぞれの平坦ビット数の上限。
    pub wiring_bits: usize,
    /// 基底 NOR の数の上限。
    pub gates: usize,
    /// ラッチと RAM の状態を保持するビット数の総上限。
    pub state_bits: usize,
}

/// 入出力のビット配置と、初期化済みの順序回路 VM。
pub struct ClockedModuleVm {
    /// tick ごとに渡す入力のポート範囲。
    pub inputs: PortBitLayout,
    /// 観測値に含まれる出力のポート範囲。
    pub outputs: PortBitLayout,
    /// 回路の状態と tick 実行機能。
    pub vm: ClockedVm,
}

/// モジュールを tick 実行用の VM に変換できなかった理由。
#[derive(Debug)]
pub enum ClockedModuleVmError<'p, 'a> {
    /// ソースの型または呼び出しから、出力配線を配置できなかった。
    Endpoints(ClockedEndpointError<'p, 'a>),
    /// 呼び出しの実引数を配線へ変換できなかった。
    Arguments(ClockedArgumentWiringError<'p, 'a>),
    /// 配線の組み立てに必要な配列を確保できなかった。
    Allocation,
    /// 呼び出しの配線が、配置した入力や状態素子に合わない。
    CallWiring(LocatedName<'p, 'a>),
    /// 公開出力の駆動元を解決できなかった。
    OutputWiring {
        /// 出力ポートの添字。
        port: usize,
        /// ポート内のビット添字。
        bit: usize,
        /// 出力型の注釈。
        site: Option<LocatedName<'p, 'a>>,
    },
    /// 用意したゲートと状態素子の数が、配置と一致しない。
    InstanceCount,
    /// 組み立てたネットリストの配線に違反があった。
    Netlist(ClockedNorError),
    /// 型付きの VM 初期化診断と、該当する状態素子がある場合の呼び出し位置。
    Vm(ClockedVmError, Option<LocatedName<'p, 'a>>),
}

spec fn row_model(rows: Seq<Vec<ClockedWireDriver>>) -> Seq<ClockedWireDriver> {
    rows.map_values(|row: Vec<ClockedWireDriver>| row@).flatten()
}

spec fn resolved_bits(symbolic: Seq<ClockedWireDriver>, definitions: Seq<Wire>, wires: Seq<Wire>) -> bool {
    &&& symbolic.len() == wires.len()
    &&& forall|bit: int| 0 <= bit < wires.len() ==>
        resolved_driver(symbolic[bit], definitions) == Some(#[trigger] wires[bit])
}

enum ResolveRowError {
    Allocation,
    Driver(usize),
}

enum ResolveRowsError {
    Allocation,
    Driver { port: usize, bit: usize },
}

fn append_row(
    wires: &mut Vec<Wire>, row: &[ClockedWireDriver], definitions: &[Wire],
) -> (result: Result<(), ResolveRowError>)
    ensures
        result.is_ok() ==> final(wires)@.len() == old(wires)@.len() + row@.len()
            && final(wires)@.take(old(wires)@.len() as int) == old(wires)@
            && resolved_bits(row@, definitions@, final(wires)@.skip(old(wires)@.len() as int)),
        result matches Err(ResolveRowError::Driver(bit)) ==>
            bit < row@.len() && resolved_driver(row@[bit as int], definitions@).is_none(),
{
    if wires.try_reserve(row.len()).is_err() { return Err(ResolveRowError::Allocation); }
    let _base = wires.len();
    let mut bit = 0;
    while bit < row.len()
        invariant
            _base == old(wires)@.len(),
            bit <= row@.len(), wires@.len() == _base + bit,
            wires@.take(_base as int) == old(wires)@,
            forall|i: int| 0 <= i < bit ==>
                resolved_driver(row@[i], definitions@) == Some(#[trigger] wires@[_base + i]),
        decreases row@.len() - bit,
    {
        let Some(wire) = resolve_driver(row[bit], definitions) else { return Err(ResolveRowError::Driver(bit)); };
        let ghost before = wires@;
        wires.push(wire);
        assert forall|i: int| 0 <= i <= bit implies
            resolved_driver(row@[i], definitions@) == Some(#[trigger] wires@[_base + i]) by {
            if i < bit { assert(wires@[_base + i] == before[_base + i]); }
        };
        bit += 1;
    }
    assert forall|i: int| 0 <= i < row@.len() implies
        resolved_driver(row@[i], definitions@) == Some(#[trigger] wires@.skip(_base as int)[i]) by {
        assert(wires@.skip(_base as int)[i] == wires@[_base + i]);
    };
    Ok(())
}

fn resolve_rows(rows: &[Vec<ClockedWireDriver>], definitions: &[Wire]) -> (result: Result<Vec<Wire>, ResolveRowsError>)
    ensures
        result matches Ok(wires) ==> resolved_bits(row_model(rows@), definitions@, wires@),
        result matches Err(ResolveRowsError::Driver { port, bit }) ==>
            port < rows@.len() && bit < rows@[port as int]@.len()
            && resolved_driver(rows@[port as int]@[bit as int], definitions@).is_none(),
{
    let mut wires = Vec::new();
    let mut row = 0;
    while row < rows.len()
        invariant row <= rows@.len(), resolved_bits(row_model(rows@.take(row as int)), definitions@, wires@),
        decreases rows@.len() - row,
    {
        let ghost prior = wires@;
        let appended = append_row(&mut wires, rows[row].as_slice(), definitions);
        match appended {
            Ok(()) => {},
            Err(ResolveRowError::Allocation) => return Err(ResolveRowsError::Allocation),
            Err(ResolveRowError::Driver(bit)) => return Err(ResolveRowsError::Driver { port: row, bit }),
        }
        proof {
            assert(wires@.take(prior.len() as int) == prior);
            let previous = rows@.take(row as int).map_values(|item: Vec<ClockedWireDriver>| item@);
            let next = rows@.take(row + 1).map_values(|item: Vec<ClockedWireDriver>| item@);
            assert(next =~= previous.push(rows@[row as int]@));
            previous.lemma_flatten_push(rows@[row as int]@);
            assert(row_model(rows@.take(row + 1)) == previous.flatten() + rows@[row as int]@);
            assert(wires@.len() == prior.len() + rows@[row as int]@.len());
            assert forall|i: int| 0 <= i < wires@.len() implies
                resolved_driver(row_model(rows@.take(row + 1))[i], definitions@) == Some(#[trigger] wires@[i]) by {
                if i < prior.len() {
                    assert(wires@[i] == prior[i]);
                } else {
                    assert(wires@[i] == wires@.skip(prior.len() as int)[i - prior.len()]);
                }
            };
        }
        row += 1;
    }
    assert(rows@.take(row as int) =~= rows@);
    Ok(wires)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    spec fn vm_calls_bound(
        &self, limits: ClockedModuleVmLimits, checked: &ModuleCalls, plan: &ClockedModuleEndpoints,
        arguments: Seq<Vec<Vec<ClockedWireDriver>>>, pins: Seq<Vec<Wire>>,
        gates: Seq<NorGate>, storage: Seq<ClockedStorageInputs>,
    ) -> bool {
        &&& pins.len() == arguments.len() <= checked.calls@.len() <= usize::MAX
        &&& forall|i: int| 0 <= i < pins.len() ==> {
            let wires = #[trigger] pins[i];
            &&& self.call_wires_result(checked, limits.width, &plan.ports, i as usize, Ok(arguments[i]))
            &&& resolved_bits(row_model(arguments[i]@), plan.definitions@, wires@)
            &&& if let Some(gate) = plan.gate_by_call@[i] {
                gate < gates.len() && wires@.len() == 2
                    && gates[gate as int].left == wires@[0] && gates[gate as int].right == wires@[1]
            } else {
                plan.storage.by_call@[i] matches Some(slot) && slot < storage.len()
                    && slot < plan.storage.instances@.len()
                    && plan.storage.instances@[slot as int].storage_inputs_match(wires@, Some(storage[slot as int]))
            }
        }
    }

    proof fn extend_bound_calls(
        &self, limits: ClockedModuleVmLimits, checked: &ModuleCalls, plan: &ClockedModuleEndpoints,
        before: (Seq<Vec<Vec<ClockedWireDriver>>>, Seq<Vec<Wire>>, Seq<NorGate>, Seq<ClockedStorageInputs>),
        after: (Seq<NorGate>, Seq<ClockedStorageInputs>),
        added: (Vec<Vec<ClockedWireDriver>>, Vec<Wire>), index: usize,
    )
        requires
            self.vm_calls_bound(limits, checked, plan, before.0, before.1, before.2, before.3),
            index == before.1.len() < checked.calls@.len() <= usize::MAX,
            self.call_wires_result(checked, limits.width, &plan.ports, index, Ok(added.0)),
            resolved_bits(row_model(added.0@), plan.definitions@, added.1@),
            before.2.len() <= after.0.len() && after.0.take(before.2.len() as int) == before.2,
            before.3.len() <= after.1.len() && after.1.take(before.3.len() as int) == before.3,
            ({
                let wires = added.1@;
                let i = index as int;
                if let Some(gate) = plan.gate_by_call@[i] {
                    gate < after.0.len() && wires.len() == 2
                        && after.0[gate as int].left == wires[0] && after.0[gate as int].right == wires[1]
                } else {
                    plan.storage.by_call@[i] matches Some(slot) && slot < after.1.len() && slot < plan.storage.instances@.len()
                        && plan.storage.instances@[slot as int].storage_inputs_match(wires, Some(after.1[slot as int]))
                }
            }),
        ensures self.vm_calls_bound(limits, checked, plan, before.0.push(added.0), before.1.push(added.1), after.0, after.1),
    {
        reveal(UseAliases::vm_calls_bound);
        let arguments = before.0.push(added.0);
        let pins = before.1.push(added.1);
        assert forall|i: int| 0 <= i < pins.len() implies {
            let wires = #[trigger] pins[i];
            &&& self.call_wires_result(checked, limits.width, &plan.ports, i as usize, Ok(arguments[i]))
            &&& resolved_bits(row_model(arguments[i]@), plan.definitions@, wires@)
            &&& if let Some(gate) = plan.gate_by_call@[i] {
                gate < after.0.len() && wires@.len() == 2
                    && after.0[gate as int].left == wires@[0] && after.0[gate as int].right == wires@[1]
            } else {
                plan.storage.by_call@[i] matches Some(slot) && slot < after.1.len()
                    && slot < plan.storage.instances@.len()
                    && plan.storage.instances@[slot as int].storage_inputs_match(wires@, Some(after.1[slot as int]))
            }
        } by {
            if i < index {
                assert(arguments[i] == before.0[i] && pins[i] == before.1[i]);
                if let Some(gate) = plan.gate_by_call@[i] {
                    assert(after.0[gate as int] == before.2[gate as int]);
                } else {
                    let slot = plan.storage.by_call@[i]->Some_0 as int;
                    assert(after.1[slot] == before.3[slot]);
                }
            }
        };
    }

    spec fn vm_wiring_on_checked(
        &self, limits: ClockedModuleVmLimits, checked: &ModuleCalls, plan: &ClockedModuleEndpoints,
        vm: &ClockedModuleVm,
    ) -> bool {
        let external = plan.ports.inputs.total_bits_model();
        &&& vm.inputs == plan.ports.inputs && vm.outputs == plan.ports.outputs
        &&& exists|circuit: ClockedNor, storage: Seq<ClockedStorageInputs>,
            arguments: Seq<Vec<Vec<ClockedWireDriver>>>, pins: Seq<Vec<Wire>>| {
            &&& #[trigger] self.vm_calls_bound(limits, checked, plan, arguments, pins, circuit.netlist_model().gates@, storage)
            &&& #[trigger] clocked_vm_result(&circuit, external, storage, limits.state_bits, Ok(vm.vm))
            &&& pins.len() == checked.calls@.len()
            &&& circuit.netlist_model().gates@.len() == plan.gate_count && storage.len() == plan.storage.instances@.len()
            &&& circuit.netlist_model().input_count == plan.storage.augmented_inputs
            &&& resolved_bits(row_model(plan.ports.drivers@), plan.definitions@, circuit.netlist_model().outputs@)
        }
    }

    proof fn finish_vm_wiring(
        &self, limits: ClockedModuleVmLimits, checked: &ModuleCalls, plan: &ClockedModuleEndpoints,
        vm: &ClockedModuleVm, circuit: &ClockedNor, storage: Seq<ClockedStorageInputs>,
        arguments: Seq<Vec<Vec<ClockedWireDriver>>>, pins: Seq<Vec<Wire>>,
    )
        requires
            vm.inputs == plan.ports.inputs, vm.outputs == plan.ports.outputs,
            self.vm_calls_bound(limits, checked, plan, arguments, pins, circuit.netlist_model().gates@, storage),
            clocked_vm_result(circuit, plan.ports.inputs.total_bits_model(), storage, limits.state_bits, Ok(vm.vm)),
            pins.len() == checked.calls@.len(),
            circuit.netlist_model().gates@.len() == plan.gate_count,
            storage.len() == plan.storage.instances@.len(),
            circuit.netlist_model().input_count == plan.storage.augmented_inputs,
            resolved_bits(row_model(plan.ports.drivers@), plan.definitions@, circuit.netlist_model().outputs@),
        ensures self.vm_wiring_on_checked(limits, checked, plan, vm),
    {
    }

    fn assemble_direct_vm(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, checked: &ModuleCalls<'p, 'a>,
        plan: ClockedModuleEndpoints<'p, 'a>,
    ) -> (result: Result<ClockedModuleVm, ClockedModuleVmError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
            self.endpoints_on_checked(checked, limits.width, limits.wiring_bits, limits.gates, &plan),
        ensures result matches Ok(compiled) ==> compiled.vm.valid() && compiled.vm.initial()
            && compiled.vm.external_count() == compiled.inputs.total_bits_model()
            && self.vm_wiring_on_checked(limits, checked, &plan, &compiled),
    {
        let mut gates = Vec::new();
        let mut storage: Vec<ClockedStorageInputs> = Vec::new();
        if gates.try_reserve_exact(plan.gate_count).is_err()
            || storage.try_reserve_exact(plan.storage.instances.len()).is_err() {
            return Err(ClockedModuleVmError::Allocation);
        }
        let mut index = 0;
        let ghost mut args = Seq::<Vec<Vec<ClockedWireDriver>>>::empty();
        let ghost mut pins = Seq::<Vec<Wire>>::empty();
        assert(self.vm_calls_bound(limits, checked, &plan, args, pins, gates@, storage@)) by {
            reveal(UseAliases::vm_calls_bound);
            vstd::std_specs::vec::axiom_spec_len(&checked.calls);
        };
        while index < checked.calls.len()
            invariant
                self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
                self.endpoints_on_checked(checked, limits.width, limits.wiring_bits, limits.gates, &plan),
                index == args.len() == pins.len() <= checked.calls@.len(),
                self.vm_calls_bound(limits, checked, &plan, args, pins, gates@, storage@),
            decreases checked.calls@.len() - index,
        {
            let call = &checked.calls[index].inputs.ports.signature;
            let site = LocatedName { source: call.source, span: call.call.span.start..call.call.span.end };
            proof {
                self.storage_layout_call(checked, limits.width, plan.ports.inputs.total_bits_model(),
                    limits.wiring_bits, &plan.storage, index);
            }
            let arguments = match self.wire_call_arguments(owner, limits.width, limits.wiring_bits, checked, &plan.ports, index) {
                Ok(arguments) => arguments,
                Err(error) => return Err(ClockedModuleVmError::Arguments(error)),
            };
            let wires = match resolve_rows(arguments.as_slice(), plan.definitions.as_slice()) {
                Ok(wires) => wires,
                Err(ResolveRowsError::Allocation) => return Err(ClockedModuleVmError::Allocation),
                Err(ResolveRowsError::Driver { port, .. }) => {
                    proof { self.call_wires_count(checked, limits.width, &plan.ports, index, arguments); }
                    let argument = self.module_argument(owner, limits.width, checked, index, port);
                    return Err(ClockedModuleVmError::CallWiring(crate::project::circuits::form_location(
                        argument.source, argument.forms, argument.root)));
                },
            };
            let ghost before = (args, pins, gates@, storage@);
            if let Some(gate) = plan.gate_by_call[index] {
                if gate != gates.len() || wires.len() != 2 {
                    return Err(ClockedModuleVmError::CallWiring(site));
                }
                gates.push(NorGate { left: wires[0], right: wires[1] });
            } else if let Some(instance) = plan.storage.by_call[index] {
                if instance != storage.len() {
                    return Err(ClockedModuleVmError::CallWiring(site));
                }
                let placement = &plan.storage.instances[instance];
                let Some(inputs) = placement.storage_inputs(wires.as_slice()) else {
                    return Err(ClockedModuleVmError::CallWiring(site));
                };
                storage.push(inputs);
            } else {
                return Err(ClockedModuleVmError::CallWiring(site));
            }
            proof {
                assert(gates@.take(before.2.len() as int) =~= before.2);
                assert(storage@.take(before.3.len() as int) =~= before.3);
                self.extend_bound_calls(limits, checked, &plan, before, (gates@, storage@), (arguments, wires), index);
                args = args.push(arguments);
                pins = pins.push(wires);
            }
            index += 1;
        }
        if gates.len() != plan.gate_count || storage.len() != plan.storage.instances.len() {
            return Err(ClockedModuleVmError::InstanceCount);
        }
        let outputs = match resolve_rows(plan.ports.drivers.as_slice(), plan.definitions.as_slice()) {
            Ok(outputs) => outputs,
            Err(ResolveRowsError::Allocation) => return Err(ClockedModuleVmError::Allocation),
            Err(ResolveRowsError::Driver { port, bit }) => {
                let declared = &checked.module.expressions.typed.sources.roots.wiring.drivers.signature.outputs;
                let site = if port < declared.len() {
                    Some(super::super::copy_location(&declared[port].annotation))
                } else { None };
                return Err(ClockedModuleVmError::OutputWiring { port, bit, site });
            },
        };
        let netlist = NorNetlist { input_count: plan.storage.augmented_inputs, gates, outputs };
        let circuit = match ClockedNor::check(netlist) {
            Ok(circuit) => circuit,
            Err(error) => return Err(ClockedModuleVmError::Netlist(error)),
        };
        let external = plan.ports.inputs.total_bits();
        let ghost source_plan = plan;
        let ghost built = circuit;
        let ghost boards = storage@;
        match ClockedVm::new(circuit, external, storage, limits.state_bits) {
            Ok(vm) => {
                let result = ClockedModuleVm { inputs: plan.ports.inputs, outputs: plan.ports.outputs, vm };
                proof { self.finish_vm_wiring(limits, checked, &source_plan, &result, &built, boards, args, pins); }
                Ok(result)
            },
            Err(error) => {
                let site = if let ClockedVmError::Storage { instance, .. } = error {
                    if instance < plan.storage.instances.len() {
                        Some(super::super::copy_location(&plan.storage.instances[instance].call))
                    } else { None }
                } else { None };
                Err(ClockedModuleVmError::Vm(error, site))
            },
        }
    }

    /// 実行時のゲート、状態素子、公開出力が、ソースで指定した配線を読むことを表す。
    pub closed spec fn clocked_module_vm_wiring(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, vm: &ClockedModuleVm,
    ) -> bool {
        exists|checked: ModuleCalls, plan: ClockedModuleEndpoints|
            #[trigger] self.module_calls_result(owner, limits.width, Ok(Some(checked)))
            && #[trigger] self.endpoints_on_checked(&checked, limits.width, limits.wiring_bits, limits.gates, &plan)
            && self.vm_wiring_on_checked(limits, &checked, &plan, vm)
    }

    /// 直接の基底 NOR、ラッチ、RAM の呼び出しから tick 実行用の VM を初期化する。
    ///
    /// 実引数には裸の信号名、ビットリテラル、信号名からのビット選択を使える。
    /// 指定位置がモジュール本体を指さない場合は `Ok(None)` を返す。
    ///
    /// # Errors
    ///
    /// 型、定義と出力の配置、直接呼び出しの入力、ネットリスト、状態メモリの順に検査する。
    pub fn lower_clocked_vm(&self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits)
        -> (result: Result<Option<ClockedModuleVm>, ClockedModuleVmError<'p, 'a>>)
        requires self.can_resolve(),
        ensures result matches Ok(Some(compiled)) ==> compiled.vm.valid() && compiled.vm.initial()
            && compiled.vm.external_count() == compiled.inputs.total_bits_model()
            && self.clocked_module_vm_wiring(owner, limits, &compiled),
    {
        let checked = match self.check_module_calls(owner, limits.width) {
            Ok(Some(checked)) => checked,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ClockedModuleVmError::Endpoints(ClockedEndpointError::Calls(error))),
        };
        let plan = match self.prepare_vm_endpoints(owner, limits.width, limits.wiring_bits, limits.gates, &checked) {
            Ok(plan) => plan,
            Err(error) => return Err(ClockedModuleVmError::Endpoints(error)),
        };
        match self.assemble_direct_vm(owner, limits, &checked, plan) {
            Ok(vm) => Ok(Some(vm)),
            Err(error) => Err(error),
        }
    }
}

} // verus!
