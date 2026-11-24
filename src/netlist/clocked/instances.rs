//! 回路全体に予約した番号を使い、順序回路のインスタンスの配線を接続する。

use super::{ClockedNor, Wire, wire_within};
use crate::netlist::{ClockedStorageInputs, NorGate, instances::instantiate_wire};
#[cfg(verus_only)]
use super::{NorNetlist, TickFrame, clocked_gate_updates, clocked_wiring_valid, gate_prefix_valid, tick_matches};
#[cfg(verus_only)]
use crate::netlist::{instances::{instance_gates_at, instance_gates_match, instance_outputs_match, instance_wire},
    clocked_storage_output_width, clocked_storage_pin_values, output_ports_available, output_values_match, wire_available, wire_value};
#[cfg(verus_only)]
use crate::netlist::clocked_vm::{storage_output_width_total, wiring_width, wiring_width_grows, wiring_width_step, wiring_width_zero};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 子回路のゲートを追加する前に見つかった組み立て上の違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedInstanceError {
    /// 実引数のビット数が子回路の入力数と異なる。
    InputCount,
    /// 追加後のゲート数が、親回路全体で予約した件数を超える。
    GateCapacity,
    /// 最初に見つかった、親回路の範囲外を指す実引数の添字。
    Argument(usize),
}

/// 親に配置した状態付きインスタンスの公開出力と状態素子の入力配線。
#[derive(Debug)]
pub struct ClockedStatefulInstance {
    /// 子の公開出力を親へ移した配線。ポート順とビット順を保つ。
    pub outputs: Vec<Wire>,
    /// 子のインスタンス順で親に移した状態素子の入力配線。
    pub storage: Vec<ClockedStorageInputs>,
}

/// 状態付きインスタンスの配線を変換できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedStatefulInstanceError {
    /// 子の外部入力と状態出力の総幅が、子のネットリストの入力幅と一致しない。
    InputLayout,
    /// 子の状態出力を並べると、親の増補入力の範囲を超える。
    StorageCapacity,
    /// 親の引数またはゲートの配置に違反があった。
    Instance(ClockedInstanceError),
    /// 子回路の範囲外を参照する最初の状態素子の添字。
    StoragePins(usize),
    /// ゲート列、子の入出力配線列、または状態素子の配線列を確保できなかった。
    Allocation,
}

spec fn arguments_valid(arguments: Seq<Wire>, inputs: usize, planned: usize, end: int) -> bool {
    &&& 0 <= end <= arguments.len()
    &&& forall|i: int| 0 <= i < end ==> wire_available(#[trigger] arguments[i], inputs as nat, planned as nat)
}

/// 追加前のゲート列、実引数、予約件数から、接続結果と最初の診断を定める。
pub closed spec fn clocked_instance_result(
    callee: &NorNetlist, before: Seq<NorGate>, arguments: Seq<Wire>, inputs: usize, planned: usize,
    after: Seq<NorGate>, result: Result<Vec<Wire>, ClockedInstanceError>,
) -> bool {
    let total = before.len() + callee.gates@.len();
    match result {
        Err(error) => after == before && match error {
            ClockedInstanceError::InputCount => arguments.len() != callee.input_count,
            ClockedInstanceError::GateCapacity => arguments.len() == callee.input_count && total > planned,
            ClockedInstanceError::Argument(at) => arguments.len() == callee.input_count && total <= planned
                && at < arguments.len() && arguments_valid(arguments, inputs, planned, at as int)
                && !wire_available(arguments[at as int], inputs as nat, planned as nat),
        },
        Ok(outputs) =>
            arguments.len() == callee.input_count && total <= planned
                && arguments_valid(arguments, inputs, planned, arguments.len() as int)
                && instance_gates_match(before, callee.gates@, arguments, after)
                && instance_outputs_match(callee.outputs@, arguments, before.len() as usize, outputs@)
                && (forall|i: int| before.len() <= i < after.len() ==> {
                    let gate = #[trigger] after[i];
                    wire_available(gate.left, inputs as nat, planned as nat)
                        && wire_available(gate.right, inputs as nat, planned as nat)
                })
                && (forall|i: int| 0 <= i < outputs@.len() ==>
                    wire_available(#[trigger] outputs@[i], inputs as nat, planned as nat)),
    }
}

#[verifier::opaque]
spec fn storage_pins_prefix(storage: Seq<ClockedStorageInputs>, inputs: usize, gates: usize, end: int) -> bool {
    &&& 0 <= end <= storage.len()
    &&& forall|i: int| 0 <= i < end ==> (#[trigger] storage[i]).pins_available(inputs as nat, gates as nat)
}

fn check_instance_storage(storage: &[ClockedStorageInputs], inputs: usize, gates: usize)
    -> (result: Option<usize>)
    ensures match result {
        None => storage_pins_prefix(storage@, inputs, gates, storage@.len() as int),
        Some(i) => i < storage@.len() && storage_pins_prefix(storage@, inputs, gates, i as int)
            && !storage@[i as int].pins_available(inputs as nat, gates as nat),
    },
{
    let mut i = 0;
    assert(storage_pins_prefix(storage@, inputs, gates, 0)) by { reveal(storage_pins_prefix); };
    while i < storage.len()
        invariant i <= storage@.len(), storage_pins_prefix(storage@, inputs, gates, i as int),
        decreases storage@.len() - i,
    {
        if !storage[i].pin_wiring_in_range(inputs, gates) { return Some(i); }
        assert(storage_pins_prefix(storage@, inputs, gates, i + 1)) by {
            reveal(storage_pins_prefix);
        };
        i += 1;
    }
    None
}

#[verifier::opaque]
spec fn placed_storage_prefix(
    child: Seq<ClockedStorageInputs>, arguments: Seq<Wire>, base: usize,
    parent: Seq<ClockedStorageInputs>, inputs: usize, gates: usize,
) -> bool {
    &&& parent.len() <= child.len()
    &&& forall|i: int| 0 <= i < parent.len() ==> {
        let mapped = #[trigger] parent[i];
        child[i].parent_placement_matches(arguments, base, &mapped)
            && mapped.pins_available(inputs as nat, gates as nat)
    }
}

/// 状態付きの子の配線と、親へ移したゲート、出力、状態素子の対応を表す。
pub closed spec fn clocked_stateful_instance_result(
    callee: &NorNetlist, child: Seq<ClockedStorageInputs>, before: Seq<NorGate>, arguments: Seq<Wire>,
    inputs: usize, planned: usize, after: Seq<NorGate>,
    result: Result<ClockedStatefulInstance, ClockedStatefulInstanceError>,
) -> bool {
    let base = before.len() as usize;
    let count = callee.gates@.len() as usize;
    let arguments_ok = instance_arguments_result(arguments, callee.input_count, base, count, inputs, planned, Ok(()));
    let storage_ok = storage_pins_prefix(child, callee.input_count, count, child.len() as int);
    match result {
        Ok(instance) => arguments_ok && storage_ok
            && clocked_instance_result(callee, before, arguments, inputs, planned, after, Ok(instance.outputs))
            && placed_storage_prefix(child, arguments, base, instance.storage@, inputs, planned)
            && instance.storage@.len() == child.len(),
        Err(error) => after == before && match error {
            ClockedStatefulInstanceError::Instance(reason) =>
                clocked_instance_result(callee, before, arguments, inputs, planned, after, Err(reason)),
            ClockedStatefulInstanceError::StoragePins(i) => arguments_ok
                && i < child.len() && storage_pins_prefix(child, callee.input_count, count, i as int)
                && !child[i as int].pins_available(callee.input_count as nat, count as nat),
            ClockedStatefulInstanceError::Allocation => arguments_ok && storage_ok,
            ClockedStatefulInstanceError::InputLayout | ClockedStatefulInstanceError::StorageCapacity => false,
        },
    }
}

fn storage_outputs_fit(child: &[ClockedStorageInputs], bits: usize) -> (fit: bool)
    ensures fit <==> wiring_width(child@, child@.len()) == bits,
{
    let mut used = 0usize;
    let mut i = 0usize;
    proof { wiring_width_zero(child@); }
    while i < child.len()
        invariant i <= child@.len(), used == wiring_width(child@, i as nat) <= bits,
        decreases child@.len() - i,
    {
        let width = child[i].data.len();
        proof { wiring_width_step(child@, i as nat); }
        if width > bits - used {
            proof { wiring_width_grows(child@, (i + 1) as nat, child@.len()); }
            return false;
        }
        used += width;
        i += 1;
    }
    used == bits
}

/// 子の外部入力に、親でこの子のために予約する状態出力の連続区間を続ける。
pub open spec fn clocked_stateful_arguments(external: Seq<Wire>, start: usize, width: nat) -> Seq<Wire> {
    external + Seq::new(width, |bit: int| Wire::Input((start + bit) as usize))
}

fn collect_stateful_arguments(
    external: &[Wire], _total: usize, start: usize, width: usize,
) -> (result: Option<Vec<Wire>>)
    requires external@.len() + width == _total, start + width <= usize::MAX,
    ensures result matches Some(arguments) ==> arguments@ == clocked_stateful_arguments(external@, start, width as nat),
{
    let mut arguments = Vec::new();
    if arguments.try_reserve_exact(_total).is_err() { return None; }
    let mut i = 0usize;
    while i < external.len()
        invariant i <= external@.len(), arguments@ == external@.take(i as int),
        decreases external@.len() - i,
    {
        arguments.push(external[i]);
        assert(arguments@ =~= external@.take(i + 1));
        i += 1;
    }
    assert(arguments@ =~= external@);
    let mut bit = 0usize;
    while bit < width
        invariant
            bit <= width, start + width <= usize::MAX,
            arguments@ == clocked_stateful_arguments(external@, start, bit as nat),
        decreases width - bit,
    {
        arguments.push(Wire::Input(start + bit));
        assert(arguments@ =~= clocked_stateful_arguments(external@, start, (bit + 1) as nat));
        bit += 1;
    }
    Some(arguments)
}

proof fn mapped_wire_available(
    wire: Wire, arguments: Seq<Wire>, base: usize, inputs: usize, planned: usize, callee_gates: nat,
)
    requires wire_available(wire, arguments.len(), callee_gates), base + callee_gates <= planned,
        arguments_valid(arguments, inputs, planned, arguments.len() as int),
    ensures wire_available(instance_wire(wire, arguments, base), inputs as nat, planned as nat),
{
    if let Wire::Input(i) = wire {
        assert(wire_available(arguments[i as int], inputs as nat, planned as nat));
    }
}

spec fn instance_arguments_result(
    arguments: Seq<Wire>, expected: usize, base: usize, count: usize, inputs: usize, planned: usize,
    result: Result<(), ClockedInstanceError>,
) -> bool {
    match result {
        Ok(()) => arguments.len() == expected && base + count <= planned
            && arguments_valid(arguments, inputs, planned, arguments.len() as int),
        Err(ClockedInstanceError::InputCount) => arguments.len() != expected,
        Err(ClockedInstanceError::GateCapacity) => arguments.len() == expected && base + count > planned,
        Err(ClockedInstanceError::Argument(i)) => arguments.len() == expected && base + count <= planned
            && i < arguments.len() && arguments_valid(arguments, inputs, planned, i as int)
            && !wire_available(arguments[i as int], inputs as nat, planned as nat),
    }
}

fn check_instance_arguments(
    arguments: &[Wire], expected: usize, base: usize, count: usize, inputs: usize, planned: usize,
) -> (result: Result<(), ClockedInstanceError>)
    ensures instance_arguments_result(arguments@, expected, base, count, inputs, planned, result),
{
    if arguments.len() != expected { return Err(ClockedInstanceError::InputCount); }
    if base > planned || count > planned - base { return Err(ClockedInstanceError::GateCapacity); }
    let mut i = 0;
    while i < arguments.len()
        invariant i <= arguments@.len(), arguments@.len() == expected, base + count <= planned,
            arguments_valid(arguments@, inputs, planned, i as int),
        decreases arguments@.len() - i,
    {
        if !wire_within(arguments[i], inputs, planned) {
            return Err(ClockedInstanceError::Argument(i));
        }
        i += 1;
    }
    Ok(())
}

impl ClockedNor {
    /// 子回路の全ゲートを順に追加し、親回路での出力配線を宣言順に返す。
    ///
    /// `inputs` は親回路の入力ビット数、`planned` は親回路全体の最終ゲート数。
    /// 実引数には後から追加するゲートの出力も指定できる。各ゲートは tick ごとに1回更新する。
    /// 全ゲートを追加した後、[`Self::check`] で親回路全体の配線を検査する。
    ///
    /// # Errors
    ///
    /// 実引数のビット数、追加後のゲート件数、各実引数の参照先の順に検査する。
    /// 違反があれば、親回路のゲート列を変更せずに診断を返す。
    pub fn append_instance(
        &self, caller: &mut Vec<NorGate>, arguments: &[Wire], inputs: usize, planned: usize,
    ) -> (result: Result<Vec<Wire>, ClockedInstanceError>)
        ensures
            clocked_instance_result(&self.netlist_model(), old(caller)@, arguments@, inputs, planned, final(caller)@, result),
            result.is_err() ==> final(caller)@ == old(caller)@,
            result matches Ok(outputs) ==> {
                let base = old(caller)@.len() as usize;
                &&& final(caller)@.len() == base + self.netlist_model().gates@.len() <= planned
                &&& final(caller)@.take(base as int) == old(caller)@
                &&& instance_gates_at(self.netlist_model().gates@, arguments@, base, final(caller)@)
                &&& instance_outputs_match(self.netlist_model().outputs@, arguments@, base, outputs@)
                &&& forall|i: int| base <= i < final(caller)@.len() ==> {
                    let gate = #[trigger] final(caller)@[i];
                    wire_available(gate.left, inputs as nat, planned as nat)
                        && wire_available(gate.right, inputs as nat, planned as nat)
                }
                &&& forall|i: int| 0 <= i < outputs@.len() ==>
                    wire_available(#[trigger] outputs@[i], inputs as nat, planned as nat)
            },
    {
        let callee = &self.netlist;
        check_instance_arguments(arguments, callee.input_count, caller.len(), callee.gates.len(), inputs, planned)?;
        let outputs = Vec::with_capacity(callee.outputs.len());
        Ok(self.append_checked_instance(caller, arguments, inputs, planned, outputs))
    }

    /// 親で子の状態出力の連続区間を予約し、ゲートと状態素子の配線を移す。
    ///
    /// `external` は子の外部入力を宣言順に並べる。`next_state_input` は親の増補入力で
    /// 次の状態出力を置く位置。成功時は子の状態出力の総ビット数だけ進む。返された状態素子を
    /// 予約順に VM へ渡すと、各状態出力はそのインスタンスに割り当てた位置に現れる。
    ///
    /// # Errors
    ///
    /// 子の入力幅と親の状態出力範囲を確認し、配線を変換する。失敗時は
    /// 親のゲート列の内容と状態出力の予約位置を保つ。
    pub fn append_stateful_instance(
        &self, caller: &mut Vec<NorGate>, child: &[ClockedStorageInputs], external: &[Wire],
        next_state_input: &mut usize, inputs: usize, planned: usize,
    ) -> (result: Result<ClockedStatefulInstance, ClockedStatefulInstanceError>)
        ensures
            result.is_err() ==> final(caller)@ == old(caller)@ && *final(next_state_input) == *old(next_state_input),
            result matches Ok(instance) ==> {
                let netlist = self.netlist_model();
                let width = clocked_storage_output_width(child@);
                let start = *old(next_state_input);
                &&& external@.len() + width == netlist.input_count
                &&& start + width == *final(next_state_input) <= inputs
                &&& clocked_stateful_instance_result(&netlist, child@, old(caller)@,
                    clocked_stateful_arguments(external@, start, width), inputs, planned, final(caller)@, Ok(instance))
            },
            result matches Err(error) ==> {
                let netlist = self.netlist_model();
                let width = clocked_storage_output_width(child@);
                let start = *old(next_state_input);
                (error is Instance || error is StoragePins) ==> {
                    &&& external@.len() + width == netlist.input_count
                    &&& start + width <= inputs
                    &&& clocked_stateful_instance_result(&netlist, child@, old(caller)@,
                        clocked_stateful_arguments(external@, start, width), inputs, planned, final(caller)@, Err(error))
                }
            },
            result == Err(ClockedStatefulInstanceError::InputLayout) ==>
                external@.len() + clocked_storage_output_width(child@) != self.netlist_model().input_count,
            result == Err(ClockedStatefulInstanceError::StorageCapacity) ==>
                external@.len() + clocked_storage_output_width(child@) == self.netlist_model().input_count
                && *old(next_state_input) + clocked_storage_output_width(child@) > inputs,
            result == Err(ClockedStatefulInstanceError::Allocation) ==>
                external@.len() + clocked_storage_output_width(child@) == self.netlist_model().input_count
                && *old(next_state_input) + clocked_storage_output_width(child@) <= inputs,
    {
        proof { storage_output_width_total(child@); }
        let total = self.netlist.input_count;
        if external.len() > total { return Err(ClockedStatefulInstanceError::InputLayout); }
        let width = total - external.len();
        if !storage_outputs_fit(child, width) { return Err(ClockedStatefulInstanceError::InputLayout); }
        let start = *next_state_input;
        if start > inputs || width > inputs - start { return Err(ClockedStatefulInstanceError::StorageCapacity); }
        let Some(arguments) = collect_stateful_arguments(external, total, start, width) else {
            return Err(ClockedStatefulInstanceError::Allocation);
        };
        let instance = self.append_mapped_stateful_instance(caller, child, arguments.as_slice(), inputs, planned)?;
        *next_state_input = start + width;
        Ok(instance)
    }

    fn append_mapped_stateful_instance(
        &self, caller: &mut Vec<NorGate>, child: &[ClockedStorageInputs], arguments: &[Wire],
        inputs: usize, planned: usize,
    ) -> (result: Result<ClockedStatefulInstance, ClockedStatefulInstanceError>)
        ensures
            clocked_stateful_instance_result(&self.netlist_model(), child@, old(caller)@, arguments@,
                inputs, planned, final(caller)@, result),
            result.is_err() ==> final(caller)@ == old(caller)@,
            result matches Ok(instance) ==> {
                let netlist = self.netlist_model();
                let base = old(caller)@.len() as usize;
                &&& final(caller)@.len() == base + netlist.gates@.len() <= planned
                &&& instance.storage@.len() == child@.len()
                &&& instance_outputs_match(netlist.outputs@, arguments@, base, instance.outputs@)
                &&& forall|i: int| 0 <= i < instance.storage@.len() ==>
                    child@[i].parent_placement_matches(arguments@, base, &(#[trigger] instance.storage@[i]))
            },
    {
        let callee = &self.netlist;
        let child_gates = callee.gates.len();
        let base = caller.len();
        let ghost before = caller@;
        if let Err(reason) = check_instance_arguments(arguments, callee.input_count, base, child_gates, inputs, planned) {
            return Err(ClockedStatefulInstanceError::Instance(reason));
        }
        if let Some(i) = check_instance_storage(child, callee.input_count, child_gates) {
            return Err(ClockedStatefulInstanceError::StoragePins(i));
        }
        let mut storage = Vec::new();
        if storage.try_reserve_exact(child.len()).is_err() {
            return Err(ClockedStatefulInstanceError::Allocation);
        }
        let mut i = 0usize;
        assert(placed_storage_prefix(child@, arguments@, base, storage@, inputs, planned)) by {
            reveal(placed_storage_prefix);
        };
        while i < child.len()
            invariant
                i == storage@.len() <= child@.len(), base == before.len(), caller@ == before,
                *callee == self.netlist_model(), child_gates == callee.gates@.len(), child_gates <= usize::MAX,
                instance_arguments_result(arguments@, callee.input_count, base, child_gates, inputs, planned, Ok(())),
                storage_pins_prefix(child@, callee.input_count, child_gates, child@.len() as int),
                placed_storage_prefix(child@, arguments@, base, storage@, inputs, planned),
            decreases child@.len() - i,
        {
            proof {
                assert(child@[i as int].pins_available(callee.input_count as nat, child_gates as nat)) by {
                    reveal(storage_pins_prefix);
                };
                assert(output_ports_available(arguments@, inputs as nat, planned as nat, arguments@.len() as int));
            }
            let mapped = match child[i].place_in_parent(arguments, base, child_gates, inputs, planned) {
                Ok(mapped) => mapped,
                Err(_) => return Err(ClockedStatefulInstanceError::Allocation),
            };
            let ghost previous = storage@;
            storage.push(mapped);
            assert(placed_storage_prefix(child@, arguments@, base, storage@, inputs, planned)) by {
                reveal(placed_storage_prefix);
                assert forall|j: int| 0 <= j <= i implies
                    child@[j].parent_placement_matches(arguments@, base, &(#[trigger] storage@[j]))
                        && storage@[j].pins_available(inputs as nat, planned as nat) by {
                    if j < i { assert(storage@[j] == previous[j]); }
                };
            };
            i += 1;
        }
        let mut outputs = Vec::new();
        if outputs.try_reserve_exact(callee.outputs.len()).is_err() || caller.try_reserve(child_gates).is_err() {
            return Err(ClockedStatefulInstanceError::Allocation);
        }
        let outputs = self.append_checked_instance(caller, arguments, inputs, planned, outputs);
        reveal(placed_storage_prefix);
        Ok(ClockedStatefulInstance { outputs, storage })
    }

    fn append_checked_instance(
        &self, caller: &mut Vec<NorGate>, arguments: &[Wire], _inputs: usize, _planned: usize, mut outputs: Vec<Wire>,
    ) -> (result: Vec<Wire>)
        requires
            arguments@.len() == self.netlist_model().input_count,
            old(caller)@.len() + self.netlist_model().gates@.len() <= _planned,
            arguments_valid(arguments@, _inputs, _planned, arguments@.len() as int),
            outputs@.len() == 0,
        ensures
            clocked_instance_result(&self.netlist_model(), old(caller)@, arguments@, _inputs, _planned, final(caller)@, Ok(result)),
            ({
                let base = old(caller)@.len() as usize;
                &&& final(caller)@.len() == base + self.netlist_model().gates@.len() <= _planned
                &&& final(caller)@.take(base as int) == old(caller)@
                &&& instance_gates_at(self.netlist_model().gates@, arguments@, base, final(caller)@)
                &&& instance_outputs_match(self.netlist_model().outputs@, arguments@, base, result@)
                &&& forall|i: int| base <= i < final(caller)@.len() ==> {
                    let gate = #[trigger] final(caller)@[i];
                    wire_available(gate.left, _inputs as nat, _planned as nat)
                        && wire_available(gate.right, _inputs as nat, _planned as nat)
                }
                &&& forall|i: int| 0 <= i < result@.len() ==>
                    wire_available(#[trigger] result@[i], _inputs as nat, _planned as nat)
            }),
    {
        proof { use_type_invariant(self); }
        let callee = &self.netlist;
        let base = caller.len();
        let count = callee.gates.len();
        let ghost before = caller@;
        let mut i = 0;
        assert(caller@.take(base as int) =~= before);
        while i < count
            invariant
                base == before.len(), count == callee.gates@.len(), base + count <= _planned,
                arguments@.len() == callee.input_count, i <= count,
                clocked_wiring_valid(callee), arguments_valid(arguments@, _inputs, _planned, arguments@.len() as int),
                instance_gates_match(before, callee.gates@.take(i as int), arguments@, caller@),
                forall|j: int| base <= j < caller@.len() ==> {
                    let gate = #[trigger] caller@[j];
                    wire_available(gate.left, _inputs as nat, _planned as nat)
                        && wire_available(gate.right, _inputs as nat, _planned as nat)
                },
            decreases count - i,
        {
            let gate = callee.gates[i];
            proof { assert(gate_prefix_valid(callee, count as int)); }
            let left = instantiate_wire(gate.left, arguments, base);
            let right = instantiate_wire(gate.right, arguments, base);
            proof {
                mapped_wire_available(gate.left, arguments@, base, _inputs, _planned, count as nat);
                mapped_wire_available(gate.right, arguments@, base, _inputs, _planned, count as nat);
            }
            let ghost prior = caller@;
            caller.push(NorGate { left, right });
            assert(caller@.take(base as int) =~= before);
            assert forall|j: int| 0 <= j < i + 1 implies {
                let saved = #[trigger] caller@[base + j];
                let original = callee.gates@.take(i + 1)[j];
                &&& saved.left == instance_wire(original.left, arguments@, base)
                &&& saved.right == instance_wire(original.right, arguments@, base)
                &&& wire_available(saved.left, _inputs as nat, _planned as nat)
                &&& wire_available(saved.right, _inputs as nat, _planned as nat)
            } by {
                if j < i {
                    assert(caller@[base + j] == prior[base + j]);
                    assert(callee.gates@.take(i as int)[j] == callee.gates@[j]);
                }
            };
            i += 1;
        }
        assert(callee.gates@.take(count as int) =~= callee.gates@);
        let mut i = 0;
        while i < callee.outputs.len()
            invariant
                base == before.len(), count == callee.gates@.len(), base + count <= _planned,
                arguments@.len() == callee.input_count, i == outputs@.len() <= callee.outputs@.len(),
                clocked_wiring_valid(callee), arguments_valid(arguments@, _inputs, _planned, arguments@.len() as int),
                instance_outputs_match(callee.outputs@.take(i as int), arguments@, base, outputs@),
                forall|j: int| 0 <= j < i ==> wire_available(#[trigger] outputs@[j], _inputs as nat, _planned as nat),
            decreases callee.outputs@.len() - i,
        {
            let output = callee.outputs[i];
            let wire = instantiate_wire(output, arguments, base);
            proof { mapped_wire_available(output, arguments@, base, _inputs, _planned, count as nat); }
            let ghost prior = outputs@;
            outputs.push(wire);
            assert forall|j: int| 0 <= j < outputs@.len() implies {
                let mapped = #[trigger] outputs@[j];
                mapped == instance_wire(callee.outputs@.take(i + 1)[j], arguments@, base)
                    && wire_available(mapped, _inputs as nat, _planned as nat)
            } by {
                if j < i {
                    assert(outputs@[j] == prior[j]);
                    assert(callee.outputs@.take(i as int)[j] == callee.outputs@[j]);
                }
            };
            i += 1;
        }
        assert(callee.outputs@.take(i as int) =~= callee.outputs@);
        outputs
    }
}

/// 指定した親回路の状態で、子回路の入力に接続した配線の値を読む。
pub open spec fn clocked_instance_inputs(arguments: Seq<Wire>, input: Seq<bool>, state: Seq<bool>) -> Seq<bool> {
    Seq::new(arguments.len(), |i: int| wire_value(arguments[i], input, state))
}

proof fn mapped_wire_value(
    wire: Wire, arguments: Seq<Wire>, base: usize, count: nat, input: Seq<bool>, state: Seq<bool>,
)
    requires base + count <= state.len() <= usize::MAX, wire_available(wire, arguments.len(), count),
        forall|i: int| 0 <= i < arguments.len() ==> wire_available(#[trigger] arguments[i], input.len(), state.len()),
    ensures wire_value(instance_wire(wire, arguments, base), input, state)
        == wire_value(wire, clocked_instance_inputs(arguments, input, state), state[base as int..base + count]),
{
}

/// 親回路の1 tick が、子回路の各ゲートを同じ開始状態から1回更新することを示す。
pub proof fn clocked_instance_steps_match(
    callee: &NorNetlist, parent: &NorNetlist, arguments: Seq<Wire>, base: usize,
    input: Seq<bool>, previous: Seq<bool>, frame: TickFrame,
)
    requires
        clocked_wiring_valid(callee), tick_matches(parent, previous, input, frame),
        callee.input_count == arguments.len(),
        instance_gates_at(callee.gates@, arguments, base, parent.gates@),
        forall|i: int| 0 <= i < arguments.len() ==> wire_available(#[trigger] arguments[i], input.len(), previous.len()),
    ensures
        clocked_gate_updates(callee.gates@, clocked_instance_inputs(arguments, input, previous),
            previous[base as int..base + callee.gates@.len()],
            frame.gates@[base as int..base + callee.gates@.len()]),
{
    let count = callee.gates@.len();
    vstd::std_specs::vec::axiom_spec_len(&parent.gates);
    let local_before = previous[base as int..base + count];
    let local_after = frame.gates@[base as int..base + count];
    let inputs = clocked_instance_inputs(arguments, input, previous);
    assert forall|i: int| 0 <= i < local_after.len() implies {
        let gate = callee.gates@[i];
        (#[trigger] local_after[i]) == !(wire_value(gate.left, inputs, local_before)
            || wire_value(gate.right, inputs, local_before))
    } by {
        let gate = callee.gates@[i];
        let mapped = parent.gates@[base + i];
        assert(mapped.left == instance_wire(gate.left, arguments, base));
        assert(mapped.right == instance_wire(gate.right, arguments, base));
        mapped_wire_value(gate.left, arguments, base, count, input, previous);
        mapped_wire_value(gate.right, arguments, base, count, input, previous);
        assert(local_after[i] == frame.gates@[base + i]);
    };
}

/// 観測対象の親回路の状態から、子回路の出力配線も同じ値を読むことを示す。
///
/// tick 後の観測では確定済みの状態を渡す。子の出力が実引数に直結している場合も、その値を使う。
pub proof fn clocked_instance_outputs_match(
    callee: &NorNetlist, arguments: Seq<Wire>, mapped: Seq<Wire>, base: usize,
    input: Seq<bool>, state: Seq<bool>, values: Seq<bool>,
)
    requires
        clocked_wiring_valid(callee), callee.input_count == arguments.len(),
        base + callee.gates@.len() <= state.len() <= usize::MAX,
        instance_outputs_match(callee.outputs@, arguments, base, mapped), values.len() == mapped.len(),
        output_values_match(input, state, mapped, values),
        forall|i: int| 0 <= i < arguments.len() ==> wire_available(#[trigger] arguments[i], input.len(), state.len()),
    ensures output_values_match(clocked_instance_inputs(arguments, input, state),
        state[base as int..base + callee.gates@.len()], callee.outputs@, values),
{
    let count = callee.gates@.len();
    let inputs = clocked_instance_inputs(arguments, input, state);
    let local = state[base as int..base + count];
    assert forall|i: int| 0 <= i < values.len() implies
        (#[trigger] values[i]) == wire_value(callee.outputs@[i], inputs, local) by {
        let output = callee.outputs@[i];
        assert(mapped[i] == instance_wire(output, arguments, base));
        mapped_wire_value(output, arguments, base, count, input, state);
    };
}

proof fn instance_pin_values_match(
    child: Seq<Wire>, mapped: Seq<Wire>, arguments: Seq<Wire>, base: usize, count: nat,
    input: Seq<bool>, state: Seq<bool>,
)
    requires
        instance_outputs_match(child, arguments, base, mapped),
        output_ports_available(child, arguments.len(), count, child.len() as int),
        output_ports_available(arguments, input.len(), state.len(), arguments.len() as int),
        base + count <= state.len() <= usize::MAX,
    ensures mapped.map_values(|wire: Wire| wire_value(wire, input, state)) ==
        child.map_values(|wire: Wire| wire_value(wire, clocked_instance_inputs(arguments, input, state),
            state[base as int..base + count])),
{
    let inputs = clocked_instance_inputs(arguments, input, state);
    let local = state[base as int..base + count];
    let actual = mapped.map_values(|wire: Wire| wire_value(wire, input, state));
    let expected = child.map_values(|wire: Wire| wire_value(wire, inputs, local));
    assert forall|i: int| 0 <= i < child.len() implies actual[i] == expected[i] by {
        assert(mapped[i] == instance_wire(child[i], arguments, base));
        mapped_wire_value(child[i], arguments, base, count, input, state);
    };
    assert(actual =~= expected);
}

/// 親に移した状態素子が、子の回路で読んだときと同じ入力値を得ることを示す。
pub proof fn clocked_stateful_instance_reads_match(
    callee: &NorNetlist, child: Seq<ClockedStorageInputs>, before: Seq<NorGate>, arguments: Seq<Wire>,
    inputs: usize, planned: usize, after: Seq<NorGate>, instance: &ClockedStatefulInstance, index: int,
    input: Seq<bool>, state: Seq<bool>,
)
    requires
        clocked_stateful_instance_result(callee, child, before, arguments, inputs, planned, after, Ok(*instance)),
        0 <= index < child.len(),
        input.len() == inputs, state.len() == planned,
    ensures clocked_storage_pin_values(&instance.storage@[index], input, state) ==
        clocked_storage_pin_values(&child[index], clocked_instance_inputs(arguments, input, state),
            state[before.len() as int..before.len() + callee.gates@.len()]),
{
    reveal(storage_pins_prefix);
    reveal(placed_storage_prefix);
    let base = before.len() as usize;
    let count = callee.gates@.len();
    let original = child[index];
    let mapped = instance.storage@[index];
    assert(placed_storage_prefix(child, arguments, base, instance.storage@, inputs, planned));
    assert(original.parent_placement_matches(arguments, base, &mapped));
    assert(original.pins_available(arguments.len(), count));
    assert(output_ports_available(arguments, input.len(), state.len(), arguments.len() as int));
    if let Some(address) = original.address {
        let mapped_address = mapped.address->Some_0;
        instance_pin_values_match(address@, mapped_address@, arguments, base, count, input, state);
    }
    instance_pin_values_match(original.data@, mapped.data@, arguments, base, count, input, state);
    mapped_wire_value(original.enable, arguments, base, count, input, state);
}

} // verus!
