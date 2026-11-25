//! 2入力 NOR を基底とする組み合わせ回路の配線と評価。
//!
//! `func` の単体評価では、先行ゲートの評価値を読み、入力から出力まで値を伝える。

mod clocked;
mod clocked_io;
mod clocked_storage;
mod clocked_session;
mod clocked_vm;
pub(crate) mod instances;
mod port_layout;
mod state_elements;
#[cfg(verus_only)]
mod source_trace;
#[cfg(verus_only)]
mod source_vm_trace;
#[cfg(verus_only)]
pub(crate) use source_vm_trace::{
    source_vm_layout_for_orders, source_vm_layout_from_pairs, source_vm_layout_port_evidence, source_vm_lift_stateless,
    source_vm_paired_rows_agree,
    source_vm_row_pair, source_vm_stateless_model, source_vm_storage_pair,
    source_vm_terminal_pair,
};
#[cfg(verus_only)]
pub use source_vm_trace::{
    SourceDeviceId, SourceDeviceState, SourceStorage, SourceVmCircuit, SourceVmFrame, SourceVmNor,
    SourceVmLayout, SourceVmState, SourceVmWire, source_vm_layout_matches, source_vm_mapped_wire_value,
    source_vm_next_frame, source_vm_outputs_match, source_vm_project_observation, source_vm_project_reset,
    source_vm_project_step, source_vm_project_trace, source_vm_read_wire,
    source_vm_reset_frame, source_vm_reset_matches, source_vm_state_projection,
    source_vm_run_trace, source_vm_state_matches, source_vm_step_matches, source_vm_trace,
    source_vm_trace_outputs_agree, source_vm_traces_agree, source_vm_wire_matches, source_vm_wiring_valid,
};

pub use clocked::{ClockedNor, ClockedNorError, TickFrame, TickInputError};
pub use clocked::{ClockedInstanceError, ClockedStatefulInstance, ClockedStatefulInstanceError};
#[cfg(verus_only)]
pub use clocked::{clocked_mapped_storage_reads_match, clocked_stateful_arguments, clocked_stateful_instance_reads_match, clocked_stateful_instance_result,
    clocked_storage_pins_valid};
pub use clocked_storage::{ClockedStorage, ClockedStorageError, ClockedStorageInputs};
#[cfg(verus_only)]
pub use clocked_storage::{clocked_storage_memory_width, clocked_storage_pin_values, clocked_storage_result, clocked_storage_steps_agree,
    clocked_storage_value_transition};
pub use clocked_io::PendingIoTick;
pub use clocked_session::{ClockedSession, PendingIoReset, PendingVmTick};
pub use clocked_vm::{ClockedVm, ClockedVmError};
#[cfg(verus_only)]
pub use clocked_vm::{clocked_storage_output_width, clocked_storage_width_concat, clocked_storage_width_push, clocked_storage_widths_agree,
    clocked_vm_result, clocked_vm_trace, clocked_vm_trace_from_reset, clocked_vm_trace_push_tick};
pub(crate) use clocked::wire_within;
#[cfg(verus_only)]
pub(crate) use clocked::{clocked_wiring_endpoints, clocked_wiring_from_endpoints};
#[cfg(verus_only)]
pub use clocked::{
    clocked_gate_updates, clocked_wiring_error, clocked_wiring_valid, nor_trace, nor_trace_from_reset, nor_trace_push_tick,
    nor_traces_agree, reset_matches, tick_matches,
};
#[cfg(verus_only)]
pub use clocked::{clocked_instance_gate_updates_match, clocked_instance_inputs, clocked_instance_outputs_match,
    clocked_instance_result, clocked_instance_steps_match};
#[cfg(verus_only)]
pub use instances::{instance_gates_at, instance_gates_in_extension, instance_outputs_match, instance_wire};
pub use port_layout::{PortBitLayout, PortBitLayoutError};
pub use state_elements::{LatchState, RamState, StateAllocationError, StateInputError};
#[cfg(verus_only)]
pub use state_elements::{latch_next, ram_address_value, ram_next_memory, ram_read_word, ram_resident_bits, state_bits_fit};
#[cfg(verus_only)]
pub use source_trace::{
    SourceGateId, SourceNor, SourceTickCircuit, SourceTickFrame, SourceWire, source_clocked_layout, source_clocked_layout_valid,
    source_reset_matches, source_step_matches, source_tick_trace, source_tick_traces_agree, source_trace_from_flat,
    source_trace_outputs_preserved, source_wiring_valid,
};
#[cfg(verus_only)]
pub(crate) use source_trace::{
    builtin_nor_source, builtin_nor_source_layout, builtin_nor_template,
    source_gate_under, source_instance_gate_agrees, source_instance_order, source_instance_order_at,
    source_instance_outputs_agree, source_wire_in_parent, source_gate_under_distinct, source_gate_belongs_to_call,
    source_call_gate_order, source_call_order_appended, source_instance_order_appended,
    source_clocked_layout_from_pairs, source_gate_positions_distinct, source_gate_wiring_pair, source_output_pair_at, source_output_pairs,
    source_output_wiring_pair, source_trace_gate_index, source_trace_layout_counts, source_wire_pair,
};
#[cfg(verus_only)]
pub use port_layout::{port_bit_layout_port, port_bit_layout_result, port_bit_layout_size, port_widths_fit, preceding_port_bits};
#[cfg(verus_only)]
pub(crate) use port_layout::preceding_port_bits_grow;

use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 1ビットの配線元。入力とゲートはそれぞれ0から番号を付ける。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Wire {
    /// 平坦な入力列の1ビット。
    Input(usize),
    /// 固定値を持つ配線。
    Constant(bool),
    /// NOR ゲートの出力。
    Gate(usize),
}

/// 2本の配線を入力とする NOR ゲート。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NorGate {
    /// 先に検査する入力配線。
    pub left: Wire,
    /// 後に検査する入力配線。
    pub right: Wire,
}

/// ゲートの入力側を識別する。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GateInput {
    /// 左の入力。
    Left,
    /// 右の入力。
    Right,
}

/// 組み合わせ回路の評価前または評価中に検出した入力・配線の違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NorEvaluationError {
    /// 入力列の長さが入力ビット数と一致しない。
    InputCount {
        /// ネットリストの入力ビット数。
        expected: usize,
        /// 渡された入力値の数。
        actual: usize,
    },
    /// ゲートの入力が存在する入力ビット、定数、先行ゲートのいずれも指していない。
    GateInput {
        /// 違反があるゲートの番号。
        gate: usize,
        /// 違反がある入力側。
        input: GateInput,
    },
    /// 出力ビットの配線元が存在しない。
    Output {
        /// 違反がある出力ビットの添字。
        output: usize,
    },
}

/// 1ビット配線で構成する NOR ネットリスト。
///
/// 組み合わせ評価の [`Self::evaluate`] では、ゲート入力から参照できるゲートを配列内の先行ゲートに限る。
/// tick 単位の [`ClockedNor::check`] では、同じ回路内の全ゲートを参照できる。
/// 入出力はポートの宣言順に並び、各ポート内は最下位ビットから並ぶ。
#[derive(Debug, Eq, PartialEq)]
pub struct NorNetlist {
    /// 平坦な入力列のビット数。
    pub input_count: usize,
    /// ゲート番号順の配列。組み合わせ評価では、参照先が参照元より先に現れる順に置く。
    pub gates: Vec<NorGate>,
    /// 平坦な出力列の各ビットを駆動する配線。
    pub outputs: Vec<Wire>,
}

/// 指定した数の入力ポートと先行ゲートから、配線元を参照できることを表す。
pub open spec fn wire_available(wire: Wire, inputs: nat, gates: nat) -> bool {
    match wire {
        Wire::Input(index) => index < inputs,
        Wire::Constant(_) => true,
        Wire::Gate(index) => index < gates,
    }
}

/// 入力値またはゲートの出力値から、配線元の値を求める。
pub open spec fn wire_value(wire: Wire, inputs: Seq<bool>, gates: Seq<bool>) -> bool
    recommends wire_available(wire, inputs.len(), gates.len()),
{
    match wire {
        Wire::Input(index) => inputs[index as int],
        Wire::Constant(value) => value,
        Wire::Gate(index) => gates[index as int],
    }
}

/// 指定した位置までのゲートが参照順に並んでいることを表す。
pub open spec fn gates_available(gates: Seq<NorGate>, inputs: nat, end: int) -> bool {
    &&& 0 <= end <= gates.len()
    &&& forall|i: int| 0 <= i < end ==> {
        &&& wire_available((#[trigger] gates[i]).left, inputs, i as nat)
        &&& wire_available(gates[i].right, inputs, i as nat)
    }
}

/// 指定した位置までの出力ポートが参照可能な配線を持つことを表す。
pub open spec fn output_ports_available(ports: Seq<Wire>, inputs: nat, gates: nat, end: int) -> bool {
    &&& 0 <= end <= ports.len()
    &&& forall|i: int| 0 <= i < end ==> wire_available(#[trigger] ports[i], inputs, gates)
}

/// 入力数と全配線の参照先が、ネットリストの評価条件を満たすことを表す。
pub open spec fn nor_evaluation_ready(netlist: &NorNetlist, input_count: nat) -> bool {
    let gates = netlist.gates@;
    let ports = netlist.outputs@;
    &&& input_count == netlist.input_count
    &&& gates_available(gates, input_count, gates.len() as int)
    &&& output_ports_available(ports, input_count, gates.len(), ports.len() as int)
}

/// ゲート列の先頭から、各値が NOR の真理値を満たすことを表す。
#[verifier::opaque]
pub open spec fn gate_values_match(input: Seq<bool>, gates: Seq<NorGate>, values: Seq<bool>) -> bool {
    &&& gates_available(gates, input.len(), values.len() as int)
    &&& forall|i: int| 0 <= i < values.len() ==> {
        let gate = gates[i];
        (#[trigger] values[i]) == !(wire_value(gate.left, input, values) || wire_value(gate.right, input, values))
    }
}

/// 出力値が宣言順に各ポートの配線元から得られることを表す。
pub open spec fn output_values_match(
    input: Seq<bool>, gates: Seq<bool>, ports: Seq<Wire>, values: Seq<bool>,
) -> bool {
    &&& output_ports_available(ports, input.len(), gates.len(), values.len() as int)
    &&& forall|i: int| 0 <= i < values.len() ==>
        (#[trigger] values[i]) == wire_value(ports[i], input, gates)
}

/// 完全なゲート評価とポート順の射影により、ネットリストの出力値を定める。
#[verifier::opaque]
pub open spec fn nor_evaluation(netlist: &NorNetlist, input: Seq<bool>, output: Seq<bool>) -> bool {
    &&& input.len() == netlist.input_count
    &&& output.len() == netlist.outputs@.len()
    &&& exists|values: Seq<bool>| #[trigger] gate_values_match(input, netlist.gates@, values)
        && values.len() == netlist.gates@.len()
        && output_values_match(input, values, netlist.outputs@, output)
}

/// 入力数、ゲート順と入力側、出力ポート順で選ぶ最初の違反を定める。
pub open spec fn nor_evaluation_error(
    netlist: &NorNetlist, input: Seq<bool>, error: NorEvaluationError,
) -> bool {
    match error {
        NorEvaluationError::InputCount { expected, actual } =>
            expected == netlist.input_count && actual == input.len() && expected != actual,
        NorEvaluationError::GateInput { gate, input: side } => {
            let gates = netlist.gates@;
            &&& input.len() == netlist.input_count
            &&& gate < gates.len()
            &&& gates_available(gates, input.len(), gate as int)
            &&& match side {
                GateInput::Left => !wire_available(gates[gate as int].left, input.len(), gate as nat),
                GateInput::Right => wire_available(gates[gate as int].left, input.len(), gate as nat)
                    && !wire_available(gates[gate as int].right, input.len(), gate as nat),
            }
        },
        NorEvaluationError::Output { output } => {
            let gates = netlist.gates@;
            let ports = netlist.outputs@;
            &&& input.len() == netlist.input_count
            &&& gates_available(gates, input.len(), gates.len() as int)
            &&& output < ports.len()
            &&& output_ports_available(ports, input.len(), gates.len(), output as int)
            &&& !wire_available(ports[output as int], input.len(), gates.len())
        },
    }
}

/// 評価結果の成功条件、出力列、または最初の配線違反を表す。
pub open spec fn nor_evaluation_result(
    netlist: &NorNetlist, input: Seq<bool>, result: Result<Vec<bool>, NorEvaluationError>,
) -> bool {
    &&& (result.is_ok() <==> nor_evaluation_ready(netlist, input.len()))
    &&& match result {
        Ok(output) => nor_evaluation(netlist, input, output@),
        Err(error) => nor_evaluation_error(netlist, input, error),
    }
}

proof fn gate_value_equation(input: Seq<bool>, gates: Seq<NorGate>, values: Seq<bool>, i: int)
    requires gate_values_match(input, gates, values), 0 <= i < values.len(),
    ensures
        values.len() <= gates.len(),
        wire_available(gates[i].left, input.len(), i as nat),
        wire_available(gates[i].right, input.len(), i as nat),
        values[i] == !(wire_value(gates[i].left, input, values) || wire_value(gates[i].right, input, values)),
{
    reveal(gate_values_match);
}

proof fn gate_value_agrees(
    input: Seq<bool>, gates: Seq<NorGate>, left: Seq<bool>, right: Seq<bool>, i: nat,
)
    requires
        gate_values_match(input, gates, left),
        gate_values_match(input, gates, right),
        i < left.len(),
        i < right.len(),
    ensures left[i as int] == right[i as int],
    decreases i,
{
    gate_value_equation(input, gates, left, i as int);
    gate_value_equation(input, gates, right, i as int);
    let gate = gates[i as int];
    if let Wire::Gate(j) = gate.left {
        gate_value_agrees(input, gates, left, right, j as nat);
    }
    if let Wire::Gate(j) = gate.right {
        gate_value_agrees(input, gates, left, right, j as nat);
    }
}

/// 同じネットリストと入力に対し、ポート順の出力が一意に定まることを示す。
pub proof fn nor_evaluations_agree(netlist: &NorNetlist, input: Seq<bool>, left: Seq<bool>, right: Seq<bool>)
    requires nor_evaluation(netlist, input, left), nor_evaluation(netlist, input, right),
    ensures left == right,
{
    reveal(nor_evaluation);
    let gates = netlist.gates@;
    let ports = netlist.outputs@;
    let a = choose|values: Seq<bool>| #[trigger] gate_values_match(input, gates, values)
        && values.len() == gates.len() && output_values_match(input, values, ports, left);
    let b = choose|values: Seq<bool>| #[trigger] gate_values_match(input, gates, values)
        && values.len() == gates.len() && output_values_match(input, values, ports, right);
    assert(a =~= b) by {
        assert forall|i: int| 0 <= i < gates.len() implies (#[trigger] a[i]) == (#[trigger] b[i]) by {
            gate_value_agrees(input, gates, a, b, i as nat);
        };
    };
    assert(left =~= right);
}

fn read_wire(wire: Wire, input: &[bool], gates: &[bool]) -> (value: Option<bool>)
    ensures
        value.is_some() <==> wire_available(wire, input@.len(), gates@.len()),
        value matches Some(bit) ==> bit == wire_value(wire, input@, gates@),
{
    match wire {
        Wire::Input(index) => if index < input.len() { Some(input[index]) } else { None },
        Wire::Constant(bit) => Some(bit),
        Wire::Gate(index) => if index < gates.len() { Some(gates[index]) } else { None },
    }
}

proof fn push_gate_value(input: Seq<bool>, gates: Seq<NorGate>, previous: Seq<bool>, value: bool)
    requires
        gate_values_match(input, gates, previous),
        previous.len() < gates.len(),
        wire_available(gates[previous.len() as int].left, input.len(), previous.len()),
        wire_available(gates[previous.len() as int].right, input.len(), previous.len()),
        value == !(wire_value(gates[previous.len() as int].left, input, previous)
            || wire_value(gates[previous.len() as int].right, input, previous)),
    ensures gate_values_match(input, gates, previous.push(value)),
{
    reveal(gate_values_match);
    let next = previous.push(value);
    assert forall|i: int| 0 <= i < next.len() implies {
        let gate = gates[i];
        (#[trigger] next[i]) == !(wire_value(gate.left, input, next) || wire_value(gate.right, input, next))
    } by {
        if i < previous.len() {
            assert(next[i] == previous[i]);
        }
        assert(wire_value(gates[i].left, input, previous) == wire_value(gates[i].left, input, next));
        assert(wire_value(gates[i].right, input, previous) == wire_value(gates[i].right, input, next));
    };
}

impl NorNetlist {
    /// 入力をポート順に受け取り、ゲートを順に評価して出力をポート順に返す。
    ///
    /// # Errors
    ///
    /// 入力数が異なれば、その数を返す。その後、ゲートを左入力から検査し、
    /// 最後に出力を検査する。参照先が範囲外または未評価なら、最初の配線違反を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::netlist::{NorGate, NorNetlist, Wire};
    ///
    /// let circuit = NorNetlist {
    ///     input_count: 1,
    ///     gates: vec![NorGate { left: Wire::Input(0), right: Wire::Input(0) }],
    ///     outputs: vec![Wire::Gate(0)],
    /// };
    /// assert_eq!(circuit.evaluate(&[true]), Ok(vec![false]));
    /// ```
    pub fn evaluate(&self, input: &[bool]) -> (result: Result<Vec<bool>, NorEvaluationError>)
        ensures nor_evaluation_result(self, input@, result),
    {
        if input.len() != self.input_count {
            return Err(NorEvaluationError::InputCount { expected: self.input_count, actual: input.len() });
        }

        let mut gate_values = Vec::new();
        assert(gate_values_match(input@, self.gates@, gate_values@)) by { reveal(gate_values_match); };
        let mut i = 0;
        while i < self.gates.len()
            invariant
                input@.len() == self.input_count,
                i <= self.gates@.len(),
                i == gate_values@.len(),
                gate_values_match(input@, self.gates@, gate_values@),
            decreases self.gates@.len() - i,
        {
            let gate = &self.gates[i];
            assert(gates_available(self.gates@, input@.len(), i as int)) by { reveal(gate_values_match); };
            let Some(left) = read_wire(gate.left, input, gate_values.as_slice()) else {
                return Err(NorEvaluationError::GateInput { gate: i, input: GateInput::Left });
            };
            let Some(right) = read_wire(gate.right, input, gate_values.as_slice()) else {
                return Err(NorEvaluationError::GateInput { gate: i, input: GateInput::Right });
            };
            let value = !(left || right);
            proof { push_gate_value(input@, self.gates@, gate_values@, value); }
            gate_values.push(value);
            i += 1;
        }
        assert(gates_available(self.gates@, input@.len(), self.gates@.len() as int)) by {
            reveal(gate_values_match);
        };

        let mut output = Vec::new();
        let mut i = 0;
        while i < self.outputs.len()
            invariant
                input@.len() == self.input_count,
                gate_values@.len() == self.gates@.len(),
                gate_values_match(input@, self.gates@, gate_values@),
                gates_available(self.gates@, input@.len(), gate_values@.len() as int),
                i <= self.outputs@.len(),
                i == output@.len(),
                output_values_match(input@, gate_values@, self.outputs@, output@),
            decreases self.outputs@.len() - i,
        {
            let Some(value) = read_wire(self.outputs[i], input, gate_values.as_slice()) else {
                return Err(NorEvaluationError::Output { output: i });
            };
            let ghost previous = output@;
            output.push(value);
            assert forall|k: int| 0 <= k < output@.len() implies
                wire_available(#[trigger] self.outputs@[k], input@.len(), gate_values@.len()) by {};
            assert forall|k: int| 0 <= k < output@.len() implies
                (#[trigger] output@[k]) == wire_value(self.outputs@[k], input@, gate_values@) by {
                if k < i {
                    assert(output@[k] == previous[k]);
                }
            };
            i += 1;
        }
        assert(nor_evaluation(self, input@, output@)) by { reveal(nor_evaluation); };
        Ok(output)
    }
}

} // verus!
