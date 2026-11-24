//! NOR ゲートの出力を tick ごとに同時更新する。

mod instances;
pub use instances::{ClockedInstanceError, ClockedStatefulInstance, ClockedStatefulInstanceError};
#[cfg(verus_only)]
pub use instances::{clocked_stateful_arguments, clocked_stateful_instance_reads_match, clocked_stateful_instance_result};
#[cfg(verus_only)]
pub use instances::{clocked_instance_inputs, clocked_instance_outputs_match, clocked_instance_result, clocked_instance_steps_match};

use super::{GateInput, NorNetlist, Wire, read_wire};
#[cfg(verus_only)]
use super::{NorGate, nor_evaluation_ready, output_ports_available, output_values_match, wire_available, wire_value};
use alloc::{vec, vec::Vec};
use vstd::prelude::*;

verus! {

/// 全ゲートへの参照を検査済みの、tick 単位で動く NOR 回路。
///
/// ゲート入力は、自身の出力や配列内で後ろに並ぶゲートの出力も参照できる。
/// ゲートから読む値は、いずれも tick 開始時の出力である。
#[derive(Debug)]
pub struct ClockedNor {
    netlist: NorNetlist,
}

/// 回路を組み立てるときに見つかった範囲外の配線参照。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedNorError {
    /// 存在しない入力ビットまたはゲートを、ゲート入力から参照した。
    GateInput {
        /// ゲート列の添字。
        gate: usize,
        /// ゲートの左右いずれかの入力。
        side: GateInput,
    },
    /// 出力ポートが存在しない入力ビットまたはゲートを参照した。
    Output {
        /// 平坦な出力列の添字。
        output: usize,
    },
}

/// 1 tick の入力フレームまたは開始時の状態の長さが回路と一致しない。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TickInputError {
    /// 入力フレームをポート順に平坦化した列の長さが異なる。
    InputCount,
    /// ゲート出力をゲート順に並べた列の長さが異なる。
    GateCount,
}

/// reset または tick 確定直後のゲート状態と公開出力。
#[derive(Debug, Eq, PartialEq)]
pub struct TickFrame {
    /// ゲート列と同じ順の状態。次の tick の開始状態に使う。
    pub gates: Vec<bool>,
    /// ポートの宣言順で、各ポート内は最下位ビットから並ぶ。
    pub outputs: Vec<bool>,
}

spec fn gate_prefix_valid(netlist: &NorNetlist, end: int) -> bool {
    &&& 0 <= end <= netlist.gates@.len()
    &&& forall|i: int| 0 <= i < end ==> {
        let gate = #[trigger] netlist.gates@[i];
        wire_available(gate.left, netlist.input_count as nat, netlist.gates@.len())
            && wire_available(gate.right, netlist.input_count as nat, netlist.gates@.len())
    }
}

/// ゲートからの参照と公開出力が、すべて回路内の配線を指すことを表す。
pub closed spec fn clocked_wiring_valid(netlist: &NorNetlist) -> bool {
    &&& gate_prefix_valid(netlist, netlist.gates@.len() as int)
    &&& output_ports_available(netlist.outputs@, netlist.input_count as nat, netlist.gates@.len(),
        netlist.outputs@.len() as int)
}

/// 各ゲートと出力の参照先が範囲内なら、ネットリスト全体が検査条件を満たす。
pub(crate) proof fn clocked_wiring_from_endpoints(netlist: &NorNetlist)
    requires
        forall|i: int| 0 <= i < netlist.gates@.len() ==> {
            let gate = #[trigger] netlist.gates@[i];
            wire_available(gate.left, netlist.input_count as nat, netlist.gates@.len())
                && wire_available(gate.right, netlist.input_count as nat, netlist.gates@.len())
        },
        output_ports_available(netlist.outputs@, netlist.input_count as nat, netlist.gates@.len(),
            netlist.outputs@.len() as int),
    ensures clocked_wiring_valid(netlist),
{
}

/// 検査を通ったネットリストのゲート入力と公開出力が回路内を指すことを示す。
pub(crate) proof fn clocked_wiring_endpoints(netlist: &NorNetlist)
    requires clocked_wiring_valid(netlist),
    ensures
        forall|i: int| 0 <= i < netlist.gates@.len() ==> {
            let gate = #[trigger] netlist.gates@[i];
            wire_available(gate.left, netlist.input_count as nat, netlist.gates@.len())
                && wire_available(gate.right, netlist.input_count as nat, netlist.gates@.len())
        },
        output_ports_available(netlist.outputs@, netlist.input_count as nat, netlist.gates@.len(),
            netlist.outputs@.len() as int),
{
}

/// ゲート順と入力側、次いで公開出力の順で最初の配線違反を定める。
pub closed spec fn clocked_wiring_error(netlist: &NorNetlist, error: ClockedNorError) -> bool {
    let count = netlist.gates@.len();
    let inputs = netlist.input_count as nat;
    match error {
        ClockedNorError::GateInput { gate, side } => {
            &&& gate < count && gate_prefix_valid(netlist, gate as int)
            &&& match side {
                GateInput::Left => !wire_available(netlist.gates@[gate as int].left, inputs, count),
                GateInput::Right => wire_available(netlist.gates@[gate as int].left, inputs, count)
                    && !wire_available(netlist.gates@[gate as int].right, inputs, count),
            }
        },
        ClockedNorError::Output { output } => {
            &&& gate_prefix_valid(netlist, count as int)
            &&& output < netlist.outputs@.len()
            &&& output_ports_available(netlist.outputs@, inputs, count, output as int)
            &&& !wire_available(netlist.outputs@[output as int], inputs, count)
        },
    }
}

/// 更新済みの接頭部について、各値を同じ tick 開始時の状態から求める。
pub open spec fn clocked_gate_updates(gates: Seq<NorGate>, input: Seq<bool>, previous: Seq<bool>, next: Seq<bool>) -> bool {
    &&& next.len() <= gates.len()
    &&& forall|i: int| 0 <= i < next.len() ==> {
        let gate = gates[i];
        (#[trigger] next[i]) == !(wire_value(gate.left, input, previous) || wire_value(gate.right, input, previous))
    }
}

/// reset では入力とゲート出力をすべて0にし、その状態から公開出力を読む。
pub open spec fn reset_matches(netlist: &NorNetlist, frame: TickFrame) -> bool {
    &&& clocked_wiring_valid(netlist)
    &&& frame.gates@ == Seq::new(netlist.gates@.len(), |i: int| false)
    &&& frame.outputs@.len() == netlist.outputs@.len()
    &&& output_values_match(Seq::new(netlist.input_count as nat, |i: int| false),
        frame.gates@, netlist.outputs@, frame.outputs@)
}

/// 各ゲートは同じ開始状態を読み、公開出力は確定済みの状態とその tick の入力から読む。
pub open spec fn tick_matches(
    netlist: &NorNetlist, previous: Seq<bool>, input: Seq<bool>, frame: TickFrame,
) -> bool {
    &&& clocked_wiring_valid(netlist)
    &&& input.len() == netlist.input_count
    &&& previous.len() == netlist.gates@.len()
    &&& frame.gates@.len() == netlist.gates@.len()
    &&& clocked_gate_updates(netlist.gates@, input, previous, frame.gates@)
    &&& frame.outputs@.len() == netlist.outputs@.len()
    &&& output_values_match(input, frame.gates@, netlist.outputs@, frame.outputs@)
}

/// reset の観測と、各入力フレームを順に適用した後の観測を定める。
pub open spec fn nor_trace(netlist: &NorNetlist, inputs: Seq<Seq<bool>>, frames: Seq<TickFrame>) -> bool {
    &&& frames.len() == inputs.len() + 1
    &&& reset_matches(netlist, frames[0])
    &&& forall|i: int| 0 < i < frames.len() ==>
        tick_matches(netlist, frames[i - 1].gates@, inputs[i - 1], #[trigger] frames[i])
}

/// reset の結果を、入力フレームをまだ適用していない trace として扱えることを示す。
pub proof fn nor_trace_from_reset(netlist: &NorNetlist, frame: TickFrame)
    requires reset_matches(netlist, frame),
    ensures nor_trace(netlist, Seq::empty(), seq![frame]),
{
}

/// 1 tick の結果を追加しても、すべての観測が入力の適用順と対応することを示す。
pub proof fn nor_trace_push_tick(
    netlist: &NorNetlist, inputs: Seq<Seq<bool>>, frames: Seq<TickFrame>, input: Seq<bool>, frame: TickFrame,
)
    requires
        nor_trace(netlist, inputs, frames),
        tick_matches(netlist, frames.last().gates@, input, frame),
    ensures nor_trace(netlist, inputs.push(input), frames.push(frame)),
{
    let next = frames.push(frame);
    let inputs_next = inputs.push(input);
    assert forall|i: int| 0 < i < next.len() implies
        tick_matches(netlist, next[i - 1].gates@, inputs_next[i - 1], #[trigger] next[i]) by {
        assert(next[i - 1] == frames[i - 1]);
        if i < frames.len() {
            assert(next[i] == frames[i]);
            assert(inputs_next[i - 1] == inputs[i - 1]);
            assert(tick_matches(netlist, frames[i - 1].gates@, inputs[i - 1], frames[i]));
        } else {
            assert(next[i] == frame && inputs_next[i - 1] == input);
            assert(frames[i - 1] == frames.last());
        }
    };
}

proof fn frames_agree_at(
    netlist: &NorNetlist, inputs: Seq<Seq<bool>>, left: Seq<TickFrame>, right: Seq<TickFrame>, index: nat,
)
    requires nor_trace(netlist, inputs, left), nor_trace(netlist, inputs, right), index < left.len(),
    ensures left[index as int].gates@ == right[index as int].gates@,
        left[index as int].outputs@ == right[index as int].outputs@,
    decreases index,
{
    let at = index as int;
    if index == 0 {
        assert(reset_matches(netlist, left[0]));
        assert(reset_matches(netlist, right[0]));
    } else {
        frames_agree_at(netlist, inputs, left, right, (index - 1) as nat);
        assert(tick_matches(netlist, left[at - 1].gates@, inputs[at - 1], left[at]));
        assert(tick_matches(netlist, right[at - 1].gates@, inputs[at - 1], right[at]));
        assert(left[at].gates@ =~= right[at].gates@);
    }
    assert(left[at].outputs@ =~= right[at].outputs@);
}

/// 同じ入力列を使った任意の有限 trace で、全 tick の状態と出力が一致することを示す。
pub proof fn nor_traces_agree(netlist: &NorNetlist, inputs: Seq<Seq<bool>>, left: Seq<TickFrame>, right: Seq<TickFrame>)
    requires nor_trace(netlist, inputs, left), nor_trace(netlist, inputs, right),
    ensures forall|i: int| 0 <= i < inputs.len() + 1 ==>
        (#[trigger] left[i]).gates@ == (#[trigger] right[i]).gates@ && left[i].outputs@ == right[i].outputs@,
{
    assert forall|i: int| 0 <= i < inputs.len() + 1 implies
        (#[trigger] left[i]).gates@ == (#[trigger] right[i]).gates@ && left[i].outputs@ == right[i].outputs@ by {
        frames_agree_at(netlist, inputs, left, right, i as nat);
    };
}

pub(crate) fn wire_within(wire: Wire, inputs: usize, gates: usize) -> (valid: bool)
    ensures valid == wire_available(wire, inputs as nat, gates as nat),
{
    match wire {
        Wire::Input(index) => index < inputs,
        Wire::Gate(index) => index < gates,
        Wire::Constant(_) => true,
    }
}

pub(super) fn observe(ports: &[Wire], input: &[bool], gates: &[bool]) -> (output: Vec<bool>)
    requires output_ports_available(ports@, input@.len(), gates@.len(), ports@.len() as int),
    ensures output@.len() == ports@.len(), output_values_match(input@, gates@, ports@, output@),
{
    let mut output = Vec::with_capacity(ports.len());
    let mut i = 0;
    while i < ports.len()
        invariant
            i <= ports@.len(),
            i == output@.len(),
            output_ports_available(ports@, input@.len(), gates@.len(), ports@.len() as int),
            output_values_match(input@, gates@, ports@, output@),
        decreases ports@.len() - i,
    {
        let wire = ports[i];
        let value = read_wire(wire, input, gates).unwrap();
        let ghost prior = output@;
        output.push(value);
        assert forall|j: int| 0 <= j < output@.len() implies
            (#[trigger] output@[j]) == wire_value(ports@[j], input@, gates@) by {
            if j < i {
                assert(output@[j] == prior[j]);
            }
        };
        i += 1;
    }
    output
}

fn observe_reset(ports: &[Wire], Ghost(input_count): Ghost<nat>, Ghost(gates): Ghost<Seq<bool>>) -> (output: Vec<bool>)
    requires
        output_ports_available(ports@, input_count, gates.len(), ports@.len() as int),
        forall|i: int| 0 <= i < gates.len() ==> !(#[trigger] gates[i]),
    ensures output@.len() == ports@.len(),
        output_values_match(Seq::new(input_count, |i: int| false), gates, ports@, output@),
{
    let ghost zero_input = Seq::new(input_count, |i: int| false);
    let mut output = Vec::with_capacity(ports.len());
    let mut i = 0;
    while i < ports.len()
        invariant
            i <= ports@.len(),
            i == output@.len(),
            zero_input == Seq::new(input_count, |i: int| false),
            output_ports_available(ports@, input_count, gates.len(), ports@.len() as int),
            output_values_match(zero_input, gates, ports@, output@),
            forall|j: int| 0 <= j < gates.len() ==> !(#[trigger] gates[j]),
        decreases ports@.len() - i,
    {
        let wire = ports[i];
        let value = match wire {
            Wire::Constant(value) => value,
            Wire::Input(_) | Wire::Gate(_) => false,
        };
        assert(wire_available(wire, zero_input.len(), gates.len()));
        assert(value == wire_value(wire, zero_input, gates));
        let ghost prior = output@;
        output.push(value);
        assert forall|j: int| 0 <= j < output@.len() implies
            (#[trigger] output@[j]) == wire_value(ports@[j], zero_input, gates) by {
            if j < i {
                assert(output@[j] == prior[j]);
            }
        };
        assert(output_ports_available(ports@, zero_input.len(), gates.len(), output@.len() as int));
        i += 1;
    }
    output
}

impl ClockedNor {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        clocked_wiring_valid(&self.netlist)
    }

    /// 子回路の配置に使う検査済みの配線を返す。
    pub(crate) fn checked_netlist(&self) -> (netlist: &NorNetlist)
        ensures *netlist == self.netlist_model(), clocked_wiring_valid(netlist),
    {
        proof { use_type_invariant(self); }
        &self.netlist
    }

    /// 配線の仕様から参照する、検査済みのネットリスト。
    pub closed spec fn netlist_model(&self) -> NorNetlist {
        self.netlist
    }

    /// 組み合わせ評価の配線検査を通った回路を、同じ配線のまま tick 実行に使う。
    pub(crate) fn from_combinational(netlist: NorNetlist) -> (circuit: Self)
        requires nor_evaluation_ready(&netlist, netlist.input_count as nat),
        ensures circuit.netlist_model() == netlist,
    {
        proof {
            assert forall|i: int| 0 <= i < netlist.gates@.len() implies {
                let gate = #[trigger] netlist.gates@[i];
                &&& wire_available(gate.left, netlist.input_count as nat, netlist.gates@.len())
                &&& wire_available(gate.right, netlist.input_count as nat, netlist.gates@.len())
            } by {
                let gate = netlist.gates@[i];
                assert(wire_available(gate.left, netlist.input_count as nat, i as nat));
                assert(wire_available(gate.right, netlist.input_count as nat, i as nat));
            };
            clocked_wiring_from_endpoints(&netlist);
        }
        Self { netlist }
    }

    /// 全ゲートと出力の参照先を検査し、tick 実行用の回路を作る。
    ///
    /// # Errors
    ///
    /// ゲート列を先頭から左右の順に検査し、続いて出力を検査する。
    /// 最初に見つかった範囲外の配線参照を返す。
    pub fn check(netlist: NorNetlist) -> (result: Result<Self, ClockedNorError>)
        ensures
            result.is_ok() <==> clocked_wiring_valid(&netlist),
            result matches Ok(circuit) ==> circuit.netlist_model() == netlist,
            result matches Err(error) ==> clocked_wiring_error(&netlist, error),
    {
        let n = netlist.gates.len();
        let mut i = 0;
        while i < n
            invariant n == netlist.gates@.len(), gate_prefix_valid(&netlist, i as int),
            decreases n - i,
        {
            let gate = netlist.gates[i];
            if !wire_within(gate.left, netlist.input_count, n) {
                return Err(ClockedNorError::GateInput { gate: i, side: GateInput::Left });
            }
            if !wire_within(gate.right, netlist.input_count, n) {
                return Err(ClockedNorError::GateInput { gate: i, side: GateInput::Right });
            }
            i += 1;
        }
        let mut i = 0;
        while i < netlist.outputs.len()
            invariant
                n == netlist.gates@.len(),
                gate_prefix_valid(&netlist, n as int),
                output_ports_available(netlist.outputs@, netlist.input_count as nat, n as nat, i as int),
            decreases netlist.outputs@.len() - i,
        {
            if !wire_within(netlist.outputs[i], netlist.input_count, n) {
                return Err(ClockedNorError::Output { output: i });
            }
            i += 1;
        }
        Ok(Self { netlist })
    }

    /// 全入力とゲート出力を0として、初期状態とその公開出力を返す。
    pub fn reset(&self) -> (frame: TickFrame)
        ensures reset_matches(&self.netlist_model(), frame),
    {
        proof { use_type_invariant(self); }
        let gates = vec![false; self.netlist.gates.len()];
        assert(gates@ =~= Seq::new(self.netlist.gates@.len(), |i: int| false));
        let outputs = observe_reset(self.netlist.outputs.as_slice(), Ghost(self.netlist.input_count as nat), Ghost(gates@));
        TickFrame { gates, outputs }
    }

    /// 開始状態と入力を受け取り、1 tick 後の状態と公開出力を返す。
    ///
    /// # Errors
    ///
    /// 入力フレームの長さが異なる場合はそのエラーを返し、その後で状態の長さを検査する。
    pub fn step(&self, previous: &[bool], input: &[bool]) -> (result: Result<TickFrame, TickInputError>)
        ensures
            match result {
                Ok(frame) => tick_matches(&self.netlist_model(), previous@, input@, frame),
                Err(TickInputError::InputCount) => input@.len() != self.netlist_model().input_count,
                Err(TickInputError::GateCount) => input@.len() == self.netlist_model().input_count
                    && previous@.len() != self.netlist_model().gates@.len(),
            },
    {
        proof { use_type_invariant(self); }
        if input.len() != self.netlist.input_count {
            return Err(TickInputError::InputCount);
        }
        let n = self.netlist.gates.len();
        if previous.len() != n {
            return Err(TickInputError::GateCount);
        }
        let gates = self.next_gates(previous, input);
        let outputs = observe(self.netlist.outputs.as_slice(), input, gates.as_slice());
        Ok(TickFrame { gates, outputs })
    }

    // 混在回路はゲートを更新した後、状態素子の確定出力と合わせて観測する。
    pub(super) fn next_gates(&self, previous: &[bool], input: &[bool]) -> (gates: Vec<bool>)
        requires
            clocked_wiring_valid(&self.netlist_model()),
            input@.len() == self.netlist_model().input_count,
            previous@.len() == self.netlist_model().gates@.len(),
        ensures
            gates@.len() == self.netlist_model().gates@.len(),
            clocked_gate_updates(self.netlist_model().gates@, input@, previous@, gates@),
    {
        let n = self.netlist.gates.len();
        let mut gates = Vec::with_capacity(n);
        let mut i = 0;
        while i < n
            invariant
                n == self.netlist.gates@.len() == previous@.len(),
                input@.len() == self.netlist.input_count,
                clocked_wiring_valid(&self.netlist),
                i == gates@.len(),
                clocked_gate_updates(self.netlist.gates@, input@, previous@, gates@),
            decreases n - i,
        {
            let gate = self.netlist.gates[i];
            let left = read_wire(gate.left, input, previous).unwrap();
            let right = read_wire(gate.right, input, previous).unwrap();
            let ghost prior = gates@;
            gates.push(!(left || right));
            assert forall|j: int| 0 <= j < gates@.len() implies {
                let gate = self.netlist.gates@[j];
                (#[trigger] gates@[j]) == !(wire_value(gate.left, input@, previous@)
                    || wire_value(gate.right, input@, previous@))
            } by {
                if j < i {
                    assert(gates@[j] == prior[j]);
                }
            };
            i += 1;
        }
        gates
    }
}

} // verus!
