//! 同じ NOR 回路を、各配線の64ビットに独立した状態を詰めて実行する。

use alloc::{vec, vec::Vec};
use vstd::prelude::*;

use super::{ClockedNor, TickInputError, Wire};
#[cfg(verus_only)]
use super::{
    NorGate, NorNetlist, TickFrame, clocked_gate_updates, clocked_wiring_endpoints, clocked_wiring_valid,
    nor_trace, output_ports_available, output_values_match, reset_matches, tick_matches, wire_available, wire_value,
};

verus! {

/// 同じ回路の64実行を、配線ごとのワードで表した tick の結果。
///
/// ワードのビット `k` は実行 `k` の値である。`k = 0` は最下位ビットに当たる。
#[derive(Debug, Eq, PartialEq)]
pub struct PackedNorFrame {
    /// ゲート順の状態。次の tick の開始状態に渡す。
    pub gates: Vec<u64>,
    /// ポートの宣言順で、各ポート内は最下位ビットから並ぶ。
    pub outputs: Vec<u64>,
}

/// ワードから指定の実行に対応するビットを取り出す。
pub open spec fn nor_lane_bit(word: u64, lane: u32) -> bool
    recommends lane < 64,
{
    (word >> lane) & 1u64 == 1u64
}

/// 各ワードから同じビットを取り出し、一つの実行の配線列に戻す。
pub open spec fn nor_lane(words: Seq<u64>, lane: u32) -> Seq<bool>
    recommends lane < 64,
{
    Seq::new(words.len(), |i: int| nor_lane_bit(words[i], lane))
}

spec fn wire_word(wire: Wire, input: Seq<u64>, gates: Seq<u64>) -> u64 {
    match wire {
        Wire::Input(index) => input[index as int],
        Wire::Constant(value) => if value { u64::MAX } else { 0 },
        Wire::Gate(index) => gates[index as int],
    }
}

fn read_word(wire: Wire, input: &[u64], gates: &[u64]) -> (word: u64)
    requires wire_available(wire, input@.len(), gates@.len()),
    ensures word == wire_word(wire, input@, gates@),
{
    match wire {
        Wire::Input(index) => input[index],
        Wire::Constant(value) => if value { u64::MAX } else { 0 },
        Wire::Gate(index) => gates[index],
    }
}

proof fn wire_lane(wire: Wire, input: Seq<u64>, gates: Seq<u64>, lane: u32)
    requires lane < 64, wire_available(wire, input.len(), gates.len()),
    ensures nor_lane_bit(wire_word(wire, input, gates), lane)
        == wire_value(wire, nor_lane(input, lane), nor_lane(gates, lane)),
{
    match wire {
        Wire::Input(i) => assert(nor_lane(input, lane)[i as int] == nor_lane_bit(input[i as int], lane)),
        Wire::Gate(i) => assert(nor_lane(gates, lane)[i as int] == nor_lane_bit(gates[i as int], lane)),
        Wire::Constant(value) => {
            assert(lane < 64 ==> ((u64::MAX >> lane) & 1u64 == 1u64)) by (bit_vector);
            assert(lane < 64 ==> ((0u64 >> lane) & 1u64 == 0u64)) by (bit_vector);
        },
    }
}

proof fn nor_lane_commutes(left: u64, right: u64, lane: u32)
    requires lane < 64,
    ensures nor_lane_bit(!(left | right), lane) == !(nor_lane_bit(left, lane) || nor_lane_bit(right, lane)),
{
    assert(lane < 64 ==> (((!(left | right) >> lane) & 1u64 == 1u64)
        == !(((left >> lane) & 1u64 == 1u64) || ((right >> lane) & 1u64 == 1u64)))) by (bit_vector);
}

/// 1レーンに射影した結果が、通常の NOR tick の規則を満たすことを表す。
pub open spec fn packed_nor_step_lane(
    netlist: &NorNetlist, previous: Seq<u64>, input: Seq<u64>, frame: &PackedNorFrame, lane: u32,
) -> bool
    recommends lane < 64,
{
    &&& clocked_gate_updates(netlist.gates@, nor_lane(input, lane), nor_lane(previous, lane), nor_lane(frame.gates@, lane))
    &&& output_values_match(nor_lane(input, lane), nor_lane(frame.gates@, lane), netlist.outputs@, nor_lane(frame.outputs@, lane))
}

/// 64レーンすべてが通常の NOR tick の規則を満たすことを表す。
pub open spec fn packed_nor_step_matches(
    netlist: &NorNetlist, previous: Seq<u64>, input: Seq<u64>, frame: &PackedNorFrame,
) -> bool {
    &&& clocked_wiring_valid(netlist)
    &&& input.len() == netlist.input_count
    &&& previous.len() == netlist.gates@.len()
    &&& frame.gates@.len() == netlist.gates@.len()
    &&& frame.outputs@.len() == netlist.outputs@.len()
    &&& forall|lane: u32| lane < 64 ==> #[trigger] packed_nor_step_lane(netlist, previous, input, frame, lane)
}

/// 個別に実行した tick と、同じ入力と開始状態を持つレーンの結果が一致する。
pub proof fn packed_nor_step_agrees(
    netlist: &NorNetlist, previous: Seq<u64>, input: Seq<u64>,
    packed: &PackedNorFrame, scalar: TickFrame, lane: u32,
)
    requires
        lane < 64,
        packed_nor_step_matches(netlist, previous, input, packed),
        tick_matches(netlist, nor_lane(previous, lane), nor_lane(input, lane), scalar),
    ensures
        nor_lane(packed.gates@, lane) =~= scalar.gates@,
        nor_lane(packed.outputs@, lane) =~= scalar.outputs@,
{
    assert(packed_nor_step_lane(netlist, previous, input, packed, lane));
    assert(nor_lane(packed.gates@, lane) =~= scalar.gates@);
    assert(nor_lane(packed.outputs@, lane) =~= scalar.outputs@);
}

spec fn packed_gates_match(wiring: Seq<NorGate>, previous: Seq<u64>, input: Seq<u64>, next: Seq<u64>) -> bool {
    forall|i: int| 0 <= i < next.len() ==> {
        let gate = wiring[i];
        (#[trigger] next[i]) == !(wire_word(gate.left, input, previous) | wire_word(gate.right, input, previous))
    }
}

spec fn packed_outputs_match(wiring: Seq<Wire>, input: Seq<u64>, gates: Seq<u64>, outputs: Seq<u64>) -> bool {
    forall|i: int| 0 <= i < outputs.len() ==> #[trigger] outputs[i] == wire_word(wiring[i], input, gates)
}

proof fn project_step(netlist: &NorNetlist, previous: Seq<u64>, input: Seq<u64>, frame: &PackedNorFrame)
    requires
        clocked_wiring_valid(netlist),
        input.len() == netlist.input_count,
        previous.len() == netlist.gates@.len(),
        frame.gates@.len() == netlist.gates@.len(),
        frame.outputs@.len() == netlist.outputs@.len(),
        packed_gates_match(netlist.gates@, previous, input, frame.gates@),
        packed_outputs_match(netlist.outputs@, input, frame.gates@, frame.outputs@),
    ensures packed_nor_step_matches(netlist, previous, input, frame),
{
    clocked_wiring_endpoints(netlist);
    assert forall|lane: u32| lane < 64 implies #[trigger] packed_nor_step_lane(netlist, previous, input, frame, lane) by {
        let lanes_in = nor_lane(input, lane);
        let lanes_old = nor_lane(previous, lane);
        let lanes_new = nor_lane(frame.gates@, lane);
        let lanes_out = nor_lane(frame.outputs@, lane);
        assert forall|i: int| 0 <= i < lanes_new.len() implies
            #[trigger] lanes_new[i] == !(wire_value(netlist.gates@[i].left, lanes_in, lanes_old)
                || wire_value(netlist.gates@[i].right, lanes_in, lanes_old)) by {
            let gate = netlist.gates@[i];
            let left = wire_word(gate.left, input, previous);
            let right = wire_word(gate.right, input, previous);
            assert(frame.gates@[i] == !(left | right));
            wire_lane(gate.left, input, previous, lane);
            wire_lane(gate.right, input, previous, lane);
            nor_lane_commutes(left, right, lane);
        };
        assert forall|i: int| 0 <= i < lanes_out.len() implies
            #[trigger] lanes_out[i] == wire_value(netlist.outputs@[i], lanes_in, lanes_new) by {
            let port = netlist.outputs@[i];
            assert(frame.outputs@[i] == wire_word(port, input, frame.gates@));
            wire_lane(port, input, frame.gates@, lane);
        };
    };
}

/// reset 時の入力とゲートを0とし、そこから各レーンの公開出力を定める。
pub closed spec fn packed_nor_reset_matches(netlist: &NorNetlist, frame: &PackedNorFrame) -> bool {
    let zero_input = Seq::new(netlist.input_count as nat, |i: int| 0u64);
    &&& clocked_wiring_valid(netlist)
    &&& frame.gates@ =~= Seq::new(netlist.gates@.len(), |i: int| 0u64)
    &&& frame.outputs@.len() == netlist.outputs@.len()
    &&& packed_outputs_match(netlist.outputs@, zero_input, frame.gates@, frame.outputs@)
}

/// reset 直後の各レーンと、通常の reset の状態・出力が一致する。
pub proof fn packed_nor_reset_agrees(
    netlist: &NorNetlist, packed: &PackedNorFrame, scalar: TickFrame, lane: u32,
)
    requires
        lane < 64,
        packed_nor_reset_matches(netlist, packed),
        reset_matches(netlist, scalar),
    ensures
        nor_lane(packed.gates@, lane) =~= scalar.gates@,
        nor_lane(packed.outputs@, lane) =~= scalar.outputs@,
{
    let zero_input = Seq::new(netlist.input_count as nat, |i: int| 0u64);
    let scalar_input = Seq::new(netlist.input_count as nat, |i: int| false);
    assert(lane < 64 ==> ((0u64 >> lane) & 1u64 == 0u64)) by (bit_vector);
    assert(nor_lane(zero_input, lane) =~= scalar_input);
    assert(nor_lane(packed.gates@, lane) =~= scalar.gates@);
    clocked_wiring_endpoints(netlist);
    assert forall|i: int| 0 <= i < packed.outputs@.len() implies
        nor_lane(packed.outputs@, lane)[i] == scalar.outputs@[i] by {
        let port = netlist.outputs@[i];
        assert(packed.outputs@[i] == wire_word(port, zero_input, packed.gates@));
        wire_lane(port, zero_input, packed.gates@, lane);
    };
    assert(nor_lane(packed.outputs@, lane) =~= scalar.outputs@);
}

/// 全レーンの reset と、入力フレームごとの tick の結果を入力順に記述する。
pub open spec fn packed_nor_trace(netlist: &NorNetlist, inputs: Seq<Seq<u64>>, frames: Seq<PackedNorFrame>) -> bool {
    &&& frames.len() == inputs.len() + 1
    &&& packed_nor_reset_matches(netlist, &frames[0])
    &&& forall|i: int| #![trigger frames[i]] 0 < i < frames.len() ==>
        packed_nor_step_matches(netlist, frames[i - 1].gates@, inputs[i - 1], &frames[i])
}

/// 同じレーンの入力列で通常実行したとき、任意の tick のゲート状態と公開出力が一致する。
pub proof fn packed_nor_trace_agrees_at(
    netlist: &NorNetlist, inputs: Seq<Seq<u64>>, packed: Seq<PackedNorFrame>,
    scalar: Seq<TickFrame>, lane: u32, index: nat,
)
    requires
        lane < 64,
        packed_nor_trace(netlist, inputs, packed),
        nor_trace(netlist, Seq::new(inputs.len(), |i: int| nor_lane(inputs[i], lane)), scalar),
        index < packed.len(),
    ensures
        nor_lane(packed[index as int].gates@, lane) =~= scalar[index as int].gates@,
        nor_lane(packed[index as int].outputs@, lane) =~= scalar[index as int].outputs@,
    decreases index,
{
    let at = index as int;
    if index == 0 {
        packed_nor_reset_agrees(netlist, &packed[0], scalar[0], lane);
    } else {
        packed_nor_trace_agrees_at(netlist, inputs, packed, scalar, lane, (index - 1) as nat);
        let scalar_inputs = Seq::new(inputs.len(), |i: int| nor_lane(inputs[i], lane));
        assert(scalar_inputs[at - 1] == nor_lane(inputs[at - 1], lane));
        assert(packed_nor_step_matches(netlist, packed[at - 1].gates@, inputs[at - 1], &packed[at]));
        assert(tick_matches(netlist, scalar[at - 1].gates@, scalar_inputs[at - 1], scalar[at]));
        packed_nor_step_agrees(netlist, packed[at - 1].gates@, inputs[at - 1], &packed[at], scalar[at], lane);
    }
}

impl ClockedNor {
    /// 全レーンの入力とゲートを0とした初期状態と公開出力を返す。
    pub fn reset_packed(&self) -> (frame: PackedNorFrame)
        ensures
            clocked_wiring_valid(&self.netlist_model()),
            frame.gates@.len() == self.netlist_model().gates@.len(),
            frame.outputs@.len() == self.netlist_model().outputs@.len(),
            packed_nor_reset_matches(&self.netlist_model(), &frame),
    {
        let netlist = self.checked_netlist();
        let gates = vec![0u64; netlist.gates.len()];
        let ports = netlist.outputs.len();
        let ghost zero_input = Seq::new(netlist.input_count as nat, |i: int| 0u64);
        assert(forall|i: int| 0 <= i < zero_input.len() ==> #[trigger] zero_input[i] == 0u64);
        assert(gates@ =~= Seq::new(netlist.gates@.len(), |i: int| 0u64));
        proof { clocked_wiring_endpoints(netlist); }
        let mut outputs = Vec::with_capacity(ports);
        let mut i = 0;
        while i < ports
            invariant
                gates@ =~= Seq::new(netlist.gates@.len(), |i: int| 0u64),
                ports == netlist.outputs@.len(),
                zero_input.len() == netlist.input_count,
                forall|i: int| 0 <= i < zero_input.len() ==> #[trigger] zero_input[i] == 0u64,
                output_ports_available(netlist.outputs@, zero_input.len(), gates@.len(), ports as int),
                i == outputs@.len() <= ports,
                packed_outputs_match(netlist.outputs@, zero_input, gates@, outputs@),
            decreases ports - i,
        {
            let port = netlist.outputs[i];
            let value = match port {
                Wire::Constant(true) => u64::MAX,
                _ => 0,
            };
            proof {
                assert(wire_available(port, zero_input.len(), gates@.len()));
                match port {
                    Wire::Input(index) => {
                        assert(index < zero_input.len());
                        assert(zero_input[index as int] == 0u64);
                    },
                    Wire::Gate(index) => assert(gates@[index as int] == 0),
                    Wire::Constant(_) => {},
                }
                assert(value == wire_word(port, zero_input, gates@));
            }
            outputs.push(value);
            i += 1;
        }
        PackedNorFrame { gates, outputs }
    }

    /// 同じ回路の64実行を、それぞれ1 tick 進める。
    ///
    /// 入力およびゲート状態は配線ごとに1ワードを渡す。
    /// ゲートは全レーンで同じ配線を使い、それぞれの開始状態を読む。
    ///
    /// # Examples
    ///
    /// 入力がレーン0だけで1なら、その入力を反転した出力はレーン0だけで0になる。
    ///
    /// ```
    /// use circuitgame2_core::netlist::{ClockedNor, NorGate, NorNetlist, Wire};
    ///
    /// let circuit = ClockedNor::check(NorNetlist {
    ///     input_count: 1,
    ///     gates: vec![NorGate { left: Wire::Input(0), right: Wire::Input(0) }],
    ///     outputs: vec![Wire::Gate(0)],
    /// }).unwrap();
    /// let initial = circuit.reset_packed();
    /// let frame = circuit.step_packed(&initial.gates, &[1]).unwrap();
    /// assert_eq!(frame.outputs, [!1u64]);
    /// ```
    ///
    /// # Errors
    ///
    /// 入力のワード数を先に検査し、続いてゲート状態のワード数を検査する。
    pub fn step_packed(&self, previous: &[u64], input: &[u64]) -> (result: Result<PackedNorFrame, TickInputError>)
        ensures
            match result {
                Ok(frame) => packed_nor_step_matches(&self.netlist_model(), previous@, input@, &frame),
                Err(TickInputError::InputCount) => input@.len() != self.netlist_model().input_count,
                Err(TickInputError::GateCount) => input@.len() == self.netlist_model().input_count
                    && previous@.len() != self.netlist_model().gates@.len(),
            },
    {
        let netlist = self.checked_netlist();
        if input.len() != netlist.input_count {
            return Err(TickInputError::InputCount);
        }
        let count = netlist.gates.len();
        if previous.len() != count {
            return Err(TickInputError::GateCount);
        }
        proof { clocked_wiring_endpoints(netlist); }
        let mut gates = Vec::with_capacity(count);
        let mut i = 0;
        while i < count
            invariant
                count == netlist.gates@.len() == previous@.len(),
                input@.len() == netlist.input_count,
                clocked_wiring_valid(netlist),
                i == gates@.len() <= count,
                packed_gates_match(netlist.gates@, previous@, input@, gates@),
            decreases count - i,
        {
            proof { clocked_wiring_endpoints(netlist); }
            let gate = netlist.gates[i];
            let left = read_word(gate.left, input, previous);
            let right = read_word(gate.right, input, previous);
            gates.push(!(left | right));
            i += 1;
        }
        let ports = netlist.outputs.len();
        let mut outputs = Vec::with_capacity(ports);
        let mut i = 0;
        while i < ports
            invariant
                gates@.len() == netlist.gates@.len(),
                input@.len() == netlist.input_count,
                ports == netlist.outputs@.len(),
                output_ports_available(netlist.outputs@, input@.len(), gates@.len(), ports as int),
                i == outputs@.len() <= ports,
                packed_outputs_match(netlist.outputs@, input@, gates@, outputs@),
            decreases ports - i,
        {
            outputs.push(read_word(netlist.outputs[i], input, gates.as_slice()));
            i += 1;
        }
        let frame = PackedNorFrame { gates, outputs };
        proof { project_step(netlist, previous@, input@, &frame); }
        Ok(frame)
    }
}

} // verus!
