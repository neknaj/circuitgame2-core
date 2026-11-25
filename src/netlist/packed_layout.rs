//! 検査済み NOR 回路のポートを、バックエンドで共有する配線番号に変換する。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{ClockedNor, PackedNorGate32, Wire};
#[cfg(verus_only)]
use super::{NorNetlist, clocked_gate_updates, clocked_wiring_endpoints, clocked_wiring_valid, gate_value_matches, nor_lane_bit32, output_ports_available, output_values_match, wire_available, wire_value, wires_fit};

verus! {

/// 外部入力、ゲート状態、定数二つの順に並ぶ配線の配置。
///
/// 各配線のワードは最下位ビットをレーン0とする。偽のワードは 0、真のワードは u32::MAX。
pub struct PackedNorLayout32 {
    input_count: usize,
    source_count: usize,
    gates: Vec<PackedNorGate32>,
    outputs: Vec<usize>,
}

/// 元の配線に対応する共通配列の添字。
pub open spec fn packed_wire_slot(wire: Wire, inputs: nat, gates: nat) -> int {
    match wire {
        Wire::Input(index) => index as int,
        Wire::Gate(index) => inputs + index,
        Wire::Constant(value) => inputs + gates + if value { 1int } else { 0int },
    }
}

/// バックエンドの1レーンの配線列から読む値が、Core の配線値と一致する。
pub proof fn packed_wire_slot_agrees(wire: Wire, inputs: Seq<bool>, gates: Seq<bool>)
    requires wire_available(wire, inputs.len(), gates.len()),
    ensures
        0 <= packed_wire_slot(wire, inputs.len(), gates.len()) < inputs.len() + gates.len() + 2,
        (inputs + gates + seq![false, true])[packed_wire_slot(wire, inputs.len(), gates.len())]
            == wire_value(wire, inputs, gates),
{
    let slot = packed_wire_slot(wire, inputs.len(), gates.len());
    match wire {
        Wire::Input(_) => assert((inputs + gates + seq![false, true])[slot] == inputs[slot]),
        Wire::Gate(_) => assert((inputs + gates + seq![false, true])[slot] == gates[slot - inputs.len()]),
        Wire::Constant(_) => assert((inputs + gates + seq![false, true])[slot]
            == seq![false, true][slot - inputs.len() - gates.len()]),
    }
}

fn slot(wire: Wire, inputs: usize, gates: usize) -> (index: usize)
    requires wire_available(wire, inputs as nat, gates as nat),
        inputs as int + gates as int + 2 <= usize::MAX,
    ensures index as int == packed_wire_slot(wire, inputs as nat, gates as nat),
        index < inputs as int + gates as int + 2,
{
    match wire {
        Wire::Input(index) => index,
        Wire::Gate(index) => inputs + index,
        Wire::Constant(value) => inputs + gates + if value { 1 } else { 0 },
    }
}

impl PackedNorLayout32 {
    /// 検査済み配置と元のネットリストとの対応を表す。
    pub closed spec fn matches(&self, netlist: &NorNetlist) -> bool {
        let inputs = netlist.input_count as nat;
        let count = netlist.gates@.len();
        &&& self.input_model() == inputs
        &&& self.source_model() == inputs + count + 2
        &&& self.gates_model().len() == count
        &&& self.outputs_model().len() == netlist.outputs@.len()
        &&& forall|i: int| 0 <= i < count ==> {
            let gate = netlist.gates@[i];
            let flat = #[trigger] self.gates_model()[i];
            &&& flat.left < self.source_model()
            &&& flat.right < self.source_model()
            &&& flat.left == packed_wire_slot(gate.left, inputs, count)
            &&& flat.right == packed_wire_slot(gate.right, inputs, count)
        }
        &&& forall|i: int| 0 <= i < self.outputs_model().len() ==> {
            let flat = #[trigger] self.outputs_model()[i];
            &&& flat < self.source_model()
            &&& flat == packed_wire_slot(netlist.outputs@[i], inputs, count)
        }
    }

    /// 元のネットリストにある外部入力の数。
    pub closed spec fn input_model(&self) -> nat { self.input_count as nat }
    /// ワードを並べる配列の長さ。
    pub closed spec fn source_model(&self) -> nat { self.source_count as nat }
    /// ゲート順で並べた配線番号。
    pub closed spec fn gates_model(&self) -> Seq<PackedNorGate32> { self.gates@ }
    /// 公開出力の宣言順で並べた配線番号。
    pub closed spec fn outputs_model(&self) -> Seq<usize> { self.outputs@ }

    /// 配列先頭に並べる外部入力の数。
    pub fn input_count(&self) -> (count: usize)
        ensures count == self.input_model(),
    { self.input_count }

    /// 入力・ゲート状態・定数を合わせた配線数。
    pub fn source_count(&self) -> (count: usize)
        ensures count == self.source_model(),
    { self.source_count }

    /// 前の状態からゲートの入力を読む配線番号を、ゲート順に返す。
    pub fn gates(&self) -> (gates: &[PackedNorGate32])
        ensures gates@ == self.gates_model(),
    { self.gates.as_slice() }

    /// 確定後の状態から公開出力を読む配線番号を、宣言順に返す。
    pub fn outputs(&self) -> (outputs: &[usize])
        ensures outputs@ == self.outputs_model(),
    { self.outputs.as_slice() }
}

/// 配線ごとのワードを、一つの実行の配線列に射影する。
pub open spec fn packed_lane32(words: Seq<u32>, lane: u32) -> Seq<bool>
    recommends lane < 32,
{
    Seq::new(words.len(), |i: int| nor_lane_bit32(words[i], lane))
}

/// 配線の配置と32レーンのゲート更新を、Core の同じ tick に結び付ける。
///
/// 更新前後の配列に同じ外部入力と定数が入っていることを前提とする。ゲート更新は更新前の
/// 配列から読み、公開出力は確定後の配列から読み出す。
pub proof fn packed_tick32_agrees(
    netlist: &NorNetlist, layout: &PackedNorLayout32, lane: u32,
    input: Seq<bool>, previous: Seq<bool>, flat_before: Seq<u32>, updated: Seq<u32>,
    flat_after: Seq<u32>, outputs: Seq<u32>,
)
    requires
        lane < 32,
        clocked_wiring_valid(netlist),
        layout.matches(netlist),
        input.len() == netlist.input_count,
        previous.len() == netlist.gates@.len(),
        updated.len() == netlist.gates@.len(),
        outputs.len() == netlist.outputs@.len(),
        flat_after.len() == layout.source_model(),
        packed_lane32(flat_before, lane) == input + previous + seq![false, true],
        packed_lane32(flat_after, lane) == input + packed_lane32(updated, lane) + seq![false, true],
        forall|i: int| 0 <= i < updated.len() ==>
            #[trigger] gate_value_matches(layout.gates_model()[i], flat_before, updated[i]),
        forall|i: int| 0 <= i < outputs.len() ==>
            #[trigger] outputs[i] == flat_after[layout.outputs_model()[i] as int],
    ensures
        clocked_gate_updates(netlist.gates@, input, previous, packed_lane32(updated, lane)),
        output_values_match(input, packed_lane32(updated, lane), netlist.outputs@, packed_lane32(outputs, lane)),
{
    let after = packed_lane32(updated, lane);
    let lanes_before = packed_lane32(flat_before, lane);
    let lanes_after = packed_lane32(flat_after, lane);
    let lanes_out = packed_lane32(outputs, lane);
    assert(after.len() == updated.len() == netlist.gates@.len());
    assert(lanes_before.len() == flat_before.len());
    assert(lanes_after.len() == flat_after.len());
    assert(lanes_out.len() == outputs.len() == netlist.outputs@.len());
    clocked_wiring_endpoints(netlist);
    reveal(PackedNorLayout32::matches);
    assert forall|i: int| 0 <= i < after.len() implies {
        let gate = netlist.gates@[i];
        (#[trigger] after[i]) == !(wire_value(gate.left, input, previous)
            || wire_value(gate.right, input, previous))
    } by {
        let gate = netlist.gates@[i];
        let flat = layout.gates_model()[i];
        packed_wire_slot_agrees(gate.left, input, previous);
        packed_wire_slot_agrees(gate.right, input, previous);
        assert(flat.left as int == packed_wire_slot(gate.left, input.len(), previous.len()));
        assert(flat.right as int == packed_wire_slot(gate.right, input.len(), previous.len()));
        assert(lanes_before[flat.left as int] == wire_value(gate.left, input, previous));
        assert(lanes_before[flat.right as int] == wire_value(gate.right, input, previous));
        assert(lanes_before[flat.left as int] == nor_lane_bit32(flat_before[flat.left as int], lane));
        assert(lanes_before[flat.right as int] == nor_lane_bit32(flat_before[flat.right as int], lane));
        assert(after[i] == nor_lane_bit32(updated[i], lane));
        assert(gate_value_matches(flat, flat_before, updated[i]));
        assert(nor_lane_bit32(updated[i], lane) == !(nor_lane_bit32(flat_before[flat.left as int], lane)
            || nor_lane_bit32(flat_before[flat.right as int], lane)));
    };
    assert forall|i: int| 0 <= i < lanes_out.len() implies
        (#[trigger] lanes_out[i]) == wire_value(netlist.outputs@[i], input, after) by {
        let port = netlist.outputs@[i];
        let slot = layout.outputs_model()[i];
        packed_wire_slot_agrees(port, input, after);
        assert(slot as int == packed_wire_slot(port, input.len(), after.len()));
        assert(outputs[i] == flat_after[slot as int]);
        assert(lanes_out[i] == nor_lane_bit32(outputs[i], lane));
        assert(lanes_after[slot as int] == nor_lane_bit32(flat_after[slot as int], lane));
        assert(lanes_after[slot as int] == wire_value(port, input, after));
    };
}

impl ClockedNor {
    /// GPU やマイコンが共有する配線番号に変換する。
    ///
    /// 外部入力の後にゲートを並べ、末尾の二つは偽・真を表す。
    ///
    /// # Errors
    ///
    /// 配線数を usize で表せない場合は None を返す。GPU で使う添字の幅とデバイスの資源上限は
    /// バックエンド側で検査する。
    pub fn packed_layout32(&self) -> (result: Option<PackedNorLayout32>)
        ensures
            result.is_some() <==>
                (self.netlist_model().input_count as int + self.netlist_model().gates@.len() + 2 <= usize::MAX),
            result matches Some(layout) ==>
                layout.matches(&self.netlist_model())
                && clocked_wiring_valid(&self.netlist_model())
                && wires_fit(layout.gates_model(), layout.source_model() as usize),
    {
        let netlist = self.checked_netlist();
        let inputs = netlist.input_count;
        let count = netlist.gates.len();
        if inputs > usize::MAX - 2 || count > usize::MAX - 2 - inputs {
            return None;
        }
        let source_count = inputs + count + 2;
        let mut gates: Vec<PackedNorGate32> = Vec::with_capacity(count);
        let mut i = 0;
        while i < count
            invariant
                i == gates@.len() <= count == netlist.gates@.len(),
                inputs == netlist.input_count,
                source_count == inputs as int + count as int + 2,
                clocked_wiring_valid(netlist),
                forall|k: int| 0 <= k < i ==> {
                    let gate = netlist.gates@[k];
                    let flat = #[trigger] gates@[k];
                    &&& flat.left < source_count
                    &&& flat.right < source_count
                    &&& flat.left == packed_wire_slot(gate.left, inputs as nat, count as nat)
                    &&& flat.right == packed_wire_slot(gate.right, inputs as nat, count as nat)
                },
            decreases count - i,
        {
            proof { clocked_wiring_endpoints(netlist); }
            let gate = netlist.gates[i];
            let left = slot(gate.left, inputs, count);
            let right = slot(gate.right, inputs, count);
            gates.push(PackedNorGate32 { left, right });
            i += 1;
        }
        proof { clocked_wiring_endpoints(netlist); }
        let ports = netlist.outputs.len();
        let mut outputs: Vec<usize> = Vec::with_capacity(ports);
        let mut i = 0;
        while i < ports
            invariant
                i == outputs@.len() <= ports == netlist.outputs@.len(),
                inputs == netlist.input_count,
                count == netlist.gates@.len(),
                source_count == inputs as int + count as int + 2,
                output_ports_available(netlist.outputs@, inputs as nat, count as nat, ports as int),
                forall|k: int| 0 <= k < i ==> {
                    let flat = #[trigger] outputs@[k];
                    &&& flat < source_count
                    &&& flat == packed_wire_slot(netlist.outputs@[k], inputs as nat, count as nat)
                },
            decreases ports - i,
        {
            outputs.push(slot(netlist.outputs[i], inputs, count));
            i += 1;
        }
        assert(wires_fit(gates@, source_count));
        Some(PackedNorLayout32 { input_count: inputs, source_count, gates, outputs })
    }
}

} // verus!
