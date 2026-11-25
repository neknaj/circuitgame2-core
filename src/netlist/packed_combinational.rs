//! 組み合わせ NOR の参照順を検査し、GPU と共有できる配線番号に変換する。

#[cfg(verus_only)]
use super::clocked::clocked_wiring_from_endpoints;
use super::packed_layout::PackedNorLayout32;
#[cfg(verus_only)]
use super::packed_layout::{packed_lane32, packed_wire_slot, packed_wire_slot_agrees};
use super::{GateInput, NorEvaluationError, NorNetlist, Wire};
#[cfg(verus_only)]
use super::{
    gate_values_match, gates_available,
    nor_evaluation, nor_evaluation_error, nor_evaluation_ready, output_ports_available,
    output_values_match, wire_available, wire_value,
};
#[cfg(verus_only)]
use circuitgame2_packed_nor::{gate_value_matches, nor_lane_bit32};
use vstd::prelude::*;

verus! {

/// 組み合わせ評価用の配線配置を作れなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackedCombinationalError {
    /// 通常の組み合わせ評価で最初に検出する配線違反。
    Wiring(NorEvaluationError),
    /// 配線数を usize で表せない。
    SourceCount,
}

/// 各ゲートの参照先が依存順に現れることを検査した配置。
pub struct PackedCombinationalLayout32 {
    layout: PackedNorLayout32,
}

/// 配線のうち、当該ゲートより前の入力・ゲート、または末尾の定数を指す添字。
pub open spec fn before_gate32(slot: usize, inputs: nat, gates: nat, gate: int) -> bool {
    slot < inputs + gate || inputs + gates <= slot < inputs + gates + 2
}

/// 配線配置のすべてのゲートが、計算済みの配線だけを読むことを表す。
pub open spec fn combinational_read_order32(layout: &PackedNorLayout32) -> bool {
    let gates = layout.gates_model();
    forall|i: int| 0 <= i < gates.len() ==> {
        let gate = #[trigger] gates[i];
        before_gate32(gate.left, layout.input_model(), gates.len(), i)
            && before_gate32(gate.right, layout.input_model(), gates.len(), i)
    }
}

impl PackedCombinationalLayout32 {
    /// 共有配線番号の配置を表す。
    pub closed spec fn layout_model(&self) -> PackedNorLayout32 { self.layout }

    /// 元のネットリストの配線、ゲート順、公開出力順との対応を表す。
    pub open spec fn matches(&self, netlist: &NorNetlist) -> bool {
        &&& self.layout_model().matches(netlist)
        &&& nor_evaluation_ready(netlist, netlist.input_count as nat)
    }

    #[verifier::type_invariant]
    spec fn read_order(&self) -> bool {
        combinational_read_order32(&self.layout)
    }

    /// 検査済みの配線番号を返す。各ゲートは先行ゲート、入力、定数だけを参照する。
    pub fn layout(&self) -> (result: &PackedNorLayout32)
        ensures
            *result == self.layout_model(),
            combinational_read_order32(result),
    {
        proof { use_type_invariant(self); }
        &self.layout
    }
}

fn available(wire: Wire, inputs: usize, gates: usize) -> (valid: bool)
    ensures valid == wire_available(wire, inputs as nat, gates as nat),
{
    match wire {
        Wire::Input(index) => index < inputs,
        Wire::Constant(_) => true,
        Wire::Gate(index) => index < gates,
    }
}

fn validate(netlist: &NorNetlist) -> (result: Result<(), NorEvaluationError>)
    ensures
        result.is_ok() <==> nor_evaluation_ready(netlist, netlist.input_count as nat),
        result matches Err(error) ==> nor_evaluation_error(
            netlist, Seq::new(netlist.input_count as nat, |_: int| false), error),
{
    let inputs = netlist.input_count;
    let mut i = 0;
    while i < netlist.gates.len()
        invariant gates_available(netlist.gates@, inputs as nat, i as int), inputs == netlist.input_count,
        decreases netlist.gates.len() - i,
    {
        let gate = netlist.gates[i];
        if !available(gate.left, inputs, i) {
            return Err(NorEvaluationError::GateInput { gate: i, input: GateInput::Left });
        }
        if !available(gate.right, inputs, i) {
            return Err(NorEvaluationError::GateInput { gate: i, input: GateInput::Right });
        }
        assert(gates_available(netlist.gates@, inputs as nat, i as int + 1));
        i += 1;
    }
    let gates = i;
    let mut port = 0;
    while port < netlist.outputs.len()
        invariant
            inputs == netlist.input_count, gates == netlist.gates@.len(),
            gates_available(netlist.gates@, inputs as nat, gates as int),
            output_ports_available(netlist.outputs@, inputs as nat, gates as nat, port as int),
        decreases netlist.outputs.len() - port,
    {
        if !available(netlist.outputs[port], inputs, gates) {
            return Err(NorEvaluationError::Output { output: port });
        }
        assert(output_ports_available(netlist.outputs@, inputs as nat, gates as nat, port as int + 1));
        port += 1;
    }
    Ok(())
}

impl NorNetlist {
    /// 参照順を検査し、組み合わせ用の32レーン配線配置に変換する。
    ///
    /// # Errors
    ///
    /// 通常の組み合わせ評価と同じ最初の配線違反を返す。配線に違反がなく、
    /// 入力・ゲート・定数を合わせた配線数を usize で表せない場合は SourceCount を返す。
    pub fn packed_combinational_layout32(&self) -> (result: Result<PackedCombinationalLayout32, PackedCombinationalError>)
        ensures
            result.is_ok() <==> nor_evaluation_ready(self, self.input_count as nat)
                && self.input_count as int + self.gates@.len() + 2 <= usize::MAX,
            result matches Ok(layout) ==> layout.matches(self),
            result matches Err(PackedCombinationalError::Wiring(error)) ==> nor_evaluation_error(
                self, Seq::new(self.input_count as nat, |_: int| false), error),
            result == Err(PackedCombinationalError::SourceCount) ==> nor_evaluation_ready(self, self.input_count as nat)
                && self.input_count as int + self.gates@.len() + 2 > usize::MAX,
    {
        if let Err(error) = validate(self) {
            return Err(PackedCombinationalError::Wiring(error));
        }
        proof {
            assert forall|i: int| 0 <= i < self.gates@.len() implies {
                let gate = #[trigger] self.gates@[i];
                wire_available(gate.left, self.input_count as nat, self.gates@.len())
                    && wire_available(gate.right, self.input_count as nat, self.gates@.len())
            } by {};
            clocked_wiring_from_endpoints(self);
        }
        let Some(layout) = PackedNorLayout32::from_valid_wiring(self) else {
            return Err(PackedCombinationalError::SourceCount);
        };
        proof { layout.combinational_read_order(self); }
        Ok(PackedCombinationalLayout32 { layout })
    }
}

/// 配線ごとに各ワードを連続して並べた GPU バッファーの添字。
pub open spec fn packed_word_offset32(slot: int, words: int, word: int) -> int {
    slot * words + word
}

/// GPU が異なるワードを評価するとき、配線バッファー内の添字は重ならない。
///
/// ホストが配線数とワード数の積を u32 の範囲内に制限すると、WGSL の添字計算は
/// 乗算と加算の途中も同じ範囲に収まる。
pub proof fn packed_word_offsets32_disjoint(
    slots: int, words: int, first_slot: int, first_word: int, second_slot: int, second_word: int,
)
    requires
        0 < words,
        0 <= first_slot < slots, 0 <= second_slot < slots,
        0 <= first_word < words, 0 <= second_word < words,
        first_word != second_word,
        slots * words <= u32::MAX,
    ensures
        0 <= first_slot * words <= packed_word_offset32(first_slot, words, first_word) < slots * words,
        0 <= second_slot * words <= packed_word_offset32(second_slot, words, second_word) < slots * words,
        packed_word_offset32(first_slot, words, first_word)
            != packed_word_offset32(second_slot, words, second_word),
{
    let first = packed_word_offset32(first_slot, words, first_word);
    let second = packed_word_offset32(second_slot, words, second_word);
    assert(0 <= first_slot * words <= first < slots * words) by (nonlinear_arith)
        requires 0 < words, 0 <= first_slot < slots, 0 <= first_word < words,
            first == first_slot * words + first_word;
    assert(0 <= second_slot * words <= second < slots * words) by (nonlinear_arith)
        requires 0 < words, 0 <= second_slot < slots, 0 <= second_word < words,
            second == second_slot * words + second_word;
    if first_slot < second_slot {
        assert(first < second) by (nonlinear_arith)
            requires 0 <= first_word < words, 0 <= second_word < words,
                first_slot < second_slot, first == first_slot * words + first_word,
                second == second_slot * words + second_word;
    } else if second_slot < first_slot {
        assert(second < first) by (nonlinear_arith)
            requires 0 <= first_word < words, 0 <= second_word < words,
                second_slot < first_slot, first == first_slot * words + first_word,
                second == second_slot * words + second_word;
    }
}

/// 共有配線で評価した1レーンの公開出力が、組み合わせ NOR の参照意味論に一致する。
///
/// 一つのレーンワードに入力を配置どおりに格納し、各ゲートを NOR で評価してから
/// 公開出力を配線表の順に読み出すことを前提とする。
pub proof fn packed_combinational32_agrees(
    netlist: &NorNetlist, checked: &PackedCombinationalLayout32, lane: u32,
    input: Seq<bool>, gates: Seq<u32>, flat: Seq<u32>, output: Seq<u32>,
)
    requires
        lane < 32, checked.matches(netlist), input.len() == netlist.input_count,
        gates.len() == netlist.gates@.len(), output.len() == netlist.outputs@.len(),
        packed_lane32(flat, lane) == input + packed_lane32(gates, lane) + seq![false, true],
        forall|i: int| 0 <= i < gates.len() ==>
            #[trigger] gate_value_matches(checked.layout_model().gates_model()[i], flat, gates[i]),
        forall|i: int| 0 <= i < output.len() ==>
            #[trigger] output[i] == flat[checked.layout_model().outputs_model()[i] as int],
    ensures nor_evaluation(netlist, input, packed_lane32(output, lane)),
{
    let layout = checked.layout_model();
    let values = packed_lane32(gates, lane);
    let published = packed_lane32(output, lane);
    let lanes = packed_lane32(flat, lane);
    layout.port_slots(netlist);
    assert(lanes.len() == flat.len());
    assert(published.len() == output.len() == netlist.outputs@.len());
    assert(values.len() == gates.len() == netlist.gates@.len());
    assert(layout.input_model() == input.len() && layout.gates_model().len() == values.len());
    assert forall|i: int| 0 <= i < values.len() implies #[trigger] values[i]
        == !(wire_value(netlist.gates@[i].left, input, values)
            || wire_value(netlist.gates@[i].right, input, values)) by {
        let gate = netlist.gates@[i];
        let route = layout.gates_model()[i];
        layout.gate_route(netlist, i);
        packed_wire_slot_agrees(gate.left, input, values);
        packed_wire_slot_agrees(gate.right, input, values);
        assert(route.left as int == packed_wire_slot(gate.left, input.len(), values.len()));
        assert(route.right as int == packed_wire_slot(gate.right, input.len(), values.len()));
        assert(lanes[route.left as int] == wire_value(gate.left, input, values));
        assert(lanes[route.right as int] == wire_value(gate.right, input, values));
        assert(lanes[route.left as int] == nor_lane_bit32(flat[route.left as int], lane));
        assert(lanes[route.right as int] == nor_lane_bit32(flat[route.right as int], lane));
        assert(gate_value_matches(route, flat, gates[i]));
        assert(values[i] == nor_lane_bit32(gates[i], lane));
        assert(nor_lane_bit32(gates[i], lane)
            == !(nor_lane_bit32(flat[route.left as int], lane)
                || nor_lane_bit32(flat[route.right as int], lane)));
    };
    assert(gate_values_match(input, netlist.gates@, values)) by { reveal(gate_values_match); };
    assert forall|i: int| 0 <= i < published.len() implies
        #[trigger] published[i] == wire_value(netlist.outputs@[i], input, values) by {
        packed_wire_slot_agrees(netlist.outputs@[i], input, values);
        let address = layout.outputs_model()[i];
        assert(output[i] == flat[address as int]);
        assert(address as int == packed_wire_slot(netlist.outputs@[i], input.len(), values.len()));
        assert(lanes[address as int] == wire_value(netlist.outputs@[i], input, values));
        assert(lanes[address as int] == nor_lane_bit32(flat[address as int], lane));
        assert(published[i] == nor_lane_bit32(output[i], lane));
    };
    assert(output_values_match(input, values, netlist.outputs@, published));
    reveal(nor_evaluation);
}

} // verus!
