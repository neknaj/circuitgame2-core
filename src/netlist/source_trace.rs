//! ソース上のゲートをインスタンス経路で識別する tick の参照意味論。

use super::{NorNetlist, TickFrame, Wire, clocked_wiring_valid, nor_trace, reset_matches, tick_matches, wire_available, wire_value};
use crate::project::DefinitionPosition;
use vstd::prelude::*;

verus! {

/// ソースのゲート位置と、その位置に至る回路呼び出しの列。
pub struct SourceGateId {
    /// 外側のモジュールから順にたどった呼び出し。直下のゲートなら空。
    pub instance: Seq<DefinitionPosition>,
    /// そのインスタンス内にある基底 NOR の呼び出し。
    pub gate: DefinitionPosition,
}

/// 配線元を、入力のビット位置またはソースのゲートの識別子で表す。
pub enum SourceWire {
    /// 宣言順に平坦化した入力のビット位置。
    Input(usize),
    /// 回路の状態に依存しない定数。
    Constant(bool),
    /// ソース上のインスタンスに属するゲートの出力。
    Gate(SourceGateId),
}

/// ソース回路の一つの基底 NOR と、その二つの配線元。
pub struct SourceNor {
    /// 左入力の配線元。
    pub left: SourceWire,
    /// 右入力の配線元。
    pub right: SourceWire,
}

/// 型と配線を解決したソース回路の tick 意味論に使う構造。
pub struct SourceTickCircuit {
    /// 入力ポートが占めるビットの合計。
    pub input_count: usize,
    /// 各ソース位置とインスタンスに対応する基底ゲート。
    pub gates: Map<SourceGateId, SourceNor>,
    /// 宣言順かつ各ポート内は下位ビット順の公開出力。
    pub outputs: Seq<SourceWire>,
}

/// ソース上の全ゲートの状態と、公開ポートの観測値。
pub struct SourceTickFrame {
    /// インスタンスとソース位置で引くゲート出力。
    pub gates: Map<SourceGateId, bool>,
    /// 宣言順かつ各ポート内は下位ビット順の公開出力。
    pub outputs: Seq<bool>,
}

spec fn source_wire_valid(source: &SourceTickCircuit, wire: SourceWire) -> bool {
    match wire {
        SourceWire::Input(i) => i < source.input_count,
        SourceWire::Constant(_) => true,
        SourceWire::Gate(site) => source.gates.dom().contains(site),
    }
}

spec fn source_wire_value(wire: SourceWire, input: Seq<bool>, gates: Map<SourceGateId, bool>) -> bool {
    match wire {
        SourceWire::Input(i) => input[i as int],
        SourceWire::Constant(bit) => bit,
        SourceWire::Gate(site) => gates[site],
    }
}

/// ソースの各ゲート入力と公開出力が、入力ビット、定数、または存在するゲートを参照する。
pub closed spec fn source_wiring_valid(source: &SourceTickCircuit) -> bool {
    &&& forall|site: SourceGateId| source.gates.dom().contains(site) ==> {
        let gate = #[trigger] source.gates[site];
        source_wire_valid(source, gate.left) && source_wire_valid(source, gate.right)
    }
    &&& forall|i: int| 0 <= i < source.outputs.len() ==> source_wire_valid(source, #[trigger] source.outputs[i])
}

spec fn source_outputs_match(source: &SourceTickCircuit, input: Seq<bool>, frame: SourceTickFrame) -> bool {
    &&& frame.outputs.len() == source.outputs.len()
    &&& forall|i: int| 0 <= i < frame.outputs.len() ==> {
        let wire = source.outputs[i];
        source_wire_valid(source, wire) && (#[trigger] frame.outputs[i]) == source_wire_value(wire, input, frame.gates)
    }
}

/// reset では全ゲートと入力を0とし、定数を含む公開出力を読む。
pub closed spec fn source_reset_matches(source: &SourceTickCircuit, frame: SourceTickFrame) -> bool {
    &&& source_wiring_valid(source)
    &&& frame.gates.dom() == source.gates.dom()
    &&& forall|site: SourceGateId| source.gates.dom().contains(site) ==> !(#[trigger] frame.gates[site])
    &&& source_outputs_match(source, Seq::new(source.input_count as nat, |_: int| false), frame)
}

/// ゲートの更新には共通の開始状態を使い、公開出力は確定後の状態から読む。
pub closed spec fn source_step_matches(
    source: &SourceTickCircuit, previous: Map<SourceGateId, bool>, input: Seq<bool>, frame: SourceTickFrame,
) -> bool {
    &&& source_wiring_valid(source)
    &&& input.len() == source.input_count
    &&& previous.dom() == source.gates.dom()
    &&& frame.gates.dom() == source.gates.dom()
    &&& forall|site: SourceGateId| source.gates.dom().contains(site) ==> {
        let gate = source.gates[site];
        &&& source_wire_valid(source, gate.left) && source_wire_valid(source, gate.right)
        &&& (#[trigger] frame.gates[site]) == !(source_wire_value(gate.left, input, previous)
            || source_wire_value(gate.right, input, previous))
    }
    &&& source_outputs_match(source, input, frame)
}

/// ソース回路を reset し、任意の有限入力列を順に適用したときの状態と観測を表す。
pub open spec fn source_tick_trace(
    source: &SourceTickCircuit, inputs: Seq<Seq<bool>>, frames: Seq<SourceTickFrame>,
) -> bool {
    &&& frames.len() == inputs.len() + 1
    &&& source_reset_matches(source, frames[0])
    &&& forall|i: int| 0 < i < frames.len() ==>
        source_step_matches(source, frames[i - 1].gates, inputs[i - 1], #[trigger] frames[i])
}

pub(crate) open spec fn source_wire_pair(order: Seq<SourceGateId>, original: SourceWire, lowered: Wire) -> bool {
    match (original, lowered) {
        (SourceWire::Input(i), Wire::Input(j)) => i == j,
        (SourceWire::Constant(a), Wire::Constant(b)) => a == b,
        (SourceWire::Gate(site), Wire::Gate(i)) => i < order.len() && order[i as int] == site,
        _ => false,
    }
}

spec fn endpoints_agree(source: &SourceTickCircuit, order: Seq<SourceGateId>, original: SourceWire, lowered: Wire) -> bool {
    source_wire_valid(source, original) && source_wire_pair(order, original, lowered)
}

pub(crate) open spec fn source_output_pair_at(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, i: int,
) -> bool {
    wire_available(netlist.outputs@[i], netlist.input_count as nat, order.len())
        && source_wire_pair(order, source.outputs[i], netlist.outputs@[i])
}

pub(crate) open spec fn source_output_pairs(source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>) -> bool {
    &&& source.outputs.len() == netlist.outputs@.len()
    &&& forall|i: int| 0 <= i < source.outputs.len() ==>
        #[trigger] source_output_pair_at(source, netlist, order, i)
}

/// ゲート番号とソース上の識別子の全単射、および全配線と公開出力の対応を表す。
pub closed spec fn source_clocked_layout(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
) -> bool {
    &&& source.input_count == netlist.input_count
    &&& order.len() == netlist.gates@.len()
    &&& index.dom() == source.gates.dom()
    &&& forall|site: SourceGateId| index.dom().contains(site) ==> {
        let i = #[trigger] index[site];
        0 <= i < order.len() && order[i] == site
    }
    &&& forall|i: int| 0 <= i < order.len() ==> {
        let site = #[trigger] order[i];
        let lowered = netlist.gates@[i];
        let original = source.gates[site];
        &&& index.dom().contains(site) && index[site] == i
        &&& endpoints_agree(source, order, original.left, lowered.left)
        &&& endpoints_agree(source, order, original.right, lowered.right)
    }
    &&& source.outputs.len() == netlist.outputs@.len()
    &&& forall|i: int| 0 <= i < source.outputs.len() ==>
        endpoints_agree(source, order, #[trigger] source.outputs[i], netlist.outputs@[i])
}

/// 指定したゲートの左右の入力が、ソースとネットリストで対応する配線を指すことを示す。
pub(crate) proof fn source_gate_wiring_pair(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>, gate: int,
)
    requires source_clocked_layout(source, netlist, order, index), 0 <= gate < order.len(),
    ensures
        order.len() == netlist.gates@.len(),
        source.gates.dom().contains(order[gate]),
        source_wire_pair(order, source.gates[order[gate]].left, netlist.gates@[gate].left),
        source_wire_pair(order, source.gates[order[gate]].right, netlist.gates@[gate].right),
        wire_available(netlist.gates@[gate].left, netlist.input_count as nat, order.len()),
        wire_available(netlist.gates@[gate].right, netlist.input_count as nat, order.len()),
{
}

/// ゲート番号の対応が一対一であることを示す。
pub(crate) proof fn source_gate_positions_distinct(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>, a: int, b: int,
)
    requires source_clocked_layout(source, netlist, order, index), 0 <= a < b < order.len(),
    ensures order[a] != order[b],
{
    assert(index[order[a]] == a && index[order[b]] == b);
}

/// 対応表の入出力数とゲート列の長さがネットリストと一致することを示す。
pub(crate) proof fn source_trace_layout_counts(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
)
    requires source_clocked_layout(source, netlist, order, index),
    ensures source.input_count == netlist.input_count, order.len() == netlist.gates@.len(),
        source.outputs.len() == netlist.outputs@.len(),
{
}

/// ソース上の識別子を、対応するゲート番号に結び付ける。
pub(crate) proof fn source_trace_gate_index(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
    site: SourceGateId,
)
    requires source_clocked_layout(source, netlist, order, index), source.gates.dom().contains(site),
    ensures index.dom().contains(site), 0 <= index[site] < order.len(), order[index[site]] == site,
{
}

/// 指定した公開出力が、ソースとネットリストで対応する配線を指すことを示す。
pub(crate) proof fn source_output_wiring_pair(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>, port: int,
)
    requires source_clocked_layout(source, netlist, order, index), 0 <= port < netlist.outputs@.len(),
    ensures port < source.outputs.len(), source_output_pair_at(source, netlist, order, port),
{
    let original = source.outputs[port];
    let lowered = netlist.outputs@[port];
    assert(endpoints_agree(source, order, original, lowered));
    assert(wire_available(lowered, netlist.input_count as nat, order.len()));
}

/// 対応する配線の範囲とゲート番号の逆引きから、展開の対応を組み立てる。
pub(crate) proof fn source_clocked_layout_from_pairs(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
)
    requires
        source.input_count == netlist.input_count, order.len() == netlist.gates@.len(),
        index.dom() == source.gates.dom(),
        forall|site: SourceGateId| index.dom().contains(site) ==> 0 <= #[trigger] index[site] < order.len()
            && order[index[site]] == site,
        forall|i: int| 0 <= i < order.len() ==> {
            let site = #[trigger] order[i];
            let gate = netlist.gates@[i];
            &&& index.dom().contains(site) && index[site] == i
            &&& wire_available(gate.left, netlist.input_count as nat, order.len())
            &&& wire_available(gate.right, netlist.input_count as nat, order.len())
            &&& source_wire_pair(order, source.gates[site].left, gate.left)
            &&& source_wire_pair(order, source.gates[site].right, gate.right)
        },
        source_output_pairs(source, netlist, order),
    ensures source_clocked_layout(source, netlist, order, index),
{
    assert forall|i: int| 0 <= i < order.len() implies {
        let site = #[trigger] order[i];
        let gate = netlist.gates@[i];
        endpoints_agree(source, order, source.gates[site].left, gate.left)
            && endpoints_agree(source, order, source.gates[site].right, gate.right)
    } by {};
    assert forall|i: int| 0 <= i < source.outputs.len() implies
        endpoints_agree(source, order, #[trigger] source.outputs[i], netlist.outputs@[i]) by {
        assert(source_output_pair_at(source, netlist, order, i));
    };
}

/// ゲートと配線の対応から、ソースとネットリスト双方の配線の妥当性を導く。
pub proof fn source_clocked_layout_valid(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
)
    requires source_clocked_layout(source, netlist, order, index),
    ensures source_wiring_valid(source), clocked_wiring_valid(netlist),
{
    assert forall|site: SourceGateId| source.gates.dom().contains(site) implies
        source_wire_valid(source, (#[trigger] source.gates[site]).left)
            && source_wire_valid(source, source.gates[site].right) by {
        let i = index[site];
        assert(0 <= i < order.len() && order[i] == site);
    };
    assert forall|i: int| 0 <= i < netlist.gates@.len() implies {
        let gate = #[trigger] netlist.gates@[i];
        wire_available(gate.left, netlist.input_count as nat, order.len())
            && wire_available(gate.right, netlist.input_count as nat, order.len())
    } by {
        let gate = source.gates[order[i]];
        assert(endpoints_agree(source, order, gate.left, netlist.gates@[i].left));
        assert(endpoints_agree(source, order, gate.right, netlist.gates@[i].right));
    };
    assert forall|i: int| 0 <= i < netlist.outputs@.len() implies
        wire_available(#[trigger] netlist.outputs@[i], netlist.input_count as nat, order.len()) by {
        assert(endpoints_agree(source, order, source.outputs[i], netlist.outputs@[i]));
    };
    super::clocked::clocked_wiring_from_endpoints(netlist);
}

spec fn state_from_flat(index: Map<SourceGateId, int>, gates: Seq<bool>) -> Map<SourceGateId, bool> {
    Map::new(index.dom(), |site: SourceGateId| gates[index[site]])
}

spec fn frame_from_flat(index: Map<SourceGateId, int>, frame: TickFrame) -> SourceTickFrame {
    SourceTickFrame { gates: state_from_flat(index, frame.gates@), outputs: frame.outputs@ }
}

proof fn endpoint_value(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
    original: SourceWire, lowered: Wire, input: Seq<bool>, gates: Seq<bool>,
)
    requires
        source_clocked_layout(source, netlist, order, index),
        endpoints_agree(source, order, original, lowered),
        input.len() == netlist.input_count, gates.len() == order.len(),
    ensures source_wire_value(original, input, state_from_flat(index, gates)) == wire_value(lowered, input, gates),
{
    if let Wire::Gate(i) = lowered {
        assert(index[order[i as int]] == i);
    }
}

proof fn observe_source(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
    input: Seq<bool>, frame: TickFrame,
)
    requires
        source_clocked_layout(source, netlist, order, index),
        input.len() == netlist.input_count, frame.gates@.len() == order.len(),
        frame.outputs@.len() == netlist.outputs@.len(),
        super::output_values_match(input, frame.gates@, netlist.outputs@, frame.outputs@),
    ensures source_outputs_match(source, input, frame_from_flat(index, frame)),
{
    let projected = frame_from_flat(index, frame);
    assert forall|i: int| 0 <= i < projected.outputs.len() implies {
        let wire = source.outputs[i];
        source_wire_valid(source, wire) && (#[trigger] projected.outputs[i]) == source_wire_value(wire, input, projected.gates)
    } by {
        endpoint_value(source, netlist, order, index, source.outputs[i], netlist.outputs@[i], input, frame.gates@);
    };
}

proof fn project_reset(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>, frame: TickFrame,
)
    requires source_clocked_layout(source, netlist, order, index), reset_matches(netlist, frame),
    ensures source_reset_matches(source, frame_from_flat(index, frame)),
{
    let projected = frame_from_flat(index, frame);
    source_clocked_layout_valid(source, netlist, order, index);
    assert forall|site: SourceGateId| source.gates.dom().contains(site) implies !(#[trigger] projected.gates[site]) by {
        assert(0 <= index[site] < frame.gates@.len());
    };
    observe_source(source, netlist, order, index, Seq::new(netlist.input_count as nat, |_: int| false), frame);
}

proof fn project_step(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
    previous: Seq<bool>, input: Seq<bool>, frame: TickFrame,
)
    requires source_clocked_layout(source, netlist, order, index), tick_matches(netlist, previous, input, frame),
    ensures source_step_matches(source, state_from_flat(index, previous), input, frame_from_flat(index, frame)),
{
    let projected = frame_from_flat(index, frame);
    let prior = state_from_flat(index, previous);
    source_clocked_layout_valid(source, netlist, order, index);
    assert forall|site: SourceGateId| source.gates.dom().contains(site) implies {
        let gate = source.gates[site];
        &&& source_wire_valid(source, gate.left) && source_wire_valid(source, gate.right)
        &&& (#[trigger] projected.gates[site]) == !(source_wire_value(gate.left, input, prior)
            || source_wire_value(gate.right, input, prior))
    } by {
        let i = index[site];
        assert(0 <= i < order.len() && order[i] == site);
        let gate = source.gates[site];
        let lowered = netlist.gates@[i];
        endpoint_value(source, netlist, order, index, gate.left, lowered.left, input, previous);
        endpoint_value(source, netlist, order, index, gate.right, lowered.right, input, previous);
        assert(projected.gates[site] == frame.gates@[i]);
    };
    observe_source(source, netlist, order, index, input, frame);
}

/// 配線とゲートの対応が成り立つとき、有限の VM trace を同じ公開出力のソース trace に写す。
pub proof fn source_trace_from_flat(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
    inputs: Seq<Seq<bool>>, frames: Seq<TickFrame>,
) -> (projected: Seq<SourceTickFrame>)
    requires source_clocked_layout(source, netlist, order, index), nor_trace(netlist, inputs, frames),
    ensures
        source_tick_trace(source, inputs, projected),
        projected.len() == frames.len(),
        forall|i: int| 0 <= i < projected.len() ==> (#[trigger] projected[i]).outputs == frames[i].outputs@,
{
    let projected = Seq::new(frames.len(), |i: int| frame_from_flat(index, frames[i]));
    project_reset(source, netlist, order, index, frames[0]);
    assert forall|i: int| 0 < i < projected.len() implies
        source_step_matches(source, projected[i - 1].gates, inputs[i - 1], #[trigger] projected[i]) by {
        assert(tick_matches(netlist, frames[i - 1].gates@, inputs[i - 1], frames[i]));
        project_step(source, netlist, order, index, frames[i - 1].gates@, inputs[i - 1], frames[i]);
    };
    projected
}

proof fn source_observations_agree(
    source: &SourceTickCircuit, input: Seq<bool>, first: SourceTickFrame, second: SourceTickFrame,
)
    requires source_outputs_match(source, input, first), source_outputs_match(source, input, second),
        first.gates == second.gates,
    ensures first == second,
{
    assert(first.outputs =~= second.outputs);
}

proof fn source_trace_frames_agree(
    source: &SourceTickCircuit, inputs: Seq<Seq<bool>>, first: Seq<SourceTickFrame>, second: Seq<SourceTickFrame>, i: int,
)
    requires source_tick_trace(source, inputs, first), source_tick_trace(source, inputs, second), 0 <= i < first.len(),
    ensures first[i] == second[i],
    decreases i,
{
    let a = first[i];
    let b = second[i];
    let input = if i == 0 { Seq::new(source.input_count as nat, |_: int| false) } else { inputs[i - 1] };
    if i == 0 {
        assert(a.gates =~= b.gates);
    } else {
        source_trace_frames_agree(source, inputs, first, second, i - 1);
        assert(source_step_matches(source, first[i - 1].gates, input, a));
        assert(source_step_matches(source, second[i - 1].gates, input, b));
        assert(a.gates =~= b.gates);
    }
    source_observations_agree(source, input, a, b);
}

/// 同じ入力列に対し、ソースのゲート状態と公開出力は各 tick で一意に定まる。
pub proof fn source_tick_traces_agree(
    source: &SourceTickCircuit, inputs: Seq<Seq<bool>>, first: Seq<SourceTickFrame>, second: Seq<SourceTickFrame>,
)
    requires source_tick_trace(source, inputs, first), source_tick_trace(source, inputs, second),
    ensures first == second,
{
    assert forall|i: int| 0 <= i < first.len() implies (#[trigger] first[i]) == second[i] by {
        source_trace_frames_agree(source, inputs, first, second, i);
    };
    assert(first =~= second);
}

/// 同じ入力列から得た任意のソース trace と VM trace の公開出力が一致する。
pub proof fn source_trace_outputs_preserved(
    source: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
    inputs: Seq<Seq<bool>>, flat: Seq<TickFrame>, original: Seq<SourceTickFrame>,
)
    requires source_clocked_layout(source, netlist, order, index),
        nor_trace(netlist, inputs, flat), source_tick_trace(source, inputs, original),
    ensures original.len() == flat.len(),
        forall|i: int| 0 <= i < original.len() ==> (#[trigger] original[i]).outputs == flat[i].outputs@,
{
    let projected = source_trace_from_flat(source, netlist, order, index, inputs, flat);
    source_tick_traces_agree(source, inputs, original, projected);
}

// 自己参照のゲートを許し、reset の0と次の tick の1を区別することを確かめる。
proof fn source_oscillator_trace_example() {
    let id = SourceGateId {
        instance: Seq::empty(),
        gate: DefinitionPosition { file: 0, entry: 0, definition: 0, reference: 0 },
    };
    let feedback = SourceWire::Gate(id);
    let source = SourceTickCircuit {
        input_count: 0,
        gates: Map::empty().insert(id, SourceNor { left: feedback, right: feedback }),
        outputs: seq![feedback],
    };
    let initial = SourceTickFrame { gates: Map::empty().insert(id, false), outputs: seq![false] };
    let next = SourceTickFrame { gates: Map::empty().insert(id, true), outputs: seq![true] };
    let input = Seq::<bool>::empty();
    let frames = seq![initial, next];
    assert(source_wiring_valid(&source));
    assert(source_reset_matches(&source, initial));
    assert(source_step_matches(&source, initial.gates, input, next));
    assert(source_tick_trace(&source, seq![input], frames));
    assert(!source_step_matches(&source, initial.gates, input, initial)) by {
        if source_step_matches(&source, initial.gates, input, initial) {
            assert(source.gates.dom().contains(id) && source.gates[id].left == feedback && source.gates[id].right == feedback);
            assert(!initial.gates[id]);
            assert(initial.gates[id] == !(source_wire_value(feedback, input, initial.gates)
                || source_wire_value(feedback, input, initial.gates)));
        }
    };
}

} // verus!
