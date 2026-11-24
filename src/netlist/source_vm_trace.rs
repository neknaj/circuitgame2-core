//! インスタンス経路で区別する NOR、ラッチ、RAM の参照意味論。

use super::{SourceGateId, clocked_storage_value_transition, latch_next, ram_address_value, ram_next_memory, ram_read_word};
use crate::project::DefinitionPosition;
use vstd::arithmetic::power2::{lemma_pow2_unfold, pow2};
use vstd::prelude::*;

mod layout;
pub use layout::{
    SourceVmLayout, source_vm_layout_matches, source_vm_mapped_wire_value, source_vm_outputs_match,
    source_vm_project_observation, source_vm_project_reset, source_vm_read_wire, source_vm_state_projection,
    source_vm_wire_matches,
};

verus! {

/// 状態素子を呼んだ位置と、ルートからそこへ至る呼び出し位置の列。
pub struct SourceDeviceId {
    /// 外側から内側の順に並べたモジュール呼び出し。
    pub instance: Seq<DefinitionPosition>,
    /// このインスタンス内でラッチまたは RAM を呼び出した位置。
    pub call: DefinitionPosition,
}

/// ソース上の端子が読むビット。
pub enum SourceVmWire {
    /// ルートの外部入力。宣言順で、各ポート内は低位ビットから並ぶ。
    Input(usize),
    /// 状態から独立した定数。
    Constant(bool),
    /// 特定のインスタンスに属する基底 NOR の出力。
    Gate(SourceGateId),
    /// 状態素子の登録出力。添字0は最下位ビット。
    Registered(SourceDeviceId, usize),
}

/// 基底 NOR の入力端子。
pub struct SourceVmNor {
    /// 左入力。
    pub left: SourceVmWire,
    /// 右入力。
    pub right: SourceVmWire,
}

/// ソース上の状態素子の端子。
pub struct SourceStorage {
    /// RAM のアドレスを低位ビットから並べる。ラッチでは `None`。
    pub address: Option<Seq<SourceVmWire>>,
    /// 書き込むデータを低位ビットから並べる。
    pub data: Seq<SourceVmWire>,
    /// 書き込みを許可する端子。
    pub enable: SourceVmWire,
}

/// 宣言順の公開ポートと、呼び出し位置で引ける基底素子を持つ参照回路。
pub struct SourceVmCircuit {
    /// ルートの外部入力のビット数。
    pub input_count: usize,
    /// ソース上の識別子から基底 NOR を引く。
    pub gates: Map<SourceGateId, SourceVmNor>,
    /// ソース上の識別子からラッチまたは RAM を引く。
    pub storage: Map<SourceDeviceId, SourceStorage>,
    /// 宣言順、各ポート内は低位ビット順の公開出力配線。
    pub outputs: Seq<SourceVmWire>,
}

/// 状態素子の登録出力と、RAM の場合はアドレス順の記憶全体。
pub struct SourceDeviceState {
    /// ラッチの保持値または RAM の登録読み出し値。
    pub registered: Seq<bool>,
    /// RAM の記憶ビット。ラッチでは `None`。
    pub memory: Option<Seq<bool>>,
}

/// tick の境界で保持する全素子の状態。
pub struct SourceVmState {
    /// 基底 NOR ごとの出力。
    pub gates: Map<SourceGateId, bool>,
    /// ラッチと RAM ごとの状態。
    pub storage: Map<SourceDeviceId, SourceDeviceState>,
}

/// reset 直後または一つの tick が終わった時点の状態と公開出力。
pub struct SourceVmFrame {
    /// 呼び出し経路と位置で引ける全素子の状態。
    pub state: SourceVmState,
    /// 宣言順、各ポート内は低位ビット順の公開出力値。
    pub outputs: Seq<bool>,
}

spec fn wire_valid(source: &SourceVmCircuit, wire: SourceVmWire) -> bool {
    match wire {
        SourceVmWire::Input(i) => i < source.input_count,
        SourceVmWire::Constant(_) => true,
        SourceVmWire::Gate(id) => source.gates.contains_key(id),
        SourceVmWire::Registered(id, bit) => source.storage.contains_key(id) && bit < source.storage[id].data.len(),
    }
}

spec fn wire_value(wire: SourceVmWire, input: Seq<bool>, state: SourceVmState) -> bool {
    match wire {
        SourceVmWire::Input(i) => input[i as int],
        SourceVmWire::Constant(bit) => bit,
        SourceVmWire::Gate(id) => state.gates[id],
        SourceVmWire::Registered(id, bit) => state.storage[id].registered[bit as int],
    }
}

spec fn wire_row_valid(source: &SourceVmCircuit, row: Seq<SourceVmWire>) -> bool {
    forall|i: int| 0 <= i < row.len() ==> wire_valid(source, #[trigger] row[i])
}

/// 全端子が存在するビットを参照し、各状態素子には正のデータ幅がある。
pub closed spec fn source_vm_wiring_valid(source: &SourceVmCircuit) -> bool {
    &&& forall|id: SourceGateId| source.gates.contains_key(id) ==> {
        let gate = #[trigger] source.gates[id];
        wire_valid(source, gate.left) && wire_valid(source, gate.right)
    }
    &&& forall|id: SourceDeviceId| source.storage.contains_key(id) ==> {
        let device = #[trigger] source.storage[id];
        &&& device.data.len() > 0
        &&& wire_row_valid(source, device.data)
        &&& wire_valid(source, device.enable)
        &&& (device.address matches Some(address) ==> wire_row_valid(source, address))
    }
    &&& wire_row_valid(source, source.outputs)
}

spec fn storage_memory_width(device: SourceStorage) -> Option<nat> {
    match device.address {
        None => None,
        Some(address) => Some(pow2(address.len()) * device.data.len()),
    }
}

/// 保持している素子の集合、登録出力幅、記憶容量が宣言と一致する。
pub closed spec fn source_vm_state_matches(source: &SourceVmCircuit, state: SourceVmState) -> bool {
    &&& state.gates.dom() == source.gates.dom()
    &&& state.storage.dom() == source.storage.dom()
    &&& forall|id: SourceDeviceId| source.storage.contains_key(id) ==> {
        let value = #[trigger] state.storage[id];
        let device = source.storage[id];
        &&& value.registered.len() == device.data.len()
        &&& storage_memory_width(device) == match value.memory { Some(bits) => Some(bits.len()), None => None }
    }
}

spec fn outputs_match(source: &SourceVmCircuit, input: Seq<bool>, frame: SourceVmFrame) -> bool {
    &&& frame.outputs.len() == source.outputs.len()
    &&& forall|i: int| 0 <= i < frame.outputs.len() ==>
        (#[trigger] frame.outputs[i]) == wire_value(source.outputs[i], input, frame.state)
}

spec fn read_pins(device: SourceStorage, input: Seq<bool>, state: SourceVmState) -> (Option<Seq<bool>>, Seq<bool>, bool) {
    let address = match device.address {
        Some(wires) => Some(wires.map_values(|wire: SourceVmWire| wire_value(wire, input, state))),
        None => None,
    };
    (address, device.data.map_values(|wire: SourceVmWire| wire_value(wire, input, state)),
        wire_value(device.enable, input, state))
}

/// reset では外部入力と全素子をゼロにし、その状態から公開出力を読む。
pub closed spec fn source_vm_reset_matches(source: &SourceVmCircuit, frame: SourceVmFrame) -> bool {
    &&& source_vm_wiring_valid(source)
    &&& source_vm_state_matches(source, frame.state)
    &&& forall|id: SourceGateId| source.gates.contains_key(id) ==> !(#[trigger] frame.state.gates[id])
    &&& forall|id: SourceDeviceId| source.storage.contains_key(id) ==> {
        let value = #[trigger] frame.state.storage[id];
        let device = source.storage[id];
        &&& value.registered == Seq::new(device.data.len(), |_: int| false)
        &&& value.memory == match storage_memory_width(device) {
            Some(width) => Some(Seq::new(width, |_: int| false)),
            None => None,
        }
    }
    &&& outputs_match(source, Seq::new(source.input_count as nat, |_: int| false), frame)
}

/// 全素子が同じ旧状態を読み、公開出力は全更新を確定してから読む。
pub closed spec fn source_vm_step_matches(
    source: &SourceVmCircuit, previous: SourceVmState, input: Seq<bool>, frame: SourceVmFrame,
) -> bool {
    &&& source_vm_wiring_valid(source)
    &&& input.len() == source.input_count
    &&& source_vm_state_matches(source, previous)
    &&& source_vm_state_matches(source, frame.state)
    &&& forall|id: SourceGateId| source.gates.contains_key(id) ==> {
        let gate = source.gates[id];
        (#[trigger] frame.state.gates[id]) == !(wire_value(gate.left, input, previous) || wire_value(gate.right, input, previous))
    }
    &&& forall|id: SourceDeviceId| source.storage.contains_key(id) ==> {
        let old = previous.storage[id];
        let new = #[trigger] frame.state.storage[id];
        clocked_storage_value_transition(old.registered, old.memory, new.registered, new.memory,
            read_pins(source.storage[id], input, previous))
    }
    &&& outputs_match(source, input, frame)
}

/// reset と任意の有限入力列に対するソース回路の状態と観測を表す。
pub open spec fn source_vm_trace(source: &SourceVmCircuit, inputs: Seq<Seq<bool>>, frames: Seq<SourceVmFrame>) -> bool {
    &&& frames.len() == inputs.len() + 1
    &&& source_vm_reset_matches(source, frames[0])
    &&& forall|i: int| 0 < i < frames.len() ==>
        source_vm_step_matches(source, frames[i - 1].state, inputs[i - 1], #[trigger] frames[i])
}

spec fn observe(source: &SourceVmCircuit, input: Seq<bool>, state: SourceVmState) -> SourceVmFrame {
    SourceVmFrame { state, outputs: source.outputs.map_values(|wire: SourceVmWire| wire_value(wire, input, state)) }
}

/// 正しい端子を持つ回路には reset 直後の状態と出力が存在する。
pub proof fn source_vm_reset_frame(source: &SourceVmCircuit) -> (frame: SourceVmFrame)
    requires source_vm_wiring_valid(source),
    ensures source_vm_reset_matches(source, frame), source_vm_state_matches(source, frame.state),
{
    let state = SourceVmState {
        gates: Map::new(source.gates.dom(), |_: SourceGateId| false),
        storage: Map::new(source.storage.dom(), |id: SourceDeviceId| {
            let device = source.storage[id];
            SourceDeviceState {
                registered: Seq::new(device.data.len(), |_: int| false),
                memory: match storage_memory_width(device) {
                    Some(width) => Some(Seq::new(width, |_: int| false)),
                    None => None,
                },
            }
        }),
    };
    observe(source, Seq::new(source.input_count as nat, |_: int| false), state)
}

proof fn address_in_declared_range(bits: Seq<bool>)
    ensures ram_address_value(bits) < pow2(bits.len()),
    decreases bits.len(),
{
    if bits.len() == 0 {
        assert(pow2(0) == 1) by { reveal(vstd::arithmetic::power::pow); };
    } else {
        address_in_declared_range(bits.drop_first());
        lemma_pow2_unfold(bits.len());
    }
}

spec fn next_device(before: SourceDeviceState, pins: (Option<Seq<bool>>, Seq<bool>, bool)) -> SourceDeviceState {
    let (address, data, enabled) = pins;
    match address {
        None => SourceDeviceState { registered: latch_next(before.registered, data, enabled), memory: None },
        Some(bits) => {
            let address = ram_address_value(bits);
            let memory = before.memory->Some_0;
            SourceDeviceState {
                registered: ram_read_word(memory, address, data.len()),
                memory: Some(ram_next_memory(memory, address, data, enabled)),
            }
        },
    }
}

proof fn next_device_matches(
    source: &SourceVmCircuit, previous: SourceVmState, input: Seq<bool>, id: SourceDeviceId,
)
    requires source.storage.contains_key(id), source_vm_state_matches(source, previous),
    ensures
        ({
            let device = source.storage[id];
            let pins = read_pins(device, input, previous);
            let old = previous.storage[id];
            let new = next_device(old, pins);
            &&& new.registered.len() == device.data.len()
            &&& storage_memory_width(device) == match new.memory { Some(bits) => Some(bits.len()), None => None }
            &&& clocked_storage_value_transition(old.registered, old.memory, new.registered, new.memory, pins)
        }),
{
    let pins = read_pins(source.storage[id], input, previous);
    if let Some(bits) = pins.0 {
        address_in_declared_range(bits);
        let address = ram_address_value(bits);
        let width = pins.1.len();
        let words = pow2(bits.len());
        assert(address * width + width <= words * width) by (nonlinear_arith)
            requires address < words,
        {}
    }
}

/// 正しい幅の入力を与えると、任意の合法な旧状態から1 tick 進められる。
pub proof fn source_vm_next_frame(
    source: &SourceVmCircuit, previous: SourceVmState, input: Seq<bool>,
) -> (frame: SourceVmFrame)
    requires source_vm_wiring_valid(source), source_vm_state_matches(source, previous), input.len() == source.input_count,
    ensures source_vm_step_matches(source, previous, input, frame), source_vm_state_matches(source, frame.state),
{
    let state = SourceVmState {
        gates: Map::new(source.gates.dom(), |id: SourceGateId| {
            let gate = source.gates[id];
            !(wire_value(gate.left, input, previous) || wire_value(gate.right, input, previous))
        }),
        storage: Map::new(source.storage.dom(), |id: SourceDeviceId|
            next_device(previous.storage[id], read_pins(source.storage[id], input, previous))),
    };
    assert forall|id: SourceDeviceId| source.storage.contains_key(id) implies {
        let device = source.storage[id];
        let old = previous.storage[id];
        let new = #[trigger] state.storage[id];
        &&& new.registered.len() == device.data.len()
        &&& storage_memory_width(device) == match new.memory { Some(bits) => Some(bits.len()), None => None }
        &&& clocked_storage_value_transition(old.registered, old.memory, new.registered, new.memory,
            read_pins(device, input, previous))
    } by {
        next_device_matches(source, previous, input, id);
    };
    observe(source, input, state)
}

/// 各入力の幅が正しければ、reset から有限入力列の末尾までの観測が存在する。
pub proof fn source_vm_run_trace(source: &SourceVmCircuit, inputs: Seq<Seq<bool>>) -> (frames: Seq<SourceVmFrame>)
    requires source_vm_wiring_valid(source),
        forall|i: int| 0 <= i < inputs.len() ==> (#[trigger] inputs[i]).len() == source.input_count,
    ensures source_vm_trace(source, inputs, frames), source_vm_state_matches(source, frames.last().state),
    decreases inputs.len(),
{
    if inputs.len() == 0 {
        let frame = source_vm_reset_frame(source);
        seq![frame]
    } else {
        let earlier = inputs.drop_last();
        let frames = source_vm_run_trace(source, earlier);
        let frame = source_vm_next_frame(source, frames.last().state, inputs.last());
        let more = frames.push(frame);
        assert forall|i: int| 0 < i < more.len() implies
            source_vm_step_matches(source, more[i - 1].state, inputs[i - 1], #[trigger] more[i]) by {
            if i < frames.len() {
                assert(more[i] == frames[i]);
                assert(more[i - 1] == frames[i - 1]);
                assert(earlier[i - 1] == inputs[i - 1]);
            } else {
                assert(more[i - 1] == frames.last());
                assert(inputs[i - 1] == inputs.last());
            }
        };
        more
    }
}

proof fn trace_frames_agree(
    source: &SourceVmCircuit, inputs: Seq<Seq<bool>>, first: Seq<SourceVmFrame>, second: Seq<SourceVmFrame>, i: int,
)
    requires source_vm_trace(source, inputs, first), source_vm_trace(source, inputs, second), 0 <= i < first.len(),
    ensures first[i] == second[i],
    decreases i,
{
    let a = first[i];
    let b = second[i];
    let input = if i == 0 { Seq::new(source.input_count as nat, |_: int| false) } else { inputs[i - 1] };
    if i == 0 {
        assert(a.state.gates =~= b.state.gates);
        assert(a.state.storage =~= b.state.storage);
    } else {
        trace_frames_agree(source, inputs, first, second, i - 1);
        let previous = first[i - 1].state;
        assert(source_vm_step_matches(source, previous, input, a));
        assert(source_vm_step_matches(source, previous, input, b));
        assert(a.state.gates =~= b.state.gates);
        assert forall|id: SourceDeviceId| source.storage.contains_key(id) implies
            (#[trigger] a.state.storage[id]) == (#[trigger] b.state.storage[id]) by {
            let old = previous.storage[id];
            let left = a.state.storage[id];
            let right = b.state.storage[id];
            let pins = read_pins(source.storage[id], input, previous);
            assert(clocked_storage_value_transition(old.registered, old.memory, left.registered, left.memory, pins));
            assert(clocked_storage_value_transition(old.registered, old.memory, right.registered, right.memory, pins));
            assert(left.registered == right.registered && left.memory == right.memory);
        };
        assert(a.state.storage =~= b.state.storage);
    }
    assert(a.state == b.state);
    assert(a.outputs =~= b.outputs);
}

/// 同じ外部入力列から、各インスタンスの全状態と公開出力が一意に決まる。
pub proof fn source_vm_traces_agree(
    source: &SourceVmCircuit, inputs: Seq<Seq<bool>>, first: Seq<SourceVmFrame>, second: Seq<SourceVmFrame>,
)
    requires source_vm_trace(source, inputs, first), source_vm_trace(source, inputs, second),
    ensures first == second,
{
    assert forall|i: int| 0 <= i < first.len() implies (#[trigger] first[i]) == second[i] by {
        trace_frames_agree(source, inputs, first, second, i);
    };
    assert(first =~= second);
}

} // verus!
