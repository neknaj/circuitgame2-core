//! ソース上の配線と、展開後の VM の配線を対応付ける。

use super::{
    SourceDeviceId, SourceDeviceState, SourceStorage, SourceVmCircuit, SourceVmFrame, SourceVmState, SourceVmWire,
    source_vm_reset_matches, source_vm_state_matches, source_vm_step_matches, source_vm_wiring_valid,
};
use crate::netlist::{
    ClockedStorageInputs, ClockedVm, NorNetlist, SourceGateId, Wire, clocked_storage_memory_width,
    clocked_storage_output_width, clocked_storage_pin_values, clocked_storage_value_transition, clocked_vm_trace,
    output_values_match, wire_value,
};
use vstd::prelude::*;

verus! {

/// ソースの素子 ID と、ルート VM における位置の対応表。
pub struct SourceVmLayout {
    /// VM のゲート順に並べたソース ID。
    pub gates: Seq<SourceGateId>,
    /// ソース ID に対応するゲート番号。
    pub gate_index: Map<SourceGateId, int>,
    /// VM の状態素子順に並べたソース ID。
    pub devices: Seq<SourceDeviceId>,
    /// ソース ID に対応する状態素子番号。
    pub device_index: Map<SourceDeviceId, int>,
}

spec fn indexed<K>(order: Seq<K>, index: Map<K, int>, domain: Set<K>) -> bool {
    &&& domain == index.dom()
    &&& forall|id: K| domain.contains(id) ==> 0 <= #[trigger] index[id] < order.len() && order[index[id]] == id
    &&& forall|i: int| 0 <= i < order.len() ==> domain.contains(#[trigger] order[i]) && index[order[i]] == i
}

/// 端子が指すソースのビットと VM の配線が対応する。
pub(crate) open spec fn source_vm_terminal_pair(
    external: usize, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout, source: SourceVmWire, flat: Wire,
) -> bool {
    match (source, flat) {
        (SourceVmWire::Input(k), Wire::Input(i)) => i == k && k < external,
        (SourceVmWire::Constant(a), Wire::Constant(b)) => a == b,
        (SourceVmWire::Gate(id), Wire::Gate(i)) => layout.gate_index.contains_key(id)
            && i < layout.gates.len() && layout.gates[i as int] == id,
        (SourceVmWire::Registered(id, bit), Wire::Input(i)) => {
            let device = layout.device_index[id];
            &&& layout.device_index.contains_key(id)
            &&& 0 <= device < wiring.len()
            &&& bit < wiring[device].data@.len()
            &&& i == external + clocked_storage_output_width(wiring.take(device)) + bit
        },
        _ => false,
    }
}

/// 端子の本数と順序を保って、各ビットの配線を対応付ける。
pub(crate) open spec fn source_vm_row_pair(
    external: usize, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout, source: Seq<SourceVmWire>, lowered: Seq<Wire>,
) -> bool {
    &&& source.len() == lowered.len()
    &&& forall|i: int| 0 <= i < lowered.len() ==>
        source_vm_terminal_pair(external, wiring, layout, source[i], #[trigger] lowered[i])
}

/// ラッチまたは RAM の全入力端子を、役割とビット順を保って対応付ける。
pub(crate) open spec fn source_vm_storage_pair(
    external: usize, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout, source: SourceStorage, flat: ClockedStorageInputs,
) -> bool {
    &&& match (source.address, flat.address) {
        (None, None) => true,
        (Some(a), Some(b)) => source_vm_row_pair(external, wiring, layout, a, b@),
        _ => false,
    }
    &&& source_vm_row_pair(external, wiring, layout, source.data, flat.data@)
    &&& source_vm_terminal_pair(external, wiring, layout, source.enable, flat.enable)
}

/// 全ソース素子を一度ずつ配置し、端子と公開出力が対応する配線を読むことを表す。
pub closed spec fn source_vm_layout_matches(
    source: &SourceVmCircuit, netlist: &NorNetlist, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
) -> bool {
    &&& source_vm_wiring_valid(source)
    &&& source.input_count + clocked_storage_output_width(wiring) == netlist.input_count
    &&& layout.gates.len() == netlist.gates@.len()
    &&& layout.devices.len() == wiring.len()
    &&& indexed(layout.gates, layout.gate_index, source.gates.dom())
    &&& indexed(layout.devices, layout.device_index, source.storage.dom())
    &&& forall|i: int| 0 <= i < netlist.gates@.len() ==> {
        let flat = #[trigger] netlist.gates@[i];
        let original = source.gates[layout.gates[i]];
        &&& source_vm_terminal_pair(source.input_count, wiring, layout, original.left, flat.left)
        &&& source_vm_terminal_pair(source.input_count, wiring, layout, original.right, flat.right)
    }
    &&& forall|i: int| 0 <= i < wiring.len() ==> {
        let flat = #[trigger] wiring[i];
        let original = source.storage[layout.devices[i]];
        source_vm_storage_pair(source.input_count, wiring, layout, original, flat)
    }
    &&& source_vm_row_pair(source.input_count, wiring, layout, source.outputs, netlist.outputs@)
}

/// 素子 ID を VM の配列順に並べた列から、位置の逆引きを定める。
pub(crate) open spec fn source_vm_layout_for_orders(
    gates: Seq<SourceGateId>, devices: Seq<SourceDeviceId>,
) -> SourceVmLayout {
    SourceVmLayout {
        gates,
        gate_index: Map::new(gates.to_set(), |id: SourceGateId| gates.index_of(id)),
        devices,
        device_index: Map::new(devices.to_set(), |id: SourceDeviceId| devices.index_of(id)),
    }
}

proof fn index_by_order<K>(order: Seq<K>)
    requires order.no_duplicates(),
    ensures indexed(order, Map::new(order.to_set(), |id: K| order.index_of(id)), order.to_set()),
{
    order.to_set_ensures();
    let index = Map::new(order.to_set(), |id: K| order.index_of(id));
    assert forall|id: K| order.to_set().contains(id) implies 0 <= #[trigger] index[id] < order.len()
        && order[index[id]] == id by {
        assert(order.contains(id));
    };
    assert forall|i: int| 0 <= i < order.len() implies order.to_set().contains(#[trigger] order[i])
        && index[order[i]] == i by {
        let id = order[i];
        assert(order.to_set().contains(id));
        assert(order[index[id]] == id);
    };
}

proof fn paired_terminal_valid(
    source: &SourceVmCircuit, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    terminal: SourceVmWire, flat: Wire,
)
    requires
        indexed(layout.gates, layout.gate_index, source.gates.dom()),
        indexed(layout.devices, layout.device_index, source.storage.dom()),
        layout.devices.len() == wiring.len(),
        forall|i: int| 0 <= i < wiring.len() ==>
            source.storage[layout.devices[i]].data.len() == (#[trigger] wiring[i]).data@.len(),
        source_vm_terminal_pair(source.input_count, wiring, layout, terminal, flat),
    ensures super::wire_valid(source, terminal),
{
    if let SourceVmWire::Registered(id, _) = terminal {
        let i = layout.device_index[id];
        assert(layout.devices[i] == id);
        assert(source.storage[id].data.len() == wiring[i].data@.len());
    }
}

proof fn paired_row_valid(
    source: &SourceVmCircuit, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    row: Seq<SourceVmWire>, flat: Seq<Wire>,
)
    requires
        indexed(layout.gates, layout.gate_index, source.gates.dom()),
        indexed(layout.devices, layout.device_index, source.storage.dom()),
        layout.devices.len() == wiring.len(),
        forall|i: int| 0 <= i < wiring.len() ==>
            source.storage[layout.devices[i]].data.len() == (#[trigger] wiring[i]).data@.len(),
        source_vm_row_pair(source.input_count, wiring, layout, row, flat),
    ensures super::wire_row_valid(source, row),
{
    assert forall|i: int| 0 <= i < row.len() implies super::wire_valid(source, #[trigger] row[i]) by {
        paired_terminal_valid(source, wiring, layout, row[i], flat[i]);
    };
}

/// ソースの端子と VM 配線の照合から、実行全体で使う対応関係を組み立てる。
///
/// ソース回路と素子の順序は呼び出し側が与える。ゲート、状態素子、公開出力の全端子を照合する。
pub(crate) proof fn source_vm_layout_from_pairs(
    source: &SourceVmCircuit, netlist: &NorNetlist, wiring: Seq<ClockedStorageInputs>,
    gates: Seq<SourceGateId>, devices: Seq<SourceDeviceId>,
)
    requires
        gates.no_duplicates() && devices.no_duplicates(),
        source.gates.dom() == gates.to_set() && source.storage.dom() == devices.to_set(),
        gates.len() == netlist.gates@.len() && devices.len() == wiring.len(),
        source.input_count + clocked_storage_output_width(wiring) == netlist.input_count,
        forall|i: int| 0 <= i < gates.len() ==> {
            let layout = source_vm_layout_for_orders(gates, devices);
            let original = source.gates[gates[i]];
            let lowered = #[trigger] netlist.gates@[i];
            &&& source_vm_terminal_pair(source.input_count, wiring, &layout, original.left, lowered.left)
            &&& source_vm_terminal_pair(source.input_count, wiring, &layout, original.right, lowered.right)
        },
        forall|i: int| 0 <= i < devices.len() ==> {
            let flat = #[trigger] wiring[i];
            &&& flat.data@.len() > 0
            &&& source_vm_storage_pair(source.input_count, wiring, &source_vm_layout_for_orders(gates, devices),
                source.storage[devices[i]], flat)
        },
        source_vm_row_pair(source.input_count, wiring, &source_vm_layout_for_orders(gates, devices),
            source.outputs, netlist.outputs@),
    ensures source_vm_layout_matches(source, netlist, wiring, &source_vm_layout_for_orders(gates, devices)),
        source_vm_wiring_valid(source),
{
    index_by_order(gates);
    index_by_order(devices);
    let layout = source_vm_layout_for_orders(gates, devices);
    let external = source.input_count;
    assert forall|i: int| 0 <= i < wiring.len() implies
        source.storage[devices[i]].data.len() == (#[trigger] wiring[i]).data@.len() by {
        assert(source_vm_storage_pair(external, wiring, &layout, source.storage[devices[i]], wiring[i]));
    };
    assert forall|id: SourceGateId| source.gates.contains_key(id) implies {
        let gate = #[trigger] source.gates[id];
        super::wire_valid(source, gate.left) && super::wire_valid(source, gate.right)
    } by {
        let i = layout.gate_index[id];
        let flat = netlist.gates@[i];
        assert(gates[i] == id);
        paired_terminal_valid(source, wiring, &layout, source.gates[id].left, flat.left);
        paired_terminal_valid(source, wiring, &layout, source.gates[id].right, flat.right);
    };
    assert forall|id: SourceDeviceId| source.storage.contains_key(id) implies {
        let device = #[trigger] source.storage[id];
        &&& device.data.len() > 0
        &&& super::wire_row_valid(source, device.data)
        &&& super::wire_valid(source, device.enable)
        &&& (device.address matches Some(address) ==> super::wire_row_valid(source, address))
    } by {
        let i = layout.device_index[id];
        let flat = wiring[i];
        let device = source.storage[id];
        assert(devices[i] == id);
        assert(source_vm_storage_pair(external, wiring, &layout, device, flat));
        paired_row_valid(source, wiring, &layout, device.data, flat.data@);
        paired_terminal_valid(source, wiring, &layout, device.enable, flat.enable);
        if let Some(address) = device.address {
            paired_row_valid(source, wiring, &layout, address, flat.address->Some_0@);
        }
    };
    paired_row_valid(source, wiring, &layout, source.outputs, netlist.outputs@);
}

/// VM の状態を、添字に対応するソース ID から引ける形にする。
pub open spec fn source_vm_state_projection(vm: &ClockedVm, layout: &SourceVmLayout) -> SourceVmState {
    SourceVmState {
        gates: Map::new(layout.gate_index.dom(), |id: SourceGateId| vm.gate_values_model()[layout.gate_index[id]]),
        storage: Map::new(layout.device_index.dom(), |id: SourceDeviceId| {
            let value = vm.storage_model()[layout.device_index[id]];
            SourceDeviceState { registered: value.output_model(), memory: value.memory_model() }
        }),
    }
}

proof fn source_state_has_shape(
    source: &SourceVmCircuit, vm: &ClockedVm, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
)
    requires source_vm_layout_matches(source, &vm.netlist_model(), wiring, layout),
        vm.layout_matches(vm.netlist_model(), source.input_count, wiring),
    ensures source_vm_state_matches(source, source_vm_state_projection(vm, layout)),
{
    let state = source_vm_state_projection(vm, layout);
    assert forall|id: SourceDeviceId| source.storage.contains_key(id) implies {
        let value = #[trigger] state.storage[id];
        let original = source.storage[id];
        &&& value.registered.len() == original.data.len()
        &&& super::storage_memory_width(original) == match value.memory { Some(bits) => Some(bits.len()), None => None }
    } by {
        let index = layout.device_index[id];
        let flat = vm.storage_model()[index].wiring_model();
        assert(flat == wiring[index]);
        assert(source_vm_storage_pair(source.input_count, wiring, layout, source.storage[id], flat));
        vm.storage_shape_evidence(index);
        assert(super::storage_memory_width(source.storage[id]) == clocked_storage_memory_width(&flat));
    };
}

/// ソースと VM の端子が、対応する状態から同じ値を読むことを示す。
pub proof fn source_vm_mapped_wire_value(
    source: &SourceVmCircuit, vm: &ClockedVm, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    input: Seq<bool>, augmented: Seq<bool>, original: SourceVmWire, lowered: Wire,
)
    requires source_vm_layout_matches(source, &vm.netlist_model(), wiring, layout),
        vm.layout_matches(vm.netlist_model(), source.input_count, wiring),
        vm.augmented_input_matches(input, augmented),
        source_vm_wire_matches(source, wiring, layout, original, lowered),
    ensures source_vm_read_wire(original, input, source_vm_state_projection(vm, layout))
        == wire_value(lowered, augmented, vm.gate_values_model()),
{
    vm.augmented_input_shape(input, augmented);
    match original {
        SourceVmWire::Input(i) => {
            assert(augmented.take(input.len() as int)[i as int] == augmented[i as int]);
        },
        SourceVmWire::Gate(id) => {
            let gate = lowered->Gate_0 as int;
            assert(layout.gate_index[id] == gate);
        },
        SourceVmWire::Registered(id, bit) => {
            let index = layout.device_index[id];
            vm.storage_input_range_evidence(index);
            vm.augmented_storage_segment(input, augmented, index);
            let range = vm.storage_input_range_model(index);
            assert(range.start + bit < range.end);
            assert(augmented.subrange(range.start as int, range.end as int)[bit as int]
                == augmented[(range.start + bit) as int]);
        },
        SourceVmWire::Constant(_) => {},
    }
}

/// ソース配線と VM 配線が同じ端子を指す関係。
pub closed spec fn source_vm_wire_matches(
    source: &SourceVmCircuit, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    original: SourceVmWire, lowered: Wire,
) -> bool {
    source_vm_terminal_pair(source.input_count, wiring, layout, original, lowered)
}

/// ソースの配線からビットを読む。
pub closed spec fn source_vm_read_wire(wire: SourceVmWire, input: Seq<bool>, state: SourceVmState) -> bool {
    super::wire_value(wire, input, state)
}

/// 対応する配置と状態から、同じ公開ポートの値を観測する。
pub proof fn source_vm_project_observation(
    source: &SourceVmCircuit, vm: &ClockedVm, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    input: Seq<bool>, augmented: Seq<bool>, output: Seq<bool>,
) -> (frame: SourceVmFrame)
    requires source_vm_layout_matches(source, &vm.netlist_model(), wiring, layout),
        vm.layout_matches(vm.netlist_model(), source.input_count, wiring),
        vm.augmented_input_matches(input, augmented),
        output.len() == vm.netlist_model().outputs@.len(),
        output_values_match(augmented, vm.gate_values_model(), vm.netlist_model().outputs@, output),
    ensures frame.state == source_vm_state_projection(vm, layout), frame.outputs == output,
        source_vm_outputs_match(source, input, frame),
{
    let state = source_vm_state_projection(vm, layout);
    let frame = SourceVmFrame { state, outputs: output };
    let ports = vm.netlist_model().outputs@;
    assert forall|i: int| 0 <= i < output.len() implies
        (#[trigger] output[i]) == super::wire_value(source.outputs[i], input, state) by {
        assert(source_vm_wire_matches(source, wiring, layout, source.outputs[i], ports[i]));
        source_vm_mapped_wire_value(source, vm, wiring, layout, input, augmented, source.outputs[i], ports[i]);
    };
    frame
}

/// フレームの公開出力が、それに含まれる状態と外部入力から得られる。
pub closed spec fn source_vm_outputs_match(source: &SourceVmCircuit, input: Seq<bool>, frame: SourceVmFrame) -> bool {
    super::outputs_match(source, input, frame)
}

/// VM のリセット結果から、ソース上の初期状態と公開出力を求める。
///
/// 登録出力と RAM の記憶は、宣言された端子幅から決まる長さのゼロ列になる。
pub proof fn source_vm_project_reset(
    source: &SourceVmCircuit, vm: &ClockedVm, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    output: Seq<bool>,
) -> (frame: SourceVmFrame)
    requires source_vm_layout_matches(source, &vm.netlist_model(), wiring, layout),
        vm.layout_matches(vm.netlist_model(), source.input_count, wiring),
        vm.reset_matches(output),
    ensures source_vm_reset_matches(source, frame),
        frame.state == source_vm_state_projection(vm, layout),
        frame.outputs == output,
{
    let augmented = vm.reset_snapshot(output);
    let input = Seq::new(source.input_count as nat, |_: int| false);
    let frame = source_vm_project_observation(source, vm, wiring, layout, input, augmented, output);
    source_state_has_shape(source, vm, wiring, layout);
    assert forall|id: SourceGateId| source.gates.contains_key(id) implies !(#[trigger] frame.state.gates[id]) by {
        assert(0 <= layout.gate_index[id] < vm.gate_values_model().len());
    };
    assert forall|id: SourceDeviceId| source.storage.contains_key(id) implies {
        let value = #[trigger] frame.state.storage[id];
        let original = source.storage[id];
        &&& value.registered == Seq::new(original.data.len(), |_: int| false)
        &&& value.memory == match super::storage_memory_width(original) {
            Some(width) => Some(Seq::new(width, |_: int| false)),
            None => None,
        }
    } by {
        let index = layout.device_index[id];
        vm.initial_storage_values(index);
        let flat = vm.storage_model()[index].wiring_model();
        assert(flat == wiring[index]);
        assert(source_vm_storage_pair(source.input_count, wiring, layout, source.storage[id], flat));
        assert(super::storage_memory_width(source.storage[id])
            == match frame.state.storage[id].memory { Some(bits) => Some(bits.len()), None => None });
    };
    frame
}

proof fn mapped_row_values(
    source: &SourceVmCircuit, vm: &ClockedVm, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    input: Seq<bool>, augmented: Seq<bool>, original: Seq<SourceVmWire>, flat: Seq<Wire>,
)
    requires source_vm_layout_matches(source, &vm.netlist_model(), wiring, layout),
        vm.layout_matches(vm.netlist_model(), source.input_count, wiring),
        vm.augmented_input_matches(input, augmented),
        source_vm_row_pair(source.input_count, wiring, layout, original, flat),
    ensures
        original.map_values(|pin: SourceVmWire| super::wire_value(pin, input, source_vm_state_projection(vm, layout)))
            == Seq::new(flat.len(), |i: int| wire_value(flat[i], augmented, vm.gate_values_model())),
{
    let state = source_vm_state_projection(vm, layout);
    let original_bits = original.map_values(|pin: SourceVmWire| super::wire_value(pin, input, state));
    let flat_bits = Seq::new(flat.len(), |i: int| wire_value(flat[i], augmented, vm.gate_values_model()));
    assert(original_bits =~= flat_bits) by {
        assert forall|i: int| 0 <= i < flat.len() implies original_bits[i] == flat_bits[i] by {
            assert(source_vm_wire_matches(source, wiring, layout, original[i], flat[i]));
            source_vm_mapped_wire_value(source, vm, wiring, layout, input, augmented, original[i], flat[i]);
        };
    };
}

proof fn mapped_storage_pins(
    source: &SourceVmCircuit, vm: &ClockedVm, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    input: Seq<bool>, augmented: Seq<bool>, original: SourceStorage, flat: &ClockedStorageInputs,
)
    requires source_vm_layout_matches(source, &vm.netlist_model(), wiring, layout),
        vm.layout_matches(vm.netlist_model(), source.input_count, wiring),
        vm.augmented_input_matches(input, augmented),
        source_vm_storage_pair(source.input_count, wiring, layout, original, *flat),
    ensures super::read_pins(original, input, source_vm_state_projection(vm, layout))
        == clocked_storage_pin_values(flat, augmented, vm.gate_values_model()),
{
    if let Some(address) = original.address {
        let flat_address = flat.address->Some_0;
        mapped_row_values(source, vm, wiring, layout, input, augmented, address, flat_address@);
    }
    mapped_row_values(source, vm, wiring, layout, input, augmented, original.data, flat.data@);
    assert(source_vm_wire_matches(source, wiring, layout, original.enable, flat.enable));
    source_vm_mapped_wire_value(source, vm, wiring, layout, input, augmented, original.enable, flat.enable);
}

/// VM の 1 tick がソースの状態遷移と同じ結果を返すことを示す。
///
/// NOR と状態素子は tick 開始時の状態を読み、公開ポートは更新後の状態を読む。
pub proof fn source_vm_project_step(
    source: &SourceVmCircuit, previous: &ClockedVm, next: &ClockedVm,
    wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout, input: Seq<bool>, output: Seq<bool>,
) -> (frame: SourceVmFrame)
    requires source_vm_layout_matches(source, &previous.netlist_model(), wiring, layout),
        previous.layout_matches(previous.netlist_model(), source.input_count, wiring),
        next.tick_matches(previous, input, output),
    ensures source_vm_step_matches(source, source_vm_state_projection(previous, layout), input, frame),
        next.layout_matches(previous.netlist_model(), source.input_count, wiring),
        frame.state == source_vm_state_projection(next, layout),
        frame.outputs == output,
{
    let netlist = previous.netlist_model();
    let (old_inputs, new_inputs) = next.tick_snapshots(previous, input, output);
    next.preserve_layout_evidence(previous, netlist, source.input_count, wiring);
    assert(next.netlist_model() == netlist);
    let prior = source_vm_state_projection(previous, layout);
    let frame = source_vm_project_observation(source, next, wiring, layout, input, new_inputs, output);
    source_state_has_shape(source, previous, wiring, layout);
    source_state_has_shape(source, next, wiring, layout);
    assert forall|id: SourceGateId| source.gates.contains_key(id) implies {
        let gate = source.gates[id];
        (#[trigger] frame.state.gates[id]) == !(super::wire_value(gate.left, input, prior)
            || super::wire_value(gate.right, input, prior))
    } by {
        let i = layout.gate_index[id];
        assert(layout.gates[i] == id && 0 <= i < netlist.gates@.len());
        let gate = source.gates[id];
        let flat = netlist.gates@[i];
        assert(source_vm_wire_matches(source, wiring, layout, gate.left, flat.left));
        assert(source_vm_wire_matches(source, wiring, layout, gate.right, flat.right));
        source_vm_mapped_wire_value(source, previous, wiring, layout, input, old_inputs, gate.left, flat.left);
        source_vm_mapped_wire_value(source, previous, wiring, layout, input, old_inputs, gate.right, flat.right);
        assert(next.gate_values_model()[i] == !(wire_value(flat.left, old_inputs, previous.gate_values_model())
            || wire_value(flat.right, old_inputs, previous.gate_values_model())));
    };
    assert forall|id: SourceDeviceId| source.storage.contains_key(id) implies {
        let old = prior.storage[id];
        let new = #[trigger] frame.state.storage[id];
        clocked_storage_value_transition(old.registered, old.memory, new.registered, new.memory,
            super::read_pins(source.storage[id], input, prior))
    } by {
        let i = layout.device_index[id];
        let old = previous.storage_model()[i];
        let new = next.storage_model()[i];
        let flat = old.wiring_model();
        assert(layout.devices[i] == id && 0 <= i < wiring.len());
        assert(flat == wiring[i]);
        assert(source_vm_storage_pair(source.input_count, wiring, layout, source.storage[id], flat));
        mapped_storage_pins(source, previous, wiring, layout, input, old_inputs, source.storage[id], &flat);
        new.tick_values(&old, old_inputs, previous.gate_values_model());
    };
    frame
}

proof fn trace_layout(
    source: &SourceVmCircuit, inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    wiring: Seq<ClockedStorageInputs>, index: int,
)
    requires clocked_vm_trace(inputs, states, outputs),
        states[0].layout_matches(states[0].netlist_model(), source.input_count, wiring),
        0 <= index < states.len(),
    ensures states[index].layout_matches(states[0].netlist_model(), source.input_count, wiring),
    decreases index,
{
    if index > 0 {
        trace_layout(source, inputs, states, outputs, wiring, index - 1);
        let current = &states[index];
        let previous = &states[index - 1];
        current.tick_snapshots(previous, inputs[index - 1], outputs[index]);
        current.preserve_layout_evidence(previous, states[0].netlist_model(), source.input_count, wiring);
    }
}

/// VM の任意の有限実行を、同じ公開出力を持つソースの trace に対応付ける。
///
/// 先頭は reset の結果。以後の各フレームは、同じ入力で 1 tick 進めた結果を表す。
pub proof fn source_vm_project_trace(
    source: &SourceVmCircuit, inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
) -> (frames: Seq<SourceVmFrame>)
    requires clocked_vm_trace(inputs, states, outputs),
        states[0].layout_matches(states[0].netlist_model(), source.input_count, wiring),
        source_vm_layout_matches(source, &states[0].netlist_model(), wiring, layout),
    ensures super::source_vm_trace(source, inputs, frames),
        frames == Seq::new(outputs.len(), |i: int| SourceVmFrame {
            state: source_vm_state_projection(&states[i], layout), outputs: outputs[i],
        }),
        frames.map_values(|frame: SourceVmFrame| frame.outputs) == outputs,
{
    let frames = Seq::new(outputs.len(), |i: int| SourceVmFrame {
        state: source_vm_state_projection(&states[i], layout), outputs: outputs[i],
    });
    let reset = source_vm_project_reset(source, &states[0], wiring, layout, outputs[0]);
    assert(frames[0] == reset);
    assert forall|i: int| 0 < i < frames.len() implies
        source_vm_step_matches(source, frames[i - 1].state, inputs[i - 1], #[trigger] frames[i]) by {
        trace_layout(source, inputs, states, outputs, wiring, i - 1);
        let prior = &states[i - 1];
        assert(prior.netlist_model() == states[0].netlist_model());
        let step = source_vm_project_step(source, prior, &states[i], wiring, layout, inputs[i - 1], outputs[i]);
        assert(frames[i] == step);
    };
    assert(frames.map_values(|frame: SourceVmFrame| frame.outputs) =~= outputs);
    frames
}

/// ソースの参照意味論と VM の公開出力が、すべての tick で一致することを示す。
pub proof fn source_vm_trace_outputs_agree(
    source: &SourceVmCircuit, inputs: Seq<Seq<bool>>, states: Seq<ClockedVm>, outputs: Seq<Seq<bool>>,
    wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout, reference: Seq<SourceVmFrame>,
)
    requires clocked_vm_trace(inputs, states, outputs),
        states[0].layout_matches(states[0].netlist_model(), source.input_count, wiring),
        source_vm_layout_matches(source, &states[0].netlist_model(), wiring, layout),
        super::source_vm_trace(source, inputs, reference),
    ensures reference.map_values(|frame: SourceVmFrame| frame.outputs) == outputs,
{
    let frames = source_vm_project_trace(source, inputs, states, outputs, wiring, layout);
    super::source_vm_traces_agree(source, inputs, frames, reference);
}

} // verus!
