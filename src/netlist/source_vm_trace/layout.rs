//! ソース上の配線と、展開後の VM の配線を対応付ける。

use super::{SourceDeviceId, SourceDeviceState, SourceStorage, SourceVmCircuit, SourceVmFrame, SourceVmState, SourceVmWire,
    source_vm_reset_matches, source_vm_state_matches, source_vm_wiring_valid};
use crate::netlist::{ClockedStorageInputs, ClockedVm, NorNetlist, SourceGateId, Wire, clocked_storage_output_width,
    clocked_storage_memory_width, output_values_match, wire_value};
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

spec fn wire_pair(
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

spec fn row_pair(
    external: usize, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout, source: Seq<SourceVmWire>, lowered: Seq<Wire>,
) -> bool {
    &&& source.len() == lowered.len()
    &&& forall|i: int| 0 <= i < lowered.len() ==> wire_pair(external, wiring, layout, source[i], #[trigger] lowered[i])
}

spec fn storage_pair(
    external: usize, wiring: Seq<ClockedStorageInputs>, layout: &SourceVmLayout, source: SourceStorage, flat: ClockedStorageInputs,
) -> bool {
    &&& match (source.address, flat.address) {
        (None, None) => true,
        (Some(a), Some(b)) => row_pair(external, wiring, layout, a, b@),
        _ => false,
    }
    &&& row_pair(external, wiring, layout, source.data, flat.data@)
    &&& wire_pair(external, wiring, layout, source.enable, flat.enable)
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
        &&& wire_pair(source.input_count, wiring, layout, original.left, flat.left)
        &&& wire_pair(source.input_count, wiring, layout, original.right, flat.right)
    }
    &&& forall|i: int| 0 <= i < wiring.len() ==> {
        let flat = #[trigger] wiring[i];
        let original = source.storage[layout.devices[i]];
        storage_pair(source.input_count, wiring, layout, original, flat)
    }
    &&& row_pair(source.input_count, wiring, layout, source.outputs, netlist.outputs@)
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
        assert(storage_pair(source.input_count, wiring, layout, source.storage[id], flat));
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
    wire_pair(source.input_count, wiring, layout, original, lowered)
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
        assert(storage_pair(source.input_count, wiring, layout, source.storage[id], flat));
        assert(super::storage_memory_width(source.storage[id])
            == match frame.state.storage[id].memory { Some(bits) => Some(bits.len()), None => None });
    };
    frame
}

} // verus!
