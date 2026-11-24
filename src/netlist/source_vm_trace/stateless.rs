//! 状態素子を持たない関数の参照回路を、順序回路の参照モデルで使う。

use super::{
    SourceDeviceId, SourceVmCircuit, SourceVmNor, SourceVmWire, source_vm_layout_for_orders, source_vm_layout_from_pairs,
    source_vm_layout_matches, source_vm_row_pair, source_vm_terminal_pair,
};
use crate::netlist::{
    NorNetlist, SourceGateId, SourceTickCircuit, SourceWire, Wire, clocked_storage_output_width,
    clocked_storage_width_concat, source_clocked_layout, source_gate_positions_distinct, source_gate_wiring_pair,
    source_output_wiring_pair, source_trace_gate_index, source_trace_layout_counts, source_wire_pair, wire_available,
};
use vstd::prelude::*;

verus! {

spec fn stateless_terminal(wire: SourceWire) -> SourceVmWire {
    match wire {
        SourceWire::Input(index) => SourceVmWire::Input(index),
        SourceWire::Constant(bit) => SourceVmWire::Constant(bit),
        SourceWire::Gate(id) => SourceVmWire::Gate(id),
    }
}

proof fn stateless_terminal_pair(
    external: usize, order: Seq<SourceGateId>, original: SourceWire, flat: Wire,
)
    requires source_wire_pair(order, original, flat), wire_available(flat, external as nat, order.len()),
    ensures source_vm_terminal_pair(external, Seq::empty(), &source_vm_layout_for_orders(order, Seq::empty()),
        stateless_terminal(original), flat),
{
    order.to_set_ensures();
    if let SourceWire::Gate(id) = original {
        let index = flat->Gate_0;
        assert(order[index as int] == id);
        assert(order.to_set().contains(id));
    }
}

/// 元の参照モデルだけから、状態素子を持たない参照回路を定める。
pub(crate) closed spec fn source_vm_stateless_model(model: &SourceTickCircuit) -> SourceVmCircuit {
    SourceVmCircuit {
        input_count: model.input_count,
        gates: Map::new(model.gates.dom(), |id: SourceGateId| {
            let gate = model.gates[id];
            SourceVmNor { left: stateless_terminal(gate.left), right: stateless_terminal(gate.right) }
        }),
        storage: Map::empty(),
        outputs: model.outputs.map_values(|wire: SourceWire| stateless_terminal(wire)),
    }
}

/// 関数の参照回路のゲートと端子を、同じ遅延のまま順序回路の参照モデルに移す。
///
/// 呼び出し先の各 NOR は個別に値を保持する。ラッチや RAM の配置は空になる。
pub(crate) proof fn source_vm_lift_stateless(
    model: &SourceTickCircuit, netlist: &NorNetlist, order: Seq<SourceGateId>, index: Map<SourceGateId, int>,
) -> (source: SourceVmCircuit)
    requires source_clocked_layout(model, netlist, order, index),
    ensures
        source == source_vm_stateless_model(model), source.input_count == model.input_count,
        order.len() == netlist.gates@.len() && order.no_duplicates(),
        source_vm_layout_matches(&source, netlist, Seq::empty(), &source_vm_layout_for_orders(order, Seq::empty())),
{
    source_trace_layout_counts(model, netlist, order, index);
    order.to_set_ensures();
    let source = source_vm_stateless_model(model);
    assert forall|a: int, b: int| 0 <= a < b < order.len() implies (#[trigger] order[a]) != (#[trigger] order[b]) by {
        source_gate_positions_distinct(model, netlist, order, index, a, b);
    };
    assert forall|id: SourceGateId| model.gates.dom().contains(id) implies order.to_set().contains(id) by {
        source_trace_gate_index(model, netlist, order, index, id);
        assert(order[index[id]] == id);
    };
    assert forall|i: int| 0 <= i < order.len() implies model.gates.dom().contains(#[trigger] order[i]) by {
        source_gate_wiring_pair(model, netlist, order, index, i);
    };
    assert(model.gates.dom() =~= order.to_set());
    let devices = Seq::<SourceDeviceId>::empty();
    devices.to_set_ensures();
    assert(source.storage.dom() =~= devices.to_set());
    assert(source.gates.dom() == model.gates.dom());
    let layout = source_vm_layout_for_orders(order, devices);
    let storage = Seq::empty();
    clocked_storage_width_concat(storage, storage);
    assert(clocked_storage_output_width(storage) == 0);
    assert forall|i: int| 0 <= i < order.len() implies {
        let flat = #[trigger] netlist.gates@[i];
        let gate = source.gates[order[i]];
        &&& source_vm_terminal_pair(source.input_count, storage, &layout, gate.left, flat.left)
        &&& source_vm_terminal_pair(source.input_count, storage, &layout, gate.right, flat.right)
    } by {
        source_gate_wiring_pair(model, netlist, order, index, i);
        let gate = model.gates[order[i]];
        let flat = netlist.gates@[i];
        stateless_terminal_pair(model.input_count, order, gate.left, flat.left);
        stateless_terminal_pair(model.input_count, order, gate.right, flat.right);
    };
    assert(source_vm_row_pair(source.input_count, storage, &layout, source.outputs, netlist.outputs@)) by {
        assert forall|i: int| 0 <= i < netlist.outputs@.len() implies
            source_vm_terminal_pair(source.input_count, storage, &layout, source.outputs[i], #[trigger] netlist.outputs@[i]) by {
            source_output_wiring_pair(model, netlist, order, index, i);
            stateless_terminal_pair(model.input_count, order, model.outputs[i], netlist.outputs@[i]);
        };
    };
    source_vm_layout_from_pairs(&source, netlist, storage, order, devices);
    source
}

} // verus!
