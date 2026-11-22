//! 関数本体で得たゲートと公開出力から、tick の参照回路を組み立てる。

use super::SourceChildModel;
use crate::netlist::{
    NorNetlist, SourceGateId, SourceNor, SourceTickCircuit, SourceWire, nor_evaluation_ready,
    source_clocked_layout, source_clocked_layout_from_pairs, source_output_pair_at, source_output_pairs,
    source_wire_pair, wire_available,
};
use vstd::prelude::*;

verus! {

/// ソース上の識別子と配線から、ゲートの対応表と公開出力を定める。
pub(in crate::project::use_aliases::bit_func::lowering) open spec fn function_source_circuit(
    input_count: usize, order: Seq<SourceGateId>, gates: Seq<SourceNor>, outputs: Seq<SourceWire>,
) -> SourceTickCircuit {
    SourceTickCircuit {
        input_count,
        gates: Map::new(order.to_set(), |site: SourceGateId| gates[order.index_of(site)]),
        outputs,
    }
}

/// 関数のゲート番号とソース上の識別子を対応付け、全配線と公開出力を照合する。
///
/// ゲート列が空の関数でも、入力や定数を参照する出力の対応を証明する。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn function_source_layout(
    input_count: usize, order: Seq<SourceGateId>, gates: Seq<SourceNor>, outputs: Seq<SourceWire>, netlist: &NorNetlist,
) -> (model: SourceChildModel)
    requires
        nor_evaluation_ready(netlist, input_count as nat),
        order.len() == gates.len() == netlist.gates@.len(),
        order.no_duplicates(),
        forall|i: int| 0 <= i < gates.len() ==> {
            let gate = #[trigger] gates[i];
            let flat = netlist.gates@[i];
            &&& source_wire_pair(order, gate.left, flat.left)
            &&& source_wire_pair(order, gate.right, flat.right)
        },
        outputs.len() == netlist.outputs@.len(),
        forall|i: int| 0 <= i < outputs.len() ==> source_wire_pair(order, #[trigger] outputs[i], netlist.outputs@[i]),
    ensures
        model.circuit == function_source_circuit(input_count, order, gates, outputs),
        model.order == order,
        source_clocked_layout(&model.circuit, netlist, model.order, model.index),
{
    let circuit = function_source_circuit(input_count, order, gates, outputs);
    let index = Map::new(order.to_set(), |site: SourceGateId| order.index_of(site));
    order.to_set_ensures();
    assert forall|site: SourceGateId| index.dom().contains(site) implies
        0 <= #[trigger] index[site] < order.len() && order[index[site]] == site by {
        assert(order.contains(site));
    };
    assert forall|i: int| 0 <= i < order.len() implies {
        let site = #[trigger] order[i];
        let flat = netlist.gates@[i];
        &&& index.dom().contains(site) && index[site] == i
        &&& wire_available(flat.left, input_count as nat, order.len())
        &&& wire_available(flat.right, input_count as nat, order.len())
        &&& source_wire_pair(order, circuit.gates[site].left, flat.left)
        &&& source_wire_pair(order, circuit.gates[site].right, flat.right)
    } by {
        let site = order[i];
        assert(index.dom().contains(site));
        assert(order[index[site]] == site);
        assert(index[site] == i);
        assert(circuit.gates[site] == gates[i]);
        assert(wire_available(netlist.gates@[i].left, input_count as nat, i as nat));
        assert(wire_available(netlist.gates@[i].right, input_count as nat, i as nat));
    };
    assert(source_output_pairs(&circuit, netlist, order)) by {
        assert forall|i: int| 0 <= i < outputs.len() implies #[trigger]
            source_output_pair_at(&circuit, netlist, order, i) by {
            assert(wire_available(netlist.outputs@[i], input_count as nat, order.len()));
            assert(source_wire_pair(order, outputs[i], netlist.outputs@[i]));
        };
    };
    source_clocked_layout_from_pairs(&circuit, netlist, order, index);
    SourceChildModel { circuit, order, index }
}

} // verus!
