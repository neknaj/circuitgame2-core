//! ゲートの識別子と配線を、子回路から親回路へ写す。

use super::{SourceGateId, SourceNor, SourceTickCircuit, SourceWire, source_clocked_layout,
    source_gate_wiring_pair, source_output_wiring_pair, source_trace_layout_counts, source_wire_pair};
use crate::netlist::{NorGate, NorNetlist, Wire, instance_gates_at, instance_outputs_match, instance_wire};
use crate::project::DefinitionPosition;
use vstd::prelude::*;

verus! {

/// 子の内部ゲートを、親からの呼び出し経路で識別する。
pub(crate) open spec fn source_gate_under(prefix: Seq<DefinitionPosition>, child: SourceGateId) -> SourceGateId {
    SourceGateId { instance: prefix + child.instance, gate: child.gate }
}

/// 子の入力を親の実引数で置き換える。子の内部ゲートには呼び出し経路を付ける。
pub(crate) open spec fn source_wire_in_parent(prefix: Seq<DefinitionPosition>, arguments: Seq<SourceWire>, wire: SourceWire) -> SourceWire {
    match wire {
        SourceWire::Input(port) => arguments[port as int],
        SourceWire::Constant(bit) => SourceWire::Constant(bit),
        SourceWire::Gate(gate) => SourceWire::Gate(source_gate_under(prefix, gate)),
    }
}

pub(crate) proof fn source_wire_pair_in_parent(prefix: Seq<DefinitionPosition>, child_order: Seq<SourceGateId>, order: Seq<SourceGateId>,
    source_arguments: Seq<SourceWire>, flat_arguments: Seq<Wire>, gate_start: usize, source: SourceWire, flat: Wire)
    requires
        source_wire_pair(child_order, source, flat),
        source_instance_order_at(prefix, child_order, order, gate_start),
        flat matches Wire::Input(port) ==> port < source_arguments.len() == flat_arguments.len()
            && source_wire_pair(order, source_arguments[port as int], flat_arguments[port as int]),
    ensures
        source_wire_pair(order, source_wire_in_parent(prefix, source_arguments, source),
            instance_wire(flat, flat_arguments, gate_start)),
{
    match flat {
        Wire::Gate(gate) => {
            assert(order[gate_start + gate] == source_gate_under(prefix, child_order[gate as int]));
        },
        Wire::Input(port) => {
            assert(source == SourceWire::Input(port));
        },
        Wire::Constant(value) => {
            assert(source == SourceWire::Constant(value));
        },
    }
}

/// 子のゲート順を保ったまま、すべての識別子に同じ呼び出し経路を付ける。
pub(crate) open spec fn source_instance_order(prefix: Seq<DefinitionPosition>, child: Seq<SourceGateId>) -> Seq<SourceGateId> {
    Seq::new(child.len(), |i: int| source_gate_under(prefix, child[i]))
}

pub(crate) open spec fn source_instance_order_at(
    prefix: Seq<DefinitionPosition>, child: Seq<SourceGateId>, parent: Seq<SourceGateId>, start: usize,
) -> bool {
    &&& start + child.len() <= parent.len() <= usize::MAX
    &&& forall|i: int| 0 <= i < child.len() ==> (#[trigger] parent[start + i]) == source_gate_under(prefix, child[i])
}

/// 先行ゲートの識別子を保ち、ソースで定めた子の識別子を同じ順に末尾へ置く。
pub(crate) proof fn source_instance_order_appended(
    prefix: Seq<DefinitionPosition>, child: Seq<SourceGateId>, before: Seq<SourceGateId>,
)
    requires before.len() + child.len() <= usize::MAX,
    ensures source_instance_order_at(prefix, child, before + source_instance_order(prefix, child), before.len() as usize),
{
    let parent = before + source_instance_order(prefix, child);
    assert forall|i: int| 0 <= i < child.len() implies #[trigger] parent[before.len() + i] == source_gate_under(prefix, child[i]) by {
        assert(parent[before.len() + i] == source_instance_order(prefix, child)[i]);
    };
}

/// この回路の基底 NOR または通常呼び出しから生じたゲートかどうかを表す。
pub(crate) open spec fn source_gate_belongs_to_call(site: DefinitionPosition, gate: SourceGateId) -> bool {
    if gate.instance.len() == 0 { gate.gate == site } else { gate.instance[0] == site }
}

/// 基底 NOR はその場のゲート一つ、通常呼び出しは子回路の全ゲートを順に配置する。
pub(crate) open spec fn source_call_gate_order(site: DefinitionPosition, child: Option<Seq<SourceGateId>>) -> Seq<SourceGateId> {
    match child {
        None => seq![SourceGateId { instance: Seq::empty(), gate: site }],
        Some(order) => source_instance_order(seq![site], order),
    }
}

pub(crate) proof fn source_gate_under_distinct(prefix: Seq<DefinitionPosition>, a: SourceGateId, b: SourceGateId)
    requires a != b,
    ensures source_gate_under(prefix, a) != source_gate_under(prefix, b),
{
    let left = source_gate_under(prefix, a);
    let right = source_gate_under(prefix, b);
    assert(left.instance.skip(prefix.len() as int) =~= a.instance);
    assert(right.instance.skip(prefix.len() as int) =~= b.instance);
}

/// 呼び出しが追加したゲートの所属と、呼び出し内での識別子の一意性を示す。
pub(crate) proof fn source_call_gate_order_distinct(site: DefinitionPosition, child: Option<Seq<SourceGateId>>)
    requires child matches Some(order) ==> order.no_duplicates(),
    ensures
        source_call_gate_order(site, child).no_duplicates(),
        forall|i: int| 0 <= i < source_call_gate_order(site, child).len() ==>
            source_gate_belongs_to_call(site, #[trigger] source_call_gate_order(site, child)[i]),
{
    let placed = source_call_gate_order(site, child);
    if let Some(order) = child {
        let prefix = seq![site];
        assert forall|i: int| 0 <= i < placed.len() implies source_gate_belongs_to_call(site, #[trigger] placed[i]) by {
            assert(placed[i] == source_gate_under(prefix, order[i]));
            assert(placed[i].instance[0] == site);
        };
        assert forall|i: int, j: int| 0 <= i < placed.len() && 0 <= j < placed.len() && i != j
            implies #[trigger] placed[i] != #[trigger] placed[j] by {
            source_gate_under_distinct(prefix, order[i], order[j]);
        };
    }
}

/// 呼び出し位置が先行ゲートの所属と異なるとき、追加後も識別子の一意性を保つ。
pub(crate) proof fn source_call_order_appended(
    before: Seq<SourceGateId>, site: DefinitionPosition, child: Option<Seq<SourceGateId>>,
)
    requires
        before.no_duplicates(),
        child matches Some(order) ==> order.no_duplicates(),
        forall|i: int| 0 <= i < before.len() ==> !source_gate_belongs_to_call(site, #[trigger] before[i]),
    ensures
        (before + source_call_gate_order(site, child)).no_duplicates(),
        (before + source_call_gate_order(site, child)).take(before.len() as int) == before,
        forall|i: int| before.len() <= i < (before + source_call_gate_order(site, child)).len() ==>
            source_gate_belongs_to_call(site, #[trigger] (before + source_call_gate_order(site, child))[i]),
{
    source_call_gate_order_distinct(site, child);
    let tail = source_call_gate_order(site, child);
    let after = before + tail;
    assert(after.take(before.len() as int) =~= before);
    assert forall|i: int| before.len() <= i < after.len()
        implies source_gate_belongs_to_call(site, #[trigger] after[i]) by {
        assert(after[i] == tail[i - before.len()]);
    };
    assert forall|i: int, j: int| 0 <= i < after.len() && 0 <= j < after.len() && i != j
        implies #[trigger] after[i] != #[trigger] after[j] by {
        let (first, second) = if i < j { (i, j) } else { (j, i) };
        if second < before.len() {
            assert(before[first] != before[second]);
        } else if before.len() <= first {
            assert(tail[first - before.len()] != tail[second - before.len()]);
        } else {
            assert(!source_gate_belongs_to_call(site, before[first]));
            assert(source_gate_belongs_to_call(site, tail[second - before.len()]));
        }
    };
}

/// 一つのゲートの左右が、子のソース配線を親で解釈した結果に対応することを示す。
pub(crate) proof fn source_instance_gate_agrees(
    prefix: Seq<DefinitionPosition>, child: &SourceTickCircuit, netlist: &NorNetlist,
    child_order: Seq<SourceGateId>, child_index: Map<SourceGateId, int>, order: Seq<SourceGateId>,
    arguments: Seq<SourceWire>, mapped: Seq<Wire>, gates: Seq<NorGate>, start: usize, i: int,
) -> (source: SourceNor)
    requires
        source_clocked_layout(child, netlist, child_order, child_index),
        0 <= i < child_order.len(),
        source_instance_order_at(prefix, child_order, order, start),
        instance_gates_at(netlist.gates@, mapped, start, gates),
        arguments.len() == mapped.len() == netlist.input_count,
        forall|port: int| 0 <= port < arguments.len() ==> source_wire_pair(order, #[trigger] arguments[port], mapped[port]),
    ensures
        start + i < gates.len(),
        source.left == source_wire_in_parent(prefix, arguments, child.gates[child_order[i]].left),
        source.right == source_wire_in_parent(prefix, arguments, child.gates[child_order[i]].right),
        source_wire_pair(order, source.left, gates[start + i].left),
        source_wire_pair(order, source.right, gates[start + i].right),
{
    source_gate_wiring_pair(child, netlist, child_order, child_index, i);
    let gate = child.gates[child_order[i]];
    let flat = netlist.gates@[i];
    source_wire_pair_in_parent(prefix, child_order, order, arguments, mapped, start, gate.left, flat.left);
    source_wire_pair_in_parent(prefix, child_order, order, arguments, mapped, start, gate.right, flat.right);
    assert(gates[start + i].left == instance_wire(flat.left, mapped, start));
    assert(gates[start + i].right == instance_wire(flat.right, mapped, start));
    SourceNor {
        left: source_wire_in_parent(prefix, arguments, gate.left),
        right: source_wire_in_parent(prefix, arguments, gate.right),
    }
}

/// 子の各出力をビット順に親へ写す。入力直結の出力には親の実引数を渡す。
pub(crate) proof fn source_instance_outputs_agree(
    prefix: Seq<DefinitionPosition>, child: &SourceTickCircuit, netlist: &NorNetlist,
    child_order: Seq<SourceGateId>, child_index: Map<SourceGateId, int>, order: Seq<SourceGateId>,
    arguments: Seq<SourceWire>, mapped: Seq<Wire>, start: usize, outputs: Seq<Wire>,
)
    requires
        source_clocked_layout(child, netlist, child_order, child_index),
        source_instance_order_at(prefix, child_order, order, start),
        instance_outputs_match(netlist.outputs@, mapped, start, outputs),
        arguments.len() == mapped.len() == netlist.input_count,
        forall|port: int| 0 <= port < arguments.len() ==> source_wire_pair(order, #[trigger] arguments[port], mapped[port]),
    ensures
        child.outputs.len() == outputs.len(),
        forall|bit: int| 0 <= bit < child.outputs.len() ==> source_wire_pair(order,
            source_wire_in_parent(prefix, arguments, #[trigger] child.outputs[bit]), outputs[bit]),
{
    source_trace_layout_counts(child, netlist, child_order, child_index);
    assert forall|bit: int| 0 <= bit < child.outputs.len() implies source_wire_pair(order,
        source_wire_in_parent(prefix, arguments, #[trigger] child.outputs[bit]), outputs[bit]) by {
        source_output_wiring_pair(child, netlist, child_order, child_index, bit);
        source_wire_pair_in_parent(prefix, child_order, order, arguments, mapped, start, child.outputs[bit], netlist.outputs@[bit]);
        assert(outputs[bit] == instance_wire(netlist.outputs@[bit], mapped, start));
    };
}

} // verus!
