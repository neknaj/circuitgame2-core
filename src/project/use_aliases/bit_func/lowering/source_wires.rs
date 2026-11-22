//! 型検査済みの定義から、元の回路が参照するビット配線を定める。

use super::*;
use super::super::concat_operands_fit;
use crate::netlist::{SourceGateId, SourceNor, SourceWire, source_wire_pair};

verus! {

/// 宣言順の入力ビットか、先行定義のビットを参照する。
pub(super) open spec fn source_driver_wire(
    widths: Seq<u64>, prior: Seq<Seq<SourceWire>>, driver: OutputDriver, bit: int,
) -> SourceWire {
    match driver {
        OutputDriver::Input(port) => SourceWire::Input((preceding_port_bits(widths, port as nat) + bit) as usize),
        OutputDriver::Definition(slot) => prior[slot as int][bit],
    }
}

pub(super) open spec fn source_operand_bit(widths: Seq<u64>, prior: Seq<Seq<SourceWire>>, operand: SingleBitOperand, bit: int) -> SourceWire {
    match operand {
        SingleBitOperand::Constant(value) => SourceWire::Constant(value),
        SingleBitOperand::Driver(driver) => source_driver_wire(widths, prior, driver, bit),
    }
}

/// 基底 NOR の左右の入力元を、入力と先行定義から決める。
pub(super) open spec fn source_local_nor(
    widths: Seq<u64>, prior: Seq<Seq<SourceWire>>, left: SingleBitOperand, right: SingleBitOperand,
) -> SourceNor {
    SourceNor { left: source_operand_bit(widths, prior, left, 0), right: source_operand_bit(widths, prior, right, 0) }
}

/// 呼び出しの出力を除く定義について、型検査で得た順序のビット配線を返す。
///
/// 直結とビット選択は元の配線を参照し、基底 NOR だけが新しいゲートを出力する。
pub(super) closed spec fn source_local_wires(
    widths: Seq<u64>, prior: Seq<Seq<SourceWire>>, definition: CheckedBitDefinition, gate: SourceGateId,
) -> Option<Seq<SourceWire>> {
    let width = definition.width as nat;
    match definition.rhs {
        BitFuncRhs::Driver(driver) => Some(Seq::new(width, |bit: int| source_driver_wire(widths, prior, driver, bit))),
        BitFuncRhs::Constant(value) => Some(seq![SourceWire::Constant(value)]),
        BitFuncRhs::Nor { .. } => Some(seq![SourceWire::Gate(gate)]),
        BitFuncRhs::Selection { input, selection } => Some(Seq::new(width, |bit: int|
            source_driver_wire(widths, prior, input, selection.start + bit * selection.stride))),
        BitFuncRhs::BitVector => Some(Seq::new(width, |bit: int|
            SourceWire::Constant(bit_literal_value_at(literal_bytes(definition.expression), bit as nat)))),
        BitFuncRhs::Concat => Some(definition.operands@.map_values(|item: (SingleBitOperand, u64)|
            Seq::new(item.1 as nat, |bit: int| source_operand_bit(widths, prior, item.0, bit))).flatten()),
        BitFuncRhs::CallOutput { .. } | BitFuncRhs::NorCallOutput { .. } => None,
    }
}

pub(super) open spec fn source_wires_pair(order: Seq<SourceGateId>, source: Seq<SourceWire>, flat: Seq<Wire>) -> bool {
    &&& source.len() == flat.len()
    &&& forall|bit: int| 0 <= bit < source.len() ==> source_wire_pair(order, #[trigger] source[bit], flat[bit])
}

/// 先行する定義ごとに、同じビット順で並ぶソース配線と変換先を対応付ける。
pub(super) open spec fn definition_wires_pair(
    order: Seq<SourceGateId>, source: Seq<Seq<SourceWire>>, ranges: Seq<Range<usize>>, flat: Seq<Wire>,
) -> bool {
    &&& source.len() <= ranges.len()
    &&& forall|i: int| 0 <= i < source.len() ==> {
        let range = ranges[i];
        &&& range.start <= range.end <= flat.len()
        &&& source_wires_pair(order, #[trigger] source[i], flat.subrange(range.start as int, range.end as int))
    }
}

/// 型が指定する一ビット参照を、配線表の同じポートとビットに対応付ける。
pub(super) proof fn source_driver_wire_agrees(
    widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, capacity: usize,
    prior: Seq<Seq<SourceWire>>, flat: Seq<Wire>, order: Seq<SourceGateId>, driver: OutputDriver, bit: int, width: u64,
)
    requires
        body_definition_layouts(widths, definitions, capacity, layouts),
        prior.len() <= definitions.len(),
        flat.len() == preceding_port_bits(definition_widths(definitions), prior.len()),
        definition_wires_pair(order, prior, layouts.definitions.ranges_model(), flat),
        bit_driver_width(widths, definitions.take(prior.len() as int), driver) == Some(width),
        0 <= bit < width,
    ensures source_wire_pair(order, source_driver_wire(widths, prior, driver, bit),
        driver_wire(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), flat, driver, bit)),
{
    let inputs = layouts.inputs.ranges_model();
    let ranges = layouts.definitions.ranges_model();
    body_driver_bits_fit_layout(widths, definitions, layouts, capacity, prior.len() as int, flat.len() as int, driver, width, bit);
    match driver {
        OutputDriver::Input(port) => {
            port_bit_layout_port(widths, capacity, layouts.inputs, port);
        },
        OutputDriver::Definition(slot) => {
            let span = ranges[slot as int];
            let port = prior[slot as int];
            let part = flat.subrange(span.start as int, span.end as int);
            assert(source_wires_pair(order, port, part));
            assert(span.end - span.start == width);
            assert(part[bit] == flat[span.start + bit]);
            assert(source_wire_pair(order, port[bit], part[bit]));
        },
    }
}

proof fn source_operand_bit_agrees(
    widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, capacity: usize,
    prior: Seq<Seq<SourceWire>>, flat: Seq<Wire>, order: Seq<SourceGateId>, operand: SingleBitOperand, bit: int, width: u64,
)
    requires
        body_definition_layouts(widths, definitions, capacity, layouts),
        prior.len() <= definitions.len(),
        flat.len() == preceding_port_bits(definition_widths(definitions), prior.len()),
        definition_wires_pair(order, prior, layouts.definitions.ranges_model(), flat),
        match operand {
            SingleBitOperand::Constant(_) => width == 1,
            SingleBitOperand::Driver(driver) => bit_driver_width(widths, definitions.take(prior.len() as int), driver) == Some(width),
        },
        0 <= bit < width,
    ensures source_wire_pair(order, source_operand_bit(widths, prior, operand, bit),
        projected_wire(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
            flat, concat_operand_projection(operand), bit)),
{
    let inputs = layouts.inputs.ranges_model();
    let ranges = layouts.definitions.ranges_model();
    let projection = concat_operand_projection(operand);
    let lowered = projected_wire(inputs, ranges, flat, projection, bit);
    let source = source_operand_bit(widths, prior, operand, bit);
    match operand {
        SingleBitOperand::Constant(value) => {
            assert(source == SourceWire::Constant(value));
            assert(lowered == Wire::Constant(value));
        },
        SingleBitOperand::Driver(driver) => {
            source_driver_wire_agrees(widths, definitions, layouts, capacity, prior, flat, order, driver, bit, width);
            assert(bit * 1 == bit);
            assert(source == source_driver_wire(widths, prior, driver, bit));
            assert(lowered == driver_wire(inputs, ranges, flat, driver, bit));
        },
    }
}

pub(super) proof fn flatten_source_wire_pairs(order: Seq<SourceGateId>, source: Seq<Seq<SourceWire>>, flat: Seq<Seq<Wire>>)
    requires
        source.len() == flat.len(),
        forall|i: int| 0 <= i < source.len() ==> source_wires_pair(order, #[trigger] source[i], flat[i]),
    ensures source_wires_pair(order, source.flatten(), flat.flatten()),
    decreases source.len(),
{
    if source.len() > 0 {
        let n = source.len() as int - 1;
        let prefix = source.take(n);
        let wires = flat.take(n);
        assert forall|i: int| 0 <= i < prefix.len() implies source_wires_pair(order, #[trigger] prefix[i], wires[i]) by {
            assert(prefix[i] == source[i] && wires[i] == flat[i]);
        };
        flatten_source_wire_pairs(order, prefix, wires);
        let a = source[n];
        let b = flat[n];
        prefix.lemma_flatten_push(a);
        wires.lemma_flatten_push(b);
        assert(prefix.push(a) =~= source);
        assert(wires.push(b) =~= flat);
        let start = prefix.flatten().len() as int;
        assert forall|bit: int| 0 <= bit < source.flatten().len() implies
            source_wire_pair(order, #[trigger] source.flatten()[bit], flat.flatten()[bit]) by {
            if bit < start {
                assert(source.flatten()[bit] == prefix.flatten()[bit]);
                assert(flat.flatten()[bit] == wires.flatten()[bit]);
            } else {
                assert(source.flatten()[bit] == a[bit - start]);
                assert(flat.flatten()[bit] == b[bit - start]);
            }
        };
    }
}

/// 連接の引数を低位側から並べたソース配線が、変換後のビット列に対応することを示す。
proof fn source_concat_agrees(
    widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, capacity: usize,
    prior: Seq<Seq<SourceWire>>, flat: Seq<Wire>, order: Seq<SourceGateId>, operands: Seq<(SingleBitOperand, u64)>,
)
    requires
        body_definition_layouts(widths, definitions, capacity, layouts),
        prior.len() <= definitions.len(),
        flat.len() == preceding_port_bits(definition_widths(definitions), prior.len()),
        definition_wires_pair(order, prior, layouts.definitions.ranges_model(), flat),
        concat_operands_fit(widths, definitions.take(prior.len() as int), operands),
    ensures source_wires_pair(order,
        operands.map_values(|item: (SingleBitOperand, u64)| Seq::new(item.1 as nat, |bit: int|
            source_operand_bit(widths, prior, item.0, bit))).flatten(),
        concat_operand_wires(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), flat, operands).flatten()),
{
    let ports = operands.map_values(|item: (SingleBitOperand, u64)| Seq::new(item.1 as nat, |bit: int|
        source_operand_bit(widths, prior, item.0, bit)));
    let wires = concat_operand_wires(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), flat, operands);
    assert forall|i: int| 0 <= i < ports.len() implies source_wires_pair(order, #[trigger] ports[i], wires[i]) by {
        let (operand, width) = operands[i];
        let a = ports[i];
        let b = wires[i];
        assert forall|bit: int| 0 <= bit < a.len() implies source_wire_pair(order, #[trigger] a[bit], b[bit]) by {
            source_operand_bit_agrees(widths, definitions, layouts, capacity, prior, flat, order, operand, bit, width);
        };
    };
    flatten_source_wire_pairs(order, ports, wires);
}

pub(super) open spec fn local_slot_wires_pair(
    widths: Seq<u64>, prior: Seq<Seq<SourceWire>>, definition: CheckedBitDefinition, gate: SourceGateId,
    order: Seq<SourceGateId>, lowered: Seq<Wire>, gates: Seq<NorGate>,
) -> bool {
    &&& source_local_wires(widths, prior, definition, gate) matches Some(source)
    &&& source_wires_pair(order, source, lowered)
    &&& definition.rhs matches BitFuncRhs::Nor { left, right } ==> {
        let nor = source_local_nor(widths, prior, left, right);
        &&& lowered.len() == 1
        &&& lowered[0] matches Wire::Gate(i)
        &&& i < gates.len()
        &&& source_wire_pair(order, nor.left, gates[i as int].left)
        &&& source_wire_pair(order, nor.right, gates[i as int].right)
    }
}

/// 一つの定義のソース配線と、変換後の出力および NOR の左右の入力を照合する。
pub(super) proof fn source_local_slot_agrees(
    widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, capacity: usize,
    prior: Seq<Seq<SourceWire>>, final_wires: Seq<Wire>, gates: Seq<NorGate>, origins: Seq<usize>,
    order: Seq<SourceGateId>, gate: SourceGateId,
)
    requires
        body_definition_layouts(widths, definitions, capacity, layouts),
        prior.len() < definitions.len(),
        ({
            let slot = prior.len() as int;
            let definition = definitions[slot];
            let span = layouts.definitions.ranges_model()[slot];
            let flat = final_wires.take(span.start as int);
            &&& bit_definition_matches(widths, definitions.take(slot), definition)
            &&& slot_wiring_matches(definition, layouts, final_wires, gates, origins, slot)
            &&& definition_wires_pair(order, prior, layouts.definitions.ranges_model(), flat)
            &&& definition.rhs is Nor ==> (final_wires[span.start as int] matches Wire::Gate(i)
                && i < order.len() && order[i as int] == gate)
        }),
    ensures ({
        let slot = prior.len() as int;
        let span = layouts.definitions.ranges_model()[slot];
        local_slot_wires_pair(widths, prior, definitions[slot], gate, order,
            final_wires.subrange(span.start as int, span.end as int), gates)
    }),
{
    let slot = prior.len() as int;
    let definition = definitions[slot];
    let span = layouts.definitions.ranges_model()[slot];
    let flat = final_wires.take(span.start as int);
    let port = final_wires.subrange(span.start as int, span.end as int);
    let source = source_local_wires(widths, prior, definition, gate)->Some_0;
    let def_widths = definition_widths(definitions);
    assert(def_widths[slot] == definition.width);
    port_bit_layout_size(def_widths, capacity, &layouts.definitions);
    port_bit_layout_port(def_widths, capacity, layouts.definitions, slot as usize);
    assert(span.start < span.end <= final_wires.len());
    assert(flat.len() == preceding_port_bits(def_widths, prior.len()));
    assert(port.len() == definition.width);
    assert(source_local_wires(widths, prior, definition, gate).is_some());
    match definition.rhs {
        BitFuncRhs::Concat => {
            source_concat_agrees(widths, definitions, layouts, capacity, prior, flat, order, definition.operands@);
            assert(port == concat_operand_wires(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
                flat, definition.operands@).flatten());
            assert(source_wires_pair(order, source, port));
        },
        BitFuncRhs::Nor { left, right } => {
            source_operand_bit_agrees(widths, definitions, layouts, capacity, prior, flat, order, left, 0, 1);
            source_operand_bit_agrees(widths, definitions, layouts, capacity, prior, flat, order, right, 0, 1);
            let i = final_wires[span.start as int]->Gate_0;
            assert(final_wires[span.start as int] == Wire::Gate(i));
            assert(i < gates.len());
            assert(gates[i as int] == rhs_gate(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
                flat, definition.rhs)->Some_0);
            assert(port[0] == Wire::Gate(i) && port.len() == 1);
            assert(source =~= seq![SourceWire::Gate(gate)]);
            assert(source_wires_pair(order, source, port));
        },
        BitFuncRhs::Driver(driver) => {
            assert forall|bit: int| 0 <= bit < source.len() implies source_wire_pair(order, #[trigger] source[bit], port[bit]) by {
                source_driver_wire_agrees(widths, definitions, layouts, capacity, prior, flat, order, driver, bit, definition.width);
            };
        },
        BitFuncRhs::Selection { input, selection } => {
            let width = bit_driver_width(widths, definitions.take(slot), input)->Some_0;
            assert forall|bit: int| 0 <= bit < source.len() implies source_wire_pair(order, #[trigger] source[bit], port[bit]) by {
                selected_bit_in_range(width, selection.start, selection.count, selection.stride, selection.last, bit);
                source_driver_wire_agrees(widths, definitions, layouts, capacity, prior, flat, order, input,
                    selection.start + bit * selection.stride, width);
            };
        },
        _ => {
            assert forall|bit: int| 0 <= bit < source.len() implies
                source_wire_pair(order, #[trigger] source[bit], port[bit]) by {
                assert(port[bit] == final_wires[span.start + bit]);
            };
        },
    }
}

/// 宣言順に出力の駆動元を読み、ポート内は最下位ビットから並べる。
pub(super) open spec fn source_output_wires(
    widths: Seq<u64>, definitions: Seq<Seq<SourceWire>>, outputs: Seq<u64>, drivers: Seq<OutputDriver>,
) -> Seq<SourceWire> {
    Seq::new(outputs.len(), |port: int| Seq::new(outputs[port] as nat, |bit: int|
        source_driver_wire(widths, definitions, drivers[port], bit))).flatten()
}

pub(super) proof fn port_ranges_cover(
    widths: Seq<u64>, layout: &PortBitLayout, capacity: usize, wire: Seq<Wire>, ports: nat,
)
    requires
        port_bit_layout_result(widths, capacity, Ok(*layout)),
        wire.len() == layout.total_bits_model(), ports <= widths.len(),
    ensures ({
        let ranges = layout.ranges_model();
        let pieces = Seq::new(widths.len(), |i: int| wire.subrange(ranges[i].start as int, ranges[i].end as int));
        pieces.take(ports as int).flatten() == wire.take(preceding_port_bits(widths, ports) as int)
    }),
    decreases ports,
{
    let ranges = layout.ranges_model();
    let pieces = Seq::new(widths.len(), |i: int| wire.subrange(ranges[i].start as int, ranges[i].end as int));
    port_bit_layout_size(widths, capacity, layout);
    if ports > 0 {
        let port = (ports - 1) as usize;
        port_bit_layout_port(widths, capacity, *layout, port);
        port_ranges_cover(widths, layout, capacity, wire, (ports - 1) as nat);
        let prefix = pieces.take(ports - 1);
        let range = ranges[port as int];
        assert(pieces.take(ports as int) =~= prefix.push(pieces[port as int]));
        prefix.lemma_flatten_push(pieces[port as int]);
        assert(wire.take(range.start as int) + wire.subrange(range.start as int, range.end as int)
            =~= wire.take(range.end as int));
    } else {
        reveal(preceding_port_bits);
        assert(pieces.take(0) =~= Seq::<Seq<Wire>>::empty());
        assert(wire.take(0) =~= Seq::<Wire>::empty());
    }
}

/// 宣言ポートごとに対応を示し、ソースの公開出力と最終配線を照合する。
pub(super) proof fn source_output_wires_agree(
    widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, capacity: usize,
    prior: Seq<Seq<SourceWire>>, flat: Seq<Wire>, order: Seq<SourceGateId>, outputs: Seq<u64>,
    drivers: Seq<OutputDriver>, wires: Seq<Wire>,
)
    requires
        body_definition_layouts(widths, definitions, capacity, layouts),
        port_bit_layout_result(outputs, capacity, Ok(layouts.outputs)),
        prior.len() == definitions.len(),
        flat.len() == preceding_port_bits(definition_widths(definitions), prior.len()),
        definition_wires_pair(order, prior, layouts.definitions.ranges_model(), flat),
        outputs.len() == drivers.len(),
        forall|port: int| 0 <= port < outputs.len() ==>
            bit_driver_width(widths, definitions, #[trigger] drivers[port]) == Some(outputs[port]),
        body_output_wiring_matches(drivers, layouts, flat, wires, outputs.len() as int),
        wires.len() == layouts.outputs.total_bits_model(),
    ensures source_wires_pair(order, source_output_wires(widths, prior, outputs, drivers), wires),
{
    port_bit_layout_size(outputs, capacity, &layouts.outputs);
    let ranges = layouts.outputs.ranges_model();
    let source = Seq::new(outputs.len(), |port: int| Seq::new(outputs[port] as nat, |bit: int|
        source_driver_wire(widths, prior, drivers[port], bit)));
    let pieces = Seq::new(outputs.len(), |port: int| wires.subrange(ranges[port].start as int, ranges[port].end as int));
    assert(definitions.take(prior.len() as int) =~= definitions);
    assert forall|i: int| 0 <= i < source.len() implies source_wires_pair(order, #[trigger] source[i], pieces[i]) by {
        let width = outputs[i];
        let driver = drivers[i];
        port_bit_layout_port(outputs, capacity, layouts.outputs, i as usize);
        let range = ranges[i];
        assert(range.start < range.end <= wires.len() && range.end - range.start == width);
        let a = source[i];
        let b = pieces[i];
        assert(a == Seq::new(width as nat, |bit: int| source_driver_wire(widths, prior, driver, bit)));
        assert(b == wires.subrange(range.start as int, range.end as int));
        assert(a.len() == b.len() == width);
        assert forall|bit: int| 0 <= bit < a.len() implies source_wire_pair(order, #[trigger] a[bit], b[bit]) by {
            source_driver_wire_agrees(widths, definitions, layouts, capacity, prior, flat, order, driver, bit, width);
            assert(a[bit] == source_driver_wire(widths, prior, driver, bit));
            assert(b[bit] == wires[range.start + bit]);
            assert(wires[range.start + bit] == driver_wire(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), flat, driver, bit));
        };
    };
    flatten_source_wire_pairs(order, source, pieces);
    port_ranges_cover(outputs, &layouts.outputs, capacity, wires, outputs.len());
    port_bit_layout_size(outputs, capacity, &layouts.outputs);
    assert(pieces.take(outputs.len() as int) =~= pieces);
    assert(wires.take(wires.len() as int) =~= wires);
}

} // verus!
