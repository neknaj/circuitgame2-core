//! インスタンス経路を使って、子の配線を親のソース回路に接続する。
//!
//! 直結の解はソースの定義出力を結ぶ関係で定める。
//! 実引数を代入したゲートと公開出力を、組み立て後の配線と照合する。

use super::super::clocked_plan::{
    ClockedWireDriver, clocked_alias_ranks, clocked_regions_cover, clocked_wire_at, clocked_wires_match,
};
use super::{
    ModuleCalls, OutputDriver, PrimitiveOperand, SourceInstance, UseAliases, child_driver_block_matches, child_output_driver,
    arguments_valid, assembled_gate_prefix, assembled_outputs, child_drivers_match, instance_assembled, instance_counts_match, instance_output_end,
    instance_output_slots, resolved_arguments, resolved_driver, symbolic_output,
};
use crate::netlist::{
    NorGate, NorNetlist, SourceGateId, SourceNor, SourceTickCircuit, SourceWire, Wire, clocked_wiring_endpoints,
    clocked_wiring_valid, source_clocked_layout, source_clocked_layout_from_pairs,
    source_gate_under, source_wire_in_parent, source_instance_gate_agrees, source_instance_order_at,
    source_output_pair_at, source_output_pairs, source_output_wiring_pair, source_wire_pair, wire_available,
};
use crate::project::DefinitionPosition;
use core::ops::Range;
use vstd::prelude::*;

mod hierarchy_layout;
mod reference;
pub(super) use hierarchy_layout::{ModuleSourceLayout, call_layout_is_ready, prior_layout_at};

verus! {

enum SourceLink {
    Terminal(SourceWire),
    Alias(usize),
}

spec fn source_links_resolved(links: Seq<SourceLink>, wires: Seq<SourceWire>, ranks: Seq<nat>) -> bool {
    &&& wires.len() == links.len() == ranks.len()
    &&& forall|i: int| 0 <= i < links.len() ==> match #[trigger] links[i] {
        SourceLink::Terminal(wire) => wires[i] == wire,
        SourceLink::Alias(target) => target < links.len() && ranks[target as int] < ranks[i] && wires[i] == wires[target as int],
    }
}

spec fn source_link_pair(order: Seq<SourceGateId>, source: SourceLink, flat: ClockedWireDriver) -> bool {
    match (source, flat) {
        (SourceLink::Terminal(original), ClockedWireDriver::Terminal(lowered)) => source_wire_pair(order, original, lowered),
        (SourceLink::Alias(original), ClockedWireDriver::Alias(lowered)) => original == lowered,
        _ => false,
    }
}

spec fn source_operand_link(operand: PrimitiveOperand) -> SourceLink {
    match operand {
        PrimitiveOperand::Driver(OutputDriver::Input(port)) => SourceLink::Terminal(SourceWire::Input(port)),
        PrimitiveOperand::Driver(OutputDriver::Definition(slot)) => SourceLink::Alias(slot),
        PrimitiveOperand::Literal(bit) => SourceLink::Terminal(SourceWire::Constant(bit)),
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn source_argument_link_matches(&self, checked: &ModuleCalls, call: int, arg: int, link: SourceLink) -> bool {
        exists|operand: PrimitiveOperand| #[trigger] self.primitive_operand_resolves(checked, call, arg, operand)
            && link == source_operand_link(operand)
    }

    spec fn source_argument_link_list(&self, checked: &ModuleCalls, call: int, flat: Seq<ClockedWireDriver>,
        links: Seq<SourceLink>, order: Seq<SourceGateId>) -> bool
    {
        &&& links.len() == flat.len()
        &&& forall|i: int| 0 <= i < links.len() ==> self.source_argument_link_matches(checked, call, i, #[trigger] links[i])
            && source_link_pair(order, links[i], flat[i])
    }

    proof fn source_argument_links(&self, checked: &ModuleCalls, call: int, arguments: Seq<ClockedWireDriver>,
        order: Seq<SourceGateId>) -> (links: Seq<SourceLink>)
        requires 0 <= call < checked.calls@.len(), self.source_arguments_match(checked, call, arguments),
        ensures self.source_argument_link_list(checked, call, arguments, links, order),
    {
        let operands = Seq::new(arguments.len(), |i: int| choose|operand: PrimitiveOperand|
            #[trigger] self.primitive_operand_resolves(checked, call, i, operand)
                && arguments[i] == match operand {
                    PrimitiveOperand::Driver(output) => symbolic_output(output),
                    PrimitiveOperand::Literal(bit) => ClockedWireDriver::Terminal(Wire::Constant(bit)),
                });
        let links = Seq::new(arguments.len(), |i: int| source_operand_link(operands[i]));
        assert forall|i: int| 0 <= i < links.len() implies self.source_argument_link_matches(checked, call, i, #[trigger] links[i])
            && source_link_pair(order, links[i], arguments[i]) by {
            assert(self.source_argument_matches(checked, call, i, arguments[i]));
            let operand = operands[i];
            assert(self.primitive_operand_resolves(checked, call, i, operand));
            assert(self.source_argument_link_matches(checked, call, i, links[i])) by {
                assert(links[i] == source_operand_link(operand));
            };
        };
        links
    }
}

spec fn wire_with_source_id(order: Seq<SourceGateId>, flat: Wire) -> SourceWire {
    match flat {
        Wire::Input(port) => SourceWire::Input(port),
        Wire::Constant(bit) => SourceWire::Constant(bit),
        Wire::Gate(i) => SourceWire::Gate(order[i as int]),
    }
}

spec fn source_link_value(link: SourceLink, wires: Seq<SourceWire>) -> SourceWire {
    match link {
        SourceLink::Terminal(wire) => wire,
        SourceLink::Alias(target) => wires[target as int],
    }
}

proof fn source_links_from_assembly(links: Seq<SourceLink>, drivers: Seq<ClockedWireDriver>, flat_wires: Seq<Wire>,
    order: Seq<SourceGateId>) -> (resolved: (Seq<SourceWire>, Seq<nat>))
    requires
        links.len() == drivers.len() == flat_wires.len(),
        clocked_wires_match(drivers, flat_wires),
        forall|i: int| 0 <= i < links.len() ==> source_link_pair(order, #[trigger] links[i], drivers[i]),
        forall|i: int| 0 <= i < flat_wires.len() ==>
            ((#[trigger] flat_wires[i]) matches Wire::Gate(gate) ==> gate < order.len()),
    ensures
        source_links_resolved(links, resolved.0, resolved.1),
        forall|i: int| 0 <= i < flat_wires.len() ==>
            source_wire_pair(order, #[trigger] resolved.0[i], flat_wires[i]),
{
    let ranks = clocked_alias_ranks(drivers, flat_wires);
    let wires = Seq::new(flat_wires.len(), |i: int| wire_with_source_id(order, flat_wires[i]));
    assert forall|i: int| 0 <= i < flat_wires.len() implies
        source_wire_pair(order, #[trigger] wires[i], flat_wires[i]) by {};
    assert forall|i: int| 0 <= i < links.len() implies match #[trigger] links[i] {
        SourceLink::Terminal(wire) => wires[i] == wire,
        SourceLink::Alias(target) => target < links.len() && ranks[target as int] < ranks[i] && wires[i] == wires[target as int],
    } by {
        assert(source_link_pair(order, links[i], drivers[i]));
        clocked_wire_at(drivers, flat_wires, i);
    };
    (wires, ranks)
}

proof fn source_argument_values(
    instance: SourceInstance, arguments: Seq<SourceLink>, wires: Seq<SourceWire>, flat_wires: Seq<Wire>,
    order: Seq<SourceGateId>,
) -> (values: Seq<SourceWire>)
    requires
        arguments.len() == instance.arguments@.len(),
        wires.len() == flat_wires.len(),
        forall|i: int| 0 <= i < arguments.len() ==> source_link_pair(order, #[trigger] arguments[i], instance.arguments@[i])
            && resolved_driver(instance.arguments@[i], flat_wires).is_some(),
        forall|i: int| 0 <= i < wires.len() ==> source_wire_pair(order, #[trigger] wires[i], flat_wires[i]),
    ensures
        values.len() == arguments.len(),
        forall|i: int| 0 <= i < arguments.len() ==>
            (#[trigger] values[i]) == source_link_value(arguments[i], wires)
            && source_wire_pair(order, values[i], resolved_arguments(instance, flat_wires)[i]),
{
    let values = Seq::new(arguments.len(), |i: int| source_link_value(arguments[i], wires));
    assert forall|i: int| 0 <= i < arguments.len() implies
        (#[trigger] values[i]) == source_link_value(arguments[i], wires)
        && source_wire_pair(order, values[i], resolved_arguments(instance, flat_wires)[i]) by {
        let argument = arguments[i];
        let driver = instance.arguments@[i];
        assert(source_link_pair(order, argument, driver));
        if let SourceLink::Alias(target) = argument {
            assert(resolved_driver(driver, flat_wires).is_some());
            assert(source_wire_pair(order, wires[target as int], flat_wires[target as int]));
        }
    };
    values
}

proof fn assembled_child_gate_with_source(
    instance: SourceInstance, prefix: Seq<DefinitionPosition>, child: &SourceTickCircuit,
    child_order: Seq<SourceGateId>, child_index: Map<SourceGateId, int>, source_arguments: Seq<SourceWire>,
    order: Seq<SourceGateId>, flat_wires: Seq<Wire>, gates: Seq<NorGate>, start: usize, gate: int,
) -> (source: SourceNor)
    requires
        0 <= gate < child_order.len(),
        source_clocked_layout(child, &instance.template.netlist_model(), child_order, child_index),
        instance_assembled(instance, start, flat_wires, gates),
        source_instance_order_at(prefix, child_order, order, start),
        source_arguments.len() == instance.template.netlist_model().input_count,
        resolved_arguments(instance, flat_wires).len() == source_arguments.len(),
        forall|i: int| 0 <= i < source_arguments.len() ==> source_wire_pair(order, #[trigger] source_arguments[i],
            resolved_arguments(instance, flat_wires)[i]),
    ensures
        start + gate < gates.len(),
        source.left == source_wire_in_parent(prefix, source_arguments, child.gates[child_order[gate]].left),
        source.right == source_wire_in_parent(prefix, source_arguments, child.gates[child_order[gate]].right),
        source_wire_pair(order, source.left, gates[start + gate].left),
        source_wire_pair(order, source.right, gates[start + gate].right),
{
    let netlist = instance.template.netlist_model();
    let flat_arguments = resolved_arguments(instance, flat_wires);
    source_instance_gate_agrees(prefix, child, &netlist, child_order, child_index, order, source_arguments,
        flat_arguments, gates, start, gate)
}

spec fn source_output_link(prefix: Seq<DefinitionPosition>, arguments: Seq<SourceLink>, wire: SourceWire) -> SourceLink {
    match wire {
        SourceWire::Input(port) => arguments[port as int],
        SourceWire::Constant(bit) => SourceLink::Terminal(SourceWire::Constant(bit)),
        SourceWire::Gate(gate) => SourceLink::Terminal(SourceWire::Gate(source_gate_under(prefix, gate))),
    }
}

proof fn assembled_child_output_with_source(
    instance: SourceInstance, prefix: Seq<DefinitionPosition>, child: &SourceTickCircuit,
    child_order: Seq<SourceGateId>, child_index: Map<SourceGateId, int>, arguments: Seq<SourceLink>,
    order: Seq<SourceGateId>, flat_drivers: Seq<ClockedWireDriver>, start: usize, port: int,
) -> (link: SourceLink)
    requires
        0 <= port < instance.template.netlist_model().outputs@.len(),
        source_clocked_layout(child, &instance.template.netlist_model(), child_order, child_index),
        child_driver_block_matches(instance, start, flat_drivers),
        instance.arguments@.len() == instance.template.netlist_model().input_count == arguments.len(),
        source_instance_order_at(prefix, child_order, order, start),
        forall|i: int| 0 <= i < arguments.len() ==>
            source_link_pair(order, #[trigger] arguments[i], instance.arguments@[i]),
    ensures
        link == source_output_link(prefix, arguments, child.outputs[port]),
        instance._output_start@ + port < flat_drivers.len(),
        source_link_pair(order, link, flat_drivers[instance._output_start@ + port]),
{
    let netlist = instance.template.netlist_model();
    let lowered = netlist.outputs@[port];
    source_output_wiring_pair(child, &netlist, child_order, child_index, port);
    assert(flat_drivers[instance._output_start@ + port] == child_output_driver(lowered, instance.arguments@, start));
    if let Wire::Gate(gate) = lowered {
        assert(order[start + gate] == source_gate_under(prefix, child_order[gate as int]));
    }
    source_output_link(prefix, arguments, child.outputs[port])
}

struct ChildSourceLayout {
    prefix: Seq<DefinitionPosition>,
    circuit: SourceTickCircuit,
    order: Seq<SourceGateId>,
    index: Map<SourceGateId, int>,
}

spec fn child_source_placement(instance: SourceInstance, layout: ChildSourceLayout, start: usize,
    order: Seq<SourceGateId>) -> bool
{
    &&& source_clocked_layout(&layout.circuit, &instance.template.netlist_model(), layout.order, layout.index)
    &&& layout.order.len() == instance.template.netlist_model().gates@.len()
    &&& source_instance_order_at(layout.prefix, layout.order, order, start)
}

spec fn all_child_source_placements(instances: Seq<SourceInstance>, layouts: Seq<ChildSourceLayout>,
    regions: Seq<Range<usize>>, order: Seq<SourceGateId>) -> bool
{
    &&& instances.len() == layouts.len() == regions.len()
    &&& forall|i: int| 0 <= i < instances.len() ==>
        #[trigger] child_source_placement(instances[i], layouts[i], regions[i].start, order)
}

spec fn instance_owns_output(instances: Seq<SourceInstance>, i: int, slot: int) -> bool {
    &&& 0 <= i < instances.len()
    &&& instances[i]._output_start@ <= slot < instances[i]._output_start@ + instances[i].output_sites@.len()
}

spec fn boundaries_in_order_at(boundary: Seq<int>, i: int) -> bool {
    0 <= boundary[i] <= boundary[i + 1]
}

spec fn interval_contains(boundary: Seq<int>, i: int, x: int) -> bool {
    boundary[i] <= x < boundary[i + 1]
}

// 空区間を含む連続した区間を扱う。各番号は半開区間に割り当てる。
proof fn interval_owner(boundary: Seq<int>, end: int, x: int) -> (owner: Option<int>)
    requires 0 <= end < boundary.len(), boundary[0] == 0,
        forall|i: int| 0 <= i < end ==> #[trigger] boundaries_in_order_at(boundary, i),
    ensures owner.is_some() <==> 0 <= x < boundary[end],
        owner matches Some(i) ==> 0 <= i < end,
        forall|i: int| 0 <= i < end ==> (#[trigger] interval_contains(boundary, i, x) <==> owner == Some(i)),
    decreases end,
{
    if end == 0 {
        None
    } else {
        let before = interval_owner(boundary, end - 1, x);
        assert(boundaries_in_order_at(boundary, end - 1));
        let owner = if interval_contains(boundary, end - 1, x) {
            assert(before.is_none());
            Some(end - 1)
        } else { before };
        assert forall|i: int| 0 <= i < end implies
            (#[trigger] interval_contains(boundary, i, x) <==> owner == Some(i)) by {
            if i == end - 1 { assert(before != Some(i)); }
        };
        owner
    }
}

proof fn instance_for_output(instances: Seq<SourceInstance>, slot: int) -> (i: int)
    requires 0 <= slot < instance_output_end(instances, instances.len() as int),
        instance_output_slots(instances, instance_output_end(instances, instances.len() as int)),
    ensures instance_owns_output(instances, i, slot),
        forall|j: int| #[trigger] instance_owns_output(instances, j, slot) ==> j == i,
{
    let end = instances.len() as int;
    let boundary = Seq::new(instances.len() + 1, |i: int| instance_output_end(instances, i));
    assert forall|j: int| 0 <= j < end implies #[trigger] boundaries_in_order_at(boundary, j) by {
        assert(instances[j]._output_start@ == instance_output_end(instances, j));
    };
    let owner = interval_owner(boundary, end, slot);
    let i = owner->Some_0;
    assert(interval_contains(boundary, i, slot));
    assert forall|j: int| #[trigger] instance_owns_output(instances, j, slot) implies j == i by {
        assert(interval_contains(boundary, j, slot));
    };
    i
}

spec fn instance_owns_gate(regions: Seq<Range<usize>>, i: int, gate: int) -> bool {
    &&& 0 <= i < regions.len()
    &&& regions[i].start <= gate < regions[i].end
}

proof fn instance_for_gate(counts: Seq<usize>, regions: Seq<Range<usize>>, total: usize, gate: int) -> (i: int)
    requires clocked_regions_cover(counts, regions, total), 0 <= gate < total,
    ensures instance_owns_gate(regions, i, gate),
        forall|j: int| #[trigger] instance_owns_gate(regions, j, gate) ==> j == i,
{
    let end = regions.len() as int;
    let boundary = Seq::new(regions.len() + 1, |i: int| if i == 0 { 0 } else { regions[i - 1].end as int });
    assert forall|j: int| 0 <= j < end implies #[trigger] boundaries_in_order_at(boundary, j) by {
        assert(regions[j].start == boundary[j]);
    };
    assert(boundary[end] == total);
    let owner = interval_owner(boundary, end, gate);
    let i = owner->Some_0;
    assert(interval_contains(boundary, i, gate));
    assert forall|j: int| #[trigger] instance_owns_gate(regions, j, gate) implies j == i by {
        assert(interval_contains(boundary, j, gate));
    };
    i
}

spec fn child_argument_links_valid(checked: &ModuleCalls, order: Seq<SourceGateId>, instances: Seq<SourceInstance>,
    arguments: Seq<Seq<SourceLink>>, aliases: &UseAliases) -> bool
{
    &&& arguments.len() == instances.len() == checked.calls@.len()
    &&& forall|i: int| 0 <= i < instances.len() ==>
        #[trigger] aliases.source_argument_link_list(checked, i, instances[i].arguments@, arguments[i], order)
}

spec fn source_outlet(layouts: Seq<ChildSourceLayout>, arguments: Seq<Seq<SourceLink>>, instances: Seq<SourceInstance>,
    i: int, slot: int) -> SourceLink
{
    let layout = layouts[i];
    let port = slot - instances[i]._output_start@;
    source_output_link(layout.prefix, arguments[i], layout.circuit.outputs[port])
}

spec fn outlet_follows_source_call(layouts: Seq<ChildSourceLayout>, arguments: Seq<Seq<SourceLink>>,
    instances: Seq<SourceInstance>, slot: int, link: SourceLink) -> bool
{
    exists|i: int| #[trigger] instance_owns_output(instances, i, slot) && link == source_outlet(layouts, arguments, instances, i, slot)
}

spec fn outlets_follow_source_calls(layouts: Seq<ChildSourceLayout>, arguments: Seq<Seq<SourceLink>>,
    instances: Seq<SourceInstance>, outlets: Seq<SourceLink>) -> bool
{
    forall|slot: int| 0 <= slot < outlets.len() ==> #[trigger]
        outlet_follows_source_call(layouts, arguments, instances, slot, outlets[slot])
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    proof fn source_child_arguments(&self, checked: &ModuleCalls, instances: Seq<SourceInstance>,
        order: Seq<SourceGateId>) -> (arguments: Seq<Seq<SourceLink>>)
        requires instances.len() == checked.calls@.len(),
            forall|i: int| 0 <= i < instances.len() ==> self.source_arguments_match(checked, i, (#[trigger] instances[i]).arguments@),
        ensures child_argument_links_valid(checked, order, instances, arguments, self),
    {
        let arguments = Seq::new(instances.len(), |i: int| choose|links: Seq<SourceLink>|
            #[trigger] self.source_argument_link_list(checked, i, instances[i].arguments@, links, order));
        assert forall|i: int| 0 <= i < instances.len() implies
            #[trigger] self.source_argument_link_list(checked, i, instances[i].arguments@, arguments[i], order) by {
            let witness = self.source_argument_links(checked, i, instances[i].arguments@, order);
            assert(self.source_argument_link_list(checked, i, instances[i].arguments@, witness, order));
        };
        arguments
    }
}

proof fn source_assembled_outlets(checked: &ModuleCalls, layouts: Seq<ChildSourceLayout>, order: Seq<SourceGateId>,
    instances: Seq<SourceInstance>, counts: Seq<usize>, regions: Seq<Range<usize>>, arguments: Seq<Seq<SourceLink>>,
    flat_drivers: Seq<ClockedWireDriver>, aliases: &UseAliases) -> (outlets: Seq<SourceLink>)
    requires
        instance_counts_match(instances, counts),
        instance_output_slots(instances, flat_drivers.len() as int),
        child_drivers_match(instances, regions, instances.len() as int, flat_drivers),
        all_child_source_placements(instances, layouts, regions, order),
        child_argument_links_valid(checked, order, instances, arguments, aliases),
    ensures
        outlets.len() == flat_drivers.len(),
        outlets_follow_source_calls(layouts, arguments, instances, outlets),
        forall|slot: int| 0 <= slot < outlets.len() ==> source_link_pair(order, #[trigger] outlets[slot], flat_drivers[slot]),
{
    let outlets = Seq::new(flat_drivers.len(), |slot: int| {
        let i = choose|i: int| #[trigger] instance_owns_output(instances, i, slot);
        source_outlet(layouts, arguments, instances, i, slot)
    });
    assert forall|slot: int| 0 <= slot < outlets.len() implies
        source_link_pair(order, #[trigger] outlets[slot], flat_drivers[slot]) by {
        let witness = instance_for_output(instances, slot);
        assert(instance_owns_output(instances, witness, slot));
        let i = choose|i: int| #[trigger] instance_owns_output(instances, i, slot);
        source_outlet_pair(checked, layouts, order, instances, counts, regions, arguments, flat_drivers, aliases, i, slot);
        assert(outlets[slot] == source_outlet(layouts, arguments, instances, i, slot));
    };
    assert forall|slot: int| 0 <= slot < outlets.len() implies #[trigger]
        outlet_follows_source_call(layouts, arguments, instances, slot, outlets[slot]) by {
        let i = instance_for_output(instances, slot);
        assert(outlets[slot] == source_outlet(layouts, arguments, instances, i, slot));
    };
    outlets
}

proof fn source_outlet_pair(checked: &ModuleCalls, layouts: Seq<ChildSourceLayout>, order: Seq<SourceGateId>,
    instances: Seq<SourceInstance>, counts: Seq<usize>, regions: Seq<Range<usize>>, arguments: Seq<Seq<SourceLink>>,
    flat_drivers: Seq<ClockedWireDriver>, aliases: &UseAliases, i: int, slot: int)
    requires
        instance_counts_match(instances, counts),
        child_drivers_match(instances, regions, instances.len() as int, flat_drivers),
        all_child_source_placements(instances, layouts, regions, order),
        child_argument_links_valid(checked, order, instances, arguments, aliases),
        instance_owns_output(instances, i, slot),
    ensures source_link_pair(order, source_outlet(layouts, arguments, instances, i, slot), flat_drivers[slot]),
{
    let instance = instances[i];
    let start = regions[i].start;
    let child = layouts[i];
    let port = slot - instance._output_start@;
    assert(child_source_placement(instance, child, start, order));
    assert(child_driver_block_matches(instance, start, flat_drivers));
    assert(aliases.source_argument_link_list(checked, i, instance.arguments@, arguments[i], order));
    let link = assembled_child_output_with_source(instance, child.prefix, &child.circuit, child.order,
        child.index, arguments[i], order, flat_drivers, start, port);
    assert(link == source_outlet(layouts, arguments, instances, i, slot));
}

struct SourceWiring {
    arguments: Seq<Seq<SourceLink>>,
    outlets: Seq<SourceLink>,
    wires: Seq<SourceWire>,
    ranks: Seq<nat>,
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    proof fn source_assembly_wiring(&self, checked: &ModuleCalls, layouts: Seq<ChildSourceLayout>,
        order: Seq<SourceGateId>, instances: Seq<SourceInstance>, counts: Seq<usize>, regions: Seq<Range<usize>>,
        flat_drivers: Seq<ClockedWireDriver>, flat_wires: Seq<Wire>) -> (source: SourceWiring)
        requires
            instance_counts_match(instances, counts),
            instances.len() == checked.calls@.len(),
            forall|i: int| 0 <= i < instances.len() ==> self.source_arguments_match(checked, i, (#[trigger] instances[i]).arguments@),
            instance_output_slots(instances, flat_drivers.len() as int),
            child_drivers_match(instances, regions, instances.len() as int, flat_drivers),
            all_child_source_placements(instances, layouts, regions, order),
            clocked_wires_match(flat_drivers, flat_wires), flat_drivers.len() == flat_wires.len(),
            forall|i: int| 0 <= i < flat_wires.len() ==>
                ((#[trigger] flat_wires[i]) matches Wire::Gate(gate) ==> gate < order.len()),
        ensures
            child_argument_links_valid(checked, order, instances, source.arguments, self),
            source_links_resolved(source.outlets, source.wires, source.ranks),
            source.outlets.len() == flat_drivers.len() == source.wires.len(),
            outlets_follow_source_calls(layouts, source.arguments, instances, source.outlets),
            forall|i: int| 0 <= i < flat_wires.len() ==>
                source_wire_pair(order, #[trigger] source.wires[i], flat_wires[i]),
    {
        let arguments = self.source_child_arguments(checked, instances, order);
        let outlets = source_assembled_outlets(checked, layouts, order, instances, counts, regions, arguments, flat_drivers, self);
        let (wires, ranks) = source_links_from_assembly(outlets, flat_drivers, flat_wires, order);
        SourceWiring { arguments, outlets, wires, ranks }
    }
}

spec fn gate_in_parent(layout: ChildSourceLayout, arguments: Seq<SourceLink>, wires: Seq<SourceWire>, gate: int) -> SourceNor {
    let values = Seq::new(arguments.len(), |i: int| source_link_value(arguments[i], wires));
    let original = layout.circuit.gates[layout.order[gate]];
    SourceNor {
        left: source_wire_in_parent(layout.prefix, values, original.left),
        right: source_wire_in_parent(layout.prefix, values, original.right),
    }
}

spec fn gate_follows_source_call(layouts: Seq<ChildSourceLayout>, wiring: SourceWiring, regions: Seq<Range<usize>>,
    gate: int, source: SourceNor) -> bool
{
    exists|i: int| #[trigger] instance_owns_gate(regions, i, gate)
        && source == gate_in_parent(layouts[i], wiring.arguments[i], wiring.wires, gate - regions[i].start)
}

proof fn source_assembled_gates(checked: &ModuleCalls, layouts: Seq<ChildSourceLayout>, order: Seq<SourceGateId>,
    instances: Seq<SourceInstance>, counts: Seq<usize>, regions: Seq<Range<usize>>, source: SourceWiring, flat_wires: Seq<Wire>,
    gates: Seq<NorGate>, aliases: &UseAliases) -> (source_gates: Seq<SourceNor>)
    requires
        instance_counts_match(instances, counts),
        all_child_source_placements(instances, layouts, regions, order),
        order.len() == gates.len() <= usize::MAX, clocked_regions_cover(counts, regions, gates.len() as usize),
        assembled_gate_prefix(instances, regions, flat_wires, gates, instances.len() as int),
        child_argument_links_valid(checked, order, instances, source.arguments, aliases),
        source.wires.len() == flat_wires.len(),
        forall|i: int| 0 <= i < flat_wires.len() ==> source_wire_pair(order, #[trigger] source.wires[i], flat_wires[i]),
    ensures
        source_gates.len() == gates.len(),
        forall|gate: int| 0 <= gate < source_gates.len() ==> {
            let formed = #[trigger] source_gates[gate];
            &&& source_wire_pair(order, formed.left, gates[gate].left)
            &&& source_wire_pair(order, formed.right, gates[gate].right)
            &&& gate_follows_source_call(layouts, source, regions, gate, formed)
        },
{
    let source_gates = Seq::new(gates.len(), |gate: int| {
        let i = choose|i: int| #[trigger] instance_owns_gate(regions, i, gate);
        gate_in_parent(layouts[i], source.arguments[i], source.wires, gate - regions[i].start)
    });
    assert forall|gate: int| 0 <= gate < source_gates.len() implies {
        let formed = #[trigger] source_gates[gate];
        &&& source_wire_pair(order, formed.left, gates[gate].left)
        &&& source_wire_pair(order, formed.right, gates[gate].right)
        &&& gate_follows_source_call(layouts, source, regions, gate, formed)
    } by {
        let witness = instance_for_gate(counts, regions, gates.len() as usize, gate);
        assert(instance_owns_gate(regions, witness, gate));
        let i = choose|i: int| #[trigger] instance_owns_gate(regions, i, gate);
        let child = layouts[i];
        let instance = instances[i];
        let start = regions[i].start;
        let local_gate = gate - start;
        assert(instance_assembled(instance, start, flat_wires, gates));
        assert(arguments_valid(instance, flat_wires));
        let arguments = source.arguments[i];
        assert(aliases.source_argument_link_list(checked, i, instance.arguments@, arguments, order));
        assert forall|j: int| 0 <= j < arguments.len() implies
            source_link_pair(order, #[trigger] arguments[j], instance.arguments@[j])
            && resolved_driver(instance.arguments@[j], flat_wires).is_some() by {};
        let values = source_argument_values(instance, arguments, source.wires, flat_wires, order);
        assert(values =~= Seq::new(arguments.len(), |j: int| source_link_value(arguments[j], source.wires)));
        assert(child_source_placement(instance, child, start, order));
        assert(regions[i].end - start == counts[i] == child.order.len());
        let formed = assembled_child_gate_with_source(instance, child.prefix, &child.circuit, child.order, child.index, values,
            order, flat_wires, gates, start, local_gate);
        assert(formed == source_gates[gate]);
    };
    source_gates
}

proof fn source_assembled_outputs(definitions: Seq<OutputDriver>, order: Seq<SourceGateId>,
    wires: Seq<SourceWire>, flat_wires: Seq<Wire>, flat_outputs: Seq<Wire>) -> (outputs: Seq<SourceWire>)
    requires
        wires.len() == flat_wires.len(), definitions.len() == flat_outputs.len(),
        assembled_outputs(definitions, flat_wires, flat_outputs),
        forall|i: int| 0 <= i < flat_wires.len() ==> source_wire_pair(order, #[trigger] wires[i], flat_wires[i]),
    ensures
        outputs.len() == definitions.len(),
        forall|i: int| 0 <= i < outputs.len() ==> {
            let wire = #[trigger] outputs[i];
            &&& wire == source_link_value(source_operand_link(PrimitiveOperand::Driver(definitions[i])), wires)
            &&& source_wire_pair(order, wire, flat_outputs[i])
        },
{
    let outputs = Seq::new(definitions.len(),
        |i: int| source_link_value(source_operand_link(PrimitiveOperand::Driver(definitions[i])), wires));
    assert forall|i: int| 0 <= i < outputs.len() implies
        source_wire_pair(order, #[trigger] outputs[i], flat_outputs[i]) by {
        assert(Some(flat_outputs[i]) == resolved_driver(symbolic_output(definitions[i]), flat_wires));
        if let OutputDriver::Definition(slot) = definitions[i] {
            assert(slot < flat_wires.len());
            assert(source_wire_pair(order, wires[slot as int], flat_wires[slot as int]));
        }
    };
    outputs
}

struct SourceAssembly {
    circuit: SourceTickCircuit,
    index: Map<SourceGateId, int>,
    wiring: SourceWiring,
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    // 親のゲート入力と公開出力に同じ配線の解を使い、VM の配線との対応を示す。
    proof fn source_circuit_from_assembly(&self, checked: &ModuleCalls, layouts: Seq<ChildSourceLayout>,
        order: Seq<SourceGateId>, instances: Seq<SourceInstance>, counts: Seq<usize>, regions: Seq<Range<usize>>,
        flat_drivers: Seq<ClockedWireDriver>, flat_wires: Seq<Wire>, netlist: &NorNetlist) -> (source: SourceAssembly)
        requires
            instance_counts_match(instances, counts),
            instances.len() == checked.calls@.len(),
            forall|i: int| 0 <= i < instances.len() ==> self.source_arguments_match(checked, i, (#[trigger] instances[i]).arguments@),
            instance_output_slots(instances, flat_drivers.len() as int),
            flat_drivers.len() == checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len(),
            child_drivers_match(instances, regions, instances.len() as int, flat_drivers),
            all_child_source_placements(instances, layouts, regions, order),
            clocked_regions_cover(counts, regions, netlist.gates@.len() as usize),
            order.len() == netlist.gates@.len() <= usize::MAX,
            forall|i: int, j: int| 0 <= i < j < order.len() ==> #[trigger] order[i] != #[trigger] order[j],
            clocked_wiring_valid(netlist),
            clocked_wires_match(flat_drivers, flat_wires), flat_drivers.len() == flat_wires.len(),
            forall|i: int| 0 <= i < flat_wires.len() ==>
                ((#[trigger] flat_wires[i]) matches Wire::Gate(gate) ==> gate < order.len()),
            assembled_gate_prefix(instances, regions, flat_wires, netlist.gates@, instances.len() as int),
            netlist.outputs@.len() == checked.module.expressions.typed.sources.roots.wiring.drivers.outputs@.len(),
            netlist.input_count == checked.module.expressions.typed.sources.roots.wiring.drivers.signature.inputs@.len(),
            assembled_outputs(checked.module.expressions.typed.sources.roots.wiring.drivers.outputs@, flat_wires, netlist.outputs@),
        ensures
            source_clocked_layout(&source.circuit, netlist, order, source.index),
            child_argument_links_valid(checked, order, instances, source.wiring.arguments, self),
            source_links_resolved(source.wiring.outlets, source.wiring.wires, source.wiring.ranks),
            source.wiring.outlets.len() == checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len(),
            outlets_follow_source_calls(layouts, source.wiring.arguments, instances, source.wiring.outlets),
            forall|gate: int| 0 <= gate < order.len() ==> #[trigger]
                gate_follows_source_call(layouts, source.wiring, regions, gate, source.circuit.gates[order[gate]]),
            forall|port: int| 0 <= port < source.circuit.outputs.len() ==>
                (#[trigger] source.circuit.outputs[port]) == source_link_value(source_operand_link(PrimitiveOperand::Driver(
                    checked.module.expressions.typed.sources.roots.wiring.drivers.outputs@[port])), source.wiring.wires),
    {
        let wiring = self.source_assembly_wiring(checked, layouts, order, instances, counts, regions, flat_drivers, flat_wires);
        let gates = source_assembled_gates(checked, layouts, order, instances, counts, regions, wiring, flat_wires, netlist.gates@, self);
        let outputs = source_assembled_outputs(checked.module.expressions.typed.sources.roots.wiring.drivers.outputs@,
            order, wiring.wires, flat_wires, netlist.outputs@);
        let index = Map::new(order.to_set(), |site: SourceGateId| order.index_of(site));
        let circuit = SourceTickCircuit {
            input_count: netlist.input_count,
            gates: Map::new(index.dom(), |site: SourceGateId| gates[index[site]]),
            outputs,
        };
        order.to_set_ensures();
        clocked_wiring_endpoints(netlist);
        assert forall|site: SourceGateId| index.dom().contains(site) implies
            0 <= #[trigger] index[site] < order.len() && order[index[site]] == site by {
            assert(order.contains(site));
        };
        assert forall|i: int| 0 <= i < order.len() implies {
            let site = #[trigger] order[i];
            let flat = netlist.gates@[i];
            &&& index.dom().contains(site) && index[site] == i
            &&& wire_available(flat.left, netlist.input_count as nat, order.len())
            &&& wire_available(flat.right, netlist.input_count as nat, order.len())
            &&& source_wire_pair(order, circuit.gates[site].left, flat.left)
            &&& source_wire_pair(order, circuit.gates[site].right, flat.right)
        } by {
            let site = order[i];
            assert(index.dom().contains(site));
            assert(order[index[site]] == site);
            assert(index[site] == i);
            assert(circuit.gates[site] == gates[i]);
        };
        assert forall|i: int| 0 <= i < order.len() implies #[trigger]
            gate_follows_source_call(layouts, wiring, regions, i, circuit.gates[order[i]]) by {
            assert(gates[i] == circuit.gates[order[i]]);
        };
        assert(source_output_pairs(&circuit, netlist, order)) by {
            assert forall|port: int| 0 <= port < outputs.len() implies
                #[trigger] source_output_pair_at(&circuit, netlist, order, port) by {
                assert(source_wire_pair(order, outputs[port], netlist.outputs@[port]));
            };
        };
        source_clocked_layout_from_pairs(&circuit, netlist, order, index);
        SourceAssembly { circuit, index, wiring }
    }
}

} // verus!
