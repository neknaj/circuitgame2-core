//! 検査済みのソースと子回路から、親回路の配線を定める。

use super::{
    ChildSourceLayout, SourceAssembly, SourceLink, SourceWiring, child_argument_links_valid,
    child_source_placement, gate_follows_source_call, gate_in_parent, instance_for_gate,
    instance_owns_gate, instance_owns_output, outlet_follows_source_call, outlets_follow_source_calls,
    source_gate_under, source_link_value, source_links_resolved, source_operand_link, source_outlet, source_output_link,
    source_wire_in_parent,
};
use super::super::{SourceInstance, instance_counts_match, output_driver_matches};
use super::super::super::{clocked_plan::clocked_regions_cover, primitive_nor::one_bit_ports};
use super::hierarchy_layout::{builtin_source, child_layout_uses_call, child_source_at_call};
use crate::netlist::{ClockedNor, NorNetlist, SourceGateId, SourceNor, SourceTickCircuit, source_clocked_layout,
    source_gate_wiring_pair, source_trace_gate_index, source_trace_layout_counts, source_wiring_valid, source_clocked_layout_valid};
use crate::project::{DefinitionPosition, ModuleCallTarget, ModuleCalls, UseAliases};
use super::PrimitiveOperand;
use core::ops::Range;
use vstd::prelude::*;

verus! {

pub(in crate::project::use_aliases::module_types::clocked_source) struct SourceLayer {
    children: Seq<SourceTickCircuit>,
    wiring: SourceWiring,
}

impl SourceLayer {
    pub(in crate::project::use_aliases::module_types::clocked_source) closed spec fn children_model(&self)
        -> Seq<SourceTickCircuit>
    {
        self.children
    }
}

spec fn call_prefix(checked: &ModuleCalls, i: int) -> Seq<DefinitionPosition> {
    let call = checked.calls@[i];
    if call.inputs.ports.signature.target is Nor { Seq::empty() } else { seq![call.at] }
}

spec fn source_child_kind(checked: &ModuleCalls, i: int, child: SourceTickCircuit) -> bool {
    let call = checked.calls@[i];
    match call.inputs.ports.signature.target {
        ModuleCallTarget::Nor => child == builtin_source(call.at).circuit,
        ModuleCallTarget::Routine { .. } => true,
        ModuleCallTarget::StateElement { .. } => false,
    }
}

spec fn source_operand_list(aliases: &UseAliases, checked: &ModuleCalls, i: int, arguments: Seq<SourceLink>) -> bool {
    &&& arguments.len() == checked.calls@[i].inputs.ports.arguments@.len()
    &&& forall|j: int| 0 <= j < arguments.len() ==>
        aliases.source_argument_link_matches(checked, i, j, #[trigger] arguments[j])
}

spec fn named_child_output(aliases: &UseAliases, checked: &ModuleCalls, layer: &SourceLayer, slot: int,
    i: int, port: int) -> bool
{
    let call = checked.calls@[i];
    let parsed = aliases.targets.project_model().circuits_model()[call.at.file as int];
    let definition = parsed.entry_ranges@[call.at.entry as int].definitions.start + call.at.definition;
    let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
    &&& 0 <= i < checked.calls@.len() && i < layer.children.len()
    &&& 0 <= port < layer.children[i].outputs.len()
    &&& call.at.reference == 0 && parsed.definitions@[definition].expression.start == call.inputs.ports.signature.call.form
    &&& output_driver_matches(&drivers, call.at, definition as usize, slot, port)
}

spec fn reference_outlet_at(aliases: &UseAliases, checked: &ModuleCalls, layer: &SourceLayer, slot: int) -> bool {
    exists|i: int, port: int| #[trigger] named_child_output(aliases, checked, layer, slot, i, port)
        && layer.wiring.outlets[slot] == source_output_link(call_prefix(checked, i), layer.wiring.arguments[i],
            layer.children[i].outputs[port])
}

spec fn gate_by_source_call(checked: &ModuleCalls, layer: &SourceLayer, i: int, site: SourceGateId) -> SourceNor {
    let child = layer.children[i].gates[site];
    let args = layer.wiring.arguments[i];
    let values = Seq::new(args.len(), |arg: int| source_link_value(args[arg], layer.wiring.wires));
    let prefix = call_prefix(checked, i);
    SourceNor {
        left: source_wire_in_parent(prefix, values, child.left),
        right: source_wire_in_parent(prefix, values, child.right),
    }
}

spec fn source_child_has_gate(layer: &SourceLayer, i: int, site: SourceGateId) -> bool {
    0 <= i < layer.children.len() && layer.children[i].gates.dom().contains(site)
}

spec fn placed_source_gate(checked: &ModuleCalls, layer: &SourceLayer, circuit: &SourceTickCircuit,
    i: int, site: SourceGateId) -> bool
{
    let at = source_gate_under(call_prefix(checked, i), site);
    circuit.gates.dom().contains(at) && circuit.gates[at] == gate_by_source_call(checked, layer, i, site)
}

spec fn parent_gate_has_origin(checked: &ModuleCalls, layer: &SourceLayer, site: SourceGateId) -> bool {
    exists|i: int, origin: SourceGateId| #[trigger] source_child_has_gate(layer, i, origin)
        && site == source_gate_under(call_prefix(checked, i), origin)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(in crate::project::use_aliases::module_types::clocked_source) closed spec fn module_source_layer(
        &self, checked: &ModuleCalls, circuit: &SourceTickCircuit, layer: &SourceLayer,
    ) -> bool {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        &&& one_bit_ports(drivers.signature.inputs@, drivers.signature.inputs@.len() as int)
        &&& one_bit_ports(drivers.signature.outputs@, drivers.signature.outputs@.len() as int)
        &&& layer.children.len() == layer.wiring.arguments.len() == checked.calls@.len()
        &&& circuit.input_count == drivers.signature.inputs@.len()
        &&& circuit.outputs.len() == drivers.outputs@.len()
        &&& source_wiring_valid(circuit)
        &&& forall|i: int| 0 <= i < layer.children.len() ==>
            source_child_kind(checked, i, #[trigger] layer.children[i])
            && source_operand_list(self, checked, i, layer.wiring.arguments[i])
        &&& source_links_resolved(layer.wiring.outlets, layer.wiring.wires, layer.wiring.ranks)
        &&& layer.wiring.outlets.len() == drivers.definitions@.len()
        &&& forall|slot: int| 0 <= slot < layer.wiring.outlets.len() ==>
            #[trigger] reference_outlet_at(self, checked, layer, slot)
        &&& forall|i: int, site: SourceGateId| #[trigger] source_child_has_gate(layer, i, site)
            ==> placed_source_gate(checked, layer, circuit, i, site)
        &&& forall|site: SourceGateId| #[trigger] circuit.gates.dom().contains(site)
            ==> parent_gate_has_origin(checked, layer, site)
        &&& forall|port: int| 0 <= port < circuit.outputs.len() ==>
            (#[trigger] circuit.outputs[port]) == source_link_value(
                source_operand_link(PrimitiveOperand::Driver(drivers.outputs@[port])), layer.wiring.wires)
    }

    pub(in crate::project::use_aliases::module_types::clocked_source) proof fn source_layer_call_supported(
        &self, checked: &ModuleCalls, circuit: &SourceTickCircuit, layer: &SourceLayer, i: int,
    )
        requires self.module_source_layer(checked, circuit, layer), 0 <= i < checked.calls@.len(),
        ensures checked.calls@[i].inputs.ports.signature.target is Nor
            || checked.calls@[i].inputs.ports.signature.target is Routine,
    {
        assert(source_child_kind(checked, i, layer.children[i]));
    }

    proof fn reference_output_at(&self, checked: &ModuleCalls, source: &SourceLayer,
        layouts: Seq<ChildSourceLayout>, instances: Seq<SourceInstance>, counts: Seq<usize>,
        edges: Seq<Option<usize>>, templates: Seq<Option<ClockedNor>>, builtin: &ClockedNor, slot: int)
        requires
            instance_counts_match(instances, counts),
            self.instances_match_source_calls(checked, instances, edges, templates, builtin),
            instances.len() == checked.calls@.len() == layouts.len() == source.children.len(),
            forall|i: int| 0 <= i < layouts.len() ==> #[trigger]
                child_layout_uses_call(checked, i, layouts[i], &instances[i].template.netlist_model()),
            forall|i: int| 0 <= i < layouts.len() ==> #[trigger] source.children[i] == layouts[i].circuit,
            0 <= slot < source.wiring.outlets.len(),
            outlet_follows_source_call(layouts, source.wiring.arguments, instances, slot, source.wiring.outlets[slot]),
        ensures reference_outlet_at(self, checked, source, slot),
    {
        let i = choose|i: int| #[trigger] instance_owns_output(instances, i, slot)
            && source.wiring.outlets[slot] == source_outlet(layouts, source.wiring.arguments, instances, i, slot);
        let instance = instances[i];
        let layout = layouts[i];
        let template = instance.template.netlist_model();
        let port = slot - instance._output_start@;
        let call = checked.calls@[i];
        let parsed = self.targets.project_model().circuits_model()[call.at.file as int];
        let definition = parsed.entry_ranges@[call.at.entry as int].definitions.start + call.at.definition;
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        child_source_at_call(checked, i, layout, &template);
        assert(layout.prefix == call_prefix(checked, i));
        source_trace_layout_counts(&layout.circuit, &template, layout.order, layout.index);
        assert(source.children[i] == layout.circuit);
        assert(self.instance_matches_source_call(checked, i, instance, edges[i], templates, builtin));
        assert(0 <= port < instance.output_sites@.len() == source.children[i].outputs.len());
        assert(instance.output_sites@[port].span == drivers.definitions@[slot].name.span);
        assert(output_driver_matches(&drivers, call.at, definition as usize, slot, port));
        assert(named_child_output(self, checked, source, slot, i, port));
    }

    pub(super) proof fn reference_layer_from_assembly(&self, checked: &ModuleCalls, source: &SourceAssembly,
        layouts: Seq<ChildSourceLayout>, instances: Seq<SourceInstance>, counts: Seq<usize>,
        regions: Seq<Range<usize>>, order: Seq<SourceGateId>, netlist: &NorNetlist, edges: Seq<Option<usize>>,
        templates: Seq<Option<ClockedNor>>, builtin: &ClockedNor) -> (layer: SourceLayer)
        requires
            instance_counts_match(instances, counts),
            self.instances_match_source_calls(checked, instances, edges, templates, builtin),
            instances.len() == checked.calls@.len() == layouts.len() == regions.len(),
            forall|i: int| 0 <= i < layouts.len() ==> #[trigger]
                child_layout_uses_call(checked, i, layouts[i], &instances[i].template.netlist_model()),
            super::all_child_source_placements(instances, layouts, regions, order),
            order.len() <= usize::MAX, clocked_regions_cover(counts, regions, order.len() as usize),
            source_clocked_layout(&source.circuit, netlist, order, source.index),
            child_argument_links_valid(checked, order, instances, source.wiring.arguments, self),
            source_links_resolved(source.wiring.outlets, source.wiring.wires, source.wiring.ranks),
            source.wiring.outlets.len() == checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len(),
            outlets_follow_source_calls(layouts, source.wiring.arguments, instances, source.wiring.outlets),
            forall|gate: int| 0 <= gate < order.len() ==> #[trigger]
                gate_follows_source_call(layouts, source.wiring, regions, gate, source.circuit.gates[order[gate]]),
            source.circuit.input_count == checked.module.expressions.typed.sources.roots.wiring.drivers.signature.inputs@.len(),
            source.circuit.outputs.len() == checked.module.expressions.typed.sources.roots.wiring.drivers.outputs@.len(),
            ({
                let signature = checked.module.expressions.typed.sources.roots.wiring.drivers.signature;
                &&& one_bit_ports(signature.inputs@, signature.inputs@.len() as int)
                &&& one_bit_ports(signature.outputs@, signature.outputs@.len() as int)
            }),
            forall|port: int| 0 <= port < source.circuit.outputs.len() ==>
                (#[trigger] source.circuit.outputs[port]) == source_link_value(source_operand_link(PrimitiveOperand::Driver(
                    checked.module.expressions.typed.sources.roots.wiring.drivers.outputs@[port])), source.wiring.wires),
        ensures self.module_source_layer(checked, &source.circuit, &layer),
            layer.children_model().len() == layouts.len(),
            forall|i: int| 0 <= i < layouts.len() ==> (#[trigger] layer.children_model()[i]) == layouts[i].circuit,
    {
        let layer = SourceLayer {
            children: Seq::new(layouts.len(), |i: int| layouts[i].circuit),
            wiring: source.wiring,
        };
        source_clocked_layout_valid(&source.circuit, netlist, order, source.index);
        assert forall|i: int| 0 <= i < layer.children.len() implies
            source_child_kind(checked, i, #[trigger] layer.children[i])
                && source_operand_list(self, checked, i, layer.wiring.arguments[i]) by {
            let instance = instances[i];
            let model = instance.template.netlist_model();
            child_source_at_call(checked, i, layouts[i], &model);
            assert(self.instance_matches_source_call(checked, i, instance, edges[i], templates, builtin));
            assert(self.source_argument_link_list(checked, i, instance.arguments@, layer.wiring.arguments[i], order));
        };
        assert forall|slot: int| 0 <= slot < layer.wiring.outlets.len() implies
            #[trigger] reference_outlet_at(self, checked, &layer, slot) by {
            assert(outlet_follows_source_call(layouts, layer.wiring.arguments, instances, slot, layer.wiring.outlets[slot]));
            self.reference_output_at(checked, &layer, layouts, instances, counts, edges, templates, builtin, slot);
        };
        assert forall|i: int, site: SourceGateId| #[trigger] source_child_has_gate(&layer, i, site) implies
            placed_source_gate(checked, &layer, &source.circuit, i, site) by {
            placed_gate_matches(checked, &layer, source, layouts, instances, counts, regions, order, netlist, i, site);
        };
        assert forall|site: SourceGateId| #[trigger] source.circuit.gates.dom().contains(site) implies
            parent_gate_has_origin(checked, &layer, site) by {
            parent_gate_origin(checked, &layer, source, layouts, instances, counts, regions, order, netlist, site);
        };
        layer
    }
}

proof fn placed_gate_matches(checked: &ModuleCalls, layer: &SourceLayer, source: &SourceAssembly,
    layouts: Seq<ChildSourceLayout>, instances: Seq<SourceInstance>, counts: Seq<usize>, regions: Seq<Range<usize>>,
    order: Seq<SourceGateId>, netlist: &NorNetlist, i: int, site: SourceGateId)
    requires
        instance_counts_match(instances, counts), layouts.len() == instances.len() == layer.children.len() == checked.calls@.len(),
        super::all_child_source_placements(instances, layouts, regions, order),
        order.len() <= usize::MAX, clocked_regions_cover(counts, regions, order.len() as usize),
        source_clocked_layout(&source.circuit, netlist, order, source.index),
        source_child_has_gate(layer, i, site), layer.children[i] == layouts[i].circuit, layer.wiring == source.wiring,
        child_layout_uses_call(checked, i, layouts[i], &instances[i].template.netlist_model()),
        forall|gate: int| 0 <= gate < order.len() ==> #[trigger]
            gate_follows_source_call(layouts, source.wiring, regions, gate, source.circuit.gates[order[gate]]),
    ensures placed_source_gate(checked, layer, &source.circuit, i, site),
{
    let child = layouts[i];
    let template = instances[i].template.netlist_model();
    child_source_at_call(checked, i, child, &template);
    assert(child.prefix == call_prefix(checked, i));
    source_trace_gate_index(&child.circuit, &template, child.order, child.index, site);
    let start = regions[i].start;
    let local = child.index[site];
    let at = start + local;
    assert(child_source_placement(instances[i], child, start, order));
    assert(order[at] == source_gate_under(child.prefix, site));
    assert(regions[i].end - start == child.order.len());
    source_gate_wiring_pair(&source.circuit, netlist, order, source.index, at);
    let mapped = source.circuit.gates[order[at]];
    assert(gate_follows_source_call(layouts, source.wiring, regions, at, mapped));
    let found = choose|j: int| #[trigger] instance_owns_gate(regions, j, at)
        && mapped == gate_in_parent(layouts[j], source.wiring.arguments[j], source.wiring.wires, at - regions[j].start);
    let owner = instance_for_gate(counts, regions, order.len() as usize, at);
    assert(instance_owns_gate(regions, i, at));
    assert(i == owner && found == owner);
    assert(mapped == gate_by_source_call(checked, layer, i, site));
}

proof fn parent_gate_origin(checked: &ModuleCalls, layer: &SourceLayer, source: &SourceAssembly,
    layouts: Seq<ChildSourceLayout>, instances: Seq<SourceInstance>, counts: Seq<usize>, regions: Seq<Range<usize>>,
    order: Seq<SourceGateId>, netlist: &NorNetlist, site: SourceGateId)
    requires
        instance_counts_match(instances, counts),
        layouts.len() == instances.len() == layer.children.len() == checked.calls@.len(),
        super::all_child_source_placements(instances, layouts, regions, order),
        order.len() <= usize::MAX, clocked_regions_cover(counts, regions, order.len() as usize),
        source_clocked_layout(&source.circuit, netlist, order, source.index), source.circuit.gates.dom().contains(site),
        forall|i: int| 0 <= i < layouts.len() ==> #[trigger] child_layout_uses_call(checked, i, layouts[i],
            &instances[i].template.netlist_model()),
        forall|i: int| 0 <= i < layouts.len() ==> #[trigger] layer.children[i] == layouts[i].circuit,
    ensures parent_gate_has_origin(checked, layer, site),
{
    source_trace_gate_index(&source.circuit, netlist, order, source.index, site);
    let gate = source.index[site];
    let i = instance_for_gate(counts, regions, order.len() as usize, gate);
    let child = layouts[i];
    let start = regions[i].start;
    assert(child_source_placement(instances[i], child, start, order));
    assert(regions[i].end - start == child.order.len());
    gate_origin_in_child(checked, layer, instances[i], child, order, start, i, gate - start, site);
}

proof fn gate_origin_in_child(checked: &ModuleCalls, layer: &SourceLayer, instance: SourceInstance,
    child: ChildSourceLayout, order: Seq<SourceGateId>, start: usize, i: int, local: int, site: SourceGateId)
    requires
        0 <= i < layer.children.len() == checked.calls@.len(),
        child_source_placement(instance, child, start, order),
        child_layout_uses_call(checked, i, child, &instance.template.netlist_model()),
        layer.children[i] == child.circuit,
        0 <= local < child.order.len(), order[start + local] == site,
    ensures parent_gate_has_origin(checked, layer, site),
{
    let template = instance.template.netlist_model();
    child_source_at_call(checked, i, child, &template);
    source_gate_wiring_pair(&child.circuit, &template, child.order, child.index, local);
    assert(source_child_has_gate(layer, i, child.order[local]));
    assert(child.prefix == call_prefix(checked, i));
    assert(site == source_gate_under(child.prefix, child.order[local]));
}

} // verus!
