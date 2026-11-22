//! 厳格索引の呼び出し位置を使って、親子のゲートを対応付ける。

use super::{ChildSourceLayout, all_child_source_placements, child_source_placement, instance_for_gate,
    instance_owns_gate, source_gate_under};
use super::reference::SourceLayer;
use super::super::{SourceInstance, assembled_gate_prefix, assembled_outputs, builtin_nor_template, child_drivers_match,
    instance_counts_match, instance_output_slots, source_assembly_matches};
use super::super::super::clocked_plan::{ClockedWireDriver, clocked_regions_cover, clocked_wires_match};
use crate::netlist::{ClockedNor, NorNetlist, SourceGateId, SourceNor, SourceTickCircuit, SourceWire, Wire,
    source_clocked_layout, source_clocked_layout_from_pairs, source_gate_positions_distinct, source_output_pair_at, wire_available};
use crate::project::{DefinitionPosition, ModuleBodyPosition, ModuleCallTarget, ModuleCalls, UseAliases};
use core::ops::Range;
use vstd::prelude::*;

verus! {

pub(in crate::project::use_aliases::module_types::clocked_source) struct ModuleSourceLayout {
    pub(in crate::project::use_aliases::module_types::clocked_source) owner: ModuleBodyPosition,
    pub(in crate::project::use_aliases::module_types::clocked_source) circuit: SourceTickCircuit,
    pub(in crate::project::use_aliases::module_types::clocked_source) order: Seq<SourceGateId>,
    pub(in crate::project::use_aliases::module_types::clocked_source) index: Map<SourceGateId, int>,
    pub(in crate::project::use_aliases::module_types::clocked_source) layer: SourceLayer,
}

pub(in crate::project::use_aliases::module_types::clocked_source) open spec fn prior_layout_at(
    templates: Seq<Option<ClockedNor>>, layouts: Seq<Option<ModuleSourceLayout>>, i: int, owner: ModuleBodyPosition,
) -> bool {
    &&& 0 <= i < templates.len() == layouts.len()
    &&& templates[i].is_some() && layouts[i].is_some()
    &&& layouts[i]->Some_0.owner == owner
    &&& source_clocked_layout(&layouts[i]->Some_0.circuit, &templates[i]->Some_0.netlist_model(),
        layouts[i]->Some_0.order, layouts[i]->Some_0.index)
}

pub(in crate::project::use_aliases::module_types::clocked_source) open spec fn call_layout_is_ready(
    call: &crate::project::CheckedModuleCall, edge: Option<usize>, templates: Seq<Option<ClockedNor>>,
    layouts: Seq<Option<ModuleSourceLayout>>,
) -> bool {
    edge matches Some(child) ==> call.inputs.ports.signature.target matches ModuleCallTarget::Routine { position, .. }
        && prior_layout_at(templates, layouts, child as int, position)
}

pub(super) closed spec fn builtin_source(at: DefinitionPosition) -> ChildSourceLayout {
    let site = SourceGateId { instance: Seq::empty(), gate: at };
    ChildSourceLayout {
        prefix: Seq::empty(),
        circuit: SourceTickCircuit {
            input_count: 2,
            gates: Map::empty().insert(site, SourceNor { left: SourceWire::Input(0), right: SourceWire::Input(1) }),
            outputs: seq![SourceWire::Gate(site)],
        },
        order: seq![site],
        index: Map::empty().insert(site, 0int),
    }
}

proof fn builtin_source_layout(at: DefinitionPosition, netlist: &NorNetlist)
    requires builtin_nor_template(netlist),
    ensures ({
        let layout = builtin_source(at);
        source_clocked_layout(&layout.circuit, netlist, layout.order, layout.index)
    }),
{
    let layout = builtin_source(at);
    assert(source_output_pair_at(&layout.circuit, netlist, layout.order, 0));
    source_clocked_layout_from_pairs(&layout.circuit, netlist, layout.order, layout.index);
}

spec fn layout_for_call(checked: &ModuleCalls, edges: Seq<Option<usize>>, layouts: Seq<Option<ModuleSourceLayout>>, i: int)
    -> ChildSourceLayout
{
    let call = checked.calls@[i];
    if call.inputs.ports.signature.target is Nor {
        builtin_source(call.at)
    } else {
        let child = layouts[edges[i]->Some_0 as int]->Some_0;
        ChildSourceLayout { prefix: seq![call.at], circuit: child.circuit, order: child.order, index: child.index }
    }
}

pub(super) closed spec fn child_layout_uses_call(checked: &ModuleCalls, i: int, layout: ChildSourceLayout, template: &NorNetlist) -> bool {
    let call = checked.calls@[i];
    &&& source_clocked_layout(&layout.circuit, template, layout.order, layout.index)
    &&& layout.order.len() == template.gates@.len()
    &&& if call.inputs.ports.signature.target is Nor {
        layout == builtin_source(call.at)
    } else {
        layout.prefix == seq![call.at]
    }
}

pub(super) proof fn child_source_at_call(checked: &ModuleCalls, i: int, layout: ChildSourceLayout, template: &NorNetlist)
    requires child_layout_uses_call(checked, i, layout, template), 0 <= i < checked.calls@.len(),
    ensures
        source_clocked_layout(&layout.circuit, template, layout.order, layout.index),
        layout.order.len() == template.gates@.len(),
        if checked.calls@[i].inputs.ports.signature.target is Nor {
            layout == builtin_source(checked.calls@[i].at) && layout.prefix.len() == 0
        } else { layout.prefix == seq![checked.calls@[i].at] },
{
}

proof fn different_calls_use_different_gate_ids(checked: &ModuleCalls, first: ChildSourceLayout, second: ChildSourceLayout,
    first_model: &NorNetlist, second_model: &NorNetlist, a: int, b: int, x: int, y: int)
    requires
        0 <= a < checked.calls@.len(), 0 <= b < checked.calls@.len(), checked.calls@[a].at != checked.calls@[b].at,
        child_layout_uses_call(checked, a, first, first_model),
        child_layout_uses_call(checked, b, second, second_model),
        0 <= x < first.order.len(), 0 <= y < second.order.len(),
    ensures source_gate_under(first.prefix, first.order[x]) != source_gate_under(second.prefix, second.order[y]),
{
    let left = source_gate_under(first.prefix, first.order[x]);
    let right = source_gate_under(second.prefix, second.order[y]);
    if checked.calls@[a].inputs.ports.signature.target is Nor {
        assert(left.instance.len() == 0 && left.gate == checked.calls@[a].at);
    } else {
        assert(left.instance.len() > 0 && left.instance[0] == checked.calls@[a].at);
    }
    if checked.calls@[b].inputs.ports.signature.target is Nor {
        assert(right.instance.len() == 0 && right.gate == checked.calls@[b].at);
    } else {
        assert(right.instance.len() > 0 && right.instance[0] == checked.calls@[b].at);
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    proof fn order_for_assembled_calls(&self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls,
        instances: Seq<SourceInstance>, counts: Seq<usize>, regions: Seq<Range<usize>>, total: usize,
        layouts: Seq<ChildSourceLayout>) -> (order: Seq<SourceGateId>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            instances.len() == checked.calls@.len() == layouts.len(),
            instance_counts_match(instances, counts), clocked_regions_cover(counts, regions, total),
            forall|i: int| 0 <= i < layouts.len() ==> #[trigger]
                child_layout_uses_call(checked, i, layouts[i], &instances[i].template.netlist_model()),
        ensures
            order.len() == total,
            all_child_source_placements(instances, layouts, regions, order),
            forall|a: int, b: int| 0 <= a < b < order.len() ==> #[trigger] order[a] != #[trigger] order[b],
    {
        let order = Seq::new(total as nat, |gate: int| {
            let i = choose|i: int| #[trigger] instance_owns_gate(regions, i, gate);
            let child = layouts[i];
            source_gate_under(child.prefix, child.order[gate - regions[i].start])
        });
        assert forall|i: int| 0 <= i < layouts.len() implies #[trigger]
            child_source_placement(instances[i], layouts[i], regions[i].start, order) by {
            let child = layouts[i];
            let region = regions[i];
            assert(child_layout_uses_call(checked, i, child, &instances[i].template.netlist_model()));
            assert(region.end - region.start == child.order.len());
            assert forall|k: int| 0 <= k < child.order.len() implies
                (#[trigger] order[region.start + k]) == source_gate_under(child.prefix, child.order[k]) by {
                let gate = region.start + k;
                let selected = instance_for_gate(counts, regions, total, gate);
                assert(instance_owns_gate(regions, i, gate));
                assert(selected == i);
                let other = choose|j: int| #[trigger] instance_owns_gate(regions, j, gate);
                assert(other == i);
            };
        };
        assert(all_child_source_placements(instances, layouts, regions, order));
        assert forall|x: int, y: int| 0 <= x < y < order.len() implies #[trigger] order[x] != #[trigger] order[y] by {
            let a = instance_for_gate(counts, regions, total, x);
            let b = instance_for_gate(counts, regions, total, y);
            let first = layouts[a];
            let second = layouts[b];
            let first_model = instances[a].template.netlist_model();
            let second_model = instances[b].template.netlist_model();
            let u = x - regions[a].start;
            let v = y - regions[b].start;
            assert(child_layout_uses_call(checked, a, first, &first_model));
            assert(child_layout_uses_call(checked, b, second, &second_model));
            assert(child_source_placement(instances[a], first, regions[a].start, order));
            assert(child_source_placement(instances[b], second, regions[b].start, order));
            assert(regions[a].end - regions[a].start == first.order.len());
            assert(regions[b].end - regions[b].start == second.order.len());
            if a == b {
                source_gate_positions_distinct(&first.circuit, &first_model, first.order, first.index, u, v);
                let left = source_gate_under(first.prefix, first.order[u]);
                let right = source_gate_under(first.prefix, first.order[v]);
                if left == right {
                    assert(left.instance.skip(first.prefix.len() as int) =~= first.order[u].instance);
                    assert(right.instance.skip(first.prefix.len() as int) =~= first.order[v].instance);
                }
                assert(left != right);
            } else {
                if a < b { self.module_call_sites_distinct(owner, limit, checked, a, b); }
                else { self.module_call_sites_distinct(owner, limit, checked, b, a); }
                different_calls_use_different_gate_ids(checked, first, second, &first_model, &second_model, a, b, u, v);
            }
            assert(order[x] == source_gate_under(first.prefix, first.order[u]));
            assert(order[y] == source_gate_under(second.prefix, second.order[v]));
        };
        order
    }

    // 組み立てに使った証拠を取り出し、同じゲート区間と出力区間で照合する。
    pub(in crate::project::use_aliases::module_types::clocked_source) proof fn source_layout_from_compiled(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls, edges: Seq<Option<usize>>,
        templates: Seq<Option<ClockedNor>>, prior: Seq<Option<ModuleSourceLayout>>,
        builtin: &ClockedNor, netlist: &NorNetlist,
    ) -> (layout: ModuleSourceLayout)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.clocked_checked_assembly_matches(checked, edges, templates, builtin, *netlist),
            crate::netlist::clocked_wiring_valid(netlist),
            edges.len() == checked.calls@.len(),
            forall|i: int| 0 <= i < edges.len() ==>
                #[trigger] call_layout_is_ready(&checked.calls@[i], edges[i], templates, prior),
        ensures layout.owner == owner, source_clocked_layout(&layout.circuit, netlist, layout.order, layout.index),
            self.module_source_layer(checked, &layout.circuit, &layout.layer),
            layout.layer.children_model().len() == checked.calls@.len(),
            forall|i: int| 0 <= i < edges.len() ==> (#[trigger] checked.calls@[i]).inputs.ports.signature.target is Routine
                ==> edges[i].is_some(),
            forall|i: int| 0 <= i < edges.len() ==> ((#[trigger] edges[i]) matches Some(child)
                ==> layout.layer.children_model()[i] == prior[child as int]->Some_0.circuit),
    {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        vstd::std_specs::vec::axiom_spec_len(&drivers.signature.inputs);
        let input_count = drivers.signature.inputs@.len() as usize;
        let (instances, counts) = choose|instances: Seq<SourceInstance>, counts: Seq<usize>|
            #![trigger self.instances_match_source_calls(checked, instances, edges, templates, builtin),
                source_assembly_matches(instances, counts, input_count, drivers.outputs@, *netlist)]
            instances.len() == checked.calls@.len()
            && self.instances_match_source_calls(checked, instances, edges, templates, builtin)
            && instance_output_slots(instances, drivers.definitions@.len() as int)
            && source_assembly_matches(instances, counts, input_count, drivers.outputs@, *netlist);
        let end = instances.len() as int;
        let total = netlist.gates@.len() as usize;
        let (regions, flat_drivers, flat_wires) =
            choose|regions: Seq<Range<usize>>, flat_drivers: Seq<ClockedWireDriver>, flat_wires: Seq<Wire>|
            #![trigger child_drivers_match(instances, regions, end, flat_drivers),
                clocked_wires_match(flat_drivers, flat_wires)]
            clocked_regions_cover(counts, regions, total)
            && child_drivers_match(instances, regions, end, flat_drivers)
            && clocked_wires_match(flat_drivers, flat_wires) && flat_wires.len() == flat_drivers.len()
            && (forall|i: int| 0 <= i < flat_wires.len() ==>
                wire_available(#[trigger] flat_wires[i], input_count as nat, netlist.gates@.len()))
            && assembled_gate_prefix(instances, regions, flat_wires, netlist.gates@, end)
            && assembled_outputs(drivers.outputs@, flat_wires, netlist.outputs@);
        let layouts = Seq::new(instances.len(), |i: int| layout_for_call(checked, edges, prior, i));
        assert forall|i: int| 0 <= i < layouts.len() implies #[trigger]
            child_layout_uses_call(checked, i, layouts[i], &instances[i].template.netlist_model()) by {
            let call = checked.calls@[i];
            let instance = instances[i];
            assert(self.instance_matches_source_call(checked, i, instance, edges[i], templates, builtin));
            let model = instance.template.netlist_model();
            if call.inputs.ports.signature.target is Nor {
                builtin_source_layout(call.at, &model);
            } else {
                assert(edges[i].is_some());
                assert(call_layout_is_ready(&call, edges[i], templates, prior));
            }
            crate::netlist::source_trace_layout_counts(&layouts[i].circuit, &model, layouts[i].order, layouts[i].index);
        };
        let order = self.order_for_assembled_calls(owner, limit, checked, instances, counts, regions, total, layouts);
        assert forall|i: int| 0 <= i < instances.len() implies
            self.source_arguments_match(checked, i, (#[trigger] instances[i]).arguments@) by {
            assert(self.instance_matches_source_call(checked, i, instances[i], edges[i], templates, builtin));
        };
        let source = self.source_circuit_from_assembly(checked, layouts, order, instances, counts, regions, flat_drivers,
            flat_wires, netlist);
        crate::netlist::source_trace_layout_counts(&source.circuit, netlist, order, source.index);
        let layer = self.reference_layer_from_assembly(checked, &source, layouts, instances, counts,
            regions, order, netlist, edges, templates, builtin);
        assert forall|i: int| 0 <= i < edges.len() implies ((#[trigger] edges[i]) matches Some(child)
            ==> layer.children_model()[i] == prior[child as int]->Some_0.circuit) by {
            let call = &checked.calls@[i];
            assert(call_layout_is_ready(call, edges[i], templates, prior));
            assert(layer.children_model()[i] == layouts[i].circuit);
        };
        assert forall|i: int| 0 <= i < edges.len()
            && (#[trigger] checked.calls@[i]).inputs.ports.signature.target is Routine implies edges[i].is_some() by {
            assert(self.instance_matches_source_call(checked, i, instances[i], edges[i], templates, builtin));
        };
        ModuleSourceLayout { owner, circuit: source.circuit, order, index: source.index, layer }
    }
}

} // verus!
