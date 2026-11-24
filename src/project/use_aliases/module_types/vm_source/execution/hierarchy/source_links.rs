//! 階層の記号配線を、ソース上の端子と定義への直結に対応付ける。

use super::super::source_links::{
    SourceVmLink, source_vm_link_pair, source_vm_link_value, source_vm_links_resolved,
    source_vm_operand_pair, source_vm_resolve_links,
};
use super::source_ids::HierarchySourceIds;
use super::placement_model::routine_external_pin_bounds;
use super::source_placement::{source_vm_child_ports_match, source_vm_terminal_in_parent};
use super::{
    ClockedModuleNetwork, ClockedModuleOutputs, ClockedModuleVmLimits, ClockedWireDriver, HierarchyRowOrigin, ModuleCalls, UseAliases,
    resolved_driver, row_model,
};
use super::super::super::super::clocked_plan::{clocked_wire_at, clocked_wires_match};
use crate::netlist::{
    ClockedStorageInputs, SourceVmCircuit, SourceVmWire, Wire, clocked_storage_output_width, clocked_storage_width_concat,
    clocked_storage_width_push, clocked_wiring_endpoints, output_ports_available, source_vm_layout_for_orders,
    source_vm_paired_rows_agree, source_vm_row_pair, source_vm_terminal_pair, wire_available,
};
use vstd::prelude::*;

verus! {

/// 先行する状態素子の登録出力幅の和。
pub(super) open spec fn registered_prefix(widths: Seq<nat>, count: nat) -> nat
    recommends count <= widths.len(),
    decreases count,
{
    if count == 0 { 0 } else {
        registered_prefix(widths, (count - 1) as nat) + widths[count - 1]
    }
}

/// ソース上の登録出力幅は、配置された各素子のデータ端子の幅と一致する。
pub(super) open spec fn source_registered_widths_match(widths: Seq<nat>, storage: Seq<ClockedStorageInputs>) -> bool {
    &&& widths.len() == storage.len()
    &&& forall|i: int| 0 <= i < widths.len() ==> (#[trigger] widths[i]) == storage[i].data@.len()
}

proof fn registered_prefix_matches(widths: Seq<nat>, storage: Seq<ClockedStorageInputs>, count: nat)
    requires source_registered_widths_match(widths, storage), count <= widths.len(),
    ensures registered_prefix(widths, count) == clocked_storage_output_width(storage.take(count as int)),
    decreases count,
{
    if count == 0 {
        let empty = storage.take(0);
        assert(empty + empty =~= empty);
        clocked_storage_width_concat(empty, empty);
    } else {
        let i = count - 1;
        let prefix = storage.take(i);
        registered_prefix_matches(widths, storage, i as nat);
        clocked_storage_width_push(prefix, storage[i]);
        assert(prefix.push(storage[i]) =~= storage.take(count as int));
        assert(widths[i] == storage[i].data@.len());
    }
}

proof fn registered_bit_in_prefix(widths: Seq<nat>, count: nat, bit: nat) -> (index: int)
    requires count <= widths.len(), bit < registered_prefix(widths, count),
    ensures 0 <= index < count,
        registered_prefix(widths, index as nat) <= bit < registered_prefix(widths, index as nat) + widths[index],
    decreases count,
{
    assert(count > 0);
    let start = (count - 1) as nat;
    if bit < registered_prefix(widths, start) {
        registered_bit_in_prefix(widths, start, bit)
    } else {
        start as int
    }
}

/// 解決前の終点を、ソース上の素子 ID と登録出力のビット位置で表す。
///
/// 定義への直結はそのまま残す。状態素子にはソース上の順序と登録出力幅を使う。
pub(super) open spec fn hierarchy_source_link(
    external: usize, ids: HierarchySourceIds, widths: Seq<nat>, driver: ClockedWireDriver,
) -> SourceVmLink {
    match driver {
        ClockedWireDriver::Alias(target) => SourceVmLink::Alias(target),
        ClockedWireDriver::Terminal(Wire::Constant(bit)) => SourceVmLink::Terminal(SourceVmWire::Constant(bit)),
        ClockedWireDriver::Terminal(Wire::Gate(index)) =>
            SourceVmLink::Terminal(SourceVmWire::Gate(ids.gates[index as int])),
        ClockedWireDriver::Terminal(Wire::Input(index)) => {
            if index < external {
                SourceVmLink::Terminal(SourceVmWire::Input(index))
            } else {
                let bit = index - external;
                let device = choose|i: int| 0 <= i < widths.len() &&
                    #[trigger] registered_prefix(widths, i as nat) <= bit
                    < registered_prefix(widths, i as nat) + widths[i];
                SourceVmLink::Terminal(SourceVmWire::Registered(ids.devices[device],
                    (bit - registered_prefix(widths, device as nat)) as usize))
            }
        },
    }
}

proof fn hierarchy_link_matches(
    external: usize, ids: HierarchySourceIds, widths: Seq<nat>, storage: Seq<ClockedStorageInputs>,
    driver: ClockedWireDriver,
)
    requires
        source_registered_widths_match(widths, storage),
        ids.devices.len() == widths.len() && ids.devices.no_duplicates(),
        driver matches ClockedWireDriver::Terminal(flat) ==>
            wire_available(flat, (external + clocked_storage_output_width(storage)) as nat, ids.gates.len()),
    ensures source_vm_link_pair(external, storage, &source_vm_layout_for_orders(ids.gates, ids.devices),
        hierarchy_source_link(external, ids, widths, driver), driver),
{
    let layout = source_vm_layout_for_orders(ids.gates, ids.devices);
    ids.gates.to_set_ensures();
    ids.devices.to_set_ensures();
    if let ClockedWireDriver::Terminal(Wire::Input(index)) = driver {
        if index >= external {
            let bit = index - external;
            registered_prefix_matches(widths, storage, widths.len());
            assert(storage.take(widths.len() as int) =~= storage);
            let at = registered_bit_in_prefix(widths, widths.len(), bit as nat);
            assert(registered_prefix(widths, at as nat) <= bit < registered_prefix(widths, at as nat) + widths[at]);
            let device = choose|i: int| 0 <= i < widths.len() &&
                #[trigger] registered_prefix(widths, i as nat) <= bit
                < registered_prefix(widths, i as nat) + widths[i];
            let id = ids.devices[device];
            assert(layout.device_index.contains_key(id));
            assert(ids.devices[layout.device_index[id]] == id);
            assert(layout.device_index[id] == device);
            registered_prefix_matches(widths, storage, device as nat);
            assert(widths[device] == storage[device].data@.len());
        }
    }
}

/// 直結を保存した記号列を解決し、定義全体のソース端子を得る。
proof fn hierarchy_source_definitions_resolve(
    external: usize, ids: HierarchySourceIds, widths: Seq<nat>, storage: Seq<ClockedStorageInputs>,
    symbolic: Seq<ClockedWireDriver>, flat: Seq<Wire>,
) -> (definitions: Seq<SourceVmWire>)
    requires
        source_registered_widths_match(widths, storage),
        ids.devices.len() == widths.len() && ids.devices.no_duplicates(),
        clocked_wires_match(symbolic, flat), symbolic.len() == flat.len(),
        output_ports_available(flat, (external + clocked_storage_output_width(storage)) as nat, ids.gates.len(), flat.len() as int),
    ensures
        source_vm_links_resolved(symbolic.map_values(|driver: ClockedWireDriver|
            hierarchy_source_link(external, ids, widths, driver)), definitions),
        source_vm_row_pair(external, storage, &source_vm_layout_for_orders(ids.gates, ids.devices), definitions, flat),
{
    let layout = source_vm_layout_for_orders(ids.gates, ids.devices);
    let links = symbolic.map_values(|driver: ClockedWireDriver| hierarchy_source_link(external, ids, widths, driver));
    assert forall|i: int| 0 <= i < links.len() implies
        source_vm_link_pair(external, storage, &layout, #[trigger] links[i], symbolic[i]) by {
        clocked_wire_at(symbolic, flat, i);
        hierarchy_link_matches(external, ids, widths, storage, symbolic[i]);
    };
    source_vm_resolve_links(external, storage, &layout, links, symbolic, flat)
}

/// 解決したソースの定義を使って、型検査済みの引数や公開出力のビットを読む。
pub(super) open spec fn hierarchy_source_operand_row(
    external: usize, ids: HierarchySourceIds, widths: Seq<nat>,
    definitions: Seq<SourceVmWire>, symbolic: Seq<ClockedWireDriver>,
) -> Seq<SourceVmWire> {
    symbolic.map_values(|driver: ClockedWireDriver|
        source_vm_link_value(hierarchy_source_link(external, ids, widths, driver), definitions))
}

/// 同じ定義を参照する引数列や公開出力列について、ソース端子と VM 配線を照合する。
pub(super) proof fn hierarchy_source_operand_pair(
    external: usize, ids: HierarchySourceIds, widths: Seq<nat>, storage: Seq<ClockedStorageInputs>,
    definitions: Seq<SourceVmWire>, flat_definitions: Seq<Wire>, symbolic: Seq<ClockedWireDriver>, flat: Seq<Wire>,
)
    requires
        source_registered_widths_match(widths, storage),
        ids.devices.len() == widths.len() && ids.devices.no_duplicates(),
        source_vm_row_pair(external, storage, &source_vm_layout_for_orders(ids.gates, ids.devices), definitions, flat_definitions),
        super::super::resolved_bits(symbolic, flat_definitions, flat),
        output_ports_available(flat, (external + clocked_storage_output_width(storage)) as nat, ids.gates.len(), flat.len() as int),
    ensures source_vm_row_pair(external, storage, &source_vm_layout_for_orders(ids.gates, ids.devices),
        hierarchy_source_operand_row(external, ids, widths, definitions, symbolic), flat),
{
    let layout = source_vm_layout_for_orders(ids.gates, ids.devices);
    let source = hierarchy_source_operand_row(external, ids, widths, definitions, symbolic);
    assert forall|i: int| 0 <= i < flat.len() implies
        source_vm_terminal_pair(external, storage, &layout, source[i], #[trigger] flat[i]) by {
        let driver = symbolic[i];
        assert(resolved_driver(driver, flat_definitions) == Some(flat[i]));
        hierarchy_link_matches(external, ids, widths, storage, driver);
        source_vm_operand_pair(external, storage, &layout, hierarchy_source_link(external, ids, widths, driver),
            driver, definitions, flat_definitions, flat[i]);
    };
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 実際の階層展開で使った記号列から、ソース側の定義の参照先を求める。
    pub(super) proof fn hierarchy_source_definitions(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
        ids: HierarchySourceIds, widths: Seq<nat>,
    ) -> (definitions: Seq<SourceVmWire>)
        requires
            self.hierarchy_network_wiring(checked, limits, network),
            source_registered_widths_match(widths, network.storage@),
            ids.gates.len() == network.circuit.netlist_model().gates@.len(),
            ids.devices.len() == network.storage@.len() && ids.devices.no_duplicates(),
        ensures ({
            let wiring = network._hierarchy_wiring@->Some_0;
            let external = network.inputs.total_bits_model();
            &&& source_vm_links_resolved(wiring.symbolic.map_values(|driver: ClockedWireDriver|
                hierarchy_source_link(external, ids, widths, driver)), definitions)
            &&& source_vm_row_pair(external, network.storage@, &source_vm_layout_for_orders(ids.gates, ids.devices),
                definitions, wiring.definitions)
        }),
    {
        reveal(UseAliases::hierarchy_public_wiring);
        let wiring = network._hierarchy_wiring@->Some_0;
        let symbolic = wiring.symbolic;
        let flat = wiring.definitions;
        hierarchy_source_definitions_resolve(network.inputs.total_bits_model(), ids, widths, network.storage@, symbolic, flat)
    }

    /// 同じ型検査済みの記号行から、子の全実引数と親の公開出力をソース端子で表す。
    pub(super) proof fn hierarchy_source_argument_and_output_rows(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
        ports: &ClockedModuleOutputs, ids: HierarchySourceIds, widths: Seq<nat>,
    ) -> (definitions: Seq<SourceVmWire>)
        requires
            self.hierarchy_network_wiring(checked, limits, network),
            self.hierarchy_public_wiring(checked, limits.width, ports, &network._hierarchy_wiring@->Some_0,
                network.circuit.netlist_model().outputs@),
            ports.inputs == network.inputs,
            source_registered_widths_match(widths, network.storage@),
            ids.gates.len() == network.circuit.netlist_model().gates@.len(),
            ids.devices.len() == network.storage@.len() && ids.devices.no_duplicates(),
        ensures ({
            let wiring = network._hierarchy_wiring@->Some_0;
            let external = network.inputs.total_bits_model();
            let layout = source_vm_layout_for_orders(ids.gates, ids.devices);
            &&& source_vm_links_resolved(wiring.symbolic.map_values(|driver: ClockedWireDriver|
                hierarchy_source_link(external, ids, widths, driver)), definitions)
            &&& source_vm_row_pair(external, network.storage@, &layout, definitions, wiring.definitions)
            &&& source_vm_row_pair(external, network.storage@, &layout,
                hierarchy_source_operand_row(external, ids, widths, definitions, row_model(ports.drivers@)),
                network.circuit.netlist_model().outputs@)
            &&& forall|call: int| 0 <= call < wiring.routines.len() ==> ((#[trigger] wiring.routines[call]) matches Some(routine)
                ==> source_vm_row_pair(external, network.storage@, &layout,
                    hierarchy_source_operand_row(external, ids, widths, definitions, row_model(routine.argument_rows@)),
                    routine.external))
        }),
    {
        reveal(UseAliases::hierarchy_public_wiring);
        let wiring = network._hierarchy_wiring@->Some_0;
        let netlist = network.circuit.netlist_model();
        let external = network.inputs.total_bits_model();
        let layout = source_vm_layout_for_orders(ids.gates, ids.devices);
        let definitions = self.hierarchy_source_definitions(checked, limits, network, ids, widths);
        clocked_wiring_endpoints(&netlist);
        hierarchy_source_operand_pair(external, ids, widths, network.storage@, definitions, wiring.definitions,
            row_model(ports.drivers@), netlist.outputs@);
        assert forall|call: int| 0 <= call < wiring.routines.len() implies ((#[trigger] wiring.routines[call]) matches Some(routine)
            ==> source_vm_row_pair(external, network.storage@, &layout,
                hierarchy_source_operand_row(external, ids, widths, definitions, row_model(routine.argument_rows@)),
                routine.external)) by {
            if let Some(routine) = wiring.routines[call] {
                routine_external_pin_bounds(wiring.routines, netlist.input_count, netlist.gates@.len(), call);
                hierarchy_source_operand_pair(external, ids, widths, network.storage@, definitions, wiring.definitions,
                    row_model(routine.argument_rows@), routine.external);
            }
        };
        definitions
    }

    /// 子の出力を受ける定義は、同じポートのソース配線を実引数で置き換えた列になる。
    pub(super) proof fn hierarchy_definition_follows_child_output(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, network: &ClockedModuleNetwork,
        ids: HierarchySourceIds, child: HierarchySourceIds, source: &SourceVmCircuit,
        definitions: Seq<SourceVmWire>, arguments: Seq<SourceVmWire>, slot: int, call: usize,
    )
        requires ({
            let wiring = network._hierarchy_wiring@->Some_0;
            let external = network.inputs.total_bits_model();
            &&& ids.devices.no_duplicates()
            &&& 0 <= slot < wiring.origins.len()
            &&& call < wiring.routines.len()
            &&& wiring.origins[slot] == HierarchyRowOrigin::Call(call)
            &&& wiring.routines[call as int].is_some()
            &&& self.hierarchy_definition_wiring(checked, ports, &wiring, slot)
            &&& source_vm_row_pair(external, network.storage@, &source_vm_layout_for_orders(ids.gates, ids.devices),
                definitions, wiring.definitions)
            &&& source_vm_child_ports_match(&network.circuit.netlist_model(), external, network.storage@,
                wiring.direct_devices, wiring.routines[call as int]->Some_0, checked.calls@[call as int].at,
                child, ids, arguments, source)
        }),
        ensures ({
            let wiring = network._hierarchy_wiring@->Some_0;
            let routine = wiring.routines[call as int]->Some_0;
            let index = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[slot].result_index as int;
            let child_range = routine.layout.ranges_model()[index];
            let parent_range = ports.definitions.ranges_model()[slot];
            definitions.subrange(parent_range.start as int, parent_range.end as int)
                == source.outputs.subrange(child_range.start as int, child_range.end as int).map_values(
                    |wire: SourceVmWire| source_vm_terminal_in_parent(checked.calls@[call as int].at, arguments, wire))
        }),
    {
        let wiring = network._hierarchy_wiring@->Some_0;
        let routine = wiring.routines[call as int]->Some_0;
        let external = network.inputs.total_bits_model();
        let site = checked.calls@[call as int].at;
        let index = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[slot].result_index as int;
        let child_range = routine.layout.ranges_model()[index];
        let parent_range = ports.definitions.ranges_model()[slot];
        let layout = source_vm_layout_for_orders(ids.gates, ids.devices);
        let flat = wiring.definitions.subrange(parent_range.start as int, parent_range.end as int);
        let first = definitions.subrange(parent_range.start as int, parent_range.end as int);
        let second = source.outputs.subrange(child_range.start as int, child_range.end as int)
            .map_values(|wire: SourceVmWire| source_vm_terminal_in_parent(site, arguments, wire));
        assert(flat == routine.outputs.subrange(child_range.start as int, child_range.end as int));
        assert(source_vm_row_pair(external, network.storage@, &layout, first, flat)) by {
            assert forall|i: int| 0 <= i < flat.len() implies
                source_vm_terminal_pair(external, network.storage@, &layout, first[i], #[trigger] flat[i]) by {
                assert(flat[i] == wiring.definitions[parent_range.start + i]);
            };
        };
        assert(source_vm_row_pair(external, network.storage@, &layout, second, flat)) by {
            assert forall|i: int| 0 <= i < flat.len() implies
                source_vm_terminal_pair(external, network.storage@, &layout, second[i], #[trigger] flat[i]) by {
                assert(flat[i] == routine.outputs[child_range.start + i]);
            };
        };
        source_vm_paired_rows_agree(external, network.storage@, ids.gates, ids.devices, first, second, flat);
    }
}

} // verus!
