//! 子モジュールの公開ポートを、親の定義が読む配線に対応付ける。

use super::super::super::clocked_source::relocate_child_output;
#[cfg(verus_only)]
use super::super::super::clocked_source::{relocated_child_driver, resolved_driver};
use crate::netlist::{ClockedNor, PortBitLayout};
#[cfg(verus_only)]
use crate::netlist::{Wire, clocked_stateful_arguments, instance_outputs_match, instance_wire};
#[cfg(verus_only)]
use super::resolved_bits;
use super::{ClockedEndpointError, ClockedModuleVmLimits, ModuleBodyPosition, ModuleCalls, UseAliases};
use super::super::ClockedModuleOutputs;
use crate::project::ClockedWireDriver;
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

verus! {

/// 子のポートを親の定義欄に結び付ける際に見つかった違反。
pub(super) enum ChildOutputError {
    /// 指定した公開ポートが子にない。
    Port,
    /// 子の公開出力の配置がネットリストの出力ビット数と合わない。
    Layout,
    /// 配線の配列を確保できなかった。
    Allocation,
    /// 最初に親の予約区間へ移せなかったビットの、ポート内の添字。
    Driver(usize),
}

/// 親の定義が読む各ビットが、子のポートで同じ位置にある配線から導かれることを表す。
pub(super) open spec fn child_port_drivers_match(
    child: &ClockedNor, outputs: &PortBitLayout, port: usize,
    arguments: Seq<ClockedWireDriver>, states: Range<usize>, gates: Range<usize>, drivers: Seq<ClockedWireDriver>,
) -> bool {
    let wires = child.netlist_model().outputs@;
    &&& port < outputs.ranges_model().len()
    &&& outputs.total_bits_model() == wires.len()
    &&& {
        let range = outputs.ranges_model()[port as int];
        &&& range.start < range.end <= wires.len()
        &&& drivers.len() == range.end - range.start
        &&& forall|i: int| 0 <= i < drivers.len() ==> Some(#[trigger] drivers[i])
            == relocated_child_driver(wires[range.start + i], arguments, states, gates)
    }
}

/// 子のポートの各ビットを低位から読み、親の実引数と予約区間に対応付ける。
/// 外部入力への直結は別名のまま保持できるため、ここでは別名を解決しない。
pub(super) fn child_output_drivers(
    child: &ClockedNor, outputs: &PortBitLayout, port: usize, arguments: &[ClockedWireDriver],
    states: &Range<usize>, gates: &Range<usize>,
) -> (result: Result<Vec<ClockedWireDriver>, ChildOutputError>)
    ensures
        result matches Err(ChildOutputError::Port) ==> port >= outputs.ranges_model().len(),
        result matches Err(ChildOutputError::Layout) ==>
            port < outputs.ranges_model().len()
                && outputs.total_bits_model() != child.netlist_model().outputs@.len(),
        result matches Err(ChildOutputError::Allocation) ==>
            port < outputs.ranges_model().len()
                && outputs.total_bits_model() == child.netlist_model().outputs@.len(),
        result matches Ok(drivers) ==>
            child_port_drivers_match(child, outputs, port, arguments@, *states, *gates, drivers@),
        result matches Err(ChildOutputError::Driver(bit)) ==> {
            let range = outputs.ranges_model()[port as int];
            let wires = child.netlist_model().outputs@;
            &&& port < outputs.ranges_model().len()
            &&& outputs.total_bits_model() == wires.len()
            &&& range.start + bit < range.end <= wires.len()
            &&& relocated_child_driver(wires[range.start + bit], arguments@, *states, *gates).is_none()
            &&& forall|i: int| 0 <= i < bit ==> (#[trigger]
                relocated_child_driver(wires[range.start + i], arguments@, *states, *gates)).is_some()
        },
{
    let Some(range) = outputs.range(port) else { return Err(ChildOutputError::Port); };
    let netlist = child.checked_netlist();
    if outputs.total_bits() != netlist.outputs.len() { return Err(ChildOutputError::Layout); }
    let width = range.end - range.start;
    let mut drivers = Vec::new();
    if drivers.try_reserve_exact(width).is_err() { return Err(ChildOutputError::Allocation); }
    let mut bit = 0;
    while bit < width
        invariant
            port < outputs.ranges_model().len(),
            range == outputs.ranges_model()[port as int],
            outputs.total_bits_model() == netlist.outputs@.len(),
            *netlist == child.netlist_model(),
            bit == drivers@.len() <= width,
            range.start + width == range.end <= netlist.outputs@.len(),
            forall|i: int| 0 <= i < bit ==> Some(#[trigger] drivers@[i])
                == relocated_child_driver(netlist.outputs@[range.start + i], arguments@, *states, *gates),
        decreases width - bit,
    {
        let wire = netlist.outputs[range.start + bit];
        let Some(driver) = relocate_child_output(wire, arguments, states, gates) else {
            assert(wire == netlist.outputs@[range.start + bit]);
            assert(relocated_child_driver(netlist.outputs@[range.start + bit], arguments@, *states, *gates).is_none());
            assert forall|i: int| 0 <= i < bit implies (#[trigger]
                relocated_child_driver(netlist.outputs@[range.start + i], arguments@, *states, *gates)).is_some() by {
                assert(Some(drivers@[i]) == relocated_child_driver(
                    netlist.outputs@[range.start + i], arguments@, *states, *gates));
            };
            return Err(ChildOutputError::Driver(bit));
        };
        let ghost before = drivers@;
        drivers.push(driver);
        assert forall|i: int| 0 <= i <= bit implies Some(#[trigger] drivers@[i])
            == relocated_child_driver(netlist.outputs@[range.start + i], arguments@, *states, *gates) by {
            if i < bit { assert(drivers@[i] == before[i]); }
        };
        bit += 1;
    }
    Ok(drivers)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 親の定義欄が受け取る子の出力ポートを特定し、低位から順に配線を求める。
    pub(super) fn bind_child_definition(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits,
        checked: &ModuleCalls<'p, 'a>, parent: &ClockedModuleOutputs, slot: usize, call: usize,
        child: &ClockedNor, outputs: &PortBitLayout, arguments: &[ClockedWireDriver],
        states: &Range<usize>, gates: &Range<usize>,
    ) -> (result: Result<Vec<ClockedWireDriver>, ClockedEndpointError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limits.width, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limits.width, limits.wiring_bits, Ok(*parent)),
            slot < checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len(),
        ensures
            result matches Ok(wires) ==> {
                let definition = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[slot as int];
                let range = parent.definitions.ranges_model()[slot as int];
                &&& self.source_vm_root_slot(checked, slot as int, call as int)
                &&& child_port_drivers_match(child, outputs, definition.result_index, arguments@, *states, *gates, wires@)
                &&& wires@.len() == range.end - range.start
            },
            result matches Err(error) ==> error is Unsupported || error is Driver || error is Allocation
                || error is Layout || error is Width,
            result matches Err(ClockedEndpointError::Unsupported(site) | ClockedEndpointError::Driver(site)
                | ClockedEndpointError::Width { definition: site, .. }) ==> {
                let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
                &&& crate::project::location_in_source(site)
                &&& site.span == drivers.definitions@[slot as int].name.span
                &&& *site.source == self.targets.project_model().sources_model()[drivers.origins@[slot as int].file as int]
            },
            result matches Err(ClockedEndpointError::Unsupported(_)) ==>
                !self.source_vm_root_slot(checked, slot as int, call as int),
            result matches Err(ClockedEndpointError::Width { produced, allocated, .. }) ==> {
                let port = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@[slot as int].result_index;
                let parent_range = parent.definitions.ranges_model()[slot as int];
                let child_range = outputs.ranges_model()[port as int];
                &&& port < outputs.ranges_model().len()
                &&& allocated == parent_range.end - parent_range.start
                &&& produced == child_range.end - child_range.start
                &&& produced != allocated
            },
    {
        let expressions = &checked.module.expressions;
        let drivers = &expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, limits.width, checked);
            self.module_output_types_evidence(owner, limits.width, checked.module);
            self.module_selections_evidence(owner, limits.width, *expressions);
            self.module_alias_types_evidence(owner, limits.width, expressions.typed);
            self.module_type_sources_bounds(owner, limits.width, expressions.typed.sources);
            self.clocked_output_layouts(&checked.module, limits.width, limits.wiring_bits, parent);
        }
        if !self.root_call_slot(owner, limits.width, checked, drivers, slot, call) {
            return Err(ClockedEndpointError::Unsupported(self.source_driver_location(owner, limits.width, drivers, slot)));
        }
        let Some(range) = parent.definitions.range(slot) else { return Err(ClockedEndpointError::Layout); };
        let port = drivers.definitions[slot].result_index;
        let wires = match child_output_drivers(child, outputs, port, arguments, states, gates) {
            Ok(wires) => wires,
            Err(ChildOutputError::Port | ChildOutputError::Layout) => return Err(ClockedEndpointError::Layout),
            Err(ChildOutputError::Allocation) => return Err(ClockedEndpointError::Allocation),
            Err(ChildOutputError::Driver(_)) =>
                return Err(ClockedEndpointError::Driver(self.source_driver_location(owner, limits.width, drivers, slot))),
        };
        let allocated = range.end - range.start;
        if wires.len() != allocated {
            return Err(ClockedEndpointError::Width {
                definition: self.source_driver_location(owner, limits.width, drivers, slot),
                produced: wires.len(),
                allocated,
            });
        }
        Ok(wires)
    }
}

/// 記号配線で選んだ出力と、状態付きインスタンスを移した後の出力は同じ親の配線を読む。
proof fn child_driver_resolves_to_instance(
    wire: Wire, symbolic: Seq<ClockedWireDriver>, definitions: Seq<Wire>, arguments: Seq<Wire>,
    states: Range<usize>, gates: Range<usize>, driver: ClockedWireDriver,
)
    requires
        symbolic.len() == arguments.len(),
        states.start <= states.end,
        relocated_child_driver(wire, symbolic, states, gates) == Some(driver),
        forall|i: int| 0 <= i < arguments.len() ==> resolved_driver(symbolic[i], definitions)
            == Some(#[trigger] arguments[i]),
    ensures
        resolved_driver(driver, definitions) == Some(instance_wire(wire,
            clocked_stateful_arguments(arguments, states.start, (states.end - states.start) as nat), gates.start)),
{
    let inputs = clocked_stateful_arguments(arguments, states.start, (states.end - states.start) as nat);
    if let Wire::Input(index) = wire {
        if index < symbolic.len() {
            assert(inputs[index as int] == arguments[index as int]);
        } else {
            assert(states.start + index - arguments.len() < states.end);
            assert(inputs[index as int] == Wire::Input((states.start + index - arguments.len()) as usize));
        }
    }
}

/// 親で解決した定義のビット列が、インスタンスの同じ出力ポートに対応することを示す。
pub(super) proof fn child_port_resolves_to_instance(
    wires: Seq<Wire>, range: Range<usize>, drivers: Seq<ClockedWireDriver>,
    symbolic: Seq<ClockedWireDriver>, definitions: Seq<Wire>, arguments: Seq<Wire>,
    states: Range<usize>, gates: Range<usize>, outputs: Seq<Wire>,
)
    requires
        states.start <= states.end,
        range.start <= range.end <= wires.len(),
        drivers.len() == range.end - range.start,
        resolved_bits(symbolic, definitions, arguments),
        instance_outputs_match(wires,
            clocked_stateful_arguments(arguments, states.start, (states.end - states.start) as nat), gates.start, outputs),
        forall|i: int| 0 <= i < drivers.len() ==> Some(#[trigger] drivers[i])
            == relocated_child_driver(wires[range.start + i], symbolic, states, gates),
    ensures resolved_bits(drivers, definitions, outputs.subrange(range.start as int, range.end as int)),
{
    let placed = clocked_stateful_arguments(arguments, states.start, (states.end - states.start) as nat);
    let port = outputs.subrange(range.start as int, range.end as int);
    assert forall|i: int| 0 <= i < port.len() implies
        resolved_driver(drivers[i], definitions) == Some(#[trigger] port[i]) by {
        child_driver_resolves_to_instance(wires[range.start + i], symbolic, definitions,
            arguments, states, gates, drivers[i]);
        assert(port[i] == outputs[range.start + i]);
        assert(outputs[range.start + i] == instance_wire(wires[range.start + i], placed, gates.start));
    };
}

} // verus!
