//! ソース側の直結を解決し、展開後の配線と照合する。

use super::super::super::clocked_plan::{clocked_alias_ranks, clocked_wire_at, clocked_wires_match};
use crate::netlist::{
    ClockedStorageInputs, SourceVmLayout, SourceVmWire, Wire, source_vm_row_pair, source_vm_terminal_pair,
};
use crate::project::ClockedWireDriver;
use vstd::prelude::*;

verus! {

/// 直接読める端子か、別の定義ビットへの直結。
pub(super) enum SourceVmLink {
    Terminal(SourceVmWire),
    Alias(usize),
}

/// ソースの端子と配線計画の終点が対応し、直結先の添字が同じことを表す。
pub(super) open spec fn source_vm_link_pair(
    external: usize, storage: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    source: SourceVmLink, driver: ClockedWireDriver,
) -> bool {
    match (source, driver) {
        (SourceVmLink::Terminal(original), ClockedWireDriver::Terminal(flat)) =>
            source_vm_terminal_pair(external, storage, layout, original, flat),
        (SourceVmLink::Alias(a), ClockedWireDriver::Alias(b)) => a == b,
        _ => false,
    }
}

/// 解決したソース配線は、各定義の直接端子または直結先と一致する。
pub(super) open spec fn source_vm_links_resolved(links: Seq<SourceVmLink>, wires: Seq<SourceVmWire>) -> bool {
    &&& wires.len() == links.len()
    &&& forall|i: int| 0 <= i < links.len() ==> match #[trigger] links[i] {
        SourceVmLink::Terminal(wire) => wires[i] == wire,
        SourceVmLink::Alias(target) => target < wires.len() && wires[i] == wires[target as int],
    }
}

spec fn source_vm_link_ranks(links: Seq<SourceVmLink>, ranks: Seq<nat>) -> bool {
    &&& links.len() == ranks.len()
    &&& forall|i: int| 0 <= i < links.len() ==>
        ((#[trigger] links[i]) matches SourceVmLink::Alias(target) ==>
            target < links.len() && ranks[target as int] < ranks[i])
}

/// 直結先をたどり、ソース定義の終点を求める。
///
/// rank は終了を示すために使う。どの終点を返すかはソースの直結先と端子が決める。
spec fn source_vm_link_terminal(links: Seq<SourceVmLink>, ranks: Seq<nat>, i: int) -> SourceVmWire
    recommends source_vm_link_ranks(links, ranks), 0 <= i < links.len(),
    decreases ranks[i],
    when source_vm_link_ranks(links, ranks) && 0 <= i < links.len()
{
    match links[i] {
        SourceVmLink::Terminal(wire) => wire,
        SourceVmLink::Alias(target) => source_vm_link_terminal(links, ranks, target as int),
    }
}

proof fn follow_source_and_lowered_links(
    external: usize, storage: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    links: Seq<SourceVmLink>, ranks: Seq<nat>, drivers: Seq<ClockedWireDriver>, flat: Seq<Wire>, i: int,
)
    requires
        source_vm_link_ranks(links, ranks), 0 <= i < links.len(),
        links.len() == drivers.len() == flat.len(),
        clocked_wires_match(drivers, flat),
        forall|j: int| 0 <= j < links.len() ==>
            source_vm_link_pair(external, storage, layout, #[trigger] links[j], drivers[j]),
    ensures source_vm_terminal_pair(external, storage, layout, source_vm_link_terminal(links, ranks, i), flat[i]),
    decreases ranks[i],
{
    clocked_wire_at(drivers, flat, i);
    if let SourceVmLink::Alias(target) = links[i] {
        follow_source_and_lowered_links(external, storage, layout, links, ranks, drivers, flat, target as int);
    }
}

/// 同じ直結関係を解決すると、ソース上の終点と展開後の各配線の対応が保たれる。
pub(super) proof fn source_vm_resolve_links(
    external: usize, storage: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    links: Seq<SourceVmLink>, drivers: Seq<ClockedWireDriver>, flat: Seq<Wire>,
) -> (wires: Seq<SourceVmWire>)
    requires
        links.len() == drivers.len() == flat.len(),
        clocked_wires_match(drivers, flat),
        forall|i: int| 0 <= i < links.len() ==>
            source_vm_link_pair(external, storage, layout, #[trigger] links[i], drivers[i]),
    ensures source_vm_links_resolved(links, wires), source_vm_row_pair(external, storage, layout, wires, flat),
{
    let ranks = source_vm_ranks_for_links(external, storage, layout, links, drivers, flat);
    let wires = Seq::new(links.len(), |i: int| source_vm_link_terminal(links, ranks, i));
    assert forall|i: int| 0 <= i < links.len() implies match #[trigger] links[i] {
        SourceVmLink::Terminal(wire) => wires[i] == wire,
        SourceVmLink::Alias(target) => target < wires.len() && wires[i] == wires[target as int],
    } by {
        assert(wires[i] == source_vm_link_terminal(links, ranks, i));
    };
    assert forall|i: int| 0 <= i < flat.len() implies
        source_vm_terminal_pair(external, storage, layout, wires[i], #[trigger] flat[i]) by {
        follow_source_and_lowered_links(external, storage, layout, links, ranks, drivers, flat, i);
    };
    wires
}

proof fn source_vm_ranks_for_links(
    external: usize, storage: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    links: Seq<SourceVmLink>, drivers: Seq<ClockedWireDriver>, flat: Seq<Wire>,
) -> (ranks: Seq<nat>)
    requires
        links.len() == drivers.len() == flat.len(),
        clocked_wires_match(drivers, flat),
        forall|i: int| 0 <= i < links.len() ==>
            source_vm_link_pair(external, storage, layout, #[trigger] links[i], drivers[i]),
    ensures source_vm_link_ranks(links, ranks),
{
    let ranks = clocked_alias_ranks(drivers, flat);
    assert forall|i: int| 0 <= i < links.len() implies
        ((#[trigger] links[i]) matches SourceVmLink::Alias(target) ==>
            target < links.len() && ranks[target as int] < ranks[i]) by {
        if let SourceVmLink::Alias(target) = links[i] {
            assert(drivers[i] == ClockedWireDriver::Alias(target));
        }
    };
    ranks
}

proof fn source_vm_resolution_unique_at(
    links: Seq<SourceVmLink>, ranks: Seq<nat>, first: Seq<SourceVmWire>, second: Seq<SourceVmWire>, i: int,
)
    requires source_vm_link_ranks(links, ranks), source_vm_links_resolved(links, first),
        source_vm_links_resolved(links, second), 0 <= i < links.len(),
    ensures first[i] == second[i],
    decreases ranks[i],
{
    if let SourceVmLink::Alias(target) = links[i] {
        source_vm_resolution_unique_at(links, ranks, first, second, target as int);
    }
}

/// 当初のソースの直結関係を満たす二つの解決結果は、全ビットで一致する。
pub(super) proof fn source_vm_link_solutions_agree(
    external: usize, storage: Seq<ClockedStorageInputs>, layout: &SourceVmLayout,
    links: Seq<SourceVmLink>, drivers: Seq<ClockedWireDriver>, flat: Seq<Wire>,
    first: Seq<SourceVmWire>, second: Seq<SourceVmWire>,
)
    requires
        links.len() == drivers.len() == flat.len(),
        clocked_wires_match(drivers, flat),
        forall|i: int| 0 <= i < links.len() ==>
            source_vm_link_pair(external, storage, layout, #[trigger] links[i], drivers[i]),
        source_vm_links_resolved(links, first),
        source_vm_links_resolved(links, second),
    ensures first == second,
{
    let ranks = source_vm_ranks_for_links(external, storage, layout, links, drivers, flat);
    assert forall|i: int| 0 <= i < first.len() implies (#[trigger] first[i]) == second[i] by {
        source_vm_resolution_unique_at(links, ranks, first, second, i);
    };
    assert(first =~= second);
}

} // verus!
