//! モジュールの各状態素子に、増補入力列上の出力区間を割り当てる。

use super::{ModuleCalls, ModuleCallsError, UseAliases, copy_location};
use crate::netlist::{ClockedStorageInputs, Wire};
#[cfg(verus_only)]
use crate::netlist::{clocked_storage_output_width, clocked_storage_width_concat, clocked_storage_width_push};
use crate::project::{DefinitionPosition, LocatedName, ModuleBodyPosition, ModuleCallTarget,
    ResolvedPortType, StorageSignature, StructureTypeError};
#[cfg(verus_only)]
use crate::project::{StructureLayouts, location_in_source};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

verus! {

/// モジュール内で状態素子を呼び出した位置と、出力ビットの配置。
#[derive(Debug)]
pub struct ClockedStoragePlacement<'p, 'a> {
    /// 本体と断片を通した呼び出し一覧の添字。
    pub call_index: usize,
    /// 呼び出しを含むファイル、定義、参照の添字。
    pub at: DefinitionPosition,
    /// 呼び出し式全体の UTF-8 半開バイト範囲。
    pub call: LocatedName<'p, 'a>,
    /// RAM のアドレス幅。ラッチでは `None`。
    pub address_bits: Option<u64>,
    /// 増補入力列で状態素子の出力が占める半開範囲。低位ビットから並ぶ。
    pub outputs: Range<usize>,
}

/// 一つのモジュールが直接呼び出す状態素子の配置。
#[derive(Debug)]
pub struct ClockedStorageLayout<'p, 'a> {
    /// 外部入力のビット数。状態素子の出力はこの直後から並ぶ。
    pub external_inputs: usize,
    /// 外部入力と状態素子の出力を合わせたビット数。
    pub augmented_inputs: usize,
    /// ソース上の呼び出し順に並ぶ状態素子。
    pub instances: Vec<ClockedStoragePlacement<'p, 'a>>,
    /// 呼び出し一覧の各行に対応する状態素子の添字。通常の回路呼び出しは `None`。
    pub by_call: Vec<Option<usize>>,
}

/// 状態素子の出力範囲を決めるまでに見つかった違反。
#[derive(Debug)]
pub enum ClockedStorageLayoutError<'p, 'a> {
    /// 外部入力のビット数が増補入力列の上限を超えた。
    ExternalCapacity,
    /// モジュールの配線・型・呼び出しの検査に失敗した。
    Calls(ModuleCallsError<'p, 'a>),
    /// RAM のデータ型に使う構造体の配置を検査できなかった。
    Structure {
        /// RAM を呼び出した位置。
        call: LocatedName<'p, 'a>,
        /// 構造体の宣言などに対応する診断。
        reason: StructureTypeError<'p, 'a>,
    },
    /// 状態素子の出力ビットを加えると増補入力列の上限を超える。
    Capacity {
        /// 最初に上限を超えた状態素子の呼び出し。
        call: LocatedName<'p, 'a>,
        /// 宣言にある出力幅またはデータ型の注釈。
        annotation: LocatedName<'p, 'a>,
        /// 状態素子を置く前に使用済みのビット数。
        used: usize,
        /// 状態素子の出力幅。
        width: u64,
    },
}

impl ClockedStoragePlacement<'_, '_> {
    /// この状態素子の出力ビットを読む配線を返す。
    ///
    /// `bit` は0を最下位とする出力添字。範囲外、または空の範囲なら `None` を返す。
    pub fn output_wire(&self, bit: usize) -> (wire: Option<Wire>)
        ensures wire == if self.outputs.start + bit < self.outputs.end {
            Some(Wire::Input((self.outputs.start + bit) as usize))
        } else { None },
    {
        if self.outputs.start >= self.outputs.end || bit >= self.outputs.end - self.outputs.start {
            None
        } else {
            Some(Wire::Input(self.outputs.start + bit))
        }
    }

    /// 配線をアドレス、データ、許可入力に分けて VM に渡せる形にする。
    ///
    /// 配線はポート順で、各ポート内では低位ビットから並ぶ。ラッチではアドレス列を省く。
    /// 空の出力区間や、期待した入力幅と異なる配線列には `None` を返す。
    pub fn storage_inputs(&self, wires: &[Wire]) -> (inputs: Option<ClockedStorageInputs>)
        ensures self.storage_inputs_match(wires@, inputs),
    {
        if self.outputs.start >= self.outputs.end { return None; }
        let width = self.outputs.end - self.outputs.start;
        let address = self.address_bits.unwrap_or(0);
        if address > wires.len() as u64 { return None; }
        let address = address as usize;
        if wires.len() - address <= width || wires.len() - address - width != 1 { return None; }
        let end = address + width;
        let address = if self.address_bits.is_some() { Some(copy_storage_wires(wires, 0, address)) } else { None };
        let data = copy_storage_wires(wires, end - width, end);
        Some(ClockedStorageInputs { address, data, enable: wires[end] })
    }

    /// 型から求めた幅と、低位ビットを先頭にした入力配線との対応。
    pub closed spec fn storage_inputs_match(&self, wires: Seq<Wire>, inputs: Option<ClockedStorageInputs>) -> bool {
        let address = self.address_bits.unwrap_or(0) as int;
        let width = self.outputs.end - self.outputs.start;
        let end = address + width;
        if width <= 0 || wires.len() != end + 1 {
            inputs.is_none()
        } else {
            inputs matches Some(ports)
                && ports.enable == wires[end]
                && ports.data@ == wires.subrange(address, end)
                && match ports.address {
                    Some(wires_at) => self.address_bits.is_some() && wires_at@ == wires.take(address),
                    None => self.address_bits.is_none(),
                }
        }
    }

    /// VM に渡すデータ配線の幅は、この素子に割り当てた登録出力の幅に等しい。
    pub(super) proof fn storage_inputs_width(&self, wires: Seq<Wire>, inputs: ClockedStorageInputs)
        requires self.storage_inputs_match(wires, Some(inputs)),
        ensures self.outputs.start + inputs.data@.len() == self.outputs.end,
    {
    }
}

fn copy_storage_wires(wires: &[Wire], start: usize, end: usize) -> (out: Vec<Wire>)
    requires start <= end <= wires@.len(),
    ensures out@ == wires@.subrange(start as int, end as int),
{
    let mut out = Vec::with_capacity(end - start);
    let mut i = start;
    while i < end
        invariant start <= i <= end <= wires@.len(), out@ == wires@.subrange(start as int, i as int),
        decreases end - i,
    {
        out.push(wires[i]);
        assert(out@ =~= wires@.subrange(start as int, i + 1));
        i += 1;
    }
    out
}

spec fn row_site(checked: &ModuleCalls, index: int, site: LocatedName) -> bool {
    let signature = checked.calls@[index].inputs.ports.signature;
    *site.source == *signature.source && site.span == signature.call.span
        && location_in_source(site)
}

spec fn row_at(checked: &ModuleCalls, index: int) -> bool {
    checked.calls@[index].inputs.ports.signature.target is StateElement
}

spec fn data_annotation<'p, 'a>(storage: StorageSignature<'p, 'a>) -> LocatedName<'p, 'a> {
    match storage {
        StorageSignature::Latch { annotation, .. } => annotation,
        StorageSignature::Memory { data_annotation, .. } => data_annotation,
    }
}

spec fn requires_structure(checked: &ModuleCalls, index: int) -> bool {
    checked.calls@[index].inputs.ports.signature.target matches
        ModuleCallTarget::StateElement { storage: StorageSignature::Memory { data: ResolvedPortType::Struct { .. }, .. }, .. }
}

#[verifier::opaque]
spec fn ranges_follow(instances: Seq<ClockedStoragePlacement>, external: usize) -> bool {
    &&& instances.len() > 0 ==> instances[0].outputs.start == external
    &&& forall|i: int| 0 <= i < instances.len() ==>
        (#[trigger] instances[i]).outputs.start < instances[i].outputs.end
    &&& forall|i: int| #![trigger instances[i], instances[i + 1]]
        0 <= i && i + 1 < instances.len() ==>
            instances[i].outputs.end == instances[i + 1].outputs.start
                && instances[i].call_index < instances[i + 1].call_index
}

proof fn extend_storage_ranges(instances: Seq<ClockedStoragePlacement>, external: usize,
    next: usize, added: ClockedStoragePlacement,
)
    requires
        ranges_follow(instances, external), added.outputs.start == next < added.outputs.end,
        instances.len() == 0 ==> next == external,
        instances.len() > 0 ==> next == instances.last().outputs.end && instances.last().call_index < added.call_index,
    ensures ranges_follow(instances.push(added), external),
{
    reveal(ranges_follow);
    let placed = instances.push(added);
    assert forall|i: int| 0 <= i < placed.len() implies
        (#[trigger] placed[i]).outputs.start < placed[i].outputs.end by {
        if i < instances.len() { assert(placed[i] == instances[i]); }
    };
    assert forall|i: int| #![trigger placed[i], placed[i + 1]]
        0 <= i && i + 1 < placed.len() implies
            placed[i].outputs.end == placed[i + 1].outputs.start
                && placed[i].call_index < placed[i + 1].call_index by {
        assert(placed[i] == instances[i]);
        if i + 1 < instances.len() {
            assert(placed[i + 1] == instances[i + 1]);
        } else {
            assert(instances[i] == instances.last());
            assert(placed[i + 1] == added);
        }
    };
}

proof fn storage_neighbor(instances: Seq<ClockedStoragePlacement>, external: usize, i: int)
    requires ranges_follow(instances, external), 0 <= i && i + 1 < instances.len(),
    ensures instances[i].outputs.end == instances[i + 1].outputs.start,
        instances[i].call_index < instances[i + 1].call_index,
{
    reveal(ranges_follow);
}

proof fn storage_index_within_call_order(instances: Seq<ClockedStoragePlacement>, external: usize, i: int)
    requires ranges_follow(instances, external), 0 <= i < instances.len(),
    ensures i <= instances[i].call_index,
    decreases i,
{
    if i > 0 {
        storage_index_within_call_order(instances, external, i - 1);
        storage_neighbor(instances, external, i - 1);
    }
}

proof fn placed_output_width(instances: Seq<ClockedStoragePlacement>, external: usize,
    wiring: Seq<ClockedStorageInputs>, count: nat)
    requires
        ranges_follow(instances, external), wiring.len() == instances.len(), count <= wiring.len(),
        forall|i: int| 0 <= i < count ==>
            (#[trigger] instances[i]).outputs.start + (#[trigger] wiring[i]).data@.len() == instances[i].outputs.end,
    ensures external + clocked_storage_output_width(wiring.take(count as int))
        == if count == 0 { external } else { instances[count - 1].outputs.end },
    decreases count,
{
    if count == 0 {
        let empty = wiring.take(0);
        assert(empty + empty =~= empty);
        clocked_storage_width_concat(empty, empty);
    } else {
        let i = (count - 1) as int;
        placed_output_width(instances, external, wiring, i as nat);
        if i == 0 {
            reveal(ranges_follow);
        } else {
            storage_neighbor(instances, external, i - 1);
        }
        let prior = wiring.take(i);
        assert(prior.push(wiring[i]) =~= wiring.take(count as int));
        clocked_storage_width_push(prior, wiring[i]);
    }
}

proof fn ordered_storage_ranges(instances: Seq<ClockedStoragePlacement>, external: usize, first: int, later: int)
    requires ranges_follow(instances, external), 0 <= first < later < instances.len(),
    ensures instances[first].call_index < instances[later].call_index,
        instances[first].outputs.end <= instances[later].outputs.start,
    decreases later - first,
{
    reveal(ranges_follow);
    storage_neighbor(instances, external, later - 1);
    if first < later - 1 {
        ordered_storage_ranges(instances, external, first, later - 1);
        assert(instances[later - 1].outputs.start < instances[later - 1].outputs.end);
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn placement_width_matches(&self, storage: StorageSignature, limit: u64, address: Option<u64>, width: nat) -> bool {
        &&& width > 0
        &&& match storage {
            StorageSignature::Latch { width: expected, .. } => address.is_none() && width == expected,
            StorageSignature::Memory { address: expected, data, .. } =>
                address == Some(expected) && match data {
                    ResolvedPortType::Bits(bits) => width == bits,
                    _ => exists|layouts: StructureLayouts| #[trigger] self.structure_types_match(limit, Ok(layouts))
                        && self.layout_port_width_matches(&layouts, data, width as int),
                },
        }
    }

    #[verifier::opaque]
    pub(super) closed spec fn placement_matches(&self, checked: &ModuleCalls, limit: u64, instance: ClockedStoragePlacement) -> bool {
        let index = instance.call_index as int;
        let row = checked.calls@[index];
        &&& 0 <= index < checked.calls@.len()
        &&& instance.at == row.at && row_site(checked, index, instance.call)
        &&& instance.outputs.start < instance.outputs.end
        &&& row.inputs.ports.signature.target matches ModuleCallTarget::StateElement { storage, .. }
        &&& self.placement_width_matches(storage, limit, instance.address_bits,
            (instance.outputs.end - instance.outputs.start) as nat)
    }

    #[verifier::opaque]
    spec fn placed_prefix(&self, checked: &ModuleCalls, limit: u64, calls: Seq<Option<usize>>,
        instances: Seq<ClockedStoragePlacement>, external: usize, next: usize,
    ) -> bool {
        &&& calls.len() <= checked.calls@.len()
        &&& next == if instances.len() == 0 { external } else { instances.last().outputs.end }
        &&& ranges_follow(instances, external)
        &&& forall|i: int| 0 <= i < instances.len() ==> {
            let instance = #[trigger] instances[i];
            &&& self.placement_matches(checked, limit, instance)
            &&& instance.call_index < calls.len()
            &&& calls[instance.call_index as int] == Some(i as usize)
        }
        &&& forall|j: int| 0 <= j < calls.len() ==> match #[trigger] calls[j] {
            Some(i) => i < instances.len() && instances[i as int].call_index == j
                && row_at(checked, j),
            None => !row_at(checked, j),
        }
    }

    #[verifier::spinoff_prover]
    proof fn append_storage_placement(&self, checked: &ModuleCalls, limit: u64, calls: Seq<Option<usize>>,
        instances: Seq<ClockedStoragePlacement>, external: usize, next: usize, added: ClockedStoragePlacement,
    )
        requires
            self.placed_prefix(checked, limit, calls, instances, external, next),
            calls.len() < checked.calls@.len(),
            instances.len() <= usize::MAX,
            added.call_index == calls.len() && added.outputs.start == next && next < added.outputs.end,
            row_at(checked, added.call_index as int),
            self.placement_matches(checked, limit, added),
        ensures self.placed_prefix(checked, limit, calls.push(Some(instances.len() as usize)),
            instances.push(added), external, added.outputs.end),
    {
        reveal(UseAliases::placed_prefix);
        let placed = instances.push(added);
        let mapped = calls.push(Some(instances.len() as usize));
        extend_storage_ranges(instances, external, next, added);
        assert forall|j: int| 0 <= j < mapped.len() implies match #[trigger] mapped[j] {
            Some(i) => i < placed.len() && placed[i as int].call_index == j && row_at(checked, j),
            None => !row_at(checked, j),
        } by {
            if j < calls.len() {
                assert(mapped[j] == calls[j]);
                if let Some(i) = calls[j] { assert(placed[i as int] == instances[i as int]); }
            } else {
                assert(placed[instances.len() as int] == added);
            }
        };
        assert forall|i: int| 0 <= i < placed.len() implies {
            let instance = #[trigger] placed[i];
            &&& self.placement_matches(checked, limit, instance)
            &&& instance.call_index < mapped.len()
            &&& mapped[instance.call_index as int] == Some(i as usize)
        } by {
            if i < instances.len() {
                assert(placed[i] == instances[i]);
                assert(mapped[placed[i].call_index as int] == calls[instances[i].call_index as int]);
            }
        };
    }

    proof fn skip_storage_call(&self, checked: &ModuleCalls, limit: u64, calls: Seq<Option<usize>>,
        instances: Seq<ClockedStoragePlacement>, external: usize, next: usize,
    )
        requires
            self.placed_prefix(checked, limit, calls, instances, external, next),
            calls.len() < checked.calls@.len(),
            !row_at(checked, calls.len() as int),
        ensures self.placed_prefix(checked, limit, calls.push(None), instances, external, next),
    {
        reveal(UseAliases::placed_prefix);
        let mapped = calls.push(None);
        assert forall|j: int| 0 <= j < mapped.len() implies match #[trigger] mapped[j] {
            Some(i) => i < instances.len() && instances[i as int].call_index == j && row_at(checked, j),
            None => !row_at(checked, j),
        } by {
            if j < calls.len() { assert(mapped[j] == calls[j]); }
        };
    }

    #[verifier::opaque]
    spec fn capacity_at(&self, checked: &ModuleCalls, limit: u64, external: usize,
        calls: Seq<Option<usize>>, prefix: Seq<ClockedStoragePlacement>, call: LocatedName,
        annotation: LocatedName, used: usize, width: u64,
    ) -> bool {
        let i = calls.len() as int;
        &&& i < checked.calls@.len() && row_site(checked, i, call)
        &&& self.placed_prefix(checked, limit, calls, prefix, external, used)
        &&& checked.calls@[i].inputs.ports.signature.target matches ModuleCallTarget::StateElement { storage, .. }
        &&& annotation == data_annotation(storage)
        &&& self.placement_width_matches(storage, limit,
            match storage { StorageSignature::Latch { .. } => None, StorageSignature::Memory { address, .. } => Some(address) },
            width as nat)
    }

    #[verifier::opaque]
    spec fn storage_capacity_failure(&self, checked: &ModuleCalls, limit: u64, external: usize, capacity: usize,
        call: LocatedName, annotation: LocatedName, used: usize, width: u64,
    ) -> bool {
        &&& used <= capacity < used as nat + width as nat
        &&& exists|calls: Seq<Option<usize>>, prefix: Seq<ClockedStoragePlacement>|
            #[trigger] self.capacity_at(checked, limit, external, calls, prefix, call, annotation, used, width)
    }

    #[verifier::opaque]
    /// 配置または診断を、同じモジュールの呼び出し一覧に対応付ける。
    pub(super) closed spec fn storage_on_checked(&self, checked: &ModuleCalls, limit: u64, external: usize, capacity: usize,
        result: Result<ClockedStorageLayout, ClockedStorageLayoutError>,
    ) -> bool {
        match result {
            Ok(plan) => plan.external_inputs == external && plan.augmented_inputs <= capacity
                && plan.by_call@.len() == checked.calls@.len()
                && self.placed_prefix(checked, limit, plan.by_call@, plan.instances@, external, plan.augmented_inputs),
            Err(ClockedStorageLayoutError::Capacity { call, annotation, used, width }) =>
                self.storage_capacity_failure(checked, limit, external, capacity, call, annotation, used, width),
            Err(ClockedStorageLayoutError::Structure { call, reason }) =>
                self.structure_types_match(limit, Err(reason))
                    && exists|i: int, prefix: Seq<ClockedStoragePlacement>, calls: Seq<Option<usize>>, used: usize| {
                        &&& 0 <= i < checked.calls@.len() && #[trigger] row_site(checked, i, call)
                        &&& used <= capacity
                        &&& calls.len() == i
                    &&& #[trigger] self.placed_prefix(checked, limit, calls, prefix, external, used)
                        &&& requires_structure(checked, i)
                        &&& forall|j: int| 0 <= j < i ==> !#[trigger] requires_structure(checked, j)
                    },
            _ => false,
        }
    }

    /// 配置通りの幅で素子を束ねると、増補入力の末尾は計画した位置と一致する。
    pub(super) proof fn placed_storage_width_evidence(&self, checked: &ModuleCalls, limit: u64, external: usize,
        capacity: usize, plan: &ClockedStorageLayout, wiring: Seq<ClockedStorageInputs>)
        requires
            self.storage_on_checked(checked, limit, external, capacity, Ok(*plan)),
            wiring.len() == plan.instances@.len(),
            forall|i: int| 0 <= i < wiring.len() ==>
                (#[trigger] plan.instances@[i]).outputs.start + (#[trigger] wiring[i]).data@.len()
                    == plan.instances@[i].outputs.end,
        ensures external + clocked_storage_output_width(wiring) == plan.augmented_inputs,
    {
        reveal(UseAliases::storage_on_checked);
        reveal(UseAliases::placed_prefix);
        placed_output_width(plan.instances@, external, wiring, wiring.len());
        assert(wiring.take(wiring.len() as int) =~= wiring);
    }

    /// 配置の添字から呼び出しへ戻ると、同じ状態素子の添字が得られる。
    pub(super) proof fn storage_layout_call_for_instance(
        &self, checked: &ModuleCalls, limit: u64, external: usize, capacity: usize,
        plan: &ClockedStorageLayout, index: int,
    ) -> (call: int)
        requires
            self.storage_on_checked(checked, limit, external, capacity, Ok(*plan)),
            0 <= index < plan.instances@.len(),
        ensures
            0 <= index <= call < checked.calls@.len(),
            call == plan.instances@[index].call_index,
            plan.by_call@[call] == Some(index as usize),
    {
        reveal(UseAliases::storage_on_checked);
        reveal(UseAliases::placed_prefix);
        let instances = plan.instances@;
        storage_index_within_call_order(instances, external, index);
        instances[index].call_index as int
    }

    /// 状態素子の区間が、外部入力と先行する素子の登録出力の直後から始まることを示す。
    pub(super) proof fn placed_storage_range_evidence(
        &self, checked: &ModuleCalls, limit: u64, external: usize, capacity: usize,
        plan: &ClockedStorageLayout, wiring: Seq<ClockedStorageInputs>, index: int,
    )
        requires
            self.storage_on_checked(checked, limit, external, capacity, Ok(*plan)),
            wiring.len() == plan.instances@.len(),
            0 <= index < wiring.len(),
            forall|i: int| 0 <= i < wiring.len() ==>
                (#[trigger] plan.instances@[i]).outputs.start + (#[trigger] wiring[i]).data@.len()
                    == plan.instances@[i].outputs.end,
        ensures
            plan.instances@[index].outputs.start == external + clocked_storage_output_width(wiring.take(index)),
            plan.instances@[index].outputs.start < plan.instances@[index].outputs.end,
    {
        reveal(UseAliases::storage_on_checked);
        reveal(UseAliases::placed_prefix);
        reveal(ranges_follow);
        let instances = plan.instances@;
        placed_output_width(instances, external, wiring, index as nat);
        if index == 0 {
            assert(instances[index].outputs.start == external);
        } else {
            storage_neighbor(instances, external, index - 1);
            assert(instances[index].outputs.start == instances[index - 1].outputs.end);
        }
    }

    /// 呼び出し番号から、同じ状態素子に割り当てた増補入力の範囲を取り出す。
    pub(super) proof fn storage_layout_call(
        &self, checked: &ModuleCalls, limit: u64, external: usize, capacity: usize,
        layout: &ClockedStorageLayout, call: usize,
    )
        requires
            self.storage_on_checked(checked, limit, external, capacity, Ok(*layout)),
            call < checked.calls@.len(),
        ensures
            layout.by_call@.len() == checked.calls@.len(),
            layout.external_inputs == external,
            layout.augmented_inputs <= capacity,
            layout.by_call@[call as int].is_some() <==>
                checked.calls@[call as int].inputs.ports.signature.target is StateElement,
            layout.by_call@[call as int] matches Some(index) ==> {
                &&& index < layout.instances@.len()
                &&& layout.instances@[index as int].call_index == call
                &&& layout.instances@[index as int].at == checked.calls@[call as int].at
                &&& self.placement_matches(checked, limit, layout.instances@[index as int])
                &&& external <= layout.instances@[index as int].outputs.start < layout.instances@[index as int].outputs.end
                    <= layout.augmented_inputs
            },
    {
        reveal(UseAliases::storage_on_checked);
        reveal(UseAliases::placed_prefix);
        let instances = layout.instances@;
        if let Some(index) = layout.by_call@[call as int] {
            let item = instances[index as int];
            reveal(UseAliases::placement_matches);
            if index == 0 {
                reveal(ranges_follow);
            } else {
                ordered_storage_ranges(instances, external, 0, index as int);
                reveal(ranges_follow);
            }
            if index as int + 1 < instances.len() {
                ordered_storage_ranges(instances, external, index as int, instances.len() - 1);
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn storage_capacity_error(
        &self, checked: &ModuleCalls, limit: u64, external: usize, capacity: usize,
        calls: Seq<Option<usize>>, instances: Seq<ClockedStoragePlacement>, storage: StorageSignature,
        call: LocatedName, annotation: LocatedName, used: usize, width: u64,
    )
        requires
            self.placed_prefix(checked, limit, calls, instances, external, used),
            calls.len() < checked.calls@.len(),
            row_site(checked, calls.len() as int, call),
            checked.calls@[calls.len() as int].inputs.ports.signature.target matches
                ModuleCallTarget::StateElement { storage: actual, .. } && actual == storage,
            annotation == data_annotation(storage),
            used <= capacity < used as nat + width as nat,
            self.placement_width_matches(storage, limit,
                match storage { StorageSignature::Latch { .. } => None, StorageSignature::Memory { address, .. } => Some(address) },
                width as nat),
        ensures self.storage_capacity_failure(checked, limit, external, capacity, call, annotation, used, width),
    {
        assert(self.capacity_at(checked, limit, external, calls, instances, call, annotation, used, width)) by {
            reveal(UseAliases::capacity_at);
        };
        assert(exists|mapped: Seq<Option<usize>>, prefix: Seq<ClockedStoragePlacement>|
            #[trigger] self.capacity_at(checked, limit, external, mapped, prefix, call, annotation, used, width));
        reveal(UseAliases::storage_capacity_failure);
    }

    /// 名前と型を検査した呼び出しから、状態素子の出力範囲を決める。
    #[verifier::spinoff_prover]
    pub(super) fn place_clocked_storage(
        &self, _owner: ModuleBodyPosition, checked: &ModuleCalls<'p, 'a>, limit: u64, external: usize, capacity: usize,
    ) -> (result: Result<ClockedStorageLayout<'p, 'a>, ClockedStorageLayoutError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(_owner, limit, Ok(Some(*checked))), external <= capacity,
        ensures self.storage_on_checked(checked, limit, external, capacity, result),
    {
        let mut instances: Vec<ClockedStoragePlacement<'p, 'a>> = Vec::new();
        let mut by_call: Vec<Option<usize>> = Vec::new();
        let mut layouts = None;
        let mut next = external;
        let mut index = 0;
        assert(self.placed_prefix(checked, limit, by_call@, instances@, external, next)) by {
            reveal(UseAliases::placed_prefix);
            reveal(ranges_follow);
        };
        while index < checked.calls.len()
            invariant
                self.can_resolve(), self.module_calls_result(_owner, limit, Ok(Some(*checked))),
                index == by_call@.len() <= checked.calls@.len(),
                next <= capacity,
                self.placed_prefix(checked, limit, by_call@, instances@, external, next),
                layouts matches Some(layouts) ==> self.structure_types_match(limit, Ok(layouts)),
                layouts.is_none() ==> forall|j: int| 0 <= j < index ==> !#[trigger] requires_structure(checked, j),
            decreases checked.calls@.len() - index,
        {
            let row = &checked.calls[index];
            let signature = &row.inputs.ports.signature;
            if let ModuleCallTarget::StateElement { position: _source_position, storage, .. } = &signature.target {
                proof {
                    self.module_calls_item_evidence(_owner, limit, checked, index as int);
                    self.module_call_ports_evidence(row.at, limit, row.inputs.ports);
                    self.module_call_site_evidence(row.at, limit, *signature);
                    self.storage_signature_sites(_source_position.file, _source_position.entry, limit, *storage);
                }
                let call = LocatedName { source: signature.source, span: signature.call.span.start..signature.call.span.end };
                assert(row_site(checked, index as int, call));
                let (address_bits, width, annotation) = match storage {
                    StorageSignature::Latch { width, annotation } => (None, *width, annotation),
                    StorageSignature::Memory { address, data, data_annotation, .. } => {
                        let width = match data {
                            ResolvedPortType::Bits(bits) => *bits,
                            ResolvedPortType::Struct { source, form } => {
                                if layouts.is_none() {
                                    match self.check_structure_types(limit) {
                                        Ok(checked) => layouts = Some(checked),
                                        Err(reason) => {
                                            let error = ClockedStorageLayoutError::Structure { call, reason };
                                            assert(requires_structure(checked, index as int));
                                            assert(self.storage_on_checked(checked, limit, external, capacity, Err(error))) by {
                                                reveal(UseAliases::storage_on_checked);
                                            };
                                            return Err(error);
                                        },
                                    }
                                }
                                let Some(layouts) = &layouts else { unreachable!() };
                                let width = self.structure_port_width(source, form, layouts, limit);
                                width
                            },
                        };
                        (Some(*address), width, data_annotation)
                    },
                };
                assert(self.placement_width_matches(*storage, limit, address_bits, width as nat));
                if width > (capacity - next) as u64 {
                    let annotation = copy_location(annotation);
                    proof {
                        self.storage_capacity_error(checked, limit, external, capacity, by_call@, instances@,
                            *storage, call, annotation, next, width);
                    }
                    let error = ClockedStorageLayoutError::Capacity { call, annotation, used: next, width };
                    assert(self.storage_on_checked(checked, limit, external, capacity, Err(error))) by {
                        reveal(UseAliases::storage_on_checked);
                    };
                    return Err(error);
                }
                let end = next + width as usize;
                let placement = ClockedStoragePlacement {
                    call_index: index, at: row.at, call, address_bits, outputs: next..end,
                };
                assert(self.placement_matches(checked, limit, placement)) by {
                    reveal(UseAliases::placement_matches);
                };
                let instance = instances.len();
                proof { self.append_storage_placement(checked, limit, by_call@, instances@, external, next, placement); }
                by_call.push(Some(instance));
                instances.push(placement);
                next = end;
            } else {
                assert(!row_at(checked, index as int));
                proof { self.skip_storage_call(checked, limit, by_call@, instances@, external, next); }
                by_call.push(None);
            }
            index += 1;
        }
        let plan = ClockedStorageLayout { external_inputs: external, augmented_inputs: next, instances, by_call };
        assert(self.storage_on_checked(checked, limit, external, capacity, Ok(plan))) by {
            reveal(UseAliases::storage_on_checked);
        };
        Ok(plan)
    }

    /// 配置または診断が、型検査済みの呼び出しとその出力幅に対応することを表す。
    pub closed spec fn clocked_storage_layout_result(&self, owner: ModuleBodyPosition, limit: u64, external: usize, capacity: usize,
        result: Result<Option<ClockedStorageLayout>, ClockedStorageLayoutError>,
    ) -> bool {
        if external > capacity {
            result matches Err(ClockedStorageLayoutError::ExternalCapacity)
        } else {
            match result {
                Ok(None) => self.module_calls_result(owner, limit, Ok(None)),
                Err(ClockedStorageLayoutError::Calls(error)) => self.module_calls_result(owner, limit, Err(error)),
                _ => exists|checked: ModuleCalls|
                    #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
                        && match result {
                            Ok(Some(plan)) => self.storage_on_checked(&checked, limit, external, capacity, Ok(plan)),
                            Err(error) => self.storage_on_checked(&checked, limit, external, capacity, Err(error)),
                            _ => false,
                        },
            }
        }
    }

    /// 異なる配置は異なる呼び出しを指し、出力区間は呼び出し順に並んで重ならない。
    pub proof fn clocked_storage_placements_distinct(
        &self, owner: ModuleBodyPosition, limit: u64, external: usize, capacity: usize,
        plan: &ClockedStorageLayout, first: int, later: int,
    )
        requires
            self.can_resolve(),
            self.clocked_storage_layout_result(owner, limit, external, capacity, Ok(Some(*plan))),
            0 <= first < later < plan.instances@.len(),
        ensures
            plan.instances@[first].at != plan.instances@[later].at,
            plan.instances@[first].outputs.end <= plan.instances@[later].outputs.start,
    {
        reveal(UseAliases::storage_on_checked);
        reveal(UseAliases::placed_prefix);
        reveal(UseAliases::placement_matches);
        let checked = choose|checked: ModuleCalls|
            #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
                && self.storage_on_checked(&checked, limit, external, capacity, Ok(*plan));
        self.storage_placements_on_calls_distinct(owner, limit, external, capacity, &checked, plan, first, later);
    }

    /// 同じ型検査結果を使い、二つの配置が異なる呼び出しを指すことを示す。
    pub(super) proof fn storage_placements_on_calls_distinct(
        &self, owner: ModuleBodyPosition, limit: u64, external: usize, capacity: usize,
        checked: &ModuleCalls, plan: &ClockedStorageLayout, first: int, later: int,
    )
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.storage_on_checked(checked, limit, external, capacity, Ok(*plan)),
            0 <= first < later < plan.instances@.len(),
        ensures
            plan.instances@[first].at != plan.instances@[later].at,
            plan.instances@[first].outputs.end <= plan.instances@[later].outputs.start,
    {
        reveal(UseAliases::storage_on_checked);
        reveal(UseAliases::placed_prefix);
        reveal(UseAliases::placement_matches);
        ordered_storage_ranges(plan.instances@, external, first, later);
        let a = plan.instances@[first].call_index as int;
        let b = plan.instances@[later].call_index as int;
        self.module_call_sites_distinct(owner, limit, checked, a, b);
    }

    /// モジュールが直接呼び出す状態素子の出力を増補入力列に配置する。
    ///
    /// `external` は平坦化済みの外部入力幅。入出力の型検査後、本体と断片の呼び出し順に置く。
    /// モジュールが存在しない場合は `Ok(None)`。子モジュールの内部は、展開時に呼び出しごとに配置する。
    ///
    /// # Errors
    ///
    /// 外部入力の幅、モジュールの呼び出しを先に検査する。次いで呼び出し順にデータ型の配置と出力幅を確認する。
    /// `capacity` は増補入力の上限。RAM の記憶容量は VM を初期化するときに検査する。
    pub fn plan_clocked_storage(&self, owner: ModuleBodyPosition, limit: u64, external: usize, capacity: usize)
        -> (result: Result<Option<ClockedStorageLayout<'p, 'a>>, ClockedStorageLayoutError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.clocked_storage_layout_result(owner, limit, external, capacity, result),
    {
        if external > capacity { return Err(ClockedStorageLayoutError::ExternalCapacity); }
        let checked = match self.check_module_calls(owner, limit) {
            Ok(Some(checked)) => checked,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ClockedStorageLayoutError::Calls(error)),
        };
        let placed = self.place_clocked_storage(owner, &checked, limit, external, capacity);
        let ghost placed_model = placed;
        let result = match placed {
            Ok(plan) => Ok(Some(plan)),
            Err(error) => Err(error),
        };
        assert(self.storage_on_checked(&checked, limit, external, capacity, placed_model));
        assert(self.clocked_storage_layout_result(owner, limit, external, capacity, result)) by {
            reveal(UseAliases::storage_on_checked);
        };
        result
    }
}

} // verus!
