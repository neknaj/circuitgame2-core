//! ルートの直接呼び出しと、VM に渡す状態素子の配置を対応付ける。

use super::{ClockedModuleNetwork, ClockedModuleVmLimits, ModuleCalls, UseAliases};
use crate::netlist::{ClockedStorageInputs, Wire};
use crate::project::{ClockedStorageLayout, ClockedStoragePlacement, ModuleCallTarget, ResolvedPortType,
    StorageSignature, StructureLayouts};
use vstd::prelude::*;

verus! {

pub(super) open spec fn storage_site_shape(site: ClockedStoragePlacement, wiring: ClockedStorageInputs) -> bool {
    &&& site.outputs.start < site.outputs.end
    &&& site.outputs.start + wiring.data@.len() == site.outputs.end
    &&& match (site.address_bits, wiring.address) {
        (Some(width), Some(pins)) => pins@.len() == width,
        (None, None) => true,
        _ => false,
    }
}

pub(super) proof fn storage_shape_from_row(site: &ClockedStoragePlacement, row: Seq<Wire>, wiring: ClockedStorageInputs)
    requires site.storage_inputs_match(row, Some(wiring)),
    ensures storage_site_shape(*site, wiring),
{
    site.storage_input_rows_evidence(row, wiring);
    if let Some(address) = site.address_bits {
        assert(0 <= address <= row.len());
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn root_storage_from_plan(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
        plan: &ClockedStorageLayout,
    ) -> bool {
        &&& self.storage_on_checked(checked, limits.width, network.inputs.total_bits_model(), limits.wiring_bits, Ok(*plan))
        &&& network._direct_devices == plan.instances@.len()
        &&& network._direct_devices <= network.storage@.len()
        &&& network._direct_devices <= network.storage_sites@.len()
        &&& network.storage_sites@.take(network._direct_devices as int) == plan.instances@
        &&& forall|i: int| 0 <= i < network._direct_devices ==>
            #[trigger] storage_site_shape(network.storage_sites@[i], network.storage@[i])
    }

    /// 直接呼び出しの状態素子は、階層展開後も VM の格納列の先頭に並ぶ。
    pub(super) closed spec fn root_storage_matches(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
    ) -> bool {
        exists|plan: ClockedStorageLayout| #[trigger] self.root_storage_from_plan(checked, limits, network, &plan)
    }

    pub(super) proof fn finish_root_storage(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork,
        plan: &ClockedStorageLayout,
    )
        requires
            self.storage_on_checked(checked, limits.width, network.inputs.total_bits_model(), limits.wiring_bits, Ok(*plan)),
            network._direct_devices == plan.instances@.len(),
            network._direct_devices <= network.storage@.len(),
            network._direct_devices <= network.storage_sites@.len(),
            network.storage_sites@.take(network._direct_devices as int) == plan.instances@,
            forall|i: int| 0 <= i < network._direct_devices ==>
                #[trigger] storage_site_shape(network.storage_sites@[i], network.storage@[i]),
        ensures self.root_storage_matches(checked, limits, network),
    {
        assert(self.root_storage_from_plan(checked, limits, network, plan));
    }

    /// 型検査済みの呼び出しから、VM に渡す状態素子の添字と配線を得る。
    proof fn root_storage_for_call(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork, call: usize,
    ) -> (index: int)
        requires
            self.root_storage_matches(checked, limits, network),
            call < checked.calls@.len(),
            checked.calls@[call as int].inputs.ports.signature.target is StateElement,
        ensures
            0 <= index < network._direct_devices,
            index < network.storage@.len() && index < network.storage_sites@.len(),
            network.storage_sites@[index].call_index == call,
            network.storage_sites@[index].at == checked.calls@[call as int].at,
            self.placement_matches(checked, limits.width, network.storage_sites@[index]),
            storage_site_shape(network.storage_sites@[index], network.storage@[index]),
    {
        let plan = choose|plan: ClockedStorageLayout| #[trigger] self.root_storage_from_plan(checked, limits, network, &plan);
        self.storage_layout_call(checked, limits.width, network.inputs.total_bits_model(), limits.wiring_bits, &plan, call);
        let index = plan.by_call@[call as int]->Some_0 as int;
        assert(0 <= index < plan.instances@.len() == network._direct_devices);
        assert(network.storage_sites@.take(network._direct_devices as int)[index] == plan.instances@[index]);
        assert(network.storage_sites@[index] == plan.instances@[index]);
        index
    }

    /// VM に渡した RAM 配線のアドレス幅とデータ幅は、ソースの宣言に従う。
    pub(super) proof fn root_ram_for_call(
        &self, checked: &ModuleCalls, limits: ClockedModuleVmLimits, network: &ClockedModuleNetwork, call: usize,
        address: u64, data: ResolvedPortType,
    ) -> (index: int)
        requires
            self.root_storage_matches(checked, limits, network),
            call < checked.calls@.len(),
            checked.calls@[call as int].inputs.ports.signature.target matches
                ModuleCallTarget::StateElement { storage: StorageSignature::Memory { address: expected, data: word, .. }, .. }
                && address == expected && data == word,
        ensures
            0 <= index < network._direct_devices,
            index < network.storage@.len() && index < network.storage_sites@.len(),
            network.storage_sites@[index].at == checked.calls@[call as int].at,
            (network.storage@[index].address matches Some(pins) && pins@.len() == address),
            match data {
                ResolvedPortType::Bits(bits) => network.storage@[index].data@.len() == bits,
                ResolvedPortType::Struct { .. } => exists|layouts: StructureLayouts|
                    #[trigger] self.structure_types_match(limits.width, Ok(layouts))
                    && self.layout_port_width_matches(&layouts, data, network.storage@[index].data@.len() as int),
            },
    {
        let index = self.root_storage_for_call(checked, limits, network, call);
        self.placed_ram_width(checked, limits.width, network.storage_sites@[index], address, data);
        index
    }
}

} // verus!
