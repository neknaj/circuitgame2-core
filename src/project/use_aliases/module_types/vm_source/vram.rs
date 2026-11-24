//! 実行設定の読み出し信号名を、ルート本体の RAM 呼び出しに対応付ける。

use super::{ModuleBodyPosition, ModuleCalls, ModuleCallsError, UseAliases};
use crate::project::{DefinitionPosition, LocatedName, ModuleCallTarget, ResolvedPortType, StorageSignature};
use crate::project::use_aliases::function_drivers::find_driver;
#[cfg(verus_only)]
use crate::syntax::circuit::definition_target_range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 実行設定の `read-output` が指定する RAM の位置と型。
#[derive(Debug)]
pub struct VramTarget<'p, 'a> {
    /// ルート本体にある直接呼び出しの位置。
    pub call: DefinitionPosition,
    /// RAM のアドレス幅。幅が `n` ビットなら語数は `2^n`。
    pub address_bits: u64,
    /// RAM の1語の型。
    pub word_type: ResolvedPortType<'p, 'a>,
}

/// 実行設定の `read-output` を解決できなかった理由。
#[derive(Debug)]
pub enum VramOutputError<'p, 'a> {
    /// モジュールの型または呼び出しが不正だった。
    Module(ModuleCallsError<'p, 'a>),
    /// 指定名を定義する `def` が見つからなかった。
    MissingDefinition,
    /// 定義はあるが、ルート本体の直接の RAM 呼び出しに対応しない。
    NotDirectMemory(LocatedName<'p, 'a>),
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn vram_memory_call(&self, checked: &ModuleCalls, slot: int, call: int) -> bool {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        &&& 0 <= slot < drivers.definitions@.len()
        &&& self.source_vm_root_slot(checked, slot, call)
        &&& drivers.definitions@[slot].result_index == 0
        &&& checked.calls@[call].inputs.ports.signature.target matches
            ModuleCallTarget::StateElement { storage: StorageSignature::Memory { .. }, .. }
    }

    spec fn vram_definition_matches(
        &self, checked: &ModuleCalls, name: Seq<u8>, slot: int,
    ) -> bool {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        &&& 0 <= slot < drivers.definitions@.len()
        &&& drivers.definitions@[slot].name.word.spec_bytes() == name
        &&& forall|i: int| 0 <= i < slot ==> (#[trigger] drivers.definitions@[i]).name.word.spec_bytes() != name
    }

    pub(super) closed spec fn checked_vram_target(
        &self, owner: ModuleBodyPosition, checked: &ModuleCalls, name: Seq<u8>, target: VramTarget,
    ) -> bool {
        exists|slot: int, call: int| {
            let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
            &&& #[trigger] self.vram_definition_matches(checked, name, slot)
            &&& drivers.origins@[slot] == owner
            &&& #[trigger] self.vram_memory_call(checked, slot, call)
            &&& target.call == checked.calls@[call].at
            &&& self.vram_single_output(target.call)
            &&& checked.calls@[call].inputs.ports.signature.target matches
                ModuleCallTarget::StateElement { storage: StorageSignature::Memory { address, data, .. }, .. }
                && target.address_bits == address && target.word_type == data
            &&& forall|i: int| 0 <= i < call ==> !#[trigger] self.vram_memory_call(checked, slot, i)
        }
    }

    /// 解決した読み出し信号から、型検査済みの RAM 呼び出しの行を得る。
    pub(super) proof fn checked_vram_call(
        &self, owner: ModuleBodyPosition, checked: &ModuleCalls, name: Seq<u8>, target: &VramTarget,
    ) -> (call: usize)
        requires self.checked_vram_target(owner, checked, name, *target),
            checked.calls@.len() <= usize::MAX,
        ensures
            call < checked.calls@.len(),
            checked.calls@[call as int].at == target.call,
            checked.calls@[call as int].inputs.ports.signature.target matches
                ModuleCallTarget::StateElement { storage: StorageSignature::Memory { address, data, .. }, .. }
                && address == target.address_bits && data == target.word_type,
    {
        let (_slot, call) = choose|slot: int, call: int| {
            &&& #[trigger] self.vram_definition_matches(checked, name, slot)
            &&& #[trigger] self.vram_memory_call(checked, slot, call)
            &&& target.call == checked.calls@[call].at
            &&& checked.calls@[call].inputs.ports.signature.target matches
                ModuleCallTarget::StateElement { storage: StorageSignature::Memory { address, data, .. }, .. }
                && target.address_bits == address && target.word_type == data
        };
        call as usize
    }

    spec fn vram_single_output(&self, at: DefinitionPosition) -> bool {
        let parsed = self.targets.project_model().circuits_model()[at.file as int];
        let row = parsed.definitions@[parsed.entry_ranges@[at.entry as int].definitions.start + at.definition];
        let (first, end) = definition_target_range(parsed.syntax.forms@, row);
        end == first + 1
    }

    proof fn vram_memory_has_one_output(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls, slot: int, call: int,
    )
        requires self.module_calls_result(owner, limit, Ok(Some(*checked))), self.vram_memory_call(checked, slot, call),
        ensures self.vram_single_output(checked.calls@[call].at),
    {
        self.module_calls_item_evidence(owner, limit, checked, call);
        let row = checked.calls@[call];
        self.module_call_ports_evidence(row.at, limit, row.inputs.ports);
    }

    pub(super) closed spec fn checked_vram_result(
        &self, owner: ModuleBodyPosition, checked: &ModuleCalls, name: Seq<u8>,
        result: Result<VramTarget, VramOutputError>,
    ) -> bool {
        let drivers = checked.module.expressions.typed.sources.roots.wiring.drivers;
        match result {
            Ok(target) => self.checked_vram_target(owner, checked, name, target),
            Err(VramOutputError::Module(_)) => false,
            Err(VramOutputError::MissingDefinition) => forall|i: int| 0 <= i < drivers.definitions@.len() ==>
                (#[trigger] drivers.definitions@[i]).name.word.spec_bytes() != name,
            Err(VramOutputError::NotDirectMemory(site)) => exists|slot: int| {
                &&& #[trigger] self.vram_definition_matches(checked, name, slot)
                &&& crate::project::location_in_source(site)
                &&& site.span == drivers.definitions@[slot].name.span
                &&& *site.source == self.targets.project_model().sources_model()[drivers.origins@[slot].file as int]
                &&& (drivers.origins@[slot] != owner
                    || forall|call: int| 0 <= call < checked.calls@.len() ==>
                        !#[trigger] self.vram_memory_call(checked, slot, call))
            },
        }
    }

    pub(super) fn resolve_vram_checked(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls<'p, 'a>, name: &str,
    ) -> (result: Result<VramTarget<'p, 'a>, VramOutputError<'p, 'a>>)
        requires self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
        ensures self.checked_vram_result(owner, checked, name.spec_bytes(), result),
            result matches Ok(target) ==> self.checked_vram_target(owner, checked, name.spec_bytes(), target),
    {
        let expressions = &checked.module.expressions;
        let drivers = &expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, limit, checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, *expressions);
            self.module_alias_types_evidence(owner, limit, expressions.typed);
            self.module_type_sources_bounds(owner, limit, expressions.typed.sources);
        }
        let Some(slot) = find_driver(drivers.definitions.as_slice(), drivers.definitions.len(), name) else {
            return Err(VramOutputError::MissingDefinition);
        };
        assert(self.vram_definition_matches(checked, name.spec_bytes(), slot as int));
        proof { self.module_driver_sites(owner, limit, *drivers, slot as int); }
        let origin = drivers.origins[slot];
        if origin.file == owner.file && origin.entry == owner.entry && drivers.definitions[slot].result_index == 0 {
            let mut call = 0;
            while call < checked.calls.len()
                invariant
                    call <= checked.calls@.len(),
                    self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
                    self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
                    *drivers == checked.module.expressions.typed.sources.roots.wiring.drivers,
                    self.vram_definition_matches(checked, name.spec_bytes(), slot as int),
                    slot < drivers.definitions@.len(),
                    drivers.definitions@[slot as int].result_index == 0,
                    drivers.origins@[slot as int] == owner,
                    forall|i: int| 0 <= i < call ==> !#[trigger] self.vram_memory_call(checked, slot as int, i),
                decreases checked.calls@.len() - call,
            {
                let signature = &checked.calls[call].inputs.ports.signature;
                if let ModuleCallTarget::StateElement { storage: StorageSignature::Memory { address, data, .. }, .. } = &signature.target {
                    if self.root_call_slot(owner, limit, checked, drivers, slot, call) {
                        let target = VramTarget { call: checked.calls[call].at, address_bits: *address, word_type: *data };
                        assert(self.vram_memory_call(checked, slot as int, call as int));
                        proof { self.vram_memory_has_one_output(owner, limit, checked, slot as int, call as int); }
                        assert(self.checked_vram_target(owner, checked, name.spec_bytes(), target));
                        return Ok(target);
                    }
                }
                assert(!self.vram_memory_call(checked, slot as int, call as int));
                call += 1;
            }
        }
        let site = self.source_driver_location(owner, limit, drivers, slot);
        Err(VramOutputError::NotDirectMemory(site))
    }

    /// 構造化した実行設定の読み出し信号名を照合した結果を表す。
    pub closed spec fn vram_output_resolution(
        &self, owner: ModuleBodyPosition, limit: u64, name: Seq<u8>,
        result: Result<Option<VramTarget>, VramOutputError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_calls_result(owner, limit, Ok(None)),
            Err(VramOutputError::Module(error)) => self.module_calls_result(owner, limit, Err(error)),
            other => exists|checked: ModuleCalls| {
                &&& #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
                &&& self.checked_vram_result(owner, &checked, name, match other {
                    Ok(Some(target)) => Ok(target),
                    Err(error) => Err(error),
                    Ok(None) => arbitrary(),
                })
            },
        }
    }

    /// コンパイル時に得た RAM の対応を、公開の名前解決契約に結び付ける。
    pub(super) proof fn resolved_vram_output_evidence(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls, name: Seq<u8>, target: VramTarget,
    )
        requires self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.checked_vram_target(owner, checked, name, target),
        ensures self.vram_output_resolution(owner, limit, name, Ok(Some(target))),
    {
        assert(self.checked_vram_result(owner, checked, name, Ok(target)));
    }

    /// `read-output` をルート本体の RAM 呼び出しに解決する。
    ///
    /// 指定位置がモジュールを指さない場合は `Ok(None)` を返す。
    ///
    /// # Errors
    ///
    /// モジュールを検査できない場合、指定名の定義がない場合、または定義が
    /// ルート本体の直接の RAM 呼び出しに対応しない場合にエラーを返す。
    pub fn resolve_vram_output(&self, owner: ModuleBodyPosition, limit: u64, name: &str)
        -> (result: Result<Option<VramTarget<'p, 'a>>, VramOutputError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.vram_output_resolution(owner, limit, name.spec_bytes(), result),
    {
        let checked = match self.check_module_calls(owner, limit) {
            Ok(Some(checked)) => checked,
            Ok(None) => return Ok(None),
            Err(error) => return Err(VramOutputError::Module(error)),
        };
        match self.resolve_vram_checked(owner, limit, &checked, name) {
            Ok(target) => Ok(Some(target)),
            Err(error) => Err(error),
        }
    }
}

} // verus!
