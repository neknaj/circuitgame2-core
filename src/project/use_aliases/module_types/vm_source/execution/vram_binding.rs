//! 読み出し信号が指す RAM を、コンパイル済み VM の格納位置に対応付ける。

use super::{ClockedModuleCompilation, ClockedModuleVm, ClockedModuleVmError, ClockedModuleVmLimits, ModuleBodyPosition, UseAliases};
#[cfg(verus_only)]
use super::ClockedModuleNetwork;
use super::super::{VramOutputError, VramTarget};
use crate::netlist::{ClockedStorageInputs, PortBitLayout, TickInputError};
#[cfg(verus_only)]
use crate::netlist::{ClockedStorage, ClockedVm, clocked_storage_memory_width};
#[cfg(verus_only)]
use crate::netlist::{SourceDeviceId, SourceVmCircuit, SourceVmFrame, SourceVmLayout, clocked_vm_trace,
    source_vm_layout_port_evidence, source_vm_project_trace, source_vm_state_projection, source_vm_trace, source_vm_wiring_valid};
#[cfg(verus_only)]
use crate::project::{ResolvedPortType, StructureLayouts};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::encode_utf8_decode_utf8;

verus! {

/// 実行設定で公開する VRAM。
#[derive(Clone, Copy, Debug)]
pub struct VramDeclaration<'n> {
    /// 表示側が参照するときに使う公開名。
    pub name: &'n str,
    /// ルート本体で RAM の読み出し出力を受け取る信号名。
    pub read_output: &'n str,
}

/// 公開 VRAM を備えた VM を用意できなかった理由。
#[derive(Debug)]
pub enum VramSetupError<'p, 'a> {
    /// ソースのコンパイルまたは VM の初期化に失敗した。
    Circuit(ClockedModuleVmError<'p, 'a>),
    /// 設定順に検査して最初に解決できなかった読み出し信号。
    Output {
        /// 実行設定の VRAM 配列での添字。
        declaration: usize,
        /// 読み出し信号の診断。
        error: VramOutputError<'p, 'a>,
    },
    /// 公開する VRAM の一覧を確保できなかった。
    Allocation,
}

struct VramBinding<'n, 'p, 'a> {
    name: &'n str,
    target: VramTarget<'p, 'a>,
    index: usize,
}

/// 公開した RAM の型と、最後に確定した記憶部。
pub struct VramView<'b, 'p, 'a> {
    /// 設定から解決した RAM の呼び出し位置と型。
    pub target: &'b VramTarget<'p, 'a>,
    /// アドレス順のビット列。各語は最下位ビットから並ぶ。
    pub bits: &'b [bool],
}

/// 公開 VRAM の対応表と、そこから参照する VM。
pub struct ClockedVramVm<'n, 'p, 'a> {
    module: ClockedModuleVm,
    bindings: Vec<VramBinding<'n, 'p, 'a>>,
    _wiring: Ghost<Seq<ClockedStorageInputs>>,
}

impl<'n, 'p, 'a> ClockedVramVm<'n, 'p, 'a> {
    /// 公開先が現在の VM に存在し、格納位置ごとの配線が初期化時から保たれている。
    pub closed spec fn valid(&self) -> bool {
        &&& self.module.vm.layout_matches(self.module.vm.netlist_model(), self.module.vm.external_count(), self._wiring@)
        &&& forall|i: int| 0 <= i < self.bindings@.len() ==> {
            let item = #[trigger] self.bindings@[i];
            item.index < self._wiring@.len() && self._wiring@[item.index as int].address.is_some()
        }
    }

    /// 現在の VM 状態を表す。
    pub closed spec fn vm_model(&self) -> ClockedVm { self.module.vm }

    /// コンパイル時のポート配置と現在の VM 状態を表す。
    pub closed spec fn module_model(&self) -> ClockedModuleVm { self.module }

    /// 公開名と格納位置の対応が同じであることを表す。
    pub closed spec fn same_vram_configuration(&self, other: &Self) -> bool {
        self.bindings@ == other.bindings@ && self._wiring@ == other._wiring@
    }

    /// 入力フレームのポートごとのビット範囲。
    pub fn inputs(&self) -> &PortBitLayout { &self.module.inputs }

    /// 公開出力のポートごとのビット範囲。
    pub fn outputs(&self) -> &PortBitLayout { &self.module.outputs }

    /// ゲートと状態素子を初期値に戻し、リセット直後の公開出力を返す。
    pub fn reset(&mut self) -> (output: Vec<bool>)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).same_vram_configuration(old(self)),
            final(self).vm_model().reset_matches(output@),
            final(self).vm_model().same_layout(&old(self).vm_model()),
    {
        let ghost previous = self.module.vm;
        let output = self.module.vm.reset();
        proof { self.module.vm.preserve_layout_evidence(&previous, previous.netlist_model(), previous.external_count(), self._wiring@); }
        output
    }

    /// 1 tick 進めて公開出力を返す。入力幅が異なる場合は状態を保ったままエラーを返す。
    pub fn step(&mut self, input: &[bool]) -> (result: Result<Vec<bool>, TickInputError>)
        requires old(self).valid(),
        ensures
            final(self).valid(), final(self).same_vram_configuration(old(self)),
            final(self).vm_model().same_layout(&old(self).vm_model()),
            match result {
                Ok(output) => final(self).vm_model().tick_matches(&old(self).vm_model(), input@, output@),
                Err(_) => final(self).vm_model() == old(self).vm_model(),
            },
    {
        let ghost previous = self.module.vm;
        let output = self.module.vm.step(input);
        proof { self.module.vm.preserve_layout_evidence(&previous, previous.netlist_model(), previous.external_count(), self._wiring@); }
        output
    }

    /// 公開名に対応する、現在の RAM 記憶部を表す。
    pub closed spec fn vram_view_matches(&self, name: Seq<u8>, result: Option<VramView>) -> bool {
        match result {
            Some(view) => exists|i: int| {
                let binding = #[trigger] self.bindings@[i];
                &&& 0 <= i < self.bindings@.len() && binding.name.spec_bytes() == name
                &&& forall|j: int| 0 <= j < i ==> (#[trigger] self.bindings@[j]).name.spec_bytes() != name
                &&& *view.target == binding.target
                &&& self.module.vm.storage_model()[binding.index as int].memory_model() == Some(view.bits@)
            },
            None => forall|i: int| 0 <= i < self.bindings@.len() ==> (#[trigger] self.bindings@[i]).name.spec_bytes() != name,
        }
    }

    /// 最初に一致する公開名の VRAM を読み取る。名前が見つからない場合は `None` を返す。
    pub fn read_vram<'b>(&'b self, name: &str) -> (result: Option<VramView<'b, 'p, 'a>>)
        requires self.valid(),
        ensures self.vram_view_matches(name.spec_bytes(), result),
    {
        let mut i = 0;
        while i < self.bindings.len()
            invariant
                self.valid(), i <= self.bindings@.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.bindings@[j]).name.spec_bytes() != name.spec_bytes(),
            decreases self.bindings@.len() - i,
        {
            let binding = &self.bindings[i];
            proof { encode_utf8_decode_utf8(binding.name@); encode_utf8_decode_utf8(name@); }
            if binding.name == name {
                proof {
                    let wiring = self._wiring@[binding.index as int];
                    assert(self.module.vm.storage_model()[binding.index as int].wiring_model() == wiring);
                    self.module.vm.storage_shape_evidence(binding.index as int);
                    assert(clocked_storage_memory_width(&wiring).is_some());
                }
                let Some(bits) = self.module.vm.ram_memory(binding.index) else { unreachable!() };
                let view = VramView { target: &binding.target, bits };
                assert(self.vram_view_matches(name.spec_bytes(), Some(view)));
                return Some(view);
            }
            i += 1;
        }
        None
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn vram_declarations_placed(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, root: &ClockedModuleCompilation,
        declarations: Seq<VramDeclaration>, bindings: Seq<VramBinding>,
    ) -> bool {
        &&& bindings.len() <= declarations.len()
        &&& forall|i: int| 0 <= i < bindings.len() ==> {
            let binding = #[trigger] bindings[i];
            &&& binding.name == declarations[i].name
            &&& self.vram_storage_matches(owner, limits, root, declarations[i].read_output.spec_bytes(), binding.target, binding.index)
        }
    }

    /// VM の初期化結果と公開 VRAM の対応が、同じコンパイル結果に基づくことを表す。
    pub closed spec fn clocked_vram_configured(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits,
        declarations: Seq<VramDeclaration>, vm: &ClockedVramVm,
    ) -> bool {
        exists|root: ClockedModuleCompilation| {
            &&& #[trigger] self.compilation_keeps_root_storage(owner, limits, &root)
            &&& (self.direct_compilation_retains_storage(owner, limits, &root)
                || self.hierarchy_compilation_retains_storage(owner, limits, &root))
            &&& root.compiled == vm.module
            &&& vm.bindings@.len() == declarations.len()
            &&& self.vram_declarations_placed(owner, limits, &root, declarations, vm.bindings@)
        }
    }

    /// リセット直後と各 tick の公開出力および VRAM の全記憶が、ソースの参照実行と一致する。
    pub proof fn clocked_vram_source_trace(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, declarations: Seq<VramDeclaration>,
        initial: &ClockedVramVm, inputs: Seq<Seq<bool>>, states: Seq<ClockedVramVm>, outputs: Seq<Seq<bool>>,
    ) -> (reference: (SourceVmCircuit, SourceVmLayout, Seq<SourceVmFrame>))
        requires
            self.can_resolve(), self.clocked_vram_configured(owner, limits, declarations, initial),
            clocked_vm_trace(inputs, states.map_values(|state: ClockedVramVm| state.vm_model()), outputs),
            states[0].vm_model().same_layout(&initial.vm_model()),
            forall|i: int| 0 <= i < states.len() ==> (#[trigger] states[i]).same_vram_configuration(initial),
        ensures
            self.clocked_compiled_source_model(owner, limits, &initial.module_model(), &reference.0, &reference.1),
            source_vm_wiring_valid(&reference.0),
            source_vm_trace(&reference.0, inputs, reference.2),
            reference.2.map_values(|frame: SourceVmFrame| frame.outputs) == outputs,
            forall|i: int, name: Seq<u8>| 0 <= i < states.len()
                && #[trigger] states[i].vram_view_matches(name, None) ==>
                    forall|slot: int| 0 <= slot < declarations.len() ==>
                        (#[trigger] declarations[slot]).name.spec_bytes() != name,
            forall|i: int, name: Seq<u8>, view: VramView| 0 <= i < states.len()
                && #[trigger] states[i].vram_view_matches(name, Some(view)) ==> {
                    let id = SourceDeviceId { instance: Seq::empty(), call: view.target.call };
                    &&& reference.2[i].state.storage.contains_key(id)
                    &&& reference.2[i].state.storage[id].memory == Some(view.bits@)
                    &&& exists|slot: int| {
                        &&& 0 <= slot < declarations.len() && (#[trigger] declarations[slot]).name.spec_bytes() == name
                        &&& forall|earlier: int| 0 <= earlier < slot ==> (#[trigger] declarations[earlier]).name.spec_bytes() != name
                        &&& self.vram_output_resolution(owner, limits.width, declarations[slot].read_output.spec_bytes(),
                            Ok(Some(*view.target)))
                    }
                },
    {
        let root = choose|root: ClockedModuleCompilation| {
            &&& #[trigger] self.compilation_keeps_root_storage(owner, limits, &root)
            &&& (self.direct_compilation_retains_storage(owner, limits, &root)
                || self.hierarchy_compilation_retains_storage(owner, limits, &root))
            &&& root.compiled == initial.module
            &&& initial.bindings@.len() == declarations.len()
            &&& self.vram_declarations_placed(owner, limits, &root, declarations, initial.bindings@)
        };
        let vm = &root.compiled.vm;
        let (source, layout, wiring) = if self.direct_compilation_retains_storage(owner, limits, &root) {
            let model = self.direct_vram_source_layout(owner, limits, &root);
            assert(self.clocked_module_vm_wiring(owner, limits, &root.compiled));
            model
        } else {
            self.hierarchy_vram_source_layout(owner, limits, &root)
        };
        assert(self.clocked_compiled_source_model(owner, limits, &initial.module, &source, &layout));
        let vms = states.map_values(|state: ClockedVramVm| state.vm_model());
        vms[0].reset_snapshot(outputs[0]);
        vms[0].preserve_layout_evidence(vm, vm.netlist_model(), source.input_count, wiring);
        let frames = source_vm_project_trace(&source, inputs, vms, outputs, wiring, &layout);
        source_vm_layout_port_evidence(&source, &vm.netlist_model(), wiring, &layout);
        assert forall|i: int, name: Seq<u8>| 0 <= i < states.len()
            && #[trigger] states[i].vram_view_matches(name, None) implies
                forall|slot: int| 0 <= slot < declarations.len() ==> (#[trigger] declarations[slot]).name.spec_bytes() != name
        by {
            let state = &states[i];
            assert(state.bindings@ == initial.bindings@);
            assert forall|slot: int| 0 <= slot < declarations.len() implies
                (#[trigger] declarations[slot]).name.spec_bytes() != name by {
                assert(state.bindings@[slot] == initial.bindings@[slot]);
                assert(state.bindings@[slot].name == declarations[slot].name);
            };
        };
        assert forall|i: int, name: Seq<u8>, view: VramView| 0 <= i < states.len()
            && #[trigger] states[i].vram_view_matches(name, Some(view)) implies {
                let id = SourceDeviceId { instance: Seq::empty(), call: view.target.call };
                &&& frames[i].state.storage.contains_key(id)
                &&& frames[i].state.storage[id].memory == Some(view.bits@)
                &&& exists|slot: int| {
                    &&& 0 <= slot < declarations.len() && (#[trigger] declarations[slot]).name.spec_bytes() == name
                    &&& forall|earlier: int| 0 <= earlier < slot ==> (#[trigger] declarations[earlier]).name.spec_bytes() != name
                    &&& self.vram_output_resolution(owner, limits.width, declarations[slot].read_output.spec_bytes(),
                        Ok(Some(*view.target)))
                }
            } by {
            let state = &states[i];
            let slot = choose|slot: int| {
                let binding = #[trigger] state.bindings@[slot];
                &&& 0 <= slot < state.bindings@.len() && binding.name.spec_bytes() == name
                &&& forall|earlier: int| 0 <= earlier < slot ==> (#[trigger] state.bindings@[earlier]).name.spec_bytes() != name
                &&& *view.target == binding.target
                &&& state.module.vm.storage_model()[binding.index as int].memory_model() == Some(view.bits@)
            };
            assert(state.bindings@ == initial.bindings@);
            let binding = initial.bindings@[slot];
            let index = binding.index as int;
            let id = SourceDeviceId { instance: Seq::empty(), call: view.target.call };
            assert(self.vram_storage_matches(owner, limits, &root, declarations[slot].read_output.spec_bytes(),
                binding.target, binding.index));
            self.resolved_vram_output_evidence(owner, limits.width, &root._checked,
                declarations[slot].read_output.spec_bytes(), binding.target);
            assert forall|earlier: int| 0 <= earlier < slot implies
                (#[trigger] declarations[earlier]).name.spec_bytes() != name by {
                assert(state.bindings@[earlier] == initial.bindings@[earlier]);
                assert(state.bindings@[earlier].name == declarations[earlier].name);
            };
            assert(layout.devices[index] == id);
            assert(layout.device_index[id] == index);
            assert(frames[i].state == source_vm_state_projection(&vms[i], &layout));
        };
        (source, layout, frames)
    }

    /// 設定順で最初に解決できなかった読み出し信号と診断を表す。
    pub closed spec fn clocked_vram_rejected_at(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits,
        declarations: Seq<VramDeclaration>, declaration: usize, error: VramOutputError,
    ) -> bool {
        &&& declaration < declarations.len()
        &&& exists|root: ClockedModuleCompilation, earlier: Seq<VramBinding>| {
            &&& #[trigger] self.compilation_keeps_root_storage(owner, limits, &root)
            &&& earlier.len() == declaration
            &&& #[trigger] self.vram_declarations_placed(owner, limits, &root, declarations, earlier)
            &&& self.checked_vram_result(owner, &root._checked, declarations[declaration as int].read_output.spec_bytes(), Err(error))
        }
    }

    /// モジュールをコンパイルし、設定の公開名で RAM を読み取れる VM を返す。
    ///
    /// 指定位置がモジュールを指さない場合は `Ok(None)` を返す。同じ公開名が
    /// 複数ある場合、読み取りには設定順で最初のものを使う。
    ///
    /// # Errors
    ///
    /// 回路のコンパイルと VM の初期化を先に行う。成功後に VRAM の一覧を確保し、
    /// 設定順に読み出し信号を検査して最初に失敗した設定の位置を返す。
    pub fn lower_clocked_vram<'n>(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, declarations: &[VramDeclaration<'n>],
    ) -> (result: Result<Option<ClockedVramVm<'n, 'p, 'a>>, VramSetupError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            result matches Ok(Some(vm)) ==>
                self.clocked_vram_configured(owner, limits, declarations@, &vm) && vm.valid() && vm.vm_model().initial(),
            result matches Err(VramSetupError::Output { declaration, error }) ==>
                self.clocked_vram_rejected_at(owner, limits, declarations@, declaration, error),
    {
        let root = match self.compile_clocked_root(owner, limits) {
            Ok(Some(root)) => root,
            Ok(None) => return Ok(None),
            Err(error) => return Err(VramSetupError::Circuit(error)),
        };
        let mut bindings = Vec::new();
        if bindings.try_reserve_exact(declarations.len()).is_err() {
            return Err(VramSetupError::Allocation);
        }
        let mut i = 0;
        while i < declarations.len()
            invariant
                self.can_resolve(), self.compilation_keeps_root_storage(owner, limits, &root),
                self.direct_compilation_retains_storage(owner, limits, &root)
                    || self.hierarchy_compilation_retains_storage(owner, limits, &root),
                root.compiled.vm.initial(),
                i == bindings@.len() <= declarations@.len(),
                self.vram_declarations_placed(owner, limits, &root, declarations@, bindings@),
            decreases declarations@.len() - i,
        {
            let declaration = declarations[i];
            let (target, index) = match self.bind_vram_output(owner, limits, &root, declaration.read_output) {
                Ok(binding) => binding,
                Err(error) => {
                    assert(self.clocked_vram_rejected_at(owner, limits, declarations@, i, error));
                    return Err(VramSetupError::Output { declaration: i, error });
                },
            };
            let ghost before = bindings@;
            bindings.push(VramBinding { name: declaration.name, target, index });
            assert forall|j: int| 0 <= j <= i implies {
                let binding = #[trigger] bindings@[j];
                &&& binding.name == declarations@[j].name
                &&& self.vram_storage_matches(owner, limits, &root, declarations@[j].read_output.spec_bytes(),
                    binding.target, binding.index)
            } by {
                if j < i { assert(bindings@[j] == before[j]); }
            };
            i += 1;
        }
        let ghost compiled = root;
        let ghost wiring = root.compiled.vm.storage_model().map_values(|device: ClockedStorage| device.wiring_model());
        assert forall|j: int| 0 <= j < bindings@.len() implies {
            let binding = #[trigger] bindings@[j];
            binding.index < wiring.len() && wiring[binding.index as int].address.is_some()
        } by {
            assert(self.vram_storage_matches(owner, limits, &root, declarations@[j].read_output.spec_bytes(),
                bindings@[j].target, bindings@[j].index));
        };
        let vm = ClockedVramVm { module: root.compiled, bindings, _wiring: Ghost(wiring) };
        assert(vm.valid());
        assert(self.compilation_keeps_root_storage(owner, limits, &compiled));
        assert(self.clocked_vram_configured(owner, limits, declarations@, &vm));
        Ok(Some(vm))
    }

    spec fn vram_storage_matches(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, root: &ClockedModuleCompilation,
        name: Seq<u8>, target: VramTarget, index: usize,
    ) -> bool {
        &&& self.checked_vram_target(owner, &root._checked, name, target)
        &&& index < root._direct_devices <= root._storage_sites@.len()
        &&& root._storage_sites@[index as int].at == target.call
        &&& forall|i: int| 0 <= i < root._direct_devices && (#[trigger] root._storage_sites@[i]).at == target.call ==> i == index
        &&& index < root.compiled.vm.storage_model().len()
        &&& {
            let wiring = root.compiled.vm.storage_model()[index as int].wiring_model();
            &&& wiring.address matches Some(pins) && pins@.len() == target.address_bits
            &&& match target.word_type {
                ResolvedPortType::Bits(bits) => wiring.data@.len() == bits,
                ResolvedPortType::Struct { .. } => exists|layouts: StructureLayouts|
                    #[trigger] self.structure_types_match(limits.width, Ok(layouts))
                    && self.layout_port_width_matches(&layouts, target.word_type, wiring.data@.len() as int),
            }
        }
    }

    /// ルートの格納区間から、読み出し信号に対応する RAM を探す。
    fn bind_vram_output(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, root: &ClockedModuleCompilation<'p, 'a>,
        name: &str,
    ) -> (result: Result<(VramTarget<'p, 'a>, usize), VramOutputError<'p, 'a>>)
        requires self.can_resolve(), self.compilation_keeps_root_storage(owner, limits, root),
        ensures match result {
            Ok((target, index)) => self.vram_storage_matches(owner, limits, root, name.spec_bytes(), target, index),
            Err(error) => self.checked_vram_result(owner, &root._checked, name.spec_bytes(), Err(error)),
        },
    {
        let target = self.resolve_vram_checked(owner, limits.width, &root._checked, name)?;
        let ghost expected: int;
        proof {
            let network = choose|network: ClockedModuleNetwork| {
                &&& #[trigger] self.root_storage_matches(&root._checked, limits, &network)
                &&& self.network_vm_on_reset(&network, limits.state_bits, &root.compiled)
                &&& root._storage_sites@ == network.storage_sites@
                &&& root._direct_devices == network._direct_devices
            };
            vstd::std_specs::vec::axiom_spec_len(&root._checked.calls);
            let call = self.checked_vram_call(owner, &root._checked, name.spec_bytes(), &target);
            expected = self.root_ram_for_call(owner, &root._checked, limits, &network, call, target.address_bits, target.word_type);
            assert(0 <= expected < root._direct_devices <= root._storage_sites@.len());
            assert(expected as usize == expected);
            assert(root._storage_sites@[expected].at == target.call);
            assert(root.compiled.vm.storage_model().len() == network.storage@.len());
            assert(root.compiled.vm.storage_model()[expected].wiring_model() == network.storage@[expected]);
            let wiring = root.compiled.vm.storage_model()[expected].wiring_model();
            assert(wiring.address matches Some(pins) && pins@.len() == target.address_bits);
            assert(match target.word_type {
                ResolvedPortType::Bits(bits) => wiring.data@.len() == bits,
                ResolvedPortType::Struct { .. } => exists|layouts: StructureLayouts|
                    #[trigger] self.structure_types_match(limits.width, Ok(layouts))
                    && self.layout_port_width_matches(&layouts, target.word_type, wiring.data@.len() as int),
            });
            assert forall|i: int| 0 <= i < root._direct_devices && (#[trigger] root._storage_sites@[i]).at == target.call
                implies i == expected by {
                assert(network.storage_sites@[i] == root._storage_sites@[i]);
            };
            assert(self.vram_storage_matches(owner, limits, root, name.spec_bytes(), target, expected as usize));
        }
        let mut index = 0;
        while index < root._direct_devices
            invariant
                index <= expected < root._direct_devices <= root._storage_sites@.len(),
                self.vram_storage_matches(owner, limits, root, name.spec_bytes(), target, expected as usize),
            decreases root._direct_devices - index,
        {
            let site = root._storage_sites[index].at;
            let call = target.call;
            if site.file == call.file && site.entry == call.entry && site.definition == call.definition
                && site.reference == call.reference
            {
                assert(site == call);
                assert(index == expected);
                return Ok((target, index));
            }
            assert(index != expected);
            index += 1;
        }
        unreachable!()
    }
}

} // verus!
