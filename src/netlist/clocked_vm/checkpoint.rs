//! 同じ回路の状態を保存し、配線と幅を検査して復元する。

use super::{ClockedVm, snapshot};
#[cfg(verus_only)]
use super::{ClockedStorage, laid_out, update_layout};
use crate::netlist::{ClockedStorageInputs, NorNetlist, TickInputError, Wire};
use alloc::vec::Vec;
use vstd::prelude::*;
use vstd::slice::slice_to_vec;

verus! {

/// 状態素子1個の配線と確定済みの状態。
pub struct ClockedStorageCheckpoint {
    /// 状態素子のアドレス、データ、許可が読む配線。
    pub wiring: ClockedStorageInputs,
    /// ラッチの保持値、または RAM の登録読み出し出力。
    pub output: Vec<bool>,
    /// RAM の記憶内容。語はアドレス順、各語は最下位ビットから並ぶ。
    /// ラッチでは存在しない。
    pub memory: Option<Vec<bool>>,
}

/// 同じ配線の VM に復元できる、tick 確定後の回路状態。
///
/// 時刻と最後の外部入力は呼び出し側で保存する。
pub struct ClockedVmCheckpoint {
    /// 外部入力のビット数。
    pub external: usize,
    /// NOR の入力配線と公開出力の配線。添字順も比較対象になる。
    pub netlist: NorNetlist,
    /// ゲート番号順の NOR 出力。
    pub gates: Vec<bool>,
    /// 展開時のインスタンス順に並べた状態素子。
    pub storage: Vec<ClockedStorageCheckpoint>,
}

/// チェックポイントが復元先の VM と合わない理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedCheckpointError {
    /// 配線または状態素子の並びが異なる。
    Layout,
    /// ゲート出力、状態素子の出力、または RAM のビット数が異なる。
    StateShape,
}

impl ClockedStorageCheckpoint {
    /// RAM の保存ビット列。ラッチの値は保持出力に含まれる。
    pub open spec fn memory_model(&self) -> Option<Seq<bool>> {
        match &self.memory { Some(bits) => Some(bits@), None => None }
    }

    /// 保存したビット列の幅と種別が、状態素子と合うことを表す。
    pub open spec fn shape_matches(&self, device: &ClockedStorage) -> bool {
        self.output@.len() == device.output_model().len()
            && match (self.memory_model(), device.memory_model()) {
                (Some(first), Some(second)) => first.len() == second.len(),
                (None, None) => true,
                _ => false,
            }
    }

    /// 保存した保持出力と記憶内容が、状態素子と等しいことを表す。
    pub open spec fn values_match(&self, device: &ClockedStorage) -> bool {
        self.output@ == device.output_model() && self.memory_model() == device.memory_model()
    }
}

fn wire_equal(first: Wire, second: Wire) -> (equal: bool)
    ensures equal == (first == second)
{
    match (first, second) {
        (Wire::Input(a), Wire::Input(b)) | (Wire::Gate(a), Wire::Gate(b)) => a == b,
        (Wire::Constant(a), Wire::Constant(b)) => a == b,
        _ => false,
    }
}

fn wires_equal(first: &[Wire], second: &[Wire]) -> (equal: bool)
    ensures equal == (first@ == second@)
{
    if first.len() != second.len() { return false; }
    let mut i = 0;
    while i < first.len()
        invariant
            i <= first@.len() == second@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] first@[j] == second@[j],
        decreases first@.len() - i,
    {
        if !wire_equal(first[i], second[i]) { return false; }
        i += 1;
    }
    assert(first@ =~= second@);
    true
}

/// 状態素子の入力配線が同じ順で一致することを表す。
pub open spec fn same_ordered_storage_wiring(first: &ClockedStorageInputs, second: &ClockedStorageInputs) -> bool {
    &&& first.data@ == second.data@
    &&& first.enable == second.enable
    &&& match (&first.address, &second.address) {
        (Some(a), Some(b)) => a@ == b@,
        (None, None) => true,
        _ => false,
    }
}

/// NOR と公開出力の配線が同じ順で一致することを表す。
pub open spec fn same_ordered_netlist(first: &NorNetlist, second: &NorNetlist) -> bool {
    first.input_count == second.input_count
        && first.gates@ == second.gates@
        && first.outputs@ == second.outputs@
}

fn wiring_equal(first: &ClockedStorageInputs, second: &ClockedStorageInputs) -> (equal: bool)
    ensures equal == same_ordered_storage_wiring(first, second)
{
    let address_equal = match (&first.address, &second.address) {
        (Some(first), Some(second)) => wires_equal(first.as_slice(), second.as_slice()),
        (None, None) => true,
        _ => false,
    };
    let data_equal = wires_equal(first.data.as_slice(), second.data.as_slice());
    address_equal && data_equal && wire_equal(first.enable, second.enable)
}

fn netlists_equal(first: &NorNetlist, second: &NorNetlist) -> (equal: bool)
    ensures equal == same_ordered_netlist(first, second)
{
    if first.input_count != second.input_count || first.gates.len() != second.gates.len() {
        return false;
    }
    if !wires_equal(first.outputs.as_slice(), second.outputs.as_slice()) { return false; }
    let mut i = 0;
    while i < first.gates.len()
        invariant
            i <= first.gates@.len() == second.gates@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] first.gates@[j] == second.gates@[j],
        decreases first.gates@.len() - i,
    {
        let a = first.gates[i];
        let b = second.gates[i];
        if !wire_equal(a.left, b.left) || !wire_equal(a.right, b.right) { return false; }
        i += 1;
    }
    assert(first.gates@ =~= second.gates@);
    true
}

impl ClockedVmCheckpoint {
    /// 入出力、ゲート、状態素子が復元先と同じ配線を同じ順に持つことを表す。
    pub open spec fn layout_matches(&self, vm: &ClockedVm) -> bool {
        &&& self.external == vm.external_count()
        &&& same_ordered_netlist(&self.netlist, &vm.netlist_model())
        &&& self.storage@.len() == vm.storage_model().len()
        &&& forall|i: int| 0 <= i < self.storage@.len() ==>
            same_ordered_storage_wiring(&(#[trigger] self.storage@[i]).wiring, &vm.storage_model()[i].wiring_model())
    }

    /// 各状態ビット列の形が復元先と一致することを表す。
    pub open spec fn state_shape_matches(&self, vm: &ClockedVm) -> bool {
        &&& self.gates@.len() == vm.gate_values_model().len()
        &&& self.storage@.len() == vm.storage_model().len()
        &&& forall|i: int| 0 <= i < self.storage@.len() ==>
            (#[trigger] self.storage@[i]).shape_matches(&vm.storage_model()[i])
    }

    /// 確定済みの全状態が VM と同じであることを表す。
    pub open spec fn state_matches(&self, vm: &ClockedVm) -> bool {
        &&& self.gates@ == vm.gate_values_model()
        &&& self.storage@.len() == vm.storage_model().len()
        &&& forall|i: int| 0 <= i < self.storage@.len() ==>
            (#[trigger] self.storage@[i]).values_match(&vm.storage_model()[i])
    }
}

impl ClockedVm {
    /// ゲート、ラッチ、RAM の確定済み状態と配線を複製する。
    pub fn checkpoint(&self) -> (saved: ClockedVmCheckpoint)
        ensures saved.layout_matches(self), saved.state_matches(self),
    {
        let netlist = self.netlist();
        let mut storage: Vec<ClockedStorageCheckpoint> = Vec::new();
        let mut i = 0;
        while i < self.storage.len()
            invariant
                i <= self.storage@.len(),
                storage@.len() == i,
                forall|j: int| 0 <= j < i ==> {
                    let saved = #[trigger] storage@[j];
                    &&& same_ordered_storage_wiring(&saved.wiring, &self.storage@[j].wiring_model())
                    &&& saved.values_match(&self.storage@[j])
                },
            decreases self.storage@.len() - i,
        {
            let device = &self.storage[i];
            let wiring = device.wiring();
            let address = match &wiring.address {
                Some(bits) => Some(slice_to_vec(bits.as_slice())),
                None => None,
            };
            let memory = match device.ram_memory() {
                Some(bits) => Some(slice_to_vec(bits)),
                None => None,
            };
            let saved = ClockedStorageCheckpoint {
                wiring: ClockedStorageInputs {
                    address,
                    data: slice_to_vec(wiring.data.as_slice()),
                    enable: wiring.enable,
                },
                output: slice_to_vec(device.output()),
                memory,
            };
            assert(same_ordered_storage_wiring(&saved.wiring, wiring));
            assert(saved.values_match(device));
            storage.push(saved);
            i += 1;
        }
        let saved = ClockedVmCheckpoint {
            external: self.external,
            netlist: NorNetlist {
                input_count: netlist.input_count,
                gates: slice_to_vec(netlist.gates.as_slice()),
                outputs: slice_to_vec(netlist.outputs.as_slice()),
            },
            gates: slice_to_vec(self.gates.as_slice()),
            storage,
        };
        assert(same_ordered_netlist(&saved.netlist, netlist));
        saved
    }

    // 配線と状態の幅をすべて調べ、書き込み開始後に失敗しないようにする。
    fn check_checkpoint(&self, saved: &ClockedVmCheckpoint) -> (result: Result<(), ClockedCheckpointError>)
        ensures
            result == if !saved.layout_matches(self) {
                Err(ClockedCheckpointError::Layout)
            } else if !saved.state_shape_matches(self) {
                Err(ClockedCheckpointError::StateShape)
            } else {
                Ok(())
            },
    {
        if self.external != saved.external || self.storage.len() != saved.storage.len()
            || !netlists_equal(self.netlist(), &saved.netlist) {
            return Err(ClockedCheckpointError::Layout);
        }
        let mut i = 0;
        while i < self.storage.len()
            invariant
                i <= self.storage@.len() == saved.storage@.len(),
                forall|j: int| 0 <= j < i ==>
                    same_ordered_storage_wiring(&(#[trigger] saved.storage@[j]).wiring, &self.storage@[j].wiring_model()),
            decreases self.storage@.len() - i,
        {
            if !wiring_equal(self.storage[i].wiring(), &saved.storage[i].wiring) {
                return Err(ClockedCheckpointError::Layout);
            }
            i += 1;
        }
        assert(saved.layout_matches(self));
        if self.gates.len() != saved.gates.len() { return Err(ClockedCheckpointError::StateShape); }
        let mut i = 0;
        while i < self.storage.len()
            invariant
                i <= self.storage@.len() == saved.storage@.len(),
                saved.layout_matches(self),
                self.gates@.len() == saved.gates@.len(),
                forall|j: int| 0 <= j < i ==>
                    (#[trigger] saved.storage@[j]).shape_matches(&self.storage@[j]),
            decreases self.storage@.len() - i,
        {
            let device = &self.storage[i];
            let bits = &saved.storage[i];
            let memory_matches = match (device.ram_memory(), &bits.memory) {
                (Some(a), Some(b)) => a.len() == b.len(),
                (None, None) => true,
                _ => false,
            };
            if device.output().len() != bits.output.len() || !memory_matches {
                assert(!bits.shape_matches(device));
                return Err(ClockedCheckpointError::StateShape);
            }
            assert(bits.shape_matches(device));
            i += 1;
        }
        Ok(())
    }

    /// 同じ配線と幅を持つ VM に、確定済み状態を復元する。
    ///
    /// # Errors
    ///
    /// 配線やインスタンス順が異なる場合、または状態ビット列の幅が合わない場合は
    /// VM を変更せずエラーを返す。
    pub fn restore_checkpoint(&mut self, saved: &ClockedVmCheckpoint) -> (result: Result<(), ClockedCheckpointError>)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            final(self).same_layout(old(self)),
            result == if !saved.layout_matches(old(self)) {
                Err(ClockedCheckpointError::Layout)
            } else if !saved.state_shape_matches(old(self)) {
                Err(ClockedCheckpointError::StateShape)
            } else {
                Ok(())
            },
            result.is_ok() ==> saved.layout_matches(final(self)) && saved.state_matches(final(self)),
            result.is_err() ==> *final(self) == *old(self),
    {
        self.check_checkpoint(saved)?;
        let ghost netlist = self.netlist_model();
        let mut i = 0;
        while i < self.storage.len()
            invariant
                i <= self.storage@.len() == old(self).storage@.len() == saved.storage@.len(),
                self.circuit == old(self).circuit,
                self.starts@ == old(self).starts@,
                self.external == old(self).external,
                self.gates@ == old(self).gates@,
                saved.layout_matches(self),
                saved.state_shape_matches(old(self)),
                laid_out(self.storage@, self.starts@, self.external, netlist.input_count, netlist.gates@.len()),
                forall|j: int| 0 <= j < self.storage@.len() ==>
                    (#[trigger] self.storage@[j]).wiring_model() == old(self).storage@[j].wiring_model(),
                forall|j: int| 0 <= j < i ==>
                    (#[trigger] saved.storage@[j]).values_match(&self.storage@[j]),
                forall|j: int| i <= j < self.storage@.len() ==> #[trigger] self.storage@[j] == old(self).storage@[j],
            decreases self.storage@.len() - i,
        {
            let bits = &saved.storage[i];
            let memory = match &bits.memory {
                Some(memory) => Some(memory.as_slice()),
                None => None,
            };
            let ghost prior = self.storage@;
            let ghost updated: ClockedStorage;
            assert(bits.shape_matches(&prior[i as int]));
            {
                let device = &mut self.storage[i];
                device.restore_state(bits.output.as_slice(), memory);
                proof { updated = *device; }
            }
            proof { update_layout(prior, self.starts@, self.external, netlist.input_count, netlist.gates@.len(), i as int, updated); }
            i += 1;
        }
        self.gates.as_mut_slice().copy_from_slice(saved.gates.as_slice());
        Ok(())
    }

    /// 現在の確定済み状態と渡した入力から、時刻を進めず公開出力を読み直す。
    ///
    /// # Errors
    ///
    /// 入力フレームの幅が異なる場合は入力数のエラーを返す。
    pub fn observe_current(&self, input: &[bool]) -> (result: Result<Vec<bool>, TickInputError>)
        requires self.valid(),
        ensures
            result.is_ok() <==> input@.len() == self.external_count(),
            match result {
                Ok(output) => self.current_observation_matches(input@, output@),
                Err(error) => error == TickInputError::InputCount,
            },
    {
        if input.len() != self.external { return Err(TickInputError::InputCount); }
        let netlist = self.circuit.checked_netlist();
        let bits = snapshot(input, self.storage.as_slice(), self.starts.as_slice(), netlist.input_count,
            Ghost(self.gates@.len()));
        proof { super::clocked_wiring_endpoints(netlist); }
        let output = super::observe(netlist.outputs.as_slice(), bits.as_slice(), self.gates.as_slice());
        assert(self.augmented_input_matches(input@, bits@));
        Ok(output)
    }
}

} // verus!
