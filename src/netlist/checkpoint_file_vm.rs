//! 確定済みの VM 状態を、復元先の構成と照合できるファイルに変換する。

#[cfg(verus_only)]
mod layout_agreement;
#[cfg(verus_only)]
pub use layout_agreement::{canonical_vm_layout_agrees, canonical_vm_layout_transfers};

use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

use super::checkpoint_bits::{pack_checkpoint_bits, unpack_checkpoint_bits, CheckpointBitError};
#[cfg(verus_only)]
use super::checkpoint_bits::{checkpoint_bits_roundtrip, checkpoint_segment_valid, packed_checkpoint_bits};
use super::checkpoint_format::{
    checkpoint_state, read_checkpoint_header, write_checkpoint_file, write_word, CheckpointFileError,
    CheckpointHeader, CHECKPOINT_HEADER_BYTES,
};
use super::checkpoint_layout::{append_ordered_wire_layout, write_wire_layout};
#[cfg(verus_only)]
use super::checkpoint_format::{checkpoint_header_matches, checkpoint_headers_agree, word_at};
#[cfg(verus_only)]
use super::checkpoint_layout::{ordered_wire_layout, wire_layout_record};
#[cfg(verus_only)]
use super::clocked_vm::checkpoint::{same_ordered_netlist, same_ordered_storage_wiring};
#[cfg(verus_only)]
use super::ClockedStorage;
use super::{ClockedStorageCheckpoint, ClockedStorageInputs, ClockedVm, ClockedVmCheckpoint, NorGate, NorNetlist, Wire};

verus! {

/// 回路状態と最後に適用した入力を、照合済みの状態として返す。
pub struct DecodedCheckpoint {
    /// 保存した論理時刻と実行周期。
    pub header: CheckpointHeader,
    /// 最後に適用した外部入力。観測時に使う。
    pub input: Vec<bool>,
    /// ゲート、ラッチ、RAM の確定状態。
    pub vm: ClockedVmCheckpoint,
}

/// ファイルの保存・復号を完了できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VmCheckpointFileError {
    /// ファイルの形式または配線表の不一致。
    File(CheckpointFileError),
    /// 保存した周期が復元先の設定と異なる。
    PeriodMismatch,
    /// 端子配置または最後の入力幅が対象回路と異なる。
    PortLayout,
    /// 状態部のビット列が規定の形式に合わない。
    MalformedState,
    /// 領域を確保できない。
    Allocation,
}

type FileResult<T> = Result<T, VmCheckpointFileError>;

fn append<T: Copy>(target: &mut Vec<T>, source: &[T]) -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> final(target)@ == old(target)@ + source@,
        result.is_err() ==> final(target)@ == old(target)@ && result == Err(VmCheckpointFileError::Allocation),
{
    if source.len() > usize::MAX - target.len() || target.try_reserve(source.len()).is_err() {
        return Err(VmCheckpointFileError::Allocation);
    }
    let mut i = 0;
    while i < source.len()
        invariant
            i <= source@.len(),
            target@ == old(target)@ + source@.take(i as int),
            old(target)@.len() + source@.len() <= usize::MAX,
        decreases source.len() - i,
    {
        target.push(source[i]);
        assert(source@.take((i + 1) as int) =~= source@.take(i as int).push(source@[i as int]));
        i += 1;
    }
    assert(source@.take(i as int) =~= source@);
    Ok(())
}

fn copy<T: Copy>(source: &[T]) -> (result: FileResult<Vec<T>>)
    ensures
        result matches Ok(items) ==> items@ == source@,
        result.is_err() ==> result == Err(VmCheckpointFileError::Allocation),
{
    let mut result = Vec::new();
    append(&mut result, source)?;
    Ok(result)
}

fn append_word(bytes: &mut Vec<u8>, word: usize) -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> {
            let offset = old(bytes)@.len() as int;
            &&& final(bytes)@.len() == offset + 8
            &&& final(bytes)@.take(offset) == old(bytes)@
            &&& word_at(final(bytes)@.skip(offset), 0) == word as u64
        },
        result.is_err() ==> final(bytes)@ == old(bytes)@ && result == Err(VmCheckpointFileError::Allocation),
{
    hide(word_at);
    let encoded = write_word(word as u64);
    let ghost prefix = bytes@;
    append(bytes, &encoded)?;
    proof {
        assert(bytes@.take(prefix.len() as int) =~= prefix);
        assert(bytes@.skip(prefix.len() as int) =~= encoded@);
    }
    Ok(())
}

spec fn port_bound(ports: Seq<Range<usize>>, i: int) -> int {
    if i == 0 { 0 } else { ports[i - 1].end as int }
}

pub closed spec fn checkpoint_ports_valid(ports: Seq<Range<usize>>, total: int) -> bool {
    &&& port_bound(ports, ports.len() as int) == total
    &&& forall|i: int| 0 <= i < ports.len() ==> {
        let port = #[trigger] ports[i];
        &&& port.start == port_bound(ports, i)
        &&& port.start < port.end <= total
    }
}

spec fn ports_match(ports: Seq<Range<usize>>, total: int, bytes: Seq<u8>) -> bool {
    &&& port_bound(ports, ports.len() as int) == total
    &&& bytes.len() == 8 * (ports.len() + 1)
    &&& word_at(bytes.subrange(0, 8), 0) == ports.len() as u64
    &&& forall|i: int| 0 <= i < ports.len() ==> {
        let port = #[trigger] ports[i];
        &&& port.start == port_bound(ports, i)
        &&& port.start < port.end <= total
        &&& word_at(bytes.subrange(8 * (i + 1), 8 * (i + 2)), 0)
            == (port.end - port.start) as u64
    }
}

proof fn preserved_segment(before: Seq<u8>, after: Seq<u8>, start: int, end: int)
    requires
        before.len() <= after.len(),
        after.take(before.len() as int) == before,
        0 <= start <= end <= before.len(),
    ensures after.subrange(start, end) == before.subrange(start, end),
{
    assert forall|i: int| 0 <= i < end - start implies
        after.subrange(start, end)[i] == before.subrange(start, end)[i] by {
        assert(after.take(before.len() as int)[i + start] == after[i + start]);
    }
    assert(after.subrange(start, end) =~= before.subrange(start, end));
}

fn append_ports(bytes: &mut Vec<u8>, ports: &[Range<usize>], total: usize) -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> {
            let offset = old(bytes)@.len() as int;
            &&& final(bytes)@.take(offset) == old(bytes)@
            &&& final(bytes)@.len() == offset + 8 * (ports@.len() + 1)
            &&& ports_match(ports@, total as int, final(bytes)@.skip(offset))
        },
        checkpoint_ports_valid(ports@, total as int) ==>
            result.is_ok() || result == Err(VmCheckpointFileError::Allocation),
{
    hide(word_at);
    hide(port_bound);
    let ghost base = bytes@;
    let ghost offset = base.len() as int;
    append_word(bytes, ports.len())?;
    let mut bit = 0;
    let mut i = 0;
    proof {
        assert(port_bound(ports@, 0) == 0) by { reveal(port_bound); }
        assert(bytes@.subrange(offset, offset + 8) =~= bytes@.skip(offset));
    }
    while i < ports.len()
        invariant
            i <= ports@.len(),
            0 <= offset,
            bit == port_bound(ports@, i as int),
            bytes@.len() == offset + 8 * (i + 1),
            bytes@.take(offset) == base,
            word_at(bytes@.subrange(offset, offset + 8), 0) == ports@.len() as u64,
            forall|j: int| 0 <= j < i ==> {
                let port = #[trigger] ports@[j];
                &&& port.start == port_bound(ports@, j)
                &&& port.start < port.end <= total
                &&& word_at(bytes@.subrange(offset + 8 * (j + 1), offset + 8 * (j + 2)), 0)
                    == (port.end - port.start) as u64
            },
        decreases ports.len() - i,
    {
        let port = &ports[i];
        if port.start != bit || port.end <= bit || port.end > total {
            assert(ports@[i as int] == *port);
            assert(!checkpoint_ports_valid(ports@, total as int));
            return Err(VmCheckpointFileError::PortLayout);
        }
        let ghost prefix = bytes@;
        let width = port.end - bit;
        append_word(bytes, width)?;
        proof {
            assert(port_bound(ports@, (i + 1) as int) == port.end) by { reveal(port_bound); }
            preserved_segment(prefix, bytes@, 0, offset);
            preserved_segment(prefix, bytes@, offset, offset + 8);
            assert forall|j: int| 0 <= j <= i implies {
                let r = #[trigger] ports@[j];
                &&& r.start == port_bound(ports@, j)
                &&& r.start < r.end <= total
                &&& word_at(bytes@.subrange(offset + 8 * (j + 1), offset + 8 * (j + 2)), 0)
                    == (r.end - r.start) as u64
            } by {
                if j == i {
                    assert(ports@[j] == *port);
                    assert(bytes@.subrange(offset + 8 * (j + 1), offset + 8 * (j + 2))
                        =~= bytes@.skip(prefix.len() as int));
                } else {
                    preserved_segment(prefix, bytes@, offset + 8 * (j + 1), offset + 8 * (j + 2));
                }
            }
        }
        bit = port.end;
        i += 1;
    }
    if bit != total {
        return Err(VmCheckpointFileError::PortLayout);
    }
    proof {
        let encoded = bytes@.skip(offset);
        assert(encoded.subrange(0, 8) =~= bytes@.subrange(offset, offset + 8));
        assert forall|j: int| 0 <= j < ports@.len() implies
            word_at(encoded.subrange(8 * (j + 1), 8 * (j + 2)), 0)
                == (#[trigger] ports@[j].end - ports@[j].start) as u64 by {
            assert(encoded.subrange(8 * (j + 1), 8 * (j + 2))
                =~= bytes@.subrange(offset + 8 * (j + 1), offset + 8 * (j + 2)));
        }
        assert(ports_match(ports@, total as int, encoded));
    }
    Ok(())
}

} // verus!

verus! {

spec fn counted_wires(wires: Seq<Wire>, bytes: Seq<u8>) -> bool {
    &&& bytes.len() == 8 + 9 * wires.len()
    &&& word_at(bytes.take(8), 0) == wires.len() as u64
    &&& ordered_wire_layout(wires, bytes.skip(8))
}

fn append_wires(bytes: &mut Vec<u8>, wires: &[Wire]) -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> {
            let offset = old(bytes)@.len() as int;
            &&& final(bytes)@.take(offset) == old(bytes)@
            &&& final(bytes)@.len() == offset + 8 + 9 * wires@.len()
            &&& counted_wires(wires@, final(bytes)@.skip(offset))
        },
        result.is_err() ==> result == Err(VmCheckpointFileError::Allocation),
{
    hide(word_at);
    let ghost prefix = bytes@;
    let ghost offset = prefix.len() as int;
    append_word(bytes, wires.len())?;
    let ghost counted = bytes@;
    if append_ordered_wire_layout(bytes, wires).is_err() {
        return Err(VmCheckpointFileError::Allocation);
    }
    proof {
        preserved_segment(counted, bytes@, 0, offset);
        preserved_segment(counted, bytes@, offset, offset + 8);
        assert(bytes@.skip(offset).take(8) =~= counted.skip(offset));
        assert(bytes@.skip(offset).skip(8) =~= bytes@.skip(offset + 8));
    }
    Ok(())
}

spec fn ordered_gate_layout(gates: Seq<NorGate>, bytes: Seq<u8>) -> bool {
    &&& bytes.len() == 18 * gates.len()
    &&& forall|i: int| 0 <= i < gates.len() ==> {
        let gate = #[trigger] gates[i];
        &&& wire_layout_record(gate.left, bytes.subrange(18 * i, 18 * i + 9))
        &&& wire_layout_record(gate.right, bytes.subrange(18 * i + 9, 18 * (i + 1)))
    }
}

fn append_gates(bytes: &mut Vec<u8>, gates: &[NorGate]) -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> {
            let offset = old(bytes)@.len() as int;
            &&& final(bytes)@.take(offset) == old(bytes)@
            &&& final(bytes)@.len() == offset + 18 * gates@.len()
            &&& ordered_gate_layout(gates@, final(bytes)@.skip(offset))
        },
        result.is_err() ==> result == Err(VmCheckpointFileError::Allocation),
{
    let ghost prefix = bytes@;
    let ghost offset = prefix.len() as int;
    let mut i = 0;
    while i < gates.len()
        invariant
            i <= gates@.len(),
            bytes@.take(offset) == prefix,
            0 <= offset,
            bytes@.len() == offset + 18 * i,
            forall|j: int| 0 <= j < i ==> {
                let gate = #[trigger] gates@[j];
                &&& wire_layout_record(gate.left, bytes@.subrange(offset + 18 * j, offset + 18 * j + 9))
                &&& wire_layout_record(gate.right, bytes@.subrange(offset + 18 * j + 9, offset + 18 * (j + 1)))
            },
        decreases gates.len() - i,
    {
        let ghost previous = bytes@;
        let gate = gates[i];
        let left = write_wire_layout(gate.left);
        let right = write_wire_layout(gate.right);
        append(bytes, &left)?;
        append(bytes, &right)?;
        proof {
            assert(bytes@ == previous + left@ + right@);
            assert(bytes@.take(previous.len() as int) =~= previous);
            preserved_segment(previous, bytes@, 0, offset);
            assert forall|j: int| 0 <= j <= i implies {
                let gate = #[trigger] gates@[j];
                &&& wire_layout_record(gate.left, bytes@.subrange(offset + 18 * j, offset + 18 * j + 9))
                &&& wire_layout_record(gate.right, bytes@.subrange(offset + 18 * j + 9, offset + 18 * (j + 1)))
            } by {
                if j < i {
                    preserved_segment(previous, bytes@, offset + 18 * j, offset + 18 * j + 9);
                    preserved_segment(previous, bytes@, offset + 18 * j + 9, offset + 18 * (j + 1));
                } else {
                    assert(bytes@.subrange(offset + 18 * i, offset + 18 * i + 9) =~= left@);
                    assert(bytes@.subrange(offset + 18 * i + 9, offset + 18 * (i + 1)) =~= right@);
                }
            }
        }
        i += 1;
    }
    proof {
        let payload = bytes@.skip(offset);
        assert forall|j: int| 0 <= j < gates@.len() implies {
            let gate = #[trigger] gates@[j];
            &&& wire_layout_record(gate.left, payload.subrange(18 * j, 18 * j + 9))
            &&& wire_layout_record(gate.right, payload.subrange(18 * j + 9, 18 * (j + 1)))
        } by {
            assert(payload.subrange(18 * j, 18 * j + 9)
                =~= bytes@.subrange(offset + 18 * j, offset + 18 * j + 9));
            assert(payload.subrange(18 * j + 9, 18 * (j + 1))
                =~= bytes@.subrange(offset + 18 * j + 9, offset + 18 * (j + 1)));
        }
    }
    Ok(())
}

spec fn storage_address_end(wiring: &ClockedStorageInputs) -> int {
    match &wiring.address {
        None => 1,
        Some(address) => 17 + 9 * address@.len() as int,
    }
}

spec fn storage_record_len(wiring: &ClockedStorageInputs) -> int {
    storage_address_end(wiring) + 8 + 9 * wiring.data@.len() + 9
}

#[verifier::opaque]
spec fn storage_address_record(wiring: &ClockedStorageInputs, memory: Option<usize>, bytes: Seq<u8>) -> bool {
    let size = storage_address_end(wiring);
    &&& bytes.len() == size
    &&& match (&wiring.address, memory) {
        (None, None) => bytes[0] == 0,
        (Some(address), Some(memory_size)) => bytes[0] == 1
            && counted_wires(address@, bytes.subrange(1, size - 8))
            && word_at(bytes.skip(size - 8), 0) == memory_size as u64,
        _ => false,
    }
}

#[verifier::opaque]
spec fn storage_record(wiring: &ClockedStorageInputs, memory: Option<usize>, bytes: Seq<u8>) -> bool {
    let address_end = storage_address_end(wiring);
    let data_end = address_end + 8 + 9 * wiring.data@.len();
    &&& bytes.len() == storage_record_len(wiring)
    &&& storage_address_record(wiring, memory, bytes.take(address_end))
    &&& counted_wires(wiring.data@, bytes.subrange(address_end, data_end))
    &&& wire_layout_record(wiring.enable, bytes.skip(data_end))
}

fn append_storage_address(
    bytes: &mut Vec<u8>,
    wiring: &ClockedStorageInputs,
    memory: Option<usize>,
) -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> {
            let offset = old(bytes)@.len() as int;
            &&& final(bytes)@.take(offset) == old(bytes)@
            &&& final(bytes)@.len() == offset + storage_address_end(wiring)
            &&& storage_address_record(wiring, memory, final(bytes)@.skip(offset))
        },
        wiring.address.is_some() == memory.is_some() && result.is_err()
            ==> result == Err(VmCheckpointFileError::Allocation),
{
    hide(word_at);
    let ghost prefix = bytes@;
    let ghost offset = prefix.len() as int;
    match (&wiring.address, memory) {
        (Some(address), Some(size)) => {
            append(bytes, &[1])?;
            let ghost tag = bytes@;
            append_wires(bytes, address)?;
            let ghost addressed = bytes@;
            append_word(bytes, size)?;
            proof {
                preserved_segment(tag, addressed, 0, offset + 1);
                preserved_segment(addressed, bytes@, 0, offset + 1);
                preserved_segment(addressed, bytes@, offset + 1, addressed.len() as int);
                assert(bytes@.take(offset) =~= prefix);
                let record = bytes@.skip(offset);
                assert(record[0] == tag[offset]);
                assert(record.subrange(1, record.len() - 8) =~= addressed.skip(offset + 1));
                assert(record.skip(record.len() - 8) =~= bytes@.skip(addressed.len() as int));
                assert(storage_address_record(wiring, memory, record)) by { reveal(storage_address_record); }
            }
        },
        (None, None) => {
            append(bytes, &[0])?;
            assert(bytes@.take(offset) =~= prefix);
            assert(bytes@.skip(offset) =~= seq![0u8]);
            assert(storage_address_record(wiring, memory, bytes@.skip(offset))) by {
                reveal(storage_address_record);
            }
        },
        _ => return Err(VmCheckpointFileError::PortLayout),
    }
    Ok(())
}

fn append_storage_record(
    bytes: &mut Vec<u8>,
    wiring: &ClockedStorageInputs,
    memory: Option<usize>,
) -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> {
            let offset = old(bytes)@.len() as int;
            &&& final(bytes)@.take(offset) == old(bytes)@
            &&& final(bytes)@.len() == offset + storage_record_len(wiring)
            &&& storage_record(wiring, memory, final(bytes)@.skip(offset))
        },
        wiring.address.is_some() == memory.is_some() && result.is_err()
            ==> result == Err(VmCheckpointFileError::Allocation),
{
    let ghost prefix = bytes@;
    let ghost offset = prefix.len() as int;
    append_storage_address(bytes, wiring, memory)?;
    let ghost addressed = bytes@;
    let ghost address_end = addressed.len() as int;
    assert(address_end == offset + storage_address_end(wiring));
    append_wires(bytes, &wiring.data)?;
    let ghost wired = bytes@;
    let ghost data_end = wired.len() as int;
    let enabled = write_wire_layout(wiring.enable);
    append(bytes, &enabled)?;
    proof {
        assert(bytes@.take(data_end) =~= wired);
        preserved_segment(addressed, wired, 0, address_end);
        preserved_segment(wired, bytes@, 0, address_end);
        preserved_segment(wired, bytes@, address_end, data_end);
        assert(bytes@.take(offset) =~= prefix);
        let record = bytes@.skip(offset);
        assert(record.take(address_end - offset) =~= addressed.skip(offset));
        assert(record.subrange(address_end - offset, data_end - offset) =~= wired.skip(address_end));
        assert(record.skip(data_end - offset) =~= enabled@);
        assert(storage_record(wiring, memory, record)) by { reveal(storage_record); }
    }
    Ok(())
}


spec fn storage_memory_len(device: &ClockedStorage) -> Option<usize> {
    match device.memory_model() {
        Some(memory) => Some(memory.len() as usize),
        None => None,
    }
}

#[verifier::opaque]
spec fn storage_records(devices: Seq<ClockedStorage>, count: nat, bytes: Seq<u8>) -> bool
    decreases count,
{
    if count == 0 {
        bytes.len() == 0
    } else {
        let device = &devices[count - 1];
        let wiring = &device.wiring_model();
        let offset = bytes.len() - storage_record_len(wiring);
        &&& count <= devices.len()
        &&& 0 <= offset <= bytes.len()
        &&& storage_records(devices, (count - 1) as nat, bytes.take(offset))
        &&& storage_record(wiring, storage_memory_len(device), bytes.skip(offset))
    }
}
spec fn port_table_len(ports: Seq<Range<usize>>) -> int {
    8 * (ports.len() as int + 1)
}

spec fn wiring_prefix_len(vm: &ClockedVm, inputs: Seq<Range<usize>>, outputs: Seq<Range<usize>>) -> int {
    port_table_len(inputs) + port_table_len(outputs) + 16
        + 18 * vm.netlist_model().gates@.len() + 8 + 9 * vm.netlist_model().outputs@.len() + 8
}

#[verifier::opaque]
spec fn wiring_prefix(
    vm: &ClockedVm, inputs: Seq<Range<usize>>, outputs: Seq<Range<usize>>, bytes: Seq<u8>,
) -> bool {
    let netlist = vm.netlist_model();
    let inputs_end = port_table_len(inputs);
    let outputs_end = inputs_end + port_table_len(outputs);
    let gates_start = outputs_end + 16;
    let gates_end = gates_start + 18 * netlist.gates@.len();
    let outputs_wire_end = gates_end + 8 + 9 * netlist.outputs@.len();
    &&& bytes.len() == wiring_prefix_len(vm, inputs, outputs)
    &&& ports_match(inputs, vm.external_count() as int, bytes.take(inputs_end))
    &&& ports_match(outputs, netlist.outputs@.len() as int, bytes.subrange(inputs_end, outputs_end))
    &&& word_at(bytes.subrange(outputs_end, outputs_end + 8), 0) == netlist.input_count as u64
    &&& word_at(bytes.subrange(outputs_end + 8, gates_start), 0) == netlist.gates@.len() as u64
    &&& ordered_gate_layout(netlist.gates@, bytes.subrange(gates_start, gates_end))
    &&& counted_wires(netlist.outputs@, bytes.subrange(gates_end, outputs_wire_end))
    &&& word_at(bytes.skip(outputs_wire_end), 0) == vm.storage_model().len() as u64
}

/// 正準配線表が、ポート区画、展開配線と状態素子の順序・容量を記述することを表す。
#[verifier::opaque]
pub closed spec fn canonical_vm_layout(
    vm: &ClockedVm, inputs: Seq<Range<usize>>, outputs: Seq<Range<usize>>, bytes: Seq<u8>,
) -> bool {
    let prefix = wiring_prefix_len(vm, inputs, outputs);
    &&& 0 <= prefix <= bytes.len()
    &&& wiring_prefix(vm, inputs, outputs, bytes.take(prefix))
    &&& storage_records(vm.storage_model(), vm.storage_model().len(), bytes.skip(prefix))
}

fn layout_prefix(vm: &ClockedVm, inputs: &[Range<usize>], outputs: &[Range<usize>])
    -> (result: FileResult<Vec<u8>>)
    ensures result matches Ok(bytes) ==> wiring_prefix(vm, inputs@, outputs@, bytes@),
        checkpoint_ports_valid(inputs@, vm.external_count() as int)
            && checkpoint_ports_valid(outputs@, vm.netlist_model().outputs@.len() as int)
            && result.is_err() ==> result == Err(VmCheckpointFileError::Allocation),
{
    hide(word_at);
    let netlist = vm.netlist();
    let mut bytes = Vec::new();
    append_ports(&mut bytes, inputs, vm.external_input_count())?;
    let ghost input_record = bytes@;
    append_ports(&mut bytes, outputs, netlist.outputs.len())?;
    let ghost ports = bytes@;
    append_word(&mut bytes, netlist.input_count)?;
    let ghost input_count = bytes@;
    append_word(&mut bytes, netlist.gates.len())?;
    let ghost gate_count = bytes@;
    append_gates(&mut bytes, &netlist.gates)?;
    let ghost gates = bytes@;
    append_wires(&mut bytes, &netlist.outputs)?;
    let ghost output_wires = bytes@;
    append_word(&mut bytes, vm.storage_count())?;
    proof {
        let inputs_end = input_record.len() as int;
        let ports_end = ports.len() as int;
        let input_count_end = input_count.len() as int;
        let gates_start = gate_count.len() as int;
        let gates_end = gates.len() as int;
        let outputs_end = output_wires.len() as int;
        assert(inputs_end == port_table_len(inputs@));
        assert(ports_end == inputs_end + port_table_len(outputs@));
        assert(input_count_end == ports_end + 8 && gates_start == input_count_end + 8);
        assert(gates_end == gates_start + 18 * netlist.gates@.len());
        assert(outputs_end == gates_end + 8 + 9 * netlist.outputs@.len());
        preserved_segment(gate_count, gates, 0, gates_start);
        preserved_segment(gates, output_wires, 0, gates_start);
        preserved_segment(output_wires, bytes@, 0, gates_start);
        assert(bytes@.take(gates_start) =~= gate_count);
        assert(bytes@.take(input_count_end) =~= input_count);
        assert(bytes@.take(ports_end) =~= ports);
        assert(bytes@.take(inputs_end) =~= input_record);
        assert(bytes@.subrange(inputs_end, ports_end) =~= ports.skip(inputs_end));
        assert(bytes@.subrange(ports_end, input_count_end) =~= input_count.skip(ports_end));
        assert(bytes@.subrange(input_count_end, gates_start) =~= gate_count.skip(input_count_end));
        preserved_segment(gates, output_wires, gates_start, gates_end);
        preserved_segment(output_wires, bytes@, gates_start, gates_end);
        preserved_segment(output_wires, bytes@, gates_end, outputs_end);
        assert(bytes@.subrange(gates_start, gates_end) =~= gates.skip(gates_start));
        assert(bytes@.subrange(gates_end, outputs_end) =~= output_wires.skip(gates_end));
        assert(input_record.skip(0) =~= input_record);
        assert(netlist == &vm.netlist_model());
        assert(ports_match(inputs@, vm.external_count() as int, bytes@.take(inputs_end)));
        assert(ports_match(outputs@, netlist.outputs@.len() as int, bytes@.subrange(inputs_end, ports_end)));
        assert(word_at(bytes@.subrange(ports_end, input_count_end), 0) == netlist.input_count as u64);
        assert(word_at(bytes@.subrange(input_count_end, gates_start), 0) == netlist.gates@.len() as u64);
        assert(ordered_gate_layout(netlist.gates@, bytes@.subrange(gates_start, gates_end)));
        assert(counted_wires(netlist.outputs@, bytes@.subrange(gates_end, outputs_end)));
        assert(word_at(bytes@.skip(outputs_end), 0) == vm.storage_model().len() as u64);
        assert(wiring_prefix(vm, inputs@, outputs@, bytes@)) by { reveal(wiring_prefix); }
    }
    Ok(bytes)
}

} // verus!

verus! {

fn packed_len(bits: usize) -> (len: usize)
    ensures len == (bits as int + 7) / 8,
{
    bits / 8 + if bits % 8 != 0 { 1 } else { 0 }
}

fn add_bits(length: &mut usize, bits: usize) -> (result: FileResult<()>)
    ensures
        result.is_ok() <==> *old(length) + (bits as int + 7) / 8 <= usize::MAX,
        result.is_ok() ==> *final(length) == *old(length) + (bits as int + 7) / 8,
        result.is_err() ==> *final(length) == *old(length) && result == Err(VmCheckpointFileError::Allocation),
{
    *length = length.checked_add(packed_len(bits)).ok_or(VmCheckpointFileError::Allocation)?;
    Ok(())
}

} // verus!

verus! {

proof fn storage_records_push(devices: Seq<ClockedStorage>, count: nat, prefix: Seq<u8>, record: Seq<u8>)
    requires
        count < devices.len(),
        storage_records(devices, count, prefix),
        record.len() == storage_record_len(&devices[count as int].wiring_model()),
        storage_record(
            &devices[count as int].wiring_model(), storage_memory_len(&devices[count as int]), record,
        ),
    ensures storage_records(devices, count + 1, prefix + record),
{
    let combined = prefix + record;
    assert(combined.len() - storage_record_len(&devices[count as int].wiring_model()) == prefix.len());
    assert(combined.take(prefix.len() as int) =~= prefix);
    assert(combined.skip(prefix.len() as int) =~= record);
    assert(storage_records(devices, count + 1, combined)) by { reveal(storage_records); }
}

fn layout(vm: &ClockedVm, inputs: &[Range<usize>], outputs: &[Range<usize>])
    -> (result: FileResult<(Vec<u8>, usize)>)
    requires vm.valid(),
    ensures
        result matches Ok((bytes, size)) ==> canonical_vm_layout(vm, inputs@, outputs@, bytes@)
            && size == vm_checkpoint_state_len(vm),
        checkpoint_ports_valid(inputs@, vm.external_count() as int)
            && checkpoint_ports_valid(outputs@, vm.netlist_model().outputs@.len() as int)
            && result.is_err() ==> result == Err(VmCheckpointFileError::Allocation),
{
    let mut bytes = layout_prefix(vm, inputs, outputs)?;
    let ghost prefix = bytes@;
    let ghost offset = prefix.len() as int;
    assert(offset == wiring_prefix_len(vm, inputs@, outputs@)) by { reveal(wiring_prefix); }
    proof {
        assert(prefix.skip(offset) =~= Seq::<u8>::empty());
        assert(storage_records(vm.storage_model(), 0, prefix.skip(offset))) by { reveal(storage_records); }
    }
    let mut size = 0;
    add_bits(&mut size, vm.external_input_count())?;
    add_bits(&mut size, vm.nor_gate_count())?;
    let ghost base_sz = size;
    assert(checkpoint_storage_state_len(vm.storage_model(), 0) == 0) by {
        reveal(checkpoint_storage_state_len);
    };
    let mut i = 0;
    while i < vm.storage_count()
        invariant
            vm.valid(),
            i <= vm.storage_model().len(),
            0 <= offset <= bytes@.len(),
            offset == wiring_prefix_len(vm, inputs@, outputs@),
            wiring_prefix(vm, inputs@, outputs@, prefix),
            bytes@.take(offset) == prefix,
            storage_records(vm.storage_model(), i as nat, bytes@.skip(offset)),
            base_sz == (vm.external_count() as int + 7) / 8
                + (vm.netlist_model().gates@.len() as int + 7) / 8,
            size == base_sz + checkpoint_storage_state_len(vm.storage_model(), i as nat),
        decreases vm.storage_model().len() - i,
    {
        let Some((wiring, _registered)) = vm.storage_wiring(i) else {
            return Err(VmCheckpointFileError::PortLayout);
        };
        let memory = match vm.ram_memory(i) {
            Some(memory) => Some(memory.len()),
            None => None,
        };
        let ghost device = &vm.storage_model()[i as int];
        proof {
            vm.storage_shape_evidence(i as int);
            assert(memory.is_some() == wiring.address.is_some());
        }
        let ghost previous = bytes@;
        let ghost previous_size = size as int;
        append_storage_record(&mut bytes, wiring, memory)?;
        add_bits(&mut size, wiring.data.len())?;
        if let Some(memory_bits) = memory {
            add_bits(&mut size, memory_bits)?;
        }
        proof {
            let record = bytes@.skip(previous.len() as int);
            assert(memory == storage_memory_len(device));
            assert(size == previous_size + checkpoint_device_state_len(device));
            assert(bytes@.take(previous.len() as int) =~= previous);
            preserved_segment(previous, bytes@, 0, offset);
            assert(bytes@.skip(offset) =~= previous.skip(offset) + record);
            storage_records_push(vm.storage_model(), i as nat, previous.skip(offset), record);
            checkpoint_storage_state_len_push(vm.storage_model(), i as nat);
        }
        i += 1;
    }
    assert(canonical_vm_layout(vm, inputs@, outputs@, bytes@)) by { reveal(canonical_vm_layout); }
    Ok((bytes, size))
}

} // verus!

verus! {

/// 復元先の回路構成で受理するファイルの長さを返す。
pub fn checkpoint_file_len(
    vm: &ClockedVm,
    inputs: &[Range<usize>],
    outputs: &[Range<usize>],
) -> (result: FileResult<usize>)
    requires vm.valid(),
    ensures
        result matches Ok(length) ==> length <= isize::MAX
            && length == CHECKPOINT_HEADER_BYTES + checkpoint_wiring_table_len(vm, inputs@, outputs@)
                + vm_checkpoint_state_len(vm),
        checkpoint_ports_valid(inputs@, vm.external_count() as int)
            && checkpoint_ports_valid(outputs@, vm.netlist_model().outputs@.len() as int)
            && result.is_err() ==> result == Err(VmCheckpointFileError::Allocation),
{
    let netlist = vm.netlist();
    validate_checkpoint_ports(inputs, vm.external_input_count())?;
    validate_checkpoint_ports(outputs, netlist.outputs.len())?;
    // 端子数を2個、入力幅、NOR 数、出力配線数、状態素子数を各8バイトで持つ。
    let mut wiring_bytes = 6 * 8;
    add_layout_records(&mut wiring_bytes, inputs.len(), 8)?;
    add_layout_records(&mut wiring_bytes, outputs.len(), 8)?;
    add_layout_records(&mut wiring_bytes, netlist.gates.len(), 18)?;
    add_layout_records(&mut wiring_bytes, netlist.outputs.len(), 9)?;
    let ghost wiring_base = wiring_bytes as int;
    let mut state_bytes = 0;
    add_bits(&mut state_bytes, vm.external_input_count())?;
    add_bits(&mut state_bytes, netlist.gates.len())?;
    let ghost state_base = state_bytes as int;
    let count = vm.storage_count();
    let mut index = 0;
    proof {
        reveal(checkpoint_storage_state_len);
        reveal(checkpoint_storage_table_len);
        assert(checkpoint_storage_state_len(vm.storage_model(), 0) == 0);
        assert(checkpoint_storage_table_len(vm.storage_model(), 0) == 0);
    }
    while index < count
        invariant
            vm.valid(),
            count == vm.storage_model().len(),
            index <= count,
            wiring_base == wiring_prefix_len(vm, inputs@, outputs@),
            state_base == vm_payload_head_len(vm),
            wiring_bytes == wiring_base + checkpoint_storage_table_len(vm.storage_model(), index as nat),
            state_bytes == state_base + checkpoint_storage_state_len(vm.storage_model(), index as nat),
        decreases count - index,
    {
        let (wiring, _) = vm.storage_wiring(index).ok_or(VmCheckpointFileError::PortLayout)?;
        let ghost previous_wiring = wiring_bytes as int;
        let ghost previous_state = state_bytes as int;
        add_layout_records(&mut wiring_bytes, 1, 18)?;
        add_layout_records(&mut wiring_bytes, wiring.data.len(), 9)?;
        if let Some(address) = &wiring.address {
            add_layout_records(&mut wiring_bytes, 1, 16)?;
            add_layout_records(&mut wiring_bytes, address.len(), 9)?;
        }
        add_bits(&mut state_bytes, wiring.data.len())?;
        let memory = vm.ram_memory(index);
        if let Some(bits) = memory {
            add_bits(&mut state_bytes, bits.len())?;
        }
        proof {
            vm.storage_shape_evidence(index as int);
            let device = vm.storage_model()[index as int];
            assert(wiring_bytes == previous_wiring + storage_record_len(wiring));
            assert(state_bytes == previous_state + checkpoint_device_state_len(&device));
            checkpoint_storage_table_len_push(vm.storage_model(), index as nat);
            checkpoint_storage_state_len_push(vm.storage_model(), index as nat);
        }
        index += 1;
    }
    let padded = CHECKPOINT_HEADER_BYTES.checked_add(wiring_bytes)
        .ok_or(VmCheckpointFileError::Allocation)?;
    let length = padded.checked_add(state_bytes).ok_or(VmCheckpointFileError::Allocation)?;
    if length > isize::MAX as usize {
        return Err(VmCheckpointFileError::Allocation);
    }
    Ok(length)
}

#[verifier::opaque]
spec fn checkpoint_storage_table_len(devices: Seq<ClockedStorage>, count: nat) -> int
    decreases count,
{
    if count == 0 { 0 } else {
        checkpoint_storage_table_len(devices, (count - 1) as nat)
            + storage_record_len(&devices[count - 1].wiring_model())
    }
}

proof fn checkpoint_storage_table_len_push(devices: Seq<ClockedStorage>, count: nat)
    requires count < devices.len(),
    ensures checkpoint_storage_table_len(devices, count + 1)
        == checkpoint_storage_table_len(devices, count)
            + storage_record_len(&devices[count as int].wiring_model()),
{
    reveal(checkpoint_storage_table_len);
}

pub closed spec fn checkpoint_wiring_table_len(
    vm: &ClockedVm,
    inputs: Seq<Range<usize>>,
    outputs: Seq<Range<usize>>,
) -> int {
    wiring_prefix_len(vm, inputs, outputs)
        + checkpoint_storage_table_len(vm.storage_model(), vm.storage_model().len())
}

proof fn storage_table_len_matches(devices: Seq<ClockedStorage>, count: nat, table: Seq<u8>)
    requires count <= devices.len(), storage_records(devices, count, table),
    ensures table.len() == checkpoint_storage_table_len(devices, count),
    decreases count,
{
    reveal(storage_records);
    if count == 0 {
        reveal(checkpoint_storage_table_len);
    } else {
        let previous = (count - 1) as nat;
        let record_len = storage_record_len(&devices[previous as int].wiring_model());
        let boundary = table.len() - record_len;
        storage_table_len_matches(devices, previous, table.take(boundary));
        checkpoint_storage_table_len_push(devices, previous);
    }
}

/// 正準配線表の長さは、VM の構成と端子区画で決まる。
pub proof fn canonical_checkpoint_layout_len(
    vm: &ClockedVm,
    inputs: Seq<Range<usize>>,
    outputs: Seq<Range<usize>>,
    table: Seq<u8>,
)
    requires canonical_vm_layout(vm, inputs, outputs, table),
    ensures table.len() == checkpoint_wiring_table_len(vm, inputs, outputs),
{
    reveal(canonical_vm_layout);
    let prefix = wiring_prefix_len(vm, inputs, outputs);
    storage_table_len_matches(vm.storage_model(), vm.storage_model().len(), table.skip(prefix));
}

fn add_layout_records(length: &mut usize, count: usize, width: usize) -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> *final(length) == *old(length) + count * width,
        result.is_err() ==> result == Err(VmCheckpointFileError::Allocation) && *final(length) == *old(length),
{
    let bytes = count.checked_mul(width).ok_or(VmCheckpointFileError::Allocation)?;
    *length = length.checked_add(bytes).ok_or(VmCheckpointFileError::Allocation)?;
    Ok(())
}

fn validate_checkpoint_ports(ports: &[Range<usize>], total: usize) -> (result: FileResult<()>)
    ensures
        result.is_ok() <==> checkpoint_ports_valid(ports@, total as int),
        result.is_err() ==> result == Err(VmCheckpointFileError::PortLayout),
{
    hide(port_bound);
    assert(port_bound(ports@, 0) == 0) by { reveal(port_bound); }
    let mut bit = 0;
    let mut index = 0;
    while index < ports.len()
        invariant
            index <= ports@.len(),
            bit == port_bound(ports@, index as int),
            forall|j: int| 0 <= j < index ==> {
                let port = #[trigger] ports@[j];
                &&& port.start == port_bound(ports@, j)
                &&& port.start < port.end <= total
            },
        decreases ports.len() - index,
    {
        let port = &ports[index];
        if port.start != bit || port.end <= bit || port.end > total {
            assert(ports@[index as int] == *port);
            assert(!checkpoint_ports_valid(ports@, total as int));
            return Err(VmCheckpointFileError::PortLayout);
        }
        assert(port_bound(ports@, (index + 1) as int) == port.end) by { reveal(port_bound); }
        bit = port.end;
        index += 1;
    }
    if bit != total {
        return Err(VmCheckpointFileError::PortLayout);
    }
    Ok(())
}

fn bit_error(error: CheckpointBitError) -> (result: VmCheckpointFileError)
    ensures match error {
        CheckpointBitError::Malformed => result == VmCheckpointFileError::MalformedState,
        CheckpointBitError::Allocation => result == VmCheckpointFileError::Allocation,
    },
{
    match error {
        CheckpointBitError::Malformed => VmCheckpointFileError::MalformedState,
        CheckpointBitError::Allocation => VmCheckpointFileError::Allocation,
    }
}

fn append_bits(bytes: &mut Vec<u8>, bits: &[bool]) -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> {
            let offset = old(bytes)@.len() as int;
            &&& final(bytes)@.len() == offset + (bits@.len() + 7) / 8
            &&& final(bytes)@.take(offset) == old(bytes)@
            &&& bits@.len() <= isize::MAX
            &&& packed_checkpoint_bits(bits@, final(bytes)@.skip(offset))
        },
        result.is_err() ==> final(bytes)@ == old(bytes)@
            && result == Err(VmCheckpointFileError::Allocation),
{
    let encoded = match pack_checkpoint_bits(bits) {
        Ok(encoded) => encoded,
        Err(error) => return Err(bit_error(error)),
    };
    let ghost prefix = bytes@;
    append(bytes, &encoded)?;
    proof {
        assert(bytes@.take(prefix.len() as int) =~= prefix);
        assert(bytes@.skip(prefix.len() as int) =~= encoded@);
    }
    Ok(())
}

spec fn payload_pair(leading: Seq<bool>, trailing: Option<Seq<bool>>, bytes: Seq<u8>) -> bool {
    let leading_bytes = (leading.len() as int + 7) / 8;
    &&& leading_bytes <= bytes.len()
    &&& leading.len() <= isize::MAX
    &&& packed_checkpoint_bits(leading, bytes.take(leading_bytes))
    &&& match trailing {
        Some(bits) => bits.len() <= isize::MAX && packed_checkpoint_bits(bits, bytes.skip(leading_bytes)),
        None => bytes.len() == leading_bytes,
    }
}

proof fn payload_pair_is_injective(
    first_leading: Seq<bool>,
    second_leading: Seq<bool>,
    first_trailing: Option<Seq<bool>>,
    second_trailing: Option<Seq<bool>>,
    bytes: Seq<u8>,
)
    requires
        first_leading.len() == second_leading.len(),
        match (first_trailing, second_trailing) {
            (Some(a), Some(b)) => a.len() == b.len(),
            (None, None) => true,
            _ => false,
        },
        payload_pair(first_leading, first_trailing, bytes),
        payload_pair(second_leading, second_trailing, bytes),
    ensures first_leading == second_leading, first_trailing == second_trailing,
{
    let leading_bytes = (first_leading.len() as int + 7) / 8;
    checkpoint_bits_roundtrip(first_leading, second_leading, bytes.take(leading_bytes));
    if let (Some(a), Some(b)) = (first_trailing, second_trailing) {
        checkpoint_bits_roundtrip(a, b, bytes.skip(leading_bytes));
    }
}

fn append_payload_pair(bytes: &mut Vec<u8>, leading: &[bool], trailing: Option<&[bool]>)
    -> (result: FileResult<()>)
    ensures
        result.is_ok() ==> {
            let start = old(bytes)@.len() as int;
            let length = (leading@.len() + 7) / 8
                + match trailing { Some(bits) => (bits@.len() + 7) / 8, None => 0 };
            &&& final(bytes)@.len() == start + length
            &&& final(bytes)@.take(start) == old(bytes)@
            &&& payload_pair(leading@, match trailing { Some(bits) => Some(bits@), None => None }, final(bytes)@.skip(start))
        },
        result.is_err() ==> result == Err(VmCheckpointFileError::Allocation),
{
    let ghost prefix = bytes@;
    let ghost start = prefix.len() as int;
    append_bits(bytes, leading)?;
    let ghost after_leading = bytes@;
    if let Some(bits) = trailing {
        append_bits(bytes, bits)?;
    } else {
        assert(bytes@.take(after_leading.len() as int) =~= after_leading);
    }
    proof {
        let end = after_leading.len() as int;
        preserved_segment(after_leading, bytes@, 0, start);
        preserved_segment(after_leading, bytes@, start, end);
        let section = bytes@.skip(start);
        assert(section.take(end - start) =~= after_leading.skip(start));
        assert(section.skip(end - start) =~= bytes@.skip(end));
        assert(payload_pair(leading@, match trailing { Some(bits) => Some(bits@), None => None }, section));
    }
    Ok(())
}



/// 現在の確定状態からファイルを作る。VM は更新しない。
///
/// 呼び出し側は同じ確定 tick の VM と時刻情報、およびその tick に最後に適用した入力を渡す。
/// 各入出力端子は1ビット以上とし、端子の範囲を0から隙間なく並べる。
pub fn encode_vm_checkpoint(
    vm: &ClockedVm,
    inputs: &[Range<usize>],
    outputs: &[Range<usize>],
    header: CheckpointHeader,
    input: &[bool],
) -> (result: FileResult<Vec<u8>>)
    requires vm.valid(),
    ensures
        result matches Ok(file) ==> checkpoint_file_encodes(vm, inputs@, outputs@, header, input@, file@),
        input@.len() != vm.external_count() ==> result == Err(VmCheckpointFileError::PortLayout),
{
    if input.len() != vm.external_input_count() {
        return Err(VmCheckpointFileError::PortLayout);
    }
    let (layout, size) = layout(vm, inputs, outputs)?;
    let state = encode_checkpoint_payload(vm, input, size)?;
    let file = match write_checkpoint_file(header, &layout, &state) {
        Ok(file) => file,
        Err(error) => return Err(VmCheckpointFileError::File(error)),
    };
    assert(checkpoint_file_encodes(vm, inputs@, outputs@, header, input@, file@));
    Ok(file)
}



fn read_bits<'a>(remaining: &mut &'a [u8], bits: usize) -> (result: FileResult<Vec<bool>>)
    ensures
        result matches Ok(values) ==> {
            let length = (bits as int + 7) / 8;
            &&& length <= (*old(remaining))@.len()
            &&& values@.len() == bits <= isize::MAX
            &&& packed_checkpoint_bits(values@, (*old(remaining))@.take(length))
            &&& (*final(remaining))@ == (*old(remaining))@.skip(length)
        },
        result.is_err() ==> (*final(remaining))@ == (*old(remaining))@,
        result.is_err() ==> result == Err(VmCheckpointFileError::MalformedState)
            || result == Err(VmCheckpointFileError::Allocation),
        (result == Err(VmCheckpointFileError::MalformedState)) <==> {
            let length = (bits as int + 7) / 8;
            ||| (*old(remaining))@.len() < length
            ||| !checkpoint_segment_valid((*old(remaining))@.take(length), bits as int)
        },
{
    let (bytes, rest) = remaining.split_at_checked(packed_len(bits))
        .ok_or(VmCheckpointFileError::MalformedState)?;
    let result = match unpack_checkpoint_bits(bytes, bits) {
        Ok(values) => values,
        Err(error) => return Err(bit_error(error)),
    };
    *remaining = rest;
    Ok(result)
}

spec fn payload_pair_prefix_valid(bytes: Seq<u8>, leading: int, trailing: Option<usize>) -> bool {
    let head = (leading + 7) / 8;
    &&& head <= bytes.len()
    &&& checkpoint_segment_valid(bytes.take(head), leading)
    &&& match trailing {
        Some(bits) => {
            let tail = (bits as int + 7) / 8;
            &&& head + tail <= bytes.len()
            &&& checkpoint_segment_valid(bytes.skip(head).take(tail), bits as int)
        },
        None => true,
    }
}

proof fn encoded_pair_has_valid_prefix(
    leading: Seq<bool>,
    trailing: Option<Seq<bool>>,
    remainder: Seq<u8>,
    end: int,
)
    requires
        0 <= end <= remainder.len(),
        payload_pair(leading, trailing, remainder.take(end)),
    ensures payload_pair_prefix_valid(remainder, leading.len() as int,
        match trailing { Some(bits) => Some(bits.len() as usize), None => None }),
{
    let head = (leading.len() as int + 7) / 8;
    let bytes = remainder.take(end);
    assert(bytes.take(head) =~= remainder.take(head));
    if let Some(bits) = trailing {
        let tail = (bits.len() as int + 7) / 8;
        assert(end == head + tail);
        assert(bytes.skip(head) =~= remainder.skip(head).take(tail));
    }
}

fn read_payload_pair<'a>(
    remaining: &mut &'a [u8],
    leading_bits: usize,
    trailing_bits: Option<usize>,
) -> (result: FileResult<(Vec<bool>, Option<Vec<bool>>)>)
    ensures
        result matches Ok((leading, trailing)) ==> {
            let consumed = (leading_bits as int + 7) / 8 + match trailing_bits {
                Some(count) => (count as int + 7) / 8,
                None => 0,
            };
            &&& consumed <= (*old(remaining))@.len()
            &&& leading@.len() == leading_bits
            &&& match (trailing_bits, &trailing) {
                (Some(count), Some(bits)) => count == bits@.len(),
                (None, None) => true,
                _ => false,
            }
            &&& payload_pair(leading@, match &trailing { Some(bits) => Some(bits@), None => None },
                (*old(remaining))@.take(consumed))
            &&& (*final(remaining))@ == (*old(remaining))@.skip(consumed)
        },
        result.is_err() ==> (*final(remaining))@ == (*old(remaining))@,
        payload_pair_prefix_valid((*old(remaining))@, leading_bits as int, trailing_bits) ==>
            result.is_ok() || result == Err(VmCheckpointFileError::Allocation),
{
    let mut next = *remaining;
    let ghost full = next@;
    let leading = read_bits(&mut next, leading_bits)?;
    let trailing = match trailing_bits {
        Some(count) => Some(read_bits(&mut next, count)?),
        None => None,
    };
    proof {
        let cut = (leading_bits as int + 7) / 8;
        let consumed = cut + match trailing_bits {
            Some(count) => (count as int + 7) / 8,
            None => 0,
        };
        let section = full.take(consumed);
        assert(section.take(cut) =~= full.take(cut));
        assert(section.skip(cut) =~= full.skip(cut).take(consumed - cut));
        assert(next@ =~= full.skip(consumed));
    }
    *remaining = next;
    Ok((leading, trailing))
}


/// 1素子の登録出力と RAM 内容をそれぞれバイト境界で区切った状態部の長さ。
pub open spec fn checkpoint_device_state_len(device: &ClockedStorage) -> int {
    (device.output_model().len() as int + 7) / 8
        + match device.memory_model() {
            Some(bits) => (bits.len() as int + 7) / 8,
            None => 0,
        }
}

/// 宣言順で先頭から count 個の状態素子が占める状態部の長さ。
#[verifier::opaque]
pub open spec fn checkpoint_storage_state_len(devices: Seq<ClockedStorage>, count: nat) -> int
    decreases count,
{
    if count == 0 {
        0
    } else {
        checkpoint_storage_state_len(devices, (count - 1) as nat)
            + checkpoint_device_state_len(&devices[count - 1])
    }
}

/// 状態素子を宣言順で1個追加したときの状態部の長さ。
pub proof fn checkpoint_storage_state_len_push(devices: Seq<ClockedStorage>, count: nat)
    requires count < devices.len(),
    ensures checkpoint_storage_state_len(devices, count + 1)
        == checkpoint_storage_state_len(devices, count) + checkpoint_device_state_len(&devices[count as int]),
{
    reveal(checkpoint_storage_state_len);
}

/// 最後の入力、NOR 出力、各状態素子の状態を格納するバイト数。
pub open spec fn vm_checkpoint_state_len(vm: &ClockedVm) -> int {
    (vm.external_count() as int + 7) / 8
        + (vm.netlist_model().gates@.len() as int + 7) / 8
        + checkpoint_storage_state_len(vm.storage_model(), vm.storage_model().len())
}

spec fn vm_payload_head_len(vm: &ClockedVm) -> int {
    (vm.external_count() as int + 7) / 8 + (vm.netlist_model().gates@.len() as int + 7) / 8
}

spec fn vm_payload_device_start(vm: &ClockedVm, index: int) -> int {
    vm_payload_head_len(vm) + checkpoint_storage_state_len(vm.storage_model(), index as nat)
}

spec fn decoded_payload_matches(
    vm: &ClockedVm,
    input: Seq<bool>,
    gates: Seq<bool>,
    storage: Seq<ClockedStorageCheckpoint>,
    bytes: Seq<u8>,
) -> bool {
    &&& bytes.len() == vm_checkpoint_state_len(vm)
    &&& payload_pair(input, Some(gates), bytes.take(vm_payload_head_len(vm)))
    &&& storage.len() == vm.storage_model().len()
    &&& forall|i: int| 0 <= i < storage.len() ==> {
        let saved = #[trigger] storage[i];
        let start = vm_payload_device_start(vm, i);
        let end = vm_payload_device_start(vm, i + 1);
        &&& 0 <= start <= end <= bytes.len()
        &&& payload_pair(saved.output@, saved.memory_model(), bytes.subrange(start, end))
    }
}

spec fn encoded_payload_matches(vm: &ClockedVm, input: Seq<bool>, bytes: Seq<u8>) -> bool {
    &&& bytes.len() == vm_checkpoint_state_len(vm)
    &&& payload_pair(input, Some(vm.gate_values_model()), bytes.take(vm_payload_head_len(vm)))
    &&& forall|i: int| 0 <= i < vm.storage_model().len() ==> {
        let device = #[trigger] vm.storage_model()[i];
        let start = vm_payload_device_start(vm, i);
        let end = vm_payload_device_start(vm, i + 1);
        &&& 0 <= start <= end <= bytes.len()
        &&& payload_pair(device.output_model(), device.memory_model(), bytes.subrange(start, end))
    }
}

spec fn checkpoint_payload_offset(vm: &ClockedVm, file: Seq<u8>) -> int {
    file.len() - vm_checkpoint_state_len(vm)
}

/// 保存時のヘッダー、配線表と VM の全状態が同じファイルに含まれることを表す。
pub closed spec fn checkpoint_file_encodes(
    vm: &ClockedVm,
    inputs: Seq<Range<usize>>,
    outputs: Seq<Range<usize>>,
    header: CheckpointHeader,
    input: Seq<bool>,
    file: Seq<u8>,
) -> bool {
    let offset = checkpoint_payload_offset(vm, file);
    &&& CHECKPOINT_HEADER_BYTES <= offset <= file.len()
    &&& input.len() == vm.external_count()
    &&& checkpoint_header_matches(file, header)
    &&& canonical_vm_layout(vm, inputs, outputs, file.subrange(CHECKPOINT_HEADER_BYTES as int, offset))
    &&& encoded_payload_matches(vm, input, file.skip(offset))
    &&& checkpoint_payload_valid(vm, file.skip(offset))
}

/// 復号結果のヘッダー、入力、状態がファイルと復元先の回路に一致することを表す。
pub closed spec fn checkpoint_file_decodes(
    vm: &ClockedVm,
    inputs: Seq<Range<usize>>,
    outputs: Seq<Range<usize>>,
    period: (u64, u64),
    file: Seq<u8>,
    decoded: &DecodedCheckpoint,
) -> bool {
    let offset = checkpoint_payload_offset(vm, file);
    &&& CHECKPOINT_HEADER_BYTES <= offset <= file.len()
    &&& checkpoint_header_matches(file, decoded.header)
    &&& (decoded.header.period_numerator, decoded.header.period_denominator) == period
    &&& canonical_vm_layout(vm, inputs, outputs, file.subrange(CHECKPOINT_HEADER_BYTES as int, offset))
    &&& decoded.input@.len() == vm.external_count()
    &&& decoded.vm.layout_matches(vm)
    &&& decoded.vm.state_shape_matches(vm)
    &&& decoded_payload_matches(vm, decoded.input@, decoded.vm.gates@, decoded.vm.storage@, file.skip(offset))
}

/// スナップショットを共有できる VM の配線と状態の形を表す。
pub open spec fn checkpoint_vms_compatible(source: &ClockedVm, target: &ClockedVm) -> bool {
    &&& source.external_count() == target.external_count()
    &&& same_ordered_netlist(&source.netlist_model(), &target.netlist_model())
    &&& source.storage_model().len() == target.storage_model().len()
    &&& forall|i: int| 0 <= i < source.storage_model().len() ==> {
        let before = #[trigger] source.storage_model()[i];
        let after = target.storage_model()[i];
        &&& same_ordered_storage_wiring(&before.wiring_model(), &after.wiring_model())
        &&& before.output_model().len() == after.output_model().len()
        &&& match (before.memory_model(), after.memory_model()) {
            (Some(first), Some(second)) => first.len() == second.len(),
            (None, None) => true,
            _ => false,
        }
    }
}

/// 形式、周期、端子区画、配線および全状態が復元先の条件を満たすファイル。
#[verifier::opaque]
pub closed spec fn checkpoint_file_admissible(
    vm: &ClockedVm,
    inputs: Seq<Range<usize>>,
    outputs: Seq<Range<usize>>,
    period: (u64, u64),
    file: Seq<u8>,
) -> bool {
    let offset = checkpoint_payload_offset(vm, file);
    &&& CHECKPOINT_HEADER_BYTES <= offset <= file.len()
    &&& exists|header: CheckpointHeader| #[trigger] checkpoint_header_matches(file, header)
        && (header.period_numerator, header.period_denominator) == period
    &&& canonical_vm_layout(vm, inputs, outputs, file.subrange(CHECKPOINT_HEADER_BYTES as int, offset))
    &&& checkpoint_payload_valid(vm, file.skip(offset))
}

proof fn canonical_checkpoint_ports_valid(
    vm: &ClockedVm, inputs: Seq<Range<usize>>, outputs: Seq<Range<usize>>, layout: Seq<u8>,
)
    requires canonical_vm_layout(vm, inputs, outputs, layout),
    ensures checkpoint_ports_valid(inputs, vm.external_count() as int),
        checkpoint_ports_valid(outputs, vm.netlist_model().outputs@.len() as int),
{
    reveal(canonical_vm_layout);
    reveal(wiring_prefix);
}

/// 同じ回路構成と周期を使う復元先では、保存したファイルを受理できる。
pub proof fn checkpoint_file_encoding_is_admissible(
    source: &ClockedVm,
    target: &ClockedVm,
    inputs: Seq<Range<usize>>,
    outputs: Seq<Range<usize>>,
    header: CheckpointHeader,
    input: Seq<bool>,
    file: Seq<u8>,
)
    requires
        checkpoint_vms_compatible(source, target),
        checkpoint_file_encodes(source, inputs, outputs, header, input, file),
    ensures checkpoint_file_admissible(target, inputs, outputs,
        (header.period_numerator, header.period_denominator), file),
{
    let count = source.storage_model().len();
    compatible_state_offsets_agree(source, target, count);
    assert(vm_checkpoint_state_len(source) == vm_checkpoint_state_len(target));
    let offset = checkpoint_payload_offset(source, file);
    canonical_vm_layout_transfers(source, target, inputs, outputs, file.subrange(CHECKPOINT_HEADER_BYTES as int, offset));
    compatible_checkpoint_payload(source, target, file.skip(offset));
    reveal(checkpoint_file_admissible);
}

proof fn compatible_checkpoint_payload(source: &ClockedVm, target: &ClockedVm, data: Seq<u8>)
    requires checkpoint_vms_compatible(source, target), checkpoint_payload_valid(source, data),
    ensures checkpoint_payload_valid(target, data),
{
    compatible_state_offsets_agree(source, target, source.storage_model().len());
    assert forall|i: int| 0 <= i < target.storage_model().len() implies {
        let device = #[trigger] target.storage_model()[i];
        let start = vm_payload_device_start(target, i);
        &&& 0 <= start <= data.len()
        &&& payload_pair_prefix_valid(data.skip(start), device.output_model().len() as int,
            checkpoint_ram_bits(&device))
    } by {
        let before = source.storage_model()[i];
        let after = target.storage_model()[i];
        compatible_state_offsets_agree(source, target, i as nat);
        assert(checkpoint_ram_bits(&before) == checkpoint_ram_bits(&after));
    }
}


proof fn compatible_state_offsets_agree(source: &ClockedVm, target: &ClockedVm, count: nat)
    requires checkpoint_vms_compatible(source, target), count <= source.storage_model().len(),
    ensures vm_payload_device_start(source, count as int) == vm_payload_device_start(target, count as int),
    decreases count,
{
    if count == 0 {
        reveal(checkpoint_storage_state_len);
    } else {
        let previous = (count - 1) as nat;
        compatible_state_offsets_agree(source, target, previous);
        let a = source.storage_model()[previous as int];
        let b = target.storage_model()[previous as int];
        checkpoint_storage_state_len_push(source.storage_model(), previous);
        checkpoint_storage_state_len_push(target.storage_model(), previous);
        assert(checkpoint_device_state_len(&a) == checkpoint_device_state_len(&b));
    }
}

/// 適合する VM で復号に成功すると、保存元のヘッダー、入力と状態が戻る。
pub proof fn checkpoint_file_roundtrip(
    source: &ClockedVm,
    target: &ClockedVm,
    inputs: Seq<Range<usize>>,
    outputs: Seq<Range<usize>>,
    header: CheckpointHeader,
    input: Seq<bool>,
    file: Seq<u8>,
    decoded: &DecodedCheckpoint,
)
    requires
        source.valid(),
        target.valid(),
        checkpoint_vms_compatible(source, target),
        checkpoint_file_encodes(source, inputs, outputs, header, input, file),
        checkpoint_file_decodes(target, inputs, outputs, (header.period_numerator, header.period_denominator), file, decoded),
    ensures
        decoded.header == header,
        decoded.input@ == input,
        decoded.vm.layout_matches(target),
        decoded.vm.state_matches(source),
{
    source.checkpoint_gate_width();
    target.checkpoint_gate_width();
    let count = source.storage_model().len();
    compatible_state_offsets_agree(source, target, count);
    assert(vm_checkpoint_state_len(source) == vm_checkpoint_state_len(target));
    checkpoint_headers_agree(header, decoded.header, file);
    matching_payload_recovers_vm(
        source, target, input, decoded, file.skip(checkpoint_payload_offset(source, file)),
    );
}

spec fn checkpoint_ram_bits(device: &ClockedStorage) -> Option<usize> {
    match device.memory_model() {
        Some(bits) => Some(bits.len() as usize),
        None => None,
    }
}

spec fn checkpoint_payload_valid(vm: &ClockedVm, data: Seq<u8>) -> bool {
    &&& data.len() == vm_checkpoint_state_len(vm)
    &&& payload_pair_prefix_valid(data, vm.external_count() as int,
        Some(vm.netlist_model().gates@.len() as usize))
    &&& forall|i: int| 0 <= i < vm.storage_model().len() ==> {
        let device = #[trigger] vm.storage_model()[i];
        let start = vm_payload_device_start(vm, i);
        &&& 0 <= start <= data.len()
        &&& payload_pair_prefix_valid(data.skip(start), device.output_model().len() as int,
            checkpoint_ram_bits(&device))
    }
}

proof fn encoded_vm_payload_is_valid(vm: &ClockedVm, input: Seq<bool>, data: Seq<u8>)
    requires
        vm.valid(),
        input.len() == vm.external_count(),
        vm.gate_values_model().len() == vm.netlist_model().gates@.len(),
        encoded_payload_matches(vm, input, data),
        vm_payload_head_len(vm) <= data.len(),
    ensures checkpoint_payload_valid(vm, data),
{
    encoded_pair_has_valid_prefix(input, Some(vm.gate_values_model()), data, vm_payload_head_len(vm));
    assert forall|i: int| 0 <= i < vm.storage_model().len() implies {
        let device = #[trigger] vm.storage_model()[i];
        let start = vm_payload_device_start(vm, i);
        &&& 0 <= start <= data.len()
        &&& payload_pair_prefix_valid(data.skip(start), device.output_model().len() as int,
            checkpoint_ram_bits(&device))
    } by {
        let device = vm.storage_model()[i];
        let start = vm_payload_device_start(vm, i);
        let end = vm_payload_device_start(vm, i + 1);
        assert(data.subrange(start, end) =~= data.skip(start).take(end - start));
        encoded_pair_has_valid_prefix(device.output_model(), device.memory_model(),
            data.skip(start), end - start);
    }
}

proof fn matching_payload_recovers_vm(
    source: &ClockedVm,
    target: &ClockedVm,
    input: Seq<bool>,
    decoded: &DecodedCheckpoint,
    bytes: Seq<u8>,
)
    requires
        source.valid(),
        target.valid(),
        checkpoint_vms_compatible(source, target),
        encoded_payload_matches(source, input, bytes),
        decoded_payload_matches(target, decoded.input@, decoded.vm.gates@, decoded.vm.storage@, bytes),
        decoded.input@.len() == input.len(),
        decoded.vm.state_shape_matches(target),
        source.gate_values_model().len() == target.gate_values_model().len(),
    ensures decoded.input@ == input, decoded.vm.state_matches(source),
{
    payload_pair_is_injective(
        input, decoded.input@, Some(source.gate_values_model()), Some(decoded.vm.gates@),
        bytes.take(vm_payload_head_len(source)),
    );
    assert forall|i: int| 0 <= i < decoded.vm.storage@.len() implies
        (#[trigger] decoded.vm.storage@[i]).values_match(&source.storage_model()[i]) by {
        let saved = decoded.vm.storage@[i];
        let device = source.storage_model()[i];
        let target_device = target.storage_model()[i];
        assert(saved.shape_matches(&target_device));
        assert(match (device.memory_model(), target_device.memory_model()) {
            (Some(first), Some(second)) => first.len() == second.len(),
            (None, None) => true,
            _ => false,
        });
        compatible_state_offsets_agree(source, target, i as nat);
        compatible_state_offsets_agree(source, target, (i + 1) as nat);
        payload_pair_is_injective(
            device.output_model(), saved.output@, device.memory_model(), saved.memory_model(),
            bytes.subrange(vm_payload_device_start(source, i), vm_payload_device_start(source, i + 1)),
        );
    }
}

fn encode_checkpoint_payload(vm: &ClockedVm, input: &[bool], size: usize)
    -> (result: FileResult<Vec<u8>>)
    requires vm.valid(), input@.len() == vm.external_count(),
    ensures
        result matches Ok(bytes) ==> encoded_payload_matches(vm, input@, bytes@)
            && checkpoint_payload_valid(vm, bytes@),
        result.is_err() ==> result == Err(VmCheckpointFileError::Allocation),
{
    let mut bytes = Vec::new();
    if bytes.try_reserve_exact(size).is_err() {
        return Err(VmCheckpointFileError::Allocation);
    }
    let gates = vm.checkpoint_gate_values();
    append_payload_pair(&mut bytes, input, Some(gates))?;
    let ghost head = bytes@;
    proof {
        assert(head.len() == vm_payload_head_len(vm));
        assert(head.skip(0) =~= head);
        assert(vm_payload_device_start(vm, 0) == vm_payload_head_len(vm)) by {
            reveal(checkpoint_storage_state_len);
        }
    }
    let count = vm.storage_count();
    let mut index = 0;
    while index < count
        invariant
            vm.valid(),
            count == vm.storage_model().len(),
            index <= count,
            bytes@.len() == vm_payload_device_start(vm, index as int),
            bytes@.take(vm_payload_head_len(vm)) == head,
            0 <= vm_payload_head_len(vm) <= bytes@.len(),
            forall|j: int| 0 <= j < index ==> {
                let device = #[trigger] vm.storage_model()[j];
                let start = vm_payload_device_start(vm, j);
                let end = vm_payload_device_start(vm, j + 1);
                &&& 0 <= start <= end <= bytes@.len()
                &&& payload_pair(device.output_model(), device.memory_model(), bytes@.subrange(start, end))
            },
        decreases count - index,
    {
        let registered = vm.checkpoint_storage_output(index).ok_or(VmCheckpointFileError::PortLayout)?;
        let memory = vm.ram_memory(index);
        let ghost before = bytes@;
        append_payload_pair(&mut bytes, registered, memory)?;
        proof {
            let device = vm.storage_model()[index as int];
            let start = vm_payload_device_start(vm, index as int);
            let end = vm_payload_device_start(vm, index as int + 1);
            checkpoint_storage_state_len_push(vm.storage_model(), index as nat);
            assert(before.len() == start);
            assert(bytes@.len() == end);
            assert(bytes@.subrange(start, end) =~= bytes@.skip(start));
            preserved_segment(before, bytes@, 0, vm_payload_head_len(vm));
            assert forall|j: int| 0 <= j <= index implies {
                let device = #[trigger] vm.storage_model()[j];
                let first = vm_payload_device_start(vm, j);
                let last = vm_payload_device_start(vm, j + 1);
                &&& 0 <= first <= last <= bytes@.len()
                &&& payload_pair(device.output_model(), device.memory_model(), bytes@.subrange(first, last))
            } by {
                if j < index {
                    preserved_segment(before, bytes@,
                        vm_payload_device_start(vm, j), vm_payload_device_start(vm, j + 1));
                } else {
                    assert(vm.storage_model()[j] == device);
                }
            }
        }
        index += 1;
    }
    assert(bytes@.len() == vm_checkpoint_state_len(vm));
    assert(encoded_payload_matches(vm, input@, bytes@));
    proof { encoded_vm_payload_is_valid(vm, input@, bytes@); }
    Ok(bytes)
}

fn decode_checkpoint_payload(
    bytes: &[u8],
    vm: &ClockedVm,
    header: CheckpointHeader,
) -> (result: FileResult<DecodedCheckpoint>)
    requires vm.valid(),
    ensures
        result matches Ok(decoded) ==> {
            &&& decoded.header == header
            &&& decoded.input@.len() == vm.external_count()
            &&& decoded.vm.layout_matches(vm)
            &&& decoded.vm.state_shape_matches(vm)
            &&& decoded_payload_matches(vm, decoded.input@, decoded.vm.gates@, decoded.vm.storage@, bytes@)
        },
        checkpoint_payload_valid(vm, bytes@) ==>
            result.is_ok() || result == Err(VmCheckpointFileError::Allocation),
{
    let mut state = bytes;
    let netlist = vm.netlist();
    let (input, gates) = read_payload_pair(
        &mut state, vm.external_input_count(), Some(vm.checkpoint_gate_values().len()),
    )?;
    let gates = gates.ok_or(VmCheckpointFileError::MalformedState)?;
    proof {
        assert(vm_payload_device_start(vm, 0) == vm_payload_head_len(vm)) by {
            reveal(checkpoint_storage_state_len);
        }
    }
    let count = vm.storage_count();
    let mut storage: Vec<ClockedStorageCheckpoint> = Vec::new();
    if storage.try_reserve_exact(count).is_err() {
        return Err(VmCheckpointFileError::Allocation);
    }
    let mut index = 0;
    while index < count
        invariant
            vm.valid(),
            count == vm.storage_model().len(),
            index <= count,
            storage@.len() == index,
            0 <= vm_payload_device_start(vm, index as int) <= bytes@.len(),
            state@ == bytes@.skip(vm_payload_device_start(vm, index as int)),
            forall|j: int| 0 <= j < index ==> {
                let saved = #[trigger] storage@[j];
                let device = vm.storage_model()[j];
                let start = vm_payload_device_start(vm, j);
                let end = vm_payload_device_start(vm, j + 1);
                &&& saved.shape_matches(&device)
                &&& same_ordered_storage_wiring(&saved.wiring, &device.wiring_model())
                &&& 0 <= start <= end <= bytes@.len()
                &&& payload_pair(saved.output@, saved.memory_model(), bytes@.subrange(start, end))
            },
        decreases count - index,
    {
        let (wiring, _) = vm.storage_wiring(index).ok_or(VmCheckpointFileError::PortLayout)?;
        let registered = vm.checkpoint_storage_output(index).ok_or(VmCheckpointFileError::PortLayout)?;
        let memory_bits = match vm.ram_memory(index) {
            Some(memory) => Some(memory.len()),
            None => None,
        };
        let ghost start = vm_payload_device_start(vm, index as int);
        let ghost next = vm_payload_device_start(vm, index as int + 1);
        let ghost remaining = state@;
        proof {
            let device = vm.storage_model()[index as int];
            assert(memory_bits == checkpoint_ram_bits(&device));
            if checkpoint_payload_valid(vm, bytes@) {
                assert(payload_pair_prefix_valid(remaining, registered@.len() as int, memory_bits));
            }
        }
        let (output, memory) = read_payload_pair(&mut state, registered.len(), memory_bits)?;
        proof {
            let device = vm.storage_model()[index as int];
            checkpoint_storage_state_len_push(vm.storage_model(), index as nat);
            match (device.memory_model(), memory_bits) {
                (Some(bits), Some(count)) => assert(bits.len() == count),
                (None, None) => {},
                _ => assert(false),
            }
            assert(0 <= start <= next <= bytes@.len());
            assert(bytes@.subrange(start, next) =~= remaining.take(next - start));
            assert(bytes@.skip(next) =~= remaining.skip(next - start));
        }
        let address = match &wiring.address {
            Some(address) => Some(copy(address.as_slice())?),
            None => None,
        };
        let saved = ClockedStorageCheckpoint {
            wiring: ClockedStorageInputs {
                address,
                data: copy(wiring.data.as_slice())?,
                enable: wiring.enable,
            },
            output,
            memory,
        };
        assert(same_ordered_storage_wiring(&saved.wiring, wiring));
        assert(saved.shape_matches(&vm.storage_model()[index as int]));
        storage.push(saved);
        index += 1;
    }
    proof {
        if checkpoint_payload_valid(vm, bytes@) {
            assert(vm_payload_device_start(vm, count as int) == bytes@.len());
            assert(state@.len() == 0);
        }
    }
    if !state.is_empty() {
        return Err(VmCheckpointFileError::MalformedState);
    }
    assert(vm_payload_device_start(vm, count as int) == vm_checkpoint_state_len(vm));
    assert(bytes@.len() == vm_checkpoint_state_len(vm));
    let snapshot = ClockedVmCheckpoint {
        external: vm.external_input_count(),
        netlist: NorNetlist {
            input_count: netlist.input_count,
            gates: copy(netlist.gates.as_slice())?,
            outputs: copy(netlist.outputs.as_slice())?,
        },
        gates,
        storage,
    };
    assert(same_ordered_netlist(&snapshot.netlist, netlist));
    Ok(DecodedCheckpoint { header, input, vm: snapshot })
}



/// 復元先と一致するファイルを、VM を変更せずに復号する。
///
/// 周期を省略した構成では、期待する分子と分母に0を渡す。
///
/// # Errors
///
/// ヘッダー、周期、端子区画、ファイル長、配線表、状態部の順に検査する。
/// 有効なファイルでも、復号に必要な領域を確保できない場合は割り当てエラーを返す。
pub fn decode_vm_checkpoint(
    file: &[u8],
    vm: &ClockedVm,
    inputs: &[Range<usize>],
    outputs: &[Range<usize>],
    period: (u64, u64),
) -> (result: FileResult<DecodedCheckpoint>)
    requires vm.valid(),
    ensures
        result matches Ok(decoded) ==> {
            &&& checkpoint_file_decodes(vm, inputs@, outputs@, period, file@, &decoded)
            &&& decoded.input@.len() == vm.external_count()
            &&& decoded.vm.layout_matches(vm)
            &&& decoded.vm.state_shape_matches(vm)
        },
        checkpoint_file_admissible(vm, inputs@, outputs@, period, file@) && result.is_err()
            ==> result == Err(VmCheckpointFileError::Allocation),
{
    let ghost admissible = checkpoint_file_admissible(vm, inputs@, outputs@, period, file@);
    let header = match read_checkpoint_header(file) {
        Ok(header) => header,
        Err(error) => {
            assert(!admissible) by { reveal(checkpoint_file_admissible); }
            return Err(VmCheckpointFileError::File(error));
        },
    };
    assert(admissible ==> {
        &&& (header.period_numerator, header.period_denominator) == period
        &&& checkpoint_ports_valid(inputs@, vm.external_count() as int)
        &&& checkpoint_ports_valid(outputs@, vm.netlist_model().outputs@.len() as int)
        &&& file@.len() == CHECKPOINT_HEADER_BYTES + checkpoint_wiring_table_len(vm, inputs@, outputs@)
            + vm_checkpoint_state_len(vm)
    }) by {
        if admissible {
            reveal(checkpoint_file_admissible);
            let expected = choose|saved: CheckpointHeader| #[trigger] checkpoint_header_matches(file@, saved)
                && (saved.period_numerator, saved.period_denominator) == period;
            checkpoint_headers_agree(header, expected, file@);
            let offset = checkpoint_payload_offset(vm, file@);
            let table = file@.subrange(CHECKPOINT_HEADER_BYTES as int, offset);
            canonical_checkpoint_ports_valid(vm, inputs@, outputs@, table);
            canonical_checkpoint_layout_len(vm, inputs@, outputs@, table);
        }
    }
    if (header.period_numerator, header.period_denominator) != period {
        return Err(VmCheckpointFileError::PeriodMismatch);
    }
    if file.len() != checkpoint_file_len(vm, inputs, outputs)? {
        return Err(VmCheckpointFileError::File(CheckpointFileError::Length));
    }
    let (layout, size) = layout(vm, inputs, outputs)?;
    assert(admissible ==> {
        &&& file@.len() == CHECKPOINT_HEADER_BYTES + layout@.len() + size
        &&& file@.subrange(CHECKPOINT_HEADER_BYTES as int, CHECKPOINT_HEADER_BYTES + layout@.len()) == layout@
        &&& checkpoint_payload_valid(vm, file@.skip(CHECKPOINT_HEADER_BYTES + layout@.len()))
    }) by {
        if admissible {
            reveal(checkpoint_file_admissible);
            let offset = checkpoint_payload_offset(vm, file@);
            let table = file@.subrange(CHECKPOINT_HEADER_BYTES as int, offset);
            assert(checkpoint_vms_compatible(vm, vm));
            canonical_vm_layout_agrees(vm, vm, inputs@, outputs@, table, layout@);
        }
    }
    let state = match checkpoint_state(file, &layout, size) {
        Ok(state) => state,
        Err(error) => return Err(VmCheckpointFileError::File(error)),
    };
    let decoded = decode_checkpoint_payload(state, vm, header)?;
    assert(checkpoint_file_decodes(vm, inputs@, outputs@, period, file@, &decoded));
    Ok(decoded)
}

} // verus!
