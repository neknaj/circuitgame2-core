//! 配線の種類と参照先を固定幅で保存する。

use alloc::vec::Vec;
use crate::netlist::Wire;
use super::checkpoint_format::{append_bytes, write_word, CheckpointFileError};
#[cfg(verus_only)]
use super::checkpoint_format::word_at;
use vstd::prelude::*;

verus! {

/// 定数、外部または登録入力、NOR 出力は異なるタグを使う。
pub open spec fn wire_layout_record(wire: Wire, bytes: Seq<u8>) -> bool {
    &&& bytes.len() == 9
    &&& match wire {
        Wire::Constant(false) => bytes[0] == 0 && word_at(bytes, 1) == 0,
        Wire::Constant(true) => bytes[0] == 1 && word_at(bytes, 1) == 0,
        Wire::Input(index) => bytes[0] == 2 && word_at(bytes, 1) == index as u64,
        Wire::Gate(index) => bytes[0] == 3 && word_at(bytes, 1) == index as u64,
    }
}

/// 配線表の9バイトが同じなら配線元も同じになる。
pub proof fn wire_layout_record_is_injective(first: Wire, second: Wire, bytes: Seq<u8>)
    requires wire_layout_record(first, bytes), wire_layout_record(second, bytes),
    ensures first == second,
{
}

/// 配線の種類を1バイト、参照先を8バイトで出力する。
pub fn write_wire_layout(wire: Wire) -> (encoded: [u8; 9])
    ensures wire_layout_record(wire, encoded@),
{
    let (tag, index) = match wire {
        Wire::Constant(false) => (0u8, 0u64),
        Wire::Constant(true) => (1u8, 0u64),
        Wire::Input(index) => (2u8, index as u64),
        Wire::Gate(index) => (3u8, index as u64),
    };
    let bytes = write_word(index);
    let encoded = [tag, bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7]];
    assert(word_at(encoded@, 1) == word_at(bytes@, 0));
    encoded
}

/// 配線を渡された順序で保存したバイト列を表す。
pub open spec fn ordered_wire_layout(wires: Seq<Wire>, bytes: Seq<u8>) -> bool {
    &&& bytes.len() == 9 * wires.len()
    &&& forall|i: int| 0 <= i < wires.len() ==>
        wire_layout_record(#[trigger] wires[i], bytes.subrange(9 * i, 9 * (i + 1)))
}

/// 同じ配線表から配線の本数と並びが一意に決まる。
pub proof fn ordered_wire_layout_is_injective(first: Seq<Wire>, second: Seq<Wire>, bytes: Seq<u8>)
    requires ordered_wire_layout(first, bytes), ordered_wire_layout(second, bytes),
    ensures first == second,
{
    assert forall|i: int| 0 <= i < first.len() implies first[i] == second[i] by {
        wire_layout_record_is_injective(first[i], second[i], bytes.subrange(9 * i, 9 * (i + 1)));
    }
    assert(first =~= second);
}

/// 配線を渡された順序で追加する。
///
/// # Errors
///
/// 追加先の領域が確保できない場合は元の列を保つ。
pub fn append_ordered_wire_layout(target: &mut Vec<u8>, wires: &[Wire])
    -> (result: Result<(), CheckpointFileError>)
    ensures
        result is Ok ==> final(target)@.len() == old(target)@.len() + 9 * wires@.len()
            && final(target)@.take(old(target)@.len() as int) == old(target)@
            && ordered_wire_layout(wires@, final(target)@.skip(old(target)@.len() as int)),
        result is Err ==> final(target)@ == old(target)@
            && result == Err(CheckpointFileError::Allocation),
{
    let start = target.len();
    if start > isize::MAX as usize || wires.len() > (isize::MAX as usize - start) / 9 {
        return Err(CheckpointFileError::Allocation);
    }
    if target.try_reserve_exact(wires.len() * 9).is_err() {
        return Err(CheckpointFileError::Allocation);
    }
    let mut i = 0;
    while i < wires.len()
        invariant
            start == old(target)@.len(),
            i <= wires@.len(),
            start + 9 * wires@.len() <= isize::MAX,
            target@.len() == start + 9 * i,
            target@.take(start as int) == old(target)@,
            forall|j: int| 0 <= j < i ==>
                wire_layout_record(#[trigger] wires@[j], target@.subrange(start + 9 * j, start + 9 * (j + 1))),
        decreases wires.len() - i,
    {
        let record = write_wire_layout(wires[i]);
        let ghost previous = target@;
        append_bytes(target, record.as_slice());
        assert forall|j: int| 0 <= j <= i implies wire_layout_record(
            #[trigger] wires@[j], target@.subrange(start + 9 * j, start + 9 * (j + 1))) by {
            if j < i {
                assert(target@.subrange(start + 9 * j, start + 9 * (j + 1))
                    =~= previous.subrange(start + 9 * j, start + 9 * (j + 1)));
            } else {
                assert(target@.subrange(start + 9 * j, start + 9 * (j + 1)) =~= record@);
            }
        }
        i += 1;
    }
    let ghost payload = target@.skip(start as int);
    assert forall|j: int| 0 <= j < wires@.len() implies
        wire_layout_record(#[trigger] wires@[j], payload.subrange(9 * j, 9 * (j + 1))) by {
        assert(payload.subrange(9 * j, 9 * (j + 1))
            =~= target@.subrange(start + 9 * j, start + 9 * (j + 1)));
    }
    Ok(())
}

} // verus!
