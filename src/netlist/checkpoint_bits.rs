//! スナップショットのビット列を、各バイトの下位ビットから順に格納する。

use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 保存データの形式またはメモリの確保に関するエラー。
pub enum CheckpointBitError {
    /// バイト数、ビット数または末尾の未使用ビットが規定外である。
    Malformed,
    /// ビット列またはバイト列の領域を確保できない。
    Allocation,
}

/// 各ビットを順に格納し、最後のバイトに残った領域を0にする。
pub open spec fn packed_checkpoint_bits(bits: Seq<bool>, bytes: Seq<u8>) -> bool {
    &&& bytes.len() == (bits.len() + 7) / 8
    &&& forall|i: int| 0 <= i < bits.len() ==>
        #[trigger] byte_bit(bytes[i / 8], (i % 8) as u8) == bits[i]
    &&& forall|i: int| bits.len() <= i < bytes.len() * 8 ==>
        !(#[trigger] byte_bit(bytes[i / 8], (i % 8) as u8))
}

/// 同じバイト列から同じ長さに復号した結果は一意である。
pub proof fn checkpoint_bits_roundtrip(original: Seq<bool>, decoded: Seq<bool>, bytes: Seq<u8>)
    requires
        packed_checkpoint_bits(original, bytes),
        packed_checkpoint_bits(decoded, bytes),
        original.len() == decoded.len(),
    ensures decoded == original,
{
    assert forall|i: int| 0 <= i < original.len() implies decoded[i] == original[i] by {
        assert(byte_bit(bytes[i / 8], (i % 8) as u8) == original[i]);
    }
    assert(decoded =~= original);
}

/// 1バイト中の指定位置のビット。
pub open spec fn byte_bit(byte: u8, bit: u8) -> bool {
    ((byte >> bit) & 1u8) == 1u8
}

fn set_bit(byte: u8, index: u8, value: bool) -> (result: u8)
    requires index < 8,
    ensures
        byte_bit(result, index) == value,
        forall|other: u8| other < 8 && other != index ==>
            #[trigger] byte_bit(result, other) == byte_bit(byte, other),
{
    let result = if value { byte | (1u8 << index) } else { byte & !(1u8 << index) };
    proof {
        assert(byte_bit(result, index) == value) by (bit_vector)
            requires index < 8, result == if value { (byte | (1u8 << index)) } else { (byte & !(1u8 << index)) };
        assert forall|other: u8| other < 8 && other != index implies
            #[trigger] byte_bit(result, other) == byte_bit(byte, other) by {
            assert(byte_bit(result, other) == byte_bit(byte, other)) by (bit_vector)
                requires index < 8, other < 8, other != index,
                    result == if value { (byte | (1u8 << index)) } else { (byte & !(1u8 << index)) };
        }
    }
    result
}

fn read_bit(byte: u8, bit: u8) -> (value: bool)
    requires bit < 8,
    ensures value == byte_bit(byte, bit),
{
    ((byte >> bit) & 1) == 1
}

proof fn zero_byte_has_no_bits()
    ensures forall|j: u8| j < 8 ==> !(#[trigger] byte_bit(0, j)),
{
    assert forall|j: u8| j < 8 implies !(#[trigger] byte_bit(0, j)) by {
        assert(!byte_bit(0, j)) by (bit_vector);
    }
}

/// 先頭のビットを先頭バイトのビット0に詰め、末尾の未使用ビットを0にする。
///
/// # Errors
///
/// バイト列の領域を確保できない場合にエラーを返す。
pub fn pack_checkpoint_bits(bits: &[bool]) -> (result: Result<Vec<u8>, CheckpointBitError>)
    ensures match result {
        Ok(bytes) => bits@.len() <= isize::MAX && packed_checkpoint_bits(bits@, bytes@),
        Err(e) => e is Allocation,
    },
{
    if bits.len() > isize::MAX as usize {
        return Err(CheckpointBitError::Allocation);
    }
    let mut bytes = Vec::new();
    let size = bits.len() / 8 + if bits.len() % 8 == 0 { 0 } else { 1 };
    if bytes.try_reserve_exact(size).is_err() {
        return Err(CheckpointBitError::Allocation);
    }
    let mut packed: u8 = 0;
    let mut i: usize = 0;
    proof { zero_byte_has_no_bits(); }
    while i < bits.len()
        invariant
            i <= bits@.len(),
            bytes@.len() == i / 8,
            forall|j: int| 0 <= j < bytes@.len() * 8 ==>
                #[trigger] byte_bit(bytes@[j / 8], (j % 8) as u8) == bits@[j],
            forall|j: int| bytes@.len() * 8 <= j < i ==>
                #[trigger] byte_bit(packed, (j % 8) as u8) == bits@[j],
            forall|j: u8| i % 8 <= j < 8 ==> !(#[trigger] byte_bit(packed, j)),
        decreases bits.len() - i,
    {
        packed = set_bit(packed, (i % 8) as u8, bits[i]);
        i += 1;
        if i % 8 == 0 {
            bytes.push(packed);
            packed = 0;
            proof { zero_byte_has_no_bits(); }
        }
    }
    if i % 8 != 0 {
        bytes.push(packed);
    }
    Ok(bytes)
}

/// 状態の一区画が規定の長さと末尾ビットを持つことを表す。
pub open spec fn checkpoint_segment_valid(bytes: Seq<u8>, bit_count: int) -> bool {
    &&& 0 <= bit_count <= isize::MAX
    &&& bytes.len() == (bit_count + 7) / 8
    &&& forall|i: int| bit_count <= i < bytes.len() * 8 ==>
        !(#[trigger] byte_bit(bytes[i / 8], (i % 8) as u8))
}

/// 期待した長さで、使わない上位ビットが0の場合にだけビット列へ戻す。
///
/// # Errors
///
/// 長さや末尾のビットが規定外の場合や、ビット列の領域を確保できない場合にエラーを返す。
pub fn unpack_checkpoint_bits(bytes: &[u8], bit_count: usize)
    -> (result: Result<Vec<bool>, CheckpointBitError>)
    ensures
        (result matches Err(CheckpointBitError::Malformed)) <==>
            !checkpoint_segment_valid(bytes@, bit_count as int),
        result matches Ok(data) ==> data@.len() == bit_count && packed_checkpoint_bits(data@, bytes@),
{
    if bit_count > isize::MAX as usize {
        return Err(CheckpointBitError::Malformed);
    }
    let full = bit_count / 8;
    let used = (bit_count % 8) as u8;
    if bytes.len() != full + if used == 0 { 0 } else { 1 } {
        return Err(CheckpointBitError::Malformed);
    }
    if used != 0 {
        let mut tail = used;
        while tail < 8
            invariant
                0 < used <= tail <= 8,
                used == bit_count % 8,
                full == bit_count / 8,
                bytes@.len() == full + 1,
                forall|j: u8| used <= j < tail ==> !(#[trigger] byte_bit(bytes@[full as int], j)),
            decreases 8 - tail,
        {
            if read_bit(bytes[full], tail) {
                proof {
                    let i = full as int * 8 + tail as int;
                    assert(bit_count <= i < bytes@.len() * 8);
                    assert(byte_bit(bytes@[i / 8], (i % 8) as u8));
                }
                return Err(CheckpointBitError::Malformed);
            }
            tail += 1;
        }
        assert forall|i: int| bit_count <= i < bytes@.len() * 8 implies
            !(#[trigger] byte_bit(bytes@[i / 8], (i % 8) as u8)) by {
            assert(i / 8 == full);
        }
    }
    let mut data = Vec::new();
    if data.try_reserve_exact(bit_count).is_err() {
        return Err(CheckpointBitError::Allocation);
    }
    let mut i = 0;
    while i < bit_count
        invariant
            i == data@.len() <= bit_count,
            bytes@.len() == (bit_count as int + 7) / 8,
            forall|j: int| 0 <= j < i ==>
                #[trigger] byte_bit(bytes@[j / 8], (j % 8) as u8) == data@[j],
        decreases bit_count - i,
    {
        data.push(read_bit(bytes[i / 8], (i % 8) as u8));
        i += 1;
    }
    Ok(data)
}

} // verus!
