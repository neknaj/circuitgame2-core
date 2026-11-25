//! 回路ポートの下位ビットから、I²C のアドレスと送信バイトを取り出す。

#[cfg(not(verus_only))]
use verus_builtin_macros::verus;
#[cfg(verus_only)]
use vstd::prelude::*;

use super::{I2cTransfer, I2cTransferError};
#[cfg(verus_only)]
use super::i2c_transfer_error;

verus! {

broadcast use vstd::array::group_array_axioms;

/// ポートを、先頭が最下位ビットとなる順序で並べたときのバイト。
pub open spec fn i2c_octet_matches(bits: Seq<bool>, byte: u8) -> bool {
    &&& bits.len() <= 8
    &&& forall|bit: u32| bit < 8 ==> #[trigger] i2c_octet_bit(byte, bit)
        == if bit < bits.len() { bits[bit as int] } else { false }
}

/// 最下位から数えたバイトのビット値。
pub open spec fn i2c_octet_bit(byte: u8, bit: u32) -> bool {
    (byte >> bit) & 1 == 1
}

/// 応答の1バイトを回路へ渡すとき、最下位を0としてビットを取り出す。
///
/// 8以上の位置には `None` を返す。
pub fn i2c_port_bit(byte: u8, bit: u32) -> (result: Option<bool>)
    ensures result == if bit < 8 { Some(i2c_octet_bit(byte, bit)) } else { None },
{
    if bit < 8 { Some((byte >> bit) & 1 == 1) } else { None }
}

fn pack<const BITS: usize>(bits: &[bool; BITS]) -> (result: u8)
    requires BITS <= 8,
    ensures
        i2c_octet_matches(bits@, result),
        BITS <= 7 ==> result < 128u8,
{
    let mut byte = 0u8;
    let mut bit = 0u32;
    assert forall|i: u32| i < 8 implies !#[trigger] i2c_octet_bit(0, i) by {
        assert((0u8 >> i) & 1u8 == 0u8) by (bit_vector);
    };
    while (bit as usize) < BITS
        invariant
            BITS <= 8,
            bit <= BITS,
            bits@.len() == BITS,
            forall|i: u32| i < 8 ==> #[trigger] i2c_octet_bit(byte, i)
                == if i < bit { bits@[i as int] } else { false },
        decreases BITS - bit,
    {
        let level = bits[bit as usize];
        let next = byte | ((if level { 1u8 } else { 0u8 }) << bit);
        assert forall|i: u32| i < 8 implies #[trigger] i2c_octet_bit(next, i)
            == if i == bit { level || i2c_octet_bit(byte, i) } else { i2c_octet_bit(byte, i) }
        by {
            assert(i < 8 && bit < 8 ==> {
                let next = byte | ((if level { 1u8 } else { 0u8 }) << bit);
                (((next >> i) & 1u8) == 1u8) ==
                    (if i == bit { level || ((byte >> i) & 1u8) == 1u8 }
                     else { ((byte >> i) & 1u8) == 1u8 })
            }) by (bit_vector);
        };
        byte = next;
        bit += 1;
    }
    assert(BITS <= 7 ==> byte < 128u8) by {
        if BITS <= 7 {
            assert(!i2c_octet_bit(byte, 7u32));
            assert((byte >> 7u32) & 1u8 == 0u8) by (bit_vector)
                requires !((byte >> 7u32) & 1u8 == 1u8);
            assert(byte < 128u8) by (bit_vector) requires (byte >> 7u32) & 1u8 == 0u8;
        }
    };
    byte
}

/// 回路のアドレスと送信バイトが、下位ビットから順に並んだ配線に対応する。
pub open spec fn i2c_port_bytes_match<const N: usize>(
    address: Seq<bool>, data: Seq<[bool; 8]>, decoded: u8, bytes: [u8; N],
) -> bool {
    &&& address.len() == 7
    &&& i2c_octet_matches(address, decoded)
    &&& data.len() == N
    &&& forall|i: int| 0 <= i < N ==> i2c_octet_matches(#[trigger] data[i]@, bytes@[i])
}

impl<const N: usize> I2cTransfer<N> {
    /// 最下位ビットから並べた回路ポートの値を、I²C の取引に変換する。
    ///
    /// データは送信するバイトの順に並べ、各バイトの中では最下位ビットを先頭にする。
    /// 長さが0の側は省略する。両方を指定すると、書き込みと読み出しを反復 START でつなぐ。
    ///
    /// # Errors
    ///
    /// 書き込み長、読み出し長、空の取引の順で最初の違反を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_device_timing::{I2cTransfer, I2cTransferKind};
    ///
    /// let address = [false, false, false, true, false, false, true];
    /// let register = [true, false, false, false, false, false, false, false];
    /// let transfer = I2cTransfer::from_port_bits(&address, &[register], 1, 1)?;
    /// assert_eq!(transfer.parts(), (0x48, &[0x01], 1, 1, I2cTransferKind::WriteRead));
    /// # Ok::<(), circuitgame2_device_timing::I2cTransferError>(())
    /// ```
    pub fn from_port_bits(
        address: &[bool; 7], data: &[[bool; 8]; N], write_len: usize, read_len: usize,
    ) -> (result: Result<Self, I2cTransferError>)
        ensures
            result.is_ok() <==> i2c_transfer_error(0, write_len, read_len, N).is_none(),
            result matches Err(error) ==> i2c_transfer_error(0, write_len, read_len, N) == Some(error),
            result matches Ok(transfer) ==> {
                let (decoded, bytes, written, read) = transfer.model();
                &&& i2c_port_bytes_match(address@, data@, decoded, bytes)
                &&& written == write_len && read == read_len
            },
    {
        let decoded = pack(address);
        let mut bytes = [0u8; N];
        let mut i = 0;
        while i < N
            invariant
                i <= N,
                data@.len() == N,
                bytes@.len() == N,
                forall|j: int| 0 <= j < i ==> i2c_octet_matches(#[trigger] data@[j]@, bytes@[j]),
            decreases N - i,
        {
            bytes[i] = pack(&data[i]);
            i += 1;
        }
        Self::new(decoded, bytes, write_len, read_len)
    }
}

} // verus!
