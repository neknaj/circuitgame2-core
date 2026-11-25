//! SPI の全二重転送で使う固定長バッファーと、線上のビット順を扱う。

#[cfg(not(verus_only))]
use verus_builtin_macros::verus;
#[cfg(verus_only)]
use vstd::prelude::*;

verus! {

broadcast use vstd::array::group_array_axioms;

/// 各バイトを SPI の線上で送受信する順序。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpiBitOrder {
    /// 最上位ビットを先頭にする。
    MostSignificantFirst,
    /// 最下位ビットを先頭にする。
    LeastSignificantFirst,
}

/// SPI の転送長が仕様に合わない理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpiTransferError {
    /// 指定した長さが0バイト。
    Empty,
    /// 指定した長さが送受信バッファーの容量を超える。
    Capacity,
}

/// SPI コントローラーで同数のバイトを同時に送受信する要求。
///
/// `N` は送信と受信それぞれの容量。転送長は1バイトから `N` バイトまで。
#[derive(Clone, Copy)]
pub struct SpiTransfer<const N: usize> {
    write: [u8; N],
    len: usize,
}

/// 転送長が不足しているか、容量を超えているかを区別する。
pub open spec fn spi_transfer_error(len: usize, capacity: usize) -> Option<SpiTransferError> {
    if len == 0 { Some(SpiTransferError::Empty) }
    else if len > capacity { Some(SpiTransferError::Capacity) }
    else { None }
}

/// 最下位から `bit` 桁目の値。
pub open spec fn spi_byte_bit(byte: u8, bit: u32) -> bool {
    (byte >> bit) & 1 == 1
}

/// 指定した送受信順が、PL022 の MSB-first 用のバイトと対応することを表す。
///
/// `position` は線上に現れる順で数える。同じ関係を送信と受信の両方に用いる。
pub open spec fn spi_wire_byte_matches(logical: u8, wire: u8, order: SpiBitOrder) -> bool {
    forall|position: u32| position < 8 ==> #[trigger] spi_byte_bit(wire, sub(7, position))
        == match order {
            SpiBitOrder::MostSignificantFirst => spi_byte_bit(logical, sub(7, position)),
            SpiBitOrder::LeastSignificantFirst => spi_byte_bit(logical, position),
        }
}

proof fn reversed_bits_match(byte: u8, wire: u8, bit: u32)
    requires
        bit < 8,
        wire == {
            let halves = (byte << 4) | (byte >> 4);
            let pairs = ((halves & 0x33) << 2) | ((halves & 0xcc) >> 2);
            ((pairs & 0x55) << 1) | ((pairs & 0xaa) >> 1)
        },
    ensures
        spi_byte_bit(wire, sub(7, bit)) == spi_byte_bit(byte, bit),
        spi_byte_bit(wire, bit) == spi_byte_bit(byte, sub(7, bit)),
{
    assert(bit < 8 ==> {
        let halves = (byte << 4) | (byte >> 4);
        let pairs = ((halves & 0x33) << 2) | ((halves & 0xcc) >> 2);
        let reversed = ((pairs & 0x55) << 1) | ((pairs & 0xaa) >> 1);
        &&& (((reversed >> sub(7, bit)) & 1) == ((byte >> bit) & 1))
        &&& (((reversed >> bit) & 1) == ((byte >> sub(7, bit)) & 1))
    }) by (bit_vector);
}

fn spi_wire_octet(byte: u8, order: SpiBitOrder) -> (result: u8)
    ensures
        spi_wire_byte_matches(byte, result, order),
        spi_wire_byte_matches(result, byte, order),
{
    let result = match order {
        SpiBitOrder::MostSignificantFirst => byte,
        SpiBitOrder::LeastSignificantFirst => {
            // PL022 のバイト内の順序は固定なので、LSB-first では両方向とも鏡映する。
            let halves = (byte << 4) | (byte >> 4);
            let pairs = ((halves & 0x33) << 2) | ((halves & 0xcc) >> 2);
            let bits = ((pairs & 0x55) << 1) | ((pairs & 0xaa) >> 1);
            assert forall|p: u32| p < 8 implies
                #[trigger] spi_byte_bit(bits, sub(7, p)) == spi_byte_bit(byte, p) by {
                reversed_bits_match(byte, bits, p);
            };
            assert forall|p: u32| p < 8 implies
                #[trigger] spi_byte_bit(byte, sub(7, p)) == spi_byte_bit(bits, p) by {
                reversed_bits_match(byte, bits, p);
            };
            bits
        },
    };
    result
}

fn spi_wire_buffer<const N: usize>(
    source: &[u8; N], len: usize, order: SpiBitOrder,
) -> (result: [u8; N])
    requires len <= N,
    ensures forall|i: int| 0 <= i < N ==>
        if i < len {
            spi_wire_byte_matches(source@[i], #[trigger] result@[i], order)
                && spi_wire_byte_matches(result@[i], source@[i], order)
        } else { result@[i] == 0 },
{
    let mut dest = [0; N];
    let mut i = 0;
    while i < len
        invariant
            i <= len <= N,
            source@.len() == N,
            dest@.len() == N,
            forall|j: int| 0 <= j < N ==>
                if j < i {
                    spi_wire_byte_matches(source@[j], #[trigger] dest@[j], order)
                        && spi_wire_byte_matches(dest@[j], source@[j], order)
                } else { dest@[j] == 0 },
        decreases len - i,
    {
        dest[i] = spi_wire_octet(source[i], order);
        i += 1;
    }
    dest
}

impl<const N: usize> SpiTransfer<N> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        spi_transfer_error(self.len, N).is_none()
    }

    /// 論理順の送信バイトと、送受信に共通の長さ。
    pub closed spec fn model(&self) -> ([u8; N], usize) {
        (self.write, self.len)
    }

    /// 送信領域の先頭から `len` バイトを全二重で転送する要求を作る。
    ///
    /// # Errors
    ///
    /// `len` が0、または容量 `N` を超えている場合はそれぞれの理由を返す。
    pub fn new(write: [u8; N], len: usize) -> (result: Result<Self, SpiTransferError>)
        ensures
            result.is_ok() <==> spi_transfer_error(len, N).is_none(),
            result matches Ok(transfer) ==> transfer.model() == (write, len),
            result matches Err(error) ==> spi_transfer_error(len, N) == Some(error),
    {
        if len == 0 { return Err(SpiTransferError::Empty); }
        if len > N { return Err(SpiTransferError::Capacity); }
        Ok(Self { write, len })
    }

    /// PL022 に渡す送信バッファーと、DMA の送受信に共通の長さを返す。
    ///
    /// 長さより後ろの領域は0。バイト自体の順序は保つ。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_device_timing::{SpiBitOrder, SpiTransfer, SpiTransferError};
    ///
    /// let transfer = SpiTransfer::new([0x12, 0x80, 0xff], 2)?;
    /// let (sent, len) = transfer.wire_parts(SpiBitOrder::LeastSignificantFirst);
    /// assert_eq!((sent, len), ([0x48, 0x01, 0], 2));
    /// let received = transfer.readback(SpiBitOrder::LeastSignificantFirst, &sent);
    /// assert_eq!(received, [0x12, 0x80, 0]);
    /// # Ok::<(), SpiTransferError>(())
    /// ```
    pub fn wire_parts(&self, order: SpiBitOrder) -> (parts: ([u8; N], usize))
        ensures
            parts.1 == self.model().1,
            0 < parts.1 <= N,
            forall|i: int| 0 <= i < N ==>
                if i < parts.1 {
                    spi_wire_byte_matches(self.model().0@[i], #[trigger] parts.0@[i], order)
                } else { parts.0@[i] == 0 },
    {
        proof { use_type_invariant(self); }
        (spi_wire_buffer(&self.write, self.len, order), self.len)
    }

    /// 転送で受信したバイトを回路の論理ビット順に戻す。
    ///
    /// 受信バッファーの先頭から要求の長さ分を使い、残りは0にする。
    pub fn readback(&self, order: SpiBitOrder, wire: &[u8; N]) -> (result: [u8; N])
        ensures forall|i: int| 0 <= i < N ==>
            if i < self.model().1 {
                spi_wire_byte_matches(#[trigger] result@[i], wire@[i], order)
            } else { result@[i] == 0 },
    {
        proof { use_type_invariant(self); }
        spi_wire_buffer(wire, self.len, order)
    }
}

proof fn spi_transfer_examples() {
    assert(spi_transfer_error(0, 0) == Some(SpiTransferError::Empty)) by (compute);
    assert(spi_transfer_error(1, 0) == Some(SpiTransferError::Capacity)) by (compute);
    assert(spi_transfer_error(1, 1) is None) by (compute);
    assert(spi_transfer_error(255, 255) is None) by (compute);
    assert(spi_transfer_error(256, 255) == Some(SpiTransferError::Capacity)) by (compute);
}

} // verus!
