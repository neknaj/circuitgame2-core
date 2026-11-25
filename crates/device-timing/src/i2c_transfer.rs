//! 固定容量のホスト要求で I²C コントローラーに渡すアドレスとバイト数を検査する。

#[cfg(not(verus_only))]
use verus_builtin_macros::verus;
#[cfg(verus_only)]
use vstd::prelude::*;

verus! {

/// I²C コントローラーに渡す取引の形。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum I2cTransferKind {
    /// 指定されたバイト数だけ読み出す。
    Read,
    /// 送信領域の先頭から指定されたバイト数を書き込む。
    Write,
    /// 書き込みと読み出しの間に反復 START を送る。
    WriteRead,
}

/// I²C の取引を作れない最初の理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum I2cTransferError {
    /// アドレスが7ビットで表せない。
    Address,
    /// 書き込みバイト数が送信領域を超えている。
    WriteLength,
    /// 読み出しバイト数が受信領域を超えている。
    ReadLength,
    /// 書き込みと読み出しの両方が0バイトである。
    Empty,
}

/// I²C の取引のアドレス、送信領域、送受信バイト数。
///
/// 送信領域のうち取引に含まれるのは、先頭の `write_len` バイト。
/// 同じ容量 `N` の受信領域をホストが使う。
#[derive(Clone, Copy)]
pub struct I2cTransfer<const N: usize> {
    address: u8,
    write: [u8; N],
    write_len: usize,
    read_len: usize,
}

/// アドレス、送信容量、受信容量、空の取引の順で最初の違反を選ぶ。
pub open spec fn i2c_transfer_error(
    address: u8, write_len: usize, read_len: usize, capacity: usize,
) -> Option<I2cTransferError> {
    if address as int >= 128 { Some(I2cTransferError::Address) }
    else if write_len > capacity { Some(I2cTransferError::WriteLength) }
    else if read_len > capacity { Some(I2cTransferError::ReadLength) }
    else if write_len == 0 && read_len == 0 { Some(I2cTransferError::Empty) }
    else { None }
}

/// 書き込みと読み出しを両方指定した取引は、反復 START でつなぐ。
pub open spec fn i2c_transfer_kind(write_len: usize, read_len: usize) -> I2cTransferKind {
    if write_len == 0 { I2cTransferKind::Read }
    else if read_len == 0 { I2cTransferKind::Write }
    else { I2cTransferKind::WriteRead }
}

impl<const N: usize> I2cTransfer<N> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        i2c_transfer_error(self.address, self.write_len, self.read_len, N).is_none()
    }

    /// ホストが使うアドレス、送信領域、書き込み長、読み出し長。
    pub closed spec fn model(&self) -> (u8, [u8; N], usize, usize) {
        (self.address, self.write, self.write_len, self.read_len)
    }

    /// 7ビットアドレスで、両方の長さが容量内にある取引を作る。
    ///
    /// 長さが0の側は省略する。送信領域の余ったバイトは通信に使わない。
    ///
    /// # Errors
    ///
    /// アドレス、書き込み長、読み出し長、空の取引の順で最初の違反を返す。
    pub fn new(
        address: u8, write: [u8; N], write_len: usize, read_len: usize,
    ) -> (result: Result<Self, I2cTransferError>)
        ensures
            result.is_ok() <==> i2c_transfer_error(address, write_len, read_len, N).is_none(),
            result matches Ok(transfer) ==> transfer.model() == (address, write, write_len, read_len),
            result matches Err(error) ==> i2c_transfer_error(address, write_len, read_len, N) == Some(error),
    {
        if address >= 128 { return Err(I2cTransferError::Address); }
        if write_len > N { return Err(I2cTransferError::WriteLength); }
        if read_len > N { return Err(I2cTransferError::ReadLength); }
        if write_len == 0 && read_len == 0 { return Err(I2cTransferError::Empty); }
        Ok(Self { address, write, write_len, read_len })
    }

    /// アドレス、送信領域、書き込み長、読み出し長、取引の形を返す。
    ///
    /// 両方の長さは容量以下で、少なくとも一方は正である。
    pub fn parts(&self) -> (parts: (u8, &[u8; N], usize, usize, I2cTransferKind))
        ensures
            (parts.0, *parts.1, parts.2, parts.3) == self.model(),
            i2c_transfer_error(parts.0, parts.2, parts.3, N).is_none(),
            parts.4 == i2c_transfer_kind(parts.2, parts.3),
    {
        proof { use_type_invariant(self); }
        let kind = if self.write_len == 0 {
            I2cTransferKind::Read
        } else if self.read_len == 0 {
            I2cTransferKind::Write
        } else {
            I2cTransferKind::WriteRead
        };
        (self.address, &self.write, self.write_len, self.read_len, kind)
    }
}

/// 単独の読み書きと、反復 START を使う書き込み後の読み出しを区別する。
proof fn i2c_transfer_examples() {
    assert(i2c_transfer_error(0x38, 0, 2, 2) is None) by (compute);
    assert(i2c_transfer_kind(0, 2) is Read) by (compute);
    assert(i2c_transfer_kind(2, 0) is Write) by (compute);
    assert(i2c_transfer_kind(1, 2) is WriteRead) by (compute);
    assert(i2c_transfer_error(0x80, 3, 3, 2) == Some(I2cTransferError::Address)) by (compute);
    assert(i2c_transfer_error(0x38, 0, 0, 2) == Some(I2cTransferError::Empty)) by (compute);
}

} // verus!
