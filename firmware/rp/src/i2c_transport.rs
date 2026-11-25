//! Embassy の I²C コントローラーで、tick が確定した取引を処理する。

#[cfg(rp_i2c_program)]
use circuitgame2_device_timing::I2cTransferError;
use circuitgame2_device_timing::{HostRequestId, I2cTransfer, I2cTransferKind};
use embassy_rp::{
    i2c::{AbortReason, Async, Error, I2c, Instance},
    pac::i2c::regs::IcTxAbrtSource,
};
use embassy_time::{Duration, with_timeout};

/// I²C コントローラーが要求を完了できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TransferFailure {
    /// 回路から渡された送受信長では取引を開始できない。
    #[cfg(rp_i2c_program)]
    InvalidRequest(I2cTransferError),
    /// 対象アドレスに応答がなかった。
    AddressNack,
    /// 送信したデータバイトに応答がなかった。
    DataNack,
    /// バス調停で負けた。
    ArbitrationLost,
    /// コントローラーが取引を完了できなかった。
    Bus,
    /// 指定した待ち時間内に取引が完了しなかった。
    Timeout,
    /// 先行する取引が中断され、バスを再初期化する必要がある。
    Unavailable,
}

/// 読み出したバイト列。書き込みのみの場合は空になる。
#[derive(Clone, Copy)]
pub(crate) struct Readback<const N: usize> {
    bytes: [u8; N],
    len: usize,
}

impl<const N: usize> Readback<N> {
    /// 要求に応じて読み出した部分を返す。
    pub(crate) fn bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

/// 台帳と照合する元の要求 ID と、コントローラーの処理結果。
pub(crate) struct Completion<const N: usize> {
    pub(crate) id: HostRequestId,
    pub(crate) result: Result<Readback<N>, TransferFailure>,
}

/// 一つのコントローラーを所有し、取引を直列に処理する。
pub(crate) struct Controller<'d, T: Instance> {
    bus: I2c<'d, T, Async>,
    timeout: Duration,
    available: bool,
}

impl<'d, T: Instance> Controller<'d, T> {
    /// 初期化済みのコントローラーに、一つの取引に許す待ち時間を設定する。
    pub(crate) fn new(bus: I2c<'d, T, Async>, timeout: Duration) -> Self {
        Self {
            bus,
            timeout,
            available: true,
        }
    }

    /// 台帳が確定した要求を通信タスクで処理する。
    ///
    /// 呼び出しの打ち切り、タイムアウト、通信エラーの後は、
    /// コントローラーを再初期化するまで後続の取引を開始しない。
    /// 呼び出し側は完了の要求 ID と reset 世代を照合してから tick に渡す。
    pub(crate) async fn execute<const N: usize>(
        &mut self,
        id: HostRequestId,
        transfer: &I2cTransfer<N>,
    ) -> Completion<N> {
        Completion {
            id,
            result: self.transfer(transfer).await,
        }
    }

    async fn transfer<const N: usize>(
        &mut self,
        transfer: &I2cTransfer<N>,
    ) -> Result<Readback<N>, TransferFailure> {
        if !self.available {
            return Err(TransferFailure::Unavailable);
        }
        let (address, write, write_len, read_len, kind) = transfer.parts();
        let write = &write[..write_len];
        let mut bytes = [0; N];
        let read = &mut bytes[..read_len];

        // Embassy 0.10 は Future を破棄した場合にバスの停止を保証しない。
        // FIFO 排出中の異常は STOP の確認前に返る場合もあるため、成功したときだけ通信を再開する。
        self.available = false;
        let result = with_timeout(self.timeout, async {
            match kind {
                I2cTransferKind::Read => self.bus.read_async(address, read).await,
                I2cTransferKind::Write => {
                    self.bus.write_async(address, write.iter().copied()).await
                }
                I2cTransferKind::WriteRead => {
                    self.bus
                        .write_read_async(address, write.iter().copied(), read)
                        .await
                }
            }
        })
        .await
        .map_err(|_| TransferFailure::Timeout)?;

        result.map_err(failure)?;
        self.available = true;
        Ok(Readback {
            bytes,
            len: read_len,
        })
    }
}

fn failure(error: Error) -> TransferFailure {
    match error {
        Error::Abort(AbortReason::NoAcknowledge) => TransferFailure::AddressNack,
        Error::Abort(AbortReason::Other(raw)) if IcTxAbrtSource(raw).abrt_txdata_noack() => {
            TransferFailure::DataNack
        }
        Error::Abort(AbortReason::ArbitrationLoss) => TransferFailure::ArbitrationLost,
        _ => TransferFailure::Bus,
    }
}
