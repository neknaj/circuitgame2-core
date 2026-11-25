//! RP の SPI を、取引全体の GPIO チップ選択と DMA で進める。

use circuitgame2_device_timing::{HostRequestId, SpiBitOrder, SpiTransfer};
use embassy_rp::{
    gpio::Output,
    spi::{Async, Instance, Spi},
};
use embassy_time::{Duration, Timer, with_timeout};

/// SPI の応答を取得できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TransferFailure {
    /// 指定した時間内にバスが転送を完了しなかった。
    Timeout,
    /// SPI ドライバーがエラーを返した。
    Driver,
    /// 先行取引の異常後にコントローラーの再初期化が必要。
    Unavailable,
}

/// 台帳に照合する元の要求と、回路順の全二重受信領域。
pub(super) struct Completion<const N: usize> {
    /// 送信した要求の世代、インスタンス、連番。
    pub(super) id: HostRequestId,
    /// SPI が正常に終われば受信したバイト。転送長より後ろは0。
    pub(super) result: Result<[u8; N], TransferFailure>,
}

/// GPIO の active-low CS を保持し、完了や中断で解放する。
struct Selection<'a, 'd>(&'a mut Output<'d>);

impl<'a, 'd> Selection<'a, 'd> {
    fn new(pin: &'a mut Output<'d>) -> Self {
        pin.set_low();
        Self(pin)
    }
}

impl Drop for Selection<'_, '_> {
    fn drop(&mut self) {
        self.0.set_high();
    }
}

/// SPI ドライバーを一つ所有し、確定した要求を直列に処理する。
pub(super) struct Controller<'d, T: Instance> {
    spi: Spi<'d, T, Async>,
    select: Output<'d>,
    order: SpiBitOrder,
    timeout: Duration,
    busy: fn() -> bool,
    available: bool,
}

impl<'d, T: Instance> Controller<'d, T> {
    /// DMA 初期化済みの SPI と、非選択が High の GPIO を受け取る。
    ///
    /// `busy` は同じ SPI のステータスを読む関数。
    pub(super) fn new(
        spi: Spi<'d, T, Async>,
        select: Output<'d>,
        order: SpiBitOrder,
        timeout: Duration,
        busy: fn() -> bool,
    ) -> Self {
        Self {
            spi,
            select,
            order,
            timeout,
            busy,
            available: true,
        }
    }

    /// 台帳が確定した要求を、送信と同じバイト数の受信とともに実行する。
    ///
    /// 要求 ID は変更しない。結果を tick に渡す前に、呼び出し側で ID と世代を照合する。
    pub(super) async fn execute<const N: usize>(
        &mut self,
        id: HostRequestId,
        transfer: &SpiTransfer<N>,
    ) -> Completion<N> {
        Completion {
            id,
            result: self.transfer(transfer).await,
        }
    }

    async fn transfer<const N: usize>(
        &mut self,
        transfer: &SpiTransfer<N>,
    ) -> Result<[u8; N], TransferFailure> {
        if !self.available {
            return Err(TransferFailure::Unavailable);
        }
        let (write, len) = transfer.wire_parts(self.order);
        let mut read = [0; N];
        // DMA の中断は SPI の FIFO を初期化しない。完了を確認した取引の後だけ次を受け付ける。
        self.available = false;
        {
            let _selected = Selection::new(&mut self.select);
            with_timeout(self.timeout, async {
                self.spi.transfer(&mut read[..len], &write[..len]).await?;
                // 最後のクロックが終わるまで CS を保持し、tick タスクに実行機会を渡す。
                while (self.busy)() {
                    Timer::after_micros(1).await;
                }
                Ok::<(), embassy_rp::spi::Error>(())
            })
            .await
            .map_err(|_| TransferFailure::Timeout)?
            .map_err(|_| TransferFailure::Driver)?;
        }
        self.available = true;
        Ok(transfer.readback(self.order, &read))
    }
}
