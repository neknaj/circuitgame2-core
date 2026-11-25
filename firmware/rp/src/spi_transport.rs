//! RP の SPI を、取引全体の GPIO チップ選択と DMA で進める。

use core::pin::pin;

use circuitgame2_device_timing::{HostRequestId, SpiBitOrder, SpiTransfer};
use embassy_futures::select::{Either, select};
use embassy_rp::{
    gpio::Output,
    spi::{Async, Instance, Spi},
};
use embassy_time::{Duration, Instant, Timer};

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
    /// 要求 ID は変更しない。呼び出し元の常駐タスクが実行を所有し、
    /// 期限超過後も開始済みの DMA の終了を待つ。
    pub(super) async fn execute<const N: usize>(
        &mut self,
        id: HostRequestId,
        transfer: &SpiTransfer<N>,
        publish: impl AsyncFnOnce(Completion<N>),
    ) {
        let complete = async move |result| publish(Completion { id, result }).await;
        if !self.available {
            complete(Err(TransferFailure::Unavailable)).await;
            return;
        }
        // 完了を期限内に確認できた取引の後だけ、コントローラーを再利用する。
        self.available = false;
        let Some(deadline) = Instant::now().checked_add(self.timeout) else {
            complete(Err(TransferFailure::Timeout)).await;
            return;
        };
        let (write, len) = transfer.wire_parts(self.order);
        let mut read = [0; N];
        if Instant::now() >= deadline {
            complete(Err(TransferFailure::Timeout)).await;
            return;
        }
        let result = {
            let selected = Selection::new(&mut self.select);
            let mut io = pin!(async {
                // 期限切れの要求で DMA を開始しない。期限到達後に最初の poll が来る場合もある。
                if Instant::now() >= deadline {
                    return Err(TransferFailure::Timeout);
                }
                self.spi
                    .transfer(&mut read[..len], &write[..len])
                    .await
                    .map_err(|_| TransferFailure::Driver)?;
                // 最後のクロックが終わるまで CS を保持し、tick タスクに実行機会を渡す。
                while (self.busy)() {
                    Timer::after_micros(1).await;
                }
                Ok(())
            });
            // select に借用だけを渡す。RP2350-E5 により、動作中の DMA を
            // Embassy 0.10 の Drop で中断する方法には依存できない。
            let completed = select(Timer::at(deadline), io.as_mut()).await;
            drop(selected);
            match completed {
                Either::First(()) => {
                    complete(Err(TransferFailure::Timeout)).await;
                    // CS は解放済み。DMA とバッファーを保持し、終了まで新規取引を受け付けない。
                    let _ = io.await;
                    return;
                }
                Either::Second(result) if Instant::now() < deadline => result,
                Either::Second(_) => Err(TransferFailure::Timeout),
            }
        };
        let result = result.map(|()| {
            self.available = true;
            transfer.readback(self.order, &read)
        });
        complete(result).await;
    }
}
