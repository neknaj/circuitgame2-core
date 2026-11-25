//! SPI の配線表を、通信タスクと回路の tick に接続する。

use core::sync::atomic::{AtomicBool, Ordering};

use circuitgame2_device_timing::{
    HostRequestId, SpiBitOrder, SpiTransfer, SpiTransferError, i2c_port_bit as port_bit,
    i2c_port_octet as port_octet,
};
use embassy_rp::{
    Peri, bind_interrupts,
    dma::InterruptHandler,
    gpio::Output,
    peripherals::{DMA_CH0, DMA_CH1},
    spi::{ClkPin, Config, Instance, MisoPin, MosiPin, Phase, Polarity, Spi},
};
#[cfg(rp_spi_controller = "0")]
use embassy_rp::{pac::SPI0 as STATUS_REGISTERS, peripherals::SPI0 as Bus};
#[cfg(rp_spi_controller = "1")]
use embassy_rp::{pac::SPI1 as STATUS_REGISTERS, peripherals::SPI1 as Bus};
use embassy_sync::{blocking_mutex::raw::CriticalSectionRawMutex, channel::Channel};

use super::{
    Duration, SPI_CAPACITY, SPI_INPUTS, SPI_INSTANCE, SPI_OUTPUTS, Spawner,
    peripheral_program::{self, Protocol},
    spi_transport::{Controller, TransferFailure},
};

bind_interrupts!(struct SpiIrqs {
    DMA_IRQ_0 => InterruptHandler<DMA_CH0>, InterruptHandler<DMA_CH1>;
});

type Transfer = SpiTransfer<SPI_CAPACITY>;
type Request = Result<Transfer, SpiTransferError>;
type Response = Result<[u8; SPI_CAPACITY], Failure>;
type Mutex = CriticalSectionRawMutex;
type Dma = (Peri<'static, DMA_CH0>, Peri<'static, DMA_CH1>);

#[derive(Clone, Copy)]
enum Failure {
    InvalidLength,
    Transport(TransferFailure),
}

static REQUESTS: Channel<Mutex, (HostRequestId, Request), 1> = Channel::new();
static COMPLETIONS: Channel<Mutex, (HostRequestId, Response), 1> = Channel::new();
static UNAVAILABLE: AtomicBool = AtomicBool::new(false);

/// 検査済みの配線表が指定する、SPI の通信条件。
pub(super) struct Settings {
    /// 周波数の要求値。ヘルツで指定する。
    pub(super) frequency_hz: u32,
    /// クロックの極性と位相を組み合わせたモード。
    pub(super) mode: u8,
    /// 線上で最下位ビットから転送するか。
    pub(super) least_significant_first: bool,
    /// 1回の転送の期限。マイクロ秒で指定する。
    pub(super) timeout_micros: u32,
}

impl Settings {
    fn config(&self) -> Config {
        let mut config = Config::default();
        config.frequency = self.frequency_hz;
        config.polarity = if self.mode & 2 == 0 {
            Polarity::IdleLow
        } else {
            Polarity::IdleHigh
        };
        config.phase = if self.mode & 1 == 0 {
            Phase::CaptureOnFirstTransition
        } else {
            Phase::CaptureOnSecondTransition
        };
        config
    }

    fn controller<T: Instance>(
        &self,
        spi: Spi<'static, T, embassy_rp::spi::Async>,
        cs: Output<'static>,
        busy: fn() -> bool,
    ) -> Controller<'static, T> {
        let order = if self.least_significant_first {
            SpiBitOrder::LeastSignificantFirst
        } else {
            SpiBitOrder::MostSignificantFirst
        };
        Controller::new(
            spi,
            cs,
            order,
            Duration::from_micros(self.timeout_micros.into()),
            busy,
        )
    }
}

/// 選んだ SPI のピンを設定し、専用 DMA チャネルで転送するタスクを起動する。
pub(super) fn start(
    spawner: Spawner,
    device: Peri<'static, Bus>,
    pins: (
        Peri<'static, impl ClkPin<Bus>>,
        Peri<'static, impl MosiPin<Bus>>,
        Peri<'static, impl MisoPin<Bus>>,
    ),
    dma: Dma,
    cs: Output<'static>,
    settings: Settings,
) -> Option<()> {
    let spi = Spi::new(
        device,
        pins.0,
        pins.1,
        pins.2,
        dma.0,
        dma.1,
        SpiIrqs,
        settings.config(),
    );
    let controller = settings.controller(spi, cs, || STATUS_REGISTERS.sr().read().bsy());
    spawner.spawn(run_worker(controller).ok()?);
    Some(())
}

#[embassy_executor::task]
async fn run_worker(mut controller: Controller<'static, Bus>) {
    loop {
        let (id, request) = REQUESTS.receive().await;
        match request {
            Ok(transfer) => {
                controller
                    .execute(id, &transfer, async |completion| {
                        // タイムアウト応答は DMA の終了より先に届くことがある。
                        // 再初期化までは、後続の要求をキューに入れない。
                        if completion.result.is_err() {
                            UNAVAILABLE.store(true, Ordering::Relaxed);
                        }
                        COMPLETIONS
                            .send((completion.id, completion.result.map_err(Failure::Transport)))
                            .await;
                    })
                    .await
            }
            Err(_) => COMPLETIONS.send((id, Err(Failure::InvalidLength))).await,
        }
    }
}

fn status(response: &Response) -> u8 {
    match response {
        Ok(_) => 0,
        Err(Failure::InvalidLength) => 1,
        Err(Failure::Transport(TransferFailure::Driver)) => 5,
        Err(Failure::Transport(TransferFailure::Timeout)) => 6,
        Err(Failure::Transport(TransferFailure::Unavailable)) => 7,
    }
}

struct SpiProtocol;

impl Protocol for SpiProtocol {
    type Request = Request;
    type Response = Response;
    const INSTANCE: usize = SPI_INSTANCE as usize;
    const INPUTS: &'static [Option<usize>] = &SPI_INPUTS;
    const OUTPUTS: &'static [usize] = &SPI_OUTPUTS;

    fn requests() -> &'static Channel<Mutex, (HostRequestId, Request), 1> {
        &REQUESTS
    }
    fn completions() -> &'static Channel<Mutex, (HostRequestId, Response), 1> {
        &COMPLETIONS
    }
    fn available() -> bool {
        !UNAVAILABLE.load(Ordering::Relaxed)
    }

    fn request(port: impl Fn(usize) -> bool) -> Request {
        let len = port_octet(&core::array::from_fn(|bit| port(2 + bit)));
        let bytes = core::array::from_fn(|byte| {
            port_octet(&core::array::from_fn(|bit| port(10 + byte * 8 + bit)))
        });
        Transfer::new(bytes, usize::from(len))
    }

    fn input(signal: usize, ready: bool, response: Option<&Response>) -> Option<bool> {
        match signal {
            0 => Some(ready),
            1 => Some(response.is_some()),
            2..=4 => port_bit(response.map_or(0, status), (signal - 2) as u32),
            _ => {
                let bit = signal - 5;
                let byte = response
                    .and_then(|response| response.as_ref().ok())
                    .and_then(|bytes| bytes.get(bit / 8))
                    .copied()
                    .unwrap_or(0);
                port_bit(byte, (bit % 8) as u32)
            }
        }
    }
}

/// SPI と GPIO を初期化し、配線表の tick を進める。
pub(super) async fn run(spawner: Spawner) -> Option<()> {
    peripheral_program::run::<SpiProtocol>(spawner).await
}
