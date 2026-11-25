//! 固定長の SPI 折り返しを繰り返し、回路の tick と DMA を独立して進める。

#![no_std]
#![no_main]

mod spi_transport;

use circuitgame2_device_timing::{
    FixedReceiveError, FixedRequestLedger, HostRequestId, HostResponseError, RequestKey,
    SpiBitOrder, SpiTransfer, TickPosition,
};
use circuitgame2_packed_nor::{PackedClockedNorPlan32, PackedNorGate32, read_lane32};
use embassy_executor::Spawner;
use embassy_rp::{
    bind_interrupts,
    dma::InterruptHandler,
    gpio::{Level, Output},
    peripherals::{DMA_CH0, DMA_CH1, SPI0},
    spi::{Config, Phase, Polarity, Spi},
};
use embassy_sync::{blocking_mutex::raw::CriticalSectionRawMutex, channel::Channel};
use embassy_time::{Duration, Instant, Timer};
use panic_halt as _;
use spi_transport::{Completion, Controller, TransferFailure};

bind_interrupts!(struct SpiIrqs {
    DMA_IRQ_0 => InterruptHandler<DMA_CH0>, InterruptHandler<DMA_CH1>;
});

const CAPACITY: usize = 3;
const REQUEST_KEY: RequestKey = RequestKey {
    instance: 0,
    tag: 0,
};
const PERIOD: Duration = Duration::from_millis(1);
const REQUEST_INTERVAL: u64 = 250;
const WRITE: [u8; CAPACITY] = [0x12, 0x80, 0xff];
const EXPECTED: [u8; CAPACITY] = [0x12, 0x80, 0];

type Request = SpiTransfer<CAPACITY>;
type Response = Result<[u8; CAPACITY], TransferFailure>;
type Mutex = CriticalSectionRawMutex;
static REQUESTS: Channel<Mutex, (HostRequestId, Request), 1> = Channel::new();
static COMPLETIONS: Channel<Mutex, Completion<CAPACITY>, 1> = Channel::new();

#[embassy_executor::task]
async fn worker(mut controller: Controller<'static, SPI0>) {
    loop {
        let (id, request) = REQUESTS.receive().await;
        controller
            .execute(id, &request, async |completion| {
                COMPLETIONS.send(completion).await
            })
            .await;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let pins = embassy_rp::init(Default::default());
    let mut fault = Output::new(pins.PIN_6, Level::Low);
    let mut tick = Output::new(pins.PIN_7, Level::Low);
    let mut received = Output::new(pins.PIN_8, Level::Low);
    let select = Output::new(pins.PIN_5, Level::High);

    let mut config = Config::default();
    config.frequency = 1_000_000;
    config.polarity = Polarity::IdleHigh;
    config.phase = Phase::CaptureOnSecondTransition;
    let spi = Spi::new(
        pins.SPI0,
        pins.PIN_2,
        pins.PIN_3,
        pins.PIN_4,
        pins.DMA_CH0,
        pins.DMA_CH1,
        SpiIrqs,
        config,
    );
    let controller = Controller::new(
        spi,
        select,
        SpiBitOrder::LeastSignificantFirst,
        Duration::from_millis(20),
        || embassy_rp::pac::SPI0.sr().read().bsy(),
    );
    if let Ok(task) = worker(controller) {
        spawner.spawn(task);
        let _ = run(&mut fault, &mut tick, &mut received).await;
    }
    fault.set_high();
    // 異常停止後に診断を読めるよう、端子の所有権を保持する。
    core::future::pending::<()>().await;
}

async fn run(
    fault: &mut Output<'_>,
    tick: &mut Output<'_>,
    received: &mut Output<'_>,
) -> Option<()> {
    let transfer = SpiTransfer::new(WRITE, 2).ok()?;
    // 次の要求は送受信が空いている場合にだけ立て、受信結果をそのまま端子へ出す。
    let plan =
        PackedClockedNorPlan32::new(3, &[PackedNorGate32 { left: 0, right: 1 }], &[3, 2]).ok()?;
    let mut ledger = FixedRequestLedger::<Response, 1>::new();
    let mut awaiting = None;
    let mut failed = false;
    let mut read_ok = false;
    let mut valid = false;
    let mut deadline = Instant::now().checked_add(PERIOD)?;
    loop {
        let following = deadline.checked_add(PERIOD)?;
        Timer::at(deadline).await;
        if Instant::now() >= following {
            return None;
        }
        let current = ledger.position();
        let target = TickPosition {
            tick: current.tick.checked_add(1)?,
            ..current
        };
        if let Ok(completed) = COMPLETIONS.try_receive() {
            match ledger.receive(completed.id, target, completed.result) {
                Ok(())
                | Err(FixedReceiveError::Response(HostResponseError::DifferentGeneration)) => {}
                Err(_) => return None,
            }
        }
        let delivered = awaiting.and_then(|id| {
            ledger
                .peek_at(id, target)
                .map(|(_, response)| (id, response))
        });
        if let Some((_, response)) = delivered {
            read_ok = response == Ok(EXPECTED);
            failed |= !read_ok;
        }
        let blocked = failed || awaiting.is_some() || REQUESTS.is_full();
        let issue = valid && !blocked;
        let mut source = [
            u32::from(target.tick % REQUEST_INTERVAL != 0),
            u32::from(blocked),
            u32::from(read_ok),
            0,
            0,
            u32::MAX,
        ];
        let mut observed = [0; 2];
        plan.step(&mut source, &mut [0], &mut observed).ok()?;
        let keys = issue.then_some(REQUEST_KEY);
        let deliveries = delivered.map(|(id, _)| id);
        let pending = ledger
            .prepare_tick(deliveries.as_slice(), keys.as_slice())
            .ok()?;
        if Instant::now() >= following {
            return None;
        }
        let committed = pending.commit();
        valid = read_lane32(observed[0], 0)?;
        if deliveries.is_some() {
            awaiting = None;
        }
        if issue {
            let id = committed.id_at(0)?;
            // tick からだけ要求を入れる。空きの確認と送信の間に await はない。
            REQUESTS.try_send((id, transfer)).ok()?;
            awaiting = Some(id);
        }
        if failed {
            fault.set_high();
        }
        received.set_level(if read_lane32(observed[1], 0)? {
            Level::High
        } else {
            Level::Low
        });
        tick.toggle();
        deadline = following;
    }
}
