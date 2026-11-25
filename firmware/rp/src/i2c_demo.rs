//! LM75B の設定レジスタを読み、回路を通したシャットダウンビットを GPIO で観測する。

#![no_std]
#![no_main]

mod i2c_transport;

use circuitgame2_device_timing::{
    FixedReceiveError, FixedRequestLedger, HostRequestId, HostResponseError, I2cTransfer,
    RequestKey, TickPosition, i2c_port_bit,
};
use circuitgame2_packed_nor::{PackedClockedNorPlan32, PackedNorGate32, read_lane32};
use embassy_executor::Spawner;
use embassy_rp::{
    bind_interrupts,
    gpio::{Level, Output},
    i2c::{Async, Config, I2c, InterruptHandler},
    peripherals::I2C0,
};
use embassy_sync::{blocking_mutex::raw::CriticalSectionRawMutex, channel::Channel};
use embassy_time::{Duration, Instant, Timer};
use i2c_transport::{Completion, Controller, Readback, TransferFailure};
use panic_halt as _;

bind_interrupts!(struct I2cIrqs {
    I2C0_IRQ => InterruptHandler<I2C0>;
});

const CAPACITY: usize = 1;
const REQUEST_KEY: RequestKey = RequestKey {
    instance: 0,
    tag: 0,
};
const PERIOD: Duration = Duration::from_millis(1);
const REQUEST_INTERVAL: u64 = 250;

type Response = Result<Readback<CAPACITY>, TransferFailure>;
type Mutex = CriticalSectionRawMutex;
static REQUESTS: Channel<Mutex, (HostRequestId, I2cTransfer<CAPACITY>), 1> = Channel::new();
static COMPLETIONS: Channel<Mutex, Completion<CAPACITY>, 1> = Channel::new();

#[embassy_executor::task]
async fn worker(bus: I2c<'static, I2C0, Async>) {
    let mut controller = Controller::new(bus, Duration::from_millis(20));
    loop {
        let (id, request) = REQUESTS.receive().await;
        COMPLETIONS
            .send(controller.execute(id, &request).await)
            .await;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_rp::init(Default::default());
    let mut fault = Output::new(p.PIN_3, Level::Low);
    let mut tick = Output::new(p.PIN_4, Level::Low);
    let mut shutdown = Output::new(p.PIN_5, Level::Low);

    let mut config = Config::default();
    config.frequency = 100_000;
    config.sda_pullup = false;
    config.scl_pullup = false;
    let bus = I2c::new_async(p.I2C0, p.PIN_1, p.PIN_0, I2cIrqs, config);
    if let Ok(task) = worker(bus) {
        spawner.spawn(task);
        let _ = run(&mut fault, &mut tick, &mut shutdown).await;
    }
    fault.set_high();
    // 異常終了後も端子の所有権を保持し、観測できるようにする。
    core::future::pending::<()>().await;
}

async fn run(
    fault: &mut Output<'_>,
    tick: &mut Output<'_>,
    shutdown: &mut Output<'_>,
) -> Option<()> {
    // 入力は読み出しの周期外、通信中または異常、設定のシャットダウンビットの順。
    // 公開出力は要求、設定ビット、0x48 のアドレス、0x01 のポインターを並べる。
    const LOW: usize = 4;
    const HIGH: usize = 5;
    const PORTS: [usize; 17] = [
        3, 2, LOW, LOW, LOW, HIGH, LOW, LOW, HIGH, HIGH, LOW, LOW, LOW, LOW, LOW, LOW, LOW,
    ];
    let plan =
        PackedClockedNorPlan32::new(3, &[PackedNorGate32 { left: 0, right: 1 }], &PORTS).ok()?;
    let mut ledger = FixedRequestLedger::<Response, 1>::new();
    let mut awaiting = None;
    let mut failed = false;
    let mut shutdown_bit = false;
    let reset_source = [0, 0, 0, 0, 0, u32::MAX];
    let mut committed_ports = PORTS.map(|wire| reset_source[wire]);
    let mut deadline = Instant::now().checked_add(PERIOD)?;
    loop {
        let next_deadline = deadline.checked_add(PERIOD)?;
        Timer::at(deadline).await;
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
            match response {
                Ok(read) => shutdown_bit = i2c_port_bit(read.bytes().first().copied()?, 0)?,
                Err(_) => failed = true,
            }
        }

        let blocked = failed || awaiting.is_some() || REQUESTS.is_full();
        // デバイスは前の tick で確定した要求ポートを読む。
        let outgoing = if !blocked && read_lane32(committed_ports[0], 0)? {
            let address = core::array::from_fn(|bit| committed_ports[2 + bit] & 1 != 0);
            let pointer = core::array::from_fn(|bit| committed_ports[9 + bit] & 1 != 0);
            Some(I2cTransfer::from_port_bits(&address, &[pointer], 1, 1).ok()?)
        } else {
            None
        };
        let mut source = [
            u32::from(target.tick % REQUEST_INTERVAL != 0),
            u32::from(blocked),
            u32::from(shutdown_bit),
            0,
            0,
            u32::MAX,
        ];
        let mut observed = [0; PORTS.len()];
        plan.step(&mut source, &mut [0], &mut observed).ok()?;
        let next_shutdown = read_lane32(observed[1], 0)?;
        let delivered_ids = delivered.map(|(id, _)| id);
        let keys = outgoing.map(|_| REQUEST_KEY);
        let pending = ledger
            .prepare_tick(delivered_ids.as_slice(), keys.as_slice())
            .ok()?;
        if Instant::now() >= next_deadline {
            return None;
        }
        let committed = pending.commit();
        committed_ports = observed;
        if delivered_ids.is_some() {
            awaiting = None;
        }
        if let Some(transfer) = outgoing {
            let id = committed.id_at(0)?;
            // tick の唯一の生産側。空きを確認してからここまで通信タスクへ実行を渡さない。
            REQUESTS.try_send((id, transfer)).ok()?;
            awaiting = Some(id);
        }
        if failed {
            fault.set_high();
        }
        shutdown.set_level(if next_shutdown {
            Level::High
        } else {
            Level::Low
        });
        tick.toggle();
        deadline = next_deadline;
    }
}
