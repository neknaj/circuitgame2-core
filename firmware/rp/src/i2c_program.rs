//! 確定済みの回路出力と I²C の応答を照合し、通信タスクと tick を独立して進める。

use circuitgame2_device_timing::{
    FixedReceiveError, FixedRequestLedger, HostRequestId, HostResponseError, I2cTransfer,
    I2cTransferError, RequestKey, TickPosition, i2c_port_bit, i2c_port_octet,
};
use embassy_rp::{
    Peri, bind_interrupts,
    gpio::Output,
    i2c::{Async, Config, I2c, Instance, InterruptHandler, SclPin, SdaPin},
    peripherals::{I2C0, I2C1},
};
use embassy_sync::{blocking_mutex::raw::CriticalSectionRawMutex, channel::Channel};

use super::{
    Duration, GATES, I2C_CAPACITY, I2C_INPUTS, I2C_INSTANCE, I2C_OUTPUTS, INPUT_COUNT, Instant,
    LANE, Level, OUTPUT_PORTS, PERIOD_US, PORTS, PackedClockedNorPlan32, SOURCE_COUNT, Spawner,
    Timer, configure_gpio,
    i2c_transport::{Controller, Readback, TransferFailure},
    read_lane32, replace_lane32,
};

bind_interrupts!(struct I2cIrqs {
    I2C0_IRQ => InterruptHandler<I2C0>;
    I2C1_IRQ => InterruptHandler<I2C1>;
});

type Mutex = CriticalSectionRawMutex;
type Request = Result<I2cTransfer<I2C_CAPACITY>, I2cTransferError>;
type Response = Result<Readback<I2C_CAPACITY>, TransferFailure>;

static REQUESTS: Channel<Mutex, (HostRequestId, Request), 1> = Channel::new();
static COMPLETIONS: Channel<Mutex, (HostRequestId, Response), 1> = Channel::new();

/// 配線表で選んだ I²C0 を初期化して通信タスクを起動する。
pub(super) fn start0(
    spawner: Spawner,
    bus: Peri<'static, I2C0>,
    sda: Peri<'static, impl SdaPin<I2C0>>,
    scl: Peri<'static, impl SclPin<I2C0>>,
    rate: u32,
    timeout_micros: u32,
) -> Option<()> {
    spawner.spawn(
        worker0(
            I2c::new_async(bus, scl, sda, I2cIrqs, config(rate)),
            Duration::from_micros(timeout_micros.into()),
        )
        .ok()?,
    );
    Some(())
}

/// 配線表で選んだ I²C1 を初期化して通信タスクを起動する。
pub(super) fn start1(
    spawner: Spawner,
    bus: Peri<'static, I2C1>,
    sda: Peri<'static, impl SdaPin<I2C1>>,
    scl: Peri<'static, impl SclPin<I2C1>>,
    rate: u32,
    timeout_micros: u32,
) -> Option<()> {
    spawner.spawn(
        worker1(
            I2c::new_async(bus, scl, sda, I2cIrqs, config(rate)),
            Duration::from_micros(timeout_micros.into()),
        )
        .ok()?,
    );
    Some(())
}

fn config(rate: u32) -> Config {
    let mut config = Config::default();
    config.frequency = rate;
    config.scl_pullup = false;
    config.sda_pullup = false;
    config
}

#[embassy_executor::task]
async fn worker0(bus: I2c<'static, I2C0, Async>, timeout: Duration) {
    worker(bus, timeout).await;
}

#[embassy_executor::task]
async fn worker1(bus: I2c<'static, I2C1, Async>, timeout: Duration) {
    worker(bus, timeout).await;
}

async fn worker<T: Instance + 'static>(bus: I2c<'static, T, Async>, timeout: Duration) {
    let mut controller = Controller::new(bus, timeout);
    loop {
        let (id, request) = REQUESTS.receive().await;
        let completion = match request {
            Ok(transfer) => {
                let done = controller.execute(id, &transfer).await;
                (done.id, done.result)
            }
            // 長さ違反にも要求番号を対応付ける。通信には渡さない。
            Err(error) => (id, Err(TransferFailure::InvalidRequest(error))),
        };
        COMPLETIONS.send(completion).await;
    }
}

fn status(response: &Response) -> u8 {
    match response {
        Ok(_) => 0,
        Err(TransferFailure::InvalidRequest(_)) => 1,
        Err(TransferFailure::AddressNack) => 2,
        Err(TransferFailure::DataNack) => 3,
        Err(TransferFailure::ArbitrationLost) => 4,
        Err(TransferFailure::Bus) => 5,
        Err(TransferFailure::Timeout) => 6,
        Err(TransferFailure::Unavailable) => 7,
    }
}

fn input(signal: usize, ready: bool, response: Option<&Response>) -> Option<bool> {
    match signal {
        0 => Some(ready),
        1 => Some(response.is_some()),
        2..=4 => i2c_port_bit(response.map_or(0, status), (signal - 2) as u32),
        _ => {
            let bit = signal - 5;
            let byte = response
                .and_then(|result| result.as_ref().ok())
                .and_then(|data| data.bytes().get(bit / 8).copied())
                .unwrap_or(0);
            i2c_port_bit(byte, (bit % 8) as u32)
        }
    }
}

fn request(port: impl Fn(usize) -> bool) -> Request {
    let address = core::array::from_fn(|bit| port(bit + 2));
    let write_len = i2c_port_octet(&core::array::from_fn(|bit| port(bit + 9)));
    let read_len = i2c_port_octet(&core::array::from_fn(|bit| port(bit + 17)));
    let bytes = core::array::from_fn(|byte| core::array::from_fn(|bit| port(25 + byte * 8 + bit)));
    I2cTransfer::from_port_bits(&address, &bytes, write_len.into(), read_len.into())
}

async fn deadline_fault(fault: &mut Output<'_>) -> Option<()> {
    // Pico と Pico 2 の基板 LED で、通常の GPIO 出力とは別に停止を知らせる。
    fault.set_high();
    core::future::pending().await
}

/// 配線表から作った回路を進め、応答を回路が取り込むまで保持する。
pub(super) async fn run(spawner: Spawner) -> Option<()> {
    let plan = PackedClockedNorPlan32::new(INPUT_COUNT, &GATES, &PORTS).ok()?;
    let (inputs, mut outputs, mut fault) =
        configure_gpio(spawner, embassy_rp::init(Default::default()))?;
    let mut ledger = FixedRequestLedger::<Response, 1>::new();
    let mut awaiting = None;
    let mut held = None;
    let mut source = [0; SOURCE_COUNT];
    source[SOURCE_COUNT - 1] = u32::MAX;
    let mut observed = PORTS.map(|wire| source[wire]);
    let mut candidate_source = [0; SOURCE_COUNT];
    let mut candidate_observed = [0; PORTS.len()];
    let mut next = [0; GATES.len()];
    let Some(period) = Duration::try_from_micros(PERIOD_US) else {
        return deadline_fault(&mut fault).await;
    };
    let Some(mut deadline) = Instant::now().checked_add(period) else {
        return deadline_fault(&mut fault).await;
    };
    loop {
        let Some(following) = deadline.checked_add(period) else {
            return deadline_fault(&mut fault).await;
        };
        Timer::at(deadline).await;
        if Instant::now() >= following {
            // 候補を確定せず、GPIO を保持して最後に確定した出力を残す。
            return deadline_fault(&mut fault).await;
        }
        let current = ledger.position();
        let target = TickPosition {
            tick: current.tick.checked_add(1)?,
            ..current
        };
        if let Ok((id, response)) = COMPLETIONS.try_receive() {
            match ledger.receive(id, target, response) {
                Ok(())
                | Err(FixedReceiveError::Response(HostResponseError::DifferentGeneration)) => {}
                Err(_) => return None,
            }
        }
        let delivered =
            awaiting.and_then(|id| ledger.peek_at(id, target).map(|(_, result)| (id, result)));
        let response = held.or(delivered.map(|(_, result)| result));
        let circuit =
            |signal: usize| read_lane32(observed[I2C_OUTPUTS[signal]], LANE).unwrap_or(false);
        // 前の tick の出力と今回の入力フレームの両方から受け渡しを決める。
        let take_response = response.is_some() && circuit(1);
        let ready = awaiting.is_none() && response.is_none() && !REQUESTS.is_full();
        let outgoing = (ready && circuit(0)).then(|| request(circuit));
        let key = outgoing.as_ref().map(|_| RequestKey {
            instance: I2C_INSTANCE.into(),
            tag: 0,
        });
        let delivery = delivered.map(|(id, _)| id);
        let pending = ledger
            .prepare_tick(delivery.as_slice(), key.as_slice())
            .ok()?;

        candidate_source.copy_from_slice(&source);
        for ((wire, gpio), signal) in candidate_source[..INPUT_COUNT]
            .iter_mut()
            .zip(&inputs)
            .zip(I2C_INPUTS)
        {
            let level = match (gpio, signal) {
                (Some(gpio), None) => gpio.is_high(),
                (None, Some(signal)) => input(signal, ready, response.as_ref())?,
                _ => return None,
            };
            *wire = replace_lane32(*wire, LANE, level)?;
        }
        plan.step(&mut candidate_source, &mut next, &mut candidate_observed)
            .ok()?;
        if Instant::now() >= following {
            // 候補を確定せず、GPIO を保持して最後に確定した出力を残す。
            return deadline_fault(&mut fault).await;
        }
        let committed = pending.commit();
        core::mem::swap(&mut source, &mut candidate_source);
        core::mem::swap(&mut observed, &mut candidate_observed);
        if delivery.is_some() {
            awaiting = None;
        }
        held = if take_response { None } else { response };
        if let Some(request) = outgoing {
            let id = committed.id_at(0)?;
            // この tick が唯一の送信元で、空きを調べてから await を挟まない。
            REQUESTS.try_send((id, request)).ok()?;
            awaiting = Some(id);
        }
        for (port, output) in OUTPUT_PORTS.iter().zip(&mut outputs) {
            output.set_level(if read_lane32(observed[*port], LANE)? {
                Level::High
            } else {
                Level::Low
            });
        }
        // 確定後の割り込みなどで出力反映が期限を越えた場合も、次の tick に進まない。
        if Instant::now() >= following {
            return deadline_fault(&mut fault).await;
        }
        deadline = following;
    }
}
