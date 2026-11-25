//! 確定済みの回路出力と I²C の応答を照合し、通信タスクと tick を独立して進める。

use circuitgame2_device_timing::{
    HostRequestId, I2cTransfer, I2cTransferError, i2c_port_bit, i2c_port_octet,
};
use embassy_rp::{
    Peri, bind_interrupts,
    i2c::{Async, Config, I2c, Instance, InterruptHandler, SclPin, SdaPin},
    peripherals::{I2C0, I2C1},
};
use embassy_sync::{blocking_mutex::raw::CriticalSectionRawMutex, channel::Channel};

use super::{
    Duration, I2C_CAPACITY, I2C_INPUTS, I2C_INSTANCE, I2C_OUTPUTS, Spawner,
    i2c_transport::{Controller, Readback, TransferFailure},
    peripheral_program::{self, Protocol},
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

struct I2cProtocol;

impl Protocol for I2cProtocol {
    type Request = Request;
    type Response = Response;
    const INSTANCE: usize = I2C_INSTANCE as usize;
    const INPUTS: &'static [Option<usize>] = &I2C_INPUTS;
    const OUTPUTS: &'static [usize] = &I2C_OUTPUTS;

    fn requests() -> &'static Channel<Mutex, (HostRequestId, Request), 1> {
        &REQUESTS
    }
    fn completions() -> &'static Channel<Mutex, (HostRequestId, Response), 1> {
        &COMPLETIONS
    }
    fn available() -> bool {
        true
    }
    fn request(port: impl Fn(usize) -> bool) -> Request {
        request(port)
    }
    fn input(signal: usize, ready: bool, response: Option<&Response>) -> Option<bool> {
        input(signal, ready, response)
    }
}

/// I²C と GPIO を初期化し、配線表の tick を進める。
pub(super) async fn run(spawner: Spawner) -> Option<()> {
    peripheral_program::run::<I2cProtocol>(spawner).await
}
