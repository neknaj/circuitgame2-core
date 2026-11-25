//! UART の ready/valid と確定済み回路出力を照合し、物理タスクへ要求を渡す。

use circuitgame2_device_timing::{
    FixedReceiveError, FixedRequestLedger, HostRequestId, HostResponseError, RequestKey,
    TickPosition,
};
use embassy_rp::{
    Peri, bind_interrupts,
    peripherals::{UART0, UART1},
    uart::{BufferedInterruptHandler, Config, Instance, RxPin, TxPin},
};

use super::{
    Duration, GATES, INPUT_COUNT, Instant, LANE, Level, OUTPUT_PORTS, PERIOD_US, PORTS,
    PackedClockedNorPlan32, SOURCE_COUNT, Spawner, Timer, UART_INPUTS, UART_INSTANCE, UART_OUTPUTS,
    configure_gpio, read_lane32, replace_lane32, uart_transport as transport,
};
use transport::{InputEvent, TxResult};

bind_interrupts!(struct UartIrqs {
    UART0_IRQ => BufferedInterruptHandler<UART0>;
    UART1_IRQ => BufferedInterruptHandler<UART1>;
});

fn uart0_busy() -> bool {
    embassy_rp::pac::UART0.uartfr().read().busy()
}

fn uart1_busy() -> bool {
    embassy_rp::pac::UART1.uartfr().read().busy()
}

pub(super) fn start<T: Instance>(
    spawner: Spawner,
    uart: Peri<'static, T>,
    tx: Peri<'static, impl TxPin<T>>,
    rx: Peri<'static, impl RxPin<T>>,
    instance: u8,
    baud: u32,
) -> Option<()>
where
    UartIrqs: embassy_rp::interrupt::typelevel::Binding<T::Interrupt, BufferedInterruptHandler<T>>,
{
    // Embassy が分周値を飽和させる設定を拒否し、指定と異なる極端な転送速度を防ぐ。
    let ratio = 8u64 * u64::from(embassy_rp::clocks::clk_peri_freq()) / u64::from(baud);
    if ratio >> 7 == 0 || ratio >> 7 >= u64::from(u16::MAX) || ratio & 127 == 127 {
        return None;
    }
    let busy = if instance == 0 {
        uart0_busy
    } else {
        uart1_busy
    };
    let mut config = Config::default();
    config.baudrate = baud;
    transport::start(spawner, uart, tx, rx, UartIrqs, busy, config).then_some(())
}

#[derive(Clone, Copy)]
struct Signals {
    rx: Option<InputEvent>,
    tx_ready: bool,
    tx_result: Option<TxResult>,
}

impl Signals {
    fn value(self, signal: usize) -> bool {
        match signal {
            0..=7 => matches!(self.rx, Some(InputEvent::Byte(byte)) if byte & (1 << signal) != 0),
            8 => self.rx.is_some(),
            9 => matches!(self.rx, Some(InputEvent::Framing | InputEvent::Other)),
            10 => matches!(self.rx, Some(InputEvent::Overrun)),
            11 => self.tx_ready,
            12 => self.tx_result.is_some(),
            _ => matches!(self.tx_result, Some(TxResult::Sent)),
        }
    }
}

struct Device {
    ledger: FixedRequestLedger<TxResult, 1>,
    awaiting: Option<HostRequestId>,
    rx: Option<InputEvent>,
    tx_result: Option<TxResult>,
}

impl Device {
    fn new() -> Self {
        Self {
            ledger: FixedRequestLedger::new(),
            awaiting: None,
            rx: None,
            tx_result: None,
        }
    }
}

pub(super) async fn run(spawner: Spawner) -> Option<()> {
    let plan = PackedClockedNorPlan32::new(INPUT_COUNT, &GATES, &PORTS).ok()?;
    let (inputs, mut outputs) = configure_gpio(spawner, embassy_rp::init(Default::default()))?;
    let mut source = [0; SOURCE_COUNT];
    source[SOURCE_COUNT - 1] = u32::MAX;
    let mut observed = PORTS.map(|wire| source[wire]);
    let mut device = Device::new();
    let mut next = [0; GATES.len()];
    let mut candidate_source = [0; SOURCE_COUNT];
    let mut candidate_observed = [0; PORTS.len()];
    let period = Duration::from_micros(PERIOD_US);
    let mut deadline = Instant::now().checked_add(period)?;
    loop {
        let following = deadline.checked_add(period)?;
        Timer::at(deadline).await;
        if Instant::now() >= following {
            return None;
        }
        let current = device.ledger.position();
        let target = TickPosition {
            tick: current.tick.checked_add(1)?,
            ..current
        };
        // tick の準備に先立ち、完了通知の所有権を通信列から台帳に移す。
        // 台帳の候補を破棄した場合も、受け取った通知は配送待ちのまま残る。
        if let Some(done) = transport::take_completion() {
            match device.ledger.receive(done.id, target, done.result) {
                Ok(())
                | Err(FixedReceiveError::Response(HostResponseError::DifferentGeneration)) => {}
                Err(_) => return None,
            }
        }
        let delivered = device.awaiting.and_then(|id| {
            device
                .ledger
                .peek_at(id, target)
                .map(|(_, result)| (id, result))
        });
        let circuit = |port: usize| read_lane32(observed[port], LANE).unwrap_or(false);
        let mut signals = Signals {
            rx: device.rx,
            tx_ready: false,
            tx_result: device.tx_result,
        };
        // 今回の入力フレームと、直前に確定した回路出力で受け渡しを判断する。
        if let Some((_, result)) = delivered {
            signals.tx_result = Some(result);
        }
        let queued_rx = if signals.rx.is_none() {
            transport::pending_input(current.generation)
        } else {
            None
        };
        let queued_overflow = signals.rx.is_none()
            && queued_rx.is_none()
            && transport::has_overflow(current.generation);
        signals.rx = signals
            .rx
            .or(queued_rx)
            .or(queued_overflow.then_some(InputEvent::Overrun));
        signals.tx_ready =
            device.awaiting.is_none() && signals.tx_result.is_none() && transport::can_submit();
        let take_rx = signals.rx.is_some() && circuit(UART_OUTPUTS[0]);
        let take_tx_result = signals.tx_result.is_some() && circuit(UART_OUTPUTS[10]);
        let outgoing = if signals.tx_ready && circuit(UART_OUTPUTS[9]) {
            let mut byte = 0;
            for (bit, port) in UART_OUTPUTS[1..9].iter().enumerate() {
                if circuit(*port) {
                    byte |= 1 << bit;
                }
            }
            Some(byte)
        } else {
            None
        };
        let delivery = delivered.map(|(id, _)| id);
        let request = outgoing.map(|_| RequestKey {
            instance: usize::from(UART_INSTANCE),
            tag: 0,
        });
        let pending = device
            .ledger
            .prepare_tick(delivery.as_slice(), request.as_slice())
            .ok()?;
        candidate_source.copy_from_slice(&source);
        for ((wire, input), signal) in candidate_source[..INPUT_COUNT]
            .iter_mut()
            .zip(&inputs)
            .zip(UART_INPUTS)
        {
            let value = match (input, signal) {
                (Some(input), None) => input.is_high(),
                (None, Some(signal)) => signals.value(signal),
                _ => return None,
            };
            *wire = replace_lane32(*wire, LANE, value)?;
        }
        plan.step(&mut candidate_source, &mut next, &mut candidate_observed)
            .ok()?;
        if Instant::now() >= following {
            return None;
        }
        let committed = pending.commit();
        core::mem::swap(&mut source, &mut candidate_source);
        core::mem::swap(&mut observed, &mut candidate_observed);
        // 待ち行列に触れるタスクとは、この間に実行を交代しない。
        if queued_rx.is_some() {
            let _ = transport::take_input(current.generation);
        } else if queued_overflow {
            let _ = transport::take_overflow(current.generation);
        }
        if delivery.is_some() {
            device.awaiting = None;
        }
        if let Some(byte) = outgoing {
            let id = committed.id_at(0)?;
            // 唯一の生産側で、上の tick からこの位置まで await を挟まない。
            transport::submit(id, &[byte]).ok()?;
            device.awaiting = Some(id);
        }
        if take_rx {
            signals.rx = None;
        }
        if take_tx_result {
            signals.tx_result = None;
        }
        device.rx = signals.rx;
        device.tx_result = signals.tx_result;
        for (port, output) in OUTPUT_PORTS.iter().zip(&mut outputs) {
            let level = read_lane32(observed[*port], LANE)?;
            output.set_level(if level { Level::High } else { Level::Low });
        }
        deadline = following;
    }
}
