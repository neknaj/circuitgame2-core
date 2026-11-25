//! UART の受信バイトを、検査済みの回路の入出力を経由して送信する例。

#![no_std]
#![no_main]

mod uart_transport;
use uart_transport as transport;

use circuitgame2_device_timing::{
    FixedReceiveError, FixedRequestLedger, HostRequestId, HostResponseError, RequestKey,
    TickPosition,
};
use circuitgame2_packed_nor::{PackedClockedNorPlan32, read_lane32};
use embassy_executor::Spawner;
use embassy_rp::{
    bind_interrupts,
    gpio::{Input, Level, Output, Pull},
    peripherals::UART0,
    uart::{BufferedInterruptHandler, Config},
};
use embassy_time::{Duration, Instant, Timer};
use panic_halt as _;
use transport::{InputEvent, TxResult};

bind_interrupts!(struct UartIrqs {
    UART0_IRQ => BufferedInterruptHandler<UART0>;
});

fn uart0_transmitter_busy() -> bool {
    embassy_rp::pac::UART0.uartfr().read().busy()
}

const WIDTH: usize = 8;
// ポートはデータの最下位ビットから並べ、最後にバイトの有効ビットを置く。
const PORTS: [usize; WIDTH + 1] = [0, 1, 2, 3, 4, 5, 6, 7, 8];
const KEY: RequestKey = RequestKey {
    instance: 0,
    tag: 0,
};

struct Demo {
    ledger: FixedRequestLedger<TxResult, 1>,
    awaiting: Option<HostRequestId>,
    input: Option<InputEvent>,
    overflow: bool,
}

impl Demo {
    fn new() -> Self {
        Self {
            ledger: FixedRequestLedger::new(),
            awaiting: None,
            input: None,
            overflow: false,
        }
    }

    fn reset(&mut self) -> bool {
        let Some(generation) = self.ledger.position().generation.checked_add(1) else {
            return false;
        };
        if self
            .ledger
            .reset(TickPosition {
                generation,
                tick: 0,
            })
            .is_err()
        {
            return false;
        }
        self.awaiting = None;
        self.input = None;
        self.overflow = false;
        transport::set_generation(generation);
        true
    }

    // 成功した場合だけ受信イベントを手放し、新しい要求を送信タスクへ渡す。
    fn tick(&mut self, plan: &PackedClockedNorPlan32<'_>, deadline: Instant) -> Option<bool> {
        let current = self.ledger.position();
        let target = TickPosition {
            tick: current.tick.checked_add(1)?,
            ..current
        };
        let mut fault = false;
        // 完了待ちを行わず、すでに到着した通知だけを次の tick の候補に載せる。
        if let Some(completion) = transport::take_completion() {
            match self
                .ledger
                .receive(completion.id, target, completion.result)
            {
                Ok(())
                | Err(FixedReceiveError::Response(HostResponseError::DifferentGeneration)) => {}
                Err(_) => fault = true,
            }
        }
        let delivered = self.awaiting.and_then(|id| {
            self.ledger
                .peek_at(id, target)
                .map(|(_, result)| (id, result))
        });
        self.overflow |= transport::take_overflow(current.generation);
        if self.awaiting.is_none() && self.input.is_none() && transport::can_submit() {
            self.input = transport::take_input(current.generation);
        }
        let byte = match self.input {
            Some(InputEvent::Byte(byte)) => Some(byte),
            Some(_) => {
                fault = true;
                None
            }
            None => None,
        };
        let outgoing = evaluate_echo(plan, byte)?;
        let deliveries = delivered.map(|(id, _)| id);
        let key = outgoing.map(|_| KEY);
        let pending = self
            .ledger
            .prepare_tick(deliveries.as_slice(), key.as_slice())
            .ok()?;
        if Instant::now() >= deadline {
            return None;
        }
        let committed = pending.commit();
        if let Some((_, result)) = delivered {
            self.awaiting = None;
            fault |= !matches!(result, TxResult::Sent);
        }
        if let Some(byte) = outgoing {
            let id = committed.id_at(0)?;
            if transport::submit(id, &[byte]).is_err() {
                return None;
            }
            self.awaiting = Some(id);
        }
        self.input = None;
        fault |= self.overflow;
        self.overflow = false;
        Some(fault)
    }
}

fn evaluate_echo(plan: &PackedClockedNorPlan32<'_>, byte: Option<u8>) -> Option<Option<u8>> {
    let mut source = [0u32; PORTS.len() + 2];
    source[PORTS.len() + 1] = u32::MAX;
    if let Some(byte) = byte {
        for (bit, wire) in source[..WIDTH].iter_mut().enumerate() {
            *wire = u32::from(byte >> bit & 1);
        }
        source[WIDTH] = 1;
    }
    let mut observed = [0u32; PORTS.len()];
    plan.step(&mut source, &mut [], &mut observed).ok()?;
    if !read_lane32(observed[WIDTH], 0)? {
        return Some(None);
    }
    let mut byte = 0;
    for (bit, word) in observed[..WIDTH].iter().enumerate() {
        if read_lane32(*word, 0)? {
            byte |= 1 << bit;
        }
    }
    Some(Some(byte))
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_rp::init(Default::default());
    let reset = Input::new(p.PIN_2, Pull::Up);
    let mut fault = Output::new(p.PIN_3, Level::Low);
    let mut tick_trace = Output::new(p.PIN_4, Level::Low);
    let Ok(plan) = PackedClockedNorPlan32::new(PORTS.len(), &[], &PORTS) else {
        fault.set_high();
        return;
    };
    // Embassy 0.10 の既定値は 115200 baud、8データビット、パリティなし、1停止ビット。
    if !transport::start(
        spawner,
        p.UART0,
        p.PIN_0,
        p.PIN_1,
        UartIrqs,
        uart0_transmitter_busy,
        Config::default(),
    ) {
        fault.set_high();
        return;
    }
    let mut demo = Demo::new();
    let mut reset_held = false;
    let period = Duration::from_millis(1);
    let Some(mut deadline) = Instant::now().checked_add(period) else {
        fault.set_high();
        return;
    };
    loop {
        let Some(next) = deadline.checked_add(period) else {
            fault.set_high();
            return;
        };
        Timer::at(deadline).await;
        if Instant::now() >= next {
            fault.set_high();
            return;
        }
        let pressed = reset.is_low();
        if pressed && !reset_held {
            if !demo.reset() {
                fault.set_high();
                return;
            }
            fault.set_low();
        } else {
            match demo.tick(&plan, next) {
                Some(failed) => {
                    if failed {
                        fault.set_high();
                    }
                    tick_trace.toggle();
                }
                None => {
                    fault.set_high();
                    return;
                }
            }
        }
        reset_held = pressed;
        deadline = next;
    }
}
