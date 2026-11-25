//! 検査済みの配線と GPIO 割り当てで、順序 NOR の tick を進める。

#![no_std]
#![no_main]

#[cfg(not(rp_uart_program))]
use circuitgame2_device_timing::SimulationClock;

#[cfg(rp_uart_program)]
#[path = "uart_program.rs"]
mod uart;
#[cfg(rp_uart_program)]
mod uart_transport;
use circuitgame2_packed_nor::{
    PackedClockedNorPlan32, PackedNorGate32, read_lane32, replace_lane32,
};
use embassy_executor::Spawner;
use embassy_rp::gpio::{Input, Level, Output, Pull};
use embassy_time::{Duration, Instant, Timer};
use panic_halt as _;

include!(concat!(env!("OUT_DIR"), "/program.rs"));

const LANE: u32 = 0;
const SOURCE_COUNT: usize = INPUT_COUNT + GATES.len() + 2;

#[cfg(not(rp_uart_program))]
#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    // 端子を設定する前に配線番号を検査する。
    let Ok(plan) = PackedClockedNorPlan32::new(INPUT_COUNT, &GATES, &PORTS) else {
        return;
    };

    let mut source = [0; SOURCE_COUNT];
    source[SOURCE_COUNT - 1] = u32::MAX;
    let mut next = [0; GATES.len()];
    let mut observed = [0; PORTS.len()];
    let (inputs, mut outputs) = configure_gpio(embassy_rp::init(Default::default()));
    let mut clock = SimulationClock::new();
    let period = Duration::from_micros(PERIOD_US);
    let Some(mut deadline) = Instant::now().checked_add(period) else {
        return;
    };
    loop {
        let Some(following_deadline) = deadline.checked_add(period) else {
            return;
        };
        Timer::at(deadline).await;
        if Instant::now() >= following_deadline {
            return;
        }
        let Ok(tick) = clock.prepare_tick() else {
            return;
        };
        // 物理入力はレーン0にだけ反映する。
        for (slot, input) in source.iter_mut().zip(&inputs) {
            let Some(word) = replace_lane32(*slot, LANE, input.is_high()) else {
                return;
            };
            *slot = word;
        }
        if plan.step(&mut source, &mut next, &mut observed).is_err() {
            return;
        }
        // tick を確定してから、宣言順で得た出力を各端子に反映する。
        if Instant::now() >= following_deadline || clock.commit(tick).is_err() {
            return;
        }
        for (port, output) in OUTPUT_PORTS.iter().zip(&mut outputs) {
            let Some(level) = read_lane32(observed[*port], LANE) else {
                return;
            };
            output.set_level(if level { Level::High } else { Level::Low });
        }
        deadline = following_deadline;
    }
}

#[cfg(rp_uart_program)]
#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let _ = uart::run(spawner).await;
}
