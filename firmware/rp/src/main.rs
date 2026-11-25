//! GP2 から読み取った値を NOR で反転し、各 tick の結果を GP3 に出す。

#![no_std]
#![no_main]

use circuitgame2_device_timing::SimulationClock;
use circuitgame2_packed_nor::{
    PackedClockedNorPlan32, PackedNorGate32, read_lane32, replace_lane32,
};
use embassy_executor::Spawner;
use embassy_rp::gpio::{Input, Level, Output, Pull};
use embassy_time::{Duration, Ticker};
use panic_halt as _;

const LANE: u32 = 0;
const PORTS: [usize; 1] = [1];
const GATES: [PackedNorGate32; 1] = [PackedNorGate32 { left: 0, right: 0 }];

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    // 端子を設定する前に配線番号を検査する。
    let mut source = [0, 0, 0, u32::MAX];
    let mut next = [0];
    let mut observed = [0];
    let Ok(plan) = PackedClockedNorPlan32::new(1, &GATES, &PORTS) else {
        return;
    };

    let pins = embassy_rp::init(Default::default());
    let input = Input::new(pins.PIN_2, Pull::Down);
    let mut output = Output::new(pins.PIN_3, Level::Low);
    let mut clock = SimulationClock::new();
    let mut ticker = Ticker::every(Duration::from_millis(1));
    loop {
        ticker.next().await;
        let Ok(tick) = clock.prepare_tick() else {
            return;
        };
        // GP2 はレーン0だけを駆動する。他のレーンは入力0で実行する。
        let Some(word) = replace_lane32(source[0], LANE, input.is_high()) else {
            return;
        };
        source[0] = word;
        if plan.step(&mut source, &mut next, &mut observed).is_err() {
            return;
        }
        let Some(level) = read_lane32(observed[0], LANE) else {
            return;
        };
        // 同じ tick の計算が成功してから状態を確定し、GPIO に反映する。
        if clock.commit(tick).is_err() {
            return;
        }

        output.set_level(if level { Level::High } else { Level::Low });
    }
}
