//! 周辺機能の応答と順序 NOR の tick を確定し、GPIO の出力を更新する。

use circuitgame2_device_timing::{
    FixedReceiveError, FixedRequestLedger, HostRequestId, HostResponseError, RequestKey,
    TickPosition,
};
use embassy_rp::gpio::Output;
use embassy_sync::{blocking_mutex::raw::CriticalSectionRawMutex, channel::Channel};

use super::{
    Duration, GATES, INPUT_COUNT, Instant, LANE, Level, OUTPUT_PORTS, PERIOD_US, PORTS,
    PackedClockedNorPlan32, SOURCE_COUNT, Spawner, Timer, configure_gpio, read_lane32,
    replace_lane32,
};

type Mutex = CriticalSectionRawMutex;

/// 回路上の信号の解釈と、通信タスクとの受け渡し。
pub(super) trait Protocol {
    /// 確定 tick が通信タスクへ送る要求。
    type Request: 'static;
    /// 取り込まれるまで保持する応答。
    type Response: Copy + 'static;
    /// 要求 ID に入れるコントローラー番号。
    const INSTANCE: usize;
    /// 回路入力のうち、周辺機能が駆動する位置の信号番号。
    const INPUTS: &'static [Option<usize>];
    /// 周辺機能が読む順序で並べた回路出力番号。
    const OUTPUTS: &'static [usize];

    /// 唯一の送信元である tick タスクが書く要求キュー。
    fn requests() -> &'static Channel<Mutex, (HostRequestId, Self::Request), 1>;
    /// 通信タスクから要求 ID 付きの応答を受け取るキュー。
    fn completions() -> &'static Channel<Mutex, (HostRequestId, Self::Response), 1>;
    /// コントローラーが新たな要求を受け付ける状態を返す。
    fn available() -> bool;
    /// 確定済みの回路出力から通信要求を読み取る。
    fn request(port: impl Fn(usize) -> bool) -> Self::Request;
    /// 周辺機能が駆動する回路入力の値を返す。
    fn input(signal: usize, ready: bool, response: Option<&Self::Response>) -> Option<bool>;
}

async fn deadline_fault(fault: &mut Output<'_>) -> Option<()> {
    // Pico と Pico 2 の基板 LED で、通常の GPIO 出力とは別に停止を知らせる。
    fault.set_high();
    core::future::pending().await
}

/// 配線表から作った回路を進め、応答を回路が取り込むまで保持する。
pub(super) async fn run<P: Protocol>(spawner: Spawner) -> Option<()> {
    let plan = PackedClockedNorPlan32::new(INPUT_COUNT, &GATES, &PORTS).ok()?;
    let (inputs, mut outputs, mut fault) =
        configure_gpio(spawner, embassy_rp::init(Default::default()))?;
    let mut ledger = FixedRequestLedger::<P::Response, 1>::new();
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
        if let Ok((id, response)) = P::completions().try_receive() {
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
            |signal: usize| read_lane32(observed[P::OUTPUTS[signal]], LANE).unwrap_or(false);
        // 前の tick の出力と今回の入力フレームの両方から受け渡しを決める。
        let take_response = response.is_some() && circuit(1);
        let ready =
            P::available() && awaiting.is_none() && response.is_none() && !P::requests().is_full();
        let outgoing = (ready && circuit(0)).then(|| P::request(circuit));
        let key = outgoing.as_ref().map(|_| RequestKey {
            instance: P::INSTANCE,
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
            .zip(P::INPUTS.iter().copied())
        {
            let level = match (gpio, signal) {
                (Some(gpio), None) => gpio.is_high(),
                (None, Some(signal)) => P::input(signal, ready, response.as_ref())?,
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
            P::requests().try_send((id, request)).ok()?;
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
