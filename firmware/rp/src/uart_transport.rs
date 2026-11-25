//! UART の割り込みバッファーと tick 実行の間で、固定容量のメッセージを受け渡す。

use core::cell::Cell;

use circuitgame2_device_timing::HostRequestId;
use embassy_futures::select::{Either, select};
use embassy_rp::{
    Peri,
    interrupt::typelevel::Binding,
    uart::{
        BufferedInterruptHandler, BufferedUart, BufferedUartRx, BufferedUartTx, Config, Error,
        Instance, RxPin, TxPin,
    },
};
use embassy_sync::{
    blocking_mutex::{Mutex, raw::CriticalSectionRawMutex},
    channel::Channel,
    signal::Signal,
};
use embassy_time::{Duration, Timer, with_timeout};
use embedded_io_async::{Read, Write};
use static_cell::StaticCell;

/// 受信した1バイト、または受信時に検出した異常。
#[derive(Clone, Copy)]
pub(super) enum InputEvent {
    Byte(u8),
    Framing,
    Overrun,
    Other,
}

/// 論理 tick で確定した送信に対する結果。
#[derive(Clone, Copy)]
pub(super) enum TxResult {
    Sent,
    Timeout,
    DriverError,
}

#[derive(Clone, Copy)]
pub(super) struct Completion {
    pub id: HostRequestId,
    pub result: TxResult,
}

const MAX_FRAME_BYTES: usize = 32;

/// 固定長の送信キューへ要求を追加できなかった理由。
pub(super) enum SubmitError {
    /// 空のフレームか、保持できるバイト数を超えている。
    Length,
    /// 送信を始めていない別の要求が待っている。
    Full,
}

struct TxCommand {
    id: HostRequestId,
    data: [u8; MAX_FRAME_BYTES],
    length: usize,
}

type RawMutex = CriticalSectionRawMutex;
static GENERATION: Mutex<RawMutex, Cell<u64>> = Mutex::new(Cell::new(0));
static GENERATION_CHANGED: Signal<RawMutex, ()> = Signal::new();
static RX: Channel<RawMutex, (u64, InputEvent), 16> = Channel::new();
static RX_OVERFLOW: Mutex<RawMutex, Cell<Option<u64>>> = Mutex::new(Cell::new(None));
static TX: Channel<RawMutex, TxCommand, 1> = Channel::new();
static COMPLETIONS: Channel<RawMutex, Completion, 1> = Channel::new();

/// ピンと周辺機能を初期化し、受信と送信を別々の executor タスクに渡す。
pub(super) fn start<T: Instance>(
    spawner: embassy_executor::Spawner,
    uart: Peri<'static, T>,
    tx: Peri<'static, impl TxPin<T>>,
    rx: Peri<'static, impl RxPin<T>>,
    irq: impl Binding<T::Interrupt, BufferedInterruptHandler<T>>,
    transmitter_busy: fn() -> bool,
    config: Config,
) -> bool {
    static TX_BUFFER: StaticCell<[u8; 16]> = StaticCell::new();
    static RX_BUFFER: StaticCell<[u8; 32]> = StaticCell::new();
    let (tx, rx) = BufferedUart::new(
        uart,
        tx,
        rx,
        irq,
        TX_BUFFER.init([0; 16]),
        RX_BUFFER.init([0; 32]),
        config,
    )
    .split();
    let (Ok(tx_task), Ok(rx_task)) = (send(tx, transmitter_busy), receive(rx)) else {
        return false;
    };
    spawner.spawn(tx_task);
    spawner.spawn(rx_task);
    true
}

/// 新 reset 世代を通信タスクに伝える。
pub(super) fn set_generation(generation: u64) {
    GENERATION.lock(|value| value.set(generation));
    GENERATION_CHANGED.signal(());
}

fn generation() -> u64 {
    GENERATION.lock(Cell::get)
}

/// 現在の世代でソフトウェア受信列があふれたことを、次の tick に伝える。
pub(super) fn take_overflow(current: u64) -> bool {
    RX_OVERFLOW.lock(|at| at.take() == Some(current))
}

/// 現在の世代のあふれ通知を、その通知を残したまま確認する。
#[cfg(rp_uart_program)]
pub(super) fn has_overflow(current: u64) -> bool {
    RX_OVERFLOW.lock(|at| at.get() == Some(current))
}

/// 読み取りを待たずに、現在の世代が受け付けた次の受信イベントを得る。
pub(super) fn take_input(current: u64) -> Option<InputEvent> {
    pending_input(current)?;
    RX.try_receive().ok().map(|(_, event)| event)
}

/// 現在の世代の先頭イベントを、候補 tick に載せるために借りる。
pub(super) fn pending_input(current: u64) -> Option<InputEvent> {
    // 同じ executor ターンで稼働する唯一の読み手。旧世代のイベントだけをここで破棄する。
    while let Ok((at, event)) = RX.try_peek() {
        if at == current {
            return Some(event);
        }
        let _ = RX.try_receive();
    }
    None
}

/// 完了通知を待たず、到着済みの通知だけを取り出す。
pub(super) fn take_completion() -> Option<Completion> {
    COMPLETIONS.try_receive().ok()
}

/// 次の要求を通信タスクに渡せるかを確かめる。tick が唯一の生産側。
pub(super) fn can_submit() -> bool {
    !TX.is_full()
}

/// 確定済みの要求を通信タスクに渡す。空きを待たず、送信データを固定領域に複製する。
pub(super) fn submit(id: HostRequestId, bytes: &[u8]) -> Result<(), SubmitError> {
    if bytes.is_empty() || bytes.len() > MAX_FRAME_BYTES {
        return Err(SubmitError::Length);
    }
    let mut data = [0; MAX_FRAME_BYTES];
    data[..bytes.len()].copy_from_slice(bytes);
    TX.try_send(TxCommand {
        id,
        data,
        length: bytes.len(),
    })
    .map_err(|_| SubmitError::Full)
}

#[embassy_executor::task]
async fn receive(mut rx: BufferedUartRx) {
    let mut byte = [0];
    loop {
        let event = match rx.read(&mut byte).await {
            Ok(1) => InputEvent::Byte(byte[0]),
            Err(Error::Framing) => InputEvent::Framing,
            Err(Error::Overrun) => InputEvent::Overrun,
            Ok(_) | Err(_) => InputEvent::Other,
        };
        // バッファーから取り出した時点でホストの受信イベントとして記録する。
        let at = generation();
        if RX.try_send((at, event)).is_err() {
            RX_OVERFLOW.lock(|value| value.set(Some(at)));
        }
        // バッファーに連続してデータがある場合も tick に実行機会を渡す。
        embassy_futures::yield_now().await;
    }
}

async fn wait_for_reset(from: u64) {
    while generation() == from {
        GENERATION_CHANGED.wait().await;
    }
}

#[embassy_executor::task]
async fn send(mut tx: BufferedUartTx, transmitter_busy: fn() -> bool) {
    loop {
        let command = TX.receive().await;
        let opened = command.id.generation;
        let transfer = send_frame(&mut tx, transmitter_busy, &command.data[..command.length]);
        let outcome = select(
            wait_for_reset(opened),
            with_timeout(Duration::from_millis(20), transfer),
        )
        .await;
        let result = match outcome {
            Either::First(()) => continue,
            Either::Second(Ok(Ok(()))) => TxResult::Sent,
            Either::Second(Ok(Err(_))) => TxResult::DriverError,
            Either::Second(Err(_)) => TxResult::Timeout,
        };
        // タイムアウト前に物理送信が始まった可能性があるため、自動で送り直さない。
        COMPLETIONS
            .send(Completion {
                id: command.id,
                result,
            })
            .await;
    }
}

async fn send_frame(
    tx: &mut BufferedUartTx,
    transmitter_busy: fn() -> bool,
    data: &[u8],
) -> Result<(), Error> {
    tx.write_all(data).await?;
    tx.flush().await?;
    // Embassy 0.10 の flush はソフトウェアバッファーを空にする。ハードウェアの完了も待つ。
    while transmitter_busy() {
        Timer::after_micros(50).await;
    }
    Ok(())
}
