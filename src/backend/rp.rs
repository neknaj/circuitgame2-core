//! Pico と Pico 2 の外部 GPIO とハードウェア周辺機能の割り当てを検査する。

mod image;

pub use image::{I2cCircuitImage, I2cImageError, I2cInputSource, I2cPortNames, I2cSetup};
#[cfg(verus_only)]
pub use image::{i2c_assignment, i2c_image_ports_match, i2c_image_requests, i2c_port_capacity};

pub use image::{
    GpioBinding, GpioCircuitImage, GpioImageError, GpioOutputPin, RpInputSource, UartCircuitImage,
    UartImageError, UartInputSignal, UartOutputPorts, UartPortNames, UartSetup,
};
#[cfg(verus_only)]
pub use image::{
    gpio_assignment, gpio_binding_indices_match, gpio_image_ports_match, gpio_request,
    uart_assignment, uart_image_ports_match, uart_image_requests, uart_output_indices_fit,
};

use vstd::prelude::*;

verus! {

/// 割り当てを検査する基板。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Board {
    /// RP2040 を搭載する Raspberry Pi Pico。
    Pico,
    /// RP2350A を搭載する Raspberry Pi Pico 2。
    Pico2,
}

/// ハードウェア周辺機能の種別。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Controller {
    /// UART の送受信。
    Uart,
    /// SPI のコントローラー。
    Spi,
    /// I²C のコントローラー。
    I2c,
}

/// ピンが担当する信号。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Signal {
    /// 回路へ渡す GPIO 入力。
    GpioInput,
    /// 回路の確定値を出す GPIO。
    GpioOutput,
    /// UART から送信する TX。
    UartTx,
    /// UART が受信する RX。
    UartRx,
    /// SPI のクロック。
    SpiClock,
    /// SPI コントローラーのデータ出力。
    SpiMosi,
    /// SPI コントローラーのデータ入力。
    SpiMiso,
    /// GPIO で制御する SPI のチップ選択。
    SpiSelect,
    /// I²C のデータ。
    I2cData,
    /// I²C のクロック。
    I2cClock,
}

/// 一つの GPIO または周辺機能を使うための割り当て。
///
/// ピンは基板の GP 番号で指定する。例えばヘッダーの1番ピンは GP0 なので `0` を指定する。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Assignment {
    /// 回路への GPIO 入力。
    GpioInput {
        /// 入力ピンの GP 番号。
        pin: u8,
    },
    /// 回路が駆動する GPIO 出力。
    GpioOutput {
        /// 出力ピンの GP 番号。
        pin: u8,
        /// 初期化時に出すレベル。
        initial_high: bool,
    },
    /// 8N1 のハードウェア UART に割り当てる送受信ピン。
    Uart {
        /// UART のインスタンス番号。
        instance: u8,
        /// 送信ピンの GP 番号。
        tx: u8,
        /// 受信ピンの GP 番号。
        rx: u8,
    },
    /// SPI コントローラーに割り当てる信号。
    Spi {
        /// SPI のインスタンス番号。
        instance: u8,
        /// クロック出力の GP 番号。
        clock: u8,
        /// データ出力の GP 番号。
        mosi: u8,
        /// データ入力の GP 番号。
        miso: u8,
        /// チップ選択を GPIO 出力として制御するピンの GP 番号。
        select: u8,
    },
    /// I²C コントローラーに割り当てる信号。
    I2c {
        /// I²C のインスタンス番号。
        instance: u8,
        /// データピンの GP 番号。
        data: u8,
        /// クロックピンの GP 番号。
        clock: u8,
    },
}

/// 割り当てのどの信号がピンを要求したかを示す。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PinSite {
    /// 呼び出し時に渡した割り当て配列の添字。
    pub assignment: usize,
    /// 割り当てが要求した信号。
    pub signal: Signal,
}

/// ボードの配線を検査したときの最初の違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssignmentError {
    /// 周辺機能に指定された番号が範囲外。
    UnknownInstance {
        /// 割り当て配列の添字。
        assignment: usize,
        /// 番号を指定した周辺機能。
        controller: Controller,
        /// 指定したインスタンス番号。
        instance: u8,
    },
    /// 同じ周辺機能の同じ番号が複数回指定された。
    DuplicateInstance {
        /// 最初の割り当ての添字。
        first_assignment: usize,
        /// 重複した割り当ての添字。
        assignment: usize,
        /// 重複した周辺機能。
        controller: Controller,
        /// 重複したインスタンス番号。
        instance: u8,
    },
    /// 指定された番号が基板で外部接続できる GPIO の範囲外。
    UnexposedPin {
        /// ピンを指定した信号。
        site: PinSite,
        /// 指定した GP 番号。
        pin: u8,
    },
    /// そのピンを指定した周辺機能の信号として使えない。
    UnsupportedSignal {
        /// 選んだ周辺機能と信号の位置。
        site: PinSite,
        /// 指定した GP 番号。
        pin: u8,
        /// 指定した周辺機能のインスタンス番号。
        instance: u8,
    },
    /// 同じ GPIO が複数の信号に割り当てられた。
    DuplicatePin {
        /// 最初にピンを使った信号。
        first: PinSite,
        /// 重複した信号。
        site: PinSite,
        /// 重複した GP 番号。
        pin: u8,
    },
}

/// 選択した基板で使用できることを検査した割り当ての一覧。
#[derive(Debug)]
pub struct CheckedAssignments<'a> {
    board: Board,
    input: &'a [Assignment],
}

/// 両基板のヘッダー・キャスタレーションに出ている GP 番号。
pub open spec fn gpio_exposed(pin: u8) -> bool {
    pin <= 22 || 26 <= pin <= 28
}

/// 基板上の GPIO で選べる周辺機能・信号の組を表す。
///
/// GPIO と SPI の GPIO チップ選択は露出ピンを使用できる。Pico 2 の UART は F2 と F11 を使う。
/// ピンの出典は [Pico と Pico 2 のピン配置図](https://www.raspberrypi.com/documentation/microcontrollers/pico-series.html) と
/// [RP2040](https://datasheets.raspberrypi.com/rp2040/rp2040-datasheet.pdf)・
/// [RP2350](https://datasheets.raspberrypi.com/rp2350/rp2350-datasheet.pdf) の GPIO 機能選択表。
pub open spec fn signal_supported(board: Board, instance: u8, signal: Signal, pin: u8) -> bool {
    let gp = pin as int;
    &&& gpio_exposed(pin)
    &&& match signal {
        Signal::GpioInput | Signal::GpioOutput | Signal::SpiSelect => true,
        Signal::UartTx | Signal::UartRx => {
            let primary = gp % 4 == (if signal is UartTx { 0int } else { 1int });
            let auxiliary = board is Pico2 && gp % 4 == (if signal is UartTx { 2int } else { 3int });
            let controller = if gp / 4 % 4 == 0 || gp / 4 % 4 == 3 { 0int } else { 1int };
            (primary || auxiliary) && instance as int == controller
        },
        Signal::SpiClock | Signal::SpiMosi | Signal::SpiMiso => {
            let offset = match signal { Signal::SpiMiso => 0int, Signal::SpiClock => 2int, _ => 3int };
            gp % 4 == offset && instance as int == gp / 8 % 2
        },
        Signal::I2cData | Signal::I2cClock => {
            gp % 2 == (if signal is I2cData { 0int } else { 1int })
                && instance as int == gp / 2 % 2
        },
    }
}

fn exposed(pin: u8) -> (ok: bool)
    ensures ok == gpio_exposed(pin),
{
    pin <= 22 || (26 <= pin && pin <= 28)
}

fn supported(board: Board, instance: u8, signal: Signal, pin: u8) -> (ok: bool)
    ensures ok == signal_supported(board, instance, signal, pin),
{
    if !exposed(pin) { return false; }
    match signal {
        Signal::GpioInput | Signal::GpioOutput | Signal::SpiSelect => true,
        Signal::UartTx | Signal::UartRx => {
            let offset = if matches!(signal, Signal::UartTx) { 0 } else { 1 };
            let group = pin / 4 % 4;
            let controller = if group == 0 || group == 3 { 0 } else { 1 };
            let role = pin % 4;
            instance == controller && (role == offset
                || (matches!(board, Board::Pico2) && role == offset + 2))
        },
        Signal::SpiClock | Signal::SpiMosi | Signal::SpiMiso => {
            let offset = match signal { Signal::SpiMiso => 0, Signal::SpiClock => 2, _ => 3 };
            pin % 4 == offset && instance == pin / 8 % 2
        },
        Signal::I2cData | Signal::I2cClock => {
            let offset = if matches!(signal, Signal::I2cData) { 0 } else { 1 };
            pin % 2 == offset && instance == pin / 2 % 2
        },
    }
}

/// 割り当てが使用する周辺機能の種別と番号を表す。GPIO 単独の割り当ては `None` になる。
pub open spec fn assignment_controller(assignment: Assignment) -> Option<(Controller, u8)> {
    match assignment {
        Assignment::Uart { instance, .. } => Some((Controller::Uart, instance)),
        Assignment::Spi { instance, .. } => Some((Controller::Spi, instance)),
        Assignment::I2c { instance, .. } => Some((Controller::I2c, instance)),
        _ => None,
    }
}

fn controller(assignment: Assignment) -> (device: Option<(Controller, u8)>)
    ensures device == assignment_controller(assignment),
{
    match assignment {
        Assignment::Uart { instance, .. } => Some((Controller::Uart, instance)),
        Assignment::Spi { instance, .. } => Some((Controller::Spi, instance)),
        Assignment::I2c { instance, .. } => Some((Controller::I2c, instance)),
        _ => None,
    }
}

/// 割り当てが使用する信号と GPIO 番号を、検査時の順序で表す。
pub open spec fn assignment_pins(assignment: Assignment) -> Seq<(Signal, u8)> {
    match assignment {
        Assignment::GpioInput { pin } => seq![(Signal::GpioInput, pin)],
        Assignment::GpioOutput { pin, .. } => seq![(Signal::GpioOutput, pin)],
        Assignment::Uart { tx, rx, .. } => seq![(Signal::UartTx, tx), (Signal::UartRx, rx)],
        Assignment::Spi { clock, mosi, miso, select, .. } => seq![
            (Signal::SpiClock, clock), (Signal::SpiMosi, mosi),
            (Signal::SpiMiso, miso), (Signal::SpiSelect, select),
        ],
        Assignment::I2c { data, clock, .. } => seq![(Signal::I2cData, data), (Signal::I2cClock, clock)],
    }
}

fn pins(assignment: Assignment) -> (group: ([(Signal, u8); 4], usize))
    ensures group.1 <= 4, group.0@.take(group.1 as int) == assignment_pins(assignment),
{
    let unused = (Signal::GpioInput, 0);
    let group = match assignment {
        Assignment::GpioInput { pin } => ([(Signal::GpioInput, pin), unused, unused, unused], 1),
        Assignment::GpioOutput { pin, .. } => ([(Signal::GpioOutput, pin), unused, unused, unused], 1),
        Assignment::Uart { tx, rx, .. } => ([(Signal::UartTx, tx), (Signal::UartRx, rx), unused, unused], 2),
        Assignment::Spi { clock, mosi, miso, select, .. } => ([
            (Signal::SpiClock, clock), (Signal::SpiMosi, mosi),
            (Signal::SpiMiso, miso), (Signal::SpiSelect, select),
        ], 4),
        Assignment::I2c { data, clock, .. } => ([(Signal::I2cData, data), (Signal::I2cClock, clock), unused, unused], 2),
    };
    assert(group.0@.take(group.1 as int) =~= assignment_pins(assignment));
    group
}

spec fn first_controller(input: Seq<Assignment>, stop: int, value: (Controller, u8)) -> Option<usize> {
    if exists|i: int| 0 <= i < stop && #[trigger] assignment_controller(input[i]) == Some(value) {
        Some(choose|i: usize| i < stop && #[trigger] assignment_controller(input[i as int]) == Some(value)
            && forall|j: int| 0 <= j < i ==> #[trigger] assignment_controller(input[j]) != Some(value))
    } else { None }
}

spec fn controller_error(input: Seq<Assignment>, i: int) -> Option<AssignmentError> {
    match assignment_controller(input[i]) {
        None => None,
        Some((controller, instance)) => if instance > 1 {
            Some(AssignmentError::UnknownInstance { assignment: i as usize, controller, instance })
        } else {
            match first_controller(input, i, (controller, instance)) {
                None => None,
                Some(first) => Some(AssignmentError::DuplicateInstance {
                    first_assignment: first, assignment: i as usize, controller, instance,
                }),
            }
        },
    }
}

fn same_controller(left: Controller, right: Controller) -> (same: bool)
    ensures same == (left == right),
{
    match left {
        Controller::Uart => matches!(right, Controller::Uart),
        Controller::Spi => matches!(right, Controller::Spi),
        Controller::I2c => matches!(right, Controller::I2c),
    }
}


#[verifier::opaque]
spec fn no_controller_before(input: Seq<Assignment>, stop: int, value: (Controller, u8)) -> bool {
    forall|i: int| 0 <= i < stop ==> #[trigger] assignment_controller(input[i]) != Some(value)
}

proof fn extend_controller_scan(input: Seq<Assignment>, row: int, value: (Controller, u8))
    requires 0 <= row < input.len(), no_controller_before(input, row, value),
        assignment_controller(input[row]) != Some(value),
    ensures no_controller_before(input, row + 1, value),
{
    reveal(no_controller_before);
    assert forall|i: int| 0 <= i < row + 1 implies
        #[trigger] assignment_controller(input[i]) != Some(value) by {
        if i != row { assert(i < row); }
    };
}

proof fn controller_scan_result(input: Seq<Assignment>, stop: int, row: usize, value: (Controller, u8))
    requires row <= stop <= input.len(), no_controller_before(input, row as int, value),
        row < stop ==> assignment_controller(input[row as int]) == Some(value),
    ensures first_controller(input, stop, value) == if row < stop { Some(row) } else { None },
{
    reveal(no_controller_before);
    if row < stop {
        assert(exists|i: int| 0 <= i < stop && #[trigger] assignment_controller(input[i]) == Some(value)) by {
            assert(assignment_controller(input[row as int]) == Some(value));
        };
        let first = first_controller(input, stop, value)->Some_0;
        assert(first == row) by {
            if first < row {
                assert(assignment_controller(input[first as int]) != Some(value));
            } else if row < first {
                assert(assignment_controller(input[row as int]) != Some(value));
            }
        };
    } else {
        assert(!(exists|i: int| 0 <= i < stop && #[trigger] assignment_controller(input[i]) == Some(value)));
    }
}

fn check_controller(input: &[Assignment], i: usize) -> (error: Option<AssignmentError>)
    requires i < input@.len(),
    ensures error == controller_error(input@, i as int),
{
    let Some((kind, instance)) = controller(input[i]) else { return None; };
    if instance > 1 {
        return Some(AssignmentError::UnknownInstance { assignment: i, controller: kind, instance });
    }
    let ghost key = (kind, instance);
    assert(no_controller_before(input@, 0, key)) by { reveal(no_controller_before); };
    let mut k = 0;
    while k < i
        invariant k <= i < input@.len(),
            assignment_controller(input@[i as int]) == Some((kind, instance)),
            instance <= 1,
            key == (kind, instance), no_controller_before(input@, k as int, key),
        decreases i - k,
    {
        if let Some((earlier, number)) = controller(input[k]) {
            if number == instance && same_controller(earlier, kind) {
                proof { controller_scan_result(input@, i as int, k, key); }
                return Some(AssignmentError::DuplicateInstance { first_assignment: k, assignment: i, controller: kind, instance });
            }
        }
        assert(assignment_controller(input@[k as int]) != Some((kind, instance)));
        proof { extend_controller_scan(input@, k as int, key); }
        k += 1;
    }
    proof { controller_scan_result(input@, i as int, k, key); }
    None
}

spec fn prior_pin(input: Seq<Assignment>, i: int, stop: int, row: int, pos: int, pin: u8) -> bool {
    &&& 0 <= row <= i
    &&& 0 <= pos < assignment_pins(input[row]).len()
    &&& (row < i || pos < stop)
    &&& assignment_pins(input[row])[pos].1 == pin
}

spec fn earlier(row: int, pos: int, other_row: int, other_pos: int) -> bool {
    row < other_row || row == other_row && pos < other_pos
}

spec fn first_pin(input: Seq<Assignment>, i: int, stop: int, pin: u8) -> Option<PinSite> {
    if exists|row: int, pos: int| #[trigger] prior_pin(input, i, stop, row, pos, pin) {
        let (row, pos) = choose|row: int, pos: int| #[trigger] prior_pin(input, i, stop, row, pos, pin)
            && forall|r: int, p: int| #[trigger] prior_pin(input, i, stop, r, p, pin)
                ==> !earlier(r, p, row, pos);
        Some(PinSite { assignment: row as usize, signal: assignment_pins(input[row])[pos].0 })
    } else { None }
}

fn find_pin(input: &[Assignment], i: usize, stop: usize, pin: u8) -> (prior: Option<PinSite>)
    requires i < input@.len(), stop <= assignment_pins(input@[i as int]).len(),
    ensures prior == first_pin(input@, i as int, stop as int, pin),
{
    let mut row = 0;
    while row <= i
        invariant row <= i + 1, i < input@.len(), stop <= assignment_pins(input@[i as int]).len(),
            forall|r: int, p: int| r < row ==> !#[trigger] prior_pin(input@, i as int, stop as int, r, p, pin),
        decreases i + 1 - row,
    {
        let (group, length) = pins(input[row]);
        let end = if row == i { stop } else { length };
        let mut pos = 0;
        while pos < end
            invariant row <= i < input@.len(), stop <= assignment_pins(input@[i as int]).len(),
                group@.take(length as int) == assignment_pins(input@[row as int]), length <= 4,
                end == if row == i { stop } else { length },
                pos <= end <= length,
                forall|r: int, p: int| r < row ==> !#[trigger] prior_pin(input@, i as int, stop as int, r, p, pin),
                forall|p: int| p < pos ==> !#[trigger] prior_pin(input@, i as int, stop as int, row as int, p, pin),
            decreases end - pos,
        {
            let (signal, candidate) = group[pos];
            assert(assignment_pins(input@[row as int])[pos as int] == (signal, candidate));
            if candidate == pin {
                proof {
                    let ghost r = row as int;
                    let ghost p = pos as int;
                    assert(prior_pin(input@, i as int, stop as int, r, p, pin));
                    let (first, first_pos) = choose|r: int, p: int| #[trigger] prior_pin(input@, i as int, stop as int, r, p, pin)
                        && forall|rr: int, pp: int| #[trigger] prior_pin(input@, i as int, stop as int, rr, pp, pin)
                            ==> !earlier(rr, pp, r, p);
                    assert(first == r && first_pos == p) by {
                        if earlier(first, first_pos, r, p) {
                            assert(!prior_pin(input@, i as int, stop as int, first, first_pos, pin));
                        }
                        assert(!earlier(r, p, first, first_pos));
                    };
                }
                return Some(PinSite { assignment: row, signal });
            }
            assert(!prior_pin(input@, i as int, stop as int, row as int, pos as int, pin));
            pos += 1;
        }
        assert forall|r: int, p: int| r < row + 1
            implies !#[trigger] prior_pin(input@, i as int, stop as int, r, p, pin) by {
            if r == row && prior_pin(input@, i as int, stop as int, r, p, pin) {
                assert(p < end);
            }
        };
        row += 1;
    }
    None
}

spec fn pin_error(board: Board, input: Seq<Assignment>, i: int, j: int) -> Option<AssignmentError> {
    let (signal, pin) = assignment_pins(input[i])[j];
    let site = PinSite { assignment: i as usize, signal };
    let instance = match assignment_controller(input[i]) { Some(value) => value.1, None => 0 };
    if !gpio_exposed(pin) {
        Some(AssignmentError::UnexposedPin { site, pin })
    } else if !signal_supported(board, instance, signal, pin) {
        Some(AssignmentError::UnsupportedSignal { site, pin, instance })
    } else {
        match first_pin(input, i, j, pin) {
            Some(first) => Some(AssignmentError::DuplicatePin { first, site, pin }),
            None => None,
        }
    }
}

spec fn valid_assignment(board: Board, input: Seq<Assignment>, i: int) -> bool {
    &&& controller_error(input, i) is None
    &&& forall|j: int| 0 <= j < assignment_pins(input[i]).len() ==> #[trigger] pin_error(board, input, i, j) is None
}

/// 全割り当ての GPIO と周辺機能が有効で、同じ資源を重ねて使わないことを表す。
pub closed spec fn assignments_valid(board: Board, input: Seq<Assignment>) -> bool {
    forall|i: int| 0 <= i < input.len() ==> #[trigger] valid_assignment(board, input, i)
}

/// 診断が入力順で最初の違反を指すことを表す。
pub closed spec fn first_assignment_error(board: Board, input: Seq<Assignment>, error: AssignmentError) -> bool {
    exists|i: int| 0 <= i < input.len()
        && !#[trigger] valid_assignment(board, input, i)
        && (forall|prior: int| 0 <= prior < i ==> #[trigger] valid_assignment(board, input, prior))
        && (controller_error(input, i) == Some(error) || controller_error(input, i) is None
            && exists|j: int| 0 <= j < assignment_pins(input[i]).len()
                && #[trigger] pin_error(board, input, i, j) == Some(error)
                && (forall|prior: int| 0 <= prior < j ==> #[trigger] pin_error(board, input, i, prior) is None))
}

/// 割り当てた GPIO がボードに露出し、指定された信号を扱えることを示す。
pub proof fn pin_compatibility(board: Board, input: Seq<Assignment>, row: int, position: int)
    requires
        assignments_valid(board, input),
        0 <= row < input.len(),
        0 <= position < assignment_pins(input[row]).len(),
    ensures
        gpio_exposed(assignment_pins(input[row])[position].1),
        signal_supported(
            board,
            match assignment_controller(input[row]) { Some(c) => c.1, None => 0 },
            assignment_pins(input[row])[position].0,
            assignment_pins(input[row])[position].1,
        ),
{
    assert(valid_assignment(board, input, row));
    assert(pin_error(board, input, row, position) is None);
}

/// 異なる信号位置に同じ GPIO 番号が割り当てられていないことを示す。
pub proof fn pins_distinct(board: Board, input: Seq<Assignment>, row: int, position: int, other_row: int, other_position: int)
    requires
        assignments_valid(board, input),
        0 <= row < input.len(),
        0 <= other_row < input.len(),
        0 <= position < assignment_pins(input[row]).len(),
        0 <= other_position < assignment_pins(input[other_row]).len(),
        row != other_row || position != other_position,
    ensures
        assignment_pins(input[row])[position].1
            != assignment_pins(input[other_row])[other_position].1,
{
    if earlier(row, position, other_row, other_position) {
        no_pin_reuse(board, input, row, position, other_row, other_position);
    } else {
        no_pin_reuse(board, input, other_row, other_position, row, position);
    }
}

proof fn no_pin_reuse(board: Board, input: Seq<Assignment>, row: int, position: int, later_row: int, later_position: int)
    requires
        assignments_valid(board, input),
        0 <= row < input.len(),
        0 <= later_row < input.len(),
        0 <= position < assignment_pins(input[row]).len(),
        0 <= later_position < assignment_pins(input[later_row]).len(),
        earlier(row, position, later_row, later_position),
    ensures
        assignment_pins(input[row])[position].1
            != assignment_pins(input[later_row])[later_position].1,
{
    let pin = assignment_pins(input[later_row])[later_position].1;
    assert(valid_assignment(board, input, later_row));
    assert(pin_error(board, input, later_row, later_position) is None);
    if assignment_pins(input[row])[position].1 == pin {
        assert(prior_pin(input, later_row, later_position, row, position, pin));
        assert(first_pin(input, later_row, later_position, pin) is Some);
    }
}

/// 周辺機能の番号が範囲内にあり、他の割り当てが同じ種別・番号を使わないことを示す。
pub proof fn controller_is_unique(board: Board, input: Seq<Assignment>, row: int, device: (Controller, u8))
    requires
        assignments_valid(board, input),
        0 <= row < input.len(),
        assignment_controller(input[row]) == Some(device),
    ensures
        device.1 <= 1,
        forall|other: int| 0 <= other < input.len() && other != row
            ==> #[trigger] assignment_controller(input[other]) != Some(device),
{
    assert(valid_assignment(board, input, row));
    assert(controller_error(input, row) is None);
    assert forall|other: int| 0 <= other < input.len() && other != row
        implies #[trigger] assignment_controller(input[other]) != Some(device) by {
        if assignment_controller(input[other]) == Some(device) {
            let (first, last) = if other < row { (other, row) } else { (row, other) };
            assert(first < last);
            assert(assignment_controller(input[first]) == Some(device));
            assert(assignment_controller(input[last]) == Some(device));
            assert(first_controller(input, last, device) is Some);
            assert(valid_assignment(board, input, last));
            assert(controller_error(input, last) is None);
        }
    };
}

impl<'a> CheckedAssignments<'a> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        assignments_valid(self.board, self.input@)
    }

    /// 検査に用いたボードを表す。
    pub closed spec fn board_model(&self) -> Board { self.board }

    /// 入力順で保持した割り当てを表す。
    pub closed spec fn assignments_model(&self) -> Seq<Assignment> { self.input@ }

    /// 選択したボードを返す。
    pub fn board(&self) -> (board: Board)
        ensures board == self.board_model(),
    { self.board }

    /// 検査した割り当てを元の順で返す。
    pub fn assignments(&self) -> (assignments: &'a [Assignment])
        ensures assignments@ == self.assignments_model(), assignments_valid(self.board_model(), assignments@),
    {
        proof { use_type_invariant(self); }
        self.input
    }
}

/// Pico または Pico 2 のピンと周辺機能の割り当てを検査する。
///
/// # Errors
///
/// 入力順に、周辺機能の番号、同一周辺機能の重複、各信号を検査する。
/// 信号の順は UART が TX・RX、SPI がクロック・MOSI・MISO・CS、I²C が SDA・SCL。
/// 各信号ではピンの露出、機能の適合、ピンの重複を順に検査する。
pub fn check_assignments<'a>(board: Board, input: &'a [Assignment])
    -> (result: Result<CheckedAssignments<'a>, AssignmentError>)
    ensures
        result.is_ok() <==> assignments_valid(board, input@),
        match result {
            Ok(checked) => checked.board_model() == board && checked.assignments_model() == input@,
            Err(error) => first_assignment_error(board, input@, error),
        },
{
    let mut i = 0;
    while i < input.len()
        invariant i <= input@.len(), forall|k: int| 0 <= k < i ==> #[trigger] valid_assignment(board, input@, k),
        decreases input@.len() - i,
    {
        if let Some(error) = check_controller(input, i) {
            assert(!valid_assignment(board, input@, i as int));
            assert(first_assignment_error(board, input@, error));
            return Err(error);
        }
        let instance = match controller(input[i]) { Some(value) => value.1, None => 0 };
        let (group, count) = pins(input[i]);
        let mut j = 0;
        while j < count
            invariant
                i < input@.len(), count <= 4, group@.take(count as int) == assignment_pins(input@[i as int]),
                j <= count, controller_error(input@, i as int) is None,
                instance == match assignment_controller(input@[i as int]) { Some(value) => value.1, None => 0 },
                forall|k: int| 0 <= k < i ==> #[trigger] valid_assignment(board, input@, k),
                forall|p: int| 0 <= p < j ==> #[trigger] pin_error(board, input@, i as int, p) is None,
            decreases count - j,
        {
            let (signal, pin) = group[j];
            assert(assignment_pins(input@[i as int])[j as int] == (signal, pin));
            let site = PinSite { assignment: i, signal };
            let error = if !exposed(pin) {
                Some(AssignmentError::UnexposedPin { site, pin })
            } else if !supported(board, instance, signal, pin) {
                Some(AssignmentError::UnsupportedSignal { site, pin, instance })
            } else {
                match find_pin(input, i, j, pin) {
                    Some(first) => Some(AssignmentError::DuplicatePin { first, site, pin }),
                    None => None,
                }
            };
            assert(error == pin_error(board, input@, i as int, j as int));
            if let Some(error) = error {
                assert(!valid_assignment(board, input@, i as int));
                assert(first_assignment_error(board, input@, error));
                return Err(error);
            }
            j += 1;
        }
        assert(valid_assignment(board, input@, i as int));
        i += 1;
    }
    assert(assignments_valid(board, input@));
    Ok(CheckedAssignments { board, input })
}

/// 同じ設定で最初の違反と認められる診断の値は一つに定まる。
pub proof fn assignment_errors_agree(board: Board, input: Seq<Assignment>, left: AssignmentError, right: AssignmentError)
    requires first_assignment_error(board, input, left), first_assignment_error(board, input, right),
    ensures left == right,
{
    let i = choose|i: int| 0 <= i < input.len() && !#[trigger] valid_assignment(board, input, i)
        && (forall|prior: int| 0 <= prior < i ==> #[trigger] valid_assignment(board, input, prior))
        && (controller_error(input, i) == Some(left) || controller_error(input, i) is None
            && exists|j: int| 0 <= j < assignment_pins(input[i]).len() && #[trigger] pin_error(board, input, i, j) == Some(left)
                && (forall|prior: int| 0 <= prior < j ==> #[trigger] pin_error(board, input, i, prior) is None));
    let other = choose|i: int| 0 <= i < input.len() && !#[trigger] valid_assignment(board, input, i)
        && (forall|prior: int| 0 <= prior < i ==> #[trigger] valid_assignment(board, input, prior))
        && (controller_error(input, i) == Some(right) || controller_error(input, i) is None
            && exists|j: int| 0 <= j < assignment_pins(input[i]).len() && #[trigger] pin_error(board, input, i, j) == Some(right)
                && (forall|prior: int| 0 <= prior < j ==> #[trigger] pin_error(board, input, i, prior) is None));
    assert(i == other) by {
        if i < other { assert(valid_assignment(board, input, i)); }
        if other < i { assert(valid_assignment(board, input, other)); }
    };
    if controller_error(input, i) is None {
        let j = choose|j: int| 0 <= j < assignment_pins(input[i]).len() && #[trigger] pin_error(board, input, i, j) == Some(left)
            && (forall|prior: int| 0 <= prior < j ==> #[trigger] pin_error(board, input, i, prior) is None);
        let other_j = choose|j: int| 0 <= j < assignment_pins(input[i]).len() && #[trigger] pin_error(board, input, i, j) == Some(right)
            && (forall|prior: int| 0 <= prior < j ==> #[trigger] pin_error(board, input, i, prior) is None);
        assert(j == other_j) by {
            if j < other_j { assert(pin_error(board, input, i, j) is None); }
            if other_j < j { assert(pin_error(board, input, i, other_j) is None); }
        };
    }
}

} // verus!
