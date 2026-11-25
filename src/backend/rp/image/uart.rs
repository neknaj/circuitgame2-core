//! UART と GPIO の名前付き接続を、同じ回路の配線表に落とす。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{
    Assignment, Board, DevicePortRequest, DevicePortType, GpioBinding,
    GpioImageError, GpioOutputPin, ModuleBodyPosition, PackedNorLayout32, PortDirection, UseAliases,
    append_outputs, check_assignments, input_pin, requests,
};
#[cfg(verus_only)]
use super::{DevicePortBinding, gpio_assignment, gpio_binding_indices_match, gpio_request, input_at, outputs_before};

verus! {

const UART_INPUTS: usize = 14;
const UART_OUTPUTS: usize = 11;
const UART_PORTS: usize = UART_INPUTS + UART_OUTPUTS;

/// 一系統の 8N1 UART に割り当てるボードの周辺機能と端子。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UartSetup {
    /// UART0 または UART1 の番号。
    pub instance: u8,
    /// ボードの UART 送信ピン。
    pub tx: u8,
    /// ボードの UART 受信ピン。
    pub rx: u8,
    /// 1秒あたりに転送するビット数。
    pub baud: u32,
}

/// ルート回路に接続する UART の単一ビットポート名。
#[derive(Clone, Copy, Debug)]
pub struct UartPortNames<'n> {
    /// 受信データの各ビットを駆動する入力名。最下位ビットから並べる。
    pub rx_data: [&'n str; 8],
    /// 受信イベントがあることを示す入力名。
    pub rx_valid: &'n str,
    /// 受信イベントがフレーミングエラーであることを示す入力名。
    pub rx_framing: &'n str,
    /// 受信イベントがあふれを示す入力名。
    pub rx_overrun: &'n str,
    /// 受信イベントをその tick で取り込むことを示す出力名。
    pub rx_ready: &'n str,
    /// 送信するデータの各ビットを読む出力名。最下位ビットから並べる。
    pub tx_data: [&'n str; 8],
    /// 送信要求があることを示す出力名。
    pub tx_valid: &'n str,
    /// その tick で送信要求を受け付けられることを示す入力名。
    pub tx_ready: &'n str,
    /// 送信結果を保持していることを示す入力名。
    pub tx_done: &'n str,
    /// 送信が成功したことを示す入力名。送信結果を保持しているときに有効。
    pub tx_ok: &'n str,
    /// 送信結果をその tick で取り込むことを示す出力名。
    pub tx_done_ready: &'n str,
}

/// UART の接続側が駆動する回路入力の信号。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UartInputSignal {
    /// 受信データの指定ビット。
    RxBit(u8),
    /// 受信イベントの有効ビット。
    RxValid,
    /// 受信時のフレーミングエラー。
    RxFraming,
    /// 受信のあふれ。
    RxOverrun,
    /// 新規の送信要求を受け付ける準備ができたこと。
    TxReady,
    /// 送信の結果を保持していること。
    TxDone,
    /// 保持中の送信結果が成功だったこと。
    TxOk,
}

/// 宣言順の一つの回路入力を駆動する接続先。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RpInputSource {
    /// GPIO ヘッダー上のピン番号。
    Gpio(u8),
    /// UART の受信、送信準備または送信結果の信号。
    Uart(UartInputSignal),
}

/// UART が読む公開出力の宣言順の添字。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UartOutputPorts {
    /// 受信イベントの受け取り可否。
    pub rx_ready: usize,
    /// 最下位を先頭にした送信データ。
    pub tx_data: [usize; 8],
    /// 送信要求の有効ビット。
    pub tx_valid: usize,
    /// 送信結果の受け取り可否。
    pub tx_done_ready: usize,
}

/// 同じルートから組み立てた配線、GPIO 接続、UART 接続、周期。
pub struct UartCircuitImage {
    board: Board,
    layout: PackedNorLayout32,
    inputs: Vec<RpInputSource>,
    gpio_outputs: Vec<GpioOutputPin>,
    uart: UartSetup,
    uart_outputs: UartOutputPorts,
    tick_micros: u64,
}

/// UART を含む配線の設定または構築時のエラー。
#[derive(Debug)]
pub enum UartImageError<'p, 'a, 'n> {
    /// ボーレートとして0が指定された。
    ZeroBaud,
    /// ピンやポート、回路の構築時に起きた診断。
    Circuit(GpioImageError<'p, 'a, 'n>),
}

impl UartCircuitImage {
    /// 対象ボードと、GPIO/UART の物理割り当ての検査先を表す。
    pub closed spec fn board_model(&self) -> Board { self.board }
    /// ルート回路のパック済み配線を表す。
    pub closed spec fn layout_model(&self) -> PackedNorLayout32 { self.layout }
    /// 宣言順の入力を駆動する接続の列。
    pub closed spec fn inputs_model(&self) -> Seq<RpInputSource> { self.inputs@ }
    /// 公開出力から GPIO に反映する接続の列。
    pub closed spec fn gpio_outputs_model(&self) -> Seq<GpioOutputPin> { self.gpio_outputs@ }
    /// UART の周辺機能番号、端子、通信速度。
    pub closed spec fn uart_model(&self) -> UartSetup { self.uart }
    /// UART が読む出力の宣言順の添字。
    pub closed spec fn uart_outputs_model(&self) -> UartOutputPorts { self.uart_outputs }
    /// 1 tick の周期をマイクロ秒で表した値。
    pub closed spec fn tick_micros_model(&self) -> u64 { self.tick_micros }

    /// 対象ボードを返す。
    pub fn board(&self) -> (board: Board) ensures board == self.board_model() { self.board }
    /// 同じ回路の配線配置を返す。
    pub fn layout(&self) -> (layout: &PackedNorLayout32) ensures *layout == self.layout_model() { &self.layout }
    /// 入口の名前を照合した GPIO または UART の入力源を、宣言順で返す。
    pub fn inputs(&self) -> (inputs: &[RpInputSource]) ensures inputs@ == self.inputs_model() { self.inputs.as_slice() }
    /// GPIO の出力先を宣言順で返す。同じ出力を読む接続は設定順で並ぶ。
    pub fn gpio_outputs(&self) -> (outputs: &[GpioOutputPin]) ensures outputs@ == self.gpio_outputs_model() {
        self.gpio_outputs.as_slice()
    }
    /// UART に割り当てた周辺機能とピン、および通信速度を返す。
    pub fn uart(&self) -> (uart: UartSetup) ensures uart == self.uart_model() { self.uart }
    /// UART の読み取り先を公開出力の添字で返す。
    pub fn uart_outputs(&self) -> (outputs: UartOutputPorts) ensures outputs == self.uart_outputs_model() { self.uart_outputs }
    /// 1 tick の周期をマイクロ秒で返す。
    pub fn tick_micros(&self) -> (micros: u64) ensures micros == self.tick_micros_model() { self.tick_micros }
}

// 前半を回路入力、後半を回路出力にする。ビット列は低位側から並べる。
spec fn named_uart_port(names: UartPortNames, i: int) -> &str {
    if i < 8 { names.rx_data@[i] }
    else if i == 8 { names.rx_valid }
    else if i == 9 { names.rx_framing }
    else if i == 10 { names.rx_overrun }
    else if i == 11 { names.tx_ready }
    else if i == 12 { names.tx_done }
    else if i == 13 { names.tx_ok }
    else if i == 14 { names.rx_ready }
    else if i < 23 { names.tx_data@[i - 15] }
    else if i == 23 { names.tx_valid }
    else { names.tx_done_ready }
}

spec fn uart_request(names: UartPortNames, i: int) -> DevicePortRequest {
    DevicePortRequest { direction: if i < UART_INPUTS { PortDirection::Output } else { PortDirection::Input },
        circuit_port: named_uart_port(names, i), expected: DevicePortType::Bits(1) }
}

fn request_at<'n>(names: UartPortNames<'n>, i: usize) -> (request: DevicePortRequest<'n>)
    requires i < UART_PORTS,
    ensures request == uart_request(names, i as int),
{
    let direction = if i < UART_INPUTS { PortDirection::Output } else { PortDirection::Input };
    let port = match i {
        0..=7 => names.rx_data[i],
        8 => names.rx_valid,
        9 => names.rx_framing,
        10 => names.rx_overrun,
        11 => names.tx_ready,
        12 => names.tx_done,
        13 => names.tx_ok,
        14 => names.rx_ready,
        15..=22 => names.tx_data[i - 15],
        23 => names.tx_valid,
        _ => names.tx_done_ready,
    };
    DevicePortRequest { direction, circuit_port: port, expected: DevicePortType::Bits(1) }
}

/// 混在する接続で行う名前照会の順序を表す。
pub closed spec fn uart_image_requests<'n>(gpio: Seq<GpioBinding<'n>>, names: UartPortNames<'n>) -> Seq<DevicePortRequest<'n>> {
    gpio.map_values(|binding: GpioBinding| gpio_request(binding))
        + Seq::new(UART_PORTS as nat, |i: int| uart_request(names, i))
}

/// UART に割り当てる周辺機能と物理ピンを表す。
pub open spec fn uart_assignment(uart: UartSetup) -> Assignment {
    Assignment::Uart { instance: uart.instance, tx: uart.tx, rx: uart.rx }
}

fn mixed_requests<'n>(gpio: &[GpioBinding<'n>], setup: UartSetup, names: UartPortNames<'n>)
    -> (result: (Vec<Assignment>, Vec<DevicePortRequest<'n>>))
    ensures
        result.0@ == gpio@.map_values(|binding: GpioBinding| gpio_assignment(binding)).push(uart_assignment(setup)),
        result.1@ == uart_image_requests(gpio@, names),
{
    let (mut assignments, mut requests) = requests(gpio);
    assignments.push(Assignment::Uart { instance: setup.instance, tx: setup.tx, rx: setup.rx });
    let ghost base = requests@;
    let mut i = 0;
    while i < UART_PORTS
        invariant i <= UART_PORTS,
            requests@ == base + Seq::new(i as nat, |j: int| uart_request(names, j)),
        decreases UART_PORTS - i,
    {
        requests.push(request_at(names, i));
        assert(requests@ =~= base + Seq::new((i + 1) as nat, |j: int| uart_request(names, j)));
        i += 1;
    }
    (assignments, requests)
}

spec fn uart_signal(i: int) -> UartInputSignal {
    if i < 8 { UartInputSignal::RxBit(i as u8) }
    else if i == 8 { UartInputSignal::RxValid }
    else if i == 9 { UartInputSignal::RxFraming }
    else if i == 10 { UartInputSignal::RxOverrun }
    else if i == 11 { UartInputSignal::TxReady }
    else if i == 12 { UartInputSignal::TxDone }
    else { UartInputSignal::TxOk }
}

fn signal_at(i: usize) -> (signal: UartInputSignal)
    requires i < UART_INPUTS,
    ensures signal == uart_signal(i as int),
{
    match i {
        0..=7 => UartInputSignal::RxBit(i as u8),
        8 => UartInputSignal::RxValid,
        9 => UartInputSignal::RxFraming,
        10 => UartInputSignal::RxOverrun,
        11 => UartInputSignal::TxReady,
        12 => UartInputSignal::TxDone,
        _ => UartInputSignal::TxOk,
    }
}

spec fn is_uart_index(indices: Seq<usize>, offset: usize, port: usize, i: int) -> bool {
    0 <= i < UART_INPUTS && indices[offset as int + i] == port
}

spec fn uart_input_at(indices: Seq<usize>, offset: usize, port: usize) -> Option<UartInputSignal> {
    if exists|i: int| #[trigger] is_uart_index(indices, offset, port, i) {
        let first = choose|i: int| #[trigger] is_uart_index(indices, offset, port, i)
            && forall|j: int| 0 <= j < i ==> !#[trigger] is_uart_index(indices, offset, port, j);
        Some(uart_signal(first))
    } else { None }
}

fn uart_input(indices: &[usize], offset: usize, port: usize) -> (signal: Option<UartInputSignal>)
    requires offset as int + UART_INPUTS <= indices.len(),
    ensures signal == uart_input_at(indices@, offset, port),
{
    let mut i = 0;
    while i < UART_INPUTS
        invariant i <= UART_INPUTS, offset as int + UART_INPUTS <= indices.len(),
            forall|j: int| 0 <= j < i ==> !#[trigger] is_uart_index(indices@, offset, port, j),
        decreases UART_INPUTS - i,
    {
        if indices[offset + i] == port {
            proof {
                assert(is_uart_index(indices@, offset, port, i as int));
                let first = choose|j: int| #[trigger] is_uart_index(indices@, offset, port, j)
                    && forall|k: int| 0 <= k < j ==> !#[trigger] is_uart_index(indices@, offset, port, k);
                if first < i { assert(!is_uart_index(indices@, offset, port, first)); }
                if i < first { assert(!is_uart_index(indices@, offset, port, i as int)); }
                assert(first == i);
            }
            return Some(signal_at(i));
        }
        assert(!is_uart_index(indices@, offset, port, i as int));
        i += 1;
    }
    None
}

spec fn source_of_input(gpio: Seq<GpioBinding>, indices: Seq<usize>, port: usize) -> Option<RpInputSource> {
    match input_at(gpio, indices, port) {
        Some(pin) => Some(RpInputSource::Gpio(pin)),
        None => match uart_input_at(indices, gpio.len() as usize, port) {
            Some(signal) => Some(RpInputSource::Uart(signal)),
            None => None,
        },
    }
}

spec fn output_ports_match(outputs: UartOutputPorts, indices: Seq<usize>, offset: usize) -> bool {
    &&& outputs.rx_ready == indices[offset as int]
    &&& forall|i: int| 0 <= i < 8 ==> (#[trigger] outputs.tx_data@[i]) == indices[offset as int + 1 + i]
    &&& outputs.tx_valid == indices[offset as int + 9]
    &&& outputs.tx_done_ready == indices[offset as int + 10]
}

fn uart_outputs(indices: &[usize], i: usize) -> (outputs: UartOutputPorts)
    requires i as int + UART_OUTPUTS <= indices@.len(),
    ensures output_ports_match(outputs, indices@, i),
{
    UartOutputPorts { rx_ready: indices[i],
        tx_data: [indices[i + 1], indices[i + 2], indices[i + 3], indices[i + 4],
            indices[i + 5], indices[i + 6], indices[i + 7], indices[i + 8]],
        tx_valid: indices[i + 9], tx_done_ready: indices[i + 10] }
}

/// UART が読む添字は、すべて公開出力の範囲に入る。
pub open spec fn uart_output_indices_fit(outputs: UartOutputPorts, port_count: nat) -> bool {
    &&& outputs.rx_ready < port_count
    &&& outputs.tx_valid < port_count
    &&& outputs.tx_done_ready < port_count
    &&& forall|i: int| 0 <= i < 8 ==> (#[trigger] outputs.tx_data@[i]) < port_count
}

/// 宣言順の各回路入力、GPIO 出力、UART 出力の添字が、名前解決結果と一致する。
pub closed spec fn uart_image_ports_match(image: &UartCircuitImage, gpio: Seq<GpioBinding>, indices: Seq<usize>) -> bool {
    &&& indices.len() == gpio.len() + UART_PORTS
    &&& gpio.len() + UART_PORTS <= usize::MAX
    &&& image.inputs_model().len() == image.layout_model().input_model()
    &&& forall|i: int| 0 <= i < image.inputs_model().len() ==>
        source_of_input(gpio, indices, i as usize) == Some(#[trigger] image.inputs_model()[i])
    &&& output_ports_match(image.uart_outputs_model(), indices, (gpio.len() + UART_INPUTS) as usize)
    &&& image.gpio_outputs_model() == outputs_before(gpio, indices, image.layout_model().outputs_model().len())
}

fn assemble_uart_image<'p, 'a, 'n>(
    board: Board, gpio: &[GpioBinding<'n>], indices: &[usize], layout: PackedNorLayout32, setup: UartSetup, tick_micros: u64,
) -> (result: Result<UartCircuitImage, GpioImageError<'p, 'a, 'n>>)
    requires indices.len() as int == gpio.len() as int + UART_PORTS,
    ensures match result {
        Ok(image) => image.board_model() == board && image.layout_model() == layout
            && image.uart_model() == setup && image.tick_micros_model() == tick_micros
            && uart_image_ports_match(&image, gpio@, indices@),
        Err(GpioImageError::MissingInput { port }) => port < layout.input_model()
            && source_of_input(gpio@, indices@, port).is_none()
            && forall|j: usize| j < port ==> #[trigger] source_of_input(gpio@, indices@, j).is_some(),
        _ => false,
    },
{
    let input_count = layout.input_count();
    let mut inputs = Vec::new();
    let mut i = 0;
    while i < input_count
        invariant i == inputs@.len() <= input_count == layout.input_model(),
            indices@.len() == gpio@.len() + UART_PORTS,
            forall|j: int| 0 <= j < i ==> source_of_input(gpio@, indices@, j as usize) == Some(#[trigger] inputs@[j]),
        decreases input_count - i,
    {
        let source = if let Some(pin) = input_pin(gpio, indices, i) { RpInputSource::Gpio(pin) }
            else if let Some(signal) = uart_input(indices, gpio.len(), i) { RpInputSource::Uart(signal) }
            else {
                assert forall|j: usize| j < i implies #[trigger] source_of_input(gpio@, indices@, j).is_some() by {
                    assert(source_of_input(gpio@, indices@, j) == Some(inputs@[j as int]));
                };
                return Err(GpioImageError::MissingInput { port: i });
            };
        inputs.push(source);
        i += 1;
    }
    let mut gpio_outputs = Vec::new();
    let output_count = layout.outputs().len();
    let mut i = 0;
    while i < output_count
        invariant i <= output_count == layout.outputs_model().len(), indices@.len() == gpio@.len() + UART_PORTS,
            gpio_outputs@ == outputs_before(gpio@, indices@, i as nat),
        decreases output_count - i,
    {
        append_outputs(gpio, indices, i, &mut gpio_outputs);
        assert(outputs_before(gpio@, indices@, (i + 1) as nat) == gpio_outputs@);
        i += 1;
    }
    assert(gpio.len() as int + UART_PORTS <= usize::MAX);
    let uart_outputs = uart_outputs(indices, gpio.len() + UART_INPUTS);
    Ok(UartCircuitImage { board, layout, inputs, gpio_outputs, uart: setup, uart_outputs, tick_micros })
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// ルートの単一ビットポートを GPIO と UART のどちらで駆動するかを検査し、配線を組み立てる。
    ///
    /// 受信イベントと送信結果を示す有効ビットは、回路の対応する準備完了まで保持する入口に接続する。
    /// GPIO と UART が同じ入力に接続する指定は、他の重複駆動と同じ規則で拒否する。
    ///
    /// # Errors
    ///
    /// 周期とボーレート、物理ピン、名前と型、回路変換、入力の未割り当ての順で診断する。
    pub fn build_rp_uart_image<'n>(
        &self, owner: ModuleBodyPosition, board: Board, gpio: &[GpioBinding<'n>], setup: UartSetup, names: UartPortNames<'n>,
        tick_micros: u64, width_limit: u64, bit_limit: usize, gate_limit: usize,
    ) -> (result: Result<UartCircuitImage, UartImageError<'p, 'a, 'n>>)
        requires self.can_resolve(),
        ensures
            result matches Ok(image) ==> {
                &&& image.board_model() == board && image.uart_model() == setup && image.tick_micros_model() == tick_micros
                &&& tick_micros > 0 && setup.baud > 0
                &&& image.inputs_model().len() == image.layout_model().input_model()
                &&& uart_output_indices_fit(image.uart_outputs_model(), image.layout_model().outputs_model().len())
                &&& image.layout_model().source_model() <= u32::MAX
                &&& image.layout_model().gates_model().len() <= gate_limit
                &&& image.layout_model().input_model() <= bit_limit
                &&& image.layout_model().outputs_model().len() <= bit_limit
                &&& super::super::assignments_valid(board,
                    gpio@.map_values(|binding: GpioBinding| gpio_assignment(binding)).push(uart_assignment(setup)))
                &&& exists|netlist: crate::netlist::NorNetlist| #[trigger] image.layout_model().matches(&netlist)
                    && self.clocked_module_source_layout(owner, width_limit, &netlist)
                &&& exists|resolved: Vec<DevicePortBinding>, indices: Seq<usize>|
                    #[trigger] uart_image_ports_match(&image, gpio@, indices)
                    && self.device_bindings_match(owner, width_limit, uart_image_requests(gpio@, names), Ok(resolved))
                    && #[trigger] gpio_binding_indices_match(resolved@, indices)
                    && (forall|i: int, j: int| 0 <= i < j < indices.len()
                        && uart_image_requests(gpio@, names)[i].direction is Output
                        && uart_image_requests(gpio@, names)[j].direction is Output
                        ==> (#[trigger] indices[i]) != (#[trigger] indices[j]))
            },
            result matches Err(UartImageError::Circuit(GpioImageError::Binding(error))) ==>
                self.device_bindings_match(owner, width_limit, uart_image_requests(gpio@, names), Err(error)),
    {
        if tick_micros == 0 { return Err(UartImageError::Circuit(GpioImageError::ZeroTickPeriod)); }
        if setup.baud == 0 { return Err(UartImageError::ZeroBaud); }
        let (assignments, requests) = mixed_requests(gpio, setup, names);
        if let Err(error) = check_assignments(board, &assignments) {
            return Err(UartImageError::Circuit(GpioImageError::Pin(error)));
        }
        let (layout, indices) = match self.lower_rp_ports(owner, &requests, width_limit, bit_limit, gate_limit) {
            Ok(pair) => pair,
            Err(error) => return Err(UartImageError::Circuit(error)),
        };
        assert(indices@.len() == gpio@.len() + UART_PORTS);
        match assemble_uart_image(board, gpio, &indices, layout, setup, tick_micros) {
            Ok(image) => {
                proof {
                    assert forall|i: int| gpio@.len() + UART_INPUTS <= i < indices@.len()
                        implies #[trigger] indices@[i] < layout.outputs_model().len() by {
                        assert(requests@[i] == uart_request(names, i - gpio@.len()));
                        assert(requests@[i].direction is Input);
                    };
                }
                Ok(image)
            },
            Err(error) => Err(UartImageError::Circuit(error)),
        }
    }
}

} // verus!
