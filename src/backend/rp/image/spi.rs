//! SPI と GPIO の接続を検査し、回路の配線表を作る。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{
    Assignment, Board, GpioBinding, GpioImageError, GpioOutputPin, ModuleBodyPosition,
    PackedNorLayout32, SpiBitOrder, UseAliases, check_assignments, requests,
};
use super::peripheral::{
    PeripheralInputSource, append_port_requests, port_capacity, project_ports,
};
#[cfg(verus_only)]
use super::{DevicePortBinding, DevicePortRequest, gpio_assignment, gpio_binding_indices_match};
#[cfg(verus_only)]
use super::peripheral::{
    missing_input, peripheral_image_requests, peripheral_output_direction, peripheral_port_bounds,
    peripheral_port_capacity, peripheral_ports_match,
};

verus! {

const TO_CIRCUIT_HEADER: usize = 5;
const FROM_CIRCUIT_HEADER: usize = 10;

/// RP に接続する SPI コントローラーの設定。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpiSetup {
    /// SPI0 または SPI1 の番号。
    pub instance: u8,
    /// SCK の GP 番号。
    pub sck: u8,
    /// MOSI の GP 番号。
    pub mosi: u8,
    /// MISO の GP 番号。
    pub miso: u8,
    /// active-low の GPIO CS の GP 番号。
    pub cs: u8,
    /// 通信周波数の要求値。ヘルツで指定する。
    pub frequency_hz: u32,
    /// クロック極性と位相を表すモード。0から3まで。
    pub mode: u8,
    /// 各バイトを線上へ送受信する順序。
    pub bit_order: SpiBitOrder,
    /// 1取引の待ち時間。マイクロ秒で指定する。
    pub timeout_micros: u32,
}

/// 回路の単一ビットポート名を SPI の信号順に並べた指定。
///
/// 状態、長さ、データの各バイトは最下位ビットから順に並べる。
/// 送受信データはバイトの転送順に並べ、両方向に同じ容量を確保する。
/// `SpiSetup::bit_order` は線上での各バイトの順序を選ぶ。
#[derive(Clone, Copy, Debug)]
pub struct SpiPortNames<'n> {
    /// 要求 ready、応答 valid、状態3ビット、受信データの順。
    pub to_circuit: &'n [&'n str],
    /// 要求 valid、応答 ready、送受信のバイト数8ビット、送信データの順。
    pub from_circuit: &'n [&'n str],
}

/// SPI 固有の設定を受理できない理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpiSettingError {
    /// 指定モードが0から3の範囲外。
    Mode,
    /// 既定の周辺クロックと分周器が扱える範囲外。
    Frequency,
    /// 待ち時間が0マイクロ秒。
    ZeroTimeout,
    /// 必須信号の不足、または送受信の容量が一致しないか範囲外。
    PortCounts,
    /// 設定の接続数をホストの添字で表せない。
    BindingCount,
}

/// SPI を接続した RP 向けの配線表を作れなかった理由。
#[derive(Debug)]
pub enum SpiImageError<'p, 'a, 'n> {
    /// SPI の通信設定またはポート列の構造が不正。
    Setting(SpiSettingError),
    /// ボードのピン、回路側のポート、または配線の検査で起きた診断。
    Circuit(GpioImageError<'p, 'a, 'n>),
}

/// 一つのルート回路を駆動する SPI と GPIO の配線表。
pub struct SpiCircuitImage {
    board: Board,
    layout: PackedNorLayout32,
    setup: SpiSetup,
    tick_micros: u64,
    capacity: u8,
    inputs: Vec<PeripheralInputSource>,
    gpio_outputs: Vec<GpioOutputPin>,
    spi_outputs: Vec<usize>,
}

impl SpiCircuitImage {
    /// ボード、通信、周期、バイト容量の仕様上の値。
    pub closed spec fn setup_model(&self) -> (Board, SpiSetup, u64, u8) {
        (self.board, self.setup, self.tick_micros, self.capacity)
    }

    /// 回路を展開した32レーン配線。
    pub closed spec fn layout_model(&self) -> PackedNorLayout32 { self.layout }

    /// 回路入力の各駆動元と、GPIO・SPI が読む回路出力。
    pub closed spec fn port_model(&self) -> (Seq<PeripheralInputSource>, Seq<GpioOutputPin>, Seq<usize>) {
        (self.inputs@, self.gpio_outputs@, self.spi_outputs@)
    }

    /// ボード、通信設定、tick 周期のマイクロ秒数、送受信のバイト容量を返す。
    pub fn setup(&self) -> (setup: (Board, SpiSetup, u64, u8))
        ensures setup == self.setup_model(),
    { (self.board, self.setup, self.tick_micros, self.capacity) }

    /// 配線番号を確定した回路を返す。
    pub fn layout(&self) -> (layout: &PackedNorLayout32)
        ensures *layout == self.layout_model(),
    { &self.layout }

    /// 入力元は宣言順、GPIO 出力は宣言順と設定順、SPI 出力は指定した信号順で返す。
    pub fn ports(&self) -> (ports: (&[PeripheralInputSource], &[GpioOutputPin], &[usize]))
        ensures (ports.0@, ports.1@, ports.2@) == self.port_model(),
    { (self.inputs.as_slice(), self.gpio_outputs.as_slice(), self.spi_outputs.as_slice()) }
}

/// 既定のボードクロックと PL022 の偶数分周・直列分周で扱える周波数を表す。
///
/// SDK に渡す要求値の範囲を示す。実際の周波数は用いる分周比で決まる。
pub open spec fn spi_frequency_supported(board: Board, frequency: u32) -> bool {
    let clk = if board is Pico { 125_000_000int } else { 150_000_000int };
    2 * (frequency as int) <= clk && clk <= 65_024 * (frequency as int)
}

/// 既定の周辺クロックで設定できる SPI 周波数の最小値と最大値を返す。
///
/// 両端を含む。実際の周波数はこの範囲で選んだ要求値と同じとは限らない。
pub fn spi_frequency_range(board: Board) -> (range: (u32, u32))
    ensures forall|frequency: u32| #[trigger] spi_frequency_supported(board, frequency) <==>
        range.0 <= frequency <= range.1,
{
    // ファームウェアの既定 clk_peri は Embassy RP 0.10 の crystal(12 MHz) による。
    // PL022 の二段分周は 2 * [1..=127] * [1..=256]。
    let range = match board {
        Board::Pico => (1_923, 62_500_000),
        Board::Pico2 => (2_307, 75_000_000),
    };
    assert forall|frequency: u32| #[trigger] spi_frequency_supported(board, frequency)
        <==> range.0 <= frequency <= range.1 by {
        assert(spi_frequency_supported(board, frequency) == {
            let clk = if board is Pico { 125_000_000int } else { 150_000_000int };
            2 * (frequency as int) <= clk && clk <= 65_024 * (frequency as int)
        });
    };
    range
}

/// 送受信データの配線が同じ容量の全バイトを表す。
pub closed spec fn spi_port_capacity(to: int, from: int, bytes: int) -> bool {
    peripheral_port_capacity(to, from, TO_CIRCUIT_HEADER as int, FROM_CIRCUIT_HEADER as int, bytes)
}

/// SCK、MOSI、MISO と GPIO の CS を SPI コントローラーに割り当てる。
pub open spec fn spi_assignment(setup: SpiSetup) -> Assignment {
    Assignment::Spi { instance: setup.instance, clock: setup.sck, mosi: setup.mosi,
        miso: setup.miso, select: setup.cs }
}

/// GPIO、回路入力、回路出力の順でポート照会を並べる。
pub closed spec fn spi_image_requests<'n>(gpio: Seq<GpioBinding<'n>>, names: SpiPortNames<'n>) -> Seq<DevicePortRequest<'n>> {
    peripheral_image_requests(gpio, names.to_circuit@, names.from_circuit@)
}

/// モード、周波数、待ち時間、ポート数、添字上限の順で最初の設定エラーを選ぶ。
pub closed spec fn spi_setting_error(board: Board, setup: SpiSetup, gpio_count: nat, names: SpiPortNames)
    -> Option<SpiSettingError>
{
    if setup.mode > 3 { Some(SpiSettingError::Mode) }
    else if !spi_frequency_supported(board, setup.frequency_hz) { Some(SpiSettingError::Frequency) }
    else if setup.timeout_micros == 0 { Some(SpiSettingError::ZeroTimeout) }
    else if !(exists|bytes: int| spi_port_capacity(names.to_circuit@.len() as int, names.from_circuit@.len() as int, bytes)) {
        Some(SpiSettingError::PortCounts)
    } else if gpio_count + names.to_circuit@.len() + names.from_circuit@.len() > usize::MAX {
        Some(SpiSettingError::BindingCount)
    } else { None }
}

fn checked_capacity(board: Board, setup: SpiSetup, gpio_count: usize, names: SpiPortNames)
    -> (result: Result<(u8, usize), SpiSettingError>)
    ensures
        result.is_ok() <==> spi_setting_error(board, setup, gpio_count as nat, names).is_none(),
        result matches Err(error) ==> spi_setting_error(board, setup, gpio_count as nat, names) == Some(error),
        result matches Ok((capacity, split)) ==>
            spi_port_capacity(names.to_circuit@.len() as int, names.from_circuit@.len() as int, capacity as int)
            && split == gpio_count + names.to_circuit@.len()
            && split + names.from_circuit@.len() <= usize::MAX,
{
    if setup.mode > 3 { return Err(SpiSettingError::Mode); }
    let (lowest, highest) = spi_frequency_range(board);
    if setup.frequency_hz < lowest || setup.frequency_hz > highest {
        return Err(SpiSettingError::Frequency);
    }
    assert(spi_frequency_supported(board, setup.frequency_hz));
    if setup.timeout_micros == 0 { return Err(SpiSettingError::ZeroTimeout); }
    let Some(capacity) = port_capacity(names.to_circuit.len(), names.from_circuit.len(), TO_CIRCUIT_HEADER, FROM_CIRCUIT_HEADER) else {
        return Err(SpiSettingError::PortCounts);
    };
    assert(spi_port_capacity(names.to_circuit@.len() as int, names.from_circuit@.len() as int, capacity as int));
    assert(exists|bytes: int| spi_port_capacity(names.to_circuit@.len() as int, names.from_circuit@.len() as int, bytes));
    let Some(split) = gpio_count.checked_add(names.to_circuit.len()) else { return Err(SpiSettingError::BindingCount); };
    if split.checked_add(names.from_circuit.len()).is_none() { return Err(SpiSettingError::BindingCount); }
    Ok((capacity, split))
}

/// 入力駆動元と出力ポート番号が、名前を解決した配線表に対応する。
pub closed spec fn spi_image_ports_match(
    image: &SpiCircuitImage, gpio: Seq<GpioBinding>, names: SpiPortNames, indices: Seq<usize>,
) -> bool {
    peripheral_ports_match(image.port_model(), gpio, names.to_circuit@.len(), names.from_circuit@.len(), indices,
        image.layout_model().input_model(), image.layout_model().outputs_model().len())
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 指定した入力が回路の宣言順で最初の未接続入力であることを表す。
    pub closed spec fn missing_rp_spi_input(
        &self, owner: ModuleBodyPosition, width: u64, gpio: Seq<GpioBinding>, names: SpiPortNames, port: usize,
    ) -> bool {
        &&& exists|netlist: crate::netlist::NorNetlist|
            #[trigger] self.clocked_module_source_layout(owner, width, &netlist) && port < netlist.input_count
        &&& exists|resolved: Vec<DevicePortBinding>, indices: Seq<usize>|
            #[trigger] gpio_binding_indices_match(resolved@, indices)
            && self.device_bindings_match(owner, width, spi_image_requests(gpio, names), Ok(resolved))
            && missing_input(gpio, indices, names.to_circuit@.len(), port)
    }

    /// SPI と GPIO をルートモジュールの単一ビットポートに接続する。
    ///
    /// すべての回路入力に駆動元を一つ割り当てる。SPI が読む出力は信号の指定順で保持する。
    ///
    /// # Errors
    ///
    /// 周期、SPI 設定、ピン、回路ポート、回路変換、入力の未接続の順に検査する。
    pub fn build_rp_spi_image<'n>(
        &self, owner: ModuleBodyPosition, board: Board, gpio: &[GpioBinding<'n>],
        setup: SpiSetup, names: SpiPortNames<'n>, tick_micros: u64,
        width_limit: u64, bit_limit: usize, gate_limit: usize,
    ) -> (result: Result<SpiCircuitImage, SpiImageError<'p, 'a, 'n>>)
        requires self.can_resolve(),
        ensures
            result matches Ok(image) ==> {
                let bytes = image.setup_model().3;
                &&& image.setup_model() == (board, setup, tick_micros, bytes)
                &&& tick_micros > 0 && spi_setting_error(board, setup, gpio@.len(), names).is_none()
                &&& spi_port_capacity(names.to_circuit@.len() as int, names.from_circuit@.len() as int, bytes as int)
                &&& super::super::assignments_valid(board, gpio@.map_values(|binding: GpioBinding|
                    gpio_assignment(binding)).push(spi_assignment(setup)))
                &&& image.layout_model().source_model() <= u32::MAX
                &&& image.layout_model().input_model() <= bit_limit
                &&& image.layout_model().outputs_model().len() <= bit_limit
                &&& image.layout_model().gates_model().len() <= gate_limit
                &&& crate::netlist::wires_fit(image.layout_model().gates_model(), image.layout_model().source_model() as usize)
                &&& image.port_model().0.len() == image.layout_model().input_model()
                &&& image.port_model().2.len() == names.from_circuit@.len()
                &&& forall|i: int| 0 <= i < image.port_model().0.len() ==> match #[trigger] image.port_model().0[i] {
                    PeripheralInputSource::Controller(j) => j < names.to_circuit@.len(),
                    PeripheralInputSource::Gpio(_) => true,
                }
                &&& forall|i: int| 0 <= i < image.port_model().2.len() ==>
                    (#[trigger] image.port_model().2[i]) < image.layout_model().outputs_model().len()
                &&& exists|netlist: crate::netlist::NorNetlist| #[trigger] image.layout_model().matches(&netlist)
                    && self.clocked_module_source_layout(owner, width_limit, &netlist)
                &&& exists|resolved: Vec<DevicePortBinding>, indices: Seq<usize>|
                    #[trigger] spi_image_ports_match(&image, gpio@, names, indices)
                    && self.device_bindings_match(owner, width_limit, spi_image_requests(gpio@, names), Ok(resolved))
                    && #[trigger] gpio_binding_indices_match(resolved@, indices)
            },
            (result matches Err(SpiImageError::Circuit(GpioImageError::ZeroTickPeriod))) <==> tick_micros == 0,
            (result matches Err(SpiImageError::Setting(_))) <==>
                tick_micros > 0 && spi_setting_error(board, setup, gpio@.len(), names).is_some(),
            result matches Err(SpiImageError::Setting(error)) ==>
                spi_setting_error(board, setup, gpio@.len(), names) == Some(error),
            result matches Err(SpiImageError::Circuit(GpioImageError::Pin(error))) ==>
                super::super::first_assignment_error(board, gpio@.map_values(|binding: GpioBinding|
                    gpio_assignment(binding)).push(spi_assignment(setup)), error),
            result matches Err(SpiImageError::Circuit(GpioImageError::Binding(error))) ==>
                self.device_bindings_match(owner, width_limit, spi_image_requests(gpio@, names), Err(error)),
            result matches Err(SpiImageError::Circuit(GpioImageError::MissingInput { port })) ==>
                self.missing_rp_spi_input(owner, width_limit, gpio@, names, port),
    {
        if tick_micros == 0 { return Err(SpiImageError::Circuit(GpioImageError::ZeroTickPeriod)); }
        let (capacity, split) = match checked_capacity(board, setup, gpio.len(), names) {
            Ok(value) => value,
            Err(error) => return Err(SpiImageError::Setting(error)),
        };
        let (mut assignments, mut list) = requests(gpio);
        assignments.push(Assignment::Spi { instance: setup.instance, clock: setup.sck,
            mosi: setup.mosi, miso: setup.miso, select: setup.cs });
        if let Err(error) = check_assignments(board, &assignments) {
            return Err(SpiImageError::Circuit(GpioImageError::Pin(error)));
        }
        append_port_requests(gpio, names.to_circuit, names.from_circuit, &mut list);
        assert(list@ =~= spi_image_requests(gpio@, names));
        let (layout, indices) = match self.lower_rp_ports(owner, &list, width_limit, bit_limit, gate_limit) {
            Ok(value) => value,
            Err(error) => return Err(SpiImageError::Circuit(error)),
        };

        let ghost netlist = choose|netlist: crate::netlist::NorNetlist|
            #[trigger] layout.matches(&netlist) && self.clocked_module_source_layout(owner, width_limit, &netlist);
        proof {
            layout.port_slots(&netlist);
            assert forall|i: int| split <= i < indices@.len() implies
                #[trigger] indices@[i] < layout.outputs_model().len() by {
                peripheral_output_direction(gpio@, names.to_circuit@, names.from_circuit@, i);
            };
        }
        let ghost resolved = choose|resolved: Vec<DevicePortBinding>|
            #[trigger] gpio_binding_indices_match(resolved@, indices@)
                && self.device_bindings_match(owner, width_limit, spi_image_requests(gpio@, names), Ok(resolved));
        assert((split - gpio@.len()) as nat == names.to_circuit@.len());
        assert((indices@.len() - split) as nat == names.from_circuit@.len());
        let input_count = layout.input_count();
        let output_count = layout.outputs().len();
        let ports = match project_ports(gpio, &indices, split, input_count, output_count) {
            Ok(ports) => ports,
            Err(port) => {
                assert(port < netlist.input_count);
                assert(exists|bindings: Vec<DevicePortBinding>, slots: Seq<usize>|
                    #[trigger] gpio_binding_indices_match(bindings@, slots)
                    && self.device_bindings_match(owner, width_limit, spi_image_requests(gpio@, names), Ok(bindings))
                    && missing_input(gpio@, slots, names.to_circuit@.len(), port));
                assert(exists|source: crate::netlist::NorNetlist|
                    #[trigger] self.clocked_module_source_layout(owner, width_limit, &source)
                    && port < source.input_count);
                assert(self.missing_rp_spi_input(owner, width_limit, gpio@, names, port));
                return Err(SpiImageError::Circuit(GpioImageError::MissingInput { port }));
            },
        };
        let image = SpiCircuitImage {
            board, layout, setup, tick_micros, capacity, inputs: ports.inputs,
            gpio_outputs: ports.gpio_outputs, spi_outputs: ports.controller_outputs,
        };
        proof {
            peripheral_port_bounds(image.port_model(), gpio@, names.to_circuit@.len(),
                names.from_circuit@.len(), indices@, image.layout_model().input_model(), image.layout_model().outputs_model().len());
            assert(spi_image_ports_match(&image, gpio@, names, indices@));
        }
        Ok(image)
    }
}

proof fn spi_frequency_examples() {
    assert(spi_frequency_supported(Board::Pico, 1_923)) by (compute);
    assert(!spi_frequency_supported(Board::Pico, 1_922)) by (compute);
    assert(spi_frequency_supported(Board::Pico2, 75_000_000)) by (compute);
    assert(!spi_frequency_supported(Board::Pico2, 75_000_001)) by (compute);
}

} // verus!
