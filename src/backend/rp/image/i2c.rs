//! I²C のポート名と GPIO を同じルート回路の配線番号に対応付ける。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{
    Assignment, Board, GpioBinding, GpioImageError, GpioOutputPin, ModuleBodyPosition,
    PackedNorLayout32, UseAliases, check_assignments, requests,
};
use super::peripheral::{append_port_requests, port_capacity, project_ports};
pub use super::peripheral::PeripheralInputSource as I2cInputSource;
#[cfg(verus_only)]
use super::{DevicePortBinding, DevicePortRequest, gpio_assignment, gpio_binding_indices_match};
#[cfg(verus_only)]
use super::peripheral::{
    missing_input, peripheral_image_requests, peripheral_output_direction, peripheral_port_bounds,
    peripheral_port_capacity, peripheral_ports_match,
};

verus! {

const TO_CIRCUIT_HEADER: usize = 5;
const FROM_CIRCUIT_HEADER: usize = 25;

/// RP に接続する I²C コントローラーの設定。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct I2cSetup {
    /// I²C0 または I²C1 の番号。
    pub instance: u8,
    /// SDA の GP 番号。
    pub sda: u8,
    /// SCL の GP 番号。
    pub scl: u8,
    /// 通信周波数。100 kHz または 400 kHz を指定する。
    pub frequency_hz: u32,
    /// 1取引の待ち時間。マイクロ秒で指定する。
    pub timeout_micros: u32,
}

/// 回路の単一ビットポート名を I²C の信号順に並べた指定。
#[derive(Clone, Copy, Debug)]
pub struct I2cPortNames<'n> {
    /// 要求 ready、応答 valid、状態3ビット、受信データの順。
    pub to_circuit: &'n [&'n str],
    /// 要求 valid、応答 ready、アドレス7ビット、書き込み長8ビット、読み出し長8ビット、送信データの順。
    pub from_circuit: &'n [&'n str],
}

/// I²C を接続した RP 向けの配線表を作れなかった理由。
#[derive(Debug)]
pub enum I2cImageError<'p, 'a, 'n> {
    /// 指定周波数が100 kHz または400 kHz ではない。
    Frequency,
    /// 待ち時間が0マイクロ秒である。
    ZeroTimeout,
    /// 必須の信号が不足しているか、送受信の容量が同じ正のバイト数になっていない。
    PortCounts,
    /// 設定の接続数をホストの添字で表せない。
    BindingCount,
    /// 基板のピン、回路側のポート、または配線の検査で起きた診断。
    Circuit(GpioImageError<'p, 'a, 'n>),
}

/// 一つのルート回路を駆動する I²C と GPIO の配線表。
pub struct I2cCircuitImage {
    board: Board,
    layout: PackedNorLayout32,
    setup: I2cSetup,
    tick_micros: u64,
    capacity: u8,
    inputs: Vec<I2cInputSource>,
    gpio_outputs: Vec<GpioOutputPin>,
    i2c_outputs: Vec<usize>,
}

impl I2cCircuitImage {
    /// ボード、通信、周期、バイト容量の仕様上の値。
    pub closed spec fn setup_model(&self) -> (Board, I2cSetup, u64, u8) {
        (self.board, self.setup, self.tick_micros, self.capacity)
    }
    /// 回路を展開した32レーン配線。
    pub closed spec fn layout_model(&self) -> PackedNorLayout32 { self.layout }
    /// 回路入力の各駆動元と、GPIO・I²C が読む回路出力。
    pub closed spec fn port_model(&self) -> (Seq<I2cInputSource>, Seq<GpioOutputPin>, Seq<usize>) {
        (self.inputs@, self.gpio_outputs@, self.i2c_outputs@)
    }

    /// ボード、通信設定、tick 周期のマイクロ秒数、送受信のバイト容量を返す。
    pub fn setup(&self) -> (setup: (Board, I2cSetup, u64, u8))
        ensures setup == self.setup_model(),
    { (self.board, self.setup, self.tick_micros, self.capacity) }

    /// 配線番号を確定した回路を返す。
    pub fn layout(&self) -> (layout: &PackedNorLayout32)
        ensures *layout == self.layout_model(),
    { &self.layout }

    /// 入力元は宣言順、GPIO 出力は宣言順と設定順、I²C 出力は指定した信号順で返す。
    pub fn ports(&self) -> (ports: (&[I2cInputSource], &[GpioOutputPin], &[usize]))
        ensures (ports.0@, ports.1@, ports.2@) == self.port_model(),
    { (self.inputs.as_slice(), self.gpio_outputs.as_slice(), self.i2c_outputs.as_slice()) }
}

/// 送受信データの配線が同じ容量の全バイトを表す。
pub closed spec fn i2c_port_capacity(to: int, from: int, bytes: int) -> bool {
    peripheral_port_capacity(to, from, TO_CIRCUIT_HEADER as int, FROM_CIRCUIT_HEADER as int, bytes)
}

/// コントローラーを基板の I²C ピンに割り当てる。
pub open spec fn i2c_assignment(setup: I2cSetup) -> Assignment {
    Assignment::I2c { instance: setup.instance, data: setup.sda, clock: setup.scl }
}

/// GPIO、回路入力、回路出力の順でポート照会を並べる。
pub closed spec fn i2c_image_requests<'n>(gpio: Seq<GpioBinding<'n>>, names: I2cPortNames<'n>) -> Seq<DevicePortRequest<'n>> {
    peripheral_image_requests(gpio, names.to_circuit@, names.from_circuit@)
}

/// 入力駆動元と出力ポート番号が、名前を解決した配線表に対応する。
pub closed spec fn i2c_image_ports_match(
    image: &I2cCircuitImage, gpio: Seq<GpioBinding>, names: I2cPortNames, indices: Seq<usize>,
) -> bool {
    peripheral_ports_match(image.port_model(), gpio, names.to_circuit@.len(), names.from_circuit@.len(), indices,
        image.layout_model().input_model(), image.layout_model().outputs_model().len())
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 配線表の先頭から見て、指定した入力が最初の未接続入力であることを表す。
    pub closed spec fn missing_rp_i2c_input(
        &self, owner: ModuleBodyPosition, width: u64, gpio: Seq<GpioBinding>, names: I2cPortNames, port: usize,
    ) -> bool {
        &&& exists|netlist: crate::netlist::NorNetlist|
            #[trigger] self.clocked_module_source_layout(owner, width, &netlist) && port < netlist.input_count
        &&& exists|resolved: Vec<DevicePortBinding>, indices: Seq<usize>|
            #[trigger] gpio_binding_indices_match(resolved@, indices)
            && self.device_bindings_match(owner, width, i2c_image_requests(gpio, names), Ok(resolved))
            && missing_input(gpio, indices, names.to_circuit@.len(), port)
    }

    /// I²C と GPIO をルートモジュールの単一ビットポートに接続する。
    ///
    /// すべての回路入力に駆動元を一つ割り当てる。I²C が読む出力は信号の指定順で保持する。
    ///
    /// # Errors
    ///
    /// 周期、周波数、待ち時間、ポート配列の長さ、ピン、回路ポート、回路変換、入力の未接続を検査する。
    pub fn build_rp_i2c_image<'n>(
        &self, owner: ModuleBodyPosition, board: Board, gpio: &[GpioBinding<'n>],
        setup: I2cSetup, names: I2cPortNames<'n>, tick_micros: u64,
        width_limit: u64, bit_limit: usize, gate_limit: usize,
    ) -> (result: Result<I2cCircuitImage, I2cImageError<'p, 'a, 'n>>)
        requires self.can_resolve(),
        ensures
            result matches Ok(image) ==> {
                let bytes = image.setup_model().3;
                &&& image.setup_model() == (board, setup, tick_micros, bytes)
                &&& i2c_port_capacity(names.to_circuit@.len() as int, names.from_circuit@.len() as int, bytes as int)
                &&& tick_micros > 0 && setup.timeout_micros > 0
                &&& (setup.frequency_hz == 100_000 || setup.frequency_hz == 400_000)
                &&& super::super::assignments_valid(board, gpio@.map_values(|binding: GpioBinding|
                    gpio_assignment(binding)).push(i2c_assignment(setup)))
                &&& image.layout_model().source_model() <= u32::MAX
                &&& image.layout_model().input_model() <= bit_limit
                &&& image.layout_model().outputs_model().len() <= bit_limit
                &&& image.layout_model().gates_model().len() <= gate_limit
                &&& crate::netlist::wires_fit(image.layout_model().gates_model(), image.layout_model().source_model() as usize)
                &&& image.port_model().0.len() == image.layout_model().input_model()
                &&& image.port_model().2.len() == names.from_circuit@.len()
                &&& forall|i: int| 0 <= i < image.port_model().0.len() ==> match #[trigger] image.port_model().0[i] {
                    I2cInputSource::Controller(j) => j < names.to_circuit@.len(),
                    I2cInputSource::Gpio(_) => true,
                }
                &&& forall|i: int| 0 <= i < image.port_model().2.len() ==>
                    (#[trigger] image.port_model().2[i]) < image.layout_model().outputs_model().len()
                &&& exists|netlist: crate::netlist::NorNetlist| #[trigger] image.layout_model().matches(&netlist)
                    && self.clocked_module_source_layout(owner, width_limit, &netlist)
                &&& exists|resolved: Vec<DevicePortBinding>, indices: Seq<usize>|
                    #[trigger] i2c_image_ports_match(&image, gpio@, names, indices)
                    && self.device_bindings_match(owner, width_limit, i2c_image_requests(gpio@, names), Ok(resolved))
                    && #[trigger] gpio_binding_indices_match(resolved@, indices)
            },
            (result matches Err(I2cImageError::Circuit(GpioImageError::ZeroTickPeriod))) <==> tick_micros == 0,
            (result matches Err(I2cImageError::Frequency)) <==>
                tick_micros > 0 && setup.frequency_hz != 100_000 && setup.frequency_hz != 400_000,
            result matches Err(I2cImageError::ZeroTimeout) ==> setup.timeout_micros == 0,
            result matches Err(I2cImageError::PortCounts) ==>
                !(exists|bytes: int| i2c_port_capacity(names.to_circuit@.len() as int, names.from_circuit@.len() as int, bytes)),
            result matches Err(I2cImageError::BindingCount) ==>
                gpio@.len() + names.to_circuit@.len() + names.from_circuit@.len() > usize::MAX,
            result matches Err(I2cImageError::Circuit(GpioImageError::Pin(error))) ==>
                super::super::first_assignment_error(board, gpio@.map_values(|binding: GpioBinding|
                    gpio_assignment(binding)).push(i2c_assignment(setup)), error),
            result matches Err(I2cImageError::Circuit(GpioImageError::Binding(error))) ==>
                self.device_bindings_match(owner, width_limit, i2c_image_requests(gpio@, names), Err(error)),
            result matches Err(I2cImageError::Circuit(GpioImageError::MissingInput { port })) ==>
                self.missing_rp_i2c_input(owner, width_limit, gpio@, names, port),
    {
        if tick_micros == 0 { return Err(I2cImageError::Circuit(GpioImageError::ZeroTickPeriod)); }
        if setup.frequency_hz != 100_000 && setup.frequency_hz != 400_000 { return Err(I2cImageError::Frequency); }
        if setup.timeout_micros == 0 { return Err(I2cImageError::ZeroTimeout); }
        let Some(capacity) = port_capacity(names.to_circuit.len(), names.from_circuit.len(), TO_CIRCUIT_HEADER, FROM_CIRCUIT_HEADER) else {
            return Err(I2cImageError::PortCounts);
        };
        let Some(split) = gpio.len().checked_add(names.to_circuit.len()) else { return Err(I2cImageError::BindingCount); };
        if split.checked_add(names.from_circuit.len()).is_none() { return Err(I2cImageError::BindingCount); }
        let (mut assignments, mut list) = requests(gpio);
        assignments.push(Assignment::I2c { instance: setup.instance, data: setup.sda, clock: setup.scl });
        if let Err(error) = check_assignments(board, &assignments) {
            return Err(I2cImageError::Circuit(GpioImageError::Pin(error)));
        }
        append_port_requests(gpio, names.to_circuit, names.from_circuit, &mut list);
        assert(list@ =~= i2c_image_requests(gpio@, names));
        let (layout, indices) = match self.lower_rp_ports(owner, &list, width_limit, bit_limit, gate_limit) {
            Ok(value) => value,
            Err(error) => return Err(I2cImageError::Circuit(error)),
        };

        let ghost netlist = choose|netlist: crate::netlist::NorNetlist|
            #[trigger] layout.matches(&netlist) && self.clocked_module_source_layout(owner, width_limit, &netlist);
        proof { layout.port_slots(&netlist); }
        let ghost resolved = choose|resolved: Vec<DevicePortBinding>|
            #[trigger] gpio_binding_indices_match(resolved@, indices@)
                && self.device_bindings_match(owner, width_limit, i2c_image_requests(gpio@, names), Ok(resolved));

        proof {
            assert forall|i: int| split <= i < indices@.len() implies
                #[trigger] indices@[i] < layout.outputs_model().len() by {
                peripheral_output_direction(gpio@, names.to_circuit@, names.from_circuit@, i);
            };
        }
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
                    && self.device_bindings_match(owner, width_limit, i2c_image_requests(gpio@, names), Ok(bindings))
                    && missing_input(gpio@, slots, names.to_circuit@.len(), port));
                assert(exists|source: crate::netlist::NorNetlist|
                    #[trigger] self.clocked_module_source_layout(owner, width_limit, &source)
                    && port < source.input_count);
                assert(self.missing_rp_i2c_input(owner, width_limit, gpio@, names, port));
                return Err(I2cImageError::Circuit(GpioImageError::MissingInput { port }));
            },
        };
        let image = I2cCircuitImage {
            board, layout, setup, tick_micros, capacity, inputs: ports.inputs,
            gpio_outputs: ports.gpio_outputs, i2c_outputs: ports.controller_outputs,
        };
        proof {
            peripheral_port_bounds(image.port_model(), gpio@, names.to_circuit@.len(),
                names.from_circuit@.len(), indices@, image.layout_model().input_model(), image.layout_model().outputs_model().len());
            assert(i2c_image_ports_match(&image, gpio@, names, indices@));
        }
        Ok(image)
    }
}

} // verus!
