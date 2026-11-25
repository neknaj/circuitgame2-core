//! I²C のポート名と GPIO を同じルート回路の配線番号に対応付ける。

use alloc::vec::Vec;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

use super::{
    Assignment, Board, DevicePortRequest, DevicePortType, GpioBinding, GpioImageError,
    GpioOutputPin, ModuleBodyPosition, PackedNorLayout32, PortDirection, UseAliases,
    append_outputs, check_assignments, input_pin, requests,
};
#[cfg(verus_only)]
use super::{DevicePortBinding, gpio_assignment, gpio_binding_indices_match, gpio_request, input_at, outputs_before};

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

/// 宣言順の回路入力を駆動する信号。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum I2cInputSource {
    /// ボードの GPIO。
    Gpio(u8),
    /// [I2cPortNames::to_circuit] 内の位置。
    Controller(usize),
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
    1 <= bytes <= 255 && to == TO_CIRCUIT_HEADER + 8 * bytes && from == FROM_CIRCUIT_HEADER + 8 * bytes
}

fn port_capacity(to: usize, from: usize) -> (result: Option<u8>)
    ensures result.is_some() <==> exists|bytes: int| i2c_port_capacity(to as int, from as int, bytes),
        result matches Some(bytes) ==> i2c_port_capacity(to as int, from as int, bytes as int),
{
    if to < TO_CIRCUIT_HEADER || from < FROM_CIRCUIT_HEADER { return None; }
    let bits = to - TO_CIRCUIT_HEADER;
    let bytes = bits / 8;
    if bits != from - FROM_CIRCUIT_HEADER || bits % 8 != 0 || bytes == 0 || bytes > 255 {
        return None;
    }
    assert(i2c_port_capacity(to as int, from as int, bytes as int));
    Some(bytes as u8)
}

/// コントローラーを基板の I²C ピンに割り当てる。
pub open spec fn i2c_assignment(setup: I2cSetup) -> Assignment {
    Assignment::I2c { instance: setup.instance, data: setup.sda, clock: setup.scl }
}

spec fn bit_request<'n>(name: &'n str, direction: PortDirection) -> DevicePortRequest<'n> {
    DevicePortRequest { direction, circuit_port: name, expected: DevicePortType::Bits(1) }
}

/// GPIO、回路入力、回路出力の順でポート照会を並べる。
pub closed spec fn i2c_image_requests<'n>(gpio: Seq<GpioBinding<'n>>, names: I2cPortNames<'n>) -> Seq<DevicePortRequest<'n>> {
    gpio.map_values(|binding: GpioBinding| gpio_request(binding))
        + (names.to_circuit@.map_values(|name: &str| bit_request(name, PortDirection::Output))
        + names.from_circuit@.map_values(|name: &str| bit_request(name, PortDirection::Input)))
}

fn append_requests<'n>(
    names: &[&'n str], direction: PortDirection, list: &mut Vec<DevicePortRequest<'n>>,
)
    ensures final(list)@ == old(list)@ + names@.map_values(|name: &str| bit_request(name, direction)),
{
    let mut i = 0;
    while i < names.len()
        invariant i <= names@.len(),
            list@ == old(list)@ + names@.take(i as int).map_values(|name: &str| bit_request(name, direction)),
        decreases names.len() - i,
    {
        list.push(DevicePortRequest { direction, circuit_port: names[i], expected: DevicePortType::Bits(1) });
        assert(list@ =~= old(list)@ + names@.take(i as int + 1).map_values(|name: &str| bit_request(name, direction)));
        i += 1;
    }
    assert(names@.take(i as int) =~= names@);
}

spec fn controller_input_at(list: Seq<usize>, port: usize, resolved: Option<usize>) -> bool {
    match resolved {
        Some(i) => i < list.len() && list[i as int] == port
            && forall|j: int| 0 <= j < i ==> #[trigger] list[j] != port,
        None => forall|j: int| 0 <= j < list.len() ==> #[trigger] list[j] != port,
    }
}

fn controller_input(list: &[usize], port: usize) -> (index: Option<usize>)
    ensures controller_input_at(list@, port, index),
{
    let mut i = 0;
    while i < list.len()
        invariant i <= list@.len(), forall|j: int| 0 <= j < i ==> #[trigger] list@[j] != port,
        decreases list.len() - i,
    {
        if list[i] == port { return Some(i); }
        i += 1;
    }
    None
}

spec fn matches_input(
    gpio: Seq<GpioBinding>, indices: Seq<usize>, controller: Seq<usize>, port: usize, source: Option<I2cInputSource>,
) -> bool {
    match input_at(gpio, indices, port) {
        Some(pin) => source == Some(I2cInputSource::Gpio(pin)),
        None => controller_input_at(controller, port, match source {
            Some(I2cInputSource::Controller(i)) => Some(i),
            _ => None,
        }) && !(source matches Some(I2cInputSource::Gpio(_))),
    }
}

/// 入力駆動元と出力ポート番号が、名前を解決した配線表に対応する。
pub closed spec fn i2c_image_ports_match(
    image: &I2cCircuitImage, gpio: Seq<GpioBinding>, names: I2cPortNames, indices: Seq<usize>,
) -> bool {
    let (inputs, gpio_outputs, i2c_outputs) = image.port_model();
    let split = gpio.len() + names.to_circuit@.len();
    &&& indices.len() == split + names.from_circuit@.len()
    &&& inputs.len() == image.layout_model().input_model()
    &&& forall|i: int| 0 <= i < inputs.len() ==>
        matches_input(gpio, indices, indices.subrange(gpio.len() as int, split as int), i as usize,
            Some(#[trigger] inputs[i]))
    &&& gpio_outputs == outputs_before(gpio, indices, image.layout_model().outputs_model().len())
    &&& i2c_outputs == indices.skip(split as int)
    &&& forall|i: int| 0 <= i < i2c_outputs.len() ==>
        #[trigger] i2c_outputs[i] < image.layout_model().outputs_model().len()
}

/// 指定の入力に駆動元がなく、それより前の入力はすべて接続されている。
pub closed spec fn missing_input_first(
    gpio: Seq<GpioBinding>, indices: Seq<usize>, count: nat, prefix: Seq<I2cInputSource>, port: usize,
) -> bool {
    let controller = indices.subrange(gpio.len() as int, (gpio.len() + count) as int);
    &&& matches_input(gpio, indices, controller, port, None)
    &&& prefix.len() == port
    &&& forall|i: int| 0 <= i < port ==>
            matches_input(gpio, indices, controller, i as usize, Some(#[trigger] prefix[i]))
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
            && (exists|prefix: Seq<I2cInputSource>|
                #[trigger] missing_input_first(gpio, indices, names.to_circuit@.len(), prefix, port))
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
        let Some(capacity) = port_capacity(names.to_circuit.len(), names.from_circuit.len()) else {
            return Err(I2cImageError::PortCounts);
        };
        let Some(split) = gpio.len().checked_add(names.to_circuit.len()) else { return Err(I2cImageError::BindingCount); };
        if split.checked_add(names.from_circuit.len()).is_none() { return Err(I2cImageError::BindingCount); }
        let (mut assignments, mut list) = requests(gpio);
        assignments.push(Assignment::I2c { instance: setup.instance, data: setup.sda, clock: setup.scl });
        if let Err(error) = check_assignments(board, &assignments) {
            return Err(I2cImageError::Circuit(GpioImageError::Pin(error)));
        }
        append_requests(names.to_circuit, PortDirection::Output, &mut list);
        append_requests(names.from_circuit, PortDirection::Input, &mut list);
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

        let controller = slice_subrange(indices.as_slice(), gpio.len(), split);
        let mut inputs = Vec::new();
        let n = layout.input_count();
        let mut i = 0;
        while i < n
            invariant i == inputs@.len() <= n == layout.input_model(),
                tick_micros > 0,
                setup.frequency_hz == 100_000 || setup.frequency_hz == 400_000,
                n == netlist.input_count,
                self.clocked_module_source_layout(owner, width_limit, &netlist),
                gpio_binding_indices_match(resolved@, indices@),
                self.device_bindings_match(owner, width_limit, i2c_image_requests(gpio@, names), Ok(resolved)),
                split == gpio@.len() + names.to_circuit@.len() <= indices@.len(),
                controller@ == indices@.subrange(gpio@.len() as int, split as int),
                forall|j: int| 0 <= j < i ==>
                    matches_input(gpio@, indices@, controller@, j as usize, Some(#[trigger] inputs@[j])),
            decreases n - i,
        {
            let source = if let Some(pin) = input_pin(gpio, &indices, i) { I2cInputSource::Gpio(pin) }
                else if let Some(index) = controller_input(controller, i) { I2cInputSource::Controller(index) }
                else {
                    assert(matches_input(gpio@, indices@, controller@, i, None));
                    assert(missing_input_first(gpio@, indices@, names.to_circuit@.len(), inputs@, i));
                    assert(self.clocked_module_source_layout(owner, width_limit, &netlist) && i < netlist.input_count);
                    assert(gpio_binding_indices_match(resolved@, indices@));
                    assert(self.device_bindings_match(owner, width_limit, i2c_image_requests(gpio@, names), Ok(resolved)));
                    assert(exists|prefix: Seq<I2cInputSource>|
                        #[trigger] missing_input_first(gpio@, indices@, names.to_circuit@.len(), prefix, i));
                    assert(exists|bindings: Vec<DevicePortBinding>, slots: Seq<usize>|
                        #[trigger] gpio_binding_indices_match(bindings@, slots)
                        && self.device_bindings_match(owner, width_limit, i2c_image_requests(gpio@, names), Ok(bindings))
                        && (exists|prefix: Seq<I2cInputSource>|
                            #[trigger] missing_input_first(gpio@, slots, names.to_circuit@.len(), prefix, i)));
                    assert(exists|source: crate::netlist::NorNetlist|
                        #[trigger] self.clocked_module_source_layout(owner, width_limit, &source)
                        && i < source.input_count);
                    assert(self.missing_rp_i2c_input(owner, width_limit, gpio@, names, i));
                    return Err(I2cImageError::Circuit(GpioImageError::MissingInput { port: i }));
                };
            assert(matches_input(gpio@, indices@, controller@, i, Some(source)));
            inputs.push(source);
            i += 1;
        }

        let mut gpio_outputs = Vec::new();
        let n = layout.outputs().len();
        let mut i = 0;
        while i < n
            invariant i <= n == layout.outputs_model().len(), gpio@.len() <= indices@.len(),
                gpio_outputs@ == outputs_before(gpio@, indices@, i as nat),
            decreases n - i,
        {
            append_outputs(gpio, &indices, i, &mut gpio_outputs);
            assert(outputs_before(gpio@, indices@, (i + 1) as nat) == gpio_outputs@);
            i += 1;
        }
        let mut i2c_outputs = Vec::new();
        let mut i = split;
        while i < indices.len()
            invariant split <= i <= indices@.len(),
                i2c_outputs@ == indices@.subrange(split as int, i as int),
            decreases indices.len() - i,
        {
            i2c_outputs.push(indices[i]);
            assert(i2c_outputs@ =~= indices@.subrange(split as int, i as int + 1));
            i += 1;
        }
        let image = I2cCircuitImage { board, layout, setup, tick_micros, capacity, inputs, gpio_outputs, i2c_outputs };
        assert(i2c_image_ports_match(&image, gpio@, names, indices@)) by {
            assert(image.port_model().2 =~= indices@.skip(split as int));
            assert forall|j: int| 0 <= j < image.port_model().2.len() implies
                #[trigger] image.port_model().2[j] < image.layout_model().outputs_model().len() by {
                assert(list@[split + j].direction is Input);
            };
        };
        Ok(image)
    }
}

} // verus!
