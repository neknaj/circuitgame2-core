//! 一つのルート回路と GPIO 接続を、RP 向けの配線配置にまとめる。

mod i2c;
mod uart;

pub use i2c::{I2cCircuitImage, I2cImageError, I2cInputSource, I2cPortNames, I2cSetup};
#[cfg(verus_only)]
pub use i2c::{i2c_assignment, i2c_image_ports_match, i2c_image_requests, i2c_port_capacity};

pub use uart::{RpInputSource, UartCircuitImage, UartImageError, UartInputSignal, UartOutputPorts, UartPortNames, UartSetup};
#[cfg(verus_only)]
pub use uart::{uart_assignment, uart_image_ports_match, uart_image_requests, uart_output_indices_fit};

use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::seq_lib::*;

use super::{Assignment, AssignmentError, Board, check_assignments};
use crate::netlist::PackedNorLayout32;
use crate::project::{
    ClockedModuleError, DeviceBindingsError, DevicePortBinding, DevicePortRequest, DevicePortType,
    ModuleBodyPosition, PortDirection, UseAliases,
};

verus! {

/// 回路の単一ビットのポートに接続する GPIO。
#[derive(Clone, Copy, Debug)]
pub enum GpioBinding<'n> {
    /// tick の開始時にピンを読み、回路入力へ渡す。
    Input {
        /// ルートモジュールの入力ポート名。
        port: &'n str,
        /// ボードに露出する GPIO 番号。
        pin: u8,
    },
    /// tick の確定後に回路出力をピンへ反映する。
    Output {
        /// ルートモジュールの出力ポート名。
        port: &'n str,
        /// ボードに露出する GPIO 番号。
        pin: u8,
        /// 最初の tick を実行する前にピンを High にするか。
        initial_high: bool,
    },
}

/// 一つの公開出力を転送する先。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GpioOutputPin {
    /// 回路の公開出力の宣言順の添字。
    pub port: usize,
    /// 駆動する GPIO 番号。
    pub pin: u8,
    /// 最初の tick より前の High レベルの指定。
    pub initial_high: bool,
}

/// 同じルート回路から得た NOR の配線配置、GPIO 接続、tick 周期。
pub struct GpioCircuitImage {
    board: Board,
    layout: PackedNorLayout32,
    inputs: Vec<u8>,
    outputs: Vec<GpioOutputPin>,
    tick_micros: u64,
}

/// RP 向けに回路と GPIO 接続を組み立てられなかった理由。
#[derive(Debug)]
pub enum GpioImageError<'p, 'a, 'n> {
    /// 指定した周期が0だった。
    ZeroTickPeriod,
    /// 設定順の GPIO 割り当てがボードの制約に違反した。
    Pin(AssignmentError),
    /// 回路のポート名、方向、型、または入力の駆動元に問題がある。
    Binding(DeviceBindingsError<'p, 'a, 'n>),
    /// 指定位置にルートモジュールがない。
    NoModule,
    /// パックできる回路への変換が失敗した。
    Circuit(ClockedModuleError<'p, 'a>),
    /// 配線数を RP の32ビットの添字で表せない。
    LayoutSize,
    /// GPIO が割り当てられていない最初の回路入力。
    MissingInput {
        /// 入力ポートの宣言順の添字。
        port: usize,
    },
}

impl GpioCircuitImage {
    /// GPIO の検査に使ったボード。
    pub closed spec fn board_model(&self) -> Board { self.board }
    /// ルート回路の配線配置。
    pub closed spec fn layout_model(&self) -> PackedNorLayout32 { self.layout }
    /// 回路入力の宣言順で並んだ GPIO 番号。
    pub closed spec fn input_pins_model(&self) -> Seq<u8> { self.inputs@ }
    /// 回路出力の宣言順で並んだ GPIO 接続。
    pub closed spec fn output_pins_model(&self) -> Seq<GpioOutputPin> { self.outputs@ }
    /// 1 tick のマイクロ秒数。
    pub closed spec fn tick_micros_model(&self) -> u64 { self.tick_micros }

    /// 対象のボードを返す。
    pub fn board(&self) -> (board: Board)
        ensures board == self.board_model(),
    { self.board }

    /// GPIO と接続する回路の配線配置を返す。
    pub fn layout(&self) -> (layout: &PackedNorLayout32)
        ensures *layout == self.layout_model(),
    { &self.layout }

    /// 入力宣言順に GPIO 番号を返す。
    pub fn input_pins(&self) -> (pins: &[u8])
        ensures pins@ == self.input_pins_model(),
    { self.inputs.as_slice() }

    /// 出力宣言順に GPIO 接続を返す。同じ出力の接続は設定順に並ぶ。
    pub fn output_pins(&self) -> (pins: &[GpioOutputPin])
        ensures pins@ == self.output_pins_model(),
    { self.outputs.as_slice() }

    /// 正の整数で指定された1 tick のマイクロ秒数を返す。
    pub fn tick_micros(&self) -> (micros: u64)
        ensures micros == self.tick_micros_model(),
    { self.tick_micros }
}

/// GPIO 接続をボードのピン検査へ渡す割り当てに対応付ける。
pub open spec fn gpio_assignment(binding: GpioBinding) -> Assignment {
    match binding {
        GpioBinding::Input { pin, .. } => Assignment::GpioInput { pin },
        GpioBinding::Output { pin, initial_high, .. } => Assignment::GpioOutput { pin, initial_high },
    }
}

/// GPIO の読み書きを回路側の単一ビットポートへの要求に対応付ける。
pub open spec fn gpio_request(binding: GpioBinding) -> DevicePortRequest {
    match binding {
        GpioBinding::Input { port, .. } => DevicePortRequest {
            direction: PortDirection::Output, circuit_port: port, expected: DevicePortType::Bits(1),
        },
        GpioBinding::Output { port, .. } => DevicePortRequest {
            direction: PortDirection::Input, circuit_port: port, expected: DevicePortType::Bits(1),
        },
    }
}

fn requests<'n>(bindings: &[GpioBinding<'n>]) -> (result: (Vec<Assignment>, Vec<DevicePortRequest<'n>>))
    ensures
        result.0@ == bindings@.map_values(|binding: GpioBinding| gpio_assignment(binding)),
        result.1@ == bindings@.map_values(|binding: GpioBinding| gpio_request(binding)),
{
    let mut assignments = Vec::new();
    let mut requests = Vec::new();
    let mut i = 0;
    while i < bindings.len()
        invariant
            i <= bindings@.len(),
            assignments@ == bindings@.take(i as int).map_values(|binding: GpioBinding| gpio_assignment(binding)),
            requests@ == bindings@.take(i as int).map_values(|binding: GpioBinding| gpio_request(binding)),
        decreases bindings.len() - i,
    {
        let (assignment, request) = match bindings[i] {
            GpioBinding::Input { port, pin } => (Assignment::GpioInput { pin }, DevicePortRequest {
                direction: PortDirection::Output, circuit_port: port, expected: DevicePortType::Bits(1),
            }),
            GpioBinding::Output { port, pin, initial_high } => (
                Assignment::GpioOutput { pin, initial_high }, DevicePortRequest {
                    direction: PortDirection::Input, circuit_port: port, expected: DevicePortType::Bits(1),
                },
            ),
        };
        assignments.push(assignment);
        requests.push(request);
        assert(assignments@ =~= bindings@.take(i as int + 1).map_values(|binding: GpioBinding| gpio_assignment(binding)));
        assert(requests@ =~= bindings@.take(i as int + 1).map_values(|binding: GpioBinding| gpio_request(binding)));
        i += 1;
    }
    assert(bindings@.take(i as int) =~= bindings@);
    (assignments, requests)
}

spec fn is_input_at(binding: GpioBinding, index: usize, port: usize) -> bool {
    binding is Input && index == port
}

spec fn input_at(bindings: Seq<GpioBinding>, ports: Seq<usize>, port: usize) -> Option<u8> {
    if exists|i: int| 0 <= i < bindings.len() && #[trigger] is_input_at(bindings[i], ports[i], port) {
        let i = choose|i: int| 0 <= i < bindings.len() && #[trigger] is_input_at(bindings[i], ports[i], port)
            && forall|j: int| 0 <= j < i ==> !#[trigger] is_input_at(bindings[j], ports[j], port);
        Some(bindings[i]->Input_pin)
    } else { None }
}

fn input_pin(bindings: &[GpioBinding], ports: &[usize], port: usize) -> (pin: Option<u8>)
    requires bindings@.len() <= ports@.len(),
    ensures pin == input_at(bindings@, ports@, port),
{
    let mut i = 0;
    while i < bindings.len()
        invariant
            i <= bindings@.len() <= ports@.len(),
            forall|j: int| 0 <= j < i ==> !#[trigger] is_input_at(bindings@[j], ports@[j], port),
        decreases bindings.len() - i,
    {
        let binding = bindings[i];
        let index = ports[i];
        match binding {
            GpioBinding::Input { pin, .. } if index == port => {
                proof {
                    let k = choose|k: int| 0 <= k < bindings@.len() && #[trigger] is_input_at(bindings@[k], ports@[k], port)
                        && forall|j: int| 0 <= j < k ==> !#[trigger] is_input_at(bindings@[j], ports@[j], port);
                    assert(is_input_at(bindings@[i as int], ports@[i as int], port));
                    assert(k == i as int) by {
                        if k < i {
                            assert(!is_input_at(bindings@[k], ports@[k], port));
                        }
                        if i < k {
                            assert(!is_input_at(bindings@[i as int], ports@[i as int], port));
                        }
                    };
                }
                return Some(pin);
            },
            _ => {},
        }
        assert(!is_input_at(bindings@[i as int], ports@[i as int], port));
        i += 1;
    }
    None
}

spec fn output_for_port(binding: GpioBinding, index: usize, port: usize) -> Option<GpioOutputPin> {
    match binding {
        GpioBinding::Output { pin, initial_high, .. } if index == port =>
            Some(GpioOutputPin { port, pin, initial_high }),
        _ => None,
    }
}

spec fn outputs_at(bindings: Seq<GpioBinding>, ports: Seq<usize>, port: usize) -> Seq<GpioOutputPin> {
    Seq::new(bindings.len(), |i: int| output_for_port(bindings[i], ports[i], port))
        .filter(|entry: Option<GpioOutputPin>| entry.is_some()).map_values(|entry: Option<GpioOutputPin>| entry.unwrap())
}

spec fn outputs_before(bindings: Seq<GpioBinding>, ports: Seq<usize>, end: nat) -> Seq<GpioOutputPin>
    decreases end,
{
    if end == 0 { Seq::empty() }
    else { outputs_before(bindings, ports, (end - 1) as nat) + outputs_at(bindings, ports, (end - 1) as usize) }
}

fn append_outputs(bindings: &[GpioBinding], ports: &[usize], port: usize, output: &mut Vec<GpioOutputPin>)
    requires bindings@.len() <= ports@.len(),
    ensures final(output)@ == old(output)@ + outputs_at(bindings@, ports@, port),
{
    let ghost rows = Seq::new(bindings@.len(), |i: int| output_for_port(bindings@[i], ports@[i], port));
    let ghost some = |entry: Option<GpioOutputPin>| entry.is_some();
    let ghost unwrap = |entry: Option<GpioOutputPin>| entry.unwrap();
    reveal_with_fuel(Seq::<_>::filter, 2);
    let mut i = 0;
    while i < bindings.len()
        invariant
            i <= bindings@.len() == rows.len() <= ports@.len(),
            forall|j: int| 0 <= j < rows.len() ==> #[trigger] rows[j] == output_for_port(bindings@[j], ports@[j], port),
            forall|entry: Option<GpioOutputPin>| #[trigger] some(entry) == entry.is_some(),
            forall|entry: Option<GpioOutputPin>| entry.is_some() ==> #[trigger] unwrap(entry) == entry.unwrap(),
            output@ == old(output)@ + rows.take(i as int).filter(some).map_values(unwrap),
        decreases bindings.len() - i,
    {
        let ghost previous = output@;
        let binding = bindings[i];
        let index = ports[i];
        match binding {
            GpioBinding::Output { pin, initial_high, .. } if index == port => {
                output.push(GpioOutputPin { port, pin, initial_high });
            },
            _ => {},
        }
        proof {
            let row = rows[i as int];
            assert(row == output_for_port(binding, index, port));
            let before = rows.take(i as int);
            let after = rows.take(i as int + 1);
            assert(after =~= before.push(row));
            assert(after == before.push(row));
            assert(some(row) == row.is_some());
            before.lemma_filter_push(row, some);
            if row.is_some() {
                assert(output@ == previous.push(row.unwrap()));
                let selected = before.filter(some);
                assert(after.filter(some) == selected.push(row));
                assert(unwrap(row) == row.unwrap());
                selected.lemma_push_map_commute(unwrap, row);
                Seq::push_distributes_over_add(old(output)@, selected.map_values(unwrap), row.unwrap());
            } else {
                assert(output@ == previous);
                assert(after.filter(some) == before.filter(some));
            }
            assert(output@ =~= old(output)@ + after.filter(some).map_values(unwrap));
        }
        i += 1;
    }
    assert(rows.take(i as int) =~= rows);
}

/// 設定順の接続指定から、各方向の宣言順の添字へ対応付けた結果を表す。
pub closed spec fn gpio_image_ports_match(
    image: &GpioCircuitImage, bindings: Seq<GpioBinding>, indices: Seq<usize>,
) -> bool {
    &&& indices.len() == bindings.len()
    &&& image.input_pins_model().len() == image.layout_model().input_model()
    &&& forall|i: int| 0 <= i < bindings.len() ==>
        (#[trigger] indices[i]) < (if bindings[i] is Input {
            image.layout_model().input_model()
        } else { image.layout_model().outputs_model().len() })
    &&& forall|i: int| 0 <= i < image.input_pins_model().len() ==>
        input_at(bindings, indices, i as usize) == Some(#[trigger] image.input_pins_model()[i])
    &&& image.output_pins_model() == outputs_before(bindings, indices, image.layout_model().outputs_model().len())
}

/// 解決した接続から各ポートの添字を設定順に取り出したことを表す。
pub open spec fn gpio_binding_indices_match(resolved: Seq<DevicePortBinding>, indices: Seq<usize>) -> bool {
    &&& resolved.len() == indices.len()
    &&& forall|i: int| 0 <= i < indices.len() ==> #[trigger] indices[i] == resolved[i].port.index
}

fn assemble_image<'p, 'a, 'n>(
    board: Board, bindings: &[GpioBinding<'n>], ports: &[usize], layout: PackedNorLayout32, tick_micros: u64,
) -> (result: Result<GpioCircuitImage, GpioImageError<'p, 'a, 'n>>)
    requires
        bindings@.len() == ports@.len(),
        forall|i: int| 0 <= i < bindings@.len() ==> (#[trigger] ports@[i]) < (if bindings@[i] is Input {
            layout.input_model()
        } else { layout.outputs_model().len() }),
    ensures match result {
        Ok(image) => image.board_model() == board && image.layout_model() == layout
            && image.tick_micros_model() == tick_micros && gpio_image_ports_match(&image, bindings@, ports@),
        Err(GpioImageError::MissingInput { port }) => port < layout.input_model()
            && input_at(bindings@, ports@, port).is_none()
            && forall|i: usize| i < port ==> #[trigger] input_at(bindings@, ports@, i).is_some(),
        _ => false,
    },
{
    let input_count = layout.input_count();
    let mut inputs = Vec::new();
    let mut port = 0;
    while port < input_count
        invariant
            port == inputs@.len() <= input_count == layout.input_model(),
            bindings@.len() == ports@.len(),
            forall|j: int| 0 <= j < port ==> input_at(bindings@, ports@, j as usize) == Some(#[trigger] inputs@[j]),
        decreases input_count - port,
    {
        let Some(pin) = input_pin(bindings, ports, port) else {
            assert forall|i: usize| i < port implies #[trigger] input_at(bindings@, ports@, i).is_some() by {
                assert(input_at(bindings@, ports@, i) == Some(inputs@[i as int]));
            };
            return Err(GpioImageError::MissingInput { port });
        };
        inputs.push(pin);
        port += 1;
    }
    let output_count = layout.outputs().len();
    let mut outputs = Vec::new();
    let mut port = 0;
    while port < output_count
        invariant
            port <= output_count == layout.outputs_model().len(),
            bindings@.len() == ports@.len(),
            outputs@ == outputs_before(bindings@, ports@, port as nat),
        decreases output_count - port,
    {
        append_outputs(bindings, ports, port, &mut outputs);
        assert(outputs_before(bindings@, ports@, (port + 1) as nat) == outputs@);
        port += 1;
    }
    Ok(GpioCircuitImage { board, layout, inputs, outputs, tick_micros })
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    // GPIO と UART の名前を、同じルート回路のパック済み配線配置に照合する。
    fn lower_rp_ports<'n>(
        &self, owner: ModuleBodyPosition, requests: &[DevicePortRequest<'n>],
        width_limit: u64, bit_limit: usize, gate_limit: usize,
    ) -> (result: Result<(PackedNorLayout32, Vec<usize>), GpioImageError<'p, 'a, 'n>>)
        requires self.can_resolve(),
        ensures match result {
            Ok((layout, indices)) => {
                &&& layout.source_model() <= u32::MAX
                &&& layout.gates_model().len() <= gate_limit
                &&& layout.input_model() <= bit_limit
                &&& layout.outputs_model().len() <= bit_limit
                &&& crate::netlist::wires_fit(layout.gates_model(), layout.source_model() as usize)
                &&& exists|netlist: crate::netlist::NorNetlist| #[trigger] layout.matches(&netlist)
                    && self.clocked_module_source_layout(owner, width_limit, &netlist)
                &&& exists|resolved: Vec<DevicePortBinding>|
                    #[trigger] gpio_binding_indices_match(resolved@, indices@)
                    && self.device_bindings_match(owner, width_limit, requests@, Ok(resolved))
                &&& indices@.len() == requests@.len()
                &&& forall|i: int| 0 <= i < indices@.len() ==> #[trigger] indices@[i]
                    < (if requests@[i].direction is Output { layout.input_model() } else { layout.outputs_model().len() })
                &&& forall|i: int, j: int| 0 <= i < j < indices@.len()
                    && requests@[i].direction is Output && requests@[j].direction is Output
                    ==> (#[trigger] indices@[i]) != (#[trigger] indices@[j])
            },
            Err(GpioImageError::Binding(error)) => self.device_bindings_match(owner, width_limit, requests@, Err(error)),
            Err(error) => !(error is ZeroTickPeriod) && !(error is Pin) && !(error is MissingInput),
        },
    {
        let resolved = match self.resolve_device_port_bindings(owner, width_limit, requests) {
            Ok(resolved) => resolved,
            Err(error) => return Err(GpioImageError::Binding(error)),
        };
        let circuit = match self.lower_clocked_module_with_limits(owner, width_limit, bit_limit, gate_limit) {
            Ok(Some(circuit)) => circuit,
            Ok(None) => return Err(GpioImageError::NoModule),
            Err(error) => return Err(GpioImageError::Circuit(error)),
        };
        let Some(layout) = circuit.packed_layout32() else { return Err(GpioImageError::LayoutSize); };
        if layout.source_count() as u128 > u32::MAX as u128 { return Err(GpioImageError::LayoutSize); }
        let ghost netlist = circuit.netlist_model();
        let mut indices: Vec<usize> = Vec::new();
        let mut i = 0;
        while i < resolved.len()
            invariant
                self.can_resolve(),
                layout.matches(&netlist),
                self.clocked_module_ports_match(owner, width_limit, &netlist),
                self.clocked_module_source_layout(owner, width_limit, &netlist),
                self.device_bindings_match(owner, width_limit, requests@, Ok(resolved)),
                i == indices@.len() <= resolved@.len() == requests@.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] indices@[j] == resolved@[j].port.index
                    && indices@[j] < (if requests@[j].direction is Output {
                        layout.input_model()
                    } else { layout.outputs_model().len() }),
            decreases resolved.len() - i,
        {
            let bound = &resolved[i];
            proof {
                let j = i as int;
                let request = requests@[j];
                self.device_binding_at(owner, width_limit, requests@, resolved, j);
                self.device_binding_details(owner, width_limit, request, *bound);
                self.clocked_module_port_in_layout(owner, width_limit, &netlist, &layout,
                    bound.circuit_direction, request.circuit_port, bound.port);
                assert(bound.circuit_direction == if requests@[j].direction is Output {
                    PortDirection::Input
                } else { PortDirection::Output });
            }
            indices.push(bound.port.index);
            i += 1;
        }
        proof { layout.port_slots(&netlist); }
        assert(gpio_binding_indices_match(resolved@, indices@));
        assert forall|i: int, j: int| 0 <= i < j < indices@.len() && requests@[i].direction is Output
            && requests@[j].direction is Output implies (#[trigger] indices@[i]) != (#[trigger] indices@[j]) by {
            self.device_binding_at(owner, width_limit, requests@, resolved, i);
            self.device_binding_at(owner, width_limit, requests@, resolved, j);
            self.device_binding_details(owner, width_limit, requests@[i], resolved@[i]);
            self.device_binding_details(owner, width_limit, requests@[j], resolved@[j]);
        };
        Ok((layout, indices))
    }

    /// ルートモジュールをパックした NOR 回路と GPIO 接続を組み立てる。
    ///
    /// ルートから到達する回路の型と展開は、指定の幅、ビット列長、ゲート数の上限で検査する。
    /// 入力は全ポートに GPIO を一つずつ割り当てる。出力は必要なポートだけを接続できる。
    /// 複数のピンを同じ出力へ割り当てた場合、接続指定の順を保持する。
    ///
    /// # Errors
    ///
    /// 0 の周期、ピン、ポートの照合、回路の変換、配線数、入力の未割り当ての順で診断する。
    pub fn build_rp_gpio_image<'n>(
        &self, owner: ModuleBodyPosition, board: Board, bindings: &[GpioBinding<'n>], tick_micros: u64,
        width_limit: u64, bit_limit: usize, gate_limit: usize,
    ) -> (result: Result<GpioCircuitImage, GpioImageError<'p, 'a, 'n>>)
        requires self.can_resolve(),
        ensures
            result matches Ok(image) ==> {
                &&& image.board_model() == board
                &&& image.tick_micros_model() == tick_micros
                &&& tick_micros > 0
                &&& image.layout_model().source_model() <= u32::MAX
                &&& image.layout_model().gates_model().len() <= gate_limit
                &&& image.layout_model().input_model() <= bit_limit
                &&& image.layout_model().outputs_model().len() <= bit_limit
                &&& image.input_pins_model().len() == image.layout_model().input_model()
                &&& crate::netlist::wires_fit(image.layout_model().gates_model(), image.layout_model().source_model() as usize)
                &&& super::assignments_valid(board, bindings@.map_values(|binding: GpioBinding| gpio_assignment(binding)))
                &&& exists|netlist: crate::netlist::NorNetlist| #[trigger] image.layout_model().matches(&netlist)
                    && self.clocked_module_source_layout(owner, width_limit, &netlist)
                &&& exists|resolved: Vec<DevicePortBinding>, indices: Seq<usize>|
                    #[trigger] gpio_image_ports_match(&image, bindings@, indices)
                    && self.device_bindings_match(owner, width_limit, bindings@.map_values(|binding: GpioBinding| gpio_request(binding)), Ok(resolved))
                    && #[trigger] gpio_binding_indices_match(resolved@, indices)
            },
            result matches Err(GpioImageError::ZeroTickPeriod) <==> tick_micros == 0,
            result matches Err(GpioImageError::Pin(error)) ==>
                super::first_assignment_error(board, bindings@.map_values(|binding: GpioBinding| gpio_assignment(binding)), error),
            result matches Err(GpioImageError::Binding(error)) ==>
                self.device_bindings_match(owner, width_limit, bindings@.map_values(|binding: GpioBinding| gpio_request(binding)), Err(error)),
    {
        if tick_micros == 0 { return Err(GpioImageError::ZeroTickPeriod); }
        let (assignments, requests) = requests(bindings);
        if let Err(error) = check_assignments(board, &assignments) { return Err(GpioImageError::Pin(error)); }
        let (layout, indices) = self.lower_rp_ports(owner, &requests, width_limit, bit_limit, gate_limit)?;
        let result = assemble_image(board, bindings, &indices, layout, tick_micros);
        proof {
            if let Ok(image) = &result {
                assert(gpio_image_ports_match(image, bindings@, indices@));
            }
        }
        result
    }
}

} // verus!
