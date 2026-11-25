//! GPIO とバイト転送を行う周辺機能のポートを、回路の配線表へ対応付ける。

use alloc::vec::Vec;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

use super::{DevicePortRequest, DevicePortType, GpioBinding, GpioOutputPin, PortDirection,
    append_outputs, input_pin};
#[cfg(verus_only)]
use super::{gpio_request, input_at, outputs_before};

verus! {

/// 宣言順の各回路入力を駆動する信号。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PeripheralInputSource {
    /// ボードの GPIO。
    Gpio(u8),
    /// 回路へ渡す周辺機能のポート列での添字。
    Controller(usize),
}

pub(super) struct PeripheralPorts {
    pub(super) inputs: Vec<PeripheralInputSource>,
    pub(super) gpio_outputs: Vec<GpioOutputPin>,
    pub(super) controller_outputs: Vec<usize>,
}

/// 送受信のデータ配線は、制御用のヘッダーに続く同じバイト数を表す。
pub(super) open spec fn peripheral_port_capacity(to: int, from: int, header_to: int, header_from: int, bytes: int) -> bool {
    1 <= bytes <= 255 && to == header_to + 8 * bytes && from == header_from + 8 * bytes
}

pub(super) fn port_capacity(to: usize, from: usize, header_to: usize, header_from: usize) -> (result: Option<u8>)
    ensures result.is_some() <==> exists|bytes: int|
        peripheral_port_capacity(to as int, from as int, header_to as int, header_from as int, bytes),
        result matches Some(bytes) ==>
            peripheral_port_capacity(to as int, from as int, header_to as int, header_from as int, bytes as int),
{
    if to < header_to || from < header_from { return None; }
    let bits = to - header_to;
    let bytes = bits / 8;
    if bits != from - header_from || bits % 8 != 0 || bytes == 0 || bytes > 255 {
        return None;
    }
    assert(peripheral_port_capacity(to as int, from as int, header_to as int, header_from as int, bytes as int));
    Some(bytes as u8)
}

spec fn bit_request<'n>(name: &'n str, direction: PortDirection) -> DevicePortRequest<'n> {
    DevicePortRequest { direction, circuit_port: name, expected: DevicePortType::Bits(1) }
}

/// GPIO、回路入力、回路出力の順でポート照会を並べる。
pub(super) closed spec fn peripheral_image_requests<'n>(
    gpio: Seq<GpioBinding<'n>>, to: Seq<&'n str>, from: Seq<&'n str>,
) -> Seq<DevicePortRequest<'n>> {
    gpio.map_values(|binding: GpioBinding| gpio_request(binding))
        + (to.map_values(|name: &str| bit_request(name, PortDirection::Output))
        + from.map_values(|name: &str| bit_request(name, PortDirection::Input)))
}

pub(super) proof fn peripheral_output_direction<'n>(
    gpio: Seq<GpioBinding<'n>>, to: Seq<&'n str>, from: Seq<&'n str>, i: int,
)
    requires gpio.len() + to.len() <= i < gpio.len() + to.len() + from.len(),
    ensures peripheral_image_requests(gpio, to, from)[i].direction is Input,
{
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

pub(super) fn append_port_requests<'n>(
    _gpio: &[GpioBinding<'n>], to: &[&'n str], from: &[&'n str], list: &mut Vec<DevicePortRequest<'n>>,
)
    requires old(list)@ == _gpio@.map_values(|binding: GpioBinding| gpio_request(binding)),
    ensures final(list)@ == peripheral_image_requests(_gpio@, to@, from@),
        final(list)@.len() == _gpio@.len() + to@.len() + from@.len(),
{
    append_requests(to, PortDirection::Output, list);
    append_requests(from, PortDirection::Input, list);
    assert(list@ =~= peripheral_image_requests(_gpio@, to@, from@));
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
    gpio: Seq<GpioBinding>, indices: Seq<usize>, controller: Seq<usize>, port: usize,
    source: Option<PeripheralInputSource>,
) -> bool {
    match input_at(gpio, indices, port) {
        Some(pin) => source == Some(PeripheralInputSource::Gpio(pin)),
        None => controller_input_at(controller, port, match source {
            Some(PeripheralInputSource::Controller(i)) => Some(i),
            _ => None,
        }) && !(source matches Some(PeripheralInputSource::Gpio(_))),
    }
}

/// 入力駆動元と出力ポート番号が、名前を解決した配線表に対応する。
pub(super) closed spec fn peripheral_ports_match(
    ports: (Seq<PeripheralInputSource>, Seq<GpioOutputPin>, Seq<usize>),
    gpio: Seq<GpioBinding>, to: nat, from: nat, indices: Seq<usize>, input_count: nat, output_count: nat,
) -> bool {
    let (inputs, gpio_outputs, controller_outputs) = ports;
    let split = gpio.len() + to;
    &&& indices.len() == split + from
    &&& inputs.len() == input_count
    &&& forall|i: int| 0 <= i < inputs.len() ==>
        matches_input(gpio, indices, indices.subrange(gpio.len() as int, split as int), i as usize,
            Some(#[trigger] inputs[i]))
    &&& gpio_outputs == outputs_before(gpio, indices, output_count)
    &&& controller_outputs == indices.skip(split as int)
    &&& forall|i: int| 0 <= i < controller_outputs.len() ==>
        #[trigger] controller_outputs[i] < output_count
}

pub(super) proof fn peripheral_port_bounds(
    ports: (Seq<PeripheralInputSource>, Seq<GpioOutputPin>, Seq<usize>),
    gpio: Seq<GpioBinding>, to: nat, from: nat, indices: Seq<usize>, input_count: nat, output_count: nat,
)
    requires peripheral_ports_match(ports, gpio, to, from, indices, input_count, output_count),
    ensures
        ports.0.len() == input_count,
        ports.2.len() == from,
        forall|i: int| 0 <= i < ports.0.len() ==> match #[trigger] ports.0[i] {
            PeripheralInputSource::Controller(j) => j < to,
            PeripheralInputSource::Gpio(_) => true,
        },
        forall|i: int| 0 <= i < ports.2.len() ==> (#[trigger] ports.2[i]) < output_count,
{
}

/// 指定の入力に駆動元がなく、それより前の入力はすべて接続されている。
spec fn missing_input_first(
    gpio: Seq<GpioBinding>, indices: Seq<usize>, count: nat, prefix: Seq<PeripheralInputSource>, port: usize,
) -> bool {
    let controller = indices.subrange(gpio.len() as int, (gpio.len() + count) as int);
    &&& matches_input(gpio, indices, controller, port, None)
    &&& prefix.len() == port
    &&& forall|i: int| 0 <= i < port ==>
            matches_input(gpio, indices, controller, i as usize, Some(#[trigger] prefix[i]))
}

/// 駆動元のない最初の入力を表す。
pub(super) closed spec fn missing_input(
    gpio: Seq<GpioBinding>, indices: Seq<usize>, count: nat, port: usize,
) -> bool {
    exists|prefix: Seq<PeripheralInputSource>|
        #[trigger] missing_input_first(gpio, indices, count, prefix, port)
}

/// 解決済みの添字を回路の宣言順へ射影する。駆動元のない最初の入力を診断する。
pub(super) fn project_ports(
    gpio: &[GpioBinding], indices: &[usize], split: usize, input_count: usize, output_count: usize,
) -> (result: Result<PeripheralPorts, usize>)
    requires gpio@.len() <= split <= indices@.len(),
        forall|i: int| split <= i < indices@.len() ==> #[trigger] indices@[i] < output_count,
    ensures
        result matches Ok(ports) ==> peripheral_ports_match(
            (ports.inputs@, ports.gpio_outputs@, ports.controller_outputs@),
            gpio@, (split - gpio@.len()) as nat, (indices@.len() - split) as nat, indices@,
            input_count as nat, output_count as nat),
        result matches Err(port) ==> port < input_count
            && missing_input(gpio@, indices@, (split - gpio@.len()) as nat, port),
{
    let controller = slice_subrange(indices, gpio.len(), split);
    let mut inputs = Vec::new();
    let mut i = 0;
    while i < input_count
        invariant i == inputs@.len() <= input_count,
            gpio@.len() <= split <= indices@.len(),
            controller@ == indices@.subrange(gpio@.len() as int, split as int),
            forall|j: int| 0 <= j < i ==>
                matches_input(gpio@, indices@, controller@, j as usize, Some(#[trigger] inputs@[j])),
        decreases input_count - i,
    {
        let source = if let Some(pin) = input_pin(gpio, indices, i) { PeripheralInputSource::Gpio(pin) }
            else if let Some(index) = controller_input(controller, i) { PeripheralInputSource::Controller(index) }
            else {
                assert(i < input_count);
                assert(matches_input(gpio@, indices@, controller@, i, None));
                assert(missing_input_first(gpio@, indices@, (split - gpio@.len()) as nat, inputs@, i));
                assert(missing_input(gpio@, indices@, (split - gpio@.len()) as nat, i));
                return Err(i);
            };
        assert(matches_input(gpio@, indices@, controller@, i, Some(source)));
        inputs.push(source);
        i += 1;
    }

    let mut gpio_outputs = Vec::new();
    let mut i = 0;
    while i < output_count
        invariant i <= output_count, gpio@.len() <= indices@.len(),
            gpio_outputs@ == outputs_before(gpio@, indices@, i as nat),
        decreases output_count - i,
    {
        append_outputs(gpio, indices, i, &mut gpio_outputs);
        assert(outputs_before(gpio@, indices@, (i + 1) as nat) == gpio_outputs@);
        i += 1;
    }
    let mut controller_outputs = Vec::new();
    let mut i = split;
    while i < indices.len()
        invariant split <= i <= indices@.len(),
            controller_outputs@ == indices@.subrange(split as int, i as int),
        decreases indices.len() - i,
    {
        controller_outputs.push(indices[i]);
        assert(controller_outputs@ =~= indices@.subrange(split as int, i as int + 1));
        i += 1;
    }
    assert(controller_outputs@ =~= indices@.skip(split as int));
    assert forall|j: int| 0 <= j < controller_outputs@.len() implies
        #[trigger] controller_outputs@[j] < output_count by {
        assert(controller_outputs@[j] == indices@[split + j]);
    };
    Ok(PeripheralPorts { inputs, gpio_outputs, controller_outputs })
}

} // verus!
