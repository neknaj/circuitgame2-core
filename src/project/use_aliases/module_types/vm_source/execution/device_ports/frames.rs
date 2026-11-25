//! 共通の入力フレームと確定済み出力を、接続したポートごとに扱う。

use alloc::vec::Vec;
use vstd::prelude::*;
use vstd::slice::slice_subrange;
use crate::device::DeviceStateSession;
#[cfg(verus_only)]
use crate::netlist::ClockedVm;

use super::{ClockedDeviceVm, DevicePortBits, PortDirection};

verus! {

/// 同じ VM から分離した外部ポートと入出力フレームの幅。
pub struct DevicePortMap {
    ports: Vec<DevicePortBits>,
    input_width: usize,
    output_width: usize,
}

/// 外部ポートを読み書きできなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DevicePortIoError {
    /// フレーム全体の幅が設定と異なる。
    FrameWidth { expected: usize, actual: usize },
    /// 指定した接続がない。
    UnknownPort { request: usize },
    /// 接続先の方向が操作に合わない。
    Direction { request: usize, expected_direction: PortDirection },
    /// 渡した値の幅がポートと異なる。
    ValueWidth { request: usize, expected: usize, actual: usize },
}

pub(super) open spec fn ports_fit(
    ports: Seq<DevicePortBits>, input_width: usize, output_width: usize,
) -> bool {
    forall|i: int| 0 <= i < ports.len() ==> {
        let port = #[trigger] ports[i];
        &&& port.bits.start < port.bits.end
        &&& port.bits.end <= match port.circuit_direction {
            PortDirection::Input => input_width,
            PortDirection::Output => output_width,
        }
    }
}

impl ClockedDeviceVm {
    /// VM と、同じフレームから読み書きするポート接続を取り出す。
    pub fn into_device_session<I, R>(self) -> (result: (crate::device::DeviceEventSession<I, R>, DevicePortMap))
        ensures
            result.0.valid(),
            result.0.model().0.position_model() == (crate::time::TickPosition { generation: 0, tick: 0 }),
            result.0.model().1.requests().len() == 0,
            result.0.model().2.len() == 0,
            result.0.ids_model().next_model() == 0,
            result.1.ports_model() == self.ports_model(),
            result.1.frame_width(PortDirection::Input) == self.module_model().inputs.total_bits_model(),
            result.1.frame_width(PortDirection::Output) == self.module_model().outputs.total_bits_model(),
            result.0.model().0.vm_model().same_layout(&self.module_model().vm),
            result.1.fits_vm(&result.0.model().0.vm_model()),
            result.1.frame_width(PortDirection::Output) == result.0.model().0.output_model().len(),
    {
        proof { use_type_invariant(&self); }
        let input_width = self.module.inputs.total_bits();
        let output_width = self.module.outputs.total_bits();
        let ports = DevicePortMap { ports: self.ports, input_width, output_width };
        let ghost source = self.module.vm;
        let session = crate::device::DeviceEventSession::new(self.module.vm);
        proof {
            let circuit = session.model().0;
            let vm = circuit.vm_model();
            vm.same_layout_frame_widths(&source);
            vm.reset_snapshot(circuit.output_model());
        }
        (session, ports)
    }

    /// 初期化済みの状態を設定順に受け取り、同じ VM のポート配置と実行を返す。
    pub fn into_device_state_session<I, R, S>(self, initial: Vec<S>)
        -> (result: (DeviceStateSession<I, R, S>, DevicePortMap))
        ensures
            result.0.execution_model().valid(),
            result.0.states_model() == initial@,
            result.0.execution_model().model().0.position_model() ==
                (crate::time::TickPosition { generation: 0, tick: 0 }),
            result.1.ports_model() == self.ports_model(),
            result.1.fits_vm(&result.0.execution_model().model().0.vm_model()),
            result.1.frame_width(PortDirection::Output) == result.0.execution_model().model().0.output_model().len(),
    {
        let (execution, ports) = self.into_device_session();
        (DeviceStateSession::from_initial_execution(execution, initial), ports)
    }
}

impl DevicePortMap {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool { ports_fit(self.ports@, self.input_width, self.output_width) }

    /// 設定順のポート接続。
    pub closed spec fn ports_model(&self) -> Seq<DevicePortBits> { self.ports@ }

    /// 方向ごとのフレーム幅。
    pub closed spec fn frame_width(&self, direction: PortDirection) -> usize {
        match direction {
            PortDirection::Input => self.input_width,
            PortDirection::Output => self.output_width,
        }
    }

    /// 指定した方向のフレームに含まれるビット数を返す。
    pub fn frame_len(&self, direction: PortDirection) -> (length: usize)
        ensures length == self.frame_width(direction),
    {
        match direction {
            PortDirection::Input => self.input_width,
            PortDirection::Output => self.output_width,
        }
    }

    /// 入出力の幅が、このポート配置を用意したときと同じであることを表す。
    pub open spec fn fits_vm(&self, vm: &ClockedVm) -> bool {
        &&& self.frame_width(PortDirection::Input) == vm.external_count()
        &&& self.frame_width(PortDirection::Output) == vm.netlist_model().outputs@.len()
    }

    /// tick や reset で配線を保っていれば、引き続き同じポート配置を使える。
    pub proof fn same_layout_fits(&self, previous: &ClockedVm, current: &ClockedVm)
        requires self.fits_vm(previous), current.same_layout(previous),
        ensures self.fits_vm(current),
    {
        current.same_layout_frame_widths(previous);
    }

    /// フレーム幅、接続添字、ポート方向の順で診断する。
    pub open spec fn frame_port_error(
        &self, request: usize, length: usize, direction: PortDirection,
    ) -> Option<DevicePortIoError> {
        let expected = self.frame_width(direction);
        if length != expected {
            Some(DevicePortIoError::FrameWidth { expected, actual: length })
        } else if request >= self.ports_model().len() {
            Some(DevicePortIoError::UnknownPort { request })
        } else if self.ports_model()[request as int].circuit_direction != direction {
            Some(DevicePortIoError::Direction { request, expected_direction: direction })
        } else {
            None
        }
    }

    fn frame_port(&self, request: usize, length: usize, direction: PortDirection)
        -> (result: Result<&DevicePortBits, DevicePortIoError>)
        ensures
            result.is_ok() <==> self.frame_port_error(request, length, direction).is_none(),
            result matches Err(error) ==> self.frame_port_error(request, length, direction) == Some(error),
            result matches Ok(port) ==> {
                &&& request < self.ports_model().len()
                &&& *port == self.ports_model()[request as int]
                &&& port.circuit_direction == direction
                &&& port.bits.start < port.bits.end <= length
            },
    {
        proof { use_type_invariant(self); }
        let expected = self.frame_len(direction);
        if length != expected {
            return Err(DevicePortIoError::FrameWidth { expected, actual: length });
        }
        if request >= self.ports.len() {
            return Err(DevicePortIoError::UnknownPort { request });
        }
        let port = &self.ports[request];
        let same_direction = matches!((port.circuit_direction, direction),
            (PortDirection::Input, PortDirection::Input) | (PortDirection::Output, PortDirection::Output));
        if !same_direction {
            return Err(DevicePortIoError::Direction { request, expected_direction: direction });
        }
        Ok(port)
    }

    /// 直前に確定した回路出力から、指定したポートのビットを借りる。
    ///
    /// # Errors
    ///
    /// フレーム幅、接続添字、ポート方向をこの順で検査する。
    pub fn read_output<'a>(&self, request: usize, frame: &'a [bool])
        -> (result: Result<&'a [bool], DevicePortIoError>)
        ensures
            result.is_ok() <==> self.frame_port_error(request, frame@.len() as usize, PortDirection::Output).is_none(),
            result matches Err(error) ==>
                self.frame_port_error(request, frame@.len() as usize, PortDirection::Output) == Some(error),
            result matches Ok(bits) ==> {
                let range = self.ports_model()[request as int].bits;
                bits@ == frame@.subrange(range.start as int, range.end as int)
            },
    {
        let port = self.frame_port(request, frame.len(), PortDirection::Output)?;
        Ok(slice_subrange(frame, port.bits.start, port.bits.end))
    }

    /// 入力フレームの指定ポートに値を書き込む。ほかのビットを保持する。
    ///
    /// # Errors
    ///
    /// フレーム幅、接続添字、ポート方向、値の幅をこの順で検査する。エラー時はフレームを保持する。
    pub fn write_input(&self, request: usize, frame: &mut [bool], value: &[bool])
        -> (result: Result<(), DevicePortIoError>)
        ensures
            result.is_err() ==> final(frame)@ == old(frame)@,
            result matches Err(error) ==> {
                if let Some(reason) = self.frame_port_error(request, old(frame)@.len() as usize, PortDirection::Input) {
                    error == reason
                } else {
                    let range = self.ports_model()[request as int].bits;
                    let width = (range.end - range.start) as usize;
                    error == (DevicePortIoError::ValueWidth { request, expected: width, actual: value@.len() as usize })
                        && width != value@.len()
                }
            },
            result.is_ok() ==> {
                let range = self.ports_model()[request as int].bits;
                &&& self.frame_port_error(request, old(frame)@.len() as usize, PortDirection::Input).is_none()
                &&& range.end - range.start == value@.len()
                &&& final(frame)@.len() == old(frame)@.len()
                &&& forall|i: int| 0 <= i < old(frame)@.len() ==> (#[trigger] final(frame)@[i]) ==
                    if range.start <= i < range.end { value@[i - range.start] } else { old(frame)@[i] }
            },
    {
        let port = self.frame_port(request, frame.len(), PortDirection::Input)?;
        let start = port.bits.start;
        let end = port.bits.end;
        let width = end - start;
        if value.len() != width {
            return Err(DevicePortIoError::ValueWidth { request, expected: width, actual: value.len() });
        }

        let mut copied = 0;
        while copied < width
            invariant
                copied <= width == value@.len(),
                start + width == end <= frame@.len(),
                frame@.len() == old(frame)@.len(),
                forall|i: int| 0 <= i < frame@.len() ==> (#[trigger] frame@[i]) ==
                    if start <= i < start + copied { value@[i - start] } else { old(frame)@[i] },
            decreases width - copied,
        {
            frame[start + copied] = value[copied];
            copied += 1;
        }
        Ok(())
    }
}

} // verus!
