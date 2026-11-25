//! 実行設定のポート接続を、同じルート回路の VM 上のビット範囲へ変換する。

mod frames;
pub use frames::{DevicePortIoError, DevicePortMap};
#[cfg(verus_only)]
use frames::ports_fit;

use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

use super::{ClockedModuleVm, ClockedModuleVmError, ClockedModuleVmLimits, ModuleBodyPosition, UseAliases};
use crate::project::{DeviceBindingsError, DevicePortBinding, DevicePortRequest, PortDirection, ResolvedPortType};

verus! {

/// 回路と外部デバイスの間で受け渡すポートのビット範囲。
#[derive(Debug)]
pub struct DevicePortBits {
    /// 回路から見た方向。
    pub circuit_direction: PortDirection,
    /// 対応する方向のポート一覧での宣言順の添字。
    pub port: usize,
    /// ポートの最下位ビットから始まる半開範囲。
    pub bits: Range<usize>,
}

/// 実行する VM と、設定順に並んだ外部接続先。
pub struct ClockedDeviceVm {
    module: ClockedModuleVm,
    ports: Vec<DevicePortBits>,
}

/// 外部デバイスを接続する VM を準備できなかった理由。
#[derive(Debug)]
pub enum ClockedDeviceVmError<'p, 'a, 'n> {
    /// 指定位置にルートモジュールがない。
    NoModule,
    /// 設定した接続の名前、方向、型、または入力の駆動元に問題がある。
    Binding(DeviceBindingsError<'p, 'a, 'n>),
    /// 回路のコンパイルまたは VM の初期化に失敗した。
    Circuit(ClockedModuleVmError<'p, 'a>),
    /// 照合したポートの範囲がないか、ビット列の幅が VM の配置と一致しない。
    PortRange {
        /// 設定順で最初に範囲を得られなかった接続。
        request: usize,
    },
    /// ポートの総幅が VM の出力フレームと一致しない。
    OutputWidth {
        /// 出力ポートの総ビット数。
        layout: usize,
        /// VM の出力フレームのビット数。
        frame: usize,
    },
    /// 実行用の接続先を格納する領域を確保できなかった。
    Allocation,
}

impl ClockedDeviceVm {
    #[verifier::type_invariant]
    spec fn ready(&self) -> bool {
        &&& self.module.vm.valid()
        &&& ports_fit(self.ports@, self.module.inputs.total_bits_model(), self.module.outputs.total_bits_model())
        &&& self.module.vm.external_count() == self.module.inputs.total_bits_model()
        &&& self.module.vm.netlist_model().outputs@.len() == self.module.outputs.total_bits_model()
    }

    /// 入出力のビット配置と、初期化済みの VM。
    pub closed spec fn module_model(&self) -> ClockedModuleVm { self.module }

    /// 実行設定に並ぶ接続ごとのポート位置とビット範囲。
    pub closed spec fn ports_model(&self) -> Seq<DevicePortBits> { self.ports@ }

    /// 設定順で一つの接続先を返す。添字が範囲外なら `None` を返す。
    pub fn port(&self, request: usize) -> (result: Option<&DevicePortBits>)
        ensures
            result.is_some() <==> request < self.ports_model().len(),
            result matches Some(port) ==> *port == self.ports_model()[request as int],
    {
        if request < self.ports.len() { Some(&self.ports[request]) } else { None }
    }

    /// 実行設定順の接続先と、同じ回路の VM を取り出す。構文や設定を借用しない。
    pub fn into_parts(self) -> (result: (ClockedModuleVm, Vec<DevicePortBits>))
        ensures result.0 == self.module_model(), result.1@ == self.ports_model(),
    {
        (self.module, self.ports)
    }
}

/// ビット列なら、型の幅と配列上の範囲の長さが一致することを示す。
pub open spec fn device_range_width(bits: Range<usize>, ty: ResolvedPortType) -> bool {
    match ty {
        ResolvedPortType::Bits(width) => bits.end as int - bits.start as int == width as int,
        ResolvedPortType::Struct { .. } => true,
    }
}

fn range_width_matches(bits: &Range<usize>, ty: ResolvedPortType) -> (matches: bool)
    requires bits.start <= bits.end,
    ensures matches == device_range_width(*bits, ty),
{
    match ty {
        ResolvedPortType::Bits(width) => (bits.end - bits.start) as u128 == width as u128,
        ResolvedPortType::Struct { .. } => true,
    }
}

/// 接続先と同じ方向・添字にある VM のビット範囲を示す。
pub open spec fn device_port_bit_range(module: &ClockedModuleVm, binding: &DevicePortBinding)
    -> Option<Range<usize>>
{
    let ranges = match binding.circuit_direction {
        PortDirection::Input => module.inputs.ranges_model(),
        PortDirection::Output => module.outputs.ranges_model(),
    };
    let port = binding.port.index;
    if port < ranges.len() && device_range_width(ranges[port as int], binding.port.ty) {
        Some(ranges[port as int])
    } else {
        None
    }
}

pub open spec fn port_matches_binding(module: &ClockedModuleVm, binding: &DevicePortBinding, port: &DevicePortBits)
    -> bool
{
    let ranges = match port.circuit_direction {
        PortDirection::Input => module.inputs.ranges_model(),
        PortDirection::Output => module.outputs.ranges_model(),
    };
    &&& port.circuit_direction == binding.circuit_direction
    &&& port.port < ranges.len()
    &&& port.bits == ranges[port.port as int]
    &&& match port.circuit_direction {
        PortDirection::Input => module.inputs.earlier_ranges_end_by(port.port, port.bits.start),
        PortDirection::Output => module.outputs.earlier_ranges_end_by(port.port, port.bits.start),
    }
    &&& port.port == binding.port.index
    &&& device_port_bit_range(module, binding) == Some(port.bits)
    &&& port.bits.start < port.bits.end <= match port.circuit_direction {
        PortDirection::Input => module.inputs.total_bits_model(),
        PortDirection::Output => module.outputs.total_bits_model(),
    }
}

/// 最初に範囲の取得または幅の照合に失敗する設定位置を示す。
pub open spec fn first_bad_port_range(
    module: &ClockedModuleVm, bindings: Seq<DevicePortBinding>, request: usize,
) -> bool {
    &&& request < bindings.len()
    &&& device_port_bit_range(module, &bindings[request as int]).is_none()
    &&& forall|i: int| 0 <= i < request ==> device_port_bit_range(module, &#[trigger] bindings[i]).is_some()
}

fn place_ports(module: &ClockedModuleVm, bindings: &[DevicePortBinding])
    -> (result: Result<Vec<DevicePortBits>, Option<usize>>)
    ensures
        result matches Ok(ports) ==> {
            &&& ports@.len() == bindings@.len()
            &&& forall|i: int| 0 <= i < ports@.len() ==>
                port_matches_binding(module, &bindings@[i], &#[trigger] ports@[i])
        },
        result matches Err(Some(request)) ==> first_bad_port_range(module, bindings@, request),
{
    let mut ports = Vec::new();
    if ports.try_reserve_exact(bindings.len()).is_err() { return Err(None); }
    let mut i = 0;
    while i < bindings.len()
        invariant
            i == ports@.len() <= bindings@.len(),
            forall|j: int| 0 <= j < i ==> port_matches_binding(module, &bindings@[j], &#[trigger] ports@[j]),
        decreases bindings@.len() - i,
    {
        let binding = &bindings[i];
        let layout = match binding.circuit_direction {
            PortDirection::Input => &module.inputs,
            PortDirection::Output => &module.outputs,
        };
        let range = match layout.range(binding.port.index) {
            Some(bits) => if range_width_matches(&bits, binding.port.ty) { Some(bits) } else { None },
            None => None,
        };
        let Some(bits) = range else {
            assert forall|j: int| 0 <= j < i implies
                device_port_bit_range(module, &#[trigger] bindings@[j]).is_some() by {
                assert(port_matches_binding(module, &bindings@[j], &ports@[j]));
            }
            return Err(Some(i));
        };
        let port = DevicePortBits { circuit_direction: binding.circuit_direction, port: binding.port.index, bits };
        assert(port_matches_binding(module, binding, &port));
        let ghost before = ports@;
        ports.push(port);
        assert forall|j: int| 0 <= j <= i implies
            port_matches_binding(module, &bindings@[j], &#[trigger] ports@[j]) by {
            if j < i { assert(ports@[j] == before[j]); }
        }
        i += 1;
    }
    Ok(ports)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// VM と接続先が、設定と同じルートモジュールに対応することを示す。
    pub open spec fn device_vm_matches(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits,
        requests: Seq<DevicePortRequest>, device: &ClockedDeviceVm,
    ) -> bool {
        let module = device.module_model();
        let ports = device.ports_model();
        &&& (self.clocked_module_vm_wiring(owner, limits, &module)
            || self.clocked_module_hierarchy_vm(owner, limits, &module))
        &&& exists|bindings: Vec<DevicePortBinding>|
            #[trigger] self.device_bindings_match(owner, limits.width, requests, Ok(bindings))
            && bindings@.len() == ports.len()
            && forall|i: int| 0 <= i < ports.len() ==>
                port_matches_binding(&module, &bindings@[i], &#[trigger] ports[i])
    }

    /// ビット範囲の診断を、同じルートで得た接続とビット配置に対応付ける。
    pub open spec fn device_range_failure_witness(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits,
        requests: Seq<DevicePortRequest>, request: usize,
        bindings: Vec<DevicePortBinding>, module: ClockedModuleVm,
    ) -> bool {
        &&& self.device_bindings_match(owner, limits.width, requests, Ok(bindings))
        &&& (self.clocked_module_vm_wiring(owner, limits, &module)
            || self.clocked_module_hierarchy_vm(owner, limits, &module))
        &&& bindings@.len() == requests.len()
        &&& first_bad_port_range(&module, bindings@, request)
    }

    /// 設定順で最初に VM 上の範囲を得られなかった接続を示す。
    pub open spec fn device_port_range_failure(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits,
        requests: Seq<DevicePortRequest>, request: usize,
    ) -> bool {
        exists|bindings: Vec<DevicePortBinding>, module: ClockedModuleVm|
            #[trigger] self.device_range_failure_witness(owner, limits, requests, request, bindings, module)
    }

    /// 接続の検査とコンパイルを同じルートに対して実行し、VM と外部ポートを返す。
    ///
    /// エラーの接続添字は指定した列の位置を指す。成功時は入力を駆動するポートの重複がない。
    ///
    /// # Errors
    ///
    /// 接続、回路のコンパイル、ビット範囲の順に検査し、失敗した段階に対応するエラーを返す。
    pub fn lower_clocked_device_vm<'n>(
        &self, owner: ModuleBodyPosition, limits: ClockedModuleVmLimits, requests: &[DevicePortRequest<'n>],
    ) -> (result: Result<ClockedDeviceVm, ClockedDeviceVmError<'p, 'a, 'n>>)
        requires self.can_resolve(),
        ensures
            result matches Err(ClockedDeviceVmError::Binding(error)) ==>
                self.device_bindings_match(owner, limits.width, requests@, Err(error)),
            result matches Err(ClockedDeviceVmError::Circuit(
                ClockedModuleVmError::Hierarchy(crate::project::ClockedModuleError::Recursion(path))
            )) ==> self.clocked_hierarchy_recursion(owner, limits.width, path@),
            result matches Err(ClockedDeviceVmError::Circuit(
                ClockedModuleVmError::Endpoints(super::ClockedEndpointError::Calls(error))
            )) ==> self.module_calls_result(owner, limits.width, Err(error)),
            result matches Err(ClockedDeviceVmError::Circuit(
                ClockedModuleVmError::Endpoints(super::ClockedEndpointError::AliasCycle(sites))
            )) ==> self.clocked_module_vm_projection_cycle(owner, limits, sites@),
            result matches Err(ClockedDeviceVmError::Circuit(
                ClockedModuleVmError::InModule { owner: failed, reason }
            )) ==> {
                &&& ((*reason) matches ClockedModuleVmError::Hierarchy(
                    crate::project::ClockedModuleError::Function { call, expansion }
                ) ==> self.clocked_hierarchy_function_failure(owner, limits, failed, call, expansion))
                &&& ((*reason) matches ClockedModuleVmError::ChildStateCapacity { used, width, capacity, .. }
                    ==> capacity == limits.wiring_bits && used <= capacity && used + width > capacity)
            },
            result matches Err(ClockedDeviceVmError::NoModule) ==>
                self.module_calls_result(owner, limits.width, Ok(None)),
            result matches Ok(device) ==> {
                let module = device.module_model();
                let ports = device.ports_model();
                &&& self.device_vm_matches(owner, limits, requests@, &device)
                &&& module.vm.valid() && module.vm.initial()
                &&& module.vm.external_count() == module.inputs.total_bits_model()
                &&& module.vm.netlist_model().outputs@.len() == module.outputs.total_bits_model()
                &&& ports.len() == requests@.len()
                &&& forall|i: int, j: int| 0 <= i < j < ports.len()
                    && (#[trigger] ports[i]).circuit_direction == PortDirection::Input
                    && (#[trigger] ports[j]).circuit_direction == PortDirection::Input
                    ==> ports[i].bits.end <= ports[j].bits.start
                        || ports[j].bits.end <= ports[i].bits.start
                &&& forall|i: int| 0 <= i < ports.len() ==> {
                    let port = #[trigger] ports[i];
                    let ranges = match port.circuit_direction {
                        PortDirection::Input => module.inputs.ranges_model(),
                        PortDirection::Output => module.outputs.ranges_model(),
                    };
                    &&& port.port < ranges.len()
                    &&& port.bits == ranges[port.port as int]
                    &&& port.bits.start < port.bits.end <= match port.circuit_direction {
                        PortDirection::Input => module.inputs.total_bits_model(),
                        PortDirection::Output => module.outputs.total_bits_model(),
                    }
                    &&& port.circuit_direction == match requests@[i].direction {
                        PortDirection::Input => PortDirection::Output,
                        PortDirection::Output => PortDirection::Input,
                    }
                    &&& match requests@[i].expected {
                        crate::project::DevicePortType::Bits(width) =>
                            port.bits.end as int - port.bits.start as int == width as int,
                        crate::project::DevicePortType::Structure(_) => true,
                    }
                }
            },
            result matches Err(ClockedDeviceVmError::OutputWidth { layout, frame }) ==> layout != frame,
            result matches Err(ClockedDeviceVmError::PortRange { request }) ==>
                self.device_port_range_failure(owner, limits, requests@, request),
    {
        let bindings = match self.resolve_device_port_bindings(owner, limits.width, requests) {
            Ok(bindings) => bindings,
            Err(error) => return Err(ClockedDeviceVmError::Binding(error)),
        };
        let module = match self.lower_clocked_vm(owner, limits) {
            Ok(Some(module)) => module,
            Ok(None) => return Err(ClockedDeviceVmError::NoModule),
            Err(error) => return Err(ClockedDeviceVmError::Circuit(error)),
        };
        let layout = module.outputs.total_bits();
        let frame = module.vm.output_count();
        if layout != frame {
            return Err(ClockedDeviceVmError::OutputWidth { layout, frame });
        }
        let ports = match place_ports(&module, bindings.as_slice()) {
            Ok(ports) => ports,
            Err(Some(request)) => {
                assert(first_bad_port_range(&module, bindings@, request));
                assert(self.device_bindings_match(owner, limits.width, requests@, Ok(bindings)));
                assert(self.clocked_module_vm_wiring(owner, limits, &module)
                    || self.clocked_module_hierarchy_vm(owner, limits, &module));
                assert(bindings@.len() == requests@.len());
                assert(self.device_range_failure_witness(owner, limits, requests@, request, bindings, module));
                assert(self.device_port_range_failure(owner, limits, requests@, request));
                return Err(ClockedDeviceVmError::PortRange { request });
            },
            Err(None) => return Err(ClockedDeviceVmError::Allocation),
        };
        proof {
            assert forall|i: int, j: int| 0 <= i < j < ports@.len()
                && (#[trigger] ports@[i]).circuit_direction == PortDirection::Input
                && (#[trigger] ports@[j]).circuit_direction == PortDirection::Input
                implies ports@[i].bits.end <= ports@[j].bits.start
                    || ports@[j].bits.end <= ports@[i].bits.start by {
                let left = ports@[i].port;
                let right = ports@[j].port;
                assert(port_matches_binding(&module, &bindings@[i], &ports@[i]));
                assert(port_matches_binding(&module, &bindings@[j], &ports@[j]));
                assert(bindings@[i].port.index != bindings@[j].port.index);
                if left < right {
                    assert(module.inputs.earlier_ranges_end_by(right, ports@[j].bits.start));
                    assert(module.inputs.ranges_model()[left as int].end <= ports@[j].bits.start);
                } else {
                    assert(module.inputs.earlier_ranges_end_by(left, ports@[i].bits.start));
                    assert(module.inputs.ranges_model()[right as int].end <= ports@[i].bits.start);
                }
            }
            assert forall|i: int| 0 <= i < ports@.len() implies {
                let port = #[trigger] ports@[i];
                let ranges = match port.circuit_direction {
                    PortDirection::Input => module.inputs.ranges_model(),
                    PortDirection::Output => module.outputs.ranges_model(),
                };
                &&& port.port < ranges.len()
                &&& port.bits == ranges[port.port as int]
                &&& port.bits.start < port.bits.end <= match port.circuit_direction {
                    PortDirection::Input => module.inputs.total_bits_model(),
                    PortDirection::Output => module.outputs.total_bits_model(),
                }
                &&& port.circuit_direction == match requests@[i].direction {
                    PortDirection::Input => PortDirection::Output,
                    PortDirection::Output => PortDirection::Input,
                }
                &&& match requests@[i].expected {
                    crate::project::DevicePortType::Bits(width) =>
                        port.bits.end as int - port.bits.start as int == width as int,
                    crate::project::DevicePortType::Structure(_) => true,
                }
            } by {
                self.device_binding_at(owner, limits.width, requests@, bindings, i);
                self.device_binding_details(owner, limits.width, requests@[i], bindings@[i]);
                assert(port_matches_binding(&module, &bindings@[i], &ports@[i]));
            }
            assert(self.device_vm_matches(owner, limits, requests@, &ClockedDeviceVm { module, ports }));
        }
        Ok(ClockedDeviceVm { module, ports })
    }
}

} // verus!
