//! 実行設定に並んだ外部ポートの接続を検査する。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{DevicePortBinding, DevicePortBindingError, DevicePortType, PortDirection, UseAliases};
use crate::project::ModuleBodyPosition;

verus! {

/// 実行設定から読み取った、一つのデバイスポートの接続先。
#[derive(Clone, Copy, Debug)]
pub struct DevicePortRequest<'n> {
    /// デバイスから見た方向。
    pub direction: PortDirection,
    /// 接続するルートモジュールのポート名。
    pub circuit_port: &'n str,
    /// デバイスポートが要求する型。
    pub expected: DevicePortType<'n>,
}

/// 設定内の接続指定をまとめて検査できなかった理由。
#[derive(Debug)]
pub enum DeviceBindingsError<'p, 'a, 'n> {
    /// 一つの接続が、名前、方向または型の検査に失敗した。
    Binding {
        /// 設定順に並べた接続指定の添字。
        request: usize,
        /// 接続の診断。
        error: DevicePortBindingError<'p, 'a, 'n>,
    },
    /// 同じ回路入力を複数の接続が駆動する。
    DuplicateDriver {
        /// 最初にその入力を指定した接続の添字。
        first: usize,
        /// その入力への重複が最初に現れた接続の添字。
        later: usize,
    },
}

spec fn drives_same_input(left: DevicePortBinding, right: DevicePortBinding) -> bool {
    &&& left.circuit_direction == PortDirection::Input
    &&& right.circuit_direction == PortDirection::Input
    &&& left.port.index == right.port.index
}

spec fn no_duplicate_drivers_before(bindings: Seq<DevicePortBinding>, stop: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < stop ==> !drives_same_input(#[trigger] bindings[i], #[trigger] bindings[j])
}

spec fn first_driver_conflict(bindings: Seq<DevicePortBinding>, conflict: Option<(usize, usize)>) -> bool {
    match conflict {
        None => no_duplicate_drivers_before(bindings, bindings.len() as int),
        Some((first, later)) => {
            &&& first < later < bindings.len()
            &&& drives_same_input(bindings[first as int], bindings[later as int])
            &&& no_duplicate_drivers_before(bindings, later as int)
            &&& forall|index: int| 0 <= index < first ==>
                !drives_same_input(#[trigger] bindings[index], bindings[later as int])
        },
    }
}

fn scan_driver_conflicts(bindings: &[DevicePortBinding]) -> (result: Option<(usize, usize)>)
    ensures first_driver_conflict(bindings@, result),
{
    let mut later = 0;
    while later < bindings.len()
        invariant
            later <= bindings.len(),
            no_duplicate_drivers_before(bindings@, later as int),
        decreases bindings.len() - later,
    {
        let mut first = 0;
        while first < later
            invariant
                first <= later < bindings.len(),
                no_duplicate_drivers_before(bindings@, later as int),
                forall|i: int| 0 <= i < first ==>
                    !drives_same_input(#[trigger] bindings@[i], bindings@[later as int]),
            decreases later - first,
        {
            let left = &bindings[first];
            let right = &bindings[later];
            if matches!(left.circuit_direction, PortDirection::Input)
                && matches!(right.circuit_direction, PortDirection::Input)
                && left.port.index == right.port.index
            {
                return Some((first, later));
            }
            first += 1;
        }
        later += 1;
    }
    None
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn resolved_device_prefix(
        &self, owner: ModuleBodyPosition, max_width: u64,
        requests: Seq<DevicePortRequest>, bindings: Seq<DevicePortBinding>,
    ) -> bool {
        &&& bindings.len() <= requests.len()
        &&& forall|i: int| 0 <= i < bindings.len() ==> {
            let request = requests[i];
            self.device_port_binding_matches(owner, max_width, request.direction, request.circuit_port,
                request.expected, Ok(#[trigger] bindings[i]))
        }
    }

    /// 全接続の対応と、設定順に返す診断を表す。
    pub closed spec fn device_bindings_match(
        &self, owner: ModuleBodyPosition, max_width: u64, requests: Seq<DevicePortRequest>,
        result: Result<Vec<DevicePortBinding>, DeviceBindingsError>,
    ) -> bool {
        match result {
            Ok(bindings) => bindings@.len() == requests.len()
                && self.resolved_device_prefix(owner, max_width, requests, bindings@)
                && first_driver_conflict(bindings@, None),
            Err(DeviceBindingsError::Binding { request, error }) =>
                request < requests.len() && {
                    let item = requests[request as int];
                    self.device_port_binding_matches(owner, max_width, item.direction, item.circuit_port,
                        item.expected, Err(error))
                } && exists|prefix: Seq<DevicePortBinding>|
                    prefix.len() == request && #[trigger] self.resolved_device_prefix(owner, max_width, requests, prefix),
            Err(DeviceBindingsError::DuplicateDriver { first, later }) =>
                exists|bindings: Seq<DevicePortBinding>| bindings.len() == requests.len()
                    && #[trigger] self.resolved_device_prefix(owner, max_width, requests, bindings)
                    && first_driver_conflict(bindings, Some((first, later))),
        }
    }

    /// 一つのルート回路に対する接続指定を設定順に検査する。
    ///
    /// すべての接続が通れば、同じ順序で結果を返す。要求が空なら空の結果を返す。
    ///
    /// # Errors
    ///
    /// 最初に、個々の接続で設定順に見つかった違反を返す。個々の接続がすべて
    /// 妥当な場合は、最初に駆動元が重複した入力に対する二つの指定を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     DeviceBindingsError, DevicePortRequest, DevicePortType, ModuleBodyPosition,
    ///     PortDirection, SourceSnapshot, check_use_aliases, index_use_targets,
    ///     parse_circuit_project,
    /// };
    ///
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "main.ncg2", revision: 1,
    ///     text: "(using nor) (module main (in rx) (out tx) (def tx (nor rx rx)))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let root = ModuleBodyPosition { file: 0, entry: 1 };
    /// let read = DevicePortRequest {
    ///     direction: PortDirection::Input, circuit_port: "tx", expected: DevicePortType::Bits(1),
    /// };
    /// let drive = DevicePortRequest {
    ///     direction: PortDirection::Output, circuit_port: "rx", expected: DevicePortType::Bits(1),
    /// };
    /// assert_eq!(aliases.resolve_device_port_bindings(root, 64, &[read, read, drive]).unwrap().len(), 3);
    /// let error = aliases.resolve_device_port_bindings(root, 64, &[read, drive, read, drive]).unwrap_err();
    /// assert!(matches!(error, DeviceBindingsError::DuplicateDriver { first: 1, later: 3 }));
    /// ```
    pub fn resolve_device_port_bindings<'n>(
        &self, owner: ModuleBodyPosition, max_width: u64, requests: &[DevicePortRequest<'n>],
    ) -> (result: Result<Vec<DevicePortBinding<'p, 'a>>, DeviceBindingsError<'p, 'a, 'n>>)
        requires self.can_resolve(),
        ensures
            self.device_bindings_match(owner, max_width, requests@, result),
            result matches Ok(bindings) ==> {
                &&& bindings@.len() == requests@.len()
                &&& forall|i: int, j: int| 0 <= i < j < bindings@.len()
                    && (#[trigger] bindings@[i]).circuit_direction == PortDirection::Input
                    && (#[trigger] bindings@[j]).circuit_direction == PortDirection::Input
                    ==> bindings@[i].port.index != bindings@[j].port.index
            },
    {
        let mut bindings: Vec<DevicePortBinding<'p, 'a>> = Vec::new();
        let mut request = 0;
        while request < requests.len()
            invariant
                self.can_resolve(),
                request == bindings@.len() <= requests.len(),
                self.resolved_device_prefix(owner, max_width, requests@, bindings@),
            decreases requests.len() - request,
        {
            let item = requests[request];
            let binding = match self.resolve_device_port_binding(
                owner, max_width, item.direction, item.circuit_port, item.expected,
            ) {
                Ok(binding) => binding,
                Err(error) => return Err(DeviceBindingsError::Binding { request, error }),
            };
            bindings.push(binding);
            request += 1;
        }

        match scan_driver_conflicts(&bindings) {
            Some((first, later)) => Err(DeviceBindingsError::DuplicateDriver { first, later }),
            None => Ok(bindings),
        }
    }
}

} // verus!
