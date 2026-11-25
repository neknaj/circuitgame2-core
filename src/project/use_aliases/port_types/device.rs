//! 外部デバイスのポートと、実行する回路のポートを照合する。

use super::{NamedRoutinePort, PortDirection, ResolvedPortType, RoutinePortLookup, TypedSignatureError, UseAliases};
use crate::project::declarations::key_of;
#[cfg(verus_only)]
use crate::project::declarations::form_key;
#[cfg(verus_only)]
use crate::project::name_keys::key_view;
use crate::project::{ModuleBodyPosition, NameKey};
use crate::syntax::circuit::Head;
use vstd::prelude::*;

verus! {

/// デバイス設定とルートモジュールのポートが対応した結果。
#[derive(Debug)]
pub struct DevicePortBinding<'p, 'a> {
    /// 回路から見たポートの方向。
    pub circuit_direction: PortDirection,
    /// その方向のポート一覧での添字、元ソース位置、解決済みの型。
    pub port: NamedRoutinePort<'p, 'a>,
}

/// デバイスが要求するポート型。
#[derive(Clone, Copy, Debug)]
pub enum DevicePortType<'n> {
    /// 必要なビット幅。
    Bits(u64),
    /// 接続する回路と同じプロジェクトにある構造体の完全修飾名。
    Structure(NameKey<'n>),
}

/// ビット幅または同じプロジェクトの構造体名で照合する。
pub closed spec fn device_port_types_match(actual: ResolvedPortType, expected: DevicePortType) -> bool {
    match (actual, expected) {
        (ResolvedPortType::Bits(width), DevicePortType::Bits(required)) => width == required,
        (ResolvedPortType::Struct { form, .. }, DevicePortType::Structure(name)) =>
            key_view(form_key(*form)) == key_view(name),
        _ => false,
    }
}

fn same_device_port_type(actual: ResolvedPortType, expected: DevicePortType) -> (same: bool)
    ensures same == device_port_types_match(actual, expected),
{
    match (actual, expected) {
        (ResolvedPortType::Bits(width), DevicePortType::Bits(required)) => width == required,
        (ResolvedPortType::Struct { form, .. }, DevicePortType::Structure(name)) =>
            key_of(form).same_name(name),
        _ => false,
    }
}

/// 外部デバイスのポートを設定どおりに接続できなかった理由。
#[derive(Debug)]
pub enum DevicePortBindingError<'p, 'a, 'n> {
    /// 指定位置にルートとして使える `module` がない。
    NoModule,
    /// 回路の署名に違反がある。
    Signature(TypedSignatureError<'p, 'a>),
    /// 指定した回路ポート名が見つからない。
    UnknownName,
    /// 指定した名前は反対方向にだけ宣言されている。
    OppositeDirection(NamedRoutinePort<'p, 'a>),
    /// デバイス側が必要とする型と回路ポートの型が一致しない。
    TypeMismatch {
        /// デバイスが要求したポート型。
        expected: DevicePortType<'n>,
        /// 実際に見つかった回路ポートの型と元の位置。
        actual: NamedRoutinePort<'p, 'a>,
    },
}

/// デバイスが読むポートには回路出力を、駆動するポートには回路入力を対応させる。
pub open spec fn matching_circuit_direction(device: PortDirection) -> PortDirection {
    match device {
        PortDirection::Input => PortDirection::Output,
        PortDirection::Output => PortDirection::Input,
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn device_root_is_module(&self, owner: ModuleBodyPosition) -> bool {
        let circuits = self.targets.project_model().circuits_model();
        &&& owner.file < circuits.len()
        &&& owner.entry < circuits[owner.file as int].syntax.entries@.len()
        &&& circuits[owner.file as int].syntax.entries@[owner.entry as int].head == Head::Module
    }

    /// ルートの種別、方向別のポート照会、型比較の結果を表す。
    pub closed spec fn device_port_binding_matches(
        &self, owner: ModuleBodyPosition, max_width: u64, device: PortDirection, word: &str,
        expected: DevicePortType, result: Result<DevicePortBinding, DevicePortBindingError>,
    ) -> bool {
        let direction = matching_circuit_direction(device);
        if !self.device_root_is_module(owner) {
            result is Err && result->Err_0 is NoModule
        } else {
            match result {
                Ok(binding) => binding.circuit_direction == direction
                    && device_port_types_match(binding.port.ty, expected)
                    && self.routine_port_lookup_matches(owner.file, owner.entry, max_width, direction, word,
                        Ok(RoutinePortLookup::Found(binding.port))),
                Err(error) => match error {
                    DevicePortBindingError::NoModule =>
                        self.routine_port_lookup_matches(owner.file, owner.entry, max_width, direction, word,
                            Ok(RoutinePortLookup::NoSignature)),
                    DevicePortBindingError::Signature(diagnostic) =>
                        self.routine_port_lookup_matches(owner.file, owner.entry, max_width, direction, word,
                            Err(diagnostic)),
                    DevicePortBindingError::UnknownName =>
                        self.routine_port_lookup_matches(owner.file, owner.entry, max_width, direction, word,
                            Ok(RoutinePortLookup::UnknownName)),
                    DevicePortBindingError::OppositeDirection(port) =>
                        self.routine_port_lookup_matches(owner.file, owner.entry, max_width, direction, word,
                            Ok(RoutinePortLookup::OppositeDirection(port))),
                    DevicePortBindingError::TypeMismatch { expected: required, actual } =>
                        required == expected && !device_port_types_match(actual.ty, expected)
                        && self.routine_port_lookup_matches(owner.file, owner.entry, max_width, direction, word,
                            Ok(RoutinePortLookup::Found(actual))),
                },
            }
        }
    }

    /// 照合済みポートの回路側の方向、型、名前を取り出す。
    pub proof fn device_binding_details(
        &self, owner: ModuleBodyPosition, max_width: u64, request: super::DevicePortRequest,
        binding: DevicePortBinding,
    )
        requires self.device_port_binding_matches(owner, max_width, request.direction,
            request.circuit_port, request.expected, Ok(binding)),
        ensures
            binding.circuit_direction == matching_circuit_direction(request.direction),
            device_port_types_match(binding.port.ty, request.expected),
            request.expected matches DevicePortType::Bits(width) ==> binding.port.ty == ResolvedPortType::Bits(width),
            self.routine_port_lookup_matches(owner.file, owner.entry, max_width, binding.circuit_direction,
                request.circuit_port, Ok(RoutinePortLookup::Found(binding.port))),
    {
    }

    /// ルートモジュールの名前付きポートを、デバイス側の方向と型に照合する。
    ///
    /// デバイス側の入力は回路の出力を読み、デバイス側の出力は回路の入力を駆動する。
    /// 構造体型の指定は、ルートと同じプロジェクトにある完全修飾名を指す。
    ///
    /// # Errors
    ///
    /// ルート、署名、名前、方向または型の条件が合わない場合に診断を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     DevicePortBindingError, DevicePortType, ModuleBodyPosition, PortDirection,
    ///     SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    ///
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "main.ncg2", revision: 1,
    ///     text: "(using nor) (module main (in rx) (out tx) (def tx (nor rx rx)))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let root = ModuleBodyPosition { file: 0, entry: 1 };
    /// let tx = aliases.resolve_device_port_binding(
    ///     root, 64, PortDirection::Input, "tx", DevicePortType::Bits(1),
    /// ).unwrap();
    /// assert_eq!(tx.circuit_direction, PortDirection::Output);
    /// assert!(matches!(
    ///     aliases.resolve_device_port_binding(
    ///         root, 64, PortDirection::Output, "rx", DevicePortType::Bits(2),
    ///     ),
    ///     Err(DevicePortBindingError::TypeMismatch { expected: DevicePortType::Bits(2), .. }),
    /// ));
    /// ```
    pub fn resolve_device_port_binding<'n>(
        &self, owner: ModuleBodyPosition, max_width: u64, device: PortDirection, word: &str,
        expected: DevicePortType<'n>,
    ) -> (result: Result<DevicePortBinding<'p, 'a>, DevicePortBindingError<'p, 'a, 'n>>)
        requires self.can_resolve(),
        ensures
            self.device_port_binding_matches(owner, max_width, device, word, expected, result),
            result matches Ok(binding) ==> binding.circuit_direction == matching_circuit_direction(device)
                && device_port_types_match(binding.port.ty, expected),
    {
        let project = self.targets.project();
        let circuits = project.circuits();
        if owner.file >= circuits.len() {
            return Err(DevicePortBindingError::NoModule);
        }
        let entries = circuits[owner.file].syntax.entries.as_slice();
        assert(entries@ == project.circuits_model()[owner.file as int].syntax.entries@);
        if owner.entry >= entries.len() || !matches!(entries[owner.entry].head, Head::Module) {
            return Err(DevicePortBindingError::NoModule);
        }
        assert(self.device_root_is_module(owner));
        let circuit_direction = match device {
            PortDirection::Input => PortDirection::Output,
            PortDirection::Output => PortDirection::Input,
        };
        match self.resolve_routine_port(owner.file, owner.entry, max_width, circuit_direction, word) {
            Ok(RoutinePortLookup::Found(port)) => {
                if same_device_port_type(port.ty, expected) {
                    Ok(DevicePortBinding { circuit_direction, port })
                } else {
                    Err(DevicePortBindingError::TypeMismatch { expected, actual: port })
                }
            },
            Ok(RoutinePortLookup::OppositeDirection(port)) => Err(DevicePortBindingError::OppositeDirection(port)),
            Ok(RoutinePortLookup::UnknownName) => Err(DevicePortBindingError::UnknownName),
            Ok(RoutinePortLookup::NoSignature) => Err(DevicePortBindingError::NoModule),
            Err(error) => Err(DevicePortBindingError::Signature(error)),
        }
    }
}

} // verus!
