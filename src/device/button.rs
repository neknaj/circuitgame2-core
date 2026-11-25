//! レベル式ボタンを共通のホストイベントとポート照会に対応させる。

use crate::project::{DevicePortRequest, DevicePortType, PortDirection};
use vstd::prelude::*;

verus! {

/// プロジェクト設定でレベル式ボタンを指定する種別名。
pub const BUTTON_KIND: &'static str = "button";

/// レベル式ボタンが回路入力を駆動するポート名。
pub const BUTTON_PORT: &'static str = "pressed";

/// レベル式ボタンへの外部入力。適用する世代と tick はイベント列が保持する。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ButtonInput {
    /// ボタンを押す。
    Press,
    /// ボタンを離す。
    Release,
}

/// `pressed` を指定の回路入力へ接続するための単一ビットの照会を返す。
///
/// 名前、方向、幅および重複駆動は `UseAliases::lower_clocked_device_vm` が検査する。
pub fn button_port_request<'a>(circuit_port: &'a str) -> (request: DevicePortRequest<'a>)
    ensures
        request.circuit_port == circuit_port,
        request.direction == PortDirection::Output,
        request.expected == DevicePortType::Bits(1),
{
    DevicePortRequest {
        circuit_port,
        direction: PortDirection::Output,
        expected: DevicePortType::Bits(1),
    }
}

} // verus!
