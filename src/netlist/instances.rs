//! 組み合わせ回路と順序回路で共通のインスタンス配線変換。

use super::Wire;
#[cfg(verus_only)]
use super::NorGate;
use vstd::prelude::*;

verus! {

/// 呼び出し先の入力を実引数で置き換え、ゲート番号を配置先の先頭から数え直す。
pub open spec fn instance_wire(wire: Wire, arguments: Seq<Wire>, base: usize) -> Wire {
    match wire {
        Wire::Input(index) => arguments[index as int],
        Wire::Constant(value) => Wire::Constant(value),
        Wire::Gate(index) => Wire::Gate((base + index) as usize),
    }
}

/// 呼び出し先の1ビット分の配線を、呼び出し元の配線に変換する。
pub(crate) fn instantiate_wire(wire: Wire, arguments: &[Wire], base: usize) -> (mapped: Wire)
    requires
        wire matches Wire::Input(index) ==> index < arguments@.len(),
        wire matches Wire::Gate(index) ==> base + index <= usize::MAX,
    ensures mapped == instance_wire(wire, arguments@, base),
{
    match wire {
        Wire::Input(index) => arguments[index],
        Wire::Constant(value) => Wire::Constant(value),
        Wire::Gate(index) => Wire::Gate(base + index),
    }
}

/// 親回路の指定区間が、子回路の全ゲートを並び順どおりに含むことを表す。
pub open spec fn instance_gates_at(callee: Seq<NorGate>, arguments: Seq<Wire>, base: usize, parent: Seq<NorGate>) -> bool {
    &&& base + callee.len() <= parent.len()
    &&& forall|i: int| 0 <= i < callee.len() ==> {
        let original = callee[i];
        let mapped = #[trigger] parent[base + i];
        mapped.left == instance_wire(original.left, arguments, base)
            && mapped.right == instance_wire(original.right, arguments, base)
    }
}

/// 親回路の末尾に別のゲートを追加しても、既存のインスタンスの区間は保たれる。
pub proof fn instance_gates_in_extension(
    callee: Seq<NorGate>, arguments: Seq<Wire>, base: usize, prefix: Seq<NorGate>, parent: Seq<NorGate>,
)
    requires instance_gates_at(callee, arguments, base, prefix), prefix.len() <= parent.len(),
        parent.take(prefix.len() as int) == prefix,
    ensures instance_gates_at(callee, arguments, base, parent),
{
    assert forall|i: int| 0 <= i < callee.len() implies {
        let gate = #[trigger] parent[base + i];
        gate.left == instance_wire(callee[i].left, arguments, base)
            && gate.right == instance_wire(callee[i].right, arguments, base)
    } by {
        assert(parent[base + i] == prefix[base + i]);
    };
}

pub open spec fn instance_gates_match(
    before: Seq<NorGate>, callee: Seq<NorGate>, arguments: Seq<Wire>, added: Seq<NorGate>,
) -> bool {
    &&& added.len() == before.len() + callee.len()
    &&& added.take(before.len() as int) == before
    &&& instance_gates_at(callee, arguments, before.len() as usize, added)
}

/// 子の出力を、ポート順と各ポート内のビット順を保って変換することを表す。
pub open spec fn instance_outputs_match(
    callee: Seq<Wire>, arguments: Seq<Wire>, base: usize, mapped: Seq<Wire>,
) -> bool {
    &&& mapped.len() == callee.len()
    &&& forall|i: int| 0 <= i < mapped.len() ==> (#[trigger] mapped[i]) == instance_wire(callee[i], arguments, base)
}

} // verus!
