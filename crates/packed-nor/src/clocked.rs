//! バッファーを再利用し、順序 NOR の1 tick を確定して公開出力を読む。

use super::{PackedNorGate32, PackedNorPlan32, PackedNorWireError};
#[cfg(not(verus_only))]
use verus_builtin_macros::verus;
#[cfg(verus_only)]
use {
    super::{gate_value_matches, wires_fit},
    vstd::prelude::*,
};

verus! {

/// 順序回路の配線を検査したときの最初の違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedPlanError {
    /// 外部入力、ゲート、定数の共有添字を表せない。
    SourceCount,
    /// 範囲外を指すゲート配線。
    Gate(PackedNorWireError),
    /// 範囲外を指す最初の公開出力。
    Output {
        /// 公開出力の宣言順の添字。
        port: usize,
        /// 公開出力が参照した配線番号。
        wire: usize,
    },
}

/// 1 tick の実行に渡したバッファーの違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedTickError {
    /// 入力・状態・定数のバッファー長が計画と合わない。
    Sources,
    /// 次のゲート値を書くバッファー長がゲート数と合わない。
    Next,
    /// 公開出力バッファー長がポート数と合わない。
    Outputs,
    /// false または true の定数ワードが正しくない。
    Constants,
}

/// 入力・ゲート・定数を共有番号で参照する、検査済みの順序回路。
///
/// 外部入力、ゲート状態、定数 false・true の順に同じバッファーへ並べる。
/// 配線表と公開出力の参照は元データを借用する。
pub struct PackedClockedNorPlan32<'a> {
    kernel: PackedNorPlan32<'a>,
    input_count: usize,
    ports: &'a [usize],
}

pub open spec fn clocked_ports_fit(ports: Seq<usize>, sources: usize) -> bool {
    forall|i: int| 0 <= i < ports.len() ==> #[trigger] ports[i] < sources
}

/// 確定後の状態と公開出力が、与えた入力と確定前の状態に対応する。
pub open spec fn packed_clocked_tick_matches(
    gates: Seq<PackedNorGate32>, input_count: nat, ports: Seq<usize>,
    before: Seq<u32>, after: Seq<u32>, output: Seq<u32>,
) -> bool {
    &&& before.len() == after.len() == input_count + gates.len() + 2
    &&& output.len() == ports.len()
    &&& forall|i: int| 0 <= i < gates.len()
        ==> #[trigger] gate_value_matches(gates[i], before, after[input_count + i])
    &&& forall|i: int| 0 <= i < before.len() && (i < input_count || i >= input_count + gates.len())
        ==> #[trigger] after[i] == before[i]
    &&& forall|i: int| 0 <= i < ports.len() ==> #[trigger] output[i] == after[ports[i] as int]
}

/// バッファー長と定数を検査順に照合して得られるエラー。
pub open spec fn clocked_tick_error(sources: Seq<u32>, next: Seq<u32>, output: Seq<u32>,
    source_count: usize, gates: nat, ports: nat) -> Option<ClockedTickError> {
    if sources.len() != source_count { Some(ClockedTickError::Sources) }
    else if next.len() != gates { Some(ClockedTickError::Next) }
    else if output.len() != ports { Some(ClockedTickError::Outputs) }
    else if sources[source_count - 2] != 0 || sources[source_count - 1] != u32::MAX {
        Some(ClockedTickError::Constants)
    } else { None }
}

impl<'a> PackedClockedNorPlan32<'a> {
    /// 計画に含まれる外部入力数を表す。
    pub closed spec fn input_model(&self) -> nat { self.input_count as nat }

    /// 計画に含まれる配線数を表す。
    pub closed spec fn source_model(&self) -> usize { self.kernel.source_count_model() }

    /// ゲートをその確定順で表す。
    pub closed spec fn gates_model(&self) -> Seq<PackedNorGate32> { self.kernel.gates_model() }

    /// 公開出力が参照する配線を宣言順で表す。
    pub closed spec fn ports_model(&self) -> Seq<usize> { self.ports@ }

    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        &&& self.source_model() == self.input_model() + self.gates_model().len() + 2
        &&& clocked_ports_fit(self.ports_model(), self.source_model())
    }

    /// 共有配線番号でゲートと公開出力を検査する。
    ///
    /// # Errors
    ///
    /// 配線数の表現範囲、ゲート配線、公開出力の順で最初の違反を返す。
    pub fn new(input_count: usize, gates: &'a [PackedNorGate32], ports: &'a [usize])
        -> (result: Result<Self, ClockedPlanError>)
        ensures
            result.is_ok() <==> input_count as int + gates@.len() + 2 <= usize::MAX
                && wires_fit(gates@, (input_count as int + gates@.len() + 2) as usize)
                && clocked_ports_fit(ports@, (input_count as int + gates@.len() + 2) as usize),
            match result {
                Ok(plan) => {
                    &&& plan.input_model() == input_count
                    &&& plan.gates_model() == gates@
                    &&& plan.ports_model() == ports@
                    &&& plan.source_model() == input_count as int + gates@.len() + 2
                },
                Err(ClockedPlanError::SourceCount) =>
                    input_count as int + gates@.len() + 2 > usize::MAX,
                Err(ClockedPlanError::Gate(error)) => {
                    let count = input_count as int + gates@.len() + 2;
                    &&& count <= usize::MAX
                    &&& error.gate < gates.len()
                    &&& wires_fit(gates@.take(error.gate as int), count as usize)
                    &&& error.wire >= count
                    &&& error.wire == if gates@[error.gate as int].left >= count {
                        gates@[error.gate as int].left
                    } else { gates@[error.gate as int].right }
                },
                Err(ClockedPlanError::Output { port, wire }) => {
                    let count = input_count as int + gates@.len() + 2;
                    &&& count <= usize::MAX
                    &&& wires_fit(gates@, count as usize)
                    &&& port < ports.len()
                    &&& clocked_ports_fit(ports@.take(port as int), count as usize)
                    &&& wire == ports@[port as int] && wire >= count
                },
            },
    {
        let Some(state_end) = input_count.checked_add(gates.len()) else {
            return Err(ClockedPlanError::SourceCount);
        };
        let Some(source_count) = state_end.checked_add(2) else {
            return Err(ClockedPlanError::SourceCount);
        };
        let kernel = match PackedNorPlan32::new(gates, source_count) {
            Ok(kernel) => kernel,
            Err(error) => return Err(ClockedPlanError::Gate(error)),
        };
        let mut port = 0;
        while port < ports.len()
            invariant
                port <= ports.len(),
                source_count == input_count as int + gates@.len() + 2,
                wires_fit(gates@, source_count),
                clocked_ports_fit(ports@.take(port as int), source_count),
            decreases ports.len() - port,
        {
            let wire = ports[port];
            if wire >= source_count {
                assert(ports@[port as int] >= source_count);
                assert(!clocked_ports_fit(ports@, source_count));
                return Err(ClockedPlanError::Output { port, wire });
            }
            assert forall|i: int| 0 <= i <= port implies #[trigger] ports@[i] < source_count by {
                if i < port { assert(ports@.take(port as int)[i] == ports@[i]); }
            };
            port += 1;
        }
        assert(ports@.take(port as int) =~= ports@);
        Ok(Self { kernel, input_count, ports })
    }

    /// 前のゲート状態から新しいゲート状態を求め、公開出力を確定する。
    ///
    /// `source` の末尾には定数 false の `0` と true の `u32::MAX` を置く。
    /// 成功時はゲート状態を更新し、公開出力には同じ tick の新しい状態を使う。
    ///
    /// # Errors
    ///
    /// 配列長を `source`、`next`、`output` の順で検査し、その後で定数を検査する。
    /// 失敗時はどのバッファーも変更しない。
    pub fn step(&self, source: &mut [u32], next: &mut [u32], output: &mut [u32])
        -> (result: Result<(), ClockedTickError>)
        ensures
            match clocked_tick_error(old(source)@, old(next)@, old(output)@,
                self.source_model(), self.gates_model().len(), self.ports_model().len()) {
                Some(error) => result == Err(error) && final(source)@ == old(source)@
                    && final(next)@ == old(next)@ && final(output)@ == old(output)@,
                None => result == Ok(())
                    && final(next)@ == final(source)@.subrange(self.input_model() as int,
                        self.input_model() as int + self.gates_model().len() as int)
                    && packed_clocked_tick_matches(self.gates_model(), self.input_model(), self.ports_model(),
                        old(source)@, final(source)@, final(output)@),
            },
    {
        proof { use_type_invariant(self); }
        if source.len() != self.kernel.source_count {
            return Err(ClockedTickError::Sources);
        }
        if next.len() != self.kernel.gates.len() {
            return Err(ClockedTickError::Next);
        }
        if output.len() != self.ports.len() {
            return Err(ClockedTickError::Outputs);
        }
        if source[source.len() - 2] != 0 || source[source.len() - 1] != u32::MAX {
            return Err(ClockedTickError::Constants);
        }
        let Ok(()) = self.kernel.step(source, next) else { unreachable!() };
        let ghost before = old(source)@;
        let mut gate = 0;
        while gate < next.len()
            invariant
                gate <= next.len() == self.gates_model().len(),
                source.len() == before.len() == self.input_count as int + next.len() as int + 2,
                forall|i: int| 0 <= i < source.len() ==> #[trigger] source@[i]
                    == if self.input_count <= i < self.input_count + gate { next@[i - self.input_count] }
                        else { before[i] },
            decreases next.len() - gate,
        {
            source[self.input_count + gate] = next[gate];
            gate += 1;
        }
        assert(next@ =~= source@.subrange(self.input_count as int, (self.input_count + next.len()) as int));
        let mut port = 0;
        while port < output.len()
            invariant
                port <= output.len() == self.ports_model().len(),
                source.len() == self.source_model(),
                clocked_ports_fit(self.ports_model(), self.source_model()),
                forall|i: int| 0 <= i < port ==> #[trigger] output@[i] == source@[self.ports_model()[i] as int],
            decreases output.len() - port,
        {
            output[port] = source[self.ports[port]];
            port += 1;
        }
        assert forall|i: int| 0 <= i < self.gates_model().len() implies
            #[trigger] gate_value_matches(self.gates_model()[i], before, source@[self.input_count + i]) by {
            assert(source@[self.input_count + i] == next@[i]);
        };
        Ok(())
    }
}

} // verus!
