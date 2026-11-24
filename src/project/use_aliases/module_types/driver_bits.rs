//! 型に沿って配置した信号のビットを、tick 実行用の配線へ変換する。

use super::ClockedWireDriver;
use crate::netlist::{PortBitLayout, Wire};
use crate::project::{BitSelectionError, CheckedBitSelection, OutputDriver, check_bit_selection};
#[cfg(verus_only)]
use crate::project::{bit_selection_matches, selected_bit_in_range, selected_bits_values};
use alloc::vec::Vec;
#[cfg(verus_only)]
use core::ops::Range;
use vstd::prelude::*;

verus! {

/// 信号からビット配線を取り出せなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClockedDriverBitsError {
    /// 入力ポートまたは定義スロットが配置に存在しない。
    Driver(OutputDriver),
    /// 選択数、刻み、または選択範囲に違反がある。
    Selection(BitSelectionError),
    /// 選択の末尾として保持していた添字が、開始位置・選択数・刻みから求めた値と異なる。
    Last {
        /// 開始位置・選択数・刻みから計算した末尾の添字。
        expected: u64,
        /// 引数が保持していた末尾の添字。
        actual: u64,
    },
    /// 配線列が対象環境の配列に収まらない。
    Capacity {
        /// 必要な配線数。
        count: u64,
        /// この環境で配列に保持できる配線数の上限。
        limit: usize,
    },
    /// 配線列のメモリを確保できなかった。
    Allocation,
}

/// 平坦化したビット番号に対して、元の信号が指す配線の種類を保つ。
pub open spec fn clocked_driver_bit(driver: OutputDriver, index: usize) -> ClockedWireDriver {
    match driver {
        OutputDriver::Input(_) => ClockedWireDriver::Terminal(Wire::Input(index)),
        OutputDriver::Definition(_) => ClockedWireDriver::Alias(index),
    }
}

pub(super) fn mapped_driver_bit(driver: OutputDriver, index: usize) -> (wire: ClockedWireDriver)
    ensures wire == clocked_driver_bit(driver, index),
{
    match driver {
        OutputDriver::Input(_) => ClockedWireDriver::Terminal(Wire::Input(index)),
        OutputDriver::Definition(_) => ClockedWireDriver::Alias(index),
    }
}

spec fn driver_range(inputs: &PortBitLayout, definitions: &PortBitLayout, driver: OutputDriver) -> Option<Range<usize>> {
    let (ranges, slot) = match driver {
        OutputDriver::Input(port) => (inputs.ranges_model(), port),
        OutputDriver::Definition(slot) => (definitions.ranges_model(), slot),
    };
    if slot < ranges.len() { Some(ranges[slot as int]) } else { None }
}

spec fn driver_bits_capacity() -> usize {
    let element_size = vstd::layout::size_of::<ClockedWireDriver>();
    if element_size == 0 { usize::MAX } else { (isize::MAX as nat / element_size) as usize }
}

/// 配線が開始位置と刻みに従うこと、または最初に検出した違反を表す。
pub closed spec fn clocked_driver_bits_result(
    inputs: &PortBitLayout, definitions: &PortBitLayout, driver: OutputDriver,
    selection: Option<CheckedBitSelection>, result: Result<Vec<ClockedWireDriver>, ClockedDriverBitsError>,
) -> bool {
    match driver_range(inputs, definitions, driver) {
        None => result == Err(ClockedDriverBitsError::Driver(driver)),
        Some(range) => {
            let width = (range.end - range.start) as u64;
            let (start, count, stride, last) = match selection {
                Some(selection) => (selection.start, selection.count, selection.stride, selection.last),
                None => (0u64, width, 1u64, (width - 1) as u64),
            };
            &&& range.start < range.end
            &&& match result {
                Ok(wires) => {
                    &&& bit_selection_matches(width, start, count, stride, Ok(last))
                    &&& wires@.len() == count <= driver_bits_capacity()
                    &&& forall|i: int| 0 <= i < wires@.len() ==>
                        #[trigger] wires@[i] == clocked_driver_bit(driver, (range.start + start + i * stride) as usize)
                },
                Err(ClockedDriverBitsError::Selection(reason)) =>
                    selection.is_some() && bit_selection_matches(width, start, count, stride, Err(reason)),
                Err(ClockedDriverBitsError::Last { expected, actual }) =>
                    selection.is_some() && bit_selection_matches(width, start, count, stride, Ok(expected))
                    && actual == last && expected != actual,
                Err(ClockedDriverBitsError::Capacity { count: needed, limit }) =>
                    bit_selection_matches(width, start, count, stride, Ok(last))
                    && needed == count && limit == driver_bits_capacity() && count > limit,
                Err(ClockedDriverBitsError::Allocation) =>
                    bit_selection_matches(width, start, count, stride, Ok(last)) && count <= driver_bits_capacity(),
                Err(ClockedDriverBitsError::Driver(_)) => false,
            }
        },
    }
}

/// 信号全体に対応する配線列を表す。配列の確保や展開は行わない。
pub closed spec fn clocked_driver_port_model(
    inputs: &PortBitLayout, definitions: &PortBitLayout, driver: OutputDriver,
) -> Option<Seq<ClockedWireDriver>> {
    match driver_range(inputs, definitions, driver) {
        Some(range) => Some(Seq::new((range.end - range.start) as nat,
            |bit: int| clocked_driver_bit(driver, (range.start + bit) as usize))),
        None => None,
    }
}

/// 選択した配線列が、信号全体の配線に同じ選択を適用した結果と一致することを示す。
pub proof fn clocked_driver_selection_matches(
    inputs: &PortBitLayout, definitions: &PortBitLayout, driver: OutputDriver,
    selection: CheckedBitSelection, selected: Vec<ClockedWireDriver>,
)
    requires clocked_driver_bits_result(inputs, definitions, driver, Some(selection), Ok(selected)),
    ensures clocked_driver_port_model(inputs, definitions, driver) matches Some(whole)
        && selected@ == selected_bits_values(whole, selection.start, selection.count as nat, selection.stride),
{
    let range = driver_range(inputs, definitions, driver)->Some_0;
    let width = (range.end - range.start) as u64;
    let whole = clocked_driver_port_model(inputs, definitions, driver)->Some_0;
    let expected = selected_bits_values(whole, selection.start, selection.count as nat, selection.stride);
    assert forall|i: int| 0 <= i < expected.len() implies
        #[trigger] selected@[i] == #[trigger] expected[i] by {
        selected_bit_in_range(width, selection.start, selection.count, selection.stride, selection.last, i);
        let offset = selection.start + i * selection.stride;
        assert(0 <= range.start + offset < range.end);
        assert(expected[i] == whole[offset]);
        assert(selected@[i] == clocked_driver_bit(driver, (range.start + offset) as usize));
        assert(whole[offset] == clocked_driver_bit(driver, (range.start + offset) as usize));
    };
    assert(selected@ =~= expected);
}

/// 入力または定義から、低位ビットを先頭とする配線列を取り出す。
///
/// `selection` が `None` の場合は信号全体を取り出す。入力は平坦な入力列を直接指す。
/// 定義は平坦な定義列を指し、直結の解決時にその駆動元をたどる。
///
/// # Errors
///
/// 信号の存在、選択数・刻み・範囲、保持していた末尾添字、配線列の容量の順に検査する。
/// 検査後に配線列のメモリを確保できなければ、確保の失敗を返す。
pub fn clocked_driver_bits(
    inputs: &PortBitLayout, definitions: &PortBitLayout, driver: OutputDriver,
    selection: Option<CheckedBitSelection>,
) -> (result: Result<Vec<ClockedWireDriver>, ClockedDriverBitsError>)
    ensures clocked_driver_bits_result(inputs, definitions, driver, selection, result),
{
    let range = match driver {
        OutputDriver::Input(port) => inputs.range(port),
        OutputDriver::Definition(slot) => definitions.range(slot),
    };
    let Some(range) = range else { return Err(ClockedDriverBitsError::Driver(driver)); };
    let width = (range.end - range.start) as u64;
    let (start, count, stride, _last) = match selection {
        Some(selection) => {
            let expected = match check_bit_selection(width, selection.start, selection.count, selection.stride) {
                Ok(last) => last,
                Err(error) => return Err(ClockedDriverBitsError::Selection(error)),
            };
            if expected != selection.last {
                return Err(ClockedDriverBitsError::Last { expected, actual: selection.last });
            }
            (selection.start, selection.count, selection.stride, selection.last)
        },
        None => (0, width, 1, width - 1),
    };
    let element_size = core::mem::size_of::<ClockedWireDriver>();
    let limit = if element_size == 0 { usize::MAX } else { isize::MAX as usize / element_size };
    assert(limit == driver_bits_capacity());
    if count > limit as u64 {
        return Err(ClockedDriverBitsError::Capacity { count, limit });
    }
    let mut wires = Vec::new();
    if wires.try_reserve_exact(count as usize).is_err() {
        return Err(ClockedDriverBitsError::Allocation);
    }
    let mut i = 0u64;
    while i < count
        invariant
            width == range.end - range.start,
            bit_selection_matches(width, start, count, stride, Ok(_last)),
            i == wires@.len() <= count,
            forall|j: int| 0 <= j < wires@.len() ==>
                #[trigger] wires@[j] == clocked_driver_bit(driver, (range.start + start + j * stride) as usize),
        decreases count - i,
    {
        proof { selected_bit_in_range(width, start, count, stride, _last, i as int); }
        let offset = start + i * stride;
        let index = range.start + offset as usize;
        let ghost before = wires@;
        wires.push(mapped_driver_bit(driver, index));
        assert forall|j: int| 0 <= j < wires@.len() implies
            #[trigger] wires@[j] == clocked_driver_bit(driver, (range.start + start + j * stride) as usize) by {
            if j < i { assert(wires@[j] == before[j]); }
        };
        i += 1;
    }
    Ok(wires)
}

} // verus!
