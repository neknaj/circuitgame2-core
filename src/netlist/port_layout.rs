//! 宣言順のポートを、ネットリストが扱う1ビット単位の配列へ配置する。

use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

verus! {

/// ポートのビット幅を配列上の範囲にできなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PortBitLayoutError {
    /// ビット幅が0のポート。
    ZeroWidth {
        /// 宣言順のポート添字。
        port: usize,
    },
    /// ポートを加えると指定した総ビット数の上限を越える。
    CapacityExceeded {
        /// 最初に上限を越えるポートの添字。
        port: usize,
        /// このポートの幅。
        width: u64,
        /// 先行ポートの総ビット数。
        used: usize,
        /// 呼び出し側が指定した上限。
        capacity: usize,
    },
}

/// ポートの各ビットを平坦な配列上の位置に対応付ける。
///
/// ポートを宣言順に並べ、各ポートのビットを低位から順に配置する。
#[derive(Debug, Eq, PartialEq)]
pub struct PortBitLayout {
    ranges: Vec<Range<usize>>,
    total_bits: usize,
}

/// 宣言順に先頭から `ports` 個の幅を数学上の自然数として合計する。
#[verifier::opaque]
pub open spec fn preceding_port_bits(widths: Seq<u64>, ports: nat) -> nat
    recommends ports <= widths.len(),
    decreases ports,
{
    if ports == 0 || ports > widths.len() {
        0
    } else {
        preceding_port_bits(widths, (ports - 1) as nat) + widths[ports - 1] as nat
    }
}

/// 先頭から指定した個数のポートが正の幅を持ち、総ビット数が上限に収まることを表す。
pub open spec fn port_widths_fit(widths: Seq<u64>, ports: nat, capacity: usize) -> bool {
    &&& ports <= widths.len()
    &&& preceding_port_bits(widths, ports) <= capacity
    &&& forall|i: int| 0 <= i < ports ==> (#[trigger] widths[i]) > 0
}

spec fn ranges_match(widths: Seq<u64>, ranges: Seq<Range<usize>>) -> bool {
    &&& ranges.len() <= widths.len()
    &&& forall|i: int| 0 <= i < ranges.len() ==> {
        let range = #[trigger] ranges[i];
        &&& range.start == preceding_port_bits(widths, i as nat)
        &&& range.end == preceding_port_bits(widths, (i + 1) as nat)
    }
}

/// 宣言幅どおりの配置、または宣言順で最初に見つかった違反を表す。
pub closed spec fn port_bit_layout_result(
    widths: Seq<u64>, capacity: usize, result: Result<PortBitLayout, PortBitLayoutError>,
) -> bool {
    match result {
        Ok(layout) => port_widths_fit(widths, widths.len(), capacity)
            && ranges_match(widths, layout.ranges@)
            && layout.ranges@.len() == widths.len()
            && layout.total_bits == preceding_port_bits(widths, widths.len()),
        Err(PortBitLayoutError::ZeroWidth { port }) => port < widths.len()
            && port_widths_fit(widths, port as nat, capacity)
            && widths[port as int] == 0,
        Err(PortBitLayoutError::CapacityExceeded { port, width, used, capacity: limit }) =>
            port < widths.len()
            && port_widths_fit(widths, port as nat, capacity)
            && limit == capacity && used == preceding_port_bits(widths, port as nat)
            && width == widths[port as int] && width > 0
            && preceding_port_bits(widths, (port + 1) as nat) > capacity,
    }
}

/// 幅の列を長くしても、そこまでの総ビット数は減らない。
pub(crate) proof fn preceding_port_bits_grow(widths: Seq<u64>, first: nat, last: nat)
    requires first <= last <= widths.len(),
    ensures preceding_port_bits(widths, first) <= preceding_port_bits(widths, last),
    decreases last - first,
{
    reveal(preceding_port_bits);
    if first < last {
        preceding_port_bits_grow(widths, first, (last - 1) as nat);
        assert(preceding_port_bits(widths, last)
            == preceding_port_bits(widths, (last - 1) as nat) + widths[last - 1] as nat);
    }
}

impl PortBitLayout {
    #[verifier::type_invariant]
    spec fn valid_port_ranges(&self) -> bool {
        &&& (self.ranges@.len() == 0 <==> self.total_bits == 0)
        &&& self.ranges@.len() > 0 ==> self.ranges@[0].start == 0
            && self.ranges@[self.ranges@.len() - 1].end == self.total_bits
        &&& forall|i: int| 0 <= i < self.ranges@.len() ==> {
            let range = #[trigger] self.ranges@[i];
            &&& range.start < range.end <= self.total_bits
            &&& i > 0 ==> self.ranges@[i - 1].end == range.start
        }
    }

    /// 宣言順の幅から、各ポートの半開範囲を求める。
    ///
    /// `capacity` は平坦な配列の総ビット数の上限。幅の列が空なら総ビット数は0になる。
    ///
    /// # Errors
    ///
    /// 宣言順に調べ、幅が0のポートまたは総ビット数が上限を超える最初のポートを返す。
    pub fn from_widths(widths: &[u64], capacity: usize) -> (result: Result<Self, PortBitLayoutError>)
        ensures
            port_bit_layout_result(widths@, capacity, result),
            result.is_ok() <==> port_widths_fit(widths@, widths@.len(), capacity),
            match result {
                Ok(layout) => layout.ranges_model().len() == widths@.len()
                    && layout.total_bits_model() == preceding_port_bits(widths@, widths@.len()),
                Err(PortBitLayoutError::ZeroWidth { port } | PortBitLayoutError::CapacityExceeded { port, .. }) =>
                    port < widths@.len(),
            },
    {
        assert(preceding_port_bits(widths@, 0) == 0) by { reveal(preceding_port_bits); };
        let mut ranges = Vec::new();
        let mut total = 0usize;
        let mut port = 0usize;
        while port < widths.len()
            invariant
                port == ranges@.len(),
                ranges_match(widths@, ranges@),
                port_widths_fit(widths@, port as nat, capacity),
                total == preceding_port_bits(widths@, port as nat),
                forall|i: int| 0 <= i < ranges@.len() ==> {
                    let range = #[trigger] ranges@[i];
                    range.start < range.end <= total
                },
            decreases widths@.len() - port,
        {
            let width = widths[port];
            if width == 0 {
                return Err(PortBitLayoutError::ZeroWidth { port });
            }
            assert(preceding_port_bits(widths@, (port + 1) as nat) == total + width) by {
                reveal(preceding_port_bits);
            };
            let remaining = capacity - total;
            if width as u128 > remaining as u128 {
                proof { preceding_port_bits_grow(widths@, (port + 1) as nat, widths@.len()); }
                return Err(PortBitLayoutError::CapacityExceeded { port, width, used: total, capacity });
            }
            let next = total + width as usize;
            let ghost before = ranges@;
            ranges.push(total..next);
            assert forall|i: int| 0 <= i < ranges@.len() implies {
                let range = #[trigger] ranges@[i];
                &&& range.start == preceding_port_bits(widths@, i as nat)
                &&& range.end == preceding_port_bits(widths@, (i + 1) as nat)
                &&& range.start < range.end <= next
            } by {
                if i < port { assert(ranges@[i] == before[i]); }
            };
            total = next;
            port += 1;
        }
        if port > 0 {
            assert(ranges@[0].start == 0);
            assert(ranges@[port - 1].end == total);
            assert(total > 0);
        }
        assert forall|i: int| 0 < i < ranges@.len() implies
            (#[trigger] ranges@[i]).start == ranges@[i - 1].end by {
            assert(ranges@[i].start == preceding_port_bits(widths@, i as nat));
            assert(ranges@[i - 1].end == preceding_port_bits(widths@, i as nat));
        };
        Ok(Self { ranges, total_bits: total })
    }

    /// 宣言順に並んだ、各ポートの半開ビット範囲を返す。
    pub fn ranges(&self) -> (ranges: &[Range<usize>])
        ensures ranges@ == self.ranges_model(),
    {
        self.ranges.as_slice()
    }

    /// 指定したポートの半開ビット範囲を返す。ポートが存在しなければ `None` を返す。
    pub fn range(&self, port: usize) -> (range: Option<Range<usize>>)
        ensures
            range == if port < self.ranges_model().len() { Some(self.ranges_model()[port as int]) } else { None },
            range matches Some(bits) ==> bits.start < bits.end <= self.total_bits_model(),
    {
        proof { use_type_invariant(self); }
        if port >= self.ranges.len() {
            return None;
        }
        let bits = &self.ranges[port];
        Some(bits.start..bits.end)
    }

    /// 全ポートを合わせたビット数を返す。
    pub fn total_bits(&self) -> (total: usize)
        ensures total == self.total_bits_model(),
    {
        self.total_bits
    }

    /// ポート内のビットを、平坦な配列上の添字に変換する。
    ///
    /// `bit` は0が最下位。ポートまたはビットの添字が範囲外なら `None` を返す。
    pub fn bit_index(&self, port: usize, bit: usize) -> (index: Option<usize>)
        ensures
            index == self.bit_index_model(port, bit),
            index matches Some(at) ==> at < self.total_bits_model(),
    {
        if port >= self.ranges.len() {
            return None;
        }
        proof { use_type_invariant(self); }
        let range = &self.ranges[port];
        if bit >= range.end - range.start {
            None
        } else {
            Some(range.start + bit)
        }
    }

    /// 平坦なビット添字を、そのビットを含むポートの添字に戻す。
    ///
    /// 添字が総ビット数以上なら `None` を返す。
    pub fn port_at_bit(&self, bit: usize) -> (port: Option<usize>)
        ensures
            port.is_none() <==> bit >= self.total_bits_model(),
            port matches Some(i) ==> i < self.ranges_model().len()
                && self.ranges_model()[i as int].start <= bit < self.ranges_model()[i as int].end,
    {
        if bit >= self.total_bits { return None; }
        proof { use_type_invariant(self); }
        let mut first = 0usize;
        let mut end = self.ranges.len();
        while first < end
            invariant
                0 <= first < end <= self.ranges@.len(),
                self.valid_port_ranges(),
                self.ranges@[first as int].start <= bit < self.ranges@[end - 1].end,
            decreases end - first,
        {
            let middle = first + (end - first) / 2;
            let range = &self.ranges[middle];
            if bit < range.start {
                assert(first < middle);
                assert(self.ranges@[middle - 1].end == range.start);
                end = middle;
            } else if bit >= range.end {
                assert(middle + 1 < end);
                assert(self.ranges@[(middle + 1) as int].start == range.end);
                first = middle + 1;
            } else {
                return Some(middle);
            }
        }
        unreachable!()
    }

    /// 宣言順に並ぶ半開ビット範囲を表す。
    pub closed spec fn ranges_model(&self) -> Seq<Range<usize>> { self.ranges@ }

    /// 配列に含まれる総ビット数を表す。
    pub closed spec fn total_bits_model(&self) -> usize { self.total_bits }

    /// 有効なポート内のビットに、その配列添字を対応付ける。
    pub closed spec fn bit_index_model(&self, port: usize, bit: usize) -> Option<usize> {
        if port < self.ranges@.len() {
            let range = self.ranges@[port as int];
            if bit < range.end - range.start { Some((range.start + bit) as usize) } else { None }
        } else {
            None
        }
    }
}

/// 空のポート列も含め、成功した配置からポート数と総ビット数を取り出す。
pub proof fn port_bit_layout_size(widths: Seq<u64>, capacity: usize, layout: &PortBitLayout)
    requires port_bit_layout_result(widths, capacity, Ok(*layout)),
    ensures
        layout.ranges_model().len() == widths.len() <= usize::MAX,
        layout.total_bits_model() == preceding_port_bits(widths, widths.len()),
        layout.total_bits_model() <= capacity,
{
    vstd::std_specs::vec::axiom_spec_len(&layout.ranges);
}

/// 成功時の各ポートの配置と、その最下位ビットを起点にした添字を取り出す。
pub proof fn port_bit_layout_port(
    widths: Seq<u64>, capacity: usize, layout: PortBitLayout, port: usize,
)
    requires port_bit_layout_result(widths, capacity, Ok(layout)), port < widths.len(),
    ensures
        layout.ranges_model().len() == widths.len(),
        layout.total_bits_model() == preceding_port_bits(widths, widths.len()),
        layout.ranges_model()[port as int].start == preceding_port_bits(widths, port as nat),
        layout.ranges_model()[port as int].end == preceding_port_bits(widths, (port + 1) as nat),
        layout.ranges_model()[port as int].start < layout.ranges_model()[port as int].end <= layout.total_bits_model(),
        layout.ranges_model()[port as int].end - layout.ranges_model()[port as int].start == widths[port as int],
        forall|bit: usize| #[trigger] layout.bit_index_model(port, bit)
            == if bit < widths[port as int] {
                Some((preceding_port_bits(widths, port as nat) + bit) as usize)
            } else {
                None
            },
{
    reveal(preceding_port_bits);
    assert(preceding_port_bits(widths, (port + 1) as nat)
        == preceding_port_bits(widths, port as nat) + widths[port as int] as nat);
    preceding_port_bits_grow(widths, (port + 1) as nat, widths.len());
}

} // verus!
