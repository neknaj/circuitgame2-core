//! 配線履歴の左辺区間を、定義順の区間列と照合する。

use super::*;

verus! {

/// 空でない区間が重ならず、スロット 0 から終端まで隙間なく並ぶことを表す。
pub(in crate::project::use_aliases::bit_func) open spec fn source_slot_partition(
    ranges: Seq<Range<usize>>, end: usize,
) -> bool {
    &&& if ranges.len() == 0 { end == 0 } else { ranges[0].start == 0 }
    &&& forall|i: int| 0 <= i < ranges.len() ==> {
        let next = #[trigger] ranges[i].end;
        &&& ranges[i].start < next <= end
        &&& next == if i + 1 < ranges.len() { ranges[i + 1].start } else { end }
    }
}

/// 履歴の各段が書き込んだ左辺スロットを並べる。
pub(in crate::project::use_aliases::bit_func) open spec fn rooted_source_step_ranges(
    steps: Seq<WiringStep>,
) -> Seq<Range<usize>> {
    Seq::new(steps.len(), |i: int| source_step_slots(steps[i]))
}

proof fn partition_starts_increase(ranges: Seq<Range<usize>>, end: usize, first: int, later: int)
    requires
        source_slot_partition(ranges, end),
        0 <= first < later < ranges.len(),
    ensures ranges[first].start < ranges[later].start,
    decreases later - first,
{
    assert(ranges[later - 1].end == ranges[later].start);
    if first < later - 1 {
        partition_starts_increase(ranges, end, first, later - 1);
    }
}

proof fn partition_prefix_matches(
    actual: Seq<Range<usize>>, expected: Seq<Range<usize>>, end: usize, count: int,
)
    requires
        source_slot_partition(actual, end), source_slot_partition(expected, end),
        0 <= count <= actual.len(), count <= expected.len(),
        forall|i: int| 0 <= i < actual.len() ==> #[trigger] expected.contains(actual[i]),
    ensures actual.take(count) == expected.take(count),
    decreases count,
{
    if count > 0 {
        let i = count - 1;
        partition_prefix_matches(actual, expected, end, i);
        if i > 0 {
            assert(actual.take(i)[i - 1] == actual[i - 1]);
            assert(expected.take(i)[i - 1] == expected[i - 1]);
            assert(actual[i - 1].end == actual[i].start);
            assert(expected[i - 1].end == expected[i].start);
        }
        assert(actual[i].start == expected[i].start);
        let target = actual[i];
        assert(expected.contains(target));
        let j = choose|j: int| 0 <= j < expected.len() && expected[j] == target;
        if i < j {
            partition_starts_increase(expected, end, i, j);
        } else if j < i {
            partition_starts_increase(expected, end, j, i);
        }
        assert(i == j && actual[i] == expected[i]);
    }
    assert(actual.take(count) =~= expected.take(count));
}

proof fn partition_prefix_reaches_end(
    shorter: Seq<Range<usize>>, longer: Seq<Range<usize>>, end: usize,
)
    requires
        source_slot_partition(shorter, end), source_slot_partition(longer, end),
        shorter.len() <= longer.len(),
        shorter == longer.take(shorter.len() as int),
    ensures shorter.len() == longer.len(),
{
    if shorter.len() < longer.len() {
        let next = shorter.len() as int;
        assert(longer[next].start == end) by {
            if next > 0 {
                assert(shorter[next - 1] == longer[next - 1]);
                assert(shorter[next - 1].end == end);
                assert(longer[next - 1].end == longer[next].start);
            }
        };
        assert(longer[next].start < longer[next].end <= end);
    }
}

/// 配線履歴は左辺を先頭から順に埋め、現在のスロットまでを覆う。
proof fn rooted_source_step_ranges_partition(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    roots: Seq<NorBinding>, limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, wiring: WiringView,
)
    requires rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, wiring),
    ensures source_slot_partition(rooted_source_step_ranges(steps), slot),
{
    let ranges = rooted_source_step_ranges(steps);
    assert(if ranges.len() == 0 { slot == 0 } else { ranges[0].start == 0 }) by {
        reveal(rooted_mixed_trace);
        reveal(source_step_slots);
        if steps.len() > 0 {
            assert(steps[0].from == 0);
        }
    };
    assert forall|i: int| 0 <= i < ranges.len() implies {
        let next = #[trigger] ranges[i].end;
        &&& ranges[i].start < next
        &&& next == if i + 1 < ranges.len() { ranges[i + 1].start } else { slot }
    } by {
        rooted_source_step_adjacent(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, wiring, i);
    };
    assert forall|i: int| 0 <= i < ranges.len() implies #[trigger] ranges[i].end <= slot by {
        let last = (ranges.len() - 1) as int;
        if i < last {
            partition_ends_no_later(ranges, slot, i, last);
        }
    };
}

proof fn rooted_source_step_adjacent(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    roots: Seq<NorBinding>, limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, wiring: WiringView,
    i: int,
)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, wiring),
        0 <= i < steps.len(),
    ensures ({
        let here = source_step_slots(steps[i]);
        &&& here.start < here.end
        &&& here.end == if i + 1 < steps.len() { source_step_slots(steps[i + 1]).start } else { slot }
    }),
{
    reveal(source_step_slots);
    let step = steps[i];
    let ordinary = step.nor_before == step.nor_after;
    assert(if ordinary {
        wiring_step_valid(body, layouts, forms, bindings, limit, step)
    } else {
        nor_wiring_step_valid(body, layouts, forms, roots, limit, step)
    }) by {
        reveal(rooted_mixed_trace);
    };
    assert(step.from < step.to) by {
        if ordinary {
            reveal(wiring_step_valid);
        } else {
            reveal(nor_wiring_step_valid);
        }
    };
    if i + 1 < steps.len() {
        assert(steps[i + 1].from == step.to) by { reveal(rooted_mixed_trace); };
    } else {
        assert(step.to == slot) by {
            reveal(rooted_mixed_trace);
            assert(steps.last() == step);
        };
    }
}

proof fn partition_ends_no_later(ranges: Seq<Range<usize>>, end: usize, first: int, later: int)
    requires
        0 <= first < later < ranges.len(),
        forall|i: int| 0 <= i < ranges.len() ==> {
            let next = #[trigger] ranges[i].end;
            &&& ranges[i].start < next
            &&& next == if i + 1 < ranges.len() { ranges[i + 1].start } else { end }
        },
    ensures ranges[first].end < ranges[later].end,
    decreases later - first,
{
    assert(ranges[later - 1].end == ranges[later].start);
    if first < later - 1 {
        partition_ends_no_later(ranges, end, first, later - 1);
    }
}

/// 履歴の区間がすべて正準列に属するなら、左辺を覆う両方の列が長さと順序まで一致する。
pub(in crate::project::use_aliases::bit_func::lowering) proof fn rooted_source_step_ranges_match(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>,
    roots: Seq<NorBinding>, limit: usize, steps: Seq<WiringStep>, slot: usize, group: usize, nor: usize, wiring: WiringView,
    expected: Seq<Range<usize>>,
)
    requires
        rooted_mixed_trace(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, wiring),
        source_slot_partition(expected, slot),
        forall|i: int| 0 <= i < steps.len() ==> #[trigger] expected.contains(source_step_slots(steps[i])),
    ensures rooted_source_step_ranges(steps) == expected,
{
    rooted_source_step_ranges_partition(body, layouts, forms, bindings, roots, limit, steps, slot, group, nor, wiring);
    let actual = rooted_source_step_ranges(steps);
    assert forall|i: int| 0 <= i < actual.len() implies #[trigger] expected.contains(actual[i]) by {
        assert(actual[i] == source_step_slots(steps[i]));
    };
    if actual.len() <= expected.len() {
        let count = actual.len() as int;
        partition_prefix_matches(actual, expected, slot, count);
        assert(actual.take(count) =~= actual);
        partition_prefix_reaches_end(actual, expected, slot);
        assert(expected.take(count) =~= expected);
    } else {
        let count = expected.len() as int;
        partition_prefix_matches(actual, expected, slot, count);
        assert(expected.take(count) =~= expected);
        partition_prefix_reaches_end(expected, actual, slot);
    }
}

} // verus!
