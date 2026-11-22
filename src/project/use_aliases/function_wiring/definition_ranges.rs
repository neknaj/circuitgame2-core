//! 厳格定義の順序から、関数の各左辺が占めるスロット区間を得る。

use super::*;
use core::ops::Range;
use crate::syntax::circuit::definition_target_range_nonempty;

verus! {

/// 厳格索引の定義番号から、左辺の駆動元が並ぶ区間を求める。
pub(in crate::project::use_aliases) closed spec fn strict_definition_slots(
    parsed: &NamedBuildCircuit, entry: usize, wiring: &FuncWiring,
) -> Seq<Range<usize>> {
    let frame = parsed.entry_ranges@[entry as int].definitions;
    let drivers = wiring.drivers.definitions@;
    Seq::new((frame.end - frame.start) as nat, |i: int| {
        let definition = frame.start + i;
        let first = choose|at: int| 0 <= at < drivers.len()
            && (#[trigger] drivers[at]).definition == definition && drivers[at].result_index == 0;
        let (start, end) = definition_target_range(parsed.syntax.forms@, parsed.definitions@[definition]);
        (first as usize)..((first + end - start) as usize)
    })
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 厳格定義の全左辺が連続するスロットを占め、その区間が同じ定義の全駆動元を覆うことを示す。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases) proof fn strict_definition_slot_at(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, i: int,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))),
            ({
                let parsed = &self.targets.project_model().circuits_model()[file as int];
                let frame = parsed.entry_ranges@[entry as int].definitions;
                &&& file < self.targets.project_model().circuits_model().len()
                &&& entry < parsed.entry_ranges@.len()
                &&& 0 <= i < frame.end - frame.start
            }),
        ensures ({
            let parsed = &self.targets.project_model().circuits_model()[file as int];
            let frame = parsed.entry_ranges@[entry as int].definitions;
            let definition = frame.start + i;
            let ranges = strict_definition_slots(parsed, entry, wiring);
            let range = ranges[i];
            let drivers = wiring.drivers.definitions@;
            let (start, end) = definition_target_range(parsed.syntax.forms@, parsed.definitions@[definition]);
            &&& ranges.len() == frame.end - frame.start
            &&& range.start < range.end <= drivers.len() && range.end - range.start == end - start
            &&& forall|at: int| 0 <= at < drivers.len() && (#[trigger] drivers[at]).definition == definition ==>
                range.start <= at < range.end && drivers[at].result_index == at - range.start
            &&& forall|at: int| range.start <= at < range.end ==>
                (#[trigger] drivers[at]).definition == definition && drivers[at].result_index == at - range.start
        }),
    {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int].definitions;
        let definition = (frame.start + i) as usize;
        let drivers = wiring.drivers.definitions@;
        self.checked_wiring_is_func(file, entry, limit, *wiring);
        self.targets.parsed_project_model();
        parsed_index_evidence(*source, *parsed);
        build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, definition as int);
        definition_target_range_nonempty(parsed.syntax.forms@, parsed.definitions@[definition as int]);
        let first = self.checked_wiring_first_definition_driver(file, entry, limit, *wiring, definition);
        let count = self.checked_wiring_output_group(file, entry, limit, *wiring, first);
        vstd::std_specs::vec::axiom_spec_len(&wiring.drivers.definitions);
        let chosen = choose|at: int| 0 <= at < drivers.len()
            && (#[trigger] drivers[at]).definition == definition && drivers[at].result_index == 0;
        assert(chosen == first) by {
            if chosen < first {
                assert(drivers[chosen].result_index < drivers[first].result_index);
            } else if first < chosen {
                assert(drivers[first].result_index < drivers[chosen].result_index);
            }
        };
        let ranges = strict_definition_slots(parsed, entry, wiring);
        assert(ranges[i] == ((first as usize)..((first + count) as usize)));
        assert forall|at: int| 0 <= at < drivers.len() && (#[trigger] drivers[at]).definition == definition implies
            first <= at < first + count && drivers[at].result_index == at - first by {
            let driver = drivers[at];
            assert(indexed_driver_site(source, parsed, entry as int, driver));
            assert(driver.result_index < count);
            let found = first + driver.result_index;
            assert(drivers[found].definition == definition && drivers[found].result_index == driver.result_index);
            if at < found {
                assert(drivers[at].result_index < drivers[found].result_index);
            } else if found < at {
                assert(drivers[found].result_index < drivers[at].result_index);
            }
        };
        let range = ranges[i];
        assert forall|at: int| range.start <= at < range.end implies
            (#[trigger] drivers[at]).definition == definition && drivers[at].result_index == at - range.start by {
            let j = at - first;
            assert(0 <= j < count && first + j == at);
            assert(drivers[first + j].definition == definition && drivers[first + j].result_index == j);
        };
    }

    /// 定義順に並ぶ左辺スロットの区間が、先頭から末尾まで駆動元を分割することを示す。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases) proof fn strict_definition_slot_partition(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))),
        ensures ({
            let parsed = &self.targets.project_model().circuits_model()[file as int];
            let frame = parsed.entry_ranges@[entry as int].definitions;
            let ranges = strict_definition_slots(parsed, entry, wiring);
            let drivers = wiring.drivers.definitions@;
            &&& ranges.len() == frame.end - frame.start
            &&& if ranges.len() == 0 { drivers.len() == 0 }
                else { ranges[0].start == 0 && ranges.last().end == drivers.len() }
            &&& forall|i: int| 0 <= i < ranges.len() ==> ranges[i].start < #[trigger] ranges[i].end <= drivers.len()
            &&& forall|i: int| 0 < i < ranges.len() ==> #[trigger] ranges[i].start == ranges[i - 1].end
        }),
    {
        self.checked_wiring_is_func(file, entry, limit, *wiring);
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int].definitions;
        let ranges = strict_definition_slots(parsed, entry, wiring);
        let drivers = wiring.drivers.definitions@;
        assert(frame.start <= frame.end <= parsed.definitions@.len()) by {
            self.targets.parsed_project_model();
            parsed_index_evidence(project.sources_model()[file as int], *parsed);
            build_entry_ranges_evidence(project.sources_model()[file as int].text, &parsed.build_model(), entry as int);
        };
        if ranges.len() == 0 {
            if drivers.len() > 0 {
                assert(frame.start <= drivers[0].definition < frame.end);
            }
        } else {
            self.strict_definition_slot_at(file, entry, limit, wiring, 0);
            let first = ranges[0].start;
            if first > 0 {
                assert(frame.start <= drivers[0].definition <= drivers[first as int].definition == frame.start);
                assert(drivers[0].definition == frame.start);
            }
            let i = ranges.len() as int - 1;
            self.strict_definition_slot_at(file, entry, limit, wiring, i);
            let last = ranges[i];
            assert(ranges.last() == last);
            if last.end < drivers.len() {
                let later = last.end as int;
                assert(drivers[last.start as int].definition <= drivers[later].definition < frame.end);
                assert(drivers[later].definition == frame.end - 1);
            }
        }
        assert forall|i: int| 0 <= i < ranges.len() implies ranges[i].start < #[trigger] ranges[i].end <= drivers.len() by {
            self.strict_definition_slot_at(file, entry, limit, wiring, i);
        };
        assert forall|i: int| 0 < i < ranges.len() implies #[trigger] ranges[i].start == ranges[i - 1].end by {
            self.strict_definition_slot_at(file, entry, limit, wiring, i - 1);
            self.strict_definition_slot_at(file, entry, limit, wiring, i);
            let left = ranges[i - 1];
            let right = ranges[i];
            let lhs = frame.start + i - 1;
            let rhs = frame.start + i;
            assert(drivers[left.start as int].definition == lhs && drivers[right.start as int].definition == rhs);
            assert(left.start < right.start) by {
                if right.start < left.start { assert(drivers[right.start as int].definition <= drivers[left.start as int].definition); }
            };
            if right.start < left.end { assert(drivers[right.start as int].definition == lhs); }
            if left.end < right.start {
                let between = left.end as int;
                assert(lhs <= drivers[between].definition <= rhs);
                if drivers[between].definition == lhs {
                    assert(left.start <= between < left.end);
                } else {
                    assert(drivers[between].definition == rhs);
                    assert(right.start <= between < right.end);
                }
            }
        };
    }
}

} // verus!
