//! 型検査の訪問記録を、構文上の式の位置と照合する。

use super::*;
use super::super::{is_expression_slot, mark_expression_slots};
#[cfg(verus_only)]
use super::super::{expression_slot, slot_marked};

verus! {

#[verifier::opaque]
pub(super) open spec fn call_trace_covers_slots(
    source: &str, forms: Seq<Form>, calls: Seq<CallTypeEntry>, trace: Seq<usize>, body: usize,
    arithmetic: bool,
) -> bool {
    forall|i: usize| i < calls.len() && (calls[i as int].target is Arithmetic) == arithmetic
        && #[trigger] expression_slot(source, forms, body, calls[i as int].at)
        ==> trace.contains(i)
}

fn visited_entries(trace: &[usize], count: usize) -> (seen: Vec<bool>)
    requires forall|i: int| 0 <= i < trace@.len() ==> (#[trigger] trace@[i]) < count,
    ensures seen@.len() == count,
        forall|i: usize| i < count ==> (#[trigger] seen@[i as int]) == trace@.contains(i),
{
    let mut seen = Vec::<bool>::new();
    while seen.len() < count
        invariant seen@.len() <= count, forall|i: int| 0 <= i < seen@.len() ==> !(#[trigger] seen@[i]),
        decreases count - seen@.len(),
    {
        seen.push(false);
    }
    let mut cursor = 0;
    while cursor < trace.len()
        invariant
            seen@.len() == count,
            cursor <= trace@.len(),
            forall|i: int| 0 <= i < trace@.len() ==> (#[trigger] trace@[i]) < count,
            forall|i: usize| i < count ==> (#[trigger] seen@[i as int]) == trace@.take(cursor as int).contains(i),
        decreases trace@.len() - cursor,
    {
        let index = trace[cursor];
        let ghost before = seen@;
        seen.set(index, true);
        proof {
            let prefix = trace@.take(cursor as int);
            assert(trace@.take(cursor as int + 1) =~= prefix.push(index));
            assert forall|i: usize| i < count implies
                (#[trigger] seen@[i as int]) == prefix.push(index).contains(i) by {
                if i != index { assert(seen@[i as int] == before[i as int]); }
                assert(prefix.push(index).contains(i) <==> (prefix.contains(i) || i == index)) by {
                    let grown = prefix.push(index);
                    if grown.contains(i) {
                        let j = choose|j: int| 0 <= j < grown.len() && (#[trigger] grown[j]) == i;
                        if j == prefix.len() { assert(i == index); }
                        else { assert(prefix[j] == i); }
                    }
                    if prefix.contains(i) {
                        let j = choose|j: int| 0 <= j < prefix.len() && (#[trigger] prefix[j]) == i;
                        assert(grown[j] == i);
                    }
                    if i == index { assert(grown[prefix.len() as int] == i); }
                };
            };
        }
        cursor += 1;
    }
    assert(trace@.take(cursor as int) =~= trace@);
    seen
}

pub(super) fn first_unvisited_expression_entry(
    source: &str, forms: &[Form], calls: &[CallTypeEntry], trace: &[usize], body: usize,
    arithmetic: bool,
) -> (missing: Option<usize>)
    requires
        usable_forms(source, forms@), body < forms@.len(),
        if arithmetic { arithmetic_trace_fits(calls@, trace@, body, forms@.len()) }
            else { call_trace_fits(calls@, trace@, body, forms@.len()) },
    ensures
        missing.is_none() <==> call_trace_covers_slots(source, forms@, calls@, trace@, body, arithmetic),
        missing matches Some(i) ==> i < calls@.len()
            && (calls@[i as int].target is Arithmetic) == arithmetic
            && expression_slot(source, forms@, body, calls@[i as int].at) && !trace@.contains(i),
{
    let count = calls.len();
    proof {
        reveal(arithmetic_trace_fits);
        assert forall|i: int| 0 <= i < trace@.len() implies (#[trigger] trace@[i]) < count by {
            if !arithmetic { trace_entry_in_range(calls@, trace@, body, forms@.len(), i); }
        };
    }
    if count == 0 {
        assert(call_trace_covers_slots(source, forms@, calls@, trace@, body, arithmetic)) by { reveal(call_trace_covers_slots); };
        return None;
    }
    let seen = visited_entries(trace, count);
    let mask = mark_expression_slots(source, forms, body);
    let mut i = 0;
    while i < count
        invariant
            count == calls@.len(),
            i <= count, seen@.len() == count,
            usable_forms(source, forms@), body < forms@.len(),
            forall|at: usize| #[trigger] expression_slot(source, forms@, body, at) ==> slot_marked(mask@, body, at),
            forall|j: usize| j < count ==> (#[trigger] seen@[j as int]) == trace@.contains(j),
            forall|j: usize| j < i && (calls@[j as int].target is Arithmetic) == arithmetic
                && #[trigger] expression_slot(source, forms@, body, calls@[j as int].at)
                ==> trace@.contains(j),
        decreases count - i,
    {
        let at = calls[i].at;
        if matches!(calls[i].target, CallTypeTarget::Arithmetic(_)) == arithmetic
            && !seen[i] && at >= body && at - body < mask.len() && mask[at - body] {
            // 食い違いの候補だけを元の式位置の照会で確かめ、呼び出しを示す。
            if is_expression_slot(source, forms, body, at) {
                assert(!call_trace_covers_slots(source, forms@, calls@, trace@, body, arithmetic)) by {
                    reveal(call_trace_covers_slots);
                    assert(calls@[i as int].at == at && i < calls@.len());
                    assert(!trace@.contains(i));
                    assert(expression_slot(source, forms@, body, calls@[i as int].at));
                };
                return Some(i);
            }
        }
        i += 1;
    }
    assert(call_trace_covers_slots(source, forms@, calls@, trace@, body, arithmetic)) by { reveal(call_trace_covers_slots); };
    None
}

}
