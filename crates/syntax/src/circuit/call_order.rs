//! 厳格参照から、呼び出しを子から親の順に並べる。

use super::*;
#[cfg(verus_only)]
use super::call_shapes::definition_call_index;
#[cfg(verus_only)]
use super::expression_forest::{
    expression_callee_location, expression_references, expression_references_in_order, expression_root_callee,
};
#[cfg(verus_only)]
use super::expressions::after_form;

verus! {

#[derive(Clone, Copy)]
struct PendingCall {
    reference: usize,
    end: usize,
}

spec fn call_start(references: Seq<ExpressionReference>, reference: usize) -> int {
    references[reference as int].form - 1
}

spec fn call_end(forms: Seq<Form>, references: Seq<ExpressionReference>, reference: usize) -> int {
    forms[call_start(references, reference)]->List_end as int
}

spec fn precedes(forms: Seq<Form>, refs: Seq<ExpressionReference>, a: usize, b: usize) -> bool {
    let x = call_end(forms, refs, a);
    let y = call_end(forms, refs, b);
    x < y || (x == y && call_start(refs, b) < call_start(refs, a))
}

#[verifier::opaque]
spec fn contains_call(pending: Seq<PendingCall>, reference: usize) -> bool {
    exists|i: int| 0 <= i < pending.len() && (#[trigger] pending[i]).reference == reference
}

#[verifier::opaque]
spec fn seen_call(pending: Seq<PendingCall>, order: Seq<usize>, reference: usize) -> bool {
    order.contains(reference) || contains_call(pending, reference)
}

spec fn is_callee(refs: Seq<ExpressionReference>, start: usize, end: usize, r: usize) -> bool {
    start <= r < end && refs[r as int].kind is Callee
}

/// 呼び出し参照がちょうど一度ずつ現れ、子から親の順に並ぶことを表す。
///
/// 構文木で閉じる位置が早いものから並べる。同じ位置なら、内側の呼び出しを先に置く。
pub closed spec fn call_references_in_postorder(
    forms: Seq<Form>, refs: Seq<ExpressionReference>, range: Range<usize>, order: Seq<usize>,
) -> bool {
    &&& forall|r: usize| #[trigger] order.contains(r) <==> is_callee(refs, range.start, range.end, r)
    &&& forall|i: int, j: int| 0 <= i < j < order.len() ==>
        precedes(forms, refs, #[trigger] order[i], #[trigger] order[j])
}

#[verifier::opaque]
spec fn reference_bounds(
    forms: Seq<Form>, refs: Seq<ExpressionReference>, start: usize, end: usize,
) -> bool {
    &&& start <= end <= refs.len()
    &&& forall|r: usize| start <= r < end && (#[trigger] refs[r as int]).kind is Callee ==> {
        let first = call_start(refs, r);
        &&& 0 <= first < forms.len()
        &&& forms[first] is List
        &&& first + 2 <= call_end(forms, refs, r) <= forms.len()
    }
    &&& forall|a: int, b: int| start <= a < b < end ==>
        (#[trigger] refs[a]).form < (#[trigger] refs[b]).form
}

proof fn row_reference_bounds(source: &str, forms: Seq<Form>, refs: Seq<ExpressionReference>, row: BuildDefinition)
    requires definition_call_index(source, forms, row, refs), forms.len() <= usize::MAX,
    ensures reference_bounds(forms, refs, row.references.start, row.references.end),
{
    reveal(reference_bounds);
    let start = row.references.start;
    let end = row.references.end;
    let a = row.expression.start as int;
    let b = row.expression.end as int;
    let selected = expression_references(source, forms, a, b);
    expression_references_in_order(source, forms, a, b);
    assert forall|r: usize| start <= r < end && (#[trigger] refs[r as int]).kind is Callee implies {
        let first = call_start(refs, r);
        &&& 0 <= first < forms.len()
        &&& forms[first] is List
        &&& first + 2 <= call_end(forms, refs, r) <= forms.len()
    } by {
        assert(refs[r as int] == selected[r - start]);
        expression_callee_location(source, forms, a, b, r - start);
    };
    assert forall|i: int, j: int| start <= i < j < end implies
        (#[trigger] refs[i]).form < (#[trigger] refs[j]).form by {
        assert(refs[i] == selected[i - start] && refs[j] == selected[j - start]);
    };
}

#[verifier::opaque]
spec fn walk_prefix(
    forms: Seq<Form>, refs: Seq<ExpressionReference>, start: usize, end: usize, cursor: usize,
    pending: Seq<PendingCall>, order: Seq<usize>,
) -> bool {
    &&& start <= cursor <= end
    &&& forall|r: usize| #[trigger] seen_call(pending, order, r) <==> is_callee(refs, start, cursor, r)
    &&& forall|i: int| 0 <= i < order.len() ==> order.contains(#[trigger] order[i])
    &&& forall|i: int| 0 <= i < pending.len() ==> {
        let node = #[trigger] pending[i];
        &&& is_callee(refs, start, cursor, node.reference)
        &&& node.end == call_end(forms, refs, node.reference)
    }
    &&& forall|i: int, j: int| 0 <= i < j < pending.len() ==>
        (#[trigger] pending[i]).reference < (#[trigger] pending[j]).reference
        && pending[j].end <= pending[i].end
    &&& forall|i: int, j: int| 0 <= i < j < order.len() ==>
        precedes(forms, refs, #[trigger] order[i], #[trigger] order[j])
    &&& forall|i: int, j: int| 0 <= i < order.len() && 0 <= j < pending.len() ==>
        precedes(forms, refs, #[trigger] order[i], (#[trigger] pending[j]).reference)
    &&& (cursor < end ==> forall|i: int| 0 <= i < order.len() ==>
        call_end(forms, refs, #[trigger] order[i]) < refs[cursor as int].form)
}

proof fn walk_read_reference(
    forms: Seq<Form>, refs: Seq<ExpressionReference>, start: usize, end: usize, cursor: usize,
    pending: Seq<PendingCall>, order: Seq<usize>, added: Option<PendingCall>,
)
    requires
        reference_bounds(forms, refs, start, end), nested_list_indices(forms),
        walk_prefix(forms, refs, start, end, cursor, pending, order),
        cursor < end,
        pending.len() > 0 ==> refs[cursor as int].form <= pending.last().end,
        added.is_some() <==> refs[cursor as int].kind is Callee,
        added matches Some(node) ==> node.reference == cursor && node.end == call_end(forms, refs, cursor),
    ensures walk_prefix(forms, refs, start, end, (cursor + 1) as usize,
        if let Some(node) = added { pending.push(node) } else { pending }, order),
{
    reveal(walk_prefix);
    reveal(reference_bounds);
    reveal(nested_list_indices);
    let after = if let Some(node) = added { pending.push(node) } else { pending };
    if let Some(node) = added {
        assert(after.last() == node);
        if pending.len() > 0 {
            let top = pending.last();
            assert(top == pending[pending.len() - 1]);
            let parent = call_start(refs, top.reference);
            let child = call_start(refs, cursor);
            assert(parent < child < top.end);
            assert(forms[parent] is List && forms[child] is List);
            assert(node.end <= top.end);
        }
    }
    reveal(contains_call);
    assert forall|r: usize| #[trigger] contains_call(after, r)
        <==> contains_call(pending, r) || (added.is_some() && r == cursor) by {
        if contains_call(after, r) {
            let i = choose|i: int| 0 <= i < after.len() && (#[trigger] after[i]).reference == r;
            if i < pending.len() { assert(after[i] == pending[i]); }
        }
        if contains_call(pending, r) {
            let i = choose|i: int| 0 <= i < pending.len() && (#[trigger] pending[i]).reference == r;
            assert(after[i] == pending[i]);
        }
        if added.is_some() && r == cursor {
            assert(after[pending.len() as int].reference == r);
        }
    };
    assert forall|i: int| 0 <= i < after.len() implies {
        let node = #[trigger] after[i];
        is_callee(refs, start, (cursor + 1) as usize, node.reference) && node.end == call_end(forms, refs, node.reference)
    } by {
        if i < pending.len() { assert(after[i] == pending[i]); }
    };
    assert forall|i: int, j: int| 0 <= i < j < after.len() implies
        (#[trigger] after[i]).reference < (#[trigger] after[j]).reference && after[j].end <= after[i].end by {
        assert(after[i] == pending[i]);
        if j < pending.len() {
            assert(after[j] == pending[j]);
        } else {
            let top = pending[pending.len() - 1];
            assert(top == pending.last());
            if i < pending.len() - 1 { assert(top.end <= pending[i].end); }
        }
    };
    assert forall|i: int, j: int| 0 <= i < order.len() && 0 <= j < after.len() implies
        precedes(forms, refs, #[trigger] order[i], (#[trigger] after[j]).reference) by {
        if j < pending.len() { assert(after[j] == pending[j]); }
        else {
            assert(call_end(forms, refs, order[i]) < refs[cursor as int].form);
            assert(call_end(forms, refs, cursor) >= refs[cursor as int].form + 1);
        }
    };
    assert forall|r: usize| #[trigger] seen_call(after, order, r)
        <==> is_callee(refs, start, (cursor + 1) as usize, r) by {
        assert(seen_call(pending, order, r) == is_callee(refs, start, cursor, r));
        reveal(seen_call);
        assert(contains_call(after, r) == (contains_call(pending, r) || (added.is_some() && r == cursor)));
    };
    if cursor + 1 < end {
        assert(refs[cursor as int].form < refs[cursor + 1].form);
        assert forall|i: int| 0 <= i < order.len() implies
            call_end(forms, refs, #[trigger] order[i]) < refs[cursor + 1].form by {
            assert(call_end(forms, refs, order[i]) < refs[cursor as int].form);
        };
    }
}

proof fn walk_close_call(
    forms: Seq<Form>, refs: Seq<ExpressionReference>, start: usize, end: usize, cursor: usize,
    pending: Seq<PendingCall>, order: Seq<usize>,
)
    requires
        reference_bounds(forms, refs, start, end),
        walk_prefix(forms, refs, start, end, cursor, pending, order),
        pending.len() > 0,
        cursor < end ==> pending.last().end < refs[cursor as int].form,
    ensures walk_prefix(forms, refs, start, end, cursor, pending.drop_last(), order.push(pending.last().reference)),
{
    reveal(walk_prefix);
    reveal(reference_bounds);
    let node = pending.last();
    assert(node == pending[pending.len() - 1]);
    let stack = pending.drop_last();
    let after = order.push(node.reference);
    reveal(contains_call);
    assert forall|r: usize| #[trigger] contains_call(pending, r) <==> contains_call(stack, r) || r == node.reference by {
        if contains_call(pending, r) {
            let k = choose|k: int| 0 <= k < pending.len() && (#[trigger] pending[k]).reference == r;
            if k < stack.len() { assert(stack[k] == pending[k]); }
        }
        if contains_call(stack, r) {
            let k = choose|k: int| 0 <= k < stack.len() && (#[trigger] stack[k]).reference == r;
            assert(stack[k] == pending[k]);
        }
        if r == node.reference { assert(pending[pending.len() - 1].reference == r); }
    };
    assert forall|r: usize| #[trigger] seen_call(stack, after, r) <==> is_callee(refs, start, cursor, r) by {
        assert(seen_call(pending, order, r) == is_callee(refs, start, cursor, r));
        vstd::seq_lib::lemma_seq_contains_after_push(order, node.reference, r);
        assert(contains_call(pending, r) == (contains_call(stack, r) || r == node.reference));
        reveal(seen_call);
    };
    assert forall|i: int| 0 <= i < after.len() implies after.contains(#[trigger] after[i]) by {};
    assert forall|i: int, j: int| 0 <= i < j < after.len() implies
        precedes(forms, refs, #[trigger] after[i], #[trigger] after[j]) by {
        assert(after[i] == order[i]);
        if j < order.len() { assert(after[j] == order[j]); }
        else { assert(after[j] == node.reference); }
    };
    assert forall|i: int, j: int| 0 <= i < after.len() && 0 <= j < stack.len() implies
        precedes(forms, refs, #[trigger] after[i], (#[trigger] stack[j]).reference) by {
        let parent = pending[j];
        assert(stack[j] == parent);
        if i < order.len() { assert(after[i] == order[i]); }
        else {
            assert(after[i] == node.reference);
            assert(parent.reference < node.reference && node.end <= parent.end);
            assert(call_start(refs, parent.reference) < call_start(refs, node.reference));
        }
    };
    if cursor < end {
        assert forall|i: int| 0 <= i < after.len() implies
            call_end(forms, refs, #[trigger] after[i]) < refs[cursor as int].form by {
            if i < order.len() { assert(after[i] == order[i]); }
        };
    }
}

/// 順序内の一項目が、指定した定義の呼び出し参照を指すことを示す。
pub proof fn call_postorder_reference(
    forms: Seq<Form>, references: Seq<ExpressionReference>, range: Range<usize>, order: Seq<usize>, index: int,
)
    requires
        call_references_in_postorder(forms, references, range, order),
        range.end <= references.len(),
        0 <= index < order.len(),
    ensures range.start <= order[index] < range.end, references[order[index] as int].kind is Callee,
{
    reveal(call_references_in_postorder);
    order.lemma_index_contains(index);
    assert(order.contains(order[index]));
}

/// 後順の異なる位置では、同じ呼び出し参照が繰り返されない。
pub proof fn call_postorder_references_distinct(
    forms: Seq<Form>, refs: Seq<ExpressionReference>, range: Range<usize>, order: Seq<usize>,
    i: int, j: int,
)
    requires call_references_in_postorder(forms, refs, range, order), 0 <= i < j < order.len(),
    ensures order[i] != order[j],
{
    reveal(call_references_in_postorder);
    assert(precedes(forms, refs, order[i], order[j]));
}

/// 元ソースで先に始まる呼び出しと、後から始まる呼び出しの処理順を取り出す。
///
/// 後の呼び出しが前の呼び出しの内側なら子を先に処理する。区間が離れていれば元ソース順になる。
pub proof fn call_postorder_positions(
    source: &str, forms: Seq<Form>, references: Seq<ExpressionReference>, row: BuildDefinition,
    order: Seq<usize>, first: usize, second: usize,
) -> (positions: (int, int))
    requires
        definition_call_index(source, forms, row, references), forms.len() <= usize::MAX,
        nested_list_indices(forms), call_references_in_postorder(forms, references, row.references, order),
        row.references.start <= first < second < row.references.end,
        references[first as int].kind is Callee, references[second as int].kind is Callee,
    ensures
        0 <= positions.0 < order.len(), order[positions.0] == first,
        0 <= positions.1 < order.len(), order[positions.1] == second,
        references[first as int].form < references[second as int].form,
        ({
            let parent_start = references[first as int].form - 1;
            let second_start = references[second as int].form - 1;
            let inside = second_start < forms[parent_start]->List_end;
            positions.1 < positions.0 <==> inside
        }),
    {
        row_reference_bounds(source, forms, references, row);
        reveal(reference_bounds);
        reveal(nested_list_indices);
        reveal(call_references_in_postorder);
        assert(order.contains(first) && order.contains(second));
        let a = order.lemma_contains_to_index(first);
        let b = order.lemma_contains_to_index(second);
        let first_start = call_start(references, first);
        let second_start = call_start(references, second);
        let first_end = call_end(forms, references, first);
        let second_end = call_end(forms, references, second);
        assert(a != b && first_start < second_start);
        if second_start < first_end {
            assert(forms[first_start] is List && forms[second_start] is List);
            assert(second_end <= first_end);
            if a < b { assert(precedes(forms, references, first, second)); }
        } else {
            assert(first_end <= second_start < second_end);
            if b < a { assert(precedes(forms, references, second, first)); }
        }
        (a, b)
    }

/// 同じ定義の参照が同じフォームを指すなら、その参照添字は等しい。
pub proof fn definition_reference_form_unique(
    source: &str, forms: Seq<Form>, references: Seq<ExpressionReference>, row: BuildDefinition,
    left: usize, right: usize,
)
    requires
        definition_call_index(source, forms, row, references), forms.len() <= usize::MAX,
        row.references.start <= left < row.references.end,
        row.references.start <= right < row.references.end,
        references[left as int].form == references[right as int].form,
    ensures left == right,
{
    row_reference_bounds(source, forms, references, row);
    reveal(reference_bounds);
    if left < right {
        assert(references[left as int].form < references[right as int].form);
    } else if right < left {
        assert(references[right as int].form < references[left as int].form);
    }
}

/// 親のリスト内で始まる呼び出しについて、親より前の処理位置を返す。
pub proof fn nested_call_postorder_position(
    source: &str, forms: Seq<Form>, references: Seq<ExpressionReference>, row: BuildDefinition,
    order: Seq<usize>, parent: usize, child: usize, parent_position: int,
) -> (position: int)
    requires
        definition_call_index(source, forms, row, references), forms.len() <= usize::MAX,
        nested_list_indices(forms), call_references_in_postorder(forms, references, row.references, order),
        row.references.start <= parent < row.references.end, row.references.start <= child < row.references.end,
        references[parent as int].kind is Callee, references[child as int].kind is Callee,
        0 <= parent_position < order.len(), order[parent_position] == parent,
        references[parent as int].form < references[child as int].form,
        0 <= references[parent as int].form - 1 < forms.len(),
        forms[references[parent as int].form - 1] is List,
        references[child as int].form - 1 < forms[references[parent as int].form - 1]->List_end,
    ensures 0 <= position < parent_position, order[position] == child,
{
    row_reference_bounds(source, forms, references, row);
    reveal(reference_bounds);
    if child < parent {
        assert(references[child as int].form < references[parent as int].form);
    }
    let (first, second) = call_postorder_positions(source, forms, references, row, order, parent, child);
    reveal(call_references_in_postorder);
    if first < parent_position {
        assert(precedes(forms, references, order[first], order[parent_position]));
    } else if parent_position < first {
        assert(precedes(forms, references, order[parent_position], order[first]));
    }
    assert(first == parent_position);
    second
}

/// 右辺全体が通常呼び出しなら、その参照は順序の最後に現れる。
pub proof fn root_call_postorder_last(
    source: &str, forms: Seq<Form>, references: Seq<ExpressionReference>, row: BuildDefinition,
    order: Seq<usize>,
)
    requires
        definition_call_index(source, forms, row, references), forms.len() <= usize::MAX,
        super::expression_forest::ordinary_call_at(source, forms, row.expression.start as int, row.expression.end as int),
        call_references_in_postorder(forms, references, row.references, order),
    ensures order.len() > 0, order.last() == row.references.start,
{
    let first = row.references.start;
    let a = row.expression.start as int;
    let b = row.expression.end as int;
    row_reference_bounds(source, forms, references, row);
    assert(after_form(forms, a) == b);
    expression_root_callee(source, forms, a, b);
    let refs = expression_references(source, forms, a, b);
    assert(refs[0] == references[first as int]);
    reveal(reference_bounds);
    reveal(call_references_in_postorder);
    assert(order.contains(first));
    let at = order.lemma_contains_to_index(first);
    let last = order.len() - 1;
    if at < last {
        let other = order[last];
        order.lemma_index_contains(last);
        assert(order.contains(other));
        assert(first <= other < row.references.end);
        if first < other {
            expression_callee_location(source, forms, a, b, other - first);
            let offset = other - first;
            assert(expression_references(source, forms, a, b)[offset] == references[other as int]);
            assert(call_end(forms, references, other) <= b);
            assert(call_start(references, first) < call_start(references, other));
        }
        assert(call_end(forms, references, first) == b);
        assert(precedes(forms, references, order[at], order[last]));
        assert(false);
    }
    assert(order.last() == order[last]);
}

/// 定義内の呼び出しを、子から親の順に並べて参照添字を返す。
///
/// 厳格解析で得た同じ構文木・定義行・参照配列を渡す。型名参照は結果に含まれない。
/// 右辺を再解析せず、参照を先頭から一度たどる。
///
/// # Panics
///
/// 入力を手動で組み立て、添字や呼び出しリストが対応しない場合はパニックすることがある。
pub fn postorder_call_references(
    _source: &str, forms: &[Form], row: &BuildDefinition, references: &[ExpressionReference],
) -> (order: Vec<usize>)
    requires definition_call_index(_source, forms@, *row, references@), nested_list_indices(forms@),
    ensures call_references_in_postorder(forms@, references@, row.references, order@),
{
    let _length = forms.len();
    let start = row.references.start;
    let end = row.references.end;
    proof {
        row_reference_bounds(_source, forms@, references@, *row);
        reveal(reference_bounds);
        reveal(walk_prefix);
    }
    let mut cursor = start;
    let mut pending: Vec<PendingCall> = Vec::new();
    let mut order: Vec<usize> = Vec::new();
    assert(walk_prefix(forms@, references@, start, end, cursor, pending@, order@)) by {
        reveal(seen_call);
        reveal(contains_call);
    };
    while cursor < end || !pending.is_empty()
        invariant
            start == row.references.start, end == row.references.end,
            reference_bounds(forms@, references@, start, end),
            nested_list_indices(forms@),
            walk_prefix(forms@, references@, start, end, cursor, pending@, order@),
        decreases end - cursor, pending@.len(),
    {
        proof { reveal(walk_prefix); reveal(reference_bounds); }
        let close = !pending.is_empty()
            && (cursor == end || pending[pending.len() - 1].end < references[cursor].form);
        if close {
            let ghost before = pending@;
            let ghost completed = order@;
            let node = pending.pop().unwrap();
            order.push(node.reference);
            proof {
                walk_close_call(forms@, references@, start, end, cursor, before, completed);
            }
        } else {
            let ghost before = pending@;
            let item = &references[cursor];
            if matches!(item.kind, ExpressionReferenceKind::Callee) {
                let form = item.form - 1;
                let Form::List { end: close, .. } = &forms[form] else {
                    proof { assert(false); }
                    unreachable!()
                };
                let node = PendingCall { reference: cursor, end: *close };
                pending.push(node);
                proof { walk_read_reference(forms@, references@, start, end, cursor, before, order@, Some(node)); }
            } else {
                proof { walk_read_reference(forms@, references@, start, end, cursor, before, order@, None); }
            }
            cursor += 1;
        }
    }
    proof {
        reveal(walk_prefix);
        reveal(call_references_in_postorder);
        assert forall|r: usize| #[trigger] order@.contains(r) <==> is_callee(references@, start, end, r) by {
            assert(seen_call(pending@, order@, r) == is_callee(references@, start, end, r));
            reveal(seen_call);
            reveal(contains_call);
        };
    }
    order
}

} // verus!
