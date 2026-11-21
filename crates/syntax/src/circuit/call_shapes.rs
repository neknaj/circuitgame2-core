//! 検査済みの右辺と参照索引から、通常呼び出しの引数数と位置を求める。

#[cfg(verus_only)]
use super::expression_forest::{
    call_argument_signal_index, expression_callee_location, expression_forest, expression_references,
    expression_references_in_order, expression_region, expression_root_callee, expression_signals,
    expression_signals_in_order, ordinary_call_at, ordinary_call_in_reference_index, signal_indices_in_order,
};
#[cfg(verus_only)]
use super::expressions::after_form;
use super::ports::routine_layout;
#[cfg(verus_only)]
use super::ports::{RoutineLayout, routine_layout_matches};
use super::*;

verus! {

/// 通常呼び出しの元構文と、直接の引数の個数。
#[derive(Debug, Eq, PartialEq)]
pub struct CallShape {
    /// 平坦な構文木で呼び出しのリストを指す添字。
    pub form: usize,
    /// 呼び出し全体の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 入れ子の式も一つと数えた、呼び出しの直接の引数の個数。
    pub arguments: usize,
}

/// 関数またはモジュールが宣言した入出力ポートの個数。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RoutineArity {
    /// `in` 節のポート数。入力がなければ 0。
    pub inputs: usize,
    /// `out` 節のポート数。厳格索引では 1 以上。
    pub outputs: usize,
}

/// 定義の参照範囲が、検査済みの右辺を文法上の子式に沿ってたどった結果に対応することを表す。
pub open spec fn definition_call_index(
    source: &str, forms: Seq<Form>, row: BuildDefinition, references: Seq<ExpressionReference>,
) -> bool {
    let start = row.expression.start as int;
    let end = row.expression.end as int;
    &&& 0 <= start < end <= forms.len()
    &&& end == if forms[start] is List { forms[start]->List_end as int } else { start + 1 }
    &&& expression_forest(source, forms, start, end)
    &&& row.references.start <= row.references.end <= references.len()
    &&& references[row.references.start as int..row.references.end as int] == expression_references(source, forms, start, end)
}

#[verifier::opaque]
pub(super) open spec fn argument_count(forms: Seq<Form>, first: int, end: int) -> nat
    decreases end - first,
{
    if 0 <= first < end <= forms.len() && first < after_form(forms, first) <= end {
        1 + argument_count(forms, after_form(forms, first), end)
    } else {
        0
    }
}

/// 呼び出しの種類、元のリスト位置、引数数が索引項目と文法に合うことを表す。
pub closed spec fn call_shape_matches(
    source: &str, forms: Seq<Form>, row: BuildDefinition, reference: ExpressionReference,
    shape: Option<CallShape>,
) -> bool {
    if reference.kind is Callee {
        let call = reference.form - 1;
        shape matches Some(shape)
            && row.expression.start <= call && ordinary_call_at(source, forms, call, row.expression.end as int)
            && shape.form == call && shape.span == form_span(forms[call])
            && shape.arguments == argument_count(forms, call + 2, forms[call]->List_end as int)
            && shape.span.start < shape.span.end <= source.spec_bytes().len()
            && is_char_boundary(source.spec_bytes(), shape.span.start as int)
            && is_char_boundary(source.spec_bytes(), shape.span.end as int)
    } else {
        shape is None
    }
}

/// 同じ呼び出し参照のリスト位置、範囲、引数数は一意に定まる。
pub proof fn indexed_call_shapes_agree(
    source: &str, forms: Seq<Form>, row: BuildDefinition, reference: ExpressionReference,
    first: CallShape, second: CallShape,
)
    requires
        call_shape_matches(source, forms, row, reference, Some(first)),
        call_shape_matches(source, forms, row, reference, Some(second)),
    ensures first == second,
{
}

/// 右辺全体が通常呼び出しなら、先頭の参照がその呼び出しを指すことを示す。
pub proof fn root_call_shape_location(
    source: &str, forms: Seq<Form>, row: BuildDefinition, references: Seq<ExpressionReference>, call: CallShape,
)
    requires
        definition_call_index(source, forms, row, references),
        forms.len() <= usize::MAX,
        ordinary_call_at(source, forms, row.expression.start as int, row.expression.end as int),
        row.references.start < row.references.end <= references.len(),
        call_shape_matches(source, forms, row, references[row.references.start as int], Some(call)),
    ensures call.form == row.expression.start,
{
    expression_root_callee(source, forms, row.expression.start as int, row.expression.end as int);
    let refs = references.subrange(row.references.start as int, row.references.end as int);
    assert(refs[0] == references[row.references.start as int]);
}

/// 呼び出しの構文木に直接の引数列があり、その個数が索引に記録した値と一致することを表す。
pub closed spec fn call_arguments_match(forms: Seq<Form>, call: CallShape) -> bool {
    let form = call.form as int;
    &&& form < forms.len() && forms[form] is List
    &&& form + 2 <= forms[form]->List_end <= forms.len()
    &&& call.arguments == argument_count(forms, form + 2, forms[form]->List_end as int)
}

/// 呼び出し直下の引数式を、元の出現順にすべて列挙した添字列を表す。
pub closed spec fn call_argument_positions(forms: Seq<Form>, call: CallShape, positions: Seq<usize>) -> bool {
    let first = call.form + 2;
    let end = forms[call.form as int]->List_end;
    &&& call_arguments_match(forms, call)
    &&& positions.len() == call.arguments
    &&& if positions.len() == 0 { first == end }
        else { after_form(forms, positions.last() as int) == end }
    &&& forall|i: int| 0 <= i < positions.len() ==> {
        let at = (#[trigger] positions[i]) as int;
        &&& first <= at < end
        &&& at < after_form(forms, at) <= end
        &&& at == if i == 0 { first } else { after_form(forms, positions[i - 1] as int) }
    }
}

/// 組み立てた引数列が、各部分木の終端をたどって呼び出しの末尾に達することを示す。
pub proof fn call_argument_positions_from_steps(forms: Seq<Form>, call: CallShape, positions: Seq<usize>)
    requires
        call_arguments_match(forms, call), complete_list_indices(forms), nested_list_indices(forms),
        positions.len() == call.arguments,
        if positions.len() == 0 { call.form + 2 == forms[call.form as int]->List_end }
            else {
                let last = positions.last() as int;
                forms[call.form as int]->List_end as int
                    == if forms[last] is List { forms[last]->List_end as int } else { last + 1 }
            },
        forall|i: int| 0 <= i < positions.len() ==> {
            let at = (#[trigger] positions[i]) as int;
            &&& direct_call_argument(forms, call, at)
            &&& at == if i == 0 { call.form + 2 } else {
                let previous = positions[i - 1] as int;
                if forms[previous] is List { forms[previous]->List_end as int } else { previous + 1 }
            }
        },
    ensures call_argument_positions(forms, call, positions),
{
    reveal(direct_form_in_range);
    reveal(complete_list_indices);
    assert forall|i: int| 0 <= i < positions.len() implies {
        let at = (#[trigger] positions[i]) as int;
        &&& call.form + 2 <= at < forms[call.form as int]->List_end
        &&& at < after_form(forms, at) <= forms[call.form as int]->List_end
    } by {
        let at = positions[i] as int;
        assert(direct_call_argument(forms, call, at));
    };
}

/// 呼び出し形状は構文木内のリストを指す。引数が空の呼び出しにも適用できる。
pub proof fn call_form_bounds(forms: Seq<Form>, call: CallShape)
    requires call_arguments_match(forms, call),
    ensures call.form < forms.len(), forms[call.form as int] is List,
{}

/// 引数の先頭は、その呼び出しリストの内部にある。
pub proof fn call_argument_position_bounds(forms: Seq<Form>, call: CallShape, positions: Seq<usize>, port: int)
    requires call_argument_positions(forms, call, positions), 0 <= port < positions.len(),
    ensures call.form + 2 <= positions[port] < forms[call.form as int]->List_end <= forms.len(),
{}

/// 呼び出し内のフォームを含む直接引数を見つける。フォーム自体が引数の先頭でもよい。
proof fn call_argument_containing_form(forms: Seq<Form>, call: CallShape, positions: Seq<usize>, form: int)
    -> (port: int)
    requires
        call_argument_positions(forms, call, positions),
        call.form + 2 <= form < forms[call.form as int]->List_end,
    ensures
        0 <= port < positions.len(),
        call.form + 2 <= positions[port] <= form,
        if forms[positions[port] as int] is List {
            form < forms[positions[port] as int]->List_end <= forms[call.form as int]->List_end
        } else { form == positions[port] },
{
    let last = positions.len() as int - 1;
    assert(positions[last] == positions.last());
    call_argument_in_prefix(forms, call, positions, form, last)
}

proof fn call_argument_in_prefix(forms: Seq<Form>, call: CallShape, positions: Seq<usize>, form: int, last: int)
    -> (port: int)
    requires
        call_argument_positions(forms, call, positions),
        0 <= last < positions.len(),
        call.form + 2 <= form < after_form(forms, positions[last] as int),
    ensures
        0 <= port <= last,
        call.form + 2 <= positions[port] <= form < after_form(forms, positions[port] as int)
            <= forms[call.form as int]->List_end,
    decreases last,
{
    let start = positions[last] as int;
    if start <= form {
        last
    } else {
        assert(last > 0);
        assert(start == after_form(forms, positions[last - 1] as int));
        call_argument_in_prefix(forms, call, positions, form, last - 1)
    }
}

/// 通常呼び出し内のリストは、いずれかの直接引数のリストに含まれる。
pub proof fn call_argument_containing_list(
    source: &str, forms: Seq<Form>, call: CallShape, positions: Seq<usize>, stop: int, descendant: int,
) -> (port: int)
    requires
        ordinary_call_at(source, forms, call.form as int, stop),
        call_argument_positions(forms, call, positions),
        call.form < descendant < forms[call.form as int]->List_end <= forms.len(),
        forms[descendant] is List,
    ensures
        0 <= port < positions.len(),
        call.form + 2 <= positions[port] <= descendant,
        forms[positions[port] as int] is List,
        descendant < forms[positions[port] as int]->List_end <= forms[call.form as int]->List_end,
{
    super::expression_forest::ordinary_call_bounds(source, forms, call.form as int, stop);
    let port = call_argument_containing_form(forms, call, positions, descendant);
    assert(forms[positions[port] as int] is List);
    port
}

/// 二つの列が同じ呼び出しの引数を列挙するなら、対応する引数の位置は等しい。
pub proof fn call_argument_positions_agree(forms: Seq<Form>, call: CallShape, a: Seq<usize>, b: Seq<usize>)
    requires call_argument_positions(forms, call, a), call_argument_positions(forms, call, b),
    ensures a == b,
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == #[trigger] b[i] by {
        call_argument_position_agrees(forms, call, a, b, i);
    };
    assert(a =~= b);
}

proof fn call_argument_position_agrees(forms: Seq<Form>, call: CallShape, a: Seq<usize>, b: Seq<usize>, i: int)
    requires call_argument_positions(forms, call, a), call_argument_positions(forms, call, b), 0 <= i < a.len(),
    ensures a[i] == b[i],
    decreases i,
{
    if i > 0 {
        call_argument_position_agrees(forms, call, a, b, i - 1);
        assert(a[i - 1] == b[i - 1]);
    }
}

/// 参照索引から得た呼び出しの形を、直接の引数列に結び付ける。
pub proof fn indexed_call_arguments(
    source: &str, forms: Seq<Form>, row: BuildDefinition, reference: ExpressionReference, call: CallShape,
)
    requires call_shape_matches(source, forms, row, reference, Some(call)),
    ensures
        call_arguments_match(forms, call),
        ordinary_call_at(source, forms, call.form as int, row.expression.end as int),
{
    super::expression_forest::ordinary_call_bounds(source, forms, reference.form - 1, row.expression.end as int);
}

/// 呼び出しの引数として残っている構文木範囲に、指定数の直接の式が並ぶことを表す。
pub closed spec fn call_argument_sequence(forms: Seq<Form>, range: Range<usize>, count: int) -> bool {
    expression_region(forms, range.start as int, range.end as int)
        && count == argument_count(forms, range.start as int, range.end as int)
}

/// 引数列の末尾に達したなら、残りの引数はないことを示す。
pub proof fn exhausted_call_arguments(forms: Seq<Form>, range: Range<usize>, count: int)
    requires call_argument_sequence(forms, range, count), range.start == range.end,
    ensures count == 0,
{
    reveal_with_fuel(argument_count, 1);
}

/// 添字が呼び出し直下の引数式の先頭を指すことを表す。
pub closed spec fn direct_call_argument(forms: Seq<Form>, call: CallShape, index: int) -> bool {
    call_arguments_match(forms, call)
        && direct_form_in_range(forms, call.form + 2, forms[call.form as int]->List_end as int, index)
}


/// 直接の引数の部分木が、呼び出しリストの内部に収まることを示す。
pub proof fn direct_call_argument_bounds(forms: Seq<Form>, call: CallShape, index: int)
    requires direct_call_argument(forms, call, index), nested_list_indices(forms), complete_list_indices(forms),
    ensures ({
        let end = forms[call.form as int]->List_end as int;
        let next = if forms[index] is List { forms[index]->List_end as int } else { index + 1 };
        &&& call.form < forms.len() && forms[call.form as int] is List
        &&& call.form + 2 <= index < next <= end <= forms.len()
    }),
{
    reveal(direct_form_in_range);
    reveal(nested_list_indices);
    reveal(complete_list_indices);
}

/// 呼び出しの引数列が空でなければ、先頭を直接の引数として扱えることを示す。
pub proof fn first_call_argument_evidence(forms: Seq<Form>, call: CallShape, range: Range<usize>)
    requires
        call_arguments_match(forms, call), range.start == call.form + 2,
        range.end == forms[call.form as int]->List_end,
    ensures range.start < range.end ==> direct_call_argument(forms, call, range.start as int),
{
    reveal(direct_form_in_range);
}

/// 一つの引数の部分木を飛ばした位置が、列の末尾か次の直接の引数であることを示す。
pub proof fn following_call_argument(
    forms: Seq<Form>, call: CallShape, index: int, next: int,
)
    requires
        direct_call_argument(forms, call, index), nested_list_indices(forms),
        0 <= index < next <= forms[call.form as int]->List_end <= forms.len(),
        next == if forms[index] is List { forms[index]->List_end as int } else { index + 1 },
    ensures next < forms[call.form as int]->List_end ==> direct_call_argument(forms, call, next),
{
    node_end_is_following_direct_form(forms, index, next);
    reveal(following_direct_form);
    assert(form_region_ends_at(forms, call.form + 2, forms[call.form as int]->List_end as int));
}

/// 呼び出しの直接の裸名に対応する、ファイル全体の信号索引の添字を返す。
///
/// 厳格解析で得た同一ファイルの構文木と索引を渡す。定義の信号区間を二分探索する。
///
/// # Panics
///
/// 同じ解析から得た索引を渡さず、該当する信号の添字を取得できない場合はパニックする。
pub fn indexed_call_signal(
    _source: &str, _forms: &[Form], row: &BuildDefinition, _references: &[ExpressionReference],
    _reference: usize, _call: &CallShape, signals: &[usize], argument: usize,
) -> (position: usize)
    requires
        definition_call_index(_source, _forms@, *row, _references@),
        row.references.start <= _reference < row.references.end,
        call_shape_matches(_source, _forms@, *row, _references@[_reference as int], Some(*_call)),
        row.signals.start <= row.signals.end <= signals@.len(),
        signals@[row.signals.start as int..row.signals.end as int]
            == expression_signals(_source, _forms@, row.expression.start as int, row.expression.end as int),
        complete_list_indices(_forms@), nested_list_indices(_forms@),
        direct_call_argument(_forms@, *_call, argument as int),
        argument < _forms@.len() && _forms@[argument as int] is Atom
            && _forms@[argument as int]->Atom_kind is Name,
    ensures row.signals.start <= position < row.signals.end && signals@[position as int] == argument,
{
    let first = row.signals.start;
    let mut lo = first;
    let mut hi = row.signals.end;
    let _forms_len = _forms.len();
    let ghost indexed = signals@[first as int..hi as int];
    proof {
        let start = row.expression.start as int;
        let stop = row.expression.end as int;
        reveal(nested_list_indices);
        reveal(expression_region);
        assert forall|f: int| start <= f < stop && #[trigger] _forms@[f] is List
            implies _forms@[f]->List_end <= stop by {
            if f != start {
                assert(_forms@[start] is List && _forms@[start]->List_end == stop);
            }
        };
        let refs = _references@[row.references.start as int..row.references.end as int];
        let offset = _reference - row.references.start;
        assert(refs[offset] == _references@[_reference as int]);
        call_argument_signal_index(_source, _forms@, start, stop, offset, argument);
        expression_signals_in_order(_source, _forms@, start, stop);
    }
    let ghost at = choose|i: int| 0 <= i < indexed.len() && indexed[i] == argument;
    let ghost target = (first + at) as int;
    assert(signals@[target] == indexed[at]);
    while lo < hi
        invariant
            first == row.signals.start, first <= lo <= target < hi <= row.signals.end <= signals@.len(),
            indexed == signals@[first as int..row.signals.end as int],
            signals@[target] == argument, signal_indices_in_order(indexed),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let value = signals[mid];
        proof {
            assert(signals@[mid as int] == indexed[mid - first]);
            assert(signals@[target] == indexed[target - first]);
        }
        if value < argument {
            assert(mid < target);
            lo = mid + 1;
        } else if value > argument {
            assert(target < mid);
            hi = mid;
        } else {
            return mid;
        }
    }
    proof { assert(false); }
    unreachable!()
}

/// 検査済みの呼び出しから、引数列の構文木範囲を返す。
///
/// 戻り値は半開範囲で、呼び出し名を含まない。引数がなければ空になる。
///
/// # Panics
///
/// 呼び出しの添字と構文木を手動で組み立て、対応しない値を渡すとパニックすることがある。
pub fn call_argument_range(forms: &[Form], call: &CallShape) -> (range: Range<usize>)
    requires call_arguments_match(forms@, *call), nested_list_indices(forms@),
    ensures
        call_argument_sequence(forms@, range, call.arguments as int),
        expression_region(forms@, range.start as int, range.end as int),
        range.start == call.form + 2 <= range.end <= forms@.len(),
        call.form < forms@.len() && forms@[call.form as int] is List,
        range.end == forms@[call.form as int]->List_end,
{
    let Form::List { end: list_end, .. } = &forms[call.form] else {
        proof { assert(false); }
        unreachable!()
    };
    proof { list_children_region(forms@, call.form as int, call.form + 2, *list_end as int); }
    call.form + 2..*list_end
}

/// 残りの引数列から、先頭の引数式が占める半開範囲を返す。
///
/// 通常呼び出しや [`concat`](super::concat_argument_range) の引数範囲を渡せる。
/// 次の呼び出しでは、この範囲の末尾を残りの引数列の先頭に使う。
/// 入れ子のリストは、その末尾の添字まで一度に進む。
///
/// # Panics
///
/// 構文木と引数範囲を手動で変更し、範囲が構文木に収まらなければパニックすることがある。
pub fn next_call_argument(
    forms: &[Form], remaining: Range<usize>,
) -> (argument: Option<Range<usize>>)
    requires expression_region(forms@, remaining.start as int, remaining.end as int), complete_list_indices(forms@),
    ensures
        argument.is_none() <==> remaining.start == remaining.end,
        argument matches Some(arg) ==>
            arg.start == remaining.start && arg.start < arg.end <= remaining.end
                && arg.end == (if forms@[arg.start as int] is List {
                    forms@[arg.start as int]->List_end as int
                } else { arg.start + 1 })
                && expression_region(forms@, arg.end as int, remaining.end as int),
        forall|count: int| #[trigger] call_argument_sequence(forms@, remaining, count) ==> match argument {
            None => count == 0,
            Some(arg) => 0 < count && call_argument_sequence(forms@, (arg.end..remaining.end), count - 1),
        },
{
    proof {
        reveal(expression_region);
        reveal(complete_list_indices);
        reveal_with_fuel(argument_count, 1);
    }
    if remaining.start == remaining.end {
        return None;
    }
    let end = match &forms[remaining.start] {
        Form::Atom { .. } => remaining.start + 1,
        Form::List { end, .. } => *end,
    };
    assert(expression_region(forms@, end as int, remaining.end as int));
    Some(remaining.start..end)
}

fn count_arguments(forms: &[Form], first: usize, end: usize) -> (count: usize)
    requires expression_region(forms@, first as int, end as int), complete_list_indices(forms@),
    ensures count == argument_count(forms@, first as int, end as int),
{
    let mut index = first;
    let mut count: usize = 0;
    proof { reveal(expression_region); }
    while index < end
        invariant
            complete_list_indices(forms@), expression_region(forms@, first as int, end as int),
            first <= index <= end <= forms@.len(),
            count <= index - first,
            count + argument_count(forms@, index as int, end as int)
                == argument_count(forms@, first as int, end as int),
        decreases end - index,
    {
        let next = match &forms[index] {
            Form::Atom { .. } => index + 1,
            Form::List { end, .. } => *end,
        };
        proof {
            reveal(expression_region);
            reveal(complete_list_indices);
            assert(index < next <= end);
            reveal_with_fuel(argument_count, 1);
        }
        index = next;
        count += 1;
    }
    proof { reveal_with_fuel(argument_count, 1); }
    count
}

pub(super) proof fn list_children_region(forms: Seq<Form>, parent: int, first: int, end: int)
    requires
        0 <= parent < first <= end <= forms.len(),
        forms[parent] is List && forms[parent]->List_end == end,
        nested_list_indices(forms),
    ensures expression_region(forms, first, end),
{
    reveal(expression_region);
    reveal(nested_list_indices);
    assert forall|i: int| first <= i < end && #[trigger] forms[i] is List
        implies forms[i]->List_end <= end by {
        assert(parent < i < forms[parent]->List_end);
    };
}

/// `def` の右辺全体が、回路を呼び出す式であるかを調べる。
///
/// 元の構文木と検査済みの参照索引を渡す。右辺を再走査せず、最初の参照だけを調べる。
///
/// # Panics
///
/// 空でない参照範囲の先頭が配列の外を指す場合はパニックする。
pub fn definition_root_is_call(
    _source: &str, forms: &[Form], row: &BuildDefinition, references: &[ExpressionReference],
) -> (call: bool)
    requires definition_call_index(_source, forms@, *row, references@),
    ensures
        call == ordinary_call_at(_source, forms@, row.expression.start as int, row.expression.end as int),
        call <==> row.references.start < row.references.end
            && references@[row.references.start as int].kind is Callee
            && references@[row.references.start as int].form == row.expression.start + 1,
{
    let _length = forms.len();
    proof {
        expression_root_callee(_source, forms@, row.expression.start as int, row.expression.end as int);
    }
    if row.references.start == row.references.end {
        return false;
    }
    let first = &references[row.references.start];
    matches!(first.kind, ExpressionReferenceKind::Callee)
        && first.form == row.expression.start + 1
}

/// 定義の参照索引から、指定した通常呼び出しの参照を探す。
///
/// ソース、構文木、定義、参照配列は、同じ厳格解析の入力と結果から渡す。
/// `form` は式の先頭を指す構文木添字。見つかった参照の添字はファイル全体の参照配列を基準とする。
/// 専用フォームやアトムを指定した場合、または添字が定義の右辺の外にある場合は `None` を返す。
/// 定義の参照範囲が配列に収まらない場合も `None` を返す。
pub fn callee_reference_at_form(
    _source: &str, _forms: &[Form], row: &BuildDefinition, references: &[ExpressionReference], form: usize,
) -> (reference: Option<usize>)
    requires definition_call_index(_source, _forms@, *row, references@),
    ensures
        reference.is_some() <==>
            row.expression.start <= form < row.expression.end
                && ordinary_call_at(_source, _forms@, form as int, row.expression.end as int),
        row.expression.start <= form < row.expression.end ==>
            (reference.is_some() <==> exists|i: int| row.references.start <= i < row.references.end
                && (#[trigger] references@[i]).form == form + 1 && references@[i].kind is Callee),
        reference matches Some(at) ==>
            row.references.start <= at < row.references.end
                && references@[at as int].form == form + 1
                && references@[at as int].kind is Callee,
{
    if form < row.expression.start || form >= row.expression.end {
        return None;
    }
    let first = row.references.start;
    let end = row.references.end;
    if first > end || end > references.len() {
        proof { assert(false); }
        return None;
    }
    let key = form + 1;
    let _length = _forms.len();
    proof {
        callee_reference_search_evidence(_source, _forms@, *row, references@, form);
    }
    let mut lo = first;
    let mut hi = end;
    while lo < hi
        invariant
            row.expression.start <= form < row.expression.end,
            key == form + 1,
            first == row.references.start, end == row.references.end,
            first <= lo <= hi <= end <= references@.len(),
            forall|i: int, j: int| first <= i < j < end ==>
                (#[trigger] references@[i]).form < (#[trigger] references@[j]).form,
            forall|i: int| first <= i < end && (#[trigger] references@[i]).form == key ==> lo <= i < hi,
            ordinary_call_at(_source, _forms@, form as int, row.expression.end as int)
                <==> exists|i: int| first <= i < end
                    && (#[trigger] references@[i]).form == key && references@[i].kind is Callee,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let item = &references[mid];
        if item.form < key {
            assert forall|i: int| first <= i < end && (#[trigger] references@[i]).form == key
                implies mid < i by { assert(references@[mid as int] == *item); };
            lo = mid + 1;
        } else if item.form > key {
            assert forall|i: int| first <= i < end && (#[trigger] references@[i]).form == key
                implies i < mid by { assert(references@[mid as int] == *item); };
            hi = mid;
        } else {
            assert(references@[mid as int] == *item);
            if matches!(item.kind, ExpressionReferenceKind::Callee) {
                assert(exists|i: int| first <= i < end
                    && (#[trigger] references@[i]).form == key && references@[i].kind is Callee);
                return Some(mid);
            }
            proof {
                assert forall|i: int| first <= i < end && (#[trigger] references@[i]).form == key
                    implies i == mid by {};
            }
            return None;
        }
    }
    None
}

proof fn callee_reference_search_evidence(
    source: &str, forms: Seq<Form>, row: BuildDefinition, references: Seq<ExpressionReference>, form: usize,
)
    requires
        forms.len() <= usize::MAX,
        definition_call_index(source, forms, row, references),
        row.expression.start <= form < row.expression.end,
    ensures ({
        let first = row.references.start as int;
        let end = row.references.end as int;
        &&& forall|i: int, j: int| first <= i < j < end ==>
            (#[trigger] references[i]).form < (#[trigger] references[j]).form
        &&& (ordinary_call_at(source, forms, form as int, row.expression.end as int)
            <==> exists|i: int| first <= i < end
                && (#[trigger] references[i]).form == form + 1 && references[i].kind is Callee)
    }),
{
    let start = row.expression.start as int;
    let stop = row.expression.end as int;
    let first = row.references.start as int;
    let end = row.references.end as int;
    let refs = expression_references(source, forms, start, stop);
    expression_references_in_order(source, forms, start, stop);
    assert forall|i: int, j: int| first <= i < j < end implies
        (#[trigger] references[i]).form < (#[trigger] references[j]).form by {
        assert(references[i] == refs[i - first]);
        assert(references[j] == refs[j - first]);
    };
    if ordinary_call_at(source, forms, form as int, stop) {
        ordinary_call_in_reference_index(source, forms, start, stop, form as int, stop);
        let i = choose|i: int| 0 <= i < refs.len() && (#[trigger] refs[i]).form == form + 1 && refs[i].kind is Callee;
        assert(references[first + i] == refs[i]);
    }
    if exists|i: int| first <= i < end && (#[trigger] references[i]).form == form + 1 && references[i].kind is Callee {
        let i = choose|i: int| first <= i < end && (#[trigger] references[i]).form == form + 1 && references[i].kind is Callee;
        assert(references[i] == refs[i - first]);
        expression_callee_location(source, forms, start, stop, i - first);
    }
}

/// 検査済みの定義に属する参照から、通常呼び出しの形を取り出す。
///
/// `position` はファイル全体の参照配列の添字。型名の参照には `None` を返す。
/// 引数の個数は各引数の先頭をたどって求め、入れ子のリストの中は読み直さない。
///
/// # Panics
///
/// 参照の添字が配列の範囲外にあるか、呼び出し名の直前に対応するリストがなければパニックする。
pub fn indexed_call_shape(
    _source: &str, forms: &[Form], _row: &BuildDefinition,
    references: &[ExpressionReference], position: usize,
) -> (shape: Option<CallShape>)
    requires
        definition_call_index(_source, forms@, *_row, references@),
        _row.references.start <= position < _row.references.end,
        complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(_source, forms@, _source.spec_bytes().len() as int),
    ensures
        call_shape_matches(_source, forms@, *_row, references@[position as int], shape),
        shape.is_some() <==> references@[position as int].kind is Callee,
        shape matches Some(call) ==>
            _row.expression.start <= call.form < _row.expression.end <= forms@.len()
                && call.form + 1 == references@[position as int].form
                && call.span.start < call.span.end <= _source.spec_bytes().len()
                && is_char_boundary(_source.spec_bytes(), call.span.start as int)
                && is_char_boundary(_source.spec_bytes(), call.span.end as int),
{
    let reference = &references[position];
    if !matches!(reference.kind, ExpressionReferenceKind::Callee) {
        return None;
    }
    let _length = forms.len();
    proof {
        let refs = references@[_row.references.start as int.._row.references.end as int];
        let offset = position - _row.references.start;
        assert(refs[offset] == *reference);
        expression_callee_location(_source, forms@, _row.expression.start as int, _row.expression.end as int, offset);
    }
    let form = reference.form - 1;
    let Form::List { span: list_span, end: list_end } = &forms[form] else {
        proof { assert(false); }
        unreachable!();
    };
    proof {
        reveal(form_spans_valid);
        list_children_region(forms@, form as int, form + 2, *list_end as int);
    }
    let arguments = count_arguments(forms, form + 2, *list_end);
    Some(CallShape { form, span: list_span.start..list_span.end, arguments })
}

/// 厳格索引にある署名の `in` と `out` が、指定のポート数を持つことを表す。
pub closed spec fn routine_arity_matches(
    source: &str, syntax: &CircuitForms, entry: int, arity: Option<RoutineArity>,
) -> bool {
    let forms = syntax.forms@;
    match arity {
        Some(arity) => exists|layout: RoutineLayout|
            #[trigger] routine_layout_matches(source, syntax, entry, Some(layout))
                && arity.inputs == argument_count(forms, layout.input + 2, layout.output as int)
                && arity.outputs == argument_count(forms, layout.output + 2, layout.body as int)
                && arity.outputs > 0,
        None => routine_layout_matches(source, syntax, entry, None),
    }
}

/// 個数だけを取り出した署名と、全ポートを取り出した署名が同じ個数を持つことを示す。
pub proof fn routine_arity_port_counts(
    source: &str, syntax: &CircuitForms, entry: int, arity: RoutineArity, ports: RoutinePorts,
)
    requires
        routine_arity_matches(source, syntax, entry, Some(arity)),
        routine_ports_match(source, syntax, entry, Some(ports)),
    ensures arity.inputs == ports.inputs@.len(), arity.outputs == ports.outputs@.len(),
{
    let forms = syntax.forms@;
    let layout = choose|layout: RoutineLayout|
        #[trigger] routine_layout_matches(source, syntax, entry, Some(layout))
            && arity.inputs == argument_count(forms, layout.input + 2, layout.output as int)
            && arity.outputs == argument_count(forms, layout.output + 2, layout.body as int)
            && arity.outputs > 0;
    super::ports::routine_port_list_counts(source, syntax, entry, ports, layout);
}

/// 厳格索引の項目から、宣言された入力数と出力数を求める。
///
/// ポート一覧は割り当てず、型を指定したポートも一つと数える。
/// 添字が範囲外か、項目が `func` と `module` のいずれでもなければ `None` を返す。
///
/// # Panics
///
/// 手動で作った索引の添字やリスト範囲が、元の構文木と対応していなければパニックすることがある。
pub fn routine_arity(
    source: &str, syntax: &CircuitForms, entry: usize,
) -> (arity: Option<RoutineArity>)
    requires
        circuit_index_matches(source, syntax.forms@, syntax.entries@),
        complete_list_indices(syntax.forms@), nested_list_indices(syntax.forms@),
    ensures
        routine_arity_matches(source, syntax, entry as int, arity),
        arity.is_some() <==> entry < syntax.entries@.len()
            && (syntax.entries@[entry as int].head is Func || syntax.entries@[entry as int].head is Module),
        arity matches Some(counts) ==> counts.outputs > 0,
{
    let layout = routine_layout(source, syntax, entry)?;
    let forms = syntax.forms.as_slice();
    proof {
        list_children_region(forms@, layout.input as int, layout.input + 2, layout.output as int);
        list_children_region(forms@, layout.output as int, layout.output + 2, layout.body as int);
    }
    let inputs = count_arguments(forms, layout.input + 2, layout.output);
    let outputs = count_arguments(forms, layout.output + 2, layout.body);
    proof {
        reveal(expression_region);
        reveal(complete_list_indices);
        reveal_with_fuel(argument_count, 1);
        assert(layout.output + 2 < layout.body);
        assert(layout.output + 2 < after_form(forms@, layout.output + 2) <= layout.body);
        assert(outputs > 0);
    }
    Some(RoutineArity { inputs, outputs })
}

} // verus!
