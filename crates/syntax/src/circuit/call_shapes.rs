//! 検査済みの右辺と参照索引から、通常呼び出しの引数数と位置を求める。

#[cfg(verus_only)]
use super::expression_forest::{
    expression_callee_location, expression_forest, expression_references, expression_region,
    expression_root_callee, ordinary_call_at,
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
spec fn argument_count(forms: Seq<Form>, first: int, end: int) -> nat
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

proof fn list_children_region(forms: Seq<Form>, parent: int, first: int, end: int)
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
