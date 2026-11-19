//! 確定した回路フォームの境界から、局所の診断を記録して兄弟の検査を続ける。

use super::*;
use crate::{Recovered, parse_recovering};
#[cfg(verus_only)]
use crate::{inserted_closes_match, original_list_ranges, repair_input_spans_valid};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::valid_utf8;

verus! {

/// エディタ向けの回路フォーム検査結果。
#[derive(Debug)]
pub enum CircuitRecovery {
    /// 回路文法に従ったソースから得た厳格索引。
    Complete(CircuitForms),
    /// S 式として読めるソースに、回路文法の違反がある。
    Inspected {
        /// 元入力の厳格な S 式構文木。
        forms: Vec<Form>,
        /// 検査したフォームと、各フォームに対する判定を元ソース順に並べた一覧。
        checked: Vec<RecoveredCircuitForm>,
    },
    /// 字句または S 式を修復し、元入力で境界が確定したリストを個別に検査した。
    WithSyntaxRepairs {
        /// ファイル全体の暫定構文木と修復記録。
        recovered: Recovered,
        /// `recovered.original_lists` と同じ順で並ぶ検査結果。
        ///
        /// 各区間を一つのリストとして厳格に読み直せたときに結果を付ける。
        original: Vec<Option<OriginalCircuitList>>,
    },
}

/// 元入力の一つのリストを厳格に解析し、回路文法に照らして検査した結果。
#[derive(Debug)]
pub struct OriginalCircuitList {
    /// 元入力全体に対する、このリストの UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 区間内の厳格な構文木。各範囲は `span.start` を起点とする。
    pub forms: Vec<Form>,
    /// ルートと検査可能な名前空間直下の判定。添字はこの構文木を参照する。
    ///
    /// 主診断と関連箇所のバイト位置は区間内の位置である。ファイル内の位置には `span.start` を加える。
    pub checked: Vec<RecoveredCircuitForm>,
}

/// 確定した境界で検査した回路フォーム。
#[derive(Debug)]
pub struct RecoveredCircuitForm {
    /// 元の構文木でフォームを指す添字。
    pub form: usize,
    /// フォームを囲む名前空間。トップレベルでは `None`。
    pub namespace: Option<usize>,
    /// 回路文法による判定。
    pub outcome: RecoveredFormOutcome,
}

/// 回路フォームを検査した結果。
#[derive(Debug)]
pub enum RecoveredFormOutcome {
    /// 元ソースのフォームが文法に従う。名前空間の直下は個別に検査する。
    Valid(Head),
    /// フォームを確定索引から外し、次の兄弟へ進んだ。
    Rejected {
        /// フォーム内で最初に検出した違反の種別。
        kind: HeaderError,
        /// 元入力の診断範囲。欠落した要素の範囲は長さ 0。
        span: Range<usize>,
        /// 検査対象から外したフォーム全体の元入力の範囲。
        skipped: Range<usize>,
    },
}

spec fn after_node(forms: Seq<Form>, index: int) -> int
    recommends 0 <= index < forms.len(),
{
    match forms[index] { Form::List { end, .. } => end as int, _ => index + 1 }
}

spec fn checked_matches(source: &str, forms: Seq<Form>, item: RecoveredCircuitForm) -> bool {
    &&& 0 <= item.form < forms.len()
    &&& indexed_location(source, forms, item.form as int, item.namespace)
    &&& item.namespace matches Some(parent) ==>
        header_matches(source, forms, parent as int, false, Head::Namespace)
    &&& match item.outcome {
        RecoveredFormOutcome::Valid(head) =>
            header_matches(source, forms, item.form as int, item.namespace.is_some(), head),
        RecoveredFormOutcome::Rejected { kind, span, skipped } =>
            skipped == form_span(forms[item.form as int])
            && header_error_evidence(source, forms, item.form as int, item.namespace.is_some(), kind, span),
    }
}

spec fn next_location(forms: Seq<Form>, item: RecoveredCircuitForm) -> (int, Option<usize>) {
    let index = item.form as int;
    let end = after_node(forms, index);
    if item.namespace is None
        && (item.outcome matches RecoveredFormOutcome::Valid(Head::Namespace))
        && index + 3 < end
    {
        (index + 3, Some(item.form))
    } else if let Some(parent) = item.namespace {
        if end < after_node(forms, parent as int) { (end, Some(parent)) } else { (end, None) }
    } else {
        (end, None)
    }
}

#[verifier::opaque]
spec fn check_trace(
    source: &str, forms: Seq<Form>, checked: Seq<RecoveredCircuitForm>, next: (int, Option<usize>),
) -> bool {
    &&& next == if checked.len() == 0 { (0int, None) } else { next_location(forms, checked.last()) }
    &&& forall|i: int| 0 <= i < checked.len() ==> {
        let item = #[trigger] checked[i];
        &&& checked_matches(source, forms, item)
        &&& (item.form as int, item.namespace) ==
            if i == 0 { (0int, None) } else { next_location(forms, checked[i - 1]) }
    }
    &&& forall|i: int, j: int| 0 <= i < j < checked.len()
        ==> (#[trigger] checked[i]).form < (#[trigger] checked[j]).form
    &&& forall|i: int| 0 <= i < checked.len() ==> (#[trigger] checked[i]).form < next.0
}

proof fn record_check(
    source: &str, forms: Seq<Form>, checked: Seq<RecoveredCircuitForm>, item: RecoveredCircuitForm,
    next: (int, Option<usize>),
)
    requires
        check_trace(source, forms, checked, (item.form as int, item.namespace)),
        checked_matches(source, forms, item),
        next_location(forms, item) == next,
        item.form < next.0,
    ensures check_trace(source, forms, checked.push(item), next),
{
    reveal(check_trace);
}

/// 回復結果の構文木、検査した境界と所属、各診断の根拠を表す。
pub closed spec fn circuit_recovery_matches(source: &str, result: CircuitRecovery) -> bool {
    &&& (result is Complete <==> circuit_source_matches(source))
    &&& match result {
        CircuitRecovery::Complete(index) => circuit_index_matches(source, index.forms@, index.entries@)
            && complete_list_indices(index.forms@) && nested_list_indices(index.forms@)
            && list_source_delimiters(source, index.forms@, false)
            && form_spans_valid(source, index.forms@, source.spec_bytes().len() as int),
        CircuitRecovery::Inspected { forms, checked } => well_formed_sexpr(source)
            && sexpr_form_model(source) == Some(forms@)
            && complete_list_indices(forms@) && nested_list_indices(forms@)
            && list_source_delimiters(source, forms@, false)
            && form_spans_valid(source, forms@, source.spec_bytes().len() as int)
            && check_trace(source, forms@, checked@, (forms@.len() as int, None)),
        CircuitRecovery::WithSyntaxRepairs { recovered, original } => !well_formed_sexpr(source)
            && complete_list_indices(recovered.forms@)
            && nested_list_indices(recovered.forms@)
            && list_source_delimiters(source, recovered.forms@, true)
            && form_spans_valid(source, recovered.forms@, source.spec_bytes().len() as int)
            && inserted_closes_match(source, recovered.forms@, recovered.repairs@)
            && repair_input_spans_valid(source, recovered.repairs@, source.spec_bytes().len() as int)
            && original_list_ranges(source, recovered.original_lists@, recovered.repairs@, source.spec_bytes().len() as int)
            && original@.len() == recovered.original_lists@.len()
            && original_circuit_lists(source, recovered.original_lists@, original@),
    }
}

/// 回路フォームを検査し、回路文法に違反したフォームの後も検査を続ける。
///
/// 妥当なソースでは厳格索引を返す。S 式として読めるソースでは、壊れたフォームの後にある兄弟も検査する。
/// 名前空間のヘッダーが正しければ、その直下も同じ順序で検査する。
/// 字句や S 式の修復が必要な場合は、暫定構文木と修復記録を返し、元の括弧で閉じた区間を個別に検査する。
pub fn recover_circuit_forms(source: &str) -> (result: CircuitRecovery)
    ensures
        circuit_recovery_matches(source, result),
        result is Complete <==> circuit_source_matches(source),
{
    let forms = match parse(source) {
        Ok(forms) => forms,
        Err(_) => {
            let recovered = parse_recovering(source);
            let original = inspect_original_circuit_lists(source, &recovered);
            return CircuitRecovery::WithSyntaxRepairs { recovered, original };
        },
    };
    match index_parsed_headers(source, forms.as_slice()) {
        Ok(entries) => CircuitRecovery::Complete(CircuitForms { forms, entries }),
        Err(_) => {
            let checked = inspect_circuit_forms(source, forms.as_slice());
            CircuitRecovery::Inspected { forms, checked }
        },
    }
}

spec fn one_original_circuit_list(source: &str, span: Range<usize>, list: OriginalCircuitList) -> bool {
    &&& list.span == span
    &&& exists|fragment: &str| {
        &&& fragment.spec_bytes() == source.spec_bytes()[span.start as int..span.end as int]
        &&& sexpr_form_model(fragment) == Some(list.forms@)
        &&& list.forms@.len() > 0
        &&& list.forms@[0] is List && list.forms@[0]->List_end == list.forms@.len()
        &&& form_span(list.forms@[0]) == (0usize..fragment.spec_bytes().len() as usize)
        &&& form_spans_valid(fragment, list.forms@, fragment.spec_bytes().len() as int)
        &&& #[trigger] check_trace(fragment, list.forms@, list.checked@, (list.forms@.len() as int, None))
    }
}

spec fn original_circuit_lists(
    source: &str, spans: Seq<Range<usize>>, lists: Seq<Option<OriginalCircuitList>>,
) -> bool {
    &&& lists.len() <= spans.len()
    &&& forall|i: int| 0 <= i < lists.len() ==> match #[trigger] lists[i] {
        Some(list) => one_original_circuit_list(source, spans[i], list),
        None => true,
    }
}

fn inspect_original_circuit_lists(source: &str, recovered: &Recovered) -> (lists: Vec<Option<OriginalCircuitList>>)
    requires original_list_ranges(source, recovered.original_lists@, recovered.repairs@, source.spec_bytes().len() as int),
    ensures
        lists@.len() == recovered.original_lists@.len(),
        original_circuit_lists(source, recovered.original_lists@, lists@),
{
    let mut lists: Vec<Option<OriginalCircuitList>> = Vec::new();
    let mut at = 0;
    while at < recovered.original_lists.len()
        invariant
            at == lists@.len() <= recovered.original_lists@.len(),
            original_circuit_lists(source, recovered.original_lists@, lists@),
            original_list_ranges(source, recovered.original_lists@, recovered.repairs@, source.spec_bytes().len() as int),
        decreases recovered.original_lists@.len() - at,
    {
        let span = &recovered.original_lists[at];
        proof {
            reveal(original_list_ranges);
            encode_utf8_valid_utf8(source@);
        }
        let list = inspect_original_circuit_list(source, span);
        let ghost previous = lists@;
        let ghost picked = list;
        lists.push(list);
        assert forall|i: int| 0 <= i < lists@.len() implies match #[trigger] lists@[i] {
            Some(list) => one_original_circuit_list(source, recovered.original_lists@[i], list),
            None => true,
        } by {
            if i < at { assert(lists@[i] == previous[i]); } else { assert(lists@[i] == picked); }
        };
        at += 1;
    }
    lists
}

fn inspect_original_circuit_list(source: &str, span: &Range<usize>) -> (list: Option<OriginalCircuitList>)
    requires
        valid_utf8(source.spec_bytes()),
        span.start < span.end <= source.spec_bytes().len(),
        is_char_boundary(source.spec_bytes(), span.start as int),
        is_char_boundary(source.spec_bytes(), span.end as int),
    ensures list matches Some(list) ==> one_original_circuit_list(source, *span, list),
{
    let fragment = source_span(source, span.start, span.end);
    let forms = parse(fragment).ok()?;
    let Some(Form::List { span: inner, end: inner_end }) = forms.first() else { return None; };
    if *inner_end != forms.len() || inner.start != 0 || inner.end != fragment.as_bytes().len() {
        return None;
    }
    assert(forms@.len() > 0 && forms@[0] is List);
    assert(forms@[0]->List_end == forms@.len());
    assert(form_span(forms@[0]) == (0usize..fragment.spec_bytes().len() as usize));
    let checked = inspect_circuit_forms(fragment, forms.as_slice());
    let list = OriginalCircuitList { span: span.start..span.end, forms, checked };
    assert(one_original_circuit_list(source, *span, list)) by {
        assert(check_trace(fragment, list.forms@, list.checked@, (list.forms@.len() as int, None)));
    };
    Some(list)
}

fn inspect_circuit_forms(source: &str, forms: &[Form]) -> (checked: Vec<RecoveredCircuitForm>)
    requires
        complete_list_indices(forms@), nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures check_trace(source, forms@, checked@, (forms@.len() as int, None)),
{
    let mut checked = Vec::new();
    let mut index = 0;
    let mut namespace: Option<usize> = None;
    let mut limit = forms.len();
    proof {
        reveal(direct_form_in_range);
        assert(forms@.len() > 0 ==> direct_form_in_range(forms@, 0, forms@.len() as int, 0));
    }
    assert(check_trace(source, forms@, checked@, (0int, None))) by { reveal(check_trace); }
    while index < forms.len()
        invariant
            complete_list_indices(forms@), nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            index <= limit <= forms@.len(),
            match namespace {
                None => limit == forms@.len(),
                Some(parent) => parent + 3 <= index < limit
                    && header_matches(source, forms@, parent as int, false, Head::Namespace)
                    && limit == after_node(forms@, parent as int),
            },
            index < forms@.len() ==> indexed_location(source, forms@, index as int, namespace),
            check_trace(source, forms@, checked@, (index as int, namespace)),
        decreases forms@.len() - index,
    {
        let current = &forms[index];
        let end = match current { Form::List { end, .. } => *end, _ => index + 1 };
        proof {
            node_end_is_following_direct_form(forms@, index as int, end as int);
            reveal(following_direct_form);
            if let Some(parent) = namespace {
                assert(form_region_ends_at(forms@, parent + 3, limit as int));
            } else {
                assert(form_region_ends_at(forms@, 0, limit as int));
            }
        }
        let outcome = match read_header(source, forms, index, namespace.is_some()) {
            Ok((head, _)) => RecoveredFormOutcome::Valid(head),
            Err((kind, span)) => RecoveredFormOutcome::Rejected {
                kind, span, skipped: form_span_exec(current),
            },
        };
        let item = RecoveredCircuitForm { form: index, namespace, outcome };
        let (next, owner, next_limit) = if namespace.is_none() && matches!(item.outcome, RecoveredFormOutcome::Valid(Head::Namespace)) {
            if index + 3 < end {
                proof {
                    reveal(direct_form_in_range);
                    reveal(head_word_matches);
                    assert(direct_form_in_range(forms@, 0, forms@.len() as int, index as int));
                    assert(form_has_head(source, forms@, index as int, false, Head::Namespace));
                    assert(indexed_location(source, forms@, index + 3, Some(index)));
                }
                (index + 3, Some(index), end)
            } else {
                (end, None, forms.len())
            }
        } else if let Some(_parent) = namespace {
            if end < limit {
                assert(direct_form_in_range(forms@, _parent + 3, limit as int, end as int));
                assert(indexed_location(source, forms@, end as int, Some(_parent)));
                (end, namespace, limit)
            } else {
                proof {
                    assert(end == limit);
                    node_end_is_following_direct_form(forms@, _parent as int, end as int);
                    reveal(following_direct_form);
                    assert(direct_form_in_range(forms@, 0, forms@.len() as int, _parent as int));
                    assert(end < forms@.len() ==> direct_form_in_range(forms@, 0, forms@.len() as int, end as int));
                }
                (end, None, forms.len())
            }
        } else {
            (end, None, forms.len())
        };
        proof {
            record_check(source, forms@, checked@, item, (next as int, owner));
        }
        checked.push(item);
        index = next;
        namespace = owner;
        limit = next_limit;
    }
    checked
}

} // verus!
