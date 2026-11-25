//! 確定した回路フォームの境界から、局所の診断を記録して兄弟の検査を続ける。

use super::*;
use crate::{Recovered, parse_recovering};
#[cfg(verus_only)]
use crate::{inserted_closes_match, original_list_ranges, original_list_roots, repair_input_spans_valid};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::valid_utf8;

mod names;
#[cfg(verus_only)]
pub use names::recovered_names_agree;
pub use names::{RecoveredName, RecoveredNamePosition, RecoveredNames, recover_circuit_names};

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
    /// 主診断と関連箇所の位置は区間内のバイト位置。ファイル内の位置は [`Self::source_diagnostics`] で参照する。
    pub checked: Vec<RecoveredCircuitForm>,
    source_diagnostics: Vec<Option<CircuitFormError>>,
}

impl OriginalCircuitList {
    /// 元入力全体に対するリストのバイト範囲を表す。
    pub closed spec fn span_model(&self) -> Range<usize> {
        self.span
    }

    /// 各フォームの診断を、解析時のファイル全体に対する UTF-8 バイト範囲で返す。
    ///
    /// 結果は解析時の `checked` と同じ順に並ぶ。回路文法に従う項目や元入力の範囲を確認できない項目は `None`。
    /// 関連箇所も同じファイルの位置を使い、要素の欠落位置は長さ 0 の範囲で返す。
    pub fn source_diagnostics(&self) -> (diagnostics: &[Option<CircuitFormError>])
        ensures diagnostics@ == self.source_diagnostics_model(),
    {
        self.source_diagnostics.as_slice()
    }

    /// ファイル内の位置で表した診断の列を返す。
    pub closed spec fn source_diagnostics_model(&self) -> Seq<Option<CircuitFormError>> {
        self.source_diagnostics@
    }
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

#[verifier::opaque]
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
            && header_error_evidence(source, forms, item.form as int, item.namespace.is_some(), kind, span)
            && (forall|head: Head| !#[trigger] header_matches(source, forms, item.form as int, item.namespace.is_some(), head)),
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

proof fn checked_forms_agree(
    source: &str, forms: Seq<Form>, left: RecoveredCircuitForm, right: RecoveredCircuitForm,
)
    requires
        checked_matches(source, forms, left),
        checked_matches(source, forms, right),
        left.form == right.form,
        left.namespace == right.namespace,
    ensures left == right,
{
    reveal(checked_matches);
    match (left.outcome, right.outcome) {
        (RecoveredFormOutcome::Valid(a), RecoveredFormOutcome::Valid(b)) =>
            same_head_word(source, forms[left.form + 1], a, b),
        (
            RecoveredFormOutcome::Rejected { kind: a, span: a_span, .. },
            RecoveredFormOutcome::Rejected { kind: b, span: b_span, .. },
        ) => header_errors_agree(source, forms, left.form as int, left.namespace.is_some(), (a, a_span), (b, b_span)),
        _ => {},
    }
}

proof fn check_traces_agree_through(
    source: &str, forms: Seq<Form>, left: Seq<RecoveredCircuitForm>, right: Seq<RecoveredCircuitForm>, count: int,
)
    requires
        check_trace(source, forms, left, (forms.len() as int, None)),
        check_trace(source, forms, right, (forms.len() as int, None)),
        0 <= count <= left.len(),
        count <= right.len(),
    ensures forall|i: int| 0 <= i < count ==> (#[trigger] left[i]) == (#[trigger] right[i]),
    decreases count,
{
    if count > 0 {
        let i = count - 1;
        check_traces_agree_through(source, forms, left, right, i);
        reveal(check_trace);
        // 先頭は同じ位置から開始し、それ以降は一つ前の判定が次の位置と所属を決める。
        if i > 0 {
            assert(left[i - 1] == right[i - 1]);
        }
        checked_forms_agree(source, forms, left[i], right[i]);
    }
}

proof fn complete_check_traces_agree(
    source: &str, forms: Seq<Form>, left: Seq<RecoveredCircuitForm>, right: Seq<RecoveredCircuitForm>,
)
    requires
        check_trace(source, forms, left, (forms.len() as int, None)),
        check_trace(source, forms, right, (forms.len() as int, None)),
    ensures left == right,
{
    let (short, long) = if left.len() <= right.len() { (left, right) } else { (right, left) };
    let stop = short.len() as int;
    check_traces_agree_through(source, forms, short, long, stop);
    if stop < long.len() {
        reveal(check_trace);
        if stop > 0 {
            assert(short.last() == long[stop - 1]);
        }
        // 短い列を読み終えた位置は構文木の末尾なので、続くフォームはない。
        assert(long[stop].form == forms.len());
        assert(long[stop].form < forms.len());
    }
    assert(short =~= long);
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
            && original_list_roots(recovered.forms@, recovered.original_lists@)
            && original@.len() == recovered.original_lists@.len()
            && original_circuit_lists(source, recovered.original_lists@, original@),
    }
}

/// 妥当なソースでは、回復解析と厳格解析の構文木と索引項目が一致する。
///
/// 回復結果と厳格索引は、どちらも同じソースに対する契約を満たす必要がある。
pub proof fn complete_recovery_agrees_with_index(source: &str, recovered: &CircuitRecovery, strict: &CircuitForms)
    requires
        circuit_source_matches(source),
        circuit_recovery_matches(source, *recovered),
        circuit_index_matches(source, strict.forms@, strict.entries@),
    ensures recovered matches CircuitRecovery::Complete(index)
        && index.forms@ == strict.forms@ && index.entries@ == strict.entries@,
{
    if let CircuitRecovery::Complete(index) = recovered {
        circuit_indexes_agree(source, index, strict);
    }
}

/// S 式として妥当な同じソースの回復結果は、構文木と検査結果が一致する。
///
/// 回路文法に適合すれば厳格索引が一致する。違反があれば各フォームの検査順と所属、
/// 診断の種別・主範囲・関連範囲、および読み飛ばした範囲が一致する。
pub proof fn circuit_recovery_results_agree_on_sexpr(source: &str, left: &CircuitRecovery, right: &CircuitRecovery)
    requires
        well_formed_sexpr(source),
        circuit_recovery_matches(source, *left),
        circuit_recovery_matches(source, *right),
    ensures match (left, right) {
        (CircuitRecovery::Complete(a), CircuitRecovery::Complete(b)) =>
            a.forms@ == b.forms@ && a.entries@ == b.entries@,
        (CircuitRecovery::Inspected { forms: a, checked: a_checked },
         CircuitRecovery::Inspected { forms: b, checked: b_checked }) =>
            a@ == b@ && a_checked@ == b_checked@,
        _ => false,
    },
{
    match (left, right) {
        (CircuitRecovery::Complete(a), CircuitRecovery::Complete(b)) => circuit_indexes_agree(source, a, b),
        (CircuitRecovery::Inspected { forms, checked: a }, CircuitRecovery::Inspected { checked: b, .. }) =>
            complete_check_traces_agree(source, forms@, a@, b@),
        _ => {},
    }
}

proof fn check_trace_transfers_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, checked: Seq<RecoveredCircuitForm>, next: (int, Option<usize>),
)
    requires left.spec_bytes() == right.spec_bytes(), check_trace(left, forms, checked, next),
    ensures check_trace(right, forms, checked, next),
{
    reveal(check_trace);
    assert forall|i: int| 0 <= i < checked.len() implies checked_matches(right, forms, #[trigger] checked[i]) by {
        reveal(checked_matches);
        let item = checked[i];
        let index = item.form as int;
        let in_namespace = item.namespace.is_some();
        assert(checked_matches(left, forms, item));
        super::indexed_location_agrees_on_bytes(left, right, forms, index, item.namespace);
        if let Some(parent) = item.namespace {
            crate::circuit::circuit_header_agrees_on_bytes(left, right, forms, parent as int, false, Head::Namespace,
                (HeaderError::ExpectedList, 0..0));
        }
        match item.outcome {
            RecoveredFormOutcome::Valid(head) => {
                crate::circuit::circuit_header_agrees_on_bytes(left, right, forms, index, in_namespace, head,
                    (HeaderError::ExpectedList, 0..0));
            },
            RecoveredFormOutcome::Rejected { kind, span, .. } => {
                assert forall|head: Head| !#[trigger] header_matches(right, forms, index, in_namespace, head) by {
                    crate::circuit::circuit_header_agrees_on_bytes(left, right, forms, index, in_namespace, head, (kind, span));
                };
                crate::circuit::circuit_header_agrees_on_bytes(left, right, forms, index, in_namespace, Head::Namespace,
                    (kind, span));
            },
        }
    };
}

/// S 式として読める本文の回復結果は、同じ UTF-8 バイト列を持つ入力の契約も満たす。
pub proof fn circuit_recovery_transfers_on_sexpr_bytes(left: &str, right: &str, recovery: &CircuitRecovery)
    requires
        left.spec_bytes() == right.spec_bytes(),
        well_formed_sexpr(left),
        circuit_recovery_matches(left, *recovery),
    ensures circuit_recovery_matches(right, *recovery),
{
    crate::sexpr_models_agree_on_bytes(left, right);
    super::circuit_acceptance_agrees_on_bytes(left, right);
    reveal(form_spans_valid);
    reveal(list_source_delimiters);
    match recovery {
        CircuitRecovery::Complete(index) => super::circuit_index_agrees_on_bytes(left, right, index.forms@, index.entries@),
        CircuitRecovery::Inspected { forms, checked } =>
            check_trace_transfers_on_bytes(left, right, forms@, checked@, (forms@.len() as int, None)),
        _ => {},
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
    &&& list.source_diagnostics@.len() == list.checked@.len()
    &&& original_diagnostics_match(source, span, list.checked@, list.source_diagnostics@)
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

spec fn can_rebase(source: &str, outer: Range<usize>, start: usize, end: usize) -> bool {
    &&& outer.start <= outer.end <= source.spec_bytes().len()
    &&& start <= end <= outer.end - outer.start
    &&& is_char_boundary(source.spec_bytes(), outer.start + start)
    &&& is_char_boundary(source.spec_bytes(), outer.start + end)
}

fn rebase_span(source: &str, outer: &Range<usize>, start: usize, end: usize)
    -> (span: Option<Range<usize>>)
    ensures
        span.is_some() <==> can_rebase(source, *outer, start, end),
        span matches Some(span) ==> span.start == outer.start + start && span.end == outer.start + end,
{
    let bytes = source.as_bytes();
    if outer.start > outer.end || outer.end > bytes.len()
        || start > end || end > outer.end - outer.start {
        return None;
    }
    let first = outer.start + start;
    let last = outer.start + end;
    if source.is_char_boundary(first) && source.is_char_boundary(last) {
        Some(first..last)
    } else {
        None
    }
}

spec fn shifted_kind(kind: HeaderError, origin: usize) -> HeaderError {
    match kind {
        HeaderError::MixedTestItems { first_head: (start, end) } => HeaderError::MixedTestItems {
            first_head: ((origin + start) as usize, (origin + end) as usize),
        },
        _ => kind,
    }
}

spec fn related_range_valid(source: &str, outer: Range<usize>, kind: HeaderError) -> bool {
    match kind {
        HeaderError::MixedTestItems { first_head: (start, end) } => can_rebase(source, outer, start, end),
        _ => true,
    }
}

spec fn original_diagnostic_matches(
    source: &str, outer: Range<usize>, outcome: RecoveredFormOutcome, diagnostic: Option<CircuitFormError>,
) -> bool {
    match outcome {
        RecoveredFormOutcome::Valid(_) => diagnostic.is_none(),
        RecoveredFormOutcome::Rejected { kind, span, .. } =>
            if can_rebase(source, outer, span.start, span.end) && related_range_valid(source, outer, kind) {
                diagnostic == Some(CircuitFormError::Header {
                    kind: shifted_kind(kind, outer.start),
                    span: (outer.start + span.start) as usize..(outer.start + span.end) as usize,
                })
            } else {
                diagnostic.is_none()
            },
    }
}

fn source_diagnostic(source: &str, outer: &Range<usize>, outcome: &RecoveredFormOutcome)
    -> (diagnostic: Option<CircuitFormError>)
    ensures original_diagnostic_matches(source, *outer, *outcome, diagnostic),
{
    let RecoveredFormOutcome::Rejected { kind: local_kind, span: local_span, .. } = outcome else { return None; };
    let primary = rebase_span(source, outer, local_span.start, local_span.end)?;
    let kind = match *local_kind {
        HeaderError::MixedTestItems { first_head: (start, end) } => {
            let related = rebase_span(source, outer, start, end)?;
            HeaderError::MixedTestItems { first_head: (related.start, related.end) }
        },
        HeaderError::ExpectedList | HeaderError::ExpectedHead | HeaderError::UnknownHead
        | HeaderError::MisplacedHead(_) | HeaderError::ExpectedNamespacePath | HeaderError::ExpectedNor
        | HeaderError::ExpectedAbsolutePath | HeaderError::ExpectedName | HeaderError::ExpectedReference
        | HeaderError::ExpectedNatural | HeaderError::ExpectedPort | HeaderError::ExpectedType
        | HeaderError::ExpectedBodyItem | HeaderError::ExpectedTarget | HeaderError::ExpectedExpression
        | HeaderError::ExpectedTestItem | HeaderError::ExpectedTestValue
        | HeaderError::ExpectedTestValueOrAny | HeaderError::ExpectedClause(_)
        | HeaderError::UnexpectedArgument => *local_kind,
    };
    Some(CircuitFormError::Header { kind, span: primary })
}

spec fn original_diagnostics_match(
    source: &str, outer: Range<usize>, checked: Seq<RecoveredCircuitForm>,
    diagnostics: Seq<Option<CircuitFormError>>,
) -> bool {
    &&& diagnostics.len() <= checked.len()
    &&& forall|i: int| 0 <= i < diagnostics.len() ==> original_diagnostic_matches(
        source, outer, checked[i].outcome, #[trigger] diagnostics[i])
}

fn source_diagnostics(
    source: &str, outer: &Range<usize>, checked: &[RecoveredCircuitForm],
) -> (diagnostics: Vec<Option<CircuitFormError>>)
    ensures
        diagnostics@.len() == checked@.len(),
        original_diagnostics_match(source, *outer, checked@, diagnostics@),
{
    let mut diagnostics: Vec<Option<CircuitFormError>> = Vec::new();
    let mut at = 0;
    while at < checked.len()
        invariant
            at == diagnostics@.len() <= checked@.len(),
            original_diagnostics_match(source, *outer, checked@, diagnostics@),
        decreases checked@.len() - at,
    {
        let diagnostic = source_diagnostic(source, outer, &checked[at].outcome);
        diagnostics.push(diagnostic);
        at += 1;
    }
    diagnostics
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
    let source_diagnostics = source_diagnostics(source, span, checked.as_slice());
    let list = OriginalCircuitList { span: span.start..span.end, forms, checked, source_diagnostics };
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
            reveal(checked_matches);
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

#[cfg(test)]
mod tests {
    use super::{HeaderError, RecoveredFormOutcome, rebase_span, source_diagnostic};

    #[test]
    fn projects_only_ordered_ranges_at_utf8_boundaries() {
        let source = "|é語|";
        let outer = 1..6;
        assert_eq!(rebase_span(source, &outer, 0, 5), Some(1..6));
        assert_eq!(rebase_span(source, &outer, 2, 2), Some(3..3));
        assert_eq!(rebase_span(source, &outer, 5, 5), Some(6..6));
        for (first, last) in [(0, 1), (2, 4), (2, 1), (2, 6), (2, usize::MAX)] {
            assert_eq!(rebase_span(source, &outer, first, last), None);
        }
        assert_eq!(rebase_span(source, &(usize::MAX..usize::MAX), 0, 0), None);
    }

    #[test]
    fn requires_the_related_range_to_be_valid_too() {
        let outcome = RecoveredFormOutcome::Rejected {
            kind: HeaderError::MixedTestItems { first_head: (0, 1) },
            span: 2..5,
            skipped: 0..5,
        };
        assert!(source_diagnostic("|é語|", &(1..6), &outcome).is_none());
    }
}
