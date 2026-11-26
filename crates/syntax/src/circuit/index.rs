//! トップレベルのフォームと名前空間の直下を入力順に索引に載せる。

#[cfg(verus_only)]
use super::build::{build_entry_matches, keep_build_entry};
use super::*;
mod recovery;
#[cfg(verus_only)]
pub use recovery::recovered_names_agree;
#[cfg(verus_only)]
use crate::{sexpr_form_model, strict_syntax_rejection, strict_token_errors_agree,
    structural_error_location, syntax_error_evidence, well_formed_sexpr};
#[cfg(verus_only)]
pub use recovery::{circuit_recovery_matches, circuit_recovery_repair_evidence, circuit_recovery_results_agree_on_sexpr, circuit_recovery_transfers_on_sexpr_bytes,
    complete_recovery_agrees_with_index, one_original_circuit_list, original_diagnostic_relocated, original_list_diagnostics_relocate, original_diagnostic_within, original_list_is_inspectable, original_list_observations_agree, repaired_circuit_recoveries_agree};
pub use recovery::{
    CachedCircuitRecovery, CircuitRecovery, CircuitRecoveryReuseWindow, OriginalCircuitList, RecoveredCircuitForm, RecoveredFormOutcome,
    relocate_circuit_span,
    RecoveredName, RecoveredNamePosition, RecoveredNames, recover_circuit_build_index, recover_circuit_forms, recover_circuit_names,
    recover_circuit_names_with_cache,
};

verus! {

#[verifier::opaque]
pub(super) open spec fn build_rows_match(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, ranges: Seq<BuildEntryRanges>,
    definitions: Seq<BuildDefinition>, references: Seq<ExpressionReference>, signals: Seq<usize>,
) -> bool {
    &&& ranges.len() == entries.len()
    &&& definitions.len() == if ranges.len() == 0 { 0 } else { ranges.last().definitions.end }
    &&& references.len() == if ranges.len() == 0 { 0 } else { ranges.last().references.end }
    &&& signals.len() == if ranges.len() == 0 { 0 } else { ranges.last().signals.end }
    &&& forall|i: int| 0 <= i < entries.len() ==> {
        let range = #[trigger] ranges[i];
        &&& range.definitions.start == if i == 0 { 0 } else { ranges[i - 1].definitions.end }
        &&& range.references.start == if i == 0 { 0 } else { ranges[i - 1].references.end }
        &&& range.signals.start == if i == 0 { 0 } else { ranges[i - 1].signals.end }
        &&& build_entry_matches(source, forms, entries[i].form as int, entries[i].head, range, definitions, references, signals)
    }
}

/// 新しい索引項目の区間を追加し、既存の項目が指す区間との連続性を保つ。
proof fn record_build_entry(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, prior: BuildRows, rows: BuildRows, entry: Entry,
    range: BuildEntryRanges,
)
    requires
        build_rows_match(source, forms, entries, prior.entry_ranges@, prior.definitions@, prior.references@, prior.signals@),
        rows.entry_ranges@ == prior.entry_ranges@.push(range),
        prior.definitions@.len() <= rows.definitions@.len(),
        rows.definitions@.take(prior.definitions@.len() as int) == prior.definitions@,
        prior.references@.len() <= rows.references@.len(),
        rows.references@.take(prior.references@.len() as int) == prior.references@,
        prior.signals@.len() <= rows.signals@.len(),
        rows.signals@.take(prior.signals@.len() as int) == prior.signals@,
        range.signals.start == prior.signals@.len(), range.signals.end == rows.signals@.len(),
        range.definitions.start == prior.definitions@.len(), range.definitions.end == rows.definitions@.len(),
        range.references.start == prior.references@.len(), range.references.end == rows.references@.len(),
        build_entry_matches(source, forms, entry.form as int, entry.head, range, rows.definitions@, rows.references@, rows.signals@),
    ensures build_rows_match(source, forms, entries.push(entry), rows.entry_ranges@, rows.definitions@, rows.references@, rows.signals@),
{
    reveal(build_rows_match);
    let more = entries.push(entry);
    assert forall|i: int| 0 <= i < more.len() implies {
        let range = #[trigger] rows.entry_ranges@[i];
        &&& range.definitions.start == if i == 0 { 0 } else { rows.entry_ranges@[i - 1].definitions.end }
        &&& range.references.start == if i == 0 { 0 } else { rows.entry_ranges@[i - 1].references.end }
        &&& range.signals.start == if i == 0 { 0 } else { rows.entry_ranges@[i - 1].signals.end }
        &&& build_entry_matches(source, forms, more[i].form as int, more[i].head, range, rows.definitions@, rows.references@, rows.signals@)
    } by {
        if i < entries.len() {
            let ranges = prior.entry_ranges@[i];
            keep_build_entry(source, forms, entries[i].form as int, entries[i].head, ranges, prior, rows);
        }
    };
}

/// 索引を付ける位置と、直接の親名前空間の添字を定める。
pub open spec fn indexed_location(source: &str, forms: Seq<Form>, index: int, namespace: Option<usize>) -> bool {
    match namespace {
        None => direct_form_in_range(forms, 0, forms.len() as int, index),
        Some(parent) => {
            &&& direct_form_in_range(forms, 0, forms.len() as int, parent as int)
            &&& form_has_head(source, forms, parent as int, false, Head::Namespace)
            &&& direct_form_in_range(forms, parent + 3, forms[parent as int]->List_end as int, index)
        },
    }
}

spec fn forms_before(source: &str, forms: Seq<Form>, cursor: int) -> bool {
    forall|index: int, namespace: Option<usize>| #[trigger] indexed_location(source, forms, index, namespace)
        && index < cursor ==> exists|head: Head| #[trigger] header_matches(source, forms, index, namespace.is_some(), head)
}

/// 元入力に対応する S 式の列が回路文法に従うことを表す。
pub closed spec fn circuit_source_matches(source: &str) -> bool {
    well_formed_sexpr(source) && (exists|forms: Seq<Form>| sexpr_form_model(source) == Some(forms)
        && #[trigger] forms_before(source, forms, forms.len() as int))
}

/// 回路文法に最初に違反するフォームと、その直接の親名前空間を表す。
///
/// 位置は平坦な S 式構文木の添字で表す。親名前空間がない場合は `None` になる。
pub closed spec fn circuit_header_error_at(
    source: &str, error: CircuitFormError, index: int, namespace: Option<usize>,
) -> bool {
    &&& well_formed_sexpr(source)
    &&& sexpr_form_model(source) matches Some(forms)
    &&& error matches CircuitFormError::Header { kind, span }
    &&& indexed_location(source, forms, index, namespace)
    &&& forms_before(source, forms, index)
    &&& (forall|head: Head| !#[trigger] header_matches(source, forms, index, namespace.is_some(), head))
    &&& header_error_evidence(source, forms, index, namespace.is_some(), kind, span)
}

/// 字句、S 式、回路文法のいずれかの診断に根拠を与える。
///
/// 回路文法の診断では、入力全体が S 式の文法に従い、診断位置より前に検査するすべてのフォームが回路文法に従う。
pub closed spec fn circuit_source_error(source: &str, error: CircuitFormError) -> bool {
    match error {
        CircuitFormError::Syntax(error) => !well_formed_sexpr(source) && syntax_error_evidence(source, error)
            && strict_syntax_rejection(source, error),
        CircuitFormError::Header { .. } => exists|index: int, namespace: Option<usize>|
            #[trigger] circuit_header_error_at(source, error, index, namespace),
    }
}

/// 回路ソースが診断の根拠を持つなら、回路文法には適合しない。
proof fn circuit_diagnostic_excludes_match(source: &str, error: CircuitFormError)
    requires circuit_source_error(source, error),
    ensures !circuit_source_matches(source),
{
    if circuit_source_matches(source) && error is Header {
        let (index, owner) = choose|index: int, owner: Option<usize>|
            #[trigger] circuit_header_error_at(source, error, index, owner);
        let forms = sexpr_form_model(source)->Some_0;
        reveal(direct_form_in_range);
        assert(index < forms.len());
        assert(exists|head: Head| #[trigger] header_matches(source, forms, index, owner.is_some(), head));
    }
}

pub(super) proof fn reject_circuit_syntax(source: &str, error: Error)
    requires !well_formed_sexpr(source), syntax_error_evidence(source, error), strict_syntax_rejection(source, error),
    ensures !circuit_source_matches(source), circuit_source_error(source, CircuitFormError::Syntax(error)),
{
}

/// 字句または S 式に違反があるとき、厳格な回路索引のエラー値が一致することを示す。
pub proof fn circuit_token_errors_agree(source: &str, left: CircuitFormError, right: CircuitFormError)
    requires
        circuit_source_error(source, left), circuit_source_error(source, right),
        left is Syntax,
    ensures left == right,
{
    let a = left->Syntax_0;
    let b = right->Syntax_0;
    reveal(syntax_error_evidence);
    assert(right is Syntax);
    assert(structural_error_location(source, a) && structural_error_location(source, b));
    strict_token_errors_agree(source, a, b);
}

/// 同じ入力で回路文法に違反した両索引が、最初に検査を通らないフォームを同じ位置で見つけることを示す。
pub proof fn first_circuit_header_error(
    source: &str, left: CircuitFormError, right: CircuitFormError,
) -> (site: (int, Option<usize>))
    requires circuit_source_error(source, left), circuit_source_error(source, right), left is Header,
    ensures
        circuit_header_error_at(source, left, site.0, site.1),
        circuit_header_error_at(source, right, site.0, site.1),
{
    let (a, a_owner) = choose|index: int, owner: Option<usize>| #[trigger] circuit_header_error_at(source, left, index, owner);
    assert(well_formed_sexpr(source) && right is Header);
    let (b, b_owner) = choose|index: int, owner: Option<usize>| #[trigger] circuit_header_error_at(source, right, index, owner);
    let forms = sexpr_form_model(source)->Some_0;
    if a < b {
        assert(exists|head: Head| #[trigger] header_matches(source, forms, a, a_owner.is_some(), head));
    } else if b < a {
        assert(exists|head: Head| #[trigger] header_matches(source, forms, b, b_owner.is_some(), head));
    }
    assert(a == b);
    if let Some(parent) = a_owner {
        same_namespace_owner(source, forms, a, parent, b_owner);
    } else if let Some(parent) = b_owner {
        same_namespace_owner(source, forms, a, parent, a_owner);
    }
    (a, a_owner)
}

proof fn same_namespace_owner(source: &str, forms: Seq<Form>, index: int, parent: usize, owner: Option<usize>)
    requires
        indexed_location(source, forms, index, Some(parent)),
        indexed_location(source, forms, index, owner),
    ensures owner == Some(parent),
{
    reveal(direct_form_in_range);
    indexed_subtree_location(source, forms, parent as int, forms[parent as int]->List_end as int, index, owner);
}

proof fn head_rejection_excludes_recognition(
    source: &str, forms: Seq<Form>, index: int, in_namespace: bool, error: (HeaderError, Range<usize>),
)
    requires form_head_error_evidence(source, forms, index, in_namespace, error.0, error.1),
    ensures forall|head: Head| !#[trigger] form_has_head(source, forms, index, in_namespace, head),
{
    assert forall|head: Head| !#[trigger] form_has_head(source, forms, index, in_namespace, head) by {
        if form_has_head(source, forms, index, in_namespace, head) {
            if let HeaderError::MisplacedHead(found) = error.0 {
                same_head_word(source, forms[index + 1], found, head);
            } else {
                reveal(head_word_matches);
            }
        }
    };
}

proof fn head_errors_agree(
    source: &str, forms: Seq<Form>, index: int, in_namespace: bool,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        form_head_error_evidence(source, forms, index, in_namespace, left.0, left.1),
        form_head_error_evidence(source, forms, index, in_namespace, right.0, right.1),
    ensures left == right,
{
    reveal(head_word_matches);
    if let (HeaderError::MisplacedHead(a), HeaderError::MisplacedHead(b)) = (left.0, right.0) {
        same_head_word(source, forms[index + 1], a, b);
    }
}

proof fn header_errors_agree(
    source: &str, forms: Seq<Form>, index: int, in_namespace: bool,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        header_error_evidence(source, forms, index, in_namespace, left.0, left.1),
        header_error_evidence(source, forms, index, in_namespace, right.0, right.1),
    ensures left == right,
{
    let a_rejected = form_head_error_evidence(source, forms, index, in_namespace, left.0, left.1);
    let b_rejected = form_head_error_evidence(source, forms, index, in_namespace, right.0, right.1);
    if a_rejected || b_rejected {
        if a_rejected {
            head_rejection_excludes_recognition(source, forms, index, in_namespace, left);
        } else {
            head_rejection_excludes_recognition(source, forms, index, in_namespace, right);
        }
        assert(a_rejected && b_rejected);
        head_errors_agree(source, forms, index, in_namespace, left, right);
    } else {
        let closing = (form_span(forms[index]).end - 1) as usize;
        let stop = forms[index]->List_end as int;
        let a = choose|head: Head| #[trigger] form_has_head(source, forms, index, in_namespace, head)
            && form_span(forms[index]).end > 0
            && header_arguments_error(source, forms, index + 2, stop, closing, head, left.0, left.1);
        let b = choose|head: Head| #[trigger] form_has_head(source, forms, index, in_namespace, head)
            && form_span(forms[index]).end > 0
            && header_arguments_error(source, forms, index + 2, stop, closing, head, right.0, right.1);
        same_head_word(source, forms[index + 1], a, b);
        reveal(header_arguments_error);
        let first = index + 2;
        match a {
            Head::Struct => super::structure::structure_errors_agree(source, forms, first, stop, closing, left, right),
            Head::Test => super::test_diagnostics::test_arguments_errors_agree(source, forms, first, stop, closing, left, right),
            Head::Latch | Head::Memory => {
                if directive_word_at(source, forms, first, stop, HeaderError::ExpectedName) {
                    super::clause_diagnostics::storage_errors_agree(
                        source, forms, first + 1, stop, closing, a, left, right);
                }
            },
            Head::Func | Head::Module | Head::ModulePart =>
                super::body::routine_arguments_errors_agree(source, forms, first, stop, closing, a, left, right),
            Head::Using | Head::Namespace | Head::Export | Head::Use =>
                super::directive_diagnostics::directive_errors_agree(source, forms, first, stop, closing, a, left, right),
        }
    }
}

/// 同じ回路フォームの違反を報告する診断は、種別と範囲を含む値全体が一致する。
///
/// フォームの位置は `first_circuit_header_error` から得られる。
pub proof fn circuit_header_errors_agree(
    source: &str, left: CircuitFormError, right: CircuitFormError, index: int, namespace: Option<usize>,
)
    requires
        circuit_header_error_at(source, left, index, namespace),
        circuit_header_error_at(source, right, index, namespace),
    ensures left == right,
{
    let forms = sexpr_form_model(source)->Some_0;
    header_errors_agree(source, forms, index, namespace.is_some(),
        (left->Header_kind, left->Header_span), (right->Header_kind, right->Header_span));
}

/// 同じ入力について、厳格解析の診断仕様を満たすエラー値は一意に定まる。
///
/// 字句と S 式の違反、およびすべての回路フォームの違反を対象とする。
/// 診断が保持する主範囲と関連範囲も一致する。
pub proof fn circuit_source_errors_agree(source: &str, left: CircuitFormError, right: CircuitFormError)
    requires circuit_source_error(source, left), circuit_source_error(source, right),
    ensures left == right,
{
    match left {
        CircuitFormError::Syntax(_) => circuit_token_errors_agree(source, left, right),
        CircuitFormError::Header { .. } => {
            let (index, namespace) = first_circuit_header_error(source, left, right);
            circuit_header_errors_agree(source, left, right, index, namespace);
        },
    }
}

/// 診断の仕様と実行結果の対応を、索引の表現に依存せず示す。
pub(super) proof fn circuit_result_diagnostics<T>(source: &str, result: Result<T, CircuitFormError>)
    requires
        result.is_ok() <==> circuit_source_matches(source),
        result matches Err(error) ==> circuit_source_error(source, error),
    ensures
        forall|error: CircuitFormError| #[trigger] circuit_source_error(source, error) <==> result == Err(error),
{
    assert forall|error: CircuitFormError| #[trigger] circuit_source_error(source, error)
        implies result == Err(error) by {
        circuit_diagnostic_excludes_match(source, error);
        let reported = result->Err_0;
        circuit_source_errors_agree(source, reported, error);
    };
}

/// 同じフォームの先頭語または指示フォームの引数に違反があるとき、厳格索引の診断値が一致する。
///
/// フォームの位置は `first_circuit_header_error` から得られる。先頭語が有効な場合は
/// `using`、`namespace`、`export`、`use` のいずれかであることを前提とする。
pub proof fn circuit_directive_errors_agree(
    source: &str, left: CircuitFormError, right: CircuitFormError, index: int, namespace: Option<usize>,
)
    requires
        circuit_header_error_at(source, left, index, namespace),
        circuit_header_error_at(source, right, index, namespace),
        forall|head: Head| #[trigger] form_has_head(
            source, sexpr_form_model(source)->Some_0, index, namespace.is_some(), head)
            ==> head is Using || head is Namespace || head is Export || head is Use,
    ensures left == right,
{
    circuit_header_errors_agree(source, left, right, index, namespace);
}

#[verifier::opaque]
spec fn index_prefix(source: &str, forms: Seq<Form>, entries: Seq<Entry>, cursor: int) -> bool {
    &&& forall|k: int| 0 <= k < entries.len() ==> {
        let entry = #[trigger] entries[k];
        &&& entry.form < cursor
        &&& indexed_location(source, forms, entry.form as int, entry.namespace)
        &&& header_matches(source, forms, entry.form as int, entry.namespace.is_some(), entry.head)
    }
    &&& forall|index: int, namespace: Option<usize>| #[trigger] indexed_location(source, forms, index, namespace)
        && index < cursor ==> exists|k: int| 0 <= k < entries.len()
            && (#[trigger] entries[k]).form == index && entries[k].namespace == namespace
    &&& forall|left: int, right: int| 0 <= left < right < entries.len()
        ==> (#[trigger] entries[left]).form < (#[trigger] entries[right]).form
}

/// 索引は対象位置を漏れなく一度ずつ含み、種別と親の添字を入力順に保存する。
pub closed spec fn circuit_index_matches(source: &str, forms: Seq<Form>, entries: Seq<Entry>) -> bool {
    sexpr_form_model(source) == Some(forms) && index_prefix(source, forms, entries, forms.len() as int)
}

/// 厳格な回路索引が保持するリストの範囲を、元の括弧に結び付ける。
pub proof fn circuit_index_delimiters(source: &str, forms: Seq<Form>, entries: Seq<Entry>)
    requires circuit_index_matches(source, forms, entries), source.spec_bytes().len() <= usize::MAX,
    ensures list_source_delimiters(source, forms, false),
{
    crate::sexpr_model_delimiters(source, forms);
}

proof fn indexed_location_agrees_on_bytes(left: &str, right: &str, forms: Seq<Form>, index: int, owner: Option<usize>)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures indexed_location(left, forms, index, owner) == indexed_location(right, forms, index, owner),
{
    if let Some(parent) = owner {
        super::form_heads_agree_on_bytes(left, right, forms, parent as int, false, Head::Namespace);
    }
}

proof fn forms_before_transfers_on_bytes(left: &str, right: &str, forms: Seq<Form>, cursor: int)
    requires left.spec_bytes() == right.spec_bytes(), forms_before(left, forms, cursor),
    ensures forms_before(right, forms, cursor),
{
    assert forall|index: int, namespace: Option<usize>| #[trigger] indexed_location(right, forms, index, namespace)
        && index < cursor implies exists|head: Head| #[trigger] header_matches(right, forms, index, namespace.is_some(), head) by {
        indexed_location_agrees_on_bytes(left, right, forms, index, namespace);
        assert(indexed_location(left, forms, index, namespace));
        let head = choose|head: Head| #[trigger] header_matches(left, forms, index, namespace.is_some(), head);
        super::circuit_header_agrees_on_bytes(left, right, forms, index, namespace.is_some(), head,
            (HeaderError::ExpectedList, 0..0));
        assert(header_matches(right, forms, index, namespace.is_some(), head));
    };
}

proof fn circuit_acceptance_agrees_on_bytes(left: &str, right: &str)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures circuit_source_matches(left) == circuit_source_matches(right),
{
    crate::sexpr_models_agree_on_bytes(left, right);
    if let Some(forms) = sexpr_form_model(left) {
        if forms_before(left, forms, forms.len() as int) {
            forms_before_transfers_on_bytes(left, right, forms, forms.len() as int);
        }
        if forms_before(right, forms, forms.len() as int) {
            forms_before_transfers_on_bytes(right, left, forms, forms.len() as int);
        }
    }
}

pub(super) proof fn circuit_index_agrees_on_bytes(left: &str, right: &str, forms: Seq<Form>, entries: Seq<Entry>)
    requires left.spec_bytes() == right.spec_bytes(), circuit_index_matches(left, forms, entries),
    ensures circuit_index_matches(right, forms, entries),
{
    crate::sexpr_models_agree_on_bytes(left, right);
    reveal(index_prefix);
    assert forall|k: int| 0 <= k < entries.len() implies {
        let entry = #[trigger] entries[k];
        &&& indexed_location(right, forms, entry.form as int, entry.namespace)
        &&& header_matches(right, forms, entry.form as int, entry.namespace.is_some(), entry.head)
    } by {
        let entry = entries[k];
        indexed_location_agrees_on_bytes(left, right, forms, entry.form as int, entry.namespace);
        super::circuit_header_agrees_on_bytes(left, right, forms, entry.form as int, entry.namespace.is_some(), entry.head,
            (HeaderError::ExpectedList, 0..0));
    };
    assert forall|i: int, namespace: Option<usize>| #[trigger] indexed_location(right, forms, i, namespace)
        && i < forms.len() implies exists|k: int| 0 <= k < entries.len()
            && (#[trigger] entries[k]).form == i && entries[k].namespace == namespace by {
        indexed_location_agrees_on_bytes(left, right, forms, i, namespace);
        assert(indexed_location(left, forms, i, namespace));
    };
}

pub(super) proof fn same_indexed_forms(
    source: &str, left: Seq<Form>, left_entries: Seq<Entry>, right: Seq<Form>, right_entries: Seq<Entry>,
)
    requires circuit_index_matches(source, left, left_entries), circuit_index_matches(source, right, right_entries),
    ensures left == right,
{
}

proof fn same_head_word(source: &str, form: Form, left: Head, right: Head)
    requires head_word_matches(source, form, left), head_word_matches(source, form, right),
    ensures left == right,
{
    reveal(head_word_matches);
    let left_word = head_spelling(left);
    let right_word = head_spelling(right);
    encode_utf8_decode_utf8(left_word@);
    encode_utf8_decode_utf8(right_word@);
    assert(left_word@ == right_word@);
}

proof fn index_contains_entry(source: &str, forms: Seq<Form>, entries: Seq<Entry>, entry: Entry)
    requires
        circuit_index_matches(source, forms, entries),
        entry.form < forms.len(),
        indexed_location(source, forms, entry.form as int, entry.namespace),
        header_matches(source, forms, entry.form as int, entry.namespace.is_some(), entry.head),
    ensures exists|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]) == entry,
{
    reveal(index_prefix);
    let i = choose|i: int| 0 <= i < entries.len()
        && (#[trigger] entries[i]).form == entry.form && entries[i].namespace == entry.namespace;
    same_head_word(source, forms[entry.form + 1], entries[i].head, entry.head);
    assert(entries[i] == entry);
}

proof fn indexes_agree_through(
    source: &str, forms: Seq<Form>, left: Seq<Entry>, right: Seq<Entry>, count: int,
)
    requires
        circuit_index_matches(source, forms, left),
        circuit_index_matches(source, forms, right),
        0 <= count <= left.len(),
        count <= right.len(),
    ensures forall|i: int| 0 <= i < count ==> (#[trigger] left[i]) == (#[trigger] right[i]),
    decreases count,
{
    if count > 0 {
        let i = count - 1;
        indexes_agree_through(source, forms, left, right, i);
        reveal(index_prefix);
        let a = left[i];
        let b = right[i];
        index_contains_entry(source, forms, right, a);
        index_contains_entry(source, forms, left, b);
        let j = choose|j: int| 0 <= j < right.len() && (#[trigger] right[j]) == a;
        let k = choose|k: int| 0 <= k < left.len() && (#[trigger] left[k]) == b;
        // 先行項目は一致しているため、現在の要素に対応する項目は先行部分に現れない。
        assert(i <= j) by {
            if j < i {
                assert(left[j] == right[j]);
                assert(left[j].form < a.form);
            }
        };
        assert(i <= k) by {
            if k < i {
                assert(left[k] == right[k]);
                assert(right[k].form < b.form);
            }
        };
        if j > i {
            assert(b.form < a.form);
            assert(k > i);
            assert(a.form < b.form);
        }
        assert(a == b);
    }
}

/// 同じソースから得た回路フォームの索引は、構文木とすべての索引項目で一致する。
///
/// 両方の索引が `circuit_index_matches` を満たすとき、各項目の元の添字、種別、親名前空間が同じ順に並ぶ。
pub proof fn circuit_indexes_agree(
    source: &str, left: &CircuitForms, right: &CircuitForms,
)
    requires
        circuit_index_matches(source, left.forms@, left.entries@),
        circuit_index_matches(source, right.forms@, right.entries@),
    ensures left.forms@ == right.forms@, left.entries@ == right.entries@,
{
    let forms = left.forms@;
    let a = left.entries@;
    let b = right.entries@;
    assert(forms == right.forms@);
    let common = if a.len() < b.len() { a.len() } else { b.len() } as int;
    indexes_agree_through(source, forms, a, b, common);
    reveal(index_prefix);
    if common < a.len() {
        let entry = a[common];
        index_contains_entry(source, forms, b, entry);
        let j = choose|j: int| 0 <= j < b.len() && (#[trigger] b[j]) == entry;
        assert(a[j] == entry);
        assert(a[j].form < entry.form);
    }
    if common < b.len() {
        let entry = b[common];
        index_contains_entry(source, forms, a, entry);
        let j = choose|j: int| 0 <= j < a.len() && (#[trigger] a[j]) == entry;
        assert(b[j] == entry);
        assert(b[j].form < entry.form);
    }
    assert(a =~= b);
}

pub(super) proof fn entry_forms_in_order(source: &str, forms: Seq<Form>, entries: Seq<Entry>)
    requires circuit_index_matches(source, forms, entries),
    ensures forall|i: int, j: int| 0 <= i < j < entries.len()
        ==> (#[trigger] entries[i]).form < (#[trigger] entries[j]).form,
{
    reveal(index_prefix);
}

/// 検証済みの索引項目の位置と種別を、回路文法の認識関係に結び付ける。
pub proof fn indexed_entry_evidence(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, index: int,
)
    requires
        circuit_index_matches(source, forms, entries),
        0 <= index < entries.len(),
    ensures
        indexed_location(source, forms, entries[index].form as int, entries[index].namespace),
        header_matches(source, forms, entries[index].form as int, entries[index].namespace.is_some(), entries[index].head),
        forall|earlier: int| 0 <= earlier < index ==> (#[trigger] entries[earlier]).form < entries[index].form,
        entries[index].namespace matches Some(parent) ==>
            exists|head: Head| #[trigger] header_matches(source, forms, parent as int, false, head),
{
    reveal(index_prefix);
    if let Some(parent) = entries[index].namespace {
        let entry = entries[index];
        assert(indexed_location(source, forms, parent as int, None));
        reveal(direct_form_in_range);
        assert(parent < forms.len());
        indexed_prefix_is_valid(source, forms, entries, forms.len() as int);
    }
}

pub(super) proof fn namespace_entry_for(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, form: int, parent: usize,
)
    requires circuit_index_matches(source, forms, entries),
        indexed_location(source, forms, form, Some(parent)),
    ensures exists|i: int| 0 <= i < entries.len() && (#[trigger] entries[i]).form == parent
        && entries[i].head is Namespace && entries[i].namespace is None,
{
    reveal(index_prefix);
    reveal(direct_form_in_range);
    assert(indexed_location(source, forms, parent as int, None));
    let i = choose|i: int| 0 <= i < entries.len()
        && (#[trigger] entries[i]).form == parent && entries[i].namespace is None;
    indexed_entry_evidence(source, forms, entries, i);
    names::namespace_head_is_unique(source, forms[parent + 1], entries[i].head);
}

/// 基底指定の引数が元ソースの `nor` を指すことを示す。
pub proof fn basis_entry_evidence(source: &str, forms: Seq<Form>, entries: Seq<Entry>, index: int)
    requires circuit_index_matches(source, forms, entries),
        0 <= index < entries.len(), entries[index].head is Using,
    ensures entries[index].namespace is None, ({
        let arg = entries[index].form + 2;
        &&& 0 <= arg < forms.len()
        &&& forms[arg] is Atom
        &&& {
            let span = form_span(forms[arg]);
            source.spec_bytes()[span.start as int..span.end as int] == "nor".spec_bytes()
        }
    }),
{
    indexed_entry_evidence(source, forms, entries, index);
    reveal(header_arguments_match);
    reveal(directive_word_matches);
}

/// 索引に含まれる公開指定の引数と、所属名前空間のパスの位置を示す。
pub proof fn export_entry_evidence(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, entry: int,
)
    requires
        circuit_index_matches(source, forms, entries),
        0 <= entry < entries.len(),
        entries[entry].head is Export,
    ensures
        ({
            let item = entries[entry];
            let root = item.form as int;
            &&& 0 <= root < forms.len()
            &&& forms[root] is List
            &&& {
                let end = forms[root]->List_end as int;
                &&& root + 2 < end <= forms.len()
                &&& forall|i: int| root + 2 <= i < end ==> #[trigger] forms[i] is Atom
            }
        }),
        entries[entry].namespace matches Some(parent) ==>
            (parent + 2 < forms.len() && forms[parent + 2] is Atom),
{
    indexed_entry_evidence(source, forms, entries, entry);
    let item = entries[entry];
    let root = item.form as int;
    let end = forms[root]->List_end as int;
    assert(header_matches(source, forms, root, item.namespace.is_some(), Head::Export));
    reveal(header_arguments_match);
    assert(directive_arguments_match(source, forms, root + 2, end, Head::Export));
    assert forall|i: int| root + 2 <= i < end implies #[trigger] forms[i] is Atom by {
        assert(directive_word_at(source, forms, i, end, HeaderError::ExpectedName));
    };
    owner_path_evidence(source, forms, entries, entry);
}

proof fn owner_path_evidence(source: &str, forms: Seq<Form>, entries: Seq<Entry>, entry: int)
    requires
        circuit_index_matches(source, forms, entries),
        0 <= entry < entries.len(),
    ensures
        entries[entry].namespace matches Some(parent) ==>
            (parent + 2 < forms.len() && forms[parent + 2] is Atom),
{
    indexed_entry_evidence(source, forms, entries, entry);
    reveal(header_arguments_match);
    let item = entries[entry];
    if let Some(parent) = item.namespace {
        let head = choose|head: Head| #[trigger] header_matches(source, forms, parent as int, false, head);
        names::namespace_head_is_unique(source, forms[parent + 1], head);
        assert(header_matches(source, forms, parent as int, false, Head::Namespace));
        assert(directive_word_at(source, forms, parent + 2, forms[parent as int]->List_end as int,
            HeaderError::ExpectedNamespacePath));
    }
}

/// 索引に含まれる `use` の参照先、別名、所属名前空間のパスの位置を示す。
pub proof fn use_entry_evidence(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, entry: int,
)
    requires
        circuit_index_matches(source, forms, entries),
        0 <= entry < entries.len(),
        entries[entry].head is Use,
    ensures
        ({
            let item = entries[entry];
            let root = item.form as int;
            &&& 0 <= root < root + 3 < forms.len()
            &&& forms[root + 2] is Atom && forms[root + 2]->Atom_kind is AbsolutePath
            &&& forms[root + 3] is Atom && forms[root + 3]->Atom_kind is Name
        }),
        entries[entry].namespace matches Some(parent) ==>
            (parent + 2 < forms.len() && forms[parent + 2] is Atom),
{
    indexed_entry_evidence(source, forms, entries, entry);
    owner_path_evidence(source, forms, entries, entry);
    let item = entries[entry];
    let root = item.form as int;
    let limit = forms[root]->List_end as int;
    reveal(header_arguments_match);
    assert(header_matches(source, forms, root, item.namespace.is_some(), Head::Use));
    assert(directive_arguments_match(source, forms, root + 2, limit, Head::Use));
}

proof fn indexed_subtree_location(
    source: &str, forms: Seq<Form>, root: int, end: int, index: int, owner: Option<usize>,
)
    requires
        0 <= root < end <= forms.len(),
        direct_form_in_range(forms, 0, forms.len() as int, root),
        forms[root] is List && forms[root]->List_end == end,
        root <= index < end,
        indexed_location(source, forms, index, owner),
    ensures
        (index == root && owner is None)
        || (owner is Some && owner->Some_0 == root),
{
    reveal(direct_form_in_range);
    if let Some(parent) = owner {
        if parent < root {
            assert(forms[parent as int]->List_end <= root);
        } else if parent > root {
            assert(root < parent < end);
        }
    } else if root < index {
        assert(forms[root]->List_end <= index);
    }
}

proof fn root_index_gap(
    source: &str, forms: Seq<Form>, root: int, end: int, next: int, head: Head,
)
    requires
        0 <= root < end <= forms.len(),
        direct_form_in_range(forms, 0, forms.len() as int, root),
        forms[root] is List && forms[root]->List_end == end,
        forall|other: Head| #[trigger] form_has_head(source, forms, root, false, other) <==> other == head,
        if head is Namespace { next == root + 3 <= end } else { next == end },
    ensures
        forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
            && root <= index < next ==> index == root && owner is None,
{
    assert forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
        && root <= index < next implies index == root && owner is None by {
        indexed_subtree_location(source, forms, root, end, index, owner);
        if let Some(parent) = owner {
            assert(parent == root);
            assert(form_has_head(source, forms, root, false, Head::Namespace));
            reveal(direct_form_in_range);
            assert(root + 3 <= index);
        }
    };
}

proof fn member_index_gap(
    source: &str, forms: Seq<Form>, root: int, end: int, index: int, next: int,
)
    requires
        0 <= root < end <= forms.len(),
        direct_form_in_range(forms, 0, forms.len() as int, root),
        forms[root] is List && forms[root]->List_end == end,
        root + 3 <= index < next <= end,
        direct_form_in_range(forms, root + 3, end, index),
        following_direct_form(forms, index, next),
    ensures
        forall|at: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, at, owner)
            && index <= at < next ==> at == index && owner == Some(root as usize),
{
    reveal(following_direct_form);
    assert(form_region_ends_at(forms, root + 3, end)) by {
        assert(exists|parent: int| 0 <= parent < root + 3
            && #[trigger] forms[parent] is List && forms[parent]->List_end == end);
    };
    assert forall|at: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, at, owner)
        && index <= at < next implies at == index && owner == Some(root as usize) by {
        indexed_subtree_location(source, forms, root, end, at, owner);
        assert(owner == Some(root as usize));
        if at > index {
            assert(direct_form_in_range(forms, root + 3, end, at));
        }
    };
}

proof fn append_index_entry(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, entry: Entry, next: int,
)
    requires
        index_prefix(source, forms, entries, entry.form as int),
        entry.form < next,
        indexed_location(source, forms, entry.form as int, entry.namespace),
        header_matches(source, forms, entry.form as int, entry.namespace.is_some(), entry.head),
        forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
            && entry.form <= index < next ==> index == entry.form && owner == entry.namespace,
    ensures index_prefix(source, forms, entries.push(entry), next),
{
    reveal(index_prefix);
    let extended = entries.push(entry);
    assert forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
        && index < next implies exists|k: int| 0 <= k < extended.len()
            && (#[trigger] extended[k]).form == index && extended[k].namespace == owner by {
        if index < entry.form {
            let k = choose|k: int| 0 <= k < entries.len()
                && (#[trigger] entries[k]).form == index && entries[k].namespace == owner;
            assert(extended[k] == entries[k]);
        } else {
            assert(extended[entries.len() as int] == entry);
        }
    };
}

proof fn indexed_prefix_is_valid(source: &str, forms: Seq<Form>, entries: Seq<Entry>, cursor: int)
    requires index_prefix(source, forms, entries, cursor),
    ensures forms_before(source, forms, cursor),
{
    reveal(index_prefix);
    assert forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
        && index < cursor implies exists|head: Head| #[trigger] header_matches(source, forms, index, owner.is_some(), head) by {
        let k = choose|k: int| 0 <= k < entries.len()
            && (#[trigger] entries[k]).form == index && entries[k].namespace == owner;
        assert(header_matches(source, forms, index, owner.is_some(), entries[k].head));
    };
}

proof fn reject_index_entry(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, index: int, owner: Option<usize>, kind: HeaderError, span: Range<usize>,
)
    requires
        well_formed_sexpr(source),
        sexpr_form_model(source) == Some(forms),
        index_prefix(source, forms, entries, index),
        indexed_location(source, forms, index, owner),
        0 <= index < forms.len(),
        forall|head: Head| !#[trigger] header_matches(source, forms, index, owner.is_some(), head),
        header_error_evidence(source, forms, index, owner.is_some(), kind, span),
    ensures
        !circuit_source_matches(source),
        circuit_source_error(source, CircuitFormError::Header { kind, span }),
{
    indexed_prefix_is_valid(source, forms, entries, index);
    assert(!forms_before(source, forms, forms.len() as int));
    assert(circuit_header_error_at(source, CircuitFormError::Header { kind, span }, index, owner));
}

fn index_namespace(
    source: &str, forms: &[Form], entries: &mut Vec<Entry>, root: usize, first: usize, end: usize,
    collect: bool, rows: &mut BuildRows,
) -> (result: Result<(), CircuitFormError>)
    requires
        well_formed_sexpr(source),
        sexpr_form_model(source) == Some(forms@),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        direct_form_in_range(forms@, 0, forms@.len() as int, root as int),
        form_has_head(source, forms@, root as int, false, Head::Namespace),
        forms@[root as int]->List_end == end,
        first == root + 3 <= end,
        index_prefix(source, forms@, old(entries)@, first as int),
        collect ==> build_rows_match(source, forms@, old(entries)@, old(rows).entry_ranges@,
            old(rows).definitions@, old(rows).references@, old(rows).signals@),
    ensures
        match result {
            Ok(()) => index_prefix(source, forms@, final(entries)@, end as int)
                && (collect ==> build_rows_match(source, forms@, final(entries)@, final(rows).entry_ranges@,
                    final(rows).definitions@, final(rows).references@, final(rows).signals@)),
            Err(error) => !circuit_source_matches(source) && circuit_source_error(source, error),
        },
{
    let mut index = first;
    proof { reveal(direct_form_in_range); }
    while index < end
        invariant
            first <= index <= end <= forms@.len(),
            first == root + 3,
            well_formed_sexpr(source),
            sexpr_form_model(source) == Some(forms@),
            complete_list_indices(forms@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            direct_form_in_range(forms@, 0, forms@.len() as int, root as int),
            form_has_head(source, forms@, root as int, false, Head::Namespace),
            forms@[root as int]->List_end == end,
            index < end ==> direct_form_in_range(forms@, first as int, end as int, index as int),
            index_prefix(source, forms@, entries@, index as int),
            collect ==> build_rows_match(source, forms@, entries@, rows.entry_ranges@, rows.definitions@, rows.references@, rows.signals@),
        decreases end - index,
    {
        assert(indexed_location(source, forms@, index as int, Some(root)));
        let ghost prior = *rows;
        let first_definition = rows.definitions.len();
        let first_reference = rows.references.len();
        let first_signal = rows.signals.len();
        let (head, next) = match read_header_into(source, forms, index, true, collect, rows) {
            Ok(header) => header,
            Err((kind, span)) => {
                proof { reject_index_entry(source, forms@, entries@, index as int, Some(root), kind, span); }
                return Err(CircuitFormError::Header { kind, span });
            }
        };
        let entry = Entry { head, form: index, namespace: Some(root) };
        proof {
            reveal(following_direct_form);
            assert(form_region_ends_at(forms@, first as int, end as int));
            member_index_gap(source, forms@, root as int, end as int, index as int, next as int);
            append_index_entry(source, forms@, entries@, entry, next as int);
        }
        if collect {
            let range = BuildEntryRanges {
                definitions: first_definition..rows.definitions.len(),
                references: first_reference..rows.references.len(),
                signals: first_signal..rows.signals.len(),
            };
            let ghost added = range;
            rows.entry_ranges.push(range);
            proof { record_build_entry(source, forms@, entries@, prior, *rows, entry, added); }
        }
        entries.push(entry);
        index = next;
    }
    Ok(())
}

/// 回路フォームの宣言位置を構文木の添字で返す。
///
/// 単一ソースの宣言シグネチャ、回路本体、テスト本体を検査する。
/// 索引にはトップレベルのフォームと名前空間の直下のフォームが入力順に一度ずつ現れる。
/// `(using nor)` を一度だけ指定する要件は、名前解決と同様にソース集合を対象とする後続の検査で扱う。
/// 型と結線の検査も後続の処理で扱う。
///
/// # Errors
///
/// 字句、S 式、検査対象の回路フォームに誤りがあれば、元入力の UTF-8 バイト範囲をエラーに含める。
/// 回路フォームに必須の要素がなければ、挿入位置を長さ0の範囲で示す。
/// テストで `case` と操作が混在すると、最初と種類が異なる項目の先頭語を主範囲とする。最初の項目についても先頭語の範囲をエラーに含める。
///
/// # Examples
///
/// ```
/// use circuitgame2_syntax::circuit::{Head, index_headers};
///
/// let result = index_headers("(namespace gates (func f (in) (out y) (def y 0)))")?;
/// assert_eq!(result.entries[1].head, Head::Func);
/// assert_eq!(result.entries[1].namespace, Some(result.entries[0].form));
/// # Ok::<(), circuitgame2_syntax::circuit::CircuitFormError>(())
/// ```
pub fn index_headers(source: &str) -> (result: Result<CircuitForms, CircuitFormError>)
    ensures
        result.is_ok() <==> circuit_source_matches(source),
        forall|error: CircuitFormError| #[trigger] circuit_source_error(source, error) <==> result == Err(error),
        match result {
            Ok(index) => circuit_index_matches(source, index.forms@, index.entries@)
                && form_spans_valid(source, index.forms@, source.spec_bytes().len() as int)
                && complete_list_indices(index.forms@) && nested_list_indices(index.forms@)
                && list_source_delimiters(source, index.forms@, false),
            Err(error) => circuit_source_error(source, error),
        },
{
    let forms = match parse(source) {
        Ok(forms) => forms,
        Err(error) => {
            proof {
                reject_circuit_syntax(source, error);
                circuit_result_diagnostics::<()>(source, Err(CircuitFormError::Syntax(error)));
            }
            return Err(CircuitFormError::Syntax(error));
        },
    };
    let indexed = index_parsed_headers(source, forms.as_slice());
    proof { circuit_result_diagnostics(source, indexed); }
    let entries = indexed?;
    Ok(CircuitForms { forms, entries })
}

/// 厳格に解析した S 式構文木から回路フォームを索引に載せる。
fn index_parsed_headers(source: &str, forms: &[Form])
    -> (result: Result<Vec<Entry>, CircuitFormError>)
    requires
        well_formed_sexpr(source),
        sexpr_form_model(source) == Some(forms@),
        complete_list_indices(forms@), nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> circuit_source_matches(source),
        match result {
            Ok(entries) => circuit_index_matches(source, forms@, entries@),
            Err(error) => circuit_source_error(source, error),
        },
{
    let mut rows = BuildRows::new();
    index_parsed_headers_into(source, forms, false, &mut rows)
}

pub(super) fn index_parsed_headers_into(source: &str, forms: &[Form], collect: bool, rows: &mut BuildRows)
    -> (result: Result<Vec<Entry>, CircuitFormError>)
    requires
        well_formed_sexpr(source),
        sexpr_form_model(source) == Some(forms@),
        complete_list_indices(forms@), nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        rows.entry_ranges@.len() == 0 && rows.definitions@.len() == 0 && rows.references@.len() == 0 && rows.signals@.len() == 0,
    ensures
        result.is_ok() <==> circuit_source_matches(source),
        match result {
            Ok(entries) => circuit_index_matches(source, forms@, entries@)
                && (collect ==> build_rows_match(source, forms@, entries@, final(rows).entry_ranges@,
                    final(rows).definitions@, final(rows).references@, final(rows).signals@)),
            Err(error) => circuit_source_error(source, error),
        },
{
    let mut entries: Vec<Entry> = Vec::new();
    let mut root = 0;
    let length = forms.len();
    proof {
        reveal(direct_form_in_range);
        reveal(index_prefix);
        reveal(build_rows_match);
    }
    while root < length
        invariant
            root <= length == forms@.len(),
            well_formed_sexpr(source),
            sexpr_form_model(source) == Some(forms@),
            complete_list_indices(forms@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            root < length ==> direct_form_in_range(forms@, 0, length as int, root as int),
            index_prefix(source, forms@, entries@, root as int),
            collect ==> build_rows_match(source, forms@, entries@, rows.entry_ranges@, rows.definitions@, rows.references@, rows.signals@),
        decreases length - root,
    {
        let ghost prior = *rows;
        let first_definition = rows.definitions.len();
        let first_reference = rows.references.len();
        let first_signal = rows.signals.len();
        let (head, end) = match read_header_into(source, forms, root, false, collect, rows) {
            Ok(header) => header,
            Err((kind, span)) => {
                proof { reject_index_entry(source, forms@, entries@, root as int, None, kind, span); }
                return Err(CircuitFormError::Header { kind, span });
            }
        };
        proof {
            reveal(following_direct_form);
            assert(form_region_ends_at(forms@, 0, length as int));
        }
        let entry = Entry { head, form: root, namespace: None };
        let next = if matches!(head, Head::Namespace) { root + 3 } else { end };
        proof {
            root_index_gap(source, forms@, root as int, end as int, next as int, head);
            append_index_entry(source, forms@, entries@, entry, next as int);
        }
        if collect {
            let range = BuildEntryRanges {
                definitions: first_definition..rows.definitions.len(),
                references: first_reference..rows.references.len(),
                signals: first_signal..rows.signals.len(),
            };
            let ghost added = range;
            rows.entry_ranges.push(range);
            proof { record_build_entry(source, forms@, entries@, prior, *rows, entry, added); }
        }
        entries.push(entry);
        if matches!(head, Head::Namespace) {
            index_namespace(source, forms, &mut entries, root, next, end, collect, rows)?;
        }
        root = end;
    }
    proof { indexed_prefix_is_valid(source, forms@, entries@, length as int); }
    Ok(entries)
}

} // verus!
