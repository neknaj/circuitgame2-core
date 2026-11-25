//! 元の本体と呼び出し先の署名を結び付け、型検査スタックに渡す。

use super::*;
use super::typing::{CallTypeEntry, check_typed_body_with_calls};
#[cfg(verus_only)]
use super::typing::{call_entries_fit, call_trace_fits, call_trace_model, trace_entry_in_range, canonical_call, typed_body_with_calls};
use super::named_call::{prepare_call_types, read_call_form};
#[cfg(verus_only)]
use super::named_call::{call_form_matches, call_form_origin, call_signature_types_match, decoded_call_has_arity};
use crate::project::{DefnCallEdge, DefnCallError, DefnCallSite, MixedUseAliases, PreparedDefnCall};
#[cfg(verus_only)]
use crate::project::{ProjectDeclaration, ProjectSource, ResolvedDefnName, call_arity_matches, defn_name_resolution,
    mixed_use_targets_match, prepared_call_site, resolved_defn_name_origin};
#[cfg(verus_only)]
use crate::ncg2m::defn::DefnHeader;
#[cfg(verus_only)]
use crate::syntax::{preorder_range_pair, strict_preorder_ranges};

mod coverage;
use coverage::first_unvisited_expression_entry;
#[cfg(verus_only)]
use coverage::call_trace_covers_slots;
#[cfg(verus_only)]
use super::named_call::{expression_slot, expression_slot_bounds};

verus! {

/// 名前付き呼び出しを含む補助関数の本体検査で見つかった最初の問題。
#[derive(Debug)]
pub enum DefnBodyCallError<'p, 'a> {
    /// 呼び出し先、公開範囲、引数の個数に関する診断。
    Call(DefnCallError<'p, 'a>),
    /// 式の構文・型の違反、または実行段階の確定を待つ式。
    Expression(ExpressionCheckFailure<'a>),
}

struct CallIssue<'p, 'a> {
    at: Ghost<usize>,
    span: Range<usize>,
    error: DefnCallError<'p, 'a>,
}

struct CallTypingInputs<'p, 'a> {
    calls: Vec<CallTypeEntry>,
    issues: Vec<CallIssue<'p, 'a>>,
    outcomes: Ghost<Seq<CallOutcome<'p, 'a>>>,
}

type CallOutcome<'p, 'a> = Option<Result<PreparedDefnCall<'p, 'a>, DefnCallError<'p, 'a>>>;

spec fn call_shape_at(calls: Seq<CallTypeEntry>, at: usize, signature: DefnSignature) -> bool {
    exists|i: int| 0 <= i < calls.len() && (#[trigger] calls[i]).at == at
        && call_signature_types_match(calls[i], signature)
}

spec fn issue_at(issues: Seq<CallIssue>, at: usize, error: DefnCallError) -> bool {
    exists|i: int| 0 <= i < issues.len() && (#[trigger] issues[i]).at@ == at && issues[i].error == error
}

#[verifier::opaque]
spec fn entry_witness(entry: CallTypeEntry, outcomes: Seq<CallOutcome>, body: usize) -> bool {
    body <= entry.at < body + outcomes.len()
        && (outcomes[entry.at - body] matches Some(Ok(PreparedDefnCall::Declared { declaration, signature, .. }))
            && entry.target == (DefnPosition { file: declaration.file, item: declaration.item })
            && call_signature_types_match(entry, signature))
}

spec fn issue_witness(forms: Seq<Form>, issue: CallIssue, outcomes: Seq<CallOutcome>, body: usize) -> bool {
    body <= issue.at@ < body + outcomes.len()
        && outcomes[issue.at@ - body] == Some(Err(issue.error))
        && issue.span == form_span(forms[issue.at@ as int])
}

#[verifier::opaque]
spec fn form_outcome_matches(
    aliases: &MixedUseAliases, file: usize, item: usize, forms: Seq<Form>, at: usize, result: CallOutcome,
) -> bool {
    let source = aliases.targets_model().project_model().sources_model()[file as int].text_model();
    exists|decoded: Option<CallForm>| #[trigger] call_form_matches(source, forms, at, decoded)
        && match (decoded, result) {
            (None, None) => true,
            (Some(form), Some(outcome)) => call_arity_matches(aliases, file, item, form, outcome),
            _ => false,
        }
}

#[verifier::opaque]
spec fn outcomes_recorded(
    aliases: &MixedUseAliases, file: usize, item: usize, forms: Seq<Form>, body: usize,
    outcomes: Seq<CallOutcome>, calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>,
) -> bool {
    forall|i: int| 0 <= i < outcomes.len() ==> {
        let result = #[trigger] outcomes[i];
        &&& form_outcome_matches(aliases, file, item, forms, (body + i) as usize, result)
        &&& match result {
            Some(Ok(PreparedDefnCall::Declared { signature, .. })) => call_shape_at(calls, (body + i) as usize, signature),
            Some(Err(error)) => issue_at(issues, (body + i) as usize, error),
            _ => true,
        }
    }
}

#[verifier::opaque]
spec fn call_inputs_match(
    aliases: &MixedUseAliases, file: usize, item: usize, forms: Seq<Form>, body: usize,
    outcomes: Seq<CallOutcome>, calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>,
) -> bool {
    &&& call_entries_fit(forms, calls)
    &&& forall|i: int| 0 <= i < calls.len() ==> entry_witness(#[trigger] calls[i], outcomes, body)
    &&& forall|i: int| 0 <= i < issues.len() ==> issue_witness(forms, #[trigger] issues[i], outcomes, body)
    &&& outcomes_recorded(aliases, file, item, forms, body, outcomes, calls, issues)
}

spec fn appended_call_type(
    forms: Seq<Form>, at: usize, outcome: CallOutcome, calls: Seq<CallTypeEntry>, added: Seq<CallTypeEntry>,
) -> bool {
    match outcome {
        Some(Ok(PreparedDefnCall::Declared { declaration, signature, .. })) =>
            added.len() == calls.len() + 1 && added.take(calls.len() as int) == calls
                && added[calls.len() as int].at == at
                && added[calls.len() as int].target == (DefnPosition { file: declaration.file, item: declaration.item })
                && canonical_call(forms, added[calls.len() as int])
                && call_signature_types_match(added[calls.len() as int], signature),
        _ => added == calls,
    }
}

spec fn appended_call_issue(
    forms: Seq<Form>, at: usize, outcome: CallOutcome, issues: Seq<CallIssue>, added: Seq<CallIssue>,
) -> bool {
    match outcome {
        Some(Err(error)) =>
            added.len() == issues.len() + 1 && added.take(issues.len() as int) == issues
                && added[issues.len() as int].at@ == at
                && added[issues.len() as int].span == form_span(forms[at as int])
                && added[issues.len() as int].error == error,
        _ => added == issues,
    }
}

proof fn append_ordered_type(
    forms: Seq<Form>, calls: Seq<CallTypeEntry>, next: CallTypeEntry,
)
    requires
        call_entries_fit(forms, calls), canonical_call(forms, next),
        forall|i: int| 0 <= i < calls.len() ==> (#[trigger] calls[i]).at < next.at,
    ensures call_entries_fit(forms, calls.push(next)),
{
    let added = calls.push(next);
    assert forall|i: int, j: int| 0 <= i < j < added.len()
        implies (#[trigger] added[i]).at < (#[trigger] added[j]).at by {
        assert(added[i] == calls[i]);
        if j < calls.len() { assert(added[j] == calls[j]); }
        else { assert(added[j] == next); }
    };
    assert forall|i: int| 0 <= i < added.len() implies canonical_call(forms, #[trigger] added[i]) by {
        if i < calls.len() { assert(added[i] == calls[i]); }
        else { assert(added[i] == next); }
    };
}

proof fn extend_type_witnesses(
    forms: Seq<Form>, body: usize, outcomes: Seq<CallOutcome>, at: usize, outcome: CallOutcome,
    calls: Seq<CallTypeEntry>, added: Seq<CallTypeEntry>,
)
    requires
        at == body + outcomes.len(),
        forall|i: int| 0 <= i < calls.len() ==> entry_witness(#[trigger] calls[i], outcomes, body),
        appended_call_type(forms, at, outcome, calls, added),
    ensures
        forall|i: int| 0 <= i < added.len() ==> entry_witness(#[trigger] added[i], outcomes.push(outcome), body),
{
    let prefix = outcomes.push(outcome);
    assert forall|i: int| 0 <= i < added.len() implies entry_witness(#[trigger] added[i], prefix, body) by {
        if i < calls.len() {
            assert(added[i] == calls[i]);
            assert(entry_witness(calls[i], outcomes, body));
            assert(entry_witness(calls[i], prefix, body)) by {
                reveal(entry_witness);
                let index = calls[i].at - body;
                assert(prefix[index] == outcomes[index]);
            };
        } else {
            assert(entry_witness(added[i], prefix, body)) by {
                reveal(entry_witness);
                assert(i == calls.len());
                assert(added[i].at == at);
                assert(prefix[at - body] == outcome);
            };
        }
    };
}

proof fn extend_call_types(
    forms: Seq<Form>, body: usize, outcomes: Seq<CallOutcome>, at: usize, outcome: CallOutcome,
    calls: Seq<CallTypeEntry>, added: Seq<CallTypeEntry>,
)
    requires
        at == body + outcomes.len(), at < forms.len(),
        call_entries_fit(forms, calls),
        forall|i: int| 0 <= i < calls.len() ==> entry_witness(#[trigger] calls[i], outcomes, body),
        appended_call_type(forms, at, outcome, calls, added),
    ensures
        call_entries_fit(forms, added),
        forall|i: int| 0 <= i < added.len() ==> entry_witness(#[trigger] added[i], outcomes.push(outcome), body),
{
    extend_type_witnesses(forms, body, outcomes, at, outcome, calls, added);
    if let Some(Ok(PreparedDefnCall::Declared { .. })) = outcome {
        let next = added[calls.len() as int];
        assert(added =~= calls.push(next));
        assert forall|i: int| 0 <= i < calls.len() implies (#[trigger] calls[i]).at < next.at by {
            reveal(entry_witness);
            assert(entry_witness(calls[i], outcomes, body));
        };
        append_ordered_type(forms, calls, next);
    }
}

proof fn extend_call_issues(
    forms: Seq<Form>, body: usize, outcomes: Seq<CallOutcome>, at: usize, outcome: CallOutcome,
    issues: Seq<CallIssue>, added: Seq<CallIssue>,
)
    requires
        at == body + outcomes.len(), at < forms.len(),
        forall|i: int| 0 <= i < issues.len() ==> issue_witness(forms, #[trigger] issues[i], outcomes, body),
        appended_call_issue(forms, at, outcome, issues, added),
    ensures
        forall|i: int| 0 <= i < added.len() ==> issue_witness(forms, #[trigger] added[i], outcomes.push(outcome), body),
{
    let prefix = outcomes.push(outcome);
    assert forall|i: int| 0 <= i < added.len() implies issue_witness(forms, #[trigger] added[i], prefix, body) by {
        if i < issues.len() {
            assert(added[i] == issues[i]);
            assert(issue_witness(forms, issues[i], outcomes, body));
        }
    };
}

proof fn extend_recorded_outcomes(
    aliases: &MixedUseAliases, file: usize, item: usize, forms: Seq<Form>, body: usize,
    outcomes: Seq<CallOutcome>, at: usize, outcome: CallOutcome,
    calls: Seq<CallTypeEntry>, next_calls: Seq<CallTypeEntry>,
    issues: Seq<CallIssue>, next_issues: Seq<CallIssue>,
)
    requires
        at == body + outcomes.len(), at < forms.len(),
        outcomes_recorded(aliases, file, item, forms, body, outcomes, calls, issues),
        form_outcome_matches(aliases, file, item, forms, at, outcome),
        appended_call_type(forms, at, outcome, calls, next_calls),
        appended_call_issue(forms, at, outcome, issues, next_issues),
    ensures outcomes_recorded(aliases, file, item, forms, body, outcomes.push(outcome), next_calls, next_issues),
{
    reveal(outcomes_recorded);
    let prefix = outcomes.push(outcome);
    assert forall|i: int| 0 <= i < prefix.len() implies {
        let result = #[trigger] prefix[i];
        &&& form_outcome_matches(aliases, file, item, forms, (body + i) as usize, result)
        &&& match result {
            Some(Ok(PreparedDefnCall::Declared { signature, .. })) => call_shape_at(next_calls, (body + i) as usize, signature),
            Some(Err(error)) => issue_at(next_issues, (body + i) as usize, error),
            _ => true,
        }
    } by {
        if i < outcomes.len() {
            assert(prefix[i] == outcomes[i]);
            match outcomes[i] {
                Some(Ok(PreparedDefnCall::Declared { signature, .. })) => {
                    let j = choose|j: int| 0 <= j < calls.len() && (#[trigger] calls[j]).at == body + i
                        && call_signature_types_match(calls[j], signature);
                    assert(next_calls[j] == calls[j]);
                }
                Some(Err(error)) => {
                    let j = choose|j: int| 0 <= j < issues.len() && (#[trigger] issues[j]).at@ == body + i && issues[j].error == error;
                    assert(next_issues[j] == issues[j]);
                }
                _ => (),
            }
        } else {
            assert(prefix[i] == outcome);
            match outcome {
                Some(Ok(PreparedDefnCall::Declared { signature, .. })) => {
                    let j = calls.len() as int;
                    assert(next_calls[j].at == body + i);
                    assert(call_signature_types_match(next_calls[j], signature));
                    assert(call_shape_at(next_calls, (body + i) as usize, signature));
                }
                Some(Err(error)) => {
                    let j = issues.len() as int;
                    assert(next_issues[j].at@ == body + i && next_issues[j].error == error);
                    assert(issue_at(next_issues, (body + i) as usize, error));
                }
                _ => (),
            }
        }
    };
}

proof fn record_call_input(
    aliases: &MixedUseAliases, file: usize, item: usize, forms: Seq<Form>, body: usize,
    outcomes: Seq<CallOutcome>, at: usize, outcome: CallOutcome,
    calls: Seq<CallTypeEntry>, next_calls: Seq<CallTypeEntry>,
    issues: Seq<CallIssue>, next_issues: Seq<CallIssue>,
)
    requires
        at == body + outcomes.len(), at < forms.len(),
        call_inputs_match(aliases, file, item, forms, body, outcomes, calls, issues),
        form_outcome_matches(aliases, file, item, forms, at, outcome),
        appended_call_type(forms, at, outcome, calls, next_calls),
        appended_call_issue(forms, at, outcome, issues, next_issues),
    ensures call_inputs_match(aliases, file, item, forms, body, outcomes.push(outcome), next_calls, next_issues),
{
    reveal(call_inputs_match);
    extend_call_types(forms, body, outcomes, at, outcome, calls, next_calls);
    extend_call_issues(forms, body, outcomes, at, outcome, issues, next_issues);
    extend_recorded_outcomes(aliases, file, item, forms, body, outcomes, at, outcome, calls, next_calls, issues, next_issues);
}

fn gather_call_types<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize, source: &'a str, forms: &[Form],
    body: usize, end: usize,
) -> (inputs: CallTypingInputs<'p, 'a>)
    requires
        usable_forms(source, forms@), body <= end <= forms@.len(),
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
        aliases.targets_model().project_model().has_source_indexes(),
        file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().sources_model()[file as int].text_model() == source,
        aliases.targets_model().project_model().functional_forms_model(file) == Some(forms@),
    ensures
        call_entries_fit(forms@, inputs.calls@),
        inputs.outcomes@.len() == end - body,
        call_inputs_match(aliases, file, item, forms@, body, inputs.outcomes@, inputs.calls@, inputs.issues@),
{
    let mut calls = Vec::new();
    let mut issues = Vec::new();
    let mut at = body;
    let ghost mut outcomes: Seq<CallOutcome> = Seq::empty();
    assert(call_inputs_match(aliases, file, item, forms@, body, outcomes, calls@, issues@)) by {
        reveal(call_inputs_match);
        reveal(outcomes_recorded);
    };
    while at < end
        invariant
            usable_forms(source, forms@), body <= at <= end <= forms@.len(), outcomes.len() == at - body,
            mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
            aliases.targets_model().project_model().has_source_indexes(),
            file < aliases.targets_model().project_model().sources_model().len(),
            aliases.targets_model().project_model().sources_model()[file as int].text_model() == source,
            aliases.targets_model().project_model().functional_forms_model(file) == Some(forms@),
            call_inputs_match(aliases, file, item, forms@, body, outcomes, calls@, issues@),
        decreases end - at,
    {
        // 構文木を順に走査して候補を集める。式の位置は、後続の型検査がたどる。
        let form = read_call_form(source, forms, at);
        let checked = match &form {
            Some(decoded) => Some(aliases.prepare_decoded_call(file, item, decoded)),
            None => None,
        };
        assert(form_outcome_matches(aliases, file, item, forms@, at, checked)) by {
            reveal(form_outcome_matches);
        };
        let ghost outcome = checked;
        let ghost before = calls@;
        let ghost earlier = issues@;
        match checked {
            Some(Ok(PreparedDefnCall::Declared { site: _site, declaration, signature })) => {
                proof {
                    let decoded = form->Some_0;
                    decoded_call_has_arity(source, forms@, at, decoded);
                    assert(decoded.arguments == signature.parameters@.len());
                }
                let _len = signature.parameters.len();
                let target = DefnPosition { file: declaration.file, item: declaration.item };
                let entry = prepare_call_types(source, forms, at, target, &signature);
                calls.push(entry);
                assert(calls@.take(before.len() as int) =~= before);
            }
            Some(Err(error)) => {
                issues.push(CallIssue { at: Ghost(at), span: span_of(&forms[at]), error });
                assert(issues@.take(earlier.len() as int) =~= earlier);
            }
            _ => (),
        }
        proof {
            record_call_input(aliases, file, item, forms@, body, outcomes, at, outcome, before, calls@, earlier, issues@);
            outcomes = outcomes.push(outcome);
        }
        at += 1;
    }
    proof { reveal(call_inputs_match); }
    CallTypingInputs { calls, issues, outcomes: Ghost(outcomes) }
}

spec fn selected_body_error<'p, 'a>(
    issues: Seq<CallIssue<'p, 'a>>, error: ExpressionCheckFailure<'a>, result: DefnBodyCallError<'p, 'a>,
) -> bool {
    if let ExpressionCheckFailure::Deferred(DeferredExpression::Form(span)) = error {
        if exists|i: int| 0 <= i < issues.len() && (#[trigger] issues[i]).span == span {
            exists|i: int| 0 <= i < issues.len() && (#[trigger] issues[i]).span == span
                && result == DefnBodyCallError::Call(issues[i].error)
        } else { result == DefnBodyCallError::Expression(error) }
    } else { result == DefnBodyCallError::Expression(error) }
}

proof fn selected_call_issue<'p, 'a>(issues: Seq<CallIssue<'p, 'a>>, index: int, span: Range<usize>)
    requires 0 <= index < issues.len(), issues[index].span == span,
    ensures selected_body_error(issues, ExpressionCheckFailure::Deferred(DeferredExpression::Form(span)),
        DefnBodyCallError::Call(issues[index].error)),
{
    assert(exists|i: int| 0 <= i < issues.len() && (#[trigger] issues[i]).span == span
        && issues[i].error == issues[index].error);
}

fn match_body_error<'p, 'a>(issues: &mut Vec<CallIssue<'p, 'a>>, error: ExpressionCheckFailure<'a>)
    -> (result: DefnBodyCallError<'p, 'a>)
    ensures selected_body_error(old(issues)@, error, result),
{
    if let ExpressionCheckFailure::Deferred(DeferredExpression::Form(ref span)) = error {
        assert(error == ExpressionCheckFailure::Deferred(DeferredExpression::Form(*span)));
        let mut i = 0;
        let len = issues.len();
        while i < len
            invariant issues@ == old(issues)@, issues@.len() == len, i <= len,
                error == ExpressionCheckFailure::Deferred(DeferredExpression::Form(*span)),
                forall|j: int| 0 <= j < i ==> (#[trigger] old(issues)@[j]).span != *span,
            decreases len - i,
        {
            if issues[i].span.start == span.start && issues[i].span.end == span.end {
                let ghost found = old(issues)@[i as int];
                assert(issues@[i as int] == found && found.span == *span);
                assert(error == ExpressionCheckFailure::Deferred(DeferredExpression::Form(*span)));
                let issue = issues.swap_remove(i);
                assert(issue == found);
                let result = DefnBodyCallError::Call(issue.error);
                proof { selected_call_issue(old(issues)@, i as int, *span); }
                return result;
            }
            i += 1;
        }
    }
    DefnBodyCallError::Expression(error)
}

spec fn call_body_outcome<'p, 'a>(
    calls: Seq<CallTypeEntry>, issues: Seq<CallIssue<'p, 'a>>, source: &'a str, forms: Seq<Form>, body: usize,
    signature: DefnSignature<'a>, result: Result<DefnSignature<'a>, DefnBodyCallError<'p, 'a>>,
) -> bool {
    let typed = typed_body_with_calls(calls, source, forms, environment_view(signature.parameters@),
        body, type_shape(signature.result_type.ty));
    match (typed, result) {
        (BodyVerdict::Accepted, Ok(checked)) => checked == signature,
        (BodyVerdict::Rejected(error), Err(result)) => selected_body_error(issues, error, result),
        _ => false,
    }
}

/// 解析済み本体を、同じプロジェクトの呼び出し先と署名を使って検査したことを表す。
pub(crate) closed spec fn indexed_call_body_matches<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize, source: &'a str, forms: Seq<Form>,
    entries: Seq<MetaItem>, result: Result<DefnSignature<'a>, DefnBodyCallError<'p, 'a>>,
) -> bool {
    &&& meta_ast_matches(source, forms, entries)
    &&& item < entries.len()
    &&& entries[item as int].kind is Defn
    &&& {
        let header = entries[item as int].kind->Defn_0;
        exists|root: usize, body: usize, signature: DefnSignature, outcomes: Seq<CallOutcome>,
            calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>|
            #[trigger] indexed_body_site(source, forms, root, body, header)
                && signature_matches_header(source, header, signature)
                && outcomes.len() == subtree_limit(forms, body) - body
                && #[trigger] call_inputs_match(aliases, file, item, forms, body, outcomes, calls, issues)
                && #[trigger] call_body_outcome(calls, issues, source, forms, body, signature, result)
    }
}

pub(crate) proof fn indexed_call_body_locally_typed(
    aliases: &MixedUseAliases, file: usize, item: usize, source: &str, forms: Seq<Form>, entries: Seq<MetaItem>,
    at: usize, checked: DefnSignature, actual: DefnSignature,
)
    requires
        indexed_call_body_matches(aliases, file, item, source, forms, entries, Ok(checked)),
        same_defn_signature(checked, actual), checked.body_span == actual.body_span,
        actual.result_type.ty.list_depth == 0,
        actual.result_type.ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)),
        at < forms.len(), form_span(forms[at as int]) == actual.body_span,
        crate::ncg2m::file::retained_forms_in_source_order(forms),
        local_scalar_fragment(source, forms, at),
    ensures local_scalar_site_is_typed(source, forms, actual.parameters@, at, actual.result_type.ty),
{
    let header = entries[item as int].kind->Defn_0;
    let (root, body, signature, outcomes, calls, issues) = choose|
        root: usize, body: usize, signature: DefnSignature, outcomes: Seq<CallOutcome>,
        calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>|
        #[trigger] indexed_body_site(source, forms, root, body, header)
            && signature_matches_header(source, header, signature)
            && outcomes.len() == subtree_limit(forms, body) - body
            && #[trigger] call_inputs_match(aliases, file, item, forms, body, outcomes, calls, issues)
            && #[trigger] call_body_outcome(calls, issues, source, forms, body, signature, Ok(checked));
    assert(signature == checked);
    crate::ncg2m::data_types::signature_result_origin(source, header, signature);
    reveal(crate::ncg2m::file::retained_forms_in_source_order);
    crate::ncg2m::file::meta_ast_unique_start(forms, at, body);
    super::typing::scalar::checked_local_body_ignores_call_types(calls, source, forms, body, checked, actual);
}

proof fn span_within_subtree(forms: Seq<Form>, root: usize, at: usize)
    requires strict_preorder_ranges(forms), root <= at < subtree_limit(forms, root) <= forms.len(),
    ensures form_span(forms[root as int]).start <= form_span(forms[at as int]).start
        && form_span(forms[at as int]).end <= form_span(forms[root as int]).end,
{
    if root < at {
        assert(forms[root as int] is List);
        reveal(strict_preorder_ranges);
        assert(preorder_range_pair(forms[root as int], forms[at as int], at as int));
    }
}

pub(crate) proof fn indexed_call_body_origin<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize, source: &'a str, forms: Seq<Form>,
    entries: Seq<MetaItem>, outcome: Result<DefnSignature<'a>, DefnBodyCallError<'p, 'a>>,
)
    requires indexed_call_body_matches(aliases, file, item, source, forms, entries, outcome),
    ensures
        outcome matches Ok(signature) ==>
            signature_matches_header(source, entries[item as int].kind->Defn_0, signature),
        outcome matches Err(DefnBodyCallError::Call(error)) ==> {
            let site = prepared_call_site(Err(error));
            &&& *site.source == aliases.targets_model().project_model().sources_model()[file as int]
            &&& entries[item as int].kind matches MetaItemKind::Defn(header) && {
                &&& header.body_span.start <= site.span.start
                &&& site.span.end <= header.body_span.end
            }
            &&& site.span.start <= site.head.start && site.head.end <= site.span.end
            &&& exists|at: usize| at + 1 < forms.len() && (#[trigger] forms[at as int]) is List
                && forms[at + 1] is Atom
                && site.span == form_span(forms[at as int]) && site.head == form_span(forms[at + 1])
        },
{
    let header = entries[item as int].kind->Defn_0;
    let (root, body, signature, outcomes, calls, issues) = choose|
        root: usize, body: usize, signature: DefnSignature, outcomes: Seq<CallOutcome>,
        calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>|
        #[trigger] indexed_body_site(source, forms, root, body, header)
            && signature_matches_header(source, header, signature)
            && outcomes.len() == subtree_limit(forms, body) - body
            && #[trigger] call_inputs_match(aliases, file, item, forms, body, outcomes, calls, issues)
            && #[trigger] call_body_outcome(calls, issues, source, forms, body, signature, outcome);
    if let Err(DefnBodyCallError::Call(error)) = outcome {
        let verdict = typed_body_with_calls(calls, source, forms, environment_view(signature.parameters@),
            body, type_shape(signature.result_type.ty));
        let failure = verdict->Rejected_0;
        let span = failure->Deferred_0->Form_0;
        let i = choose|i: int| 0 <= i < issues.len() && (#[trigger] issues[i]).span == span
            && issues[i].error == error;
        let at = issues[i].at@;
        reveal(call_inputs_match);
        assert(issue_witness(forms, issues[i], outcomes, body));
        assert(outcomes[at - body] == Some(Err(error)));
        reveal(outcomes_recorded);
        assert(form_outcome_matches(aliases, file, item, forms, at, Some(Err(error))));
        reveal(form_outcome_matches);
        let call = choose|decoded: Option<CallForm>| #[trigger] call_form_matches(
            aliases.targets_model().project_model().sources_model()[file as int].text_model(), forms, at, decoded,
        ) && decoded.is_some() && call_arity_matches(aliases, file, item, decoded->Some_0, Err(error));
        call_form_origin(aliases.targets_model().project_model().sources_model()[file as int].text_model(),
            forms, at, call->Some_0);
        meta_ast_body_origin(source, forms, entries, item as int);
        assert(body <= at < subtree_limit(forms, body) <= forms.len());
        span_within_subtree(forms, body, at);
        span_within_subtree(forms, at, (at + 1) as usize);
    }
}

/// 引数の添字が、呼び出し先の名前の直後からフォーム末尾までを左から覆うことを表す。
pub closed spec fn defn_call_arguments(forms: Seq<Form>, at: usize, arguments: Seq<usize>) -> bool {
    &&& at < forms.len()
    &&& forms[at as int] is List
    &&& at + 2 <= subtree_limit(forms, at) <= forms.len()
    &&& if arguments.len() == 0 { at + 2 == subtree_limit(forms, at) }
        else { arguments[0] == at + 2 }
    &&& forall|i: int| 0 <= i < arguments.len() ==> {
        let child = #[trigger] arguments[i];
        &&& at < child < subtree_limit(forms, child) <= subtree_limit(forms, at)
        &&& if i + 1 < arguments.len() { subtree_limit(forms, child) == arguments[i + 1] }
            else { subtree_limit(forms, child) == subtree_limit(forms, at) }
    }
}

/// 指定した引数の構文木上の位置と、隣の引数との境界を取り出す。
pub proof fn defn_call_argument_origin(forms: Seq<Form>, at: usize, arguments: Seq<usize>, slot: usize)
    requires defn_call_arguments(forms, at, arguments), slot < arguments.len(),
    ensures {
        let child = arguments[slot as int];
        let limit = match forms[child as int] {
            Form::Atom { .. } => (child + 1) as usize,
            Form::List { end, .. } => end,
        };
        &&& forms[at as int] is List
        &&& at < child < limit <= forms[at as int]->List_end <= forms.len()
        &&& slot == 0 ==> child == at + 2
        &&& if slot + 1 < arguments.len() { limit == arguments[slot + 1] }
            else { limit == forms[at as int]->List_end }
    },
{}

pub(in crate::ncg2m) proof fn argument_positions_increase(
    forms: Seq<Form>, at: usize, arguments: Seq<usize>, slot: int,
)
    requires defn_call_arguments(forms, at, arguments), 0 <= slot < arguments.len(),
    ensures
        at < arguments[slot],
        slot + 1 < arguments.len() ==> arguments[slot] < arguments[slot + 1],
{
    assert(at < arguments[slot] < subtree_limit(forms, arguments[slot]));
}

proof fn canonical_call_preserves_arguments(forms: Seq<Form>, entry: CallTypeEntry, arguments: Seq<usize>)
    requires canonical_call(forms, entry), arguments == entry.arguments@.map_values(|arg: super::typing::CallArgument| arg.at),
    ensures defn_call_arguments(forms, entry.at, arguments),
{
    assert forall|i: int| 0 <= i < arguments.len() implies {
        let child = #[trigger] arguments[i];
        &&& entry.at < child < subtree_limit(forms, child) <= subtree_limit(forms, entry.at)
        &&& if i + 1 < arguments.len() { subtree_limit(forms, child) == arguments[i + 1] }
            else { subtree_limit(forms, child) == subtree_limit(forms, entry.at) }
    } by {
        assert(arguments[i] == entry.arguments@[i].at);
        if i + 1 < arguments.len() { assert(arguments[i + 1] == entry.arguments@[i + 1].at); }
    };
}

/// 呼び出しの元の範囲と参照先が、同じプロジェクトにあることを表す。
#[verifier::opaque]
pub open spec fn defn_call_edge_matches(aliases: &MixedUseAliases, edge: DefnCallEdge) -> bool {
    let project = aliases.targets_model().project_model();
    &&& edge.from.file < project.sources_model().len()
    &&& *edge.call.source == project.sources_model()[edge.from.file as int]
    &&& project.indexed_defn(edge.from.file, edge.from.item) matches Some(header) && {
        &&& header.body_span.start <= edge.call.span.start
        &&& edge.call.span.end <= header.body_span.end
        &&& edge.call.span.start <= edge.call.head.start
        &&& edge.call.head.end <= edge.call.span.end
    }
    &&& project.functional_forms_model(edge.from.file) matches Some(forms) && {
        let at = edge.at;
        &&& at + 1 < forms.len()
        &&& forms[at as int] is List && forms[at + 1] is Atom
        &&& edge.call.span == form_span(forms[at as int]) && edge.call.head == form_span(forms[at + 1])
        &&& defn_call_arguments(forms, at, edge.arguments@)
    }
    &&& project.indexed_defn(edge.to.file, edge.to.item) matches Some(header)
        && header.parameters@.len() == edge.arguments@.len()
    &&& exists|name: &str, declaration: ProjectDeclaration|
        #[trigger] defn_name_resolution(aliases, edge.from.file, edge.from.item, name,
            Ok(ResolvedDefnName::Declaration(declaration)))
            && declaration.file == edge.to.file && declaration.item == edge.to.item
            && name.spec_bytes() == edge.call.source.text_model().spec_bytes()
                [edge.call.head.start as int..edge.call.head.end as int]
}

spec fn edge_projects(source: &ProjectSource, forms: Seq<Form>, entry: CallTypeEntry, edge: DefnCallEdge) -> bool {
    &&& edge.to == entry.target
    &&& edge.at == entry.at
    &&& edge.arguments@ == entry.arguments@.map_values(|arg: super::typing::CallArgument| arg.at)
    &&& *edge.call.source == *source
    &&& edge.call.span == form_span(forms[entry.at as int])
    &&& edge.call.head == form_span(forms[entry.at + 1])
}

proof fn finish_edge_evidence(
    aliases: &MixedUseAliases, edge: DefnCallEdge, forms: Seq<Form>, at: usize,
    name: &str, declaration: ProjectDeclaration,
)
    requires
        ({
            let project = aliases.targets_model().project_model();
            &&& edge.from.file < project.sources_model().len()
            &&& *edge.call.source == project.sources_model()[edge.from.file as int]
            &&& project.indexed_defn(edge.from.file, edge.from.item) matches Some(header) && {
                &&& header.body_span.start <= edge.call.span.start
                &&& edge.call.span.end <= header.body_span.end
                &&& edge.call.span.start <= edge.call.head.start
                &&& edge.call.head.end <= edge.call.span.end
            }
            &&& project.functional_forms_model(edge.from.file) == Some(forms)
            &&& project.indexed_defn(edge.to.file, edge.to.item) matches Some(header)
                && header.parameters@.len() == edge.arguments@.len()
        }),
        at == edge.at,
        at + 1 < forms.len(), forms[at as int] is List, forms[at + 1] is Atom,
        defn_call_arguments(forms, at, edge.arguments@),
        edge.call.span == form_span(forms[at as int]),
        edge.call.head == form_span(forms[at + 1]),
        defn_name_resolution(aliases, edge.from.file, edge.from.item, name,
            Ok(ResolvedDefnName::Declaration(declaration))),
        declaration.file == edge.to.file, declaration.item == edge.to.item,
        name.spec_bytes() == edge.call.source.text_model().spec_bytes()
            [edge.call.head.start as int..edge.call.head.end as int],
    ensures defn_call_edge_matches(aliases, edge),
{
    reveal(defn_call_edge_matches);
    assert(forms[at as int] is List && forms[at + 1] is Atom);
}

#[verifier::spinoff_prover]
proof fn trace_entry_resolution<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, forms: Seq<Form>, body: usize,
    outcomes: Seq<CallOutcome<'p, 'a>>, calls: Seq<CallTypeEntry>, issues: Seq<CallIssue<'p, 'a>>, index: usize,
) -> (evidence: (CallForm<'a>, ProjectDeclaration<'p, 'a>, DefnSignature<'a>))
    requires
        index < calls.len(),
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues),
    ensures
        body <= calls[index as int].at < body + outcomes.len(),
        call_form_matches(aliases.targets_model().project_model().sources_model()[caller.file as int].text_model(),
            forms, calls[index as int].at, Some(evidence.0)),
        defn_name_resolution(aliases, caller.file, caller.item, evidence.0.word,
            Ok(ResolvedDefnName::Declaration(evidence.1))),
        calls[index as int].target == (DefnPosition { file: evidence.1.file, item: evidence.1.item }),
        aliases.targets_model().project_model().defn_signature_matches_index(
            evidence.1.file, evidence.1.item, Some(evidence.2),
        ),
        call_signature_types_match(calls[index as int], evidence.2),
{
    let project = aliases.targets_model().project_model();
    let entry = calls[index as int];
    let at = entry.at;
    let src = project.sources_model()[caller.file as int].text_model();
    assert(entry_witness(entry, outcomes, body)) by { reveal(call_inputs_match); };
    let resolved = outcomes[at - body]->Some_0;
    let declaration = resolved->Ok_0->Declared_declaration;
    let signature = resolved->Ok_0->Declared_signature;
    assert(body <= at < body + outcomes.len() && outcomes[at - body] == Some(resolved)
        && resolved is Ok && resolved->Ok_0 is Declared
        && call_signature_types_match(entry, signature)
        && entry.target == (DefnPosition { file: declaration.file, item: declaration.item })) by {
        reveal(entry_witness);
    };
    assert(form_outcome_matches(aliases, caller.file, caller.item, forms, at, Some(resolved))) by {
        reveal(call_inputs_match);
        reveal(outcomes_recorded);
    };
    reveal(form_outcome_matches);
    let form = choose|decoded: Option<CallForm>| #[trigger] call_form_matches(src, forms, at, decoded)
        && decoded.is_some() && call_arity_matches(aliases, caller.file, caller.item, decoded->Some_0, resolved);
    (form->Some_0, declaration, signature)
}

proof fn recorded_edge_has_origin<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, forms: Seq<Form>, entries: Seq<MetaItem>,
    body: usize, outcomes: Seq<CallOutcome<'p, 'a>>, calls: Seq<CallTypeEntry>, issues: Seq<CallIssue<'p, 'a>>,
    index: usize, edge: DefnCallEdge<'p, 'a>,
)
    requires
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
        edge.from == caller,
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().functional_forms_model(caller.file) == Some(forms),
        caller.item < entries.len(), entries[caller.item as int].kind is Defn,
        aliases.targets_model().project_model().indexed_defn(caller.file, caller.item)
            == Some(entries[caller.item as int].kind->Defn_0),
        meta_ast_matches(edge.call.source.text_model(), forms, entries),
        form_span(forms[body as int]) == entries[caller.item as int].kind->Defn_0.body_span,
        index < calls.len(),
        outcomes.len() == subtree_limit(forms, body) - body,
        call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues),
        edge_projects(&aliases.targets_model().project_model().sources_model()[caller.file as int],
            forms, calls[index as int], edge),
    ensures defn_call_edge_matches(aliases, edge),
{
    let project = aliases.targets_model().project_model();
    let entry = calls[index as int];
    let at = entry.at;
    let src = project.sources_model()[caller.file as int].text_model();
    let (form, declaration, signature) = trace_entry_resolution(aliases, caller, forms, body, outcomes, calls, issues, index);
    resolved_defn_name_origin(aliases, caller.file, caller.item, form.word, declaration);
    call_form_origin(src, forms, at, form);
    meta_ast_body_origin(src, forms, entries, caller.item as int);
    assert(body <= at < subtree_limit(forms, body) <= forms.len());
    span_within_subtree(forms, body, at);
    span_within_subtree(forms, at, (at + 1) as usize);
    let name = form.word;
    assert(defn_name_resolution(aliases, caller.file, caller.item, name, Ok(ResolvedDefnName::Declaration(declaration))));
    assert(name.spec_bytes() == src.spec_bytes()[edge.call.head.start as int..edge.call.head.end as int]);
    assert(canonical_call(forms, entry)) by { reveal(call_inputs_match); }
    canonical_call_preserves_arguments(forms, entry, edge.arguments@);
    project.indexed_defn_signature_origin(edge.to.file, edge.to.item, Some(signature));
    let header = project.indexed_defn(edge.to.file, edge.to.item)->Some_0;
    let callee = project.sources_model()[edge.to.file as int].text_model();
    crate::ncg2m::data_types::signature_result_origin(callee, header, signature);
    assert(edge.arguments@.len() == entry.arguments@.len());
    finish_edge_evidence(aliases, edge, forms, at, name, declaration);
}

fn call_argument_positions(entry: &CallTypeEntry) -> (positions: Vec<usize>)
    ensures positions@ == entry.arguments@.map_values(|arg: super::typing::CallArgument| arg.at),
{
    let mut positions = Vec::new();
    let mut i = 0;
    while i < entry.arguments.len()
        invariant
            i == positions@.len() <= entry.arguments@.len(),
            forall|slot: int| 0 <= slot < i ==> (#[trigger] positions@[slot]) == entry.arguments@[slot].at,
        decreases entry.arguments@.len() - i,
    {
        positions.push(entry.arguments[i].at);
        i += 1;
    }
    assert(positions@ =~= entry.arguments@.map_values(|arg: super::typing::CallArgument| arg.at));
    positions
}

fn read_call_edge<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, forms: &[Form], calls: &[CallTypeEntry],
    row: usize, Ghost(entries): Ghost<Seq<MetaItem>>, Ghost(body): Ghost<usize>,
    Ghost(outcomes): Ghost<Seq<CallOutcome<'p, 'a>>>, Ghost(issues): Ghost<Seq<CallIssue<'p, 'a>>>,
) -> (edge: DefnCallEdge<'p, 'a>)
    requires
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().functional_forms_model(caller.file) == Some(forms@),
        caller.item < entries.len(), entries[caller.item as int].kind is Defn,
        aliases.targets_model().project_model().indexed_defn(caller.file, caller.item)
            == Some(entries[caller.item as int].kind->Defn_0),
        meta_ast_matches(aliases.targets_model().project_model().sources_model()[caller.file as int].text_model(),
            forms@, entries),
        form_span(forms@[body as int]) == entries[caller.item as int].kind->Defn_0.body_span,
        outcomes.len() == subtree_limit(forms@, body) - body,
        call_entries_fit(forms@, calls@),
        call_inputs_match(aliases, caller.file, caller.item, forms@, body, outcomes, calls@, issues),
        row < calls@.len(), body <= calls@[row as int].at < forms@.len(),
    ensures edge.from == caller,
        edge_projects(&aliases.targets_model().project_model().sources_model()[caller.file as int],
            forms@, calls@[row as int], edge),
        defn_call_edge_matches(aliases, edge),
{
    let source = &aliases.targets().project().sources()[caller.file];
    let entry = &calls[row];
    let at = entry.at;
    assert(canonical_call(forms@, *entry));
    let call = DefnCallSite { source, head: span_of(&forms[at + 1]), span: span_of(&forms[at]) };
    let arguments = call_argument_positions(entry);
    let edge = DefnCallEdge { from: caller, at, arguments, call, to: entry.target };
    proof { recorded_edge_has_origin(aliases, caller, forms@, entries, body, outcomes, calls@, issues, row, edge); }
    edge
}

fn project_call_trace<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, forms: &[Form], calls: &[CallTypeEntry],
    trace: &[usize], Ghost(entries): Ghost<Seq<MetaItem>>, Ghost(body): Ghost<usize>,
    Ghost(outcomes): Ghost<Seq<CallOutcome<'p, 'a>>>, Ghost(issues): Ghost<Seq<CallIssue<'p, 'a>>>,
) -> (edges: Vec<DefnCallEdge<'p, 'a>>)
    requires
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().functional_forms_model(caller.file) == Some(forms@),
        caller.item < entries.len(), entries[caller.item as int].kind is Defn,
        aliases.targets_model().project_model().indexed_defn(caller.file, caller.item)
            == Some(entries[caller.item as int].kind->Defn_0),
        meta_ast_matches(aliases.targets_model().project_model().sources_model()[caller.file as int].text_model(),
            forms@, entries),
        form_span(forms@[body as int]) == entries[caller.item as int].kind->Defn_0.body_span,
        outcomes.len() == subtree_limit(forms@, body) - body,
        call_entries_fit(forms@, calls@),
        call_trace_fits(calls@, trace@, body, forms@.len()),
        call_inputs_match(aliases, caller.file, caller.item, forms@, body, outcomes, calls@, issues),
    ensures edges@.len() == trace@.len(),
        forall|i: int| 0 <= i < edges@.len() ==> {
            let edge = #[trigger] edges@[i];
            &&& edge.from == caller
            &&& edge_projects(&aliases.targets_model().project_model().sources_model()[caller.file as int],
                forms@, calls@[trace@[i] as int], edge)
            &&& defn_call_edge_matches(aliases, edge)
        },
{
    let ghost source = aliases.targets_model().project_model().sources_model()[caller.file as int];
    let mut edges = Vec::<DefnCallEdge>::new();
    let mut i = 0;
    while i < trace.len()
        invariant
            i == edges@.len() <= trace@.len(),
            source == aliases.targets_model().project_model().sources_model()[caller.file as int],
            mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
            caller.file < aliases.targets_model().project_model().sources_model().len(),
            aliases.targets_model().project_model().functional_forms_model(caller.file) == Some(forms@),
            caller.item < entries.len(), entries[caller.item as int].kind is Defn,
            aliases.targets_model().project_model().indexed_defn(caller.file, caller.item)
                == Some(entries[caller.item as int].kind->Defn_0),
            meta_ast_matches(source.text_model(), forms@, entries),
            form_span(forms@[body as int]) == entries[caller.item as int].kind->Defn_0.body_span,
            outcomes.len() == subtree_limit(forms@, body) - body,
            call_entries_fit(forms@, calls@),
            call_trace_fits(calls@, trace@, body, forms@.len()),
            call_inputs_match(aliases, caller.file, caller.item, forms@, body, outcomes, calls@, issues),
            forall|j: int| 0 <= j < edges@.len() ==> {
                let edge = #[trigger] edges@[j];
                &&& edge.from == caller
                &&& edge_projects(&source, forms@, calls@[trace@[j] as int], edge)
                &&& defn_call_edge_matches(aliases, edge)
            },
        decreases trace@.len() - i,
    {
        proof { trace_entry_in_range(calls@, trace@, body, forms@.len(), i as int); }
        let edge = read_call_edge(aliases, caller, forms, calls, trace[i], Ghost(entries),
            Ghost(body), Ghost(outcomes), Ghost(issues));
        edges.push(edge);
        i += 1;
    }
    edges
}

#[verifier::opaque]
spec fn all_slots_projected(
    source: &str, forms: Seq<Form>, caller: DefnPosition, body: usize, outcomes: Seq<CallOutcome>,
    edges: Seq<DefnCallEdge>,
) -> bool {
    forall|at: usize| body <= at < body + outcomes.len()
        && #[trigger] expression_slot(source, forms, body, at) ==> {
        match outcomes[at - body] {
            Some(Ok(PreparedDefnCall::Declared { declaration, .. })) =>
                exists|i: int| 0 <= i < edges.len() && {
                    let edge = #[trigger] edges[i];
                    &&& edge.from == caller
                    &&& edge.at == at
                    &&& edge.to == (DefnPosition { file: declaration.file, item: declaration.item })
                    &&& edge.call.span == form_span(forms[at as int])
                    &&& edge.call.head == form_span(forms[at + 1])
                },
            _ => true,
        }
    }
}

#[verifier::opaque]
spec fn covered_body_slots(
    aliases: &MixedUseAliases, caller: DefnPosition, source: &str, forms: Seq<Form>, header: DefnHeader,
    edges: Seq<DefnCallEdge>,
) -> bool {
    exists|root: usize, body: usize, outcomes: Seq<CallOutcome>, calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>|
        #[trigger] indexed_body_site(source, forms, root, body, header)
            && outcomes.len() == subtree_limit(forms, body) - body
            && #[trigger] call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues)
            && #[trigger] all_slots_projected(source, forms, caller, body, outcomes, edges)
}

/// 呼び出し列が、型検査とは独立に定義した式の位置にある解決済みの宣言呼び出しをすべて含む。
#[verifier::opaque]
pub closed spec fn defn_body_calls_cover_slots(
    aliases: &MixedUseAliases, caller: DefnPosition, edges: Seq<DefnCallEdge>,
) -> bool {
    let project = aliases.targets_model().project_model();
    &&& caller.file < project.sources_model().len()
    &&& match (project.indexed_defn(caller.file, caller.item), project.functional_forms_model(caller.file)) {
        (Some(header), Some(forms)) => {
            let source = project.sources_model()[caller.file as int].text_model();
            covered_body_slots(aliases, caller, source, forms, header, edges)
        }
        _ => false,
    }
}

#[verifier::opaque]
spec fn body_contains_call_slot(source: &str, forms: Seq<Form>, header: DefnHeader, span: Range<usize>) -> bool {
    exists|root: usize, body: usize, at: usize|
        #[trigger] indexed_body_site(source, forms, root, body, header)
            && at < forms.len()
            && #[trigger] expression_slot(source, forms, body, at)
            && span == form_span(forms[at as int])
}

/// 呼び出しの範囲が、指定した補助関数の本体から式としてたどれる位置を指すことを表す。
#[verifier::opaque]
pub closed spec fn defn_call_is_expression_slot(aliases: &MixedUseAliases, edge: DefnCallEdge) -> bool {
    let project = aliases.targets_model().project_model();
    &&& defn_call_edge_matches(aliases, edge)
    &&& edge.from.file < project.sources_model().len()
    &&& match (project.indexed_defn(edge.from.file, edge.from.item), project.functional_forms_model(edge.from.file)) {
        (Some(header), Some(forms)) => {
            let source = project.sources_model()[edge.from.file as int].text_model();
            body_contains_call_slot(source, forms, header, edge.call.span)
        }
        _ => false,
    }
}

proof fn prove_expression_slot_projection(
    aliases: &MixedUseAliases, caller: DefnPosition, forms: Seq<Form>, body: usize,
    outcomes: Seq<CallOutcome>, calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>,
    trace: Seq<usize>, edges: Seq<DefnCallEdge>,
)
    requires
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        calls.len() <= usize::MAX,
        call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues),
        call_trace_covers_slots(aliases.targets_model().project_model().sources_model()[caller.file as int].text_model(),
            forms, calls, trace, body),
        edges.len() == trace.len(),
        forall|i: int| 0 <= i < edges.len() ==> {
            let edge = #[trigger] edges[i];
            edge.from == caller && edge_projects(
                &aliases.targets_model().project_model().sources_model()[caller.file as int],
                forms, calls[trace[i] as int], edge)
        },
    ensures all_slots_projected(aliases.targets_model().project_model().sources_model()[caller.file as int].text_model(),
        forms, caller, body, outcomes, edges),
{
    let source = aliases.targets_model().project_model().sources_model()[caller.file as int].text_model();
    reveal(call_inputs_match);
    reveal(outcomes_recorded);
    reveal(call_trace_covers_slots);
    reveal(all_slots_projected);
    assert forall|at: usize| body <= at < body + outcomes.len()
        && #[trigger] expression_slot(source, forms, body, at) implies {
        match outcomes[at - body] {
            Some(Ok(PreparedDefnCall::Declared { declaration, .. })) =>
                exists|i: int| 0 <= i < edges.len() && {
                    let edge = #[trigger] edges[i];
                    &&& edge.from == caller
                    &&& edge.at == at
                    &&& edge.to == (DefnPosition { file: declaration.file, item: declaration.item })
                    &&& edge.call.span == form_span(forms[at as int])
                    &&& edge.call.head == form_span(forms[at + 1])
                },
            _ => true,
        }
    } by {
        let decoded = outcomes[at - body];
        if let Some(Ok(PreparedDefnCall::Declared { declaration, signature, .. })) = decoded {
            assert(call_shape_at(calls, at, signature));
            let j = choose|j: int| 0 <= j < calls.len() && (#[trigger] calls[j]).at == at
                && call_signature_types_match(calls[j], signature);
            assert(entry_witness(calls[j], outcomes, body));
            assert(calls[j].target == (DefnPosition { file: declaration.file, item: declaration.item })) by {
                reveal(entry_witness);
            };
            assert(trace.contains(j as usize));
            let i = choose|i: int| 0 <= i < trace.len() && (#[trigger] trace[i]) == j as usize;
            assert(edges[i].from == caller);
            assert(edges[i].to == calls[j].target);
        }
    };
}

proof fn finish_expression_slot_coverage(
    aliases: &MixedUseAliases, caller: DefnPosition, source: &str, forms: Seq<Form>,
    root: usize, body: usize, header: DefnHeader, outcomes: Seq<CallOutcome>,
    calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>, edges: Seq<DefnCallEdge>,
)
    requires
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().sources_model()[caller.file as int].text_model() == source,
        aliases.targets_model().project_model().functional_forms_model(caller.file) == Some(forms),
        aliases.targets_model().project_model().indexed_defn(caller.file, caller.item) == Some(header),
        indexed_body_site(source, forms, root, body, header),
        outcomes.len() == subtree_limit(forms, body) - body,
        call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues),
        all_slots_projected(source, forms, caller, body, outcomes, edges),
    ensures defn_body_calls_cover_slots(aliases, caller, edges),
{
    assert(covered_body_slots(aliases, caller, source, forms, header, edges)) by {
        reveal(covered_body_slots);
        assert(indexed_body_site(source, forms, root, body, header));
        assert(all_slots_projected(source, forms, caller, body, outcomes, edges));
        assert(call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues));
    };
    reveal(defn_body_calls_cover_slots);
}

proof fn finish_unvisited_expression_evidence(
    aliases: &MixedUseAliases, caller: DefnPosition, source: &str, forms: Seq<Form>,
    root: usize, body: usize, header: DefnHeader, at: usize, edge: DefnCallEdge,
)
    requires
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().sources_model()[caller.file as int].text_model() == source,
        aliases.targets_model().project_model().functional_forms_model(caller.file) == Some(forms),
        aliases.targets_model().project_model().indexed_defn(caller.file, caller.item) == Some(header),
        indexed_body_site(source, forms, root, body, header),
        at < forms.len(), expression_slot(source, forms, body, at),
        edge.from == caller, edge.call.span == form_span(forms[at as int]),
        defn_call_edge_matches(aliases, edge),
    ensures defn_call_is_expression_slot(aliases, edge),
{
    assert(body_contains_call_slot(source, forms, header, edge.call.span)) by {
        reveal(body_contains_call_slot);
        assert(indexed_body_site(source, forms, root, body, header));
        assert(expression_slot(source, forms, body, at));
        assert(edge.call.span == form_span(forms[at as int]));
    };
    reveal(defn_call_is_expression_slot);
}

fn capture_checked_call_body<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, source: &'a str, forms: &[Form],
    body: usize, calls: &[CallTypeEntry], trace: &[usize],
    Ghost(entries): Ghost<Seq<MetaItem>>, Ghost(root): Ghost<usize>,
    Ghost(outcomes): Ghost<Seq<CallOutcome<'p, 'a>>>, Ghost(issues): Ghost<Seq<CallIssue<'p, 'a>>>,
) -> (result: Result<Vec<DefnCallEdge<'p, 'a>>, DefnCallEdge<'p, 'a>>)
    requires
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().sources_model()[caller.file as int].text_model() == source,
        aliases.targets_model().project_model().functional_forms_model(caller.file) == Some(forms@),
        caller.item < entries.len(), entries[caller.item as int].kind is Defn,
        aliases.targets_model().project_model().indexed_defn(caller.file, caller.item)
            == Some(entries[caller.item as int].kind->Defn_0),
        meta_ast_matches(source, forms@, entries),
        usable_forms(source, forms@), body < forms@.len(),
        indexed_body_site(source, forms@, root, body, entries[caller.item as int].kind->Defn_0),
        outcomes.len() == subtree_limit(forms@, body) - body,
        call_entries_fit(forms@, calls@),
        call_trace_fits(calls@, trace@, body, forms@.len()),
        call_inputs_match(aliases, caller.file, caller.item, forms@, body, outcomes, calls@, issues),
    ensures
        match result {
            Ok(edges) => {
                &&& defn_body_calls_cover_slots(aliases, caller, edges@)
                &&& forall|i: int| 0 <= i < edges@.len() ==> {
                    let edge = #[trigger] edges@[i];
                    edge.from == caller && defn_call_edge_matches(aliases, edge)
                }
            }
            Err(edge) => edge.from == caller && defn_call_is_expression_slot(aliases, edge),
        },
{
    let _count = calls.len();
    if let Some(index) = first_unvisited_expression_entry(source, forms, calls, trace, body) {
        proof { expression_slot_bounds(source, forms@, body, calls@[index as int].at); }
        let edge = read_call_edge(aliases, caller, forms, calls, index, Ghost(entries),
            Ghost(body), Ghost(outcomes), Ghost(issues));
        proof {
            finish_unvisited_expression_evidence(aliases, caller, source, forms@, root, body,
                entries[caller.item as int].kind->Defn_0, calls@[index as int].at, edge);
        }
        Err(edge)
    } else {
        let edges = project_call_trace(aliases, caller, forms, calls, trace, Ghost(entries),
            Ghost(body), Ghost(outcomes), Ghost(issues));
        proof {
            assert forall|j: int| 0 <= j < edges@.len() implies {
                let edge = #[trigger] edges@[j];
                let source = aliases.targets_model().project_model().sources_model()[caller.file as int];
                edge.from == caller && edge_projects(&source, forms@, calls@[trace@[j] as int], edge)
            } by {
                let edge = edges@[j];
                let source = aliases.targets_model().project_model().sources_model()[caller.file as int];
                assert(edge_projects(&source, forms@, calls@[trace@[j] as int], edge));
            };
            prove_expression_slot_projection(aliases, caller, forms@, body, outcomes, calls@, issues, trace@, edges@);
            finish_expression_slot_coverage(aliases, caller, source, forms@, root, body,
                entries[caller.item as int].kind->Defn_0, outcomes, calls@, issues, edges@);
            assert forall|j: int| 0 <= j < edges@.len() implies {
                let edge = #[trigger] edges@[j];
                edge.from == caller && defn_call_edge_matches(aliases, edge)
            } by {};
        }
        Ok(edges)
    }
}

pub(crate) fn check_indexed_call_body<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize, source: &'a str, forms: &[Form],
    entries: &[MetaItem], collect_edges: bool,
) -> (result: (Result<DefnSignature<'a>, DefnBodyCallError<'p, 'a>>, Result<Vec<DefnCallEdge<'p, 'a>>, DefnCallEdge<'p, 'a>>))
    requires
        meta_ast_matches(source, forms@, entries@), meta_binding_spans_valid(source, entries@),
        item < entries@.len(), entries@[item as int].kind is Defn,
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
        aliases.targets_model().project_model().has_source_indexes(),
        file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().sources_model()[file as int].text_model() == source,
        aliases.targets_model().project_model().functional_forms_model(file) == Some(forms@),
        !collect_edges || aliases.targets_model().project_model().indexed_defn(file, item)
            == Some(entries@[item as int].kind->Defn_0),
    ensures indexed_call_body_matches(aliases, file, item, source, forms@, entries@, result.0),
        (!collect_edges || result.0.is_err()) ==> (result.1 matches Ok(edges) && edges@.len() == 0),
        result.1 matches Ok(edges) ==> {
            &&& (collect_edges && result.0.is_ok()) ==>
                defn_body_calls_cover_slots(aliases, DefnPosition { file, item }, edges@)
            &&& forall|i: int| 0 <= i < edges@.len() ==> {
                let edge = #[trigger] edges@[i];
                edge.from == (DefnPosition { file, item }) && defn_call_edge_matches(aliases, edge)
            }
        },
        result.1 matches Err(edge) ==>
            edge.from == (DefnPosition { file, item }) && defn_call_is_expression_slot(aliases, edge),
{
    let MetaItemKind::Defn(header) = &entries[item].kind else { unreachable!() };
    let body = indexed_meta_body(source, forms, entries, item);
    proof { meta_defn_signature_spans(source, entries@, item as int); }
    let signature = read_header_signature(source, header);
    let _size = forms.len();
    let end = subtree_end(forms, body);
    proof {
        assert(body < forms@.len());
        match forms@[body as int] {
            Form::List { end: list_end, .. } => assert(body < list_end == end <= forms@.len()),
            Form::Atom { .. } => assert(end == body + 1 <= forms@.len() <= usize::MAX),
        }
        assert(body <= end <= forms@.len());
    }
    let CallTypingInputs { calls: call_types, issues: mut call_issues, outcomes: Ghost(outcomes) } =
        gather_call_types(aliases, file, item, source, forms, body, end);
    let ghost root = choose|root: usize| #[trigger] indexed_body_site(source, forms@, root, body, *header);
    let expected = shape_of_type(signature.result_type.ty);
    let ghost original_issues = call_issues@;
    let mut trace = if collect_edges { Some(Vec::new()) } else { None };
    let outcome = match check_typed_body_with_calls(&call_types, source, forms, &signature.parameters, body, expected, &mut trace) {
        BodyVerdict::Accepted => Ok(signature),
        BodyVerdict::Rejected(error) => Err(match_body_error(&mut call_issues, error)),
    };
    assert(call_body_outcome(call_types@, original_issues, source, forms@, body, signature, outcome));
    assert(indexed_body_site(source, forms@, root, body, *header));
    assert(call_inputs_match(aliases, file, item, forms@, body, outcomes, call_types@, original_issues));
    let edges = if collect_edges && outcome.is_ok() {
        let recorded: &[usize] = match &trace {
            Some(entries) => entries.as_slice(),
            None => &[],
        };
        assert(recorded@ =~= call_trace_model(trace));
        capture_checked_call_body(aliases, DefnPosition { file, item }, source, forms, body, &call_types,
            recorded, Ghost(entries@), Ghost(root), Ghost(outcomes), Ghost(original_issues))
    } else {
        Ok(Vec::new())
    };
    (outcome, edges)
}

}
