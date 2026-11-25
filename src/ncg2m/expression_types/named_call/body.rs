//! 元の本体と呼び出し先の署名を結び付け、型検査スタックに渡す。

use super::*;
use super::typing::{CallTypeEntry, check_typed_body_with_calls};
#[cfg(verus_only)]
use super::typing::{call_entries_fit, canonical_call, typed_body_with_calls};
use super::named_call::{prepare_call_types, read_call_form};
#[cfg(verus_only)]
use super::named_call::{call_form_matches, call_form_origin, call_signature_types_match, decoded_call_has_arity};
use crate::project::{DefnCallError, MixedUseAliases, PreparedDefnCall};
#[cfg(verus_only)]
use crate::project::{call_arity_matches, mixed_use_targets_match, prepared_call_site};

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
        && (outcomes[entry.at - body] matches Some(Ok(PreparedDefnCall::Declared { signature, .. }))
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
        Some(Ok(PreparedDefnCall::Declared { signature, .. })) =>
            added.len() == calls.len() + 1 && added.take(calls.len() as int) == calls
                && added[calls.len() as int].at == at
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
            Some(Ok(PreparedDefnCall::Declared { site: _site, declaration: _declaration, signature })) => {
                proof {
                    let decoded = form->Some_0;
                    decoded_call_has_arity(source, forms@, at, decoded);
                    assert(decoded.arguments == signature.parameters@.len());
                }
                let _len = signature.parameters.len();
                let entry = prepare_call_types(source, forms, at, &signature);
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
    }
}

pub(crate) fn check_indexed_call_body<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize, source: &'a str, forms: &[Form],
    entries: &[MetaItem],
) -> (result: Result<DefnSignature<'a>, DefnBodyCallError<'p, 'a>>)
    requires
        meta_ast_matches(source, forms@, entries@), meta_binding_spans_valid(source, entries@),
        item < entries@.len(), entries@[item as int].kind is Defn,
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
        aliases.targets_model().project_model().has_source_indexes(),
        file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().sources_model()[file as int].text_model() == source,
        aliases.targets_model().project_model().functional_forms_model(file) == Some(forms@),
    ensures indexed_call_body_matches(aliases, file, item, source, forms@, entries@, result),
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
    let outcome = match check_typed_body_with_calls(&call_types, source, forms, &signature.parameters, body, expected) {
        BodyVerdict::Accepted => Ok(signature),
        BodyVerdict::Rejected(error) => Err(match_body_error(&mut call_issues, error)),
    };
    assert(call_body_outcome(call_types@, original_issues, source, forms@, body, signature, outcome));
    assert(indexed_body_site(source, forms@, root, body, *header));
    assert(call_inputs_match(aliases, file, item, forms@, body, outcomes, call_types@, original_issues));
    outcome
}

}
