//! 元の本体と呼び出し先の署名を結び付け、型検査スタックに渡す。

use super::*;
use super::typing::{CallTypeEntry, CallTypeTarget, check_typed_body_with_calls};
use crate::ncg2m::integers::IntegerOperation;
#[cfg(verus_only)]
use super::typing::{arithmetic_trace_fits, widen_arithmetic_trace, call_entries_fit, call_trace_fits, call_trace_model,
    trace_entry_in_range, canonical_call, typed_body_with_calls};
use super::named_call::{prepare_call_types, read_call_form};
#[cfg(verus_only)]
use super::named_call::{call_form_matches, call_form_origin, call_signature_types_match, decoded_call_has_arity};
use crate::project::{DefnCallEdge, DefnCallError, DefnCallGraphError, DefnCallSite,
    MixedUseAliases, PreparedDefnCall, TypedArithmeticSite};
#[cfg(verus_only)]
use crate::project::{ProjectDeclaration, ProjectSource, ResolvedDefnName, arithmetic_sites_fit, call_arity_matches, defn_name_resolution,
    mixed_use_targets_match, prepared_call_site, resolved_defn_name_origin};
#[cfg(verus_only)]
use crate::ncg2m::defn::DefnHeader;
#[cfg(verus_only)]
use crate::syntax::{preorder_range_pair, strict_preorder_ranges};

mod coverage;
#[cfg(verus_only)]
mod typed_sites;
#[cfg(verus_only)]
pub(crate) use typed_sites::{CheckedNamedTarget, checked_atom_uses_only_parameters, checked_body_scalar_position,
    recorded_edge_has_call_syntax, defn_checked_call_arguments, defn_checked_call_target,
    defn_checked_expression_site, defn_checked_if_child_sites, defn_checked_site_at_body_root};
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

spec fn outcome_has_entry(outcome: CallOutcome) -> bool {
    outcome matches Some(Ok(PreparedDefnCall::Declared { .. } | PreparedDefnCall::Arithmetic { .. }))
}

spec fn entry_represents(entry: CallTypeEntry, outcome: CallOutcome) -> bool {
    match outcome {
        Some(Ok(PreparedDefnCall::Declared { declaration, signature, .. })) =>
            entry.target == CallTypeTarget::Declared(DefnPosition { file: declaration.file, item: declaration.item })
                && call_signature_types_match(entry, signature),
        Some(Ok(PreparedDefnCall::Arithmetic { operation, arguments, .. })) =>
            entry.target == CallTypeTarget::Arithmetic(operation)
                && entry.arguments@.len() == 2
                && entry.arguments@[0].at == arguments.0
                && entry.arguments@[1].at == arguments.1,
        _ => false,
    }
}

spec fn call_shape_at(calls: Seq<CallTypeEntry>, at: usize, outcome: CallOutcome) -> bool {
    exists|i: int| 0 <= i < calls.len() && (#[trigger] calls[i]).at == at
        && entry_represents(calls[i], outcome)
}

spec fn issue_at(issues: Seq<CallIssue>, at: usize, error: DefnCallError) -> bool {
    exists|i: int| 0 <= i < issues.len() && (#[trigger] issues[i]).at@ == at && issues[i].error == error
}

#[verifier::opaque]
spec fn entry_witness(entry: CallTypeEntry, outcomes: Seq<CallOutcome>, body: usize) -> bool {
    body <= entry.at < body + outcomes.len()
        && entry_represents(entry, outcomes[entry.at - body])
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
        &&& (outcome_has_entry(result) ==> call_shape_at(calls, (body + i) as usize, result))
        &&& (result matches Some(Err(error)) ==> issue_at(issues, (body + i) as usize, error))
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
    if outcome_has_entry(outcome) {
        let next = added[calls.len() as int];
        added.len() == calls.len() + 1 && added.take(calls.len() as int) == calls
            && next.at == at && canonical_call(forms, next) && entry_represents(next, outcome)
    } else {
        added == calls
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
    if outcome_has_entry(outcome) {
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
        &&& (outcome_has_entry(result) ==> call_shape_at(next_calls, (body + i) as usize, result))
        &&& (result matches Some(Err(error)) ==> issue_at(next_issues, (body + i) as usize, error))
    } by {
        if i < outcomes.len() {
            assert(prefix[i] == outcomes[i]);
            if outcome_has_entry(outcomes[i]) {
                let j = choose|j: int| 0 <= j < calls.len() && (#[trigger] calls[j]).at == body + i
                    && entry_represents(calls[j], outcomes[i]);
                assert(next_calls[j] == calls[j]);
            }
            if let Some(Err(error)) = outcomes[i] {
                let j = choose|j: int| 0 <= j < issues.len() && (#[trigger] issues[j]).at@ == body + i && issues[j].error == error;
                assert(next_issues[j] == issues[j]);
            }
        } else {
            assert(prefix[i] == outcome);
            if outcome_has_entry(outcome) {
                let j = calls.len() as int;
                assert(next_calls[j].at == body + i && entry_represents(next_calls[j], outcome));
                assert(call_shape_at(next_calls, (body + i) as usize, outcome));
            }
            if let Some(Err(error)) = outcome {
                let j = issues.len() as int;
                assert(next_issues[j].at@ == body + i && next_issues[j].error == error);
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

fn arithmetic_type_entry(
    at: usize, operation: IntegerOperation, arguments: (usize, usize), Ghost(forms): Ghost<Seq<Form>>,
) -> (entry: CallTypeEntry)
    requires defn_call_arguments(forms, at, seq![arguments.0, arguments.1]),
    ensures
        canonical_call(forms, entry), entry.at == at,
        entry.target == CallTypeTarget::Arithmetic(operation),
        entry.arguments@.len() == 2,
        entry.arguments@[0].at == arguments.0 && entry.arguments@[1].at == arguments.1,
{
    let left = arguments.0;
    let right = arguments.1;
    let _context = TypeShape { builtin: None, list_depth: 0 };
    let mut slots = Vec::new();
    slots.push(super::typing::CallArgument { at: left, expected: _context });
    slots.push(super::typing::CallArgument { at: right, expected: _context });
    proof {
        let operands = seq![left, right];
        call_argument_intervals(forms, at, operands, 0);
        call_argument_intervals(forms, at, operands, 1);
    }
    CallTypeEntry { at, target: CallTypeTarget::Arithmetic(operation), arguments: slots, result: _context }
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
            Some(Ok(PreparedDefnCall::Arithmetic { operation, arguments, .. })) => {
                proof {
                    let decoded = form->Some_0;
                    call_form_origin(source, forms@, at, decoded);
                    assert(decoded.binary_arguments == Some(arguments));
                }
                let entry = arithmetic_type_entry(at, operation, arguments, Ghost(forms@));
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

pub(super) proof fn call_arguments_from_intervals(
    forms: Seq<Form>, owner: usize, arguments: Seq<usize>,
)
    requires
        owner < forms.len(), forms[owner as int] is List,
        owner + 2 <= subtree_limit(forms, owner) <= forms.len(),
        if arguments.len() == 0 { owner + 2 == subtree_limit(forms, owner) } else { arguments[0] == owner + 2 },
        forall|i: int| 0 <= i < arguments.len() ==> {
            let child = #[trigger] arguments[i];
            &&& owner < child < subtree_limit(forms, child) <= subtree_limit(forms, owner)
            &&& if i + 1 < arguments.len() { subtree_limit(forms, child) == arguments[i + 1] }
                else { subtree_limit(forms, child) == subtree_limit(forms, owner) }
        },
    ensures defn_call_arguments(forms, owner, arguments),
{}

pub(super) proof fn call_argument_intervals(
    forms: Seq<Form>, owner: usize, arguments: Seq<usize>, index: int,
)
    requires defn_call_arguments(forms, owner, arguments),
    ensures
        owner + 2 <= subtree_limit(forms, owner) <= forms.len(),
        arguments.len() == 0 ==> owner + 2 == subtree_limit(forms, owner),
        arguments.len() > 0 ==> arguments[0] == owner + 2,
        0 <= index < arguments.len() ==> {
            let child = arguments[index];
            &&& owner < child < subtree_limit(forms, child) <= subtree_limit(forms, owner)
            &&& if index + 1 < arguments.len() { subtree_limit(forms, child) == arguments[index + 1] }
                else { subtree_limit(forms, child) == subtree_limit(forms, owner) }
        },
{}

proof fn argument_position_agrees(forms: Seq<Form>, at: usize, first: Seq<usize>, second: Seq<usize>, slot: int)
    requires
        defn_call_arguments(forms, at, first), defn_call_arguments(forms, at, second),
        0 <= slot < first.len() && slot < second.len(),
    ensures first[slot] == second[slot],
    decreases slot,
{
    if slot > 0 {
        argument_position_agrees(forms, at, first, second, slot - 1);
        assert(subtree_limit(forms, first[slot - 1]) == first[slot]);
        assert(subtree_limit(forms, second[slot - 1]) == second[slot]);
    }
}

pub(super) proof fn call_argument_positions_are_unique(
    forms: Seq<Form>, at: usize, first: Seq<usize>, second: Seq<usize>,
)
    requires defn_call_arguments(forms, at, first), defn_call_arguments(forms, at, second),
    ensures first == second,
{
    if first.len() == 0 {
        if second.len() > 0 {
            assert(at < second[0] < subtree_limit(forms, second[0]) <= subtree_limit(forms, at));
        }
    } else if second.len() == 0 {
        assert(at < first[0] < subtree_limit(forms, first[0]) <= subtree_limit(forms, at));
    } else if first.len() < second.len() {
        let last = first.len() - 1;
        argument_position_agrees(forms, at, first, second, last);
        assert(subtree_limit(forms, first[last]) == subtree_limit(forms, at));
        assert(subtree_limit(forms, second[last]) == second[last + 1]);
        assert(second[last + 1] < subtree_limit(forms, second[last + 1]) <= subtree_limit(forms, at));
    } else if second.len() < first.len() {
        let last = second.len() - 1;
        argument_position_agrees(forms, at, first, second, last);
        assert(subtree_limit(forms, second[last]) == subtree_limit(forms, at));
        assert(subtree_limit(forms, first[last]) == first[last + 1]);
        assert(first[last + 1] < subtree_limit(forms, first[last + 1]) <= subtree_limit(forms, at));
    }
    assert(first =~= second) by {
        assert forall|slot: int| 0 <= slot < first.len() implies #[trigger] first[slot] == #[trigger] second[slot] by {
            argument_position_agrees(forms, at, first, second, slot);
        };
    };
}

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
        &&& conditional_positions(edge.call.source.text_model(), forms, at).is_none()
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
    &&& entry.target == CallTypeTarget::Declared(edge.to)
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
        conditional_positions(edge.call.source.text_model(), forms, at).is_none(),
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
        index < calls.len(), calls[index as int].target is Declared,
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues),
    ensures
        body <= calls[index as int].at < body + outcomes.len(),
        call_form_matches(aliases.targets_model().project_model().sources_model()[caller.file as int].text_model(),
            forms, calls[index as int].at, Some(evidence.0)),
        defn_name_resolution(aliases, caller.file, caller.item, evidence.0.word,
            Ok(ResolvedDefnName::Declaration(evidence.1))),
        calls[index as int].target == CallTypeTarget::Declared(DefnPosition { file: evidence.1.file, item: evidence.1.item }),
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
        && entry.target == CallTypeTarget::Declared(DefnPosition { file: declaration.file, item: declaration.item })) by {
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
    super::named_call::declared_head_is_deferred_by_local_typing(src, forms, at, form);
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
        row < calls@.len(), calls@[row as int].target is Declared,
        body <= calls@[row as int].at < forms@.len(),
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
    let CallTypeTarget::Declared(to) = entry.target else { unreachable!() };
    let edge = DefnCallEdge { from: caller, at, arguments, call, to };
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

spec fn edges_project_trace(
    source: &ProjectSource, forms: Seq<Form>, calls: Seq<CallTypeEntry>, trace: Seq<usize>, edges: Seq<DefnCallEdge>,
) -> bool {
    &&& edges.len() == trace.len()
    &&& forall|i: int| 0 <= i < edges.len() ==>
        edge_projects(source, forms, calls[trace[i] as int], #[trigger] edges[i])
}

type CallTypingSnapshot<'p, 'a> = (
    usize, usize, DefnSignature<'a>, Seq<CallOutcome<'p, 'a>>, Seq<CallTypeEntry>,
    Seq<CallIssue<'p, 'a>>, Seq<usize>,
);

#[verifier::opaque]
spec fn all_arithmetic_slots_projected(
    source: &str, forms: Seq<Form>, body: usize, outcomes: Seq<CallOutcome>,
    arithmetic: Seq<TypedArithmeticSite>,
) -> bool {
    &&& forall|at: usize| body <= at < body + outcomes.len()
        && #[trigger] expression_slot(source, forms, body, at) ==> {
        outcomes[at - body] matches Some(Ok(PreparedDefnCall::Arithmetic { operation, arguments, .. }))
            ==> arithmetic.contains(TypedArithmeticSite { at, arguments, operation })
    }
    &&& forall|i: int| 0 <= i < arithmetic.len() ==> {
        let site = #[trigger] arithmetic[i];
        &&& body <= site.at < body + outcomes.len()
        &&& outcomes[site.at - body] matches Some(Ok(PreparedDefnCall::Arithmetic { operation, arguments, .. }))
            && site.operation == operation && site.arguments == arguments
    }
}

spec fn call_typing_snapshot_matches<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, source: &'a str,
    forms: Seq<Form>, header: DefnHeader, edges: Seq<DefnCallEdge<'p, 'a>>,
    arithmetic: Option<Seq<TypedArithmeticSite>>, snapshot: CallTypingSnapshot<'p, 'a>,
) -> bool {
    let document = aliases.targets_model().project_model().sources_model()[caller.file as int];
    let (root, body, signature, outcomes, calls, issues, trace) = snapshot;
    &&& usable_forms(source, forms) && forms.len() <= usize::MAX
    &&& indexed_body_site(source, forms, root, body, header)
    &&& signature_matches_header(source, header, signature)
    &&& outcomes.len() == subtree_limit(forms, body) - body
    &&& call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues)
    &&& call_body_outcome(calls, issues, source, forms, body, signature, Ok(signature))
    &&& call_trace_fits(calls, trace, body, forms.len())
    &&& edges_project_trace(&document, forms, calls, trace, edges)
    &&& all_slots_projected(source, forms, caller, body, outcomes, edges)
    &&& arithmetic matches Some(sites) ==> all_arithmetic_slots_projected(source, forms, body, outcomes, sites)
}

#[verifier::opaque]
spec fn covered_body_slots<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, source: &'a str, forms: Seq<Form>, header: DefnHeader,
    edges: Seq<DefnCallEdge<'p, 'a>>, arithmetic: Option<Seq<TypedArithmeticSite>>,
) -> bool {
    exists|snapshot: CallTypingSnapshot<'p, 'a>|
        #[trigger] call_typing_snapshot_matches(aliases, caller, source, forms, header, edges, arithmetic, snapshot)
}

spec fn recorded_call_typing<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, edges: Seq<DefnCallEdge<'p, 'a>>,
    arithmetic: Option<Seq<TypedArithmeticSite>>,
) -> CallTypingSnapshot<'p, 'a> {
    let project = aliases.targets_model().project_model();
    let source = project.sources_model()[caller.file as int].text_model();
    let forms = project.functional_forms_model(caller.file)->Some_0;
    let header = project.indexed_defn(caller.file, caller.item)->Some_0;
    choose|snapshot: CallTypingSnapshot<'p, 'a>|
        #[trigger] call_typing_snapshot_matches(aliases, caller, source, forms, header, edges, arithmetic, snapshot)
}

proof fn recorded_call_typing_matches<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, edges: Seq<DefnCallEdge<'p, 'a>>,
    arithmetic: Option<Seq<TypedArithmeticSite>>,
)
    requires match arithmetic {
        Some(sites) => defn_body_sites_cover_slots(aliases, caller, edges, sites),
        None => defn_body_calls_cover_slots(aliases, caller, edges),
    },
    ensures {
        let project = aliases.targets_model().project_model();
        &&& caller.file < project.sources_model().len()
        &&& project.functional_forms_model(caller.file) matches Some(forms)
        &&& project.indexed_defn(caller.file, caller.item) matches Some(header)
        &&& call_typing_snapshot_matches(aliases, caller, project.sources_model()[caller.file as int].text_model(),
            forms, header, edges, arithmetic, recorded_call_typing(aliases, caller, edges, arithmetic))
    },
{
    reveal(defn_body_calls_cover_slots);
    reveal(defn_body_sites_cover_slots);
    reveal(covered_body_slots);
}

/// 呼び出し列が、型検査とは独立に定義した式の位置にある解決済みの宣言呼び出しをすべて含む。
///
/// 各辺は、同じ本体の型検査で使った署名と、実際に検査した呼び出しの記録に対応する。
#[verifier::opaque]
pub closed spec fn defn_body_calls_cover_slots(
    aliases: &MixedUseAliases, caller: DefnPosition, edges: Seq<DefnCallEdge>,
) -> bool {
    let project = aliases.targets_model().project_model();
    &&& caller.file < project.sources_model().len()
    &&& match (project.indexed_defn(caller.file, caller.item), project.functional_forms_model(caller.file)) {
        (Some(header), Some(forms)) => {
            let source = project.sources_model()[caller.file as int].text_model();
            covered_body_slots(aliases, caller, source, forms, header, edges, None)
        }
        _ => false,
    }
}

/// 宣言と算術の両方が、同じ本体の型検査と元の式の位置に対応する。
#[verifier::opaque]
pub(crate) closed spec fn defn_body_sites_cover_slots(
    aliases: &MixedUseAliases, caller: DefnPosition, edges: Seq<DefnCallEdge>, arithmetic: Seq<TypedArithmeticSite>,
) -> bool {
    let project = aliases.targets_model().project_model();
    &&& caller.file < project.sources_model().len()
    &&& match (project.indexed_defn(caller.file, caller.item), project.functional_forms_model(caller.file)) {
        (Some(header), Some(forms)) => covered_body_slots(
            aliases, caller, project.sources_model()[caller.file as int].text_model(), forms, header, edges,
            Some(arithmetic)),
        _ => false,
    }
}

// 同じ型検査の記録から、根の呼び出しとその引数の型を取り出す。
pub(crate) proof fn defn_root_call_preserves_scalar_types<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, row: Seq<DefnCallEdge<'p, 'a>>,
    arithmetic: Seq<TypedArithmeticSite>, site: usize,
    body: crate::ncg2m::call_evaluation::DefnEvaluationBody<'p, 'a>,
    callee: crate::ncg2m::call_evaluation::DefnEvaluationBody<'p, 'a>,
)
    requires
        defn_body_sites_cover_slots(aliases, caller, row, arithmetic), site < row.len(), row[site as int].at == body.at,
        {
            let project = aliases.targets_model().project_model();
            let to = row[site as int].to;
            &&& caller.file < project.sources_model().len()
            &&& to.file < project.sources_model().len()
            &&& *body.source == project.sources_model()[caller.file as int]
            &&& *callee.source == project.sources_model()[to.file as int]
            &&& project.functional_forms_model(caller.file) == Some(body.forms@)
            &&& project.defn_signature_matches_index(caller.file, caller.item, Some(body.signature))
            &&& project.defn_signature_matches_index(to.file, to.item, Some(callee.signature))
        },
        body.at < body.forms@.len(), form_span(body.forms@[body.at as int]) == body.signature.body_span,
        crate::ncg2m::file::retained_forms_in_source_order(body.forms@),
        body.signature.result_type.ty.list_depth == 0,
        body.signature.result_type.ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)),
    ensures
        body.signature.result_type.ty == callee.signature.result_type.ty,
        row[site as int].arguments@.len() == callee.signature.parameters@.len(),
        forall|slot: int| 0 <= slot < row[site as int].arguments@.len() ==> {
            let at = #[trigger] row[site as int].arguments@[slot];
            let ty = callee.signature.parameters@[slot].ty.ty;
            &&& at < body.forms@.len()
            &&& (local_scalar_fragment(body.source.text_model(), body.forms@, at) && ty.list_depth == 0
                && (ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_)))
                ==> local_scalar_site_is_typed(body.source.text_model(), body.forms@, body.signature.parameters@, at, ty))
        },
{
    defn_checked_site_at_body_root(aliases, caller, row, arithmetic, body);
    typed_sites::defn_checked_call_arguments(aliases, caller, row, arithmetic, site, body, body.signature.result_type.ty, callee);
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
            forms, calls, trace, body, false),
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
            assert(call_shape_at(calls, at, decoded));
            let j = choose|j: int| 0 <= j < calls.len() && (#[trigger] calls[j]).at == at
                && entry_represents(calls[j], decoded);
            assert(entry_witness(calls[j], outcomes, body));
            assert(calls[j].target == CallTypeTarget::Declared(DefnPosition { file: declaration.file, item: declaration.item })) by {
                reveal(entry_witness);
            };
            assert(trace.contains(j as usize));
            let i = choose|i: int| 0 <= i < trace.len() && (#[trigger] trace[i]) == j as usize;
            assert(edges[i].from == caller);
            assert(calls[j].target == CallTypeTarget::Declared(edges[i].to));
        }
    };
}

proof fn finish_expression_slot_coverage(
    aliases: &MixedUseAliases, caller: DefnPosition, source: &str, forms: Seq<Form>,
    root: usize, body: usize, header: DefnHeader, outcomes: Seq<CallOutcome>,
    calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>, edges: Seq<DefnCallEdge>,
    signature: DefnSignature, trace: Seq<usize>, arithmetic: Option<Seq<TypedArithmeticSite>>,
)
    requires
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        aliases.targets_model().project_model().sources_model()[caller.file as int].text_model() == source,
        aliases.targets_model().project_model().functional_forms_model(caller.file) == Some(forms),
        aliases.targets_model().project_model().indexed_defn(caller.file, caller.item) == Some(header),
        usable_forms(source, forms), forms.len() <= usize::MAX,
        indexed_body_site(source, forms, root, body, header),
        outcomes.len() == subtree_limit(forms, body) - body,
        call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues),
        all_slots_projected(source, forms, caller, body, outcomes, edges),
        signature_matches_header(source, header, signature),
        call_body_outcome(calls, issues, source, forms, body, signature, Ok(signature)),
        call_trace_fits(calls, trace, body, forms.len()),
        edges_project_trace(&aliases.targets_model().project_model().sources_model()[caller.file as int],
            forms, calls, trace, edges),
        arithmetic matches Some(sites) ==> all_arithmetic_slots_projected(source, forms, body, outcomes, sites),
    ensures match arithmetic {
        Some(sites) => defn_body_sites_cover_slots(aliases, caller, edges, sites),
        None => defn_body_calls_cover_slots(aliases, caller, edges),
    },
{
    assert(covered_body_slots(aliases, caller, source, forms, header, edges, arithmetic)) by {
        reveal(covered_body_slots);
        let snapshot = (root, body, signature, outcomes, calls, issues, trace);
        assert(call_typing_snapshot_matches(aliases, caller, source, forms, header, edges, arithmetic, snapshot));
    };
    reveal(defn_body_calls_cover_slots);
    reveal(defn_body_sites_cover_slots);
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
    Ghost(entries): Ghost<Seq<MetaItem>>, Ghost(root): Ghost<usize>, Ghost(signature): Ghost<DefnSignature<'a>>,
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
        usable_forms(source, forms@), body < forms@.len() <= usize::MAX,
        indexed_body_site(source, forms@, root, body, entries[caller.item as int].kind->Defn_0),
        outcomes.len() == subtree_limit(forms@, body) - body,
        call_entries_fit(forms@, calls@),
        call_trace_fits(calls@, trace@, body, forms@.len()),
        signature_matches_header(source, entries[caller.item as int].kind->Defn_0, signature),
        call_body_outcome(calls@, issues, source, forms@, body, signature, Ok(signature)),
        call_inputs_match(aliases, caller.file, caller.item, forms@, body, outcomes, calls@, issues),
    ensures
        match result {
            Ok(edges) => {
                &&& defn_body_calls_cover_slots(aliases, caller, edges@)
                &&& all_slots_projected(source, forms@, caller, body, outcomes, edges@)
                &&& edges_project_trace(&aliases.targets_model().project_model().sources_model()[caller.file as int],
                    forms@, calls@, trace@, edges@)
                &&& forall|i: int| 0 <= i < edges@.len() ==> {
                    let edge = #[trigger] edges@[i];
                    edge.from == caller && defn_call_edge_matches(aliases, edge)
                }
            }
            Err(edge) => edge.from == caller && defn_call_is_expression_slot(aliases, edge),
        },
{
    let _count = calls.len();
    if let Some(index) = first_unvisited_expression_entry(source, forms, calls, trace, body, false) {
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
            let document = aliases.targets_model().project_model().sources_model()[caller.file as int];
            assert(edges_project_trace(&document, forms@, calls@, trace@, edges@));
            prove_expression_slot_projection(aliases, caller, forms@, body, outcomes, calls@, issues, trace@, edges@);
            finish_expression_slot_coverage(aliases, caller, source, forms@, root, body,
                entries[caller.item as int].kind->Defn_0, outcomes, calls@, issues, edges@, signature, trace@, None);
            assert forall|j: int| 0 <= j < edges@.len() implies {
                let edge = #[trigger] edges@[j];
                edge.from == caller && defn_call_edge_matches(aliases, edge)
            } by {};
        }
        Ok(edges)
    }
}

spec fn arithmetic_origin(calls: Seq<CallTypeEntry>, visit: usize) -> TypedArithmeticSite {
    let entry = calls[visit as int];
    TypedArithmeticSite {
        at: entry.at,
        arguments: (entry.arguments@[0].at, entry.arguments@[1].at),
        operation: entry.target->Arithmetic_0,
    }
}

/// 診断に含まれる演算の範囲と文書が、呼び出し元の本体の構文位置に対応することを表す。
pub closed spec fn unvisited_arithmetic_at_source(
    aliases: &MixedUseAliases, caller: DefnPosition, at: usize, site: DefnCallSite,
) -> bool {
    let project = aliases.targets_model().project_model();
    &&& caller.file < project.sources_model().len()
    &&& *site.source == project.sources_model()[caller.file as int]
    &&& project.functional_forms_model(caller.file) matches Some(forms)
        && project.indexed_defn(caller.file, caller.item) matches Some(header) && {
            &&& at + 1 < forms.len()
            &&& forms[at as int] is List && forms[at + 1] is Atom
            &&& site.span == form_span(forms[at as int]) && site.head == form_span(forms[at + 1])
            &&& header.body_span.start <= site.span.start <= site.span.end <= header.body_span.end
            &&& body_contains_call_slot(site.source.text_model(), forms, header, site.span)
        }
}

fn capture_arithmetic_sites(calls: &[CallTypeEntry], trace: &[usize], Ghost(forms): Ghost<Seq<Form>>)
    -> (sites: Vec<TypedArithmeticSite>)
    requires call_entries_fit(forms, calls@), arithmetic_trace_fits(calls@, trace@, 0, forms.len()),
    ensures sites@ == trace@.map_values(|visit: usize| arithmetic_origin(calls@, visit)),
        arithmetic_sites_fit(forms, sites@),
{
    reveal(arithmetic_trace_fits);
    let mut sites = Vec::<TypedArithmeticSite>::new();
    let mut next = 0;
    while next < trace.len()
        invariant
            call_entries_fit(forms, calls@),
            arithmetic_trace_fits(calls@, trace@, 0, forms.len()),
            next <= trace@.len(),
            sites@ == trace@.take(next as int).map_values(|visit: usize| arithmetic_origin(calls@, visit)),
        decreases trace@.len() - next,
    {
        let visit = trace[next];
        proof {
            reveal(arithmetic_trace_fits);
            assert(visit < calls@.len() && calls@[visit as int].target is Arithmetic);
        }
        let call = &calls[visit];
        let CallTypeTarget::Arithmetic(operation) = call.target else { unreachable!() };
        assert(canonical_call(forms, *call));
        sites.push(TypedArithmeticSite {
            at: call.at,
            arguments: (call.arguments[0].at, call.arguments[1].at),
            operation,
        });
        proof {
            let prefix = trace@.take(next as int);
            let grown = trace@.take(next as int + 1);
            assert(grown =~= prefix.push(visit));
            assert(grown.map_values(|item: usize| arithmetic_origin(calls@, item)) =~= sites@);
        }
        next += 1;
    }
    assert(trace@.take(next as int) =~= trace@);
    proof {
        assert forall|i: int| 0 <= i < sites@.len() implies {
            let site = #[trigger] sites@[i];
            defn_call_arguments(forms, site.at, seq![site.arguments.0, site.arguments.1])
        } by {
            let entry = calls@[trace@[i] as int];
            assert(canonical_call(forms, entry));
            let site = arithmetic_origin(calls@, trace@[i]);
            let arguments = seq![site.arguments.0, site.arguments.1];
            let end = subtree_limit(forms, entry.at);
            assert forall|j: int| 0 <= j < arguments.len() implies {
                let child = #[trigger] arguments[j];
                &&& entry.at + 2 <= child < subtree_limit(forms, child) <= end
                &&& if j + 1 < arguments.len() { subtree_limit(forms, child) == arguments[j + 1] }
                    else { subtree_limit(forms, child) == end }
            } by {
                assert(arguments[j] == entry.arguments@[j].at);
                if j == 0 { assert(arguments[1] == entry.arguments@[1].at); }
            };
            call_arguments_from_intervals(forms, entry.at, arguments);
        };
        assert forall|i: int, j: int| 0 <= i < j < sites@.len()
            implies (#[trigger] sites@[i]).at < (#[trigger] sites@[j]).at by {
            assert(sites@[i].at == calls@[trace@[i] as int].at);
            assert(sites@[j].at == calls@[trace@[j] as int].at);
        };
    }
    sites
}

proof fn recorded_arithmetic_entry(
    aliases: &MixedUseAliases, caller: DefnPosition, forms: Seq<Form>, body: usize,
    outcomes: Seq<CallOutcome>, calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>,
    at: usize, site: TypedArithmeticSite,
) -> (visit: usize)
    requires
        calls.len() <= usize::MAX,
        call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues),
        body <= at < body + outcomes.len(),
        outcomes[at - body] matches Some(Ok(PreparedDefnCall::Arithmetic { operation, arguments, .. }))
            && site == (TypedArithmeticSite { at, arguments, operation }),
    ensures visit < calls.len(), calls[visit as int].at == at,
        calls[visit as int].target is Arithmetic, arithmetic_origin(calls, visit) == site,
{
    let outcome = outcomes[at - body];
    assert(call_shape_at(calls, at, outcome)) by {
        reveal(call_inputs_match);
        reveal(outcomes_recorded);
    };
    let i = choose|i: int| 0 <= i < calls.len() && (#[trigger] calls[i]).at == at
        && entry_represents(calls[i], outcome);
    let visit = i as usize;
    assert(visit as int == i);
    visit
}

#[verifier::spinoff_prover]
proof fn prove_arithmetic_slot_projection(
    aliases: &MixedUseAliases, caller: DefnPosition, forms: Seq<Form>, body: usize,
    outcomes: Seq<CallOutcome>, calls: Seq<CallTypeEntry>, issues: Seq<CallIssue>,
    trace: Seq<usize>, arithmetic: Seq<TypedArithmeticSite>,
)
    requires
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        calls.len() <= usize::MAX,
        call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues),
        arithmetic_trace_fits(calls, trace, body, forms.len()),
        call_trace_covers_slots(aliases.targets_model().project_model().sources_model()[caller.file as int].text_model(),
            forms, calls, trace, body, true),
        arithmetic == trace.map_values(|row: usize| arithmetic_origin(calls, row)),
    ensures all_arithmetic_slots_projected(
        aliases.targets_model().project_model().sources_model()[caller.file as int].text_model(),
        forms, body, outcomes, arithmetic),
{
    reveal(all_arithmetic_slots_projected);
    let source = aliases.targets_model().project_model().sources_model()[caller.file as int].text_model();
    assert forall|at: usize| body <= at < body + outcomes.len()
        && #[trigger] expression_slot(source, forms, body, at) implies {
        outcomes[at - body] matches Some(Ok(PreparedDefnCall::Arithmetic { operation, arguments, .. }))
            ==> arithmetic.contains(TypedArithmeticSite { at, arguments, operation })
    } by {
        let outcome = outcomes[at - body];
        if let Some(Ok(PreparedDefnCall::Arithmetic { operation, arguments, .. })) = outcome {
            let site = TypedArithmeticSite { at, arguments, operation };
            let visit = recorded_arithmetic_entry(aliases, caller, forms, body, outcomes, calls, issues, at, site);
            assert(trace.contains(visit)) by {
                reveal(call_trace_covers_slots);
                assert(expression_slot(source, forms, body, calls[visit as int].at));
            };
            let i = choose|i: int| 0 <= i < trace.len() && (#[trigger] trace[i]) == visit;
            assert(arithmetic[i] == site);
        }
    };
    assert forall|i: int| 0 <= i < arithmetic.len() implies {
        let site = #[trigger] arithmetic[i];
        &&& body <= site.at < body + outcomes.len()
        &&& outcomes[site.at - body] matches Some(Ok(PreparedDefnCall::Arithmetic { operation, arguments, .. }))
            && site.operation == operation && site.arguments == arguments
    } by {
        reveal(arithmetic_trace_fits);
        let entry = calls[trace[i] as int];
        assert(entry_witness(entry, outcomes, body)) by { reveal(call_inputs_match); };
        reveal(entry_witness);
        assert(arithmetic[i] == arithmetic_origin(calls, trace[i]));
    };
}

pub(crate) fn check_indexed_call_body<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, file: usize, item: usize, source: &'a str, forms: &[Form],
    entries: &[MetaItem], collect_edges: bool,
) -> (result: (Result<DefnSignature<'a>, DefnBodyCallError<'p, 'a>>,
    Result<Vec<DefnCallEdge<'p, 'a>>, DefnCallGraphError<'p, 'a>>, Vec<TypedArithmeticSite>))
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
        (!collect_edges || result.0.is_err()) ==> result.2@.len() == 0,
        arithmetic_sites_fit(forms@, result.2@),
        result.1 matches Ok(edges) ==> {
            &&& (collect_edges && result.0.is_ok()) ==>
                defn_body_calls_cover_slots(aliases, DefnPosition { file, item }, edges@)
                    && defn_body_sites_cover_slots(aliases, DefnPosition { file, item }, edges@, result.2@)
            &&& forall|i: int| 0 <= i < edges@.len() ==> {
                let edge = #[trigger] edges@[i];
                edge.from == (DefnPosition { file, item }) && defn_call_edge_matches(aliases, edge)
            }
        },
        match result.1 {
            Err(DefnCallGraphError::UnvisitedCall(edge)) =>
                edge.from == (DefnPosition { file, item }) && defn_call_is_expression_slot(aliases, edge),
            Err(DefnCallGraphError::UnvisitedArithmetic { from, at, site }) =>
                from == (DefnPosition { file, item }) && unvisited_arithmetic_at_source(aliases, from, at, site),
            Ok(_) => true,
            _ => false,
        },
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
    let mut arithmetic = if collect_edges { Some(Vec::new()) } else { None };
    let outcome = match check_typed_body_with_calls(
        &call_types, source, forms, &signature.parameters, body, expected, &mut trace, &mut arithmetic,
    ) {
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
        assert(outcome == Ok(signature) && forms@.len() <= usize::MAX);
        match capture_checked_call_body(aliases, DefnPosition { file, item }, source, forms, body, &call_types,
            recorded, Ghost(entries@), Ghost(root), Ghost(signature), Ghost(outcomes), Ghost(original_issues))
        {
            Ok(edges) => Ok(edges),
            Err(edge) => Err(DefnCallGraphError::UnvisitedCall(edge)),
        }
    } else {
        Ok(Vec::new())
    };
    let sites = if collect_edges && outcome.is_ok() {
        match arithmetic.as_ref() {
            Some(visits) => {
                proof { widen_arithmetic_trace(call_types@, visits@, body, forms@.len(), 0, forms@.len()); }
                if let Some(index) = first_unvisited_expression_entry(
                    source, forms, &call_types, visits.as_slice(), body, true,
                ) {
                    let at = call_types[index].at;
                    let from = DefnPosition { file, item };
                    let origin = &aliases.targets().project().sources()[file];
                    assert(canonical_call(forms@, call_types@[index as int]));
                    let site = DefnCallSite { source: origin,
                        head: span_of(&forms[at + 1]), span: span_of(&forms[at]) };
                    proof {
                        reveal(unvisited_arithmetic_at_source);
                        expression_slot_bounds(source, forms@, body, at);
                        crate::ncg2m::file::meta_ast_body_origin(source, forms@, entries@, item as int);
                        assert(entry_witness(call_types@[index as int], outcomes, body)) by { reveal(call_inputs_match); };
                        reveal(entry_witness);
                        assert(body <= at < end == subtree_limit(forms@, body));
                        let target = outcomes[at - body];
                        assert(target matches Some(Ok(PreparedDefnCall::Arithmetic { .. })));
                        let form = read_recorded_call_form(aliases, from, forms@, body, outcomes, call_types@,
                            original_issues, at);
                        call_form_origin(source, forms@, at, form);
                        span_within_subtree(forms@, body, at);
                        assert(indexed_body_site(source, forms@, root, body, *header));
                        assert(body_contains_call_slot(source, forms@, *header, site.span)) by {
                            reveal(body_contains_call_slot);
                            assert(expression_slot(source, forms@, body, at));
                            assert(site.span == form_span(forms@[at as int]));
                        };
                        crate::ncg2m::defn::form_span_readable(source, forms@, at);
                        assert(unvisited_arithmetic_at_source(aliases, from, at, site));
                    }
                    return (outcome, Err(DefnCallGraphError::UnvisitedArithmetic { from, at, site }), Vec::new());
                }
                let sites = capture_arithmetic_sites(&call_types, visits.as_slice(), Ghost(forms@));
                proof {
                    let caller = DefnPosition { file, item };
                    prove_arithmetic_slot_projection(aliases, caller, forms@, body, outcomes, call_types@,
                        original_issues, visits@, sites@);
                    if let Ok(projected) = &edges {
                        finish_expression_slot_coverage(aliases, caller, source, forms@, root, body, *header,
                            outcomes, call_types@, original_issues, projected@, signature, call_trace_model(trace), Some(sites@));
                    }
                }
                sites
            }
            None => Vec::new(),
        }
    } else {
        Vec::new()
    };
    (outcome, edges, sites)
}

proof fn read_recorded_call_form<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, caller: DefnPosition, forms: Seq<Form>, body: usize,
    outcomes: Seq<CallOutcome<'p, 'a>>, calls: Seq<CallTypeEntry>, issues: Seq<CallIssue<'p, 'a>>, at: usize,
) -> (form: CallForm<'a>)
    requires
        caller.file < aliases.targets_model().project_model().sources_model().len(),
        call_inputs_match(aliases, caller.file, caller.item, forms, body, outcomes, calls, issues),
        body <= at < body + outcomes.len(), outcomes[at - body].is_some(),
    ensures
        call_form_matches(aliases.targets_model().project_model().sources_model()[caller.file as int].text_model(),
            forms, at, Some(form)),
        call_arity_matches(aliases, caller.file, caller.item, form, outcomes[at - body]->Some_0),
{
    let source = aliases.targets_model().project_model().sources_model()[caller.file as int].text_model();
    let outcome = outcomes[at - body];
    assert(form_outcome_matches(aliases, caller.file, caller.item, forms, at, outcome)) by {
        reveal(call_inputs_match);
        reveal(outcomes_recorded);
    };
    reveal(form_outcome_matches);
    let form = choose|form: Option<CallForm>| #[trigger] call_form_matches(source, forms, at, form)
        && form.is_some() && call_arity_matches(aliases, caller.file, caller.item, form->Some_0, outcome->Some_0);
    form->Some_0
}

}
