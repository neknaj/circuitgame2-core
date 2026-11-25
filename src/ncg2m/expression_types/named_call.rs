//! 補助関数の本体にある呼び出し形から、先頭の名前と引数列を取り出す。

use super::*;
use crate::project::DefnPosition;
use super::typing::{CallArgument, CallTypeEntry, CallTypeTarget};
#[cfg(verus_only)]
use super::typing::canonical_call;

mod body;
mod fragment;
pub(crate) use fragment::check_scalar_body_syntax;
#[cfg(verus_only)]
pub use fragment::{scalar_call_syntax_at, scalar_evaluator_syntax, scalar_syntax_call_arguments,
    scalar_syntax_form_kind, scalar_syntax_if_children, scalar_syntax_matches_call_arguments,
    scalar_syntax_atom_from_kind, scalar_syntax_if_from_children, scalar_syntax_call_from_arguments};
pub use body::DefnBodyCallError;
pub(crate) use body::check_indexed_call_body;
#[cfg(verus_only)]
pub(crate) use body::{indexed_call_body_locally_typed, indexed_call_body_matches, indexed_call_body_origin, defn_root_call_preserves_scalar_types,
    CheckedNamedTarget, checked_atom_uses_only_parameters, checked_body_scalar_position, recorded_edge_has_call_syntax,
    defn_checked_call_arguments, defn_checked_call_target, defn_checked_expression_site,
    defn_checked_if_child_sites, defn_checked_site_at_body_root, defn_body_sites_cover_slots};
#[cfg(verus_only)]
pub(in crate::ncg2m) use body::argument_positions_increase;
#[cfg(verus_only)]
pub use body::{defn_body_calls_cover_slots, defn_call_argument_origin, defn_call_arguments, defn_call_edge_matches, defn_call_is_expression_slot, unvisited_arithmetic_at_source};
mod slots;
pub(in crate::ncg2m) use slots::{is_expression_slot, mark_expression_slots};
#[cfg(verus_only)]
pub use slots::{expression_slot, expression_slot_at_root};
#[cfg(verus_only)]
pub(in crate::ncg2m::expression_types) use slots::list_in_supported_body_is_expression_slot;
#[cfg(verus_only)]
pub(in crate::ncg2m) use slots::{expression_slot_bounds, slot_marked};

verus! {

/// 呼び出し形と、元ファイルにおける先頭の名前の位置。
#[derive(Debug)]
pub(crate) struct CallForm<'a> {
    /// 呼び出し先として書かれた名前。
    pub word: &'a str,
    /// 名前の元ファイル上の UTF-8 半開バイト範囲。
    pub head_span: Range<usize>,
    /// フォーム全体の元ファイル上の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 呼び出し形の直下にある引数の個数。
    pub arguments: usize,
    /// 引数が二つあるときの、左から順に並ぶ構文木の添字。
    pub binary_arguments: Option<(usize, usize)>,
}

spec fn is_stage_form(word: Seq<u8>) -> bool {
    word == "syntax".spec_bytes() || word == "unsyntax".spec_bytes() || word == "splice".spec_bytes()
}

fn stage_form(word: &str) -> (matches: bool)
    ensures matches == is_stage_form(word.spec_bytes()),
{
    is_spelling(word, "syntax") || is_spelling(word, "unsyntax") || is_spelling(word, "splice")
}

spec fn named_call_head(source: &str, forms: Seq<Form>, at: usize) -> bool {
    &&& at < forms.len()
    &&& forms[at as int] is List
    &&& at + 1 < forms[at as int]->List_end <= forms.len()
    &&& {
        let head = forms[at + 1];
        let word = spelling(source, head);
        &&& head is Atom
        &&& match head->Atom_kind {
            AtomKind::Name => keyword(word).is_none() && !is_stage_form(word),
            AtomKind::RelativePath | AtomKind::AbsolutePath => true,
            _ => false,
        }
    }
}

spec fn argument_count(forms: Seq<Form>, first: usize, end: usize) -> nat
    decreases end - first,
{
    if first >= end || end > forms.len() {
        0
    } else {
        let next = subtree_limit(forms, first);
        if first < next <= end { 1 + argument_count(forms, next, end) } else { 0 }
    }
}

proof fn count_does_not_exceed_nodes(forms: Seq<Form>, first: usize, end: usize)
    requires first <= end <= forms.len(),
    ensures argument_count(forms, first, end) <= end - first,
    decreases end - first,
{
    if first < end {
        let next = subtree_limit(forms, first);
        if first < next <= end {
            count_does_not_exceed_nodes(forms, next, end);
        }
    }
}

/// 呼び出しの先頭の字句、元範囲、直下の引数の個数を表す。
pub(in crate::ncg2m) closed spec fn call_form_matches(
    source: &str, forms: Seq<Form>, at: usize, result: Option<CallForm>,
) -> bool {
    &&& result.is_some() == named_call_head(source, forms, at)
    &&& result matches Some(call) ==> {
        let head = forms[at + 1];
        &&& call.word.spec_bytes() == spelling(source, head)
        &&& call.head_span == form_span(head)
        &&& call.span == form_span(forms[at as int])
        &&& call.arguments == argument_count(forms, (at + 2) as usize, forms[at as int]->List_end)
        &&& call.binary_arguments.is_some() == (call.arguments == 2)
        &&& call.binary_arguments matches Some((left, right)) ==>
            defn_call_arguments(forms, at, seq![left, right])
    }
}

pub(in crate::ncg2m) proof fn call_form_origin(source: &str, forms: Seq<Form>, at: usize, call: CallForm)
    requires call_form_matches(source, forms, at, Some(call)),
    ensures
        at + 1 < subtree_limit(forms, at) <= forms.len(),
        forms[at as int] is List, forms[at + 1] is Atom,
        call.span == form_span(forms[at as int]), call.head_span == form_span(forms[at + 1]),
        call.word.spec_bytes() == spelling(source, forms[at + 1]),
        call.binary_arguments.is_some() == (call.arguments == 2),
        call.binary_arguments matches Some((left, right)) ==>
            defn_call_arguments(forms, at, seq![left, right]),
{}

proof fn declared_head_is_deferred_by_local_typing(source: &str, forms: Seq<Form>, at: usize, call: CallForm)
    requires call_form_matches(source, forms, at, Some(call)),
    ensures
        shape(source, forms, at) == Err(ExpressionCheckFailure::Deferred(
            DeferredExpression::Form(form_span(forms[at as int])),
        )),
        conditional_positions(source, forms, at).is_none(),
{}

fn count_call_arguments(forms: &[Form], _call: usize, first: usize, end: usize) -> (count: usize)
    requires complete_list_indices(forms@), nested_list_indices(forms@), _call < first <= end <= forms@.len(),
        forms@[_call as int] is List, subtree_limit(forms@, _call) == end,
    ensures count == argument_count(forms@, first, end),
{
    let mut at = first;
    let mut count = 0usize;
    while at < end
        invariant
            complete_list_indices(forms@), nested_list_indices(forms@),
            _call < first <= at <= end <= forms@.len(),
            forms@[_call as int] is List, subtree_limit(forms@, _call) == end,
            count + argument_count(forms@, at, end) == argument_count(forms@, first, end),
        decreases end - at,
    {
        proof {
            super::super::forms::child_stays_inside(forms@, _call, at);
            count_does_not_exceed_nodes(forms@, first, end);
        }
        let next = subtree_end(forms, at);
        count += 1;
        at = next;
    }
    count
}

fn read_named_head<'a>(source: &'a str, forms: &[Form], at: usize) -> (result: Option<(usize, usize, &'a str)>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures result.is_some() == named_call_head(source, forms@, at),
        result matches Some((head, end, word)) ==> head == at + 1 < end <= forms@.len()
            && forms@[at as int] is List && forms@[at as int]->List_end == end
            && word.spec_bytes() == spelling(source, forms@[head as int]),
{
    let Form::List { end: list_end, .. } = &forms[at] else { return None };
    let _length = forms.len();
    assert(at < *list_end <= _length);
    let head = at + 1;
    if head >= *list_end {
        return None;
    }
    let Form::Atom { kind: atom_kind, .. } = &forms[head] else { return None };
    let word = source_word(source, forms, head);
    match atom_kind {
        AtomKind::Name => {
            if read_keyword(word).is_some() || stage_form(word) {
                return None;
            }
        }
        AtomKind::RelativePath | AtomKind::AbsolutePath => (),
        _ => return None,
    }
    Some((head, *list_end, word))
}

#[verifier::spinoff_prover]
fn binary_call_arguments(forms: &[Form], Ghost(at): Ghost<usize>, left: usize, Ghost(end): Ghost<usize>)
    -> (arguments: (usize, usize))
    requires
        complete_list_indices(forms@), nested_list_indices(forms@), at < forms@.len(),
        forms@[at as int] is List, left == at + 2 <= end <= forms@.len(),
        subtree_limit(forms@, at) == end, argument_count(forms@, left, end) == 2,
    ensures defn_call_arguments(forms@, at, seq![arguments.0, arguments.1]),
{
    proof {
        reveal_with_fuel(argument_count, 3);
        assert(left < end);
        super::super::forms::child_stays_inside(forms@, at, left);
    }
    let right = subtree_end(forms, left);
    proof {
        reveal_with_fuel(argument_count, 3);
        assert(left < right < end);
        super::super::forms::child_stays_inside(forms@, at, right);
        let last = subtree_limit(forms@, right);
        if last < end {
            super::super::forms::child_stays_inside(forms@, at, last);
            assert(argument_count(forms@, last, end) > 0);
        }
        assert(last == end);
        let operands = seq![left, right];
        assert forall|i: int| 0 <= i < operands.len() implies {
            let child = #[trigger] operands[i];
            &&& left <= child < subtree_limit(forms@, child) <= end
            &&& if i + 1 < operands.len() { subtree_limit(forms@, child) == operands[i + 1] }
                else { subtree_limit(forms@, child) == end }
        } by {
            if i == 0 { assert(operands[i] == left && operands[i + 1] == right); }
            else { assert(operands[i] == right); }
        };
        body::call_arguments_from_intervals(forms@, at, operands);
    }
    (left, right)
}

pub(in crate::ncg2m) fn read_call_form<'a>(source: &'a str, forms: &[Form], at: usize) -> (result: Option<CallForm<'a>>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures call_form_matches(source, forms@, at, result),
        result matches Some(call) ==> call.binary_arguments.is_some() == (call.arguments == 2),
{
    let (head, end, word) = read_named_head(source, forms, at)?;
    let left = head + 1;
    let count = count_call_arguments(forms, at, left, end);
    let binary_arguments = if count == 2 {
        Some(binary_call_arguments(forms, Ghost(at), left, Ghost(end)))
    } else {
        None
    };
    Some(CallForm {
        word,
        head_span: span_of(&forms[head]),
        span: span_of(&forms[at]),
        arguments: count,
        binary_arguments,
    })
}

/// 呼び出し形の直下から、指定した個数の引数を読み取れることを表す。
pub(crate) closed spec fn call_has_arity(source: &str, forms: Seq<Form>, at: usize, count: usize) -> bool {
    &&& named_call_head(source, forms, at)
    &&& argument_count(forms, (at + 2) as usize, forms[at as int]->List_end) == count
}

pub(in crate::ncg2m) proof fn decoded_call_has_arity(
    source: &str, forms: Seq<Form>, at: usize, call: CallForm,
)
    requires call_form_matches(source, forms, at, Some(call)),
    ensures call_has_arity(source, forms, at, call.arguments),
{}

pub(super) open spec fn call_signature_types_match(entry: CallTypeEntry, signature: DefnSignature) -> bool {
    &&& entry.target is Declared
    &&& entry.result == type_shape(signature.result_type.ty)
    &&& entry.arguments@.len() == signature.parameters@.len()
    &&& forall|i: int| 0 <= i < entry.arguments@.len() ==>
        (#[trigger] entry.arguments@[i]).expected == type_shape(signature.parameters@[i].ty.ty)
}

pub(super) fn prepare_call_types<'a>(
    source: &'a str, forms: &[Form], call: usize, target: DefnPosition, signature: &DefnSignature<'a>,
) -> (entry: CallTypeEntry)
    requires usable_forms(source, forms@), call_has_arity(source, forms@, call, signature.parameters@.len() as usize),
        signature.parameters@.len() <= usize::MAX,
    ensures canonical_call(forms@, entry), entry.at == call, entry.target == CallTypeTarget::Declared(target),
        call_signature_types_match(entry, *signature),
{
    let Some((head, end, _)) = read_named_head(source, forms, call) else { unreachable!() };
    let first = head + 1;
    let params = &signature.parameters;
    let mut arguments = Vec::<CallArgument>::new();
    let mut cursor = first;
    let mut i = 0;
    let _len = params.len();
    assert(argument_count(forms@, first, end) == params@.len());
    while i < params.len()
        invariant
            usable_forms(source, forms@), forms@[call as int] is List, subtree_limit(forms@, call) == end,
            call + 2 == first <= cursor <= end <= forms@.len(),
            i == arguments@.len() <= params@.len(),
            argument_count(forms@, cursor, end) + i == params@.len(),
            i == 0 ==> cursor == first,
            i > 0 ==> arguments@[0].at == first
                && subtree_limit(forms@, arguments@[i - 1].at) == cursor,
            forall|j: int| 0 <= j < arguments@.len() ==> {
                let arg = #[trigger] arguments@[j];
                &&& call < arg.at < subtree_limit(forms@, arg.at) <= end
                &&& arg.expected == type_shape(params@[j].ty.ty)
                &&& j + 1 < i ==> subtree_limit(forms@, arg.at) == arguments@[j + 1].at
            },
        decreases params@.len() - i,
    {
        assert(cursor < end);
        proof { super::super::forms::child_stays_inside(forms@, call, cursor); }
        let next = subtree_end(forms, cursor);
        let expected = shape_of_type(params[i].ty.ty);
        arguments.push(CallArgument { at: cursor, expected });
        cursor = next;
        i += 1;
    }
    if cursor < end {
        proof { super::super::forms::child_stays_inside(forms@, call, cursor); }
        assert(argument_count(forms@, cursor, end) > 0);
        assert(false);
    }
    CallTypeEntry {
        at: call,
        target: CallTypeTarget::Declared(target),
        arguments,
        result: shape_of_type(signature.result_type.ty),
    }
}
}
