//! 補助関数の本体にある呼び出し形から、先頭の名前と引数列を取り出す。

use super::*;

mod slots;
pub(in crate::ncg2m) use slots::is_expression_slot;
#[cfg(verus_only)]
pub(in crate::ncg2m) use slots::{expression_slot, expression_slot_bounds};

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
    }
}

pub(in crate::ncg2m) proof fn call_form_origin(source: &str, forms: Seq<Form>, at: usize, call: CallForm)
    requires call_form_matches(source, forms, at, Some(call)),
    ensures
        at + 1 < forms.len(),
        forms[at as int] is List, forms[at + 1] is Atom,
        call.span == form_span(forms[at as int]), call.head_span == form_span(forms[at + 1]),
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

pub(in crate::ncg2m) fn read_call_form<'a>(source: &'a str, forms: &[Form], at: usize) -> (result: Option<CallForm<'a>>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures call_form_matches(source, forms@, at, result),
{
    let (head, end, word) = read_named_head(source, forms, at)?;
    Some(CallForm {
        word,
        head_span: span_of(&forms[head]),
        span: span_of(&forms[at]),
        arguments: count_call_arguments(forms, at, head + 1, end),
    })
}

}
