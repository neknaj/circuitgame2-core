//! NCG2M のフォームの検査で共有する、構文木の添字とトークンの読み取り。

use crate::project::read_source_span;
use crate::syntax::Form;
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_span, form_spans_valid, nested_list_indices};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::encode_utf8_decode_utf8;

verus! {

pub(super) open spec fn spelling(source: &str, form: Form) -> Seq<u8> {
    let span = form_span(form);
    source.spec_bytes()[span.start as int..span.end as int]
}

pub(super) fn source_word<'a>(source: &'a str, forms: &[Form], index: usize) -> (word: &'a str)
    requires index < forms@.len(), form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures word.spec_bytes() == spelling(source, forms@[index as int]),
{
    let span = match &forms[index] {
        Form::Atom { span, .. } | Form::List { span, .. } => span,
    };
    proof {
        reveal(form_spans_valid);
        assert(*span == form_span(forms@[index as int]));
    }
    read_source_span(source, span.start, span.end)
}

pub(super) fn is_spelling(word: &str, name: &str) -> (matches: bool)
    ensures matches == (word.spec_bytes() == name.spec_bytes()),
{
    proof {
        encode_utf8_decode_utf8(word@);
        encode_utf8_decode_utf8(name@);
    }
    word == name
}

pub(super) open spec fn subtree_limit(forms: Seq<Form>, at: usize) -> usize
    recommends at < forms.len(),
{
    match forms[at as int] {
        Form::Atom { .. } => (at + 1) as usize,
        Form::List { end, .. } => end,
    }
}

pub(super) fn subtree_end(forms: &[Form], at: usize) -> (end: usize)
    requires at < forms@.len(),
    ensures end == subtree_limit(forms@, at),
{
    match &forms[at] {
        Form::Atom { .. } => at + 1,
        Form::List { end, .. } => *end,
    }
}

pub(super) proof fn child_stays_inside(forms: Seq<Form>, parent: usize, child: usize)
    requires
        complete_list_indices(forms), nested_list_indices(forms),
        parent < child < subtree_limit(forms, parent) <= forms.len(),
        forms[parent as int] is List,
    ensures child < subtree_limit(forms, child) <= subtree_limit(forms, parent),
{
    reveal(nested_list_indices);
    assert(forms[parent as int] is List);
    if forms[child as int] is List {
        assert(forms[child as int] is List);
    }
}

}
