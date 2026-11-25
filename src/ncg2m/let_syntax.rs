//! 局所束縛の文法と、元ソース上の名前・右辺の位置を検査する。

use alloc::vec::Vec;
use core::ops::Range;
use crate::syntax::Form;
#[cfg(verus_only)]
use crate::syntax::form_span;
use super::defn::{is_name, span_of, tagged};
#[cfg(verus_only)]
use super::defn::{plain_name, tagged_arguments, usable_forms};
use super::forms::{is_spelling, source_word, subtree_end};
#[cfg(verus_only)]
use super::forms::{child_stays_inside, spelling, subtree_limit};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// `let` の局所束縛列で最初に見つかった文法違反。
#[derive(Debug, Eq, PartialEq)]
pub enum LetSyntaxError {
    /// `let` に束縛列と本体式を一つずつ書く。違反したフォーム全体の範囲を返す。
    Arguments(Range<usize>),
    /// 束縛列はリストで書く。束縛列の位置にあったフォームの範囲を返す。
    BindingList(Range<usize>),
    /// 束縛は名前と値の式を一つずつ持つリストで書く。違反した束縛の範囲を返す。
    Binding(Range<usize>),
    /// 束縛名には無修飾名を使う。違反したフォームの範囲を返す。
    Name(Range<usize>),
    /// 同じ束縛列で名前が重複している。
    Duplicate {
        /// 最初に同名となった後続の名前の範囲。
        duplicate: Range<usize>,
        /// 同じ綴りを持つ先行の名前の範囲。
        first: Range<usize>,
    },
}

#[derive(Clone, Copy)]
pub(super) struct LocalBinding {
    pub(super) name: usize,
    pub(super) value: usize,
}

pub(super) struct LetHeader {
    pub(super) bindings: Vec<LocalBinding>,
    pub(super) body: usize,
}

spec fn binding_at(forms: Seq<Form>, at: usize, limit: usize) -> Result<LocalBinding, LetSyntaxError> {
    let span = form_span(forms[at as int]);
    match forms[at as int] {
        Form::List { end, .. } if at + 1 < end <= limit => {
            let name = (at + 1) as usize;
            if !plain_name(forms[name as int]) {
                Err(LetSyntaxError::Name(form_span(forms[name as int])))
            } else if name + 1 >= end || subtree_limit(forms, (name + 1) as usize) != end {
                Err(LetSyntaxError::Binding(span))
            } else {
                Ok(LocalBinding { name, value: (name + 1) as usize })
            }
        }
        _ => Err(LetSyntaxError::Binding(span)),
    }
}

fn read_binding(forms: &[Form], at: usize, limit: usize) -> (result: Result<LocalBinding, LetSyntaxError>)
    requires at < limit <= forms@.len(),
    ensures result == binding_at(forms@, at, limit),
{
    let Form::List { end: binding_end, .. } = &forms[at] else {
        return Err(LetSyntaxError::Binding(span_of(&forms[at])));
    };
    let name = at + 1;
    if name >= *binding_end || *binding_end > limit {
        return Err(LetSyntaxError::Binding(span_of(&forms[at])));
    }
    if !is_name(&forms[name]) {
        return Err(LetSyntaxError::Name(span_of(&forms[name])));
    }
    let value = name + 1;
    if value >= *binding_end || subtree_end(forms, value) != *binding_end {
        return Err(LetSyntaxError::Binding(span_of(&forms[at])));
    }
    Ok(LocalBinding { name, value })
}

spec fn earlier_name(source: &str, forms: Seq<Form>, prior: Seq<LocalBinding>, word: Seq<u8>, at: nat)
    -> Option<usize>
    decreases prior.len() - at,
{
    if at >= prior.len() {
        None
    } else {
        let name = prior[at as int].name;
        if spelling(source, forms[name as int]) == word {
            Some(name)
        } else {
            earlier_name(source, forms, prior, word, at + 1)
        }
    }
}

fn first_same_name(source: &str, forms: &[Form], prior: &[LocalBinding], name: usize)
    -> (result: Option<usize>)
    requires
        usable_forms(source, forms@), name < forms@.len(),
        forall|i: int| 0 <= i < prior@.len() ==> (#[trigger] prior@[i]).name < forms@.len(),
    ensures result == earlier_name(source, forms@, prior@, spelling(source, forms@[name as int]), 0),
{
    let word = source_word(source, forms, name);
    let mut at = 0;
    while at < prior.len()
        invariant
            usable_forms(source, forms@), at <= prior@.len(),
            word.spec_bytes() == spelling(source, forms@[name as int]),
            forall|i: int| 0 <= i < prior@.len() ==> (#[trigger] prior@[i]).name < forms@.len(),
            earlier_name(source, forms@, prior@, word.spec_bytes(), 0)
                == earlier_name(source, forms@, prior@, word.spec_bytes(), at as nat),
        decreases prior@.len() - at,
    {
        reveal_with_fuel(earlier_name, 2);
        let first = prior[at].name;
        if is_spelling(source_word(source, forms, first), word) {
            return Some(first);
        }
        at += 1;
    }
    None
}

#[verifier::opaque]
spec fn binding_sequence(source: &str, forms: Seq<Form>, limit: usize, at: usize, prior: Seq<LocalBinding>)
    -> Result<Seq<LocalBinding>, LetSyntaxError>
    decreases limit - at,
{
    if at == limit {
        Ok(prior)
    } else if !(at < limit <= forms.len()) {
        Err(LetSyntaxError::Binding(0..0))
    } else {
        match binding_at(forms, at, limit) {
            Err(error) => Err(error),
            Ok(row) => match earlier_name(source, forms, prior, spelling(source, forms[row.name as int]), 0) {
                Some(first) => Err(LetSyntaxError::Duplicate {
                    duplicate: form_span(forms[row.name as int]),
                    first: form_span(forms[first as int]),
                }),
                None => {
                    let end = subtree_limit(forms, at);
                    if at < end <= limit {
                        binding_sequence(source, forms, limit, end, prior.push(row))
                    } else {
                        Err(LetSyntaxError::Binding(form_span(forms[at as int])))
                    }
                }
            },
        }
    }
}

pub(super) open spec fn valid_bindings(forms: Seq<Form>, bindings: Seq<LocalBinding>, first: usize, end: usize) -> bool {
    forall|i: int| 0 <= i < bindings.len() ==> {
        let row = #[trigger] bindings[i];
        first < row.name < row.value < end <= forms.len()
            && plain_name(forms[row.name as int])
    }
}

fn read_binding_sequence(source: &str, forms: &[Form], first: usize)
    -> (result: Result<Vec<LocalBinding>, LetSyntaxError>)
    requires
        usable_forms(source, forms@), first < forms@.len(),
        forms@[first as int] is List,
    ensures
        result matches Ok(rows) ==> valid_bindings(forms@, rows@, first, subtree_limit(forms@, first)),
        (match result { Ok(rows) => Ok(rows@), Err(error) => Err(error) })
            == binding_sequence(source, forms@, subtree_limit(forms@, first),
                (first + 1) as usize, Seq::empty()),
{
    let limit = subtree_end(forms, first);
    assert(first < limit <= forms@.len());
    let mut at = first + 1;
    let mut rows = Vec::<LocalBinding>::new();
    while at < limit
        invariant
            usable_forms(source, forms@), forms@[first as int] is List,
            first < at <= limit <= forms@.len(), limit == subtree_limit(forms@, first),
            valid_bindings(forms@, rows@, first, limit),
            binding_sequence(source, forms@, limit, (first + 1) as usize, Seq::empty())
                == binding_sequence(source, forms@, limit, at, rows@),
        decreases limit - at,
    {
        reveal(binding_sequence);
        let row = read_binding(forms, at, limit)?;
        proof {
            assert forall|i: int| 0 <= i < rows@.len() implies (#[trigger] rows@[i]).name < forms@.len() by {};
            assert(row.name < forms@.len() && row.value < forms@.len());
        }
        if let Some(first) = first_same_name(source, forms, rows.as_slice(), row.name) {
            assert(first < forms@.len()) by {
                first_same_name_in_range(source, forms@, rows@,
                    spelling(source, forms@[row.name as int]), 0);
            };
            return Err(LetSyntaxError::Duplicate {
                duplicate: span_of(&forms[row.name]), first: span_of(&forms[first]),
            });
        }
        let end = subtree_end(forms, at);
        proof { child_stays_inside(forms@, first, at); }
        rows.push(row);
        at = end;
    }
    proof { reveal(binding_sequence); }
    Ok(rows)
}

proof fn first_same_name_in_range(source: &str, forms: Seq<Form>, prior: Seq<LocalBinding>, word: Seq<u8>, at: nat)
    requires forall|i: int| 0 <= i < prior.len() ==> (#[trigger] prior[i]).name < forms.len(),
    ensures earlier_name(source, forms, prior, word, at) matches Some(name) ==> name < forms.len(),
    decreases prior.len() - at,
{
    if at < prior.len() {
        reveal_with_fuel(earlier_name, 2);
        first_same_name_in_range(source, forms, prior, word, at + 1);
    }
}

pub(super) closed spec fn let_structure(source: &str, forms: Seq<Form>, at: usize)
    -> Result<(Seq<LocalBinding>, usize), LetSyntaxError>
{
    match tagged_arguments(source, forms, at, "let", true) {
        None => Err(LetSyntaxError::Arguments(form_span(forms[at as int]))),
        Some((bindings, body)) => {
            if forms[bindings as int] is List {
                match binding_sequence(source, forms, subtree_limit(forms, bindings), (bindings + 1) as usize, Seq::empty()) {
                    Ok(rows) => Ok((rows, body)),
                    Err(error) => Err(error),
                }
            } else {
                Err(LetSyntaxError::BindingList(form_span(forms[bindings as int])))
            }
        }
    }
}

pub(super) fn read_let_structure(source: &str, forms: &[Form], at: usize)
    -> (result: Result<LetHeader, LetSyntaxError>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures
        (match result { Ok(header) => Ok((header.bindings@, header.body)), Err(error) => Err(error) })
            == let_structure(source, forms@, at),
        result matches Ok(header) ==> at < header.body < forms@.len()
            && valid_bindings(forms@, header.bindings@, at, header.body),
{
    let Some((bindings, body)) = tagged(source, forms, at, "let", true) else {
        return Err(LetSyntaxError::Arguments(span_of(&forms[at])));
    };
    if !matches!(&forms[bindings], Form::List { .. }) {
        return Err(LetSyntaxError::BindingList(span_of(&forms[bindings])));
    }
    let rows = read_binding_sequence(source, forms, bindings)?;
    assert(valid_bindings(forms@, rows@, at, body)) by {
        assert forall|i: int| 0 <= i < rows@.len() implies {
            let row = #[trigger] rows@[i];
            at < row.name < row.value < body <= forms@.len() && plain_name(forms@[row.name as int])
        } by {
            assert(valid_bindings(forms@, rows@, bindings, subtree_limit(forms@, bindings)));
        };
    };
    Ok(LetHeader { bindings: rows, body })
}

}
