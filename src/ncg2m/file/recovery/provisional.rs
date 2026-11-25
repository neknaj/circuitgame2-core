//! 未閉鎖の名前空間から、所属が確定していない宣言を拾う。

use alloc::vec::Vec;
use core::ops::Range;

use super::{MetaFileRecovery, recover_meta_file};
#[cfg(verus_only)]
use super::meta_file_recovery_matches;
use super::super::{ItemTag, MetaItem, MetaItemKind, index_meta_file, read_item_tag};
#[cfg(verus_only)]
use super::super::{item_tag, meta_file_matches, valid_meta_file};
use crate::ncg2m::{defn::span_of, forms::subtree_end};
#[cfg(verus_only)]
use crate::ncg2m::{defn::usable_forms, forms::subtree_limit};
use crate::project::read_source_span;
use crate::syntax::{AtomKind, Form, Recovered, Repair};
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid, inserted_closes_match, located_span};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    direct_form_in_range, following_direct_form, node_end_is_following_direct_form,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 宣言自体は厳格に読めるが、名前空間への所属が確定していない箇所。
#[derive(Debug)]
pub struct ProvisionalMetaDeclaration {
    /// 文書を基準とする宣言全体の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 宣言の先頭を基準とする局所索引。所属はこの値から決めない。
    pub item: MetaItem,
}

spec fn unclosed_namespace(source: &str, forms: Seq<Form>, repairs: Seq<Repair>, parent: int) -> bool {
    &&& repairs.len() > 0
    &&& repairs.last() matches Repair::InsertedClose { list, .. } && list == parent
    &&& direct_form_in_range(forms, 0, forms.len() as int, parent)
    &&& forms[parent] is List && parent + 3 <= forms[parent]->List_end == forms.len()
    &&& item_tag(source, forms, parent as usize) == Some(ItemTag::Namespace)
    &&& forms[parent + 2] matches Form::Atom { kind, .. }
        && (kind is Name || kind is RelativePath)
}

spec fn provisional_decl_matches(source: &str, decl: ProvisionalMetaDeclaration) -> bool {
    &&& located_span(source, decl.span)
    &&& decl.item.span == (0usize..(decl.span.end - decl.span.start) as usize)
    &&& decl.item.namespace.is_none()
    &&& (decl.item.kind is Defn || decl.item.kind is Defmacro)
    &&& exists|text: &str, indexed: Vec<MetaItem>| {
        &&& text.spec_bytes() == source.spec_bytes()[decl.span.start as int..decl.span.end as int]
        &&& #[trigger] meta_file_matches(text, Ok(indexed))
        &&& valid_meta_file(text)
        &&& indexed@.len() == 1 && indexed@[0] == decl.item
    }
}

spec fn matches_under(
    source: &str, syntax: &Recovered, parent: int, declarations: Seq<ProvisionalMetaDeclaration>,
) -> bool {
    forall|i: int| 0 <= i < declarations.len() ==> {
        let decl = #[trigger] declarations[i];
        &&& provisional_decl_matches(source, decl)
        &&& exists|child: int| {
            &&& #[trigger] direct_form_in_range(syntax.forms@, parent + 3, syntax.forms@.len() as int, child)
            &&& syntax.forms@[child] is List
            &&& form_span(syntax.forms@[child]) == decl.span
        }
    }
}

/// 暫定の各宣言が、元入力で厳格に読める範囲と未閉鎖ブロック直下の候補に対応することを表す。
pub closed spec fn provisional_meta_matches(
    source: &str, recovery: MetaFileRecovery, declarations: Seq<ProvisionalMetaDeclaration>,
) -> bool {
    if declarations.len() == 0 {
        true
    } else {
        match recovery {
            MetaFileRecovery::Incomplete { syntax, .. } =>
                exists|parent: int| #[trigger] unclosed_namespace(source, syntax.forms@, syntax.repairs@, parent)
                    && matches_under(source, &syntax, parent, declarations),
            MetaFileRecovery::Complete(_) => false,
        }
    }
}

fn find_unclosed_namespace(source: &str, syntax: &Recovered) -> (parent: Option<usize>)
    requires usable_forms(source, syntax.forms@),
        inserted_closes_match(source, syntax.forms@, syntax.repairs@),
    ensures parent matches Some(parent) ==> unclosed_namespace(source, syntax.forms@, syntax.repairs@, parent as int),
{
    let Some(Repair::InsertedClose { list, .. }) = syntax.repairs.last() else { return None; };
    let forms = syntax.forms.as_slice();
    proof { reveal(inserted_closes_match); }
    let mut at = 0;
    proof { reveal(direct_form_in_range); }
    while at < *list
        invariant
            usable_forms(source, forms@), *list < forms@.len(), at <= forms@.len(),
            at < forms@.len() ==> direct_form_in_range(forms@, 0, forms@.len() as int, at as int),
        decreases forms@.len() - at,
    {
        let next = subtree_end(forms, at);
        proof {
            reveal(crate::syntax::complete_list_indices);
            node_end_is_following_direct_form(forms@, at as int, next as int);
            reveal(following_direct_form);
        }
        at = next;
    }
    if at != *list { return None; }
    let limit = subtree_end(forms, at);
    proof { reveal(crate::syntax::complete_list_indices); }
    if limit != forms.len() || limit - at < 3 || !matches!(read_item_tag(source, forms, at), Some(ItemTag::Namespace)) {
        return None;
    }
    if !matches!(&forms[at + 2], Form::Atom { kind: AtomKind::Name | AtomKind::RelativePath, .. }) {
        return None;
    }
    Some(at)
}

fn inspect_declaration(source: &str, forms: &[Form], at: usize)
    -> (declaration: Option<ProvisionalMetaDeclaration>)
    requires at < forms@.len(), form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures declaration matches Some(decl) ==> forms@[at as int] is List
        && decl.span == form_span(forms@[at as int]) && provisional_decl_matches(source, decl),
{
    if !matches!(&forms[at], Form::List { .. }) { return None; }
    let span = span_of(&forms[at]);
    proof { reveal(form_spans_valid); }
    let text = read_source_span(source, span.start, span.end);
    let Ok(mut items) = index_meta_file(text) else { return None; };
    if items.len() != 1 { return None; }
    let ghost original = items;
    let item = items.remove(0);
    if item.span.start != 0 || item.span.end != span.end - span.start || item.namespace.is_some()
        || !matches!(item.kind, MetaItemKind::Defn(_) | MetaItemKind::Defmacro { .. })
    {
        return None;
    }
    let decl = ProvisionalMetaDeclaration { span, item };
    assert(provisional_decl_matches(source, decl)) by {
        assert(meta_file_matches(text, Ok(original)));
    };
    Some(decl)
}

fn collect_provisional(
    source: &str, syntax: &Recovered, parent: usize,
) -> (declarations: Vec<ProvisionalMetaDeclaration>)
    requires usable_forms(source, syntax.forms@),
        unclosed_namespace(source, syntax.forms@, syntax.repairs@, parent as int),
    ensures matches_under(source, syntax, parent as int, declarations@),
{
    let forms = syntax.forms.as_slice();
    let mut declarations = Vec::new();
    let mut at = parent + 3;
    proof { reveal(direct_form_in_range); }
    while at < forms.len()
        invariant
            usable_forms(source, forms@), forms@ == syntax.forms@,
            parent + 3 <= at <= forms@.len(),
            at < forms@.len() ==> direct_form_in_range(forms@, parent + 3, forms@.len() as int, at as int),
            matches_under(source, syntax, parent as int, declarations@),
        decreases forms@.len() - at,
    {
        let next = subtree_end(forms, at);
        proof {
            reveal(crate::syntax::complete_list_indices);
            node_end_is_following_direct_form(forms@, at as int, next as int);
            reveal(following_direct_form);
        }
        if let Some(recovered) = inspect_declaration(source, forms, at) {
            let ghost previous = declarations@;
            let ghost addition = recovered;
            declarations.push(recovered);
            assert forall|i: int| 0 <= i < declarations@.len() implies {
                let decl = #[trigger] declarations@[i];
                &&& provisional_decl_matches(source, decl)
                &&& exists|child: int| {
                    &&& #[trigger] direct_form_in_range(forms@, parent + 3, forms@.len() as int, child)
                    &&& forms@[child] is List
                    &&& form_span(forms@[child]) == decl.span
                }
            } by {
                if i < previous.len() {
                    assert(declarations@[i] == previous[i]);
                } else {
                    assert(declarations@[i] == addition);
                    assert(form_span(forms@[at as int]) == addition.span);
                }
            };
        }
        at = next;
    }
    declarations
}

/// 確定した回復結果と、閉じ括弧が欠けた名前空間から読み取れた暫定宣言を返す。
///
/// 暫定宣言の本体と見出しの文字はすべて元入力にあり、その範囲だけで宣言の構文検査を通る。
/// 所属が確定するまで、暫定宣言は名前解決や型検査に使わない。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::ncg2m::file::recovery::recover_meta_file_with_provisional;
///
/// let source = "(namespace tools (defmacro saved () (quote value)) (defmacro unfinished";
/// let (_, declarations) = recover_meta_file_with_provisional(source);
/// assert_eq!(declarations.len(), 1);
/// assert_eq!(&source[declarations[0].span.clone()], "(defmacro saved () (quote value))");
/// assert!(declarations[0].item.namespace.is_none());
/// ```
pub fn recover_meta_file_with_provisional(
    source: &str,
) -> (result: (MetaFileRecovery, Vec<ProvisionalMetaDeclaration>))
    ensures
        meta_file_recovery_matches(source, result.0),
        provisional_meta_matches(source, result.0, result.1@),
{
    let recovery = recover_meta_file(source);
    let declarations = if let MetaFileRecovery::Incomplete { syntax, .. } = &recovery {
        if let Some(parent) = find_unclosed_namespace(source, syntax) {
            let declarations = collect_provisional(source, syntax, parent);
            assert(provisional_meta_matches(source, recovery, declarations@));
            declarations
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };
    (recovery, declarations)
}

}
