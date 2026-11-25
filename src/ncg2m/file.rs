//! NCG2M のファイルを厳格に解析し、宣言と名前解決の指示を元の順序で索引化する。

use alloc::vec::Vec;
use core::ops::Range;
use crate::syntax::{
    self, Form,
    circuit::{Head, HeaderError, check_named_directive},
};
#[cfg(verus_only)]
use crate::syntax::{
    complete_list_indices, form_span, list_source_delimiters, nested_list_indices, sexpr_form_model, strict_syntax_rejection,
    strict_token_errors_agree, structural_error_location, syntax_error_evidence, well_formed_sexpr,
    circuit::{directive_arguments_match, directive_error_evidence, directive_errors_agree},
};
use super::defn::{DefnHeader, DefnHeaderError, is_name, read_defn_at, span_of};
#[cfg(verus_only)]
use super::defn::{HeaderContents, declaration_model, form_span_readable, header_contents, plain_name, readable_span, usable_forms};
use super::forms::{is_spelling, source_word, subtree_end};
#[cfg(verus_only)]
use super::forms::{spelling, subtree_limit};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 宣言または名前解決の指示と、その位置。
#[derive(Debug, Eq, PartialEq)]
pub struct MetaItem {
    /// フォーム全体の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 所属ブロックの名前空間パスの範囲。トップレベルは `None`。
    pub namespace: Option<Range<usize>>,
    /// フォームの種類と各要素の位置。
    pub kind: MetaItemKind,
}

/// NCG2M のファイル内索引の要素。
///
/// 各範囲はファイル先頭を基準とする UTF-8 半開バイト範囲。
#[derive(Debug, Eq, PartialEq)]
pub enum MetaItemKind {
    /// トップレベルの名前空間ブロック。後続の要素が所属ブロックを個別に指す。
    Namespace {
        /// 名前空間を指定するパスの範囲。
        path: Range<usize>,
    },
    /// 名前空間または宣言を指す別名。
    Use {
        /// 参照先の完全修飾名の範囲。
        target: Range<usize>,
        /// 無修飾の別名の範囲。
        alias: Range<usize>,
    },
    /// 同じ名前空間に属する宣言の公開指定。
    Export {
        /// 公開する名前の範囲を記述順に並べた列。
        names: Vec<Range<usize>>,
    },
    /// 補助関数の署名と本体の位置。
    Defn(DefnHeader),
    /// マクロの仮引数と本体の位置。
    Defmacro {
        /// マクロ名の範囲。
        name: Range<usize>,
        /// 仮引数名の範囲を記述順に並べた列。
        parameters: Vec<Range<usize>>,
        /// 共通 S 式1個の範囲。式の文法と型は後段で検査する。
        body: Range<usize>,
    },
}

/// NCG2M のファイル索引を作れなかった最初の理由。
#[derive(Debug, Eq, PartialEq)]
pub enum MetaFileError {
    /// 共通の字句または S 式解析の違反。
    Syntax(syntax::Error),
    /// この位置に書けるフォームに該当しない。
    ExpectedItem(Range<usize>),
    /// 名前空間・別名・公開指定の引数が規則に合わない。
    Directive {
        /// 先に規則に違反した引数、または引数が欠けた位置の範囲。
        span: Range<usize>,
        /// 引数に必要な形式。
        kind: HeaderError,
    },
    /// 補助関数のヘッダーが規則に合わない。
    Defn(DefnHeaderError),
    /// マクロ宣言の外形または名前が規則に合わない。
    Defmacro {
        /// 違反したフォームまたは名前の範囲。
        span: Range<usize>,
        /// その位置に必要な形式。
        part: MacroPart,
    },
}

/// マクロヘッダーに必要な構文上の部分。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MacroPart {
    /// `(defmacro name (parameter ...) body)` の形。
    Declaration,
    /// 無修飾の宣言名。
    Name,
    /// 仮引数名のリスト。
    Parameters,
    /// 無修飾の仮引数名。
    ParameterName,
}

#[derive(Clone, Copy)]
enum ItemTag {
    Namespace,
    Use,
    Export,
    Defn,
    Defmacro,
}

#[cfg(verus_only)]
enum ItemContents {
    Namespace(Range<usize>),
    Use(Range<usize>, Range<usize>),
    Export(Seq<Range<usize>>),
    Defn(HeaderContents),
    Defmacro(Range<usize>, Seq<Range<usize>>, Range<usize>),
}

#[cfg(verus_only)]
type EntryView = (Range<usize>, Option<Range<usize>>, ItemContents);

spec fn binding_kind_span_valid(source: &str, kind: MetaItemKind) -> bool {
    match kind {
        MetaItemKind::Namespace { path } => readable_span(source, path),
        MetaItemKind::Defn(header) => readable_span(source, header.name_span),
        MetaItemKind::Defmacro { name, .. } => readable_span(source, name),
        _ => true,
    }
}

/// 宣言名と所属名前空間の範囲が、元ソースの UTF-8 境界にあることを表す。
pub closed spec fn meta_binding_spans_valid(source: &str, items: Seq<MetaItem>) -> bool {
    forall|i: int| 0 <= i < items.len() ==> {
        let item = #[trigger] items[i];
        &&& binding_kind_span_valid(source, item.kind)
        &&& (item.namespace matches Some(path) ==> readable_span(source, path))
    }
}

pub(crate) proof fn meta_binding_span_evidence(source: &str, items: Seq<MetaItem>, rank: int)
    requires meta_binding_spans_valid(source, items), 0 <= rank < items.len(),
    ensures
        match items[rank].kind {
            MetaItemKind::Namespace { path } => readable_span(source, path),
            MetaItemKind::Defn(header) => readable_span(source, header.name_span),
            MetaItemKind::Defmacro { name, .. } => readable_span(source, name),
            _ => true,
        },
        items[rank].namespace matches Some(path) ==> readable_span(source, path),
{}

spec fn kind_view(kind: MetaItemKind) -> ItemContents {
    match kind {
        MetaItemKind::Namespace { path } => ItemContents::Namespace(path),
        MetaItemKind::Use { target, alias } => ItemContents::Use(target, alias),
        MetaItemKind::Export { names } => ItemContents::Export(names@),
        MetaItemKind::Defn(header) => ItemContents::Defn(header_contents(header)),
        MetaItemKind::Defmacro { name, parameters, body } => ItemContents::Defmacro(name, parameters@, body),
    }
}

spec fn entry_view(entry: MetaItem) -> EntryView {
    (entry.span, entry.namespace, kind_view(entry.kind))
}

spec fn word_tag(word: Seq<u8>) -> Option<ItemTag> {
    if word == "namespace".spec_bytes() { Some(ItemTag::Namespace) }
    else if word == "use".spec_bytes() { Some(ItemTag::Use) }
    else if word == "export".spec_bytes() { Some(ItemTag::Export) }
    else if word == "defn".spec_bytes() { Some(ItemTag::Defn) }
    else if word == "defmacro".spec_bytes() { Some(ItemTag::Defmacro) }
    else { None }
}

fn read_tag(word: &str) -> (tag: Option<ItemTag>)
    ensures tag == word_tag(word.spec_bytes()),
{
    if is_spelling(word, "namespace") { Some(ItemTag::Namespace) }
    else if is_spelling(word, "use") { Some(ItemTag::Use) }
    else if is_spelling(word, "export") { Some(ItemTag::Export) }
    else if is_spelling(word, "defn") { Some(ItemTag::Defn) }
    else if is_spelling(word, "defmacro") { Some(ItemTag::Defmacro) }
    else { None }
}

spec fn item_tag(source: &str, forms: Seq<Form>, root: usize) -> Option<ItemTag> {
    if forms[root as int] is List && root + 1 < subtree_limit(forms, root) <= forms.len()
        && plain_name(forms[root + 1])
    {
        word_tag(spelling(source, forms[root + 1]))
    } else {
        None
    }
}

fn read_item_tag(source: &str, forms: &[Form], root: usize) -> (tag: Option<ItemTag>)
    requires usable_forms(source, forms@), root < forms@.len(),
    ensures
        tag == item_tag(source, forms@, root),
        tag.is_some() ==> forms@[root as int] is List && root + 2 <= subtree_limit(forms@, root),
{
    if !matches!(&forms[root], Form::List { .. }) { return None; }
    let end = subtree_end(forms, root);
    assert(root < end <= forms@.len());
    let head = root + 1;
    if head >= end || !is_name(&forms[head]) { return None; }
    read_tag(source_word(source, forms, head))
}

spec fn spans_model(forms: Seq<Form>, first: usize, end: usize) -> Seq<Range<usize>> {
    Seq::new((end - first) as nat, |i: int| form_span(forms[first + i]))
}

fn collect_spans(forms: &[Form], first: usize, end: usize) -> (spans: Vec<Range<usize>>)
    requires first <= end <= forms@.len(),
    ensures spans@ == spans_model(forms@, first, end),
{
    let mut spans = Vec::new();
    let mut at = first;
    while at < end
        invariant
            first <= at <= end <= forms@.len(),
            spans@.len() == at - first,
            forall|i: int| 0 <= i < spans@.len() ==> #[trigger] spans@[i] == form_span(forms@[first + i]),
        decreases end - at,
    {
        spans.push(span_of(&forms[at]));
        at += 1;
    }
    assert(spans@ =~= spans_model(forms@, first, end));
    spans
}

spec fn first_invalid_parameter(forms: Seq<Form>, first: usize, end: usize) -> Option<usize> {
    if exists|i: int| first <= i < end && !plain_name(#[trigger] forms[i]) {
        Some(choose|i: usize| first <= i < end && !plain_name(#[trigger] forms[i as int])
            && (forall|j: int| first <= j < i ==> plain_name(#[trigger] forms[j])))
    } else {
        None
    }
}

proof fn first_parameter_is_unique(forms: Seq<Form>, first: usize, end: usize, i: usize)
    requires first <= i < end, !plain_name(forms[i as int]),
        forall|j: int| first <= j < i ==> plain_name(#[trigger] forms[j]),
    ensures first_invalid_parameter(forms, first, end) == Some(i),
{
    assert(exists|k: int| first <= k < end && !plain_name(#[trigger] forms[k]));
    let chosen = choose|k: usize| first <= k < end && !plain_name(#[trigger] forms[k as int])
        && (forall|j: int| first <= j < k ==> plain_name(#[trigger] forms[j]));
    if chosen < i { assert(plain_name(forms[chosen as int])); }
    if i < chosen { assert(plain_name(forms[i as int])); }
}

spec fn macro_error(forms: Seq<Form>, index: usize, part: MacroPart) -> MetaFileError {
    MetaFileError::Defmacro { span: form_span(forms[index as int]), part }
}

spec fn macro_sites(forms: Seq<Form>, root: usize) -> Result<(usize, usize, usize), MetaFileError> {
    let end = subtree_limit(forms, root);
    if !(root + 4 < end <= forms.len()) {
        Err(macro_error(forms, root, MacroPart::Declaration))
    } else if !plain_name(forms[root + 2]) {
        Err(macro_error(forms, (root + 2) as usize, MacroPart::Name))
    } else {
        let names = (root + 3) as usize;
        let body = subtree_limit(forms, names);
        if !(forms[names as int] is List) {
            Err(macro_error(forms, names, MacroPart::Parameters))
        } else if !(names < body < end && subtree_limit(forms, body) == end) {
            Err(macro_error(forms, root, MacroPart::Declaration))
        } else {
            Ok(((root + 2) as usize, names, body))
        }
    }
}

fn read_macro_sites(forms: &[Form], root: usize) -> (sites: Result<(usize, usize, usize), MetaFileError>)
    requires complete_list_indices(forms@), root < forms@.len(), forms@[root as int] is List,
    ensures sites == macro_sites(forms@, root),
        sites matches Ok((name, names, body)) ==> name < names < body < forms@.len(),
{
    let end = subtree_end(forms, root);
    assert(root < end <= forms@.len());
    if end - root <= 4 {
        return Err(MetaFileError::Defmacro { span: span_of(&forms[root]), part: MacroPart::Declaration });
    }
    let name = root + 2;
    if !is_name(&forms[name]) {
        return Err(MetaFileError::Defmacro { span: span_of(&forms[name]), part: MacroPart::Name });
    }
    let names = root + 3;
    if !matches!(&forms[names], Form::List { .. }) {
        return Err(MetaFileError::Defmacro { span: span_of(&forms[names]), part: MacroPart::Parameters });
    }
    let body = subtree_end(forms, names);
    assert(names < body <= forms@.len());
    if body >= end || subtree_end(forms, body) != end {
        return Err(MetaFileError::Defmacro { span: span_of(&forms[root]), part: MacroPart::Declaration });
    }
    Ok((name, names, body))
}

spec fn macro_model(forms: Seq<Form>, root: usize) -> Result<ItemContents, MetaFileError> {
    match macro_sites(forms, root) {
        Err(error) => Err(error),
        Ok((name, names, body)) => {
            let first = (names + 1) as usize;
            match first_invalid_parameter(forms, first, body) {
                Some(index) => Err(macro_error(forms, index, MacroPart::ParameterName)),
                None => Ok(ItemContents::Defmacro(form_span(forms[name as int]),
                    spans_model(forms, first, body), form_span(forms[body as int]))),
            }
        }
    }
}

spec fn kind_result(result: Result<MetaItemKind, MetaFileError>) -> Result<ItemContents, MetaFileError> {
    match result { Ok(kind) => Ok(kind_view(kind)), Err(error) => Err(error) }
}

fn read_macro(_source: &str, forms: &[Form], root: usize) -> (result: Result<MetaItemKind, MetaFileError>)
    requires usable_forms(_source, forms@), root < forms@.len(), forms@[root as int] is List,
    ensures kind_result(result) == macro_model(forms@, root),
        result matches Ok(kind) ==> binding_kind_span_valid(_source, kind),
{
    let (name, names, body) = read_macro_sites(forms, root)?;
    let first = names + 1;
    let mut at = first;
    while at < body
        invariant
            first <= at <= body < forms@.len(), first == names + 1,
            macro_sites(forms@, root) == Ok((name, names, body)),
            forall|i: int| first <= i < at ==> plain_name(#[trigger] forms@[i]),
        decreases body - at,
    {
        if !is_name(&forms[at]) {
            proof { first_parameter_is_unique(forms@, first, body, at); }
            return Err(MetaFileError::Defmacro { span: span_of(&forms[at]), part: MacroPart::ParameterName });
        }
        at += 1;
    }
    assert(first_invalid_parameter(forms@, first, body).is_none());
    proof { form_span_readable(_source, forms@, name); }
    Ok(MetaItemKind::Defmacro {
        name: span_of(&forms[name]), parameters: collect_spans(forms, first, body), body: span_of(&forms[body]),
    })
}


spec fn directive_issue(
    source: &str, forms: Seq<Form>, first: int, end: int, close: usize, head: Head,
) -> MetaFileError {
    let (kind, span) = choose|kind: HeaderError, span: Range<usize>|
        directive_error_evidence(source, forms, first, end, close, head, kind, span);
    MetaFileError::Directive { span, kind }
}

proof fn directive_issue_is_unique(
    source: &str, forms: Seq<Form>, first: int, end: int, close: usize, head: Head,
    kind: HeaderError, span: Range<usize>,
)
    requires
        head is Namespace || head is Use || head is Export,
        directive_error_evidence(source, forms, first, end, close, head, kind, span),
    ensures directive_issue(source, forms, first, end, close, head) == (MetaFileError::Directive { span, kind }),
{
    let (other, position) = choose|other: HeaderError, position: Range<usize>|
        directive_error_evidence(source, forms, first, end, close, head, other, position);
    directive_errors_agree(source, forms, first, end, close, head, (kind, span), (other, position));
}

spec fn direct_item_model(source: &str, forms: Seq<Form>, root: usize, head: Head)
    -> Result<ItemContents, MetaFileError>
{
    let first = (root + 2) as usize;
    let end = subtree_limit(forms, root);
    let close = (form_span(forms[root as int]).end - 1) as usize;
    if !directive_arguments_match(source, forms, first as int, end as int, head) {
        Err(directive_issue(source, forms, first as int, end as int, close, head))
    } else {
        match head {
            Head::Namespace => Ok(ItemContents::Namespace(form_span(forms[first as int]))),
            Head::Use => Ok(ItemContents::Use(form_span(forms[first as int]), form_span(forms[first + 1]))),
            _ => Ok(ItemContents::Export(spans_model(forms, first, end))),
        }
    }
}

fn read_directive(source: &str, forms: &[Form], root: usize, head: Head)
    -> (result: Result<MetaItemKind, MetaFileError>)
    requires
        meta_forms(source, forms@), root < forms@.len(), forms@[root as int] is List,
        root + 2 <= subtree_limit(forms@, root), head is Namespace || head is Use || head is Export,
    ensures kind_result(result) == direct_item_model(source, forms@, root, head),
        result matches Ok(kind) ==> binding_kind_span_valid(source, kind),
{
    let end = subtree_end(forms, root);
    let span = span_of(&forms[root]);
    proof { reveal(list_source_delimiters); }
    assert(root + 2 <= end <= forms@.len());
    assert(0 < span.end <= source.spec_bytes().len());
    let close = span.end - 1;
    let first = root + 2;
    let check = check_named_directive(source, forms, first, end, close, head);
    match check {
        Some(Ok(())) => Ok(match head {
            Head::Namespace => {
                proof { form_span_readable(source, forms@, first); }
                MetaItemKind::Namespace { path: span_of(&forms[first]) }
            },
            Head::Use => MetaItemKind::Use { target: span_of(&forms[first]), alias: span_of(&forms[first + 1]) },
            _ => MetaItemKind::Export { names: collect_spans(forms, first, end) },
        }),
        Some(Err((kind, span))) => {
            proof { directive_issue_is_unique(source, forms@, first as int, end as int, close, head, kind, span); }
            Err(MetaFileError::Directive { span, kind })
        }
        None => unreachable!(),
    }
}

spec fn meta_forms(source: &str, forms: Seq<Form>) -> bool {
    usable_forms(source, forms) && list_source_delimiters(source, forms, false)
}

spec fn item_model(source: &str, forms: Seq<Form>, root: usize, in_namespace: bool)
    -> Result<ItemContents, MetaFileError>
{
    match item_tag(source, forms, root) {
        Some(ItemTag::Namespace) if !in_namespace => direct_item_model(source, forms, root, Head::Namespace),
        Some(ItemTag::Use) => direct_item_model(source, forms, root, Head::Use),
        Some(ItemTag::Export) => direct_item_model(source, forms, root, Head::Export),
        Some(ItemTag::Defn) => match declaration_model(source, forms, root) {
            Ok(header) => Ok(ItemContents::Defn(header)),
            Err(error) => Err(MetaFileError::Defn(error)),
        },
        Some(ItemTag::Defmacro) => macro_model(forms, root),
        _ => Err(MetaFileError::ExpectedItem(form_span(forms[root as int]))),
    }
}

fn read_item(source: &str, forms: &[Form], root: usize, in_namespace: bool)
    -> (result: Result<MetaItemKind, MetaFileError>)
    requires meta_forms(source, forms@), root < forms@.len(),
    ensures
        kind_result(result) == item_model(source, forms@, root, in_namespace),
        result matches Ok(kind) ==> binding_kind_span_valid(source, kind),
        result matches Ok(MetaItemKind::Namespace { path }) ==> !in_namespace
            && root + 3 <= subtree_limit(forms@, root)
            && forms@[root as int] is List
            && path == form_span(forms@[root + 2]),
{
    match read_item_tag(source, forms, root) {
        Some(ItemTag::Namespace) if !in_namespace => read_directive(source, forms, root, Head::Namespace),
        Some(ItemTag::Use) => read_directive(source, forms, root, Head::Use),
        Some(ItemTag::Export) => read_directive(source, forms, root, Head::Export),
        Some(ItemTag::Defn) => match read_defn_at(source, forms, root) {
            Ok(header) => Ok(MetaItemKind::Defn(header)),
            Err(error) => Err(MetaFileError::Defn(error)),
        },
        Some(ItemTag::Defmacro) => read_macro(source, forms, root),
        _ => Err(MetaFileError::ExpectedItem(span_of(&forms[root]))),
    }
}


spec fn parent_span(forms: Seq<Form>, parent: Option<usize>) -> Option<Range<usize>> {
    match parent {
        Some(root) => Some(form_span(forms[root + 2])),
        None => None,
    }
}

spec fn index_region(form: Seq<Form>, first: usize, end: usize, parent: Option<usize>) -> bool {
    first <= end <= form.len()
        && match parent {
            Some(root) => root + 3 <= first && form[root as int] is List && subtree_limit(form, root) == end,
            None => end == form.len(),
        }
}

// 文法上の並びはリストの直下だけを読む。名前空間はブロックの直下を先に索引化する。
#[verifier::opaque]
spec fn region_model(
    source: &str, forms: Seq<Form>, at: usize, end: usize, parent: Option<usize>, prior: Seq<EntryView>,
) -> Result<Seq<EntryView>, MetaFileError>
    decreases end - at,
{
    if at >= end {
        Ok(prior)
    } else {
        match item_model(source, forms, at, parent.is_some()) {
            Err(error) => Err(error),
            Ok(content) => {
                let next = subtree_limit(forms, at);
                let span = form_span(forms[at as int]);
                let rows = prior.push((span, parent_span(forms, parent), content));
                if !(at < next <= end) {
                    Err(MetaFileError::ExpectedItem(span))
                } else if content is Namespace {
                    if at + 3 <= next {
                        match region_model(source, forms, (at + 3) as usize, next, Some(at), rows) {
                            Err(error) => Err(error),
                            Ok(children) => region_model(source, forms, next, end, parent, children),
                        }
                    } else {
                        Err(MetaFileError::ExpectedItem(span))
                    }
                } else {
                    region_model(source, forms, next, end, parent, rows)
                }
            }
        }
    }
}

spec fn entry_views(entries: Seq<MetaItem>) -> Seq<EntryView> {
    entries.map_values(|entry: MetaItem| entry_view(entry))
}

proof fn region_child_end(forms: Seq<Form>, root: usize, end: usize, parent: Option<usize>)
    requires
        complete_list_indices(forms), nested_list_indices(forms),
        index_region(forms, root, end, parent), root < end,
    ensures root < subtree_limit(forms, root) <= end,
{
    reveal(nested_list_indices);
    if let Some(outer) = parent {
        if forms[root as int] is List {
            assert(forms[outer as int] is List);
            assert(forms[root as int] is List);
        }
    }
}

proof fn region_finished(
    source: &str, forms: Seq<Form>, end: usize, parent: Option<usize>, prior: Seq<EntryView>,
)
    ensures region_model(source, forms, end, end, parent, prior) == Ok(prior),
{
    reveal(region_model);
}

proof fn region_failed(
    source: &str, forms: Seq<Form>, at: usize, end: usize, parent: Option<usize>,
    prior: Seq<EntryView>, error: MetaFileError,
)
    requires at < end, item_model(source, forms, at, parent.is_some()) == Err(error),
    ensures region_model(source, forms, at, end, parent, prior) == Err(error),
{
    reveal(region_model);
}

proof fn region_advanced(
    source: &str, forms: Seq<Form>, at: usize, end: usize, parent: Option<usize>,
    prior: Seq<EntryView>, content: ItemContents, next: usize,
)
    requires
        at < next <= end, next == subtree_limit(forms, at),
        item_model(source, forms, at, parent.is_some()) == Ok(content),
        content is Namespace ==> at + 3 <= next,
    ensures ({
        let rows = prior.push((form_span(forms[at as int]), parent_span(forms, parent), content));
        region_model(source, forms, at, end, parent, prior) == if content is Namespace {
            match region_model(source, forms, (at + 3) as usize, next, Some(at), rows) {
                Err(error) => Err(error),
                Ok(children) => region_model(source, forms, next, end, parent, children),
            }
        } else {
            region_model(source, forms, next, end, parent, rows)
        }
    }),
{
    reveal(region_model);
}

fn read_region(
    source: &str, forms: &[Form], first: usize, end: usize, parent: Option<usize>, entries: &mut Vec<MetaItem>,
) -> (result: Result<(), MetaFileError>)
    requires meta_forms(source, forms@), index_region(forms@, first, end, parent),
        meta_binding_spans_valid(source, old(entries)@),
    ensures result.is_ok() ==> meta_binding_spans_valid(source, final(entries)@),
        region_model(source, forms@, first, end, parent, entry_views(old(entries)@))
        == match result { Ok(()) => Ok(entry_views(final(entries)@)), Err(error) => Err(error) },
    decreases end - first,
{
    let mut at = first;
    let ghost initial = entry_views(entries@);
    while at < end
        invariant
            meta_forms(source, forms@), first <= at, index_region(forms@, at, end, parent),
            initial == entry_views(old(entries)@),
            meta_binding_spans_valid(source, entries@),
            region_model(source, forms@, first, end, parent, initial)
                == region_model(source, forms@, at, end, parent, entry_views(entries@)),
        decreases end - at,
    {
        let kind = match read_item(source, forms, at, parent.is_some()) {
            Ok(kind) => kind,
            Err(error) => {
                proof { region_failed(source, forms@, at, end, parent, entry_views(entries@), error); }
                return Err(error);
            }
        };
        let is_namespace = matches!(&kind, MetaItemKind::Namespace { .. });
        let namespace = match parent {
            Some(root) => {
                proof { form_span_readable(source, forms@, (root + 2) as usize); }
                Some(span_of(&forms[root + 2]))
            },
            None => None,
        };
        proof { region_child_end(forms@, at, end, parent); }
        let next = subtree_end(forms, at);
        let span = span_of(&forms[at]);
        let ghost content = kind_view(kind);
        let entry = MetaItem { span, namespace, kind };
        let ghost pushed = entry_view(entry);
        let ghost prior = entry_views(entries@);
        proof { region_advanced(source, forms@, at, end, parent, prior, content, next); }
        let ghost previous = entries@;
        entries.push(entry);
        assert(meta_binding_spans_valid(source, entries@)) by {
            assert forall|i: int| 0 <= i < entries@.len() implies {
                let item = #[trigger] entries@[i];
                &&& binding_kind_span_valid(source, item.kind)
                &&& (item.namespace matches Some(path) ==> readable_span(source, path))
            } by {
                if i < previous.len() {
                    assert(entries@[i] == previous[i]);
                }
            };
        };
        assert(entry_views(entries@) =~= prior.push(pushed));
        if is_namespace {
            read_region(source, forms, at + 3, next, Some(at), entries)?;
        }
        at = next;
    }
    proof { region_finished(source, forms@, end, parent, entry_views(entries@)); }
    Ok(())
}

/// 厳格なファイル索引の受理条件を表す。
///
/// 共通 S 式の構文と、各トップレベルまたは名前空間ブロック内のフォームを検査する。
pub closed spec fn valid_meta_file(source: &str) -> bool {
    well_formed_sexpr(source) && (sexpr_form_model(source) matches Some(forms)
        && region_model(source, forms, 0, forms.len() as usize, None, Seq::empty()).is_ok())
}

/// ファイルの索引または最初の構文違反が元ソースに対応することを表す。
pub closed spec fn meta_file_matches(source: &str, result: Result<Vec<MetaItem>, MetaFileError>) -> bool {
    if !well_formed_sexpr(source) {
        result matches Err(MetaFileError::Syntax(error)) && strict_syntax_rejection(source, error)
            && syntax_error_evidence(source, error)
    } else {
        sexpr_form_model(source) matches Some(forms)
            && region_model(source, forms, 0, forms.len() as usize, None, Seq::empty())
                == match result {
                    Ok(entries) => Ok(entry_views(entries@)),
                    Err(error) => Err(error),
                }
    }
}

/// 2つの索引項目の位置と内容が一致することを表す。
pub open spec fn same_meta_item(left: MetaItem, right: MetaItem) -> bool {
    left.span == right.span && left.namespace == right.namespace
        && match (left.kind, right.kind) {
            (MetaItemKind::Namespace { path: a }, MetaItemKind::Namespace { path: b }) => a == b,
            (MetaItemKind::Use { target: a, alias: x }, MetaItemKind::Use { target: b, alias: y }) => a == b && x == y,
            (MetaItemKind::Export { names: a }, MetaItemKind::Export { names: b }) => a@ == b@,
            (MetaItemKind::Defn(a), MetaItemKind::Defn(b)) => a.span == b.span && a.name_span == b.name_span
                && a.parameters@ == b.parameters@ && a.result_type == b.result_type && a.body_span == b.body_span,
            (MetaItemKind::Defmacro { name: a, parameters: x, body: left_body },
                MetaItemKind::Defmacro { name: b, parameters: y, body: right_body }) =>
                a == b && x@ == y@ && left_body == right_body,
            _ => false,
        }
}

proof fn item_views_agree(left: MetaItem, right: MetaItem)
    requires entry_view(left) == entry_view(right),
    ensures same_meta_item(left, right),
{}

/// 同じソースを厳格に索引化した結果は、索引の全項目またはエラー全体が一致する。
pub proof fn meta_file_results_agree(
    source: &str, a: Result<Vec<MetaItem>, MetaFileError>, b: Result<Vec<MetaItem>, MetaFileError>,
)
    requires meta_file_matches(source, a), meta_file_matches(source, b),
    ensures match (a, b) {
        (Ok(left), Ok(right)) => left@.len() == right@.len()
            && (forall|i: int| 0 <= i < left@.len() ==> #[trigger] same_meta_item(left@[i], right@[i])),
        (Err(left), Err(right)) => left == right,
        _ => false,
    },
{
    if !well_formed_sexpr(source) {
        let left = a->Err_0->Syntax_0;
        let right = b->Err_0->Syntax_0;
        reveal(syntax_error_evidence);
        assert(structural_error_location(source, left) && structural_error_location(source, right));
        strict_token_errors_agree(source, left, right);
    }
    if let (Ok(left), Ok(right)) = (a, b) {
        assert(entry_views(left@) == entry_views(right@));
        assert forall|i: int| 0 <= i < left@.len()
            implies #[trigger] same_meta_item(left@[i], right@[i]) by {
            assert(entry_views(left@)[i] == entry_view(left@[i]));
            assert(entry_views(right@)[i] == entry_view(right@[i]));
            item_views_agree(left@[i], right@[i]);
        };
    }
}
/// 1つの NCG2M ファイルを厳格に解析し、フォームを記述順に返す。
///
/// 名前空間の要素を、そのブロックに含まれる要素より先に返す。各範囲はファイル先頭からの
/// UTF-8 半開バイト範囲。式の検査、型と名前の解決は、索引が保持した範囲を使って後段で行う。
///
/// # Errors
///
/// ファイル全体の字句と共通 S 式を先に検査する。続いてフォームを記述順に検査し、最初の違反を返す。
pub fn index_meta_file(source: &str) -> (result: Result<Vec<MetaItem>, MetaFileError>)
    ensures result.is_ok() == valid_meta_file(source), meta_file_matches(source, result),
        result matches Ok(items) ==> meta_binding_spans_valid(source, items@),
{
    let forms = match syntax::parse(source) {
        Ok(forms) => forms,
        Err(error) => return Err(MetaFileError::Syntax(error)),
    };
    let mut entries = Vec::new();
    assert(entry_views(entries@) =~= Seq::<EntryView>::empty());
    assert(meta_binding_spans_valid(source, entries@));
    read_region(source, &forms, 0, forms.len(), None, &mut entries)?;
    Ok(entries)
}

}
