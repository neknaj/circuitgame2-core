//! NCG2M のファイルを厳格に解析し、宣言と名前解決の指示を元の順序で索引化する。

use alloc::vec::Vec;
use core::ops::Range;
use crate::syntax::{
    self, Form,
    circuit::{Head, HeaderError, check_named_directive},
};
#[cfg(verus_only)]
use crate::syntax::{
    AtomKind, bare_atom_kind, complete_list_indices, form_span, form_spans_valid, list_source_delimiters, nested_list_indices, strict_preorder_ranges, strict_sexpr_derivation, sexpr_form_model, strict_syntax_rejection,
    strict_token_errors_agree, structural_error_location, syntax_error_evidence, well_formed_sexpr,
    circuit::{directive_arguments_match, directive_error_evidence, directive_errors_agree},
};
use super::defn::{DefnHeader, DefnHeaderError, is_name, read_defn_at, span_of};
#[cfg(verus_only)]
use super::defn::{HeaderContents, defn_header_matches, declaration_model, form_span_readable, header_contents, indexed_body_site, plain_name, readable_span, signature_spans_valid, standalone_header_is_only_root, tagged_arguments, usable_forms};
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

pub(crate) open spec fn meta_use_spans_valid(source: &str, target: Range<usize>, alias: Range<usize>) -> bool {
    &&& readable_span(source, target)
    &&& readable_span(source, alias)
    &&& bare_atom_kind(source.spec_bytes()[target.start as int..target.end as int]) == Some(AtomKind::AbsolutePath)
    &&& bare_atom_kind(source.spec_bytes()[alias.start as int..alias.end as int]) == Some(AtomKind::Name)
}

spec fn binding_kind_span_valid(source: &str, kind: MetaItemKind) -> bool {
    match kind {
        MetaItemKind::Namespace { path } => readable_span(source, path),
        MetaItemKind::Defn(header) => readable_span(source, header.name_span) && signature_spans_valid(source, header),
        MetaItemKind::Defmacro { name, .. } => readable_span(source, name),
        MetaItemKind::Use { target, alias } => meta_use_spans_valid(source, target, alias),
        MetaItemKind::Export { names } => forall|i: int| 0 <= i < names@.len()
            ==> readable_span(source, #[trigger] names@[i]),
    }
}

/// 宣言名、署名、名前空間のパスと名前解決の指示の引数が、元ソースの UTF-8 文字境界にあることを表す。
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

/// 公開名の範囲が元ソースの UTF-8 文字境界にあることを示す。
pub(crate) proof fn meta_export_span_evidence(source: &str, items: Seq<MetaItem>, rank: int, arg: int)
    requires meta_binding_spans_valid(source, items), 0 <= rank < items.len(),
        items[rank].kind is Export, 0 <= arg < items[rank].kind->Export_names@.len(),
    ensures readable_span(source, items[rank].kind->Export_names@[arg]),
{}

/// 別名指定の参照先と別名が、元ソース上の対応する字句を指すことを示す。
pub(crate) proof fn meta_use_span_evidence(source: &str, items: Seq<MetaItem>, item: int)
    requires meta_binding_spans_valid(source, items), 0 <= item < items.len(), items[item].kind is Use,
    ensures meta_use_spans_valid(source, items[item].kind->Use_target, items[item].kind->Use_alias),
{}

pub(crate) proof fn meta_defn_signature_spans(source: &str, items: Seq<MetaItem>, rank: int)
    requires meta_binding_spans_valid(source, items), 0 <= rank < items.len(), items[rank].kind is Defn,
    ensures signature_spans_valid(source, items[rank].kind->Defn_0),
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
            Head::Use => {
                proof {
                    reveal(form_spans_valid);
                    form_span_readable(source, forms@, first);
                    form_span_readable(source, forms@, (first + 1) as usize);
                    assert(forms@[first as int]->Atom_kind == AtomKind::AbsolutePath);
                    assert(forms@[first + 1]->Atom_kind == AtomKind::Name);
                }
                MetaItemKind::Use { target: span_of(&forms[first]), alias: span_of(&forms[first + 1]) }
            },
            _ => {
                let names = collect_spans(forms, first, end);
                proof {
                    assert forall|i: int| 0 <= i < names@.len() implies readable_span(source, #[trigger] names@[i]) by {
                        assert(names@[i] == form_span(forms@[first + i]));
                        form_span_readable(source, forms@, (first + i) as usize);
                    };
                }
                MetaItemKind::Export { names }
            },
        }),
        Some(Err((kind, span))) => {
            proof { directive_issue_is_unique(source, forms@, first as int, end as int, close, head, kind, span); }
            Err(MetaFileError::Directive { span, kind })
        }
        None => unreachable!(),
    }
}

pub(super) proof fn indexed_standalone_header(
    source: &str, forms: Seq<Form>, entries: Vec<MetaItem>, standalone: super::defn::DefnHeader,
)
    requires
        meta_ast_matches(source, forms, entries@),
        meta_file_matches(source, Ok(entries)),
        defn_header_matches(source, Ok(standalone)),
    ensures
        entries@.len() == 1,
        entries@[0].kind is Defn,
        header_contents(entries@[0].kind->Defn_0) == header_contents(standalone),
{
    standalone_header_is_only_root(source, forms, standalone);
    let content = ItemContents::Defn(header_contents(standalone));
    let single = (form_span(forms[0]), None, content);
    let end = forms.len() as usize;
    assert(tagged_arguments(source, forms, 0, "defn", true).is_some());
    assert(forms[0] is List && 1 < subtree_limit(forms, 0) <= forms.len());
    assert(plain_name(forms[1]));
    assert(spelling(source, forms[1]) == "defn".spec_bytes());
    reveal_strlit("defn");
    reveal_strlit("namespace");
    reveal_strlit("use");
    reveal_strlit("export");
    vstd::utf8::encode_utf8_decode_utf8("defn"@);
    vstd::utf8::encode_utf8_decode_utf8("namespace"@);
    vstd::utf8::encode_utf8_decode_utf8("use"@);
    vstd::utf8::encode_utf8_decode_utf8("export"@);
    assert(word_tag(spelling(source, forms[1])) == Some(ItemTag::Defn));
    assert(item_tag(source, forms, 0) == Some(ItemTag::Defn));
    assert(item_model(source, forms, 0, false) == Ok(content));
    region_advanced(source, forms, 0, end, None, Seq::empty(), content, end);
    region_finished(source, forms, end, None, Seq::empty().push(single));
    assert(region_model(source, forms, 0, end, None, Seq::empty()) == Ok(Seq::empty().push(single)));
    assert(region_model(source, forms, 0, end, None, Seq::empty()) == Ok(entry_views(entries@)));
    assert(entry_views(entries@) == Seq::empty().push(single));
    assert(entry_views(entries@).len() == entries@.len());
    assert(entry_views(entries@)[0] == entry_view(entries@[0]));
}

pub(super) proof fn meta_ast_unique_start(forms: Seq<Form>, first: usize, second: usize)
    requires strict_preorder_ranges(forms), first < forms.len(), second < forms.len(),
        form_span(forms[first as int]).start == form_span(forms[second as int]).start,
    ensures first == second,
{
    if first < second { starts_in_source_order(forms, first as int, second as int); }
    if second < first { starts_in_source_order(forms, second as int, first as int); }
}

spec fn meta_forms(source: &str, forms: Seq<Form>) -> bool {
    usable_forms(source, forms) && list_source_delimiters(source, forms, false)
}

spec fn defn_item_at(source: &str, forms: Seq<Form>, at: usize, kind: MetaItemKind) -> bool {
    match kind {
        MetaItemKind::Defn(header) => exists|body: usize| #[trigger] indexed_body_site(source, forms, at, body, header),
        _ => true,
    }
}

spec fn defn_items_in_forms(source: &str, forms: Seq<Form>, entries: Seq<MetaItem>) -> bool {
    forall|i: int| 0 <= i < entries.len() ==> {
        let entry = #[trigger] entries[i];
        entry.kind matches MetaItemKind::Defn(header) ==> exists|root: usize, body: usize|
            #[trigger] indexed_body_site(source, forms, root, body, header)
    }
}

pub(crate) closed spec fn meta_ast_matches(source: &str, forms: Seq<Form>, entries: Seq<MetaItem>) -> bool {
    &&& usable_forms(source, forms)
    &&& strict_preorder_ranges(forms)
    &&& sexpr_form_model(source) == Some(forms)
    &&& defn_items_in_forms(source, forms, entries)
}

pub(super) proof fn meta_ast_source(source: &str, forms: Seq<Form>, entries: Seq<MetaItem>)
    requires meta_ast_matches(source, forms, entries),
    ensures sexpr_form_model(source) == Some(forms),
{}

pub(super) proof fn meta_ast_body_origin(source: &str, forms: Seq<Form>, entries: Seq<MetaItem>, item: int)
    -> (site: (usize, usize))
    requires meta_ast_matches(source, forms, entries), 0 <= item < entries.len(), entries[item].kind is Defn,
    ensures usable_forms(source, forms), strict_preorder_ranges(forms), sexpr_form_model(source) == Some(forms),
        indexed_body_site(source, forms, site.0, site.1, entries[item].kind->Defn_0),
{
    let header = entries[item].kind->Defn_0;
    choose|root: usize, body: usize| #[trigger] indexed_body_site(source, forms, root, body, header)
}


proof fn starts_in_source_order(forms: Seq<Form>, earlier: int, later: int)
    requires strict_preorder_ranges(forms), 0 <= earlier < later < forms.len(),
    ensures form_span(forms[earlier]).start < form_span(forms[later]).start,
{
    reveal(strict_preorder_ranges);
    assert(crate::syntax::preorder_range_pair(forms[earlier], forms[later], later));
}

fn find_form_start(forms: &[Form], byte: usize) -> (found: Option<usize>)
    requires strict_preorder_ranges(forms@),
    ensures found matches Some(at) ==> at < forms@.len() && form_span(forms@[at as int]).start == byte,
        found.is_none() ==> (forall|i: int| 0 <= i < forms@.len()
            ==> form_span(#[trigger] forms@[i]).start != byte),
{
    let mut low = 0;
    let mut high = forms.len();
    while low < high
        invariant
            strict_preorder_ranges(forms@),
            low <= high <= forms@.len(),
            forall|i: int| 0 <= i < low ==> form_span(#[trigger] forms@[i]).start < byte,
            forall|i: int| high <= i < forms@.len() ==> byte < form_span(#[trigger] forms@[i]).start,
        decreases high - low,
    {
        let middle = low + (high - low) / 2;
        let start = span_of(&forms[middle]).start;
        if start == byte {
            return Some(middle);
        } else if start < byte {
            assert forall|i: int| low <= i <= middle implies form_span(#[trigger] forms@[i]).start < byte by {
                if i < middle { starts_in_source_order(forms@, i, middle as int); }
            };
            low = middle + 1;
        } else {
            assert forall|i: int| middle <= i < high implies byte < form_span(#[trigger] forms@[i]).start by {
                if middle < i { starts_in_source_order(forms@, middle as int, i); }
            };
            high = middle;
        }
    }
    None
}

pub(super) fn indexed_meta_body(
    _source: &str, forms: &[Form], entries: &[MetaItem], item: usize,
) -> (body: usize)
    requires meta_ast_matches(_source, forms@, entries@), item < entries@.len(), entries@[item as int].kind is Defn,
    ensures usable_forms(_source, forms@), body < forms@.len(),
        exists|root: usize| #[trigger] indexed_body_site(_source, forms@, root, body, entries@[item as int].kind->Defn_0),
{
    let ghost witness = meta_ast_body_origin(_source, forms@, entries@, item as int);
    let MetaItemKind::Defn(header) = &entries[item].kind else { unreachable!() };
    let Some(found) = find_form_start(forms, header.body_span.start) else { unreachable!() };
    proof {
        if found < witness.1 {
            starts_in_source_order(forms@, found as int, witness.1 as int);
        } else if witness.1 < found {
            starts_in_source_order(forms@, witness.1 as int, found as int);
        }
        assert(found == witness.1);
    }
    found
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
        result matches Ok(kind) ==> binding_kind_span_valid(source, kind) && defn_item_at(source, forms@, root, kind),
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
        meta_binding_spans_valid(source, old(entries)@), defn_items_in_forms(source, forms@, old(entries)@),
    ensures result.is_ok() ==> meta_binding_spans_valid(source, final(entries)@)
        && defn_items_in_forms(source, forms@, final(entries)@),
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
            defn_items_in_forms(source, forms@, entries@),
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
        assert(defn_items_in_forms(source, forms@, entries@)) by {
            assert forall|i: int| 0 <= i < entries@.len() implies {
                let row = #[trigger] entries@[i];
                row.kind matches MetaItemKind::Defn(header) ==> exists|root: usize, body: usize|
                    #[trigger] indexed_body_site(source, forms@, root, body, header)
            } by {
                if i < previous.len() {
                    assert(entries@[i] == previous[i]);
                } else if let MetaItemKind::Defn(header) = entry.kind {
                    let root = at;
                    let body = choose|body: usize| #[trigger] indexed_body_site(source, forms@, root, body, header);
                    assert(indexed_body_site(source, forms@, root, body, header));
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
    match index_meta_with_forms(source) {
        Ok((items, _)) => Ok(items),
        Err(error) => Err(error),
    }
}

pub(crate) fn index_meta_with_forms(source: &str)
    -> (result: Result<(Vec<MetaItem>, Vec<Form>), MetaFileError>)
    ensures result.is_ok() == valid_meta_file(source),
        match result {
            Ok((items, forms)) => meta_file_matches(source, Ok(items))
                && meta_binding_spans_valid(source, items@) && meta_ast_matches(source, forms@, items@),
            Err(error) => meta_file_matches(source, Err(error)),
        },
{
    let forms = match syntax::parse(source) {
        Ok(forms) => forms,
        Err(error) => return Err(MetaFileError::Syntax(error)),
    };
    let mut entries = Vec::new();
    assert(entry_views(entries@) =~= Seq::<EntryView>::empty());
    assert(meta_binding_spans_valid(source, entries@));
    assert(defn_items_in_forms(source, forms@, entries@));
    read_region(source, &forms, 0, forms.len(), None, &mut entries)?;
    assert(strict_sexpr_derivation(source, forms@));
    assert(usable_forms(source, forms@));
    assert(strict_preorder_ranges(forms@)) by { reveal(strict_sexpr_derivation); }
    assert(meta_ast_matches(source, forms@, entries@));
    Ok((entries, forms))
}

}
