//! トップレベルのフォームと名前空間の直下を入力順に索引に載せる。

use super::*;
#[cfg(verus_only)]
use crate::{sexpr_form_model, syntax_error_evidence, well_formed_sexpr};

verus! {

/// 索引を付ける位置と、直接の親名前空間の添字を定める。
pub open spec fn indexed_location(source: &str, forms: Seq<Form>, index: int, namespace: Option<usize>) -> bool {
    match namespace {
        None => direct_form_in_range(forms, 0, forms.len() as int, index),
        Some(parent) => {
            &&& direct_form_in_range(forms, 0, forms.len() as int, parent as int)
            &&& form_has_head(source, forms, parent as int, false, Head::Namespace)
            &&& direct_form_in_range(forms, parent + 3, forms[parent as int]->List_end as int, index)
        },
    }
}

spec fn forms_before(source: &str, forms: Seq<Form>, cursor: int) -> bool {
    forall|index: int, namespace: Option<usize>| #[trigger] indexed_location(source, forms, index, namespace)
        && index < cursor ==> exists|head: Head| #[trigger] header_matches(source, forms, index, namespace.is_some(), head)
}

/// 元入力に対応する S 式の列が回路文法に従うことを表す。
pub closed spec fn circuit_source_matches(source: &str) -> bool {
    well_formed_sexpr(source) && (exists|forms: Seq<Form>| sexpr_form_model(source) == Some(forms)
        && #[trigger] forms_before(source, forms, forms.len() as int))
}

/// 字句、S 式、回路文法のいずれかの診断に根拠を与える。
///
/// 回路文法の診断では、入力全体が S 式の文法に従い、診断位置より前に検査するすべてのフォームが回路文法に従う。
pub closed spec fn circuit_source_error(source: &str, error: CircuitFormError) -> bool {
    match error {
        CircuitFormError::Syntax(error) => !well_formed_sexpr(source) && syntax_error_evidence(source, error),
        CircuitFormError::Header { kind, span } => well_formed_sexpr(source)
            && (exists|forms: Seq<Form>, index: int, namespace: Option<usize>|
                sexpr_form_model(source) == Some(forms)
                && #[trigger] indexed_location(source, forms, index, namespace)
                && forms_before(source, forms, index)
                && header_error_evidence(source, forms, index, namespace.is_some(), kind, span)),
    }
}

#[verifier::opaque]
spec fn index_prefix(source: &str, forms: Seq<Form>, entries: Seq<Entry>, cursor: int) -> bool {
    &&& forall|k: int| 0 <= k < entries.len() ==> {
        let entry = #[trigger] entries[k];
        &&& entry.form < cursor
        &&& indexed_location(source, forms, entry.form as int, entry.namespace)
        &&& header_matches(source, forms, entry.form as int, entry.namespace.is_some(), entry.head)
    }
    &&& forall|index: int, namespace: Option<usize>| #[trigger] indexed_location(source, forms, index, namespace)
        && index < cursor ==> exists|k: int| 0 <= k < entries.len()
            && (#[trigger] entries[k]).form == index && entries[k].namespace == namespace
    &&& forall|left: int, right: int| 0 <= left < right < entries.len()
        ==> (#[trigger] entries[left]).form < (#[trigger] entries[right]).form
}

/// 索引は対象位置を漏れなく一度ずつ含み、種別と親の添字を入力順に保存する。
pub closed spec fn circuit_index_matches(source: &str, forms: Seq<Form>, entries: Seq<Entry>) -> bool {
    sexpr_form_model(source) == Some(forms) && index_prefix(source, forms, entries, forms.len() as int)
}

/// 検証済みの索引項目の位置と種別を、回路文法の認識関係に結び付ける。
pub(super) proof fn indexed_entry_evidence(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, index: int,
)
    requires
        circuit_index_matches(source, forms, entries),
        0 <= index < entries.len(),
    ensures
        indexed_location(source, forms, entries[index].form as int, entries[index].namespace),
        header_matches(source, forms, entries[index].form as int, entries[index].namespace.is_some(), entries[index].head),
        forall|earlier: int| 0 <= earlier < index ==> (#[trigger] entries[earlier]).form < entries[index].form,
        entries[index].namespace matches Some(parent) ==>
            exists|head: Head| #[trigger] header_matches(source, forms, parent as int, false, head),
{
    reveal(index_prefix);
    if let Some(parent) = entries[index].namespace {
        let entry = entries[index];
        assert(indexed_location(source, forms, parent as int, None));
        reveal(direct_form_in_range);
        assert(parent < forms.len());
        indexed_prefix_is_valid(source, forms, entries, forms.len() as int);
    }
}

/// 索引に含まれる公開指定の引数と、所属名前空間のパスの位置を示す。
pub proof fn export_entry_evidence(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, entry: int,
)
    requires
        circuit_index_matches(source, forms, entries),
        0 <= entry < entries.len(),
        entries[entry].head is Export,
    ensures
        ({
            let item = entries[entry];
            let root = item.form as int;
            &&& 0 <= root < forms.len()
            &&& forms[root] is List
            &&& {
                let end = forms[root]->List_end as int;
                &&& root + 2 < end <= forms.len()
                &&& forall|i: int| root + 2 <= i < end ==> #[trigger] forms[i] is Atom
            }
        }),
        entries[entry].namespace matches Some(parent) ==>
            (parent + 2 < forms.len() && forms[parent + 2] is Atom),
{
    indexed_entry_evidence(source, forms, entries, entry);
    let item = entries[entry];
    let root = item.form as int;
    let end = forms[root]->List_end as int;
    assert(header_matches(source, forms, root, item.namespace.is_some(), Head::Export));
    reveal(header_arguments_match);
    assert(directive_arguments_match(source, forms, root + 2, end, Head::Export));
    assert forall|i: int| root + 2 <= i < end implies #[trigger] forms[i] is Atom by {
        assert(directive_word_at(source, forms, i, end, HeaderError::ExpectedName));
    };
    owner_path_evidence(source, forms, entries, entry);
}

proof fn owner_path_evidence(source: &str, forms: Seq<Form>, entries: Seq<Entry>, entry: int)
    requires
        circuit_index_matches(source, forms, entries),
        0 <= entry < entries.len(),
    ensures
        entries[entry].namespace matches Some(parent) ==>
            (parent + 2 < forms.len() && forms[parent + 2] is Atom),
{
    indexed_entry_evidence(source, forms, entries, entry);
    reveal(header_arguments_match);
    let item = entries[entry];
    if let Some(parent) = item.namespace {
        let head = choose|head: Head| #[trigger] header_matches(source, forms, parent as int, false, head);
        names::namespace_head_is_unique(source, forms[parent + 1], head);
        assert(header_matches(source, forms, parent as int, false, Head::Namespace));
        assert(directive_word_at(source, forms, parent + 2, forms[parent as int]->List_end as int,
            HeaderError::ExpectedNamespacePath));
    }
}

/// 索引に含まれる `use` の参照先、別名、所属名前空間のパスの位置を示す。
pub proof fn use_entry_evidence(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, entry: int,
)
    requires
        circuit_index_matches(source, forms, entries),
        0 <= entry < entries.len(),
        entries[entry].head is Use,
    ensures
        ({
            let item = entries[entry];
            let root = item.form as int;
            &&& 0 <= root < root + 3 < forms.len()
            &&& forms[root + 2] is Atom && forms[root + 2]->Atom_kind is AbsolutePath
            &&& forms[root + 3] is Atom && forms[root + 3]->Atom_kind is Name
        }),
        entries[entry].namespace matches Some(parent) ==>
            (parent + 2 < forms.len() && forms[parent + 2] is Atom),
{
    indexed_entry_evidence(source, forms, entries, entry);
    owner_path_evidence(source, forms, entries, entry);
    let item = entries[entry];
    let root = item.form as int;
    let limit = forms[root]->List_end as int;
    reveal(header_arguments_match);
    assert(header_matches(source, forms, root, item.namespace.is_some(), Head::Use));
    assert(directive_arguments_match(source, forms, root + 2, limit, Head::Use));
}

proof fn indexed_subtree_location(
    source: &str, forms: Seq<Form>, root: int, end: int, index: int, owner: Option<usize>,
)
    requires
        0 <= root < end <= forms.len(),
        direct_form_in_range(forms, 0, forms.len() as int, root),
        forms[root] is List && forms[root]->List_end == end,
        root <= index < end,
        indexed_location(source, forms, index, owner),
    ensures
        (index == root && owner is None)
        || (owner is Some && owner->Some_0 == root),
{
    reveal(direct_form_in_range);
    if let Some(parent) = owner {
        if parent < root {
            assert(forms[parent as int]->List_end <= root);
        } else if parent > root {
            assert(root < parent < end);
        }
    } else if root < index {
        assert(forms[root]->List_end <= index);
    }
}

proof fn root_index_gap(
    source: &str, forms: Seq<Form>, root: int, end: int, next: int, head: Head,
)
    requires
        0 <= root < end <= forms.len(),
        direct_form_in_range(forms, 0, forms.len() as int, root),
        forms[root] is List && forms[root]->List_end == end,
        forall|other: Head| #[trigger] form_has_head(source, forms, root, false, other) <==> other == head,
        if head is Namespace { next == root + 3 <= end } else { next == end },
    ensures
        forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
            && root <= index < next ==> index == root && owner is None,
{
    assert forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
        && root <= index < next implies index == root && owner is None by {
        indexed_subtree_location(source, forms, root, end, index, owner);
        if let Some(parent) = owner {
            assert(parent == root);
            assert(form_has_head(source, forms, root, false, Head::Namespace));
            reveal(direct_form_in_range);
            assert(root + 3 <= index);
        }
    };
}

proof fn member_index_gap(
    source: &str, forms: Seq<Form>, root: int, end: int, index: int, next: int,
)
    requires
        0 <= root < end <= forms.len(),
        direct_form_in_range(forms, 0, forms.len() as int, root),
        forms[root] is List && forms[root]->List_end == end,
        root + 3 <= index < next <= end,
        direct_form_in_range(forms, root + 3, end, index),
        following_direct_form(forms, index, next),
    ensures
        forall|at: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, at, owner)
            && index <= at < next ==> at == index && owner == Some(root as usize),
{
    reveal(following_direct_form);
    assert(form_region_ends_at(forms, root + 3, end)) by {
        assert(exists|parent: int| 0 <= parent < root + 3
            && #[trigger] forms[parent] is List && forms[parent]->List_end == end);
    };
    assert forall|at: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, at, owner)
        && index <= at < next implies at == index && owner == Some(root as usize) by {
        indexed_subtree_location(source, forms, root, end, at, owner);
        assert(owner == Some(root as usize));
        if at > index {
            assert(direct_form_in_range(forms, root + 3, end, at));
        }
    };
}

proof fn append_index_entry(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, entry: Entry, next: int,
)
    requires
        index_prefix(source, forms, entries, entry.form as int),
        entry.form < next,
        indexed_location(source, forms, entry.form as int, entry.namespace),
        header_matches(source, forms, entry.form as int, entry.namespace.is_some(), entry.head),
        forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
            && entry.form <= index < next ==> index == entry.form && owner == entry.namespace,
    ensures index_prefix(source, forms, entries.push(entry), next),
{
    reveal(index_prefix);
    let extended = entries.push(entry);
    assert forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
        && index < next implies exists|k: int| 0 <= k < extended.len()
            && (#[trigger] extended[k]).form == index && extended[k].namespace == owner by {
        if index < entry.form {
            let k = choose|k: int| 0 <= k < entries.len()
                && (#[trigger] entries[k]).form == index && entries[k].namespace == owner;
            assert(extended[k] == entries[k]);
        } else {
            assert(extended[entries.len() as int] == entry);
        }
    };
}

proof fn indexed_prefix_is_valid(source: &str, forms: Seq<Form>, entries: Seq<Entry>, cursor: int)
    requires index_prefix(source, forms, entries, cursor),
    ensures forms_before(source, forms, cursor),
{
    reveal(index_prefix);
    assert forall|index: int, owner: Option<usize>| #[trigger] indexed_location(source, forms, index, owner)
        && index < cursor implies exists|head: Head| #[trigger] header_matches(source, forms, index, owner.is_some(), head) by {
        let k = choose|k: int| 0 <= k < entries.len()
            && (#[trigger] entries[k]).form == index && entries[k].namespace == owner;
        assert(header_matches(source, forms, index, owner.is_some(), entries[k].head));
    };
}

proof fn reject_index_entry(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, index: int, owner: Option<usize>, kind: HeaderError, span: Range<usize>,
)
    requires
        well_formed_sexpr(source),
        sexpr_form_model(source) == Some(forms),
        index_prefix(source, forms, entries, index),
        indexed_location(source, forms, index, owner),
        0 <= index < forms.len(),
        forall|head: Head| !#[trigger] header_matches(source, forms, index, owner.is_some(), head),
        header_error_evidence(source, forms, index, owner.is_some(), kind, span),
    ensures
        !circuit_source_matches(source),
        circuit_source_error(source, CircuitFormError::Header { kind, span }),
{
    indexed_prefix_is_valid(source, forms, entries, index);
    assert(!forms_before(source, forms, forms.len() as int));
}

fn index_namespace(
    source: &str, forms: &[Form], entries: &mut Vec<Entry>, root: usize, first: usize, end: usize,
) -> (result: Result<(), CircuitFormError>)
    requires
        well_formed_sexpr(source),
        sexpr_form_model(source) == Some(forms@),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        list_source_delimiters(source, forms@, false),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        direct_form_in_range(forms@, 0, forms@.len() as int, root as int),
        form_has_head(source, forms@, root as int, false, Head::Namespace),
        forms@[root as int]->List_end == end,
        first == root + 3 <= end,
        index_prefix(source, forms@, old(entries)@, first as int),
    ensures
        match result {
            Ok(()) => index_prefix(source, forms@, final(entries)@, end as int),
            Err(error) => !circuit_source_matches(source) && circuit_source_error(source, error),
        },
{
    let mut index = first;
    proof { reveal(direct_form_in_range); }
    while index < end
        invariant
            first <= index <= end <= forms@.len(),
            first == root + 3,
            well_formed_sexpr(source),
            sexpr_form_model(source) == Some(forms@),
            complete_list_indices(forms@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            direct_form_in_range(forms@, 0, forms@.len() as int, root as int),
            form_has_head(source, forms@, root as int, false, Head::Namespace),
            forms@[root as int]->List_end == end,
            index < end ==> direct_form_in_range(forms@, first as int, end as int, index as int),
            index_prefix(source, forms@, entries@, index as int),
        decreases end - index,
    {
        assert(indexed_location(source, forms@, index as int, Some(root)));
        let (head, next) = match read_header(source, forms, index, true) {
            Ok(header) => header,
            Err((kind, span)) => {
                proof { reject_index_entry(source, forms@, entries@, index as int, Some(root), kind, span); }
                return Err(CircuitFormError::Header { kind, span });
            }
        };
        let entry = Entry { head, form: index, namespace: Some(root) };
        proof {
            reveal(following_direct_form);
            assert(form_region_ends_at(forms@, first as int, end as int));
            member_index_gap(source, forms@, root as int, end as int, index as int, next as int);
            append_index_entry(source, forms@, entries@, entry, next as int);
        }
        entries.push(entry);
        index = next;
    }
    Ok(())
}

/// 回路フォームの宣言位置を構文木の添字で返す。
///
/// 単一ソースの宣言シグネチャ、回路本体、テスト本体を検査する。
/// 索引にはトップレベルのフォームと名前空間の直下のフォームが入力順に一度ずつ現れる。
/// `(using nor)` を一度だけ指定する要件は、名前解決と同様にソース集合を対象とする後続の検査で扱う。
/// 型と結線の検査も後続の処理で扱う。
///
/// # Errors
///
/// 字句、S 式、検査対象の回路フォームに誤りがあれば、元入力の UTF-8 バイト範囲をエラーに含める。
/// 回路フォームに必須の要素がなければ、挿入位置を長さ0の範囲で示す。
/// テストで `case` と操作が混在すると、最初と種類が異なる項目の先頭語を主範囲とする。最初の項目についても先頭語の範囲をエラーに含める。
///
/// # Examples
///
/// ```
/// use circuitgame2_syntax::circuit::{Head, index_headers};
///
/// let result = index_headers("(namespace gates (func f (in) (out y) (def y 0)))")?;
/// assert_eq!(result.entries[1].head, Head::Func);
/// assert_eq!(result.entries[1].namespace, Some(result.entries[0].form));
/// # Ok::<(), circuitgame2_syntax::circuit::CircuitFormError>(())
/// ```
pub fn index_headers(source: &str) -> (result: Result<CircuitForms, CircuitFormError>)
    ensures
        result.is_ok() <==> circuit_source_matches(source),
        match result {
            Ok(index) => circuit_index_matches(source, index.forms@, index.entries@)
                && form_spans_valid(source, index.forms@, source.spec_bytes().len() as int),
            Err(error) => circuit_source_error(source, error),
        },
{
    let forms = match parse(source) {
        Ok(forms) => forms,
        Err(error) => return Err(CircuitFormError::Syntax(error)),
    };
    let mut entries: Vec<Entry> = Vec::new();
    let mut root = 0;
    let length = forms.len();
    proof {
        reveal(direct_form_in_range);
        reveal(index_prefix);
    }
    while root < length
        invariant
            root <= length == forms@.len(),
            well_formed_sexpr(source),
            sexpr_form_model(source) == Some(forms@),
            complete_list_indices(forms@),
            nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            root < length ==> direct_form_in_range(forms@, 0, length as int, root as int),
            index_prefix(source, forms@, entries@, root as int),
        decreases length - root,
    {
        let (head, end) = match read_header(source, &forms, root, false) {
            Ok(header) => header,
            Err((kind, span)) => {
                proof { reject_index_entry(source, forms@, entries@, root as int, None, kind, span); }
                return Err(CircuitFormError::Header { kind, span });
            }
        };
        proof {
            reveal(following_direct_form);
            assert(form_region_ends_at(forms@, 0, length as int));
        }
        let entry = Entry { head, form: root, namespace: None };
        let next = if matches!(head, Head::Namespace) { root + 3 } else { end };
        proof {
            root_index_gap(source, forms@, root as int, end as int, next as int, head);
            append_index_entry(source, forms@, entries@, entry, next as int);
        }
        entries.push(entry);
        if matches!(head, Head::Namespace) {
            index_namespace(source, &forms, &mut entries, root, next, end)?;
        }
        root = end;
    }
    proof { indexed_prefix_is_valid(source, forms@, entries@, length as int); }
    Ok(CircuitForms { forms, entries })
}

} // verus!
