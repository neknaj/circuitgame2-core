//! 検証済みの回路索引から、名前解決で使う字句と所属位置を取り出す。

#[cfg(verus_only)]
use super::index::indexed_entry_evidence;
use super::*;

verus! {

/// 元ソースに現れる名前または名前空間パス。
#[derive(Debug, Eq, PartialEq)]
pub struct NameSite<'a> {
    /// 元ソースから借用した字句。
    pub word: &'a str,
    /// 字句の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
}

/// 名前解決で使う回路フォームの名前と所属。
#[derive(Debug, Eq, PartialEq)]
pub struct NamedForm<'a> {
    /// 名前空間、宣言、またはモジュール断片の種別。
    pub head: Head,
    /// [`CircuitForms::forms`] 内でフォームを指す添字。
    pub form: usize,
    /// 宣言名、モジュール断片の対象名、または名前空間のパス。
    pub name: NameSite<'a>,
    /// フォームを直接囲む名前空間の添字。トップレベルでは `None`。
    pub block: Option<usize>,
    /// 囲む名前空間のパス。トップレベルでは `None`。
    pub namespace: Option<NameSite<'a>>,
}

/// 回路フォームの構文木と、名前解決で使う字句の一覧。
#[derive(Debug, Eq, PartialEq)]
pub struct NamedCircuit<'a> {
    /// フォームと索引。各名前の添字はこの構文木を参照する。
    pub syntax: CircuitForms,
    /// 名前空間、独立した宣言、モジュール断片を入力順に並べた一覧。
    pub names: Vec<NamedForm<'a>>,
}

/// 名前を取り出す対象のフォームを定める。
pub open spec fn named_head(head: Head) -> bool {
    head is Namespace || head is Func || head is Module || head is ModulePart
        || head is Struct || head is Latch || head is Memory
}

fn has_project_name(head: Head) -> (named: bool)
    ensures named == named_head(head),
{
    matches!(head, Head::Namespace | Head::Func | Head::Module | Head::ModulePart
        | Head::Struct | Head::Latch | Head::Memory)
}

/// 名前が指定されたフォームを指し、元ソースの字句と一致することを表す。
#[verifier::opaque]
pub open spec fn name_site_matches(source: &str, forms: Seq<Form>, index: int, site: NameSite) -> bool {
    &&& 0 <= index < forms.len()
    &&& forms[index] is Atom
    &&& site.span == form_span(forms[index])
    &&& site.span.start < site.span.end <= source.spec_bytes().len()
    &&& is_char_boundary(source.spec_bytes(), site.span.start as int)
    &&& is_char_boundary(source.spec_bytes(), site.span.end as int)
    &&& site.word.spec_bytes() == source.spec_bytes()[site.span.start as int..site.span.end as int]
}

/// 取り出した名前と所属が、索引項目と元ソースの対応箇所を指すことを表す。
#[verifier::opaque]
pub open spec fn named_form_matches(source: &str, forms: Seq<Form>, entry: Entry, named: NamedForm) -> bool {
    &&& named_head(entry.head)
    &&& named.head == entry.head && named.form == entry.form && named.block == entry.namespace
    &&& name_site_matches(source, forms, entry.form + 2, named.name)
    &&& (forms[entry.form + 2]->Atom_kind is Name
        || (entry.head is Namespace && forms[entry.form + 2]->Atom_kind is RelativePath))
    &&& match (entry.namespace, named.namespace) {
        (None, None) => true,
        (Some(parent), Some(path)) => name_site_matches(source, forms, parent + 2, path)
            && (forms[parent + 2]->Atom_kind is Name || forms[parent + 2]->Atom_kind is RelativePath),
        _ => false,
    }
}

/// 索引の対象項目から名前を漏れなく一度ずつ取り出し、入力順を保つことを表す。
#[verifier::opaque]
pub open spec fn named_forms_match(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, names: Seq<NamedForm>, cursor: int,
) -> bool {
    &&& 0 <= cursor <= entries.len()
    &&& forall|k: int| 0 <= k < names.len() ==> {
        let named = #[trigger] names[k];
        exists|index: int| 0 <= index < cursor
            && #[trigger] named_form_matches(source, forms, entries[index], named)
    }
    &&& forall|index: int| 0 <= index < cursor && named_head((#[trigger] entries[index]).head)
        ==> exists|k: int| 0 <= k < names.len()
            && #[trigger] named_form_matches(source, forms, entries[index], names[k])
    &&& forall|left: int, right: int| 0 <= left < right < names.len()
        ==> (#[trigger] names[left]).form < (#[trigger] names[right]).form
}

proof fn named_first_argument(source: &str, forms: Seq<Form>, index: int, member: bool, head: Head)
    requires named_head(head), header_matches(source, forms, index, member, head),
    ensures
        index + 2 < forms.len(),
        forms[index + 2] is Atom,
        forms[index + 2]->Atom_kind is Name
            || (head is Namespace && forms[index + 2]->Atom_kind is RelativePath),
{
    let end = forms[index]->List_end as int;
    let first = index + 2;
    if head is Func || head is Module || head is ModulePart {
        assert(body::routine_arguments_match(source, forms, first, end, head));
        let body = choose|body: int| #[trigger] routine_signature_matches(source, forms, first, end, head, body)
            && body::body_items_before(source, forms, body, end, end);
        assert(routine_signature_matches(source, forms, first, end, head, body));
    }
}

pub(super) proof fn namespace_head_is_unique(source: &str, form: Form, head: Head)
    requires head_word_matches(source, form, head), head_word_matches(source, form, Head::Namespace),
    ensures head == Head::Namespace,
{
    reveal(head_word_matches);
    let word = head_spelling(head);
    let namespace = head_spelling(Head::Namespace);
    encode_utf8_decode_utf8(word@);
    encode_utf8_decode_utf8(namespace@);
    assert(word@ == namespace@);
}

fn read_name_site<'a>(source: &'a str, forms: &[Form], index: usize) -> (site: NameSite<'a>)
    requires
        index < forms@.len(),
        forms@[index as int] is Atom,
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures name_site_matches(source, forms@, index as int, site),
{
    let form = &forms[index];
    let span = form_span_exec(form);
    proof {
        reveal(form_spans_valid);
        encode_utf8_valid_utf8(source@);
    }
    let word = source_span(source, span.start, span.end);
    proof { reveal(name_site_matches); }
    NameSite { word, span }
}

fn read_named_form<'a>(
    source: &'a str, syntax: &CircuitForms, index: usize,
) -> (result: Option<NamedForm<'a>>)
    requires
        circuit_index_matches(source, syntax.forms@, syntax.entries@),
        form_spans_valid(source, syntax.forms@, source.spec_bytes().len() as int),
        index < syntax.entries@.len(),
    ensures
        match result {
            Some(named) => named_form_matches(source, syntax.forms@, syntax.entries@[index as int], named),
            None => !named_head(syntax.entries@[index as int].head),
        },
{
    let entry = &syntax.entries[index];
    if !has_project_name(entry.head) {
        return None;
    }
    proof {
        indexed_entry_evidence(source, syntax.forms@, syntax.entries@, index as int);
        named_first_argument(source, syntax.forms@, entry.form as int, entry.namespace.is_some(), entry.head);
    }
    let name = read_name_site(source, &syntax.forms, entry.form + 2);
    let namespace = if let Some(parent) = entry.namespace {
        proof {
            let head = choose|head: Head| #[trigger] header_matches(source, syntax.forms@, parent as int, false, head);
            namespace_head_is_unique(source, syntax.forms@[parent + 1], head);
            named_first_argument(source, syntax.forms@, parent as int, false, Head::Namespace);
        }
        Some(read_name_site(source, &syntax.forms, parent + 2))
    } else {
        None
    };
    proof { reveal(named_form_matches); }
    Some(NamedForm { head: entry.head, form: entry.form, name, block: entry.namespace, namespace })
}

proof fn record_named_form(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, names: Seq<NamedForm>, index: int, picked: Option<NamedForm>,
)
    requires
        circuit_index_matches(source, forms, entries),
        0 <= index < entries.len(),
        named_forms_match(source, forms, entries, names, index),
        match picked {
            Some(named) => named_form_matches(source, forms, entries[index], named),
            None => !named_head(entries[index].head),
        },
    ensures
        named_forms_match(source, forms, entries,
            if let Some(named) = picked { names.push(named) } else { names }, index + 1),
{
    reveal(named_forms_match);
    indexed_entry_evidence(source, forms, entries, index);
    if let Some(named) = picked {
        let extended = names.push(named);
        assert forall|k: int| 0 <= k < names.len() implies (#[trigger] names[k]).form < named.form by {
            let earlier = choose|earlier: int| 0 <= earlier < index
                && #[trigger] named_form_matches(source, forms, entries[earlier], names[k]);
            reveal(named_form_matches);
            assert(names[k].form == entries[earlier].form);
        };
        assert forall|k: int| 0 <= k < extended.len() implies {
            let value = #[trigger] extended[k];
            exists|i: int| 0 <= i < index + 1 && #[trigger] named_form_matches(source, forms, entries[i], value)
        } by {
            if k < names.len() {
                assert(extended[k] == names[k]);
            }
        };
        assert forall|i: int| 0 <= i < index + 1 && named_head((#[trigger] entries[i]).head)
            implies exists|k: int| 0 <= k < extended.len()
                && #[trigger] named_form_matches(source, forms, entries[i], extended[k]) by {
            if i < index {
                let k = choose|k: int| 0 <= k < names.len()
                    && #[trigger] named_form_matches(source, forms, entries[i], names[k]);
                assert(extended[k] == names[k]);
                assert(named_form_matches(source, forms, entries[i], extended[k]));
            } else {
                let k = names.len() as int;
                assert(extended[k] == named);
                assert(named_form_matches(source, forms, entries[i], extended[k]));
            }
        };
    }
}

/// 回路ソースを解析し、名前空間、宣言、モジュール断片の名前と所属を返す。
///
/// 名前は元ソースの字句を借用する。名前空間ブロックが同じパスを指定していても、それぞれの位置を保持する。
///
/// # Errors
///
/// [`index_headers`] と同じ回路構文の診断を返す。
pub fn index_named_forms(source: &str) -> (result: Result<NamedCircuit<'_>, CircuitFormError>)
    ensures
        result.is_ok() <==> circuit_source_matches(source),
        match result {
            Ok(named) => circuit_index_matches(source, named.syntax.forms@, named.syntax.entries@)
                && form_spans_valid(source, named.syntax.forms@, source.spec_bytes().len() as int)
                && named_forms_match(source, named.syntax.forms@, named.syntax.entries@,
                    named.names@, named.syntax.entries@.len() as int),
            Err(error) => circuit_source_error(source, error),
        },
{
    let syntax = index_headers(source)?;
    let mut names: Vec<NamedForm> = Vec::new();
    let mut index = 0;
    let count = syntax.entries.len();
    proof { reveal(named_forms_match); }
    while index < count
        invariant
            index <= count == syntax.entries@.len(),
            circuit_index_matches(source, syntax.forms@, syntax.entries@),
            form_spans_valid(source, syntax.forms@, source.spec_bytes().len() as int),
            circuit_source_matches(source),
            named_forms_match(source, syntax.forms@, syntax.entries@, names@, index as int),
        decreases count - index,
    {
        let candidate = read_named_form(source, &syntax, index);
        proof { record_named_form(source, syntax.forms@, syntax.entries@, names@, index as int, candidate); }
        if let Some(named) = candidate {
            names.push(named);
        }
        index += 1;
    }
    Ok(NamedCircuit { syntax, names })
}

} // verus!
