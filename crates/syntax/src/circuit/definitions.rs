//! 厳格索引と同じ構文木から、宣言と断片に属する定義の式参照を取り出す。

use super::body::collect_definitions;
#[cfg(verus_only)]
use super::body::{definitions_before, routine_arguments_match};
#[cfg(verus_only)]
use super::index::indexed_entry_evidence;
use super::*;

verus! {

/// 回路フォームの厳格索引と、各フォームの `def` に含まれる参照。
#[derive(Debug)]
pub struct CircuitDefinitionIndex {
    /// 元ソースの構文木。各索引項目は所属する名前空間ブロックも保持する。
    pub syntax: CircuitForms,
    /// `syntax.entries` と同じ順に並ぶ定義一覧。
    ///
    /// 関数、モジュール、モジュール断片の本体では `def` を出現順に並べる。
    /// それ以外のフォームには空の一覧を置く。
    pub definitions_by_entry: Vec<Vec<DefinitionReferences>>,
}

spec fn routine_definition_rows(
    source: &str, forms: Seq<Form>, entry: Entry, rows: Seq<DefinitionReferences>,
) -> bool {
    if entry.head is Func || entry.head is Module || entry.head is ModulePart {
        let root = entry.form as int;
        &&& 0 <= root < forms.len()
        &&& forms[root] is List
        &&& {
            let end = forms[root]->List_end as int;
            exists|body: int| #[trigger] routine_signature_matches(source, forms, root + 2, end, entry.head, body)
                && definitions_before(source, forms, body, end, end, rows)
        }
    } else {
        rows.len() == 0
    }
}

/// 各定義の右辺と参照が、厳格索引の対応する宣言または断片から得られたことを表す。
pub closed spec fn circuit_definitions_match(source: &str, index: CircuitDefinitionIndex) -> bool {
    let forms = index.syntax.forms@;
    let entries = index.syntax.entries@;
    &&& circuit_index_matches(source, forms, entries)
    &&& definitions_prefix(source, forms, entries, index.definitions_by_entry@)
    &&& index.definitions_by_entry@.len() == entries.len()
}

/// 定義の参照を、その宣言または断片のスコープと元ソースの字句に結び付ける。
pub proof fn definition_scope_evidence(
    source: &str, index: &CircuitDefinitionIndex, entry: int, definition: int,
)
    requires
        circuit_definitions_match(source, *index),
        0 <= entry < index.definitions_by_entry@.len(),
        0 <= definition < index.definitions_by_entry@[entry]@.len(),
    ensures
        0 <= entry < index.syntax.entries@.len(),
        ({
            let item = index.syntax.entries@[entry];
            &&& item.head is Func || item.head is Module || item.head is ModulePart
            &&& indexed_location(source, index.syntax.forms@, item.form as int, item.namespace)
            &&& forall|i: int| 0 <= i < index.definitions_by_entry@[entry]@[definition].references@.len()
                ==> expression_reference_in_source(source, index.syntax.forms@,
                    #[trigger] index.definitions_by_entry@[entry]@[definition].references@[i])
        }),
{
    let forms = index.syntax.forms@;
    let entries = index.syntax.entries@;
    let item = entries[entry];
    let root = item.form as int;
    let end = forms[root]->List_end as int;
    let rows = index.definitions_by_entry@[entry]@;
    indexed_entry_evidence(source, forms, entries, entry);
    assert(routine_definition_rows(source, forms, item, rows));
    let body = choose|body: int| #[trigger] routine_signature_matches(source, forms, root + 2, end, item.head, body)
        && definitions_before(source, forms, body, end, end, rows);
    reveal(definitions_before);
    assert(0 <= definition < rows.len());
}

spec fn definitions_prefix(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, definitions: Seq<Vec<DefinitionReferences>>,
) -> bool {
    &&& definitions.len() <= entries.len()
    &&& forall|i: int| 0 <= i < definitions.len() ==>
        routine_definition_rows(source, forms, entries[i], (#[trigger] definitions[i])@)
}

/// 回路ソースを厳格に解析し、各 `def` の右辺にある回路名と型名を取り出す。
///
/// 参照の所属は、それを含む関数、モジュール、またはモジュール断片の索引項目で確認できる。
/// `expand` の引数は展開時に扱う。
///
/// # Errors
///
/// 入力に字句、S 式、回路文法の違反があれば、[`index_headers`] と同じ診断を返す。
pub fn index_definition_references(source: &str)
    -> (result: Result<CircuitDefinitionIndex, CircuitFormError>)
    ensures
        result.is_ok() <==> circuit_source_matches(source),
        match result {
            Ok(index) => circuit_definitions_match(source, index),
            Err(error) => circuit_source_error(source, error),
        },
{
    let syntax = index_headers(source)?;
    let forms = syntax.forms.as_slice();
    let entries = syntax.entries.as_slice();
    let mut definitions = Vec::new();
    let mut i = 0;
    while i < entries.len()
        invariant
            forms@ == syntax.forms@, entries@ == syntax.entries@,
            i == definitions@.len(),
            circuit_index_matches(source, forms@, entries@),
            complete_list_indices(forms@), nested_list_indices(forms@),
            list_source_delimiters(source, forms@, false),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            definitions_prefix(source, forms@, entries@, definitions@),
        decreases entries@.len() - i,
    {
        let entry = &entries[i];
        let rows = if matches!(entry.head, Head::Func | Head::Module | Head::ModulePart) {
            let root = entry.form;
            proof {
                indexed_entry_evidence(source, forms@, entries@, i as int);
                reveal(head_word_matches);
                reveal(header_arguments_match);
                reveal(list_source_delimiters);
            }
            let Form::List { span: routine_span, end: routine_end } = &forms[root] else {
                proof { assert(false); }
                unreachable!();
            };
            assert(form_region_ends_at(forms@, root + 2, *routine_end as int));
            assert(routine_arguments_match(source, forms@, root + 2, *routine_end as int, entry.head));
            collect_definitions(source, forms, root + 2, *routine_end, routine_span.end - 1, entry.head)
        } else {
            Vec::new()
        };
        assert(routine_definition_rows(source, forms@, *entry, rows@));
        definitions.push(rows);
        i += 1;
    }
    Ok(CircuitDefinitionIndex { syntax, definitions_by_entry: definitions })
}

} // verus!
