//! 厳格索引と同じ構文木から、宣言と断片に属する定義の式参照を取り出す。

use super::body::collect_definitions;
#[cfg(verus_only)]
use super::body::{definitions_before, routine_arguments_match};
#[cfg(verus_only)]
use super::body::{flat_body_matches, same_body_references};
#[cfg(verus_only)]
use super::build::{build_entry_matches, build_has_circuit_index, indexed_build_entry_evidence};
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
    definition_rows_match(source, forms, entries, index.definitions_by_entry@)
}

proof fn same_signature_end(source: &str, forms: Seq<Form>, root: int, end: int, head: Head, a: int, b: int)
    requires
        routine_signature_matches(source, forms, root + 2, end, head, a),
        routine_signature_matches(source, forms, root + 2, end, head, b),
    ensures a == b,
{
    if head is Func || head is Module {
        let x = choose|out: int| #[trigger] ports_clause_matches(source, forms, root + 3, end, out, Clause::In)
            && ports_clause_matches(source, forms, out, end, a, Clause::Out);
        let y = choose|out: int| #[trigger] ports_clause_matches(source, forms, root + 3, end, out, Clause::In)
            && ports_clause_matches(source, forms, out, end, b, Clause::Out);
        assert(x == y);
    }
}

/// 対応する索引項目で、定義と右辺の参照が同じ順に並ぶことを表す。
pub open spec fn definition_references_agree_at(
    build: &BuildCircuitIndex, reference: &CircuitDefinitionIndex, build_entry: int, reference_entry: int,
) -> bool {
    &&& 0 <= build_entry < build.entry_ranges@.len()
    &&& 0 <= reference_entry < reference.definitions_by_entry@.len()
    &&& {
        let range = build.entry_ranges@[build_entry].definitions;
        let nested = reference.definitions_by_entry@[reference_entry]@;
        &&& 0 <= range.start <= range.end <= build.definitions@.len()
        &&& range.end - range.start == nested.len()
        &&& forall|i: int| 0 <= i < nested.len() ==> {
            let a = #[trigger] build.definitions@[range.start + i];
            let b = #[trigger] nested[i];
            &&& a.form == b.definition
            &&& a.expression == b.expression
            &&& 0 <= a.references.start <= a.references.end <= build.references@.len()
            &&& build.references@[a.references.start as int..a.references.end as int] == b.references@
        }
    }
}

/// 同じソースを受理したビルド版と参照版の索引が一致することを示す。
///
/// 構文木と索引項目の列が一致し、同じ添字の項目で定義の件数と順序、右辺の範囲、参照列が一致する。
pub proof fn definition_indexes_agree(source: &str, build: &BuildCircuitIndex, reference: &CircuitDefinitionIndex)
    requires build_index_matches(source, *build), circuit_definitions_match(source, *reference),
    ensures
        build.syntax.forms@ == reference.syntax.forms@,
        build.syntax.entries@ == reference.syntax.entries@,
        forall|i: int| 0 <= i < build.syntax.entries@.len()
            ==> #[trigger] definition_references_agree_at(build, reference, i, i),
{
    build_has_circuit_index(source, build);
    circuit_indexes_agree(source, &build.syntax, &reference.syntax);
    assert forall|i: int| 0 <= i < build.syntax.entries@.len()
        implies #[trigger] definition_references_agree_at(build, reference, i, i) by {
        same_indexed_definition_references(source, build, reference, i, i);
    };
}

/// 両方の索引にある同じ宣言または断片について、定義の順序、右辺の範囲、参照列が一致することを示す。
///
/// 呼び出し側は、両方の索引で値が等しい `Entry` の添字を渡す。
pub proof fn same_indexed_definition_references(
    source: &str, build: &BuildCircuitIndex, reference: &CircuitDefinitionIndex,
    build_entry: int, reference_entry: int,
)
    requires
        build_index_matches(source, *build),
        circuit_definitions_match(source, *reference),
        0 <= build_entry < build.syntax.entries@.len(),
        0 <= reference_entry < reference.syntax.entries@.len(),
        build.syntax.entries@[build_entry] == reference.syntax.entries@[reference_entry],
    ensures definition_references_agree_at(build, reference, build_entry, reference_entry),
{
    indexed_build_entry_evidence(source, build, build_entry);
    let forms = build.syntax.forms@;
    let entry = build.syntax.entries@[build_entry];
    let ranges = build.entry_ranges@[build_entry];
    let nested = reference.definitions_by_entry@[reference_entry]@;
    super::index::same_indexed_forms(source, forms, build.syntax.entries@,
        reference.syntax.forms@, reference.syntax.entries@);
    assert(forms == reference.syntax.forms@);
    assert(routine_definition_rows(source, forms, entry, nested));
    reveal(build_entry_matches);
    if entry.head is Func || entry.head is Module || entry.head is ModulePart {
        let root = entry.form as int;
        let end = forms[root]->List_end as int;
        let start = ranges.definitions.start as int;
        let flat = build.definitions@[start..ranges.definitions.end as int];
        let first = ranges.references.start as int;
        let stop = ranges.references.end as int;
        let references = build.references@.take(stop);
        let first_signal = ranges.signals.start as int;
        let stop_signal = ranges.signals.end as int;
        let signals = build.signals@.take(stop_signal);
        assert(exists|body: int| #[trigger] routine_signature_matches(source, forms, root + 2, end, entry.head, body)
            && flat_body_matches(source, forms, body, end, end, flat, references, signals,
                first, stop, first_signal, stop_signal));
        let a = choose|body: int| #[trigger] routine_signature_matches(source, forms, root + 2, end, entry.head, body)
            && flat_body_matches(source, forms, body, end, end, flat, references, signals, first, stop, first_signal, stop_signal);
        let b = choose|body: int| #[trigger] routine_signature_matches(source, forms, root + 2, end, entry.head, body)
            && definitions_before(source, forms, body, end, end, nested);
        same_signature_end(source, forms, root, end, entry.head, a, b);
        same_body_references(source, forms, a, end, flat, references, signals,
            first, stop, first_signal, stop_signal, nested);
        assert(flat.len() == nested.len());
        assert forall|i: int| 0 <= i < nested.len() implies {
            let row = #[trigger] build.definitions@[start + i];
            let original = #[trigger] nested[i];
            &&& row.form == original.definition
            &&& row.expression == original.expression
            &&& 0 <= row.references.start <= row.references.end <= build.references@.len()
            &&& build.references@[row.references.start as int..row.references.end as int] == original.references@
        } by {
            let row = flat[i];
            let original = nested[i];
            assert(row == build.definitions@[start + i]);
            let lo = row.references.start as int;
            let hi = row.references.end as int;
            assert(first <= lo <= hi <= stop);
            assert(references[lo..hi] == original.references@);
            assert(references[lo..hi] =~= build.references@[lo..hi]);
        };
    }
}

/// 定義一覧が厳格構文木と索引の各項目に対応することを表す。
pub closed spec fn definition_rows_match(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, rows: Seq<Vec<DefinitionReferences>>,
) -> bool {
    &&& circuit_index_matches(source, forms, entries)
    &&& definitions_prefix(source, forms, entries, rows)
    &&& rows.len() == entries.len()
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
    definition_row_evidence(source, forms, entries, index.definitions_by_entry@, entry, definition);
}

/// 各定義の参照が、所属する索引項目と元ソースの範囲に対応することを示す。
pub proof fn definition_row_evidence(
    source: &str, forms: Seq<Form>, entries: Seq<Entry>, definitions: Seq<Vec<DefinitionReferences>>,
    entry: int, definition: int,
)
    requires
        definition_rows_match(source, forms, entries, definitions),
        0 <= entry < definitions.len(),
        0 <= definition < definitions[entry]@.len(),
    ensures
        definitions.len() == entries.len(),
        ({
            let item = entries[entry];
            let references = definitions[entry]@[definition].references@;
            &&& item.head is Func || item.head is Module || item.head is ModulePart
            &&& indexed_location(source, forms, item.form as int, item.namespace)
            &&& forall|i: int| 0 <= i < references.len()
                ==> expression_reference_in_source(source, forms, #[trigger] references[i])
        }),
{
    let item = entries[entry];
    let root = item.form as int;
    let end = forms[root]->List_end as int;
    let rows = definitions[entry]@;
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
    let definitions_by_entry = collect_definition_rows(source, &syntax);
    Ok(CircuitDefinitionIndex { syntax, definitions_by_entry })
}

pub(super) fn collect_definition_rows(source: &str, syntax: &CircuitForms)
    -> (definitions: Vec<Vec<DefinitionReferences>>)
    requires
        circuit_index_matches(source, syntax.forms@, syntax.entries@),
        complete_list_indices(syntax.forms@), nested_list_indices(syntax.forms@),
        list_source_delimiters(source, syntax.forms@, false),
        form_spans_valid(source, syntax.forms@, source.spec_bytes().len() as int),
    ensures definition_rows_match(source, syntax.forms@, syntax.entries@, definitions@),
{
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
    definitions
}

} // verus!
