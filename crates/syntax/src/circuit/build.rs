//! ビルドで使う定義と参照をファイル単位の配列に格納する。

#[cfg(verus_only)]
use super::body::{flat_body_matches, flat_body_row_evidence};
use super::index::index_parsed_headers_into;
#[cfg(verus_only)]
use super::index::{build_rows_match, indexed_entry_evidence, reject_circuit_syntax};
use super::*;

verus! {

/// 一つの定義と、ファイル単位の配列にある参照の位置。
#[derive(Debug)]
pub struct BuildDefinition {
    /// 元構文木で `def` のリストを指す添字。
    pub form: usize,
    /// 元構文木で右辺の式全体を指す半開区間。
    pub expression: Range<usize>,
    /// ファイルの参照配列に対する半開区間。参照のない定義では空。
    pub references: Range<usize>,
}

/// 厳格索引の一項目に属する定義と参照の範囲。
#[derive(Debug)]
pub struct BuildEntryRanges {
    /// ファイルの定義配列に対する半開区間。
    pub definitions: Range<usize>,
    /// ファイルの参照配列に対する半開区間。
    pub references: Range<usize>,
}

/// 厳格な回路フォームの索引と、ビルドで使う平坦な定義・参照配列。
#[derive(Debug)]
pub struct BuildCircuitIndex {
    /// 元ソースの構文木と回路フォームの厳格索引。
    pub syntax: CircuitForms,
    /// `syntax.entries` と同じ順に並ぶ、各項目の範囲。
    pub entry_ranges: Vec<BuildEntryRanges>,
    /// 定義を元ソース順に並べた配列。
    pub definitions: Vec<BuildDefinition>,
    /// 各定義の参照を元ソース順に連結した配列。
    pub references: Vec<ExpressionReference>,
}

pub(super) struct BuildRows {
    pub(super) entry_ranges: Vec<BuildEntryRanges>,
    pub(super) definitions: Vec<BuildDefinition>,
    pub(super) references: Vec<ExpressionReference>,
}

impl BuildRows {
    pub(super) fn new() -> (rows: Self)
        ensures rows.entry_ranges@.len() == 0 && rows.definitions@.len() == 0
            && rows.references@.len() == 0,
    {
        Self { entry_ranges: Vec::new(), definitions: Vec::new(), references: Vec::new() }
    }
}

pub(super) open spec fn build_entry_matches(
    source: &str, forms: Seq<Form>, form: int, head: Head, ranges: BuildEntryRanges,
    definitions: Seq<BuildDefinition>, references: Seq<ExpressionReference>,
) -> bool {
    let first = ranges.definitions.start as int;
    let stop = ranges.definitions.end as int;
    let lo = ranges.references.start as int;
    let hi = ranges.references.end as int;
    &&& 0 <= first <= stop <= definitions.len()
    &&& 0 <= lo <= hi <= references.len()
    &&& if head is Func || head is Module || head is ModulePart {
        &&& 0 <= form < forms.len()
        &&& forms[form] is List
        &&& {
            let end = forms[form]->List_end as int;
            exists|body: int| #[trigger] routine_signature_matches(source, forms, form + 2, end, head, body)
                && flat_body_matches(source, forms, body, end, end, definitions[first..stop],
                    references.take(hi), lo, hi)
        }
    } else {
        first == stop && lo == hi
    }
}

/// ビルド用索引の構文木、定義、参照の範囲が元入力と文法に対応することを表す。
pub closed spec fn build_index_matches(source: &str, index: BuildCircuitIndex) -> bool {
    circuit_index_matches(source, index.syntax.forms@, index.syntax.entries@)
        && build_rows_match(source, index.syntax.forms@, index.syntax.entries@,
            index.entry_ranges@, index.definitions@, index.references@)
}

/// 索引項目の定義範囲と参照範囲が、対応する配列内に収まることを示す。
pub proof fn build_entry_ranges_evidence(source: &str, index: &BuildCircuitIndex, entry: int)
    requires build_index_matches(source, *index), 0 <= entry < index.syntax.entries@.len(),
    ensures
        index.entry_ranges@.len() == index.syntax.entries@.len(),
        index.entry_ranges@[entry].definitions.start <= index.entry_ranges@[entry].definitions.end
            <= index.definitions@.len(),
        index.entry_ranges@[entry].references.start <= index.entry_ranges@[entry].references.end
            <= index.references@.len(),
{
    reveal(build_rows_match);
    let range = index.entry_ranges@[entry];
    let item = index.syntax.entries@[entry];
    assert(build_entry_matches(source, index.syntax.forms@, item.form as int, item.head, range,
        index.definitions@, index.references@));
}

/// 定義の参照が、その索引項目の所属と元ソースの字句に対応することを示す。
///
/// `definition` はファイル全体の定義配列を指す添字。
pub proof fn build_definition_scope_evidence(
    source: &str, index: &BuildCircuitIndex, entry: int, definition: int,
)
    requires
        build_index_matches(source, *index),
        0 <= entry < index.syntax.entries@.len(), entry < index.entry_ranges@.len(),
        index.entry_ranges@[entry].definitions.start <= definition < index.entry_ranges@[entry].definitions.end,
    ensures
        0 <= definition < index.definitions@.len(),
        ({
            let item = index.syntax.entries@[entry];
            let row = index.definitions@[definition];
            &&& item.head is Func || item.head is Module || item.head is ModulePart
            &&& indexed_location(source, index.syntax.forms@, item.form as int, item.namespace)
            &&& index.entry_ranges@[entry].references.start <= row.references.start
                <= row.references.end <= index.entry_ranges@[entry].references.end <= index.references@.len()
            &&& forall|i: int| row.references.start <= i < row.references.end
                ==> expression_reference_in_source(source, index.syntax.forms@, #[trigger] index.references@[i])
        }),
{
    reveal(build_rows_match);
    build_entry_ranges_evidence(source, index, entry);
    let forms = index.syntax.forms@;
    let item = index.syntax.entries@[entry];
    let frame = index.entry_ranges@[entry];
    assert(build_entry_matches(source, forms, item.form as int, item.head, frame,
        index.definitions@, index.references@));
    indexed_entry_evidence(source, forms, index.syntax.entries@, entry);
    let end = forms[item.form as int]->List_end as int;
    let defs = index.definitions@[frame.definitions.start as int..frame.definitions.end as int];
    let refs = index.references@.take(frame.references.end as int);
    let body = choose|body: int| #[trigger] routine_signature_matches(source, forms, item.form + 2, end, item.head, body)
        && flat_body_matches(source, forms, body, end, end, defs, refs,
            frame.references.start as int, frame.references.end as int);
    let offset = definition - frame.definitions.start;
    assert(defs[offset] == index.definitions@[definition]);
    flat_body_row_evidence(source, forms, body, end, defs, refs,
        frame.references.start as int, frame.references.end as int, offset);
    let row = index.definitions@[definition];
    assert forall|i: int| row.references.start <= i < row.references.end
        implies expression_reference_in_source(source, forms, #[trigger] index.references@[i]) by {
        assert(refs[i] == index.references@[i]);
    };
}

/// 回路ソースを検査しながら、ビルドに必要な定義と参照を索引に載せる。
///
/// 定義の右辺を検査する走査で参照も集める。各定義はファイルの参照配列に対する範囲を持つ。
///
/// # Errors
///
/// 字句、S 式、回路文法の順に、最初の違反を返す。
pub fn index_build_forms(source: &str) -> (result: Result<BuildCircuitIndex, CircuitFormError>)
    ensures
        result.is_ok() <==> circuit_source_matches(source),
        match result {
            Ok(index) => build_index_matches(source, index)
                && circuit_index_matches(source, index.syntax.forms@, index.syntax.entries@)
                && form_spans_valid(source, index.syntax.forms@, source.spec_bytes().len() as int)
                && index.entry_ranges@.len() == index.syntax.entries@.len(),
            Err(error) => circuit_source_error(source, error),
        },
{
    let forms = match parse(source) {
        Ok(forms) => forms,
        Err(error) => {
            proof { reject_circuit_syntax(source, error); }
            return Err(CircuitFormError::Syntax(error));
        },
    };
    let mut rows = BuildRows::new();
    let entries = index_parsed_headers_into(source, forms.as_slice(), true, &mut rows)?;
    proof { reveal(build_rows_match); }
    Ok(BuildCircuitIndex {
        syntax: CircuitForms { forms, entries },
        entry_ranges: rows.entry_ranges,
        definitions: rows.definitions,
        references: rows.references,
    })
}

} // verus!
