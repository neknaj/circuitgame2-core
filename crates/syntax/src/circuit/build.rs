//! ビルドで使う定義と参照をファイル単位の配列に格納する。

#[cfg(verus_only)]
use super::body::{flat_body_matches, flat_body_row_evidence, flat_body_signal_cursor, targets_match};
use super::index::index_parsed_headers_into;
#[cfg(verus_only)]
use super::index::{build_rows_match, indexed_entry_evidence, reject_circuit_syntax};
#[cfg(verus_only)]
use super::expression_forest::{
    bare_signal_index, expression_forest, expression_references, expression_signal_evidence, expression_signals,
};
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
    /// ファイルの信号名配列に対する半開区間。
    pub signals: Range<usize>,
}

/// 厳格索引の一項目に属する定義と参照の範囲。
#[derive(Debug)]
pub struct BuildEntryRanges {
    /// ファイルの定義配列に対する半開区間。
    pub definitions: Range<usize>,
    /// ファイルの参照配列に対する半開区間。
    pub references: Range<usize>,
    /// ファイルの信号名配列に対する半開区間。
    pub signals: Range<usize>,
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
    /// 右辺で値として参照される信号名の構文木添字。元ソース順に並ぶ。
    pub signals: Vec<usize>,
}

pub(super) struct BuildRows {
    pub(super) entry_ranges: Vec<BuildEntryRanges>,
    pub(super) definitions: Vec<BuildDefinition>,
    pub(super) references: Vec<ExpressionReference>,
    pub(super) signals: Vec<usize>,
}

impl BuildRows {
    pub(super) fn new() -> (rows: Self)
        ensures rows.entry_ranges@.len() == 0 && rows.definitions@.len() == 0
            && rows.references@.len() == 0 && rows.signals@.len() == 0,
    {
        Self { entry_ranges: Vec::new(), definitions: Vec::new(), references: Vec::new(), signals: Vec::new() }
    }
}

#[verifier::opaque]
pub(super) open spec fn build_entry_matches(
    source: &str, forms: Seq<Form>, form: int, head: Head, ranges: BuildEntryRanges,
    definitions: Seq<BuildDefinition>, references: Seq<ExpressionReference>, signals: Seq<usize>,
) -> bool {
    let first = ranges.definitions.start as int;
    let stop = ranges.definitions.end as int;
    let lo = ranges.references.start as int;
    let hi = ranges.references.end as int;
    let signal_lo = ranges.signals.start as int;
    let signal_hi = ranges.signals.end as int;
    &&& 0 <= signal_lo <= signal_hi <= signals.len()
    &&& 0 <= first <= stop <= definitions.len()
    &&& 0 <= lo <= hi <= references.len()
    &&& if head is Func || head is Module || head is ModulePart {
        &&& 0 <= form < forms.len()
        &&& forms[form] is List
        &&& {
            let end = forms[form]->List_end as int;
            exists|body: int| #[trigger] routine_signature_matches(source, forms, form + 2, end, head, body)
                && flat_body_matches(source, forms, body, end, end, definitions[first..stop],
                    references.take(hi), signals.take(signal_hi), lo, hi, signal_lo, signal_hi)
        }
    } else {
        first == stop && lo == hi && signal_lo == signal_hi
    }
}

pub(super) proof fn keep_build_entry(
    source: &str, forms: Seq<Form>, form: int, head: Head, range: BuildEntryRanges,
    prior: BuildRows, rows: BuildRows,
)
    requires
        build_entry_matches(source, forms, form, head, range, prior.definitions@, prior.references@, prior.signals@),
        prior.definitions@.len() <= rows.definitions@.len(),
        rows.definitions@.take(prior.definitions@.len() as int) == prior.definitions@,
        prior.references@.len() <= rows.references@.len(),
        rows.references@.take(prior.references@.len() as int) == prior.references@,
        prior.signals@.len() <= rows.signals@.len(),
        rows.signals@.take(prior.signals@.len() as int) == prior.signals@,
    ensures build_entry_matches(source, forms, form, head, range, rows.definitions@, rows.references@, rows.signals@),
{
    reveal(build_entry_matches);
    let lo = range.definitions.start as int;
    let hi = range.definitions.end as int;
    let stop = range.references.end as int;
    let signals_end = range.signals.end as int;
    assert(prior.definitions@[lo..hi] =~= rows.definitions@[lo..hi]);
    assert(prior.references@.take(stop) =~= rows.references@.take(stop));
    assert(prior.signals@.take(signals_end) =~= rows.signals@.take(signals_end));
}

/// ビルド用索引の構文木、定義、参照の範囲が元入力と文法に対応することを表す。
pub closed spec fn build_index_matches(source: &str, index: BuildCircuitIndex) -> bool {
    circuit_index_matches(source, index.syntax.forms@, index.syntax.entries@)
        && build_rows_match(source, index.syntax.forms@, index.syntax.entries@,
            index.entry_ranges@, index.definitions@, index.references@, index.signals@)
}

pub(super) proof fn build_has_circuit_index(source: &str, index: &BuildCircuitIndex)
    requires build_index_matches(source, *index),
    ensures circuit_index_matches(source, index.syntax.forms@, index.syntax.entries@),
{
}

pub(super) proof fn indexed_build_entry_evidence(source: &str, index: &BuildCircuitIndex, entry: int)
    requires build_index_matches(source, *index), 0 <= entry < index.syntax.entries@.len(),
    ensures
        circuit_index_matches(source, index.syntax.forms@, index.syntax.entries@),
        index.entry_ranges@.len() == index.syntax.entries@.len(),
        ({
            let item = index.syntax.entries@[entry];
            build_entry_matches(source, index.syntax.forms@, item.form as int, item.head,
                index.entry_ranges@[entry], index.definitions@, index.references@, index.signals@)
        }),
{
    reveal(build_rows_match);
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
        index.entry_ranges@[entry].signals.start <= index.entry_ranges@[entry].signals.end
            <= index.signals@.len(),
{
    indexed_build_entry_evidence(source, index, entry);
    reveal(build_entry_matches);
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
            &&& index.entry_ranges@[entry].signals.start <= row.signals.start
                <= row.signals.end <= index.entry_ranges@[entry].signals.end <= index.signals@.len()
            &&& index.signals@[row.signals.start as int..row.signals.end as int]
                == expression_signals(source, index.syntax.forms@,
                    row.expression.start as int, row.expression.end as int)
            &&& row.expression.start < row.expression.end <= index.syntax.forms@.len()
            &&& definition_call_index(source, index.syntax.forms@, row, index.references@)
            &&& expression_forest(source, index.syntax.forms@, row.expression.start as int, row.expression.end as int)
            &&& index.references@[row.references.start as int..row.references.end as int]
                == expression_references(source, index.syntax.forms@, row.expression.start as int, row.expression.end as int)
            &&& definition_targets_match(index.syntax.forms@, row)
            &&& forall|i: int| row.references.start <= i < row.references.end
                ==> expression_reference_in_source(source, index.syntax.forms@, #[trigger] index.references@[i])
        }),
{
    indexed_build_entry_evidence(source, index, entry);
    reveal(build_entry_matches);
    let forms = index.syntax.forms@;
    let item = index.syntax.entries@[entry];
    let frame = index.entry_ranges@[entry];
    indexed_entry_evidence(source, forms, index.syntax.entries@, entry);
    let end = forms[item.form as int]->List_end as int;
    let defs = index.definitions@[frame.definitions.start as int..frame.definitions.end as int];
    let refs = index.references@.take(frame.references.end as int);
    let signals = index.signals@.take(frame.signals.end as int);
    let body = choose|body: int| #[trigger] routine_signature_matches(source, forms, item.form + 2, end, item.head, body)
        && flat_body_matches(source, forms, body, end, end, defs, refs, signals,
            frame.references.start as int, frame.references.end as int, frame.signals.start as int, frame.signals.end as int);
    let offset = definition - frame.definitions.start;
    assert(defs[offset] == index.definitions@[definition]);
    flat_body_row_evidence(source, forms, body, end, defs, refs, signals,
        frame.references.start as int, frame.references.end as int, frame.signals.start as int, frame.signals.end as int, offset);
    let row = index.definitions@[definition];
    assert(index.references@[row.references.start as int..row.references.end as int]
        =~= refs[row.references.start as int..row.references.end as int]);
    assert(index.signals@[row.signals.start as int..row.signals.end as int]
        =~= signals[row.signals.start as int..row.signals.end as int]);
    assert forall|i: int| row.references.start <= i < row.references.end
        implies expression_reference_in_source(source, forms, #[trigger] index.references@[i]) by {
        assert(refs[i] == index.references@[i]);
    };
}

/// 定義の区切りで、前の定義の信号範囲の末尾と次の範囲の先頭が一致することを示す。
/// 関数の先頭と末尾では、索引項目全体の信号範囲の端に対応する。
pub proof fn build_signal_cursor_evidence(
    source: &str, index: &BuildCircuitIndex, entry: int, cursor: int,
)
    requires
        build_index_matches(source, *index),
        0 <= entry < index.syntax.entries@.len(), entry < index.entry_ranges@.len(),
        index.entry_ranges@[entry].definitions.start <= cursor <= index.entry_ranges@[entry].definitions.end,
    ensures ({
        let frame = index.entry_ranges@[entry];
        let previous = if cursor == frame.definitions.start { frame.signals.start }
            else { index.definitions@[cursor - 1].signals.end };
        if cursor == frame.definitions.end { previous == frame.signals.end }
        else { previous == index.definitions@[cursor].signals.start }
    }),
{
    indexed_build_entry_evidence(source, index, entry);
    reveal(build_entry_matches);
    let forms = index.syntax.forms@;
    let item = index.syntax.entries@[entry];
    let frame = index.entry_ranges@[entry];
    if item.head is Func || item.head is Module || item.head is ModulePart {
        let end = forms[item.form as int]->List_end as int;
        let defs = index.definitions@[frame.definitions.start as int..frame.definitions.end as int];
        let refs = index.references@.take(frame.references.end as int);
        let signals = index.signals@.take(frame.signals.end as int);
        let body = choose|body: int| #[trigger] routine_signature_matches(source, forms, item.form + 2, end, item.head, body)
            && flat_body_matches(source, forms, body, end, end, defs, refs, signals,
                frame.references.start as int, frame.references.end as int, frame.signals.start as int, frame.signals.end as int);
        let offset = cursor - frame.definitions.start;
        if offset > 0 {
            assert(defs[offset - 1] == index.definitions@[cursor - 1]);
        }
        if offset < defs.len() {
            assert(defs[offset] == index.definitions@[cursor]);
        }
        flat_body_signal_cursor(source, forms, body, end, defs, refs, signals,
            frame.references.start as int, frame.references.end as int,
            frame.signals.start as int, frame.signals.end as int, offset);
    }
}

/// 指定した信号名が定義の右辺にあり、構文木で無修飾の名前を指すことを示す。
pub proof fn build_signal_evidence(
    source: &str, index: &BuildCircuitIndex, entry: int, definition: int, position: int,
)
    requires
        build_index_matches(source, *index),
        0 <= entry < index.syntax.entries@.len(),
        entry < index.entry_ranges@.len(),
        0 <= definition < index.definitions@.len(),
        index.entry_ranges@[entry].definitions.start <= definition < index.entry_ranges@[entry].definitions.end,
        index.definitions@[definition].signals.start <= position < index.definitions@[definition].signals.end,
    ensures
        0 <= position < index.signals@.len(),
        ({
            let row = index.definitions@[definition];
            let form = index.signals@[position] as int;
            row.expression.start <= form < row.expression.end <= index.syntax.forms@.len()
                && index.syntax.forms@[form] is Atom && index.syntax.forms@[form]->Atom_kind is Name
        }),
{
    build_definition_scope_evidence(source, index, entry, definition);
    let row = index.definitions@[definition];
    let start = row.signals.start as int;
    let offset = position - start;
    let signal_forms = index.signals@[start..row.signals.end as int];
    assert(signal_forms[offset] == index.signals@[position]);
    vstd::std_specs::vec::axiom_spec_len(&index.syntax.forms);
    expression_signal_evidence(source, index.syntax.forms@, row.expression.start as int,
        row.expression.end as int, offset);
}

/// 右辺全体が裸の名前なら、その定義の信号索引に当該アトムだけが含まれることを示す。
pub proof fn build_bare_signal_position(
    source: &str, index: &BuildCircuitIndex, entry: int, definition: int,
)
    requires
        build_index_matches(source, *index), 0 <= entry < index.syntax.entries@.len(),
        entry < index.entry_ranges@.len(),
        index.entry_ranges@[entry].definitions.start <= definition
            < index.entry_ranges@[entry].definitions.end <= index.definitions@.len(),
        ({
            let first = index.definitions@[definition].expression.start as int;
            first < index.syntax.forms@.len() && index.syntax.forms@[first] is Atom
                && index.syntax.forms@[first]->Atom_kind is Name
        }),
    ensures ({
        let frame = index.entry_ranges@[entry].signals;
        let row = index.definitions@[definition];
        &&& frame.start <= row.signals.start < row.signals.end <= frame.end <= index.signals@.len()
        &&& row.signals.end == row.signals.start + 1
        &&& index.signals@[row.signals.start as int] == row.expression.start
    }),
{
    build_definition_scope_evidence(source, index, entry, definition);
    let row = index.definitions@[definition];
    vstd::std_specs::vec::axiom_spec_len(&index.syntax.forms);
    bare_signal_index(source, index.syntax.forms@, row.expression.start as int, row.expression.end as int);
    let start = row.signals.start as int;
    let end = row.signals.end as int;
    let positions = index.signals@[start..end];
    assert(positions == seq![row.expression.start]);
    assert(positions.len() == end - start);
    assert(positions[0] == index.signals@[start]);
}

proof fn signal_ranges_ordered(source: &str, index: &BuildCircuitIndex, entry: int, left: int, right: int)
    requires
        build_index_matches(source, *index), 0 <= entry < index.syntax.entries@.len(),
        entry < index.entry_ranges@.len(),
        index.entry_ranges@[entry].definitions.start <= left < right < index.entry_ranges@[entry].definitions.end,
    ensures index.definitions@[left].signals.end <= index.definitions@[right].signals.start,
    decreases right - left,
{
    build_signal_cursor_evidence(source, index, entry, right);
    build_definition_scope_evidence(source, index, entry, right - 1);
    if left + 1 < right {
        signal_ranges_ordered(source, index, entry, left, right - 1);
    }
}

/// 一つの信号配列の添字は、同じ索引項目内の一つの定義にだけ属することを示す。
pub proof fn build_signal_owner_unique(
    source: &str, index: &BuildCircuitIndex, entry: int, first: int, other: int, position: int,
)
    requires
        build_index_matches(source, *index), 0 <= entry < index.syntax.entries@.len(),
        entry < index.entry_ranges@.len(),
        ({
            let frame = index.entry_ranges@[entry].definitions;
            frame.start <= first < frame.end && frame.start <= other < frame.end
                && frame.end <= index.definitions@.len()
        }),
        index.definitions@[first].signals.start <= position < index.definitions@[first].signals.end,
        index.definitions@[other].signals.start <= position < index.definitions@[other].signals.end,
    ensures first == other,
{
    if first < other {
        signal_ranges_ordered(source, index, entry, first, other);
    } else if other < first {
        signal_ranges_ordered(source, index, entry, other, first);
    }
}

/// 平坦な定義行の左辺が、元の構文木にある名前または名前のリストに対応することを表す。
pub closed spec fn definition_targets_match(forms: Seq<Form>, row: BuildDefinition) -> bool {
    targets_match(forms, row.form + 2, row.expression.end as int, row.expression.start as int)
}

/// 左辺の名前が並ぶ構文木の半開区間を定める。
pub open spec fn definition_target_range(forms: Seq<Form>, row: BuildDefinition) -> (int, int) {
    let start = row.form + 2;
    if forms[start] is List { (start + 1, row.expression.start as int) }
    else { (start, row.expression.start as int) }
}

/// ビルド用索引の一行から、左辺の名前が並ぶ構文木の範囲を返す。
///
/// `forms` と `row` には、同じ厳格解析で得た構文木と定義行を渡す。
///
/// # Panics
///
/// 定義行の添字を手動で組み立て、その添字が構文木の範囲を外れるとパニックすることがある。
pub fn definition_target_atoms(forms: &[Form], row: &BuildDefinition) -> (range: Range<usize>)
    requires definition_targets_match(forms@, *row),
    ensures
        range.start < range.end <= forms@.len(),
        (range.start as int, range.end as int) == definition_target_range(forms@, *row),
        forall|i: int| range.start <= i < range.end ==> (#[trigger] forms@[i]) is Atom
            && forms@[i]->Atom_kind is Name,
{
    let first = row.form + 2;
    let start = if matches!(forms[first], Form::List { .. }) { first + 1 } else { first };
    let end = row.expression.start;
    proof {
        assert forall|i: int| start <= i < end implies (#[trigger] forms@[i]) is Atom
            && forms@[i]->Atom_kind is Name by {
            if forms@[first as int] is List {
                assert(super::expressions::argument_matches(forms@, i, end as int, HeaderError::ExpectedName));
            } else {
                assert(i == first);
            }
        };
    }
    start..end
}

/// 回路ソースを検査しながら、ビルドに必要な定義と参照を索引に載せる。
///
/// 定義の右辺を検査する走査で参照も集める。各定義はファイルの参照配列に対する範囲を持つ。
///
/// # Errors
///
/// 字句と S 式の解析で最初に見つかる違反を返す。解析が成功した場合は、回路フォームを入力順に検査する。
pub fn index_build_forms(source: &str) -> (result: Result<BuildCircuitIndex, CircuitFormError>)
    ensures
        result.is_ok() <==> circuit_source_matches(source),
        forall|error: CircuitFormError| #[trigger] circuit_source_error(source, error) <==> result == Err(error),
        match result {
            Ok(index) => build_index_matches(source, index)
                && circuit_index_matches(source, index.syntax.forms@, index.syntax.entries@)
                && complete_list_indices(index.syntax.forms@) && nested_list_indices(index.syntax.forms@)
                && form_spans_valid(source, index.syntax.forms@, source.spec_bytes().len() as int)
                && index.entry_ranges@.len() == index.syntax.entries@.len(),
            Err(error) => circuit_source_error(source, error),
        },
{
    let forms = match parse(source) {
        Ok(forms) => forms,
        Err(error) => {
            proof {
                reject_circuit_syntax(source, error);
                super::index::circuit_result_diagnostics::<()>(source, Err(CircuitFormError::Syntax(error)));
            }
            return Err(CircuitFormError::Syntax(error));
        },
    };
    let mut rows = BuildRows::new();
    let indexed = index_parsed_headers_into(source, forms.as_slice(), true, &mut rows);
    proof { super::index::circuit_result_diagnostics(source, indexed); }
    let entries = indexed?;
    proof { reveal(build_rows_match); }
    Ok(BuildCircuitIndex {
        syntax: CircuitForms { forms, entries },
        entry_ranges: rows.entry_ranges,
        definitions: rows.definitions,
        references: rows.references,
        signals: rows.signals,
    })
}

} // verus!
