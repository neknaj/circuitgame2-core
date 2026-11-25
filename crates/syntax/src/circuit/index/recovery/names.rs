//! 回復解析で検査した元のフォームから、ファイル内の名前を取り出す。

use super::*;
use crate::circuit::names::read_named_entry;
#[cfg(verus_only)]
use vstd::utf8::{is_char_boundary_iff_not_is_continuation_byte, is_char_boundary_start_end_of_seq};

verus! {

/// 回復結果のうち、元ソースのフォームを選ぶ位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RecoveredNamePosition {
    /// 全文を S 式として読めた場合の索引項目または検査項目。
    File(usize),
    /// 元の括弧で閉じた区間のうち、指定の検査項目。
    Original {
        /// `CircuitRecovery::WithSyntaxRepairs::original` の添字。
        fragment: usize,
        /// 区間内の `checked` の添字。
        item: usize,
    },
}

/// 文法に従った元のフォームの名前と所属。
#[derive(Debug, Eq, PartialEq)]
pub struct RecoveredName<'a> {
    /// 名前空間、宣言、またはモジュール断片の種別。
    pub head: Head,
    /// 名前の原文と、ファイル先頭からの UTF-8 半開バイト範囲。
    pub name: NameSite<'a>,
    /// 直に囲む名前空間のパスと元の位置。トップレベルでは `None`。
    pub namespace: Option<NameSite<'a>>,
}

/// 名前を読み取るときに使う元ソースと、その回復解析結果。
pub struct RecoveredNames<'a> {
    source: &'a str,
    recovery: RecoveryStorage<'a>,
}

enum RecoveryStorage<'a> {
    Owned(CircuitRecovery),
    Cached(&'a CircuitRecovery),
}

spec fn shift_site(offset: usize, site: NameSite) -> NameSite {
    NameSite {
        word: site.word,
        span: (offset + site.span.start) as usize..(offset + site.span.end) as usize,
    }
}

spec fn projected_entry(
    fragment: &str, forms: Seq<Form>, entry: Entry, offset: usize, result: Option<RecoveredName>,
) -> bool {
    if named_head(entry.head) {
        result matches Some(value) && exists|relative: NamedForm| {
            &&& #[trigger] named_form_matches(fragment, forms, entry, relative)
            &&& value.head == relative.head
            &&& value.name == shift_site(offset, relative.name)
            &&& value.namespace == match relative.namespace {
                Some(name) => Some(shift_site(offset, name)),
                None => None,
            }
        }
    } else {
        result.is_none()
    }
}

spec fn projected_item(
    fragment: &str, forms: Seq<Form>, item: RecoveredCircuitForm, offset: usize,
    result: Option<RecoveredName>,
) -> bool {
    match item.outcome {
        RecoveredFormOutcome::Valid(head) =>
            projected_entry(fragment, forms, Entry { head, form: item.form, namespace: item.namespace }, offset, result),
        RecoveredFormOutcome::Rejected { .. } => result.is_none(),
    }
}

/// 名前と所属が同じ種別、元の範囲、UTF-8 本文を持つことを表す。
pub open spec fn recovered_names_agree(left: Option<RecoveredName>, right: Option<RecoveredName>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => left.head == right.head
            && left.name.span == right.name.span && left.name.word.spec_bytes() == right.name.word.spec_bytes()
            && match (left.namespace, right.namespace) {
                (None, None) => true,
                (Some(left), Some(right)) => left.span == right.span && left.word.spec_bytes() == right.word.spec_bytes(),
                _ => false,
            },
        (None, None) => true,
        _ => false,
    }
}

proof fn projected_entries_agree(
    a: &str, b: &str, forms: Seq<Form>, entry: Entry, offset: usize,
    left: Option<RecoveredName>, right: Option<RecoveredName>,
)
    requires
        a.spec_bytes() == b.spec_bytes(),
        projected_entry(a, forms, entry, offset, left),
        projected_entry(b, forms, entry, offset, right),
    ensures recovered_names_agree(left, right),
{
    if named_head(entry.head) {
        let l = left->Some_0;
        let r = right->Some_0;
        let x = choose|x: NamedForm| {
            &&& #[trigger] named_form_matches(a, forms, entry, x)
            &&& l.head == x.head
            &&& l.name == shift_site(offset, x.name)
            &&& l.namespace == match x.namespace {
                Some(name) => Some(shift_site(offset, name)),
                None => None,
            }
        };
        let y = choose|y: NamedForm| {
            &&& #[trigger] named_form_matches(b, forms, entry, y)
            &&& r.head == y.head
            &&& r.name == shift_site(offset, y.name)
            &&& r.namespace == match y.namespace {
                Some(name) => Some(shift_site(offset, name)),
                None => None,
            }
        };
        reveal(named_form_matches);
        reveal(name_site_matches);
        assert(name_site_matches(a, forms, entry.form + 2, x.name));
        assert(name_site_matches(b, forms, entry.form + 2, y.name));
        if let Some(parent) = entry.namespace {
            assert(name_site_matches(a, forms, parent + 2, x.namespace->Some_0));
            assert(name_site_matches(b, forms, parent + 2, y.namespace->Some_0));
        }
    }
}

proof fn projected_items_agree(
    a: &str, b: &str, forms: Seq<Form>, item: RecoveredCircuitForm, offset: usize,
    left: Option<RecoveredName>, right: Option<RecoveredName>,
)
    requires
        a.spec_bytes() == b.spec_bytes(),
        projected_item(a, forms, item, offset, left),
        projected_item(b, forms, item, offset, right),
    ensures recovered_names_agree(left, right),
{
    if let RecoveredFormOutcome::Valid(head) = item.outcome {
        projected_entries_agree(a, b, forms, Entry { head, form: item.form, namespace: item.namespace },
            offset, left, right);
    }
}


proof fn shift_boundary(source: &str, fragment: &str, span: Range<usize>, at: usize)
    requires
        valid_utf8(source.spec_bytes()),
        valid_utf8(fragment.spec_bytes()),
        span.start < span.end <= source.spec_bytes().len(),
        fragment.spec_bytes() == source.spec_bytes()[span.start as int..span.end as int],
        at <= fragment.spec_bytes().len(),
        is_char_boundary(source.spec_bytes(), span.end as int),
        is_char_boundary(fragment.spec_bytes(), at as int),
    ensures is_char_boundary(source.spec_bytes(), span.start + at),
{
    if at < fragment.spec_bytes().len() {
        is_char_boundary_iff_not_is_continuation_byte(fragment.spec_bytes(), at as int);
        assert(source.spec_bytes()[(span.start + at) as int] == fragment.spec_bytes()[at as int]);
        is_char_boundary_iff_not_is_continuation_byte(source.spec_bytes(), span.start + at);
    }
}

fn absolute_site<'a>(
    _source: &'a str, _fragment: &'a str, span: &Range<usize>, name: NameSite<'a>,
) -> (site: NameSite<'a>)
    requires
        valid_utf8(_source.spec_bytes()),
        valid_utf8(_fragment.spec_bytes()),
        span.start < span.end <= _source.spec_bytes().len(),
        _fragment.spec_bytes() == _source.spec_bytes()[span.start as int..span.end as int],
        name.span.start < name.span.end <= _fragment.spec_bytes().len(),
        is_char_boundary(_source.spec_bytes(), span.end as int),
        is_char_boundary(_fragment.spec_bytes(), name.span.start as int),
        is_char_boundary(_fragment.spec_bytes(), name.span.end as int),
        name.word.spec_bytes() == _fragment.spec_bytes()[name.span.start as int..name.span.end as int],
    ensures
        site == shift_site(span.start, name),
        absolute_name_span(_source, site),
{
    proof {
        shift_boundary(_source, _fragment, *span, name.span.start);
        shift_boundary(_source, _fragment, *span, name.span.end);
        let start = name.span.start as int;
        let end = name.span.end as int;
        let base = span.start as int;
        let local = _fragment.spec_bytes().subrange(start, end);
        let original = _source.spec_bytes().subrange(base + start, base + end);
        assert forall|i: int| 0 <= i < local.len() implies local[i] == original[i] by {
            assert(_fragment.spec_bytes()[start + i] == _source.spec_bytes()[base + start + i]);
        };
        assert(local =~= original);
    }
    NameSite { word: name.word, span: (span.start + name.span.start)..(span.start + name.span.end) }
}

spec fn absolute_name_span(source: &str, site: NameSite) -> bool {
    &&& site.span.start < site.span.end <= source.spec_bytes().len()
    &&& is_char_boundary(source.spec_bytes(), site.span.start as int)
    &&& is_char_boundary(source.spec_bytes(), site.span.end as int)
    &&& site.word.spec_bytes() == source.spec_bytes()[site.span.start as int..site.span.end as int]
}

fn project_named<'a>(
    source: &'a str, fragment: &'a str, span: &Range<usize>, forms: &[Form], entry: &Entry,
) -> (result: Option<RecoveredName<'a>>)
    requires
        span.start <= span.end <= source.spec_bytes().len(),
        fragment.spec_bytes() == source.spec_bytes()[span.start as int..span.end as int],
        is_char_boundary(source.spec_bytes(), span.end as int),
        header_matches(fragment, forms@, entry.form as int, entry.namespace.is_some(), entry.head),
        entry.namespace matches Some(parent) ==> header_matches(fragment, forms@, parent as int, false, Head::Namespace),
        form_spans_valid(fragment, forms@, fragment.spec_bytes().len() as int),
    ensures
        projected_entry(fragment, forms@, *entry, span.start, result),
        result matches Some(value) ==> absolute_name_span(source, value.name)
            && (value.namespace matches Some(site) ==> absolute_name_span(source, site)),
{
    let relative = read_named_entry(fragment, forms, entry)?;
    proof {
        encode_utf8_valid_utf8(source@);
        encode_utf8_valid_utf8(fragment@);
        reveal(named_form_matches);
        reveal(name_site_matches);
    }
    let name = absolute_site(source, fragment, span, relative.name);
    let namespace = match relative.namespace {
        Some(site) => Some(absolute_site(source, fragment, span, site)),
        None => None,
    };
    Some(RecoveredName { head: relative.head, name, namespace })
}

fn project_item<'a>(
    source: &'a str, fragment: &'a str, span: &Range<usize>, forms: &[Form], item: &RecoveredCircuitForm,
) -> (result: Option<RecoveredName<'a>>)
    requires
        span.start <= span.end <= source.spec_bytes().len(),
        fragment.spec_bytes() == source.spec_bytes()[span.start as int..span.end as int],
        is_char_boundary(source.spec_bytes(), span.end as int),
        form_spans_valid(fragment, forms@, fragment.spec_bytes().len() as int),
        checked_matches(fragment, forms@, *item),
    ensures
        projected_item(fragment, forms@, *item, span.start, result),
        result matches Some(value) ==> absolute_name_span(source, value.name)
            && (value.namespace matches Some(site) ==> absolute_name_span(source, site)),
{
    let RecoveredFormOutcome::Valid(head) = item.outcome else {
        return None;
    };
    proof { reveal(checked_matches); }
    project_named(source, fragment, span, forms, &Entry { head, form: item.form, namespace: item.namespace })
}

spec fn projected_original(
    source: &str, lists: Seq<Option<OriginalCircuitList>>, fragment: usize, item: usize,
    result: Option<RecoveredName>,
) -> bool {
    if fragment >= lists.len() {
        result.is_none()
    } else {
        match lists[fragment as int] {
            Some(list) if item < list.checked@.len() => exists|part: &str| {
                &&& part.spec_bytes() == source.spec_bytes()[list.span.start as int..list.span.end as int]
                &&& #[trigger] projected_item(part, list.forms@, list.checked@[item as int], list.span.start, result)
            },
            _ => result.is_none(),
        }
    }
}

fn name_in_original<'a>(
    source: &'a str, _recovered: &Recovered, original: &[Option<OriginalCircuitList>],
    fragment: usize, item: usize,
) -> (result: Option<RecoveredName<'a>>)
    requires
        original_list_ranges(source, _recovered.original_lists@, _recovered.repairs@, source.spec_bytes().len() as int),
        original_circuit_lists(source, _recovered.original_lists@, original@),
    ensures
        projected_original(source, original@, fragment, item, result),
        result matches Some(value) ==> absolute_name_span(source, value.name)
            && (value.namespace matches Some(site) ==> absolute_name_span(source, site)),
{
    let list = original.get(fragment)?.as_ref()?;
    let selected = list.checked.get(item)?;
    proof {
        encode_utf8_valid_utf8(source@);
        reveal(original_list_ranges);
        assert(one_original_circuit_list(source, _recovered.original_lists@[fragment as int], *list));
    }
    let part = source_span(source, list.span.start, list.span.end);
    proof {
        let previous = choose|previous: &str| {
            &&& previous.spec_bytes() == part.spec_bytes()
            &&& #[trigger] check_trace(previous, list.forms@, list.checked@, (list.forms@.len() as int, None))
            &&& form_spans_valid(previous, list.forms@, previous.spec_bytes().len() as int)
        };
        check_trace_transfers_on_bytes(previous, part, list.forms@, list.checked@, (list.forms@.len() as int, None));
        reveal(check_trace);
        reveal(form_spans_valid);
    }
    let value = project_item(source, part, &list.span, &list.forms, selected);
    assert(projected_item(part, list.forms@, *selected, list.span.start, value));
    value
}

impl OriginalCircuitList {
    /// リストが占める元ファイルの UTF-8 バイト範囲を返す。
    pub fn source_span(&self) -> (span: Range<usize>)
        ensures span == self.span_model(),
    {
        self.span.start..self.span.end
    }
}

impl<'a> RecoveredNames<'a> {
    /// 回復結果が、名前の読み取りに使う元ソースに対応することを表す。
    pub open spec fn valid(&self) -> bool {
        circuit_recovery_matches(self.source_model(), self.recovery_model())
    }

    /// 解析に使ったファイルの本文を表す。
    pub closed spec fn source_model(&self) -> &'a str {
        self.source
    }

    /// フォームを選ぶときに参照する回復結果を表す。
    pub closed spec fn recovery_model(&self) -> CircuitRecovery {
        match self.recovery {
            RecoveryStorage::Owned(recovery) => recovery,
            RecoveryStorage::Cached(recovery) => *recovery,
        }
    }

    /// 診断と名前の位置を選ぶときに使う回復結果を返す。
    pub fn recovery(&self) -> (result: &CircuitRecovery)
        ensures *result == self.recovery_model(),
    {
        match &self.recovery {
            RecoveryStorage::Owned(recovery) => recovery,
            RecoveryStorage::Cached(recovery) => recovery,
        }
    }

    /// 回復した名前の走査で参照するフォーム群の数を表す。
    pub closed spec fn position_group_count_model(&self) -> nat {
        match self.recovery_model() {
            CircuitRecovery::Complete(_) | CircuitRecovery::Inspected { .. } => 1,
            CircuitRecovery::WithSyntaxRepairs { original, .. } => original@.len(),
        }
    }

    /// フォーム群の数を返す。S 式が正しければ全文が一群で、修復があれば元の区間ごとに一群とする。
    pub fn position_group_count(&self) -> (count: usize)
        ensures count == self.position_group_count_model(),
    {
        match self.recovery() {
            CircuitRecovery::Complete(_) | CircuitRecovery::Inspected { .. } => 1,
            CircuitRecovery::WithSyntaxRepairs { original, .. } => original.len(),
        }
    }

    /// フォーム群の中で選べる検査項目の数を表す。
    pub closed spec fn position_count_model(&self, group: usize) -> nat {
        match self.recovery_model() {
            CircuitRecovery::Complete(syntax) => if group == 0 { syntax.entries@.len() } else { 0 },
            CircuitRecovery::Inspected { checked, .. } => if group == 0 { checked@.len() } else { 0 },
            CircuitRecovery::WithSyntaxRepairs { original, .. } => {
                if group < original@.len() {
                    match original@[group as int] {
                        Some(list) => list.checked@.len(),
                        None => 0,
                    }
                } else {
                    0
                }
            },
        }
    }

    /// フォーム群内の検査項目数を返す。範囲外や検査できなかった区間は 0 件とする。
    pub fn position_count(&self, group: usize) -> (count: usize)
        ensures
            count == self.position_count_model(group),
            group >= self.position_group_count_model() ==> count == 0,
    {
        match self.recovery() {
            CircuitRecovery::Complete(syntax) => if group == 0 { syntax.entries.len() } else { 0 },
            CircuitRecovery::Inspected { checked, .. } => if group == 0 { checked.len() } else { 0 },
            CircuitRecovery::WithSyntaxRepairs { original, .. } => match original.get(group) {
                Some(Some(list)) => list.checked.len(),
                _ => 0,
            },
        }
    }

    /// フォーム群とその中の順番から、回復結果内の位置を定める。
    pub closed spec fn position_model(&self, group: usize, item: usize) -> Option<RecoveredNamePosition> {
        if item >= self.position_count_model(group) {
            None
        } else {
            match self.recovery_model() {
                CircuitRecovery::Complete(_) | CircuitRecovery::Inspected { .. } => Some(RecoveredNamePosition::File(item)),
                CircuitRecovery::WithSyntaxRepairs { .. } => Some(RecoveredNamePosition::Original { fragment: group, item }),
            }
        }
    }

    /// フォーム群と検査項目を選ぶ。指定が範囲外なら `None` を返す。
    pub fn position(&self, group: usize, item: usize) -> (position: Option<RecoveredNamePosition>)
        ensures
            position == self.position_model(group, item),
            position.is_some() <==> item < self.position_count_model(group),
    {
        if item >= self.position_count(group) {
            return None;
        }
        Some(match self.recovery() {
            CircuitRecovery::Complete(_) | CircuitRecovery::Inspected { .. } => RecoveredNamePosition::File(item),
            CircuitRecovery::WithSyntaxRepairs { .. } => RecoveredNamePosition::Original { fragment: group, item },
        })
    }


    /// 取得した名前が、解析対象の元ソースと選んだ検査項目を指すことを表す。
    pub closed spec fn name_matches(&self, position: RecoveredNamePosition, result: Option<RecoveredName>) -> bool {
        let source = self.source;
        &&& (result matches Some(value) ==> absolute_name_span(source, value.name)
            && (value.namespace matches Some(site) ==> absolute_name_span(source, site)))
        &&& match (self.recovery_model(), position) {
            (CircuitRecovery::Complete(syntax), RecoveredNamePosition::File(index))
                if index < syntax.entries@.len() =>
                    projected_entry(source, syntax.forms@, syntax.entries@[index as int], 0, result),
            (CircuitRecovery::Inspected { forms, checked }, RecoveredNamePosition::File(index))
                if index < checked@.len() =>
                    projected_item(source, forms@, checked@[index as int], 0, result),
            (CircuitRecovery::WithSyntaxRepairs { original, .. }, RecoveredNamePosition::Original { fragment, item }) =>
                projected_original(source, original@, fragment, item, result),
            _ => result.is_none(),
        }
    }

    /// 同じ回復結果の同じ位置からは、同じ名前と所属が得られることを示す。
    pub proof fn names_agree_at(
        &self, position: RecoveredNamePosition, left: Option<RecoveredName>, right: Option<RecoveredName>,
    )
        requires self.name_matches(position, left), self.name_matches(position, right),
        ensures recovered_names_agree(left, right),
    {
        let source = self.source;
        match (self.recovery_model(), position) {
            (CircuitRecovery::Complete(syntax), RecoveredNamePosition::File(index))
                if index < syntax.entries@.len() => {
                    projected_entries_agree(source, source, syntax.forms@, syntax.entries@[index as int], 0, left, right);
                },
            (CircuitRecovery::Inspected { forms, checked }, RecoveredNamePosition::File(index))
                if index < checked@.len() => {
                    projected_items_agree(source, source, forms@, checked@[index as int], 0, left, right);
                },
            (CircuitRecovery::WithSyntaxRepairs { original, .. }, RecoveredNamePosition::Original { fragment, item })
                if fragment < original@.len() => {
                    if let Some(list) = original@[fragment as int] {
                        if item < list.checked@.len() {
                            let a = choose|part: &str| {
                                &&& part.spec_bytes() == source.spec_bytes()[list.span.start as int..list.span.end as int]
                                &&& #[trigger] projected_item(part, list.forms@, list.checked@[item as int], list.span.start, left)
                            };
                            let b = choose|part: &str| {
                                &&& part.spec_bytes() == source.spec_bytes()[list.span.start as int..list.span.end as int]
                                &&& #[trigger] projected_item(part, list.forms@, list.checked@[item as int], list.span.start, right)
                            };
                            projected_items_agree(a, b, list.forms@, list.checked@[item as int], list.span.start, left, right);
                        }
                    }
                },
            _ => {},
        }
    }


    /// 指定した元のフォームから名前と所属を取り出す。
    ///
    /// 位置が範囲外か、文法違反があるか、名前を持たないフォームなら `None` を返す。
    /// 修復がある場合は、元の括弧で閉じていた区間内の名前を返す。
    pub fn name_at(&self, position: RecoveredNamePosition) -> (result: Option<RecoveredName<'a>>)
        requires self.valid(),
        ensures self.name_matches(position, result),
    {
        let source = self.source;
        let len = source.as_bytes().len();
        proof {
            encode_utf8_valid_utf8(source@);
            is_char_boundary_start_end_of_seq(source.spec_bytes());
        }
        let span = 0..len;
        assert(source.spec_bytes().subrange(0, len as int) =~= source.spec_bytes());
        match (self.recovery(), position) {
            (CircuitRecovery::Complete(syntax), RecoveredNamePosition::File(index)) => {
                let entry = syntax.entries.get(index)?;
                proof {
                    indexed_entry_evidence(source, syntax.forms@, syntax.entries@, index as int);
                    if let Some(parent) = entry.namespace {
                        let head = choose|head: Head| #[trigger] header_matches(source, syntax.forms@, parent as int, false, head);
                        crate::circuit::names::namespace_head_is_unique(source, syntax.forms@[parent + 1], head);
                    }
                }
                project_named(source, source, &span, &syntax.forms, entry)
            },
            (CircuitRecovery::Inspected { forms, checked }, RecoveredNamePosition::File(index)) => {
                let item = checked.get(index)?;
                proof { reveal(check_trace); }
                project_item(source, source, &span, forms, item)
            },
            (CircuitRecovery::WithSyntaxRepairs { recovered, original }, RecoveredNamePosition::Original { fragment, item }) => {
                name_in_original(source, recovered, original, fragment, item)
            },
            _ => None,
        }
    }

    /// 修復がある場合、名前の取得に使った区間が回復後の構文木の最上位リストを指すことを示す。
    pub proof fn original_name_has_root(&self, fragment: usize, item: usize, name: RecoveredName<'a>)
        requires
            self.valid(),
            self.name_matches(RecoveredNamePosition::Original { fragment, item }, Some(name)),
        ensures
            self.recovery_model() matches CircuitRecovery::WithSyntaxRepairs { recovered, original },
            self.recovery_model() matches CircuitRecovery::WithSyntaxRepairs { recovered, original } ==> {
                &&& fragment < original@.len()
                &&& original@[fragment as int] matches Some(list)
                &&& exists|i: int| #[trigger] direct_form_in_range(recovered.forms@, 0, recovered.forms@.len() as int, i)
                    && recovered.forms@[i] is List && form_span(recovered.forms@[i]) == list.span_model()
            },
    {
        match self.recovery_model() {
            CircuitRecovery::WithSyntaxRepairs { recovered, original } => {
                assert(fragment < original@.len());
                match original@[fragment as int] {
                    Some(list) => {
                        assert(one_original_circuit_list(self.source, recovered.original_lists@[fragment as int], list));
                        crate::original_list_has_root(recovered.forms@, recovered.original_lists@, fragment as int);
                    },
                    None => { assert(false); },
                }
            },
            _ => { assert(false); },
        }
    }

    /// 名前と所属の位置が、解析に使った本文の文字境界を指すことを示す。
    pub proof fn name_uses_source_ranges(&self, position: RecoveredNamePosition, name: RecoveredName)
        requires self.name_matches(position, Some(name)),
        ensures ({
            let text = self.source_model().spec_bytes();
            let span = name.name.span;
            &&& span.start < span.end <= text.len()
            &&& is_char_boundary(text, span.start as int)
            &&& is_char_boundary(text, span.end as int)
            &&& name.name.word.spec_bytes() == text[span.start as int..span.end as int]
            &&& name.namespace matches Some(site) ==> {
                let span = site.span;
                &&& span.start < span.end <= text.len()
                &&& is_char_boundary(text, span.start as int)
                &&& is_char_boundary(text, span.end as int)
                &&& site.word.spec_bytes() == text[span.start as int..span.end as int]
            }
        }),
    {
    }
}

/// 回復解析し、元ソースで確認できた名前を読み出せる結果を作る。
pub fn recover_circuit_names(source: &str) -> (result: RecoveredNames<'_>)
    ensures result.valid(), result.source_model() == source,
{
    RecoveredNames { source, recovery: RecoveryStorage::Owned(recover_circuit_forms(source)) }
}

/// 本文が一致した場合に回復結果を借り、現在の本文から名前を読み出せる状態にする。
///
/// 再利用できない場合は現在の本文を回復解析する。名前と範囲はいずれも `source` を基準にする。
pub fn recover_circuit_names_with_cache<'a>(
    source: &'a str, cache: &'a CachedCircuitRecovery,
) -> (result: RecoveredNames<'a>)
    ensures result.valid(), result.source_model() == source,
{
    match cache.reuse(source) {
        Some(recovery) => RecoveredNames { source, recovery: RecoveryStorage::Cached(recovery) },
        None => recover_circuit_names(source),
    }
}

} // verus!
