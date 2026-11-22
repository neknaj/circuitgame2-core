//! ビット選択の数値引数を読み取り、入力幅に対する違反を元ソースの位置とともに返す。

use alloc::vec::Vec;
use super::function_atoms::copy_location;
use crate::project::circuits::{form_location, read_indexed_atom};
use crate::project::{BitSelectionError, LocatedName, ProjectSource, check_bit_selection};
use crate::syntax::circuit::{BitSelectionShape, BitSelectionTail, bit_selection_chain};
use crate::syntax::{AtomKind, Form, NaturalRangeError, read_natural_u64};
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::project::circuits::is_form_location;
#[cfg(verus_only)]
use crate::project::declarations::located_name_evidence;
#[cfg(verus_only)]
use crate::project::{bit_selection_matches, location_in_source, selected_bit_in_range, selected_bits_values};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    bit_selection_path, bit_selection_paths_agree, bit_selection_shape_matches, bit_selection_shape_positions,
    bit_selection_step_root,
};
#[cfg(verus_only)]
use crate::syntax::{decimal_natural_value, form_span, form_spans_valid, natural_atom_has_value};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// ビット選択の数値引数の役割。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SelectionArgument {
    /// 最初に選ぶビットの添字。
    Start,
    /// 選ぶビットの個数。
    Count,
    /// 選ぶビットどうしの添字の差。
    Stride,
}

/// 厳格構文から読み取ったビット選択の違反。
#[derive(Debug)]
pub enum SelectionArgumentError<'p, 'a> {
    /// 明示した自然数が `u64` の範囲を超える。
    NaturalOverflow {
        /// 範囲を超えた引数の役割。
        argument: SelectionArgument,
        /// その引数のソース範囲。
        site: LocatedName<'p, 'a>,
    },
    /// 選択数が0である。
    ZeroCount {
        /// 選択数を指定した引数の範囲。
        site: LocatedName<'p, 'a>,
    },
    /// 刻みが0である。
    ZeroStride {
        /// 刻みを指定した引数の範囲。
        site: LocatedName<'p, 'a>,
    },
    /// 選択した末尾の添字が入力のビット幅を越える。
    Outside {
        /// 開始位置から最後の明示引数までのソース範囲。
        site: LocatedName<'p, 'a>,
        /// 入力幅を決めた宣言や式のソース範囲。
        width_origin: LocatedName<'p, 'a>,
        /// 最初に選ぶ添字。
        start: u64,
        /// 最後に選ぶ添字。`u64` を超える場合も表す。
        last: u128,
        /// 入力のビット幅。
        input_width: u64,
    },
}

/// 入力幅に収まることを確認したビット選択の値。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CheckedBitSelection {
    /// 最初に選ぶ添字。
    pub start: u64,
    /// 選ぶビットの個数。
    pub count: u64,
    /// 選ぶビットどうしの添字の差。
    pub stride: u64,
    /// 最後に選ぶ添字。
    pub last: u64,
}

impl CheckedBitSelection {
    /// 選択数と刻みが正で、計算した末尾が指定した入力幅に収まることを表す。
    pub(super) open spec fn fits(self, width: u64) -> bool {
        bit_selection_matches(width, self.start, self.count, self.stride, Ok(self.last))
    }
}

/// 複数の選択式をたどると、末端が裸の信号名になることを表す。
#[verifier::opaque]
pub(super) open spec fn nested_named_selection_matches(
    source: &str, forms: Seq<Form>, root: usize, steps: Seq<BitSelectionShape>, leaf: usize,
) -> bool {
    &&& steps.len() >= 2
    &&& bit_selection_path(source, forms, root, steps, leaf)
    &&& leaf < forms.len()
    &&& forms[leaf as int] is Atom
    &&& forms[leaf as int]->Atom_kind is Name
}

/// 選択列の先頭は、元の式のビット選択に対応する。
pub(super) proof fn nested_named_selection_root(
    source: &str, forms: Seq<Form>, root: usize, steps: Seq<BitSelectionShape>, leaf: usize,
)
    requires nested_named_selection_matches(source, forms, root, steps, leaf),
    ensures
        bit_selection_shape_matches(source, forms, root as int, steps[0]),
        0 <= root < forms.len() && forms[root as int] is List,
        steps[0].input.start < forms.len() && forms[steps[0].input.start as int] is List,
{
    reveal(nested_named_selection_matches);
    assert(bit_selection_shape_matches(source, forms, bit_selection_step_root(root, steps, 0), steps[0]));
    assert(bit_selection_shape_matches(source, forms, bit_selection_step_root(root, steps, 1), steps[1]));
    bit_selection_shape_positions(source, forms, root as int, steps[0]);
    bit_selection_shape_positions(source, forms, steps[0].input.start as int, steps[1]);
}

proof fn named_leaf_is_not_selection(source: &str, forms: Seq<Form>, leaf: usize)
    requires leaf < forms.len(), forms[leaf as int] is Atom,
    ensures !(exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, leaf as int, shape)),
{
    if exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, leaf as int, shape) {
        let shape = choose|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, leaf as int, shape);
        bit_selection_shape_positions(source, forms, leaf as int, shape);
    }
}

/// 裸の信号名で終わる二つの選択列は、同じ式から始まれば一致する。
pub(super) proof fn nested_named_selections_agree(
    source: &str, forms: Seq<Form>, root: usize,
    left: Seq<BitSelectionShape>, lhs: usize, right: Seq<BitSelectionShape>, rhs: usize,
)
    requires
        nested_named_selection_matches(source, forms, root, left, lhs),
        nested_named_selection_matches(source, forms, root, right, rhs),
    ensures left == right, lhs == rhs,
{
    reveal(nested_named_selection_matches);
    named_leaf_is_not_selection(source, forms, lhs);
    named_leaf_is_not_selection(source, forms, rhs);
    bit_selection_paths_agree(source, forms, root, left, lhs, right, rhs);
}

/// 選択列の末端は、裸の信号名とフィールド式の両方にはならない。
pub(super) proof fn field_and_named_selection_disjoint(
    source: &str, forms: Seq<Form>, root: usize,
    steps: Seq<BitSelectionShape>, at: usize, shape: crate::syntax::circuit::StructureExpressionShape,
    other: Seq<BitSelectionShape>, name: usize,
)
    requires
        crate::syntax::circuit::field_selection_shape_matches(source, forms, root, steps, at, shape),
        nested_named_selection_matches(source, forms, root, other, name),
    ensures false,
{
    use crate::syntax::circuit::{bit_selection_excludes_structure, field_selection_shape_matches};
    reveal(field_selection_shape_matches);
    reveal(nested_named_selection_matches);
    named_leaf_is_not_selection(source, forms, name);
    if exists|selection: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, at as int, selection) {
        let selection = choose|selection: BitSelectionShape| #[trigger] bit_selection_shape_matches(source, forms, at as int, selection);
        bit_selection_excludes_structure(source, forms, at as int, selection);
    }
    bit_selection_paths_agree(source, forms, root, steps, at, other, name);
    crate::syntax::circuit::structure_expression_positions(source, forms, at as int, shape);
}

/// 裸の信号名で終わる二段以上の選択式から、各段の引数位置と信号名の添字を返す。
pub(super) fn nested_named_selection(source: &str, forms: &[Form], root: usize)
    -> (result: Option<(Vec<BitSelectionShape>, usize)>)
    ensures
        result matches Some((steps, leaf)) ==> nested_named_selection_matches(source, forms@, root, steps@, leaf),
        forall|steps: Seq<BitSelectionShape>, leaf: usize|
            #[trigger] nested_named_selection_matches(source, forms@, root, steps, leaf)
            ==> (result matches Some((found, at)) && found@ == steps && at == leaf),
{
    reveal(nested_named_selection_matches);
    let (steps, leaf) = bit_selection_chain(source, forms, root);
    assert forall|other: Seq<BitSelectionShape>, at: usize|
        #[trigger] nested_named_selection_matches(source, forms@, root, other, at)
        implies steps@ == other && leaf == at by {
        named_leaf_is_not_selection(source, forms@, at);
        bit_selection_paths_agree(source, forms@, root, steps@, leaf, other, at);
    };
    if steps.len() >= 2 && leaf < forms.len() && matches!(forms[leaf], Form::Atom { kind: AtomKind::Name, .. }) {
        Some((steps, leaf))
    } else {
        None
    }
}

/// 外側の選択の各要素が、二段の選択を通ると元の入力のどの位置に対応するかを表す。
pub(super) open spec fn selection_composition(
    inner: CheckedBitSelection, outer: CheckedBitSelection, composed: CheckedBitSelection,
) -> bool {
    &&& composed.count == outer.count
    &&& forall|i: int| 0 <= i < outer.count ==> #[trigger] selection_position(composed, i)
        == selection_position(inner, selection_position(outer, i))
}

pub(super) open spec fn selection_position(selection: CheckedBitSelection, index: int) -> int {
    selection.start + index * selection.stride
}

/// 半開区間のビットを先頭から並べる選択を表す。
pub(super) open spec fn contiguous_selection(start: u64, end: u64) -> CheckedBitSelection {
    CheckedBitSelection { start, count: (end - start) as u64, stride: 1, last: (end - 1) as u64 }
}

/// 入力幅に収まる半開区間を、刻み1の選択として返す。
pub(super) fn select_contiguous_range(start: u64, end: u64, _width: u64) -> (selection: CheckedBitSelection)
    requires start < end <= _width,
    ensures selection == contiguous_selection(start, end), selection.fits(_width),
{
    CheckedBitSelection { start, count: end - start, stride: 1, last: end - 1 }
}

/// 二段の選択を、元の入力に対する一段の選択にまとめる。
///
/// 選択数が1の場合は刻みを1にする。選択位置は開始位置だけで決まる。
pub(super) fn compose_selections(_width: u64, inner: CheckedBitSelection, outer: CheckedBitSelection)
    -> (composed: CheckedBitSelection)
    requires inner.fits(_width), outer.fits(inner.count),
    ensures composed.fits(_width), selection_composition(inner, outer, composed),
{
    proof {
        selected_bit_in_range(_width, inner.start, inner.count, inner.stride, inner.last, outer.start as int);
        selected_bit_in_range(_width, inner.start, inner.count, inner.stride, inner.last, outer.last as int);
    }
    let start = inner.start + outer.start * inner.stride;
    let last = inner.start + outer.last * inner.stride;
    let stride = if outer.count == 1 {
        1
    } else {
        proof {
            selected_bit_in_range(inner.count, outer.start, outer.count, outer.stride, outer.last, 1);
            selected_bit_in_range(_width, inner.start, inner.count, inner.stride, inner.last,
                outer.start + outer.stride);
            assert(0 < outer.stride * inner.stride < _width) by (nonlinear_arith)
                requires
                    0 < outer.stride, 0 < inner.stride,
                    inner.start + (outer.start + outer.stride) * inner.stride < _width,
            ;
        }
        outer.stride * inner.stride
    };
    let composed = CheckedBitSelection { start, count: outer.count, stride, last };
    proof {
        assert(start == selection_position(inner, outer.start as int));
        assert(last == selection_position(inner, outer.last as int));
        assert forall|i: int| 0 <= i < outer.count implies #[trigger] selection_position(composed, i)
            == selection_position(inner, selection_position(outer, i)) by {
            let a = outer.start as int;
            let b = outer.stride as int;
            let c = inner.start as int;
            let d = inner.stride as int;
            assert(selection_position(composed, i) == c + a * d + i * stride);
            assert(selection_position(inner, selection_position(outer, i)) == c + (a + i * b) * d);
            if outer.count == 1 {
                assert(i == 0);
                assert(c + a * d + i * stride == c + (a + i * b) * d) by (nonlinear_arith)
                    requires i == 0;
            } else {
                assert(stride == b * d);
                assert(c + a * d + i * stride == c + (a + i * b) * d) by (nonlinear_arith)
                    requires stride == b * d;
            }
        };
        assert(selection_position(composed, composed.count - 1)
            == selection_position(inner, outer.last as int));
    }
    composed
}

/// 合成した選択は、二段の選択を順に適用した場合と同じ要素列を返す。
pub(super) proof fn composed_selection_values_agree<T>(
    input: Seq<T>, inner: CheckedBitSelection, outer: CheckedBitSelection, composed: CheckedBitSelection,
)
    requires
        input.len() <= u64::MAX,
        inner.fits(input.len() as u64), outer.fits(inner.count),
        selection_composition(inner, outer, composed),
    ensures
        selected_bits_values(input, composed.start, composed.count as nat, composed.stride)
        == selected_bits_values(
            selected_bits_values(input, inner.start, inner.count as nat, inner.stride),
            outer.start, outer.count as nat, outer.stride,
        ),
{
    let intermediate = selected_bits_values(input, inner.start, inner.count as nat, inner.stride);
    let sequential = selected_bits_values(intermediate, outer.start, outer.count as nat, outer.stride);
    let combined = selected_bits_values(input, composed.start, composed.count as nat, composed.stride);
    assert forall|i: int| 0 <= i < outer.count implies #[trigger] combined[i] == #[trigger] sequential[i] by {
        selected_bit_in_range(inner.count, outer.start, outer.count, outer.stride, outer.last, i);
        let intermediate_at = selection_position(outer, i);
        assert(sequential[i] == intermediate[intermediate_at]);
        assert(combined[i] == input[selection_position(composed, i)]);
        assert(intermediate[intermediate_at] == input[selection_position(inner, intermediate_at)]);
    };
    assert(combined =~= sequential);
}

/// 外側から順に各選択の添字を当てはめ、元の入力上の位置を求める。
pub(super) open spec fn selection_chain_position(checked: Seq<CheckedBitSelection>, i: int) -> int
    decreases checked.len(),
{
    if checked.len() == 0 { i }
    else { selection_chain_position(checked.drop_first(), selection_position(checked[0], i)) }
}

spec fn projects_selection_chain(
    checked: Seq<CheckedBitSelection>, width: u64, projection: Option<CheckedBitSelection>,
) -> bool {
    if checked.len() == 0 {
        projection is None
    } else {
        &&& projection matches Some(composed)
        &&& composed.fits(width)
        &&& composed.count == checked[0].count
        &&& forall|i: int| 0 <= i < composed.count ==> #[trigger] selection_position(composed, i)
            == selection_chain_position(checked, i)
    }
}

proof fn prepend_selection_projection(
    checked: Seq<CheckedBitSelection>, width: u64, inner: CheckedBitSelection, outer: CheckedBitSelection,
    composed: CheckedBitSelection,
)
    requires
        checked.len() > 0,
        projects_selection_chain(checked, width, Some(inner)),
        outer.fits(inner.count),
        composed.fits(width),
        selection_composition(inner, outer, composed),
    ensures projects_selection_chain(seq![outer] + checked, width, Some(composed)),
{
    let all = seq![outer] + checked;
    assert(all.drop_first() =~= checked);
    assert forall|i: int| 0 <= i < composed.count implies #[trigger] selection_position(composed, i)
        == selection_chain_position(all, i) by {
        let p = selection_position(outer, i);
        selected_bit_in_range(inner.count, outer.start, outer.count, outer.stride, outer.last, i);
        assert(selection_position(inner, p) == selection_chain_position(checked, p));
    };
}

spec fn explicit_count(shape: &BitSelectionShape) -> Option<usize> {
    match shape.tail { BitSelectionTail::Bit => None, BitSelectionTail::Slice { count, .. } => Some(count) }
}

spec fn explicit_stride(shape: &BitSelectionShape) -> Option<usize> {
    match shape.tail { BitSelectionTail::Bit => None, BitSelectionTail::Slice { stride, .. } => stride }
}

spec fn last_argument(shape: &BitSelectionShape) -> usize {
    match shape.tail {
        BitSelectionTail::Bit => shape.start,
        BitSelectionTail::Slice { count, stride } => if let Some(index) = stride { index } else { count },
    }
}

spec fn natural_value(source: &ProjectSource, forms: Seq<Form>, index: usize) -> int {
    let span = form_span(forms[index as int]);
    decimal_natural_value(source.text.spec_bytes()[span.start as int..span.end as int])->Some_0
}

spec fn natural_or_one(source: &ProjectSource, forms: Seq<Form>, index: Option<usize>) -> int {
    if let Some(at) = index { natural_value(source, forms, at) } else { 1 }
}

spec fn natural_overflow_at(
    source: &ProjectSource, forms: Seq<Form>, index: usize, role: SelectionArgument,
    error: SelectionArgumentError,
) -> bool {
    error matches SelectionArgumentError::NaturalOverflow { argument, site }
        && argument == role && is_form_location(source, forms[index as int], site)
}

spec fn selection_range_site(
    source: &ProjectSource, forms: Seq<Form>, first: usize, last: usize, site: LocatedName,
) -> bool {
    &&& *site.source == *source && location_in_source(site)
    &&& site.span.start == form_span(forms[first as int]).start
    &&& site.span.end == form_span(forms[last as int]).end
}

/// 元の引数から自然数を読み取った結果を表す。入力のビット幅は参照しない。
pub(super) closed spec fn selection_numbers_match(
    source: &ProjectSource, forms: Seq<Form>, shape: &BitSelectionShape,
    result: Result<(u64, u64, u64, usize), SelectionArgumentError>,
) -> bool {
    let start = natural_value(source, forms, shape.start);
    let count = natural_or_one(source, forms, explicit_count(shape));
    let stride = natural_or_one(source, forms, explicit_stride(shape));
    if start > u64::MAX {
        result matches Err(error) && natural_overflow_at(source, forms, shape.start, SelectionArgument::Start, error)
    } else if count > u64::MAX {
        result matches Err(error) && explicit_count(shape) matches Some(index)
            && natural_overflow_at(source, forms, index, SelectionArgument::Count, error)
    } else if stride > u64::MAX {
        result matches Err(error) && explicit_stride(shape) matches Some(index)
            && natural_overflow_at(source, forms, index, SelectionArgument::Stride, error)
    } else {
        &&& 0 <= start && 0 <= count && 0 <= stride
        &&& result == Ok((start as u64, count as u64, stride as u64, last_argument(shape)))
    }
}

/// 選択の値、最初に見つかる違反、その主範囲と関連範囲を元の引数と入力幅から定める。
pub(super) closed spec fn selection_arguments_match(
    source: &ProjectSource, forms: Seq<Form>, shape: &BitSelectionShape, input_width: u64,
    width_origin: &LocatedName, result: Result<CheckedBitSelection, SelectionArgumentError>,
) -> bool {
    let start = natural_value(source, forms, shape.start);
    let count = natural_or_one(source, forms, explicit_count(shape));
    let stride = natural_or_one(source, forms, explicit_stride(shape));
    ||| result matches Err(error) && selection_numbers_match(source, forms, shape, Err(error))
    ||| {
        &&& selection_numbers_match(source, forms, shape,
            Ok((start as u64, count as u64, stride as u64, last_argument(shape))))
        &&& match result {
            Ok(checked) => checked.start == start && checked.count == count && checked.stride == stride
                && bit_selection_matches(input_width, checked.start, checked.count, checked.stride, Ok(checked.last)),
            Err(SelectionArgumentError::ZeroCount { site }) => explicit_count(shape) matches Some(index)
                && is_form_location(source, forms[index as int], site)
                && bit_selection_matches(input_width, start as u64, count as u64, stride as u64, Err(BitSelectionError::ZeroCount)),
            Err(SelectionArgumentError::ZeroStride { site }) => explicit_stride(shape) matches Some(index)
                && is_form_location(source, forms[index as int], site)
                && bit_selection_matches(input_width, start as u64, count as u64, stride as u64, Err(BitSelectionError::ZeroStride)),
            Err(SelectionArgumentError::Outside { site, width_origin: origin, start: first, last, input_width: width }) =>
                selection_range_site(source, forms, shape.start, last_argument(shape), site)
                && origin == *width_origin && location_in_source(origin)
                && bit_selection_matches(input_width, start as u64, count as u64, stride as u64,
                    Err(BitSelectionError::Outside { start: first, last, input_width: width })),
            _ => false,
        }
    }
}

/// 引数の検査結果から、選択した位置が入力幅に収まる根拠を取り出す。
pub(super) proof fn checked_selection_fits_width(
    source: &ProjectSource, forms: Seq<Form>, shape: &BitSelectionShape, input_width: u64,
    width_origin: &LocatedName, checked: CheckedBitSelection,
)
    requires selection_arguments_match(source, forms, shape, input_width, width_origin, Ok(checked)),
    ensures bit_selection_matches(input_width, checked.start, checked.count, checked.stride, Ok(checked.last)),
{
}

/// 同じ構文と入力幅からは、選択の値または診断の種別と範囲が一意に定まる。
pub(super) proof fn selection_arguments_agree(
    source: &ProjectSource, forms: Seq<Form>, shape: &BitSelectionShape, input_width: u64, width_origin: &LocatedName,
    left: Result<CheckedBitSelection, SelectionArgumentError>, right: Result<CheckedBitSelection, SelectionArgumentError>,
)
    requires
        selection_arguments_match(source, forms, shape, input_width, width_origin, left),
        selection_arguments_match(source, forms, shape, input_width, width_origin, right),
    ensures left == right,
{
}

/// 成功したビット選択の値は入力幅や診断位置にかかわらず元の引数で決まる。
pub(super) proof fn successful_selections_agree(
    source: &ProjectSource, forms: Seq<Form>, shape: &BitSelectionShape,
    left_width: u64, left_origin: &LocatedName, left: CheckedBitSelection,
    right_width: u64, right_origin: &LocatedName, right: CheckedBitSelection,
)
    requires
        selection_arguments_match(source, forms, shape, left_width, left_origin, Ok(left)),
        selection_arguments_match(source, forms, shape, right_width, right_origin, Ok(right)),
    ensures left == right,
{
}

fn read_selection_natural<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], index: usize, role: SelectionArgument,
) -> (result: Result<u64, SelectionArgumentError<'p, 'a>>)
    requires
        index < forms@.len() && forms@[index as int] is Atom && forms@[index as int]->Atom_kind is Natural,
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures
        match result {
            Ok(value) => value as int == natural_value(source, forms@, index),
            Err(error) => natural_value(source, forms@, index) > u64::MAX
                && natural_overflow_at(source, forms@, index, role, error),
        },
{
    let (word, span) = read_indexed_atom(source.text, forms, index);
    proof { natural_atom_has_value(word.spec_bytes()); }
    match read_natural_u64(word) {
        Ok(value) => Ok(value),
        Err(NaturalRangeError::OutOfRange) => {
            let site = LocatedName { source, span };
            proof { located_name_evidence(site); }
            Err(SelectionArgumentError::NaturalOverflow { argument: role, site })
        },
        Err(NaturalRangeError::InvalidDigits) => {
            proof { assert(false); }
            unreachable!()
        },
    }
}

/// 連続する数値引数の両端を使い、引数間の空白を含む範囲を作る。
fn selection_location<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], first: usize, last: usize,
) -> (site: LocatedName<'p, 'a>)
    requires
        first <= last <= first + 2 && last < forms@.len(),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures selection_range_site(source, forms@, first, last, site),
{
    let start = form_location(source, forms, first);
    let end = form_location(source, forms, last);
    let site = LocatedName { source, span: start.span.start..end.span.end };
    proof {
        reveal(form_spans_valid);
        if last == first + 2 {
            assert(form_span(forms@[first as int]).start < form_span(forms@[first + 1]).start);
            assert(form_span(forms@[first + 1]).start < form_span(forms@[last as int]).start);
        }
        located_name_evidence(site);
    }
    site
}

/// 開始位置、選択数、刻み、および最後の数値引数の構文位置を返す。
///
/// 入力幅を求める前に、選択式の型を決めるための数値を取り出せる。
/// 選択数と刻みが0かどうかは、すべての数値を読み取った後に呼び出し側で検査する。
///
/// # Errors
///
/// 開始位置、選択数、刻みの順に読み取り、最初に `u64` の範囲を超えた引数を返す。
pub(super) fn read_selection_numbers<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], _root: usize, shape: &BitSelectionShape,
) -> (result: Result<(u64, u64, u64, usize), SelectionArgumentError<'p, 'a>>)
    requires
        bit_selection_shape_matches(source.text, forms@, _root as int, *shape),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures
        selection_numbers_match(source, forms@, shape, result),
{
    proof { bit_selection_shape_positions(source.text, forms@, _root as int, *shape); }
    let start = read_selection_natural(source, forms, shape.start, SelectionArgument::Start)?;
    let (count, stride, last_arg) = match shape.tail {
        BitSelectionTail::Bit => (1, 1, shape.start),
        BitSelectionTail::Slice { count: count_arg, stride: stride_arg } => {
            let count = read_selection_natural(source, forms, count_arg, SelectionArgument::Count)?;
            match stride_arg {
                Some(at) => (count, read_selection_natural(source, forms, at, SelectionArgument::Stride)?, at),
                None => (count, 1, count_arg),
            }
        },
    };
    Ok((start, count, stride, last_arg))
}

/// 選択式の自然数を読み、入力のビット幅に収まる選択を返す。
///
/// `bit` の選択数と刻みは1とする。`slice` で刻みを省略したときも1とする。
///
/// # Errors
///
/// 明示引数を開始位置、選択数、刻みの順に変換する。変換に成功した後で、
/// 選択数、刻み、末尾の範囲の順に検査して最初の違反を返す。
pub(super) fn check_selection_arguments<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], _root: usize, shape: &BitSelectionShape,
    input_width: u64, width_origin: &LocatedName<'p, 'a>,
) -> (result: Result<CheckedBitSelection, SelectionArgumentError<'p, 'a>>)
    requires
        bit_selection_shape_matches(source.text, forms@, _root as int, *shape),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
        location_in_source(*width_origin),
    ensures
        selection_arguments_match(source, forms@, shape, input_width, width_origin, result),
        result matches Ok(checked) ==> bit_selection_matches(input_width, checked.start, checked.count, checked.stride, Ok(checked.last)),
{
    proof { bit_selection_shape_positions(source.text, forms@, _root as int, *shape); }
    let (start, count, stride, last_arg) = read_selection_numbers(source, forms, _root, shape)?;
    match check_bit_selection(input_width, start, count, stride) {
        Ok(last) => Ok(CheckedBitSelection { start, count, stride, last }),
        Err(BitSelectionError::ZeroCount) => {
            let BitSelectionTail::Slice { count: count_arg, .. } = shape.tail else {
                proof { assert(false); }
                unreachable!()
            };
            Err(SelectionArgumentError::ZeroCount { site: form_location(source, forms, count_arg) })
        },
        Err(BitSelectionError::ZeroStride) => {
            let BitSelectionTail::Slice { stride: Some(stride_arg), .. } = shape.tail else {
                proof { assert(false); }
                unreachable!()
            };
            Err(SelectionArgumentError::ZeroStride { site: form_location(source, forms, stride_arg) })
        },
        Err(BitSelectionError::Outside { start: first, last, input_width: width }) =>
            Err(SelectionArgumentError::Outside {
                site: selection_location(source, forms, shape.start, last_arg),
                width_origin: copy_location(width_origin),
                start: first, last, input_width: width,
            }),
    }
}

spec fn selection_width_origin(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>,
    i: int, base_origin: LocatedName, origin: LocatedName,
) -> bool {
    if i + 1 == steps.len() { origin == base_origin }
    else { is_form_location(source, forms[steps[i].input.start as int], origin) }
}

spec fn selection_input_width(checked: Seq<CheckedBitSelection>, index: int, base: u64) -> u64 {
    if index + 1 == checked.len() { base } else { checked[index + 1].count }
}

spec fn checked_selection_stage(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>, i: int,
    base_origin: LocatedName, width: u64, value: CheckedBitSelection,
) -> bool {
    exists|site: LocatedName| selection_width_origin(source, forms, steps, i, base_origin, site)
        && #[trigger] selection_arguments_match(source, forms, &steps[i], width, &site, Ok(value))
}

spec fn checked_selection_suffix(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>,
    base: u64, base_origin: LocatedName, offset: int, checked: Seq<CheckedBitSelection>,
) -> bool {
    &&& 0 <= offset <= steps.len()
    &&& checked.len() == steps.len() - offset
    &&& forall|j: int| 0 <= j < checked.len() ==> #[trigger]
        selection_suffix_stage(source, forms, steps, base, base_origin, offset, checked, j)
}

spec fn selection_suffix_stage(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>,
    base: u64, base_origin: LocatedName, offset: int, checked: Seq<CheckedBitSelection>, j: int,
) -> bool {
    checked_selection_stage(source, forms, steps, offset + j, base_origin,
        selection_input_width(checked, j, base), checked[j])
}

spec fn selection_chain_values<T>(input: Seq<T>, checked: Seq<CheckedBitSelection>) -> Seq<T>
    decreases checked.len(),
{
    if checked.len() == 0 {
        input
    } else {
        let outer = checked[0];
        selected_bits_values(selection_chain_values(input, checked.drop_first()),
            outer.start, outer.count as nat, outer.stride)
    }
}

/// 元の引数を使い、内側から順に選択を適用した値を表す。
pub(super) closed spec fn selection_chain_values_match<T>(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>,
    origin: LocatedName, input: Seq<T>, output: Seq<T>,
) -> bool {
    &&& input.len() <= u64::MAX
    &&& exists|checked: Seq<CheckedBitSelection>|
        #[trigger] checked_selection_suffix(source, forms, steps, input.len() as u64, origin, 0, checked)
        && output == selection_chain_values(input, checked)
}

spec fn selection_stage_fits(checked: Seq<CheckedBitSelection>, base: u64, j: int) -> bool {
    checked[j].fits(selection_input_width(checked, j, base))
}

proof fn selection_chain_values_positions<T>(input: Seq<T>, checked: Seq<CheckedBitSelection>)
    requires
        input.len() <= u64::MAX,
        forall|j: int| 0 <= j < checked.len() ==> #[trigger] selection_stage_fits(checked, input.len() as u64, j),
    ensures ({
        let output = selection_chain_values(input, checked);
        &&& output.len() == if checked.len() == 0 { input.len() } else { checked[0].count as nat }
        &&& forall|j: int| 0 <= j < output.len() ==> {
            let at = #[trigger] selection_chain_position(checked, j);
            0 <= at < input.len() && output[j] == input[at]
        }
    }),
    decreases checked.len(),
{
    let output = selection_chain_values(input, checked);
    if checked.len() == 0 {
        assert forall|j: int| 0 <= j < output.len() implies {
            let at = #[trigger] selection_chain_position(checked, j);
            0 <= at < input.len() && output[j] == input[at]
        } by {};
    } else {
        let rest = checked.drop_first();
        let base = input.len() as u64;
        assert forall|j: int| 0 <= j < rest.len() implies #[trigger] selection_stage_fits(rest, base, j) by {
            assert(selection_stage_fits(checked, base, j + 1));
            assert(rest[j] == checked[j + 1]);
            assert(selection_input_width(rest, j, base) == selection_input_width(checked, j + 1, base));
        };
        selection_chain_values_positions(input, rest);
        let outer = checked[0];
        let intermediate = selection_chain_values(input, rest);
        assert(selection_stage_fits(checked, base, 0));
        assert(outer.fits(intermediate.len() as u64));
        assert forall|j: int| 0 <= j < output.len() implies {
            let at = #[trigger] selection_chain_position(checked, j);
            0 <= at < input.len() && output[j] == input[at]
        } by {
            selected_bit_in_range(intermediate.len() as u64, outer.start, outer.count, outer.stride, outer.last, j);
            let k = selection_position(outer, j);
            let at = selection_chain_position(rest, k);
            assert(output[j] == intermediate[k]);
            assert(intermediate[k] == input[at]);
        };
    }
}

proof fn selection_stage_witness<'p, 'a>(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>, index: int,
    base_origin: LocatedName<'p, 'a>, width: u64, checked: CheckedBitSelection,
) -> (site: LocatedName<'p, 'a>)
    requires checked_selection_stage(source, forms, steps, index, base_origin, width, checked),
    ensures selection_arguments_match(source, forms, &steps[index], width, &site, Ok(checked)),
{
    choose|site: LocatedName| selection_width_origin(source, forms, steps, index, base_origin, site)
        && #[trigger] selection_arguments_match(source, forms, &steps[index], width, &site, Ok(checked))
}

/// 成功時は全段の選択と元の入力への射影を表す。失敗時は内側から最初に見つかった違反を表す。
pub(super) closed spec fn selection_chain_arguments_match(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>, base: u64, origin: LocatedName,
    result: Result<CheckedBitSelection, SelectionArgumentError>,
) -> bool {
    match result {
        Ok(projection) => exists|checked: Seq<CheckedBitSelection>|
            #[trigger] checked_selection_suffix(source, forms, steps, base, origin, 0, checked)
            && projects_selection_chain(checked, base, Some(projection)),
        Err(error) => exists|i: int, checked: Seq<CheckedBitSelection>, site: LocatedName|
            0 <= i < steps.len()
            && #[trigger] checked_selection_suffix(source, forms, steps, base, origin, i + 1, checked)
            && selection_width_origin(source, forms, steps, i, origin, site)
            && #[trigger] selection_arguments_match(source, forms, &steps[i],
                selection_input_width(checked, -1, base), &site, Err(error)),
    }
}

/// 合成した選択で取り出した値は、元の選択式を各段で評価した値と一致する。
pub(super) proof fn selection_chain_projection_preserves_values<T>(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>,
    origin: LocatedName, input: Seq<T>, projection: CheckedBitSelection,
)
    requires
        input.len() <= u64::MAX,
        selection_chain_arguments_match(source, forms, steps, input.len() as u64, origin, Ok(projection)),
    ensures selection_chain_values_match(source, forms, steps, origin, input,
        selected_bits_values(input, projection.start, projection.count as nat, projection.stride)),
{
    let base = input.len() as u64;
    let checked = choose|checked: Seq<CheckedBitSelection>|
        #[trigger] checked_selection_suffix(source, forms, steps, base, origin, 0, checked)
        && projects_selection_chain(checked, base, Some(projection));
    assert(checked.len() > 0);
    assert forall|j: int| 0 <= j < checked.len() implies #[trigger] selection_stage_fits(checked, base, j) by {
        assert(selection_suffix_stage(source, forms, steps, base, origin, 0, checked, j));
        let width = selection_input_width(checked, j, base);
        let site = selection_stage_witness(source, forms, steps, j, origin, width, checked[j]);
        checked_selection_fits_width(source, forms, &steps[j], width, &site, checked[j]);
    };
    selection_chain_values_positions(input, checked);
    let expected = selection_chain_values(input, checked);
    let combined = selected_bits_values(input, projection.start, projection.count as nat, projection.stride);
    assert forall|j: int| 0 <= j < expected.len() implies #[trigger] combined[j] == #[trigger] expected[j] by {
        let at = selection_position(projection, j);
        assert(at == selection_chain_position(checked, j));
        assert(combined[j] == input[at]);
    };
    assert(combined =~= expected);
}

/// 同じ構文と入力の選択列が取り出す値は一意に定まる。
pub(super) proof fn selection_chain_values_agree<T>(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>,
    left_origin: LocatedName, right_origin: LocatedName, input: Seq<T>, left: Seq<T>, right: Seq<T>,
)
    requires
        selection_chain_values_match(source, forms, steps, left_origin, input, left),
        selection_chain_values_match(source, forms, steps, right_origin, input, right),
    ensures left == right,
{
    let base = input.len() as u64;
    let a = choose|checked: Seq<CheckedBitSelection>|
        #[trigger] checked_selection_suffix(source, forms, steps, base, left_origin, 0, checked)
        && left == selection_chain_values(input, checked);
    let b = choose|checked: Seq<CheckedBitSelection>|
        #[trigger] checked_selection_suffix(source, forms, steps, base, right_origin, 0, checked)
        && right == selection_chain_values(input, checked);
    assert forall|j: int| 0 <= j < a.len() implies #[trigger] a[j] == #[trigger] b[j] by {
        assert(selection_suffix_stage(source, forms, steps, base, left_origin, 0, a, j));
        assert(selection_suffix_stage(source, forms, steps, base, right_origin, 0, b, j));
        let lw = selection_input_width(a, j, base);
        let rw = selection_input_width(b, j, base);
        let la = selection_stage_witness(source, forms, steps, j, left_origin, lw, a[j]);
        let ra = selection_stage_witness(source, forms, steps, j, right_origin, rw, b[j]);
        successful_selections_agree(source, forms, &steps[j], lw, &la, a[j], rw, &ra, b[j]);
    };
    assert(a =~= b);
}

/// 同じ構文と入力幅について、選択列の検査は成功と失敗を同時には満たさない。
pub(super) proof fn selection_chain_success_excludes_error(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>, base: u64,
    success_origin: LocatedName, selection: CheckedBitSelection, error_origin: LocatedName, error: SelectionArgumentError,
)
    requires
        selection_chain_arguments_match(source, forms, steps, base, success_origin, Ok(selection)),
        selection_chain_arguments_match(source, forms, steps, base, error_origin, Err(error)),
    ensures false,
{
    let good = choose|checked: Seq<CheckedBitSelection>|
        #[trigger] checked_selection_suffix(source, forms, steps, base, success_origin, 0, checked)
        && projects_selection_chain(checked, base, Some(selection));
    let (i, prefix, site) = choose|i: int, checked: Seq<CheckedBitSelection>, site: LocatedName|
        0 <= i < steps.len()
        && #[trigger] checked_selection_suffix(source, forms, steps, base, error_origin, i + 1, checked)
        && selection_width_origin(source, forms, steps, i, error_origin, site)
        && #[trigger] selection_arguments_match(source, forms, &steps[i],
            selection_input_width(checked, -1, base), &site, Err(error));
    if prefix.len() > 0 {
        assert(selection_suffix_stage(source, forms, steps, base, success_origin, 0, good, i + 1));
        assert(selection_suffix_stage(source, forms, steps, base, error_origin, i + 1, prefix, 0));
        let lw = selection_input_width(good, i + 1, base);
        let rw = selection_input_width(prefix, 0, base);
        let l = selection_stage_witness(source, forms, steps, i + 1, success_origin, lw, good[i + 1]);
        let r = selection_stage_witness(source, forms, steps, i + 1, error_origin, rw, prefix[0]);
        successful_selections_agree(source, forms, &steps[i + 1], lw, &l, good[i + 1], rw, &r, prefix[0]);
    }
    let width = selection_input_width(good, i, base);
    assert(width == selection_input_width(prefix, -1, base));
    assert(selection_suffix_stage(source, forms, steps, base, success_origin, 0, good, i));
    let other = selection_stage_witness(source, forms, steps, i, success_origin, width, good[i]);
    assert(selection_arguments_match(source, forms, &steps[i], width, &site, Ok(good[i]))) by {
        assert(selection_arguments_match(source, forms, &steps[i], width, &other, Ok(good[i])));
    };
    selection_arguments_agree(source, forms, &steps[i], width, &site, Ok(good[i]), Err(error));
}

/// 同じ選択式の列を検査できたとき、最外段の選択数は入力幅や診断位置にかかわらず一致する。
pub(super) proof fn successful_selection_chain_counts_agree(
    source: &ProjectSource, forms: Seq<Form>, steps: Seq<BitSelectionShape>,
    a_width: u64, a_origin: LocatedName, a: CheckedBitSelection,
    b_width: u64, b_origin: LocatedName, b: CheckedBitSelection,
)
    requires
        selection_chain_arguments_match(source, forms, steps, a_width, a_origin, Ok(a)),
        selection_chain_arguments_match(source, forms, steps, b_width, b_origin, Ok(b)),
    ensures a.count == b.count,
{
    let left = choose|checked: Seq<CheckedBitSelection>|
        #[trigger] checked_selection_suffix(source, forms, steps, a_width, a_origin, 0, checked)
        && projects_selection_chain(checked, a_width, Some(a));
    let right = choose|checked: Seq<CheckedBitSelection>|
        #[trigger] checked_selection_suffix(source, forms, steps, b_width, b_origin, 0, checked)
        && projects_selection_chain(checked, b_width, Some(b));
    assert(checked_selection_suffix(source, forms, steps, a_width, a_origin, 0, left));
    assert(checked_selection_suffix(source, forms, steps, b_width, b_origin, 0, right));
    assert(projects_selection_chain(left, a_width, Some(a)));
    assert(projects_selection_chain(right, b_width, Some(b)));
    assert(left.len() > 0 && right.len() > 0);
    let lw = selection_input_width(left, 0, a_width);
    let rw = selection_input_width(right, 0, b_width);
    assert(selection_suffix_stage(source, forms, steps, a_width, a_origin, 0, left, 0));
    assert(selection_suffix_stage(source, forms, steps, b_width, b_origin, 0, right, 0));
    let la = choose|site: LocatedName| selection_width_origin(source, forms, steps, 0, a_origin, site)
        && #[trigger] selection_arguments_match(source, forms, &steps[0], lw, &site, Ok(left[0]));
    let ra = choose|site: LocatedName| selection_width_origin(source, forms, steps, 0, b_origin, site)
        && #[trigger] selection_arguments_match(source, forms, &steps[0], rw, &site, Ok(right[0]));
    successful_selections_agree(source, forms, &steps[0], lw, &la, left[0], rw, &ra, right[0]);
}

/// 内側から順に選択を検査し、各段の入力幅には直前の選択数を使う。
///
/// 範囲違反の診断は、入力幅を決めた子式または基底信号の幅の根拠となる位置を示す。
pub(super) fn check_selection_chain<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], root: usize, steps: &[BitSelectionShape],
    _leaf: usize, base: u64, origin: &LocatedName<'p, 'a>,
) -> (result: Result<CheckedBitSelection, SelectionArgumentError<'p, 'a>>)
    requires
        steps@.len() > 0,
        bit_selection_path(source.text, forms@, root, steps@, _leaf),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
        location_in_source(*origin),
    ensures
        selection_chain_arguments_match(source, forms@, steps@, base, *origin, result),
        result matches Ok(projection) ==> projection.fits(base),
{
    let mut cursor = steps.len();
    let mut width_origin = copy_location(origin);
    let mut projection: Option<CheckedBitSelection> = None;
    let ghost mut checked: Seq<CheckedBitSelection> = Seq::empty();
    while cursor > 0
        invariant
            0 <= cursor <= steps@.len(),
            steps@.len() > 0,
            checked_selection_suffix(source, forms@, steps@, base, *origin, cursor as int, checked),
            projects_selection_chain(checked, base, projection),
            bit_selection_path(source.text, forms@, root, steps@, _leaf),
            form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
            location_in_source(width_origin),
            cursor > 0 ==> selection_width_origin(source, forms@, steps@, cursor - 1, *origin, width_origin),
        decreases cursor,
    {
        cursor -= 1;
        let at = if cursor == 0 { root } else { steps[cursor - 1].input.start };
        let shape = &steps[cursor];
        assert(bit_selection_shape_matches(
            source.text, forms@, bit_selection_step_root(root, steps@, cursor as int), steps@[cursor as int],
        ));
        proof { bit_selection_shape_positions(source.text, forms@, at as int, *shape); }
        let width = match projection { Some(inner) => inner.count, None => base };
        let outer = match check_selection_arguments(source, forms, at, shape, width, &width_origin) {
            Ok(selection) => selection,
            Err(error) => {
                assert(selection_chain_arguments_match(
                    source, forms@, steps@, base, *origin, Err(error),
                )) by {
                    reveal(selection_chain_arguments_match);
                    assert(checked_selection_suffix(source, forms@, steps@, base, *origin, cursor + 1, checked));
                    assert(selection_width_origin(source, forms@, steps@, cursor as int, *origin, width_origin));
                    assert(selection_input_width(checked, -1, base) == width);
                    assert(selection_arguments_match(source, forms@, &steps@[cursor as int],
                        selection_input_width(checked, -1, base), &width_origin, Err(error)));
                };
                return Err(error);
            }
        };
        proof {
            let updated = seq![outer] + checked;
            assert forall|j: int| 0 <= j < updated.len() implies #[trigger]
                selection_suffix_stage(source, forms@, steps@, base, *origin, cursor as int, updated, j) by {
                if j == 0 {
                    assert(updated[0] == outer);
                    assert(selection_input_width(updated, 0, base) == width);
                    assert(selection_arguments_match(source, forms@, shape, width, &width_origin, Ok(outer)));
                } else {
                    assert(updated[j] == checked[j - 1]);
                    assert(selection_input_width(updated, j, base) == selection_input_width(checked, j - 1, base));
                    assert(selection_suffix_stage(source, forms@, steps@, base, *origin, cursor + 1, checked, j - 1));
                }
            };
            assert(checked_selection_suffix(source, forms@, steps@, base, *origin, cursor as int, updated));
        }
        let next = if let Some(inner) = projection {
            let combined = compose_selections(base, inner, outer);
            proof { prepend_selection_projection(checked, base, inner, outer, combined); }
            combined
        } else {
            proof {
                let single = seq![outer] + checked;
                assert(single =~= seq![outer]);
                assert(single.drop_first() =~= Seq::<CheckedBitSelection>::empty());
                assert forall|i: int| 0 <= i < outer.count implies #[trigger] selection_position(outer, i)
                    == selection_chain_position(single, i) by {
                    assert(selection_chain_position(single.drop_first(), selection_position(outer, i))
                        == selection_position(outer, i));
                };
                assert(projects_selection_chain(single, base, Some(outer)));
            }
            outer
        };
        proof { checked = seq![outer] + checked; }
        projection = Some(next);
        width_origin = form_location(source, forms, at);
    }
    let Some(selection) = projection else {
        proof { assert(false); }
        unreachable!()
    };
    assert(selection_chain_arguments_match(source, forms@, steps@, base, *origin, Ok(selection))) by {
        reveal(selection_chain_arguments_match);
    };
    Ok(selection)
}

} // verus!
