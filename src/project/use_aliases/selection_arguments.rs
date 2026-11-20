//! ビット選択の数値引数を読み取り、入力幅に対する違反を元ソースの位置とともに返す。

use super::function_atoms::copy_location;
use crate::project::circuits::{form_location, read_indexed_atom};
use crate::project::{BitSelectionError, LocatedName, ProjectSource, check_bit_selection};
use crate::syntax::circuit::{BitSelectionShape, BitSelectionTail};
use crate::syntax::{Form, NaturalRangeError, read_natural_u64};
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::project::circuits::is_form_location;
#[cfg(verus_only)]
use crate::project::declarations::located_name_evidence;
#[cfg(verus_only)]
use crate::project::{bit_selection_matches, location_in_source};
#[cfg(verus_only)]
use crate::syntax::circuit::{bit_selection_shape_matches, bit_selection_shape_positions};
#[cfg(verus_only)]
use crate::syntax::{AtomKind, decimal_natural_value, form_span, form_spans_valid, natural_atom_has_value};
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
        /// 入力の幅を決めた型のソース範囲。
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

/// 選択の値、最初に見つかる違反、その主範囲と関連範囲を元の引数と入力幅から定める。
pub(super) closed spec fn selection_arguments_match(
    source: &ProjectSource, forms: Seq<Form>, shape: &BitSelectionShape, input_width: u64,
    width_origin: &LocatedName, result: Result<CheckedBitSelection, SelectionArgumentError>,
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

} // verus!
