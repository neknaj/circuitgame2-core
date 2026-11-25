//! 指示フォームの引数診断が一意に決まることを証明する。

use super::{
    Form, Head, HeaderError, Range, directive_argument_error_span, directive_arguments_match, directive_error_evidence,
    directive_word_at,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

proof fn directive_arguments_transfer_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, first: int, end: int, closing: usize, head: Head,
    error: (HeaderError, Range<usize>),
)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures
        directive_arguments_match(left, forms, first, end, head) ==> directive_arguments_match(right, forms, first, end, head),
        directive_error_evidence(left, forms, first, end, closing, head, error.0, error.1)
            ==> directive_error_evidence(right, forms, first, end, closing, head, error.0, error.1),
{
    if head is Export {
        let name = HeaderError::ExpectedName;
        if directive_arguments_match(left, forms, first, end, head) {
            assert forall|i: int| first <= i < end implies #[trigger] directive_word_at(right, forms, i, end, name) by {
                assert(directive_word_at(left, forms, i, end, name));
            };
        }
        if directive_error_evidence(left, forms, first, end, closing, head, error.0, error.1) {
            let i = choose|i: int| first <= i <= end && (i < end || i == first)
                && !#[trigger] directive_word_at(left, forms, i, end, name)
                && directive_argument_error_span(forms, i, end, closing, error.1)
                && (forall|j: int| first <= j < i ==> #[trigger] directive_word_at(left, forms, j, end, name));
            assert(!directive_word_at(right, forms, i, end, name));
            assert forall|j: int| first <= j < i implies #[trigger] directive_word_at(right, forms, j, end, name) by {
                assert(directive_word_at(left, forms, j, end, name));
            };
        }
    }
}

/// 同じ本文と構文木では、指示フォームの引数の妥当性と最初の診断の根拠が一致する。
pub(super) proof fn directive_arguments_agree_on_bytes(
    left: &str, right: &str, forms: Seq<Form>, first: int, end: int, closing: usize, head: Head,
    error: (HeaderError, Range<usize>),
)
    requires left.spec_bytes() == right.spec_bytes(),
    ensures
        directive_arguments_match(left, forms, first, end, head) == directive_arguments_match(right, forms, first, end, head),
        directive_error_evidence(left, forms, first, end, closing, head, error.0, error.1)
            == directive_error_evidence(right, forms, first, end, closing, head, error.0, error.1),
{
    directive_arguments_transfer_on_bytes(left, right, forms, first, end, closing, head, error);
    directive_arguments_transfer_on_bytes(right, left, forms, first, end, closing, head, error);
}

/// 同じ指示フォームと引数列から得られる診断の種別と範囲が一致することを示す。
pub proof fn directive_errors_agree(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, head: Head,
    left: (HeaderError, Range<usize>), right: (HeaderError, Range<usize>),
)
    requires
        directive_error_evidence(source, forms, first, end, closing, head, left.0, left.1),
        directive_error_evidence(source, forms, first, end, closing, head, right.0, right.1),
    ensures left == right,
{
    if head is Export {
        let name = HeaderError::ExpectedName;
        let a = choose|i: int| first <= i <= end && (i < end || i == first)
            && !#[trigger] directive_word_at(source, forms, i, end, name)
            && directive_argument_error_span(forms, i, end, closing, left.1)
            && (forall|j: int| first <= j < i ==> #[trigger] directive_word_at(source, forms, j, end, name));
        let b = choose|i: int| first <= i <= end && (i < end || i == first)
            && !#[trigger] directive_word_at(source, forms, i, end, name)
            && directive_argument_error_span(forms, i, end, closing, right.1)
            && (forall|j: int| first <= j < i ==> #[trigger] directive_word_at(source, forms, j, end, name));
        // 添字が異なると、先に現れる引数を後の診断が妥当とみなすことになる。
        if a < b {
            assert(directive_word_at(source, forms, a, end, name));
        } else if b < a {
            assert(directive_word_at(source, forms, b, end, name));
        }
    }
}

} // verus!
