//! 指示フォームの引数診断が一意に決まることを証明する。

use super::{
    Form, Head, HeaderError, Range, directive_argument_error_span, directive_error_evidence,
    directive_word_at,
};
use vstd::prelude::*;

verus! {

/// 同じ指示フォームと引数列から得られる診断の種別と範囲が一致することを示す。
pub(super) proof fn directive_errors_agree(
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
