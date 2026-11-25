//! 同じバイト列を保持する元リストの診断を、新しい本文の位置に移す。

#[cfg(verus_only)]
use super::*;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use super::agreement::original_list_traces_agree;
#[cfg(verus_only)]
use vstd::utf8::is_char_boundary_iff_not_is_continuation_byte;

verus! {

/// 旧基点からの相対位置を保ち、バイト範囲を新基点へ移す。
///
/// 範囲の端が旧基点より前にあるか、新しい位置が `usize` に収まらない場合は `None`。
/// 元リストで検査済みの主範囲と関連範囲には、同じ基点を使う。
///
/// # Examples
///
/// ```
/// use circuitgame2_syntax::circuit::relocate_circuit_span;
///
/// assert_eq!(relocate_circuit_span(&(12..12), 10, 3), Some(5..5));
/// assert_eq!(relocate_circuit_span(&(8..9), 10, 3), None);
/// ```
pub fn relocate_circuit_span(span: &Range<usize>, old_base: usize, new_base: usize)
    -> (result: Option<Range<usize>>)
    ensures
        result.is_some() <==> old_base <= span.start && old_base <= span.end
            && span.start - old_base + new_base <= usize::MAX
            && span.end - old_base + new_base <= usize::MAX,
        result matches Some(moved) ==> {
            &&& moved.start as int == span.start - old_base + new_base
            &&& moved.end as int == span.end - old_base + new_base
        },
{
    let start = span.start.checked_sub(old_base)?.checked_add(new_base)?;
    let end = span.end.checked_sub(old_base)?.checked_add(new_base)?;
    Some(start..end)
}

/// 元リストの主範囲と関連範囲を移し、診断種別と並びを保つことを表す。
pub open spec fn original_diagnostic_relocated(
    old: Option<CircuitFormError>, new: Option<CircuitFormError>, old_base: usize, new_base: usize,
) -> bool {
    match (old, new) {
        (None, None) => true,
        (Some(CircuitFormError::Header { kind: a, span: a_span }),
         Some(CircuitFormError::Header { kind: b, span: b_span })) => {
            &&& b_span.start as int == a_span.start - old_base + new_base
            &&& b_span.end as int == a_span.end - old_base + new_base
            &&& match (a, b) {
                (HeaderError::MixedTestItems { first_head: (a_start, a_end) },
                 HeaderError::MixedTestItems { first_head: (b_start, b_end) }) =>
                    b_start as int == a_start - old_base + new_base
                        && b_end as int == a_end - old_base + new_base,
                _ => a == b,
            }
        },
        _ => false,
    }
}

/// 同じバイト列を持つ元リストでは、検査結果が一致し、診断を新しい位置へ移せる。
///
/// 両方のリストの検査が成立し、範囲がそれぞれの本文の UTF-8 文字境界上にあることを前提とする。
/// 欠落位置の空範囲や関連範囲も、リストの先頭から同じ位置を指す。
pub proof fn original_list_diagnostics_relocate(
    old: &str, new: &str, earlier: &OriginalCircuitList, later: &OriginalCircuitList,
)
    requires
        one_original_circuit_list(old, earlier.span_model(), *earlier),
        one_original_circuit_list(new, later.span_model(), *later),
        crate::located_span(old, earlier.span_model()),
        crate::located_span(new, later.span_model()),
        old.spec_bytes()[earlier.span_model().start as int..earlier.span_model().end as int]
            == new.spec_bytes()[later.span_model().start as int..later.span_model().end as int],
    ensures
        earlier.forms_model() == later.forms_model(),
        earlier.checked_model() == later.checked_model(),
        earlier.source_diagnostics_model().len() == later.source_diagnostics_model().len(),
        forall|i: int| 0 <= i < earlier.source_diagnostics_model().len()
            ==> original_diagnostic_relocated(#[trigger] earlier.source_diagnostics_model()[i],
                #[trigger] later.source_diagnostics_model()[i], earlier.span_model().start, later.span_model().start),
        forall|i: int| 0 <= i < earlier.source_diagnostics_model().len()
            ==> (#[trigger] earlier.source_diagnostics_model()[i] matches Some(diagnostic)
                ==> original_diagnostic_within(old, earlier.span_model(), diagnostic)),
        forall|i: int| 0 <= i < later.source_diagnostics_model().len()
            ==> (#[trigger] later.source_diagnostics_model()[i] matches Some(diagnostic)
                ==> original_diagnostic_within(new, later.span_model(), diagnostic)),
{
    let old_span = earlier.span_model();
    let new_span = later.span_model();
    original_list_traces_agree(old, new, old_span, new_span, *earlier, *later);
    earlier.source_diagnostics_lie_in_original_list(old);
    later.source_diagnostics_lie_in_original_list(new);
    assert forall|i: int| 0 <= i < earlier.source_diagnostics_model().len()
        implies original_diagnostic_relocated(#[trigger] earlier.source_diagnostics_model()[i],
            #[trigger] later.source_diagnostics_model()[i], old_span.start, new_span.start) by {
        let outcome = earlier.checked@[i].outcome;
        let a = earlier.source_diagnostics_model()[i];
        let b = later.source_diagnostics_model()[i];
        assert(original_diagnostic_matches(old, old_span, outcome, a));
        assert(original_diagnostic_matches(new, new_span, outcome, b));
        if let RecoveredFormOutcome::Rejected { kind, span, .. } = outcome {
            rebasing_validity_agrees(old, new, old_span, new_span, span.start, span.end);
            if let HeaderError::MixedTestItems { first_head: (start, end) } = kind {
                rebasing_validity_agrees(old, new, old_span, new_span, start, end);
            }
        }
    };
}

// リスト内部の文字境界を、同じ UTF-8 バイト列を持つ二つの本文で照合する。
proof fn same_slice_boundary(
    old: &str, new: &str, old_span: Range<usize>, new_span: Range<usize>, offset: int,
)
    requires
        crate::located_span(old, old_span), crate::located_span(new, new_span),
        old.spec_bytes()[old_span.start as int..old_span.end as int]
            == new.spec_bytes()[new_span.start as int..new_span.end as int],
        0 <= offset <= old_span.end - old_span.start,
    ensures
        is_char_boundary(old.spec_bytes(), old_span.start + offset)
            == is_char_boundary(new.spec_bytes(), new_span.start + offset),
{
    let a = old.spec_bytes();
    let b = new.spec_bytes();
    let part = a[old_span.start as int..old_span.end as int];
    assert(part.len() == new_span.end - new_span.start);
    if offset < part.len() {
        encode_utf8_valid_utf8(old@);
        encode_utf8_valid_utf8(new@);
        is_char_boundary_iff_not_is_continuation_byte(a, old_span.start + offset);
        is_char_boundary_iff_not_is_continuation_byte(b, new_span.start + offset);
        assert(a[old_span.start + offset] == part[offset]);
        assert(b[new_span.start + offset] == part[offset]);
    }
}

proof fn rebasing_validity_agrees(
    old: &str, new: &str, old_span: Range<usize>, new_span: Range<usize>, start: usize, end: usize,
)
    requires
        crate::located_span(old, old_span), crate::located_span(new, new_span),
        old.spec_bytes()[old_span.start as int..old_span.end as int]
            == new.spec_bytes()[new_span.start as int..new_span.end as int],
    ensures can_rebase(old, old_span, start, end) == can_rebase(new, new_span, start, end),
{
    let part = old.spec_bytes()[old_span.start as int..old_span.end as int];
    assert(part.len() == new_span.end - new_span.start);
    if start <= end <= part.len() {
        same_slice_boundary(old, new, old_span, new_span, start as int);
        same_slice_boundary(old, new, old_span, new_span, end as int);
    }
}

} // verus!
