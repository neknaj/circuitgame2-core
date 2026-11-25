//! 同じ本文に対する回復診断を、全文解析と区間ごとの解析で照合する。

use super::*;

verus! {

/// 元リストを同じ範囲で検査したときに得られる観測の一致を表す。
///
/// 両方が `None` の場合は、範囲を一つのリストとして厳格に読めないことを要求する。
pub open spec fn original_list_observations_agree(
    source: &str, span: Range<usize>, left: Option<OriginalCircuitList>, right: Option<OriginalCircuitList>,
) -> bool {
    match (left, right) {
        (Some(a), Some(b)) => a.span_model() == span && b.span_model() == span
            && a.forms_model() == b.forms_model() && a.checked_model() == b.checked_model()
            && a.source_diagnostics_model() == b.source_diagnostics_model(),
        (None, None) => !original_list_is_inspectable(source, span),
        _ => false,
    }
}

// 同じバイト範囲の厳格構文木と検査列は一意で、診断の基準位置も共通する。
proof fn original_list_inspections_agree(
    source: &str, span: Range<usize>, left: Option<OriginalCircuitList>, right: Option<OriginalCircuitList>,
)
    requires
        left.is_some() == original_list_is_inspectable(source, span),
        right.is_some() == original_list_is_inspectable(source, span),
        left matches Some(list) ==> one_original_circuit_list(source, span, list),
        right matches Some(list) ==> one_original_circuit_list(source, span, list),
    ensures original_list_observations_agree(source, span, left, right),
{
    if let (Some(a), Some(b)) = (left, right) {
        let bytes = source.spec_bytes()[span.start as int..span.end as int];
        let a_text = choose|text: &str| {
            &&& text.spec_bytes() == bytes
            &&& sexpr_form_model(text) == Some(a.forms@)
            &&& #[trigger] check_trace(text, a.forms@, a.checked@, (a.forms@.len() as int, None))
        };
        let b_text = choose|text: &str| {
            &&& text.spec_bytes() == bytes
            &&& sexpr_form_model(text) == Some(b.forms@)
            &&& #[trigger] check_trace(text, b.forms@, b.checked@, (b.forms@.len() as int, None))
        };
        crate::sexpr_models_agree_on_bytes(a_text, b_text);
        assert(a.forms@ == b.forms@);
        check_trace_transfers_on_bytes(b_text, a_text, b.forms@, b.checked@, (b.forms@.len() as int, None));
        complete_check_traces_agree(a_text, a.forms@, a.checked@, b.checked@);
        let a_diagnostics = a.source_diagnostics_model();
        let b_diagnostics = b.source_diagnostics_model();
        assert(a_diagnostics =~= b_diagnostics) by {
            assert forall|i: int| 0 <= i < a_diagnostics.len() implies
                #[trigger] a_diagnostics[i] == #[trigger] b_diagnostics[i] by {
                let outcome = a.checked@[i].outcome;
                assert(original_diagnostic_matches(source, span, outcome, a_diagnostics[i]));
                assert(original_diagnostic_matches(source, span, outcome, b_diagnostics[i]));
            };
        };
    }
}

/// 同じ本文に対する二つの修復結果は、再生結果と各元リストの検査・診断が一致する。
pub proof fn repaired_circuit_recoveries_agree(
    source: &str, left: &CircuitRecovery, right: &CircuitRecovery,
)
    requires
        circuit_recovery_matches(source, *left), circuit_recovery_matches(source, *right),
        left is WithSyntaxRepairs, right is WithSyntaxRepairs,
    ensures match (left, right) {
        (CircuitRecovery::WithSyntaxRepairs { recovered: a, original: a_lists },
         CircuitRecovery::WithSyntaxRepairs { recovered: b, original: b_lists }) => {
            &&& a.forms@ == b.forms@
            &&& a.repairs@ == b.repairs@
            &&& a.original_lists@ == b.original_lists@
            &&& a_lists@.len() == a.original_lists@.len() == b_lists@.len()
            &&& forall|i: int| 0 <= i < a_lists@.len() ==>
                original_list_observations_agree(source, a.original_lists@[i],
                    #[trigger] a_lists@[i], #[trigger] b_lists@[i])
        },
        _ => false,
    },
{
    if let (CircuitRecovery::WithSyntaxRepairs { recovered: a, original: a_lists },
            CircuitRecovery::WithSyntaxRepairs { recovered: b, original: b_lists }) = (left, right) {
        circuit_recovery_repair_evidence(source, left);
        circuit_recovery_repair_evidence(source, right);
        crate::recovered_replays_agree(source, source, a, b);
        assert forall|i: int| 0 <= i < a_lists@.len() implies
            original_list_observations_agree(source, a.original_lists@[i],
                #[trigger] a_lists@[i], #[trigger] b_lists@[i]) by {
            original_list_inspections_agree(source, a.original_lists@[i], a_lists@[i], b_lists@[i]);
        };
    }
}

impl ReparsedRecovery<'_, '_> {
    /// 区間内の元リストが現在の文書内で占めるバイト範囲。
    ///
    /// 使用する区間とリストの添字は、局所再解析の結果に含まれていなければならない。
    pub open spec fn original_list_range_model(&self, section: int, list: int) -> Range<usize>
        recommends 0 <= section < 3,
            0 <= list < self.section_model(section).recovered.original_lists@.len(),
    {
        let part = self.section_model(section);
        let span = part.recovered.original_lists@[list];
        (part.byte_base + span.start) as usize..(part.byte_base + span.end) as usize
    }

    /// 同じ本文を全文回復解析した結果と、局所再解析の観測を照合する。
    ///
    /// すべての修復を元入力の位置で取得でき、三つの区間を並べると元リストの総数と順序が一致する。
    /// それぞれのリストの検査結果は [Self::original_list_agrees_with_full] で照合できる。
    pub proof fn circuit_observations_agree_with_full(&self, whole: &CircuitRecovery)
        requires self.valid(), circuit_recovery_matches(self.source_model(), *whole), whole is WithSyntaxRepairs,
        ensures match whole {
            CircuitRecovery::WithSyntaxRepairs { recovered, original } => {
                &&& self.agrees_with(recovered)
                &&& self.repair_count_model() == recovered.repairs@.len()
                &&& forall|i: int| 0 <= i < self.repair_count_model() ==>
                    #[trigger] self.repair_at_model(i) == Some(recovered.repairs@[i])
                &&& original@.len() == self.original_list_base(2)
                    + self.section_model(2).recovered.original_lists@.len()
                &&& forall|section: int, list: int| 0 <= section < 3
                    && 0 <= list < self.section_model(section).recovered.original_lists@.len() ==> {
                    let i = self.original_list_base(section) + list;
                    &&& 0 <= i < original@.len()
                    &&& #[trigger] self.original_list_range_model(section, list) == recovered.original_lists@[i]
                }
            },
            _ => false,
        },
    {
        if let CircuitRecovery::WithSyntaxRepairs { recovered, original } = whole {
            circuit_recovery_repair_evidence(self.source_model(), whole);
            self.agrees_with_full(recovered);
            self.repairs_agree_with_full(recovered);
            self.observations_agree_with_full(recovered, 2);
            assert forall|section: int, list: int| 0 <= section < 3
                && 0 <= list < self.section_model(section).recovered.original_lists@.len() implies {
                let i = self.original_list_base(section) + list;
                &&& 0 <= i < original@.len()
                &&& #[trigger] self.original_list_range_model(section, list) == recovered.original_lists@[i]
            } by {
                self.observations_agree_with_full(recovered, section);
            };
        }
    }

    /// 局所再解析で確認した元リストを検査すると、同じ本文の全文回復解析と一致する。
    ///
    /// `observed` は [Self::inspect_original_list] の契約を満たす検査結果を渡す。
    /// 比較には局所構文木、項目の順序・所属・判定、文書内の診断の主範囲と関連範囲を含む。
    pub proof fn original_list_agrees_with_full(
        &self, whole: &CircuitRecovery, section: usize, list: usize, observed: Option<OriginalCircuitList>,
    )
        requires
            self.valid(), circuit_recovery_matches(self.source_model(), *whole), whole is WithSyntaxRepairs,
            section < 3, list < self.section_model(section as int).recovered.original_lists@.len(),
            observed.is_some() == original_list_is_inspectable(self.source_model(),
                self.original_list_range_model(section as int, list as int)),
            observed matches Some(item) ==> one_original_circuit_list(self.source_model(),
                self.original_list_range_model(section as int, list as int), item),
        ensures match whole {
            CircuitRecovery::WithSyntaxRepairs { recovered, original } => {
                let i = self.original_list_base(section as int) + list;
                &&& 0 <= i < original@.len()
                &&& recovered.original_lists@[i] == self.original_list_range_model(section as int, list as int)
                &&& original_list_observations_agree(self.source_model(), recovered.original_lists@[i],
                    observed, original@[i])
            },
            _ => false,
        },
    {
        if let CircuitRecovery::WithSyntaxRepairs { recovered, original } = whole {
            let source = self.source_model();
            circuit_recovery_repair_evidence(source, whole);
            self.agrees_with_full(recovered);
            self.observations_agree_with_full(recovered, section as int);
            let i = self.original_list_base(section as int) + list;
            let span = recovered.original_lists@[i];
            assert(span == self.original_list_range_model(section as int, list as int));
            original_list_inspections_agree(source, span, observed, original@[i]);
        }
    }
}

} // verus!
