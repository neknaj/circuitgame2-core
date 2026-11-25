//! 文書の回復構文を、同じ本文に対する解析に再利用する。

use alloc::string::String;
use core::ops::Range;
use vstd::prelude::*;

use super::{BuildCircuitIndex, CircuitRecovery, CircuitRecoveryReuseWindow, NamedBuildCircuit, recover_circuit_build_index, recover_circuit_forms};
use super::window::select_recovery_window;
#[cfg(verus_only)]
use super::window::original_lists_ordered;
#[cfg(verus_only)]
use crate::{original_list_ranges, recovered_replay_matches};
use crate::circuit::build::{BuildRows, copy_build_parts};
use crate::circuit::names::name_build_index;
#[cfg(verus_only)]
use super::{
    build_index_matches, circuit_recovery_matches, circuit_recovery_transfers_on_sexpr_bytes,
    circuit_index_matches, circuit_source_matches, complete_list_indices, form_spans_valid, named_forms_match,
    nested_list_indices, well_formed_sexpr,
};
#[cfg(verus_only)]
use crate::circuit::build::{build_index_transfers_on_bytes, copied_build_index_matches};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 一つの完了済みの回復解析と、その解析に使った本文。
///
/// パスや文書版は保持しない。呼び出し側は現在のスナップショットの位置として結果を扱う。
pub struct CachedCircuitRecovery {
    source: String,
    recovery: CircuitRecovery,
    build_rows: Option<BuildRows>,
}

impl CachedCircuitRecovery {
    /// 解析時の本文を Unicode スカラー値の列として表す。
    pub closed spec fn source_model(&self) -> Seq<char> { self.source@ }

    /// 本文から得た回復結果を表す。
    pub closed spec fn recovery_model(&self) -> CircuitRecovery { self.recovery }

    /// 回路フォームの検査と同じ走査で得たビルド索引を表す。
    pub closed spec fn build_model(&self) -> Option<BuildCircuitIndex> {
        match (self.recovery, self.build_rows) {
            (CircuitRecovery::Complete(syntax), Some(rows)) => Some(BuildCircuitIndex {
                syntax, entry_ranges: rows.entry_ranges, definitions: rows.definitions,
                references: rows.references, signals: rows.signals,
            }),
            _ => None,
        }
    }

    #[verifier::type_invariant]
    spec fn analyzed(&self) -> bool {
        &&& (self.build_rows.is_some() ==> self.recovery is Complete)
        &&& exists|text: &str| text@ == self.source@
            && #[trigger] circuit_recovery_matches(text, self.recovery)
            && (self.build_model() matches Some(index) ==> build_index_matches(text, index))
    }

    /// ソースを回復解析し、本文と完了した結果を保持する。
    pub fn analyze(source: String) -> (cache: Self)
        ensures cache.source_model() == source@,
    {
        let text = source.as_str();
        let recovery = recover_circuit_forms(text);
        assert(exists|text: &str| text@ == source@ && #[trigger] circuit_recovery_matches(text, recovery));
        Self { source, recovery, build_rows: None }
    }

    /// 正常な本文では、回復解析結果と一緒に定義・参照の索引を保持する。
    ///
    /// 構文違反がある場合は、ソース上の根拠を含む既存の回復結果を保持する。
    pub fn analyze_with_build_index(source: String) -> (cache: Self)
        ensures cache.source_model() == source@,
            cache.build_model().is_some() <==> cache.recovery_model() is Complete,
    {
        let text = source.as_str();
        let scanned = recover_circuit_build_index(text);
        let ghost model = scanned;
        let (recovery, build_rows) = match scanned {
            Ok(BuildCircuitIndex { syntax, entry_ranges, definitions, references, signals }) => {
                proof {
                    super::super::super::build::build_has_circuit_index(text, &model->Ok_0);
                    assert(circuit_recovery_matches(text, CircuitRecovery::Complete(syntax)));
                }
                (
                    CircuitRecovery::Complete(syntax),
                    Some(BuildRows { entry_ranges, definitions, references, signals }),
                )
            },
            Err(recovery) => (recovery, None),
        };
        assert(exists|other: &str| other@ == source@ && #[trigger] circuit_recovery_matches(other, recovery)
            && (model matches Ok(index) ==> build_index_matches(other, index))) by {
            assert(text@ == source@ && circuit_recovery_matches(text, recovery));
        };
        Self { source, recovery, build_rows }
    }

    /// 同じ本文のビルド索引を複製し、名前の文字列を現在の本文から借用する。
    ///
    /// 本文が変わった場合や、ビルド索引を保持していない場合は `None` を返す。
    pub fn reuse_build_index<'a>(&self, current: &'a str) -> (result: Option<NamedBuildCircuit<'a>>)
        ensures
            result.is_some() <==> current@ == self.source_model() && self.build_model().is_some(),
            result matches Some(named) ==>
                circuit_source_matches(current)
                && build_index_matches(current, named.build_model())
                && named.entry_ranges@.len() == named.syntax.entries@.len()
                && circuit_index_matches(current, named.syntax.forms@, named.syntax.entries@)
                && complete_list_indices(named.syntax.forms@) && nested_list_indices(named.syntax.forms@)
                && form_spans_valid(current, named.syntax.forms@, current.spec_bytes().len() as int)
                && named_forms_match(current, named.syntax.forms@, named.syntax.entries@,
                    named.names@, named.syntax.entries@.len() as int),
    {
        match self.copy_build_index(current) {
            Some(index) => Some(name_build_index(current, index)),
            None => None,
        }
    }

    fn copy_build_index(&self, current: &str) -> (result: Option<BuildCircuitIndex>)
        ensures
            result.is_some() <==> current@ == self.source_model() && self.build_model().is_some(),
            result matches Some(index) ==>
                circuit_source_matches(current)
                && build_index_matches(current, index)
                && complete_list_indices(index.syntax.forms@) && nested_list_indices(index.syntax.forms@)
                && form_spans_valid(current, index.syntax.forms@, current.spec_bytes().len() as int),
    {
        proof { use_type_invariant(self); }
        if current != self.text() {
            return None;
        }
        if let (CircuitRecovery::Complete(syntax), Some(rows)) = (&self.recovery, &self.build_rows) {
            let index = copy_build_parts(syntax, rows);
            proof {
                let original = choose|text: &str| text@ == self.source@
                    && #[trigger] circuit_recovery_matches(text, self.recovery)
                    && (self.build_model() matches Some(index) ==> build_index_matches(text, index));
                assert(original.spec_bytes() == current.spec_bytes());
                assert(build_index_matches(original, self.build_model()->Some_0));
                build_index_transfers_on_bytes(original, current, self.build_model()->Some_0);
                copied_build_index_matches(current, self.build_model()->Some_0, index);
                circuit_recovery_transfers_on_sexpr_bytes(original, current, &self.recovery);
            }
            Some(index)
        } else {
            None
        }
    }

    /// 解析結果と一緒に保持した本文を返す。
    pub fn text(&self) -> (text: &str)
        ensures text@ == self.source_model(),
            self.recovery_model() matches CircuitRecovery::WithSyntaxRepairs { recovered, .. }
                ==> recovered_replay_matches(text, recovered.forms@, recovered.repairs@, recovered.original_lists@),
    {
        let text = self.source.as_str();
        proof {
            use_type_invariant(self);
            let original = choose|old: &str| old@ == self.source@
                && #[trigger] circuit_recovery_matches(old, self.recovery);
            if let CircuitRecovery::WithSyntaxRepairs { recovered, .. } = &self.recovery {
                reveal(circuit_recovery_matches);
                crate::recovery_replay::recovery_replay_transfers_on_bytes(original, text, recovered);
            }
        }
        text
    }

    /// 構築時の回復結果を参照する。
    pub fn recovery(&self) -> (result: &CircuitRecovery)
        ensures *result == self.recovery_model(),
    {
        &self.recovery
    }

    /// 修復を含む旧本文について、編集区間の外にある元リストの列を選ぶ。
    ///
    /// 接頭部は編集開始以前に閉じた最後の元リストまで、接尾部は編集終了以降に閉じた最初の
    /// 元リストの直後からとする。編集終了が接頭部の終端なら、同じ位置から接尾部を始める。
    /// 構文の修復がない場合、編集範囲が逆順の場合、必要な閉じ括弧を選べない場合は `None` を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_syntax::circuit::{CachedCircuitRecovery, CircuitRecoveryReuseWindow};
    ///
    /// let old = CachedCircuitRecovery::analyze("(using nor)) (unknown)".to_owned());
    /// assert_eq!(old.recovery_reuse_window(11..11), Some(CircuitRecoveryReuseWindow {
    ///     start: 11, join: 11, head_count: 1, first_tail: 1,
    /// }));
    /// ```
    pub fn recovery_reuse_window(&self, edit: Range<usize>) -> (window: Option<CircuitRecoveryReuseWindow>)
        ensures window matches Some(w) ==> self.recovery_model() matches CircuitRecovery::WithSyntaxRepairs { recovered, .. }
            && w.matches(recovered.original_lists@, edit),
    {
        let CircuitRecovery::WithSyntaxRepairs { recovered, .. } = &self.recovery else { return None; };
        proof {
            use_type_invariant(self);
            let original = choose|text: &str| text@ == self.source@
                && #[trigger] circuit_recovery_matches(text, self.recovery);
            reveal(circuit_recovery_matches);
            assert(original_list_ranges(original, recovered.original_lists@, recovered.repairs@,
                original.spec_bytes().len() as int));
            reveal(original_list_ranges);
            assert(original_lists_ordered(recovered.original_lists@));
        }
        select_recovery_window(recovered.original_lists.as_slice(), edit)
    }

    /// 同じ UTF-8 本文が S 式として読める場合に、完了した結果を返す。
    ///
    /// 回路文法の違反を含む結果も返す。字句や S 式の修復が必要な場合は、呼び出し側が回復解析する。
    pub fn reuse(&self, current: &str) -> (result: Option<&CircuitRecovery>)
        ensures
            result.is_some() <==> current@ == self.source_model() && well_formed_sexpr(current),
            result matches Some(reused) ==> *reused == self.recovery_model()
                && circuit_recovery_matches(current, *reused),
    {
        proof { use_type_invariant(self); }
        let same = current == self.text();
        proof {
            let original = choose|text: &str| text@ == self.source@ && #[trigger] circuit_recovery_matches(text, self.recovery)
                && (self.build_model() matches Some(index) ==> build_index_matches(text, index));
            if same {
                let bytes = current.spec_bytes();
                assert(original.spec_bytes() == bytes);
                crate::sexpr_models_agree_on_bytes(original, current);
                if !(self.recovery is WithSyntaxRepairs) {
                    circuit_recovery_transfers_on_sexpr_bytes(original, current, &self.recovery);
                }
            }
        }
        if same && !matches!(&self.recovery, CircuitRecovery::WithSyntaxRepairs { .. }) {
            Some(&self.recovery)
        } else {
            None
        }
    }

}

} // verus!
