//! 文書の回復構文を、同じ本文に対する解析に再利用する。

use alloc::string::String;
use vstd::prelude::*;

use super::{CircuitRecovery, recover_circuit_forms};
#[cfg(verus_only)]
use super::{
    circuit_recovery_matches, circuit_recovery_transfers_on_sexpr_bytes, well_formed_sexpr,
};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 一つの完了済みの回復解析と、その解析に使った本文。
///
/// パスや文書版は保持しない。呼び出し側は現在のスナップショットの位置として結果を扱う。
pub struct CachedCircuitRecovery {
    source: String,
    recovery: CircuitRecovery,
}

impl CachedCircuitRecovery {
    /// 解析時の本文を Unicode スカラー値の列として表す。
    pub closed spec fn source_model(&self) -> Seq<char> { self.source@ }

    /// 本文から得た回復結果を表す。
    pub closed spec fn recovery_model(&self) -> CircuitRecovery { self.recovery }

    #[verifier::type_invariant]
    spec fn analyzed(&self) -> bool {
        exists|text: &str| text@ == self.source@ && #[trigger] circuit_recovery_matches(text, self.recovery)
    }

    /// ソースを回復解析し、本文と完了した結果を保持する。
    pub fn analyze(source: String) -> (cache: Self)
        ensures cache.source_model() == source@,
    {
        let text = source.as_str();
        let recovery = recover_circuit_forms(text);
        assert(exists|text: &str| text@ == source@ && #[trigger] circuit_recovery_matches(text, recovery));
        Self { source, recovery }
    }

    /// 解析結果と一緒に保持した本文を返す。
    pub fn text(&self) -> (text: &str)
        ensures text@ == self.source_model(),
    {
        self.source.as_str()
    }

    /// 構築時の回復結果を参照する。
    pub fn recovery(&self) -> (result: &CircuitRecovery)
        ensures *result == self.recovery_model(),
    {
        &self.recovery
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
            let original = choose|text: &str| text@ == self.source@ && #[trigger] circuit_recovery_matches(text, self.recovery);
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
