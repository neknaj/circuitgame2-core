//! 通常呼び出しの出力型を信号参照に伝え、後続の呼び出しの入力型と照合する。

use super::{
    FuncAtomTypeError, FuncCallInputsError, FuncCallOutputError, FuncCallOutputTypes,
    FuncLiteralError, FuncLiteralWidths, FuncWiringResult, SignalType, UseAliases,
};
#[cfg(verus_only)]
use super::{FuncWiring, function_atoms::atoms_match};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 関数の配線、定数幅、および信号ごとに判明した型。
#[derive(Debug)]
pub struct FuncSignalTypes<'p, 'a> {
    /// 配線と定数の右辺の検査結果。対象外や展開待ちも保持する。
    pub literals: FuncLiteralWidths<'p, 'a>,
    /// 左辺の駆動元と同じ順に並ぶ型。未確定の型は `None`。
    /// 対象外や展開待ちでは空になる。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

/// 関数内の信号型と呼び出しを検査したときの最初の違反。
#[derive(Debug)]
pub enum FuncSignalTypeError<'p, 'a> {
    /// 配線、入出力数、または定数の幅に関する診断。
    Literal(FuncLiteralError<'p, 'a>),
    /// 右辺全体を占める通常呼び出しの署名または出力に関する診断。
    CallOutput(FuncCallOutputError<'p, 'a>),
    /// 裸の信号名が参照した型と、駆動先の出力宣言型の不一致。
    Signal(FuncAtomTypeError<'p, 'a>),
    /// 直接の引数を検査した呼び出しの位置と、署名または引数に関する診断。
    CallInput(FuncCallInputsError<'p, 'a>),
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn signal_type_sources(
        &self, file: usize, entry: usize, limit: u64, literals: FuncLiteralWidths, wiring: &FuncWiring,
        roots: FuncCallOutputTypes,
    ) -> bool {
        &&& literals.wiring == FuncWiringResult::Checked(*wiring)
        &&& roots.wiring == literals.wiring
        &&& self.func_literal_evidence(file, entry, limit, Ok(literals))
        &&& self.func_call_outputs_evidence(file, entry, limit, Ok(roots))
    }

    spec fn propagated_types_match(
        &self, file: usize, entry: usize, wiring: &FuncWiring, literals: FuncLiteralWidths,
        roots: FuncCallOutputTypes, result: Result<Vec<Option<SignalType>>, FuncAtomTypeError>,
    ) -> bool {
        let project = self.targets.project_model();
        atoms_match(&project.sources_model()[file as int], &project.circuits_model()[file as int],
            entry as int, wiring, literals.widths@, roots.types@, result)
    }

    /// 定数と通常呼び出しの型、信号の束縛、直接の引数の検査が結果に対応することを表す。
    pub closed spec fn func_signal_types_evidence(
        &self, file: usize, entry: usize, limit: u64, result: Result<FuncSignalTypes, FuncSignalTypeError>,
    ) -> bool {
        match result {
            Err(FuncSignalTypeError::Literal(error)) => self.func_literal_evidence(file, entry, limit, Err(error)),
            Err(FuncSignalTypeError::CallOutput(error)) => !(error is Caller)
                && self.func_call_outputs_evidence(file, entry, limit, Err(error))
                && exists|literals: FuncLiteralWidths| literals.wiring matches FuncWiringResult::Checked(scope)
                    && #[trigger] self.func_literal_evidence(file, entry, limit, Ok(literals))
                    && self.call_output_failure(file, entry, limit, &scope.drivers, error),
            Err(FuncSignalTypeError::Signal(error)) => exists|literals: FuncLiteralWidths, wiring: FuncWiring, roots: FuncCallOutputTypes|
                #[trigger] self.signal_type_sources(file, entry, limit, literals, &wiring, roots)
                && self.propagated_types_match(file, entry, &wiring, literals, roots, Err(error)),
            Err(FuncSignalTypeError::CallInput(error)) => exists|literals: FuncLiteralWidths, wiring: FuncWiring,
                roots: FuncCallOutputTypes, types: Vec<Option<SignalType>>|
                #[trigger] self.signal_type_sources(file, entry, limit, literals, &wiring, roots)
                && #[trigger] self.propagated_types_match(file, entry, &wiring, literals, roots, Ok(types))
                && self.prepared_call_inputs_match(file, entry, limit, types@, &wiring, Err(error)),
            Ok(result) => self.func_literal_evidence(file, entry, limit, Ok(result.literals))
                && if let FuncWiringResult::Checked(wiring) = result.literals.wiring {
                    exists|roots: FuncCallOutputTypes|
                        #[trigger] self.signal_type_sources(file, entry, limit, result.literals, &wiring, roots)
                        && self.propagated_types_match(file, entry, &wiring, result.literals, roots, Ok(result.types))
                        && self.prepared_call_inputs_match(file, entry, limit, result.types@, &wiring, Ok(()))
                } else { result.types@.len() == 0 },
        }
    }

    /// 定数と通常呼び出しから得た型を信号参照に伝え、関数内の呼び出しを検査する。
    ///
    /// 右辺全体が通常呼び出しなら、出力型を左辺の名前へ順に割り当てる。
    /// 裸の信号名は入力または先行定義の型を引き継ぐ。呼び出しの直接の引数が定数か、
    /// 型の判明した裸の信号名なら、対応する入力型と照合する。
    /// ほかの複合式の結果型は保留する。展開待ちは呼び出し位置を保ったまま返す。
    ///
    /// # Errors
    ///
    /// 配線・入出力数・定数幅、通常呼び出しの出力、裸の信号参照、直接の引数の順に検査し、
    /// 各段階で最初に見つけた違反を返す。
    pub fn check_func_signal_types(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncSignalTypes<'p, 'a>, FuncSignalTypeError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_signal_types_evidence(file, entry, max_width, result),
    {
        let literals = match self.check_func_literal_widths(file, entry, max_width) {
            Ok(literals) => literals,
            Err(error) => return Err(FuncSignalTypeError::Literal(error)),
        };
        if !matches!(literals.wiring, FuncWiringResult::Checked(_)) {
            return Ok(FuncSignalTypes { literals, types: Vec::new() });
        }
        proof { self.literals_preserve_arity(file, entry, max_width, literals); }
        let ghost prepared = literals;
        let FuncLiteralWidths { wiring: prepared_wiring, widths: literal_widths } = literals;
        let outputs = match self.check_call_outputs_with_arity(file, entry, max_width, prepared_wiring) {
            Ok(outputs) => outputs,
            Err(error) => {
                assert(self.func_signal_types_evidence(file, entry, max_width, Err(FuncSignalTypeError::CallOutput(error)))) by {
                    assert(self.func_literal_evidence(file, entry, max_width, Ok(prepared)));
                };
                return Err(FuncSignalTypeError::CallOutput(error));
            },
        };
        let ghost roots = outputs;
        let FuncCallOutputTypes { wiring: checked_wiring, types: call_types } = outputs;
        let literals = FuncLiteralWidths { wiring: checked_wiring, widths: literal_widths };
        let FuncWiringResult::Checked(ref scope) = literals.wiring else {
            proof { assert(false); }
            unreachable!()
        };
        proof {
            assert(literals == prepared);
            self.arity_preserves_wiring(file, entry, max_width, literals.wiring);
            self.checked_wiring_is_func(file, entry, max_width, *scope);
            self.literal_widths_fit_wiring(file, entry, max_width, &literals, scope);
            self.call_outputs_fit_wiring(file, entry, max_width, &roots, scope);
            assert(self.signal_type_sources(file, entry, max_width, literals, scope, roots));
        }
        let types = match self.check_atoms(file, entry, max_width, &literals, scope, call_types.as_slice()) {
            Ok(types) => types,
            Err(error) => {
                assert(self.func_signal_types_evidence(file, entry, max_width, Err(FuncSignalTypeError::Signal(error)))) by {
                    assert(self.propagated_types_match(file, entry, scope, literals, roots, Err(error)));
                };
                return Err(FuncSignalTypeError::Signal(error));
            },
        };
        assert(self.propagated_types_match(file, entry, scope, literals, roots, Ok(types)));
        let type_slice = types.as_slice();
        let checked = self.check_all_inputs_with_types(file, entry, max_width, type_slice, scope);
        match checked {
            Ok(()) => {
                proof {
                    assert(type_slice@ == types@);
                    self.prepared_inputs_succeeded(file, entry, max_width, types@, scope, checked);
                }
                assert(exists|outputs: FuncCallOutputTypes|
                    #[trigger] self.signal_type_sources(file, entry, max_width, literals, scope, outputs)
                    && self.propagated_types_match(file, entry, scope, literals, outputs, Ok(types))
                    && self.prepared_call_inputs_match(file, entry, max_width, types@, scope, Ok(()))) by {
                    assert(self.signal_type_sources(file, entry, max_width, literals, scope, roots));
                };
                Ok(FuncSignalTypes { literals, types })
            },
            Err(error) => {
                assert(self.func_signal_types_evidence(file, entry, max_width, Err(FuncSignalTypeError::CallInput(error))));
                Err(FuncSignalTypeError::CallInput(error))
            },
        }
    }
}

} // verus!
