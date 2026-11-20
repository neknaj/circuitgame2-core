//! 通常呼び出しの出力型を信号参照に伝え、後続の呼び出しの入力型と照合する。

use super::{
    FuncAtomTypeError, FuncCallInputsError, FuncCallOutputError, FuncCallOutputTypes,
    FuncLiteralError, FuncLiteralWidths, FuncWiringResult, SignalType, StructureExpressionTypeError,
    StructureTypeError, UseAliases,
};
#[cfg(verus_only)]
use super::{FuncWiring, function_atoms::{
    atoms_match, structure_projection_matches, structure_projection_required, structure_projections_in_order,
}};
use alloc::vec::Vec;
use super::signature_cache::SignatureCache;
use super::function_atoms::StructureProjections;
#[cfg(verus_only)]
use super::function_atoms::StructureProjection;
use super::selection_arguments::SelectionArgumentError;
use crate::project::LocatedName;
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
    /// 信号参照やビット選択式の型と、駆動先の出力宣言型の不一致。
    Signal(FuncAtomTypeError<'p, 'a>),
    /// ビット選択の入力がビット列型に合わない。
    SelectionInputType {
        /// 入力に指定した信号名の範囲。
        reference: LocatedName<'p, 'a>,
        /// 入力の型と、その型を決めた元ソースの位置。
        actual: SignalType<'p, 'a>,
    },
    /// ビット選択の数値引数または選択範囲の違反。
    SelectionArgument(SelectionArgumentError<'p, 'a>),
    /// 配置表を準備した際に見つかった構造体の宣言違反。
    StructureLayout(StructureTypeError<'p, 'a>),
    /// 構造体式の型名、入力型、幅、またはフィールドの違反。
    StructureExpression(StructureExpressionTypeError<'p, 'a>),
    /// 直接の引数を検査した呼び出しの位置と、署名または引数に関する診断。
    CallInput(FuncCallInputsError<'p, 'a>),
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) proof fn checked_types_keep_wiring(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes, wiring: FuncWiring,
    )
        requires
            self.func_signal_types_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
        ensures self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
    {
        self.literals_preserve_arity(file, entry, limit, typed.literals);
        self.arity_preserves_wiring(file, entry, limit, typed.literals.wiring);
    }

    pub(super) closed spec fn signal_type_sources(
        &self, file: usize, entry: usize, limit: u64, literals: FuncLiteralWidths, wiring: &FuncWiring,
        roots: FuncCallOutputTypes,
    ) -> bool {
        &&& literals.wiring == FuncWiringResult::Checked(*wiring)
        &&& roots.wiring == literals.wiring
        &&& self.func_literal_evidence(file, entry, limit, Ok(literals))
        &&& self.func_call_outputs_evidence(file, entry, limit, Ok(roots))
    }

    spec fn propagated_types_match(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, literals: FuncLiteralWidths,
        roots: FuncCallOutputTypes, result: Result<Vec<Option<SignalType>>, FuncSignalTypeError>,
    ) -> bool {
        let project = self.targets.project_model();
        atoms_match(self, file, limit, &project.sources_model()[file as int], &project.circuits_model()[file as int],
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
            Err(error) if error is Signal || error is SelectionInputType || error is SelectionArgument
                || error is StructureLayout || error is StructureExpression =>
                exists|literals: FuncLiteralWidths, wiring: FuncWiring, roots: FuncCallOutputTypes|
                #[trigger] self.signal_type_sources(file, entry, limit, literals, &wiring, roots)
                && self.propagated_types_match(file, entry, limit, &wiring, literals, roots, Err(error)),
            Err(FuncSignalTypeError::CallInput(error)) => exists|literals: FuncLiteralWidths, wiring: FuncWiring,
                roots: FuncCallOutputTypes, types: Vec<Option<SignalType>>|
                #[trigger] self.signal_type_sources(file, entry, limit, literals, &wiring, roots)
                && #[trigger] self.propagated_types_match(file, entry, limit, &wiring, literals, roots, Ok(types))
                && self.prepared_call_inputs_match(file, entry, limit, types@, &wiring, Err(error)),
            Ok(result) => self.func_literal_evidence(file, entry, limit, Ok(result.literals))
                && if let FuncWiringResult::Checked(wiring) = result.literals.wiring {
                    exists|roots: FuncCallOutputTypes|
                        #[trigger] self.signal_type_sources(file, entry, limit, result.literals, &wiring, roots)
                        && self.propagated_types_match(file, entry, limit, &wiring, result.literals, roots, Ok(result.types))
                        && self.prepared_call_inputs_match(file, entry, limit, result.types@, &wiring, Ok(()))
                } else { result.types@.len() == 0 },
            _ => false,
        }
    }

    /// 定数と通常呼び出しから得た型を信号参照に伝え、関数内の呼び出しを検査する。
    ///
    /// 右辺全体が通常呼び出しなら、出力型を左辺の名前へ順に割り当てる。
    /// 裸の信号名は入力または先行定義の型を引き継ぐ。型が分かる信号名を入力とする
    /// `bit` と `slice` は選択範囲を、`field`・`as`・`raw` は構造体の型と配置を検査する。
    /// 呼び出しの直接の引数が定数か、
    /// 型の判明した裸の信号名なら、対応する入力型と照合する。
    /// 参照先の署名が得られたら、その署名をこの検査の入出力の照合で再利用する。
    /// ほかの複合式の結果型は保留する。展開待ちは呼び出し位置を保ったまま返す。
    ///
    /// # Examples
    ///
    /// 構造体を経由する定義から、フィールドの型と構造体の総幅を引き継ぐ。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     ResolvedPortType, SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "packet.ncg2", revision: 1,
    ///     text: "(struct Packet (width 8) (tag (bits 3) (at 2)))
    ///            (func unpack (in (bus (bits 8))) (out (tag (bits 3)) (raw-bus (bits 8)))
    ///                (def packet (as Packet bus))
    ///                (def tag (field packet tag))
    ///                (def raw-bus (raw packet)))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let checked = aliases.check_func_signal_types(0, 1, 8).unwrap();
    /// assert!(matches!(checked.types[0].as_ref().unwrap().ty, ResolvedPortType::Struct { .. }));
    /// assert!(matches!(checked.types[1].as_ref().unwrap().ty, ResolvedPortType::Bits(3)));
    /// assert!(matches!(checked.types[2].as_ref().unwrap().ty, ResolvedPortType::Bits(8)));
    /// ```
    ///
    /// # Errors
    ///
    /// 配線・入出力数・定数幅、通常呼び出しの出力、定義順の型伝播、直接の引数の順に検査する。
    /// 型が判明した信号に対する構造体式を最初に調べる時点で、プロジェクト全体の構造体の配置と循環を検査する。
    /// その後、式ごとに `as` の型名を解決し、入力型、幅、フィールドを照合する。
    pub fn check_func_signal_types(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncSignalTypes<'p, 'a>, FuncSignalTypeError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_signal_types_evidence(file, entry, max_width, result),
    {
        match self.check_func_signal_projections(file, entry, max_width) {
            Ok((types, _)) => Ok(types),
            Err(error) => Err(error),
        }
    }

    pub(super) fn check_func_signal_projections(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<(FuncSignalTypes<'p, 'a>, StructureProjections<'p, 'a>), FuncSignalTypeError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            self.func_signal_types_evidence(file, entry, max_width, match result {
                Ok((types, _)) => Ok(types),
                Err(error) => Err(error),
            }),
            result matches Ok((typed, projections)) ==> {
                &&& projections.layouts matches Some(layouts) ==> self.structure_types_match(max_width, Ok(layouts))
                &&& projections.layouts.is_none() ==> projections.entries@.len() == 0
                &&& if let FuncWiringResult::Checked(wiring) = typed.literals.wiring {
                    &&& typed.types@.len() == wiring.drivers.definitions@.len()
                    &&& structure_projections_in_order(projections.entries@, typed.types@.len() as int,
                        wiring.drivers.signature.inputs@.len() as int)
                    &&& projections.layouts matches Some(table) ==> forall|j: int| 0 <= j < projections.entries@.len()
                        ==> structure_projection_matches(self, file, entry, max_width, &wiring, table, typed.types@,
                            #[trigger] projections.entries@[j])
                    &&& self.func_structure_projections_complete(file, entry, max_width, typed, &wiring, projections.entries@)
                } else {
                    projections.entries@.len() == 0
                }
            },
    {
        let literals = match self.check_func_literal_widths(file, entry, max_width) {
            Ok(literals) => literals,
            Err(error) => return Err(FuncSignalTypeError::Literal(error)),
        };
        if !matches!(literals.wiring, FuncWiringResult::Checked(_)) {
            return Ok((
                FuncSignalTypes { literals, types: Vec::new() },
                StructureProjections { entries: Vec::new(), layouts: None },
            ));
        }
        proof { self.literals_preserve_arity(file, entry, max_width, literals); }
        let ghost prepared = literals;
        let FuncLiteralWidths { wiring: prepared_wiring, widths: literal_widths } = literals;
        let mut signatures = SignatureCache::new();
        let outputs = match self.check_call_outputs_with_arity(file, entry, max_width, prepared_wiring, &mut signatures) {
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
        let (types, projections) = match self.check_atoms(file, entry, max_width, &literals, scope, call_types.as_slice()) {
            Ok(propagated) => propagated,
            Err(error) => {
                assert(self.func_signal_types_evidence(file, entry, max_width, Err(error))) by {
                    assert(self.propagated_types_match(file, entry, max_width, scope, literals, roots, Err(error)));
                };
                return Err(error);
            },
        };
        assert(self.propagated_types_match(file, entry, max_width, scope, literals, roots, Ok(types)));
        let type_slice = types.as_slice();
        let checked = self.check_all_inputs_with_types(file, entry, max_width, type_slice, scope, &mut signatures);
        match checked {
            Ok(()) => {
                proof {
                    assert(type_slice@ == types@);
                    self.prepared_inputs_succeeded(file, entry, max_width, types@, scope, checked);
                }
                assert(exists|outputs: FuncCallOutputTypes|
                    #[trigger] self.signal_type_sources(file, entry, max_width, literals, scope, outputs)
                    && self.propagated_types_match(file, entry, max_width, scope, literals, outputs, Ok(types))
                    && self.prepared_call_inputs_match(file, entry, max_width, types@, scope, Ok(()))) by {
                    assert(self.signal_type_sources(file, entry, max_width, literals, scope, roots));
                };
                Ok((FuncSignalTypes { literals, types }, projections))
            },
            Err(error) => {
                assert(self.func_signal_types_evidence(file, entry, max_width, Err(FuncSignalTypeError::CallInput(error))));
                Err(FuncSignalTypeError::CallInput(error))
            },
        }
    }

    pub(super) open spec fn func_structure_projections_complete(
        &self, file: usize, entry: usize, limit: u64, typed: FuncSignalTypes,
        wiring: &FuncWiring, rows: Seq<StructureProjection>,
    ) -> bool {
        let project = self.targets.project_model();
        exists|roots: FuncCallOutputTypes|
            #[trigger] self.signal_type_sources(file, entry, limit, typed.literals, wiring, roots)
            && roots.types@.len() == wiring.drivers.definitions@.len()
            && (forall|target: int| 0 <= target < typed.types@.len() &&
                #[trigger] structure_projection_required(
                    &project.sources_model()[file as int], &project.circuits_model()[file as int],
                    entry, wiring, typed.literals.widths@, roots.types@, typed.types@, target,
                ) ==> exists|j: int| 0 <= j < rows.len() && (#[trigger] rows[j]).target == target)
    }
}

} // verus!
