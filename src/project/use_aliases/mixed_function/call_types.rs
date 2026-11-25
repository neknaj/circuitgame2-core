//! 混在プロジェクトで通常呼び出しの出力型を左辺の名前に対応付ける。

mod inputs;
pub use inputs::MixedFuncInputTypes;

use super::{MixedFuncArityError, MixedTypedSignatureError, MixedUseAliases, ProjectSourceIndex, arity::CheckedMixedCalls};
use crate::project::{CallInputError, DefinitionPosition, FuncAtomTypeError, FuncCallArity, FuncCallOutputError, FuncCallTarget, FuncLiteralError, FuncLiteralWidths,
    FuncDrivers, FuncWiringResult, LocatedName, PortDirection, ProjectSource, SignalType};
use crate::project::use_aliases::{
    call_arity::{outputs::transfer_call_output, typed::{cached_signature, signature_port}},
    function_atoms::copy_location, function_literals::{check_literals, index_outputs}, signature_cache::SignatureCache,
};
#[cfg(verus_only)]
use super::{mixed_use_targets_match, parsed_index_evidence, project_source_index_evidence};
#[cfg(verus_only)]
use crate::project::{FuncWiring, ResolvedPortType, TypedRoutineSignature};
#[cfg(verus_only)]
use crate::project::use_aliases::{
    call_arity::{checks::target_count, outputs::output_transfer},
    call_arity::typed::cached_call_model,
    definitions::definition_count,
    function_drivers::{expected_output_context, indexed_driver_site},
    function_literals::{literal_widths_match, output_indices},
};
use crate::syntax::circuit::NamedBuildCircuit;
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence,
    ordinary_call_at, root_call_shape_location};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 混在プロジェクトで、定数と通常呼び出しの出力から決まった型。
#[derive(Debug)]
pub struct MixedFuncOutputTypes<'p, 'a> {
    /// 結線と、定義の左辺に対応する定数の幅。
    pub literals: FuncLiteralWidths<'p, 'a>,
    /// 定義の左辺順に並ぶ出力型。右辺全体が通常呼び出しである定義にだけ型を置く。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

struct PreparedMixedOutputs<'p, 'a> {
    typed: MixedFuncOutputTypes<'p, 'a>,
    calls: CheckedMixedCalls<'p, 'a>,
    signatures: SignatureCache<'p, 'a>,
}

/// 混在プロジェクトの関数で、結線、個数、型または幅を検査して見つかった違反。
#[derive(Debug)]
pub enum MixedFuncTypeError<'p, 'a> {
    /// 結線またはポート数の違反。
    Arity(MixedFuncArityError<'p, 'a>),
    /// 定数の幅または出力に必要な型の違反。
    Literal(FuncLiteralError<'p, 'a>),
    /// 呼び出し先の署名の違反。
    Signature {
        /// 元の呼び出し式と、選んだ宣言の位置。
        call: FuncCallArity<'p, 'a>,
        /// 宣言側の違反。
        error: MixedTypedSignatureError<'p, 'a>,
    },
    /// 呼び出しが返した型と、対応する出力ポートの型の違い。
    Output(FuncCallOutputError<'p, 'a>),
    /// 裸の信号の型と、駆動先で要求された型が異なる。
    Signal(FuncAtomTypeError<'p, 'a>),
    /// 通常呼び出しの実引数の幅または型が合わない。
    Input(CallInputError<'p, 'a>),
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    fn prepare_mixed_call_signature(
        &self, _at: Ghost<DefinitionPosition>, call: &FuncCallArity<'p, 'a>, limit: u64,
        signatures: &mut SignatureCache<'p, 'a>,
    ) -> (result: Result<(), MixedFuncTypeError<'p, 'a>>)
        requires
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
            self.mixed_checked_call(_at@, *call), old(signatures).matches_mixed(self, limit),
        ensures
            final(signatures).matches_mixed(self, limit),
            forall|place: (usize, usize)| #[trigger] old(signatures).signatures().contains_key(place) ==>
                final(signatures).signatures().contains_key(place)
                    && final(signatures).signatures()[place] == old(signatures).signatures()[place],
            match result {
                Ok(()) => call.target matches FuncCallTarget::Function { file, entry, arity, .. } ==> {
                    let stored = final(signatures).signatures();
                    &&& stored.contains_key((file, entry))
                    &&& stored[(file, entry)].inputs@.len() == arity.inputs
                    &&& stored[(file, entry)].outputs@.len() == arity.outputs
                },
                Err(error) => self.mixed_target_signature_failure(*call, limit, error),
            },
    {
        if let FuncCallTarget::Function { file, entry, arity: _arity, .. } = &call.target {
            proof { self.mixed_func_call_arity_origin(_at@.file, _at@.entry, _at@.definition, _at@.reference, *call); }
            match signatures.prepare_mixed(self, *file, *entry, limit) {
                Ok(true) => {
                    proof {
                        let typed = signatures.signatures()[(*file, *entry)];
                        self.mixed_typed_signature_arity(*file, *entry, limit, typed, *_arity);
                    }
                },
                Ok(false) => {
                    proof { assert(false); }
                    unreachable!()
                },
                Err(error) => return Err(MixedFuncTypeError::Signature { call: call.copy_site(), error }),
            }
        }
        Ok(())
    }

    spec fn mixed_target_signature_failure(&self, call: FuncCallArity, limit: u64, error: MixedFuncTypeError) -> bool {
        &&& error matches MixedFuncTypeError::Signature { call: original, error: signature }
        &&& call == original
        &&& call.target matches FuncCallTarget::Function { file, entry, .. }
        &&& self.mixed_typed_signature_matches(file, entry, limit, Err(signature))
    }

    proof fn retained_root_position(&self, file: usize, entry: usize, definition: usize, calls: CheckedMixedCalls)
        requires
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
            self.retained_mixed_calls(file, entry, calls), definition < calls.definitions@.len(),
            self.targets_model().project_model().has_func_callee(file, entry, definition, 0),
        ensures ({
            let range = calls.definitions@[definition as int];
            &&& range.start < range.end
            &&& calls.positions@[range.start as int].0 == 0
            &&& self.mixed_checked_call(DefinitionPosition { file, entry, definition, reference: 0 }, calls.positions@[range.start as int].1)
        }),
    {
        let range = calls.definitions@[definition as int];
        let rows = calls.positions@[range.start as int..range.end as int];
        let i = choose|i: int| 0 <= i < rows.len() && (#[trigger] rows[i]).0 == 0;
        assert(rows[0] == calls.positions@[range.start as int]);
        assert(i == 0) by { if i > 0 { assert(rows[0].0 < rows[i].0); } };
    }

    /// 定数幅を検査し、通常呼び出しの出力型を、その出力を受け取る左辺へ割り当てる。
    ///
    /// 結線と入出力数を先に検査する。対象外と展開待ちはその結果を引き継ぐ。
    ///
    /// # Errors
    ///
    /// 定数幅は呼び出しの出力型に先立って検査する。その後、定義順、各定義の左辺の順に
    /// 呼び出し先の署名と呼び出し元の出力型を照合する。実引数の型は後続の検査で確かめる。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{FuncCallOutputError, MixedFuncTypeError, ResolvedPortType,
    ///     SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources};
    ///
    /// let design = "(func forward (in (x (bits 8))) (out (y (bits 8))) (def y (::lib::byte x)))
    ///     (func wrong (in (x (bits 8))) (out (y (bits 4))) (def y (::lib::byte x)))";
    /// let library = "(namespace lib (export byte) (func byte (in (x (bits 8))) (out (x (bits 8)))))";
    /// let project = parse_project_sources(&[
    ///     SourceSnapshot { path: "design.ncg2", revision: 8, text: design },
    ///     SourceSnapshot { path: "library.ncg2", revision: 3, text: library },
    ///     SourceSnapshot { path: "helper.ncg2m", revision: 2,
    ///         text: "(defn ready (as-type (Fn () Bool) (fn () true)))" },
    /// ]).unwrap();
    /// let targets = index_mixed_use_targets(&project).unwrap();
    /// let aliases = check_mixed_use_aliases(&targets).unwrap();
    /// let checked = aliases.check_mixed_func_output_types(0, 0, 64).unwrap();
    /// assert!(matches!(checked.types[0].as_ref().unwrap().ty, ResolvedPortType::Bits(8)));
    /// let Err(MixedFuncTypeError::Output(FuncCallOutputError::OutputType { call, expected, actual, .. })) =
    ///     aliases.check_mixed_func_output_types(0, 1, 64) else { panic!() };
    /// assert_eq!((&design[call.span], call.source.revision), ("(::lib::byte x)", 8));
    /// assert!(matches!(expected.ty, ResolvedPortType::Bits(4)));
    /// assert_eq!(actual.origin.source.revision, 3);
    /// ```
    pub fn check_mixed_func_output_types(&self, file: usize, entry: usize, limit: u64)
        -> (result: Result<MixedFuncOutputTypes<'p, 'a>, MixedFuncTypeError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures self.mixed_func_output_types_match(file, entry, limit, result),
    {
        match self.prepare_mixed_output_analysis(file, entry, limit) {
            Ok(prepared) => Ok(prepared.typed),
            Err(error) => Err(error),
        }
    }

    fn prepare_mixed_output_analysis(&self, file: usize, entry: usize, limit: u64)
        -> (result: Result<PreparedMixedOutputs<'p, 'a>, MixedFuncTypeError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures match result {
            Ok(prepared) => {
                let project = self.targets_model().project_model();
                &&& self.mixed_func_output_types_match(file, entry, limit, Ok(prepared.typed))
                &&& prepared.signatures.matches_mixed(self, limit)
                &&& prepared.typed.literals.wiring matches FuncWiringResult::Checked(scope) ==> {
                    let source = &project.sources_model()[file as int];
                    let parsed = &project.indexes_model()[file as int]->Circuit_0;
                    &&& self.mixed_output_context(file, entry, source, parsed, &scope.drivers, prepared.calls)
                    &&& prepared.typed.literals.widths@.len() == scope.drivers.definitions@.len()
                }
            },
            Err(error) => self.mixed_func_output_types_match(file, entry, limit, Err(error)),
        },
    {
        let (wiring, calls) = match self.prepare_mixed_func_arity(file, entry, limit, true) {
            Ok(prepared) => prepared,
            Err(error) => return Err(MixedFuncTypeError::Arity(error)),
        };
        let mut signatures = SignatureCache::new();
        let FuncWiringResult::Checked(ref scope) = wiring else {
            let typed = MixedFuncOutputTypes { literals: FuncLiteralWidths { wiring, widths: Vec::new() }, types: Vec::new() };
            return Ok(PreparedMixedOutputs { typed, calls, signatures });
        };
        proof {
            self.mixed_arity_preserves_wiring(file, entry, limit, wiring);
            self.mixed_wiring_index_origin(file, entry, limit, *scope);
            self.mixed_wiring_driver_evidence(file, entry, limit, *scope);
            self.mixed_driver_output_context(file, entry, limit, scope.drivers);
        }
        let project = self.targets().project();
        let source = &project.sources()[file];
        let index = &project.indexes()[file];
        let ProjectSourceIndex::Circuit(parsed) = index else { unreachable!() };
        proof {
            project_source_index_evidence(*source, *index);
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
            assert(self.mixed_output_context(file, entry, source, parsed, &scope.drivers, calls)) by {
                reveal(MixedUseAliases::mixed_output_context);
            };
        }
        let drivers = &scope.drivers;
        let widths = match check_literals(source, parsed, entry, drivers, limit) {
            Ok(widths) => widths,
            Err(error) => return Err(MixedFuncTypeError::Literal(error)),
        };
        let outlets = index_outputs(drivers);
        let mut types = Vec::new();
        let mut index = 0;
        proof { reveal(MixedUseAliases::mixed_output_prefix); }
        while index < drivers.definitions.len()
            invariant
                mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
                self.mixed_func_arity_matches(file, entry, limit, Ok(wiring)), wiring == FuncWiringResult::Checked(*scope),
                *drivers == scope.drivers,
                *source == self.targets_model().project_model().sources_model()[file as int],
                *parsed == self.targets_model().project_model().indexes_model()[file as int]->Circuit_0,
                self.mixed_output_context(file, entry, source, parsed, drivers, calls),
                literal_widths_match(source, parsed, drivers, limit, Ok(widths)),
                output_indices(drivers, drivers.outputs@.len() as int, outlets@),
                signatures.matches_mixed(self, limit),
                index == types@.len() <= drivers.definitions@.len(),
                self.mixed_output_prefix(file, entry, limit, drivers, calls, outlets@, types@),
            decreases drivers.definitions@.len() - index,
        {
            let result = match self.check_mixed_output_step(file, entry, limit, source, parsed, drivers,
                &calls, outlets.as_slice(), index, &mut signatures) {
                Ok(typed) => typed,
                Err(error) => {
                    proof {
                        assert(self.mixed_output_context(file, entry, source, parsed, &scope.drivers, calls));
                        assert(literal_widths_match(source, parsed, &scope.drivers, limit, Ok(widths)));
                        assert(self.mixed_output_step(file, entry, limit, &scope.drivers, calls, outlets@,
                            types@.len() as int, Err(error)));
                        self.mixed_output_failed(file, entry, limit, *scope, calls, widths, outlets@, types@, error);
                    }
                    return Err(error);
                },
            };
            let ghost before = types@;
            types.push(result);
            proof {
                reveal(MixedUseAliases::mixed_output_prefix);
                assert forall|i: int| 0 <= i < types@.len() implies #[trigger]
                    self.mixed_output_step(file, entry, limit, drivers, calls, outlets@, i, Ok(types@[i])) by {
                    if i < before.len() { assert(types@[i] == before[i]); }
                };
            }
            index += 1;
        }
        let typed = MixedFuncOutputTypes { literals: FuncLiteralWidths { wiring, widths }, types };
        Ok(PreparedMixedOutputs { typed, calls, signatures })
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(48)]
    fn check_mixed_output_step(
        &self, _file: usize, entry: usize, limit: u64, source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>,
        drivers: &FuncDrivers<'p, 'a>, retained: &CheckedMixedCalls<'p, 'a>, outlets: &[Option<usize>],
        index: usize, signatures: &mut SignatureCache<'p, 'a>,
    ) -> (result: Result<Option<SignalType<'p, 'a>>, MixedFuncTypeError<'p, 'a>>)
        requires
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
            self.mixed_output_context(_file, entry, source, parsed, drivers, *retained),
            output_indices(drivers, drivers.outputs@.len() as int, outlets@),
            index < drivers.definitions@.len(),
            old(signatures).matches_mixed(self, limit),
        ensures
            final(signatures).matches_mixed(self, limit),
            self.mixed_output_step(_file, entry, limit, drivers, *retained, outlets@, index as int, result),
            result matches Err(error) ==> error is Signature || error is Output,
    {
        let ghost calls = *retained;
        proof {
            reveal(MixedUseAliases::mixed_output_context);
            parsed_index_evidence(*source, *parsed);
        }
        let frame = &parsed.entry_ranges[entry].definitions;
        let driver = &drivers.definitions[index];
        let definition = driver.definition - frame.start;
        let row = &parsed.definitions[driver.definition];
        let forms = parsed.syntax.forms.as_slice();
        let _form_count = forms.len();
        proof {
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, driver.definition as int);
            reveal(output_indices);
        }
        let result = if crate::syntax::circuit::definition_root_is_call(source.text, forms, row, parsed.references.as_slice()) {
            let range = &retained.definitions[definition];
            proof { self.retained_root_position(_file, entry, definition, calls); }
            let call = &retained.positions[range.start].1;
            let ghost at = DefinitionPosition { file: _file, entry, definition, reference: 0 };
            proof {
                self.mixed_func_call_arity_origin(_file, entry, definition, 0, *call);
                source.text_model_is_text();
                assert(frame.start + definition == driver.definition);
                root_call_shape_location(source.text, forms@, *row, parsed.references@, call.call);
            }
            match self.prepare_mixed_call_signature(Ghost(at), call, limit, signatures) {
                Ok(()) => (),
                Err(error) => {
                    proof {
                        reveal(MixedUseAliases::mixed_output_step);
                        reveal(MixedUseAliases::mixed_call_output_outcome);
                        assert(self.mixed_output_step(_file, entry, limit, drivers, calls, outlets@, index as int, Err(error)));
                    }
                    return Err(error);
                },
            }
            let expression = LocatedName { source: call.source, span: call.call.span.start..call.call.span.end };
            let actual = self.read_mixed_cached_output(call, limit, driver.result_index, signatures);
            let expected = match outlets[index] {
                Some(port) => Some(&drivers.signature.outputs[port]),
                None => None,
            };
            match transfer_call_output(source, &driver.name, expression, expected, actual) {
                Ok(got) => {
                    proof {
                        assert(mixed_output_transfer(actual, match expected { Some(port) => Some(*port), None => None },
                            LocatedName { source, span: driver.name.span }, expression, Ok(Some(got))));
                        self.record_mixed_output_transfer(_file, entry, limit, drivers, calls, outlets@, index as int, actual, Ok(Some(got)));
                    }
                    Some(got)
                },
                Err(error) => {
                    let error = MixedFuncTypeError::Output(error);
                    proof {
                        assert(mixed_output_transfer(actual, match expected { Some(port) => Some(*port), None => None },
                            LocatedName { source, span: driver.name.span }, expression, Err(error)));
                        self.record_mixed_output_transfer(_file, entry, limit, drivers, calls, outlets@, index as int, actual, Err(error));
                    }
                    return Err(error);
                },
            }
        } else {
            assert(self.mixed_output_step(_file, entry, limit, drivers, calls, outlets@, index as int, Ok(None))) by {
                reveal(MixedUseAliases::mixed_output_step);
            };
            None
        };
        Ok(result)
    }

    fn read_mixed_cached_output(
        &self, call: &FuncCallArity<'p, 'a>, _limit: u64, index: usize, signatures: &SignatureCache<'p, 'a>,
    ) -> (actual: SignalType<'p, 'a>)
        requires
            signatures.matches_mixed(self, _limit),
            index < call.target.port_counts().outputs,
            call.target matches FuncCallTarget::Function { file, entry, arity, .. } ==> {
                let stored = signatures.signatures();
                stored.contains_key((file, entry)) && stored[(file, entry)].outputs@.len() == arity.outputs
            },
        ensures self.mixed_call_returns_type(*call, _limit, index, actual),
    {
        let signature = cached_signature(signatures, call);
        let Some(port) = signature_port(signature, PortDirection::Output, index) else { unreachable!() };
        let origin = match port.annotation {
            Some(site) => copy_location(site),
            None => LocatedName { source: call.source, span: call.call.span.start..call.call.span.end },
        };
        let actual = SignalType { ty: port.ty, origin };
        proof {
            reveal(MixedUseAliases::mixed_call_returns_type);
            let model = cached_call_model(signatures, *call);
            if let FuncCallTarget::Function { file, entry, .. } = call.target {
                let typed = model.signature->Function_0;
                assert(self.mixed_typed_signature_matches(file, entry, _limit, Ok(Some(typed))));
            }
        }
        actual
    }

    #[verifier::opaque]
    spec fn mixed_output_context(
        &self, file: usize, entry: usize, source: &ProjectSource, parsed: &NamedBuildCircuit,
        drivers: &FuncDrivers, calls: CheckedMixedCalls,
    ) -> bool {
        let project = self.targets_model().project_model();
        &&& super::typed::has_mixed_func(&project, file, entry)
        &&& *source == project.sources_model()[file as int]
        &&& *parsed == project.indexes_model()[file as int]->Circuit_0
        &&& crate::project::parsed_circuit_matches(*source, *parsed)
        &&& expected_output_context(source, parsed, entry as int, *drivers)
        &&& forall|i: int| 0 <= i < drivers.definitions@.len()
            ==> indexed_driver_site(source, parsed, entry as int, #[trigger] drivers.definitions@[i])
        &&& calls.definitions@.len() == definition_count(parsed, entry as int)
        &&& self.retained_mixed_calls(file, entry, calls)
    }

    #[verifier::opaque]
    spec fn mixed_call_returns_type(&self, call: FuncCallArity, limit: u64, result_index: usize, actual: SignalType) -> bool {
        match call.target {
            FuncCallTarget::Nor => actual == (SignalType { ty: ResolvedPortType::Bits(1),
                origin: LocatedName { source: call.source, span: call.call.span } }),
            FuncCallTarget::Function { file: to, entry: target, .. } => exists|typed: TypedRoutineSignature|
                #[trigger] self.mixed_typed_signature_matches(to, target, limit, Ok(Some(typed)))
                    && result_index < typed.outputs@.len()
                    && actual.ty == typed.outputs@[result_index as int].ty
                    && actual.origin == typed.outputs@[result_index as int].annotation,
        }
    }

    #[verifier::opaque]
    spec fn mixed_call_output_outcome(
        &self, call: FuncCallArity, limit: u64, result_index: usize,
        expected: Option<crate::project::TypedPort>, target: LocatedName, expression: LocatedName,
        result: Result<Option<SignalType>, MixedFuncTypeError>,
    ) -> bool {
        (result matches Err(error) && self.mixed_target_signature_failure(call, limit, error))
            || exists|actual: SignalType| {
                &&& self.mixed_call_returns_type(call, limit, result_index, actual)
                &&& #[trigger] mixed_output_transfer(actual, expected, target, expression, result)
            }
    }

    #[verifier::opaque]
    spec fn mixed_output_step(
        &self, file: usize, entry: usize, limit: u64, drivers: &FuncDrivers,
        calls: CheckedMixedCalls, outlets: Seq<Option<usize>>, i: int,
        result: Result<Option<SignalType>, MixedFuncTypeError>,
    ) -> bool {
        let project = self.targets_model().project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.indexes_model()[file as int]->Circuit_0;
        let driver = drivers.definitions@[i];
        let def = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let row = parsed.definitions@[driver.definition as int];
        if ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int) {
            let range = calls.definitions@[def as int];
            let call = calls.positions@[range.start as int].1;
            let expected = match outlets[i] {
                Some(port) => Some(drivers.signature.outputs@[port as int]), None => None,
            };
            &&& range.start < range.end && calls.positions@[range.start as int].0 == 0
            &&& call.call.form == row.expression.start
            &&& self.mixed_call_output_outcome(call, limit, driver.result_index, expected,
                LocatedName { source, span: driver.name.span }, LocatedName { source, span: call.call.span }, result)
        } else { result == Ok(None) }
    }

    proof fn record_mixed_output_transfer(
        &self, file: usize, entry: usize, limit: u64, drivers: &FuncDrivers, calls: CheckedMixedCalls,
        outlets: Seq<Option<usize>>, i: int, actual: SignalType, result: Result<Option<SignalType>, MixedFuncTypeError>,
    )
        requires
            result is Ok || result matches Err(MixedFuncTypeError::Output(_)),
            0 <= i < drivers.definitions@.len(),
            ({
                let project = self.targets_model().project_model();
                self.mixed_output_context(file, entry, &project.sources_model()[file as int],
                    &project.indexes_model()[file as int]->Circuit_0, drivers, calls)
            }),
            ({
                let project = self.targets_model().project_model();
                let source = &project.sources_model()[file as int];
                let parsed = &project.indexes_model()[file as int]->Circuit_0;
                let driver = drivers.definitions@[i];
                let def = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
                let row = parsed.definitions@[driver.definition as int];
                let range = calls.definitions@[def as int];
                let call = calls.positions@[range.start as int].1;
                let expected = match outlets[i] { Some(port) => Some(drivers.signature.outputs@[port as int]), None => None };
                &&& ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int)
                &&& range.start < range.end && calls.positions@[range.start as int].0 == 0
                &&& call.call.form == row.expression.start
                &&& self.mixed_call_returns_type(call, limit, driver.result_index, actual)
                &&& mixed_output_transfer(actual, expected, LocatedName { source, span: driver.name.span },
                    LocatedName { source, span: call.call.span }, result)
            }),
        ensures self.mixed_output_step(file, entry, limit, drivers, calls, outlets, i, result),
    {
        let project = self.targets_model().project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.indexes_model()[file as int]->Circuit_0;
        let driver = drivers.definitions@[i];
        let def = (driver.definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let row = parsed.definitions@[driver.definition as int];
        let range = calls.definitions@[def as int];
        let call = calls.positions@[range.start as int].1;
        let expected = match outlets[i] { Some(port) => Some(drivers.signature.outputs@[port as int]), None => None };
        let target = LocatedName { source, span: driver.name.span };
        let expression = LocatedName { source, span: call.call.span };
        reveal(MixedUseAliases::mixed_output_context);
        reveal(MixedUseAliases::mixed_output_step);
        reveal(MixedUseAliases::mixed_call_output_outcome);
        assert(ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int));
        assert(range.start < range.end);
        assert(calls.positions@[range.start as int].0 == 0);
        assert(call.call.form == row.expression.start);
        assert(exists|typed: SignalType| {
            &&& self.mixed_call_returns_type(call, limit, driver.result_index, typed)
            &&& #[trigger] mixed_output_transfer(typed, expected, target, expression, result)
        }) by {
            assert(mixed_output_transfer(actual, expected, target, expression, result));
        };
        assert(self.mixed_call_output_outcome(call, limit, driver.result_index, expected, target, expression, result));
    }

    #[verifier::opaque]
    spec fn mixed_output_prefix(&self, file: usize, entry: usize, limit: u64, drivers: &FuncDrivers,
        calls: CheckedMixedCalls, outlets: Seq<Option<usize>>, types: Seq<Option<SignalType>>) -> bool {
        &&& types.len() <= drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < types.len() ==> #[trigger]
            self.mixed_output_step(file, entry, limit, drivers, calls, outlets, i, Ok(types[i]))
    }

    proof fn mixed_output_failed(
        &self, file: usize, entry: usize, limit: u64, scope: FuncWiring, calls: CheckedMixedCalls,
        widths: Vec<Option<u64>>, map: Seq<Option<usize>>, before: Seq<Option<SignalType>>, error: MixedFuncTypeError,
    )
        requires
            self.mixed_func_arity_matches(file, entry, limit, Ok(FuncWiringResult::Checked(scope))),
            error is Signature || error is Output,
            ({
                let drivers = &scope.drivers;
                let project = self.targets_model().project_model();
                let source = &project.sources_model()[file as int];
                let parsed = &project.indexes_model()[file as int]->Circuit_0;
                &&& self.mixed_output_context(file, entry, source, parsed, drivers, calls)
                &&& literal_widths_match(source, parsed, drivers, limit, Ok(widths))
                &&& output_indices(drivers, drivers.outputs@.len() as int, map)
                &&& before.len() < drivers.definitions@.len()
                &&& self.mixed_output_prefix(file, entry, limit, drivers, calls, map, before)
                &&& self.mixed_output_step(file, entry, limit, drivers, calls, map, before.len() as int, Err(error))
            }),
        ensures self.mixed_func_output_types_match(file, entry, limit, Err(error)),
    {
        let drivers = &scope.drivers;
        let project = self.targets_model().project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.indexes_model()[file as int]->Circuit_0;
        assert(exists|value: Vec<Option<u64>>| #[trigger] literal_widths_match(source, parsed, drivers, limit, Ok(value))) by {
            assert(literal_widths_match(source, parsed, drivers, limit, Ok(widths)));
        };
    }

    /// 出力型が元の結線・呼び出し先・出力宣言に対応することを表す。
    pub closed spec fn mixed_func_output_types_match(&self, file: usize, entry: usize, limit: u64,
        result: Result<MixedFuncOutputTypes, MixedFuncTypeError>) -> bool {
        let project = self.targets_model().project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.indexes_model()[file as int]->Circuit_0;
        match result {
            Err(MixedFuncTypeError::Arity(error)) => self.mixed_func_arity_matches(file, entry, limit, Err(error)),
            Ok(typed) if !(typed.literals.wiring is Checked) =>
                self.mixed_func_arity_matches(file, entry, limit, Ok(typed.literals.wiring))
                    && typed.literals.widths@.len() == 0 && typed.types@.len() == 0,
            _ => exists|scope: FuncWiring, calls: CheckedMixedCalls| {
                &&& #[trigger] self.mixed_func_arity_matches(file, entry, limit, Ok(FuncWiringResult::Checked(scope)))
                &&& #[trigger] self.mixed_output_context(file, entry, source, parsed, &scope.drivers, calls)
                &&& match result {
                    Err(MixedFuncTypeError::Literal(error)) => literal_widths_match(source, parsed, &scope.drivers, limit, Err(error)),
                    Ok(typed) => typed.literals.wiring == FuncWiringResult::Checked(scope)
                        && literal_widths_match(source, parsed, &scope.drivers, limit, Ok(typed.literals.widths))
                        && typed.types@.len() == scope.drivers.definitions@.len()
                        && exists|map: Seq<Option<usize>>| #[trigger] output_indices(&scope.drivers, scope.drivers.outputs@.len() as int, map)
                            && self.mixed_output_prefix(file, entry, limit, &scope.drivers, calls, map, typed.types@),
                    Err(error) => (exists|widths: Vec<Option<u64>>| #[trigger] literal_widths_match(source, parsed, &scope.drivers, limit, Ok(widths)))
                        && exists|map: Seq<Option<usize>>, before: Seq<Option<SignalType>>|
                            before.len() < scope.drivers.definitions@.len()
                            && #[trigger] output_indices(&scope.drivers, scope.drivers.outputs@.len() as int, map)
                            && #[trigger] self.mixed_output_prefix(file, entry, limit, &scope.drivers, calls, map, before)
                            && self.mixed_output_step(file, entry, limit, &scope.drivers, calls, map, before.len() as int, Err(error)),
                }
            },
        }
    }

    /// 出力型の検査結果から、同じ結線と個数検査の保証を取り出す。
    pub proof fn mixed_output_types_preserve_arity(
        &self, file: usize, entry: usize, limit: u64, typed: MixedFuncOutputTypes,
    )
        requires self.mixed_func_output_types_match(file, entry, limit, Ok(typed)),
        ensures
            self.mixed_func_arity_matches(file, entry, limit, Ok(typed.literals.wiring)),
            typed.literals.wiring matches FuncWiringResult::Checked(scope)
                ==> typed.types@.len() == scope.drivers.definitions@.len(),
    {}
}

spec fn mixed_output_transfer(actual: SignalType, expected: Option<crate::project::TypedPort>,
    target: LocatedName, expression: LocatedName, result: Result<Option<SignalType>, MixedFuncTypeError>) -> bool {
    match result {
        Ok(typed) => output_transfer(actual, expected, target, expression, Ok(typed)),
        Err(MixedFuncTypeError::Output(error)) => output_transfer(actual, expected, target, expression, Err(error)),
        _ => false,
    }
}

}
