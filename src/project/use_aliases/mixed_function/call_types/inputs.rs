//! 混在プロジェクトで型が分かる信号を伝播し、通常呼び出しの実引数を検査する。

use super::*;
use crate::project::{FuncWiring, ResolvedPortType};
#[cfg(verus_only)]
use crate::project::OutputDriver;
use crate::project::circuits::form_location;
use crate::project::use_aliases::function_atoms::{copy_signal_type, inherit_type};
use crate::project::use_aliases::call_arity::{check_leaf, report_call_argument};
#[cfg(verus_only)]
use crate::project::use_aliases::{call_arity::{leaf_result, reported_argument}, function_atoms::signal_type_at};
#[cfg(verus_only)]
use crate::syntax::circuit::{BuildDefinition, build_bare_signal_position, call_argument_sequence, direct_call_argument,
    expression_region, first_call_argument_evidence, following_call_argument};
use crate::syntax::circuit::{call_argument_range, indexed_call_signal, next_call_argument};
use crate::syntax::{AtomKind, Form};

verus! {

/// 混在プロジェクトで、型を確認できた信号と実引数の検査結果。
#[derive(Debug)]
pub struct MixedFuncInputTypes<'p, 'a> {
    /// 結線、定数幅、および通常呼び出しの出力型。
    pub outputs: MixedFuncOutputTypes<'p, 'a>,
    /// 定義の左辺順に並ぶ型。型を確定できなかった式には `None` を置く。
    pub signals: Vec<Option<SignalType<'p, 'a>>>,
    /// 実引数のうち、型が確定していない最初の式の元の位置。
    pub deferred_argument: Option<LocatedName<'p, 'a>>,
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// 結線、出力型、裸の信号の型伝播を済ませ、定数と型が分かる実引数を照合する。
    ///
    /// 実引数の型を確定できない場合は、その先頭の位置を `deferred_argument` に返す。
    /// 定数、裸の信号、定義を直接駆動する呼び出しの出力型から信号の型を求める。
    /// 入れ子の呼び出しの戻り値や他の複合式は未確定として保持する。実引数がすべて確定していても、
    /// 型が未確定の左辺には `signals` に `None` が残る。
    /// 対象外と展開待ちは結線検査から引き継ぐ。
    ///
    /// # Errors
    ///
    /// 定数幅と出力型を先に検査する。その後、定義の左辺と実引数をそれぞれ元の出現順で調べる。
    /// 不一致には実引数の位置と、参照先の入力ポートが指定した型の位置が付く。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{CallInputError, CallInputReason, MixedFuncTypeError, ResolvedPortType,
    ///     SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources};
    ///
    /// let design = "(func wrong (in (x (bits 4))) (out (y (bits 8))) (def t x) (def y (::lib::byte t)))";
    /// let library = "(namespace lib (export byte) (func byte (in (x (bits 8))) (out (x (bits 8)))))";
    /// let project = parse_project_sources(&[
    ///     SourceSnapshot { path: "design.ncg2", revision: 8, text: design },
    ///     SourceSnapshot { path: "library.ncg2", revision: 3, text: library },
    ///     SourceSnapshot { path: "helper.ncg2m", revision: 2, text: "" },
    /// ]).unwrap();
    /// let targets = index_mixed_use_targets(&project).unwrap();
    /// let aliases = check_mixed_use_aliases(&targets).unwrap();
    /// let Err(MixedFuncTypeError::Input(CallInputError::Argument {
    ///     argument, required_at: Some(required), expected: ResolvedPortType::Bits(8),
    ///     reason: CallInputReason::SignalType(actual), ..
    /// })) = aliases.check_mixed_func_input_types(0, 0, 64) else { panic!() };
    /// assert_eq!((&design[argument.span], argument.source.revision), ("t", 8));
    /// assert_eq!((&library[required.span], required.source.revision), ("8", 3));
    /// assert!(matches!(actual.ty, ResolvedPortType::Bits(4)));
    /// ```
    pub fn check_mixed_func_input_types(&self, file: usize, entry: usize, limit: u64)
        -> (result: Result<MixedFuncInputTypes<'p, 'a>, MixedFuncTypeError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures self.mixed_func_input_types_match(file, entry, limit, result),
    {
        let prepared = match self.prepare_mixed_output_analysis(file, entry, limit) {
            Ok(prepared) => prepared,
            Err(error) => {
                proof { reveal(MixedUseAliases::mixed_func_input_types_match); }
                return Err(error);
            }
        };
        let PreparedMixedOutputs { typed: outputs, calls, mut signatures } = prepared;
        let FuncWiringResult::Checked(ref scope) = outputs.literals.wiring else {
            proof { reveal(MixedUseAliases::mixed_func_input_types_match); }
            return Ok(MixedFuncInputTypes { outputs, signals: Vec::new(), deferred_argument: None });
        };
        proof {
            self.mixed_output_types_preserve_arity(file, entry, limit, outputs);
            self.mixed_arity_preserves_wiring(file, entry, limit, outputs.literals.wiring);
            self.mixed_wiring_index_origin(file, entry, limit, *scope);
        }
        let project = self.targets().project();
        let source = &project.sources()[file];
        let index = &project.indexes()[file];
        let ProjectSourceIndex::Circuit(parsed) = index else { unreachable!() };
        proof { reveal(MixedUseAliases::mixed_output_context); }
        let signals = match self.propagate_mixed_signals(file, entry, limit, source, parsed, scope,
            outputs.literals.widths.as_slice(), outputs.types.as_slice()) {
            Ok(signals) => signals,
            Err(error) => {
                proof { self.record_mixed_inputs(file, entry, limit, outputs, calls, Err(error), Err(error)); }
                return Err(error);
            }
        };
        let pending = match self.check_retained_mixed_inputs((file, entry), source, parsed, scope, signals.as_slice(),
            &calls, limit, &mut signatures) {
            Ok(pending) => pending,
            Err(error) => {
                proof { self.record_mixed_inputs(file, entry, limit, outputs, calls, Ok(signals), Err(error)); }
                return Err(error);
            }
        };
        let typed = MixedFuncInputTypes { outputs, signals, deferred_argument: pending };
        proof { self.record_mixed_inputs(file, entry, limit, typed.outputs, calls, Ok(typed.signals), Ok(typed)); }
        Ok(typed)
    }

    /// ?????????????????????????????????????????
    #[verifier::opaque]
    pub closed spec fn mixed_func_input_types_match(&self, file: usize, entry: usize, limit: u64,
        result: Result<MixedFuncInputTypes, MixedFuncTypeError>) -> bool {
        match result {
            Ok(typed) if !(typed.outputs.literals.wiring is Checked) =>
                self.mixed_func_output_types_match(file, entry, limit, Ok(typed.outputs))
                    && typed.signals@.len() == 0 && typed.deferred_argument.is_none(),
            _ => (result matches Err(error) && self.mixed_func_output_types_match(file, entry, limit, Err(error)))
                || exists|outputs: MixedFuncOutputTypes, calls: CheckedMixedCalls|
                    #[trigger] self.mixed_prepared_input_result(file, entry, limit, outputs, calls, result),
        }
    }

    #[verifier::opaque]
    spec fn mixed_prepared_input_result(&self, file: usize, entry: usize, limit: u64, outputs: MixedFuncOutputTypes,
        calls: CheckedMixedCalls, result: Result<MixedFuncInputTypes, MixedFuncTypeError>) -> bool {
        let project = self.targets_model().project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.indexes_model()[file as int]->Circuit_0;
        &&& self.mixed_func_output_types_match(file, entry, limit, Ok(outputs))
        &&& outputs.literals.wiring matches FuncWiringResult::Checked(scope)
        &&& self.mixed_output_context(file, entry, source, parsed, &scope.drivers, calls)
        &&& match result {
            Ok(typed) => typed.outputs == outputs
                && self.mixed_propagation_result(source, parsed, entry, &scope, outputs.literals.widths@,
                    outputs.types@, Ok(typed.signals))
                && self.retained_mixed_inputs_match(source, parsed, entry, &scope, typed.signals@, calls, limit,
                    Ok(typed.deferred_argument)),
            Err(error) => self.mixed_propagation_result(source, parsed, entry, &scope, outputs.literals.widths@,
                outputs.types@, Err(error))
                || exists|types: Vec<Option<SignalType>>|
                    #[trigger] self.mixed_propagation_result(source, parsed, entry, &scope, outputs.literals.widths@,
                        outputs.types@, Ok(types))
                    && self.retained_mixed_inputs_match(source, parsed, entry, &scope, types@, calls, limit, Err(error)),
        }
    }

    #[verifier::spinoff_prover]
    proof fn record_mixed_inputs(&self, file: usize, entry: usize, limit: u64, outputs: MixedFuncOutputTypes,
        calls: CheckedMixedCalls, propagation: Result<Vec<Option<SignalType>>, MixedFuncTypeError>,
        result: Result<MixedFuncInputTypes, MixedFuncTypeError>)
        requires ({
            let project = self.targets_model().project_model();
            let source = &project.sources_model()[file as int];
            let parsed = &project.indexes_model()[file as int]->Circuit_0;
            &&& self.mixed_func_output_types_match(file, entry, limit, Ok(outputs))
            &&& outputs.literals.wiring matches FuncWiringResult::Checked(scope)
            &&& self.mixed_output_context(file, entry, source, parsed, &scope.drivers, calls)
            &&& self.mixed_propagation_result(source, parsed, entry, &scope, outputs.literals.widths@,
                outputs.types@, propagation)
            &&& match propagation {
                Err(error) => result == Err(error),
                Ok(signals) => match result {
                    Ok(typed) => typed.outputs == outputs && typed.signals == signals
                        && self.retained_mixed_inputs_match(source, parsed, entry, &scope, signals@, calls, limit,
                            Ok(typed.deferred_argument)),
                    Err(error) => self.retained_mixed_inputs_match(source, parsed, entry, &scope, signals@, calls, limit,
                        Err(error)),
                },
            }
        }),
        ensures self.mixed_func_input_types_match(file, entry, limit, result),
    {
        reveal(MixedUseAliases::mixed_prepared_input_result);
        reveal(MixedUseAliases::mixed_func_input_types_match);
        assert(self.mixed_prepared_input_result(file, entry, limit, outputs, calls, result));
    }

    #[verifier::opaque]
    spec fn retained_mixed_inputs_before(&self, source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize,
        scope: &FuncWiring, types: Seq<Option<SignalType>>, calls: CheckedMixedCalls, limit: u64, outcomes: Seq<Option<LocatedName>>) -> bool {
        forall|d: int, i: int| 0 <= d < calls.definitions@.len()
            && (#[trigger] calls.definitions@[d]).start <= i < calls.definitions@[d].end
            && i < outcomes.len() ==> self.mixed_call_inputs_match(source, parsed,
                crate::project::use_aliases::call_arity::checks::at_definition(parsed, entry as int, d), entry, scope,
                types, calls.positions@[i].1, limit, Ok(#[trigger] outcomes[i]))
    }

    #[verifier::opaque]
    spec fn retained_mixed_inputs_match(&self, source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize,
        scope: &FuncWiring, types: Seq<Option<SignalType>>, calls: CheckedMixedCalls, limit: u64,
        result: Result<Option<LocatedName>, MixedFuncTypeError>) -> bool {
        match result {
            Ok(pending) => exists|outcomes: Seq<Option<LocatedName>>|
                outcomes.len() == calls.positions@.len()
                && #[trigger] self.retained_mixed_inputs_before(source, parsed, entry, scope, types, calls, limit, outcomes)
                && first_pending_call(outcomes, pending),
            Err(error) => exists|outcomes: Seq<Option<LocatedName>>, definition: int|
                0 <= definition < calls.definitions@.len()
                && (#[trigger] calls.definitions@[definition]).start <= outcomes.len() < calls.definitions@[definition].end
                && #[trigger] self.retained_mixed_inputs_before(source, parsed, entry, scope, types, calls, limit, outcomes)
                && self.mixed_call_inputs_match(source, parsed,
                    crate::project::use_aliases::call_arity::checks::at_definition(parsed, entry as int, definition), entry,
                    scope, types, calls.positions@[outcomes.len() as int].1, limit, Err(error)),
        }
    }

    proof fn retained_input_at(&self, file: usize, entry: usize, source: &ProjectSource, parsed: &NamedBuildCircuit,
        scope: &FuncWiring, calls: CheckedMixedCalls, definition: usize, position: usize)
        requires
            self.mixed_output_context(file, entry, source, parsed, &scope.drivers, calls),
            definition < calls.definitions@.len(),
            calls.definitions@[definition as int].start <= position < calls.definitions@[definition as int].end,
        ensures
            position < calls.positions@.len(),
            self.mixed_checked_call(DefinitionPosition { file, entry, definition, reference: calls.positions@[position as int].0 },
                calls.positions@[position as int].1),
            *source == self.targets_model().project_model().sources_model()[file as int],
            *parsed == self.targets_model().project_model().indexes_model()[file as int]->Circuit_0,
            crate::project::parsed_circuit_matches(*source, *parsed),
    {
        reveal(MixedUseAliases::mixed_output_context);
        let range = calls.definitions@[definition as int];
        let rows = calls.positions@[range.start as int..range.end as int];
        let selected = (position - range.start) as int;
        assert(0 <= selected < rows.len());
        assert(rows[selected] == calls.positions@[position as int]);
        assert(self.mixed_checked_call(DefinitionPosition { file, entry, definition, reference: rows[selected].0 },
            rows[selected].1));
    }

    #[verifier::spinoff_prover]
    proof fn extend_retained_mixed_inputs(&self, file: usize, entry: usize, source: &ProjectSource, parsed: &NamedBuildCircuit,
        scope: &FuncWiring, types: Seq<Option<SignalType>>, calls: CheckedMixedCalls, limit: u64,
        outcomes: Seq<Option<LocatedName>>, definition: usize, found: Option<LocatedName>)
        requires
            self.mixed_output_context(file, entry, source, parsed, &scope.drivers, calls),
            definition < calls.definitions@.len(),
            calls.definitions@[definition as int].start <= outcomes.len() < calls.definitions@[definition as int].end,
            self.retained_mixed_inputs_before(source, parsed, entry, scope, types, calls, limit, outcomes),
            self.mixed_call_inputs_match(source, parsed, crate::project::use_aliases::call_arity::checks::at_definition(
                parsed, entry as int, definition as int), entry, scope, types, calls.positions@[outcomes.len() as int].1, limit, Ok(found)),
        ensures self.retained_mixed_inputs_before(source, parsed, entry, scope, types, calls, limit, outcomes.push(found)),
    {
        reveal(MixedUseAliases::retained_mixed_inputs_before);
        reveal(MixedUseAliases::mixed_output_context);
        let next = outcomes.push(found);
        assert forall|d: int, i: int| 0 <= d < calls.definitions@.len()
            && (#[trigger] calls.definitions@[d]).start <= i < calls.definitions@[d].end && i < next.len()
            implies self.mixed_call_inputs_match(source, parsed,
                crate::project::use_aliases::call_arity::checks::at_definition(parsed, entry as int, d), entry, scope,
                types, calls.positions@[i].1, limit, Ok(#[trigger] next[i])) by {
            if i < outcomes.len() {
                assert(next[i] == outcomes[i]);
            } else {
                if d < definition { Self::retained_def_ranges_ordered(calls.definitions@, d, definition as int); }
                if definition < d { Self::retained_def_ranges_ordered(calls.definitions@, definition as int, d); }
                assert(d == definition);
            }
        };
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(48)]
    fn check_retained_mixed_inputs(&self, owner: (usize, usize), source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>,
        scope: &FuncWiring<'p, 'a>, types: &[Option<SignalType<'p, 'a>>], calls: &CheckedMixedCalls<'p, 'a>,
        limit: u64, signatures: &mut SignatureCache<'p, 'a>,
    ) -> (result: Result<Option<LocatedName<'p, 'a>>, MixedFuncTypeError<'p, 'a>>)
        requires
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
            self.mixed_output_context(owner.0, owner.1, source, parsed, &scope.drivers, *calls),
            self.mixed_func_wiring_matches(owner.0, owner.1, limit, Ok(FuncWiringResult::Checked(*scope))),
            types@.len() == scope.drivers.definitions@.len(), old(signatures).matches_mixed(self, limit),
        ensures
            final(signatures).matches_mixed(self, limit),
            self.retained_mixed_inputs_match(source, parsed, owner.1, scope, types@, *calls, limit, result),
    {
        let (file, entry) = owner;
        let mut definition = 0;
        let mut position = 0;
        let mut pending = None;
        let ghost outcomes: Seq<Option<LocatedName>> = Seq::empty();
        proof { reveal(MixedUseAliases::retained_mixed_inputs_before); }
        while definition < calls.definitions.len()
            invariant
                mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()), owner == (file, entry),
                self.mixed_output_context(file, entry, source, parsed, &scope.drivers, *calls),
                self.mixed_func_wiring_matches(file, entry, limit, Ok(FuncWiringResult::Checked(*scope))),
                types@.len() == scope.drivers.definitions@.len(), signatures.matches_mixed(self, limit),
                definition <= calls.definitions@.len(), position <= calls.positions@.len(), outcomes.len() == position,
                position == if definition == 0 { 0 } else { calls.definitions@[definition - 1].end },
                self.retained_mixed_inputs_before(source, parsed, entry, scope, types@, *calls, limit, outcomes),
                first_pending_call(outcomes, pending),
            decreases calls.definitions@.len() - definition,
        {
            let range = &calls.definitions[definition];
            proof {
                reveal(MixedUseAliases::mixed_output_context);
                assert(range.start == position);
                assert(range.start <= range.end <= calls.positions@.len());
            }
            while position < range.end
                invariant
                    mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()), owner == (file, entry),
                    self.mixed_output_context(file, entry, source, parsed, &scope.drivers, *calls),
                    self.mixed_func_wiring_matches(file, entry, limit, Ok(FuncWiringResult::Checked(*scope))),
                    types@.len() == scope.drivers.definitions@.len(), signatures.matches_mixed(self, limit),
                    definition < calls.definitions@.len(), *range == calls.definitions@[definition as int],
                    range.start <= position <= range.end <= calls.positions@.len(), outcomes.len() == position,
                    self.retained_mixed_inputs_before(source, parsed, entry, scope, types@, *calls, limit, outcomes),
                    first_pending_call(outcomes, pending),
                decreases range.end - position,
            {
                proof { self.retained_input_at(file, entry, source, parsed, scope, *calls, definition, position); }
                let observed = self.check_mixed_call_arguments((file, entry, definition), source, parsed, scope,
                    types, &calls.positions[position], limit, signatures);
                let observed = match observed {
                    Ok(observed) => observed,
                    Err(error) => {
                        proof {
                            reveal(MixedUseAliases::retained_mixed_inputs_match);
                            assert(exists|before: Seq<Option<LocatedName>>, d: int|
                                0 <= d < calls.definitions@.len()
                                && (#[trigger] calls.definitions@[d]).start <= before.len() < calls.definitions@[d].end
                                && #[trigger] self.retained_mixed_inputs_before(source, parsed, entry, scope, types@, *calls, limit, before)
                                && self.mixed_call_inputs_match(source, parsed,
                                    crate::project::use_aliases::call_arity::checks::at_definition(parsed, entry as int, d), entry,
                                    scope, types@, calls.positions@[before.len() as int].1, limit, Err(error)));
                        }
                        return Err(error);
                    }
                };
                let ghost found = observed;
                let ghost previous = pending;
                if pending.is_none() { pending = observed; }
                proof {
                    extend_first_pending_call(outcomes, found, previous, pending);
                    self.extend_retained_mixed_inputs(file, entry, source, parsed, scope, types@, *calls, limit,
                        outcomes, definition, found);
                    outcomes = outcomes.push(found);
                }
                position += 1;
            }
            definition += 1;
        }
        proof {
            reveal(MixedUseAliases::mixed_output_context);
            reveal(MixedUseAliases::retained_mixed_inputs_match);
        }
        Ok(pending)
    }

    #[verifier::opaque]
    spec fn mixed_propagation_result(
        &self, source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, scope: &FuncWiring,
        widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, result: Result<Vec<Option<SignalType>>, MixedFuncTypeError>,
    ) -> bool {
        let drivers = &scope.drivers;
        exists|map: Seq<Option<usize>>| #[trigger] output_indices(drivers, drivers.outputs@.len() as int, map)
            && match result {
                Ok(types) => types@.len() == drivers.definitions@.len()
                    && self.mixed_propagation_prefix(source, parsed, entry, scope, widths, roots, map, types@),
                Err(error) => exists|before: Seq<Option<SignalType>>|
                    before.len() < drivers.definitions@.len()
                    && #[trigger] self.mixed_propagation_prefix(source, parsed, entry, scope, widths, roots, map, before)
                    && self.mixed_propagation_step(source, parsed, entry, scope, widths, roots, map, before, before.len() as int, Err(error)),
            }
    }

    #[verifier::spinoff_prover]
    fn propagate_mixed_signals(
        &self, _file: usize, entry: usize, _limit: u64,
        source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>, scope: &FuncWiring<'p, 'a>,
        widths: &[Option<u64>], roots: &[Option<SignalType<'p, 'a>>],
    ) -> (result: Result<Vec<Option<SignalType<'p, 'a>>>, MixedFuncTypeError<'p, 'a>>)
        requires
            ({
                let project = self.targets_model().project_model();
                &&& self.mixed_func_wiring_matches(_file, entry, _limit, Ok(FuncWiringResult::Checked(*scope)))
                &&& *source == project.sources_model()[_file as int]
                &&& *parsed == project.indexes_model()[_file as int]->Circuit_0
            }),
            crate::project::parsed_circuit_matches(*source, *parsed), entry < parsed.syntax.entries@.len(),
            expected_output_context(source, parsed, entry as int, scope.drivers),
            widths@.len() == roots@.len() == scope.drivers.definitions@.len(),
        ensures
            self.mixed_propagation_result(source, parsed, entry, scope, widths@, roots@, result),
            result matches Ok(types) ==> types@.len() == scope.drivers.definitions@.len(),
    {
        let outlets = index_outputs(&scope.drivers);
        let mut types = Vec::new();
        let mut index = 0;
        proof {
            reveal(MixedUseAliases::mixed_propagation_prefix);
            reveal(MixedUseAliases::mixed_propagation_result);
        }
        while index < scope.drivers.definitions.len()
            invariant
                ({
                    let project = self.targets_model().project_model();
                    &&& self.mixed_func_wiring_matches(_file, entry, _limit, Ok(FuncWiringResult::Checked(*scope)))
                    &&& *source == project.sources_model()[_file as int]
                    &&& *parsed == project.indexes_model()[_file as int]->Circuit_0
                }),
                crate::project::parsed_circuit_matches(*source, *parsed), entry < parsed.syntax.entries@.len(),
                expected_output_context(source, parsed, entry as int, scope.drivers),
                output_indices(&scope.drivers, scope.drivers.outputs@.len() as int, outlets@),
                widths@.len() == roots@.len() == scope.drivers.definitions@.len(),
                index == types@.len() <= scope.drivers.definitions@.len(),
                self.mixed_propagation_prefix(source, parsed, entry, scope, widths@, roots@, outlets@, types@),
            decreases scope.drivers.definitions@.len() - index,
        {
            let next = self.propagate_mixed_signal(Ghost((_file, entry, _limit)), entry, source, parsed, scope,
                widths, roots, outlets.as_slice(), types.as_slice(), index);
            let next = match next {
                Ok(next) => next,
                Err(error) => {
                    proof {
                        reveal(MixedUseAliases::mixed_propagation_result);
                        let map = outlets@;
                        assert(exists|before: Seq<Option<SignalType>>| before.len() < scope.drivers.definitions@.len()
                            && #[trigger] self.mixed_propagation_prefix(source, parsed, entry, scope, widths@, roots@, map, before)
                            && self.mixed_propagation_step(source, parsed, entry, scope, widths@, roots@, map, before,
                                before.len() as int, Err(error)));
                    }
                    return Err(error);
                }
            };
            let ghost before = types@;
            types.push(next);
            proof {
                reveal(MixedUseAliases::mixed_propagation_prefix);
                assert forall|i: int| 0 <= i < types@.len() implies #[trigger] self.mixed_propagation_step(
                    source, parsed, entry, scope, widths@, roots@, outlets@, types@.take(i), i, Ok(types@[i])) by {
                    if i < before.len() {
                        assert(types@[i] == before[i]);
                        assert(types@.take(i) =~= before.take(i));
                    } else { assert(types@.take(i) =~= before); }
                };
            }
            index += 1;
        }
        Ok(types)
    }

    spec fn mixed_propagation_step(
        &self, source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, scope: &FuncWiring,
        widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, outlets: Seq<Option<usize>>,
        prior: Seq<Option<SignalType>>, index: int, result: Result<Option<SignalType>, MixedFuncTypeError>,
    ) -> bool {
        let drivers = &scope.drivers;
        let driver = drivers.definitions@[index];
        let row = parsed.definitions@[driver.definition as int];
        let root = parsed.syntax.forms@[row.expression.start as int];
        if let Some(width) = widths[index] {
            result matches Ok(Some(typed)) && typed.ty == ResolvedPortType::Bits(width)
                && crate::project::circuits::is_form_location(source, root, typed.origin)
        } else if driver.result_index == 0 && root is Atom && root->Atom_kind is Name {
            let first = parsed.entry_ranges@[entry as int].signals.start;
            let bound = scope.signals@[row.signals.start - first];
            let actual = signal_type_at(scope, prior, bound.driver);
            match (actual, outlets[index]) {
                (Some(actual), Some(port)) => {
                    let expected = drivers.signature.outputs@[port as int];
                    if crate::project::port_types_equal(actual.ty, expected.ty) { result == Ok(Some(actual)) }
                    else { result == Err(MixedFuncTypeError::Signal(FuncAtomTypeError::OutputType {
                        reference: bound.site, expected: SignalType { ty: expected.ty, origin: expected.annotation }, actual,
                    })) }
                },
                _ => result == Ok(actual),
            }
        } else { result == Ok(roots[index]) }
    }

    #[verifier::opaque]
    spec fn mixed_propagation_prefix(
        &self, source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, scope: &FuncWiring,
        widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, outlets: Seq<Option<usize>>, types: Seq<Option<SignalType>>,
    ) -> bool {
        &&& types.len() <= scope.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < types.len() ==> #[trigger] self.mixed_propagation_step(source, parsed, entry,
            scope, widths, roots, outlets, types.take(i), i, Ok(types[i]))
    }

    fn propagate_mixed_signal(
        &self, _caller: Ghost<(usize, usize, u64)>, entry: usize, source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>,
        scope: &FuncWiring<'p, 'a>, widths: &[Option<u64>], roots: &[Option<SignalType<'p, 'a>>],
        outlets: &[Option<usize>], prior: &[Option<SignalType<'p, 'a>>], index: usize,
    ) -> (result: Result<Option<SignalType<'p, 'a>>, MixedFuncTypeError<'p, 'a>>)
        requires
            ({
                let (file, item, limit) = _caller@;
                let project = self.targets_model().project_model();
                &&& entry == item
                &&& self.mixed_func_wiring_matches(file, entry, limit, Ok(FuncWiringResult::Checked(*scope)))
                &&& *source == project.sources_model()[file as int]
                &&& *parsed == project.indexes_model()[file as int]->Circuit_0
            }),
            crate::project::parsed_circuit_matches(*source, *parsed), entry < parsed.syntax.entries@.len(),
            expected_output_context(source, parsed, entry as int, scope.drivers),
            output_indices(&scope.drivers, scope.drivers.outputs@.len() as int, outlets@),
            widths@.len() == roots@.len() == scope.drivers.definitions@.len(),
            index == prior@.len() < scope.drivers.definitions@.len(),
        ensures self.mixed_propagation_step(source, parsed, entry, scope, widths@, roots@, outlets@, prior@, index as int, result),
    {
        let driver = &scope.drivers.definitions[index];
        let row = &parsed.definitions[driver.definition];
        let root = row.expression.start;
        let forms = parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, driver.definition as int);
            reveal(output_indices);
        }
        if let Some(width) = widths[index] {
            return Ok(Some(SignalType { ty: ResolvedPortType::Bits(width), origin: form_location(source, forms, root) }));
        }
        if driver.result_index == 0 && matches!(forms[root], Form::Atom { kind: AtomKind::Name, .. }) {
            proof {
                let (file, _, limit) = _caller@;
                build_bare_signal_position(source.text, &parsed.build_model(), entry as int, driver.definition as int);
                self.mixed_wiring_signal_driver(file, entry, limit, *scope, driver.definition, row.signals.start);
            }
            let position = row.signals.start - parsed.entry_ranges[entry].signals.start;
            let bound = &scope.signals[position];
            proof {
                if let OutputDriver::Definition(previous) = bound.driver {
                    assert(previous < index) by {
                        if index < previous {
                            assert(scope.drivers.definitions@[index as int].definition
                                <= scope.drivers.definitions@[previous as int].definition);
                        }
                    };
                }
            }
            let actual = inherit_type(scope, prior, bound.driver);
            if let (Some(typed), Some(outlet)) = (&actual, outlets[index]) {
                let port = &scope.drivers.signature.outputs[outlet];
                if !typed.ty.is_same_type(&port.ty) {
                    return Err(MixedFuncTypeError::Signal(FuncAtomTypeError::OutputType {
                        reference: copy_location(&bound.site),
                        expected: SignalType { ty: port.ty, origin: copy_location(&port.annotation) },
                        actual: SignalType { ty: typed.ty, origin: copy_location(&typed.origin) },
                    }));
                }
            }
            return Ok(actual);
        }
        Ok(copy_signal_type(&roots[index]))
    }

    spec fn mixed_known_argument(
        &self, parsed: &NamedBuildCircuit, row: BuildDefinition, entry: usize, scope: &FuncWiring,
        types: Seq<Option<SignalType>>, argument: usize, known: Option<SignalType>,
    ) -> bool {
        let forms = parsed.syntax.forms@;
        if forms[argument as int] is Atom && forms[argument as int]->Atom_kind is Name {
            let start = parsed.entry_ranges@[entry as int].signals.start;
            exists|p: int| row.signals.start <= p < row.signals.end && #[trigger] parsed.signals@[p] == argument
                && start <= p < start + scope.signals@.len()
                && known == signal_type_at(scope, types, scope.signals@[p - start].driver)
        } else { known.is_none() }
    }

    spec fn mixed_argument_at(
        &self, source: &ProjectSource, parsed: &NamedBuildCircuit, row: BuildDefinition, entry: usize, scope: &FuncWiring,
        types: Seq<Option<SignalType>>, call: FuncCallArity, limit: u64, argument: usize, ordinal: usize,
        result: Result<Option<SignalType>, MixedFuncTypeError>,
    ) -> bool {
        let form = parsed.syntax.forms@[argument as int];
        &&& direct_call_argument(parsed.syntax.forms@, call.call, argument as int)
        &&& exists|port: crate::project::CallPortType, known: Option<SignalType>, leaf: Result<Option<SignalType>, crate::project::CallInputReason>| {
            &&& self.mixed_input_port(call, limit, ordinal, port)
            &&& self.mixed_known_argument(parsed, row, entry, scope, types, argument, known)
            &&& #[trigger] leaf_result(source, form, &port, known, limit, leaf)
            &&& match result {
                Ok(ty) => reported_argument(source, form, ordinal, port, leaf, Ok(ty)),
                Err(MixedFuncTypeError::Input(error)) => reported_argument(source, form, ordinal, port, leaf, Err(error)),
                _ => false,
            }
        }
    }

    spec fn mixed_input_port(&self, call: FuncCallArity, limit: u64, ordinal: usize, port: crate::project::CallPortType) -> bool {
        match call.target {
            FuncCallTarget::Nor => ordinal < 2 && port.ty == ResolvedPortType::Bits(1) && port.annotation.is_none(),
            FuncCallTarget::Function { file, entry, .. } => exists|typed: TypedRoutineSignature|
                #[trigger] self.mixed_typed_signature_matches(file, entry, limit, Ok(Some(typed)))
                    && ordinal < typed.inputs@.len() && port.ty == typed.inputs@[ordinal as int].ty
                    && (port.annotation matches Some(origin) && *origin == typed.inputs@[ordinal as int].annotation),
        }
    }

    #[verifier::opaque]
    spec fn mixed_call_argument_prefix(
        &self, source: &ProjectSource, parsed: &NamedBuildCircuit, row: BuildDefinition, entry: usize, scope: &FuncWiring,
        types: Seq<Option<SignalType>>, call: FuncCallArity, limit: u64, arguments: Seq<usize>, values: Seq<Option<SignalType>>,
        next: usize,
    ) -> bool {
        let forms = parsed.syntax.forms@;
        &&& arguments.len() == values.len()
        &&& next == if arguments.len() == 0 { call.call.form + 2 } else { after_argument(forms, arguments.last()) }
        &&& forall|i: int| 0 <= i < arguments.len() ==> {
            let root = #[trigger] arguments[i];
            &&& root == if i == 0 { call.call.form + 2 } else { after_argument(forms, arguments[i - 1]) }
            &&& self.mixed_argument_at(source, parsed, row, entry, scope, types, call, limit, root, i as usize, Ok(values[i]))
        }
    }

    proof fn extend_mixed_argument_prefix(
        &self, source: &ProjectSource, parsed: &NamedBuildCircuit, row: BuildDefinition, entry: usize, scope: &FuncWiring,
        types: Seq<Option<SignalType>>, call: FuncCallArity, limit: u64, args: Seq<usize>, values: Seq<Option<SignalType>>,
        root: usize, next: usize, value: Option<SignalType>,
    )
        requires
            args.len() <= usize::MAX,
            self.mixed_call_argument_prefix(source, parsed, row, entry, scope, types, call, limit, args, values, root),
            self.mixed_argument_at(source, parsed, row, entry, scope, types, call, limit, root, args.len() as usize, Ok(value)),
            next == after_argument(parsed.syntax.forms@, root),
        ensures self.mixed_call_argument_prefix(source, parsed, row, entry, scope, types, call, limit,
            args.push(root), values.push(value), next),
    {
        reveal(MixedUseAliases::mixed_call_argument_prefix);
        let forms = parsed.syntax.forms@;
        let extended = args.push(root);
        let inferred = values.push(value);
        assert forall|i: int| 0 <= i < extended.len() implies {
            let argument = #[trigger] extended[i];
            &&& argument == if i == 0 { call.call.form + 2 } else { after_argument(forms, extended[i - 1]) }
            &&& self.mixed_argument_at(source, parsed, row, entry, scope, types, call, limit, argument, i as usize, Ok(inferred[i]))
        } by {
            if i < args.len() { assert(extended[i] == args[i] && inferred[i] == values[i]); }
        };
    }

    spec fn mixed_call_inputs_match(
        &self, source: &ProjectSource, parsed: &NamedBuildCircuit, row: BuildDefinition, entry: usize, scope: &FuncWiring,
        types: Seq<Option<SignalType>>, call: FuncCallArity, limit: u64, result: Result<Option<LocatedName>, MixedFuncTypeError>,
    ) -> bool {
        let end = parsed.syntax.forms@[call.call.form as int]->List_end;
        match result {
            Ok(pending) => exists|args: Seq<usize>, values: Seq<Option<SignalType>>| {
                &&& #[trigger] self.mixed_call_argument_prefix(source, parsed, row, entry, scope, types, call, limit, args, values, end)
                &&& args.len() == call.call.arguments
                &&& first_mixed_deferred(source, parsed.syntax.forms@, args, values, pending)
            },
            Err(error) => self.mixed_target_signature_failure(call, limit, error)
                || exists|args: Seq<usize>, values: Seq<Option<SignalType>>, position: usize| {
                    &&& #[trigger] self.mixed_call_argument_prefix(source, parsed, row, entry, scope, types, call, limit, args, values, position)
                    &&& args.len() < call.call.arguments
                    &&& self.mixed_argument_at(source, parsed, row, entry, scope, types, call, limit, position, args.len() as usize, Err(error))
                },
        }
    }

    proof fn record_mixed_argument_failure(&self, source: &ProjectSource, parsed: &NamedBuildCircuit,
        row: BuildDefinition, entry: usize, scope: &FuncWiring, types: Seq<Option<SignalType>>, call: FuncCallArity,
        limit: u64, args: Seq<usize>, values: Seq<Option<SignalType>>, root: usize, error: MixedFuncTypeError)
        requires
            self.mixed_call_argument_prefix(source, parsed, row, entry, scope, types, call, limit, args, values, root),
            args.len() < call.call.arguments,
            self.mixed_argument_at(source, parsed, row, entry, scope, types, call, limit, root, args.len() as usize, Err(error)),
        ensures self.mixed_call_inputs_match(source, parsed, row, entry, scope, types, call, limit, Err(error)),
    {}

    #[verifier::spinoff_prover]
    #[verifier::rlimit(48)]
    fn check_mixed_call_arguments(
        &self, caller: (usize, usize, usize), source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>,
        scope: &FuncWiring<'p, 'a>, types: &[Option<SignalType<'p, 'a>>], record: &(usize, FuncCallArity<'p, 'a>),
        limit: u64, signatures: &mut SignatureCache<'p, 'a>,
    ) -> (result: Result<Option<LocatedName<'p, 'a>>, MixedFuncTypeError<'p, 'a>>)
        requires
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
            ({
                let (_file, entry, definition) = caller;
                let project = self.targets_model().project_model();
                &&& self.mixed_func_wiring_matches(_file, entry, limit, Ok(FuncWiringResult::Checked(*scope)))
                &&& *source == project.sources_model()[_file as int]
                &&& *parsed == project.indexes_model()[_file as int]->Circuit_0
                &&& self.mixed_checked_call(DefinitionPosition { file: _file, entry, definition, reference: record.0 }, record.1)
            }),
            crate::project::parsed_circuit_matches(*source, *parsed),
            types@.len() == scope.drivers.definitions@.len(), old(signatures).matches_mixed(self, limit),
        ensures
            final(signatures).matches_mixed(self, limit),
            self.mixed_call_inputs_match(source, parsed,
                crate::project::use_aliases::call_arity::checks::at_definition(parsed, caller.1 as int, caller.2 as int),
                caller.1, scope, types@, record.1, limit, result),
    {
        let (_file, entry, definition) = caller;
        let reference = record.0;
        let call = &record.1;
        let ghost at = DefinitionPosition { file: _file, entry, definition, reference };
        proof {
            self.mixed_func_call_arity_origin(_file, entry, definition, reference, *call);
            source.text_model_is_text();
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let frame = &parsed.entry_ranges[entry];
        let absolute = frame.definitions.start + definition;
        let row = &parsed.definitions[absolute];
        let ref_pos = row.references.start + reference;
        let forms = parsed.syntax.forms.as_slice();
        proof { build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int); }
        self.prepare_mixed_call_signature(Ghost(at), call, limit, signatures)?;
        let signature = cached_signature(signatures, call);
        let mut remaining = call_argument_range(forms, &call.call);
        let mut ordinal = 0;
        let mut deferred = None;
        let ghost arguments: Seq<usize> = Seq::empty();
        let ghost values: Seq<Option<SignalType>> = Seq::empty();
        proof {
            first_call_argument_evidence(forms@, call.call, remaining);
            reveal(MixedUseAliases::mixed_call_argument_prefix);
        }
        while remaining.start < remaining.end
            invariant
                mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
                self.mixed_func_wiring_matches(_file, entry, limit, Ok(FuncWiringResult::Checked(*scope))),
                signatures.matches_mixed(self, limit),
                caller == (_file, entry, definition), *call == record.1, reference == record.0,
                self.mixed_checked_call(at, *call), at == (DefinitionPosition { file: _file, entry, definition, reference }),
                ({
                    let project = self.targets_model().project_model();
                    &&& *source == project.sources_model()[_file as int]
                    &&& *parsed == project.indexes_model()[_file as int]->Circuit_0
                }),
                *source == *call.source, forms@ == parsed.syntax.forms@,
                crate::project::parsed_circuit_matches(*source, *parsed),
                entry < parsed.syntax.entries@.len() && entry < parsed.entry_ranges@.len(),
                *frame == parsed.entry_ranges@[entry as int],
                frame.definitions.start <= absolute < frame.definitions.end <= parsed.definitions@.len(),
                absolute == frame.definitions.start + definition, *row == parsed.definitions@[absolute as int],
                row.references.start <= ref_pos < row.references.end, ref_pos == row.references.start + reference,
                types@.len() == scope.drivers.definitions@.len(),
                ordinal <= call.call.arguments, ordinal == arguments.len() == values.len(),
                call.call.form < forms@.len() && forms@[call.call.form as int] is List,
                remaining.start <= remaining.end <= forms@.len(), remaining.end == forms@[call.call.form as int]->List_end,
                expression_region(forms@, remaining.start as int, remaining.end as int),
                call_argument_sequence(forms@, remaining, call.call.arguments - ordinal),
                remaining.start < remaining.end ==> direct_call_argument(forms@, call.call, remaining.start as int),
                match (call.target, signature) {
                    (FuncCallTarget::Nor, None) => true,
                    (FuncCallTarget::Function { file: target_file, entry: target_entry, arity, .. }, Some(signature)) =>
                        self.mixed_typed_signature_matches(target_file, target_entry, limit, Ok(Some(*signature)))
                            && signature.inputs@.len() == arity.inputs,
                    _ => false,
                },
                self.mixed_call_argument_prefix(source, parsed, *row, entry, scope, types@, *call, limit,
                    arguments, values, remaining.start),
                first_mixed_deferred(source, forms@, arguments, values, deferred),
            decreases remaining.end - remaining.start,
        {
            proof {
                parsed_index_evidence(*source, *parsed);
                self.mixed_func_call_arity_origin(_file, entry, definition, reference, *call);
                source.text_model_is_text();
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
            }
            let Some(argument) = next_call_argument(forms, remaining.start..remaining.end) else { unreachable!() };
            let Some(port) = signature_port(signature, PortDirection::Input, ordinal) else { unreachable!() };
            let root = argument.start;
            let known = if matches!(forms[root], Form::Atom { kind: AtomKind::Name, .. }) {
                let position = indexed_call_signal(source.text, forms, row, parsed.references.as_slice(), ref_pos,
                    &call.call, parsed.signals.as_slice(), root);
                proof { self.mixed_wiring_signal_driver(_file, entry, limit, *scope, absolute, position); }
                let bound = &scope.signals[position - frame.signals.start];
                let known = inherit_type(scope, types, bound.driver);
                assert(self.mixed_known_argument(parsed, *row, entry, scope, types@, root, known)) by {
                    assert(parsed.signals@[position as int] == root);
                };
                known
            } else { None };
            let leaf = check_leaf(source, forms, root, &port, known, limit);
            let ghost model = leaf;
            let result = report_call_argument(source, forms, root, ordinal, &port, leaf);
            proof {
                assert(self.mixed_input_port(*call, limit, ordinal, port));
                assert(self.mixed_argument_at(source, parsed, *row, entry, scope, types@, *call, limit, root, ordinal,
                    match result { Ok(typed) => Ok(typed), Err(error) => Err(MixedFuncTypeError::Input(error)) })) by {
                    assert(leaf_result(source, forms@[root as int], &port, known, limit, model));
                };
            }
            let value = match result {
                Ok(value) => value,
                Err(error) => {
                    let error = MixedFuncTypeError::Input(error);
                    proof {
                        let definition_row = crate::project::use_aliases::call_arity::checks::at_definition(
                            parsed, entry as int, definition as int);
                        assert(*row == definition_row);
                        assert(self.mixed_argument_at(source, parsed, definition_row, entry, scope, types@, *call, limit,
                            root, ordinal, Err(error)));
                        self.record_mixed_argument_failure(source, parsed, definition_row, entry, scope, types@, *call, limit,
                            arguments, values, root, error);
                        assert(self.mixed_call_inputs_match(source, parsed,
                            crate::project::use_aliases::call_arity::checks::at_definition(parsed, caller.1 as int, caller.2 as int),
                            caller.1, scope, types@, record.1, limit, Err(error)));
                    }
                    return Err(error);
                }
            };
            let ghost previous = deferred;
            if deferred.is_none() && value.is_none() {
                deferred = Some(form_location(source, forms, root));
            }
            proof {
                extend_first_mixed_deferred(source, forms@, arguments, values, root, value, previous, deferred);
                following_call_argument(forms@, call.call, root as int, argument.end as int);
                self.extend_mixed_argument_prefix(source, parsed, *row, entry, scope, types@, *call, limit,
                    arguments, values, root, argument.end, value);
                arguments = arguments.push(root);
                values = values.push(value);
            }
            remaining.start = argument.end;
            ordinal += 1;
        }
        proof { crate::syntax::circuit::exhausted_call_arguments(forms@, remaining, call.call.arguments - ordinal); }
        Ok(deferred)
    }
}

spec fn after_argument(forms: Seq<Form>, root: usize) -> int {
    if forms[root as int] is List { forms[root as int]->List_end as int } else { root + 1 }
}

spec fn first_mixed_deferred(source: &ProjectSource, forms: Seq<Form>, args: Seq<usize>, values: Seq<Option<SignalType>>,
    deferred: Option<LocatedName>) -> bool {
    match deferred {
        None => forall|i: int| 0 <= i < values.len() ==> (#[trigger] values[i]).is_some(),
        Some(site) => exists|i: int| 0 <= i < values.len() && (#[trigger] values[i]).is_none()
            && crate::project::circuits::is_form_location(source, forms[args[i] as int], site)
            && forall|j: int| 0 <= j < i ==> (#[trigger] values[j]).is_some(),
    }
}

spec fn first_pending_call(outcomes: Seq<Option<LocatedName>>, first: Option<LocatedName>) -> bool {
    match first {
        None => forall|i: int| 0 <= i < outcomes.len() ==> (#[trigger] outcomes[i]).is_none(),
        Some(site) => exists|i: int| 0 <= i < outcomes.len() && (#[trigger] outcomes[i]) == Some(site)
            && forall|j: int| 0 <= j < i ==> (#[trigger] outcomes[j]).is_none(),
    }
}

proof fn extend_first_pending_call(outcomes: Seq<Option<LocatedName>>, item: Option<LocatedName>,
    previous: Option<LocatedName>, next: Option<LocatedName>)
    requires
        first_pending_call(outcomes, previous),
        next == if previous.is_some() { previous } else { item },
    ensures first_pending_call(outcomes.push(item), next),
{
    let extended = outcomes.push(item);
    if let Some(site) = previous {
        let i = choose|i: int| 0 <= i < outcomes.len() && (#[trigger] outcomes[i]) == Some(site)
            && forall|j: int| 0 <= j < i ==> (#[trigger] outcomes[j]).is_none();
        assert(extended[i] == outcomes[i]);
        assert forall|j: int| 0 <= j < i implies (#[trigger] extended[j]).is_none() by {
            assert(extended[j] == outcomes[j]);
        };
    } else {
        assert forall|j: int| 0 <= j < outcomes.len() implies (#[trigger] extended[j]).is_none() by {
            assert(extended[j] == outcomes[j]);
        };
        assert(extended[outcomes.len() as int] == item);
    }
}

proof fn extend_first_mixed_deferred(source: &ProjectSource, forms: Seq<Form>, args: Seq<usize>, values: Seq<Option<SignalType>>,
    root: usize, value: Option<SignalType>, previous: Option<LocatedName>, next: Option<LocatedName>)
    requires
        args.len() == values.len(),
        first_mixed_deferred(source, forms, args, values, previous),
        previous.is_some() || value.is_some() ==> next == previous,
        previous.is_none() && value.is_none() ==> next.is_some()
            && crate::project::circuits::is_form_location(source, forms[root as int], next->Some_0),
    ensures first_mixed_deferred(source, forms, args.push(root), values.push(value), next),
{
    let inferred = values.push(value);
    let extended = args.push(root);
    if let Some(site) = previous {
        let i = choose|i: int| 0 <= i < values.len() && (#[trigger] values[i]).is_none()
            && crate::project::circuits::is_form_location(source, forms[args[i] as int], site)
            && forall|j: int| 0 <= j < i ==> (#[trigger] values[j]).is_some();
        assert(inferred[i] == values[i] && extended[i] == args[i]);
        assert forall|j: int| 0 <= j < i implies (#[trigger] inferred[j]).is_some() by {
            assert(inferred[j] == values[j]);
        };
    } else {
        assert forall|j: int| 0 <= j < values.len() implies (#[trigger] inferred[j]).is_some() by {
            assert(inferred[j] == values[j]);
        };
        assert(inferred[values.len() as int] == value && extended[args.len() as int] == root);
    }
}

}
