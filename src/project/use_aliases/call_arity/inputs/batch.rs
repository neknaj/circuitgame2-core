//! 関数の配線と型を共有し、右辺に現れる呼び出しの引数を検査する。

use super::{CallInputError, FuncAtomTypeError, FuncAtomTypes, FuncWiring, FuncWiringResult, ProjectedCallArgument, UseAliases};
use super::super::RootFunctionCall;
use crate::project::use_aliases::signature_cache::SignatureCache;
use crate::project::{DefinitionPosition, SignalType};
use alloc::vec::Vec;
use core::ops::Range;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::project::use_aliases::definitions::{definition_count, reference_count};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence};
use vstd::prelude::*;

verus! {

/// 平坦な実引数列と、定義順に並ぶ呼び出しごとの引数範囲。
pub(in crate::project::use_aliases) struct CallArgumentProjections {
    pub(in crate::project::use_aliases) arguments: Vec<ProjectedCallArgument>,
    pub(in crate::project::use_aliases) ranges: Vec<Range<usize>>,
}

impl CallArgumentProjections {
    pub(in crate::project::use_aliases) fn new() -> (projections: Self)
        ensures projections.arguments@.len() == 0, projections.ranges@.len() == 0,
    {
        Self { arguments: Vec::new(), ranges: Vec::new() }
    }
}

/// 関数の引数をまとめて検査したときの最初の違反。
#[derive(Debug)]
pub enum FuncCallInputsError<'p, 'a> {
    /// 呼び出し元の配線、入出力数、定数または裸の信号参照の検査で見つかった違反。
    Caller(FuncAtomTypeError<'p, 'a>),
    /// 準備が済んだ関数の右辺で見つかった違反。
    Call {
        /// 違反が見つかった呼び出しの名前参照の添字。
        position: DefinitionPosition,
        /// 呼び出し先の署名、引数の個数、または個々の引数に関する診断。
        error: CallInputError<'p, 'a>,
    },
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn input_ref_valid(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        types: Seq<Option<SignalType>>, wiring: &FuncWiring,
    ) -> bool {
        exists|value: Option<super::CheckedCallInputs>|
            #[trigger] self.scoped_input_result(file, entry, definition, reference, limit, types, wiring, false, Ok(value))
    }

    #[verifier::opaque]
    spec fn input_refs_before(
        &self, file: usize, entry: usize, definition: usize, stop: int, limit: u64,
        types: Seq<Option<SignalType>>, wiring: &FuncWiring,
    ) -> bool {
        forall|reference: usize| reference < stop
            ==> #[trigger] self.input_ref_valid(file, entry, definition, reference, limit, types, wiring)
    }

    #[verifier::opaque]
    spec fn input_definitions_before(
        &self, file: usize, entry: usize, stop: int, limit: u64, types: Seq<Option<SignalType>>, wiring: &FuncWiring,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        forall|definition: usize| definition < stop ==> #[trigger] self.input_refs_before(
            file, entry, definition, reference_count(parsed, entry as int, definition as int),
            limit, types, wiring)
    }

    pub(in crate::project::use_aliases) closed spec fn prepared_call_inputs_match(
        &self, file: usize, entry: usize, limit: u64, types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        result: Result<(), FuncCallInputsError>,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let count = definition_count(parsed, entry as int);
        match result {
            Ok(_) => self.input_definitions_before(file, entry, count, limit, types, wiring),
            Err(FuncCallInputsError::Caller(_)) => false,
            Err(FuncCallInputsError::Call { position, error }) =>
                position.file == file && position.entry == entry && position.definition < count
                && position.reference < reference_count(parsed, entry as int, position.definition as int)
                && self.input_definitions_before(file, entry, position.definition as int, limit, types, wiring)
                && self.input_refs_before(file, entry, position.definition, position.reference as int, limit, types, wiring)
                && self.scoped_input_result(file, entry, position.definition, position.reference, limit,
                    types, wiring, false, Err(error)),
        }
    }

    pub(in crate::project::use_aliases) proof fn prepared_inputs_succeeded(
        &self, file: usize, entry: usize, limit: u64, types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        result: Result<(), FuncCallInputsError>,
    )
        requires result is Ok, self.prepared_call_inputs_match(file, entry, limit, types, wiring, result),
        ensures self.prepared_call_inputs_match(file, entry, limit, types, wiring, Ok(())),
    {}

    /// 呼び出し元の検査と、定義順・参照順で最初に見つかる引数の違反を表す。
    pub closed spec fn all_func_call_inputs_evidence(
        &self, file: usize, entry: usize, limit: u64, result: Result<FuncAtomTypes, FuncCallInputsError>,
    ) -> bool {
        match result {
            Ok(typed) => self.func_atom_type_evidence(file, entry, limit, Ok(typed))
                && (typed.literals.wiring matches FuncWiringResult::Checked(wiring) ==>
                    self.prepared_call_inputs_match(file, entry, limit, typed.types@, &wiring, Ok(()))),
            Err(FuncCallInputsError::Caller(error)) => self.func_atom_type_evidence(file, entry, limit, Err(error)),
            Err(error) => exists|typed: FuncAtomTypes| typed.literals.wiring matches FuncWiringResult::Checked(wiring)
                && #[trigger] self.func_atom_type_evidence(file, entry, limit, Ok(typed))
                && self.prepared_call_inputs_match(file, entry, limit, typed.types@, &wiring, Err(error)),
        }
    }

    fn check_definition_input_types(
        &self, file: usize, entry: usize, definition: usize, max_width: u64,
        types: &[Option<SignalType<'p, 'a>>], wiring: &FuncWiring<'p, 'a>,
        signatures: &mut SignatureCache<'p, 'a>,
        projections: &mut Vec<ProjectedCallArgument>, retain_root: bool,
    ) -> (result: Result<(), (usize, CallInputError<'p, 'a>)>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
            file < self.targets.project_model().circuits_model().len(),
            types@.len() == wiring.drivers.definitions@.len(),
            definition < definition_count(&self.targets.project_model().circuits_model()[file as int], entry as int),
            old(signatures).matches(self, max_width),
            retain_root ==> reference_count(
                &self.targets.project_model().circuits_model()[file as int], entry as int, definition as int) > 0,
        ensures final(signatures).matches(self, max_width),
        result.is_ok() ==> old(projections)@.len() <= final(projections)@.len(),
        result.is_ok() ==> final(projections)@.take(old(projections)@.len() as int) == old(projections)@,
        result.is_ok() && !retain_root ==> final(projections)@ == old(projections)@,
        retain_root && result.is_ok() ==> self.projected_input_arguments((file, entry, definition, 0),
            max_width, types@, wiring, final(projections)@.skip(old(projections)@.len() as int)),
        ({
            let parsed = &self.targets.project_model().circuits_model()[file as int];
            let count = reference_count(parsed, entry as int, definition as int);
            match result {
                Ok(()) => self.input_refs_before(file, entry, definition, count, max_width, types@, wiring),
                Err((reference, error)) => reference < count
                    && self.input_refs_before(file, entry, definition, reference as int, max_width, types@, wiring)
                    && self.scoped_input_result(file, entry, definition, reference, max_width, types@, wiring, false, Err(error)),
            }
        }),
    {
        let ghost previous = projections@;
        let ghost start = previous.len() as int;
        assert(previous.take(start) =~= previous);
        let project = self.targets.project();
        proof {
            self.checked_wiring_is_func(file, entry, max_width, *wiring);
        }
        let parsed = &project.circuits()[file];
        proof {
            let source = &project.sources_model()[file as int];
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int,
                parsed.entry_ranges@[entry as int].definitions.start + definition);
            reveal(UseAliases::input_refs_before);
        }
        let row = &parsed.definitions[parsed.entry_ranges[entry].definitions.start + definition];
        let stop = row.references.end - row.references.start;
        let mut reference = 0;
        while reference < stop
            invariant
                self.can_resolve(), self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
                types@.len() == wiring.drivers.definitions@.len(),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                file < self.targets.project_model().circuits_model().len(),
                reference <= stop == reference_count(parsed, entry as int, definition as int),
                self.input_refs_before(file, entry, definition, reference as int, max_width, types@, wiring),
                signatures.matches(self, max_width),
                previous == old(projections)@, start == previous.len(), start <= projections@.len(),
                projections@.take(start) == previous,
                (!retain_root || reference == 0) ==> projections@ == previous,
                retain_root ==> stop > 0,
                retain_root && reference > 0 ==> self.projected_input_arguments((file, entry, definition, 0),
                    max_width, types@, wiring, projections@.skip(start)),
            decreases stop - reference,
        {
            let retain = retain_root && reference == 0;
            let _value = match self.check_call_inputs_with_types(file, entry, definition, reference, max_width, types, wiring, false,
                signatures, projections, retain) {
                Ok(value) => value,
                Err(error) => return Err((reference, error)),
            };
            proof {
                reveal(UseAliases::input_refs_before);
                assert forall|prior: usize| prior <= reference
                    implies #[trigger] self.input_ref_valid(file, entry, definition, prior, max_width, types@, wiring) by {
                    if prior == reference {
                        assert(self.scoped_input_result(file, entry, definition, prior, max_width, types@, wiring, false, Ok(_value)));
                    } else {
                        assert(self.input_ref_valid(file, entry, definition, prior, max_width, types@, wiring));
                    }
                };
            }
            reference += 1;
        }
        Ok(())
    }

    #[verifier::opaque]
    pub(in crate::project::use_aliases) closed spec fn projected_roots_match(
        &self, caller: (usize, usize, u64), types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        calls: Seq<RootFunctionCall>, ranges: Seq<Range<usize>>, arguments: Seq<ProjectedCallArgument>,
    ) -> bool {
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let start = parsed.entry_ranges@[entry as int].definitions.start;
        &&& ranges.len() <= calls.len()
        &&& arguments.len() == if ranges.len() == 0 { 0 } else { ranges.last().end as nat }
        &&& forall|i: int| 0 <= i < ranges.len() ==> {
            let range = #[trigger] ranges[i];
            let call = calls[i];
            &&& range.start == if i == 0 { 0 } else { ranges[i - 1].end }
            &&& range.start <= range.end <= arguments.len()
            &&& start <= call.definition
            &&& self.projected_input_arguments((file, entry, (call.definition - start) as usize, 0),
                limit, types, wiring, arguments.subrange(range.start as int, range.end as int))
        }
    }

    /// 呼び出しの添字から、その定義に対応する引数範囲と検査の根拠を得る。
    pub(in crate::project::use_aliases) proof fn projected_root_argument_range(
        &self, caller: (usize, usize, u64), types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        calls: Seq<RootFunctionCall>, ranges: Seq<Range<usize>>, arguments: Seq<ProjectedCallArgument>,
        position: int,
    )
        requires
            self.projected_roots_match(caller, types, wiring, calls, ranges, arguments),
            0 <= position < ranges.len(),
        ensures ({
            let (file, entry, limit) = caller;
            let parsed = &self.targets.project_model().circuits_model()[file as int];
            let start = parsed.entry_ranges@[entry as int].definitions.start;
            let range = ranges[position];
            &&& position < calls.len()
            &&& start <= calls[position].definition
            &&& range.start <= range.end <= arguments.len()
            &&& self.projected_input_arguments((file, entry, (calls[position].definition - start) as usize, 0),
                limit, types, wiring, arguments.subrange(range.start as int, range.end as int))
        }),
    {
        reveal(UseAliases::projected_roots_match);
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let start = parsed.entry_ranges@[entry as int].definitions.start;
        let range = ranges[position];
        let definition = calls[position].definition;
        assert(range.start <= range.end <= arguments.len() && start <= definition);
        assert(self.projected_input_arguments((file, entry, (definition - start) as usize, 0),
            limit, types, wiring, arguments.subrange(range.start as int, range.end as int)));
    }

    proof fn extend_projected_roots(
        &self, caller: (usize, usize, u64), types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        calls: Seq<RootFunctionCall>, ranges: Seq<Range<usize>>, before: Seq<ProjectedCallArgument>,
        after: Seq<ProjectedCallArgument>, range: Range<usize>, definition: usize,
    )
        requires
            self.projected_roots_match(caller, types, wiring, calls, ranges, before),
            ranges.len() < calls.len(),
            ({
                let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
                calls[ranges.len() as int].definition == parsed.entry_ranges@[caller.1 as int].definitions.start + definition
            }),
            range.start == before.len() <= range.end == after.len(),
            after.take(before.len() as int) == before,
            self.projected_input_arguments((caller.0, caller.1, definition, 0), caller.2, types, wiring,
                after.skip(before.len() as int)),
        ensures self.projected_roots_match(caller, types, wiring, calls, ranges.push(range), after),
    {
        reveal(UseAliases::projected_roots_match);
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let start = parsed.entry_ranges@[entry as int].definitions.start;
        let result = ranges.push(range);
        assert forall|i: int| 0 <= i < result.len() implies {
            let span = #[trigger] result[i];
            let call = calls[i];
            &&& span.start == if i == 0 { 0 } else { result[i - 1].end }
            &&& span.start <= span.end <= after.len()
            &&& start <= call.definition
            &&& self.projected_input_arguments((file, entry, (call.definition - start) as usize, 0),
                limit, types, wiring, after.subrange(span.start as int, span.end as int))
        } by {
            if i < ranges.len() {
                assert(result[i] == ranges[i]);
                let span = ranges[i];
                assert(after.subrange(span.start as int, span.end as int) =~= before.subrange(span.start as int, span.end as int));
            } else {
                assert(result[i] == range);
                assert(after.subrange(range.start as int, range.end as int) == after.skip(before.len() as int));
            }
        };
    }

    /// 関数内のすべての呼び出しで、定数と型が確定した裸の信号を入力型と照合する。
    ///
    /// 呼び出し元の配線と型を一度準備し、検査結果として返す。対象外と展開待ちもその結果に含む。
    /// 入れ子の呼び出しはそれぞれ検査する。複合式や未確定の信号を渡した引数の型は保留する。
    ///
    /// # Errors
    ///
    /// 呼び出し元の検査を先に行う。その後は定義順・参照順に進み、各呼び出しの署名と
    /// 入力ポート数を確かめてから直接の引数を左から調べる。最初の違反を返す。
    pub fn check_all_func_call_inputs(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncAtomTypes<'p, 'a>, FuncCallInputsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.all_func_call_inputs_evidence(file, entry, max_width, result),
    {
        let typed = match self.check_func_atom_types(file, entry, max_width) {
            Ok(typed) => typed,
            Err(error) => return Err(FuncCallInputsError::Caller(error)),
        };
        let FuncWiringResult::Checked(ref wiring) = typed.literals.wiring else { return Ok(typed); };
        proof { self.atom_types_keep_wiring(file, entry, max_width, typed, *wiring); }
        let mut signatures = SignatureCache::new();
        let mut projections = CallArgumentProjections::new();
        match self.check_all_inputs_with_types(file, entry, max_width, typed.types.as_slice(), wiring, &mut signatures,
            &[], &mut projections) {
            Ok(()) => Ok(typed),
            Err(error) => {
                assert(self.all_func_call_inputs_evidence(file, entry, max_width, Err(error))) by {
                    assert(self.func_atom_type_evidence(file, entry, max_width, Ok(typed)));
                };
                Err(error)
            },
        }
    }

    pub(in crate::project::use_aliases) fn check_all_inputs_with_types(
        &self, file: usize, entry: usize, max_width: u64,
        types: &[Option<SignalType<'p, 'a>>], wiring: &FuncWiring<'p, 'a>,
        signatures: &mut SignatureCache<'p, 'a>,
        calls: &[RootFunctionCall], projections: &mut CallArgumentProjections,
    ) -> (result: Result<(), FuncCallInputsError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
            types@.len() == wiring.drivers.definitions@.len(),
            old(signatures).matches(self, max_width),
            self.root_call_definitions_in_order(file, entry, calls@),
            old(projections).arguments@.len() == 0, old(projections).ranges@.len() == 0,
        ensures self.prepared_call_inputs_match(file, entry, max_width, types@, wiring, result),
            final(signatures).matches(self, max_width),
            result.is_ok() ==> final(projections).ranges@.len() == calls@.len()
                && self.projected_roots_match((file, entry, max_width), types@, wiring, calls@,
                    final(projections).ranges@, final(projections).arguments@),
    {
        let project = self.targets.project();
        proof {
            self.checked_wiring_is_func(file, entry, max_width, *wiring);
        }
        let parsed = &project.circuits()[file];
        proof {
            let source = &project.sources_model()[file as int];
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
            reveal(UseAliases::input_definitions_before);
        }
        let range = &parsed.entry_ranges[entry].definitions;
        let stop = range.end - range.start;
        let mut cursor = 0;
        let mut definition = 0;
        assert(self.projected_roots_match((file, entry, max_width), types@, wiring, calls@,
            projections.ranges@, projections.arguments@)) by { reveal(UseAliases::projected_roots_match); };
        while definition < stop
            invariant
                self.can_resolve(), self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
                types@.len() == wiring.drivers.definitions@.len(),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                definition <= stop == definition_count(parsed, entry as int),
                range.start + stop == range.end,
                entry < parsed.entry_ranges@.len(),
                range.start <= range.end <= parsed.definitions@.len(),
                *range == parsed.entry_ranges@[entry as int].definitions,
                self.root_call_definitions_in_order(file, entry, calls@),
                file < self.targets.project_model().circuits_model().len(),
                cursor == projections.ranges@.len() <= calls@.len(),
                forall|i: int| cursor <= i < calls@.len() ==> (#[trigger] calls@[i]).definition >= range.start + definition,
                self.projected_roots_match((file, entry, max_width), types@, wiring, calls@,
                    projections.ranges@, projections.arguments@),
                self.input_definitions_before(file, entry, definition as int, max_width, types@, wiring),
                signatures.matches(self, max_width),
            decreases stop - definition,
        {
            let retain = cursor < calls.len() && calls[cursor].definition == range.start + definition;
            let start = projections.arguments.len();
            let ghost before = projections.arguments@;
            let ghost previous_cursor = cursor;
            proof {
                if retain {
                    let absolute = range.start + definition;
                    assert(calls@[cursor as int].definition == absolute);
                    let refs = parsed.definitions@[absolute as int].references;
                    assert(refs.start < refs.end);
                    assert(reference_count(parsed, entry as int, definition as int) == refs.end - refs.start);
                    assert(reference_count(parsed, entry as int, definition as int) > 0);
                }
            }
            if let Err((reference, error)) = self.check_definition_input_types(file, entry, definition, max_width, types, wiring, signatures,
                &mut projections.arguments, retain) {
                let position = DefinitionPosition { file, entry, definition, reference };
                return Err(FuncCallInputsError::Call { position, error });
            }
            if retain {
                let span = start..projections.arguments.len();
                proof { self.extend_projected_roots((file, entry, max_width), types@, wiring, calls@,
                    projections.ranges@, before, projections.arguments@, span, definition); }
                projections.ranges.push(span);
                cursor += 1;
            }
            proof {
                assert forall|i: int| cursor <= i < calls@.len()
                    implies (#[trigger] calls@[i]).definition >= range.start + definition + 1 by {
                    assert(calls@[previous_cursor as int].definition >= range.start + definition);
                    if i > previous_cursor {
                        assert(calls@[i].definition > calls@[previous_cursor as int].definition);
                    }
                };
                reveal(UseAliases::input_definitions_before);
                assert forall|prior: usize| prior <= definition implies #[trigger] self.input_refs_before(
                    file, entry, prior, reference_count(parsed, entry as int, prior as int), max_width, types@, wiring)
                by {
                    if prior < definition {
                        assert(self.input_refs_before(file, entry, prior,
                            reference_count(parsed, entry as int, prior as int), max_width, types@, wiring));
                    }
                };
            }
            definition += 1;
        }
        if cursor < calls.len() {
            assert(calls@[cursor as int].definition < range.end);
            assert(calls@[cursor as int].definition >= range.start + definition);
        }
        assert(cursor == calls@.len());
        Ok(())
    }
}

} // verus!
