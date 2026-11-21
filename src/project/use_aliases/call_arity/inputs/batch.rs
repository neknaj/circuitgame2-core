//! 関数の配線と型を共有し、右辺に現れる呼び出しの引数を検査する。

use super::{CallInputError, FuncAtomTypeError, FuncAtomTypes, FuncWiring, FuncWiringResult, ProjectedCallArgument, UseAliases};
use super::super::RootFunctionCall;
use crate::project::use_aliases::signature_cache::SignatureCache;
use crate::project::{DefinitionPosition, SignalType};
use alloc::vec::Vec;
use core::ops::Range;
#[cfg(verus_only)]
use crate::project::circuits::{parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::project::use_aliases::definitions::{definition_count, reference_count};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    build_definition_reference_boundaries, build_definition_scope_evidence, build_entry_ranges_evidence,
};
use vstd::prelude::*;

#[cfg(test)]
mod tests {
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    #[test]
    fn retains_nested_argument_ranges_after_an_earlier_functions_references() {
        let text = concat!(
            "(using nor) (struct T (width 1)) ",
            "(func earlier (in a) (out y) (def y (nor a a))) ",
            "(func zero (in) (out y) (def y 0)) ",
            "(func id (in a) (out a)) ",
            "(func main (in a) (out y) (def tagged (as T a)) ",
            " (def inverted (nor (zero) a)) (def y (id (zero))))",
        );
        let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 1, text }]).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let aliases = check_use_aliases(&targets).unwrap();
        let (_, retained) = aliases.check_func_signal_projections(0, 5, 8, false, true).unwrap();
        assert_eq!(retained.call_arguments.reference_argument_ends, [0, 2, 2, 3, 3]);
        assert_eq!(retained.call_arguments.ranges, [2..3]);
        assert_eq!(retained.call_arguments.arguments.len(), 3);
        let (_, regular) = aliases.check_func_signal_projections(0, 5, 8, false, false).unwrap();
        assert!(regular.call_arguments.reference_argument_ends.is_empty());
        assert!(regular.call_arguments.arguments.is_empty());
    }
}

verus! {

/// 関数内の実引数を、定義順・参照順で一つの配列に並べる。
pub(in crate::project::use_aliases) struct CallArgumentProjections {
    pub(in crate::project::use_aliases) arguments: Vec<ProjectedCallArgument>,
    /// 右辺全体にある展開対象の関数呼び出しが占める引数範囲。
    pub(in crate::project::use_aliases) ranges: Vec<Range<usize>>,
    /// 関数内の厳格参照順に並ぶ、引数範囲の末尾。
    ///
    /// 各範囲は直前の末尾から始まる。先頭の範囲は 0 から始まる。
    /// 型名参照と引数がない呼び出しの範囲は空になる。
    pub(in crate::project::use_aliases) reference_argument_ends: Vec<usize>,
}

impl CallArgumentProjections {
    pub(in crate::project::use_aliases) fn new() -> (projections: Self)
        ensures projections.arguments@.len() == 0, projections.ranges@.len() == 0,
            projections.reference_argument_ends@.len() == 0,
    {
        Self { arguments: Vec::new(), ranges: Vec::new(), reference_argument_ends: Vec::new() }
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

    spec fn argument_boundary(ends: Seq<usize>, reference: int) -> int {
        if reference == 0 { 0 } else { ends[reference - 1] as int }
    }

    #[verifier::opaque]
    spec fn projected_reference_prefix(
        &self, caller: (usize, usize, u64), types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        definition: usize, count: int, ends: Seq<usize>, arguments: Seq<ProjectedCallArgument>,
    ) -> bool {
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int];
        let refs = parsed.definitions@[frame.definitions.start + definition].references;
        let base = refs.start - frame.references.start;
        &&& 0 <= base && 0 <= count <= refs.end - refs.start
        &&& base + count <= ends.len()
        &&& forall|r: int| 0 <= r < count ==> {
            let end = (#[trigger] ends[base + r]) as int;
            let start = Self::argument_boundary(ends, base + r);
            &&& 0 <= start <= end <= arguments.len()
            &&& self.projected_input_arguments((file, entry, definition, r as usize), limit, types, wiring,
                arguments.subrange(start, end))
        }
    }

    #[verifier::opaque]
    spec fn root_range_matches_reference(
        &self, caller: (usize, usize, u64), call: RootFunctionCall, range: Range<usize>, ends: Seq<usize>,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
        let frame = parsed.entry_ranges@[caller.1 as int];
        let refs = parsed.definitions@[call.definition as int].references;
        let reference = refs.start - frame.references.start;
        &&& 0 <= reference < ends.len()
        &&& range.start == Self::argument_boundary(ends, reference)
        &&& range.end == ends[reference]
    }

    /// 完成した実引数配列の範囲が、関数内のすべての厳格参照に対応することを表す。
    pub(in crate::project::use_aliases) closed spec fn projected_references_match(
        &self, caller: (usize, usize, u64), types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        projections: &CallArgumentProjections, calls: Seq<RootFunctionCall>,
    ) -> bool {
        let ends = projections.reference_argument_ends@;
        let arguments = projections.arguments@;
        let (file, entry, _) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int];
        &&& ends.len() == frame.references.end - frame.references.start
        &&& arguments.len() == Self::argument_boundary(ends, ends.len() as int)
        &&& self.projected_definitions_before(caller, types, wiring, definition_count(parsed, entry as int), ends, arguments)
        &&& projections.ranges@.len() == calls.len()
        &&& forall|i: int| 0 <= i < calls.len() ==> self.root_range_matches_reference(
            caller, calls[i], #[trigger] projections.ranges@[i], ends)
    }

    #[verifier::opaque]
    spec fn projected_definitions_before(
        &self, caller: (usize, usize, u64), types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        definition: int, ends: Seq<usize>, arguments: Seq<ProjectedCallArgument>,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
        forall|d: usize| d < definition ==> #[trigger] self.projected_reference_prefix(caller, types, wiring, d,
            reference_count(parsed, caller.1 as int, d as int), ends, arguments)
    }

    proof fn projected_reference_range_evidence(
        &self, caller: (usize, usize, u64), types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        definition: usize, count: int, reference: usize, ends: Seq<usize>, arguments: Seq<ProjectedCallArgument>,
    )
        requires reference < count,
            self.projected_reference_prefix(caller, types, wiring, definition, count, ends, arguments),
        ensures ({
            let (file, entry, limit) = caller;
            let parsed = &self.targets.project_model().circuits_model()[file as int];
            let frame = parsed.entry_ranges@[entry as int];
            let refs = parsed.definitions@[frame.definitions.start + definition].references;
            let index = refs.start - frame.references.start + reference;
            let start = Self::argument_boundary(ends, index);
            let end = ends[index] as int;
            &&& 0 <= index < ends.len() && 0 <= start <= end <= arguments.len()
            &&& self.projected_input_arguments((file, entry, definition, reference), limit, types, wiring,
                arguments.subrange(start, end))
        }),
    {
        reveal(UseAliases::projected_reference_prefix);
    }

    /// 型検査で保持した引数範囲を、定義内の参照添字から取り出す。
    ///
    /// 同じプロジェクトの型検査で得た投影と、その関数に属する定義・参照の添字を渡す。
    /// 引数がなければ空の半開範囲を返す。呼び出しと型名参照の区別には元の参照種別を使う。
    pub(in crate::project::use_aliases) fn retained_call_argument_range(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        projections: &CallArgumentProjections,
        Ghost(limit): Ghost<u64>, Ghost(types): Ghost<Seq<Option<SignalType<'p, 'a>>>>,
        Ghost(wiring): Ghost<FuncWiring<'p, 'a>>, Ghost(roots): Ghost<Seq<RootFunctionCall>>,
    ) -> (range: Range<usize>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
            self.projected_references_match((file, entry, limit), types, &wiring, projections, roots),
            ({
                let parsed = &self.targets.project_model().circuits_model()[file as int];
                definition < definition_count(parsed, entry as int)
                && reference < reference_count(parsed, entry as int, definition as int)
            }),
        ensures
            range.start <= range.end <= projections.arguments@.len(),
            self.projected_input_arguments((file, entry, definition, reference), limit, types, &wiring,
                projections.arguments@.subrange(range.start as int, range.end as int)),
            ({
                let parsed = &self.targets.project_model().circuits_model()[file as int];
                let frame = parsed.entry_ranges@[entry as int];
                let def = frame.definitions.start + definition;
                let key = parsed.definitions@[def].references.start - frame.references.start + reference;
                let ends = projections.reference_argument_ends@;
                &&& 0 <= key < ends.len()
                &&& range.start == if key == 0 { 0 } else { ends[key - 1] }
                &&& range.end == ends[key]
                &&& forall|i: int| 0 <= i < roots.len() && (#[trigger] roots[i]).definition == def && reference == 0
                    ==> projections.ranges@[i] == range
            }),
    {
        let project = self.targets.project();
        proof { self.checked_wiring_is_func(file, entry, limit, wiring); }
        let parsed = &project.circuits()[file];
        let frame = &parsed.entry_ranges[entry];
        let absolute = frame.definitions.start + definition;
        let row = &parsed.definitions[absolute];
        proof {
            let source = project.sources_model()[file as int];
            parsed_index_evidence(source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
            reveal(UseAliases::projected_definitions_before);
            let count = reference_count(parsed, entry as int, definition as int);
            self.projected_reference_range_evidence((file, entry, limit), types, &wiring, definition,
                count, reference, projections.reference_argument_ends@, projections.arguments@);
        }
        let index = row.references.start - frame.references.start + reference;
        let ends = &projections.reference_argument_ends;
        let start = if index == 0 { 0 } else { ends[index - 1] };
        let range = start..ends[index];
        proof {
            assert forall|i: int| 0 <= i < roots.len() && (#[trigger] roots[i]).definition == absolute && reference == 0
                implies projections.ranges@[i] == range by {
                assert(self.root_range_matches_reference((file, entry, limit), roots[i],
                    projections.ranges@[i], ends@));
                reveal(UseAliases::root_range_matches_reference);
            };
        }
        range
    }

    fn check_definition_input_types(
        &self, file: usize, entry: usize, definition: usize, max_width: u64,
        types: &[Option<SignalType<'p, 'a>>], wiring: &FuncWiring<'p, 'a>,
        signatures: &mut SignatureCache<'p, 'a>,
        projections: &mut Vec<ProjectedCallArgument>, ends: &mut Vec<usize>, retain: bool,
    ) -> (result: Result<(), (usize, CallInputError<'p, 'a>)>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
            file < self.targets.project_model().circuits_model().len(),
            types@.len() == wiring.drivers.definitions@.len(),
            definition < definition_count(&self.targets.project_model().circuits_model()[file as int], entry as int),
            old(signatures).matches(self, max_width),
            retain ==> ({
                let parsed = &self.targets.project_model().circuits_model()[file as int];
                let frame = parsed.entry_ranges@[entry as int];
                let refs = parsed.definitions@[frame.definitions.start + definition].references;
                &&& refs.start == frame.references.start + old(ends)@.len()
                &&& old(projections)@.len() == Self::argument_boundary(old(ends)@, old(ends)@.len() as int)
            }),
        ensures final(signatures).matches(self, max_width),
        result.is_ok() ==> old(projections)@.len() <= final(projections)@.len(),
        result.is_ok() ==> final(projections)@.take(old(projections)@.len() as int) == old(projections)@,
        result.is_ok() && !retain ==> final(projections)@ == old(projections)@ && final(ends)@ == old(ends)@,
        result.is_ok() && retain ==> ({
            let parsed = &self.targets.project_model().circuits_model()[file as int];
            let count = reference_count(parsed, entry as int, definition as int);
            &&& final(ends)@.len() == old(ends)@.len() + count
            &&& final(ends)@.take(old(ends)@.len() as int) == old(ends)@
            &&& final(projections)@.len() == Self::argument_boundary(final(ends)@, final(ends)@.len() as int)
            &&& self.projected_reference_prefix((file, entry, max_width), types@, wiring, definition,
                count, final(ends)@, final(projections)@)
        }),
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
        let ghost previous_ends = ends@;
        let ghost caller = (file, entry, max_width);
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
        let ghost first = previous_ends.len() as int;
        proof { reveal(UseAliases::projected_reference_prefix); }
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
                caller == (file, entry, max_width),
                previous_ends == old(ends)@, first == previous_ends.len(),
                !retain ==> projections@ == previous && ends@ == previous_ends,
                retain ==> ({
                    let frame = parsed.entry_ranges@[entry as int];
                    &&& *row == parsed.definitions@[frame.definitions.start + definition]
                    &&& row.references.start == frame.references.start + first
                    &&& ends@.len() == first + reference
                    &&& ends@.take(first) == previous_ends
                    &&& projections@.len() == Self::argument_boundary(ends@, ends@.len() as int)
                    &&& self.projected_reference_prefix(caller, types@, wiring, definition,
                        reference as int, ends@, projections@)
                }),
            decreases stop - reference,
        {
            let ghost before = projections@;
            let ghost before_ends = ends@;
            let _value = match self.check_call_inputs_with_types(file, entry, definition, reference, max_width, types, wiring, false,
                signatures, projections, retain) {
                Ok(value) => value,
                Err(error) => return Err((reference, error)),
            };
            if retain {
                ends.push(projections.len());
                proof {
                    assert(ends@ =~= before_ends.push(projections@.len() as usize));
                    assert(ends@.take(first) =~= previous_ends);
                    assert(projections@.take(start) =~= previous);
                    reveal(UseAliases::projected_reference_prefix);
                    assert forall|r: int| 0 <= r < reference + 1 implies {
                        let end = (#[trigger] ends@[first + r]) as int;
                        let begin = Self::argument_boundary(ends@, first + r);
                        &&& 0 <= begin <= end <= projections@.len()
                        &&& self.projected_input_arguments((file, entry, definition, r as usize), max_width,
                            types@, wiring, projections@.subrange(begin, end))
                    } by {
                        let key = first + r;
                        if r < reference {
                            let begin = Self::argument_boundary(before_ends, key);
                            let end = before_ends[key] as int;
                            assert(ends@[key] == before_ends[key]);
                            assert(Self::argument_boundary(ends@, key) == begin);
                            assert(projections@.subrange(begin, end) =~= before.subrange(begin, end));
                        } else {
                            assert(Self::argument_boundary(ends@, key) == before.len());
                            assert(projections@.subrange(before.len() as int, projections@.len() as int)
                                =~= projections@.skip(before.len() as int));
                        }
                    };
                    assert(self.projected_reference_prefix(caller, types@, wiring, definition,
                        reference + 1, ends@, projections@));
                }
            }
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

    proof fn preserve_root_reference_ranges(
        &self, caller: (usize, usize, u64), calls: Seq<RootFunctionCall>, ranges: Seq<Range<usize>>,
        before: Seq<usize>, after: Seq<usize>,
    )
        requires
            before.len() <= after.len(), after.take(before.len() as int) == before,
            forall|i: int| 0 <= i < ranges.len() ==> self.root_range_matches_reference(
                caller, calls[i], #[trigger] ranges[i], before),
        ensures forall|i: int| 0 <= i < ranges.len() ==> self.root_range_matches_reference(
                caller, calls[i], #[trigger] ranges[i], after),
    {
        assert forall|i: int| 0 <= i < ranges.len() implies self.root_range_matches_reference(
            caller, calls[i], #[trigger] ranges[i], after) by {
            assert(self.root_range_matches_reference(caller, calls[i], ranges[i], before));
            reveal(UseAliases::root_range_matches_reference);
            let parsed = &self.targets.project_model().circuits_model()[caller.0 as int];
            let frame = parsed.entry_ranges@[caller.1 as int];
            let refs = parsed.definitions@[calls[i].definition as int].references;
            let reference = refs.start - frame.references.start;
            assert(after[reference] == before[reference]);
        };
    }

    proof fn preserve_projected_definitions(
        &self, caller: (usize, usize, u64), types: Seq<Option<SignalType>>, wiring: &FuncWiring,
        definition: usize, before_ends: Seq<usize>, ends: Seq<usize>,
        before: Seq<ProjectedCallArgument>, arguments: Seq<ProjectedCallArgument>,
    )
        requires
            before_ends.len() <= ends.len(), ends.take(before_ends.len() as int) == before_ends,
            before.len() <= arguments.len(), arguments.take(before.len() as int) == before,
            self.projected_definitions_before(caller, types, wiring, definition as int, before_ends, before),
            self.projected_reference_prefix(caller, types, wiring, definition,
                reference_count(&self.targets.project_model().circuits_model()[caller.0 as int],
                    caller.1 as int, definition as int), ends, arguments),
        ensures self.projected_definitions_before(caller, types, wiring, definition + 1, ends, arguments),
    {
        let (file, entry, limit) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int];
        reveal(UseAliases::projected_definitions_before);
        reveal(UseAliases::projected_reference_prefix);
        assert forall|d: usize| d < definition + 1 implies #[trigger] self.projected_reference_prefix(
            caller, types, wiring, d, reference_count(parsed, entry as int, d as int), ends, arguments) by {
            if d < definition {
                let count = reference_count(parsed, entry as int, d as int);
                let base = parsed.definitions@[frame.definitions.start + d].references.start - frame.references.start;
                assert(self.projected_reference_prefix(caller, types, wiring, d, count, before_ends, before));
                assert forall|r: int| 0 <= r < count implies {
                    let end = (#[trigger] ends[base + r]) as int;
                    let start = Self::argument_boundary(ends, base + r);
                    &&& 0 <= start <= end <= arguments.len()
                    &&& self.projected_input_arguments((file, entry, d, r as usize), limit, types, wiring,
                        arguments.subrange(start, end))
                } by {
                    let key = base + r;
                    assert(ends[key] == before_ends[key]);
                    assert(Self::argument_boundary(ends, key) == Self::argument_boundary(before_ends, key));
                    let start = Self::argument_boundary(before_ends, key);
                    let end = before_ends[key] as int;
                    assert(arguments.subrange(start, end) =~= before.subrange(start, end));
                };
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
            &[], &mut projections, false) {
            Ok(()) => Ok(typed),
            Err(error) => {
                assert(self.all_func_call_inputs_evidence(file, entry, max_width, Err(error))) by {
                    assert(self.func_atom_type_evidence(file, entry, max_width, Ok(typed)));
                };
                Err(error)
            },
        }
    }

    #[verifier::rlimit(32)]
    pub(in crate::project::use_aliases) fn check_all_inputs_with_types(
        &self, file: usize, entry: usize, max_width: u64,
        types: &[Option<SignalType<'p, 'a>>], wiring: &FuncWiring<'p, 'a>,
        signatures: &mut SignatureCache<'p, 'a>,
        calls: &[RootFunctionCall], projections: &mut CallArgumentProjections, retain: bool,
    ) -> (result: Result<(), FuncCallInputsError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
            types@.len() == wiring.drivers.definitions@.len(),
            old(signatures).matches(self, max_width),
            self.root_call_definitions_in_order(file, entry, calls@),
            old(projections).arguments@.len() == 0, old(projections).ranges@.len() == 0,
            old(projections).reference_argument_ends@.len() == 0,
            !retain ==> calls@.len() == 0,
        ensures self.prepared_call_inputs_match(file, entry, max_width, types@, wiring, result),
            final(signatures).matches(self, max_width),
            result.is_ok() ==> final(projections).ranges@.len() == calls@.len()
                && (if retain {
                    self.projected_references_match((file, entry, max_width), types@, wiring,
                        final(projections), calls@)
                } else { final(projections).reference_argument_ends@.len() == 0 && final(projections).arguments@.len() == 0 }),
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
            build_definition_reference_boundaries(source.text, &parsed.build_model(), entry as int);
            reveal(UseAliases::input_definitions_before);
            reveal(UseAliases::projected_definitions_before);
        }
        let frame = &parsed.entry_ranges[entry];
        let range = &frame.definitions;
        let stop = range.end - range.start;
        let mut cursor = 0;
        let mut definition = 0;
        while definition < stop
            invariant
                self.can_resolve(), self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
                types@.len() == wiring.drivers.definitions@.len(),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                definition <= stop == definition_count(parsed, entry as int),
                range.start + stop == range.end,
                entry < parsed.entry_ranges@.len(),
                range.start <= range.end <= parsed.definitions@.len(),
                *frame == parsed.entry_ranges@[entry as int], *range == frame.definitions,
                parsed_circuit_matches(self.targets.project_model().sources_model()[file as int], *parsed),
                frame.references.start <= frame.references.end,
                frame.references.end == if stop == 0 { frame.references.start }
                    else { parsed.definitions@[range.end - 1].references.end },
                forall|d: int| range.start <= d < range.end ==> {
                    let refs = (#[trigger] parsed.definitions@[d]).references;
                    refs.start == if d == range.start { frame.references.start } else { parsed.definitions@[d - 1].references.end }
                },
                retain ==> {
                    let ends = projections.reference_argument_ends@;
                    let boundary = if definition == 0 { frame.references.start }
                        else { parsed.definitions@[range.start + definition - 1].references.end };
                    &&& frame.references.start + ends.len() == boundary
                    &&& projections.arguments@.len() == Self::argument_boundary(ends, ends.len() as int)
                    &&& self.projected_definitions_before((file, entry, max_width), types@, wiring,
                        definition as int, ends, projections.arguments@)
                },
                !retain ==> projections.reference_argument_ends@.len() == 0 && projections.arguments@.len() == 0
                    && calls@.len() == 0,
                self.root_call_definitions_in_order(file, entry, calls@),
                file < self.targets.project_model().circuits_model().len(),
                cursor == projections.ranges@.len() <= calls@.len(),
                forall|i: int| 0 <= i < cursor ==> self.root_range_matches_reference(
                    (file, entry, max_width), calls@[i], #[trigger] projections.ranges@[i],
                    projections.reference_argument_ends@),
                forall|i: int| cursor <= i < calls@.len() ==> (#[trigger] calls@[i]).definition >= range.start + definition,
                self.input_definitions_before(file, entry, definition as int, max_width, types@, wiring),
                signatures.matches(self, max_width),
            decreases stop - definition,
        {
            let retain_root = cursor < calls.len() && calls[cursor].definition == range.start + definition;
            let start = projections.arguments.len();
            let reference_start = projections.reference_argument_ends.len();
            let ghost before_ends = projections.reference_argument_ends@;
            let ghost caller = (file, entry, max_width);
            let ghost before = projections.arguments@;
            let ghost previous_cursor = cursor;
            let ghost previous_ranges = projections.ranges@;
            let ghost refs = parsed.definitions@[range.start + definition].references;
            proof {
                let absolute = range.start + definition;
                let source = &self.targets.project_model().sources_model()[file as int];
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute);
                assert(retain ==> refs.start == frame.references.start + before_ends.len());
                assert(reference_count(parsed, entry as int, definition as int) == refs.end - refs.start);
                if retain_root {
                    assert(calls@[cursor as int].definition == absolute);
                    assert(refs.start < refs.end);
                    assert(reference_count(parsed, entry as int, definition as int) == refs.end - refs.start);
                    assert(reference_count(parsed, entry as int, definition as int) > 0);
                }
            }
            if let Err((reference, error)) = self.check_definition_input_types(file, entry, definition, max_width, types, wiring, signatures,
                &mut projections.arguments, &mut projections.reference_argument_ends, retain) {
                let position = DefinitionPosition { file, entry, definition, reference };
                let error = FuncCallInputsError::Call { position, error };
                assert(self.prepared_call_inputs_match(file, entry, max_width, types@, wiring, Err(error)));
                return Err(error);
            }
            proof {
                if !retain {
                    assert(projections.reference_argument_ends@ == before_ends);
                    assert(projections.reference_argument_ends@.take(before_ends.len() as int) =~= before_ends);
                }
                self.preserve_root_reference_ranges(caller, calls@, projections.ranges@, before_ends,
                    projections.reference_argument_ends@);
                if retain {
                    self.preserve_projected_definitions(caller, types@, wiring, definition, before_ends,
                        projections.reference_argument_ends@, before, projections.arguments@);
                }
            }
            if retain_root {
                let span = start..projections.reference_argument_ends[reference_start];
                proof {
                    let ends = projections.reference_argument_ends@;
                    assert(reference_start == before_ends.len());
                    assert(refs.start - frame.references.start == reference_start);
                    assert(Self::argument_boundary(ends, reference_start as int) == start);
                    assert(self.root_range_matches_reference(caller, calls@[cursor as int], span, ends)) by {
                        reveal(UseAliases::root_range_matches_reference);
                    };
                }
                projections.ranges.push(span);
                assert forall|i: int| 0 <= i < projections.ranges@.len() implies self.root_range_matches_reference(
                    caller, calls@[i], #[trigger] projections.ranges@[i], projections.reference_argument_ends@) by {
                    if i < previous_ranges.len() {
                        assert(projections.ranges@[i] == previous_ranges[i]);
                    } else {
                        assert(i == cursor && projections.ranges@[i] == span);
                    }
                };
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
        proof {
            assert(definition == stop);
            assert(self.prepared_call_inputs_match(file, entry, max_width, types@, wiring, Ok(())));
            if retain {
                let caller = (file, entry, max_width);
                let ends = projections.reference_argument_ends@;
                assert(frame.references.start + ends.len() == frame.references.end);
                assert(self.projected_references_match(caller, types@, wiring, projections, calls@));
            }
        }
        Ok(())
    }
}

} // verus!
