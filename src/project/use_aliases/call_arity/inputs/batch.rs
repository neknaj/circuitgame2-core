//! 関数の配線と型を共有し、右辺に現れる呼び出しの引数を検査する。

use super::{CallInputError, FuncAtomTypeError, FuncAtomTypes, FuncWiring, FuncWiringResult, UseAliases};
use crate::project::DefinitionPosition;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::project::use_aliases::definitions::{definition_count, reference_count};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence};
use vstd::prelude::*;

verus! {

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
        typed: &FuncAtomTypes, wiring: &FuncWiring,
    ) -> bool {
        exists|value: Option<super::CheckedCallInputs>|
            #[trigger] self.scoped_input_result(file, entry, definition, reference, limit, typed, wiring, false, Ok(value))
    }

    #[verifier::opaque]
    spec fn input_refs_before(
        &self, file: usize, entry: usize, definition: usize, stop: int, limit: u64,
        typed: &FuncAtomTypes, wiring: &FuncWiring,
    ) -> bool {
        forall|reference: usize| reference < stop
            ==> #[trigger] self.input_ref_valid(file, entry, definition, reference, limit, typed, wiring)
    }

    #[verifier::opaque]
    spec fn input_definitions_before(
        &self, file: usize, entry: usize, stop: int, limit: u64, typed: &FuncAtomTypes, wiring: &FuncWiring,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        forall|definition: usize| definition < stop ==> #[trigger] self.input_refs_before(
            file, entry, definition, reference_count(parsed, entry as int, definition as int),
            limit, typed, wiring)
    }

    /// 呼び出し元の検査と、定義順・参照順で最初に見つかる引数の違反を表す。
    pub closed spec fn all_func_call_inputs_evidence(
        &self, file: usize, entry: usize, limit: u64, result: Result<FuncAtomTypes, FuncCallInputsError>,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let count = definition_count(parsed, entry as int);
        match result {
            Ok(typed) => self.func_atom_type_evidence(file, entry, limit, Ok(typed))
                && (typed.literals.wiring matches FuncWiringResult::Checked(wiring) ==>
                    self.input_definitions_before(file, entry, count, limit, &typed, &wiring)),
            Err(FuncCallInputsError::Caller(error)) => self.func_atom_type_evidence(file, entry, limit, Err(error)),
            Err(FuncCallInputsError::Call { position, error }) =>
                position.file == file && position.entry == entry && position.definition < count
                && position.reference < reference_count(parsed, entry as int, position.definition as int)
                && exists|typed: FuncAtomTypes| typed.literals.wiring matches FuncWiringResult::Checked(wiring)
                    && #[trigger] self.func_atom_type_evidence(file, entry, limit, Ok(typed))
                    && self.input_definitions_before(file, entry, position.definition as int, limit, &typed, &wiring)
                    && self.input_refs_before(file, entry, position.definition, position.reference as int, limit, &typed, &wiring)
                    && self.scoped_input_result(file, entry, position.definition, position.reference, limit,
                        &typed, &wiring, false, Err(error)),
        }
    }

    fn check_definition_input_types(
        &self, file: usize, entry: usize, definition: usize, max_width: u64,
        typed: &FuncAtomTypes<'p, 'a>, wiring: &FuncWiring<'p, 'a>,
    ) -> (result: Result<(), (usize, CallInputError<'p, 'a>)>)
        requires
            self.can_resolve(),
            self.func_atom_type_evidence(file, entry, max_width, Ok(*typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*wiring),
            definition < definition_count(&self.targets.project_model().circuits_model()[file as int], entry as int),
        ensures ({
            let parsed = &self.targets.project_model().circuits_model()[file as int];
            let count = reference_count(parsed, entry as int, definition as int);
            match result {
                Ok(()) => self.input_refs_before(file, entry, definition, count, max_width, typed, wiring),
                Err((reference, error)) => reference < count
                    && self.input_refs_before(file, entry, definition, reference as int, max_width, typed, wiring)
                    && self.scoped_input_result(file, entry, definition, reference, max_width, typed, wiring, false, Err(error)),
            }
        }),
    {
        let project = self.targets.project();
        proof {
            self.atom_types_keep_wiring(file, entry, max_width, *typed, *wiring);
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
                self.can_resolve(), self.func_atom_type_evidence(file, entry, max_width, Ok(*typed)),
                typed.literals.wiring == FuncWiringResult::Checked(*wiring),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                reference <= stop == reference_count(parsed, entry as int, definition as int),
                self.input_refs_before(file, entry, definition, reference as int, max_width, typed, wiring),
            decreases stop - reference,
        {
            let _value = match self.check_call_inputs_with_types(file, entry, definition, reference, max_width, typed, wiring, false) {
                Ok(value) => value,
                Err(error) => return Err((reference, error)),
            };
            proof {
                reveal(UseAliases::input_refs_before);
                assert forall|prior: usize| prior <= reference
                    implies #[trigger] self.input_ref_valid(file, entry, definition, prior, max_width, typed, wiring) by {
                    if prior == reference {
                        assert(self.scoped_input_result(file, entry, definition, prior, max_width, typed, wiring, false, Ok(_value)));
                    } else {
                        assert(self.input_ref_valid(file, entry, definition, prior, max_width, typed, wiring));
                    }
                };
            }
            reference += 1;
        }
        Ok(())
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
        let project = self.targets.project();
        proof {
            self.atom_types_keep_wiring(file, entry, max_width, typed, *wiring);
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
        let mut definition = 0;
        while definition < stop
            invariant
                self.can_resolve(), self.func_atom_type_evidence(file, entry, max_width, Ok(typed)),
                typed.literals.wiring == FuncWiringResult::Checked(*wiring),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                definition <= stop == definition_count(parsed, entry as int),
                self.input_definitions_before(file, entry, definition as int, max_width, &typed, wiring),
            decreases stop - definition,
        {
            if let Err((reference, error)) = self.check_definition_input_types(file, entry, definition, max_width, &typed, wiring) {
                let position = DefinitionPosition { file, entry, definition, reference };
                return Err(FuncCallInputsError::Call { position, error });
            }
            proof {
                reveal(UseAliases::input_definitions_before);
                assert forall|prior: usize| prior <= definition implies #[trigger] self.input_refs_before(
                    file, entry, prior, reference_count(parsed, entry as int, prior as int), max_width, &typed, wiring)
                by {
                    if prior < definition {
                        assert(self.input_refs_before(file, entry, prior,
                            reference_count(parsed, entry as int, prior as int), max_width, &typed, wiring));
                    }
                };
            }
            definition += 1;
        }
        Ok(typed)
    }
}

} // verus!
