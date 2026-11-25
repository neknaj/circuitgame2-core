//! 混在プロジェクトの関数で呼び出しの入出力数を検査する。

use super::{MixedFuncCallError, MixedFuncWiringError, MixedUseAliases, ProjectSourceIndex};
use crate::project::{FuncArityError, FuncWiringResult};
use crate::project::use_aliases::call_arity::checks::{check_indexed_call_counts, check_indexed_root_count};
#[cfg(verus_only)]
use super::{mixed_use_targets_match, parsed_index_evidence, project_source_index_evidence, typed::has_mixed_func};
#[cfg(verus_only)]
use crate::project::use_aliases::{
    call_arity::checks::{at_definition, bad_root_count, call_count_error, expected_outputs, root_count_valid, target_count},
    definitions::definition_count,
};
#[cfg(verus_only)]
use crate::project::{DefinitionPosition, FuncCallArity, parsed_circuit_matches};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence};
use vstd::prelude::*;

verus! {

/// 混在プロジェクトの関数で、結線、呼び出し先の解決、入出力数の照合で見つかった違反。
#[derive(Debug)]
pub enum MixedFuncArityError<'p, 'a> {
    /// 署名、駆動元、局所信号のいずれかに違反がある。
    Wiring(MixedFuncWiringError<'p, 'a>),
    /// 呼び出し先の名前を解決できない。
    Reference(MixedFuncCallError<'p, 'a>),
    /// [`FuncArityError::ArgumentCount`] または [`FuncArityError::OutputCount`]。
    /// 式と、特定できた呼び出し先の位置を保持する。
    Count(FuncArityError<'p, 'a>),
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    spec fn mixed_ref_counts_valid(&self, at: DefinitionPosition) -> bool {
        let project = self.targets_model().project_model();
        let parsed = &project.indexes_model()[at.file as int]->Circuit_0;
        let row = at_definition(parsed, at.entry as int, at.definition as int);
        !project.has_func_callee(at.file, at.entry, at.definition, at.reference)
            || exists|call: FuncCallArity|
                #[trigger] self.mixed_func_call_arity_matches(at.file, at.entry, at.definition, at.reference, Some(Ok(call)))
                    && call.call.arguments == call.target.port_counts().inputs
                    && call.target.port_counts().outputs == expected_outputs(parsed, row, call)
    }

    spec fn mixed_ref_count_error(&self, at: DefinitionPosition, error: MixedFuncArityError) -> bool {
        let project = self.targets_model().project_model();
        let parsed = &project.indexes_model()[at.file as int]->Circuit_0;
        let row = at_definition(parsed, at.entry as int, at.definition as int);
        &&& project.has_func_callee(at.file, at.entry, at.definition, at.reference)
        &&& match error {
            MixedFuncArityError::Reference(error) =>
                self.mixed_func_call_arity_matches(at.file, at.entry, at.definition, at.reference, Some(Err(error))),
            MixedFuncArityError::Count(error) => exists|call: FuncCallArity|
                #[trigger] self.mixed_func_call_arity_matches(at.file, at.entry, at.definition, at.reference, Some(Ok(call)))
                    && call_count_error(parsed, row, call, error),
            _ => false,
        }
    }

    #[verifier::opaque]
    spec fn mixed_refs_counts_before(&self, file: usize, entry: usize, definition: usize, stop: usize) -> bool {
        forall|reference: usize| reference < stop ==> #[trigger] self.mixed_ref_counts_valid(
            DefinitionPosition { file, entry, definition, reference })
    }

    spec fn mixed_definition_arity_matches(
        &self, file: usize, entry: usize, definition: usize, result: Result<(), MixedFuncArityError>,
    ) -> bool {
        let project = self.targets_model().project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.indexes_model()[file as int]->Circuit_0;
        let row = at_definition(parsed, entry as int, definition as int);
        let stop = (row.references.end - row.references.start) as usize;
        match result {
            Ok(()) => root_count_valid(source, parsed, row) && self.mixed_refs_counts_before(file, entry, definition, stop),
            Err(error) => (error matches MixedFuncArityError::Count(error) && bad_root_count(source, parsed, row, error))
                || (root_count_valid(source, parsed, row)
                    && exists|reference: usize| reference < stop
                        && #[trigger] self.mixed_refs_counts_before(file, entry, definition, reference)
                        && self.mixed_ref_count_error(DefinitionPosition { file, entry, definition, reference }, error)),
        }
    }

    fn check_mixed_definition_arity(&self, file: usize, entry: usize, definition: usize)
        -> (result: Result<(), MixedFuncArityError<'p, 'a>>)
        requires
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
            self.targets_model().project_model().has_source_indexes(),
            has_mixed_func(&self.targets_model().project_model(), file, entry),
            definition < definition_count(&self.targets_model().project_model().indexes_model()[file as int]->Circuit_0, entry as int),
        ensures self.mixed_definition_arity_matches(file, entry, definition, result),
    {
        let project = self.targets().project();
        let source = &project.sources()[file];
        let indexed = &project.indexes()[file];
        let ProjectSourceIndex::Circuit(parsed) = indexed else { unreachable!() };
        let ghost model = parsed.build_model();
        proof {
            project_source_index_evidence(*source, *indexed);
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, entry as int);
        }
        let absolute = parsed.entry_ranges[entry].definitions.start + definition;
        let row = &parsed.definitions[absolute];
        proof { build_definition_scope_evidence(source.text, &model, entry as int, absolute as int); }
        let count = match check_indexed_root_count(source, parsed, row) {
            Ok(count) => count,
            Err(error) => return Err(MixedFuncArityError::Count(error)),
        };
        let stop = row.references.end - row.references.start;
        let mut reference = 0;
        proof { reveal(MixedUseAliases::mixed_refs_counts_before); }
        while reference < stop
            invariant
                mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
                self.targets_model().project_model().has_source_indexes(),
                *project == self.targets_model().project_model(),
                has_mixed_func(project, file, entry), parsed_circuit_matches(*source, *parsed),
                *source == project.sources_model()[file as int], *parsed == project.indexes_model()[file as int]->Circuit_0,
                *row == at_definition(parsed, entry as int, definition as int),
                row.form + 2 < parsed.syntax.forms@.len(), row.references.start <= row.references.end,
                count == target_count(parsed, *row), root_count_valid(source, parsed, *row),
                stop == row.references.end - row.references.start, reference <= stop,
                self.mixed_refs_counts_before(file, entry, definition, reference),
            decreases stop - reference,
        {
            let ghost at = DefinitionPosition { file, entry, definition, reference };
            match self.resolve_mixed_func_call_arity(file, entry, definition, reference) {
                Some(Ok(call)) => {
                    proof { self.mixed_func_call_arity_origin(file, entry, definition, reference, call); }
                    let ghost checked = call;
                    if let Err(error) = check_indexed_call_counts(source, parsed, row, count, call) {
                        let error = MixedFuncArityError::Count(error);
                        assert(self.mixed_ref_count_error(at, error));
                        return Err(error);
                    }
                    assert(self.mixed_ref_counts_valid(at));
                },
                Some(Err(error)) => {
                    let error = MixedFuncArityError::Reference(error);
                    assert(self.mixed_ref_count_error(at, error));
                    return Err(error);
                },
                None => { assert(self.mixed_ref_counts_valid(at)); },
            }
            proof {
                reveal(MixedUseAliases::mixed_refs_counts_before);
                assert forall|prior: usize| prior <= reference implies #[trigger] self.mixed_ref_counts_valid(
                    DefinitionPosition { file, entry, definition, reference: prior }) by {};
            }
            reference += 1;
        }
        Ok(())
    }

    #[verifier::opaque]
    spec fn mixed_definitions_arity_before(&self, file: usize, entry: usize, stop: int) -> bool {
        forall|definition: usize| definition < stop
            ==> #[trigger] self.mixed_definition_arity_matches(file, entry, definition, Ok(()))
    }

    /// 最初の個数の違反が同じ結線と定義・参照の順に対応することを表す。
    pub closed spec fn mixed_func_arity_matches(
        &self, file: usize, entry: usize, max_width: u64, result: Result<FuncWiringResult, MixedFuncArityError>,
    ) -> bool {
        let project = self.targets_model().project_model();
        let count = definition_count(&project.indexes_model()[file as int]->Circuit_0, entry as int);
        match result {
            Ok(wiring) => self.mixed_func_wiring_matches(file, entry, max_width, Ok(wiring))
                && (wiring is Checked ==> self.mixed_definitions_arity_before(file, entry, count)),
            Err(MixedFuncArityError::Wiring(error)) => self.mixed_func_wiring_matches(file, entry, max_width, Err(error)),
            Err(error) => {
                &&& exists|wiring: FuncWiringResult| wiring is Checked
                    && #[trigger] self.mixed_func_wiring_matches(file, entry, max_width, Ok(wiring))
                &&& exists|definition: usize| definition < count
                    && #[trigger] self.mixed_definitions_arity_before(file, entry, definition as int)
                    && self.mixed_definition_arity_matches(file, entry, definition, Err(error))
            },
        }
    }

    /// 個数検査を通った結果が同じ関数の結線検査にも対応することを示す。
    pub proof fn mixed_arity_preserves_wiring(&self, file: usize, entry: usize, max_width: u64, wiring: FuncWiringResult)
        requires self.mixed_func_arity_matches(file, entry, max_width, Ok(wiring)),
        ensures self.mixed_func_wiring_matches(file, entry, max_width, Ok(wiring)),
    {}

    /// 混在プロジェクトで結線を検査し、各 `def` の右辺と呼び出しの入出力数を照合する。
    ///
    /// 右辺全体の出力数は左辺の名前の数に、子式の出力数は 1 にそろえる。
    /// 対象外と展開待ちは結線検査から引き継ぐ。型と幅は後続の検査で確かめる。
    ///
    /// # Errors
    ///
    /// 結線の違反を先に返す。定義は元ソース順に調べ、右辺全体が通常呼び出しでなければ
    /// 出力数を先に確認する。通常呼び出しは元ソース順に、名前解決、引数数、出力数を調べる。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{FuncArityError, FuncCallTarget, FuncWiringResult, MixedFuncArityError,
    ///     SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources};
    ///
    /// let design = "(func good (in a b) (out x y) (def (x y) (::lib::pair a b)))
    ///     (func nested (in a b) (out y) (def y (nor (::lib::pair a b) a)))
    ///     (func too_few (in a) (out y) (def y (::lib::pair a)))";
    /// let library = "(namespace lib (export pair) (func pair (in a b) (out a b)))";
    /// let project = parse_project_sources(&[
    ///     SourceSnapshot { path: "design.ncg2", revision: 21, text: design },
    ///     SourceSnapshot { path: "library.ncg2", revision: 6, text: library },
    ///     SourceSnapshot { path: "helper.ncg2m", revision: 4,
    ///         text: "(defn ready (as-type (Fn () Bool) (fn () true)))" },
    /// ]).unwrap();
    /// let targets = index_mixed_use_targets(&project).unwrap();
    /// let aliases = check_mixed_use_aliases(&targets).unwrap();
    /// assert!(matches!(aliases.check_mixed_func_arity(0, 0, 64), Ok(FuncWiringResult::Checked(_))));
    /// let Err(MixedFuncArityError::Count(FuncArityError::OutputCount { expression, left: None,
    ///     callee: Some(FuncCallTarget::Function { declaration, .. }), expected: 1, actual: 2 })) =
    ///     aliases.check_mixed_func_arity(0, 1, 64) else { panic!() };
    /// assert_eq!((&design[expression.span], expression.source.revision), ("(::lib::pair a b)", 21));
    /// assert_eq!((&library[declaration.span], declaration.source.revision), ("pair", 6));
    /// assert!(matches!(aliases.check_mixed_func_arity(0, 2, 64),
    ///     Err(MixedFuncArityError::Count(FuncArityError::ArgumentCount { expected: 2, actual: 1, .. }))));
    /// ```
    pub fn check_mixed_func_arity(&self, file: usize, entry: usize, max_width: u64)
        -> (result: Result<FuncWiringResult<'p, 'a>, MixedFuncArityError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures self.mixed_func_arity_matches(file, entry, max_width, result),
    {
        let wiring = match self.check_mixed_func_wiring(file, entry, max_width) {
            Ok(wiring) => wiring,
            Err(error) => return Err(MixedFuncArityError::Wiring(error)),
        };
        let FuncWiringResult::Checked(ref _checked) = wiring else { return Ok(wiring); };
        proof { self.mixed_wiring_index_origin(file, entry, max_width, *_checked); }
        let project = self.targets().project();
        let index = &project.indexes()[file];
        let ProjectSourceIndex::Circuit(parsed) = index else { unreachable!() };
        proof {
            let source = &project.sources_model()[file as int];
            project_source_index_evidence(*source, *index);
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
            reveal(MixedUseAliases::mixed_definitions_arity_before);
        }
        let range = &parsed.entry_ranges[entry].definitions;
        let stop = range.end - range.start;
        let mut definition = 0;
        while definition < stop
            invariant
                mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
                project.has_source_indexes(), *project == self.targets_model().project_model(),
                has_mixed_func(project, file, entry), *parsed == project.indexes_model()[file as int]->Circuit_0,
                self.mixed_func_wiring_matches(file, entry, max_width, Ok(wiring)), wiring is Checked,
                stop == definition_count(parsed, entry as int), definition <= stop,
                self.mixed_definitions_arity_before(file, entry, definition as int),
            decreases stop - definition,
        {
            if let Err(error) = self.check_mixed_definition_arity(file, entry, definition) {
                return Err(error);
            }
            proof {
                reveal(MixedUseAliases::mixed_definitions_arity_before);
                assert forall|prior: usize| prior <= definition
                    implies #[trigger] self.mixed_definition_arity_matches(file, entry, prior, Ok(())) by {};
            }
            definition += 1;
        }
        Ok(wiring)
    }
}

}
