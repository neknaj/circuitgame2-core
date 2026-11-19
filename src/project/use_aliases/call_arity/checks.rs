//! 配線を確認した関数について、右辺と呼び出しのポート数を検査する。

use super::{DefinitionReferenceError, FuncCallTarget, UseAliases};
#[cfg(verus_only)]
use super::FuncCallArity;
#[cfg(verus_only)]
use super::super::definitions::definition_count;
use crate::project::{FuncWiringError, FuncWiringResult, LocatedName, ProjectSource};
#[cfg(verus_only)]
use crate::project::DefinitionPosition;
#[cfg(verus_only)]
use crate::project::circuits::{parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::project::declarations::located_name_evidence;
#[cfg(verus_only)]
use crate::project::location_in_source;
use crate::syntax::{Form, circuit::{definition_root_is_call, definition_target_atoms}};
#[cfg(verus_only)]
use crate::syntax::{
    circuit::{BuildDefinition, NamedBuildCircuit, build_definition_scope_evidence,
        build_entry_ranges_evidence, definition_target_range, ordinary_call_at},
    form_span, form_spans_valid,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 配線の検査、呼び出し先の解決、または入出力数の照合で見つかった違反。
#[derive(Debug)]
pub enum FuncArityError<'p, 'a> {
    /// 出力の駆動元または局所信号の束縛に違反がある。
    Wiring(FuncWiringError<'p, 'a>),
    /// 呼び出し先の名前を解決できない。
    Reference(DefinitionReferenceError<'p, 'a>),
    /// 実引数の数が、呼び出し先の入力ポート数と一致しない。
    ArgumentCount {
        /// 呼び出し全体の範囲。
        call: LocatedName<'p, 'a>,
        /// 名前解決で選んだ参照先。関数の場合は宣言位置を含む。
        target: FuncCallTarget<'p, 'a>,
        /// 呼び出し先が要求する入力数。
        expected: usize,
        /// 呼び出しに書かれた直接の引数数。
        actual: usize,
    },
    /// 式の出力数が、その式を使う箇所が要求する数と一致しない。
    OutputCount {
        /// 出力数が合わない式全体の範囲。
        expression: LocatedName<'p, 'a>,
        /// 右辺全体を検査した場合は左辺の範囲。子式では `None`。
        left: Option<LocatedName<'p, 'a>>,
        /// 通常呼び出しの場合は、名前解決で選んだ参照先。
        callee: Option<FuncCallTarget<'p, 'a>>,
        /// 左辺の名前の数。子式の場合は 1。
        expected: usize,
        /// 式が返す出力の数。
        actual: usize,
    },
}

spec fn at_definition(parsed: &NamedBuildCircuit, entry: int, definition: int) -> BuildDefinition {
    parsed.definitions@[parsed.entry_ranges@[entry].definitions.start + definition]
}

spec fn target_count(parsed: &NamedBuildCircuit, row: BuildDefinition) -> int {
    let (start, end) = definition_target_range(parsed.syntax.forms@, row);
    end - start
}

spec fn is_form_location(source: &ProjectSource, form: Form, loc: LocatedName) -> bool {
    *loc.source == *source && loc.span == form_span(form) && location_in_source(loc)
}

fn form_location<'p, 'a>(source: &'p ProjectSource<'a>, forms: &[Form], index: usize)
    -> (loc: LocatedName<'p, 'a>)
    requires
        index < forms@.len(),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures is_form_location(source, forms@[index as int], loc),
{
    let source_span = match &forms[index] {
        Form::Atom { span: atom, .. } => atom,
        Form::List { span: list, .. } => list,
    };
    let loc = LocatedName { source, span: source_span.start..source_span.end };
    proof {
        reveal(form_spans_valid);
        assert(loc.span == form_span(forms@[index as int]));
        located_name_evidence(loc);
    }
    loc
}

spec fn root_count_valid(source: &ProjectSource, parsed: &NamedBuildCircuit, row: BuildDefinition) -> bool {
    ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int)
        || target_count(parsed, row) == 1
}

spec fn bad_root_count(
    source: &ProjectSource, parsed: &NamedBuildCircuit, row: BuildDefinition, error: FuncArityError,
) -> bool {
    &&& !root_count_valid(source, parsed, row)
    &&& error matches FuncArityError::OutputCount { expression, left: Some(left), callee: None, expected, actual }
    &&& expected == target_count(parsed, row) && actual == 1
    &&& is_form_location(source, parsed.syntax.forms@[row.expression.start as int], expression)
    &&& is_form_location(source, parsed.syntax.forms@[row.form + 2], left)
}

spec fn expected_outputs(parsed: &NamedBuildCircuit, row: BuildDefinition, call: FuncCallArity) -> int {
    if call.call.form == row.expression.start { target_count(parsed, row) } else { 1 }
}

spec fn call_location(call: FuncCallArity, loc: LocatedName) -> bool {
    *loc.source == *call.source && loc.span == call.call.span && location_in_source(loc)
}

spec fn call_count_error(
    parsed: &NamedBuildCircuit, row: BuildDefinition, call: FuncCallArity, error: FuncArityError,
) -> bool {
    let ports = call.target.port_counts();
    match error {
        FuncArityError::ArgumentCount { call: loc, target, expected, actual } =>
            call_location(call, loc) && target == call.target
                && expected == ports.inputs && actual == call.call.arguments && expected != actual,
        FuncArityError::OutputCount { expression, left, callee: Some(callee), expected, actual } =>
            call_location(call, expression) && callee == call.target && call.call.arguments == ports.inputs
                && expected == expected_outputs(parsed, row, call) && actual == ports.outputs && expected != actual
                && if call.call.form == row.expression.start {
                    left matches Some(left) && is_form_location(call.source, parsed.syntax.forms@[row.form + 2], left)
                } else { left is None },
        _ => false,
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn arity_func(&self, file: usize, entry: usize) -> bool {
        let project = self.targets.project_model();
        let circuits = project.circuits_model();
        &&& file < circuits.len() && file < project.sources_model().len()
        &&& entry < circuits[file as int].syntax.entries@.len()
        &&& circuits[file as int].syntax.entries@[entry as int].head is Func
    }

    spec fn ref_count_valid(
        &self, at: DefinitionPosition, parsed: &NamedBuildCircuit, row: BuildDefinition,
    ) -> bool {
        !self.func_call_at(at.file, at.entry, at.definition, at.reference)
            || exists|call: FuncCallArity|
                #[trigger] self.func_call_arity_evidence(at.file, at.entry, at.definition, at.reference, Ok(Some(call)))
                    && call.call.arguments == call.target.port_counts().inputs
                    && call.target.port_counts().outputs == expected_outputs(parsed, row, call)
    }

    spec fn bad_ref_count(
        &self, at: DefinitionPosition, parsed: &NamedBuildCircuit, row: BuildDefinition, error: FuncArityError,
    ) -> bool {
        self.func_call_at(at.file, at.entry, at.definition, at.reference)
            && match error {
                FuncArityError::Reference(error) =>
                    self.func_call_arity_evidence(at.file, at.entry, at.definition, at.reference, Err(error)),
                _ => exists|call: FuncCallArity|
                    #[trigger] self.func_call_arity_evidence(at.file, at.entry, at.definition, at.reference, Ok(Some(call)))
                        && call_count_error(parsed, row, call, error),
            }
    }

    proof fn record_count_mismatch(
        &self, at: DefinitionPosition, parsed: &NamedBuildCircuit, row: BuildDefinition,
        call: FuncCallArity, error: FuncArityError,
    )
        requires
            self.func_call_at(at.file, at.entry, at.definition, at.reference),
            self.func_call_arity_evidence(at.file, at.entry, at.definition, at.reference, Ok(Some(call))),
            call_count_error(parsed, row, call, error),
        ensures self.bad_ref_count(at, parsed, row, error),
    {
        assert(!(error is Reference));
        assert(exists|witness: FuncCallArity|
            #[trigger] self.func_call_arity_evidence(at.file, at.entry, at.definition, at.reference, Ok(Some(witness)))
                && call_count_error(parsed, row, witness, error)) by {
            assert(self.func_call_arity_evidence(at.file, at.entry, at.definition, at.reference, Ok(Some(call))));
        };
    }

    #[verifier::opaque]
    spec fn definition_refs_valid(
        &self, file: usize, entry: usize, definition: usize, stop: int,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let row = at_definition(parsed, entry as int, definition as int);
        &&& 0 <= stop <= row.references.end - row.references.start
        &&& forall|reference: usize| reference < stop ==> #[trigger] self.ref_count_valid(
            DefinitionPosition { file, entry, definition, reference }, parsed, row)
    }

    spec fn definition_arity_result(
        &self, file: usize, entry: usize, definition: usize, result: Result<(), FuncArityError>,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let row = at_definition(parsed, entry as int, definition as int);
        match result {
            Ok(()) => root_count_valid(source, parsed, row)
                && self.definition_refs_valid(file, entry, definition, row.references.end - row.references.start),
            Err(error) => bad_root_count(source, parsed, row, error)
                || (root_count_valid(source, parsed, row)
                    && exists|reference: usize| reference < row.references.end - row.references.start
                        && #[trigger] self.definition_refs_valid(file, entry, definition, reference as int)
                        && self.bad_ref_count(DefinitionPosition { file, entry, definition, reference }, parsed, row, error)),
        }
    }

    fn check_definition_arity(
        &self, file: usize, entry: usize, definition: usize,
    ) -> (result: Result<(), FuncArityError<'p, 'a>>)
        requires
            self.can_resolve(), self.arity_func(file, entry),
            definition < definition_count(
                &self.targets.project_model().circuits_model()[file as int], entry as int),
        ensures self.definition_arity_result(file, entry, definition, result),
    {
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let forms = parsed.syntax.forms.as_slice();
        let ghost row_model = at_definition(parsed, entry as int, definition as int);
        let ghost index = parsed.build_model();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &index, entry as int);
            build_definition_scope_evidence(source.text, &index, entry as int,
                parsed.entry_ranges@[entry as int].definitions.start + definition);
        }
        let row = &parsed.definitions[parsed.entry_ranges[entry].definitions.start + definition];
        let targets = definition_target_atoms(forms, row);
        let count = targets.end - targets.start;
        if !definition_root_is_call(source.text, forms, row, parsed.references.as_slice()) && count != 1 {
            let expression = form_location(source, forms, row.expression.start);
            let left = form_location(source, forms, row.form + 2);
            return Err(FuncArityError::OutputCount { expression, left: Some(left), callee: None, expected: count, actual: 1 });
        }
        let mut reference = 0;
        let stop = row.references.end - row.references.start;
        proof { reveal(UseAliases::definition_refs_valid); }
        while reference < stop
            invariant
                self.can_resolve(), self.arity_func(file, entry), parsed_circuit_matches(*source, *parsed),
                *source == project.sources_model()[file as int], *project == self.targets.project_model(),
                *parsed == project.circuits_model()[file as int], forms@ == parsed.syntax.forms@,
                row_model == at_definition(parsed, entry as int, definition as int), *row == row_model,
                row.form + 2 < forms@.len(), row.expression.start < forms@.len(),
                row.references.end <= parsed.references@.len(),
                row.references.start <= row.references.end,
                definition < definition_count(parsed, entry as int),
                count == target_count(parsed, *row),
                root_count_valid(source, parsed, *row),
                stop == row.references.end - row.references.start,
                reference <= stop,
                self.definition_refs_valid(file, entry, definition, reference as int),
            decreases stop - reference,
        {
            let ghost at = DefinitionPosition { file, entry, definition, reference };
            let resolution = self.resolve_func_call_arity(file, entry, definition, reference);
            match resolution {
                Err(error) => {
                    let error = FuncArityError::Reference(error);
                    assert(self.bad_ref_count(at, parsed, *row, error));
                    return Err(error);
                },
                Ok(Some(call)) => {
                    let ghost resolved = call;
                    assert(self.func_call_arity_evidence(file, entry, definition, reference, Ok(Some(resolved))));
                    assert(self.func_call_at(file, entry, definition, reference));
                    let ports = call.target.ports();
                    let loc = LocatedName { source: call.source, span: call.call.span };
                    if call.call.arguments != ports.inputs {
                        let error = FuncArityError::ArgumentCount {
                            call: loc, target: call.target, expected: ports.inputs, actual: call.call.arguments,
                        };
                        assert(call_count_error(parsed, *row, resolved, error));
                        proof { self.record_count_mismatch(at, parsed, *row, resolved, error); }
                        return Err(error);
                    }
                    let root = call.call.form == row.expression.start;
                    let expected = if root { count } else { 1 };
                    if ports.outputs != expected {
                        proof { parsed_index_evidence(*source, *parsed); }
                        let left = if root { Some(form_location(source, forms, row.form + 2)) } else { None };
                        let error = FuncArityError::OutputCount {
                            expression: loc, left, callee: Some(call.target), expected, actual: ports.outputs,
                        };
                        assert(call_count_error(parsed, *row, resolved, error));
                        proof { self.record_count_mismatch(at, parsed, *row, resolved, error); }
                        return Err(error);
                    }
                    assert(self.ref_count_valid(at, parsed, *row));
                },
                Ok(None) => { assert(self.ref_count_valid(at, parsed, *row)); },
            }
            proof {
                reveal(UseAliases::definition_refs_valid);
                assert forall|prior: usize| prior <= reference implies #[trigger] self.ref_count_valid(
                    DefinitionPosition { file, entry, definition, reference: prior }, parsed, *row) by {
                    if prior < reference {
                        assert(self.ref_count_valid(DefinitionPosition { file, entry, definition, reference: prior }, parsed, *row));
                    }
                };
            }
            reference += 1;
        }
        Ok(())
    }

    #[verifier::opaque]
    spec fn definitions_count_before(&self, file: usize, entry: usize, stop: int) -> bool {
        forall|definition: usize| definition < stop
            ==> #[trigger] self.definition_arity_result(file, entry, definition, Ok(()))
    }

    /// 結果が配線の検査と入出力数の規則を満たすか、最初の違反に対応することを表す。
    pub closed spec fn func_arity_evidence(
        &self, file: usize, entry: usize, max_width: u64, result: Result<FuncWiringResult, FuncArityError>,
    ) -> bool {
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let count = definition_count(parsed, entry as int);
        match result {
            Err(FuncArityError::Wiring(error)) =>
                self.func_wiring_evidence(file, entry, max_width, Err(error)),
            Ok(wiring) => self.func_wiring_evidence(file, entry, max_width, Ok(wiring))
                && (wiring is Checked ==> self.arity_func(file, entry)
                    && self.definitions_count_before(file, entry, count)),
            Err(error) => self.arity_func(file, entry)
                && (exists|wiring: FuncWiringResult| wiring is Checked
                    && #[trigger] self.func_wiring_evidence(file, entry, max_width, Ok(wiring)))
                && exists|definition: usize| definition < count
                    && #[trigger] self.definitions_count_before(file, entry, definition as int)
                    && self.definition_arity_result(file, entry, definition, Err(error)),
        }
    }

    /// 配線を検査した後、`func` の右辺の入出力数を確かめる。
    ///
    /// 右辺全体の出力数は左辺の名前の数に、子式の出力数は 1 にそろえる。
    /// 対象外と展開待ちは配線検査の結果を引き継ぐ。幅と型の適合は後続の検査で確かめる。
    ///
    /// # Errors
    ///
    /// 配線の違反を先に返す。定義は元ソース順に調べ、右辺全体が通常呼び出しでなければ
    /// 出力数を先に確認する。通常呼び出しは元ソース順に、名前解決、引数数、出力数を調べる。
    pub fn check_func_arity(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncWiringResult<'p, 'a>, FuncArityError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_arity_evidence(file, entry, max_width, result),
    {
        let wiring = match self.check_func_wiring(file, entry, max_width) {
            Ok(result) => result,
            Err(error) => return Err(FuncArityError::Wiring(error)),
        };
        let FuncWiringResult::Checked(ref _checked) = wiring else { return Ok(wiring); };
        proof { self.checked_wiring_is_func(file, entry, max_width, *_checked); }
        let project = self.targets.project();
        let parsed = &project.circuits()[file];
        proof {
            let source = &project.sources_model()[file as int];
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
            reveal(UseAliases::definitions_count_before);
        }
        let range = &parsed.entry_ranges[entry].definitions;
        let stop = range.end - range.start;
        let mut definition = 0;
        while definition < stop
            invariant
                self.can_resolve(), self.arity_func(file, entry),
                self.func_wiring_evidence(file, entry, max_width, Ok(wiring)),
                wiring is Checked,
                stop == definition_count(parsed, entry as int),
                *parsed == self.targets.project_model().circuits_model()[file as int],
                definition <= stop,
                self.definitions_count_before(file, entry, definition as int),
            decreases stop - definition,
        {
            if let Err(error) = self.check_definition_arity(file, entry, definition) {
                return Err(error);
            }
            proof {
                reveal(UseAliases::definitions_count_before);
                assert forall|prior: usize| prior <= definition
                    implies #[trigger] self.definition_arity_result(file, entry, prior, Ok(())) by {
                    if prior < definition {
                        assert(self.definition_arity_result(file, entry, prior, Ok(())));
                    }
                };
            }
            definition += 1;
        }
        Ok(wiring)
    }
}

} // verus!
