//! 実引数の位置から、内側の通常呼び出しが返す単一出力の型を取得する。

use super::*;
use crate::syntax::circuit::{BuildDefinition, callee_reference_at_form};
#[cfg(verus_only)]
use crate::syntax::circuit::{definition_call_index, ordinary_call_at};

verus! {

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    pub(super) closed spec fn mixed_nested_argument(
        &self, caller: (usize, usize, usize), source: &ProjectSource, parsed: &NamedBuildCircuit,
        row: BuildDefinition, root: usize, limit: u64, known: Option<SignalType>,
    ) -> bool {
        let (file, entry, definition) = caller;
        let forms = parsed.syntax.forms@;
        if row.expression.start <= root < row.expression.end
            && ordinary_call_at(source.text_model(), forms, root as int, row.expression.end as int) {
            exists|reference: usize, call: FuncCallArity| {
                &&& #[trigger] self.mixed_checked_call(DefinitionPosition { file, entry, definition, reference }, call)
                &&& reference < row.references.end - row.references.start
                &&& call.call.form == root
                &&& call.target.port_counts().outputs == 1
                &&& match known {
                    Some(ty) => self.mixed_call_returns_type(call, limit, 0, ty),
                    None => exists|error: MixedFuncTypeError| #[trigger] self.mixed_target_signature_failure(call, limit, error),
                }
            }
        } else { known.is_none() }
    }

    #[verifier::spinoff_prover]
    pub(super) fn nested_mixed_output(
        &self, caller: (usize, usize, usize), source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>,
        row: &BuildDefinition, _parent_reference: Ghost<usize>, rows: &[(usize, FuncCallArity<'p, 'a>)], root: usize, limit: u64,
        signatures: &mut SignatureCache<'p, 'a>,
    ) -> (known: Option<SignalType<'p, 'a>>)
        requires
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
            ({
                let project = self.targets_model().project_model();
                let (file, entry, definition) = caller;
                &&& project.has_func_callee(file, entry, definition, _parent_reference@)
                &&& *source == project.sources_model()[file as int]
                &&& *parsed == project.indexes_model()[file as int]->Circuit_0
                &&& *row == crate::project::use_aliases::call_arity::checks::at_definition(parsed, entry as int, definition as int)
            }),
            row.expression.start < root < row.expression.end,
            definition_call_index(source.text, parsed.syntax.forms@, *row, parsed.references@),
            self.retained_definition_calls(caller.0, caller.1, caller.2, (row.references.end - row.references.start) as usize, rows@),
            old(signatures).matches_mixed(self, limit),
        ensures
            self.mixed_nested_argument(caller, source, parsed, *row, root, limit, known),
            final(signatures).matches_mixed(self, limit),
            forall|place: (usize, usize)| #[trigger] old(signatures).signatures().contains_key(place) ==>
                final(signatures).signatures().contains_key(place)
                    && final(signatures).signatures()[place] == old(signatures).signatures()[place],
    {
        let (file, entry, definition) = caller;
        proof {
            reveal(MixedUseAliases::mixed_nested_argument);
            source.text_model_is_text();
        }
        let Some(absolute) = callee_reference_at_form(source.text, parsed.syntax.forms.as_slice(),
            row, parsed.references.as_slice(), root) else { return None; };
        let reference = absolute - row.references.start;
        let _at = DefinitionPosition { file, entry, definition, reference };
        proof {
            let project = self.targets_model().project_model();
            assert(project.has_func_callee(file, entry, definition, _parent_reference@));
            let frame = parsed.entry_ranges@[entry as int].definitions;
            assert(frame.start + definition < frame.end);
            assert(row.references.start + reference == absolute);
            assert(absolute < parsed.references@.len());
            assert(parsed.references@[absolute as int].kind is Callee);
            assert(project.has_func_callee(file, entry, definition, reference));
        }
        let Some(call) = retained_call_at(rows, reference) else { unreachable!() };
        proof {
            assert(self.mixed_checked_call(_at, *call));
            self.mixed_func_call_arity_origin(file, entry, definition, reference, *call);
            assert(call.call.form == root);
            assert(call.target.port_counts().outputs == 1);
        }
        // 子の署名エラーは、参照順にその子自身を検査するときに返す。
        let resolution = self.prepare_mixed_call_signature(Ghost(_at), call, limit, signatures);
        if let Err(error) = resolution {
            proof { self.record_nested_output(caller, source, parsed, *row, root, limit, reference, *call, None, Some(error)); }
            return None;
        }
        let typed = self.read_mixed_cached_output(call, limit, 0, signatures);
        proof { self.record_nested_output(caller, source, parsed, *row, root, limit, reference, *call, Some(typed), None); }
        Some(typed)
    }

    proof fn record_nested_output(&self, caller: (usize, usize, usize), source: &ProjectSource,
        parsed: &NamedBuildCircuit, row: BuildDefinition, root: usize, limit: u64, reference: usize,
        call: FuncCallArity, known: Option<SignalType>, failure: Option<MixedFuncTypeError>)
        requires
            row.expression.start <= root < row.expression.end,
            ordinary_call_at(source.text_model(), parsed.syntax.forms@, root as int, row.expression.end as int),
            self.mixed_checked_call(DefinitionPosition { file: caller.0, entry: caller.1, definition: caller.2, reference }, call),
            reference < row.references.end - row.references.start,
            call.call.form == root, call.target.port_counts().outputs == 1,
            match known {
                Some(ty) => self.mixed_call_returns_type(call, limit, 0, ty),
                None => failure matches Some(error) && self.mixed_target_signature_failure(call, limit, error),
            },
        ensures self.mixed_nested_argument(caller, source, parsed, row, root, limit, known),
    {
        reveal(MixedUseAliases::mixed_nested_argument);
        if known.is_none() {
            let error = failure->Some_0;
            assert(exists|problem: MixedFuncTypeError| #[trigger] self.mixed_target_signature_failure(call, limit, problem)) by {
                assert(self.mixed_target_signature_failure(call, limit, error));
            };
        }
        let (file, entry, definition) = caller;
        assert(exists|r: usize, record: FuncCallArity| {
            &&& #[trigger] self.mixed_checked_call(DefinitionPosition { file, entry, definition, reference: r }, record)
            &&& r < row.references.end - row.references.start
            &&& record.call.form == root
            &&& record.target.port_counts().outputs == 1
            &&& match known {
                Some(ty) => self.mixed_call_returns_type(record, limit, 0, ty),
                None => exists|error: MixedFuncTypeError| #[trigger] self.mixed_target_signature_failure(record, limit, error),
            }
        }) by {
            assert(self.mixed_checked_call(DefinitionPosition { file, entry, definition, reference }, call));
        };
    }
}

fn retained_call_at<'s, 'p, 'a>(rows: &'s [(usize, FuncCallArity<'p, 'a>)], reference: usize)
    -> (found: Option<&'s FuncCallArity<'p, 'a>>)
    requires
        forall|i: int, j: int| 0 <= i < j < rows@.len() ==> (#[trigger] rows@[i]).0 < (#[trigger] rows@[j]).0,
    ensures
        found.is_some() <==> exists|i: int| 0 <= i < rows@.len() && (#[trigger] rows@[i]).0 == reference,
        found matches Some(call) ==> exists|i: int| 0 <= i < rows@.len() && (#[trigger] rows@[i]) == (reference, *call),
{
    let mut start = 0;
    let mut end = rows.len();
    while start < end
        invariant
            start <= end <= rows@.len(),
            forall|i: int, j: int| 0 <= i < j < rows@.len() ==> (#[trigger] rows@[i]).0 < (#[trigger] rows@[j]).0,
            forall|i: int| 0 <= i < start ==> (#[trigger] rows@[i]).0 < reference,
            forall|i: int| end <= i < rows@.len() ==> reference < (#[trigger] rows@[i]).0,
        decreases end - start,
    {
        let middle = start + (end - start) / 2;
        let candidate = &rows[middle];
        if candidate.0 == reference { return Some(&candidate.1); }
        if candidate.0 < reference { start = middle + 1; }
        else { end = middle; }
    }
    None
}

}
