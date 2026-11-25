//! バイト位置を、名前解決に渡す厳格索引の参照位置へ変換する。

use super::{DefinitionPosition, DefinitionReferenceError, ResolvedDefinitionReference, UseAliases};
use crate::project::CircuitProject;
use crate::syntax::circuit::NamedBuildCircuit;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_has_entry, build_reference_has_definition};
use vstd::prelude::*;

verus! {

spec fn contains(span: core::ops::Range<usize>, offset: usize) -> bool {
    span.start <= offset < span.end
}

spec fn first_reference(parsed: &NamedBuildCircuit, offset: usize, result: Option<usize>) -> bool {
    let refs = parsed.references@;
    match result {
        Some(i) => i < refs.len() && contains(refs[i as int].span, offset)
            && forall|j: int| 0 <= j < i ==> !contains((#[trigger] refs[j]).span, offset),
        None => forall|j: int| 0 <= j < refs.len() ==> !contains((#[trigger] refs[j]).span, offset),
    }
}

spec fn first_definition(parsed: &NamedBuildCircuit, reference: usize, result: Option<usize>) -> bool {
    let definitions = parsed.definitions@;
    match result {
        Some(i) => i < definitions.len() && contains(definitions[i as int].references, reference)
            && forall|j: int| 0 <= j < i ==> !contains((#[trigger] definitions[j]).references, reference),
        None => forall|j: int| 0 <= j < definitions.len() ==>
            !contains((#[trigger] definitions[j]).references, reference),
    }
}

spec fn first_entry(parsed: &NamedBuildCircuit, definition: usize, result: Option<usize>) -> bool {
    let ranges = parsed.entry_ranges@;
    match result {
        Some(i) => i < ranges.len() && contains(ranges[i as int].definitions, definition)
            && forall|j: int| 0 <= j < i ==> !contains((#[trigger] ranges[j]).definitions, definition),
        None => forall|j: int| 0 <= j < ranges.len() ==> !contains((#[trigger] ranges[j]).definitions, definition),
    }
}

fn reference_slot(parsed: &NamedBuildCircuit, offset: usize) -> (result: Option<usize>)
    ensures first_reference(parsed, offset, result),
{
    let mut i = 0usize;
    while i < parsed.references.len()
        invariant
            i <= parsed.references@.len(),
            forall|j: int| 0 <= j < i ==> !contains((#[trigger] parsed.references@[j]).span, offset),
        decreases parsed.references@.len() - i,
    {
        let span = &parsed.references[i].span;
        if span.start <= offset && offset < span.end {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn definition_slot(parsed: &NamedBuildCircuit, reference: usize) -> (result: Option<usize>)
    ensures first_definition(parsed, reference, result),
{
    let mut i = 0usize;
    while i < parsed.definitions.len()
        invariant
            i <= parsed.definitions@.len(),
            forall|j: int| 0 <= j < i ==> !contains((#[trigger] parsed.definitions@[j]).references, reference),
        decreases parsed.definitions@.len() - i,
    {
        let range = &parsed.definitions[i].references;
        if range.start <= reference && reference < range.end {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn entry_slot(parsed: &NamedBuildCircuit, definition: usize) -> (result: Option<usize>)
    ensures first_entry(parsed, definition, result),
{
    let mut i = 0usize;
    while i < parsed.entry_ranges.len()
        invariant
            i <= parsed.entry_ranges@.len(),
            forall|j: int| 0 <= j < i ==> !contains((#[trigger] parsed.entry_ranges@[j]).definitions, definition),
        decreases parsed.entry_ranges@.len() - i,
    {
        let range = &parsed.entry_ranges[i].definitions;
        if range.start <= definition && definition < range.end {
            return Some(i);
        }
        i += 1;
    }
    None
}

impl CircuitProject<'_> {
    /// バイト位置を含む参照の索引位置を表す。見つからない場合は `None`。
    pub closed spec fn reference_position_matches(
        &self, file: usize, offset: usize, result: Option<DefinitionPosition>,
    ) -> bool {
        if file >= self.circuits_model().len() {
            result.is_none()
        } else {
            let parsed = &(self.circuits_model()[file as int]);
            match result {
                Some(position) => exists|r: usize, d: usize| {
                    &&& #[trigger] first_reference(parsed, offset, Some(r))
                    &&& #[trigger] first_definition(parsed, r, Some(d))
                    &&& first_entry(parsed, d, Some(position.entry))
                    &&& position.file == file
                    &&& position.definition == d - parsed.entry_ranges@[position.entry as int].definitions.start
                    &&& position.reference == r - parsed.definitions@[d as int].references.start
                },
                None => first_reference(parsed, offset, None),
            }
        }
    }

    /// 対象ファイルの指定位置にある回路名・型名を、名前解決用の索引位置で返す。
    ///
    /// [`crate::project::parse_circuit_project`] が返したプロジェクトで使う。
    /// 参照が占める UTF-8 の半開バイト範囲で照合する。ファイル番号が範囲外か、
    /// その位置に参照がなければ `None` を返す。
    pub fn reference_position_at(&self, file: usize, offset: usize) -> (result: Option<DefinitionPosition>)
        requires self.has_parsed_sources(),
        ensures self.reference_position_matches(file, offset, result),
    {
        let circuits = self.circuits();
        if file >= circuits.len() {
            return None;
        }
        let parsed = &circuits[file];
        let Some(reference) = reference_slot(parsed, offset) else { return None; };
        let ghost source = self.sources_model()[file as int];
        proof {
            parsed_index_evidence(source, *parsed);
            build_reference_has_definition(source.text, &parsed.build_model(), reference);
        }
        let Some(definition) = definition_slot(parsed, reference) else { return None; };
        proof { build_definition_has_entry(source.text, &parsed.build_model(), definition); }
        let Some(entry) = entry_slot(parsed, definition) else { return None; };
        Some(DefinitionPosition {
            file, entry,
            definition: definition - parsed.entry_ranges[entry].definitions.start,
            reference: reference - parsed.definitions[definition].references.start,
        })
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// カーソルの参照に、コンパイラと同じ解決規則を適用した結果を表す。
    pub closed spec fn reference_at_offset_matches(
        &self, file: usize, offset: usize,
        result: Option<Result<ResolvedDefinitionReference, DefinitionReferenceError>>,
    ) -> bool {
        let project = self.targets.project_model();
        match result {
            Some(hit) => exists|position: DefinitionPosition| {
                &&& #[trigger] project.reference_position_matches(file, offset, Some(position))
                &&& self.definition_resolution_evidence(
                    file, position.entry, position.definition, position.reference, hit,
                )
            },
            None => project.reference_position_matches(file, offset, None),
        }
    }

    /// 指定位置の名前だけを、その定義のスコープで解決する。
    ///
    /// [`crate::project::check_use_aliases`] が返した別名表を使う。ファイル番号が範囲外か、
    /// その位置に参照がなければ `None` を返す。参照があれば、解決結果または診断を返す。
    pub fn resolve_reference_at_offset(&self, file: usize, offset: usize)
        -> (result: Option<Result<ResolvedDefinitionReference<'p, 'a>, DefinitionReferenceError<'p, 'a>>>)
        requires self.can_resolve(),
        ensures
            self.reference_at_offset_matches(file, offset, result),
            result != Some(Err(DefinitionReferenceError::UnknownPosition)),
    {
        let project = self.targets.project();
        let Some(position) = project.reference_position_at(file, offset) else { return None; };
        let hit = self.resolve_definition_reference(file, position.entry, position.definition, position.reference);
        proof {
            if hit == Err(DefinitionReferenceError::UnknownPosition) {
                self.valid_position_is_not_unknown(file, position.entry, position.definition, position.reference);
            }
        }
        Some(hit)
    }
}

} // verus!
