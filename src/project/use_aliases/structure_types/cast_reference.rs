//! `as` の型名を、定義のスコープに従って構造体の宣言位置へ解決する。

use super::{DefinitionBinding, StructurePosition, UseAliases};
use crate::project::DefinitionReferenceError;
use crate::syntax::circuit::{StructureExpressionKind, structure_expression_shape};
use vstd::prelude::*;

#[cfg(verus_only)]
use super::super::definitions::definition_count;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::project::ResolvedDefinitionReference;
#[cfg(verus_only)]
use crate::syntax::circuit::{
    StructureExpressionShape, build_definition_scope_evidence, build_entry_ranges_evidence,
    structure_cast_reference, structure_expression_matches,
};

verus! {

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn cast_definition_exists(&self, file: usize, entry: usize, definition: usize) -> bool {
        let circuits = self.targets.project_model().circuits_model();
        &&& file < circuits.len()
        &&& entry < circuits[file as int].entry_ranges@.len()
        &&& definition < definition_count(&circuits[file as int], entry as int)
    }

    spec fn cast_root_is_as(&self, file: usize, entry: usize, definition: usize) -> bool {
        let project = self.targets.project_model();
        let parsed = project.circuits_model()[file as int];
        let row = parsed.definitions@[parsed.entry_ranges@[entry as int].definitions.start + definition];
        let source = project.sources_model()[file as int].text;
        exists|shape: StructureExpressionShape| #[trigger] structure_expression_matches(
            source, parsed.syntax.forms@, row.expression.start as int, shape,
        ) && shape.kind is As
    }

    /// 結果が右辺全体の `as` と、その型名の名前解決に対応することを表す。
    pub closed spec fn structure_cast_resolution_matches(
        &self, file: usize, entry: usize, definition: usize,
        result: Result<Option<StructurePosition>, DefinitionReferenceError>,
    ) -> bool {
        if !self.cast_definition_exists(file, entry, definition) {
            result == Err(DefinitionReferenceError::UnknownPosition)
        } else if !self.cast_root_is_as(file, entry, definition) {
            result == Ok(None)
        } else {
            match result {
                Ok(Some(position)) => exists|resolved: ResolvedDefinitionReference|
                    #[trigger] self.definition_resolution_evidence(file, entry, definition, 0, Ok(resolved))
                    && self.structure_position_matches(position, resolved.binding),
                Err(error) => error is Rejected
                    && self.definition_resolution_evidence(file, entry, definition, 0, Err(error)),
                Ok(None) => false,
            }
        }
    }

    /// 右辺全体が `as` の定義について、変換先の構造体宣言の位置を返す。
    ///
    /// 型名は定義を囲む名前空間ブロックの別名と公開規則に従って解決する。
    /// `definition` は宣言内での定義の添字。右辺全体が `as` でなければ `Ok(None)` を返す。
    ///
    /// # Examples
    ///
    /// 別名で指定した型を、元の構造体宣言の位置に解決する。
    ///
    /// ```
    /// use circuitgame2_core::{
    ///     project::{SourceSnapshot, StructurePosition, check_use_aliases, index_use_targets, parse_circuit_project},
    ///     syntax::circuit::Head,
    /// };
    /// let project = parse_circuit_project(&[
    ///     SourceSnapshot { path: "app.ncg2", revision: 1,
    ///         text: "(namespace app (use ::lib::Word imported)
    ///             (func f (in (x (bits 8))) (out (y (bits 8)))
    ///                 (def word (as imported x))
    ///                 (def y (raw (as imported x)))))" },
    ///     SourceSnapshot { path: "lib.ncg2", revision: 1,
    ///         text: "(namespace lib (struct Word (width 8)) (export Word))" },
    /// ]).unwrap();
    /// let entry = |file: usize, head| project.circuits()[file].syntax.entries.iter()
    ///     .position(|item| item.head == head).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let function = entry(0, Head::Func);
    /// assert_eq!(aliases.resolve_structure_cast(0, function, 0).unwrap(),
    ///     Some(StructurePosition { file: 1, entry: entry(1, Head::Struct) }));
    /// assert_eq!(aliases.resolve_structure_cast(0, function, 1).unwrap(), None);
    /// ```
    ///
    /// # Errors
    ///
    /// ファイル、厳格索引項目、定義の添字が範囲外なら `UnknownPosition` を返す。
    /// 型名の解決に失敗した場合は、元の型名の範囲と解決できなかった理由を返す。
    pub fn resolve_structure_cast(
        &self, file: usize, entry: usize, definition: usize,
    ) -> (result: Result<Option<StructurePosition>, DefinitionReferenceError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.structure_cast_resolution_matches(file, entry, definition, result),
    {
        let project = self.targets.project();
        let circuits = project.circuits();
        if file >= circuits.len() {
            return Err(DefinitionReferenceError::UnknownPosition);
        }
        let parsed = &circuits[file];
        if entry >= parsed.entry_ranges.len() {
            return Err(DefinitionReferenceError::UnknownPosition);
        }
        let source = &project.sources()[file];
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let defs = &parsed.entry_ranges[entry].definitions;
        if definition >= defs.end - defs.start {
            return Err(DefinitionReferenceError::UnknownPosition);
        }
        let index = defs.start + definition;
        proof {
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, index as int);
        }
        let row = &parsed.definitions[index];
        let forms = parsed.syntax.forms.as_slice();
        let projection = structure_expression_shape(source.text, forms, row.expression.start);
        let Some(shape) = projection else {
            return Ok(None);
        };
        let StructureExpressionKind::As { .. } = shape.kind else {
            return Ok(None);
        };
        proof {
            assert(projection == Some(shape));
            assert(structure_expression_matches(source.text, forms@, row.expression.start as int, shape));
            structure_cast_reference(source.text, forms@, row.expression.start as int, row.expression.end as int, shape);
            assert(self.cast_root_is_as(file, entry, definition));
        }
        let resolved = match self.resolve_definition_reference(file, entry, definition, 0) {
            Err(error) => {
                proof {
                    if error is UnknownPosition {
                        self.valid_position_is_not_unknown(file, entry, definition, 0);
                    }
                }
                return Err(error);
            },
            Ok(resolved) => resolved,
        };
        proof { self.resolved_cast_declaration(file, entry, definition, 0, resolved); }
        let DefinitionBinding::Declaration { source: target_source, form: target_form } = resolved.binding else { unreachable!() };
        let position = self.resolved_structure_position(target_source, target_form);
        assert(self.structure_cast_resolution_matches(file, entry, definition, Ok(Some(position))));
        Ok(Some(position))
    }
}

} // verus!
