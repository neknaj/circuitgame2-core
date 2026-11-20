//! 構造体式を検査し、信号型と入力上のビット区間を求める。

use super::{StructureFieldType, StructureLayouts, StructureOperation, StructureOperationError, TypedStructureOperation, UseAliases};
use super::super::{ResolvedPortType, SignalType};
use crate::project::{DefinitionReferenceError, LocatedName, ProjectSource};
use crate::project::circuits::{form_location, read_indexed_atom};
use crate::syntax::circuit::{NamedBuildCircuit, StructureExpressionKind, StructureExpressionShape};
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::project::circuits::{is_form_location, parsed_index_evidence};
#[cfg(verus_only)]
use crate::syntax::circuit::{structure_expression_matches, structure_expression_positions};
#[cfg(verus_only)]
use crate::syntax::form_span;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 構造体式の型名または入力型に関する診断。
#[derive(Debug)]
pub enum StructureExpressionTypeError<'p, 'a> {
    /// `as` の型名を参照元のスコープから解決できなかった。
    Cast(DefinitionReferenceError<'p, 'a>),
    /// 入力のビット幅が変換先の構造体の総幅と異なる。
    WidthMismatch {
        /// `as` に書いた型名の範囲。
        target: LocatedName<'p, 'a>,
        /// 変換先の構造体宣言の名前。
        declaration: LocatedName<'p, 'a>,
        /// 入力のビット列型と、その型を決めた範囲。
        input: SignalType<'p, 'a>,
        /// 変換先の総幅。
        expected: u64,
    },
    /// 入力型またはフィールド名に対して演算を適用できなかった。
    Operation {
        /// 違反のある入力式またはフィールド名の範囲。
        site: LocatedName<'p, 'a>,
        /// 入力の型と、その型を決めた範囲。
        input: SignalType<'p, 'a>,
        /// 入力型またはフィールド名に関する理由。
        reason: StructureOperationError,
    },
}

pub(in crate::project::use_aliases) struct StructureExpressionContext<'p, 'a> {
    pub(in crate::project::use_aliases) file: usize,
    pub(in crate::project::use_aliases) entry: usize,
    pub(in crate::project::use_aliases) definition: usize,
    pub(in crate::project::use_aliases) limit: u64,
    pub(in crate::project::use_aliases) source: &'p ProjectSource<'a>,
    pub(in crate::project::use_aliases) parsed: &'p NamedBuildCircuit<'a>,
}

pub(in crate::project::use_aliases) type CheckedStructureExpression<'p, 'a> =
    (SignalType<'p, 'a>, Ghost<TypedStructureOperation>);

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(in crate::project::use_aliases) open spec fn structure_expression_context_matches(
        &self, context: &StructureExpressionContext, shape: StructureExpressionShape,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = context.parsed;
        &&& context.file < project.sources_model().len() && context.file < project.circuits_model().len()
        &&& *context.source == project.sources_model()[context.file as int]
        &&& *parsed == project.circuits_model()[context.file as int]
        &&& context.entry < parsed.entry_ranges@.len()
        &&& {
            let defs = parsed.entry_ranges@[context.entry as int].definitions;
            &&& defs.start + context.definition < defs.end <= parsed.definitions@.len()
            &&& structure_expression_matches(context.source.text, parsed.syntax.forms@,
                parsed.definitions@[defs.start + context.definition].expression.start as int, shape)
        }
    }

    spec fn structure_operation_from_source(
        &self, context: &StructureExpressionContext, shape: StructureExpressionShape, op: StructureOperation,
    ) -> bool {
        match (shape.kind, op) {
            (StructureExpressionKind::Field { name }, StructureOperation::Field(word)) => {
                let span = form_span(context.parsed.syntax.forms@[name as int]);
                word.spec_bytes() == context.source.text.spec_bytes()[span.start as int..span.end as int]
            },
            (StructureExpressionKind::As { .. }, StructureOperation::As(position)) =>
                self.structure_cast_resolution_matches(context.file, context.entry, context.definition, Ok(Some(position))),
            (StructureExpressionKind::Raw, StructureOperation::Raw) => true,
            _ => false,
        }
    }

    spec fn expression_port_matches(&self, field: StructureFieldType, ty: ResolvedPortType) -> bool {
        match field {
            StructureFieldType::Bits(width) => ty == ResolvedPortType::Bits(width),
            StructureFieldType::Struct(position) => self.structure_port_type_matches(position, Some(ty)),
        }
    }

    pub(in crate::project::use_aliases) closed spec fn structure_expression_type_matches(
        &self, context: &StructureExpressionContext, shape: StructureExpressionShape, layouts: &StructureLayouts,
        input: SignalType, result: Result<CheckedStructureExpression, StructureExpressionTypeError>,
    ) -> bool {
        if let Err(StructureExpressionTypeError::Cast(error)) = result {
            shape.kind is As
                && self.structure_cast_resolution_matches(context.file, context.entry, context.definition, Err(error))
        } else {
            let defs = context.parsed.entry_ranges@[context.entry as int].definitions;
            let root = context.parsed.definitions@[defs.start + context.definition].expression.start;
            let form = context.parsed.syntax.forms@[root as int];
            exists|op: StructureOperation, input_type: StructureFieldType|
                #[trigger] self.structure_operation_from_source(context, shape, op)
                && #[trigger] self.expression_port_matches(input_type, input.ty)
                && match result {
                    Ok((signal, operation)) => layouts.structure_operation_matches(op, input_type, Ok(operation@))
                        && self.expression_port_matches(operation@.ty, signal.ty)
                        && is_form_location(context.source, form, signal.origin),
                    Err(StructureExpressionTypeError::WidthMismatch { target, declaration, input: actual, expected }) =>
                        input == actual
                            && (shape.kind matches StructureExpressionKind::As { target: at }
                                && is_form_location(context.source, context.parsed.syntax.forms@[at as int], target))
                            && (op matches StructureOperation::As(position)
                                && exists|ty: ResolvedPortType| #[trigger] self.structure_port_type_matches(position, Some(ty))
                                    && (ty matches ResolvedPortType::Struct { source, form }
                                        && *declaration.source == *source && declaration.span == form.name.span
                                        && crate::project::location_in_source(declaration)))
                            && (input_type matches StructureFieldType::Bits(width)
                                && layouts.structure_operation_matches(op, input_type,
                                    Err(StructureOperationError::WidthMismatch { input: width, expected }))),
                    Err(StructureExpressionTypeError::Operation { site, input: actual, reason }) => {
                        let at = if reason is UnknownField && shape.kind is Field { shape.kind->Field_name } else { shape.input.start };
                        input == actual && !(reason is WidthMismatch) && !(reason is UnknownStructure)
                            && is_form_location(context.source, context.parsed.syntax.forms@[at as int], site)
                            && layouts.structure_operation_matches(op, input_type, Err(reason))
                    },
                    _ => false,
                }
        }
    }

    pub(in crate::project::use_aliases) fn check_structure_expression_type(
        &self, context: &StructureExpressionContext<'p, 'a>, shape: &StructureExpressionShape,
        layouts: &StructureLayouts<'p, 'a>, input: SignalType<'p, 'a>,
    ) -> (result: Result<CheckedStructureExpression<'p, 'a>, StructureExpressionTypeError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.structure_expression_context_matches(context, *shape),
            self.structure_types_match(context.limit, Ok(*layouts)),
            self.declared_port_type(input.ty),
        ensures
            self.structure_expression_type_matches(context, *shape, layouts, input, result),
            result matches Ok((signal, operation)) ==> self.declared_port_type(signal.ty)
                && crate::project::location_in_source(signal.origin)
                && operation@.range.start < operation@.range.end,
    {
        let source = context.source;
        let parsed = context.parsed;
        let defs = &parsed.entry_ranges[context.entry].definitions;
        let row = &parsed.definitions[defs.start + context.definition];
        let forms = parsed.syntax.forms.as_slice();
        let root = row.expression.start;
        proof {
            self.targets.parsed_project_model();
            parsed_index_evidence(*source, *parsed);
            structure_expression_positions(source.text, forms@, root as int, *shape);
        }
        let expression = form_location(source, forms, root);
        let op = match shape.kind {
            StructureExpressionKind::Field { name } => {
                let (word, _) = read_indexed_atom(source.text, forms, name);
                StructureOperation::Field(word)
            },
            StructureExpressionKind::As { .. } => {
                let target = self.resolve_structure_cast(context.file, context.entry, context.definition);
                proof {
                    self.recognized_cast_has_resolution(context.file, context.entry, context.definition, *shape, target);
                }
                match target {
                    Ok(Some(position)) => StructureOperation::As(position),
                    Err(error) => return Err(StructureExpressionTypeError::Cast(error)),
                    Ok(None) => unreachable!(),
                }
            },
            StructureExpressionKind::Raw => StructureOperation::Raw,
        };
        assert(self.structure_operation_from_source(context, *shape, op));
        let input_type = match input.ty {
            ResolvedPortType::Bits(width) => StructureFieldType::Bits(width),
            ResolvedPortType::Struct { source, form } =>
                StructureFieldType::Struct(self.resolved_structure_position(source, form)),
        };
        assert(self.expression_port_matches(input_type, input.ty));
        let operation = match layouts.check_operation(op, input_type) {
            Ok(checked) => checked,
            Err(StructureOperationError::WidthMismatch { input: _width, expected }) => {
                let StructureOperation::As(position) = op else { unreachable!() };
                let StructureExpressionKind::As { target: target_form } = shape.kind else { unreachable!() };
                proof { self.cast_targets_structure(context.file, context.entry, context.definition, position); }
                let port = self.structure_port_type(position);
                proof { self.structure_port_type_resolved(position, port); }
                let Some(ResolvedPortType::Struct { source: declared_source, form: declared_form }) = port
                else { unreachable!() };
                assert(self.structure_port_type_matches(position, port));
                let error = StructureExpressionTypeError::WidthMismatch {
                    target: form_location(source, forms, target_form),
                    declaration: LocatedName {
                        source: declared_source, span: declared_form.name.span.start..declared_form.name.span.end,
                    },
                    input,
                    expected,
                };
                assert(layouts.structure_operation_matches(op, input_type, Err(StructureOperationError::WidthMismatch {
                    input: _width, expected,
                })));
                assert(self.structure_expression_type_matches(context, *shape, layouts, input, Err(error)));
                return Err(error);
            },
            Err(reason) => {
                proof {
                    if let StructureOperationError::UnknownStructure(position) = reason {
                        layouts.unknown_operation_structure_is_missing(op, input_type, position);
                        if let StructureOperation::As(target) = op {
                            if target == position {
                                self.cast_targets_structure(context.file, context.entry, context.definition, position);
                            }
                        }
                        if input_type == StructureFieldType::Struct(position) {
                            self.structure_port_type_resolved(position, Some(input.ty));
                        }
                        assert(self.is_structure_position(position));
                        self.checked_layout_contains(context.limit, *layouts, position);
                        assert(false);
                    }
                }
                let at = match (reason, shape.kind) {
                    (StructureOperationError::UnknownField(_), StructureExpressionKind::Field { name }) => name,
                    _ => shape.input.start,
                };
                let error = StructureExpressionTypeError::Operation { site: form_location(source, forms, at), input, reason };
                assert(self.structure_expression_type_matches(context, *shape, layouts, input, Err(error)));
                return Err(error);
            },
        };
        let ty = match operation.ty {
            StructureFieldType::Bits(width) => ResolvedPortType::Bits(width),
            StructureFieldType::Struct(position) => {
                proof {
                    layouts.representation_has_layout(position, operation.range.end - operation.range.start);
                    self.checked_layout_positions_are_declared(context.limit, *layouts);
                    let i = choose|i: int| 0 <= i < layouts.entries_model().len()
                        && (#[trigger] layouts.entries_model()[i]).position == position;
                    assert(self.is_structure_position(layouts.entries_model()[i].position));
                }
                let port = self.structure_port_type(position);
                proof { self.structure_port_type_resolved(position, port); }
                let Some(ty) = port else { unreachable!() };
                ty
            },
        };
        let checked = (SignalType { ty, origin: expression }, Ghost(operation));
        assert(self.structure_expression_type_matches(context, *shape, layouts, input, Ok(checked)));
        Ok(checked)
    }
}

} // verus!
