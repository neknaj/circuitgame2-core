//! 構造体式を検査し、信号型と入力上のビット区間を求める。

use super::{StructureFieldType, StructureLayouts, StructureOperation, StructureOperationError, TypedStructureOperation, UseAliases};
use super::super::{ResolvedPortType, SignalType};
use crate::project::{DefinitionReferenceError, LocatedName, ProjectSource};
use crate::project::circuits::{form_location, read_indexed_atom};
use crate::syntax::circuit::{FieldSelectionShape, NamedBuildCircuit, StructureExpressionKind, StructureExpressionShape};
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::project::circuits::{is_form_location, parsed_index_evidence};
#[cfg(verus_only)]
use crate::syntax::circuit::{field_selection_shape_matches, structure_expression_matches, structure_expression_positions};
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
    (SignalType<'p, 'a>, TypedStructureOperation, u64);

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(in crate::project::use_aliases) open spec fn structure_expression_root(context: &StructureExpressionContext) -> usize {
        let parsed = context.parsed;
        let defs = parsed.entry_ranges@[context.entry as int].definitions;
        parsed.definitions@[defs.start + context.definition].expression.start
    }

    pub(in crate::project::use_aliases) open spec fn structure_expression_context_matches(
        &self, context: &StructureExpressionContext, shape: StructureExpressionShape,
    ) -> bool {
        self.structure_expression_at_matches(context, Self::structure_expression_root(context), shape)
    }

    pub(in crate::project::use_aliases) open spec fn structure_expression_at_matches(
        &self, context: &StructureExpressionContext, at: usize, shape: StructureExpressionShape,
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
            &&& (at == Self::structure_expression_root(context) || shape.kind is Field)
            &&& structure_expression_matches(context.source.text, parsed.syntax.forms@, at as int, shape)
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

    pub(in crate::project::use_aliases) closed spec fn layout_port_width_matches(
        &self, layouts: &StructureLayouts, port: ResolvedPortType, width: int,
    ) -> bool {
        exists|field: StructureFieldType| #[trigger] self.expression_port_matches(field, port)
            && layouts.representation_width_matches(field, width)
    }

    pub(in crate::project::use_aliases) proof fn layout_port_widths_agree(
        &self, layouts: &StructureLayouts, port: ResolvedPortType, left: int, right: int,
    )
        requires
            self.can_resolve(),
            self.layout_port_width_matches(layouts, port, left),
            self.layout_port_width_matches(layouts, port, right),
        ensures left == right,
    {
        let a = choose|ty: StructureFieldType| #[trigger] self.expression_port_matches(ty, port)
            && layouts.representation_width_matches(ty, left);
        let b = choose|ty: StructureFieldType| #[trigger] self.expression_port_matches(ty, port)
            && layouts.representation_width_matches(ty, right);
        self.structure_input_types_agree(port, a, b);
        layouts.representation_width_agrees(a, left, right);
    }

    pub(in crate::project::use_aliases) proof fn layout_port_widths_agree_across_tables(
        &self, limit: u64, left: &StructureLayouts, right: &StructureLayouts, port: ResolvedPortType, a: int, b: int,
    )
        requires
            self.can_resolve(),
            self.structure_types_match(limit, Ok(*left)),
            self.structure_types_match(limit, Ok(*right)),
            self.layout_port_width_matches(left, port, a),
            self.layout_port_width_matches(right, port, b),
        ensures a == b,
    {
        let x = choose|ty: StructureFieldType| #[trigger] self.expression_port_matches(ty, port)
            && left.representation_width_matches(ty, a);
        let y = choose|ty: StructureFieldType| #[trigger] self.expression_port_matches(ty, port)
            && right.representation_width_matches(ty, b);
        self.structure_input_types_agree(port, x, y);
        self.representation_widths_agree_across_layouts(limit, left, right, x, a, b);
    }

    proof fn structure_input_types_agree(
        &self, port: ResolvedPortType, left: StructureFieldType, right: StructureFieldType,
    )
        requires
            self.can_resolve(),
            self.expression_port_matches(left, port),
            self.expression_port_matches(right, port),
        ensures left == right,
    {
        if let (StructureFieldType::Struct(a), StructureFieldType::Struct(b)) = (left, right) {
            self.structure_port_positions_agree(port, a, b);
        } else if let StructureFieldType::Struct(position) = left {
            self.structure_port_type_resolved(position, Some(port));
        } else if let StructureFieldType::Struct(position) = right {
            self.structure_port_type_resolved(position, Some(port));
        }
    }

    pub(in crate::project::use_aliases) proof fn layout_bits_port_width(
        &self, layouts: &StructureLayouts, bits: u64, width: int,
    )
        requires self.layout_port_width_matches(layouts, ResolvedPortType::Bits(bits), width),
        ensures width == bits,
    {
        let ty = choose|ty: StructureFieldType| #[trigger] self.expression_port_matches(ty, ResolvedPortType::Bits(bits))
            && layouts.representation_width_matches(ty, width);
        layouts.bits_representation_width(bits, width);
    }

    pub(in crate::project::use_aliases) fn structure_port_width(
        &self, source: &ProjectSource<'a>, form: &crate::syntax::circuit::NamedForm<'a>,
        layouts: &StructureLayouts<'p, 'a>, _limit: u64,
    ) -> (width: u64)
        requires
            self.can_resolve(),
            self.declared_port_type(ResolvedPortType::Struct { source, form }),
            self.structure_types_match(_limit, Ok(*layouts)),
        ensures width > 0,
            self.layout_port_width_matches(layouts, ResolvedPortType::Struct { source, form }, width as int),
    {
        let position = self.resolved_structure_position(source, form);
        proof { self.checked_layout_contains(_limit, *layouts, position); }
        let Some(layout) = layouts.get(position) else { unreachable!() };
        proof {
            assert(self.expression_port_matches(StructureFieldType::Struct(position), ResolvedPortType::Struct { source, form }));
            assert(layouts.representation_width_matches(StructureFieldType::Struct(position), layout.width as int));
        }
        layout.width
    }

    pub(in crate::project::use_aliases) closed spec fn structure_expression_type_matches(
        &self, context: &StructureExpressionContext, shape: StructureExpressionShape, layouts: &StructureLayouts,
        input: SignalType, result: Result<CheckedStructureExpression, StructureExpressionTypeError>,
    ) -> bool {
        self.structure_expression_type_at_matches(context, Self::structure_expression_root(context), shape, layouts, input, result)
    }

    /// 式の型と配置、および診断の場所を指定したフォームに結び付ける。
    pub(in crate::project::use_aliases) closed spec fn structure_expression_type_at_matches(
        &self, context: &StructureExpressionContext, at: usize, shape: StructureExpressionShape, layouts: &StructureLayouts,
        input: SignalType, result: Result<CheckedStructureExpression, StructureExpressionTypeError>,
    ) -> bool {
        if let Err(StructureExpressionTypeError::Cast(error)) = result {
            shape.kind is As
                && self.structure_cast_resolution_matches(context.file, context.entry, context.definition, Err(error))
        } else {
            let form = context.parsed.syntax.forms@[at as int];
            exists|op: StructureOperation, input_type: StructureFieldType|
                #[trigger] self.structure_operation_from_source(context, shape, op)
                && #[trigger] self.expression_port_matches(input_type, input.ty)
                && match result {
                    Ok((signal, operation, width)) => layouts.structure_operation_matches(op, input_type, Ok(operation))
                        && self.expression_port_matches(operation.ty, signal.ty)
                        && is_form_location(context.source, form, signal.origin)
                        && operation.range.start < operation.range.end
                        && self.layout_port_width_matches(layouts, signal.ty, operation.range.end - operation.range.start)
                        && self.layout_port_width_matches(layouts, input.ty, width as int)
                        && operation.range.end <= width
                        && (!(op is Field) ==> operation.range.start == 0 && operation.range.end == width),
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

    proof fn checked_structure_operation(
        &self, context: &StructureExpressionContext, at: usize, shape: StructureExpressionShape,
        layouts: &StructureLayouts, input: SignalType, checked: CheckedStructureExpression,
    ) -> (found: (StructureOperation<'a>, StructureFieldType))
        requires self.structure_expression_type_at_matches(context, at, shape, layouts, input, Ok(checked)),
        ensures
            self.structure_operation_from_source(context, shape, found.0),
            self.expression_port_matches(found.1, input.ty),
            layouts.structure_operation_matches(found.0, found.1, Ok(checked.1)),
            self.expression_port_matches(checked.1.ty, checked.0.ty),
    {
        choose|op: StructureOperation<'a>, field: StructureFieldType|
            #[trigger] self.structure_operation_from_source(context, shape, op)
            && #[trigger] self.expression_port_matches(field, input.ty)
            && layouts.structure_operation_matches(op, field, Ok(checked.1))
    }

    /// 同じ構造体式と入力型を別々の配置表で検査した成功結果は、型・区間・入力幅が一致する。
    pub(in crate::project::use_aliases) proof fn checked_structure_expressions_agree(
        &self, context: &StructureExpressionContext, shape: StructureExpressionShape,
        left: &StructureLayouts, right: &StructureLayouts, input: SignalType,
        first: CheckedStructureExpression, second: CheckedStructureExpression,
    )
        requires
            self.can_resolve(),
            self.structure_types_match(context.limit, Ok(*left)),
            self.structure_types_match(context.limit, Ok(*right)),
            self.structure_expression_type_matches(context, shape, left, input, Ok(first)),
            self.structure_expression_type_matches(context, shape, right, input, Ok(second)),
        ensures first == second,
    {
        self.checked_structure_expressions_agree_at(context, Self::structure_expression_root(context), shape,
            left, right, input, first, second);
    }

    /// 同じ構文位置の構造体式は、配置を独立に検査しても同じ型とビット区間を持つ。
    pub(in crate::project::use_aliases) proof fn checked_structure_expressions_agree_at(
        &self, context: &StructureExpressionContext, at: usize, shape: StructureExpressionShape,
        left: &StructureLayouts, right: &StructureLayouts, input: SignalType,
        first: CheckedStructureExpression, second: CheckedStructureExpression,
    )
        requires
            self.can_resolve(),
            self.structure_types_match(context.limit, Ok(*left)),
            self.structure_types_match(context.limit, Ok(*right)),
            self.structure_expression_type_at_matches(context, at, shape, left, input, Ok(first)),
            self.structure_expression_type_at_matches(context, at, shape, right, input, Ok(second)),
        ensures first == second,
    {
        let (a, left_input) = self.checked_structure_operation(context, at, shape, left, input, first);
        let (b, right_input) = self.checked_structure_operation(context, at, shape, right, input, second);
        self.structure_input_types_agree(input.ty, left_input, right_input);
        self.structure_expression_width_at(context, at, shape, left, input, first);
        self.structure_expression_width_at(context, at, shape, right, input, second);
        self.layout_port_widths_agree_across_tables(context.limit, left, right, input.ty, first.2 as int, second.2 as int);
        match shape.kind {
            StructureExpressionKind::Field { .. } => {
                left.checked_field_requires_structure(a->Field_0, left_input, first.1);
                self.checked_field_operations_agree(context.limit, left, right, left_input->Struct_0,
                    a->Field_0, b->Field_0, first.1, second.1);
            },
            StructureExpressionKind::As { .. } => {
                self.structure_cast_targets_agree(context.file, context.entry, context.definition, a->As_0, b->As_0);
                left.checked_conversion_operation_type(a, left_input, first.1);
                right.checked_conversion_operation_type(b, right_input, second.1);
            },
            StructureExpressionKind::Raw => {
                left.checked_conversion_operation_type(a, left_input, first.1);
                right.checked_conversion_operation_type(b, right_input, second.1);
                self.layout_bits_port_width(left, first.1.ty->Bits_0, first.1.range.end - first.1.range.start);
                self.layout_bits_port_width(right, second.1.ty->Bits_0, second.1.range.end - second.1.range.start);
            },
        }
        assert(first.1 == second.1);
        if let StructureFieldType::Struct(position) = first.1.ty {
            self.structure_port_types_agree(position, Some(first.0.ty), Some(second.0.ty));
        }
        assert(first.0.origin == second.0.origin);
    }

    /// 式の結果幅と入力上の選択範囲を、型の表現幅に結び付ける。
    pub(in crate::project::use_aliases) proof fn structure_expression_width_evidence(
        &self, context: &StructureExpressionContext, shape: StructureExpressionShape, layouts: &StructureLayouts,
        input: SignalType, checked: CheckedStructureExpression,
    )
        requires self.structure_expression_type_matches(context, shape, layouts, input, Ok(checked)),
        ensures
            checked.1.range.start < checked.1.range.end,
            self.layout_port_width_matches(layouts, checked.0.ty, checked.1.range.end - checked.1.range.start),
            self.layout_port_width_matches(layouts, input.ty, checked.2 as int),
            checked.1.range.end <= checked.2,
            !(shape.kind is Field) ==> checked.1.range.start == 0 && checked.1.range.end == checked.2,
    {
        self.structure_expression_width_at(context, Self::structure_expression_root(context), shape, layouts, input, checked);
    }

    pub(in crate::project::use_aliases) proof fn structure_expression_width_at(
        &self, context: &StructureExpressionContext, at: usize, shape: StructureExpressionShape,
        layouts: &StructureLayouts, input: SignalType, checked: CheckedStructureExpression,
    )
        requires self.structure_expression_type_at_matches(context, at, shape, layouts, input, Ok(checked)),
        ensures
            checked.1.range.start < checked.1.range.end,
            self.layout_port_width_matches(layouts, checked.0.ty, checked.1.range.end - checked.1.range.start),
            self.layout_port_width_matches(layouts, input.ty, checked.2 as int),
            checked.1.range.end <= checked.2,
            !(shape.kind is Field) ==> checked.1.range.start == 0 && checked.1.range.end == checked.2,
    {
        let op = choose|op: StructureOperation, field: StructureFieldType|
            #[trigger] self.structure_operation_from_source(context, shape, op)
                && #[trigger] self.expression_port_matches(field, input.ty)
                && layouts.structure_operation_matches(op, field, Ok(checked.1))
                && self.expression_port_matches(checked.1.ty, checked.0.ty)
                && (!(op is Field) ==> checked.1.range.start == 0 && checked.1.range.end == checked.2);
        let (op, _) = op;
        assert((op is Field) == (shape.kind is Field));
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
            result matches Ok((signal, operation, width)) ==> self.declared_port_type(signal.ty)
                && crate::project::location_in_source(signal.origin)
                && operation.range.start < operation.range.end <= width,
    {
        let parsed = context.parsed;
        let defs = &parsed.entry_ranges[context.entry].definitions;
        let row = &parsed.definitions[defs.start + context.definition];
        self.check_structure_expression_type_at(context, row.expression.start, shape, layouts, input)
    }

    /// 選択式の末端にあるフィールドの型と配置を検査する。
    pub(in crate::project::use_aliases) fn check_selected_field_type(
        &self, context: &StructureExpressionContext<'p, 'a>, field: &FieldSelectionShape,
        layouts: &StructureLayouts<'p, 'a>, input: SignalType<'p, 'a>,
    ) -> (result: Result<CheckedStructureExpression<'p, 'a>, StructureExpressionTypeError<'p, 'a>>)
        requires
            self.can_resolve(),
            ({
                let project = self.targets.project_model();
                let parsed = context.parsed;
                &&& context.file < project.sources_model().len() && context.file < project.circuits_model().len()
                &&& *context.source == project.sources_model()[context.file as int]
                &&& *parsed == project.circuits_model()[context.file as int]
                &&& context.entry < parsed.entry_ranges@.len()
                &&& {
                    let defs = parsed.entry_ranges@[context.entry as int].definitions;
                    &&& defs.start + context.definition < defs.end <= parsed.definitions@.len()
                    &&& field_selection_shape_matches(context.source.text, parsed.syntax.forms@,
                        Self::structure_expression_root(context), field.steps@, field.field, field.shape)
                }
            }),
            self.structure_types_match(context.limit, Ok(*layouts)),
            self.declared_port_type(input.ty),
        ensures
            self.structure_expression_type_at_matches(context, field.field, field.shape, layouts, input, result),
            result matches Ok((signal, operation, width)) ==> self.declared_port_type(signal.ty)
                && is_form_location(context.source, context.parsed.syntax.forms@[field.field as int], signal.origin)
                && crate::project::location_in_source(signal.origin)
                && operation.range.start < operation.range.end <= width,
    {
        reveal(field_selection_shape_matches);
        self.check_structure_expression_type_at(context, field.field, &field.shape, layouts, input)
    }

    fn check_structure_expression_type_at(
        &self, context: &StructureExpressionContext<'p, 'a>, root: usize, shape: &StructureExpressionShape,
        layouts: &StructureLayouts<'p, 'a>, input: SignalType<'p, 'a>,
    ) -> (result: Result<CheckedStructureExpression<'p, 'a>, StructureExpressionTypeError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.structure_expression_at_matches(context, root, *shape),
            self.structure_types_match(context.limit, Ok(*layouts)),
            self.declared_port_type(input.ty),
        ensures
            self.structure_expression_type_at_matches(context, root, *shape, layouts, input, result),
            result matches Ok((signal, operation, width)) ==> self.declared_port_type(signal.ty)
                && is_form_location(context.source, context.parsed.syntax.forms@[root as int], signal.origin)
                && crate::project::location_in_source(signal.origin)
                && operation.range.start < operation.range.end <= width,
    {
        let source = context.source;
        let parsed = context.parsed;
        let forms = parsed.syntax.forms.as_slice();
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
        let (operation, input_width) = match layouts.check_operation_with_width(op, input_type) {
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
                assert(self.structure_expression_type_at_matches(context, root, *shape, layouts, input, Err(error)));
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
                assert(self.structure_expression_type_at_matches(context, root, *shape, layouts, input, Err(error)));
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
        let checked = (SignalType { ty, origin: expression }, operation, input_width);
        assert(self.structure_expression_type_at_matches(context, root, *shape, layouts, input, Ok(checked))) by {
            assert(self.layout_port_width_matches(layouts, input.ty, input_width as int));
            assert(self.layout_port_width_matches(layouts, ty, operation.range.end - operation.range.start)) by {
                assert(self.expression_port_matches(operation.ty, ty));
                assert(layouts.representation_width_matches(operation.ty, operation.range.end - operation.range.start));
            };
        };
        Ok(checked)
    }
}

} // verus!
