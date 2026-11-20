//! 選択列の末端にあるフィールドの型を求め、外側の選択へ伝える。

use super::*;
use crate::syntax::circuit::FieldSelectionShape;
#[cfg(verus_only)]
use crate::syntax::circuit::structure_expression_positions;
#[cfg(verus_only)]
use super::super::structure_types::CheckedStructureExpression;

verus! {

type CheckedFieldSelection<'p, 'a> =
    (SignalType<'p, 'a>, TypedStructureOperation, u64, CheckedBitSelection);

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 結線からフィールドの入力を求め、必要なときに構造体の配置を検査する。
    pub(super) fn check_indexed_field_selection(
        &self, context: &StructureExpressionContext<'p, 'a>, wiring: &FuncWiring<'p, 'a>,
        index: usize, prior: &[Option<SignalType<'p, 'a>>], field: &FieldSelectionShape,
        layouts: &mut Option<StructureLayouts<'p, 'a>>, expected: Option<&TypedPort<'p, 'a>>,
    ) -> (result: Result<Option<(SignalType<'p, 'a>, StructureProjection)>, FuncSignalTypeError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(context.file, context.entry, context.limit, Ok(FuncWiringResult::Checked(*wiring))),
            ({
                let project = self.targets.project_model();
                let parsed = context.parsed;
                &&& context.file < project.sources_model().len() && context.file < project.circuits_model().len()
                &&& *context.source == project.sources_model()[context.file as int]
                &&& *parsed == project.circuits_model()[context.file as int]
                &&& parsed_circuit_matches(*context.source, *parsed)
                &&& context.entry < parsed.syntax.entries@.len() && context.entry < parsed.entry_ranges@.len()
                &&& {
                    let defs = parsed.entry_ranges@[context.entry as int].definitions;
                    let definition = wiring.drivers.definitions@[index as int].definition;
                    &&& defs.start <= definition < defs.end <= parsed.definitions@.len()
                    &&& definition == defs.start + context.definition
                    &&& field_selection_shape_matches(context.source.text, parsed.syntax.forms@,
                        parsed.definitions@[definition as int].expression.start, field.steps@, field.field, field.shape)
                }
            }),
            index == prior@.len() < wiring.drivers.definitions@.len(),
            forall|j: int| 0 <= j < prior@.len() && (#[trigger] prior@[j]).is_some()
                ==> self.declared_port_type(prior@[j]->Some_0.ty),
            *old(layouts) matches Some(table) ==> self.structure_types_match(context.limit, Ok(table)),
        ensures
            old(layouts).is_some() ==> *final(layouts) == *old(layouts),
            *final(layouts) matches Some(table) ==> self.structure_types_match(context.limit, Ok(table)),
            ({
                let definition = wiring.drivers.definitions@[index as int].definition;
                let row = context.parsed.definitions@[definition as int];
                let first = context.parsed.entry_ranges@[context.entry as int].signals.start;
                let bound = wiring.signals@[row.signals.start - first];
                &&& first <= row.signals.start < first + wiring.signals@.len()
                &&& bound.definition == definition
                &&& is_form_location(context.source, context.parsed.syntax.forms@[field.shape.input.start as int], bound.site)
                &&& match bound.driver {
                    OutputDriver::Input(input) => input < wiring.drivers.signature.inputs@.len(),
                    OutputDriver::Definition(i) => i < prior@.len(),
                }
                &&& self.field_selection_atom_step(context, row.expression.start, field.steps@, field.field, field.shape,
                    signal_type_at(wiring, prior@, bound.driver),
                    match expected { Some(port) => Some(*port), None => None },
                    match result { Ok(Some((ty, _))) => Ok(Some(ty)), Ok(None) => Ok(None), Err(error) => Err(error) })
                &&& result == Ok(None) ==> signal_type_at(wiring, prior@, bound.driver).is_none()
            }),
            result matches Ok(Some((ty, projection))) ==> {
                &&& location_in_source(ty.origin) && ty.ty is Bits
                &&& projection.target == index
                &&& projection.selection.is_some()
                &&& structure_projections_in_order(seq![projection], index + 1, wiring.drivers.signature.inputs@.len() as int)
                &&& *final(layouts) matches Some(table)
                &&& structure_projection_matches(self, context.file, context.entry, context.limit, wiring,
                    table, prior@.push(Some(ty)), projection)
            },
            result matches Err(error) ==> error is Signal || error is SelectionInputType || error is SelectionArgument
                || error is StructureExpression || error is StructureLayout,
            result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
    {
        let parsed = context.parsed;
        let definition = wiring.drivers.definitions[index].definition;
        let row = &parsed.definitions[definition];
        let root = row.expression.start;
        proof {
            let source = context.source;
            self.checked_wiring_is_func(context.file, context.entry, context.limit, *wiring);
            parsed_index_evidence(*source, *parsed);
            build_field_selection_signal(source.text, &parsed.build_model(), context.entry as int,
                definition as int, field.steps@, field.field, field.shape);
            self.checked_signal_driver(context.file, context.entry, context.limit, *wiring, definition, row.signals.start);
            assert(self.structure_expression_at_matches(context, field.field, field.shape)) by {
                reveal(field_selection_shape_matches);
            };
        }
        let position = row.signals.start - parsed.entry_ranges[context.entry].signals.start;
        let bound = &wiring.signals[position];
        proof {
            if let OutputDriver::Definition(before) = bound.driver {
                assert(before < index) by {
                    if index < before {
                        assert(wiring.drivers.definitions@[index as int].definition
                            <= wiring.drivers.definitions@[before as int].definition);
                    }
                };
            }
        }
        let ghost expected_type = match expected { Some(port) => Some(*port), None => None };
        let Some(input) = inherit_type(wiring, prior, bound.driver) else {
            assert(self.field_selection_atom_step(context, root, field.steps@, field.field, field.shape,
                None, expected_type, Ok(None))) by { reveal(UseAliases::field_selection_atom_step); };
            return Ok(None);
        };
        if layouts.is_none() {
            match self.check_structure_types(context.limit) {
                Ok(table) => *layouts = Some(table),
                Err(error) => {
                    let error = FuncSignalTypeError::StructureLayout(error);
                    assert(self.field_selection_atom_step(context, root, field.steps@, field.field, field.shape,
                        Some(input), expected_type, Err(error))) by { reveal(UseAliases::field_selection_atom_step); };
                    return Err(error);
                }
            }
        }
        let Some(table) = &*layouts else { unreachable!() };
        let (ty, operation, input_width, selection) = self.check_field_selection_type(
            context, root, field, table, input, expected,
        )?;
        let projection = StructureProjection {
            target: index, input: bound.driver, operation, input_width, selection: Some(selection),
        };
        assert(structure_projection_matches(self, context.file, context.entry, context.limit, wiring,
            *table, prior@.push(Some(ty)), projection)) by {
            reveal(structure_projection_matches);
            assert(prior@.push(Some(ty)).take(index as int) =~= prior@);
        };
        Ok(Some((ty, projection)))
    }

    #[verifier::opaque]
    pub(super) open spec fn field_selection_atom_step(
        &self, context: &StructureExpressionContext, root: usize, steps: Seq<BitSelectionShape>,
        at: usize, shape: StructureExpressionShape, input: Option<SignalType>, expected: Option<TypedPort>,
        result: Result<Option<SignalType>, FuncSignalTypeError>,
    ) -> bool {
        match input {
            None => result == Ok(None),
            Some(input) => match result {
                Err(FuncSignalTypeError::StructureLayout(error)) => self.structure_types_match(context.limit, Err(error)),
                _ => exists|table: StructureLayouts| #[trigger] self.structure_types_match(context.limit, Ok(table))
                    && match result {
                        Err(FuncSignalTypeError::StructureExpression(error)) =>
                            self.structure_expression_type_at_matches(context, at, shape, &table, input, Err(error)),
                        _ => exists|field: CheckedStructureExpression|
                            #[trigger] self.structure_expression_type_at_matches(context, at, shape, &table, input, Ok(field))
                            && nested_selection_type_matches(context.source, context.parsed.syntax.forms@, root, steps, at,
                                Some(field.0), expected, result),
                    },
            },
        }
    }

    pub(super) proof fn field_selection_types_agree(
        &self, context: &StructureExpressionContext, root: usize, input: Option<SignalType>, expected: Option<TypedPort>,
        steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape,
        left: Option<SignalType>, right: Option<SignalType>,
    )
        requires
            self.can_resolve(),
            self.field_selection_atom_step(context, root, steps, at, shape, input, expected, Ok(left)),
            self.field_selection_atom_step(context, root, steps, at, shape, input, expected, Ok(right)),
        ensures left == right,
    {
        reveal(UseAliases::field_selection_atom_step);
        if let Some(input) = input {
            let (a, lhs) = choose|table: StructureLayouts, field: CheckedStructureExpression|
                #[trigger] self.structure_types_match(context.limit, Ok(table))
                && #[trigger] self.structure_expression_type_at_matches(context, at, shape, &table, input, Ok(field))
                && nested_selection_type_matches(context.source, context.parsed.syntax.forms@, root, steps, at,
                    Some(field.0), expected, Ok(left));
            let (b, rhs) = choose|table: StructureLayouts, field: CheckedStructureExpression|
                #[trigger] self.structure_types_match(context.limit, Ok(table))
                && #[trigger] self.structure_expression_type_at_matches(context, at, shape, &table, input, Ok(field))
                && nested_selection_type_matches(context.source, context.parsed.syntax.forms@, root, steps, at,
                    Some(field.0), expected, Ok(right));
            self.checked_structure_expressions_agree_at(context, at, shape, &a, &b, input, lhs, rhs);
            nested_selection_type_successes_agree(context.source, context.parsed.syntax.forms@, root, steps, at,
                Some(lhs.0), expected, left, right);
        }
    }

    /// フィールドを調べた後、その型と幅を内側の選択から順に検査する。
    fn check_field_selection_type(
        &self, context: &StructureExpressionContext<'p, 'a>, root: usize, field: &FieldSelectionShape,
        layouts: &StructureLayouts<'p, 'a>, input: SignalType<'p, 'a>, expected: Option<&TypedPort<'p, 'a>>,
    ) -> (result: Result<CheckedFieldSelection<'p, 'a>, FuncSignalTypeError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.structure_types_match(context.limit, Ok(*layouts)),
            self.declared_port_type(input.ty),
            self.structure_expression_at_matches(context, field.field, field.shape),
            root == Self::structure_expression_root(context),
            field_selection_shape_matches(context.source.text, context.parsed.syntax.forms@, root,
                field.steps@, field.field, field.shape),
            form_spans_valid(context.source.text, context.parsed.syntax.forms@, context.source.text.spec_bytes().len() as int),
        ensures
            self.field_selection_atom_step(context, root, field.steps@, field.field, field.shape, Some(input),
                match expected { Some(port) => Some(*port), None => None },
                match result { Ok((ty, _, _, _)) => Ok(Some(ty)), Err(error) => Err(error) }),
            result matches Ok((ty, operation, input_width, outer)) ==> {
                &&& location_in_source(ty.origin)
                &&& is_form_location(context.source, context.parsed.syntax.forms@[root as int], ty.origin)
                &&& ty.ty == ResolvedPortType::Bits(outer.count)
                &&& operation.range.start < operation.range.end <= input_width
                &&& outer.fits((operation.range.end - operation.range.start) as u64)
                &&& exists|base: SignalType| #[trigger] self.structure_expression_type_at_matches(
                    context, field.field, field.shape, layouts, input, Ok((base, operation, input_width)))
                    && base.ty == ResolvedPortType::Bits((operation.range.end - operation.range.start) as u64)
                    && selection_chain_arguments_match(context.source, context.parsed.syntax.forms@, field.steps@,
                        (operation.range.end - operation.range.start) as u64, base.origin, Ok(outer))
            },
            result matches Err(error) ==> (error is Signal || error is SelectionInputType || error is SelectionArgument
                || error is StructureExpression),
            result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
    {
        reveal(UseAliases::field_selection_atom_step);
        let checked = match self.check_selected_field_type(context, field, layouts, input) {
            Ok(checked) => checked,
            Err(error) => return Err(FuncSignalTypeError::StructureExpression(error)),
        };
        proof {
            reveal(field_selection_shape_matches);
            structure_expression_positions(context.source.text, context.parsed.syntax.forms@, field.field as int, field.shape);
        }
        let ghost base = checked.0;
        let result = check_nested_selection_type(context.source, context.parsed.syntax.forms.as_slice(), root,
            field.steps.as_slice(), field.field, Some(checked.0), expected)?;
        let Some((ty, outer)) = result else {
            proof { reveal(nested_selection_type_matches); }
            unreachable!()
        };
        proof {
            let width = checked.1.range.end - checked.1.range.start;
            self.structure_expression_width_at(context, field.field, field.shape, layouts, input, (base, checked.1, checked.2));
            self.layout_bits_port_width(layouts, base.ty->Bits_0, width);
        }
        Ok((ty, checked.1, checked.2, outer))
    }
}

} // verus!
