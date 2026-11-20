//! フィールドの値に選択を適用する参照評価と、合成した配線との対応を示す。

use super::*;
use crate::project::selected_bits_values;
use crate::syntax::circuit::{field_selection_shape_matches, field_selection_shapes_agree};
use super::super::super::super::selection_arguments::composed_selection_values_agree;

verus! {

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) open spec fn source_field_selection_value(
        &self, context: &SourceFunc, layouts: &StructureLayouts, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> bool {
        exists|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape, field: CheckedStructureExpression|
            #[trigger] self.source_field_selection_case(context, layouts, types, inputs, prior, value, steps, at, shape, field)
    }

    #[verifier::opaque]
    pub(super) open spec fn source_field_selection_case(
        &self, context: &SourceFunc, layouts: &StructureLayouts, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
        steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape, field: CheckedStructureExpression,
    ) -> bool {
        let index = prior.len() as int;
        let parsed = context.parsed;
        let forms = parsed.syntax.forms@;
        let definition = context.wiring.drivers.definitions@[index].definition;
        let row = parsed.definitions@[definition as int];
        let frame = parsed.entry_ranges@[context.entry as int];
        let first = row.signals.start - frame.signals.start;
        let bound = context.wiring.signals@[first];
        let site = StructureExpressionContext { file: context.file, entry: context.entry, limit: context.limit,
            source: context.source, parsed, definition: (definition - frame.definitions.start) as usize };
        let bits = driver_values(inputs, prior, bound.driver);
        let range = field.1.range;
        &&& field_selection_shape_matches(context.source.text, forms, row.expression.start, steps, at, shape)
        &&& 0 <= first < context.wiring.signals@.len() && bound.definition == definition
        &&& is_form_location(context.source, forms[shape.input.start as int], bound.site)
        &&& signal_type_at(context.wiring, types.take(index), bound.driver) matches Some(input)
        &&& self.structure_expression_type_at_matches(&site, at, shape, layouts, input, Ok(field))
        &&& field.0.ty == ResolvedPortType::Bits((range.end - range.start) as u64)
        &&& field.2 == bits.len()
        &&& selection_chain_values_match(context.source, forms, steps, field.0.origin,
            bits.subrange(range.start as int, range.end as int), value)
    }

    pub(super) proof fn field_projection_preserves_rhs_value(
        &self, scope: &FuncProjection, definitions: Seq<CheckedBitDefinition>,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, checked: CheckedBitDefinition, at: int,
    )
        requires
            self.projection_context(scope),
            self.projection_structures_match(scope),
            values.len() == definitions.len() < scope.wiring.drivers.definitions@.len(),
            inputs.len() == scope.inputs@.len(),
            forall|i: int| 0 <= i < inputs.len() ==> (#[trigger] inputs[i]).len() == scope.inputs@[i],
            forall|i: int| 0 <= i < values.len() ==> (#[trigger] values[i]).len() == definitions[i].width,
            self.bit_definition_from_source(scope, definitions, definitions.len() as int, checked),
            0 <= at < scope.structures@.len(),
            scope.structures@[at].target == definitions.len(),
            scope.structures@[at].selection.is_some(),
        ensures self.source_field_selection_value(
            &SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
                source: scope.source, parsed: scope.parsed, wiring: scope.wiring },
            scope.layouts->Some_0, scope.types@, inputs, values, definition_values(checked.rhs, inputs, values),
        ),
    {
        let index = definitions.len() as int;
        let projection = scope.structures@[at];
        let layout = scope.layouts->Some_0;
        let found = choose|j: int| 0 <= j < scope.structures@.len() && {
            let row = #[trigger] scope.structures@[j];
            &&& row.target == index
            &&& bit_driver_width(scope.inputs@, definitions, row.input) == Some(row.input_width)
            &&& structure_rhs_matches(checked.rhs, row)
        };
        assert(found == at);
        let (steps, field_at, shape, field_type) = self.field_projection_evidence(scope.file, scope.entry,
            scope.limit, scope.wiring, *layout, scope.types@, projection);
        driver_value_length(scope, definitions, inputs, values, projection.input, projection.input_width);
        let range = projection.operation.range;
        let inner = contiguous_selection(range.start, range.end);
        let outer = projection.selection->Some_0;
        let combined = checked.rhs->Selection_selection;
        let bits = driver_values(inputs, values, projection.input);
        let field_bits = bits.subrange(range.start as int, range.end as int);
        let result = definition_values(checked.rhs, inputs, values);
        assert(inner.fits(projection.input_width));
        assert(outer.fits(inner.count));
        composed_selection_values_agree(bits, inner, outer, combined);
        assert(selected_bits_values(bits, inner.start, inner.count as nat, inner.stride) =~= field_bits);
        reveal(definition_values);
        assert(result =~= selected_bits_values(bits, combined.start, combined.count as nat, combined.stride));
        let forms = scope.parsed.syntax.forms@;
        selection_chain_projection_preserves_values(scope.source, forms, steps, field_type.origin, field_bits, outer);
        let context = SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
            source: scope.source, parsed: scope.parsed, wiring: scope.wiring };
        assert(self.source_field_selection_case(&context, layout, scope.types@, inputs, values, result, steps,
            field_at, shape, (field_type, projection.operation, projection.input_width))) by {
            reveal(UseAliases::source_field_selection_case);
        };
    }

    pub(super) proof fn source_field_selection_values_agree(
        &self, context: &SourceFunc, other: &SourceFunc, layouts: &StructureLayouts, other_layouts: &StructureLayouts,
        types: Seq<Option<SignalType>>, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
        a: (Seq<BitSelectionShape>, usize, StructureExpressionShape, CheckedStructureExpression),
        b: (Seq<BitSelectionShape>, usize, StructureExpressionShape, CheckedStructureExpression),
    )
        requires
            self.can_resolve(),
            same_source_bindings(context, other),
            prior.len() < context.wiring.drivers.definitions@.len(),
            self.structure_types_match(context.limit, Ok(*layouts)),
            self.structure_types_match(context.limit, Ok(*other_layouts)),
            self.source_field_selection_case(context, layouts, types, inputs, prior, left, a.0, a.1, a.2, a.3),
            self.source_field_selection_case(other, other_layouts, types, inputs, prior, right, b.0, b.1, b.2, b.3),
        ensures left == right,
    {
        reveal(UseAliases::source_field_selection_case);
        let index = prior.len() as int;
        let parsed = context.parsed;
        assert(same_definition_driver(context.wiring.drivers.definitions@[index], other.wiring.drivers.definitions@[index]));
        let definition = context.wiring.drivers.definitions@[index].definition;
        let row = parsed.definitions@[definition as int];
        let frame = parsed.entry_ranges@[context.entry as int];
        let bound = context.wiring.signals@[row.signals.start - frame.signals.start];
        let site = StructureExpressionContext { file: context.file, entry: context.entry, limit: context.limit,
            source: context.source, parsed, definition: (definition - frame.definitions.start) as usize };
        let input = signal_type_at(context.wiring, types.take(index), bound.driver)->Some_0;
        field_selection_shapes_agree(context.source.text, parsed.syntax.forms@, row.expression.start,
            a.0, a.1, a.2, b.0, b.1, b.2);
        self.checked_structure_expressions_agree_at(&site, a.1, a.2, layouts, other_layouts, input, a.3, b.3);
        let range = a.3.1.range;
        let bits = driver_values(inputs, prior, bound.driver).subrange(range.start as int, range.end as int);
        selection_chain_values_agree(context.source, parsed.syntax.forms@, a.0, a.3.0.origin, b.3.0.origin, bits, left, right);
    }
}

} // verus!
