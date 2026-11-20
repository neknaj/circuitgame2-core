//! 同じソースの同じ入力から得られる値が一意であることを示す。

use super::*;
use crate::syntax::circuit::{concat_argument_ranges_agree, concat_excludes_other_shapes, field_selection_root, field_selection_shape_matches};
use super::super::super::super::selection_arguments::field_and_named_selection_disjoint;

verus! {

enum SourceRhsKind<'p, 'a> {
    Atom,
    Nor,
    Concat(core::ops::Range<usize>, Seq<Seq<bool>>),
    Selection(BitSelectionShape),
    NestedSelection(Seq<BitSelectionShape>, usize),
    FieldSelection((Seq<BitSelectionShape>, usize, StructureExpressionShape, CheckedStructureExpression<'p, 'a>)),
    Structure(StructureExpressionShape),
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) proof fn source_values_prefix_agrees(
        &self, context: &SourceFunc, other: &SourceFunc, layouts: Option<&StructureLayouts>,
        other_layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, a: Seq<Seq<bool>>, b: Seq<Seq<bool>>, end: nat,
    )
        requires
            self.can_resolve(),
            parsed_circuit_matches(*context.source, *context.parsed),
            context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
            forall|i: int| 0 <= i < context.wiring.drivers.definitions@.len()
                ==> indexed_driver_site(context.source, context.parsed, context.entry as int,
                    #[trigger] context.wiring.drivers.definitions@[i]),
            same_source_bindings(context, other),
            self.structure_layout_for_ports(context.limit, layouts),
            self.structure_layout_for_ports(context.limit, other_layouts),
            self.source_definitions_evaluate(context, layouts, types, inputs, a),
            self.source_definitions_evaluate(other, other_layouts, types, inputs, b),
            end <= a.len(),
        ensures a.take(end as int) == b.take(end as int),
        decreases end,
    {
        reveal(UseAliases::source_definitions_evaluate);
        if end == 0 {
            assert(a.take(0) =~= b.take(0));
        } else {
            let i = (end - 1) as int;
            self.source_values_prefix_agrees(context, other, layouts, other_layouts, types, inputs, a, b, i as nat);
            assert(self.source_definition_value(context, layouts, types, inputs, a, i));
            assert(self.source_definition_value(other, other_layouts, types, inputs, b, i));
            reveal(UseAliases::source_definition_value);
            let driver = context.wiring.drivers.definitions@[i];
            assert(indexed_driver_site(context.source, context.parsed, context.entry as int, driver));
            self.source_rhs_values_agree(context, other, layouts, other_layouts, types, inputs, a.take(i), a[i], b[i]);
            assert forall|j: int| 0 <= j < end implies
                (#[trigger] a.take(end as int)[j]) == (#[trigger] b.take(end as int)[j]) by {
                if j < i {
                    assert(a.take(i)[j] == b.take(i)[j]);
                }
            };
            assert(a.take(end as int) =~= b.take(end as int));
        }
    }

    proof fn source_rhs_values_agree(
        &self, context: &SourceFunc, other: &SourceFunc, layouts: Option<&StructureLayouts>,
        other_layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
    )
        requires
            self.can_resolve(),
            parsed_circuit_matches(*context.source, *context.parsed),
            context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
            prior.len() < context.wiring.drivers.definitions@.len(),
            indexed_driver_site(context.source, context.parsed, context.entry as int,
                context.wiring.drivers.definitions@[prior.len() as int]),
            same_source_bindings(context, other),
            self.structure_layout_for_ports(context.limit, layouts),
            self.structure_layout_for_ports(context.limit, other_layouts),
            self.source_rhs_can_evaluate(context, layouts, types, inputs, prior, left),
            self.source_rhs_can_evaluate(other, other_layouts, types, inputs, prior, right),
        ensures left == right,
    {
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let row = context.parsed.definitions@[definition as int];
        let forms = context.parsed.syntax.forms@;
        let root = row.expression.start as int;
        let a = self.source_rhs_kind(context, layouts, types, inputs, prior, left);
        let b = self.source_rhs_kind(other, other_layouts, types, inputs, prior, right);
        assert(same_definition_driver(context.wiring.drivers.definitions@[prior.len() as int],
            other.wiring.drivers.definitions@[prior.len() as int]));
        match (a, b) {
            (SourceRhsKind::Atom, SourceRhsKind::Atom) =>
                atomic_values_agree(context, other, definition, root, inputs, prior, left, right),
            (SourceRhsKind::Nor, SourceRhsKind::Nor) =>
                self.source_nor_values_agree(context, other, inputs, prior, left, right),
            (SourceRhsKind::Concat(ar, ap), SourceRhsKind::Concat(br, bp)) => {
                reveal(UseAliases::source_concat_case);
                assert(self.source_concat_case(context, inputs, prior, left, ar, ap));
                assert(self.source_concat_case(other, inputs, prior, right, br, bp));
                concat_argument_ranges_agree(context.source.text, forms, root, ar, br);
                assert forall|j: int| 0 <= j < ap.len() implies (#[trigger] ap[j]) == bp[j] by {
                    atomic_values_agree(context, other, definition, ar.start + j, inputs, prior, ap[j], bp[j]);
                };
                assert(ap =~= bp);
            },
            (SourceRhsKind::Selection(_), SourceRhsKind::Selection(_)) =>
                self.source_selection_values_agree(context, other, inputs, prior, left, right),
            (SourceRhsKind::NestedSelection(a, al), SourceRhsKind::NestedSelection(b, bl)) =>
                self.source_nested_selection_values_agree(context, other, inputs, prior, left, right, a, al, b, bl),
            (SourceRhsKind::FieldSelection(a), SourceRhsKind::FieldSelection(b)) =>
                self.source_field_selection_values_agree(context, other, layouts->Some_0, other_layouts->Some_0,
                    types, inputs, prior, left, right, a, b),
            (SourceRhsKind::Structure(_), SourceRhsKind::Structure(_)) =>
                self.source_structure_values_agree(context, other, layouts->Some_0, other_layouts->Some_0, types, inputs, prior, left, right),
            (SourceRhsKind::Nor, _) | (_, SourceRhsKind::Nor) =>
                ordinary_call_excludes_special_forms(context.source.text, forms, root, row.expression.end as int),
            (SourceRhsKind::Concat(arguments, _), _) | (_, SourceRhsKind::Concat(arguments, _)) =>
                concat_excludes_other_shapes(context.source.text, forms, root, arguments),
            (SourceRhsKind::Selection(shape), SourceRhsKind::Structure(_))
            | (SourceRhsKind::Structure(_), SourceRhsKind::Selection(shape)) =>
                bit_selection_excludes_structure(context.source.text, forms, root, shape),
            (SourceRhsKind::NestedSelection(steps, leaf), SourceRhsKind::Structure(_))
            | (SourceRhsKind::Structure(_), SourceRhsKind::NestedSelection(steps, leaf)) => {
                nested_named_selection_root(context.source.text, forms, root as usize, steps, leaf);
                bit_selection_excludes_structure(context.source.text, forms, root, steps[0]);
            },
            (SourceRhsKind::NestedSelection(steps, leaf), SourceRhsKind::Selection(shape))
            | (SourceRhsKind::Selection(shape), SourceRhsKind::NestedSelection(steps, leaf)) => {
                nested_named_selection_root(context.source.text, forms, root as usize, steps, leaf);
                bit_selection_shapes_agree(context.source.text, forms, root, steps[0], shape);
            },
            (SourceRhsKind::FieldSelection((steps, at, shape, _)), SourceRhsKind::NestedSelection(other, name))
            | (SourceRhsKind::NestedSelection(other, name), SourceRhsKind::FieldSelection((steps, at, shape, _))) =>
                field_and_named_selection_disjoint(context.source.text, forms, root as usize, steps, at, shape, other, name),
            (SourceRhsKind::FieldSelection((steps, _, _, _)), SourceRhsKind::Selection(shape))
            | (SourceRhsKind::Selection(shape), SourceRhsKind::FieldSelection((steps, _, _, _))) =>
                bit_selection_shapes_agree(context.source.text, forms, root, steps[0], shape),
            (SourceRhsKind::FieldSelection((steps, _, _, _)), SourceRhsKind::Structure(_))
            | (SourceRhsKind::Structure(_), SourceRhsKind::FieldSelection((steps, _, _, _))) =>
                bit_selection_excludes_structure(context.source.text, forms, root, steps[0]),
            _ => {},
        }
    }


    proof fn source_rhs_kind(
        &self, context: &SourceFunc, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> (kind: SourceRhsKind<'p, 'a>)
        requires self.source_rhs_can_evaluate(context, layouts, types, inputs, prior, value),
        ensures ({
            let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
            let row = context.parsed.definitions@[definition as int];
            let root = row.expression.start as int;
            let forms = context.parsed.syntax.forms@;
            match kind {
                SourceRhsKind::Atom => forms[root] is Atom
                    && atomic_value(context, definition, root, inputs, prior, value),
                SourceRhsKind::Nor => forms[root] is List
                    && ordinary_call_at(context.source.text, forms, root, row.expression.end as int)
                    && self.source_nor_value(context, inputs, prior, value),
                SourceRhsKind::Concat(arguments, parts) => forms[root] is List
                    && concat_arguments_match(context.source.text, forms, root, arguments)
                    && self.source_concat_case(context, inputs, prior, value, arguments, parts),
                SourceRhsKind::Selection(shape) => forms[root] is List
                    && named_selection_matches(context.source.text, forms, root, shape)
                    && self.source_selection_value(context, inputs, prior, value),
                SourceRhsKind::NestedSelection(steps, leaf) => forms[root] is List
                    && bit_selection_shape_matches(context.source.text, forms, root, steps[0])
                    && nested_named_selection_matches(context.source.text, forms, root as usize, steps, leaf)
                    && exists|driver: OutputDriver, origin: LocatedName|
                        #[trigger] self.source_nested_selection_case(context, inputs, prior, value, steps, leaf, driver, origin),
                SourceRhsKind::FieldSelection((steps, at, shape, field)) => forms[root] is List
                    && bit_selection_shape_matches(context.source.text, forms, root, steps[0])
                    && forms[steps[0].input.start as int] is List
                    && field_selection_shape_matches(context.source.text, forms, root as usize, steps, at, shape)
                    && (layouts matches Some(table) && self.source_field_selection_case(
                        context, table, types, inputs, prior, value, steps, at, shape, field)),
                SourceRhsKind::Structure(shape) => forms[root] is List
                    && structure_expression_matches(context.source.text, forms, root, shape)
                    && (layouts matches Some(table) && self.structure_source_rhs_value(context, table, types, inputs, prior, value)),
            }
        }),
    {
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let root = context.parsed.definitions@[definition as int].expression.start as int;
        reveal(UseAliases::ordinary_source_rhs_value);
        if atomic_value(context, definition, root, inputs, prior, value) {
            SourceRhsKind::Atom
        } else if self.source_nor_value(context, inputs, prior, value) {
            let (call, left, right) = choose|call: TypedFuncCall, left: Seq<bool>, right: Seq<bool>|
                #[trigger] self.source_nor_operands(context, inputs, prior, call, left, right)
                && value == seq![!(left[0] || right[0])];
            reveal(UseAliases::source_nor_operands);
            assert(self.source_nor_operands(context, inputs, prior, call, left, right));
            SourceRhsKind::Nor
        } else if self.source_concat_value(context, inputs, prior, value) {
            let (arguments, parts) = choose|arguments: core::ops::Range<usize>, parts: Seq<Seq<bool>>|
                #[trigger] self.source_concat_case(context, inputs, prior, value, arguments, parts);
            reveal(UseAliases::source_concat_case);
            assert(self.source_concat_case(context, inputs, prior, value, arguments, parts));
            concat_excludes_other_shapes(context.source.text, context.parsed.syntax.forms@, root, arguments);
            SourceRhsKind::Concat(arguments, parts)
        } else if self.source_selection_value(context, inputs, prior, value) {
            let (shape, driver, selection, origin) = self.source_selection_witness(context, inputs, prior, value);
            reveal(UseAliases::source_selection_case);
            assert(self.source_selection_case(context, inputs, prior, value, shape, driver, selection, origin));
            SourceRhsKind::Selection(shape)
        } else if self.source_nested_selection_value(context, inputs, prior, value) {
            let (steps, leaf, driver, origin) = choose|
                steps: Seq<BitSelectionShape>, leaf: usize, driver: OutputDriver, origin: LocatedName|
                #[trigger] self.source_nested_selection_case(context, inputs, prior, value, steps, leaf, driver, origin);
            reveal(UseAliases::source_nested_selection_case);
            assert(self.source_nested_selection_case(context, inputs, prior, value, steps, leaf, driver, origin));
            nested_named_selection_root(context.source.text, context.parsed.syntax.forms@, root as usize, steps, leaf);
            SourceRhsKind::NestedSelection(steps, leaf)
        } else {
            let table = layouts->Some_0;
            if self.source_field_selection_value(context, table, types, inputs, prior, value) {
                let (steps, at, shape, field) = choose|
                    steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape, field: CheckedStructureExpression|
                    #[trigger] self.source_field_selection_case(context, table, types, inputs, prior, value, steps, at, shape, field);
                reveal(UseAliases::source_field_selection_case);
                assert(self.source_field_selection_case(context, table, types, inputs, prior, value, steps, at, shape, field));
                field_selection_root(context.source.text, context.parsed.syntax.forms@, root as usize, steps, at, shape);
                return SourceRhsKind::FieldSelection((steps, at, shape, field));
            }
            reveal(UseAliases::structure_source_rhs_value);
            let (shape, checked) = choose|shape: StructureExpressionShape, checked: CheckedStructureExpression|
                #[trigger] self.source_structure_case(context, table, types, inputs, prior, value, shape, checked);
            reveal(UseAliases::source_structure_case);
            assert(self.source_structure_case(context, table, types, inputs, prior, value, shape, checked));
            SourceRhsKind::Structure(shape)
        }
    }

    proof fn source_nested_selection_values_agree(
        &self, context: &SourceFunc, other: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>,
        left: Seq<bool>, right: Seq<bool>, left_steps: Seq<BitSelectionShape>, left_leaf: usize,
        right_steps: Seq<BitSelectionShape>, right_leaf: usize,
    )
        requires
            parsed_circuit_matches(*context.source, *context.parsed),
            context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
            indexed_driver_site(context.source, context.parsed, context.entry as int,
                context.wiring.drivers.definitions@[prior.len() as int]),
            same_source_bindings(context, other),
            prior.len() < context.wiring.drivers.definitions@.len(),
            exists|driver: OutputDriver, origin: LocatedName|
                #[trigger] self.source_nested_selection_case(context, inputs, prior, left, left_steps, left_leaf, driver, origin),
            exists|driver: OutputDriver, origin: LocatedName|
                #[trigger] self.source_nested_selection_case(other, inputs, prior, right, right_steps, right_leaf, driver, origin),
        ensures left == right,
    {
        reveal(UseAliases::source_nested_selection_case);
        let (a, a_origin) = choose|driver: OutputDriver, origin: LocatedName|
            #[trigger] self.source_nested_selection_case(context, inputs, prior, left, left_steps, left_leaf, driver, origin);
        let (b, b_origin) = choose|driver: OutputDriver, origin: LocatedName|
            #[trigger] self.source_nested_selection_case(other, inputs, prior, right, right_steps, right_leaf, driver, origin);
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let row = context.parsed.definitions@[definition as int];
        let forms = context.parsed.syntax.forms@;
        nested_named_selections_agree(context.source.text, forms, row.expression.start, left_steps, left_leaf,
            right_steps, right_leaf);
        source_operands_agree(context.source, context.parsed, context.entry, definition, left_leaf as int,
            context.wiring, other.wiring, prior.len() as int, SingleBitOperand::Driver(a), SingleBitOperand::Driver(b));
        selection_chain_values_agree(context.source, forms, left_steps, a_origin, b_origin,
            driver_values(inputs, prior, a), left, right);
    }

    proof fn source_nor_values_agree(
        &self, context: &SourceFunc, other: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
    )
        requires
            parsed_circuit_matches(*context.source, *context.parsed),
            context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
            indexed_driver_site(context.source, context.parsed, context.entry as int,
                context.wiring.drivers.definitions@[prior.len() as int]),
            same_source_bindings(context, other),
            prior.len() < context.wiring.drivers.definitions@.len(),
            self.source_nor_value(context, inputs, prior, left),
            self.source_nor_value(other, inputs, prior, right),
        ensures left == right,
    {
        let (call_a, a0, a1) = choose|call: TypedFuncCall, a: Seq<bool>, b: Seq<bool>|
            #[trigger] self.source_nor_operands(context, inputs, prior, call, a, b)
                && left == seq![!(a[0] || b[0])];
        let (call_b, b0, b1) = choose|call: TypedFuncCall, a: Seq<bool>, b: Seq<bool>|
            #[trigger] self.source_nor_operands(other, inputs, prior, call, a, b)
                && right == seq![!(a[0] || b[0])];
        reveal(UseAliases::source_nor_operands);
        assert(self.source_nor_operands(context, inputs, prior, call_a, a0, a1));
        assert(self.source_nor_operands(other, inputs, prior, call_b, b0, b1));
        assert(same_definition_driver(context.wiring.drivers.definitions@[prior.len() as int],
            other.wiring.drivers.definitions@[prior.len() as int]));
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let root = context.parsed.definitions@[definition as int].expression.start as int;
        atomic_values_agree(context, other, definition, root + 2, inputs, prior, a0, b0);
        atomic_values_agree(context, other, definition, root + 3, inputs, prior, a1, b1);
    }

    proof fn source_selection_witness(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> (found: (BitSelectionShape, OutputDriver, CheckedBitSelection, LocatedName<'p, 'a>))
        requires self.source_selection_value(context, inputs, prior, value),
        ensures self.source_selection_case(context, inputs, prior, value, found.0, found.1, found.2, found.3),
    {
        choose|shape: BitSelectionShape, driver: OutputDriver, selection: CheckedBitSelection, origin: LocatedName<'p, 'a>|
            #[trigger] self.source_selection_case(context, inputs, prior, value, shape, driver, selection, origin)
    }

    proof fn source_selection_values_agree(
        &self, context: &SourceFunc, other: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
    )
        requires
            parsed_circuit_matches(*context.source, *context.parsed),
            context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
            indexed_driver_site(context.source, context.parsed, context.entry as int,
                context.wiring.drivers.definitions@[prior.len() as int]),
            same_source_bindings(context, other),
            prior.len() < context.wiring.drivers.definitions@.len(),
            self.source_selection_value(context, inputs, prior, left),
            self.source_selection_value(other, inputs, prior, right),
        ensures left == right,
    {
        let (shape_a, driver_a, selection_a, origin_a) = self.source_selection_witness(context, inputs, prior, left);
        let (shape_b, driver_b, selection_b, origin_b) = self.source_selection_witness(other, inputs, prior, right);
        reveal(UseAliases::source_selection_case);
        assert(same_definition_driver(context.wiring.drivers.definitions@[prior.len() as int],
            other.wiring.drivers.definitions@[prior.len() as int]));
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let root = context.parsed.definitions@[definition as int].expression.start as int;
        let forms = context.parsed.syntax.forms@;
        bit_selection_shapes_agree(context.source.text, forms, root, shape_a, shape_b);
        source_operands_agree(context.source, context.parsed, context.entry, definition, shape_a.input.start as int,
            context.wiring, other.wiring, prior.len() as int, SingleBitOperand::Driver(driver_a), SingleBitOperand::Driver(driver_b));
        let width = driver_values(inputs, prior, driver_a).len() as u64;
        successful_selections_agree(context.source, forms, &shape_a, width, &origin_a, selection_a,
            width, &origin_b, selection_b);
        assert(left =~= right);
    }
}

proof fn atomic_values_agree(
    context: &SourceFunc, other: &SourceFunc, definition: usize, form: int,
    inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
)
    requires
        parsed_circuit_matches(*context.source, *context.parsed),
        context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
        context.parsed.entry_ranges@[context.entry as int].definitions.start <= definition
            < context.parsed.entry_ranges@[context.entry as int].definitions.end,
        same_source_bindings(context, other),
        atomic_value(context, definition, form, inputs, prior, left),
        atomic_value(other, definition, form, inputs, prior, right),
    ensures left == right,
{
    let a = choose|operand: SingleBitOperand|
        #[trigger] operand_matches(context.source, context.parsed, context.entry, definition, form,
            context.wiring, prior.len() as int, operand) && left == atom_result(inputs, prior, operand);
    let b = choose|operand: SingleBitOperand|
        #[trigger] operand_matches(other.source, other.parsed, other.entry, definition, form,
            other.wiring, prior.len() as int, operand) && right == atom_result(inputs, prior, operand);
    source_operands_agree(context.source, context.parsed, context.entry, definition, form,
        context.wiring, other.wiring, prior.len() as int, a, b);
}

} // verus!
