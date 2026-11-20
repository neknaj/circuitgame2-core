//! 同じソースの同じ入力から得られる値が一意であることを示す。

use super::*;

verus! {

enum SourceRhsKind {
    Atom,
    Nor,
    Selection(BitSelectionShape),
    Structure(StructureExpressionShape),
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) proof fn source_values_prefix_agrees(
        &self, context: &SourceFunc, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, a: Seq<Seq<bool>>, b: Seq<Seq<bool>>, end: nat,
    )
        requires
            self.can_resolve(),
            parsed_circuit_matches(*context.source, *context.parsed),
            context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
            forall|i: int| 0 <= i < context.wiring.drivers.definitions@.len()
                ==> indexed_driver_site(context.source, context.parsed, context.entry as int,
                    #[trigger] context.wiring.drivers.definitions@[i]),
            self.source_definitions_evaluate(context, layouts, types, inputs, a),
            self.source_definitions_evaluate(context, layouts, types, inputs, b),
            end <= a.len(),
        ensures a.take(end as int) == b.take(end as int),
        decreases end,
    {
        reveal(UseAliases::source_definitions_evaluate);
        if end == 0 {
            assert(a.take(0) =~= b.take(0));
        } else {
            let i = (end - 1) as int;
            self.source_values_prefix_agrees(context, layouts, types, inputs, a, b, i as nat);
            assert(self.source_definition_value(context, layouts, types, inputs, a, i));
            assert(self.source_definition_value(context, layouts, types, inputs, b, i));
            reveal(UseAliases::source_definition_value);
            let driver = context.wiring.drivers.definitions@[i];
            assert(indexed_driver_site(context.source, context.parsed, context.entry as int, driver));
            self.source_rhs_values_agree(context, layouts, types, inputs, a.take(i), a[i], b[i]);
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
        &self, context: &SourceFunc, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
    )
        requires
            self.can_resolve(),
            parsed_circuit_matches(*context.source, *context.parsed),
            context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
            prior.len() < context.wiring.drivers.definitions@.len(),
            indexed_driver_site(context.source, context.parsed, context.entry as int,
                context.wiring.drivers.definitions@[prior.len() as int]),
            self.source_rhs_can_evaluate(context, layouts, types, inputs, prior, left),
            self.source_rhs_can_evaluate(context, layouts, types, inputs, prior, right),
        ensures left == right,
    {
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let row = context.parsed.definitions@[definition as int];
        let forms = context.parsed.syntax.forms@;
        let root = row.expression.start as int;
        let a = self.source_rhs_kind(context, layouts, types, inputs, prior, left);
        let b = self.source_rhs_kind(context, layouts, types, inputs, prior, right);
        match (a, b) {
            (SourceRhsKind::Atom, SourceRhsKind::Atom) =>
                atomic_values_agree(context, definition, root, inputs, prior, left, right),
            (SourceRhsKind::Nor, SourceRhsKind::Nor) =>
                self.source_nor_values_agree(context, inputs, prior, left, right),
            (SourceRhsKind::Selection(_), SourceRhsKind::Selection(_)) =>
                self.source_selection_values_agree(context, inputs, prior, left, right),
            (SourceRhsKind::Structure(_), SourceRhsKind::Structure(_)) =>
                self.source_structure_values_agree(context, layouts->Some_0, types, inputs, prior, left, right),
            (SourceRhsKind::Nor, _) | (_, SourceRhsKind::Nor) =>
                ordinary_call_excludes_special_forms(context.source.text, forms, root, row.expression.end as int),
            (SourceRhsKind::Selection(shape), SourceRhsKind::Structure(_))
            | (SourceRhsKind::Structure(_), SourceRhsKind::Selection(shape)) =>
                bit_selection_excludes_structure(context.source.text, forms, root, shape),
            _ => {},
        }
    }


    proof fn source_rhs_kind(
        &self, context: &SourceFunc, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> (kind: SourceRhsKind)
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
                SourceRhsKind::Selection(shape) => forms[root] is List
                    && named_selection_matches(context.source.text, forms, root, shape)
                    && self.source_selection_value(context, inputs, prior, value),
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
        } else if self.source_selection_value(context, inputs, prior, value) {
            let (shape, driver, selection, origin) = self.source_selection_witness(context, inputs, prior, value);
            reveal(UseAliases::source_selection_case);
            assert(self.source_selection_case(context, inputs, prior, value, shape, driver, selection, origin));
            SourceRhsKind::Selection(shape)
        } else {
            let table = layouts->Some_0;
            reveal(UseAliases::structure_source_rhs_value);
            let (shape, checked) = choose|shape: StructureExpressionShape, checked: CheckedStructureExpression|
                #[trigger] self.source_structure_case(context, table, types, inputs, prior, value, shape, checked);
            reveal(UseAliases::source_structure_case);
            assert(self.source_structure_case(context, table, types, inputs, prior, value, shape, checked));
            SourceRhsKind::Structure(shape)
        }
    }

    proof fn source_nor_values_agree(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
    )
        requires
            parsed_circuit_matches(*context.source, *context.parsed),
            context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
            indexed_driver_site(context.source, context.parsed, context.entry as int,
                context.wiring.drivers.definitions@[prior.len() as int]),
            self.source_nor_value(context, inputs, prior, left),
            self.source_nor_value(context, inputs, prior, right),
        ensures left == right,
    {
        let (call_a, a0, a1) = choose|call: TypedFuncCall, a: Seq<bool>, b: Seq<bool>|
            #[trigger] self.source_nor_operands(context, inputs, prior, call, a, b)
                && left == seq![!(a[0] || b[0])];
        let (call_b, b0, b1) = choose|call: TypedFuncCall, a: Seq<bool>, b: Seq<bool>|
            #[trigger] self.source_nor_operands(context, inputs, prior, call, a, b)
                && right == seq![!(a[0] || b[0])];
        reveal(UseAliases::source_nor_operands);
        assert(self.source_nor_operands(context, inputs, prior, call_a, a0, a1));
        assert(self.source_nor_operands(context, inputs, prior, call_b, b0, b1));
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let root = context.parsed.definitions@[definition as int].expression.start as int;
        atomic_values_agree(context, definition, root + 2, inputs, prior, a0, b0);
        atomic_values_agree(context, definition, root + 3, inputs, prior, a1, b1);
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
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
    )
        requires
            parsed_circuit_matches(*context.source, *context.parsed),
            context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
            indexed_driver_site(context.source, context.parsed, context.entry as int,
                context.wiring.drivers.definitions@[prior.len() as int]),
            self.source_selection_value(context, inputs, prior, left),
            self.source_selection_value(context, inputs, prior, right),
        ensures left == right,
    {
        let (shape_a, driver_a, selection_a, origin_a) = self.source_selection_witness(context, inputs, prior, left);
        let (shape_b, driver_b, selection_b, origin_b) = self.source_selection_witness(context, inputs, prior, right);
        reveal(UseAliases::source_selection_case);
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let root = context.parsed.definitions@[definition as int].expression.start as int;
        let forms = context.parsed.syntax.forms@;
        bit_selection_shapes_agree(context.source.text, forms, root, shape_a, shape_b);
        source_operands_agree(context.source, context.parsed, context.entry, definition, shape_a.input.start as int,
            context.wiring, prior.len() as int, SingleBitOperand::Driver(driver_a), SingleBitOperand::Driver(driver_b));
        let width = driver_values(inputs, prior, driver_a).len() as u64;
        successful_selections_agree(context.source, forms, &shape_a, width, &origin_a, selection_a,
            width, &origin_b, selection_b);
        assert(left =~= right);
    }
}

proof fn atomic_values_agree(
    context: &SourceFunc, definition: usize, form: int,
    inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
)
    requires
        parsed_circuit_matches(*context.source, *context.parsed),
        context.entry < context.parsed.syntax.entries@.len() && context.entry < context.parsed.entry_ranges@.len(),
        context.parsed.entry_ranges@[context.entry as int].definitions.start <= definition
            < context.parsed.entry_ranges@[context.entry as int].definitions.end,
        atomic_value(context, definition, form, inputs, prior, left),
        atomic_value(context, definition, form, inputs, prior, right),
    ensures left == right,
{
    let a = choose|operand: SingleBitOperand|
        #[trigger] operand_matches(context.source, context.parsed, context.entry, definition, form,
            context.wiring, prior.len() as int, operand) && left == atom_result(inputs, prior, operand);
    let b = choose|operand: SingleBitOperand|
        #[trigger] operand_matches(context.source, context.parsed, context.entry, definition, form,
            context.wiring, prior.len() as int, operand) && right == atom_result(inputs, prior, operand);
    source_operands_agree(context.source, context.parsed, context.entry, definition, form,
        context.wiring, prior.len() as int, a, b);
}

} // verus!
