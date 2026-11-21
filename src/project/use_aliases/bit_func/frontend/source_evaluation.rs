//! 厳格解析した関数の構文と信号の束縛から右辺の値を定める。

mod determinism;
mod field_selection;
mod project;

use super::*;
use super::super::semantics::{
    bit_func_definitions_match, bit_func_evaluation, bit_func_evaluation_values, bit_func_inputs_match,
    checked_definition_values, concat_operand_values, contiguous_rhs_preserves_range, definition_values, driver_values,
};
use super::super::super::function_atoms::named_structure_expression_matches;
use super::super::super::function_atoms::concat_projection_positions;
use super::super::super::function_drivers::same_definition_driver;
use super::super::super::selection_arguments::{
    nested_named_selection_matches, nested_named_selection_root, nested_named_selections_agree, selection_chain_values_agree,
    selection_chain_projection_preserves_values, selection_chain_values_match, successful_selections_agree,
};
use super::super::super::single_bit_func::{source_operand_is_atom, source_operands_agree};
use super::super::super::structure_types::{CheckedStructureExpression, StructureExpressionContext};
use crate::syntax::circuit::{
    StructureExpressionShape, bit_selection_excludes_structure, bit_selection_shape_matches, bit_selection_shapes_agree,
    concat_arguments_match, indexed_call_arguments, ordinary_call_at, ordinary_call_excludes_special_forms,
    structure_expression_matches, structure_expression_positions, structure_expression_shapes_agree,
};
use super::super::{LoweredBitFunc, bit_func_lowering_preserves_evaluation, lowered_bit_func_result, port_values};
use super::super::lowering::{
    expanded_definition_values, projected_lowering_local_values, projected_lowering_view,
};
use super::super::expansion::CheckedExpansionCall;
use super::super::templates::ResolvedTemplateCall;
use crate::netlist::{NorEvaluationError, gate_values_match, nor_evaluation_result};
use crate::syntax::{bit_literal_value_at, form_span};

verus! {

struct SourceFunc<'w, 'p, 'a> {
    file: usize,
    entry: usize,
    limit: u64,
    source: &'p ProjectSource<'a>,
    parsed: &'p NamedBuildCircuit<'a>,
    wiring: &'w FuncWiring<'p, 'a>,
}

spec fn same_source_bindings(context: &SourceFunc, other: &SourceFunc) -> bool {
    &&& context.file == other.file && context.entry == other.entry && context.limit == other.limit
    &&& context.source == other.source && context.parsed == other.parsed
    &&& context.wiring.drivers.signature.inputs@ == other.wiring.drivers.signature.inputs@
    &&& context.wiring.signals@ == other.wiring.signals@
    &&& context.wiring.drivers.definitions@.len() == other.wiring.drivers.definitions@.len()
    &&& forall|i: int| 0 <= i < context.wiring.drivers.definitions@.len() ==>
        same_definition_driver(#[trigger] context.wiring.drivers.definitions@[i],
            #[trigger] other.wiring.drivers.definitions@[i])
}

spec fn atomic_value(
    context: &SourceFunc, definition: usize, form: int,
    inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
) -> bool {
    &&& 0 <= form < context.parsed.syntax.forms@.len()
    &&& context.parsed.syntax.forms@[form] is Atom
    &&& exists|operand: SingleBitOperand|
        #[trigger] operand_matches(context.source, context.parsed, context.entry, definition, form,
            context.wiring, prior.len() as int, operand)
        && value == atom_result(inputs, prior, operand)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn source_inputs_match(
        &self, wiring: &FuncWiring, layouts: Option<&StructureLayouts>, inputs: Seq<Seq<bool>>,
    ) -> bool {
        let ports = wiring.drivers.signature.inputs@;
        &&& inputs.len() == ports.len()
        &&& forall|i: int| 0 <= i < inputs.len() ==> {
            let width = (#[trigger] inputs[i]).len();
            width <= u64::MAX && self.port_width_matches(ports[i].ty, width as u64, layouts)
        }
    }

    /// 検査済みの型と配置に従い、ソースで結線された出力を宣言順に評価する。
    pub closed spec fn source_func_evaluation(
        &self, file: usize, entry: usize, limit: u64, typed: &FuncSignalTypes, layouts: Option<&StructureLayouts>,
        inputs: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
    ) -> bool {
        let project = self.targets.project_model();
        &&& self.can_resolve()
        &&& file < project.sources_model().len() && file < project.circuits_model().len()
        &&& self.func_signal_types_evidence(file, entry, limit, Ok(*typed))
        &&& self.structure_layout_for_ports(limit, layouts)
        &&& typed.literals.wiring matches FuncWiringResult::Checked(wiring) && {
            let source = &project.sources_model()[file as int];
            let parsed = &project.circuits_model()[file as int];
            let context = SourceFunc { file, entry, limit, source, parsed, wiring: &wiring };
            &&& entry < parsed.syntax.entries@.len() && parsed.syntax.entries@[entry as int].head is Func
            &&& self.source_inputs_match(&wiring, layouts, inputs)
            &&& exists|values: Seq<Seq<bool>>| #[trigger]
                self.source_definitions_evaluate(&context, layouts, typed.types@, inputs, values)
                && source_outputs_match(&wiring, inputs, values, outputs)
        }
    }

    /// 同じ型・配置・入力に対する二つのソース評価の出力は、宣言順に一致する。
    pub proof fn source_func_evaluations_agree(
        &self, file: usize, entry: usize, limit: u64, typed: &FuncSignalTypes, layouts: Option<&StructureLayouts>,
        inputs: Seq<Seq<bool>>, left: Seq<Seq<bool>>, right: Seq<Seq<bool>>,
    )
        requires
            self.source_func_evaluation(file, entry, limit, typed, layouts, inputs, left),
            self.source_func_evaluation(file, entry, limit, typed, layouts, inputs, right),
        ensures left == right,
    {
        self.source_func_evaluations_agree_across_checks(file, entry, limit, typed, layouts, typed, layouts, inputs, left, right);
    }

    /// 同じ関数・幅上限・入力で評価に成功すると、型と配置を別々に検査しても出力が宣言順に一致する。
    pub proof fn source_func_evaluations_agree_across_checks(
        &self, file: usize, entry: usize, limit: u64, typed: &FuncSignalTypes, layouts: Option<&StructureLayouts>,
        other_typed: &FuncSignalTypes, other_layouts: Option<&StructureLayouts>,
        inputs: Seq<Seq<bool>>, left: Seq<Seq<bool>>, right: Seq<Seq<bool>>,
    )
        requires
            self.source_func_evaluation(file, entry, limit, typed, layouts, inputs, left),
            self.source_func_evaluation(file, entry, limit, other_typed, other_layouts, inputs, right),
        ensures left == right,
    {
        let project = self.targets.project_model();
        let wiring = typed.literals.wiring->Checked_0;
        let other_wiring = other_typed.literals.wiring->Checked_0;
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let context = SourceFunc { file, entry, limit, source, parsed, wiring: &wiring };
        let other = SourceFunc { file, entry, limit, source, parsed, wiring: &other_wiring };
        self.checked_types_keep_wiring(file, entry, limit, *typed, wiring);
        self.checked_types_keep_wiring(file, entry, limit, *other_typed, other_wiring);
        self.checked_wiring_is_func(file, entry, limit, wiring);
        self.checked_func_wiring_agrees(file, entry, limit, wiring, other_wiring);
        self.checked_function_signal_types_agree(file, entry, limit, *typed, *other_typed);
        assert(same_source_bindings(&context, &other));
        self.targets.parsed_project_model();
        let a = choose|values: Seq<Seq<bool>>| #[trigger]
            self.source_definitions_evaluate(&context, layouts, typed.types@, inputs, values)
                && source_outputs_match(&wiring, inputs, values, left);
        let b = choose|values: Seq<Seq<bool>>| #[trigger]
            self.source_definitions_evaluate(&other, other_layouts, other_typed.types@, inputs, values)
                && source_outputs_match(&other_wiring, inputs, values, right);
        reveal(UseAliases::source_definitions_evaluate);
        self.source_values_prefix_agrees(&context, &other, layouts, other_layouts, typed.types@, inputs, a, b, a.len());
        assert(a.len() == b.len());
        assert(a.take(a.len() as int) =~= a);
        assert(b.take(a.len() as int) =~= b);
        assert(a == b);
        assert(left.len() == right.len());
        assert forall|i: int| 0 <= i < left.len() implies (#[trigger] left[i]) == (#[trigger] right[i]) by {
            assert(source_output_at(&wiring, inputs, a, left, i));
            assert(source_output_at(&other_wiring, inputs, b, right, i));
        };
        assert(left =~= right);
    }

    proof fn checked_evaluation_preserves_source_values(
        &self, file: usize, entry: usize, limit: u64, checked: &CheckedBitFunc,
        inputs: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
    )
        requires
            self.checked_bit_func_matches(file, entry, limit, checked),
            bit_func_evaluation(checked, inputs, outputs),
        ensures exists|typed: FuncSignalTypes, layouts: Option<&StructureLayouts>| #[trigger]
            self.source_func_evaluation(file, entry, limit, &typed, layouts, inputs, outputs),
    {
        let (typed, layouts, structures) = choose|
            typed: FuncSignalTypes, layouts: Option<&StructureLayouts>, structures: Vec<StructureProjection>
        | #![trigger self.func_signal_types_evidence(file, entry, limit, Ok(typed)), self.structure_layout_for_ports(limit, layouts), structures@]
            self.checked_bit_func_projection(file, entry, limit, checked, typed, layouts, structures);
        self.projected_evaluation_preserves_source_values(file, entry, limit, checked, typed, layouts, structures, inputs, outputs);
    }

    proof fn projected_evaluation_preserves_source_values(
        &self, file: usize, entry: usize, limit: u64, checked: &CheckedBitFunc,
        typed: FuncSignalTypes, layouts: Option<&StructureLayouts>, structures: Vec<StructureProjection>,
        inputs: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
    )
        requires
            self.checked_bit_func_projection(file, entry, limit, checked, typed, layouts, structures),
            bit_func_evaluation(checked, inputs, outputs),
        ensures self.source_func_evaluation(file, entry, limit, &typed, layouts, inputs, outputs),
    {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let wiring = typed.literals.wiring->Checked_0;
        let scope = FuncProjection { file, entry, limit, source, parsed, wiring: &wiring,
            inputs: &checked.input_widths, outputs: &checked.output_widths, layouts, types: &typed.types, structures: &structures };
        self.checked_wiring_is_func(file, entry, limit, wiring);
        let values = bit_func_evaluation_values(checked, inputs, outputs);
        self.checked_definitions_preserve_source_values(&scope, checked, inputs, values);
        assert(self.source_inputs_match(&wiring, layouts, inputs)) by {
            assert forall|i: int| 0 <= i < inputs.len() implies {
                let width = (#[trigger] inputs[i]).len();
                width <= u64::MAX && self.port_width_matches(wiring.drivers.signature.inputs@[i].ty, width as u64, layouts)
            } by {
                assert(inputs[i].len() == scope.inputs@[i]);
            };
        };
        source_outputs_follow_wiring(checked, &wiring, inputs, values, outputs);
    }

    /// 合法な入力に対するネットリストの出力が、元の関数の評価規則を満たすことを示す。
    pub proof fn bit_func_lowering_preserves_source_evaluation(
        &self, file: usize, entry: usize, limit: u64, checked: &CheckedBitFunc,
        capacity: usize, lowered: &LoweredBitFunc, input: Seq<bool>, output: Result<Vec<bool>, NorEvaluationError>,
    )
        requires
            self.checked_bit_func_matches(file, entry, limit, checked),
            checked_bit_func_available(checked),
            lowered_bit_func_result(checked, capacity, Ok(*lowered)),
            input.len() == lowered.input_layout_model().total_bits_model(),
            nor_evaluation_result(lowered.netlist_model(), input, output),
        ensures output matches Ok(bits) && {
            let inputs = port_values(lowered.input_layout_model(), input);
            let outputs = port_values(lowered.output_layout_model(), bits@);
            exists|typed: FuncSignalTypes, layouts: Option<&StructureLayouts>| #[trigger]
                self.source_func_evaluation(file, entry, limit, &typed, layouts, inputs, outputs)
        },
    {
        bit_func_lowering_preserves_evaluation(checked, capacity, lowered, input, output);
        self.checked_evaluation_preserves_source_values(file, entry, limit, checked,
            port_values(lowered.input_layout_model(), input), port_values(lowered.output_layout_model(), output->Ok_0@));
    }
    /// ネットリストの出力は別に検査した型と配置でのソース評価とも宣言順に一致する。
    pub proof fn bit_func_netlist_agrees_with_source_evaluation(
        &self, file: usize, entry: usize, limit: u64, checked: &CheckedBitFunc,
        capacity: usize, lowered: &LoweredBitFunc, input: Seq<bool>, output: Result<Vec<bool>, NorEvaluationError>,
        typed: &FuncSignalTypes, layouts: Option<&StructureLayouts>, expected: Seq<Seq<bool>>,
    )
        requires
            self.checked_bit_func_matches(file, entry, limit, checked),
            checked_bit_func_available(checked),
            lowered_bit_func_result(checked, capacity, Ok(*lowered)),
            input.len() == lowered.input_layout_model().total_bits_model(),
            nor_evaluation_result(lowered.netlist_model(), input, output),
            self.source_func_evaluation(file, entry, limit, typed, layouts,
                port_values(lowered.input_layout_model(), input), expected),
        ensures output matches Ok(bits) && port_values(lowered.output_layout_model(), bits@) == expected,
    {
        self.bit_func_lowering_preserves_source_evaluation(file, entry, limit, checked, capacity, lowered, input, output);
        let inputs = port_values(lowered.input_layout_model(), input);
        let actual = port_values(lowered.output_layout_model(), output->Ok_0@);
        let (other, other_layouts) = choose|other: FuncSignalTypes, other_layouts: Option<&StructureLayouts>| #[trigger]
            self.source_func_evaluation(file, entry, limit, &other, other_layouts, inputs, actual);
        self.source_func_evaluations_agree_across_checks(file, entry, limit, typed, layouts, &other, other_layouts,
            inputs, expected, actual);
    }

    /// 各定義の値は入力とそれ以前の定義の値を使ってソース上の順序で決まる。
    #[verifier::opaque]
    spec fn source_definitions_evaluate(
        &self, context: &SourceFunc, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>,
    ) -> bool {
        &&& values.len() == context.wiring.drivers.definitions@.len()
        &&& values.len() == types.len()
        &&& forall|i: int| 0 <= i < values.len() ==>
            #[trigger] self.source_definition_value(context, layouts, types, inputs, values, i)
    }

    #[verifier::opaque]
    spec fn source_definition_value(
        &self, context: &SourceFunc, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, i: int,
    ) -> bool {
        let value = values[i];
        &&& value.len() <= u64::MAX
        &&& types[i] matches Some(ty) && self.port_width_matches(ty.ty, value.len() as u64, layouts)
        &&& self.source_rhs_can_evaluate(context, layouts, types, inputs, values.take(i), value)
    }

    spec fn source_rhs_can_evaluate(
        &self, context: &SourceFunc, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> bool {
        self.ordinary_source_rhs_value(context, inputs, prior, value)
            || source_bit_vector_value(context, types, prior.len() as int, value)
            || (layouts matches Some(table) && (self.structure_source_rhs_value(context, table, types, inputs, prior, value)
                || self.source_field_selection_value(context, table, types, inputs, prior, value)))
    }

    /// 型検査済みの通常の定義について、評価値が元の右辺の意味を満たすことを示す。
    proof fn checked_slot_preserves_source_value(
        &self, scope: &FuncProjection, definitions: Seq<CheckedBitDefinition>,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, i: int,
    )
        requires
            self.projection_context(scope),
            self.projection_structures_match(scope),
            0 <= i < definitions.len() == values.len() <= scope.wiring.drivers.definitions@.len(),
            self.bit_definition_from_source(scope, definitions.take(i), i, definitions[i]),
            self.definition_widths_match(scope, definitions),
            inputs.len() == scope.inputs@.len(),
            forall|j: int| 0 <= j < inputs.len() ==> (#[trigger] inputs[j]).len() == scope.inputs@[j],
            forall|j: int| 0 <= j <= i ==> (#[trigger] values[j]).len() == definitions[j].width,
            values[i] == checked_definition_values(definitions[i], inputs, values.take(i)),
        ensures self.source_definition_value(
            &SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
                source: scope.source, parsed: scope.parsed, wiring: scope.wiring },
            scope.layouts, scope.types@, inputs, values, i,
        ),
    {
        reveal(UseAliases::source_definition_value);
        reveal(UseAliases::definition_widths_match);
        let context = SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
            source: scope.source, parsed: scope.parsed, wiring: scope.wiring };
        let definition = definitions[i];
        let prior = definitions.take(i);
        let prior_values = values.take(i);
        assert forall|j: int| 0 <= j < prior_values.len() implies
            (#[trigger] prior_values[j]).len() == prior[j].width by {
            assert(prior_values[j] == values[j]);
            assert(prior[j] == definitions[j]);
        };
        if definition.rhs is BitVector {
            let row = scope.parsed.definitions@[scope.wiring.drivers.definitions@[i].definition as int];
            let root = scope.parsed.syntax.forms@[row.expression.start as int];
            assert(self.bit_rhs_from_source(scope, prior, i, definition.rhs, definition.operands@));
            assert(definition.expression.span == form_span(root));
            assert(source_bit_vector_value(&context, scope.types@, i, values[i]));
        } else if exists|at: int| 0 <= at < scope.structures@.len() && (#[trigger] scope.structures@[at]).target == i {
            let at = choose|at: int| 0 <= at < scope.structures@.len() && (#[trigger] scope.structures@[at]).target == i;
            if scope.structures@[at].selection.is_some() {
                self.field_projection_preserves_rhs_value(scope, prior, inputs, prior_values, definition, at);
            } else {
                self.structure_lowering_preserves_rhs_value(scope, prior, inputs, prior_values, definition, at);
            }
        } else {
            self.ordinary_lowering_preserves_rhs_value(scope, prior, inputs, prior_values, definition);
        }
    }

    /// 展開準備で確認した通常の定義を、元の構文に従う参照評価に対応付ける。
    proof fn prepared_slot_preserves_source_value(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>,
        selected: Seq<ResolvedTemplateCall>,
        definitions: Vec<CheckedBitDefinition>, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, i: int,
    )
        requires
            self.projection_context(scope),
            self.projection_structures_match(scope),
            self.prepared_definition_result(scope, calls, selected, Ok(definitions)),
            0 <= i < definitions@.len() == values.len(),
            !super::body::call_covers(calls, i),
            inputs.len() == scope.inputs@.len(),
            forall|j: int| 0 <= j < inputs.len() ==> (#[trigger] inputs[j]).len() == scope.inputs@[j],
            forall|j: int| 0 <= j <= i ==> (#[trigger] values[j]).len() == definitions@[j].width,
            values[i] == checked_definition_values(definitions@[i], inputs, values.take(i)),
        ensures self.source_definition_value(
            &SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
                source: scope.source, parsed: scope.parsed, wiring: scope.wiring },
            scope.layouts, scope.types@, inputs, values, i,
        ),
    {
        self.prepared_ordinary_definition_evidence(scope, calls, selected, definitions, i);
        self.checked_slot_preserves_source_value(scope, definitions@, inputs, values, i);
    }


    spec fn source_value_has_type(
        &self, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>, values: Seq<Seq<bool>>, i: int,
    ) -> bool {
        &&& 0 <= i < types.len() && i < values.len()
        &&& values[i].len() <= u64::MAX
        &&& types[i] matches Some(ty)
        &&& self.port_width_matches(ty.ty, values[i].len() as u64, layouts)
    }

    /// 展開した関数の通常の定義が、元の構文に従う値を持つことを示す。
    proof fn projected_ordinary_definitions_preserve_source_values(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, selected: Seq<ResolvedTemplateCall>,
        definitions: Vec<CheckedBitDefinition>, layout_limit: usize, gate_limit: usize,
        function: &LoweredBitFunc, inputs: Seq<bool>, gates: Seq<bool>,
    )
        requires
            self.projection_context(scope),
            self.projection_structures_match(scope),
            self.projection_port_widths_match(scope),
            self.prepared_definition_result(scope, calls, selected, Ok(definitions)),
            projected_lowering_view(scope.inputs@, definitions@, scope.outputs@, scope.wiring.drivers.outputs@,
                scope.parsed.syntax.forms@, selected, layout_limit, gate_limit, Ok(*function)),
            calls.len() == selected.len(),
            forall|g: int| 0 <= g < selected.len() ==> *(#[trigger] selected[g]).group == calls[g],
            forall|a: int, b: int| 0 <= a < b < calls.len()
                ==> (#[trigger] calls[a]).outputs.end <= (#[trigger] calls[b]).outputs.start,
            inputs.len() == function.input_layout_model().total_bits_model(),
            gate_values_match(inputs, function.netlist_model().gates@, gates),
            gates.len() == function.netlist_model().gates@.len(),
        ensures ({
            let incoming = port_values(function.input_layout_model(), inputs);
            let values = expanded_definition_values(function, inputs, gates);
            let context = SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
                source: scope.source, parsed: scope.parsed, wiring: scope.wiring };
            &&& self.source_inputs_match(scope.wiring, scope.layouts, incoming)
            &&& values.len() == definitions@.len()
            &&& forall|i: int| #![trigger values[i]] 0 <= i < values.len()
                ==> self.source_value_has_type(scope.layouts, scope.types@, values, i)
            &&& forall|i: int| 0 <= i < values.len() && !super::body::call_covers(calls, i) ==>
                #[trigger] self.source_definition_value(&context, scope.layouts, scope.types@, incoming, values, i)
        }),
    {
        assert forall|i: int| 0 <= i < definitions@.len() && !super::body::call_covers(calls, i) implies
            bit_definition_matches(scope.inputs@, definitions@.take(i), #[trigger] definitions@[i]) by {
            self.prepared_ordinary_definition_evidence(scope, calls, selected, definitions, i);
        };
        projected_lowering_local_values(scope.inputs@, definitions@, scope.outputs@, scope.wiring.drivers.outputs@,
            scope.parsed.syntax.forms@, selected, calls, layout_limit, gate_limit, function, inputs, gates);
        let incoming = port_values(function.input_layout_model(), inputs);
        let values = expanded_definition_values(function, inputs, gates);
        assert(self.source_inputs_match(scope.wiring, scope.layouts, incoming));
        self.prepared_definition_width_evidence(scope, calls, selected, definitions);
        assert(values.len() <= scope.types@.len()) by { reveal(UseAliases::definition_widths_match); };
        assert forall|i: int| #![trigger values[i]] 0 <= i < values.len() implies
            self.source_value_has_type(scope.layouts, scope.types@, values, i) by {
            reveal(UseAliases::definition_widths_match);
            assert(values[i].len() == definitions@[i].width);
        };
        let context = SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
            source: scope.source, parsed: scope.parsed, wiring: scope.wiring };
        assert forall|i: int| 0 <= i < values.len() && !super::body::call_covers(calls, i) implies
            #[trigger] self.source_definition_value(&context, scope.layouts, scope.types@, incoming, values, i) by {
            assert(values[i] == checked_definition_values(definitions@[i], incoming, values.take(i)));
            self.prepared_slot_preserves_source_value(scope, calls, selected, definitions, incoming, values, i);
        };
    }

    proof fn checked_definitions_preserve_source_values(
        &self, scope: &FuncProjection, checked: &CheckedBitFunc,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>,
    )
        requires
            self.projection_context(scope),
            self.projection_structures_match(scope),
            scope.inputs@ == checked.input_widths@,
            checked.definitions@.len() == scope.wiring.drivers.definitions@.len(),
            self.definition_prefix(scope, checked.definitions@),
            self.definition_widths_match(scope, checked.definitions@),
            bit_func_inputs_match(checked, inputs),
            bit_func_definitions_match(checked, inputs, values),
        ensures self.source_definitions_evaluate(
            &SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
                source: scope.source, parsed: scope.parsed, wiring: scope.wiring },
            scope.layouts, scope.types@, inputs, values,
        ),
    {
        reveal(bit_func_definitions_match);
        reveal(UseAliases::definition_widths_match);
        reveal(UseAliases::definition_prefix);
        reveal(UseAliases::source_definitions_evaluate);
        let context = SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
            source: scope.source, parsed: scope.parsed, wiring: scope.wiring };
        assert forall|i: int| 0 <= i < values.len() implies
            #[trigger] self.source_definition_value(&context, scope.layouts, scope.types@, inputs, values, i) by {
            assert(self.bit_definition_from_source(scope, checked.definitions@.take(i), i, checked.definitions@[i]));
            self.checked_slot_preserves_source_value(scope, checked.definitions@, inputs, values, i);
        };
        assert(values.len() == scope.wiring.drivers.definitions@.len());
        assert(values.len() == scope.types@.len());
        assert(self.source_definitions_evaluate(&context, scope.layouts, scope.types@, inputs, values));
    }

    /// 定数、信号名、基底 NOR、選択式、連接式を元の構文から評価する。
    #[verifier::opaque]
    spec fn ordinary_source_rhs_value(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> bool {
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let root = context.parsed.definitions@[definition as int].expression.start as int;
        ||| atomic_value(context, definition, root, inputs, prior, value)
        ||| self.source_nor_value(context, inputs, prior, value)
        ||| self.source_selection_value(context, inputs, prior, value)
        ||| self.source_nested_selection_value(context, inputs, prior, value)
        ||| self.source_concat_value(context, inputs, prior, value)
    }

    spec fn source_concat_value(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> bool {
        exists|arguments: core::ops::Range<usize>, parts: Seq<Seq<bool>>|
            #[trigger] self.source_concat_case(context, inputs, prior, value, arguments, parts)
    }

    /// 元の式の直下にある裸の信号名と定数から、連接の値を定める。
    #[verifier::opaque]
    spec fn source_concat_case(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
        arguments: core::ops::Range<usize>, parts: Seq<Seq<bool>>,
    ) -> bool {
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let root = context.parsed.definitions@[definition as int].expression.start;
        &&& concat_arguments_match(context.source.text, context.parsed.syntax.forms@, root as int, arguments)
        &&& parts.len() == arguments.end - arguments.start
        &&& forall|i: int| 0 <= i < parts.len() ==>
            atomic_value(context, definition, arguments.start + i, inputs, prior, #[trigger] parts[i])
        &&& value == parts.flatten()
    }

    spec fn source_nor_value(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> bool {
        exists|call: TypedFuncCall, left: Seq<bool>, right: Seq<bool>|
            #[trigger] self.source_nor_operands(context, inputs, prior, call, left, right)
            && value == seq![!(left[0] || right[0])]
    }

    spec fn source_selection_value(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> bool {
        exists|shape: BitSelectionShape, driver: OutputDriver, selection: CheckedBitSelection, origin: LocatedName|
            #[trigger] self.source_selection_case(context, inputs, prior, value, shape, driver, selection, origin)
    }

    spec fn source_nested_selection_value(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> bool {
        exists|steps: Seq<BitSelectionShape>, leaf: usize, driver: OutputDriver, origin: LocatedName|
            #[trigger] self.source_nested_selection_case(context, inputs, prior, value, steps, leaf, driver, origin)
    }

    #[verifier::opaque]
    spec fn source_nested_selection_case(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
        steps: Seq<BitSelectionShape>, leaf: usize, driver: OutputDriver, origin: LocatedName,
    ) -> bool {
        let parsed = context.parsed;
        let forms = parsed.syntax.forms@;
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let root = parsed.definitions@[definition as int].expression.start;
        &&& nested_named_selection_matches(context.source.text, forms, root, steps, leaf)
        &&& operand_matches(context.source, parsed, context.entry, definition, leaf as int,
            context.wiring, prior.len() as int, SingleBitOperand::Driver(driver))
        &&& selection_chain_values_match(context.source, forms, steps, origin, driver_values(inputs, prior, driver), value)
    }

    #[verifier::opaque]
    spec fn source_selection_case(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
        shape: BitSelectionShape, driver: OutputDriver, selection: CheckedBitSelection, origin: LocatedName,
    ) -> bool {
        let parsed = context.parsed;
        let forms = parsed.syntax.forms@;
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let root = parsed.definitions@[definition as int].expression.start as int;
        let input = driver_values(inputs, prior, driver);
        &&& forms[root] is List
        &&& named_selection_matches(context.source.text, forms, root, shape)
        &&& operand_matches(context.source, parsed, context.entry, definition, shape.input.start as int,
            context.wiring, prior.len() as int, SingleBitOperand::Driver(driver))
        &&& input.len() <= u64::MAX
        &&& selection_arguments_match(context.source, forms, &shape, input.len() as u64, &origin, Ok(selection))
        &&& value == Seq::new(selection.count as nat, |i: int| input[selection.start + i * selection.stride])
    }

    #[verifier::opaque]
    spec fn source_nor_operands(
        &self, context: &SourceFunc, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>,
        call: TypedFuncCall, left: Seq<bool>, right: Seq<bool>,
    ) -> bool {
        let parsed = context.parsed;
        let forms = parsed.syntax.forms@;
        let definition = context.wiring.drivers.definitions@[prior.len() as int].definition;
        let row = parsed.definitions@[definition as int];
        let root = row.expression.start as int;
        let local = (definition - parsed.entry_ranges@[context.entry as int].definitions.start) as usize;
        &&& self.func_call_signature_evidence(context.file, context.entry, local, 0, context.limit, Ok(Some(call)))
        &&& call.call.target is Nor && call.call.call.form == root && call.call.call.arguments == 2
        &&& forms[root] is List && row.expression.end == root + 4
        &&& ordinary_call_at(context.source.text, forms, root, row.expression.end as int)
        &&& left.len() == 1 && right.len() == 1
        &&& atomic_value(context, definition, root + 2, inputs, prior, left)
        &&& atomic_value(context, definition, root + 3, inputs, prior, right)
    }

    /// 構造体式を配置表で解釈し、入力から指定されたビット区間を得る。
    #[verifier::opaque]
    spec fn structure_source_rhs_value(
        &self, context: &SourceFunc, layouts: &StructureLayouts, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
    ) -> bool {
        exists|shape: StructureExpressionShape, checked: CheckedStructureExpression|
            #[trigger] self.source_structure_case(context, layouts, types, inputs, prior, value, shape, checked)
    }

    #[verifier::opaque]
    spec fn source_structure_case(
        &self, context: &SourceFunc, layouts: &StructureLayouts, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, value: Seq<bool>,
        shape: StructureExpressionShape, checked: CheckedStructureExpression,
    ) -> bool {
        let index = prior.len() as int;
        let parsed = context.parsed;
        let forms = parsed.syntax.forms@;
        let definition = context.wiring.drivers.definitions@[index].definition;
        let row = parsed.definitions@[definition as int];
        let root = row.expression.start as int;
        let frame = parsed.entry_ranges@[context.entry as int];
        let first = row.signals.start - frame.signals.start;
        let bound = context.wiring.signals@[first];
        let site = StructureExpressionContext { file: context.file, entry: context.entry, limit: context.limit,
            source: context.source, parsed, definition: (definition - frame.definitions.start) as usize };
        let bits = driver_values(inputs, prior, bound.driver);
        &&& 0 <= first < context.wiring.signals@.len()
        &&& bound.definition == definition
        &&& signal_type_at(context.wiring, types.take(index), bound.driver) matches Some(input)
        &&& forms[root] is List
        &&& named_structure_expression_matches(context.source.text, forms, root, shape)
        &&& is_form_location(context.source, forms[shape.input.start as int], bound.site)
        &&& self.structure_expression_type_matches(&site, shape, layouts, input, Ok(checked))
        &&& types[index] == Some(checked.0)
        &&& checked.2 == bits.len()
        &&& value == bits.subrange(checked.1.range.start as int, checked.1.range.end as int)
    }

    proof fn source_structure_values_agree(
        &self, context: &SourceFunc, other: &SourceFunc, layouts: &StructureLayouts, other_layouts: &StructureLayouts,
        types: Seq<Option<SignalType>>, inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, left: Seq<bool>, right: Seq<bool>,
    )
        requires
            self.can_resolve(),
            same_source_bindings(context, other),
            prior.len() < context.wiring.drivers.definitions@.len(),
            self.structure_types_match(context.limit, Ok(*layouts)),
            self.structure_types_match(context.limit, Ok(*other_layouts)),
            self.structure_source_rhs_value(context, layouts, types, inputs, prior, left),
            self.structure_source_rhs_value(other, other_layouts, types, inputs, prior, right),
        ensures left == right,
    {
        reveal(UseAliases::structure_source_rhs_value);
        let (shape_a, checked_a) = choose|shape: StructureExpressionShape, checked: CheckedStructureExpression|
            #[trigger] self.source_structure_case(context, layouts, types, inputs, prior, left, shape, checked);
        let (shape_b, checked_b) = choose|shape: StructureExpressionShape, checked: CheckedStructureExpression|
            #[trigger] self.source_structure_case(other, other_layouts, types, inputs, prior, right, shape, checked);
        reveal(UseAliases::source_structure_case);
        let index = prior.len() as int;
        let parsed = context.parsed;
        assert(same_definition_driver(context.wiring.drivers.definitions@[index], other.wiring.drivers.definitions@[index]));
        let definition = context.wiring.drivers.definitions@[index].definition;
        let row = parsed.definitions@[definition as int];
        let frame = parsed.entry_ranges@[context.entry as int];
        let reference = context.wiring.signals@[row.signals.start - frame.signals.start];
        let site = StructureExpressionContext { file: context.file, entry: context.entry, limit: context.limit,
            source: context.source, parsed, definition: (definition - frame.definitions.start) as usize };
        let input = signal_type_at(context.wiring, types.take(index), reference.driver)->Some_0;
        structure_expression_shapes_agree(context.source.text, parsed.syntax.forms@,
            row.expression.start as int, shape_a, shape_b);
        self.checked_structure_expressions_agree(&site, shape_a, layouts, other_layouts, input, checked_a, checked_b);
    }

    proof fn structure_lowering_preserves_rhs_value(
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
            scope.structures@[at].selection.is_none(),
        ensures self.structure_source_rhs_value(
            &SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
                source: scope.source, parsed: scope.parsed, wiring: scope.wiring },
            scope.layouts->Some_0, scope.types@, inputs, values, definition_values(checked.rhs, inputs, values),
        ),
    {
        reveal(UseAliases::structure_source_rhs_value);
        let index = definitions.len() as int;
        let projection = scope.structures@[at];
        let layout = scope.layouts->Some_0;
        let j = choose|j: int| 0 <= j < scope.structures@.len() && {
            let row = #[trigger] scope.structures@[j];
            let range = row.operation.range;
            &&& row.target == index
            &&& bit_driver_width(scope.inputs@, definitions, row.input) == Some(row.input_width)
            &&& structure_rhs_matches(checked.rhs, row)
        };
        assert(at == j);
        assert(contiguous_rhs_matches(checked.rhs, projection.input,
            projection.operation.range.start, projection.operation.range.end, projection.input_width));
        let shape = self.structure_projection_widths(scope.file, scope.entry, scope.limit,
            scope.wiring, *layout, scope.types@, projection);
        driver_value_length(scope, definitions, inputs, values, projection.input, projection.input_width);
        let range = projection.operation.range;
        contiguous_rhs_preserves_range(checked.rhs, inputs, values, projection.input,
            range.start, range.end, projection.input_width);
        let context = SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
            source: scope.source, parsed: scope.parsed, wiring: scope.wiring };
        let row = scope.parsed.definitions@[scope.wiring.drivers.definitions@[index].definition as int];
        structure_expression_positions(scope.source.text, scope.parsed.syntax.forms@,
            row.expression.start as int, shape);
        assert(self.source_structure_case(&context, layout, scope.types@, inputs, values,
            definition_values(checked.rhs, inputs, values), shape,
            (scope.types@[index]->Some_0, projection.operation, projection.input_width))) by {
            reveal(UseAliases::source_structure_case);
        };
    }

    proof fn ordinary_lowering_preserves_rhs_value(
        &self, scope: &FuncProjection, definitions: Seq<CheckedBitDefinition>,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, checked: CheckedBitDefinition,
    )
        requires
            !(checked.rhs is BitVector),
            self.projection_context(scope),
            values.len() == definitions.len() < scope.wiring.drivers.definitions@.len(),
            inputs.len() == scope.inputs@.len(),
            forall|i: int| 0 <= i < inputs.len() ==> (#[trigger] inputs[i]).len() == scope.inputs@[i],
            forall|i: int| 0 <= i < values.len() ==> (#[trigger] values[i]).len() == definitions[i].width,
            self.bit_definition_from_source(scope, definitions, definitions.len() as int, checked),
            forall|j: int| 0 <= j < scope.structures@.len() ==> (#[trigger] scope.structures@[j]).target != definitions.len(),
        ensures self.ordinary_source_rhs_value(
            &SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
                source: scope.source, parsed: scope.parsed, wiring: scope.wiring },
            inputs, values, checked_definition_values(checked, inputs, values),
        ),
    {
        reveal(UseAliases::ordinary_source_rhs_value);
        reveal(definition_values);
        let context = SourceFunc { file: scope.file, entry: scope.entry, limit: scope.limit,
            source: scope.source, parsed: scope.parsed, wiring: scope.wiring };
        let index = definitions.len() as int;
        let definition = scope.wiring.drivers.definitions@[index].definition;
        let row = scope.parsed.definitions@[definition as int];
        let root = row.expression.start as int;
        let result = checked_definition_values(checked, inputs, values);
        assert(self.bit_rhs_from_source(scope, definitions, index, checked.rhs, checked.operands@));
        assert(!(exists|j: int| 0 <= j < scope.structures@.len() && (#[trigger] scope.structures@[j]).target == index));
        match checked.rhs {
            BitFuncRhs::BitVector | BitFuncRhs::CallOutput { .. } => { assert(false); },
            BitFuncRhs::Concat => {
                let projection = choose|concat: ConcatProjection|
                    #[trigger] concat_projection_matches(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                        scope.wiring, scope.types@, concat)
                    && concat.target == index && concat.operands@ == checked.operands@;
                let arguments = concat_projection_positions(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                    scope.wiring, scope.types@, projection);
                let parts = concat_operand_values(inputs, values, checked.operands@);
                assert forall|j: int| 0 <= j < parts.len() implies
                    atomic_value(&context, definition, arguments.start + j, inputs, values, #[trigger] parts[j]) by {
                    let operand = checked.operands@[j].0;
                    atomic_value_intro(&context, definition, arguments.start + j, inputs, values, operand);
                    assert(parts[j] == atom_result(inputs, values, operand));
                };
                assert(self.source_concat_case(&context, inputs, values, result, arguments, parts)) by {
                    reveal(UseAliases::source_concat_case);
                };
            },
            BitFuncRhs::Constant(bit) => {
                atomic_value_intro(&context, definition, root, inputs, values, SingleBitOperand::Constant(bit));
                assert(result == seq![bit]);
                assert(self.ordinary_source_rhs_value(&context, inputs, values, result));
            },
            BitFuncRhs::Driver(driver) => {
                atomic_value_intro(&context, definition, root, inputs, values, SingleBitOperand::Driver(driver));
                assert(result == driver_values(inputs, values, driver));
                assert(self.ordinary_source_rhs_value(&context, inputs, values, result));
            },
            BitFuncRhs::Nor { left, right } => {
                let first = atom_result(inputs, values, left);
                let second = atom_result(inputs, values, right);
                atomic_value_is_bit(scope, definitions, inputs, values, left);
                atomic_value_is_bit(scope, definitions, inputs, values, right);
                atomic_value_intro(&context, definition, root + 2, inputs, values, left);
                atomic_value_intro(&context, definition, root + 3, inputs, values, right);
                assert(first[0] == super::super::semantics::operand_value(inputs, values, left));
                assert(second[0] == super::super::semantics::operand_value(inputs, values, right));
                let local = (definition - scope.parsed.entry_ranges@[scope.entry as int].definitions.start) as usize;
                let call = choose|call: TypedFuncCall| #[trigger] self.func_call_signature_evidence(
                    scope.file, scope.entry, local, 0, scope.limit, Ok(Some(call)),
                ) && call.call.call.form == root && call.call.call.arguments == 2 && call.call.target is Nor;
                self.checked_wiring_is_func(scope.file, scope.entry, scope.limit, *scope.wiring);
                assert(indexed_driver_site(scope.source, scope.parsed, scope.entry as int, scope.wiring.drivers.definitions@[index]));
                self.typed_call_arguments_ready(scope.file, scope.entry, local, 0, scope.limit, call);
                indexed_call_arguments(scope.source.text, scope.parsed.syntax.forms@, row,
                    scope.parsed.references@[row.references.start as int], call.call.call);
                assert(self.source_nor_operands(&context, inputs, values, call, first, second)) by {
                    reveal(UseAliases::source_nor_operands);
                };
                assert(result == seq![!(first[0] || second[0])]);
                assert(self.ordinary_source_rhs_value(&context, inputs, values, result));
            },
            BitFuncRhs::Selection { input, selection } => {
                let signature = &scope.wiring.drivers.signature;
                let forms = scope.parsed.syntax.forms@;
                let width = bit_driver_width(scope.inputs@, definitions, input)->Some_0;
                let origin = driver_width_origin(signature, definitions, input);
                driver_value_length(scope, definitions, inputs, values, input, width);
                let input_bits = driver_values(inputs, values, input);
                assert(result =~= Seq::new(selection.count as nat,
                    |i: int| input_bits[selection.start + i * selection.stride]));
                if Self::nested_selection_projection(scope, definitions, index, input, selection) {
                    reveal(UseAliases::nested_selection_projection);
                    let (steps, leaf) = choose|steps: Seq<BitSelectionShape>, leaf: usize|
                        #[trigger] nested_named_selection_matches(scope.source.text, forms, root as usize, steps, leaf)
                        && operand_matches(scope.source, scope.parsed, scope.entry, definition, leaf as int,
                            scope.wiring, index, SingleBitOperand::Driver(input))
                        && selection_chain_arguments_match(scope.source, forms, steps, width, origin, Ok(selection));
                    selection_chain_projection_preserves_values(scope.source, forms, steps, origin, input_bits, selection);
                    assert(self.source_nested_selection_case(&context, inputs, values, result, steps, leaf, input, origin)) by {
                        reveal(UseAliases::source_nested_selection_case);
                    };
                } else {
                    let shape = choose|shape: BitSelectionShape|
                        #[trigger] named_selection_matches(scope.source.text, forms, root, shape)
                        && operand_matches(scope.source, scope.parsed, scope.entry, definition, shape.input.start as int,
                            scope.wiring, index, SingleBitOperand::Driver(input))
                        && selection_arguments_match(scope.source, forms, &shape, width, &origin, Ok(selection));
                    bit_selection_shape_positions(scope.source.text, forms, root, shape);
                    assert(self.source_selection_case(&context, inputs, values, result, shape, input, selection, origin)) by {
                        reveal(UseAliases::source_selection_case);
                    };
                }
                assert(self.ordinary_source_rhs_value(&context, inputs, values, result));
            },
        }
    }
}

/// 元ソースのビット列リテラルを、型で指定された幅の値として読む。
spec fn source_bit_vector_value(
    context: &SourceFunc, types: Seq<Option<SignalType>>, index: int, value: Seq<bool>,
) -> bool {
    let definition = context.wiring.drivers.definitions@[index].definition;
    let row = context.parsed.definitions@[definition as int];
    let form = context.parsed.syntax.forms@[row.expression.start as int];
    let span = form_span(form);
    let bytes = context.source.text.spec_bytes()[span.start as int..span.end as int];
    &&& bit_vector_form(form)
    &&& types[index] matches Some(ty)
    &&& ty.ty matches ResolvedPortType::Bits(width)
    &&& value == Seq::new(width as nat, |bit: int| bit_literal_value_at(bytes, bit as nat))
}

pub(super) closed spec fn source_outputs_match(
    wiring: &FuncWiring, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
) -> bool {
    &&& outputs.len() == wiring.drivers.signature.outputs@.len()
    &&& outputs.len() == wiring.drivers.outputs@.len()
    &&& forall|i: int| 0 <= i < outputs.len() ==>
        #[trigger] source_output_at(wiring, inputs, values, outputs, i)
}

spec fn source_output_at(
    wiring: &FuncWiring, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>, i: int,
) -> bool {
    let driver = wiring.drivers.outputs@[i];
    &&& match driver {
        OutputDriver::Input(port) => port < inputs.len(),
        OutputDriver::Definition(index) => index < values.len(),
    }
    &&& outputs[i] == driver_values(inputs, values, driver)
}

/// 宣言順に並べた出力値を、ソース上の出力の参照評価に対応付ける。
pub(super) proof fn source_outputs_from_driver_values(
    wiring: &FuncWiring, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
)
    requires
        outputs.len() == wiring.drivers.outputs@.len() == wiring.drivers.signature.outputs@.len(),
        forall|i: int| 0 <= i < outputs.len() ==> {
            let driver = #[trigger] wiring.drivers.outputs@[i];
            match driver {
                OutputDriver::Input(port) => port < inputs.len(),
                OutputDriver::Definition(index) => index < values.len(),
            }
        },
        forall|i: int| 0 <= i < outputs.len() ==>
            (#[trigger] outputs[i]) == driver_values(inputs, values, wiring.drivers.outputs@[i]),
    ensures source_outputs_match(wiring, inputs, values, outputs),
{
    assert forall|i: int| 0 <= i < outputs.len() implies
        #[trigger] source_output_at(wiring, inputs, values, outputs, i) by {};
}

proof fn source_outputs_follow_wiring(
    checked: &CheckedBitFunc, wiring: &FuncWiring, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
)
    requires
        checked_bit_func_available(checked),
        bit_func_inputs_match(checked, inputs),
        bit_func_definitions_match(checked, inputs, values),
        super::super::semantics::bit_func_outputs_match(checked, inputs, values, outputs),
        checked.signature == wiring.drivers.signature,
        checked.output_drivers@ == wiring.drivers.outputs@,
    ensures source_outputs_match(wiring, inputs, values, outputs),
{
    reveal(checked_bit_func_available);
    reveal(bit_func_definitions_match);
    assert forall|i: int| 0 <= i < outputs.len() implies {
        let driver = #[trigger] wiring.drivers.outputs@[i];
        match driver {
            OutputDriver::Input(port) => port < inputs.len(),
            OutputDriver::Definition(index) => index < values.len(),
        }
    } by {
        let driver = checked.output_drivers@[i];
        assert(bit_driver_width(checked.input_widths@, checked.definitions@, driver) == Some(checked.output_widths@[i]));
    };
    source_outputs_from_driver_values(wiring, inputs, values, outputs);
}

proof fn atomic_value_intro(
    context: &SourceFunc, definition: usize, form: int,
    inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, operand: SingleBitOperand,
)
    requires operand_matches(context.source, context.parsed, context.entry, definition, form,
        context.wiring, prior.len() as int, operand),
    ensures atomic_value(context, definition, form, inputs, prior, atom_result(inputs, prior, operand)),
{
    source_operand_is_atom(context.source, context.parsed, context.entry, definition, form,
        context.wiring, prior.len() as int, operand);
}

spec fn atom_result(inputs: Seq<Seq<bool>>, prior: Seq<Seq<bool>>, operand: SingleBitOperand) -> Seq<bool> {
    match operand {
        SingleBitOperand::Constant(bit) => seq![bit],
        SingleBitOperand::Driver(driver) => driver_values(inputs, prior, driver),
    }
}

proof fn driver_value_length(
    scope: &FuncProjection, definitions: Seq<CheckedBitDefinition>,
    inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, driver: OutputDriver, width: u64,
)
    requires
        values.len() == definitions.len(),
        inputs.len() == scope.inputs@.len(),
        forall|i: int| 0 <= i < inputs.len() ==> (#[trigger] inputs[i]).len() == scope.inputs@[i],
        forall|i: int| 0 <= i < values.len() ==> (#[trigger] values[i]).len() == definitions[i].width,
        bit_driver_width(scope.inputs@, definitions, driver) == Some(width),
    ensures driver_values(inputs, values, driver).len() == width,
{
    match driver {
        OutputDriver::Input(port) => { assert(inputs[port as int].len() == width); },
        OutputDriver::Definition(index) => { assert(values[index as int].len() == width); },
    }
}

proof fn atomic_value_is_bit(
    scope: &FuncProjection, definitions: Seq<CheckedBitDefinition>,
    inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, operand: SingleBitOperand,
)
    requires
        values.len() == definitions.len(),
        inputs.len() == scope.inputs@.len(),
        forall|i: int| 0 <= i < inputs.len() ==> (#[trigger] inputs[i]).len() == scope.inputs@[i],
        forall|i: int| 0 <= i < values.len() ==> (#[trigger] values[i]).len() == definitions[i].width,
        nor_operand_matches(scope.inputs@, definitions, operand),
    ensures atom_result(inputs, values, operand).len() == 1,
{
    if let SingleBitOperand::Driver(driver) = operand {
        driver_value_length(scope, definitions, inputs, values, driver, 1);
    }
}

} // verus!
