//! 通常の右辺と関数呼び出しの出力を、定義順に取り出す。

use super::*;
use super::super::templates::{FunctionTemplates, ResolvedTemplateCall};
#[cfg(verus_only)]
use super::super::templates::{ResolvedExpressionCall, ResolvedNorRoot};
use super::super::lowering::{LoweredBitFunc, ProjectedLoweringError, lower_projected_expansion};
#[cfg(verus_only)]
use super::super::lowering::{
    expanded_definition_values, projected_lowering_output_values, projected_lowering_view, resolved_call_fits_body,
    evaluated_flat_call_matches, evaluated_nested_call_matches, MixedCallEvaluation,
    projected_lowering_call_evaluation, projected_lowering_ports, port_values,
};
#[cfg(verus_only)]
use super::source_evaluation::{source_outputs_from_driver_values, source_outputs_match};
#[cfg(verus_only)]
use crate::netlist::{
    gate_values_match, nor_evaluation, nor_evaluation_ready, output_values_match, port_bit_layout_port,
    port_bit_layout_result, preceding_port_bits,
};
use super::super::expansion::{ExpansionSlot, PreparedExpansionBody, expansion_call_at_slot};
#[cfg(verus_only)]
use super::super::expansion::{PreparedExpressionCall, prepared_nested_output_matches};
use super::super::super::FunctionExpansionOrder;
#[cfg(verus_only)]
use super::super::super::function_atoms::{
    concat_projection_positions, concat_projections_match, ordinary_call_excludes_structure_projection,
};
#[cfg(verus_only)]
use crate::syntax::circuit::{ordinary_call_at, ordinary_call_excludes_special_forms};

#[cfg(verus_only)]
use crate::project::use_aliases::call_arity::{CallArgumentSource, ProjectedCallArgument};
#[cfg(verus_only)]
use super::super::lowering::literal_argument_matches_width;

verus! {

pub(in crate::project::use_aliases::bit_func) open spec fn argument_matches_width(
    source: &ProjectSource, forms: Seq<Form>, inputs: Seq<u64>, prior: Seq<CheckedBitDefinition>,
    argument: ProjectedCallArgument, width: u64, limit: u64,
) -> bool {
    &&& argument.form < forms.len()
    &&& match argument.source {
        CallArgumentSource::Driver(driver) => bit_driver_width(inputs, prior, driver) == Some(width),
        CallArgumentSource::Literal(bits) => {
            let span = crate::syntax::form_span(forms[argument.form as int]);
            let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
            &&& width == bits
            &&& literal_argument_matches_width(source, forms, argument.form, width as int)
            &&& circuit_literal_width_matches(bytes, Some(width), limit, Ok(width))
        },
        CallArgumentSource::Deferred | CallArgumentSource::NestedCall(_) => true,
    }
}

pub(in crate::project::use_aliases::bit_func) open spec fn expression_input_width(call: ResolvedExpressionCall, port: int) -> u64 {
    match call.template {
        Some(template) => template.input_widths_model()[port],
        None => 1,
    }
}

pub(in crate::project::use_aliases::bit_func) open spec fn expression_output_bits(call: ResolvedExpressionCall) -> nat {
    match call.template {
        Some(template) => template.circuit_model().netlist_model().outputs@.len(),
        None => 1,
    }
}

/// 入れ子の引数が、指定した位置より前にある子の同じ幅の出力を参照することを表す。
pub(in crate::project::use_aliases::bit_func) open spec fn selected_child_output_matches(
    children: Seq<ResolvedExpressionCall>, reference_start: usize, before: int, argument: ProjectedCallArgument, width: u64,
) -> bool {
    &&& 0 <= before <= children.len()
    &&& if let CallArgumentSource::NestedCall(reference) = argument.source {
        exists|earlier: int| 0 <= earlier < before
            && (#[trigger] children[earlier]).child.reference == reference_start + reference
            && expression_output_bits(children[earlier]) == width
    } else { true }
}

#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func) open spec fn nested_argument_output_matches(
    selected: ResolvedTemplateCall, before: int, argument: ProjectedCallArgument, width: u64,
) -> bool {
    selected_child_output_matches(selected.children@, selected.group.references.start, before, argument, width)
}

/// 根と子の型検査済み引数が、先行する定義または子の出力と同じ幅を持つ。
pub(in crate::project::use_aliases::bit_func) open spec fn nor_root_arguments_match_widths(
    selected: &ResolvedNorRoot, references: core::ops::Range<usize>, source: &ProjectSource, forms: Seq<Form>,
    inputs: Seq<u64>, slots: Seq<CheckedBitDefinition>, first: usize, limit: u64,
) -> bool {
    let children = selected.children@;
    let prior = slots.take(first as int);
    &&& first <= slots.len()
    &&& selected.arguments@.len() == 2
    &&& forall|port: int| 0 <= port < 2 ==> {
        let arg = #[trigger] selected.arguments@[port];
        &&& argument_matches_width(source, forms, inputs, prior, arg, 1, limit)
        &&& selected_child_output_matches(children, references.start, children.len() as int, arg, 1)
    }
    &&& forall|i: int, port: int| 0 <= i < children.len() && 0 <= port < children[i].arguments@.len() ==> {
        let child = children[i];
        let arg = #[trigger] children[i].arguments@[port];
        let width = expression_input_width(child, port);
        &&& child.template matches Some(template) ==> port < template.input_widths_model().len()
        &&& argument_matches_width(source, forms, inputs, prior, arg, width, limit)
        &&& selected_child_output_matches(children, references.start, i, arg, width)
    }
}

pub(in crate::project::use_aliases::bit_func) open spec fn root_argument_matches_width(
    source: &ProjectSource, forms: Seq<Form>, inputs: Seq<u64>, slots: Seq<CheckedBitDefinition>,
    selected: ResolvedTemplateCall, port: int, limit: u64,
) -> bool {
    let argument = selected.arguments@[port];
    let width = selected.template.input_widths_model()[port];
    &&& selected.group.outputs.start <= slots.len()
    &&& 0 <= port < selected.arguments@.len() == selected.template.input_widths_model().len()
    &&& argument_matches_width(source, forms, inputs, slots.take(selected.group.outputs.start as int), argument, width, limit)
    &&& nested_argument_output_matches(selected, selected.children@.len() as int, argument, width)
}

pub(in crate::project::use_aliases::bit_func) open spec fn expression_argument_matches_width(
    source: &ProjectSource, forms: Seq<Form>, inputs: Seq<u64>, slots: Seq<CheckedBitDefinition>,
    selected: ResolvedTemplateCall, child_index: int, port: int, limit: u64,
) -> bool {
    let child = selected.children@[child_index];
    let argument = child.arguments@[port];
    let width = expression_input_width(child, port);
    &&& selected.group.outputs.start <= slots.len()
    &&& 0 <= child_index < selected.children@.len()
    &&& 0 <= port < child.arguments@.len()
    &&& child.template matches Some(template) ==> port < template.input_widths_model().len()
    &&& argument_matches_width(source, forms, inputs, slots.take(selected.group.outputs.start as int), argument, width, limit)
    &&& nested_argument_output_matches(selected, child_index, argument, width)
}

pub(in crate::project::use_aliases::bit_func) open spec fn call_covers(calls: Seq<CheckedExpansionCall>, at: int) -> bool {
    exists|group: int| 0 <= group < calls.len()
        && (#[trigger] calls[group]).outputs.start <= at < calls[group].outputs.end
}

spec fn projected_call_slot(
    calls: Seq<CheckedExpansionCall>, group: int, at: int, slot: CheckedBitDefinition,
) -> bool {
    let call = calls[group];
    &&& call.outputs.start <= at < call.outputs.end
    &&& slot.rhs == BitFuncRhs::CallOutput {
        group: group as usize, port: (at - call.outputs.start) as usize,
    }
    &&& slot.expression == call.expression
    &&& slot.operands@.len() == 0
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    pub(super) closed spec fn expansion_definition_prefix(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, slots: Seq<CheckedBitDefinition>,
    ) -> bool {
        &&& slots.len() <= scope.types@.len()
        &&& forall|at: int| 0 <= at < slots.len() ==> {
            let slot = #[trigger] slots[at];
            if call_covers(calls, at) {
                exists|group: int| 0 <= group < calls.len()
                    && #[trigger] projected_call_slot(calls, group, at, slot)
            } else {
                self.bit_definition_from_source(scope, slots.take(at), at, slot)
            }
        }
    }

    #[verifier::opaque]
    pub(super) closed spec fn body_calls_match(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, widths: Seq<&[u64]>,
        concats: Seq<ConcatProjection>,
    ) -> bool {
        &&& calls.len() == widths.len()
        &&& forall|group: int| 0 <= group < calls.len() ==> {
            let call = #[trigger] calls[group];
            &&& call.outputs.start < call.outputs.end <= scope.types@.len()
            &&& location_in_source(call.expression)
            &&& widths[group]@.len() == call.outputs.end - call.outputs.start
            &&& self.call_definition_widths_match(scope, call.outputs.start, widths[group]@)
            &&& forall|j: int| 0 <= j < scope.structures@.len() ==>
                ! (call.outputs.start <= (#[trigger] scope.structures@[j]).target < call.outputs.end)
            &&& forall|j: int| 0 <= j < concats.len() ==>
                ! (call.outputs.start <= (#[trigger] concats[j]).target < call.outputs.end)
        }
        &&& forall|a: int, b: int| 0 <= a < b < calls.len() ==>
            (#[trigger] calls[a]).outputs.end <= (#[trigger] calls[b]).outputs.start
    }

    proof fn special_projections_outside_call(
        &self, scope: &FuncProjection, call: CheckedExpansionCall, definition: usize,
        concats: Seq<ConcatProjection>,
    )
        requires
            self.projection_context(scope), self.projection_structures_match(scope),
            ({
                let expr = scope.parsed.definitions@[definition as int].expression;
                ordinary_call_at(scope.source.text, scope.parsed.syntax.forms@, expr.start as int, expr.end as int)
            }),
            forall|i: int| call.outputs.start <= i < call.outputs.end ==>
                (#[trigger] scope.wiring.drivers.definitions@[i]).definition == definition,
            concat_projections_match(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                scope.wiring, scope.types@, concats),
        ensures
            forall|j: int| 0 <= j < scope.structures@.len() ==>
                !(call.outputs.start <= (#[trigger] scope.structures@[j]).target < call.outputs.end),
            forall|j: int| 0 <= j < concats.len() ==>
                !(call.outputs.start <= (#[trigger] concats[j]).target < call.outputs.end),
    {
        let expr = scope.parsed.definitions@[definition as int].expression;
        ordinary_call_excludes_special_forms(scope.source.text, scope.parsed.syntax.forms@,
            expr.start as int, expr.end as int);
        concat_projections_order(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
            scope.wiring, scope.types@, concats);

        assert forall|j: int| 0 <= j < concats.len() implies
            !(call.outputs.start <= (#[trigger] concats[j]).target < call.outputs.end) by {
            let row = concats[j];
            if call.outputs.start <= row.target < call.outputs.end {
                assert(scope.wiring.drivers.definitions@[row.target as int].definition == definition);
                concat_projection_positions(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                    scope.wiring, scope.types@, row);
            }
        };
        assert forall|j: int| 0 <= j < scope.structures@.len() implies
            !(call.outputs.start <= (#[trigger] scope.structures@[j]).target < call.outputs.end) by {
            let row = scope.structures@[j];
            if call.outputs.start <= row.target < call.outputs.end {
                assert(scope.wiring.drivers.definitions@[row.target as int].definition == definition);
                assert(scope.layouts.is_some());
                let table = scope.layouts->Some_0;
                ordinary_call_excludes_structure_projection(self, scope.file, scope.entry, scope.limit,
                    scope.wiring, *table, scope.types@, row);
            }
        };
    }

    proof fn prepared_calls_fit_body(
        &self, scope: &FuncProjection, plan: FunctionExpansionOrder, prepared: &PreparedExpansionBody,
        widths: Seq<&[u64]>,
    )
        requires
            self.projection_context(scope), self.projection_structures_match(scope),
            self.prepared_expansion_body_matches(plan, scope.file, scope.entry, scope.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            prepared.calls@.len() == widths.len(),
            forall|i: int| 0 <= i < widths.len() ==> {
                let signature = (#[trigger] prepared.calls@[i])._signature@.signature;
                signature is Function && self.port_widths_match(signature->Function_0.outputs@, widths[i]@, scope.layouts)
            },
        ensures self.body_calls_match(scope, prepared.calls@, widths, prepared.projections.concats@),
    {
        reveal(UseAliases::body_calls_match);
        let caller = (scope.file, scope.entry, scope.limit);
        let concats = prepared.projections.concats@;
        assert forall|i: int| 0 <= i < prepared.calls@.len() implies {
            let call = #[trigger] prepared.calls@[i];
            &&& call.outputs.start < call.outputs.end <= scope.types@.len()
            &&& location_in_source(call.expression)
            &&& widths[i]@.len() == call.outputs.end - call.outputs.start
            &&& self.call_definition_widths_match(scope, call.outputs.start, widths[i]@)
            &&& forall|j: int| 0 <= j < scope.structures@.len() ==>
                !(call.outputs.start <= (#[trigger] scope.structures@[j]).target < call.outputs.end)
            &&& forall|j: int| 0 <= j < concats.len() ==>
                !(call.outputs.start <= (#[trigger] concats[j]).target < call.outputs.end)
        } by {
            let call = prepared.calls@[i];
            let root = prepared.projections.calls@[i];
            self.expansion_call_output_types(plan, caller, prepared.typed, scope.wiring, root,
                prepared.projections.call_arguments.ranges@[i], &prepared.projections.call_arguments, call);
            self.call_definition_widths_from_signature(scope, &call, widths[i]@);
            self.special_projections_outside_call(scope, call, root.definition, concats);
        };
    }

    /// 呼び出し先のポート幅と、呼び出し元の駆動元またはリテラルの幅を照合する。
    proof fn prepared_argument_matches_width(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates, prepared: &PreparedExpansionBody,
        selected: ResolvedTemplateCall, group: int, port: int, slots: Seq<CheckedBitDefinition>,
    )
        requires
            self.projection_context(scope), self.projection_port_widths_match(scope),
            self.structure_layout_for_ports(scope.limit, scope.layouts),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            self.resolved_template_call_matches(plan, (scope.file, scope.entry, scope.limit), prepared, group, selected),
            self.resolved_expression_calls_match(plan, table, scope.limit, selected.group.postorder,
                prepared.projections.call_arguments.arguments@, selected.children@),
            selected.group.outputs.start <= slots.len(),
            self.definition_widths_match(scope, slots),
            0 <= port < selected.arguments@.len(),
            scope.layouts.is_none() ==>
                !has_structure_port(selected.template.signature_model().inputs@)
                    && !has_structure_port(selected.template.signature_model().outputs@),
        ensures root_argument_matches_width(scope.source, scope.parsed.syntax.forms@, scope.inputs@,
            slots, selected, port, scope.limit),
    {
        reveal(nested_argument_output_matches);
        let call = *selected.group;
        let template = selected.template;
        let signature = template.signature_model();
        let inputs = template.input_widths_model();
        let position = plan.position_model(call._order@.0)->Some_0;
        self.template_port_evidence(position, scope.limit, template);
        self.template_widths_in_caller_layout(signature, scope.limit, inputs,
            template.output_widths_model(), template.structure_layouts_model(), scope.layouts);

        self.expansion_callee_template_evidence(*plan, (scope.file, scope.entry, scope.limit), prepared, group);
        let root = prepared.projections.calls@[group];
        assert(call == prepared.calls@[group]);
        self.expansion_argument_evidence(*plan, (scope.file, scope.entry, scope.limit), prepared.typed,
            scope.wiring, root, call.arguments, &prepared.projections.call_arguments, call, port);
        let arg = selected.arguments@[port];
        assert(arg == prepared.projections.call_arguments.arguments@[call.arguments.start + port]);
        let expected = signature.inputs@[port].ty;
        let width = inputs[port];
        assert(self.port_width_matches(expected, width, scope.layouts));
        match arg.source {
            CallArgumentSource::Driver(driver) => {
                let actual = self.preceding_argument_driver_width(scope, slots, call.outputs.start as int, driver);
                let known = signal_type_at(scope.wiring, scope.types@, driver)->Some_0;
                self.equivalent_port_widths(scope.layouts, known.ty, actual, expected, width);
            },
            CallArgumentSource::NestedCall(_) => {
                self.resolved_nested_output_width(plan, table, scope.limit, prepared.projections.call_arguments.arguments@,
                    selected.group.postorder, selected.children@, selected.group.references.start,
                    selected.children@.len() as int, arg, (expected, width, scope.layouts));
            },
            _ => {},
        }
    }

    /// 同じ引数フォームを指す子の出力型から、実際に返す配線数を導く。
    proof fn resolved_nested_output_width(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, limit: u64,
        arguments: Seq<ProjectedCallArgument>, postorder: Option<Vec<PreparedExpressionCall>>, children: Seq<ResolvedExpressionCall>,
        reference_start: usize, before: int,
        argument: ProjectedCallArgument, expected: (ResolvedPortType, u64, Option<&StructureLayouts>),
    )
        requires
            self.can_resolve(),
            self.structure_layout_for_ports(limit, expected.2),
            self.port_width_matches(expected.0, expected.1, expected.2),
            self.resolved_expression_calls_match(plan, table, limit, postorder, arguments, children),
            postorder matches Some(children) && prepared_nested_output_matches(children@,
                reference_start, before, argument, expected.0),
        ensures selected_child_output_matches(children, reference_start, before, argument, expected.1),
    {
        reveal(UseAliases::resolved_expression_call_matches);
        reveal(UseAliases::template_port_widths_match);
        let rows = postorder->Some_0@;
        let earlier = choose|i: int| 0 <= i < before
            && (#[trigger] rows[i]).reference == reference_start + argument.source->NestedCall_0
            && rows[i]._signature@.call.call.form == argument.form
            && rows[i]._signature@.call.target.port_counts().outputs == 1
            && match rows[i]._signature@.signature {
                crate::project::FuncCallSignature::Nor =>
                    crate::project::port_types_equal(ResolvedPortType::Bits(1), expected.0),
                crate::project::FuncCallSignature::Function(ports) =>
                    ports.outputs@.len() == 1 && crate::project::port_types_equal(ports.outputs@[0].ty, expected.0),
            };
        let producer = children[earlier];
        let row = rows[earlier];
        assert(self.resolved_expression_call_matches(plan, table, limit, arguments, row, producer));
        let (ty, bits, layout) = match producer.template {
            Some(template) => {
                let target = plan.position_model(row._rank@->Some_0)->Some_0;
                self.template_port_evidence(target, limit, template);
                self.template_circuit_evidence(target, limit, template);
                let outputs = template.output_widths_model();
                let output_layout = template.circuit_model().output_layout_model();
                assert(outputs.len() == 1);
                port_bit_layout_port(outputs, template.bit_limit_model(), *output_layout, 0);
                assert(preceding_port_bits(outputs, 0) == 0) by { reveal(preceding_port_bits); };
                assert(expression_output_bits(producer) == outputs[0]);
                (template.signature_model().outputs@[0].ty, outputs[0], template.structure_layouts_model())
            },
            None => (ResolvedPortType::Bits(1), 1u64, None),
        };
        let table_for_output = match &layout { Some(table) => Some(table), None => None };
        assert(self.port_width_matches(ty, bits, table_for_output));
        self.argument_widths_agree(limit, (ty, bits, table_for_output), expected);
        assert(expression_output_bits(producer) == expected.1);
    }

    /// 左辺の手前までで利用できる駆動元の幅が、検査済みの型に対応することを示す。
    proof fn preceding_argument_driver_width(
        &self, scope: &FuncProjection, slots: Seq<CheckedBitDefinition>, end: int, driver: OutputDriver,
    ) -> (width: u64)
        requires
            self.definition_widths_match(scope, slots), self.projection_port_widths_match(scope),
            0 <= end <= slots.len(),
            match driver {
                OutputDriver::Input(i) => i < scope.inputs@.len(),
                OutputDriver::Definition(i) => i < end,
            },
        ensures
            bit_driver_width(scope.inputs@, slots.take(end), driver) == Some(width),
            signal_type_at(scope.wiring, scope.types@, driver) matches Some(known)
                && self.port_width_matches(known.ty, width, scope.layouts),
    {
        let prefix = slots.take(end);
        reveal(UseAliases::definition_widths_match);
        assert forall|i: int| 0 <= i < prefix.len() implies {
            let definition = #[trigger] prefix[i];
            scope.types@[i] matches Some(ty) && self.port_width_matches(ty.ty, definition.width, scope.layouts)
        } by { assert(prefix[i] == slots[i]); };
        let width = bit_driver_width(scope.inputs@, prefix, driver)->Some_0;
        assert(bit_driver_width(scope.inputs@, prefix, driver) == Some(width));
        self.driver_type_matches_width(scope, prefix, driver, width);
        assert(signal_type_at(scope.wiring, scope.types@.take(prefix.len() as int), driver)
            == signal_type_at(scope.wiring, scope.types@, driver));
        width
    }

    /// 検査済みの別々の配置表でも、同じ型のポートは同じ表現幅を持つ。
    proof fn argument_widths_agree(
        &self, limit: u64, left: (ResolvedPortType, u64, Option<&StructureLayouts>),
        right: (ResolvedPortType, u64, Option<&StructureLayouts>),
    )
        requires
            self.can_resolve(), crate::project::port_types_equal(left.0, right.0),
            self.structure_layout_for_ports(limit, left.2), self.structure_layout_for_ports(limit, right.2),
            self.port_width_matches(left.0, left.1, left.2), self.port_width_matches(right.0, right.1, right.2),
        ensures left.1 == right.1,
    {
        if right.0 is Struct {
            self.layout_port_width_transfers(limit, right.2->Some_0, left.2->Some_0, right.0, right.1 as int);
        }
        self.equivalent_port_widths(left.2, left.0, left.1, right.0, right.1);
    }

    /// 実引数の型を、子の入力配置が要求する幅と照合する。
    ///
    /// 入れ子の呼び出しでは、後順で先行する子が実際に返す配線数まで対応付ける。
    pub(super) proof fn prepared_child_argument_matches_width(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: ResolvedTemplateCall,
        group_index: int, child_index: int, port: int, slots: Seq<CheckedBitDefinition>,
    )
        requires
            self.projection_context(scope), self.projection_port_widths_match(scope),
            self.structure_layout_for_ports(scope.limit, scope.layouts),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            0 <= group_index < prepared.calls@.len(), *selected.group == prepared.calls@[group_index],
            self.resolved_expression_calls_match(plan, table, scope.limit, selected.group.postorder,
                prepared.projections.call_arguments.arguments@, selected.children@),
            0 <= child_index < selected.children@.len(),
            0 <= port < selected.children@[child_index].arguments@.len(),
            selected.group.outputs.start <= slots.len(), self.definition_widths_match(scope, slots),
        ensures expression_argument_matches_width(scope.source, scope.parsed.syntax.forms@, scope.inputs@,
            slots, selected, child_index, port, scope.limit),
    {
        reveal(nested_argument_output_matches);
        reveal(UseAliases::resolved_expression_call_matches);
        reveal(UseAliases::template_port_widths_match);
        let group = *selected.group;
        let children = group.postorder->Some_0@;
        let child = selected.children@[child_index];
        let prepared_child = children[child_index];
        let arguments = prepared.projections.call_arguments.arguments@;
        assert(self.resolved_expression_call_matches(plan, table, scope.limit, arguments, prepared_child, child));
        let caller = (scope.file, scope.entry, scope.limit);
        self.expansion_child_argument_evidence(*plan, caller, prepared, group_index, child_index, port);
        let arg = child.arguments@[port];
        assert(arg == arguments[prepared_child.arguments.start + port]);
        let expected = match prepared_child._signature@.signature {
            crate::project::FuncCallSignature::Nor => ResolvedPortType::Bits(1),
            crate::project::FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
        };
        let width = expression_input_width(child, port);
        let layout = match child.template {
            Some(template) => {
                let rank = prepared_child._rank@->Some_0;
                self.template_port_evidence(plan.position_model(rank)->Some_0, scope.limit, template);
                template.structure_layouts_model()
            },
            None => None,
        };
        let table_for_input = match &layout { Some(table) => Some(table), None => None };
        assert(self.structure_layout_for_ports(scope.limit, table_for_input));
        assert(self.port_width_matches(expected, width, table_for_input));
        match arg.source {
            CallArgumentSource::Driver(driver) => {
                let actual = self.preceding_argument_driver_width(scope, slots, group.outputs.start as int, driver);
                let known = signal_type_at(scope.wiring, scope.types@, driver)->Some_0;
                self.argument_widths_agree(scope.limit, (known.ty, actual, scope.layouts), (expected, width, table_for_input));
            },
            CallArgumentSource::NestedCall(_) => self.resolved_nested_output_width(
                plan, table, scope.limit, arguments, selected.group.postorder, selected.children@,
                selected.group.references.start, child_index, arg, (expected, width, table_for_input)),
            _ => {},
        }
    }

    /// 根とすべての子に渡す幅を、同じ定義の型検査結果から得る。
    pub(super) proof fn resolved_nor_arguments_fit_body(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: &ResolvedNorRoot, index: int, first: usize, slots: Seq<CheckedBitDefinition>,
    )
        requires
            self.projection_context(scope), self.projection_port_widths_match(scope),
            self.structure_layout_for_ports(scope.limit, scope.layouts),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            0 <= index < prepared.nor_roots@.len(), *selected.prepared == prepared.nor_roots@[index],
            first < scope.wiring.drivers.definitions@.len(),
            scope.wiring.drivers.definitions@[first as int].definition == selected.prepared.definition,
            scope.wiring.drivers.definitions@[first as int].result_index == 0,
            first <= slots.len(), self.definition_widths_match(scope, slots),
            selected.prepared.root.arguments.start <= selected.prepared.root.arguments.end
                <= prepared.projections.call_arguments.arguments@.len(),
            selected.arguments@ == prepared.projections.call_arguments.arguments@.subrange(
                selected.prepared.root.arguments.start as int, selected.prepared.root.arguments.end as int),
            self.resolved_expression_calls_match(plan, table, scope.limit, Some(selected.prepared.postorder),
                prepared.projections.call_arguments.arguments@, selected.children@),
        ensures nor_root_arguments_match_widths(selected, scope.parsed.definitions@[selected.prepared.definition as int].references,
            scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots, first, scope.limit),
    {
        let caller = (scope.file, scope.entry, scope.limit);
        self.nor_root_template_evidence(*plan, caller, prepared, index);
        let root = selected.prepared;
        let args = prepared.projections.call_arguments.arguments@;
        let references = scope.parsed.definitions@[root.definition as int].references;
        let forms = scope.parsed.syntax.forms@;
        let prior = slots.take(first as int);
        let count = selected.children@.len() as int;
        assert(count == root.postorder@.len());
        assert(selected.arguments@.len() == 2);
        assert forall|port: int| 0 <= port < 2 implies {
            let arg = #[trigger] selected.arguments@[port];
            &&& argument_matches_width(scope.source, forms, scope.inputs@, prior, arg, 1, scope.limit)
            &&& selected_child_output_matches(selected.children@, references.start, count, arg, 1)
        } by {
            self.resolved_nor_argument_width(scope, plan, table, prepared, selected, index, first, slots, count, port,
                (ResolvedPortType::Bits(1), 1u64, None));
        };
        assert forall|i: int, port: int| 0 <= i < count && 0 <= port < selected.children@[i].arguments@.len() implies {
            let child = selected.children@[i];
            let arg = #[trigger] selected.children@[i].arguments@[port];
            let width = expression_input_width(child, port);
            &&& child.template matches Some(template) ==> port < template.input_widths_model().len()
            &&& argument_matches_width(scope.source, forms, scope.inputs@, prior, arg, width, scope.limit)
            &&& selected_child_output_matches(selected.children@, references.start, i, arg, width)
        } by {
            reveal(UseAliases::resolved_expression_call_matches);
            reveal(UseAliases::template_port_widths_match);
            let row = root.postorder@[i];
            let child = selected.children@[i];
            assert(self.resolved_expression_call_matches(plan, table, scope.limit, args, row, child));
            let expected = match row._signature@.signature {
                crate::project::FuncCallSignature::Nor => ResolvedPortType::Bits(1),
                crate::project::FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
            };
            let width = expression_input_width(child, port);
            let layout = match child.template {
                Some(template) => {
                    let rank = row._rank@->Some_0;
                    self.template_port_evidence(plan.position_model(rank)->Some_0, scope.limit, template);
                    template.structure_layouts_model()
                },
                None => None,
            };
            let input_layout = match &layout { Some(layout) => Some(layout), None => None };
            self.resolved_nor_argument_width(scope, plan, table, prepared, selected, index, first, slots, i, port,
                (expected, width, input_layout));
        };
    }

    proof fn resolved_nor_argument_width(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: &ResolvedNorRoot, index: int, first: usize, slots: Seq<CheckedBitDefinition>,
        parent: int, port: int, expected: (ResolvedPortType, u64, Option<&StructureLayouts>),
    )
        requires
            self.projection_context(scope), self.projection_port_widths_match(scope),
            self.structure_layout_for_ports(scope.limit, scope.layouts),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            0 <= index < prepared.nor_roots@.len(), *selected.prepared == prepared.nor_roots@[index],
            first < scope.wiring.drivers.definitions@.len(),
            scope.wiring.drivers.definitions@[first as int].definition == selected.prepared.definition,
            scope.wiring.drivers.definitions@[first as int].result_index == 0,
            first <= slots.len(), self.definition_widths_match(scope, slots),
            selected.prepared.root.arguments.start <= selected.prepared.root.arguments.end
                <= prepared.projections.call_arguments.arguments@.len(),
            selected.arguments@ == prepared.projections.call_arguments.arguments@.subrange(
                selected.prepared.root.arguments.start as int, selected.prepared.root.arguments.end as int),
            self.resolved_expression_calls_match(plan, table, scope.limit, Some(selected.prepared.postorder),
                prepared.projections.call_arguments.arguments@, selected.children@),
            self.structure_layout_for_ports(scope.limit, expected.2),
            self.port_width_matches(expected.0, expected.1, expected.2),
            ({
                let children = selected.prepared.postorder@;
                let row = if parent == children.len() { selected.prepared.root } else { children[parent] };
                &&& 0 <= parent <= children.len()
                &&& 0 <= port < row.arguments.end - row.arguments.start
                &&& expected.0 == match row._signature@.signature {
                    crate::project::FuncCallSignature::Nor => ResolvedPortType::Bits(1),
                    crate::project::FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
                }
            }),
        ensures ({
            let args = if parent == selected.children@.len() { selected.arguments@ }
                else { selected.children@[parent].arguments@ };
            let arg = args[port];
            let references = scope.parsed.definitions@[selected.prepared.definition as int].references;
            &&& argument_matches_width(scope.source, scope.parsed.syntax.forms@, scope.inputs@,
                slots.take(first as int), arg, expected.1, scope.limit)
            &&& selected_child_output_matches(selected.children@, references.start, parent, arg, expected.1)
        }),
    {
        reveal(UseAliases::resolved_expression_call_matches);
        let caller = (scope.file, scope.entry, scope.limit);
        let root = selected.prepared;
        let args = prepared.projections.call_arguments.arguments@;
        let refs = scope.parsed.definitions@[root.definition as int].references;
        let children = root.postorder@;
        let row = if parent == children.len() { root.root } else { children[parent] };
        let argument = args[row.arguments.start + port];
        self.prepared_nor_argument_evidence(*plan, caller, prepared, index, first, parent, port);
        if parent < children.len() {
            let child = selected.children@[parent];
            assert(self.resolved_expression_call_matches(plan, table, scope.limit, args, row, child));
            assert(argument == child.arguments@[port]);
        } else {
            assert(argument == selected.arguments@[port]);
        }
        match argument.source {
            CallArgumentSource::Driver(driver) => {
                let actual = self.preceding_argument_driver_width(scope, slots, first as int, driver);
                let known = signal_type_at(scope.wiring, scope.types@, driver)->Some_0;
                self.argument_widths_agree(scope.limit, (known.ty, actual, scope.layouts), expected);
            },
            CallArgumentSource::NestedCall(_) => self.resolved_nested_output_width(
                plan, table, scope.limit, args, Some(root.postorder), selected.children@, refs.start, parent, argument, expected),
            _ => {},
        }
    }

    fn resolved_call_output_widths<'s>(
        &self, scope: &FuncProjection<'_, 'p, 'a>, selected: &[ResolvedTemplateCall<'s, 'p, 'a>],
        Ghost(plan): Ghost<FunctionExpansionOrder<'p, 'a>>, Ghost(prepared): Ghost<PreparedExpansionBody<'p, 'a>>,
    ) -> (widths: Vec<&'s [u64]>)
        requires
            self.can_resolve(),
            self.structure_layout_for_ports(scope.limit, scope.layouts),
            selected@.len() == prepared.calls@.len(),
            forall|i: int| 0 <= i < selected@.len() ==> {
                let call = #[trigger] selected@[i];
                &&& self.resolved_template_call_matches(&plan, (scope.file, scope.entry, scope.limit), &prepared, i, call)
                &&& scope.layouts.is_none() ==>
                    !has_structure_port(call.template.signature_model().inputs@)
                        && !has_structure_port(call.template.signature_model().outputs@)
            },
        ensures
            widths@.len() == prepared.calls@.len(),
            forall|i: int| 0 <= i < widths@.len() ==> {
                let signature = prepared.calls@[i]._signature@.signature;
                &&& (#[trigger] widths@[i])@ == selected@[i].template.output_widths_model()
                &&& signature is Function
                &&& self.port_widths_match(signature->Function_0.outputs@, widths@[i]@, scope.layouts)
            },
    {
        let mut widths: Vec<&'s [u64]> = Vec::new();
        let mut index = 0;
        while index < selected.len()
            invariant
                self.can_resolve(),
                self.structure_layout_for_ports(scope.limit, scope.layouts),
                index == widths@.len() <= selected@.len() == prepared.calls@.len(),
                forall|i: int| 0 <= i < selected@.len() ==> {
                    let call = #[trigger] selected@[i];
                    &&& self.resolved_template_call_matches(&plan, (scope.file, scope.entry, scope.limit), &prepared, i, call)
                    &&& scope.layouts.is_none() ==>
                        !has_structure_port(call.template.signature_model().inputs@)
                            && !has_structure_port(call.template.signature_model().outputs@)
                },
                forall|i: int| 0 <= i < widths@.len() ==> {
                    let signature = prepared.calls@[i]._signature@.signature;
                    &&& (#[trigger] widths@[i])@ == selected@[i].template.output_widths_model()
                    &&& signature is Function
                    &&& self.port_widths_match(signature->Function_0.outputs@, widths@[i]@, scope.layouts)
                },
            decreases selected@.len() - index,
        {
            let template = selected[index].template;
            proof {
                let rank = prepared.calls@[index as int]._order@.0;
                let position = plan.position_model(rank)->Some_0;
                self.template_port_evidence(position, scope.limit, template);
                self.template_widths_in_caller_layout(template.signature_model(), scope.limit, template.input_widths_model(),
                    template.output_widths_model(), template.structure_layouts_model(), scope.layouts);
            }
            let row = template.output_widths();
            let ghost prior = widths@;
            widths.push(row);
            assert forall|i: int| 0 <= i < widths@.len() implies {
                let signature = prepared.calls@[i]._signature@.signature;
                &&& (#[trigger] widths@[i])@ == selected@[i].template.output_widths_model()
                &&& signature is Function
                &&& self.port_widths_match(signature->Function_0.outputs@, widths@[i]@, scope.layouts)
            } by {
                if i < index { assert(widths@[i] == prior[i]); }
            };
            index += 1;
        }
        widths
    }

    pub(super) closed spec fn prepared_definition_result(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, selected: Seq<ResolvedTemplateCall>,
        result: Result<Vec<CheckedBitDefinition>, BitFuncError>,
    ) -> bool {
        match result {
            Ok(slots) => slots@.len() == scope.wiring.drivers.definitions@.len()
                && self.expansion_definition_prefix(scope, calls, slots@)
                && self.definition_widths_match(scope, slots@)
                && (forall|slot: int| 0 <= slot < slots@.len() && !call_covers(calls, slot) ==>
                    bit_definition_matches(scope.inputs@, slots@.take(slot), #[trigger] slots@[slot]))
                && (forall|group: int| 0 <= group < selected.len() ==> {
                    let call = #[trigger] selected[group];
                    let range = call.group.outputs;
                    let outputs = call.template.output_widths_model();
                    &&& range.start < range.end <= slots@.len()
                    &&& range.start + outputs.len() == range.end
                    &&& forall|port: int| 0 <= port < outputs.len() ==>
                        slots@[range.start + port].width == #[trigger] outputs[port]
                })
                && form_spans_valid(scope.source.text, scope.parsed.syntax.forms@, scope.source.text.spec_bytes().len() as int)
                && (forall|group: int| 0 <= group < selected.len()
                    ==> *(#[trigger] selected[group]).group.expression.source == *scope.source)
                && (forall|group: int, port: int| 0 <= group < selected.len()
                    && 0 <= port < selected[group].arguments@.len() ==>
                    #[trigger] root_argument_matches_width(scope.source, scope.parsed.syntax.forms@, scope.inputs@,
                        slots@, selected[group], port, scope.limit))
                && forall|group: int, child: int, port: int| 0 <= group < selected.len()
                    && 0 <= child < selected[group].children@.len()
                    && 0 <= port < selected[group].children@[child].arguments@.len() ==>
                    #[trigger] expression_argument_matches_width(scope.source, scope.parsed.syntax.forms@,
                        scope.inputs@, slots@, selected[group], child, port, scope.limit),
            Err(error) => exists|prefix: Seq<CheckedBitDefinition>|
                #[trigger] self.expansion_definition_prefix(scope, calls, prefix)
                && self.definition_widths_match(scope, prefix)
                && prefix.len() < scope.wiring.drivers.definitions@.len()
                && !call_covers(calls, prefix.len() as int)
                && self.definition_error(scope, prefix, error),
        }
    }

    pub(super) proof fn prepared_definition_width_evidence(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, selected: Seq<ResolvedTemplateCall>,
        definitions: Vec<CheckedBitDefinition>,
    )
        requires self.prepared_definition_result(scope, calls, selected, Ok(definitions)),
        ensures
            definitions@.len() == scope.wiring.drivers.definitions@.len(),
            self.definition_widths_match(scope, definitions@),
    {}

    /// 展開準備が成功したとき、通常の定義が元の右辺と型に対応することを取り出す。
    pub(super) proof fn prepared_ordinary_definition_evidence(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, selected: Seq<ResolvedTemplateCall>,
        definitions: Vec<CheckedBitDefinition>, i: int,
    )
        requires
            self.prepared_definition_result(scope, calls, selected, Ok(definitions)),
            0 <= i < definitions@.len(),
            !call_covers(calls, i),
        ensures
            definitions@.len() == scope.wiring.drivers.definitions@.len(),
            self.bit_definition_from_source(scope, definitions@.take(i), i, definitions@[i]),
            self.definition_widths_match(scope, definitions@),
    {
        reveal(UseAliases::expansion_definition_prefix);
    }

    /// 展開準備で確定した呼び出しと実際の出力幅から、関数本体を定義順に取り出す。
    ///
    /// # Errors
    ///
    /// 通常の右辺の変換で最初に見つかったエラーを返す。
    pub(super) fn project_prepared_definition_body(
        &self, scope: &FuncProjection<'_, 'p, 'a>, calls: &[CheckedExpansionCall<'p, 'a>],
        selected: &[ResolvedTemplateCall<'_, 'p, 'a>], literal_widths: &[Option<u64>], concats: Vec<ConcatProjection>,
        Ghost(plan): Ghost<FunctionExpansionOrder<'p, 'a>>, Ghost(prepared): Ghost<PreparedExpansionBody<'p, 'a>>,
        Ghost(templates): Ghost<&FunctionTemplates<'p, 'a>>,
    ) -> (result: Result<Vec<CheckedBitDefinition<'p, 'a>>, BitFuncError<'p, 'a>>)
        requires
            self.projection_context(scope), self.projection_port_widths_match(scope), self.projection_structures_match(scope),
            self.prepared_expansion_body_matches(plan, scope.file, scope.entry, scope.limit, &prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            calls@ == prepared.calls@,
            literal_widths@ == prepared.typed.literals.widths@ && literal_widths@.len() == scope.types@.len(),
            concats@ == prepared.projections.concats@,
            scope.structures@ == prepared.projections.entries@,
            self.expansion_selection_matches(&plan, templates, (scope.file, scope.entry, scope.limit), &prepared, selected@),
            forall|i: int| 0 <= i < selected@.len() ==> {
                let call = #[trigger] selected@[i];
                &&& self.resolved_template_call_matches(&plan, (scope.file, scope.entry, scope.limit), &prepared, i, call)
                &&& scope.layouts.is_none() ==>
                    !has_structure_port(call.template.signature_model().inputs@)
                        && !has_structure_port(call.template.signature_model().outputs@)
            },
        ensures self.prepared_definition_result(scope, calls@, selected@, result),
    {
        let call_widths = self.resolved_call_output_widths(scope, selected, Ghost(plan), Ghost(prepared));
        proof {
            assert forall|i: int| 0 <= i < call_widths@.len() implies {
                let signature = (#[trigger] prepared.calls@[i])._signature@.signature;
                signature is Function && self.port_widths_match(signature->Function_0.outputs@, call_widths@[i]@, scope.layouts)
            } by {
                assert(call_widths@[i]@ == selected@[i].template.output_widths_model());
            };
            self.prepared_calls_fit_body(scope, plan, &prepared, call_widths@);
        }
        let result = self.project_definition_body(scope, calls, call_widths.as_slice(), literal_widths, concats, Ghost(prepared.typed));
        proof {
            if let Ok(slots) = &result {
                reveal(UseAliases::body_calls_match);
                reveal(UseAliases::expansion_definition_prefix);
                reveal(UseAliases::definition_widths_match);
                assert forall|slot: int| 0 <= slot < slots@.len() && !call_covers(calls@, slot) implies
                    bit_definition_matches(scope.inputs@, slots@.take(slot), #[trigger] slots@[slot]) by {
                    assert(self.bit_definition_from_source(scope, slots@.take(slot), slot, slots@[slot]));
                };
                assert forall|group: int| 0 <= group < selected@.len() implies {
                    let call = #[trigger] selected@[group];
                    let range = call.group.outputs;
                    let outputs = call.template.output_widths_model();
                    &&& range.start < range.end <= slots@.len()
                    &&& range.start + outputs.len() == range.end
                    &&& forall|port: int| 0 <= port < outputs.len() ==>
                        slots@[range.start + port].width == #[trigger] outputs[port]
                } by {
                    assert(calls@[group] == *selected@[group].group);
                    let call = &calls@[group];
                    let outputs = selected@[group].template.output_widths_model();
                    let first = call.outputs.start;
                    assert(call_widths@[group]@ == outputs);
                    reveal(UseAliases::call_definition_widths_match);
                    assert forall|port: int| 0 <= port < outputs.len() implies
                        slots@[first + port].width == #[trigger] outputs[port] by {
                        let slot = slots@[first + port];
                        let ty = scope.types@[first + port]->Some_0.ty;
                        assert(self.port_width_matches(ty, slot.width, scope.layouts));
                        assert(self.port_width_matches(ty, outputs[port], scope.layouts));
                        if let ResolvedPortType::Struct { .. } = ty {
                            self.layout_port_widths_agree(scope.layouts->Some_0, ty, slot.width as int, outputs[port] as int);
                        }
                    };
                };
                parsed_index_evidence(*scope.source, *scope.parsed);
                assert forall|group: int| 0 <= group < selected@.len()
                    implies *(#[trigger] selected@[group]).group.expression.source == *scope.source by {
                    self.expansion_callee_template_evidence(plan, (scope.file, scope.entry, scope.limit), &prepared, group);
                };
                assert forall|group: int, port: int| 0 <= group < selected@.len()
                    && 0 <= port < selected@[group].arguments@.len() implies
                    #[trigger] root_argument_matches_width(scope.source, scope.parsed.syntax.forms@, scope.inputs@,
                        slots@, selected@[group], port, scope.limit) by {
                    reveal(UseAliases::body_calls_match);
                    let group_call = calls@[group];
                    assert(selected@[group].group.outputs.start == group_call.outputs.start);
                    self.prepared_argument_matches_width(scope, &plan, templates, &prepared, selected@[group], group, port, slots@);
                };
                assert forall|group: int, child: int, port: int| 0 <= group < selected@.len()
                    && 0 <= child < selected@[group].children@.len()
                    && 0 <= port < selected@[group].children@[child].arguments@.len() implies
                    #[trigger] expression_argument_matches_width(scope.source, scope.parsed.syntax.forms@,
                        scope.inputs@, slots@, selected@[group], child, port, scope.limit) by {
                    self.prepared_child_argument_matches_width(scope, &plan, templates, &prepared,
                        selected@[group], group, child, port, slots@);
                };
            }
        }
        result
    }

    proof fn keep_body_prefix(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>,
        before: Seq<CheckedBitDefinition>, after: Seq<CheckedBitDefinition>, active: Option<usize>,
    )
        requires
            self.expansion_definition_prefix(scope, calls, before),
            before.len() < after.len() <= scope.types@.len(),
            after.take(before.len() as int) == before,
            forall|j: int| 0 <= j < before.len() ==>
                location_in_source((#[trigger] before[j]).expression) && before[j].width > 0,
            match active {
                Some(g) => {
                    &&& g < calls.len()
                    &&& calls[g as int].outputs.start == before.len()
                    &&& calls[g as int].outputs.end == after.len()
                    &&& location_in_source(calls[g as int].expression)
                    &&& forall|j: int| before.len() <= j < after.len() ==>
                        projected_call_slot(calls, g as int, j, #[trigger] after[j]) && after[j].width > 0
                },
                None => {
                    &&& after.len() == before.len() + 1
                    &&& !call_covers(calls, before.len() as int)
                    &&& self.bit_definition_from_source(scope, before, before.len() as int, after[before.len() as int])
                },
            },
        ensures
            self.expansion_definition_prefix(scope, calls, after),
            forall|j: int| 0 <= j < after.len() ==>
                location_in_source((#[trigger] after[j]).expression) && after[j].width > 0,
    {
        reveal(UseAliases::expansion_definition_prefix);
        assert forall|j: int| 0 <= j < after.len() implies {
            let slot = #[trigger] after[j];
            &&& location_in_source(slot.expression) && slot.width > 0
            &&& if call_covers(calls, j) {
                exists|g: int| 0 <= g < calls.len() && #[trigger] projected_call_slot(calls, g, j, slot)
            } else {
                self.bit_definition_from_source(scope, after.take(j), j, slot)
            }
        } by {
            if j < before.len() {
                assert(after[j] == before[j]);
                assert(after.take(j) =~= before.take(j));
                if call_covers(calls, j) {
                    let g = choose|g: int| 0 <= g < calls.len() && #[trigger] projected_call_slot(calls, g, j, before[j]);
                    assert(projected_call_slot(calls, g, j, after[j]));
                } else {
                    assert(self.bit_definition_from_source(scope, before.take(j), j, before[j]));
                }
            } else if let Some(g) = active {
                assert(projected_call_slot(calls, g as int, j, after[j]));
                assert(call_covers(calls, j));
            } else {
                assert(j == before.len());
                assert(after.take(j) == before);
            }
        };
    }

    proof fn next_call_is_later(
        calls: Seq<CheckedExpansionCall>, group: usize, at: usize,
    )
        requires
            group <= calls.len(),
            group < calls.len() ==> at < calls[group as int].outputs.start,
            forall|g: int| 0 <= g < group ==> (#[trigger] calls[g]).outputs.end <= at,
            forall|a: int, b: int| 0 <= a < b < calls.len() ==>
                (#[trigger] calls[a]).outputs.end <= (#[trigger] calls[b]).outputs.start,
            forall|g: int| 0 <= g < calls.len() ==> (#[trigger] calls[g]).outputs.start < calls[g].outputs.end,
        ensures
            !call_covers(calls, at as int),
            forall|g: int| group <= g < calls.len() ==> at < (#[trigger] calls[g]).outputs.start,
    {
        assert forall|g: int| group <= g < calls.len() implies at < (#[trigger] calls[g]).outputs.start by {
            if group < g {
                assert(calls[group as int].outputs.end <= calls[g].outputs.start);
            }
        };
    }

    pub(super) fn project_standalone_definitions(
        &self, scope: &FuncProjection<'_, 'p, 'a>, literal_widths: &[Option<u64>], concats: Vec<ConcatProjection>,
        Ghost(typed): Ghost<FuncSignalTypes<'p, 'a>>,
    ) -> (result: Result<Vec<CheckedBitDefinition<'p, 'a>>, BitFuncError<'p, 'a>>)
        requires
            self.projection_context(scope), self.projection_port_widths_match(scope), self.projection_structures_match(scope),
            0 < scope.wiring.drivers.signature.outputs@.len(),
            supported_ports(scope.wiring.drivers.signature.inputs@),
            supported_ports(scope.wiring.drivers.signature.outputs@),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            typed.types@ == scope.types@,
            literal_widths@ == typed.literals.widths@,
            literal_widths@.len() == scope.types@.len(),
            self.func_structure_projections_complete(scope.file, scope.entry, scope.limit, typed, scope.wiring, scope.structures@),
            self.func_concat_projections_complete(scope.file, scope.entry, scope.limit, typed, scope.wiring, concats@),
            super::super::super::function_atoms::concat_projections_match(scope.file, scope.entry, scope.limit,
                scope.source, scope.parsed, scope.wiring, scope.types@, concats@),
        ensures match result {
            Ok(slots) => slots@.len() == scope.wiring.drivers.definitions@.len()
                && self.definition_prefix(scope, slots@) && self.definition_widths_match(scope, slots@),
            Err(error) => self.projection_failure(scope, error),
        },
    {
        reveal(UseAliases::body_calls_match);
        let calls: &[CheckedExpansionCall] = &[];
        assert(calls@ =~= Seq::empty());
        let result = self.project_definition_body(scope, calls, &[], literal_widths, concats, Ghost(typed));
        proof {
            reveal(UseAliases::expansion_definition_prefix);
            reveal(UseAliases::definition_prefix);
            match &result {
                Ok(slots) => { assert(self.definition_prefix(scope, slots@)); },
                Err(error) => {
                    let prefix = choose|prefix: Seq<CheckedBitDefinition>|
                        #[trigger] self.expansion_definition_prefix(scope, calls@, prefix)
                        && self.definition_widths_match(scope, prefix)
                        && prefix.len() < scope.wiring.drivers.definitions@.len()
                        && !call_covers(calls@, prefix.len() as int)
                        && self.definition_error(scope, prefix, *error);
                    assert(self.definition_prefix(scope, prefix));
                    assert(self.projection_failure(scope, *error));
                },
            }
        }
        result
    }

    /// 検査済みの定義をソース順に取り出す。呼び出しは全出力を登録してから次の定義へ進む。
    ///
    /// # Errors
    ///
    /// 通常の右辺を取り出せない場合は、定義順で最初に失敗した式の診断を返す。
    #[verifier::rlimit(32)]
    pub(super) fn project_definition_body<'b>(
        &self, scope: &FuncProjection<'_, 'p, 'a>, calls: &[CheckedExpansionCall<'p, 'a>],
        call_widths: &[&'b [u64]], literal_widths: &[Option<u64>], mut concats: Vec<ConcatProjection>,
        Ghost(typed): Ghost<FuncSignalTypes<'p, 'a>>,
    ) -> (result: Result<Vec<CheckedBitDefinition<'p, 'a>>, BitFuncError<'p, 'a>>)
        requires
            self.projection_context(scope),
            self.projection_port_widths_match(scope),
            self.projection_structures_match(scope),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            typed.types@ == scope.types@,
            literal_widths@ == typed.literals.widths@,
            literal_widths@.len() == scope.types@.len(),
            self.func_structure_projections_complete(scope.file, scope.entry, scope.limit, typed, scope.wiring, scope.structures@),
            self.func_concat_projections_complete(scope.file, scope.entry, scope.limit, typed, scope.wiring, concats@),
            super::super::super::function_atoms::concat_projections_match(scope.file, scope.entry, scope.limit,
                scope.source, scope.parsed, scope.wiring, scope.types@, concats@),
            self.body_calls_match(scope, calls@, call_widths@, concats@),
        ensures match result {
            Ok(slots) => slots@.len() == scope.wiring.drivers.definitions@.len()
                && self.expansion_definition_prefix(scope, calls@, slots@)
                && self.definition_widths_match(scope, slots@),
            Err(error) => exists|prefix: Seq<CheckedBitDefinition>|
                #[trigger] self.expansion_definition_prefix(scope, calls@, prefix)
                && self.definition_widths_match(scope, prefix)
                && prefix.len() < scope.wiring.drivers.definitions@.len()
                && !call_covers(calls@, prefix.len() as int)
                && self.definition_error(scope, prefix, error),
        },
    {
        let ghost concat_model = concats@;
        let mut slots: Vec<CheckedBitDefinition<'p, 'a>> = Vec::new();
        let mut i = 0usize;
        let mut group = 0usize;
        let mut next_structure = 0usize;
        let mut next_concat = 0usize;
        proof {
            concat_projections_order(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                scope.wiring, scope.types@, concat_model);
            reveal(concat_cursor_ready);
            reveal(UseAliases::expansion_definition_prefix);
            reveal(UseAliases::definition_widths_match);
        }
        while i < scope.wiring.drivers.definitions.len()
            invariant
                self.projection_context(scope),
                self.projection_port_widths_match(scope),
                self.projection_structures_match(scope),
                self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
                typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
                typed.types@ == scope.types@,
                literal_widths@ == typed.literals.widths@,
                literal_widths@.len() == scope.types@.len(),
                self.func_structure_projections_complete(scope.file, scope.entry, scope.limit, typed, scope.wiring, scope.structures@),
                self.func_concat_projections_complete(scope.file, scope.entry, scope.limit, typed, scope.wiring, concat_model),
                self.body_calls_match(scope, calls@, call_widths@, concat_model),
                i == slots@.len() <= scope.wiring.drivers.definitions@.len(),
                group <= calls@.len(),
                forall|j: int| 0 <= j < group ==> (#[trigger] calls@[j]).outputs.end <= i,
                forall|j: int| group <= j < calls@.len() ==> i <= (#[trigger] calls@[j]).outputs.start,
                next_structure <= scope.structures@.len(),
                forall|j: int| 0 <= j < next_structure ==> (#[trigger] scope.structures@[j]).target < i,
                forall|j: int| next_structure <= j < scope.structures@.len() ==> i <= (#[trigger] scope.structures@[j]).target,
                concat_cursor_ready(concats@, concat_model, next_concat, i as int),
                forall|a: int, b: int| 0 <= a < b < concat_model.len()
                    ==> (#[trigger] concat_model[a]).target < (#[trigger] concat_model[b]).target,
                forall|j: int| 0 <= j < concat_model.len() ==> concat_projection_matches(
                    scope.file, scope.entry, scope.limit, scope.source, scope.parsed, scope.wiring, scope.types@,
                    #[trigger] concat_model[j]),
                self.expansion_definition_prefix(scope, calls@, slots@),
                self.definition_widths_match(scope, slots@),
                forall|j: int| 0 <= j < slots@.len() ==>
                    location_in_source((#[trigger] slots@[j]).expression) && slots@[j].width > 0,
            decreases scope.wiring.drivers.definitions@.len() - i,
        {
            let ghost before = slots@;
            let head = if group < calls.len() { Some(calls[group].outputs.start) } else { None };
            if matches!(expansion_call_at_slot(head, None, i), ExpansionSlot::Function) {
                let call = &calls[group];
                proof { reveal(UseAliases::body_calls_match); }
                self.append_call_definitions(scope, call, group, call_widths[group], &mut slots);
                proof {
                    reveal(concat_cursor_ready);
                    assert forall|j: int| before.len() <= j < slots@.len() implies
                        projected_call_slot(calls@, group as int, j, #[trigger] slots@[j]) && slots@[j].width > 0 by {
                        assert(calls@[group as int] == *call);
                        let port = j - call.outputs.start;
                        assert(slots@[call.outputs.start + port] == slots@[j]);
                    };
                    self.keep_body_prefix(scope, calls@, before, slots@, Some(group));
                    assert forall|j: int| group < j < calls@.len() implies
                        call.outputs.end <= (#[trigger] calls@[j]).outputs.start by {
                        assert(calls@[group as int].outputs.end <= calls@[j].outputs.start);
                    };
                    assert forall|j: int| next_structure <= j < scope.structures@.len() implies
                        call.outputs.end <= (#[trigger] scope.structures@[j]).target by {
                        assert(!(call.outputs.start <= scope.structures@[j].target < call.outputs.end));
                    };
                    assert forall|j: int| next_concat <= j < concat_model.len() implies
                        call.outputs.end <= (#[trigger] concat_model[j]).target by {
                        assert(concats@[j] == concat_model[j]);
                        assert(i <= concat_model[j].target);
                        assert(!(call.outputs.start <= concat_model[j].target < call.outputs.end));
                    };
                }
                i = call.outputs.end;
                group += 1;
                continue;
            }

            proof {
                reveal(UseAliases::body_calls_match);
                Self::next_call_is_later(calls@, group, i);
            }

            let (cursor, structure) = next_structure_projection(scope.structures.as_slice(), next_structure, i);
            next_structure = cursor;
            let (cursor, concat) = take_concat_projection(&mut concats, next_concat, i, Ghost(concat_model));
            proof {
                if let Some(row) = &concat {
                    assert(*row == concat_model[next_concat as int]);
                } else if concat_type_ready(scope, i as int) {
                    self.ready_concat_has_row(scope, typed, concat_model, i as int);
                    assert(false);
                }
            }
            next_concat = cursor;
            let slot = match self.project_definition(scope, slots.as_slice(), i, structure, concat,
                literal_widths[i], Ghost(typed)) {
                Ok(slot) => slot,
                Err(error) => {
                    assert(exists|prefix: Seq<CheckedBitDefinition>|
                        #[trigger] self.expansion_definition_prefix(scope, calls@, prefix)
                        && self.definition_widths_match(scope, prefix)
                        && prefix.len() < scope.wiring.drivers.definitions@.len()
                        && !call_covers(calls@, prefix.len() as int)
                        && self.definition_error(scope, prefix, error));
                    return Err(error);
                },
            };
            proof { self.extend_definition_widths(scope, typed, before, slot, structure); }
            slots.push(slot);
            proof {
                assert(slots@.take(before.len() as int) =~= before);
                self.keep_body_prefix(scope, calls@, before, slots@, None);
            }
            i += 1;
        }
        Ok(slots)
    }
}

/// 展開したネットリストと、宣言順の入出力幅および構造体配置。
pub(in crate::project::use_aliases::bit_func) struct ExpandedBody<'p, 'a> {
    pub(in crate::project::use_aliases::bit_func) circuit: LoweredBitFunc,
    pub(in crate::project::use_aliases::bit_func) ports: PreparedBitFuncPorts<'p, 'a>,
    pub(in crate::project::use_aliases::bit_func) has_structure_ports: bool,
}

/// 呼び出しを含む関数の本体をネットリストに変換するときの診断。
#[derive(Debug)]
pub(in crate::project::use_aliases::bit_func) enum ExpandedBodyError<'p, 'a> {
    /// 宣言したポートまたは構造体配置に関する診断。
    Ports(BitFuncError<'p, 'a>),
    /// 定義の右辺を変換するときの診断。
    Definition(BitFuncError<'p, 'a>),
    /// 宣言と実際の出力幅が一致しない箇所。
    Output(BitFuncError<'p, 'a>),
    /// ビット範囲の割り当てまたは配線に関する診断。
    Lowering(ProjectedLoweringError<'p, 'a>),
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(in crate::project::use_aliases::bit_func) closed spec fn expanded_body_lowering_result(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        layout_limit: usize, gate_limit: usize, result: Result<ExpandedBody, ExpandedBodyError>,
    ) -> bool {
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let wiring = &prepared.typed.literals.wiring->Checked_0;
        exists|selected: Seq<ResolvedTemplateCall>|
        {
            &&& #[trigger] self.expansion_selection_matches(plan, table, caller, prepared, selected)
            &&& match result {
                Err(ExpandedBodyError::Ports(error)) => self.expanded_routine_ports_result(
                    file, entry, limit, wiring, prepared.projections.layouts, selected, Err(error)),
                _ => exists|ports: PreparedBitFuncPorts|
                    #[trigger] self.expanded_routine_ports_result(
                        file, entry, limit, wiring, prepared.projections.layouts, selected, Ok(ports))
                    && (result matches Ok(expanded) ==> expanded.ports == ports
                        && (expanded.has_structure_ports <==> has_structure_port(wiring.drivers.signature.inputs@)
                            || has_structure_port(wiring.drivers.signature.outputs@)))
                    && {
                        let scope = FuncProjection {
                            file, entry, limit, source, parsed, wiring,
                            inputs: &ports.inputs, outputs: &ports.outputs,
                            layouts: match &ports.layouts { Some(table) => Some(table), None => None },
                            types: &prepared.typed.types, structures: &prepared.projections.entries,
                        };
                        self.expanded_definition_lowering_result(&scope, prepared.calls@, selected,
                            prepared.projections.call_arguments.arguments@, layout_limit, gate_limit, result)
                    },
            }
        }
    }

    spec fn expanded_definition_lowering_result(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, selected: Seq<ResolvedTemplateCall>,
        arguments: Seq<ProjectedCallArgument>, layout_limit: usize, gate_limit: usize, result: Result<ExpandedBody, ExpandedBodyError>,
    ) -> bool {
        let drivers = scope.wiring.drivers.outputs@;
        &&& self.projection_context(scope)
        &&& match result {
            Err(ExpandedBodyError::Definition(error)) => self.prepared_definition_result(scope, calls, selected, Err(error)),
            _ => exists|slots: Vec<CheckedBitDefinition>|
                #[trigger] self.prepared_definition_result(scope, calls, selected, Ok(slots))
                && match result {
                    Err(ExpandedBodyError::Output(error)) => output_width_failure(
                        &scope.wiring.drivers.signature, scope.inputs@, scope.outputs@, slots@, drivers, error),
                    Ok(value) => output_widths_before(scope.inputs@, scope.outputs@, slots@, drivers, drivers.len() as int)
                        && projected_lowering_view(scope.inputs@, slots@, scope.outputs@,
                            drivers, scope.parsed.syntax.forms@, selected, arguments, layout_limit, gate_limit, Ok(value.circuit)),
                    Err(ExpandedBodyError::Lowering(error)) => output_widths_before(
                        scope.inputs@, scope.outputs@, slots@, drivers, drivers.len() as int)
                        && projected_lowering_view(scope.inputs@, slots@, scope.outputs@,
                            drivers, scope.parsed.syntax.forms@, selected, arguments, layout_limit, gate_limit, Err(error)),
                    _ => false,
                },
        }
    }

    /// 展開に成功した本体から、元ソースの検査結果と同じ呼び出し先を取り出す。
    pub(super) proof fn expanded_body_success<'w>(
        &self, plan: &FunctionExpansionOrder, table: &'w FunctionTemplates<'p, 'a>, caller: (usize, usize, u64),
        prepared: &'w PreparedExpansionBody<'p, 'a>, bit_limit: usize, gate_limit: usize, value: &'w ExpandedBody<'p, 'a>,
    ) -> (witness: (FuncProjection<'w, 'p, 'a>, Seq<ResolvedTemplateCall<'w, 'p, 'a>>, Vec<CheckedBitDefinition<'p, 'a>>))
        requires self.expanded_body_lowering_result(plan, table, caller, prepared, bit_limit, gate_limit, Ok(*value)),
        ensures ({
            let (scope, selected, slots) = witness;
            let (file, entry, limit) = caller;
            let project = self.targets.project_model();
            let wiring = &prepared.typed.literals.wiring->Checked_0;
            let ports = &value.ports;
            let drivers = wiring.drivers.outputs@;
            &&& scope == (FuncProjection { file, entry, limit, source: &project.sources_model()[file as int],
                parsed: &project.circuits_model()[file as int], wiring, inputs: &ports.inputs, outputs: &ports.outputs,
                layouts: match &ports.layouts { Some(table) => Some(table), None => None },
                types: &prepared.typed.types, structures: &prepared.projections.entries })
            &&& self.projection_context(&scope)
            &&& self.projection_port_widths_match(&scope)
            &&& self.prepared_expansion_body_matches(*plan, file, entry, limit, prepared)
                ==> self.projection_structures_match(&scope)
            &&& self.expansion_selection_matches(plan, table, caller, prepared, selected)
            &&& self.expanded_routine_ports_result(file, entry, limit, wiring, prepared.projections.layouts, selected, Ok(*ports))
            &&& self.prepared_definition_result(&scope, prepared.calls@, selected, Ok(slots))
            &&& output_widths_before(ports.inputs@, ports.outputs@, slots@, drivers, drivers.len() as int)
            &&& projected_lowering_view(ports.inputs@, slots@, ports.outputs@, drivers, scope.parsed.syntax.forms@,
                selected, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, Ok(value.circuit))
            &&& value.has_structure_ports <==> has_structure_port(wiring.drivers.signature.inputs@)
                || has_structure_port(wiring.drivers.signature.outputs@)
        }),
    {
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let wiring = &prepared.typed.literals.wiring->Checked_0;
        let ports = &value.ports;
        let scope = FuncProjection {
            file, entry, limit, source, parsed, wiring, inputs: &ports.inputs, outputs: &ports.outputs,
            layouts: match &ports.layouts { Some(table) => Some(table), None => None },
            types: &prepared.typed.types, structures: &prepared.projections.entries,
        };
        let selected = choose|rows: Seq<ResolvedTemplateCall<'w, 'p, 'a>>|
            #[trigger] self.expansion_selection_matches(plan, table, caller, prepared, rows)
            && self.expanded_routine_ports_result(file, entry, limit, wiring, prepared.projections.layouts, rows, Ok(*ports))
            && self.expanded_definition_lowering_result(&scope, prepared.calls@, rows, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, Ok(*value));
        let drivers = wiring.drivers.outputs@;
        let slots = choose|slots: Vec<CheckedBitDefinition>|
            #[trigger] self.prepared_definition_result(&scope, prepared.calls@, selected, Ok(slots))
            && output_widths_before(ports.inputs@, ports.outputs@, slots@, drivers, drivers.len() as int)
            && projected_lowering_view(ports.inputs@, slots@, ports.outputs@, drivers,
                parsed.syntax.forms@, selected, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, Ok(value.circuit));
        reveal(UseAliases::routine_ports_result);
        assert(self.projection_port_widths_match(&scope));
        assert(self.prepared_expansion_body_matches(*plan, file, entry, limit, prepared)
            ==> self.projection_structures_match(&scope)) by {
            if prepared.projections.layouts.is_none() {
                assert(self.prepared_expansion_body_matches(*plan, file, entry, limit, prepared)
                    ==> prepared.projections.entries@.len() == 0);
            }
        };
        (scope, selected, slots)
    }

    /// 展開した本体のポート幅とビット配置を、元の宣言の署名に結び付ける。
    pub(in crate::project::use_aliases::bit_func) proof fn expanded_body_ports_evidence(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, bit_limit: usize, gate_limit: usize, value: &ExpandedBody,
    )
        requires self.expanded_body_lowering_result(plan, table, caller, prepared, bit_limit, gate_limit, Ok(*value)),
        ensures ({
            let (file, entry, limit) = caller;
            let signature = prepared.typed.literals.wiring->Checked_0.drivers.signature;
            &&& self.typed_signature_evidence(file, entry, limit, Ok(Some(signature)))
            &&& self.template_port_widths_match(signature, limit, value.ports.inputs@, value.ports.outputs@, value.ports.layouts)
            &&& value.has_structure_ports <==> has_structure_port(signature.inputs@) || has_structure_port(signature.outputs@)
            &&& port_bit_layout_result(value.ports.inputs@, bit_limit, Ok(*value.circuit.input_layout_model()))
            &&& port_bit_layout_result(value.ports.outputs@, bit_limit, Ok(*value.circuit.output_layout_model()))
            &&& nor_evaluation_ready(value.circuit.netlist_model(), value.circuit.input_layout_model().total_bits_model() as nat)
            &&& value.circuit.netlist_model().outputs@.len() == value.circuit.output_layout_model().total_bits_model()
        }),
    {
        let (file, entry, limit) = caller;
        let (scope, selected, slots) = self.expanded_body_success(plan, table, caller, prepared, bit_limit, gate_limit, value);
        let wiring = scope.wiring;
        let ports = &value.ports;
        let drivers = wiring.drivers.outputs@;
        self.checked_wiring_is_func(file, entry, limit, *wiring);
        reveal(UseAliases::routine_ports_result);
        reveal(UseAliases::template_port_widths_match);
        projected_lowering_ports(ports.inputs@, slots@, ports.outputs@, drivers, scope.parsed.syntax.forms@,
            selected, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, &value.circuit);
    }

    /// 展開後の評価結果を、ソースが出力ポートごとに指定した駆動元の値に結び付ける。
    pub(super) proof fn expanded_body_output_values(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, bit_limit: usize, gate_limit: usize, value: &ExpandedBody,
        input: Seq<bool>, output: Seq<bool>,
    ) -> (gates: Seq<bool>)
        requires
            self.expanded_body_lowering_result(plan, table, caller, prepared, bit_limit, gate_limit, Ok(*value)),
            nor_evaluation(value.circuit.netlist_model(), input, output),
        ensures
            input.len() == value.circuit.input_layout_model().total_bits_model(),
            gate_values_match(input, value.circuit.netlist_model().gates@, gates),
            gates.len() == value.circuit.netlist_model().gates@.len() <= usize::MAX,
            source_outputs_match(&prepared.typed.literals.wiring->Checked_0,
                port_values(value.circuit.input_layout_model(), input), expanded_definition_values(&value.circuit, input, gates),
                port_values(value.circuit.output_layout_model(), output)),
    {
        let (scope, selected, slots) = self.expanded_body_success(plan, table, caller, prepared, bit_limit, gate_limit, value);
        let circuit = &value.circuit;
        let netlist = circuit.netlist_model();
        let drivers = scope.wiring.drivers.outputs@;
        projected_lowering_ports(scope.inputs@, slots@, scope.outputs@, drivers, scope.parsed.syntax.forms@,
            selected, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, circuit);
        reveal(UseAliases::routine_ports_result);
        reveal(nor_evaluation);
        vstd::std_specs::vec::axiom_spec_len(&netlist.gates);
        let gates = choose|gates: Seq<bool>| #[trigger] gate_values_match(input, netlist.gates@, gates)
            && gates.len() == netlist.gates@.len() && output_values_match(input, gates, netlist.outputs@, output);
        reveal(UseAliases::template_port_widths_match);
        projected_lowering_output_values(scope.inputs@, slots@, scope.outputs@, drivers, scope.parsed.syntax.forms@,
            selected, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, circuit, input, gates, output);
        let incoming = port_values(circuit.input_layout_model(), input);
        let values = expanded_definition_values(circuit, input, gates);
        let outgoing = port_values(circuit.output_layout_model(), output);
        assert forall|i: int| 0 <= i < outgoing.len() implies {
            let driver = #[trigger] drivers[i];
            match driver {
                OutputDriver::Input(port) => port < incoming.len(),
                OutputDriver::Definition(index) => index < values.len(),
            }
        } by {
            assert(bit_driver_width(scope.inputs@, slots@, drivers[i]) == Some(scope.outputs@[i]));
        };
        source_outputs_from_driver_values(scope.wiring, incoming, values, outgoing);
        gates
    }

    /// 展開した呼び出しの評価を、同じ参照先と元ソースの引数・左辺に結び付ける。
    pub(super) proof fn expanded_body_source_call_evaluation<'w>(
        &self, plan: &FunctionExpansionOrder, table: &'w FunctionTemplates<'p, 'a>, caller: (usize, usize, u64),
        prepared: &'w PreparedExpansionBody<'p, 'a>, bit_limit: usize, gate_limit: usize, value: &'w ExpandedBody<'p, 'a>,
        index: int, input: Seq<bool>, gates: Seq<bool>,
    ) -> (result: (ResolvedTemplateCall<'w, 'p, 'a>, MixedCallEvaluation))
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
            self.expanded_body_lowering_result(plan, table, caller, prepared, bit_limit, gate_limit, Ok(*value)),
            0 <= index < prepared.calls@.len(),
            input.len() == value.circuit.input_layout_model().total_bits_model(),
            gate_values_match(input, value.circuit.netlist_model().gates@, gates),
            gates.len() == value.circuit.netlist_model().gates@.len() <= usize::MAX,
        ensures ({
            let group = prepared.calls@[index];
            let root = prepared.projections.calls@[index];
            let selected = result.0;
            let template = selected.template;
            let callee = template.circuit_model();
            let wiring = prepared.typed.literals.wiring->Checked_0;
            let incoming = port_values(value.circuit.input_layout_model(), input);
            let definitions = expanded_definition_values(&value.circuit, input, gates);
            &&& self.resolved_template_call_matches(plan, caller, prepared, index, selected)
            &&& self.resolved_expression_calls_match(plan, table, caller.2, selected.group.postorder,
                prepared.projections.call_arguments.arguments@, selected.children@)
            &&& 0 <= group._order@.0 < group._order@.1 < plan.order_model().len()
            &&& plan.position_model(group._order@.0) == Some((root.target_file, root.target_entry))
            &&& plan.position_model(group._order@.1) == Some((caller.0, caller.1))
            &&& group.vertex == plan.order_model()[group._order@.0]
            &&& table.slots_model()[group.vertex as int] == Some(*template)
            &&& group.outputs.end <= definitions.len()
            &&& match result.1 {
                MixedCallEvaluation::Flat(arguments, outputs) =>
                    nor_evaluation(callee.netlist_model(), arguments, outputs)
                    && self.source_function_call_values(caller, &wiring, root.definition, group._signature@, group.outputs,
                        (root.target_file, root.target_entry), incoming, definitions, template.input_widths_model(),
                        port_values(callee.input_layout_model(), arguments), port_values(callee.output_layout_model(), outputs)),
                MixedCallEvaluation::Nested(evaluation) =>
                    evaluated_nested_call_matches(self, caller, prepared, index, &selected, incoming, definitions, evaluation),
            }
        }),
    {
        let (scope, selected, slots) = self.expanded_body_success(plan, table, caller, prepared, bit_limit, gate_limit, value);
        let call = selected[index];
        let root = prepared.projections.calls@[index];
        let forms = scope.parsed.syntax.forms@;
        let drivers = scope.wiring.drivers.outputs@;
        let values = expanded_definition_values(&value.circuit, input, gates);
        self.prepared_call_matches_source_site(plan, caller, prepared, index);
        reveal(UseAliases::routine_ports_result);
        reveal(UseAliases::template_port_widths_match);
        reveal(UseAliases::prepared_definition_result);
        let evidence = projected_lowering_call_evaluation(self, plan, caller, prepared, scope.inputs@,
            slots@, scope.outputs@, drivers, forms, selected, index, bit_limit, gate_limit, &value.circuit, input, gates);
        if let MixedCallEvaluation::Flat(arguments, outputs) = evidence {
            let callee = call.template.circuit_model();
            assert(evaluated_flat_call_matches(self, caller, prepared, index, call,
                port_values(value.circuit.input_layout_model(), input), values, arguments, outputs));
            self.source_function_call_values_intro(caller, scope.wiring, root.definition, call.group._signature@,
                call.group.outputs, (root.target_file, root.target_entry), port_values(value.circuit.input_layout_model(), input),
                values, call.template.input_widths_model(), port_values(callee.input_layout_model(), arguments),
                port_values(callee.output_layout_model(), outputs));
        }
        (call, evidence)
    }

    /// 厳格解析と型検査を終えた本体を、先行する関数のネットリストを使って配線へ変換する。
    ///
    /// # Errors
    ///
    /// ポート、定義の右辺、出力幅、ビット範囲と配線の順に検査し、失敗した段階の診断を返す。
    pub(in crate::project::use_aliases::bit_func) fn lower_expanded_body(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, templates: &FunctionTemplates<'p, 'a>,
        caller: (usize, usize, u64), prepared: PreparedExpansionBody<'p, 'a>, layout_limit: usize, gate_limit: usize,
    ) -> (result: Result<ExpandedBody<'p, 'a>, ExpandedBodyError<'p, 'a>>)
        requires
            self.can_resolve(), self.function_expansion_evidence(Ok(*plan)),
            self.function_templates_match(plan, caller.2, templates),
            plan.position_model(templates.next_rank() as int) == Some((caller.0, caller.1)),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, &prepared),
        ensures self.expanded_body_lowering_result(plan, templates, caller, &prepared, layout_limit, gate_limit, result),
    {
        let (file, entry, limit) = caller;
        let ghost original = prepared;
        let FuncWiringResult::Checked(wiring) = &prepared.typed.literals.wiring else {
            proof { assert(false); }
            unreachable!()
        };
        proof {
            self.checked_types_keep_wiring(file, entry, limit, prepared.typed, *wiring);
            self.literal_widths_fit_wiring(file, entry, limit, &prepared.typed.literals, wiring);
            self.checked_wiring_is_func(file, entry, limit, *wiring);
            self.targets.parsed_project_model();
        }
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let selected = self.resolve_template_calls(plan, templates, prepared.calls.as_slice(),
            prepared.projections.call_arguments.arguments.as_slice(), Ghost(original), Ghost(caller));
        let port_result = self.prepare_expanded_routine_ports(file, entry, limit, wiring,
            prepared.projections.layouts, selected.as_slice());
        let ports = match port_result {
            Ok(ports) => ports,
            Err(error) => return Err(ExpandedBodyError::Ports(error)),
        };
        let _layout_ref = ports.layouts.as_ref();
        let scope = FuncProjection { file, entry, limit, source, parsed, wiring,
            inputs: &ports.inputs, outputs: &ports.outputs,
            #[cfg(verus_only)]
            layouts: _layout_ref,
            #[cfg(verus_only)]
            types: &prepared.typed.types,
            structures: &prepared.projections.entries,
        };
        proof {
            reveal(UseAliases::routine_ports_result);
            assert(self.projection_port_widths_match(&scope));
            assert(self.projection_structures_match(&scope)) by {
                if original.projections.layouts.is_none() {
                    assert(prepared.projections.entries@.len() == 0);
                }
            };
            assert forall|i: int| 0 <= i < selected@.len() implies {
                let call = #[trigger] selected@[i];
                &&& self.resolved_template_call_matches(plan, caller, &original, i, call)
                &&& scope.layouts.is_none() ==> !has_structure_port(call.template.signature_model().inputs@)
                    && !has_structure_port(call.template.signature_model().outputs@)
            } by {
                if scope.layouts.is_none() {
                    assert(!call_ports_need_structure_layout(selected@));
                    assert(!selected@[i].template.has_structure_ports_model());
                }
            };
        }
        let definitions = match self.project_prepared_definition_body(&scope, prepared.calls.as_slice(),
            selected.as_slice(), prepared.typed.literals.widths.as_slice(), prepared.projections.concats,
            Ghost(*plan), Ghost(original), Ghost(templates)) {
            Ok(definitions) => definitions,
            Err(error) => {
                let result = Err(ExpandedBodyError::Definition(error));
                assert(self.expanded_definition_lowering_result(&scope, original.calls@, selected@,
                    original.projections.call_arguments.arguments@, layout_limit, gate_limit, result));
                return result;
            },
        };
        if let Err(error) = check_output_widths(wiring, ports.inputs.as_slice(), ports.outputs.as_slice(), definitions.as_slice()) {
            let result = Err(ExpandedBodyError::Output(error));
            assert(self.expanded_definition_lowering_result(&scope, original.calls@, selected@,
                original.projections.call_arguments.arguments@, layout_limit, gate_limit, result));
            return result;
        }
        let forms = parsed.syntax.forms.as_slice();
        proof {
            assert forall|g: int| 0 <= g < selected@.len() implies
                resolved_call_fits_body(#[trigger] selected@[g], ports.inputs@, definitions@, forms@, limit) by {
                assert(*selected@[g].group.expression.source == *source);
            };
        }
        let lowered = lower_projected_expansion(self, ports.inputs.as_slice(), definitions.as_slice(),
            ports.outputs.as_slice(), wiring.drivers.outputs.as_slice(), forms, selected.as_slice(),
            layout_limit, gate_limit, Ghost((plan, caller, &original)), Ghost(templates));
        let has_structure_ports = contains_structure_port(wiring.drivers.signature.inputs.as_slice())
            || contains_structure_port(wiring.drivers.signature.outputs.as_slice());
        let result = match lowered {
            Ok(circuit) => Ok(ExpandedBody { circuit, ports, has_structure_ports }),
            Err(error) => Err(ExpandedBodyError::Lowering(error)),
        };
        assert(self.expanded_definition_lowering_result(&scope, original.calls@, selected@,
            original.projections.call_arguments.arguments@, layout_limit, gate_limit, result));
        result
    }
}

} // verus!
