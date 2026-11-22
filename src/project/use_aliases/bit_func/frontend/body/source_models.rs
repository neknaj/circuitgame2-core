//! 解決済みの呼び出しに、先行する関数のソース回路を割り当てる。

use super::*;
use super::super::super::lowering::{SourceChildModel, nested_arguments_ready, projected_call_mode, source_models_match_calls};
use super::super::super::lowering::{
    SourceBodyDefinition, function_body_source_circuit, projected_function_source_layout, source_body_matches_steps, source_step_ready,
};
use crate::netlist::source_clocked_layout;
use crate::project::DefinitionPosition;
use core::ops::Range;

verus! {

/// 展開順の接頭部にある各ソース回路が、同じ順位で完成したテンプレートに対応する。
pub(in crate::project::use_aliases::bit_func) open spec fn prior_function_source_models(
    plan: &FunctionExpansionOrder, table: &FunctionTemplates, models: Seq<SourceChildModel>,
) -> bool {
    &&& models.len() == table.next_rank() <= plan.order_model().len()
    &&& forall|rank: int| 0 <= rank < models.len() ==> {
        let model = #[trigger] models[rank];
        let vertex = plan.order_model()[rank];
        &&& vertex < table.slots_model().len()
        &&& table.slots_model()[vertex as int] matches Some(template)
        &&& source_clocked_layout(&model.circuit, template.circuit_model().netlist_model(), model.order, model.index)
    }
}

spec fn expression_source_models(
    selected: Seq<ResolvedExpressionCall>, prior: Seq<SourceChildModel>,
) -> Seq<Option<SourceChildModel>> {
    Seq::new(selected.len(), |i: int| {
        let child = selected[i];
        match child.template {
            Some(_) => Some(prior[child.child._rank@->Some_0]),
            None => None,
        }
    })
}

/// 型付きの呼び出しが選んだ順位から、根と子に渡す参照回路を得る。
pub(in crate::project::use_aliases::bit_func) closed spec fn source_models_for_step(
    target: SourceStepTarget, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, prior: Seq<SourceChildModel>,
) -> (Option<SourceChildModel>, Seq<Option<SourceChildModel>>) {
    match target {
        SourceStepTarget::Local => (None, Seq::empty()),
        SourceStepTarget::Function(index) => {
            let call = selected[index];
            (Some(prior[call.group._order@.0]), expression_source_models(call.children@, prior))
        },
        SourceStepTarget::Nor(index) =>
            (None, expression_source_models(roots[index].selected.children@, prior)),
    }
}

/// 厳格定義の先頭スロットから、型付きの右辺を選ぶ。
pub(in crate::project::use_aliases::bit_func) closed spec fn source_target_for_slot(
    first: usize, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>,
) -> SourceStepTarget {
    if exists|i: int| 0 <= i < selected.len() && (#[trigger] selected[i]).group.outputs.start == first {
        SourceStepTarget::Function(choose|i: int| 0 <= i < selected.len() && (#[trigger] selected[i]).group.outputs.start == first)
    } else if exists|i: int| 0 <= i < roots.len() && (#[trigger] roots[i]).selected.prepared.output_slot == first {
        SourceStepTarget::Nor(choose|i: int| 0 <= i < roots.len() && (#[trigger] roots[i]).selected.prepared.output_slot == first)
    } else {
        SourceStepTarget::Local
    }
}

/// 厳格な定義順で、左辺区間、型付きの右辺、先行する呼び出し先の回路を並べる。
pub(in crate::project::use_aliases::bit_func) closed spec fn strict_source_body(
    file: usize, entry: usize, ranges: Seq<Range<usize>>, selected: Seq<ResolvedTemplateCall>,
    roots: Seq<NorBinding>, prior: Seq<SourceChildModel>,
) -> Seq<SourceBodyDefinition> {
    Seq::new(ranges.len(), |i: int| {
        let slots = ranges[i];
        let target = source_target_for_slot(slots.start, selected, roots);
        let (ordinary, children) = source_models_for_step(target, selected, roots, prior);
        SourceBodyDefinition {
            site: DefinitionPosition { file, entry, definition: i as usize, reference: 0 },
            slots, target, ordinary, children,
        }
    })
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 署名と定義を型検査した結果から、関数のソース回路を定める。
    pub(in crate::project::use_aliases::bit_func) closed spec fn checked_function_source_layout(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, prior: Seq<SourceChildModel>, model: SourceChildModel,
    ) -> bool {
        exists|scope: FuncProjection, slots: Vec<CheckedBitDefinition>, selected: Seq<ResolvedTemplateCall>,
            rows: Seq<NorDefinition>, roots: Seq<NorBinding>| {
            &&& (scope.file, scope.entry, scope.limit) == caller
            &&& scope.wiring == &prepared.typed.literals.wiring->Checked_0
            &&& scope.types == &prepared.typed.types && scope.structures == &prepared.projections.entries
            &&& self.projection_context(&scope)
            &&& self.projection_port_widths_match(&scope)
            &&& self.projection_structures_match(&scope)
            &&& #[trigger] self.expansion_selection_matches(plan, table, caller, prepared, selected)
            &&& #[trigger] self.prepared_definition_result(&scope, prepared.calls@, selected, rows, Ok(slots))
            &&& #[trigger] self.expanded_body_nor_bindings(&scope, plan, table, prepared, rows, roots, slots@)
            &&& function_body_source_circuit(scope.source, scope.inputs@, slots@, scope.outputs@,
                scope.wiring.drivers.outputs@, scope.parsed.syntax.forms@, selected, roots,
                strict_source_body(scope.file, scope.entry, strict_definition_slots(scope.parsed, scope.entry, scope.wiring),
                    selected, roots, prior)) == Some((model.circuit, model.order))
        }
    }

    /// 厳格な定義順と先行する関数のソース回路から、現在の関数の配線と公開出力を求める。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases::bit_func) proof fn expanded_function_source_layout<'w>(
        &self, plan: &FunctionExpansionOrder, table: &'w FunctionTemplates<'p, 'a>, caller: (usize, usize, u64),
        prepared: &'w PreparedExpansionBody<'p, 'a>, capacity: usize, limit: usize, value: &'w ExpandedBody<'p, 'a>,
        prior: Seq<SourceChildModel>,
    ) -> (model: SourceChildModel)
        requires
            self.can_resolve(), self.function_template_plan(*plan),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
            self.expanded_body_lowering_result(plan, table, caller, prepared, capacity, limit, Ok(*value)),
            plan.position_model(table.next_rank() as int) == Some((caller.0, caller.1)),
            prior_function_source_models(plan, table, prior),
        ensures
            self.checked_function_source_layout(plan, table, caller, prepared, prior, model),
            source_clocked_layout(&model.circuit, value.circuit.netlist_model(), model.order, model.index),
    {
        let (scope, selected, roots, slots, steps, rows) =
            self.expanded_body_strict_steps(plan, table, caller, prepared, capacity, limit, value);
        self.strict_source_body_matches_history(&scope, plan, table, prepared, selected, rows, roots, slots, prior, steps);
        let ranges = strict_definition_slots(scope.parsed, scope.entry, scope.wiring);
        let definitions = strict_source_body(scope.file, scope.entry, ranges, selected, roots, prior);
        let model = projected_function_source_layout(scope.source, value.ports.inputs@, slots@, value.ports.outputs@,
            scope.wiring.drivers.outputs@, scope.parsed.syntax.forms@, selected, roots,
            prepared.projections.call_arguments.arguments@, capacity, caller.2, limit, &value.circuit, steps, definitions);
        reveal(UseAliases::checked_function_source_layout);
        assert(self.checked_function_source_layout(plan, table, caller, prepared, prior, model));
        model
    }

    /// 厳格索引から組み立てた各定義を、実際の変換が処理した右辺と照合する。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases::bit_func::frontend) proof fn strict_source_body_matches_history(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>, rows: Seq<NorDefinition>,
        roots: Seq<NorBinding>, slots: Vec<CheckedBitDefinition>, prior: Seq<SourceChildModel>,
        steps: Seq<super::super::super::lowering::WiringStep>,
    )
        requires
            self.projection_context(scope),
            self.function_template_plan(*plan),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            plan.position_model(table.next_rank() as int) == Some((scope.file, scope.entry)),
            self.expansion_selection_matches(plan, table, (scope.file, scope.entry, scope.limit), prepared, selected),
            self.expanded_body_nor_bindings(scope, plan, table, prepared, rows, roots, slots@),
            self.prepared_definition_result(scope, prepared.calls@, selected, rows, Ok(slots)),
            prior_function_source_models(plan, table, prior),
            rooted_source_step_ranges(steps) == strict_definition_slots(scope.parsed, scope.entry, scope.wiring),
            forall|i: int| 0 <= i < steps.len() ==> {
                let step = #[trigger] steps[i];
                let target = source_step_target(step);
                &&& source_step_range_matches(step, selected, roots, slots@.len())
                &&& target == source_target_for_slot(source_step_slots(step).start, selected, roots)
                &&& match target {
                    SourceStepTarget::Function(index) => 0 <= index < selected.len()
                        && (selected[index].children@.len() > 0 ==> nested_arguments_ready(&selected[index])),
                    _ => true,
                }
            },
        ensures source_body_matches_steps(scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots@, scope.limit,
            selected, roots, strict_source_body(scope.file, scope.entry,
                strict_definition_slots(scope.parsed, scope.entry, scope.wiring), selected, roots, prior), steps),
    {
        let ranges = strict_definition_slots(scope.parsed, scope.entry, scope.wiring);
        let definitions = strict_source_body(scope.file, scope.entry, ranges, selected, roots, prior);
        let forms = scope.parsed.syntax.forms@;
        let calls = Seq::new(selected.len(), |i: int| *selected[i].group);
        assert(calls =~= prepared.calls@) by {
            assert forall|i: int| 0 <= i < selected.len() implies #[trigger] calls[i] == prepared.calls@[i] by {
                assert(self.resolved_template_call_matches(plan, (scope.file, scope.entry, scope.limit), prepared, i, selected[i]));
            };
        };
        assert(definitions.len() == steps.len() == ranges.len());
        assert(ranges.len() <= usize::MAX) by {
            self.strict_definition_slot_partition(scope.file, scope.entry, scope.limit, scope.wiring);
            assert(scope.parsed == &self.targets.project_model().circuits_model()[scope.file as int]);
        };
        assert forall|i: int, j: int| 0 <= i < j < definitions.len() implies
            (#[trigger] definitions[i]).site.definition < (#[trigger] definitions[j]).site.definition by {};
        assert forall|i: int| 0 <= i < definitions.len() implies {
            let row = #[trigger] definitions[i];
            &&& row.slots == source_step_slots(steps[i])
            &&& row.target == source_step_target(steps[i])
            &&& source_step_ready(scope.source, forms, scope.inputs@, slots@, scope.limit, row.target, row.slots.start,
                selected, roots, row.ordinary, row.children)
        } by {
            let row = definitions[i];
            let step = steps[i];
            assert(ranges[i] == source_step_slots(step));
            assert(row.target == source_step_target(step));
            assert(source_step_range_matches(step, selected, roots, slots@.len()));
            self.expanded_step_source_models(scope, plan, table, prepared, selected, rows, roots, slots@, row.target, prior);
            reveal(UseAliases::expanded_body_nor_bindings);
            match row.target {
                SourceStepTarget::Local => {
                    let first = row.slots.start as int;
                    assert(!call_covers(prepared.calls@, first) && !nor_covers(rows, first));
                    reveal(UseAliases::prepared_definition_result);
                    assert(bit_definition_matches(scope.inputs@, slots@.take(first), slots@[first]));
                },
                SourceStepTarget::Function(index) => {
                    let call = selected[index];
                    reveal(UseAliases::prepared_definition_result);
                    assert(resolved_call_fits_body(call, scope.inputs@, slots@, forms, scope.limit)) by {
                        assert forall|port: int| 0 <= port < call.arguments@.len() implies
                            #[trigger] root_argument_matches_width(call.group.expression.source, forms,
                                scope.inputs@, slots@, call, port, scope.limit) by {};
                        assert forall|child: int, port: int| 0 <= child < call.children@.len()
                            && 0 <= port < call.children@[child].arguments@.len() implies
                            #[trigger] expression_argument_matches_width(call.group.expression.source, forms,
                                scope.inputs@, slots@, call, child, port, scope.limit) by {};
                    };
                },
                SourceStepTarget::Nor(index) => {
                    assert(nor_binding_fits_body(roots[index], scope.source, forms, scope.inputs@, slots@, scope.limit));
                },
            }
        };
    }

    /// 成功履歴の種別が、厳格定義の先頭から選んだ種別と等しいことを示す。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases::bit_func::frontend) proof fn source_target_for_strict_step(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>, rows: Seq<NorDefinition>,
        roots: Seq<NorBinding>, slots: Vec<CheckedBitDefinition>, step: super::super::super::lowering::WiringStep,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            self.expansion_selection_matches(plan, table, (scope.file, scope.entry, scope.limit), prepared, selected),
            self.prepared_definition_result(scope, prepared.calls@, selected, rows, Ok(slots)),
            self.expanded_body_nor_bindings(scope, plan, table, prepared, rows, roots, slots@),
            source_step_range_matches(step, selected, roots, slots@.len()),
        ensures source_target_for_slot(source_step_slots(step).start, selected, roots) == source_step_target(step),
    {
        let first = source_step_slots(step).start;
        let target = source_step_target(step);
        let calls = Seq::new(selected.len(), |i: int| *selected[i].group);
        let caller = (scope.file, scope.entry, scope.limit);
        assert(calls =~= prepared.calls@) by {
            assert forall|i: int| 0 <= i < selected.len() implies #[trigger] calls[i] == prepared.calls@[i] by {
                assert(self.resolved_template_call_matches(plan, caller, prepared, i, selected[i]));
            };
        };
        self.prepared_expansion_ordered_call_ranges(*plan, caller, prepared);
        assert forall|i: int| 0 <= i < selected.len() implies
            (#[trigger] selected[i]).group.outputs.start < selected[i].group.outputs.end by {
            assert(*selected[i].group == prepared.calls@[i]);
        };
        if let SourceStepTarget::Function(index) = target {
            assert(selected[index].group.outputs.start == first);
            let chosen = source_target_for_slot(first, selected, roots)->Function_0;
            assert(0 <= chosen < selected.len() && selected[chosen].group.outputs.start == first);
            if chosen != index {
                assert(*selected[chosen].group == prepared.calls@[chosen] && *selected[index].group == prepared.calls@[index]);
                if chosen < index {
                    assert(selected[chosen].group.outputs.end <= selected[index].group.outputs.start);
                } else {
                    assert(selected[index].group.outputs.end <= selected[chosen].group.outputs.start);
                }
            }
        } else {
            assert forall|i: int| 0 <= i < selected.len() implies (#[trigger] selected[i]).group.outputs.start != first by {
                if selected[i].group.outputs.start == first {
                    assert(calls[i] == *selected[i].group);
                    assert(call_covers(calls, first as int));
                    if let SourceStepTarget::Nor(index) = target {
                        reveal(UseAliases::expanded_body_nor_bindings);
                        assert(roots[index].selected.prepared.output_slot == first);
                        assert(!call_covers(prepared.calls@, first as int));
                    }
                }
            };
            if let SourceStepTarget::Nor(index) = target {
                let chosen = source_target_for_slot(first, selected, roots)->Nor_0;
                assert(0 <= chosen < roots.len() && roots[chosen].selected.prepared.output_slot == first);
                assert(chosen == index) by {
                    reveal(UseAliases::expanded_body_nor_bindings);
                    if chosen < index {
                        assert(roots[chosen].selected.prepared.output_slot < roots[index].selected.prepared.output_slot);
                    } else if index < chosen {
                        assert(roots[index].selected.prepared.output_slot < roots[chosen].selected.prepared.output_slot);
                    }
                };
            } else {
                assert forall|i: int| 0 <= i < roots.len() implies (#[trigger] roots[i]).selected.prepared.output_slot != first by {
                    if roots[i].selected.prepared.output_slot == first {
                        assert(nor_binding_covers(roots, first as int));
                    }
                };
            }
        }
    }

    /// 成功した関数呼び出しが子を持つ場合、その引数は入れ子の展開に渡せる。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases::bit_func::frontend) proof fn expanded_call_step_ready(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, inputs: Seq<u64>, slots: Seq<CheckedBitDefinition>, outputs: Seq<u64>,
        drivers: Seq<OutputDriver>, forms: Seq<Form>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>,
        capacity: usize, limit: usize, value: &LoweredBitFunc, steps: Seq<super::super::super::lowering::WiringStep>,
        at: int, index: int,
    )
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
            self.expansion_selection_matches(plan, table, caller, prepared, selected),
            projected_definition_history(inputs, slots, outputs, drivers, forms, selected, roots,
                prepared.projections.call_arguments.arguments@, capacity, limit, value, steps),
            slots.len() <= usize::MAX,
            0 <= at < steps.len(), 0 <= index < selected.len(),
            source_step_target(steps[at]) == SourceStepTarget::Function(index),
        ensures selected[index].children@.len() > 0 ==> nested_arguments_ready(&selected[index]),
    {
        let call = selected[index];
        let group = prepared.calls@[index];
        let arguments = prepared.projections.call_arguments.arguments@;
        projected_call_mode(inputs, slots, outputs, drivers, forms, selected, roots, arguments,
            capacity, limit, value, steps, at, index);
        if !nested_arguments_ready(&call) {
            assert(self.resolved_template_call_matches(plan, caller, prepared, index, call));
            assert forall|i: int| group.arguments.start <= i < group.arguments.end implies
                (#[trigger] arguments[i]).source.has_direct_wires() by {
                let port = i - group.arguments.start;
                assert(0 <= port < call.arguments@.len());
                assert(call.arguments@[port] == arguments[i]);
            };
            self.direct_expansion_has_no_children(*plan, caller, prepared, index);
            assert(self.resolved_expression_calls_match(plan, table, caller.2, group.postorder, arguments, call.children@));
            assert(call.children@.len() == 0);
        }
    }

    proof fn expression_source_models_match(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, limit: u64, references: core::ops::Range<usize>,
        prepared: Option<Vec<PreparedExpressionCall>>, arguments: Seq<ProjectedCallArgument>,
        selected: Seq<ResolvedExpressionCall>, prior: Seq<SourceChildModel>,
    )
        requires
            prior_function_source_models(plan, table, prior),
            self.resolved_expression_calls_match(plan, table, limit, prepared, arguments, selected),
            references.start <= references.end,
            forall|i: int| 0 <= i < selected.len()
                ==> references.start < (#[trigger] selected[i]).child.reference < references.end,
        ensures source_models_match_calls(selected, expression_source_models(selected, prior), references),
    {
        let models = expression_source_models(selected, prior);
        assert forall|i: int| 0 <= i < selected.len() implies {
            let call = #[trigger] selected[i];
            &&& references.start < call.child.reference < references.end
            &&& match call.template {
                Some(template) => models[i] matches Some(model)
                    && source_clocked_layout(&model.circuit, template.circuit_model().netlist_model(), model.order, model.index),
                None => models[i].is_none(),
            }
        } by {
            reveal(UseAliases::resolved_expression_call_matches);
            let call = selected[i];
            assert(prepared.is_some());
            let child = prepared->Some_0@[i];
            assert(self.resolved_expression_call_matches(plan, table, limit, arguments, child, call));
            if let Some(template) = call.template {
                assert(child._rank@.is_some() && child.vertex.is_some());
                let rank = child._rank@->Some_0;
                assert(0 <= rank < table.next_rank() == prior.len());
                assert(rank < plan.order_model().len());
                let vertex = plan.order_model()[rank];
                let model = prior[rank];
                assert(*call.child == child);
                assert(models[i] == Some(model));
                assert(vertex == child.vertex->Some_0);
                assert(table.slots_model()[vertex as int] == Some(*template));
                assert(source_clocked_layout(&model.circuit, template.circuit_model().netlist_model(), model.order, model.index));
            }
        };
    }

    /// 通常の根と入れ子の子を、実際に選択した先行テンプレートのソース回路に結び付ける。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases::bit_func::frontend) proof fn expanded_step_source_models(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates, prepared: &PreparedExpansionBody,
        selected: Seq<ResolvedTemplateCall>, rows: Seq<NorDefinition>, roots: Seq<NorBinding>, slots: Seq<CheckedBitDefinition>,
        target: SourceStepTarget, prior: Seq<SourceChildModel>,
    )
        requires
            self.projection_context(scope), self.function_template_plan(*plan),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            plan.position_model(table.next_rank() as int) == Some((scope.file, scope.entry)),
            self.expansion_selection_matches(plan, table, (scope.file, scope.entry, scope.limit), prepared, selected),
            self.expanded_body_nor_bindings(scope, plan, table, prepared, rows, roots, slots),
            prior_function_source_models(plan, table, prior),
            match target {
                SourceStepTarget::Function(index) => 0 <= index < selected.len(),
                SourceStepTarget::Nor(index) => 0 <= index < roots.len(),
                SourceStepTarget::Local => true,
            },
        ensures ({
            let (model, children) = source_models_for_step(target, selected, roots, prior);
            match target {
                SourceStepTarget::Function(index) => {
                    let call = selected[index];
                    &&& model matches Some(root)
                        && source_clocked_layout(&root.circuit, call.template.circuit_model().netlist_model(), root.order, root.index)
                    &&& source_models_match_calls(call.children@, children, call.group.references)
                },
                SourceStepTarget::Nor(index) => model.is_none()
                    && source_models_match_calls(roots[index].selected.children@, children, *roots[index].references),
                SourceStepTarget::Local => model.is_none() && children.len() == 0,
            }
        }),
    {
        let caller = (scope.file, scope.entry, scope.limit);
        let arguments = prepared.projections.call_arguments.arguments@;
        reveal(UseAliases::resolved_expression_call_matches);
        match target {
            SourceStepTarget::Function(index) => {
                let call = selected[index];
                let group = prepared.calls@[index];
                assert(self.resolved_template_call_matches(plan, caller, prepared, index, call));
                self.function_template_rank_at(*plan, (scope.file, scope.entry), group._order@.1, table.next_rank() as int);
                let root = prior[group._order@.0];
                assert(source_clocked_layout(&root.circuit, call.template.circuit_model().netlist_model(), root.order, root.index));
                let references = call.group.references;
                assert(self.resolved_expression_calls_match(plan, table, scope.limit, group.postorder, arguments, call.children@));
                assert forall|i: int| 0 <= i < call.children@.len() implies
                    references.start < (#[trigger] call.children@[i]).child.reference < references.end by {
                    assert(group.postorder.is_some());
                    let child = group.postorder->Some_0@[i];
                    assert(self.resolved_expression_call_matches(plan, table, scope.limit, arguments, child, call.children@[i]));
                    self.expansion_child_template_evidence(*plan, caller, prepared, index, i);
                };
                self.expression_source_models_match(plan, table, scope.limit, references, group.postorder, arguments, call.children@, prior);
            },
            SourceStepTarget::Nor(index) => {
                reveal(UseAliases::expanded_body_nor_bindings);
                let binding = roots[index];
                let prepared_root = binding.selected.prepared;
                let children = binding.selected.children@;
                let references = *binding.references;
                assert(self.nor_binding_context(plan, table, scope.limit, arguments, binding));
                assert(binding.candidate < prepared.nor_roots@.len());
                let candidate = binding.candidate as int;
                assert(*prepared_root == prepared.nor_roots@[candidate]);
                self.prepared_nor_reference_evidence(*plan, caller, prepared, candidate);
                let parsed = self.targets.project_model().circuits_model()[scope.file as int];
                assert(references == parsed.definitions@[prepared_root.definition as int].references);
                assert forall|i: int| 0 <= i < children.len() implies
                    references.start < (#[trigger] children[i]).child.reference < references.end by {
                    let child = prepared_root.postorder@[i];
                    assert(self.resolved_expression_call_matches(plan, table, scope.limit, arguments, child, children[i]));
                    assert(references.start < child.reference < references.end);
                    assert(*children[i].child == child);
                };
                self.expression_source_models_match(plan, table, scope.limit, references, Some(prepared_root.postorder), arguments, children, prior);
            },
            SourceStepTarget::Local => {},
        }
    }
}

} // verus!
