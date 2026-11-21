//! プロジェクト内の呼び出しを含む関数の参照評価と意味保存。

use super::*;
use crate::project::FunctionExpansionOrder;
use crate::netlist::nor_evaluation;
use crate::project::use_aliases::bit_func::templates::FunctionTemplates;
use core::ops::Range;

verus! {

/// 一つのソース呼び出しで用いる宣言位置、引数値、出力値をまとめる。
struct SourceCallEvaluation<'p, 'a> {
    definition: usize,
    signature: TypedFuncCall<'p, 'a>,
    outputs: Range<usize>,
    rank: int,
    widths: Seq<u64>,
    arguments: Seq<Seq<bool>>,
    results: Seq<Seq<bool>>,
}

struct SourceInvocation {
    rank: int,
    inputs: Seq<Seq<bool>>,
    outputs: Seq<Seq<bool>>,
}

struct SourceFunctionEvaluation<'p, 'a> {
    typed: FuncSignalTypes<'p, 'a>,
    layouts: Option<StructureLayouts<'p, 'a>>,
    values: Seq<Seq<bool>>,
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 依存順の順位で関数を指定し、通常の右辺と関数呼び出しをソースの規則で評価する。
    pub closed spec fn project_source_func_evaluation(
        &self, plan: &FunctionExpansionOrder, limit: u64, rank: int, inputs: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
    ) -> bool {
        &&& self.can_resolve()
        &&& self.function_expansion_evidence(Ok(*plan))
        &&& exists|derivation: ISet<SourceInvocation>|
            #[trigger] self.source_evaluation_derivation(plan, limit, derivation)
            && derivation.contains(SourceInvocation { rank, inputs, outputs })
    }

    /// 呼び出し先の評価を同じ集合に含め、各参照先の順位が呼び出し元より小さいことを保つ。
    #[verifier::opaque]
    spec fn source_evaluation_derivation(
        &self, plan: &FunctionExpansionOrder, limit: u64, derivation: ISet<SourceInvocation>,
    ) -> bool {
        forall|invocation: SourceInvocation| #[trigger] derivation.contains(invocation) ==>
            self.source_invocation_evaluates(plan, limit, derivation, invocation)
    }

    #[verifier::opaque]
    spec fn source_invocation_evaluates(
        &self, plan: &FunctionExpansionOrder, limit: u64, derivation: ISet<SourceInvocation>, invocation: SourceInvocation,
    ) -> bool {
        let rank = invocation.rank;
        &&& 0 <= rank < plan.order_model().len()
        &&& plan.position_model(rank) matches Some((file, entry))
        &&& exists|evaluation: SourceFunctionEvaluation|
            #[trigger] self.source_function_evaluation_frame(plan, (file, entry, limit), derivation, invocation, evaluation)
    }

    #[verifier::opaque]
    spec fn source_function_evaluation_frame(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), derivation: ISet<SourceInvocation>,
        invocation: SourceInvocation, evaluation: SourceFunctionEvaluation,
    ) -> bool
    {
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let SourceInvocation { rank, inputs, outputs } = invocation;
        let typed = evaluation.typed;
        let values = evaluation.values;
        let layout_ref = match &evaluation.layouts { Some(table) => Some(table), None => None };
        &&& 0 <= rank
        &&& file < project.sources_model().len() && file < project.circuits_model().len()
        &&& self.func_signal_types_evidence(file, entry, limit, Ok(evaluation.typed))
        &&& self.structure_layout_for_ports(limit, layout_ref)
        &&& typed.literals.wiring matches FuncWiringResult::Checked(wiring)
        &&& {
            let parsed = &project.circuits_model()[file as int];
            let context = SourceFunc { file, entry, limit, source: &project.sources_model()[file as int],
                parsed, wiring: &wiring };
            &&& entry < parsed.syntax.entries@.len() && parsed.syntax.entries@[entry as int].head is Func
            &&& self.source_inputs_match(&wiring, layout_ref, inputs)
            &&& values.len() == wiring.drivers.definitions@.len() == typed.types@.len()
            &&& forall|i: int| #![trigger values[i]] 0 <= i < values.len() ==> {
                &&& self.source_value_has_type(layout_ref, typed.types@, values, i)
                &&& (self.source_definition_value(&context, layout_ref, typed.types@, inputs, values, i)
                    || self.source_call_slot_evaluates(plan, caller, rank, derivation, &wiring, inputs, values, i))
            }
            &&& source_outputs_match(&wiring, inputs, values, outputs)
        }
    }

    spec fn source_call_matches_slot(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int, wiring: &FuncWiring,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, slot: int, site: SourceCallEvaluation,
    ) -> bool {
        &&& site.outputs.start <= slot < site.outputs.end
        &&& 0 <= site.rank < rank
        &&& plan.position_model(site.rank).is_some()
        &&& self.source_function_call_values(caller, wiring, site.definition, site.signature, site.outputs,
            plan.position_model(site.rank)->Some_0, inputs, values, site.widths, site.arguments, site.results)
    }

    #[verifier::opaque]
    spec fn source_call_slot_evaluates(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int, derivation: ISet<SourceInvocation>,
        wiring: &FuncWiring, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, slot: int,
    ) -> bool {
        exists|site: SourceCallEvaluation|
            #[trigger] self.source_call_matches_slot(plan, caller, rank, wiring, inputs, values, slot, site)
            && derivation.contains(SourceInvocation { rank: site.rank, inputs: site.arguments, outputs: site.results })
    }

    proof fn source_call_slot_intro(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int, derivation: ISet<SourceInvocation>,
        wiring: &FuncWiring, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, slot: int, site: SourceCallEvaluation,
    )
        requires
            self.source_call_matches_slot(plan, caller, rank, wiring, inputs, values, slot, site),
            derivation.contains(SourceInvocation { rank: site.rank, inputs: site.arguments, outputs: site.results }),
        ensures self.source_call_slot_evaluates(plan, caller, rank, derivation, wiring, inputs, values, slot),
    {
        reveal(UseAliases::source_call_slot_evaluates);
    }

    spec fn template_invocation_matches(
        plan: &FunctionExpansionOrder, table: &FunctionTemplates, invocation: SourceInvocation,
        input: Seq<bool>, output: Seq<bool>,
    ) -> bool {
        let rank = invocation.rank;
        &&& 0 <= rank < plan.order_model().len()
        &&& plan.order_model()[rank] < table.slots_model().len()
        &&& table.slots_model()[plan.order_model()[rank] as int] matches Some(template)
        &&& {
            let circuit = template.circuit_model();
            &&& nor_evaluation(circuit.netlist_model(), input, output)
            &&& invocation.inputs == port_values(circuit.input_layout_model(), input)
            &&& invocation.outputs == port_values(circuit.output_layout_model(), output)
        }
    }

    spec fn template_evaluations(plan: &FunctionExpansionOrder, table: &FunctionTemplates) -> ISet<SourceInvocation> {
        ISet::new(|invocation: SourceInvocation| exists|input: Seq<bool>, output: Seq<bool>|
            #[trigger] Self::template_invocation_matches(plan, table, invocation, input, output))
    }

    proof fn completed_template_source_frame(
        &self, plan: &FunctionExpansionOrder, width_limit: u64, bit_limit: usize, gate_limit: usize,
        table: &FunctionTemplates, invocation: SourceInvocation, input: Seq<bool>, output: Seq<bool>,
    )
        requires
            self.can_resolve(),
            self.function_expansion_evidence(Ok(*plan)),
            self.ordered_template_build_result(plan, width_limit, bit_limit, gate_limit, Ok(*table)),
            Self::template_invocation_matches(plan, table, invocation, input, output),
        ensures self.source_invocation_evaluates(plan, width_limit, Self::template_evaluations(plan, table), invocation),
    {
        let rank = invocation.rank;
        let derivation = Self::template_evaluations(plan, table);
        self.completed_templates_ready(plan, width_limit, bit_limit, gate_limit, table);
        let (template, prior, prepared, body) =
            self.completed_template_expansion_at(plan, width_limit, bit_limit, gate_limit, table, rank);
        let (file, entry) = plan.position_model(rank)->Some_0;
        let caller = (file, entry, width_limit);
        let gates = self.expanded_body_output_values(plan, &prior, caller, &prepared, bit_limit, gate_limit, &body, input, output);
        let (scope, selected, slots) =
            self.expanded_body_success(plan, &prior, caller, &prepared, bit_limit, gate_limit, &body);
        let circuit = template.circuit_model();
        let incoming = port_values(circuit.input_layout_model(), input);
        let outgoing = port_values(circuit.output_layout_model(), output);
        let values = expanded_definition_values(circuit, input, gates);
        let calls = prepared.calls@;
        let context = SourceFunc { file, entry, limit: width_limit, source: scope.source, parsed: scope.parsed, wiring: scope.wiring };
        let layouts = body.ports.layouts;
        let layout_ref = match &layouts { Some(table) => Some(table), None => None };
        assert(scope.layouts == layout_ref);
        assert forall|g: int| 0 <= g < selected.len() implies *(#[trigger] selected[g]).group == calls[g] by {
            assert(self.resolved_template_call_matches(plan, caller, &prepared, g, selected[g]));
        };
        self.projected_ordinary_definitions_preserve_source_values(&scope, calls, selected, slots, bit_limit,
            gate_limit, circuit, input, gates);
        self.prepared_definition_width_evidence(&scope, calls, selected, slots);
        self.checked_wiring_is_func(file, entry, width_limit, *scope.wiring);

        assert forall|i: int| #![trigger values[i]] 0 <= i < values.len() implies {
            &&& self.source_value_has_type(layout_ref, prepared.typed.types@, values, i)
            &&& (self.source_definition_value(&context, layout_ref, prepared.typed.types@, incoming, values, i)
                || self.source_call_slot_evaluates(plan, caller, rank, derivation, scope.wiring, incoming, values, i))
        } by {
            if call_covers(calls, i) {
                let index = choose|index: int| 0 <= index < calls.len()
                    && (#[trigger] calls[index]).outputs.start <= i < calls[index].outputs.end;
                let group = calls[index];
                let root = prepared.projections.calls@[index];
                let (callee, arguments, results) = self.expanded_body_source_call_values(plan, &prior, caller, &prepared,
                    bit_limit, gate_limit, &body, index, input, gates);
                self.template_rank_from_position(*plan, (file, entry), group._order@.1, rank);
                let callee_rank = group._order@.0;
                let callee_circuit = callee.circuit_model();
                assert(plan.order_model()[callee_rank] < table.slots_model().len());
                assert(prior.slots_model()[plan.order_model()[callee_rank] as int]
                    == table.slots_model()[plan.order_model()[callee_rank] as int]);
                assert(table.slots_model()[group.vertex as int] == Some(callee));
                let site = SourceCallEvaluation { definition: root.definition, signature: group._signature@,
                    outputs: group.outputs, rank: callee_rank, widths: callee.input_widths_model(),
                    arguments: port_values(callee_circuit.input_layout_model(), arguments),
                    results: port_values(callee_circuit.output_layout_model(), results) };
                assert(site.outputs.start <= i < site.outputs.end && 0 <= site.rank < rank);
                assert(plan.position_model(site.rank) == Some((root.target_file, root.target_entry)));
                assert(self.source_function_call_values(caller, scope.wiring, site.definition, site.signature, site.outputs,
                    plan.position_model(site.rank)->Some_0, incoming, values, site.widths, site.arguments, site.results));
                let child = SourceInvocation { rank: site.rank, inputs: site.arguments, outputs: site.results };
                assert(Self::template_invocation_matches(plan, table, child, arguments, results));
                assert(derivation.contains(child));
                self.source_call_slot_intro(plan, caller, rank, derivation, scope.wiring, incoming, values, i, site);
            } else {
                assert(self.source_definition_value(&context, layout_ref, prepared.typed.types@, incoming, values, i));
            }
        };
        let evaluation = SourceFunctionEvaluation { typed: prepared.typed, layouts, values };
        let project = self.targets.project_model();
        assert(scope.source == &project.sources_model()[file as int]);
        assert(scope.parsed == &project.circuits_model()[file as int]);
        assert(*scope.wiring == evaluation.typed.literals.wiring->Checked_0);
        assert(evaluation.typed.literals.wiring is Checked);
        assert(entry < scope.parsed.syntax.entries@.len() && scope.parsed.syntax.entries@[entry as int].head is Func);
        assert(self.func_signal_types_evidence(file, entry, width_limit, Ok(evaluation.typed)));
        assert(self.structure_layout_for_ports(width_limit, layout_ref));
        assert(self.source_inputs_match(scope.wiring, layout_ref, incoming));
        assert(source_outputs_match(scope.wiring, incoming, values, outgoing));
        assert(values.len() == scope.wiring.drivers.definitions@.len() == prepared.typed.types@.len());
        reveal(UseAliases::source_function_evaluation_frame);
        assert(self.source_function_evaluation_frame(plan, caller, derivation, invocation, evaluation));
        reveal(UseAliases::source_invocation_evaluates);
    }

    /// 完成表の関数を評価すると、ソースの参照評価が同じ出力を与えることを示す。
    pub(in crate::project::use_aliases::bit_func) proof fn completed_template_preserves_source_evaluation(
        &self, plan: &FunctionExpansionOrder, width_limit: u64, bit_limit: usize, gate_limit: usize,
        table: &FunctionTemplates, rank: int, input: Seq<bool>, output: Seq<bool>,
    )
        requires
            self.can_resolve(),
            self.function_expansion_evidence(Ok(*plan)),
            self.ordered_template_build_result(plan, width_limit, bit_limit, gate_limit, Ok(*table)),
            0 <= rank < plan.order_model().len(),
            plan.order_model()[rank] < table.slots_model().len(),
            table.slots_model()[plan.order_model()[rank] as int] matches Some(template)
                && nor_evaluation(template.circuit_model().netlist_model(), input, output),
        ensures ({
            let template = table.slots_model()[plan.order_model()[rank] as int]->Some_0;
            let circuit = template.circuit_model();
            self.project_source_func_evaluation(plan, width_limit, rank, port_values(circuit.input_layout_model(), input),
                port_values(circuit.output_layout_model(), output))
        }),
    {
        let template = table.slots_model()[plan.order_model()[rank] as int]->Some_0;
        let circuit = template.circuit_model();
        let invocation = SourceInvocation { rank, inputs: port_values(circuit.input_layout_model(), input),
            outputs: port_values(circuit.output_layout_model(), output) };
        let derivation = Self::template_evaluations(plan, table);
        assert(Self::template_invocation_matches(plan, table, invocation, input, output));
        assert(derivation.contains(invocation));
        assert(self.source_evaluation_derivation(plan, width_limit, derivation)) by {
            reveal(UseAliases::source_evaluation_derivation);
            assert forall|call: SourceInvocation| #[trigger] derivation.contains(call) implies
                self.source_invocation_evaluates(plan, width_limit, derivation, call) by {
                let (flat_input, flat_output) = choose|flat_input: Seq<bool>, flat_output: Seq<bool>|
                    #[trigger] Self::template_invocation_matches(plan, table, call, flat_input, flat_output);
                self.completed_template_source_frame(plan, width_limit, bit_limit, gate_limit,
                    table, call, flat_input, flat_output);
            };
        };
    }
}

} // verus!
