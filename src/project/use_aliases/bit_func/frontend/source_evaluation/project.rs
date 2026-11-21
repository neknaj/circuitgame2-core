//! プロジェクト内の呼び出しを含む関数の参照評価と意味保存。

mod determinism;
mod expressions;

use super::*;
use self::expressions::{NestedSourceArguments, source_expression_scope};
use crate::project::FunctionExpansionOrder;
use crate::netlist::nor_evaluation;
use crate::project::use_aliases::bit_func::lowering::MixedCallEvaluation;
use crate::project::use_aliases::bit_func::templates::{FunctionTemplate, FunctionTemplates};
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
    nested: Option<NestedSourceArguments<'p, 'a>>,
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
            &&& forall|i: int| #![trigger values[i]] 0 <= i < values.len() ==>
                self.source_value_has_type(layout_ref, typed.types@, values, i)
            &&& self.source_slots_evaluate(plan, rank, derivation, &context, layout_ref, typed.types@, inputs, values)
            &&& source_outputs_match(&wiring, inputs, values, outputs)
        }
    }

    #[verifier::opaque]
    spec fn source_slots_evaluate(
        &self, plan: &FunctionExpansionOrder, rank: int, derivation: ISet<SourceInvocation>,
        context: &SourceFunc, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>,
    ) -> bool {
        forall|i: int| 0 <= i < values.len() ==>
            #[trigger] self.source_slot_evaluates(plan, rank, derivation, context, layouts, types, inputs, values, i)
    }

    #[verifier::opaque]
    spec fn source_slot_evaluates(
        &self, plan: &FunctionExpansionOrder, rank: int, derivation: ISet<SourceInvocation>,
        context: &SourceFunc, layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, i: int,
    ) -> bool {
        let caller = (context.file, context.entry, context.limit);
        self.source_definition_value(context, layouts, types, inputs, values, i)
            || self.source_call_slot_evaluates(plan, caller, rank, derivation, context.wiring, inputs, values, i)
            || self.source_nested_nor_slot_evaluates(plan, rank, derivation, context, types, inputs, values, i)
    }

    spec fn source_call_matches_slot(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int, wiring: &FuncWiring,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, slot: int, site: SourceCallEvaluation,
        derivation: ISet<SourceInvocation>,
    ) -> bool {
        &&& site.outputs.start <= slot < site.outputs.end
        &&& 0 <= site.rank < rank
        &&& plan.position_model(site.rank).is_some()
        &&& match &site.nested {
            None => self.source_function_call_values(caller, wiring, site.definition, site.signature, site.outputs,
                plan.position_model(site.rank)->Some_0, inputs, values, site.widths, site.arguments, site.results),
            Some(nested) => {
                let project = self.targets.project_model();
                let context = SourceFunc { file: caller.0, entry: caller.1, limit: caller.2,
                    source: &project.sources_model()[caller.0 as int], parsed: &project.circuits_model()[caller.0 as int], wiring };
                let scope = source_expression_scope(&context, plan, rank, derivation, site, nested, inputs, values);
                &&& self.source_function_call_site(caller, wiring, site.definition, site.signature, site.outputs,
                    plan.position_model(site.rank)->Some_0)
                &&& site.outputs.end <= values.len()
                &&& site.results == values.subrange(site.outputs.start as int, site.outputs.end as int)
                &&& self.source_nested_arguments_match(&scope, site.signature, site.widths, site.arguments, nested.children)
            },
        }
    }

    /// 左辺との対応と入力幅は、どちらの引数評価でも同じ形で取り出せる。
    proof fn source_project_call_values_evidence(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int, wiring: &FuncWiring,
        inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, slot: int, site: SourceCallEvaluation,
        derivation: ISet<SourceInvocation>,
    )
        requires self.source_call_matches_slot(plan, caller, rank, wiring, inputs, values, slot, site, derivation),
        ensures
            self.source_function_call_site(caller, wiring, site.definition, site.signature, site.outputs,
                plan.position_model(site.rank)->Some_0),
            self.func_wiring_evidence(caller.0, caller.1, caller.2, Ok(FuncWiringResult::Checked(*wiring))),
            site.outputs.start <= slot < site.outputs.end <= values.len(),
            site.results == values.subrange(site.outputs.start as int, site.outputs.end as int),
            site.arguments.len() == site.widths.len(),
            forall|i: int| 0 <= i < site.arguments.len() ==> (#[trigger] site.arguments[i]).len() == site.widths[i],
    {
        match &site.nested {
            None => self.source_function_call_values_evidence(caller, wiring, site.definition, site.signature, site.outputs,
                plan.position_model(site.rank)->Some_0, inputs, values, site.widths, site.arguments, site.results),
            Some(nested) => {
                let project = self.targets.project_model();
                let context = SourceFunc { file: caller.0, entry: caller.1, limit: caller.2,
                    source: &project.sources_model()[caller.0 as int], parsed: &project.circuits_model()[caller.0 as int], wiring };
                let scope = source_expression_scope(&context, plan, rank, derivation, site, nested, inputs, values);
                self.source_nested_argument_lengths(&scope, site.signature, site.widths, site.arguments, nested.children);
            },
        }
        self.source_function_call_site_evidence(caller, wiring, slot, site.definition, site.signature, site.outputs,
            plan.position_model(site.rank)->Some_0);
    }

    #[verifier::opaque]
    spec fn source_call_slot_evaluates(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int, derivation: ISet<SourceInvocation>,
        wiring: &FuncWiring, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, slot: int,
    ) -> bool {
        exists|site: SourceCallEvaluation|
            #[trigger] self.source_call_matches_slot(plan, caller, rank, wiring, inputs, values, slot, site, derivation)
            && derivation.contains(SourceInvocation { rank: site.rank, inputs: site.arguments, outputs: site.results })
    }

    proof fn source_call_slot_intro(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int, derivation: ISet<SourceInvocation>,
        wiring: &FuncWiring, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>, slot: int, site: SourceCallEvaluation,
    )
        requires
            self.source_call_matches_slot(plan, caller, rank, wiring, inputs, values, slot, site, derivation),
            derivation.contains(SourceInvocation { rank: site.rank, inputs: site.arguments, outputs: site.results }),
        ensures self.source_call_slot_evaluates(plan, caller, rank, derivation, wiring, inputs, values, slot),
    {
        reveal(UseAliases::source_call_slot_evaluates);
    }

    /// 二つの評価が使う構造体配置表が異なっていても、同じ宣言の入力幅は等しい。
    proof fn source_invocation_input_widths_agree(
        &self, plan: &FunctionExpansionOrder, limit: u64, left_derivation: ISet<SourceInvocation>,
        right_derivation: ISet<SourceInvocation>, left: SourceInvocation, right: SourceInvocation,
    )
        requires
            self.can_resolve(),
            left.rank == right.rank,
            self.source_invocation_evaluates(plan, limit, left_derivation, left),
            self.source_invocation_evaluates(plan, limit, right_derivation, right),
        ensures
            left.inputs.len() == right.inputs.len(),
            forall|i: int| 0 <= i < left.inputs.len() ==> (#[trigger] left.inputs[i]).len() == right.inputs[i].len(),
    {
        reveal(UseAliases::source_invocation_evaluates);
        let (file, entry) = plan.position_model(left.rank)->Some_0;
        let caller = (file, entry, limit);
        let a = choose|body: SourceFunctionEvaluation|
            #[trigger] self.source_function_evaluation_frame(plan, caller, left_derivation, left, body);
        let b = choose|body: SourceFunctionEvaluation|
            #[trigger] self.source_function_evaluation_frame(plan, caller, right_derivation, right, body);
        reveal(UseAliases::source_function_evaluation_frame);
        let al = match &a.layouts { Some(table) => Some(table), None => None };
        let bl = match &b.layouts { Some(table) => Some(table), None => None };
        let aw = a.typed.literals.wiring->Checked_0;
        let bw = b.typed.literals.wiring->Checked_0;
        self.checked_types_keep_wiring(file, entry, limit, a.typed, aw);
        self.checked_types_keep_wiring(file, entry, limit, b.typed, bw);
        self.checked_func_wiring_agrees(file, entry, limit, aw, bw);
        let ports = aw.drivers.signature.inputs@;
        assert forall|i: int| 0 <= i < left.inputs.len() implies
            (#[trigger] left.inputs[i]).len() == right.inputs[i].len() by {
            let ty = ports[i].ty;
            let x = left.inputs[i].len();
            let y = right.inputs[i].len();
            if ty is Struct {
                self.layout_port_widths_agree_across_tables(limit, al->Some_0, bl->Some_0, ty, x as int, y as int);
            }
        };
    }

    /// 同じ左辺の二つの評価から、同じ呼び出し先に同じ入力を渡すことを示す。
    proof fn source_call_slots_agree_on_inputs(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int, slot: int,
        left_derivation: ISet<SourceInvocation>, right_derivation: ISet<SourceInvocation>,
        left_wiring: &FuncWiring, right_wiring: &FuncWiring,
        inputs: Seq<Seq<bool>>, left: Seq<Seq<bool>>, right: Seq<Seq<bool>>,
    ) -> (children: (SourceInvocation, SourceInvocation))
        requires
            self.can_resolve(),
            self.function_expansion_evidence(Ok(*plan)),
            self.source_evaluation_derivation(plan, caller.2, left_derivation),
            self.source_evaluation_derivation(plan, caller.2, right_derivation),
            self.source_call_slot_evaluates(plan, caller, rank, left_derivation, left_wiring, inputs, left, slot),
            self.source_call_slot_evaluates(plan, caller, rank, right_derivation, right_wiring, inputs, right, slot),
            left.take(slot) == right.take(slot),
            forall|x: SourceInvocation, y: SourceInvocation|
                (#[trigger] left_derivation.contains(x)) && (#[trigger] right_derivation.contains(y))
                    && 0 <= x.rank == y.rank < rank && x.inputs == y.inputs ==> x.outputs == y.outputs,
        ensures
            left_derivation.contains(children.0),
            right_derivation.contains(children.1),
            0 <= children.0.rank == children.1.rank < rank,
            children.0.inputs == children.1.inputs,
            children.0.outputs == children.1.outputs ==> left[slot] == right[slot],
    {
        reveal(UseAliases::source_call_slot_evaluates);
        let a = choose|site: SourceCallEvaluation|
            #[trigger] self.source_call_matches_slot(plan, caller, rank, left_wiring, inputs, left, slot, site, left_derivation)
            && left_derivation.contains(SourceInvocation { rank: site.rank, inputs: site.arguments, outputs: site.results });
        let b = choose|site: SourceCallEvaluation|
            #[trigger] self.source_call_matches_slot(plan, caller, rank, right_wiring, inputs, right, slot, site, right_derivation)
            && right_derivation.contains(SourceInvocation { rank: site.rank, inputs: site.arguments, outputs: site.results });
        let (at, bt) = (plan.position_model(a.rank)->Some_0, plan.position_model(b.rank)->Some_0);
        self.source_project_call_values_evidence(plan, caller, rank, left_wiring, inputs, left, slot, a, left_derivation);
        self.source_project_call_values_evidence(plan, caller, rank, right_wiring, inputs, right, slot, b, right_derivation);
        self.source_call_sites_agree(caller, left_wiring, right_wiring, slot,
            (a.definition, a.signature, a.outputs, at), (b.definition, b.signature, b.outputs, bt));
        self.template_rank_from_position(*plan, at, a.rank, b.rank);
        let ca = SourceInvocation { rank: a.rank, inputs: a.arguments, outputs: a.results };
        let cb = SourceInvocation { rank: b.rank, inputs: b.arguments, outputs: b.results };
        reveal(UseAliases::source_evaluation_derivation);
        self.source_invocation_input_widths_agree(plan, caller.2, left_derivation, right_derivation, ca, cb);
        assert(a.widths.len() == b.widths.len());
        assert forall|i: int| 0 <= i < a.widths.len() implies #[trigger] a.widths[i] == b.widths[i] by {
            assert(a.arguments[i].len() == a.widths[i]);
            assert(b.arguments[i].len() == b.widths[i]);
            assert(ca.inputs[i].len() == cb.inputs[i].len());
        };
        assert(a.widths =~= b.widths);
        assert(left.take(a.outputs.start as int) =~= right.take(b.outputs.start as int));
        self.source_project_call_arguments_agree(plan, caller, rank, slot, left_derivation, right_derivation,
            left_wiring, right_wiring, inputs, left, right, a, b);
        if ca.outputs == cb.outputs {
            let i = slot - a.outputs.start;
            assert(a.results[i] == left[slot] && b.results[i] == right[slot]);
        }
        (ca, cb)
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

    /// 先行表から選んで評価した回路は、完成した表でも同じ順位の関数の評価を表す。
    proof fn prior_template_invocation(
        plan: &FunctionExpansionOrder, prior: &FunctionTemplates, table: &FunctionTemplates,
        rank: int, template: &FunctionTemplate, input: Seq<bool>, output: Seq<bool>,
    ) -> (invocation: SourceInvocation)
        requires
            0 <= rank < prior.next_rank(),
            rank < plan.order_model().len(),
            prior.slots_model().len() == table.slots_model().len(),
            plan.order_model()[rank] < prior.slots_model().len(),
            prior.slots_model()[plan.order_model()[rank] as int] == Some(*template),
            forall|i: int| 0 <= i < prior.next_rank() ==> {
                let vertex = #[trigger] plan.order_model()[i];
                prior.slots_model()[vertex as int] == table.slots_model()[vertex as int]
            },
            nor_evaluation(template.circuit_model().netlist_model(), input, output),
        ensures
            invocation.rank == rank,
            invocation.inputs == port_values(template.circuit_model().input_layout_model(), input),
            invocation.outputs == port_values(template.circuit_model().output_layout_model(), output),
            Self::template_invocation_matches(plan, table, invocation, input, output),
            Self::template_evaluations(plan, table).contains(invocation),
    {
        let vertex = plan.order_model()[rank];
        assert(prior.slots_model()[vertex as int] == table.slots_model()[vertex as int]);
        let circuit = template.circuit_model();
        let invocation = SourceInvocation { rank, inputs: port_values(circuit.input_layout_model(), input),
            outputs: port_values(circuit.output_layout_model(), output) };
        assert(Self::template_invocation_matches(plan, table, invocation, input, output));
        invocation
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
        self.projected_ordinary_definitions_preserve_source_values(&scope, calls, selected, slots,
            prepared.projections.call_arguments.arguments@, bit_limit,
            gate_limit, circuit, input, gates);
        self.prepared_definition_width_evidence(&scope, calls, selected, slots);
        self.checked_wiring_is_func(file, entry, width_limit, *scope.wiring);

        assert forall|i: int| 0 <= i < values.len() implies
            #[trigger] self.source_slot_evaluates(plan, rank, derivation, &context, layout_ref, prepared.typed.types@,
                incoming, values, i) by {
            reveal(UseAliases::source_slot_evaluates);
            if call_covers(calls, i) {
                let index = choose|index: int| 0 <= index < calls.len()
                    && (#[trigger] calls[index]).outputs.start <= i < calls[index].outputs.end;
                let group = calls[index];
                let root = prepared.projections.calls@[index];
                let (selection, evidence) = self.expanded_body_source_call_evaluation(plan, &prior, caller, &prepared,
                    bit_limit, gate_limit, &body, index, input, gates);
                let callee = selection.template;
                let (arguments, results) = match evidence {
                    MixedCallEvaluation::Flat(arguments, results) => (arguments, results),
                    MixedCallEvaluation::Nested(call) => (call.root.input, call.root.output),
                };
                self.template_rank_from_position(*plan, (file, entry), group._order@.1, rank);
                let callee_rank = group._order@.0;
                let child = Self::prior_template_invocation(plan, &prior, table, callee_rank, callee, arguments, results);
                let site = SourceCallEvaluation { definition: root.definition, signature: group._signature@,
                    outputs: group.outputs, rank: callee_rank, widths: callee.input_widths_model(),
                    arguments: child.inputs, results: child.outputs, nested: None };
                assert(site.outputs.start <= i < site.outputs.end && 0 <= site.rank < rank);
                assert(plan.position_model(site.rank) == Some((root.target_file, root.target_entry)));
                let site = if let MixedCallEvaluation::Nested(call) = evidence {
                    self.prepared_call_matches_source_site(plan, caller, &prepared, index);
                    let nested = self.source_nested_call_from_wiring(&context, plan, rank, &prior, table, &prepared, index,
                        &selection, layouts, incoming, values, call, site);
                    SourceCallEvaluation { nested: Some(nested), ..site }
                } else { site };
                assert(self.source_call_matches_slot(plan, caller, rank, scope.wiring, incoming, values, i, site, derivation));
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
        assert(self.source_slots_evaluate(plan, rank, derivation, &context, layout_ref, prepared.typed.types@, incoming, values)) by {
            reveal(UseAliases::source_slots_evaluate);
        };
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
