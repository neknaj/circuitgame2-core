//! 呼び出し先の依存順と本体の定義順から、参照評価の出力が一意に決まることを示す。

use super::*;

verus! {

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 同じソース関数の同じ入力から得られる出力は、呼び出しを含めて一意に決まる。
    pub proof fn project_source_func_evaluations_agree(
        &self, plan: &FunctionExpansionOrder, limit: u64, rank: int,
        inputs: Seq<Seq<bool>>, left: Seq<Seq<bool>>, right: Seq<Seq<bool>>,
    )
        requires
            self.project_source_func_evaluation(plan, limit, rank, inputs, left),
            self.project_source_func_evaluation(plan, limit, rank, inputs, right),
        ensures left == right,
    {
        let a = SourceInvocation { rank, inputs, outputs: left };
        let b = SourceInvocation { rank, inputs, outputs: right };
        let left_derivation = choose|d: ISet<SourceInvocation>|
            #[trigger] self.source_evaluation_derivation(plan, limit, d) && d.contains(a);
        let right_derivation = choose|d: ISet<SourceInvocation>|
            #[trigger] self.source_evaluation_derivation(plan, limit, d) && d.contains(b);
        reveal(UseAliases::source_evaluation_derivation);
        self.source_invocation_outputs_agree(plan, limit, left_derivation, right_derivation, a, b);
    }

    proof fn source_invocation_outputs_agree(
        &self, plan: &FunctionExpansionOrder, limit: u64,
        left_derivation: ISet<SourceInvocation>, right_derivation: ISet<SourceInvocation>,
        a: SourceInvocation, b: SourceInvocation,
    )
        requires
            self.can_resolve(), self.function_expansion_evidence(Ok(*plan)),
            self.source_evaluation_derivation(plan, limit, left_derivation),
            self.source_evaluation_derivation(plan, limit, right_derivation),
            left_derivation.contains(a), right_derivation.contains(b),
            a.rank == b.rank, a.inputs == b.inputs,
        ensures a.outputs == b.outputs,
        decreases a.rank,
    {
        reveal(UseAliases::source_evaluation_derivation);
        reveal(UseAliases::source_invocation_evaluates);
        let (file, entry) = plan.position_model(a.rank)->Some_0;
        let caller = (file, entry, limit);
        let left = choose|body: SourceFunctionEvaluation|
            #[trigger] self.source_function_evaluation_frame(plan, caller, left_derivation, a, body);
        let right = choose|body: SourceFunctionEvaluation|
            #[trigger] self.source_function_evaluation_frame(plan, caller, right_derivation, b, body);
        assert forall|x: SourceInvocation, y: SourceInvocation|
            (#[trigger] left_derivation.contains(x)) && (#[trigger] right_derivation.contains(y))
                && 0 <= x.rank == y.rank < a.rank && x.inputs == y.inputs
            implies x.outputs == y.outputs by {
                self.source_invocation_outputs_agree(plan, limit, left_derivation, right_derivation, x, y);
            };
        self.source_frames_outputs_agree(plan, caller, left_derivation, right_derivation, a, b, left, right);
    }

    proof fn source_frames_outputs_agree(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64),
        left_derivation: ISet<SourceInvocation>, right_derivation: ISet<SourceInvocation>,
        a: SourceInvocation, b: SourceInvocation, left: SourceFunctionEvaluation, right: SourceFunctionEvaluation,
    )
        requires
            self.can_resolve(), self.function_expansion_evidence(Ok(*plan)),
            self.source_evaluation_derivation(plan, caller.2, left_derivation),
            self.source_evaluation_derivation(plan, caller.2, right_derivation),
            self.source_function_evaluation_frame(plan, caller, left_derivation, a, left),
            self.source_function_evaluation_frame(plan, caller, right_derivation, b, right),
            a.rank == b.rank, a.inputs == b.inputs,
            forall|x: SourceInvocation, y: SourceInvocation|
                (#[trigger] left_derivation.contains(x)) && (#[trigger] right_derivation.contains(y))
                    && 0 <= x.rank == y.rank < a.rank && x.inputs == y.inputs ==> x.outputs == y.outputs,
        ensures a.outputs == b.outputs,
    {
        reveal(UseAliases::source_function_evaluation_frame);
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let aw = left.typed.literals.wiring->Checked_0;
        let bw = right.typed.literals.wiring->Checked_0;
        let ac = SourceFunc { file, entry, limit, source, parsed, wiring: &aw };
        let bc = SourceFunc { file, entry, limit, source, parsed, wiring: &bw };
        let al = match &left.layouts { Some(table) => Some(table), None => None };
        let bl = match &right.layouts { Some(table) => Some(table), None => None };
        self.checked_types_keep_wiring(file, entry, limit, left.typed, aw);
        self.checked_types_keep_wiring(file, entry, limit, right.typed, bw);
        self.checked_wiring_is_func(file, entry, limit, aw);
        self.checked_func_wiring_agrees(file, entry, limit, aw, bw);
        self.checked_function_signal_types_agree(file, entry, limit, left.typed, right.typed);
        self.targets.parsed_project_model();
        assert(same_source_bindings(&ac, &bc));
        let x = left.values;
        let y = right.values;
        self.source_project_prefix_agrees(plan, a.rank, left_derivation, right_derivation,
            &ac, &bc, al, bl, left.typed.types@, a.inputs, x, y, x.len());
        assert(x.take(x.len() as int) =~= x);
        assert(y.take(x.len() as int) =~= y);
        assert(x == y);
        assert(a.outputs.len() == b.outputs.len());
        assert forall|i: int| 0 <= i < a.outputs.len() implies
            (#[trigger] a.outputs[i]) == (#[trigger] b.outputs[i]) by {
            assert(source_output_at(&aw, a.inputs, x, a.outputs, i));
            assert(source_output_at(&bw, a.inputs, y, b.outputs, i));
        };
        assert(a.outputs =~= b.outputs);
    }

    proof fn source_project_prefix_agrees(
        &self, plan: &FunctionExpansionOrder, rank: int,
        left_derivation: ISet<SourceInvocation>, right_derivation: ISet<SourceInvocation>,
        ac: &SourceFunc, bc: &SourceFunc, al: Option<&StructureLayouts>, bl: Option<&StructureLayouts>,
        types: Seq<Option<SignalType>>, inputs: Seq<Seq<bool>>, a: Seq<Seq<bool>>, b: Seq<Seq<bool>>, end: nat,
    )
        requires
            self.can_resolve(), self.function_expansion_evidence(Ok(*plan)),
            same_source_bindings(ac, bc),
            ac.file < self.targets.project_model().sources_model().len(),
            ac.file < self.targets.project_model().circuits_model().len(),
            *ac.source == self.targets.project_model().sources_model()[ac.file as int],
            *ac.parsed == self.targets.project_model().circuits_model()[ac.file as int],
            parsed_circuit_matches(*ac.source, *ac.parsed),
            ac.entry < ac.parsed.syntax.entries@.len() && ac.entry < ac.parsed.entry_ranges@.len(),
            self.structure_layout_for_ports(ac.limit, al), self.structure_layout_for_ports(ac.limit, bl),
            a.len() == b.len() == ac.wiring.drivers.definitions@.len() == types.len(),
            forall|i: int| 0 <= i < a.len() ==> indexed_driver_site(ac.source, ac.parsed, ac.entry as int,
                #[trigger] ac.wiring.drivers.definitions@[i]),
            self.source_evaluation_derivation(plan, ac.limit, left_derivation),
            self.source_evaluation_derivation(plan, ac.limit, right_derivation),
            self.source_slots_evaluate(plan, rank, left_derivation, ac, al, types, inputs, a),
            self.source_slots_evaluate(plan, rank, right_derivation, bc, bl, types, inputs, b),
            forall|x: SourceInvocation, y: SourceInvocation|
                (#[trigger] left_derivation.contains(x)) && (#[trigger] right_derivation.contains(y))
                    && 0 <= x.rank == y.rank < rank && x.inputs == y.inputs ==> x.outputs == y.outputs,
            end <= a.len(),
        ensures a.take(end as int) == b.take(end as int),
        decreases end,
    {
        if end == 0 {
            assert(a.take(0) =~= b.take(0));
        } else {
            let i = (end - 1) as int;
            self.source_project_prefix_agrees(plan, rank, left_derivation, right_derivation,
                ac, bc, al, bl, types, inputs, a, b, i as nat);
            let caller = (ac.file, ac.entry, ac.limit);
            assert(self.source_slot_evaluates(plan, rank, left_derivation, ac, al, types, inputs, a, i)
                && self.source_slot_evaluates(plan, rank, right_derivation, bc, bl, types, inputs, b, i)) by {
                reveal(UseAliases::source_slots_evaluate);
            };
            reveal(UseAliases::source_slot_evaluates);
            let a_ordinary = self.source_definition_value(ac, al, types, inputs, a, i);
            let b_ordinary = self.source_definition_value(bc, bl, types, inputs, b, i);
            let a_nor = self.source_nested_nor_slot_evaluates(plan, rank, left_derivation, ac, types, inputs, a, i);
            let b_nor = self.source_nested_nor_slot_evaluates(plan, rank, right_derivation, bc, types, inputs, b, i);
            if a_nor && b_nor {
                self.source_nested_nor_slots_agree(plan, rank, left_derivation, right_derivation, ac, bc, types, inputs, a, b, i);
            } else if a_nor {
                self.source_nested_nor_excludes_other_slot(plan, caller, rank, left_derivation, right_derivation,
                    ac, bc, bl, types, inputs, a, b, i);
            } else if b_nor {
                self.source_nested_nor_excludes_other_slot(plan, caller, rank, right_derivation, left_derivation,
                    bc, ac, al, types, inputs, b, a, i);
            } else if a_ordinary && b_ordinary {
                reveal(UseAliases::source_definition_value);
                self.source_rhs_values_agree(ac, bc, al, bl, types, inputs, a.take(i), a[i], b[i]);
            } else if a_ordinary {
                self.source_slot_excludes_ordinary(plan, caller, rank, right_derivation, ac, bc, al, types, inputs, a, b, i);
                assert(false);
            } else if b_ordinary {
                self.source_slot_excludes_ordinary(plan, caller, rank, left_derivation, bc, ac, bl, types, inputs, b, a, i);
                assert(false);
            } else {
                assert(self.source_call_slot_evaluates(plan, caller, rank, left_derivation, ac.wiring, inputs, a, i));
                assert(self.source_call_slot_evaluates(plan, caller, rank, right_derivation, bc.wiring, inputs, b, i));
                let (x, y) = self.source_call_slots_agree_on_inputs(plan, caller, rank, i, left_derivation,
                    right_derivation, ac.wiring, bc.wiring, inputs, a, b);
                assert(x.outputs == y.outputs);
            }
            assert(a.take(end as int) =~= b.take(end as int));
        }
    }

    /// 型検査済みの根 NOR を、平坦な右辺や通常関数の呼び出しとして評価することはできない。
    #[verifier::spinoff_prover]
    proof fn source_nested_nor_excludes_other_slot(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int,
        nor_derivation: ISet<SourceInvocation>, other_derivation: ISet<SourceInvocation>,
        nor: &SourceFunc, other: &SourceFunc, layouts: Option<&StructureLayouts>,
        types: Seq<Option<SignalType>>, inputs: Seq<Seq<bool>>, a: Seq<Seq<bool>>, b: Seq<Seq<bool>>, slot: int,
    )
        requires
            same_source_bindings(nor, other),
            (nor.file, nor.entry, nor.limit) == caller,
            0 <= slot < b.len(),
            self.source_nested_nor_slot_evaluates(plan, rank, nor_derivation, nor, types, inputs, a, slot),
            self.source_definition_value(other, layouts, types, inputs, b, slot)
                || self.source_call_slot_evaluates(plan, caller, rank, other_derivation, other.wiring, inputs, b, slot),
        ensures false,
    {
        let (call, list) = self.source_nested_nor_slot_evidence(plan, rank, nor_derivation, nor, types, inputs, a, slot);
        let driver = nor.wiring.drivers.definitions@[slot];
        assert(same_definition_driver(driver, other.wiring.drivers.definitions@[slot]));
        if self.source_definition_value(other, layouts, types, inputs, b, slot) {
            self.source_rhs_excludes_list_argument(other, layouts, types, inputs, b, slot, list);
        } else {
            reveal(UseAliases::source_call_slot_evaluates);
            let site = choose|site: SourceCallEvaluation|
                #[trigger] self.source_call_matches_slot(plan, caller, rank, other.wiring, inputs, b, slot, site, other_derivation)
                && other_derivation.contains(SourceInvocation { rank: site.rank, inputs: site.arguments, outputs: site.results });
            self.source_project_call_values_evidence(plan, caller, rank, other.wiring, inputs, b, slot, site, other_derivation);
            let target = plan.position_model(site.rank)->Some_0;
            self.source_function_call_site_evidence(caller, other.wiring, slot, site.definition, site.signature, site.outputs, target);
            let base = nor.parsed.entry_ranges@[nor.entry as int].definitions.start;
            self.resolved_nor_call_agrees(nor.file, nor.entry, (driver.definition - base) as usize,
                0, nor.limit, call, Some(site.signature));
        }
    }

    proof fn source_slot_excludes_ordinary(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int,
        derivation: ISet<SourceInvocation>, ordinary: &SourceFunc, call: &SourceFunc,
        layouts: Option<&StructureLayouts>, types: Seq<Option<SignalType>>,
        inputs: Seq<Seq<bool>>, a: Seq<Seq<bool>>, b: Seq<Seq<bool>>, slot: int,
    )
        requires
            self.can_resolve(), same_source_bindings(ordinary, call),
            (ordinary.file, ordinary.entry, ordinary.limit) == caller,
            *ordinary.source == self.targets.project_model().sources_model()[caller.0 as int],
            *ordinary.parsed == self.targets.project_model().circuits_model()[caller.0 as int],
            0 <= slot < a.len(),
            self.source_definition_value(ordinary, layouts, types, inputs, a, slot),
            self.source_call_slot_evaluates(plan, caller, rank, derivation, call.wiring, inputs, b, slot),
        ensures false,
    {
        reveal(UseAliases::source_call_slot_evaluates);
        let site = choose|site: SourceCallEvaluation|
            #[trigger] self.source_call_matches_slot(plan, caller, rank, call.wiring, inputs, b, slot, site, derivation)
            && derivation.contains(SourceInvocation { rank: site.rank, inputs: site.arguments, outputs: site.results });
        let target = plan.position_model(site.rank)->Some_0;
        self.source_project_call_values_evidence(plan, caller, rank, call.wiring, inputs, b, slot, site, derivation);
        self.source_rhs_excludes_function_call(ordinary, call, layouts, types, inputs, a, slot,
            site.definition, site.signature, site.outputs, target);
    }
}

} // verus!
