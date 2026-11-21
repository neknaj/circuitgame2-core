//! 展開済みの関数を、展開計画で割り当てた頂点番号で引く。

use super::super::{FunctionExpansionOrder, StructureLayouts, TypedRoutineSignature, UseAliases};
use super::{CheckedBitFunc, LoweredBitFunc};
use super::expansion::{CheckedExpansionCall, PreparedExpansionBody};
#[cfg(verus_only)]
use super::{lowered_bit_func_result, lowering::standalone_template_layouts};
#[cfg(verus_only)]
use crate::netlist::{nor_evaluation_ready, port_bit_layout_result};
use super::super::call_arity::ProjectedCallArgument;
use alloc::vec::Vec;
use vstd::slice::slice_subrange;
use vstd::prelude::*;

verus! {

enum TemplateOrigin<'p, 'a> {
    Standalone(CheckedBitFunc<'p, 'a>),
}

/// 呼び出し側から再利用できるネットリストと、宣言順の入出力幅。
pub(super) struct FunctionTemplate<'p, 'a> {
    pub(super) circuit: LoweredBitFunc,
    pub(super) inputs: Vec<u64>,
    pub(super) outputs: Vec<u64>,
    pub(super) _signature: Ghost<TypedRoutineSignature<'p, 'a>>,
    pub(super) _structure_layouts: Ghost<Option<StructureLayouts<'p, 'a>>>,
    pub(super) _bit_limit: Ghost<usize>,
    _origin: Ghost<TemplateOrigin<'p, 'a>>,
}

/// 一つの呼び出しと、その実引数および変換済みの呼び出し先。
pub(super) struct ResolvedTemplateCall<'s, 'p, 'a> {
    pub(super) group: &'s CheckedExpansionCall<'p, 'a>,
    pub(super) arguments: &'s [ProjectedCallArgument],
    pub(super) template: &'s FunctionTemplate<'p, 'a>,
}

/// 展開順の先頭から格納する。実際の配列の添字には頂点番号を使う。
pub(super) struct FunctionTemplates<'p, 'a> {
    slots: Vec<Option<FunctionTemplate<'p, 'a>>>,
    next: usize,
}

impl<'p, 'a> FunctionTemplate<'p, 'a> {
    pub(super) closed spec fn signature_model(&self) -> TypedRoutineSignature<'p, 'a> { self._signature@ }
    pub(super) closed spec fn input_widths_model(&self) -> Seq<u64> { self.inputs@ }

    pub(super) closed spec fn output_widths_model(&self) -> Seq<u64> { self.outputs@ }

    pub(super) closed spec fn structure_layouts_model(&self) -> Option<StructureLayouts<'p, 'a>> {
        self._structure_layouts@
    }

    pub(super) closed spec fn circuit_model(&self) -> &LoweredBitFunc { &self.circuit }
    pub(super) closed spec fn bit_limit_model(&self) -> usize { self._bit_limit@ }

    /// 展開時に複製する配線と、入出力のビット配置を借りる。
    pub(super) fn circuit(&self) -> (circuit: &LoweredBitFunc)
        ensures circuit == self.circuit_model(),
    {
        &self.circuit
    }

    /// 変換した関数の出力幅を宣言順に借りる。
    pub(super) fn output_widths(&self) -> (widths: &[u64])
        ensures widths@ == self.output_widths_model(),
    {
        self.outputs.as_slice()
    }
}

impl<'p, 'a> FunctionTemplates<'p, 'a> {
    /// 次に変換する関数の展開順での位置を返す。
    pub(super) fn next_index(&self) -> (rank: usize)
        ensures rank == self.next_rank(),
    {
        self.next
    }

    pub(super) closed spec fn next_rank(&self) -> usize { self.next }

    pub(super) closed spec fn slots_model(&self) -> Seq<Option<FunctionTemplate<'p, 'a>>> { self.slots@ }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) closed spec fn function_template_matches(
        &self, position: (usize, usize), width_limit: u64, template: &FunctionTemplate,
    ) -> bool {
        &&& self.typed_signature_evidence(position.0, position.1, width_limit, Ok(Some(template._signature@)))
        &&& self.template_port_widths_match(template._signature@, width_limit, template.inputs@, template.outputs@,
            template._structure_layouts@)
        &&& port_bit_layout_result(template.inputs@, template._bit_limit@, Ok(*template.circuit.input_layout_model()))
        &&& port_bit_layout_result(template.outputs@, template._bit_limit@, Ok(*template.circuit.output_layout_model()))
        &&& nor_evaluation_ready(template.circuit.netlist_model(), template.circuit.input_layout_model().total_bits_model() as nat)
        &&& template.circuit.netlist_model().outputs@.len() == template.circuit.output_layout_model().total_bits_model()
        &&& match template._origin@ {
            TemplateOrigin::Standalone(checked) =>
                checked.signature == template._signature@
                    && checked.input_widths@ == template.inputs@ && checked.output_widths@ == template.outputs@
                    && self.checked_bit_func_matches(position.0, position.1, width_limit, &checked)
                    && lowered_bit_func_result(&checked, template._bit_limit@, Ok(template.circuit)),
        }
    }

    pub(super) proof fn template_port_evidence(
        &self, position: (usize, usize), limit: u64, template: &FunctionTemplate,
    )
        requires self.function_template_matches(position, limit, template),
        ensures self.template_port_widths_match(template.signature_model(), limit, template.input_widths_model(),
            template.output_widths_model(), template.structure_layouts_model()),
    {
        reveal(UseAliases::function_template_matches);
    }

    /// 署名の各ポート幅が、保存したネットリストの入出力配置に対応することを示す。
    pub(super) proof fn template_circuit_evidence(
        &self, position: (usize, usize), limit: u64, template: &FunctionTemplate,
    )
        requires self.function_template_matches(position, limit, template),
        ensures
            port_bit_layout_result(template.input_widths_model(), template.bit_limit_model(), Ok(*template.circuit_model().input_layout_model())),
            port_bit_layout_result(template.output_widths_model(), template.bit_limit_model(), Ok(*template.circuit_model().output_layout_model())),
            nor_evaluation_ready(template.circuit_model().netlist_model(),
                template.circuit_model().input_layout_model().total_bits_model() as nat),
            template.circuit_model().netlist_model().outputs@.len() == template.circuit_model().output_layout_model().total_bits_model(),
    {
        reveal(UseAliases::function_template_matches);
    }

    /// 検査した単独関数のネットリストを、同じ宣言の入出力幅とともに保持する。
    pub(super) fn standalone_function_template(
        &self, position: (usize, usize), width_limit: u64, checked: CheckedBitFunc<'p, 'a>,
        circuit: LoweredBitFunc, _bit_limit: usize,
    ) -> (template: FunctionTemplate<'p, 'a>)
        requires
            self.can_resolve(),
            self.checked_bit_func_matches(position.0, position.1, width_limit, &checked),
            lowered_bit_func_result(&checked, _bit_limit, Ok(circuit)),
        ensures self.function_template_matches(position, width_limit, &template),
    {
        let ghost table = self.standalone_template_ports(position.0, position.1, width_limit, &checked);
        proof { standalone_template_layouts(&checked, _bit_limit, &circuit); }
        let ghost origin = TemplateOrigin::Standalone(checked);
        let template = FunctionTemplate { circuit, inputs: checked.input_widths, outputs: checked.output_widths,
            _signature: Ghost(checked.signature), _structure_layouts: Ghost(table), _bit_limit: Ghost(_bit_limit), _origin: Ghost(origin) };
        assert(self.function_template_matches(position, width_limit, &template)) by {
            reveal(UseAliases::function_template_matches);
        };
        template
    }

    #[verifier::opaque]
    pub(super) closed spec fn function_templates_match(
        &self, plan: &FunctionExpansionOrder, width_limit: u64, table: &FunctionTemplates,
    ) -> bool {
        let order = plan.order_model();
        &&& table.slots@.len() == order.len()
        &&& table.next <= order.len()
        &&& forall|rank: int| 0 <= rank < order.len() ==> {
            let vertex = #[trigger] order[rank];
            &&& vertex < table.slots@.len()
            &&& if rank < table.next {
                &&& plan.position_model(rank) matches Some(position)
                &&& table.slots@[vertex as int] matches Some(template)
                &&& self.function_template_matches(position, width_limit, &template)
            } else { table.slots@[vertex as int].is_none() }
        }
    }

    /// 展開計画の頂点数と同じ長さの空の索引を作る。
    pub(super) fn new_function_templates(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, Ghost(width_limit): Ghost<u64>,
    ) -> (table: FunctionTemplates<'p, 'a>)
        requires self.function_expansion_evidence(Ok(*plan)),
        ensures self.function_templates_match(plan, width_limit, &table), table.next_rank() == 0,
    {
        proof { self.template_index_evidence(*plan); }
        let count = plan.len();
        let mut slots: Vec<Option<FunctionTemplate<'p, 'a>>> = Vec::new();
        let mut i = 0;
        while i < count
            invariant
                i == slots@.len() <= count,
                forall|j: int| 0 <= j < slots@.len() ==> (#[trigger] slots@[j]).is_none(),
            decreases count - i,
        {
            let ghost before = slots@;
            slots.push(None);
            assert forall|j: int| 0 <= j < slots@.len() implies (#[trigger] slots@[j]).is_none() by {
                if j < i { assert(slots@[j] == before[j]); }
            };
            i += 1;
        }
        let table = FunctionTemplates { slots, next: 0 };
        assert(self.function_templates_match(plan, width_limit, &table)) by {
            reveal(UseAliases::function_templates_match);
        };
        table
    }

    /// 次の順位の関数を、計画で指定された頂点へ格納する。
    pub(super) fn insert_function_template(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, table: &mut FunctionTemplates<'p, 'a>,
        template: FunctionTemplate<'p, 'a>, Ghost(width_limit): Ghost<u64>,
    )
        requires
            self.function_expansion_evidence(Ok(*plan)),
            self.function_templates_match(plan, width_limit, old(table)),
            old(table).next_rank() < plan.order_model().len(),
            plan.position_model(old(table).next_rank() as int) matches Some(position)
                && self.function_template_matches(position, width_limit, &template),
        ensures
            self.function_templates_match(plan, width_limit, final(table)),
            final(table).next_rank() == old(table).next_rank() + 1,
            final(table).slots_model() == old(table).slots_model().update(plan.order_model()[old(table).next_rank() as int] as int, Some(template)),
    {
        reveal(UseAliases::function_templates_match);
        proof { self.template_index_evidence(*plan); }
        let next = table.next;
        let Some(vertex) = plan.template_at(next) else {
            proof { assert(false); }
            unreachable!()
        };
        let ghost prior = table.slots@;
        let mut replacement = Some(template);
        table.slots.set_and_swap(vertex, &mut replacement);
        table.next = next + 1;
        let ghost order = plan.order_model();
        assert forall|rank: int| 0 <= rank < order.len() implies {
            let v = #[trigger] order[rank];
            &&& v < table.slots@.len()
            &&& if rank < table.next {
                &&& plan.position_model(rank) matches Some(position)
                &&& table.slots@[v as int] matches Some(template)
                &&& self.function_template_matches(position, width_limit, &template)
            } else { table.slots@[v as int].is_none() }
        } by {
            if rank != next {
                assert(order[rank] != vertex);
                assert(table.slots@[order[rank] as int] == prior[order[rank] as int]);
            }
        };
    }

    /// 処理済みの順位を持つ呼び出し先を、頂点番号から取り出す。
    pub(super) fn get_function_template<'s>(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, table: &'s FunctionTemplates<'p, 'a>,
        vertex: usize, Ghost(rank): Ghost<int>, Ghost(width_limit): Ghost<u64>,
    ) -> (template: &'s FunctionTemplate<'p, 'a>)
        requires
            self.function_templates_match(plan, width_limit, table),
            0 <= rank < table.next_rank(),
            vertex == plan.order_model()[rank],
        ensures
            table.slots_model()[vertex as int] == Some(*template),
            plan.position_model(rank) matches Some(position) && self.function_template_matches(position, width_limit, template),
    {
        reveal(UseAliases::function_templates_match);
        let Some(template) = &table.slots[vertex] else {
            proof { assert(false); }
            unreachable!()
        };
        template
    }
    pub(super) open spec fn resolved_template_call_matches(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        index: int, selected: ResolvedTemplateCall,
    ) -> bool {
        let group = prepared.calls@[index];
        &&& 0 <= index < prepared.calls@.len()
        &&& *selected.group == group
        &&& group.arguments.start <= group.arguments.end <= prepared.projections.call_arguments.arguments@.len()
        &&& selected.arguments@ == prepared.projections.call_arguments.arguments@.subrange(
            group.arguments.start as int, group.arguments.end as int)
        &&& selected.arguments@.len() == selected.template.signature_model().inputs@.len()
        &&& 0 <= group._order@.0 < group._order@.1 < plan.order_model().len()
        &&& plan.position_model(group._order@.1) == Some((caller.0, caller.1))
        &&& group.vertex == plan.order_model()[group._order@.0]
        &&& plan.position_model(group._order@.0) matches Some(target)
        &&& self.function_template_matches(target, caller.2, selected.template)
        &&& group._signature@.signature matches crate::project::FuncCallSignature::Function(signature)
        &&& signature.inputs@ == selected.template.signature_model().inputs@
        &&& signature.outputs@ == selected.template.signature_model().outputs@
        &&& signature.output_inputs@ == selected.template.signature_model().output_inputs@
    }

    /// 呼び出し順に、元の実引数区間と展開済みの関数を組にする。
    pub(super) fn resolve_template_calls<'s>(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, table: &'s FunctionTemplates<'p, 'a>,
        groups: &'s [CheckedExpansionCall<'p, 'a>], arguments: &'s [ProjectedCallArgument],
        Ghost(prepared): Ghost<PreparedExpansionBody<'p, 'a>>, Ghost(caller): Ghost<(usize, usize, u64)>,
    ) -> (selected: Vec<ResolvedTemplateCall<'s, 'p, 'a>>)
        requires
            self.can_resolve(),
            self.function_expansion_evidence(Ok(*plan)),
            self.function_templates_match(plan, caller.2, table),
            plan.position_model(table.next_rank() as int) == Some((caller.0, caller.1)),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, &prepared),
            groups@ == prepared.calls@,
            arguments@ == prepared.projections.call_arguments.arguments@,
        ensures
            selected@.len() == prepared.calls@.len(),
            forall|i: int| 0 <= i < selected@.len() ==>
                self.resolved_template_call_matches(plan, caller, &prepared, i, #[trigger] selected@[i]),
    {
        let mut selected: Vec<ResolvedTemplateCall<'s, 'p, 'a>> = Vec::new();
        let mut index = 0;
        while index < groups.len()
            invariant
                self.can_resolve(),
                self.function_expansion_evidence(Ok(*plan)),
                self.function_templates_match(plan, caller.2, table),
                plan.position_model(table.next_rank() as int) == Some((caller.0, caller.1)),
                self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, &prepared),
                groups@ == prepared.calls@,
                arguments@ == prepared.projections.call_arguments.arguments@,
                index == selected@.len() <= prepared.calls@.len(),
                forall|i: int| 0 <= i < selected@.len() ==>
                    self.resolved_template_call_matches(plan, caller, &prepared, i, #[trigger] selected@[i]),
            decreases prepared.calls@.len() - index,
        {
            let group = &groups[index];
            proof {
                self.expansion_callee_template_evidence(*plan, caller, &prepared, index as int);
                self.template_rank_from_position(*plan, (caller.0, caller.1), group._order@.1, table.next_rank() as int);
            }
            let template = self.template_for_expansion_call(plan, table, group, Ghost(caller), Ghost(&prepared), Ghost(index as int));
            let inputs = slice_subrange(arguments, group.arguments.start, group.arguments.end);
            let call = ResolvedTemplateCall { group, arguments: inputs, template };
            assert(self.resolved_template_call_matches(plan, caller, &prepared, index as int, call));
            let ghost previous = selected@;
            selected.push(call);
            assert forall|i: int| 0 <= i < selected@.len() implies
                self.resolved_template_call_matches(plan, caller, &prepared, i, #[trigger] selected@[i]) by {
                if i < index { assert(selected@[i] == previous[i]); }
            };
            index += 1;
        }
        selected
    }

    /// 解決済みの呼び出し先と同じ宣言のネットリストを取り出す。
    pub(super) fn template_for_expansion_call<'s>(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, table: &'s FunctionTemplates<'p, 'a>,
        group: &CheckedExpansionCall<'p, 'a>, Ghost(caller): Ghost<(usize, usize, u64)>,
        Ghost(prepared): Ghost<&PreparedExpansionBody<'p, 'a>>, Ghost(index): Ghost<int>,
    ) -> (template: &'s FunctionTemplate<'p, 'a>)
        requires
            self.can_resolve(),
            self.function_templates_match(plan, caller.2, table),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
            0 <= index < prepared.calls@.len() && prepared.calls@[index] == *group,
            group._order@.1 == table.next_rank(),
        ensures
            plan.position_model(group._order@.0) matches Some(target)
                && self.function_template_matches(target, caller.2, template),
            group._signature@.signature matches crate::project::FuncCallSignature::Function(signature)
                && signature.inputs@ == template.signature_model().inputs@
                && signature.outputs@ == template.signature_model().outputs@
                && signature.output_inputs@ == template.signature_model().output_inputs@,
    {
        proof { self.expansion_callee_template_evidence(*plan, caller, prepared, index); }
        let template = self.get_function_template(plan, table, group.vertex, Ghost(group._order@.0), Ghost(caller.2));
        proof {
            reveal(UseAliases::function_template_matches);
            let target = plan.position_model(group._order@.0)->Some_0;
            let signature = group._signature@.signature->Function_0;
            self.typed_routine_signatures_agree(target.0, target.1, caller.2, signature, template._signature@);
        }
        template
    }
}

} // verus!
