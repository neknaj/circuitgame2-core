//! 展開済みの関数を、展開計画で割り当てた頂点番号で引く。

use super::super::{FunctionExpansionOrder, StructureLayouts, TypedRoutineSignature, UseAliases};
use super::{CheckedBitFunc, LoweredBitFunc};
use super::super::StructureTypeError;
use super::frontend::{BitFuncError, contains_structure_port, ExpandedBody, ExpandedBodyError};
#[cfg(verus_only)]
use super::frontend::has_structure_port;
use super::expansion::{CheckedExpansionCall, PreparedExpansionBody, PreparedExpressionCall};
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
    Expanded {
        plan: FunctionExpansionOrder<'p, 'a>,
        prior: FunctionTemplates<'p, 'a>,
        prepared: PreparedExpansionBody<'p, 'a>,
        body: ExpandedBody<'p, 'a>,
        gate_limit: usize,
    },
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
    has_structure_ports: bool,
}

/// 一つの呼び出しと、その実引数および変換済みの呼び出し先。
pub(super) struct ResolvedTemplateCall<'s, 'p, 'a> {
    pub(super) group: &'s CheckedExpansionCall<'p, 'a>,
    pub(super) arguments: &'s [ProjectedCallArgument],
    pub(super) template: &'s FunctionTemplate<'p, 'a>,
    /// 内側から外側へ並べた、定義の右辺にある子呼び出し。
    pub(super) children: Vec<ResolvedExpressionCall<'s, 'p, 'a>>,
}

/// 子の呼び出しと、型検査済みの実引数から切り出した区間。
pub(super) struct ResolvedExpressionCall<'s, 'p, 'a> {
    pub(super) child: &'s PreparedExpressionCall<'p, 'a>,
    pub(super) arguments: &'s [ProjectedCallArgument],
    /// 基底 NOR では `None`。通常関数では展開済みのネットリストを指す。
    pub(super) template: Option<&'s FunctionTemplate<'p, 'a>>,
}

/// 展開順の先頭から格納する。実際の配列の添字には頂点番号を使う。
pub(super) struct FunctionTemplates<'p, 'a> {
    slots: Vec<Option<FunctionTemplate<'p, 'a>>>,
    next: usize,
}

/// 展開順で最初にネットリストを作れなかった関数と、その診断。
#[derive(Debug)]
pub(super) enum FunctionTemplateBuildError<'p, 'a> {
    /// 型と結線を検査して展開に必要な情報を集める段階の失敗。
    Prepare((usize, usize), BitFuncError<'p, 'a>),
    /// 検査した本体を配線へ変換する段階の失敗。
    Lower((usize, usize), ExpandedBodyError<'p, 'a>),
}

pub(super) open spec fn complete_circuit_table(plan: &FunctionExpansionOrder, table: &FunctionTemplates) -> bool {
    forall|rank: int| 0 <= rank < plan.order_model().len() ==> {
        let v = #[trigger] plan.order_model()[rank];
        &&& v < table.slots_model().len()
        &&& table.slots_model()[v as int] matches Some(template)
        &&& nor_evaluation_ready(template.circuit_model().netlist_model(),
            template.circuit_model().input_layout_model().total_bits_model() as nat)
        &&& template.circuit_model().netlist_model().outputs@.len() == template.circuit_model().output_layout_model().total_bits_model()
    }
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

    pub(super) closed spec fn has_structure_ports_model(&self) -> bool { self.has_structure_ports }

    /// 入出力の署名に構造体型が含まれるかを返す。
    pub(super) fn has_structure_ports(&self) -> (value: bool)
        ensures value == self.has_structure_ports_model(),
    {
        self.has_structure_ports
    }

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

    /// 頂点に対応する格納済みネットリストを借りる。未登録の頂点では `None` を返す。
    pub(super) fn circuit_at_vertex(&self, vertex: usize) -> (circuit: Option<&LoweredBitFunc>)
        ensures circuit == if vertex < self.slots_model().len() {
            match &self.slots_model()[vertex as int] {
                Some(template) => Some(template.circuit_model()),
                None => None,
            }
        } else { None },
    {
        if vertex >= self.slots.len() {
            return None;
        }
        match &self.slots[vertex] {
            Some(template) => Some(template.circuit()),
            None => None,
        }
    }

    pub(super) closed spec fn next_rank(&self) -> usize { self.next }

    pub(super) closed spec fn slots_model(&self) -> Seq<Option<FunctionTemplate<'p, 'a>>> { self.slots@ }
}

pub(super) open spec fn call_ports_need_structure_layout(selected: Seq<ResolvedTemplateCall>) -> bool {
    exists|i: int| 0 <= i < selected.len() && (#[trigger] selected[i]).template.has_structure_ports_model()
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) open spec fn called_structure_layout_result(
        &self, selected: Seq<ResolvedTemplateCall>, limit: u64,
        layouts: Option<StructureLayouts>, result: Result<Option<StructureLayouts>, StructureTypeError>,
    ) -> bool {
        match result {
            Ok(value) => {
                &&& layouts.is_some() ==> value == layouts
                &&& value.is_some() <==> layouts.is_some() || call_ports_need_structure_layout(selected)
                &&& value matches Some(table) ==> self.structure_types_match(limit, Ok(table))
            },
            Err(error) => layouts.is_none() && call_ports_need_structure_layout(selected)
                && self.structure_types_match(limit, Err(error)),
        }
    }

    /// 既存の構造体配置を使う。配置がなければ、呼び出し先の署名に必要な場合に検査する。
    ///
    /// # Errors
    ///
    /// 呼び出し先の署名に構造体があり、構造体の配置を検査できなかった場合に、その診断を返す。
    pub(super) fn prepare_called_structure_layout(
        &self, selected: &[ResolvedTemplateCall<'_, 'p, 'a>], limit: u64,
        layouts: Option<StructureLayouts<'p, 'a>>,
    ) -> (result: Result<Option<StructureLayouts<'p, 'a>>, StructureTypeError<'p, 'a>>)
        requires
            self.can_resolve(),
            layouts matches Some(table) ==> self.structure_types_match(limit, Ok(table)),
        ensures self.called_structure_layout_result(selected@, limit, layouts, result),
    {
        reveal(UseAliases::called_structure_layout_result);
        if layouts.is_some() {
            return Ok(layouts);
        }
        let mut index = 0;
        while index < selected.len()
            invariant
                self.can_resolve(),
                layouts.is_none(),
                index <= selected@.len(),
                forall|i: int| 0 <= i < index ==> !(#[trigger] selected@[i]).template.has_structure_ports_model(),
            decreases selected@.len() - index,
        {
            if selected[index].template.has_structure_ports() {
                assert(call_ports_need_structure_layout(selected@));
                return match self.check_structure_types(limit) {
                    Ok(table) => Ok(Some(table)),
                    Err(error) => Err(error),
                };
            }
            index += 1;
        }
        Ok(None)
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) closed spec fn template_abi_matches(
        &self, position: (usize, usize), width_limit: u64, template: &FunctionTemplate,
    ) -> bool {
        &&& self.typed_signature_evidence(position.0, position.1, width_limit, Ok(Some(template._signature@)))
        &&& template.has_structure_ports_model() <==> has_structure_port(template._signature@.inputs@)
            || has_structure_port(template._signature@.outputs@)
        &&& self.template_port_widths_match(template._signature@, width_limit, template.inputs@, template.outputs@,
            template._structure_layouts@)
        &&& port_bit_layout_result(template.inputs@, template._bit_limit@, Ok(*template.circuit.input_layout_model()))
        &&& port_bit_layout_result(template.outputs@, template._bit_limit@, Ok(*template.circuit.output_layout_model()))
        &&& nor_evaluation_ready(template.circuit.netlist_model(), template.circuit.input_layout_model().total_bits_model() as nat)
        &&& template.circuit.netlist_model().outputs@.len() == template.circuit.output_layout_model().total_bits_model()
    }

    pub(super) closed spec fn function_template_matches(
        &self, position: (usize, usize), width_limit: u64, template: &FunctionTemplate,
    ) -> bool {
        &&& self.template_abi_matches(position, width_limit, template)
        &&& match template._origin@ {
            TemplateOrigin::Standalone(checked) =>
                checked.signature == template._signature@
                    && checked.input_widths@ == template.inputs@ && checked.output_widths@ == template.outputs@
                    && self.checked_bit_func_matches(position.0, position.1, width_limit, &checked)
                    && lowered_bit_func_result(&checked, template._bit_limit@, Ok(template.circuit)),
            TemplateOrigin::Expanded { plan, prior, prepared, body, gate_limit } => {
                &&& body.circuit == template.circuit
                &&& body.ports.inputs@ == template.inputs@
                &&& body.ports.outputs@ == template.outputs@
                &&& body.ports.layouts == template._structure_layouts@
                &&& prepared.typed.literals.wiring matches crate::project::FuncWiringResult::Checked(wiring)
                &&& wiring.drivers.signature == template._signature@
                &&& self.prepared_expansion_body_matches(plan, position.0, position.1, width_limit, &prepared)
                &&& self.expanded_body_lowering_result(&plan, &prior, (position.0, position.1, width_limit),
                    &prepared, template._bit_limit@, gate_limit, Ok(body))
            },
        }
    }

    pub(super) proof fn template_port_evidence(
        &self, position: (usize, usize), limit: u64, template: &FunctionTemplate,
    )
        requires self.template_abi_matches(position, limit, template),
        ensures self.template_port_widths_match(template.signature_model(), limit, template.input_widths_model(),
            template.output_widths_model(), template.structure_layouts_model()),
    {
        reveal(UseAliases::function_template_matches);
    }

    /// 署名の各ポート幅が、保存したネットリストの入出力配置に対応することを示す。
    pub(super) proof fn template_circuit_evidence(
        &self, position: (usize, usize), limit: u64, template: &FunctionTemplate,
    )
        requires self.template_abi_matches(position, limit, template),
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
        let has_structure_ports = contains_structure_port(checked.signature.inputs.as_slice())
            || contains_structure_port(checked.signature.outputs.as_slice());
        let template = FunctionTemplate { circuit, inputs: checked.input_widths, outputs: checked.output_widths, has_structure_ports,
            _signature: Ghost(checked.signature), _structure_layouts: Ghost(table), _bit_limit: Ghost(_bit_limit), _origin: Ghost(origin) };
        assert(self.function_template_matches(position, width_limit, &template)) by {
            reveal(UseAliases::function_template_matches);
        };
        template
    }

    /// 検査した呼び出し付き本体を、後続の呼び出しで使えるテンプレートにする。
    fn expanded_function_template(
        &self, body: ExpandedBody<'p, 'a>, _bit_limit: usize, _gate_limit: usize,
        Ghost(context): Ghost<(
            &FunctionExpansionOrder<'p, 'a>, &FunctionTemplates<'p, 'a>, (usize, usize, u64), &PreparedExpansionBody<'p, 'a>,
        )>,
    ) -> (template: FunctionTemplate<'p, 'a>)
        requires
            self.prepared_expansion_body_matches(*context.0, context.2.0, context.2.1, context.2.2, context.3),
            self.expanded_body_lowering_result(context.0, context.1, context.2, context.3, _bit_limit, _gate_limit, Ok(body)),
        ensures
            self.function_template_matches((context.2.0, context.2.1), context.2.2, &template),
            template.bit_limit_model() == _bit_limit,
            template._origin@ matches TemplateOrigin::Expanded { plan, prior, gate_limit, .. }
                && plan == *context.0 && prior == *context.1 && gate_limit == _gate_limit,
    {
        proof { self.expanded_body_ports_evidence(context.0, context.1, context.2, context.3, _bit_limit, _gate_limit, &body); }
        let ghost signature = context.3.typed.literals.wiring->Checked_0.drivers.signature;
        let ghost origin = TemplateOrigin::Expanded {
            plan: *context.0, prior: *context.1, prepared: *context.3, body, gate_limit: _gate_limit,
        };
        let ghost layouts = body.ports.layouts;
        let ExpandedBody { circuit, ports, has_structure_ports } = body;
        let template = FunctionTemplate {
            circuit, inputs: ports.inputs, outputs: ports.outputs, has_structure_ports,
            _signature: Ghost(signature), _structure_layouts: Ghost(layouts), _bit_limit: Ghost(_bit_limit), _origin: Ghost(origin),
        };
        assert(self.function_template_matches((context.2.0, context.2.1), context.2.2, &template));
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
        assert(next < table.slots@.len() <= usize::MAX) by {
            vstd::std_specs::vec::axiom_spec_len(&table.slots);
        };
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

    #[verifier::opaque]
    spec fn ordered_template_prefix(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, bit_limit: usize, gate_limit: usize,
    ) -> bool {
        let order = plan.order_model();
        &&& table.slots_model().len() == order.len()
        &&& table.next_rank() <= order.len()
        &&& forall|rank: int| 0 <= rank < table.next_rank() ==> {
            let vertex = #[trigger] order[rank];
            &&& table.slots_model()[vertex as int] matches Some(template)
            &&& template.bit_limit_model() == bit_limit
            &&& template._origin@ matches TemplateOrigin::Expanded { plan: original, prior, gate_limit: limit, .. }
            &&& original == *plan && limit == gate_limit
            &&& prior.next_rank() == rank && prior.slots_model().len() == order.len()
            &&& forall|i: int| 0 <= i < rank ==> {
                let previous = #[trigger] order[i];
                prior.slots_model()[previous as int] == table.slots_model()[previous as int]
            }
        }
    }

    /// 追加した回路が同じ上限で生成され、以前に参照した回路が同じ頂点に残ることを示す。
    proof fn extend_ordered_template_prefix(
        &self, plan: &FunctionExpansionOrder, before: &FunctionTemplates, after: &FunctionTemplates,
        bit_limit: usize, gate_limit: usize, template: FunctionTemplate,
    )
        requires
            self.function_expansion_evidence(Ok(*plan)),
            self.ordered_template_prefix(plan, before, bit_limit, gate_limit),
            before.next_rank() < plan.order_model().len(),
            after.next_rank() == before.next_rank() + 1,
            before.slots_model().len() == plan.order_model().len(),
            plan.order_model()[before.next_rank() as int] < before.slots_model().len(),
            after.slots_model() == before.slots_model().update(plan.order_model()[before.next_rank() as int] as int, Some(template)),
            template.bit_limit_model() == bit_limit,
            template._origin@ matches TemplateOrigin::Expanded { plan: original, prior, gate_limit: limit, .. }
                && original == *plan && prior == *before && limit == gate_limit,
        ensures self.ordered_template_prefix(plan, after, bit_limit, gate_limit),
    {
        reveal(UseAliases::ordered_template_prefix);
        self.template_index_evidence(*plan);
        let order = plan.order_model();
        let at = before.next_rank() as int;
        assert forall|rank: int| 0 <= rank < after.next_rank() implies {
            let vertex = #[trigger] order[rank];
            &&& after.slots_model()[vertex as int] matches Some(template)
            &&& template.bit_limit_model() == bit_limit
            &&& template._origin@ matches TemplateOrigin::Expanded { plan: original, prior, gate_limit: limit, .. }
            &&& original == *plan && limit == gate_limit
            &&& prior.next_rank() == rank && prior.slots_model().len() == order.len()
            &&& forall|i: int| 0 <= i < rank ==> {
                let previous = #[trigger] order[i];
                prior.slots_model()[previous as int] == after.slots_model()[previous as int]
            }
        } by {
            let vertex = order[rank];
            assert(vertex < order.len());
            if rank < at {
                assert(vertex != order[at]);
                assert(after.slots_model()[vertex as int] == before.slots_model()[vertex as int]);
            } else {
                assert(after.slots_model()[vertex as int] == Some(template));
            }
            let earlier_table = after.slots_model()[vertex as int]->Some_0._origin@->Expanded_prior;
            assert forall|i: int| 0 <= i < rank implies
                earlier_table.slots_model()[#[trigger] order[i] as int] == after.slots_model()[order[i] as int] by {
                assert(order[i] < order.len());
                assert(order[i] != order[at]);
                assert(after.slots_model()[order[i] as int] == before.slots_model()[order[i] as int]);
                if rank == at {
                    assert(earlier_table == *before);
                } else {
                    assert(earlier_table.slots_model()[order[i] as int] == before.slots_model()[order[i] as int]);
                }
            };
        };
    }

    pub(super) closed spec fn ordered_template_build_result(
        &self, plan: &FunctionExpansionOrder, width_limit: u64, bit_limit: usize, gate_limit: usize,
        result: Result<FunctionTemplates, FunctionTemplateBuildError>,
    ) -> bool {
        match result {
            Ok(table) => self.function_templates_match(plan, width_limit, &table)
                && self.ordered_template_prefix(plan, &table, bit_limit, gate_limit)
                && table.next_rank() == plan.order_model().len(),
            Err(error) => exists|prior: FunctionTemplates| {
                &&& #[trigger] self.function_templates_match(plan, width_limit, &prior)
                &&& self.ordered_template_prefix(plan, &prior, bit_limit, gate_limit)
                &&& prior.next_rank() < plan.order_model().len()
                &&& plan.position_model(prior.next_rank() as int) matches Some(position)
                &&& match error {
                    FunctionTemplateBuildError::Prepare(site, error) => site == position
                        && self.expansion_body_preparation_result(*plan, position.0, position.1, width_limit, Err(error)),
                    FunctionTemplateBuildError::Lower(site, error) => site == position
                        && exists|body: PreparedExpansionBody|
                            #[trigger] self.prepared_expansion_body_matches(*plan, position.0, position.1, width_limit, &body)
                            && self.expanded_body_lowering_result(plan, &prior, (position.0, position.1, width_limit),
                                &body, bit_limit, gate_limit, Err(error)),
                }
            },
        }
    }

    /// 各関数の展開元を取り出し、参照した先行関数が完成後の表にも同じ頂点にあることを示す。
    pub(super) proof fn completed_template_expansion_at(
        &self, plan: &FunctionExpansionOrder, width_limit: u64, bit_limit: usize, gate_limit: usize,
        table: &FunctionTemplates, rank: int,
    ) -> (evidence: (FunctionTemplate<'p, 'a>, FunctionTemplates<'p, 'a>, PreparedExpansionBody<'p, 'a>, ExpandedBody<'p, 'a>))
        requires
            self.function_expansion_evidence(Ok(*plan)),
            self.ordered_template_build_result(plan, width_limit, bit_limit, gate_limit, Ok(*table)),
            0 <= rank < plan.order_model().len(),
        ensures ({
            let (template, prior, prepared, body) = evidence;
            let vertex = plan.order_model()[rank];
            &&& vertex < table.slots_model().len()
            &&& table.slots_model()[vertex as int] == Some(template)
            &&& plan.position_model(rank) matches Some(position)
            &&& body.circuit == *template.circuit_model()
            &&& self.prepared_expansion_body_matches(*plan, position.0, position.1, width_limit, &prepared)
            &&& self.expanded_body_lowering_result(plan, &prior, (position.0, position.1, width_limit),
                &prepared, bit_limit, gate_limit, Ok(body))
            &&& prior.next_rank() == rank
            &&& prior.slots_model().len() == table.slots_model().len()
            &&& forall|i: int| 0 <= i < rank ==> {
                let earlier = #[trigger] plan.order_model()[i];
                prior.slots_model()[earlier as int] == table.slots_model()[earlier as int]
            }
        }),
    {
        reveal(UseAliases::ordered_template_build_result);
        reveal(UseAliases::ordered_template_prefix);
        reveal(UseAliases::function_templates_match);
        let vertex = plan.order_model()[rank];
        let template = table.slots_model()[vertex as int]->Some_0;
        let position = plan.position_model(rank)->Some_0;
        assert(self.function_template_matches(position, width_limit, &template));
        reveal(UseAliases::function_template_matches);
        match template._origin@ {
            TemplateOrigin::Expanded { prior, prepared, body, .. } => (template, prior, prepared, body),
            TemplateOrigin::Standalone(_) => { assert(false); arbitrary() },
        }
    }

    /// 展開済みの表から、全順位で評価に必要な入出力配置と配線がそろっていることを示す。
    pub(super) proof fn completed_templates_ready(
        &self, plan: &FunctionExpansionOrder, width_limit: u64, bit_limit: usize, gate_limit: usize,
        table: &FunctionTemplates,
    )
        requires
            self.function_expansion_evidence(Ok(*plan)),
            self.ordered_template_build_result(plan, width_limit, bit_limit, gate_limit, Ok(*table)),
        ensures
            plan.source_positions_complete(), plan.source_vertices_match(),
            complete_circuit_table(plan, table),
    {
        reveal(UseAliases::ordered_template_build_result);
        reveal(UseAliases::function_templates_match);
        self.template_index_evidence(*plan);
        assert forall|rank: int| 0 <= rank < plan.order_model().len() implies {
            let v = #[trigger] plan.order_model()[rank];
            &&& v < table.slots_model().len()
            &&& table.slots_model()[v as int] matches Some(template)
            &&& nor_evaluation_ready(template.circuit_model().netlist_model(),
                template.circuit_model().input_layout_model().total_bits_model() as nat)
            &&& template.circuit_model().netlist_model().outputs@.len() == template.circuit_model().output_layout_model().total_bits_model()
        } by {
            let v = plan.order_model()[rank];
            let template = &table.slots_model()[v as int]->Some_0;
            reveal(UseAliases::function_template_matches);
            reveal(UseAliases::template_abi_matches);
            assert(self.template_abi_matches(plan.position_model(rank)->Some_0, width_limit, template));
        };
    }

    /// 展開計画の順に関数を変換し、変換したネットリストを後続の呼び出しで使う。
    ///
    /// # Errors
    ///
    /// 最初に変換できなかった関数の宣言位置と診断を返す。
    pub(super) fn expand_templates_in_order(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, width_limit: u64, bit_limit: usize, gate_limit: usize,
    ) -> (result: Result<FunctionTemplates<'p, 'a>, FunctionTemplateBuildError<'p, 'a>>)
        requires self.can_resolve(), self.function_expansion_evidence(Ok(*plan)),
        ensures self.ordered_template_build_result(plan, width_limit, bit_limit, gate_limit, result),
    {
        reveal(UseAliases::ordered_template_build_result);
        proof {
            self.template_index_evidence(*plan);
            assert forall|rank: int| 0 <= rank < plan.order_model().len()
                implies (#[trigger] plan.position_model(rank)).is_some() by {
                assert(plan.order_model()[rank] < plan.order_model().len());
            };
        }
        let mut templates = self.new_function_templates(plan, Ghost(width_limit));
        proof {
            reveal(UseAliases::function_templates_match);
            assert(templates.slots_model().len() == plan.order_model().len());
            assert(self.ordered_template_prefix(plan, &templates, bit_limit, gate_limit)) by {
                reveal(UseAliases::ordered_template_prefix);
            };
        }
        while templates.next_index() < plan.len()
            invariant
                self.can_resolve(),
                self.function_expansion_evidence(Ok(*plan)),
                self.function_templates_match(plan, width_limit, &templates),
                self.ordered_template_prefix(plan, &templates, bit_limit, gate_limit),
                templates.next_rank() <= plan.order_model().len(),
                templates.slots_model().len() == plan.order_model().len(),
                forall|rank: int| 0 <= rank < plan.order_model().len() ==> (#[trigger] plan.order_model()[rank]) < plan.order_model().len(),
                forall|rank: int| 0 <= rank < plan.order_model().len() ==> (#[trigger] plan.position_model(rank)).is_some(),
            decreases plan.order_model().len() - templates.next_rank(),
        {
            let next = templates.next_index();
            let Some(position) = plan.get(next) else {
                proof { assert(false); }
                unreachable!()
            };
            let caller = (position.0, position.1, width_limit);
            let prepared = match self.prepare_expansion_body(plan, position.0, position.1, width_limit) {
                Ok(body) => body,
                Err(error) => return Err(FunctionTemplateBuildError::Prepare(position, error)),
            };
            let ghost original = prepared;
            let body = match self.lower_expanded_body(plan, &templates, caller, prepared, bit_limit, gate_limit) {
                Ok(body) => body,
                Err(error) => {
                    assert(exists|prepared: PreparedExpansionBody|
                        #[trigger] self.prepared_expansion_body_matches(*plan, position.0, position.1, width_limit, &prepared)
                        && self.expanded_body_lowering_result(plan, &templates, caller, &prepared, bit_limit, gate_limit, Err(error)));
                    return Err(FunctionTemplateBuildError::Lower(position, error));
                },
            };
            let template = self.expanded_function_template(body, bit_limit, gate_limit, Ghost((plan, &templates, caller, &original)));
            let ghost before = templates;
            self.insert_function_template(plan, &mut templates, template, Ghost(width_limit));
            proof { self.extend_ordered_template_prefix(plan, &before, &templates, bit_limit, gate_limit, template); }
        }
        Ok(templates)
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
        &&& selected.arguments@.len() == selected.template.input_widths_model().len()
        &&& selected.template.has_structure_ports_model() <==> has_structure_port(selected.template.signature_model().inputs@)
            || has_structure_port(selected.template.signature_model().outputs@)
        &&& 0 <= group._order@.0 < group._order@.1 < plan.order_model().len()
        &&& plan.position_model(group._order@.1) == Some((caller.0, caller.1))
        &&& group.vertex == plan.order_model()[group._order@.0]
        &&& plan.position_model(group._order@.0) matches Some(target)
        &&& self.template_abi_matches(target, caller.2, selected.template)
        &&& group._signature@.signature matches crate::project::FuncCallSignature::Function(signature)
        &&& signature.inputs@ == selected.template.signature_model().inputs@
        &&& signature.outputs@ == selected.template.signature_model().outputs@
        &&& signature.output_inputs@ == selected.template.signature_model().output_inputs@
    }

    pub(super) open spec fn expansion_selection_matches(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>,
    ) -> bool {
        &&& selected.len() == prepared.calls@.len()
        &&& forall|i: int| 0 <= i < selected.len() ==> {
            let call = #[trigger] selected[i];
            &&& self.resolved_template_call_matches(plan, caller, prepared, i, call)
            &&& table.slots_model()[call.group.vertex as int] == Some(*call.template)
            &&& self.resolved_expression_calls_match(plan, table, caller.2, call.group.postorder,
                prepared.projections.call_arguments.arguments@, call.children@)
        }
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
        ensures self.expansion_selection_matches(plan, table, caller, &prepared, selected@),
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
                forall|i: int| 0 <= i < selected@.len() ==> {
                    let call = #[trigger] selected@[i];
                    &&& self.resolved_template_call_matches(plan, caller, &prepared, i, call)
                    &&& table.slots_model()[call.group.vertex as int] == Some(*call.template)
                    &&& self.resolved_expression_calls_match(plan, table, caller.2, call.group.postorder,
                        arguments@, call.children@)
                },
            decreases prepared.calls@.len() - index,
        {
            let group = &groups[index];
            proof {
                self.expansion_callee_template_evidence(*plan, caller, &prepared, index as int);
                self.template_rank_from_position(*plan, (caller.0, caller.1), group._order@.1, table.next_rank() as int);
            }
            let template = self.template_for_expansion_call(plan, table, group, Ghost(caller), Ghost(&prepared), Ghost(index as int));
            let inputs = slice_subrange(arguments, group.arguments.start, group.arguments.end);
            let children = self.select_expression_calls(plan, table, group, arguments,
                Ghost(caller), Ghost(&prepared), Ghost(index as int));
            let call = ResolvedTemplateCall { group, arguments: inputs, template, children };
            proof {
                let target = plan.position_model(group._order@.0)->Some_0;
                self.template_port_evidence(target, caller.2, template);
                self.template_port_counts(template.signature_model(), caller.2, template.input_widths_model(),
                    template.output_widths_model(), template.structure_layouts_model());
            }
            assert(self.resolved_template_call_matches(plan, caller, &prepared, index as int, call));
            let ghost previous = selected@;
            selected.push(call);
            assert forall|i: int| 0 <= i < selected@.len() implies {
                let row = #[trigger] selected@[i];
                &&& self.resolved_template_call_matches(plan, caller, &prepared, i, row)
                &&& table.slots_model()[row.group.vertex as int] == Some(*row.template)
                &&& self.resolved_expression_calls_match(plan, table, caller.2, row.group.postorder,
                    arguments@, row.children@)
            } by {
                if i < index { assert(selected@[i] == previous[i]); }
            };
            index += 1;
        }
        selected
    }

    #[verifier::opaque]
    pub(super) open spec fn resolved_expression_call_matches(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, limit: u64,
        arguments: Seq<ProjectedCallArgument>, child: PreparedExpressionCall, selected: ResolvedExpressionCall,
    ) -> bool {
        let span = child.arguments;
        &&& *selected.child == child
        &&& span.start <= span.end <= arguments.len()
        &&& selected.arguments@ == arguments.subrange(span.start as int, span.end as int)
        &&& match (child._signature@.signature, selected.template) {
            (crate::project::FuncCallSignature::Nor, None) => child.vertex.is_none() && selected.arguments@.len() == 2,
            (crate::project::FuncCallSignature::Function(signature), Some(template)) =>
                match (child.vertex, child._rank@) {
                    (Some(vertex), Some(rank)) => {
                        &&& vertex < table.slots_model().len()
                        &&& 0 <= rank < table.next_rank()
                        &&& rank < plan.order_model().len() && plan.order_model()[rank] == vertex
                        &&& table.slots_model()[vertex as int] == Some(*template)
                        &&& plan.position_model(rank) matches Some(target)
                            && self.template_abi_matches(target, limit, template)
                        &&& signature.inputs@ == template.signature_model().inputs@
                        &&& selected.arguments@.len() == signature.inputs@.len()
                        &&& signature.outputs@ == template.signature_model().outputs@
                        &&& signature.output_inputs@ == template.signature_model().output_inputs@
                    },
                    _ => false,
                },
            _ => false,
        }
    }

    pub(super) open spec fn resolved_expression_calls_match(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, limit: u64,
        children: Option<Vec<PreparedExpressionCall>>, arguments: Seq<ProjectedCallArgument>,
        selected: Seq<ResolvedExpressionCall>,
    ) -> bool {
        match children {
            None => selected.len() == 0,
            Some(children) => selected.len() == children@.len()
                && forall|i: int| 0 <= i < selected.len() ==> self.resolved_expression_call_matches(
                    plan, table, limit, arguments, children@[i], #[trigger] selected[i]),
        }
    }

    /// 子の実引数を借用し、保存済みの頂点番号で展開済みの回路を引く。
    fn select_expression_calls<'s>(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, table: &'s FunctionTemplates<'p, 'a>,
        group: &'s CheckedExpansionCall<'p, 'a>, arguments: &'s [ProjectedCallArgument],
        Ghost(caller): Ghost<(usize, usize, u64)>, Ghost(prepared): Ghost<&PreparedExpansionBody<'p, 'a>>,
        Ghost(group_index): Ghost<int>,
    ) -> (selected: Vec<ResolvedExpressionCall<'s, 'p, 'a>>)
        requires
            self.can_resolve(),
            self.function_templates_match(plan, caller.2, table),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
            0 <= group_index < prepared.calls@.len() && prepared.calls@[group_index] == *group,
            group._order@.1 == table.next_rank(),
            arguments@ == prepared.projections.call_arguments.arguments@,
        ensures self.resolved_expression_calls_match(plan, table, caller.2, group.postorder, arguments@, selected@),
    {
        let mut selected: Vec<ResolvedExpressionCall<'s, 'p, 'a>> = Vec::new();
        let Some(children) = &group.postorder else {
            return selected;
        };
        let mut index = 0;
        while index < children.len()
            invariant
                self.can_resolve(),
                self.function_templates_match(plan, caller.2, table),
                self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
                0 <= group_index < prepared.calls@.len() && prepared.calls@[group_index] == *group,
                group._order@.1 == table.next_rank(), group.postorder == Some(*children),
                arguments@ == prepared.projections.call_arguments.arguments@,
                index == selected@.len() <= children@.len(),
                forall|i: int| 0 <= i < selected@.len() ==> self.resolved_expression_call_matches(
                    plan, table, caller.2, arguments@, children@[i], #[trigger] selected@[i]),
            decreases children@.len() - index,
        {
            let child = &children[index];
            proof { self.expansion_child_template_evidence(*plan, caller, prepared, group_index, index as int); }
            let template = if let Some(vertex) = child.vertex {
                let ghost rank = child._rank@->Some_0;
                let template = self.get_function_template(plan, table, vertex, Ghost(rank), Ghost(caller.2));
                proof {
                    reveal(UseAliases::function_template_matches);
                    let target = plan.position_model(rank)->Some_0;
                    self.typed_routine_signatures_agree(target.0, target.1, caller.2,
                        child._signature@.signature->Function_0, template.signature_model());
                }
                Some(template)
            } else { None };
            let inputs = slice_subrange(arguments, child.arguments.start, child.arguments.end);
            let call = ResolvedExpressionCall { child, arguments: inputs, template };
            assert(self.resolved_expression_call_matches(plan, table, caller.2, arguments@, *child, call)) by {
                reveal(UseAliases::resolved_expression_call_matches);
                reveal(UseAliases::function_templates_match);
            };
            let ghost previous = selected@;
            selected.push(call);
            assert forall|i: int| 0 <= i < selected@.len() implies self.resolved_expression_call_matches(
                plan, table, caller.2, arguments@, children@[i], #[trigger] selected@[i]) by {
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
            table.slots_model()[group.vertex as int] == Some(*template),
            template.has_structure_ports_model() <==> has_structure_port(template.signature_model().inputs@)
                || has_structure_port(template.signature_model().outputs@),
            plan.position_model(group._order@.0) matches Some(target)
                && self.template_abi_matches(target, caller.2, template),
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

#[cfg(all(test, not(verus_only)))]
#[test]
fn selects_a_template_for_the_same_child_and_keeps_nor_builtin() {
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    let project = parse_circuit_project(&[SourceSnapshot {
        path: "calls.ncg2",
        revision: 1,
        text: "(using nor) (func id (in a) (out a))
               (func caller (in a) (out y) (def y (id (id (nor a a)))))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let mut table = aliases.new_function_templates(&plan, Ghost(8u64));
    let position = plan.get(0).unwrap();
    let checked = aliases.check_bit_func(position.0, position.1, 8).unwrap();
    let circuit = checked.lower_bit_func(8).unwrap();
    let template = aliases.standalone_function_template(position, 8, checked, circuit, 8);
    aliases.insert_function_template(&plan, &mut table, template, Ghost(8u64));
    let position = plan.get(1).unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, position.0, position.1, 8).unwrap();
    let selected = aliases.resolve_template_calls(&plan, &table, &prepared.calls,
        &prepared.projections.call_arguments.arguments, Ghost(prepared), Ghost((position.0, position.1, 8u64)));
    let children = &selected[0].children;
    assert!(children[0].template.is_none());
    assert_eq!(children[0].arguments.len(), 2);
    assert!(core::ptr::eq(children[1].template.unwrap(), selected[0].template));
    assert_eq!(children[1].arguments.len(), 1);
}

} // verus!
