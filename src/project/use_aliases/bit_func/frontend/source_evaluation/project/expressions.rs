//! 厳格構文木にある呼び出し式の引数と、単一の出力値を対応付ける。

use super::*;
use crate::netlist::{port_bit_layout_port, port_bit_layout_size, preceding_port_bits};
use crate::project::{FuncCallSignature, FuncCallTarget, ResolvedPortType, port_types_equal};
use crate::project::use_aliases::bit_func::expansion::{
    PreparedExpansionBody, expansion_child_reachable, prepared_nested_output_matches, source_call_argument_value, source_call_argument_values_agree,
    source_call_arguments_match,
};
use crate::project::use_aliases::call_arity::CallArgumentSource;
use crate::project::use_aliases::bit_func::frontend::expression_input_width;
use crate::project::use_aliases::bit_func::lowering::{EvaluatedCallBits, EvaluatedNestedCall, evaluated_nested_call_matches};
use crate::project::use_aliases::bit_func::templates::{ResolvedExpressionCall, ResolvedTemplateCall};
use crate::syntax::circuit::{
    build_definition_scope_evidence, call_argument_position_bounds, call_argument_positions,
    call_argument_positions_agree, definition_reference_form_unique,
};

verus! {

/// 一つの定義の右辺を評価するときに読めるソース上の値と、先行する関数の評価。
pub(super) struct SourceExpressionScope<'s, 'w, 'p, 'a> {
    context: &'s SourceFunc<'w, 'p, 'a>,
    definition: usize,
    plan: &'s FunctionExpansionOrder<'p, 'a>,
    rank: int,
    derivation: ISet<SourceInvocation>,
    typed: FuncSignalTypes<'p, 'a>,
    layouts: Option<&'s StructureLayouts<'p, 'a>>,
    inputs: Seq<Seq<bool>>,
    prior: Seq<Seq<bool>>,
}

/// 一つの入れ子呼び出しが使う相対参照と、宣言順の引数値および単一の出力値。
pub(super) struct SourceExpressionCall<'p, 'a> {
    reference: usize,
    signature: TypedFuncCall<'p, 'a>,
    callee_rank: Option<int>,
    widths: Seq<u64>,
    arguments: Seq<Seq<bool>>,
    result: Seq<bool>,
}

/// 型検査の結果と、同じ定義の内側にある呼び出しの値を保持する。
pub(super) struct NestedSourceArguments<'p, 'a> {
    pub(super) typed: FuncSignalTypes<'p, 'a>,
    pub(super) layouts: Option<StructureLayouts<'p, 'a>>,
    pub(super) children: Map<usize, SourceExpressionCall<'p, 'a>>,
}

pub(super) closed spec fn source_expression_scope<'s, 'w, 'p, 'a>(
    context: &'s SourceFunc<'w, 'p, 'a>, plan: &'s FunctionExpansionOrder<'p, 'a>, rank: int,
    derivation: ISet<SourceInvocation>, site: SourceCallEvaluation<'p, 'a>,
    nested: &'s NestedSourceArguments<'p, 'a>, inputs: Seq<Seq<bool>>, values: Seq<Seq<bool>>,
) -> SourceExpressionScope<'s, 'w, 'p, 'a> {
    SourceExpressionScope { context, plan, rank, derivation, definition: site.definition,
        typed: nested.typed, layouts: match &nested.layouts { Some(table) => Some(table), None => None },
        inputs, prior: values.take(site.outputs.start as int) }
}

spec fn source_expression_output_type<'p, 'a>(call: TypedFuncCall<'p, 'a>) -> Option<ResolvedPortType<'p, 'a>> {
    match call.signature {
        FuncCallSignature::Nor => Some(ResolvedPortType::Bits(1)),
        FuncCallSignature::Function(ports) => if ports.outputs@.len() == 1 {
            Some(ports.outputs@[0].ty)
        } else { None },
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn source_expression_scope_matches(&self, scope: &SourceExpressionScope) -> bool {
        let source = scope.context;
        let project = self.targets.project_model();
        &&& self.can_resolve()
        &&& self.function_expansion_evidence(Ok(*scope.plan))
        &&& 0 <= scope.rank < scope.plan.order_model().len()
        &&& scope.plan.position_model(scope.rank) == Some((source.file, source.entry))
        &&& source.file < project.sources_model().len() && source.file < project.circuits_model().len()
        &&& *source.source == project.sources_model()[source.file as int]
        &&& *source.parsed == project.circuits_model()[source.file as int]
        &&& source.entry < source.parsed.entry_ranges@.len()
        &&& source.parsed.entry_ranges@[source.entry as int].definitions.start <= scope.definition
            < source.parsed.entry_ranges@[source.entry as int].definitions.end <= source.parsed.definitions@.len()
        &&& self.func_wiring_evidence(source.file, source.entry, source.limit, Ok(FuncWiringResult::Checked(*source.wiring)))
        &&& self.func_signal_types_evidence(source.file, source.entry, source.limit, Ok(scope.typed))
        &&& scope.typed.literals.wiring == FuncWiringResult::Checked(*source.wiring)
        &&& scope.prior.len() <= source.wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < source.wiring.drivers.definitions@.len() ==>
            (i < scope.prior.len()) == ((#[trigger] source.wiring.drivers.definitions@[i]).definition < scope.definition)
        &&& self.structure_layout_for_ports(source.limit, scope.layouts)
    }

    /// 構造体ポートを持つテンプレートから、検査済みの構造体配置を得る。
    proof fn source_template_structure_layout(
        &self, target: (usize, usize), limit: u64, template: &FunctionTemplate,
    ) -> (layouts: StructureLayouts<'p, 'a>)
        requires
            self.template_abi_matches(target, limit, template),
            has_structure_port(template.signature_model().inputs@) || has_structure_port(template.signature_model().outputs@),
        ensures self.structure_types_match(limit, Ok(layouts)),
    {
        self.template_port_evidence(target, limit, template);
        reveal(UseAliases::template_port_widths_match);
        let signature = template.signature_model();
        let layouts = template.structure_layouts_model();
        if layouts.is_none() {
            let (ports, widths) = if has_structure_port(signature.inputs@) {
                (signature.inputs@, template.input_widths_model())
            } else {
                (signature.outputs@, template.output_widths_model())
            };
            let i = choose|i: int| 0 <= i < ports.len() && (#[trigger] ports[i]).ty is Struct;
            assert(self.port_width_matches(ports[i].ty, widths[i], None));
            assert(false);
        }
        layouts->Some_0
    }

    /// 根と各子の幅を比較するときに使う一つの検査済み配置表を選ぶ。
    proof fn source_nested_call_layout(
        &self, plan: &FunctionExpansionOrder, prior: &FunctionTemplates, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, group_index: int, selected: &ResolvedTemplateCall,
        preferred: Option<StructureLayouts>,
    ) -> (layouts: Option<StructureLayouts<'p, 'a>>)
        requires
            self.resolved_template_call_matches(plan, caller, prepared, group_index, *selected),
            self.resolved_expression_calls_match(plan, prior, caller.2, selected.group.postorder,
                prepared.projections.call_arguments.arguments@, selected.children@),
            preferred matches Some(table) ==> self.structure_types_match(caller.2, Ok(table)),
        ensures
            layouts matches Some(table) ==> self.structure_types_match(caller.2, Ok(table)),
            layouts.is_none() ==> !has_structure_port(selected.template.signature_model().inputs@)
                && !has_structure_port(selected.template.signature_model().outputs@),
            layouts.is_none() ==> (forall|i: int| 0 <= i < selected.children@.len() ==>
                ((#[trigger] selected.children@[i]).template matches Some(template) ==>
                    !has_structure_port(template.signature_model().inputs@) && !has_structure_port(template.signature_model().outputs@))),
    {
        if preferred.is_some() {
            preferred
        } else if has_structure_port(selected.template.signature_model().inputs@)
            || has_structure_port(selected.template.signature_model().outputs@) {
            let target = plan.position_model(selected.group._order@.0)->Some_0;
            Some(self.source_template_structure_layout(target, caller.2, selected.template))
        } else if exists|i: int| 0 <= i < selected.children@.len() && (
            (#[trigger] selected.children@[i]).template matches Some(template)
            && (has_structure_port(template.signature_model().inputs@) || has_structure_port(template.signature_model().outputs@))) {
            let i = choose|i: int| 0 <= i < selected.children@.len() && (
                (#[trigger] selected.children@[i]).template matches Some(template)
                && (has_structure_port(template.signature_model().inputs@) || has_structure_port(template.signature_model().outputs@)));
            let child = selected.children@[i];
            reveal(UseAliases::resolved_expression_call_matches);
            let target = plan.position_model(child.child._rank@->Some_0)->Some_0;
            Some(self.source_template_structure_layout(target, caller.2, child.template->Some_0))
        } else {
            None
        }
    }

    /// 配線から得た値を、根が参照する先行定義と呼び出し式のソース評価に結び付ける。
    pub(super) proof fn source_nested_call_from_wiring(
        &self, context: &SourceFunc, plan: &FunctionExpansionOrder, rank: int,
        prior: &FunctionTemplates, table: &FunctionTemplates, prepared: &PreparedExpansionBody,
        index: int, selected: &ResolvedTemplateCall, preferred: Option<StructureLayouts>,
        inputs: Seq<Seq<bool>>, assigned: Seq<Seq<bool>>, values: EvaluatedNestedCall, site: SourceCallEvaluation,
    ) -> (nested: NestedSourceArguments<'p, 'a>)
        requires
            self.can_resolve(),
            self.function_expansion_evidence(Ok(*plan)),
            0 <= rank < plan.order_model().len(),
            plan.position_model(rank) == Some((context.file, context.entry)),
            ({
                let project = self.targets.project_model();
                &&& context.file < project.sources_model().len() && context.file < project.circuits_model().len()
                &&& *context.source == project.sources_model()[context.file as int]
                &&& *context.parsed == project.circuits_model()[context.file as int]
            }),
            preferred matches Some(layouts) ==> self.structure_types_match(context.limit, Ok(layouts)),
            self.prepared_expansion_body_matches(*plan, context.file, context.entry, context.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*context.wiring),
            assigned.len() == context.wiring.drivers.definitions@.len(),
            self.resolved_template_call_matches(plan, (context.file, context.entry, context.limit), prepared, index, *selected),
            self.resolved_expression_calls_match(plan, prior, context.limit, selected.group.postorder,
                prepared.projections.call_arguments.arguments@, selected.children@),
            evaluated_nested_call_matches(self, (context.file, context.entry, context.limit), prepared, index,
                selected, inputs, assigned, values),
            prior.next_rank() == rank,
            prior.slots_model().len() == table.slots_model().len(),
            forall|i: int| 0 <= i < rank ==> {
                let vertex = #[trigger] plan.order_model()[i];
                prior.slots_model()[vertex as int] == table.slots_model()[vertex as int]
            },
            site.definition == prepared.projections.calls@[index].definition,
            site.outputs == selected.group.outputs,
            site.signature == selected.group._signature@,
            site.widths == selected.template.input_widths_model() && site.arguments == values.root.ports,
        ensures
            self.source_nested_arguments_match(
                &source_expression_scope(context, plan, rank, Self::template_evaluations(plan, table),
                    SourceCallEvaluation { nested: Some(nested), ..site }, &nested, inputs, assigned),
                site.signature, site.widths, site.arguments, nested.children),
    {
        let caller = (context.file, context.entry, context.limit);
        let layouts = self.source_nested_call_layout(plan, prior, caller, prepared, index, selected, preferred);
        let layout_ref = match &layouts { Some(table) => Some(table), None => None };
        self.prepared_call_matches_source_site(plan, caller, prepared, index);
        self.expansion_callee_template_evidence(*plan, caller, prepared, index);
        let root = prepared.projections.calls@[index];
        let first = site.outputs.start as int;
        self.source_function_call_site_evidence(caller, context.wiring, first, site.definition, site.signature,
            site.outputs, (root.target_file, root.target_entry));
        self.checked_wiring_is_func(context.file, context.entry, context.limit, *context.wiring);
        let drivers = context.wiring.drivers.definitions@;
        assert forall|i: int| 0 <= i < drivers.len() implies
            (i < first) == ((#[trigger] drivers[i]).definition < site.definition) by {
            if i < first {
                assert(drivers[i].definition < drivers[first].definition
                    || (drivers[i].definition == drivers[first].definition && drivers[i].result_index < drivers[first].result_index));
            } else if first < i {
                assert(drivers[first].definition < drivers[i].definition
                    || (drivers[first].definition == drivers[i].definition && drivers[first].result_index < drivers[i].result_index));
            }
        };
        let scope = SourceExpressionScope { context, plan, rank, derivation: Self::template_evaluations(plan, table),
            definition: site.definition, typed: prepared.typed, layouts: layout_ref, inputs, prior: assigned.take(first) };
        let children = self.source_children_from_wiring(&scope, prior, table, prepared, index, selected, assigned, values);
        NestedSourceArguments { typed: prepared.typed, layouts, children }
    }

    spec fn source_expression_atom_type(
        &self, scope: &SourceExpressionScope, form: usize, expected: ResolvedPortType,
    ) -> bool {
        let context = scope.context;
        let frame = context.parsed.entry_ranges@[context.entry as int];
        let row = context.parsed.definitions@[scope.definition as int];
        let forms = context.parsed.syntax.forms@;
        &&& form < forms.len() && forms[form as int] is Atom
        &&& if forms[form as int]->Atom_kind is Name {
            exists|i: int| row.signals.start <= i < row.signals.end <= context.parsed.signals@.len()
                && (#[trigger] context.parsed.signals@[i]) == form
                && 0 <= i - frame.signals.start < context.wiring.signals@.len()
                && (signal_type_at(context.wiring, scope.typed.types@,
                    context.wiring.signals@[i - frame.signals.start].driver) matches Some(known)
                    && port_types_equal(known.ty, expected))
        } else { expected is Bits }
    }

    spec fn source_expression_argument_matches(
        &self, scope: &SourceExpressionScope, call: TypedFuncCall, port: int, form: usize,
        width: u64, value: Seq<bool>, children: Map<usize, SourceExpressionCall>,
    ) -> bool {
        let context = scope.context;
        let forms = context.parsed.syntax.forms@;
        let expected = match call.signature {
            FuncCallSignature::Nor => ResolvedPortType::Bits(1),
            FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
        };
        &&& call.call.call.form < form < forms.len()
        &&& value.len() == width
        &&& match forms[form as int] {
            Form::Atom { .. } => {
                &&& self.source_expression_atom_type(scope, form, expected)
                &&& source_call_argument_value(context.source, context.parsed, context.wiring, context.entry,
                    scope.definition, form, context.limit, scope.inputs, scope.prior, width, value)
            },
            Form::List { .. } => {
                &&& children.contains_key(form)
                &&& source_expression_output_type(children[form].signature) matches Some(output)
                    && port_types_equal(output, expected)
                &&& value == children[form].result
            },
        }
    }

    /// 実引数を元の出現順に評価する。リストの引数は同じフォームに対応する子の出力を読む。
    spec fn source_expression_arguments_match(
        &self, scope: &SourceExpressionScope, call: TypedFuncCall,
        widths: Seq<u64>, values: Seq<Seq<bool>>, children: Map<usize, SourceExpressionCall>,
    ) -> bool {
        let context = scope.context;
        let forms = context.parsed.syntax.forms@;
        &&& match call.signature {
            FuncCallSignature::Nor => widths == seq![1u64, 1u64],
            FuncCallSignature::Function(ports) => self.port_widths_match(ports.inputs@, widths, scope.layouts),
        }
        &&& exists|positions: Seq<usize>| #[trigger] call_argument_positions(forms, call.call.call, positions)
            && positions.len() == widths.len() == values.len()
            && forall|port: int| 0 <= port < positions.len() ==>
                self.source_expression_argument_matches(scope, call, port, #[trigger] positions[port],
                    widths[port], values[port], children)
    }

    proof fn source_expression_argument_positions(
        &self, scope: &SourceExpressionScope, call: TypedFuncCall, widths: Seq<u64>,
        values: Seq<Seq<bool>>, children: Map<usize, SourceExpressionCall>,
    ) -> (positions: Seq<usize>)
        requires self.source_expression_arguments_match(scope, call, widths, values, children),
        ensures
            call_argument_positions(scope.context.parsed.syntax.forms@, call.call.call, positions),
            positions.len() == widths.len() == values.len(),
            forall|port: int| 0 <= port < positions.len() ==>
                self.source_expression_argument_matches(scope, call, port, #[trigger] positions[port],
                    widths[port], values[port], children),
    {
        choose|positions: Seq<usize>| #[trigger] call_argument_positions(scope.context.parsed.syntax.forms@, call.call.call, positions)
            && positions.len() == widths.len() == values.len()
            && forall|port: int| 0 <= port < positions.len() ==>
                self.source_expression_argument_matches(scope, call, port, #[trigger] positions[port],
                    widths[port], values[port], children)
    }

    /// 子の出力は、依存先の参照評価または基底 NOR の真理値から定まる。
    spec fn source_expression_call_evaluates(
        &self, scope: &SourceExpressionScope, form: usize, child: SourceExpressionCall,
        children: Map<usize, SourceExpressionCall>,
    ) -> bool {
        let context = scope.context;
        let entry = context.parsed.entry_ranges@[context.entry as int];
        let definition = (scope.definition - entry.definitions.start) as usize;
        let signature = child.signature;
        &&& signature.call.call.form == form
        &&& self.func_call_form_reference(context.file, context.entry, definition, form, child.reference)
        &&& self.func_call_signature_evidence(context.file, context.entry, definition, child.reference,
            context.limit, Ok(Some(signature)))
        &&& source_expression_output_type(signature) matches Some(output)
            && 0 < child.result.len() <= u64::MAX
            && self.port_width_matches(output, child.result.len() as u64, scope.layouts)
        &&& self.source_expression_arguments_match(scope, signature, child.widths, child.arguments, children)
        &&& self.source_expression_result_matches(scope, child)
    }

    spec fn source_expression_result_matches(&self, scope: &SourceExpressionScope, child: SourceExpressionCall) -> bool {
        let signature = child.signature;
        match (signature.call.target, signature.signature, child.callee_rank) {
            (FuncCallTarget::Nor, FuncCallSignature::Nor, None) =>
                child.arguments.len() == 2 && child.arguments[0].len() == 1 && child.arguments[1].len() == 1
                && child.result == seq![!(child.arguments[0][0] || child.arguments[1][0])],
            (FuncCallTarget::Function { file, entry, .. }, FuncCallSignature::Function(_), Some(rank)) =>
                0 <= rank < scope.rank && scope.plan.position_model(rank) == Some((file, entry))
                && scope.derivation.contains(SourceInvocation {
                    rank, inputs: child.arguments, outputs: seq![child.result],
                }),
            _ => false,
        }
    }

    spec fn source_child_projection_matches(
        &self, scope: &SourceExpressionScope, reference_start: usize, selected: ResolvedExpressionCall,
        values: EvaluatedCallBits, child: SourceExpressionCall,
    ) -> bool {
        &&& child.signature == selected.child._signature@
        &&& child.callee_rank == selected.child._rank@
        &&& child.reference + reference_start == selected.child.reference
        &&& child.arguments == values.ports && child.result == values.output
        &&& child.widths.len() == child.arguments.len() == selected.arguments@.len()
        &&& forall|port: int| 0 <= port < child.widths.len() ==>
            (#[trigger] child.widths[port]) == expression_input_width(selected, port)
        &&& match child.signature.signature {
            FuncCallSignature::Nor => child.widths == seq![1u64, 1u64],
            FuncCallSignature::Function(ports) => self.port_widths_match(ports.inputs@, child.widths, scope.layouts),
        }
        &&& source_expression_output_type(child.signature) matches Some(ty)
            && 0 < child.result.len() <= u64::MAX
            && self.port_width_matches(ty, child.result.len() as u64, scope.layouts)
        &&& self.source_expression_result_matches(scope, child)
    }

    /// 一つの子の配線評価を、ソース側で参照する署名と値へ写す。
    proof fn project_source_child_values(
        &self, scope: &SourceExpressionScope, prior: &FunctionTemplates, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, group_index: int, selected: &ResolvedTemplateCall,
        assigned: Seq<Seq<bool>>, values: EvaluatedNestedCall, child_index: int,
    ) -> (child: SourceExpressionCall<'p, 'a>)
        requires
            self.source_expression_scope_matches(scope),
            self.prepared_expansion_body_matches(*scope.plan, scope.context.file, scope.context.entry, scope.context.limit, prepared),
            0 <= group_index < prepared.calls@.len(),
            prepared.projections.calls@[group_index].definition == scope.definition,
            self.resolved_template_call_matches(scope.plan, (scope.context.file, scope.context.entry, scope.context.limit),
                prepared, group_index, *selected),
            self.resolved_expression_calls_match(scope.plan, prior, scope.context.limit, selected.group.postorder,
                prepared.projections.call_arguments.arguments@, selected.children@),
            assigned.take(selected.group.outputs.start as int) == scope.prior,
            evaluated_nested_call_matches(self, (scope.context.file, scope.context.entry, scope.context.limit),
                prepared, group_index, selected, scope.inputs, assigned, values),
            0 <= child_index < values.children.len(),
            scope.derivation == Self::template_evaluations(scope.plan, table),
            prior.next_rank() == scope.rank,
            prior.slots_model().len() == table.slots_model().len(),
            forall|i: int| 0 <= i < scope.rank ==> {
                let vertex = #[trigger] scope.plan.order_model()[i];
                prior.slots_model()[vertex as int] == table.slots_model()[vertex as int]
            },
            scope.layouts.is_none() ==> (selected.children@[child_index].template matches Some(template) ==>
                !has_structure_port(template.signature_model().inputs@) && !has_structure_port(template.signature_model().outputs@)),
        ensures self.source_child_projection_matches(scope, selected.group.references.start, selected.children@[child_index],
            values.children[child_index], child),
    {
        reveal(UseAliases::source_expression_scope_matches);
        let context = scope.context;
        let caller = (context.file, context.entry, context.limit);
        let row = selected.children@[child_index];
        let value = values.children[child_index];
        self.expansion_child_template_evidence(*scope.plan, caller, prepared, group_index, child_index);
        if row.template.is_some() {
            self.source_prepared_function_child(scope, prior, table, prepared, group_index, child_index, row, value.input, value.output)
        } else {
            reveal(UseAliases::resolved_expression_call_matches);
            SourceExpressionCall { reference: (row.child.reference - selected.group.references.start) as usize,
                signature: row.child._signature@, callee_rank: None, widths: seq![1u64, 1u64],
                arguments: value.ports, result: value.output }
        }
    }

    /// 後順の配線評価をフォーム添字で引ける表にし、各項目がソースの評価規則を満たすことを示す。
    proof fn source_children_from_wiring(
        &self, scope: &SourceExpressionScope, prior: &FunctionTemplates, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, group_index: int, selected: &ResolvedTemplateCall,
        assigned: Seq<Seq<bool>>, values: EvaluatedNestedCall,
    ) -> (children: Map<usize, SourceExpressionCall<'p, 'a>>)
        requires
            self.source_expression_scope_matches(scope),
            self.prepared_expansion_body_matches(*scope.plan, scope.context.file, scope.context.entry, scope.context.limit, prepared),
            prepared.typed == scope.typed,
            0 <= group_index < prepared.calls@.len(),
            prepared.projections.calls@[group_index].definition == scope.definition,
            self.resolved_template_call_matches(scope.plan, (scope.context.file, scope.context.entry, scope.context.limit),
                prepared, group_index, *selected),
            self.resolved_expression_calls_match(scope.plan, prior, scope.context.limit, selected.group.postorder,
                prepared.projections.call_arguments.arguments@, selected.children@),
            assigned.take(selected.group.outputs.start as int) == scope.prior,
            evaluated_nested_call_matches(self, (scope.context.file, scope.context.entry, scope.context.limit),
                prepared, group_index, selected, scope.inputs, assigned, values),
            scope.derivation == Self::template_evaluations(scope.plan, table),
            prior.next_rank() == scope.rank,
            prior.slots_model().len() == table.slots_model().len(),
            forall|i: int| 0 <= i < scope.rank ==> {
                let vertex = #[trigger] scope.plan.order_model()[i];
                prior.slots_model()[vertex as int] == table.slots_model()[vertex as int]
            },
            scope.layouts.is_none() ==> !has_structure_port(selected.template.signature_model().inputs@)
                && !has_structure_port(selected.template.signature_model().outputs@),
            scope.layouts.is_none() ==> (forall|i: int| 0 <= i < selected.children@.len() ==>
                ((#[trigger] selected.children@[i]).template matches Some(template) ==>
                    !has_structure_port(template.signature_model().inputs@) && !has_structure_port(template.signature_model().outputs@))),
        ensures
            forall|i: int| 0 <= i < values.children.len() ==> {
                let item = (#[trigger] selected.children@[i]).child;
                let form = item._signature@.call.call.form;
                &&& children.contains_key(form)
                &&& children[form].signature == item._signature@
                &&& children[form].result == values.children[i].output
            },
            forall|form: usize| #[trigger] children.contains_key(form) ==> {
                let row = scope.context.parsed.definitions@[scope.definition as int];
                &&& row.expression.start < form < row.expression.end
                &&& self.source_expression_call_evaluates(scope, form, children[form], children)
            },
            self.source_nested_arguments_match(scope, selected.group._signature@,
                selected.template.input_widths_model(), values.root.ports, children),
    {
        reveal(UseAliases::source_expression_scope_matches);
        let context = scope.context;
        let caller = (context.file, context.entry, context.limit);
        let group = selected.group;
        let postorder = group.postorder->Some_0@;
        let arguments = prepared.projections.call_arguments.arguments@;
        let start = group.references.start;
        assert forall|i: int| #![trigger values.children[i]] 0 <= i < values.children.len() implies exists|child: SourceExpressionCall|
            #[trigger] self.source_child_projection_matches(scope, start, selected.children@[i],
                values.children[i], child) by {
            self.project_source_child_values(scope, prior, table, prepared, group_index, selected, assigned, values, i);
        };
        let projected = Seq::new(postorder.len(), |i: int| choose|child: SourceExpressionCall|
            #[trigger] self.source_child_projection_matches(scope, start, selected.children@[i], values.children[i], child));
        assert forall|i: int| 0 <= i < postorder.len() implies
            self.source_child_projection_matches(scope, start, selected.children@[i], values.children[i], #[trigger] projected[i]) by {
            assert(i < values.children.len());
            assert(values.children[i].ports.len() == selected.children@[i].arguments@.len());
            assert(exists|child: SourceExpressionCall| #[trigger] self.source_child_projection_matches(
                scope, start, selected.children@[i], values.children[i], child));
        };
        let forms = Seq::new(postorder.len(), |i: int| postorder[i]._signature@.call.call.form);
        forms.to_set_ensures();
        let domain = forms.to_set();
        let positions = |form: usize| choose|i: int| 0 <= i < forms.len() && (#[trigger] forms[i]) == form;
        let children = Map::new(domain, |form: usize| projected[positions(form)]);
        vstd::map::lemma_map_new_domain(domain, |form: usize| projected[positions(form)]);
        assert forall|i: int| 0 <= i < postorder.len() implies {
            let item = #[trigger] postorder[i];
            let form = item._signature@.call.call.form;
            &&& children.contains_key(form)
            &&& children[form] == projected[i]
        } by {
            let form = postorder[i]._signature@.call.call.form;
            assert(forms[i] == form);
            assert(forms.contains(form));
            assert(domain.contains(form));
            let key = positions(form);
            self.expansion_children_at_same_form(*scope.plan, caller, prepared, group_index, i, key);
            vstd::map::lemma_map_new_index(domain, |form: usize| projected[positions(form)], form);
        };
        assert forall|i: int| 0 <= i < postorder.len() implies {
            let item = (#[trigger] selected.children@[i]).child;
            let form = item._signature@.call.call.form;
            &&& children.contains_key(form)
            &&& children[form].signature == item._signature@
            &&& children[form].result == values.children[i].output
        } by {
            reveal(UseAliases::resolved_expression_call_matches);
            assert(postorder[i] == *selected.children@[i].child);
            assert(children[postorder[i]._signature@.call.call.form] == projected[i]);
        };
        assert forall|form: usize| #[trigger] children.contains_key(form) implies {
            let row = scope.context.parsed.definitions@[scope.definition as int];
            &&& row.expression.start < form < row.expression.end
            &&& self.source_expression_call_evaluates(scope, form, children[form], children)
        } by {
            assert(forms.contains(form));
            let i = positions(form);
            let item = postorder[i];
            let expression = selected.children@[i];
            let child = projected[i];
            assert(form == item._signature@.call.call.form && children[form] == child);
            reveal(UseAliases::resolved_expression_call_matches);
            assert(item == *expression.child);
            self.expansion_child_template_evidence(*scope.plan, caller, prepared, group_index, i);
            assert forall|port: int| 0 <= port < child.arguments.len() implies {
                let argument = #[trigger] arguments[item.arguments.start + port];
                &&& child.arguments[port].len() == child.widths[port]
                &&& if argument.source.has_direct_wires() {
                    source_call_argument_value(context.source, context.parsed, context.wiring, context.entry,
                        scope.definition, argument.form, context.limit, scope.inputs, scope.prior,
                        child.widths[port], child.arguments[port])
                } else {
                    &&& argument.source is NestedCall
                    &&& children.contains_key(argument.form)
                    &&& child.arguments[port] == children[argument.form].result
                }
            } by {
                let argument = expression.arguments@[port];
                assert(argument == arguments[item.arguments.start + port]);
                assert(child.arguments == values.children[i].ports);
                if !argument.source.has_direct_wires() {
                    let earlier = choose|producer: int| 0 <= producer < i
                        && (#[trigger] selected.children@[producer]).child.reference == start + argument.source->NestedCall_0
                        && selected.children@[producer].child._signature@.call.call.form == argument.form
                        && child.arguments[port] == values.children[producer].output;
                    assert(children[argument.form].result == values.children[earlier].output);
                }
            };
            assert forall|j: int| 0 <= j < i implies {
                let earlier = #[trigger] postorder[j];
                let form = earlier._signature@.call.call.form;
                &&& children.contains_key(form)
                &&& children[form].signature == earlier._signature@
            } by {
                assert(*selected.children@[j].child == postorder[j]);
            };
            self.source_prepared_child_evaluation(scope, prepared, group_index, i, child, children);
        };
        self.source_root_arguments_from_wiring(scope, prior, prepared, group_index, selected, assigned, values, children);
        children
    }

    /// 根の実引数を元の順序で読み、入れ子の引数は同じフォームの評価表から得る。
    proof fn source_root_arguments_from_wiring(
        &self, scope: &SourceExpressionScope, prior: &FunctionTemplates, prepared: &PreparedExpansionBody, group_index: int,
        selected: &ResolvedTemplateCall, assigned: Seq<Seq<bool>>, values: EvaluatedNestedCall,
        children: Map<usize, SourceExpressionCall>,
    )
        requires
            self.source_expression_scope_matches(scope),
            self.prepared_expansion_body_matches(*scope.plan, scope.context.file, scope.context.entry, scope.context.limit, prepared),
            prepared.typed == scope.typed,
            0 <= group_index < prepared.calls@.len(),
            prepared.projections.calls@[group_index].definition == scope.definition,
            self.resolved_template_call_matches(scope.plan, (scope.context.file, scope.context.entry, scope.context.limit),
                prepared, group_index, *selected),
            self.resolved_expression_calls_match(scope.plan, prior, scope.context.limit, selected.group.postorder,
                prepared.projections.call_arguments.arguments@, selected.children@),
            assigned.take(selected.group.outputs.start as int) == scope.prior,
            evaluated_nested_call_matches(self, (scope.context.file, scope.context.entry, scope.context.limit),
                prepared, group_index, selected, scope.inputs, assigned, values),
            scope.layouts.is_none() ==> !has_structure_port(selected.template.signature_model().inputs@)
                && !has_structure_port(selected.template.signature_model().outputs@),
            forall|i: int| 0 <= i < values.children.len() ==> {
                let item = (#[trigger] selected.children@[i]).child;
                let form = item._signature@.call.call.form;
                &&& children.contains_key(form)
                &&& children[form].signature == item._signature@
                &&& children[form].result == values.children[i].output
            },
            forall|form: usize| #[trigger] children.contains_key(form) ==> {
                let row = scope.context.parsed.definitions@[scope.definition as int];
                &&& row.expression.start < form < row.expression.end
                &&& self.source_expression_call_evaluates(scope, form, children[form], children)
            },
        ensures self.source_nested_arguments_match(scope, selected.group._signature@,
            selected.template.input_widths_model(), values.root.ports, children),
    {
        reveal(UseAliases::source_expression_scope_matches);
        reveal(UseAliases::source_nested_arguments_match);
        let context = scope.context;
        let caller = (context.file, context.entry, context.limit);
        let group = *selected.group;
        let projections = &prepared.projections.call_arguments;
        let range = projections.ranges@[group_index];
        let root = prepared.projections.calls@[group_index];
        let signature = group._signature@;
        let template = selected.template;
        let widths = template.input_widths_model();
        let ports = values.root.ports;
        let forms = context.parsed.syntax.forms@;
        let positions = Seq::new(selected.arguments@.len(), |port: int| selected.arguments@[port].form);
        self.targets.parsed_project_model();
        parsed_index_evidence(*context.source, *context.parsed);
        build_definition_scope_evidence(context.source.text, &context.parsed.build_model(),
            context.entry as int, scope.definition as int);
        self.expansion_callee_template_evidence(*scope.plan, caller, prepared, group_index);
        self.expansion_arguments_in_source_order(*scope.plan, caller, scope.typed, context.wiring, root, range, projections, group);
        let target = scope.plan.position_model(group._order@.0)->Some_0;
        self.template_port_evidence(target, context.limit, template);
        self.template_widths_in_caller_layout(template.signature_model(), context.limit, widths,
            template.output_widths_model(), template.structure_layouts_model(), scope.layouts);
        assert(call_argument_positions(forms, signature.call.call, positions));
        assert forall|port: int| 0 <= port < positions.len() implies
            self.source_expression_argument_matches(scope, signature, port, #[trigger] positions[port], widths[port],
                ports[port], children) by {
            let argument = selected.arguments@[port];
            assert(argument == projections.arguments@[range.start + port]);
            self.expansion_argument_evidence(*scope.plan, caller, scope.typed, context.wiring, root, range, projections, group, port);
            call_argument_position_bounds(forms, signature.call.call, positions, port);
            let expected = signature.signature->Function_0.inputs@[port].ty;
            if argument.source.has_direct_wires() {
                assert(self.source_expression_atom_type(scope, argument.form, expected));
            } else {
                assert(argument.source is NestedCall);
                let producer = choose|i: int| 0 <= i < values.children.len()
                    && (#[trigger] selected.children@[i]).child.reference == group.references.start + argument.source->NestedCall_0
                    && selected.children@[i].child._signature@.call.call.form == argument.form
                    && ports[port] == values.children[i].output;
                let item = selected.children@[producer].child;
                assert(children[argument.form].result == values.children[producer].output);
                let postorder = group.postorder->Some_0@;
                assert(prepared_nested_output_matches(postorder, group.references.start, postorder.len() as int, argument, expected));
                let earlier = choose|i: int| 0 <= i < postorder.len() as int
                    && (#[trigger] postorder[i]).reference == group.references.start + argument.source->NestedCall_0
                    && postorder[i]._signature@.call.call.form == argument.form
                    && postorder[i]._signature@.call.target.port_counts().outputs == 1
                    && match source_expression_output_type(postorder[i]._signature@) {
                        Some(output) => port_types_equal(output, expected),
                        None => false,
                    };
                reveal(UseAliases::resolved_expression_call_matches);
                assert(*selected.children@[earlier].child == postorder[earlier]);
                assert(children[argument.form].signature == postorder[earlier]._signature@);
            }
        };
        assert(self.source_expression_arguments_match(scope, signature, widths, ports, children));
    }

    /// 選択した通常関数の配線評価を、先行するソース呼び出しの入出力に対応付ける。
    proof fn source_prepared_function_child(
        &self, scope: &SourceExpressionScope, prior: &FunctionTemplates, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, group_index: int, index: int, selected: ResolvedExpressionCall,
        input: Seq<bool>, output: Seq<bool>,
    ) -> (child: SourceExpressionCall<'p, 'a>)
        requires
            self.source_expression_scope_matches(scope),
            self.prepared_expansion_body_matches(*scope.plan, scope.context.file, scope.context.entry, scope.context.limit, prepared),
            0 <= group_index < prepared.calls@.len(),
            prepared.projections.calls@[group_index].definition == scope.definition,
            ({
                let group = prepared.calls@[group_index];
                &&& group.postorder matches Some(children)
                &&& 0 <= index < children@.len()
                &&& self.resolved_expression_call_matches(scope.plan, prior, scope.context.limit,
                    prepared.projections.call_arguments.arguments@, children@[index], selected)
                &&& expansion_child_reachable(&prepared.calls@[group_index], prepared.projections.call_arguments.arguments@,
                    children@.len() as int, index)
            }),
            scope.derivation == Self::template_evaluations(scope.plan, table),
            prior.next_rank() == scope.rank,
            prior.slots_model().len() == table.slots_model().len(),
            forall|i: int| 0 <= i < scope.rank ==> {
                let vertex = #[trigger] scope.plan.order_model()[i];
                prior.slots_model()[vertex as int] == table.slots_model()[vertex as int]
            },
            selected.template matches Some(template)
                && nor_evaluation(template.circuit_model().netlist_model(), input, output)
                && (scope.layouts.is_none() ==> !has_structure_port(template.signature_model().inputs@)
                    && !has_structure_port(template.signature_model().outputs@)),
        ensures
            child.signature == selected.child._signature@,
            child.callee_rank == selected.child._rank@,
            child.reference + prepared.calls@[group_index].references.start == selected.child.reference,
            child.result == output,
            ({
                let template = selected.template->Some_0;
                let signature = template.signature_model();
                &&& child.widths == template.input_widths_model()
                &&& child.arguments == port_values(template.circuit_model().input_layout_model(), input)
                &&& child.arguments.len() == child.widths.len() == selected.arguments@.len()
                &&& forall|port: int| 0 <= port < child.widths.len() ==>
                    (#[trigger] child.arguments[port]).len() == child.widths[port]
                &&& child.signature.signature matches FuncCallSignature::Function(ports)
                    && ports.inputs@ == signature.inputs@
                    && self.port_widths_match(ports.inputs@, child.widths, scope.layouts)
            }),
            source_expression_output_type(child.signature) matches Some(ty)
                && 0 < output.len() <= u64::MAX && self.port_width_matches(ty, output.len() as u64, scope.layouts),
            self.source_expression_result_matches(scope, child),
    {
        reveal(UseAliases::resolved_expression_call_matches);
        reveal(UseAliases::source_expression_scope_matches);
        let context = scope.context;
        let item = selected.child;
        let group = prepared.calls@[group_index];
        let caller = (context.file, context.entry, context.limit);
        self.expansion_child_template_evidence(*scope.plan, caller, prepared, group_index, index);
        self.expansion_child_single_output(*scope.plan, caller, prepared, group_index, index);
        let template = selected.template->Some_0;
        let rank = item._rank@->Some_0;
        let position = scope.plan.position_model(rank)->Some_0;
        let invocation = Self::prior_template_invocation(scope.plan, prior, table, rank, template, input, output);
        let circuit = template.circuit_model();
        let signature = template.signature_model();
        let inputs = template.input_widths_model();
        let outputs = template.output_widths_model();
        let capacity = template.bit_limit_model();
        self.template_port_evidence(position, context.limit, template);
        self.template_circuit_evidence(position, context.limit, template);
        self.template_widths_in_caller_layout(signature, context.limit, inputs, outputs, template.structure_layouts_model(), scope.layouts);
        let input_layout = circuit.input_layout_model();
        let output_layout = circuit.output_layout_model();
        reveal(nor_evaluation);
        port_bit_layout_size(inputs, capacity, input_layout);
        reveal(port_values);
        assert forall|port: int| 0 <= port < inputs.len() implies
            (#[trigger] invocation.inputs[port]).len() == inputs[port] by {
            port_bit_layout_port(inputs, capacity, *input_layout, port as usize);
        };
        assert(outputs.len() == 1);
        port_bit_layout_port(outputs, capacity, *output_layout, 0);
        assert(preceding_port_bits(outputs, 0) == 0) by { reveal(preceding_port_bits); };
        assert(invocation.outputs[0] =~= output);
        assert(invocation.outputs =~= seq![output]);
        let child = SourceExpressionCall { reference: (item.reference - group.references.start) as usize,
            signature: item._signature@, callee_rank: item._rank@, widths: inputs, arguments: invocation.inputs, result: output };
        assert(self.source_expression_result_matches(scope, child));
        child
    }

    /// 配線から読んだ一つの子の入出力値を、対応する厳格構文木の評価に結び付ける。
    proof fn source_prepared_child_evaluation(
        &self, scope: &SourceExpressionScope, prepared: &PreparedExpansionBody, group_index: int, index: int,
        child: SourceExpressionCall, children: Map<usize, SourceExpressionCall>,
    )
        requires
            self.source_expression_scope_matches(scope),
            self.prepared_expansion_body_matches(*scope.plan, scope.context.file, scope.context.entry, scope.context.limit, prepared),
            prepared.typed == scope.typed,
            0 <= group_index < prepared.calls@.len(),
            prepared.projections.calls@[group_index].definition == scope.definition,
            ({
                let group = prepared.calls@[group_index];
                let arguments = prepared.projections.call_arguments.arguments@;
                let context = scope.context;
                let frame = context.parsed.entry_ranges@[context.entry as int];
                let local = (scope.definition - frame.definitions.start) as usize;
                &&& group.postorder matches Some(postorder)
                &&& 0 <= index < postorder@.len()
                &&& {
                    let item = postorder@[index];
                    let range = item.arguments;
                    &&& range.start <= range.end <= arguments.len()
                    &&& child.signature == item._signature@
                    &&& child.callee_rank == item._rank@
                    &&& child.reference + group.references.start == item.reference
                    &&& self.func_call_form_reference(context.file, context.entry, local,
                        child.signature.call.call.form, child.reference)
                    &&& self.func_call_signature_evidence(context.file, context.entry, local, child.reference,
                        context.limit, Ok(Some(child.signature)))
                    &&& child.arguments.len() == child.widths.len() == range.end - range.start
                    &&& forall|port: int| 0 <= port < child.arguments.len() ==> {
                        let argument = #[trigger] arguments[range.start + port];
                        &&& child.arguments[port].len() == child.widths[port]
                        &&& if argument.source.has_direct_wires() {
                            source_call_argument_value(context.source, context.parsed, context.wiring, context.entry,
                                scope.definition, argument.form, context.limit, scope.inputs, scope.prior,
                                child.widths[port], child.arguments[port])
                        } else {
                            &&& argument.source is NestedCall
                            &&& children.contains_key(argument.form)
                            &&& child.arguments[port] == children[argument.form].result
                        }
                    }
                }
                &&& forall|i: int| 0 <= i < index ==> {
                    let earlier = #[trigger] postorder@[i];
                    let form = earlier._signature@.call.call.form;
                    &&& children.contains_key(form)
                    &&& children[form].signature == earlier._signature@
                }
            }),
            match child.signature.signature {
                FuncCallSignature::Nor => child.widths == seq![1u64, 1u64],
                FuncCallSignature::Function(ports) => self.port_widths_match(ports.inputs@, child.widths, scope.layouts),
            },
            source_expression_output_type(child.signature) matches Some(output)
                && 0 < child.result.len() <= u64::MAX
                && self.port_width_matches(output, child.result.len() as u64, scope.layouts),
            self.source_expression_result_matches(scope, child),
        ensures self.source_expression_call_evaluates(scope, child.signature.call.call.form, child, children),
    {
        let context = scope.context;
        let caller = (context.file, context.entry, context.limit);
        let group = prepared.calls@[group_index];
        let postorder = group.postorder->Some_0@;
        let range = postorder[index].arguments;
        let arguments = prepared.projections.call_arguments.arguments@;
        let projected = arguments.subrange(range.start as int, range.end as int);
        let positions = Seq::new(projected.len(), |port: int| projected[port].form);
        let forms = context.parsed.syntax.forms@;
        let call = child.signature;
        self.expansion_child_arguments_in_source_order(*scope.plan, caller, prepared, group_index, index);
        assert forall|port: int| 0 <= port < positions.len() implies
            self.source_expression_argument_matches(scope, call, port, #[trigger] positions[port],
                child.widths[port], child.arguments[port], children) by {
            let argument = projected[port];
            assert(argument == arguments[range.start + port]);
            self.expansion_child_argument_evidence(*scope.plan, caller, prepared, group_index, index, port);
            call_argument_position_bounds(forms, call.call.call, positions, port);
            let expected = match call.signature {
                FuncCallSignature::Nor => ResolvedPortType::Bits(1),
                FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
            };
            match argument.source {
                CallArgumentSource::Driver(_) | CallArgumentSource::Literal(_) => {
                    assert(self.source_expression_atom_type(scope, argument.form, expected));
                },
                CallArgumentSource::NestedCall(reference) => {
                    assert(prepared_nested_output_matches(postorder, group.references.start, index, argument, expected));
                    let i = choose|i: int| 0 <= i < index
                        && (#[trigger] postorder[i]).reference == group.references.start + reference
                        && postorder[i]._signature@.call.call.form == argument.form
                        && match source_expression_output_type(postorder[i]._signature@) {
                            Some(output) => port_types_equal(output, expected),
                            None => false,
                        };
                    assert(children[argument.form].signature == postorder[i]._signature@);
                    assert(forms[argument.form as int] is List);
                },
                CallArgumentSource::Deferred => {},
            }
        };
        assert(self.source_expression_arguments_match(scope, call, child.widths, child.arguments, children));
    }

    /// 元の右辺の根から引数をたどり、各リストの呼び出しをソースの規則で評価する。
    ///
    /// 引数のフォーム添字は呼び出しの添字より大きいため、値を得るために同じ呼び出しへ戻ることはない。
    pub(super) closed spec fn source_nested_arguments_match(
        &self, scope: &SourceExpressionScope, root: TypedFuncCall, widths: Seq<u64>,
        values: Seq<Seq<bool>>, children: Map<usize, SourceExpressionCall>,
    ) -> bool {
        let context = scope.context;
        let row = context.parsed.definitions@[scope.definition as int];
        let frame = context.parsed.entry_ranges@[context.entry as int].definitions;
        &&& self.source_expression_scope_matches(scope)
        &&& root.call.call.form == row.expression.start
        &&& self.func_call_signature_evidence(context.file, context.entry, (scope.definition - frame.start) as usize,
            0, context.limit, Ok(Some(root)))
        &&& self.source_expression_arguments_match(scope, root, widths, values, children)
        &&& forall|form: usize| #[trigger] children.contains_key(form) ==>
            root.call.call.form < form < row.expression.end
            && self.source_expression_call_evaluates(scope, form, children[form], children)
    }

    /// 各引数のビット列は、呼び出し先の対応するポート幅を持つ。
    pub(super) proof fn source_nested_argument_lengths(
        &self, scope: &SourceExpressionScope, root: TypedFuncCall, widths: Seq<u64>,
        values: Seq<Seq<bool>>, children: Map<usize, SourceExpressionCall>,
    )
        requires self.source_nested_arguments_match(scope, root, widths, values, children),
        ensures values.len() == widths.len(),
            forall|i: int| 0 <= i < values.len() ==> (#[trigger] values[i]).len() == widths[i],
    {
        let positions = self.source_expression_argument_positions(scope, root, widths, values, children);
        assert forall|i: int| 0 <= i < values.len() implies (#[trigger] values[i]).len() == widths[i] by {
            assert(self.source_expression_argument_matches(scope, root, i, positions[i], widths[i], values[i], children));
        };
    }

    /// 型検査済みの原子だけを渡す場合、従来の引数評価を子が空の評価として使える。
    proof fn source_flat_arguments_match_nested(
        &self, scope: &SourceExpressionScope, root: TypedFuncCall, widths: Seq<u64>, values: Seq<Seq<bool>>,
    )
        requires
            self.source_expression_scope_matches(scope),
            self.func_call_signature_evidence(scope.context.file, scope.context.entry,
                (scope.definition - scope.context.parsed.entry_ranges@[scope.context.entry as int].definitions.start) as usize,
                0, scope.context.limit, Ok(Some(root))),
            match root.signature {
                FuncCallSignature::Nor => widths == seq![1u64, 1u64],
                FuncCallSignature::Function(ports) => self.port_widths_match(ports.inputs@, widths, scope.layouts),
            },
            source_call_arguments_match(scope.context.source, scope.context.parsed, scope.context.wiring,
                scope.context.entry, scope.definition, root.call.call, scope.context.limit, scope.inputs, scope.prior,
                widths, values),
            forall|positions: Seq<usize>, port: int| #[trigger] call_argument_positions(
                scope.context.parsed.syntax.forms@, root.call.call, positions) && 0 <= port < positions.len() ==>
                self.source_expression_atom_type(scope, #[trigger] positions[port], match root.signature {
                    FuncCallSignature::Nor => ResolvedPortType::Bits(1),
                    FuncCallSignature::Function(ports) => ports.inputs@[port].ty,
                }),
        ensures self.source_nested_arguments_match(scope, root, widths, values, Map::empty()),
    {
        let context = scope.context;
        let forms = context.parsed.syntax.forms@;
        let call = root.call.call;
        let positions = choose|positions: Seq<usize>| #[trigger] call_argument_positions(forms, call, positions)
            && positions.len() == values.len() == widths.len()
            && forall|port: int| 0 <= port < positions.len() ==>
                source_call_argument_value(context.source, context.parsed, context.wiring, context.entry,
                    scope.definition, #[trigger] positions[port], context.limit, scope.inputs, scope.prior,
                    widths[port], values[port]);
        reveal(source_call_argument_value);
        assert forall|port: int| 0 <= port < positions.len() implies
            self.source_expression_argument_matches(scope, root, port, #[trigger] positions[port],
                widths[port], values[port], Map::empty()) by {
            call_argument_position_bounds(forms, call, positions, port);
        };
    }

    /// 同じソースの引数値は、依存順位の小さい関数の評価が一意なら、子の評価表の選び方によらない。
    proof fn source_expression_arguments_agree(
        &self, left: &SourceExpressionScope, right: &SourceExpressionScope,
        a: (TypedFuncCall, Seq<Seq<bool>>, Map<usize, SourceExpressionCall>),
        b: (TypedFuncCall, Seq<Seq<bool>>, Map<usize, SourceExpressionCall>),
        widths: Seq<u64>,
    )
        requires
            self.source_expression_scope_matches(left), self.source_expression_scope_matches(right),
            same_source_bindings(left.context, right.context),
            left.plan == right.plan && left.rank == right.rank && left.definition == right.definition,
            left.inputs == right.inputs && left.prior == right.prior,
            a.0.call.call == b.0.call.call,
            self.source_expression_arguments_match(left, a.0, widths, a.1, a.2),
            self.source_expression_arguments_match(right, b.0, widths, b.1, b.2),
            forall|form: usize| #[trigger] a.2.contains_key(form) ==>
                self.source_expression_call_evaluates(left, form, a.2[form], a.2),
            forall|form: usize| #[trigger] b.2.contains_key(form) ==>
                self.source_expression_call_evaluates(right, form, b.2[form], b.2),
            forall|x: SourceInvocation, y: SourceInvocation|
                #[trigger] left.derivation.contains(x) && #[trigger] right.derivation.contains(y)
                && 0 <= x.rank == y.rank < left.rank && x.inputs == y.inputs ==> x.outputs == y.outputs,
        ensures a.1 == b.1,
        decreases left.context.parsed.syntax.forms@.len() - a.0.call.call.form,
    {
        let context = left.context;
        let forms = context.parsed.syntax.forms@;
        self.checked_wiring_is_func(context.file, context.entry, context.limit, *context.wiring);
        self.targets.parsed_project_model();
        let positions_a = self.source_expression_argument_positions(left, a.0, widths, a.1, a.2);
        let positions_b = self.source_expression_argument_positions(right, b.0, widths, b.1, b.2);
        call_argument_positions_agree(forms, a.0.call.call, positions_a, positions_b);
        assert forall|port: int| 0 <= port < a.1.len() implies #[trigger] a.1[port] == b.1[port] by {
            let form = positions_a[port];
            assert(form == positions_b[port]);
            assert(self.source_expression_argument_matches(left, a.0, port, form, widths[port], a.1[port], a.2));
            assert(self.source_expression_argument_matches(right, b.0, port, form, widths[port], b.1[port], b.2));
            if forms[form as int] is Atom {
                source_call_argument_values_agree(context.source, context.parsed, context.wiring, right.context.wiring,
                    context.entry, left.definition, form, context.limit, left.inputs, left.prior, widths[port], a.1[port], b.1[port]);
            } else {
                let x = a.2[form];
                let y = b.2[form];
                assert(self.source_expression_call_evaluates(left, form, x, a.2));
                assert(self.source_expression_call_evaluates(right, form, y, b.2));
                let parsed = context.parsed;
                let row = parsed.definitions@[left.definition as int];
                let frame = parsed.entry_ranges@[context.entry as int].definitions;
                let local = (left.definition - frame.start) as usize;
                parsed_index_evidence(*context.source, *parsed);
                build_definition_scope_evidence(context.source.text, &parsed.build_model(), context.entry as int, left.definition as int);
                vstd::std_specs::vec::axiom_spec_len(&parsed.syntax.forms);
                let first = (row.references.start + x.reference) as usize;
                let second = (row.references.start + y.reference) as usize;
                definition_reference_form_unique(context.source.text, forms, parsed.references@, row, first, second);
                assert(x.reference == y.reference);
                self.successful_call_signatures_agree(context.file, context.entry, local, x.reference, context.limit, x.signature, y.signature);
                match (x.signature.signature, y.signature.signature) {
                    (FuncCallSignature::Nor, FuncCallSignature::Nor) => {},
                    (FuncCallSignature::Function(p), FuncCallSignature::Function(q)) => {
                        assert(p.inputs@ == q.inputs@);
                        assert forall|i: int| 0 <= i < x.widths.len() implies #[trigger] x.widths[i] == y.widths[i] by {
                            let ty = p.inputs@[i].ty;
                            assert(self.port_width_matches(ty, x.widths[i], left.layouts));
                            assert(self.port_width_matches(ty, y.widths[i], right.layouts));
                            if ty is Struct {
                                self.layout_port_widths_agree_across_tables(context.limit, left.layouts->Some_0, right.layouts->Some_0,
                                    ty, x.widths[i] as int, y.widths[i] as int);
                            }
                        };
                    },
                    _ => assert(false),
                }
                assert(x.widths =~= y.widths);
                self.source_expression_arguments_agree(left, right, (x.signature, x.arguments, a.2),
                    (y.signature, y.arguments, b.2), x.widths);
                assert(x.arguments == y.arguments);
                if let FuncCallTarget::Function { file, entry, .. } = x.signature.call.target {
                    let target = (file, entry);
                    let r = x.callee_rank->Some_0;
                    let s = y.callee_rank->Some_0;
                    self.template_rank_from_position(*left.plan, target, r, s);
                    let cx = SourceInvocation { rank: r, inputs: x.arguments, outputs: seq![x.result] };
                    let cy = SourceInvocation { rank: s, inputs: y.arguments, outputs: seq![y.result] };
                    assert(left.derivation.contains(cx) && right.derivation.contains(cy));
                    assert(cx.outputs == cy.outputs);
                    assert(cx.outputs[0] == x.result && cy.outputs[0] == y.result);
                } else {
                    assert(x.signature.signature is Nor && y.signature.signature is Nor);
                    let bit = !(x.arguments[0][0] || x.arguments[1][0]);
                    assert(x.result == seq![bit] && y.result == seq![bit]);
                }
                assert(x.result == y.result);
            }
        };
        assert(a.1 =~= b.1);
    }

    /// 同じ式を原子の規則で評価できるとき、入れ子を許す規則でも同じ値を得る。
    proof fn source_nested_arguments_agree_with_atomic(
        &self, scope: &SourceExpressionScope, other: &FuncWiring, root: TypedFuncCall,
        widths: Seq<u64>, nested: Seq<Seq<bool>>, atomic: Seq<Seq<bool>>, children: Map<usize, SourceExpressionCall>,
    )
        requires
            self.source_nested_arguments_match(scope, root, widths, nested, children),
            self.func_wiring_evidence(scope.context.file, scope.context.entry, scope.context.limit,
                Ok(FuncWiringResult::Checked(*other))),
            source_call_arguments_match(scope.context.source, scope.context.parsed, other,
                scope.context.entry, scope.definition, root.call.call, scope.context.limit, scope.inputs, scope.prior, widths, atomic),
        ensures nested == atomic,
    {
        let context = scope.context;
        let forms = context.parsed.syntax.forms@;
        let call = root.call.call;
        self.checked_func_wiring_agrees(context.file, context.entry, context.limit, *context.wiring, *other);
        self.checked_wiring_is_func(context.file, context.entry, context.limit, *context.wiring);
        self.targets.parsed_project_model();
        let a = self.source_expression_argument_positions(scope, root, widths, nested, children);
        let b = choose|positions: Seq<usize>| #[trigger] call_argument_positions(forms, call, positions)
            && positions.len() == atomic.len() == widths.len()
            && forall|i: int| 0 <= i < positions.len() ==>
                source_call_argument_value(context.source, context.parsed, other, context.entry, scope.definition,
                    #[trigger] positions[i], context.limit, scope.inputs, scope.prior, widths[i], atomic[i]);
        call_argument_positions_agree(forms, call, a, b);
        reveal(source_call_argument_value);
        assert forall|i: int| 0 <= i < nested.len() implies #[trigger] nested[i] == atomic[i] by {
            let form = a[i];
            assert(form == b[i]);
            assert(forms[form as int] is Atom);
            assert(self.source_expression_argument_matches(scope, root, i, form, widths[i], nested[i], children));
            source_call_argument_values_agree(context.source, context.parsed, context.wiring, other, context.entry,
                scope.definition, form, context.limit, scope.inputs, scope.prior, widths[i], nested[i], atomic[i]);
        };
        assert(nested =~= atomic);
    }

    /// 同じ左辺の評価で選んだ二つの引数規則を、元の出現順で比較する。
    pub(super) proof fn source_project_call_arguments_agree(
        &self, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), rank: int, slot: int,
        left_derivation: ISet<SourceInvocation>, right_derivation: ISet<SourceInvocation>,
        left_wiring: &FuncWiring, right_wiring: &FuncWiring,
        inputs: Seq<Seq<bool>>, left: Seq<Seq<bool>>, right: Seq<Seq<bool>>,
        a: SourceCallEvaluation, b: SourceCallEvaluation,
    )
        requires
            self.can_resolve(),
            self.source_call_matches_slot(plan, caller, rank, left_wiring, inputs, left, slot, a, left_derivation),
            self.source_call_matches_slot(plan, caller, rank, right_wiring, inputs, right, slot, b, right_derivation),
            self.func_wiring_evidence(caller.0, caller.1, caller.2, Ok(FuncWiringResult::Checked(*left_wiring))),
            self.func_wiring_evidence(caller.0, caller.1, caller.2, Ok(FuncWiringResult::Checked(*right_wiring))),
            a.definition == b.definition, a.outputs == b.outputs, a.rank == b.rank,
            a.signature.call.call == b.signature.call.call, a.widths == b.widths,
            left.take(a.outputs.start as int) == right.take(a.outputs.start as int),
            forall|x: SourceInvocation, y: SourceInvocation|
                (#[trigger] left_derivation.contains(x)) && (#[trigger] right_derivation.contains(y))
                    && 0 <= x.rank == y.rank < rank && x.inputs == y.inputs ==> x.outputs == y.outputs,
        ensures a.arguments == b.arguments,
    {
        let target = plan.position_model(a.rank)->Some_0;
        let project = self.targets.project_model();
        let (file, entry, limit) = caller;
        self.checked_wiring_is_func(file, entry, limit, *left_wiring);
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let ac = SourceFunc { file, entry, limit, source, parsed, wiring: left_wiring };
        let bc = SourceFunc { file, entry, limit, source, parsed, wiring: right_wiring };
        match (&a.nested, &b.nested) {
            (None, None) => self.source_function_call_arguments_agree(caller, left_wiring, right_wiring, a.definition,
                a.signature, b.signature, a.outputs, target, inputs, left, right, a.widths,
                a.arguments, b.arguments, a.results, b.results),
            (Some(x), None) => {
                let scope = source_expression_scope(&ac, plan, rank, left_derivation, a, x, inputs, left);
                self.source_function_call_values_evidence(caller, right_wiring, b.definition, b.signature, b.outputs,
                    target, inputs, right, b.widths, b.arguments, b.results);
                self.source_nested_arguments_agree_with_atomic(&scope, right_wiring,
                    a.signature, a.widths, a.arguments, b.arguments, x.children);
            },
            (None, Some(y)) => {
                let scope = source_expression_scope(&bc, plan, rank, right_derivation, b, y, inputs, right);
                self.source_function_call_values_evidence(caller, left_wiring, a.definition, a.signature, a.outputs,
                    target, inputs, left, a.widths, a.arguments, a.results);
                self.source_nested_arguments_agree_with_atomic(&scope, left_wiring,
                    b.signature, b.widths, b.arguments, a.arguments, y.children);
            },
            (Some(x), Some(y)) => {
                let u = source_expression_scope(&ac, plan, rank, left_derivation, a, x, inputs, left);
                let v = source_expression_scope(&bc, plan, rank, right_derivation, b, y, inputs, right);
                self.checked_func_wiring_agrees(file, entry, limit, *left_wiring, *right_wiring);
                assert(same_source_bindings(&ac, &bc));
                self.source_expression_arguments_agree(&u, &v, (a.signature, a.arguments, x.children),
                    (b.signature, b.arguments, y.children), a.widths);
            },
        }
    }
}

} // verus!
