//! 通常の右辺と関数呼び出しの出力を、定義順に取り出す。

#[cfg(verus_only)]
mod source_models;
#[cfg(verus_only)]
pub(in crate::project::use_aliases::bit_func) use source_models::{
    prior_function_source_models, source_models_for_step, source_target_for_slot,
};

use super::*;
use super::super::templates::{FunctionTemplates, NorBinding, ResolvedTemplateCall};
#[cfg(verus_only)]
use super::super::templates::{ResolvedExpressionCall, ResolvedNorRoot};
use super::super::lowering::{LoweredBitFunc, ProjectedLoweringError, arguments_are_determined_exec, lower_projected_expansion};
#[cfg(verus_only)]
use super::super::lowering::arguments_are_determined;
use vstd::slice::slice_subrange;
#[cfg(verus_only)]
use super::super::lowering::{
    expanded_definition_values, projected_lowering_output_values, projected_lowering_view, resolved_call_fits_body,
    evaluated_flat_call_matches, evaluated_nested_call_matches, MixedCallEvaluation,
    projected_lowering_call_evaluation, projected_lowering_ports, port_values,
    FuncGateExpression, FuncGateOrigin, SourceStepTarget, projected_lowering_gate_origin, projected_gate_origin_link,
    projected_definition_history, projected_definition_partition, projected_definition_steps, rooted_source_step_ranges,
    source_slot_partition, source_step_range_matches, source_step_slots, source_step_target,
};
#[cfg(verus_only)]
use super::source_evaluation::{source_outputs_from_driver_values, source_outputs_match};
#[cfg(verus_only)]
use crate::netlist::{
    gate_values_match, nor_evaluation, nor_evaluation_ready, output_values_match, port_bit_layout_port,
    port_bit_layout_result, preceding_port_bits,
};
use super::super::expansion::{ExpansionSlot, PreparedExpansionBody, PreparedNorRoot, expansion_call_at_slot};
#[cfg(verus_only)]
use super::super::expansion::{PreparedExpressionCall, prepared_nested_output_matches};
use super::super::super::FunctionExpansionOrder;
#[cfg(verus_only)]
use super::super::super::function_wiring::strict_definition_slots;
#[cfg(verus_only)]
use super::super::super::function_atoms::{
    concat_projection_positions, concat_projections_match, ordinary_call_excludes_structure_projection,
};
#[cfg(verus_only)]
use crate::syntax::circuit::{ordinary_call_at, ordinary_call_excludes_special_forms};

use crate::project::use_aliases::call_arity::ProjectedCallArgument;
#[cfg(verus_only)]
use crate::project::use_aliases::call_arity::CallArgumentSource;
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

/// 投影する根 NOR を、元の候補表の添字と組にする。
pub(super) struct NorDefinition<'s, 'p, 'a> {
    pub(super) index: usize,
    pub(super) root: &'s PreparedNorRoot<'p, 'a>,
}

pub(super) open spec fn nor_covers(roots: Seq<NorDefinition>, at: int) -> bool {
    exists|index: int| 0 <= index < roots.len() && (#[trigger] roots[index]).root.output_slot == at
}

spec fn projected_nor_slot(roots: Seq<NorDefinition>, index: int, at: int, slot: CheckedBitDefinition) -> bool {
    let row = roots[index];
    &&& row.root.output_slot == at
    &&& slot.rhs == BitFuncRhs::NorCallOutput { root: row.index }
    &&& slot.expression == row.root.root.expression
    &&& slot.width == 1
    &&& slot.operands@.len() == 0
}

pub(in crate::project::use_aliases::bit_func) open spec fn nor_binding_fits_body(
    binding: NorBinding, source: &ProjectSource, forms: Seq<Form>, inputs: Seq<u64>,
    slots: Seq<CheckedBitDefinition>, limit: u64,
) -> bool {
    let root = binding.selected.prepared;
    let at = root.output_slot as int;
    &&& at < slots.len()
    &&& root.root.expression.source == source
    &&& slots[at].rhs == BitFuncRhs::NorCallOutput { root: binding.candidate }
    &&& slots[at].width == 1 && slots[at].expression == root.root.expression
    &&& slots[at].operands@.len() == 0
    &&& nor_root_arguments_match_widths(&binding.selected, *binding.references, source, forms, inputs, slots, root.output_slot, limit)
}

pub(in crate::project::use_aliases::bit_func) open spec fn nor_binding_covers(bindings: Seq<NorBinding>, at: int) -> bool {
    exists|index: int| 0 <= index < bindings.len() && (#[trigger] bindings[index]).selected.prepared.output_slot == at
}

pub(in crate::project::use_aliases::bit_func) open spec fn retained_range_determined(
    arguments: Seq<ProjectedCallArgument>, range: core::ops::Range<usize>,
) -> bool {
    &&& range.start <= range.end <= arguments.len()
    &&& arguments_are_determined(arguments.subrange(range.start as int, range.end as int))
}

#[verifier::opaque]
pub(in crate::project::use_aliases::bit_func) open spec fn nor_definition_determined(
    root: &PreparedNorRoot, arguments: Seq<ProjectedCallArgument>,
) -> bool {
    &&& retained_range_determined(arguments, root.root.arguments)
    &&& forall|i: int| 0 <= i < root.postorder@.len() ==>
        retained_range_determined(arguments, (#[trigger] root.postorder@[i]).arguments)
}

#[verifier::opaque]
spec fn nor_definition_ranges_fit(root: &PreparedNorRoot, len: nat) -> bool {
    &&& root.root.arguments.start <= root.root.arguments.end <= len
    &&& forall|i: int| 0 <= i < root.postorder@.len() ==> {
        let row = #[trigger] root.postorder@[i];
        row.arguments.start <= row.arguments.end <= len
    }
}

/// 根と後順列のすべての子について、引数の配線方法が確定しているかを調べる。
fn nor_definition_determined_exec(root: &PreparedNorRoot, arguments: &[ProjectedCallArgument]) -> (ready: bool)
    requires nor_definition_ranges_fit(root, arguments@.len()),
    ensures ready == nor_definition_determined(root, arguments@),
{
    reveal(nor_definition_determined);
    reveal(nor_definition_ranges_fit);
    let root_args = slice_subrange(arguments, root.root.arguments.start, root.root.arguments.end);
    if !arguments_are_determined_exec(root_args) {
        return false;
    }
    let mut i = 0;
    while i < root.postorder.len()
        invariant
            i <= root.postorder@.len(),
            retained_range_determined(arguments@, root.root.arguments),
            forall|j: int| 0 <= j < root.postorder@.len() ==> {
                let row = #[trigger] root.postorder@[j];
                row.arguments.start <= row.arguments.end <= arguments@.len()
            },
            forall|j: int| 0 <= j < i ==> retained_range_determined(arguments@, (#[trigger] root.postorder@[j]).arguments),
        decreases root.postorder@.len() - i,
    {
        let child = &root.postorder[i];
        let args = slice_subrange(arguments, child.arguments.start, child.arguments.end);
        if !arguments_are_determined_exec(args) {
            assert(!nor_definition_determined(root, arguments@)) by {
                reveal(nor_definition_determined);
                assert(*child == root.postorder@[i as int]);
                assert(!retained_range_determined(arguments@, child.arguments));
            };
            return false;
        }
        i += 1;
    }
    true
}

#[verifier::opaque]
spec fn nor_selection_prefix(prepared: &PreparedExpansionBody, at: int, selected: Seq<NorDefinition>) -> bool {
    let arguments = prepared.projections.call_arguments.arguments@;
    &&& forall|i: int| 0 <= i < selected.len() ==> {
        let row = #[trigger] selected[i];
        &&& row.index < at && *row.root == prepared.nor_roots@[row.index as int]
        &&& nor_definition_determined(row.root, arguments)
    }
    &&& forall|a: int, b: int| 0 <= a < b < selected.len() ==>
        (#[trigger] selected[a]).index < (#[trigger] selected[b]).index
}

#[verifier::opaque]
spec fn nor_selection_covers(prepared: &PreparedExpansionBody, at: int, indices: Seq<usize>) -> bool {
    let arguments = prepared.projections.call_arguments.arguments@;
    forall|i: int| 0 <= i < at
        && #[trigger] nor_definition_determined(&prepared.nor_roots@[i], arguments)
        ==> indices.contains(i as usize)
}

spec fn nor_selection_indices(rows: Seq<NorDefinition>) -> Seq<usize> {
    Seq::new(rows.len(), |i: int| rows[i].index)
}

proof fn extend_nor_selection_coverage(
    prepared: &PreparedExpansionBody, at: usize, root: &PreparedNorRoot, ready: bool,
    before: Seq<NorDefinition>, after: Seq<NorDefinition>,
)
    requires
        at < prepared.nor_roots@.len(), *root == prepared.nor_roots@[at as int],
        ready == nor_definition_determined(&prepared.nor_roots@[at as int], prepared.projections.call_arguments.arguments@),
        nor_selection_covers(prepared, at as int, nor_selection_indices(before)),
        after == if ready { before.push(NorDefinition { index: at, root }) } else { before },
    ensures nor_selection_covers(prepared, at + 1, nor_selection_indices(after)),
{
    reveal(nor_selection_covers);
    let old_indices = nor_selection_indices(before);
    let indices = nor_selection_indices(after);
    if ready {
        assert(indices =~= old_indices.push(at));
    }
    assert forall|i: int| 0 <= i <= at
        && #[trigger] nor_definition_determined(&prepared.nor_roots@[i], prepared.projections.call_arguments.arguments@)
        implies indices.contains(i as usize) by {
        if i < at {
            assert(old_indices.contains(i as usize));
        } else {
            assert(i == at && ready);
        }
        if ready {
            vstd::seq_lib::lemma_seq_contains_after_push(old_indices, at, i as usize);
        }
    };
}

#[verifier::spinoff_prover]
proof fn extend_nor_selection(
    prepared: &PreparedExpansionBody, at: usize, root: &PreparedNorRoot, ready: bool,
    before: Seq<NorDefinition>, after: Seq<NorDefinition>,
)
    requires
        at < prepared.nor_roots@.len(), *root == prepared.nor_roots@[at as int],
        ready == nor_definition_determined(root, prepared.projections.call_arguments.arguments@),
        nor_selection_prefix(prepared, at as int, before),
        after == if ready { before.push(NorDefinition { index: at, root }) } else { before },
    ensures nor_selection_prefix(prepared, at + 1, after),
{
    reveal(nor_selection_prefix);
    let arguments = prepared.projections.call_arguments.arguments@;
    let count = before.len() as int;
    assert(after.len() == count + if ready { 1int } else { 0int });
    assert(after.take(count) =~= before);
    if ready {
        assert(after[count] == (NorDefinition { index: at, root }));
    }
    assert forall|i: int| 0 <= i < after.len() implies {
        let row = #[trigger] after[i];
        &&& row.index < at + 1 && *row.root == prepared.nor_roots@[row.index as int]
        &&& nor_definition_determined(row.root, arguments)
    } by {
        if i < count {
            assert(after[i] == before[i]);
            assert(before[i].index < at);
        } else {
            assert(i == count && ready);
        }
    };
    assert forall|a: int, b: int| 0 <= a < b < after.len() implies
        (#[trigger] after[a]).index < (#[trigger] after[b]).index by {
        assert(a < count && after[a] == before[a]);
        if b < count {
            assert(after[b] == before[b]);
        } else {
            assert(b == count && ready);
            assert(before[a].index < at);
        }
    };
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    pub(super) closed spec fn expansion_definition_prefix(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, roots: Seq<NorDefinition>,
        slots: Seq<CheckedBitDefinition>,
    ) -> bool {
        &&& slots.len() <= scope.types@.len()
        &&& forall|at: int| 0 <= at < slots.len() ==> {
            let slot = #[trigger] slots[at];
            if call_covers(calls, at) {
                exists|group: int| 0 <= group < calls.len()
                    && #[trigger] projected_call_slot(calls, group, at, slot)
            } else if nor_covers(roots, at) {
                exists|index: int| 0 <= index < roots.len() && #[trigger] projected_nor_slot(roots, index, at, slot)
            } else {
                self.bit_definition_from_source(scope, slots.take(at), at, slot)
            }
        }
    }

    /// 根 NOR が型、元の定義、他の投影と両立することを表す。
    #[verifier::opaque]
    pub(super) closed spec fn body_nor_slots_match(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, roots: Seq<NorDefinition>,
        concats: Seq<ConcatProjection>,
    ) -> bool {
        &&& forall|index: int| 0 <= index < roots.len() ==> {
            let row = #[trigger] roots[index];
            let at = row.root.output_slot as int;
            &&& at < scope.types@.len() && at < scope.wiring.drivers.definitions@.len()
            &&& location_in_source(row.root.root.expression)
            &&& !call_covers(calls, at)
            &&& scope.types@[at] matches Some(ty) && ty.ty == ResolvedPortType::Bits(1)
            &&& scope.wiring.drivers.definitions@[at].definition == row.root.definition
            &&& scope.wiring.drivers.definitions@[at].result_index == 0
            &&& forall|j: int| 0 <= j < scope.structures@.len() ==> (#[trigger] scope.structures@[j]).target != at
            &&& forall|j: int| 0 <= j < concats.len() ==> (#[trigger] concats[j]).target != at
        }
        &&& forall|a: int, b: int| 0 <= a < b < roots.len() ==>
            (#[trigger] roots[a]).root.output_slot < (#[trigger] roots[b]).root.output_slot
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
        &self, scope: &FuncProjection, outputs: core::ops::Range<usize>, definition: usize,
        concats: Seq<ConcatProjection>,
    )
        requires
            self.projection_context(scope), self.projection_structures_match(scope),
            ({
                let expr = scope.parsed.definitions@[definition as int].expression;
                ordinary_call_at(scope.source.text, scope.parsed.syntax.forms@, expr.start as int, expr.end as int)
            }),
            forall|i: int| outputs.start <= i < outputs.end ==>
                (#[trigger] scope.wiring.drivers.definitions@[i]).definition == definition,
            concat_projections_match(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                scope.wiring, scope.types@, concats),
        ensures
            forall|j: int| 0 <= j < scope.structures@.len() ==>
                !(outputs.start <= (#[trigger] scope.structures@[j]).target < outputs.end),
            forall|j: int| 0 <= j < concats.len() ==>
                !(outputs.start <= (#[trigger] concats[j]).target < outputs.end),
    {
        let expr = scope.parsed.definitions@[definition as int].expression;
        ordinary_call_excludes_special_forms(scope.source.text, scope.parsed.syntax.forms@,
            expr.start as int, expr.end as int);
        concat_projections_order(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
            scope.wiring, scope.types@, concats);

        assert forall|j: int| 0 <= j < concats.len() implies
            !(outputs.start <= (#[trigger] concats[j]).target < outputs.end) by {
            let row = concats[j];
            if outputs.start <= row.target < outputs.end {
                assert(scope.wiring.drivers.definitions@[row.target as int].definition == definition);
                concat_projection_positions(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                    scope.wiring, scope.types@, row);
            }
        };
        assert forall|j: int| 0 <= j < scope.structures@.len() implies
            !(outputs.start <= (#[trigger] scope.structures@[j]).target < outputs.end) by {
            let row = scope.structures@[j];
            if outputs.start <= row.target < outputs.end {
                assert(scope.wiring.drivers.definitions@[row.target as int].definition == definition);
                assert(scope.layouts.is_some());
                let table = scope.layouts->Some_0;
                ordinary_call_excludes_structure_projection(self, scope.file, scope.entry, scope.limit,
                    scope.wiring, *table, scope.types@, row);
            }
        };
    }

    proof fn nor_selection_argument_ranges(
        &self, plan: FunctionExpansionOrder, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, at: int,
    )
        requires
            self.can_resolve(), self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            0 <= at < prepared.nor_roots@.len(),
        ensures nor_definition_ranges_fit(&prepared.nor_roots@[at], prepared.projections.call_arguments.arguments@.len()),
    {
        self.nor_root_template_evidence(plan, caller, prepared, at);
        reveal(nor_definition_ranges_fit);
        let root = prepared.nor_roots@[at];
        let len = prepared.projections.call_arguments.arguments@.len();
        assert forall|i: int| 0 <= i < root.postorder@.len() implies {
            let row = #[trigger] root.postorder@[i];
            row.arguments.start <= row.arguments.end <= len
        } by {
            assert(self.expression_template_ready(&plan, caller.2, root._caller_rank@, len, root.postorder@[i]));
        };
    }

    /// 展開できる根 NOR を集め、元の候補添字を残す。
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    fn select_nor_definitions<'s>(
        &self, candidates: &'s [PreparedNorRoot<'p, 'a>], arguments: &[ProjectedCallArgument],
        Ghost(prepared): Ghost<&PreparedExpansionBody<'p, 'a>>,
        Ghost(plan): Ghost<FunctionExpansionOrder<'p, 'a>>, Ghost(caller): Ghost<(usize, usize, u64)>,
    ) -> (selected: Vec<NorDefinition<'s, 'p, 'a>>)
        requires self.can_resolve(), self.prepared_expansion_body_matches(plan, caller.0, caller.1, caller.2, prepared),
            candidates@ == prepared.nor_roots@, arguments@ == prepared.projections.call_arguments.arguments@,
        ensures
            forall|i: int| 0 <= i < selected@.len() ==> {
                let row = #[trigger] selected@[i];
                &&& row.index < prepared.nor_roots@.len() && *row.root == prepared.nor_roots@[row.index as int]
                &&& nor_definition_determined(row.root, prepared.projections.call_arguments.arguments@)
            },
            forall|a: int, b: int| 0 <= a < b < selected@.len() ==> (#[trigger] selected@[a]).index < (#[trigger] selected@[b]).index,
            nor_selection_prefix(prepared, prepared.nor_roots@.len() as int, selected@),
            nor_selection_covers(prepared, prepared.nor_roots@.len() as int, nor_selection_indices(selected@)),
    {
        let mut selected: Vec<NorDefinition<'s, 'p, 'a>> = Vec::new();
        let mut at = 0;
        proof {
            assert forall|i: int| 0 <= i < prepared.nor_roots@.len() implies
                nor_definition_ranges_fit(&(#[trigger] prepared.nor_roots@[i]), arguments@.len()) by {
                self.nor_selection_argument_ranges(plan, caller, prepared, i);
            };
        }
        assert(nor_selection_prefix(prepared, 0, selected@)) by { reveal(nor_selection_prefix); };
        assert(nor_selection_covers(prepared, 0, nor_selection_indices(selected@))) by { reveal(nor_selection_covers); };
        while at < candidates.len()
            invariant
                candidates@ == prepared.nor_roots@,
                arguments@ == prepared.projections.call_arguments.arguments@,
                at <= prepared.nor_roots@.len(),
                forall|i: int| 0 <= i < prepared.nor_roots@.len() ==>
                    nor_definition_ranges_fit(&(#[trigger] prepared.nor_roots@[i]), arguments@.len()),
                nor_selection_prefix(prepared, at as int, selected@),
                nor_selection_covers(prepared, at as int, nor_selection_indices(selected@)),
            decreases prepared.nor_roots@.len() - at,
        {
            let root = &candidates[at];
            let ghost before = selected@;
            let ready = nor_definition_determined_exec(root, arguments);
            if ready {
                selected.push(NorDefinition { index: at, root });
            }
            proof {
                extend_nor_selection(prepared, at, root, ready, before, selected@);
                extend_nor_selection_coverage(prepared, at, root, ready, before, selected@);
            }
            at += 1;
        }
        reveal(nor_selection_prefix);
        selected
    }

    #[verifier::opaque]
    pub(super) closed spec fn nor_binding_matches(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, limit: u64, parsed: &NamedBuildCircuit,
        arguments: Seq<ProjectedCallArgument>, row: NorDefinition, binding: NorBinding,
    ) -> bool {
        let root = row.root;
        &&& binding.candidate == row.index && binding.selected.prepared == root
        &&& root.definition < parsed.definitions@.len()
        &&& *binding.references == parsed.definitions@[root.definition as int].references
        &&& self.nor_binding_context(plan, table, limit, arguments, binding)
        &&& nor_definition_determined(root, arguments)
    }

    /// 展開できる根 NOR を、同じ候補添字と厳格定義の参照区間を保って配線に渡す。
    #[verifier::spinoff_prover]
    pub(super) fn resolve_selected_nor_roots<'s>(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, table: &'s FunctionTemplates<'p, 'a>,
        arguments: &'s [ProjectedCallArgument], roots: &[NorDefinition<'s, 'p, 'a>],
        parsed: &'s NamedBuildCircuit, Ghost(prepared): Ghost<&PreparedExpansionBody<'p, 'a>>, Ghost(caller): Ghost<(usize, usize, u64)>,
    ) -> (bindings: Vec<NorBinding<'s, 'p, 'a>>)
        requires
            self.can_resolve(), self.function_template_plan(*plan),
            self.function_templates_match(plan, caller.2, table),
            plan.position_model(table.next_rank() as int) == Some((caller.0, caller.1)),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
            arguments@ == prepared.projections.call_arguments.arguments@,
            *parsed == self.targets.project_model().circuits_model()[caller.0 as int],
            forall|i: int| 0 <= i < roots@.len() ==> {
                let row = #[trigger] roots@[i];
                &&& row.index < prepared.nor_roots@.len() && *row.root == prepared.nor_roots@[row.index as int]
                &&& nor_definition_determined(row.root, prepared.projections.call_arguments.arguments@)
            },
            forall|i: int, j: int| 0 <= i < j < roots@.len() ==> (#[trigger] roots@[i]).index < (#[trigger] roots@[j]).index,
        ensures
            bindings@.len() == roots@.len(),
            forall|i: int| 0 <= i < bindings@.len() ==> self.nor_binding_matches(
                plan, table, caller.2, parsed, prepared.projections.call_arguments.arguments@, roots@[i], #[trigger] bindings@[i]),
            forall|i: int| 0 <= i < bindings@.len() ==> self.nor_binding_context(plan, table, caller.2,
                prepared.projections.call_arguments.arguments@, #[trigger] bindings@[i]),
            forall|i: int, j: int| 0 <= i < j < bindings@.len() ==>
                (#[trigger] bindings@[i]).selected.prepared.output_slot < (#[trigger] bindings@[j]).selected.prepared.output_slot,
    {
        let mut bindings = Vec::new();
        let mut i = 0usize;
        while i < roots.len()
            invariant
                self.can_resolve(), self.function_template_plan(*plan),
                self.function_templates_match(plan, caller.2, table),
                plan.position_model(table.next_rank() as int) == Some((caller.0, caller.1)),
                self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
                *parsed == self.targets.project_model().circuits_model()[caller.0 as int],
                arguments@ == prepared.projections.call_arguments.arguments@,
                i == bindings@.len() <= roots@.len(),
                forall|j: int| 0 <= j < roots@.len() ==> {
                    let row = #[trigger] roots@[j];
                    &&& row.index < prepared.nor_roots@.len() && *row.root == prepared.nor_roots@[row.index as int]
                    &&& nor_definition_determined(row.root, arguments@)
                },
                forall|j: int| 0 <= j < i ==> self.nor_binding_matches(
                    plan, table, caller.2, parsed, arguments@, roots@[j], #[trigger] bindings@[j]),
            decreases roots@.len() - i,
        {
            let row = &roots[i];
            proof { self.prepared_nor_reference_evidence(*plan, caller, prepared, row.index as int); }
            let references = &parsed.definitions[row.root.definition].references;
            let selected = self.resolve_nor_root(plan, table, row.root, arguments,
                Ghost(caller), Ghost(prepared), Ghost(row.index as int));
            let binding = NorBinding { candidate: row.index, selected, references };
            assert(self.nor_binding_matches(plan, table, caller.2, parsed, arguments@, *row, binding)) by {
                reveal(UseAliases::nor_binding_matches);
            };
            let ghost before = bindings@;
            bindings.push(binding);
            assert forall|j: int| 0 <= j < bindings@.len() implies self.nor_binding_matches(
                plan, table, caller.2, parsed, arguments@, roots@[j], #[trigger] bindings@[j]) by {
                if j < i { assert(bindings@[j] == before[j]); }
            };
            i += 1;
        }
        reveal(UseAliases::nor_binding_matches);
        assert forall|i: int, j: int| 0 <= i < j < bindings@.len() implies
            (#[trigger] bindings@[i]).selected.prepared.output_slot < (#[trigger] bindings@[j]).selected.prepared.output_slot by {
            assert(roots@[i].index < roots@[j].index);
            assert(*roots@[i].root == prepared.nor_roots@[roots@[i].index as int]);
            assert(*roots@[j].root == prepared.nor_roots@[roots@[j].index as int]);
        };
        bindings
    }

    /// 配線に渡す根 NOR が、同じ定義の出力スロットと型検査済みの引数に対応することを示す。
    #[verifier::spinoff_prover]
    pub(super) proof fn nor_bindings_fit_projection(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, roots: Seq<NorDefinition>, bindings: Seq<NorBinding>, slots: Seq<CheckedBitDefinition>,
    )
        requires
            self.projection_context(scope), self.projection_port_widths_match(scope),
            self.structure_layout_for_ports(scope.limit, scope.layouts),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            self.body_nor_slots_match(scope, prepared.calls@, roots, prepared.projections.concats@),
            self.expansion_definition_prefix(scope, prepared.calls@, roots, slots),
            slots.len() == scope.wiring.drivers.definitions@.len(),
            self.definition_widths_match(scope, slots),
            forall|i: int| 0 <= i < roots.len() ==> {
                let row = #[trigger] roots[i];
                &&& row.index < prepared.nor_roots@.len() && *row.root == prepared.nor_roots@[row.index as int]
            },
            bindings.len() == roots.len(),
            forall|i: int| 0 <= i < bindings.len() ==> self.nor_binding_matches(plan, table, scope.limit, scope.parsed,
                prepared.projections.call_arguments.arguments@, roots[i], #[trigger] bindings[i]),
        ensures
            forall|i: int| 0 <= i < bindings.len() ==> nor_binding_fits_body(
                #[trigger] bindings[i], scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots, scope.limit),
            forall|at: int| 0 <= at < slots.len() ==> {
                let definition = #[trigger] slots[at];
                &&& (definition.rhs is NorCallOutput) == nor_binding_covers(bindings, at)
                &&& nor_binding_covers(bindings, at) ==> !call_covers(prepared.calls@, at)
                &&& !nor_binding_covers(bindings, at) && !call_covers(prepared.calls@, at) ==>
                    bit_definition_matches(scope.inputs@, slots.take(at), definition)
            },
    {
        reveal(UseAliases::nor_binding_matches);
        reveal(UseAliases::body_nor_slots_match);
        reveal(UseAliases::expansion_definition_prefix);
        assert forall|i: int| 0 <= i < bindings.len() implies nor_binding_fits_body(
            #[trigger] bindings[i], scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots, scope.limit) by {
            let row = roots[i];
            let binding = bindings[i];
            let at = row.root.output_slot as int;
            assert(0 <= at < slots.len() && !call_covers(prepared.calls@, at) && nor_covers(roots, at));
            let j = choose|j: int| 0 <= j < roots.len() && #[trigger] projected_nor_slot(roots, j, at, slots[at]);
            if i < j { assert(roots[i].root.output_slot < roots[j].root.output_slot); }
            if j < i { assert(roots[j].root.output_slot < roots[i].root.output_slot); }
            assert(j == i);
            self.prepared_nor_reference_evidence(*plan, (scope.file, scope.entry, scope.limit), prepared, row.index as int);
            self.resolved_nor_arguments_fit_body(scope, plan, table, prepared, &binding.selected, row.index as int,
                row.root.output_slot, slots);
        };
        assert forall|at: int| 0 <= at < slots.len() implies {
            let definition = #[trigger] slots[at];
            &&& (definition.rhs is NorCallOutput) == nor_binding_covers(bindings, at)
            &&& nor_binding_covers(bindings, at) ==> !call_covers(prepared.calls@, at)
            &&& !nor_binding_covers(bindings, at) && !call_covers(prepared.calls@, at) ==>
                bit_definition_matches(scope.inputs@, slots.take(at), definition)
        } by {
            if nor_binding_covers(bindings, at) {
                let i = choose|i: int| 0 <= i < bindings.len() && (#[trigger] bindings[i]).selected.prepared.output_slot == at;
                assert(bindings[i].selected.prepared == roots[i].root);
                assert(!call_covers(prepared.calls@, at));
                assert(nor_binding_fits_body(bindings[i], scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots, scope.limit));
            } else if call_covers(prepared.calls@, at) {
                let g = choose|g: int| 0 <= g < prepared.calls@.len()
                    && #[trigger] projected_call_slot(prepared.calls@, g, at, slots[at]);
                assert(slots[at].rhs is CallOutput);
            } else {
                if nor_covers(roots, at) {
                    let i = choose|i: int| 0 <= i < roots.len() && (#[trigger] roots[i]).root.output_slot == at;
                    assert(bindings[i].selected.prepared == roots[i].root);
                    assert(nor_binding_covers(bindings, at));
                }
                assert(self.bit_definition_from_source(scope, slots.take(at), at, slots[at]));
            }
        };
    }

    /// 選択した根 NOR が、元の定義位置と1ビット幅を保つことを示す。
    pub(super) proof fn prepared_nor_slots_fit_body(
        &self, scope: &FuncProjection, plan: FunctionExpansionOrder, prepared: &PreparedExpansionBody,
        roots: Seq<NorDefinition>,
    )
        requires
            self.projection_context(scope), self.projection_structures_match(scope),
            self.prepared_expansion_body_matches(plan, scope.file, scope.entry, scope.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            forall|i: int| 0 <= i < roots.len() ==> {
                let row = #[trigger] roots[i];
                &&& row.index < prepared.nor_roots@.len() && *row.root == prepared.nor_roots@[row.index as int]
            },
            forall|i: int, j: int| 0 <= i < j < roots.len() ==> (#[trigger] roots[i]).index < (#[trigger] roots[j]).index,
        ensures self.body_nor_slots_match(scope, prepared.calls@, roots, prepared.projections.concats@),
    {
        reveal(UseAliases::body_nor_slots_match);
        reveal(UseAliases::nor_call_slots_disjoint);
        let concats = prepared.projections.concats@;
        let calls = prepared.calls@;
        vstd::std_specs::vec::axiom_spec_len(scope.types);
        assert(scope.types@.len() <= usize::MAX);
        assert forall|i: int| 0 <= i < roots.len() implies {
            let row = #[trigger] roots[i];
            let at = row.root.output_slot as int;
            &&& at < scope.types@.len() && at < scope.wiring.drivers.definitions@.len()
            &&& location_in_source(row.root.root.expression)
            &&& !call_covers(calls, at)
            &&& scope.types@[at] matches Some(ty) && ty.ty == ResolvedPortType::Bits(1)
            &&& scope.wiring.drivers.definitions@[at].definition == row.root.definition
            &&& scope.wiring.drivers.definitions@[at].result_index == 0
            &&& forall|j: int| 0 <= j < scope.structures@.len() ==> (#[trigger] scope.structures@[j]).target != at
            &&& forall|j: int| 0 <= j < concats.len() ==> (#[trigger] concats[j]).target != at
        } by {
            let row = roots[i];
            let at = row.root.output_slot;
            self.prepared_nor_output_evidence(plan, (scope.file, scope.entry, scope.limit), prepared, row.index as int);
            assert(!call_covers(calls, at as int));
            assert(at < scope.types@.len() && at as int + 1 <= usize::MAX);
            let end = (at + 1) as usize;
            assert(end == at as int + 1);
            assert(scope.wiring.drivers.definitions@[at as int].definition == row.root.definition);
            self.special_projections_outside_call(scope, at..end, row.root.definition, concats);
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
            self.special_projections_outside_call(scope, call.outputs, root.definition, concats);
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

    #[verifier::opaque]
    pub(super) closed spec fn prepared_definition_result(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorDefinition>,
        result: Result<Vec<CheckedBitDefinition>, BitFuncError>,
    ) -> bool {
        match result {
            Ok(slots) => slots@.len() == scope.wiring.drivers.definitions@.len()
                && self.expansion_definition_prefix(scope, calls, roots, slots@)
                && self.definition_widths_match(scope, slots@)
                && (forall|slot: int| 0 <= slot < slots@.len() && !call_covers(calls, slot) && !nor_covers(roots, slot) ==>
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
                #[trigger] self.expansion_definition_prefix(scope, calls, roots, prefix)
                && self.definition_widths_match(scope, prefix)
                && prefix.len() < scope.wiring.drivers.definitions@.len()
                && !call_covers(calls, prefix.len() as int)
                && !nor_covers(roots, prefix.len() as int)
                && self.definition_error(scope, prefix, error),
        }
    }

    pub(super) proof fn prepared_definition_width_evidence(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorDefinition>,
        definitions: Vec<CheckedBitDefinition>,
    )
        requires self.prepared_definition_result(scope, calls, selected, roots, Ok(definitions)),
        ensures
            definitions@.len() == scope.wiring.drivers.definitions@.len(),
            self.definition_widths_match(scope, definitions@),
    {
        reveal(UseAliases::prepared_definition_result);
    }

    /// 展開準備が成功したとき、通常の定義が元の右辺と型に対応することを取り出す。
    pub(super) proof fn prepared_ordinary_definition_evidence(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorDefinition>,
        definitions: Vec<CheckedBitDefinition>, i: int,
    )
        requires
            self.prepared_definition_result(scope, calls, selected, roots, Ok(definitions)),
            0 <= i < definitions@.len(),
            !call_covers(calls, i), !nor_covers(roots, i),
        ensures
            definitions@.len() == scope.wiring.drivers.definitions@.len(),
            self.bit_definition_from_source(scope, definitions@.take(i), i, definitions@[i]),
            self.definition_widths_match(scope, definitions@),
    {
        reveal(UseAliases::prepared_definition_result);
        reveal(UseAliases::expansion_definition_prefix);
    }

    /// 一段の変換が書き込む左辺を、厳格索引の一つの定義に対応付ける。
    ///
    /// 複数出力の左辺は宣言順の連続したスロットに入る。先行スロットはすべて別の定義に属する。
    #[verifier::spinoff_prover]
    pub(super) proof fn expanded_strict_definition_site(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>, rows: Seq<NorDefinition>,
        bindings: Seq<NorBinding>, slots: Vec<CheckedBitDefinition>, range: core::ops::Range<usize>, target: SourceStepTarget,
    ) -> (site: crate::project::DefinitionPosition)
        requires
            self.projection_context(scope),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            *scope.wiring == prepared.typed.literals.wiring->Checked_0,
            self.prepared_definition_result(scope, prepared.calls@, selected, rows, Ok(slots)),
            self.expanded_body_nor_bindings(scope, plan, table, prepared, rows, bindings, slots@),
            range.start < range.end <= slots@.len(),
            match target {
                SourceStepTarget::Function(index) => 0 <= index < prepared.calls@.len()
                    && range == prepared.calls@[index].outputs,
                SourceStepTarget::Nor(index) => 0 <= index < bindings.len()
                    && range.start == bindings[index].selected.prepared.output_slot && range.end == range.start + 1,
                SourceStepTarget::Local => range.end == range.start + 1
                    && !call_covers(prepared.calls@, range.start as int) && !nor_covers(rows, range.start as int),
            },
        ensures ({
            let drivers = scope.wiring.drivers.definitions@;
            let frame = scope.parsed.entry_ranges@[scope.entry as int].definitions;
            let absolute = frame.start + site.definition;
            let row = scope.parsed.definitions@[absolute];
            let (start, end) = definition_target_range(scope.parsed.syntax.forms@, row);
            &&& site.file == scope.file && site.entry == scope.entry && site.reference == 0
            &&& frame.start <= absolute < frame.end <= scope.parsed.definitions@.len()
            &&& end - start == range.end - range.start
            &&& range.end <= drivers.len()
            &&& forall|i: int| range.start <= i < range.end ==> {
                let driver = #[trigger] drivers[i];
                &&& driver.definition == absolute && driver.result_index == i - range.start
            }
            &&& forall|i: int| 0 <= i < range.start ==> (#[trigger] drivers[i]).definition < absolute
        }),
    {
        let caller = (scope.file, scope.entry, scope.limit);
        let drivers = scope.wiring.drivers.definitions@;
        let frame = scope.parsed.entry_ranges@[scope.entry as int].definitions;
        self.prepared_definition_width_evidence(scope, prepared.calls@, selected, rows, slots);
        self.checked_wiring_is_func(scope.file, scope.entry, scope.limit, *scope.wiring);
        let first = drivers[range.start as int];
        let absolute = first.definition;
        let row = scope.parsed.definitions@[absolute as int];
        let (start, end) = definition_target_range(scope.parsed.syntax.forms@, row);
        match target {
            SourceStepTarget::Function(index) => {
                self.prepared_call_matches_source_site(plan, caller, prepared, index);
                let group = prepared.calls@[index];
                let root = prepared.projections.calls@[index];
                self.source_function_call_site_evidence(caller, scope.wiring, range.start as int, root.definition,
                    group._signature@, group.outputs, (root.target_file, root.target_entry));
                assert forall|i: int| range.start <= i < range.end implies {
                    let driver = #[trigger] drivers[i];
                    &&& driver.definition == absolute && driver.result_index == i - range.start
                } by {
                    self.source_function_call_site_evidence(caller, scope.wiring, i, root.definition,
                        group._signature@, group.outputs, (root.target_file, root.target_entry));
                };
            },
            SourceStepTarget::Nor(index) => {
                reveal(UseAliases::expanded_body_nor_bindings);
                assert(0 <= index < bindings.len());
                let binding = bindings[index];
                assert(binding.candidate < prepared.nor_roots@.len());
                assert(*binding.selected.prepared == prepared.nor_roots@[binding.candidate as int]);
                let candidate = binding.candidate as int;
                self.prepared_nor_output_evidence(*plan, caller, prepared, candidate);
                assert(prepared.nor_roots@[candidate].output_slot == range.start);
                assert(drivers == prepared.typed.literals.wiring->Checked_0.drivers.definitions@);
                assert(first.definition == prepared.nor_roots@[candidate].definition && first.result_index == 0);
                let count = self.checked_wiring_output_group(scope.file, scope.entry, scope.limit, *scope.wiring, range.start as int);
                if count > 1 {
                    assert(drivers[range.start + 1].definition == absolute);
                    assert(false);
                }
            },
            SourceStepTarget::Local => {
                self.prepared_ordinary_definition_evidence(scope, prepared.calls@, selected, rows, slots, range.start as int);
                assert(end - start == 1);
                assert(crate::project::use_aliases::function_drivers::indexed_driver_site(
                    scope.source, scope.parsed, scope.entry as int, first));
            },
        }
        assert(first.result_index == 0);
        assert forall|i: int| 0 <= i < range.start implies (#[trigger] drivers[i]).definition < absolute by {
            assert(drivers[i].definition < first.definition
                || (drivers[i].definition == first.definition && drivers[i].result_index < first.result_index));
        };
        crate::project::DefinitionPosition {
            file: scope.file, entry: scope.entry, definition: (absolute - frame.start) as usize, reference: 0,
        }
    }

    /// 成功した一段の左辺区間を、同じ厳格定義から決めた区間に照合する。
    #[verifier::spinoff_prover]
    proof fn expanded_step_matches_strict_range(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>, rows: Seq<NorDefinition>,
        roots: Seq<NorBinding>, slots: Vec<CheckedBitDefinition>, step: super::super::lowering::WiringStep,
    )
        requires
            self.projection_context(scope),
            prepared.typed.literals.wiring matches FuncWiringResult::Checked(wiring) && *scope.wiring == wiring,
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            self.expansion_selection_matches(plan, table, (scope.file, scope.entry, scope.limit), prepared, selected),
            self.prepared_definition_result(scope, prepared.calls@, selected, rows, Ok(slots)),
            self.expanded_body_nor_bindings(scope, plan, table, prepared, rows, roots, slots@),
            source_step_range_matches(step, selected, roots, slots@.len()),
        ensures strict_definition_slots(scope.parsed, scope.entry, scope.wiring).contains(source_step_slots(step)),
    {
        let caller = (scope.file, scope.entry, scope.limit);
        let frame = scope.parsed.entry_ranges@[scope.entry as int].definitions;
        let wiring = scope.wiring;
        let expected = strict_definition_slots(scope.parsed, scope.entry, wiring);
        let range = source_step_slots(step);
        let target = source_step_target(step);
        assert(source_step_range_matches(step, selected, roots, slots@.len()));
        match target {
            SourceStepTarget::Local => {
                assert(!nor_covers(rows, range.start as int)) by {
                    reveal(UseAliases::expanded_body_nor_bindings);
                    assert(!nor_binding_covers(roots, range.start as int));
                    assert(nor_binding_covers(roots, range.start as int) == nor_covers(rows, range.start as int));
                };
                let calls = Seq::new(selected.len(), |j: int| *selected[j].group);
                assert(calls =~= prepared.calls@) by {
                    assert forall|j: int| 0 <= j < selected.len() implies #[trigger] calls[j] == prepared.calls@[j] by {
                        assert(self.resolved_template_call_matches(plan, caller, prepared, j, selected[j]));
                    };
                };
            },
            SourceStepTarget::Function(group) => {
                assert(self.resolved_template_call_matches(plan, caller, prepared, group, selected[group]));
            },
            SourceStepTarget::Nor(_) => {},
        }
        let site = self.expanded_strict_definition_site(scope, plan, table, prepared, selected, rows, roots, slots, range, target);
        let j = site.definition as int;
        self.strict_definition_slot_at(scope.file, scope.entry, scope.limit, wiring, j);
        let driver = wiring.drivers.definitions@[range.start as int];
        assert(driver.definition == frame.start + j && driver.result_index == 0);
        assert(expected[j].start == range.start && expected[j].end == range.end);
        assert(expected.contains(expected[j]));
    }

    /// 一つの関数の成功履歴が、厳格索引の各定義を先頭から一度ずつ変換したことを示す。
    #[verifier::spinoff_prover]
    pub(super) proof fn expanded_body_strict_steps<'w>(
        &self, plan: &FunctionExpansionOrder, table: &'w FunctionTemplates<'p, 'a>, caller: (usize, usize, u64),
        prepared: &'w PreparedExpansionBody<'p, 'a>, capacity: usize, limit: usize, value: &'w ExpandedBody<'p, 'a>,
    ) -> (witness: (FuncProjection<'w, 'p, 'a>, Seq<ResolvedTemplateCall<'w, 'p, 'a>>,
        Seq<NorBinding<'w, 'p, 'a>>, Vec<CheckedBitDefinition<'p, 'a>>, Seq<super::super::lowering::WiringStep>, Seq<NorDefinition<'w, 'p, 'a>>))
        requires
            self.can_resolve(),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
            self.expanded_body_lowering_result(plan, table, caller, prepared, capacity, limit, Ok(*value)),
        ensures ({
            let (scope, selected, roots, slots, steps, rows) = witness;
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[caller.0 as int];
            let wiring = &prepared.typed.literals.wiring->Checked_0;
            &&& scope.file == caller.0 && scope.entry == caller.1 && scope.limit == caller.2
            &&& scope.source == &project.sources_model()[caller.0 as int] && scope.parsed == parsed && scope.wiring == wiring
            &&& scope.inputs == &value.ports.inputs && scope.outputs == &value.ports.outputs
            &&& scope.types == &prepared.typed.types && scope.structures == &prepared.projections.entries
            &&& self.projection_context(&scope)
            &&& self.projection_port_widths_match(&scope)
            &&& self.projection_structures_match(&scope)
            &&& value.ports.outputs@.len() == wiring.drivers.outputs@.len()
            &&& output_widths_before(value.ports.inputs@, value.ports.outputs@, slots@, wiring.drivers.outputs@,
                wiring.drivers.outputs@.len() as int)
            &&& self.expansion_selection_matches(plan, table, caller, prepared, selected)
            &&& self.expanded_body_nor_bindings(&scope, plan, table, prepared, rows, roots, slots@)
            &&& slots@.len() == wiring.drivers.definitions@.len()
            &&& rooted_source_step_ranges(steps) == strict_definition_slots(parsed, caller.1, wiring)
            &&& self.prepared_definition_result(&scope, prepared.calls@, selected, rows, Ok(slots))
            &&& forall|i: int| 0 <= i < steps.len() ==> {
                let step = #[trigger] steps[i];
                let target = source_step_target(step);
                &&& source_step_range_matches(step, selected, roots, slots@.len())
                &&& target == source_target_for_slot(source_step_slots(step).start, selected, roots)
                &&& match target {
                    SourceStepTarget::Function(index) => 0 <= index < selected.len()
                        && (selected[index].children@.len() > 0 ==> super::super::lowering::nested_arguments_ready(&selected[index])),
                    _ => true,
                }
            }
            &&& projected_definition_history(value.ports.inputs@, slots@, value.ports.outputs@, wiring.drivers.outputs@,
                parsed.syntax.forms@, selected, roots, prepared.projections.call_arguments.arguments@, capacity, limit, &value.circuit, steps)
        }),
    {
        let (scope, selected, rows, roots, slots) = self.expanded_body_success(plan, table, caller, prepared, capacity, limit, value);
        self.prepared_definition_width_evidence(&scope, prepared.calls@, selected, rows, slots);
        let inputs = value.ports.inputs@;
        let outputs = value.ports.outputs@;
        let wiring = scope.wiring;
        let drivers = wiring.drivers.outputs@;
        let forms = scope.parsed.syntax.forms@;
        let arguments = prepared.projections.call_arguments.arguments@;
        let steps = projected_definition_steps(inputs, slots@, outputs, drivers, forms, selected, roots, arguments,
            capacity, limit, &value.circuit);
        self.strict_definition_slot_partition(scope.file, scope.entry, scope.limit, wiring);
        vstd::std_specs::vec::axiom_spec_len(&slots);
        let expected = strict_definition_slots(scope.parsed, scope.entry, wiring);
        assert(source_slot_partition(expected, slots@.len() as usize)) by {
            assert forall|i: int| 0 <= i < expected.len() implies {
                let end = #[trigger] expected[i].end;
                &&& expected[i].start < end <= slots@.len()
                &&& end == if i + 1 < expected.len() { expected[i + 1].start } else { slots@.len() as usize }
            } by {};
        };
        assert forall|i: int| 0 <= i < steps.len() implies #[trigger] expected.contains(source_step_slots(steps[i])) by {
            self.expanded_step_matches_strict_range(&scope, plan, table, prepared, selected, rows, roots, slots, steps[i]);
        };
        projected_definition_partition(inputs, slots@, outputs, drivers, forms, selected, roots, arguments,
            capacity, limit, &value.circuit, steps, expected);
        assert forall|i: int| 0 <= i < steps.len() implies {
            let step = #[trigger] steps[i];
            let target = source_step_target(step);
            &&& source_step_range_matches(step, selected, roots, slots@.len())
            &&& target == source_target_for_slot(source_step_slots(step).start, selected, roots)
            &&& match target {
                SourceStepTarget::Function(index) => 0 <= index < selected.len()
                    && (selected[index].children@.len() > 0 ==> super::super::lowering::nested_arguments_ready(&selected[index])),
                _ => true,
            }
        } by {
            let step = steps[i];
            self.source_target_for_strict_step(&scope, plan, table, prepared, selected, rows, roots, slots, step);
            if let SourceStepTarget::Function(index) = source_step_target(step) {
                self.expanded_call_step_ready(plan, table, caller, prepared, inputs, slots@, outputs, drivers, forms,
                    selected, roots, capacity, limit, &value.circuit, steps, i, index);
            }
        };
        assert(outputs.len() == drivers.len()) by {
            assert(self.projection_port_widths_match(&scope));
            assert(expected_output_context(scope.source, scope.parsed, scope.entry as int, scope.wiring.drivers));
        };
        (scope, selected, roots, slots, steps, rows)
    }

    /// 出力スロットを駆動する基底 NOR の定義番号と型付き署名を取り出す。
    proof fn local_nor_source_site(
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, selected: Seq<ResolvedTemplateCall>,
        roots: Seq<NorDefinition>, definitions: Vec<CheckedBitDefinition>, slot: int,
    ) -> (site: (crate::project::DefinitionPosition, TypedFuncCall<'p, 'a>))
        requires
            self.projection_context(scope),
            self.prepared_definition_result(scope, calls, selected, roots, Ok(definitions)),
            0 <= slot < definitions@.len(),
            !call_covers(calls, slot), !nor_covers(roots, slot),
            definitions@[slot].rhs is Nor,
        ensures
            site.0.file == scope.file && site.0.entry == scope.entry && site.0.reference == 0,
            scope.parsed.entry_ranges@[scope.entry as int].definitions.start + site.0.definition
                == scope.wiring.drivers.definitions@[slot].definition,
            self.func_call_signature_evidence(scope.file, scope.entry, site.0.definition, 0, scope.limit, Ok(Some(site.1))),
            site.1.call.target is Nor,
    {
        self.prepared_ordinary_definition_evidence(scope, calls, selected, roots, definitions, slot);
        let definition = scope.wiring.drivers.definitions@[slot].definition;
        let frame = scope.parsed.entry_ranges@[scope.entry as int].definitions;
        let local = (definition - frame.start) as usize;
        let row = scope.parsed.definitions@[definition as int];
        let call = choose|call: TypedFuncCall|
            #[trigger] self.func_call_signature_evidence(scope.file, scope.entry, local, 0, scope.limit, Ok(Some(call)))
            && call.call.call.form == row.expression.start && call.call.call.arguments == 2 && call.call.target is Nor;
        (crate::project::DefinitionPosition { file: scope.file, entry: scope.entry, definition: local, reference: 0 }, call)
    }

    /// 展開準備で確定した呼び出しと実際の出力幅から、関数本体を定義順に取り出す。
    ///
    /// # Errors
    ///
    /// 通常の右辺の変換で最初に見つかったエラーを返す。
    pub(super) fn project_prepared_definition_body(
        &self, scope: &FuncProjection<'_, 'p, 'a>, calls: &[CheckedExpansionCall<'p, 'a>],
        selected: &[ResolvedTemplateCall<'_, 'p, 'a>], roots: &[NorDefinition<'_, 'p, 'a>], literal_widths: &[Option<u64>], concats: Vec<ConcatProjection>,
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
            self.body_nor_slots_match(scope, calls@, roots@, concats@),
            scope.structures@ == prepared.projections.entries@,
            self.expansion_selection_matches(&plan, templates, (scope.file, scope.entry, scope.limit), &prepared, selected@),
            forall|i: int| 0 <= i < selected@.len() ==> {
                let call = #[trigger] selected@[i];
                &&& self.resolved_template_call_matches(&plan, (scope.file, scope.entry, scope.limit), &prepared, i, call)
                &&& scope.layouts.is_none() ==>
                    !has_structure_port(call.template.signature_model().inputs@)
                        && !has_structure_port(call.template.signature_model().outputs@)
            },
        ensures self.prepared_definition_result(scope, calls@, selected@, roots@, result),
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
        let result = self.project_definition_body(scope, calls, roots, call_widths.as_slice(), literal_widths, concats, Ghost(prepared.typed));
        proof {
            reveal(UseAliases::prepared_definition_result);
            if let Ok(slots) = &result {
                reveal(UseAliases::body_calls_match);
                reveal(UseAliases::expansion_definition_prefix);
                reveal(UseAliases::definition_widths_match);
                assert forall|slot: int| 0 <= slot < slots@.len() && !call_covers(calls@, slot) && !nor_covers(roots@, slot) implies
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
        &self, scope: &FuncProjection, calls: Seq<CheckedExpansionCall>, roots: Seq<NorDefinition>,
        before: Seq<CheckedBitDefinition>, after: Seq<CheckedBitDefinition>,
        active: ExpansionSlot, group: usize, nor: usize,
    )
        requires
            self.expansion_definition_prefix(scope, calls, roots, before),
            before.len() < after.len() <= scope.types@.len(),
            after.take(before.len() as int) == before,
            forall|j: int| 0 <= j < before.len() ==>
                location_in_source((#[trigger] before[j]).expression) && before[j].width > 0,
            match active {
                ExpansionSlot::Function => {
                    &&& group < calls.len()
                    &&& calls[group as int].outputs.start == before.len()
                    &&& calls[group as int].outputs.end == after.len()
                    &&& location_in_source(calls[group as int].expression)
                    &&& forall|j: int| before.len() <= j < after.len() ==>
                        projected_call_slot(calls, group as int, j, #[trigger] after[j]) && after[j].width > 0
                },
                ExpansionSlot::Nor => {
                    &&& nor < roots.len()
                    &&& after.len() == before.len() + 1
                    &&& !call_covers(calls, before.len() as int)
                    &&& projected_nor_slot(roots, nor as int, before.len() as int, after[before.len() as int])
                    &&& location_in_source(roots[nor as int].root.root.expression)
                },
                ExpansionSlot::Local => {
                    &&& after.len() == before.len() + 1
                    &&& !call_covers(calls, before.len() as int)
                    &&& !nor_covers(roots, before.len() as int)
                    &&& self.bit_definition_from_source(scope, before, before.len() as int, after[before.len() as int])
                },
            },
        ensures
            self.expansion_definition_prefix(scope, calls, roots, after),
            forall|j: int| 0 <= j < after.len() ==>
                location_in_source((#[trigger] after[j]).expression) && after[j].width > 0,
    {
        reveal(UseAliases::expansion_definition_prefix);
        assert forall|j: int| 0 <= j < after.len() implies {
            let slot = #[trigger] after[j];
            &&& location_in_source(slot.expression) && slot.width > 0
            &&& if call_covers(calls, j) {
                exists|g: int| 0 <= g < calls.len() && #[trigger] projected_call_slot(calls, g, j, slot)
            } else if nor_covers(roots, j) {
                exists|n: int| 0 <= n < roots.len() && #[trigger] projected_nor_slot(roots, n, j, slot)
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
                } else if nor_covers(roots, j) {
                    let n = choose|n: int| 0 <= n < roots.len() && #[trigger] projected_nor_slot(roots, n, j, before[j]);
                    assert(projected_nor_slot(roots, n, j, after[j]));
                } else {
                    assert(self.bit_definition_from_source(scope, before.take(j), j, before[j]));
                }
            } else {
                match active {
                    ExpansionSlot::Function => {
                        assert(projected_call_slot(calls, group as int, j, after[j]));
                        assert(call_covers(calls, j));
                    },
                    ExpansionSlot::Nor => {
                        assert(j == before.len());
                        assert(projected_nor_slot(roots, nor as int, j, after[j]));
                        assert(nor_covers(roots, j));
                    },
                    ExpansionSlot::Local => {
                        assert(j == before.len());
                        assert(after.take(j) == before);
                    },
                }
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

    proof fn extend_nor_definition_widths(
        &self, scope: &FuncProjection, before: Seq<CheckedBitDefinition>, after: Seq<CheckedBitDefinition>,
    )
        requires
            self.definition_widths_match(scope, before),
            after.len() == before.len() + 1 <= scope.types@.len(),
            after.take(before.len() as int) == before,
            scope.types@[before.len() as int] matches Some(ty) && ty.ty == ResolvedPortType::Bits(1),
            after[before.len() as int].width == 1,
        ensures self.definition_widths_match(scope, after),
    {
        reveal(UseAliases::definition_widths_match);
        let at = before.len() as int;
        assert(self.port_width_matches(ResolvedPortType::Bits(1), 1, scope.layouts));
        assert forall|j: int| 0 <= j < after.len() implies {
            let checked = #[trigger] after[j];
            scope.types@[j] matches Some(ty) && self.port_width_matches(ty.ty, checked.width, scope.layouts)
        } by {
            if j < at { assert(after[j] == before[j]); }
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
        let roots: &[NorDefinition] = &[];
        assert(roots@ =~= Seq::empty());
        assert(self.body_nor_slots_match(scope, calls@, roots@, concats@)) by {
            reveal(UseAliases::body_nor_slots_match);
        };
        let result = self.project_definition_body(scope, calls, roots, &[], literal_widths, concats, Ghost(typed));
        proof {
            reveal(UseAliases::expansion_definition_prefix);
            reveal(UseAliases::definition_prefix);
            match &result {
                Ok(slots) => { assert(self.definition_prefix(scope, slots@)); },
                Err(error) => {
                    let prefix = choose|prefix: Seq<CheckedBitDefinition>|
                        #[trigger] self.expansion_definition_prefix(scope, calls@, Seq::empty(), prefix)
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
    #[verifier::spinoff_prover]
    #[verifier::rlimit(72)]
    pub(super) fn project_definition_body<'b>(
        &self, scope: &FuncProjection<'_, 'p, 'a>, calls: &[CheckedExpansionCall<'p, 'a>],
        roots: &[NorDefinition<'_, 'p, 'a>], call_widths: &[&'b [u64]], literal_widths: &[Option<u64>], mut concats: Vec<ConcatProjection>,
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
            self.body_nor_slots_match(scope, calls@, roots@, concats@),
        ensures match result {
            Ok(slots) => slots@.len() == scope.wiring.drivers.definitions@.len()
                && self.expansion_definition_prefix(scope, calls@, roots@, slots@)
                && self.definition_widths_match(scope, slots@),
            Err(error) => exists|prefix: Seq<CheckedBitDefinition>|
                #[trigger] self.expansion_definition_prefix(scope, calls@, roots@, prefix)
                && self.definition_widths_match(scope, prefix)
                && prefix.len() < scope.wiring.drivers.definitions@.len()
                && !call_covers(calls@, prefix.len() as int)
                && !nor_covers(roots@, prefix.len() as int)
                && self.definition_error(scope, prefix, error),
        },
    {
        let ghost concat_model = concats@;
        let mut slots: Vec<CheckedBitDefinition<'p, 'a>> = Vec::new();
        let mut i = 0usize;
        let mut group = 0usize;
        let mut nor = 0usize;
        let mut next_structure = 0usize;
        let mut next_concat = 0usize;
        proof {
            concat_projections_order(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                scope.wiring, scope.types@, concat_model);
            reveal(concat_cursor_ready);
            assert(self.expansion_definition_prefix(scope, calls@, roots@, slots@)) by {
                reveal(UseAliases::expansion_definition_prefix);
            };
            assert(self.definition_widths_match(scope, slots@)) by {
                reveal(UseAliases::definition_widths_match);
            };
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
                self.body_nor_slots_match(scope, calls@, roots@, concat_model),
                i == slots@.len() <= scope.wiring.drivers.definitions@.len(),
                group <= calls@.len(),
                forall|j: int| 0 <= j < group ==> (#[trigger] calls@[j]).outputs.end <= i,
                forall|j: int| group <= j < calls@.len() ==> i <= (#[trigger] calls@[j]).outputs.start,
                nor <= roots@.len(),
                forall|j: int| 0 <= j < nor ==> (#[trigger] roots@[j]).root.output_slot < i,
                forall|j: int| nor <= j < roots@.len() ==> i <= (#[trigger] roots@[j]).root.output_slot,
                next_structure <= scope.structures@.len(),
                forall|j: int| 0 <= j < next_structure ==> (#[trigger] scope.structures@[j]).target < i,
                forall|j: int| next_structure <= j < scope.structures@.len() ==> i <= (#[trigger] scope.structures@[j]).target,
                concat_cursor_ready(concats@, concat_model, next_concat, i as int),
                forall|a: int, b: int| 0 <= a < b < concat_model.len()
                    ==> (#[trigger] concat_model[a]).target < (#[trigger] concat_model[b]).target,
                forall|j: int| 0 <= j < concat_model.len() ==> concat_projection_matches(
                    scope.file, scope.entry, scope.limit, scope.source, scope.parsed, scope.wiring, scope.types@,
                    #[trigger] concat_model[j]),
                self.expansion_definition_prefix(scope, calls@, roots@, slots@),
                self.definition_widths_match(scope, slots@),
                forall|j: int| 0 <= j < slots@.len() ==>
                    location_in_source((#[trigger] slots@[j]).expression) && slots@[j].width > 0,
            decreases scope.wiring.drivers.definitions@.len() - i,
        {
            let ghost before = slots@;
            let head = if group < calls.len() { Some(calls[group].outputs.start) } else { None };
            let nor_head = if nor < roots.len() { Some(roots[nor].root.output_slot) } else { None };
            proof {
                reveal(UseAliases::body_nor_slots_match);
                if group < calls.len() && nor < roots.len() {
                    reveal(UseAliases::body_calls_match);
                    let at = roots@[nor as int].root.output_slot as int;
                    assert(!call_covers(calls@, at));
                    if calls@[group as int].outputs.start == at {
                        assert(call_covers(calls@, at));
                    }
                }
            }
            let kind = expansion_call_at_slot(head, nor_head, i);
            if matches!(kind, ExpansionSlot::Function) {
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
                    self.keep_body_prefix(scope, calls@, roots@, before, slots@, ExpansionSlot::Function, group, nor);
                    assert forall|j: int| nor <= j < roots@.len() implies
                        call.outputs.end <= (#[trigger] roots@[j]).root.output_slot by {
                        assert(calls@[group as int] == *call);
                        assert(!call_covers(calls@, roots@[j].root.output_slot as int));
                    };
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

            if matches!(kind, ExpansionSlot::Nor) {
                let row = &roots[nor];
                let slot = CheckedBitDefinition { expression: copy_location(&row.root.root.expression),
                    width: 1, rhs: BitFuncRhs::NorCallOutput { root: row.index }, operands: Vec::new() };
                slots.push(slot);
                proof {
                    assert(slots@.take(before.len() as int) =~= before);
                    self.keep_body_prefix(scope, calls@, roots@, before, slots@, ExpansionSlot::Nor, group, nor);
                    self.extend_nor_definition_widths(scope, before, slots@);
                    assert forall|j: int| nor < j < roots@.len() implies
                        i < (#[trigger] roots@[j]).root.output_slot by {
                        assert(roots@[nor as int] == *row);
                    };
                    assert forall|j: int| next_structure <= j < scope.structures@.len() implies
                        i < (#[trigger] scope.structures@[j]).target by {};
                    reveal(concat_cursor_ready);
                    assert forall|j: int| next_concat <= j < concat_model.len() implies
                        i < (#[trigger] concat_model[j]).target by {
                        assert(concats@[j] == concat_model[j]);
                        assert(i <= concat_model[j].target);
                        assert(concat_model[j].target != i);
                    };
                }
                i += 1;
                nor += 1;
                continue;
            }
            proof {
                assert forall|j: int| nor <= j < roots@.len() implies
                    i < (#[trigger] roots@[j]).root.output_slot by {
                    if nor < j { assert(roots@[nor as int].root.output_slot < roots@[j].root.output_slot); }
                };
                assert(!nor_covers(roots@, i as int));
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
                        #[trigger] self.expansion_definition_prefix(scope, calls@, roots@, prefix)
                        && self.definition_widths_match(scope, prefix)
                        && prefix.len() < scope.wiring.drivers.definitions@.len()
                        && !call_covers(calls@, prefix.len() as int)
                        && !nor_covers(roots@, prefix.len() as int)
                        && self.definition_error(scope, prefix, error));
                    return Err(error);
                },
            };
            proof { self.extend_definition_widths(scope, typed, before, slot, structure); }
            slots.push(slot);
            proof {
                assert(slots@.take(before.len() as int) =~= before);
                self.keep_body_prefix(scope, calls@, roots@, before, slots@, ExpansionSlot::Local, group, nor);
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
    spec fn expanded_projection_scope<'w>(
        &self, caller: (usize, usize, u64), prepared: &'w PreparedExpansionBody<'p, 'a>,
        ports: &'w PreparedBitFuncPorts<'p, 'a>,
    ) -> FuncProjection<'w, 'p, 'a> {
        let (file, entry, limit) = caller;
        let project = self.targets.project_model();
        FuncProjection {
            file, entry, limit, source: &project.sources_model()[file as int],
            parsed: &project.circuits_model()[file as int], wiring: &prepared.typed.literals.wiring->Checked_0,
            inputs: &ports.inputs, outputs: &ports.outputs,
            layouts: match &ports.layouts { Some(table) => Some(table), None => None },
            types: &prepared.typed.types, structures: &prepared.projections.entries,
        }
    }

    #[verifier::opaque]
    pub(in crate::project::use_aliases::bit_func) closed spec fn expanded_body_lowering_result(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
        layout_limit: usize, gate_limit: usize, result: Result<ExpandedBody, ExpandedBodyError>,
    ) -> bool {
        let (file, entry, limit) = caller;
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
                        let scope = self.expanded_projection_scope(caller, prepared, &ports);
                        self.expanded_definition_lowering_result(&scope, plan, table, prepared, selected, layout_limit, gate_limit, result)
                    },
            }
        }
    }

    #[verifier::opaque]
    spec fn nor_expansion_selection_matches(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, rows: Seq<NorDefinition>, bindings: Seq<NorBinding>,
    ) -> bool {
        let arguments = prepared.projections.call_arguments.arguments@;
        &&& rows.len() == bindings.len()
        &&& self.body_nor_slots_match(scope, prepared.calls@, rows, prepared.projections.concats@)
        &&& nor_selection_prefix(prepared, prepared.nor_roots@.len() as int, rows)
        &&& forall|i: int| 0 <= i < bindings.len() ==>
            self.nor_binding_matches(plan, table, scope.limit, scope.parsed, arguments, rows[i], #[trigger] bindings[i])
        &&& nor_selection_covers(prepared, prepared.nor_roots@.len() as int, nor_selection_indices(rows))
        &&& forall|i: int, j: int| 0 <= i < j < bindings.len() ==>
            (#[trigger] bindings[i]).selected.prepared.output_slot < (#[trigger] bindings[j]).selected.prepared.output_slot
    }

    #[verifier::opaque]
    spec fn expanded_definition_lowering_result(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>,
        layout_limit: usize, gate_limit: usize, result: Result<ExpandedBody, ExpandedBodyError>,
    ) -> bool {
        &&& self.projection_context(scope)
        &&& exists|rows: Seq<NorDefinition>, bindings: Seq<NorBinding>|
            #[trigger] self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings)
            && self.expanded_bound_definitions_result(scope, prepared, selected, rows, bindings, layout_limit, gate_limit, result)
    }

    #[verifier::opaque]
    spec fn expanded_bound_definitions_result(
        &self, scope: &FuncProjection, prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>,
        rows: Seq<NorDefinition>, bindings: Seq<NorBinding>,
        layout_limit: usize, gate_limit: usize, result: Result<ExpandedBody, ExpandedBodyError>,
    ) -> bool {
        let drivers = scope.wiring.drivers.outputs@;
        let arguments = prepared.projections.call_arguments.arguments@;
        match result {
            Err(ExpandedBodyError::Definition(error)) =>
                self.prepared_definition_result(scope, prepared.calls@, selected, rows, Err(error)),
            _ => exists|slots: Vec<CheckedBitDefinition>|
                #[trigger] self.prepared_definition_result(scope, prepared.calls@, selected, rows, Ok(slots))
                && self.expanded_slots_result(scope, selected, bindings, arguments, slots, layout_limit, gate_limit, result),
        }
    }

    #[verifier::opaque]
    spec fn expanded_slots_result(
        &self, scope: &FuncProjection, selected: Seq<ResolvedTemplateCall>, bindings: Seq<NorBinding>,
        arguments: Seq<ProjectedCallArgument>, slots: Vec<CheckedBitDefinition>, layout_limit: usize, gate_limit: usize,
        result: Result<ExpandedBody, ExpandedBodyError>,
    ) -> bool {
        let drivers = scope.wiring.drivers.outputs@;
        &&& forall|i: int| 0 <= i < bindings.len() ==> nor_binding_fits_body(
            #[trigger] bindings[i], scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots@, scope.limit)
        &&& match result {
            Err(ExpandedBodyError::Output(error)) => output_width_failure(
                &scope.wiring.drivers.signature, scope.inputs@, scope.outputs@, slots@, drivers, error),
            Ok(value) => output_widths_before(scope.inputs@, scope.outputs@, slots@, drivers, drivers.len() as int)
                && projected_lowering_view(scope.inputs@, slots@, scope.outputs@,
                    drivers, scope.parsed.syntax.forms@, selected, bindings, arguments, layout_limit, gate_limit, Ok(value.circuit)),
            Err(ExpandedBodyError::Lowering(error)) => output_widths_before(
                scope.inputs@, scope.outputs@, slots@, drivers, drivers.len() as int)
                && projected_lowering_view(scope.inputs@, slots@, scope.outputs@,
                    drivers, scope.parsed.syntax.forms@, selected, bindings, arguments, layout_limit, gate_limit, Err(error)),
            _ => false,
        }
    }

    /// 根 NOR の選択と定義列の変換結果を、本体の診断または成功結果に対応付ける。
    #[verifier::spinoff_prover]
    proof fn expanded_definition_result_intro(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>, rows: Seq<NorDefinition>, bindings: Seq<NorBinding>,
        layout_limit: usize, gate_limit: usize, result: Result<ExpandedBody, ExpandedBodyError>,
    )
        requires
            self.projection_context(scope),
            self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings),
            self.expanded_bound_definitions_result(scope, prepared, selected, rows, bindings, layout_limit, gate_limit, result),
        ensures self.expanded_definition_lowering_result(scope, plan, table, prepared, selected, layout_limit, gate_limit, result),
    {
        reveal(UseAliases::expanded_definition_lowering_result);
    }

    /// ポートの検査に続く変換結果を、展開全体の契約に結び付ける。
    #[verifier::spinoff_prover]
    proof fn expanded_body_result_from_ports(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, ports: &PreparedBitFuncPorts, selected: Seq<ResolvedTemplateCall>,
        layout_limit: usize, gate_limit: usize, result: Result<ExpandedBody, ExpandedBodyError>,
    )
        requires
            self.expansion_selection_matches(plan, table, caller, prepared, selected),
            self.expanded_routine_ports_result(caller.0, caller.1, caller.2, &prepared.typed.literals.wiring->Checked_0,
                prepared.projections.layouts, selected, Ok(*ports)),
            self.expanded_definition_lowering_result(&self.expanded_projection_scope(caller, prepared, ports),
                plan, table, prepared, selected, layout_limit, gate_limit, result),
            !(result matches Err(ExpandedBodyError::Ports(_))),
            result matches Ok(expanded) ==> expanded.ports == *ports
                && (expanded.has_structure_ports <==>
                    has_structure_port(prepared.typed.literals.wiring->Checked_0.drivers.signature.inputs@)
                    || has_structure_port(prepared.typed.literals.wiring->Checked_0.drivers.signature.outputs@)),
        ensures self.expanded_body_lowering_result(plan, table, caller, prepared, layout_limit, gate_limit, result),
    {
        reveal(UseAliases::expanded_body_lowering_result);
    }

    /// 変換に使った NOR の束縛が、元の定義と同じ出力スロットを指すことを示す。
    #[verifier::spinoff_prover]
    proof fn expanded_nor_binding_evidence(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, rows: Seq<NorDefinition>, bindings: Seq<NorBinding>, i: int,
    )
        requires
            self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings),
            0 <= i < bindings.len(),
        ensures ({
            let binding = bindings[i];
            &&& binding.selected.prepared.output_slot == rows[i].root.output_slot
            &&& !call_covers(prepared.calls@, binding.selected.prepared.output_slot as int)
            &&& binding.candidate < prepared.nor_roots@.len()
            &&& *binding.selected.prepared == prepared.nor_roots@[binding.candidate as int]
            &&& binding.selected.prepared.definition < scope.parsed.definitions@.len()
            &&& *binding.references == scope.parsed.definitions@[binding.selected.prepared.definition as int].references
            &&& nor_definition_determined(binding.selected.prepared, prepared.projections.call_arguments.arguments@)
            &&& self.nor_binding_context(plan, table, scope.limit, prepared.projections.call_arguments.arguments@, binding)
        }),
    {
        let row = rows[i];
        let binding = bindings[i];
        let arguments = prepared.projections.call_arguments.arguments@;
        assert(0 <= i < rows.len() && self.body_nor_slots_match(
            scope, prepared.calls@, rows, prepared.projections.concats@)) by {
            reveal(UseAliases::nor_expansion_selection_matches);
        };
        assert(row.index < prepared.nor_roots@.len() && *row.root == prepared.nor_roots@[row.index as int]
            && self.nor_binding_matches(plan, table, scope.limit, scope.parsed, arguments, row, binding)) by {
            reveal(UseAliases::nor_expansion_selection_matches);
            reveal(nor_selection_prefix);
        };
        assert(!call_covers(prepared.calls@, row.root.output_slot as int)) by {
            reveal(UseAliases::body_nor_slots_match);
        };
        reveal(UseAliases::nor_binding_matches);
    }

    #[verifier::opaque]
    pub(super) open spec fn expanded_body_nor_bindings(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates, prepared: &PreparedExpansionBody,
        rows: Seq<NorDefinition>, bindings: Seq<NorBinding>, slots: Seq<CheckedBitDefinition>,
    ) -> bool {
        &&& rows.len() == bindings.len()
        &&& forall|i: int| 0 <= i < bindings.len() ==> {
            let binding = #[trigger] bindings[i];
            &&& binding.selected.prepared.output_slot == rows[i].root.output_slot
            &&& binding.selected.prepared.output_slot < slots.len()
            &&& !call_covers(prepared.calls@, binding.selected.prepared.output_slot as int)
            &&& binding.candidate < prepared.nor_roots@.len()
            &&& *binding.selected.prepared == prepared.nor_roots@[binding.candidate as int]
            &&& binding.selected.prepared.root.expression.source == scope.source
            &&& binding.selected.prepared.definition < scope.parsed.definitions@.len()
            &&& *binding.references == scope.parsed.definitions@[binding.selected.prepared.definition as int].references
            &&& nor_definition_determined(binding.selected.prepared, prepared.projections.call_arguments.arguments@)
            &&& self.nor_binding_context(plan, table, scope.limit, prepared.projections.call_arguments.arguments@, binding)
            &&& nor_binding_fits_body(binding, scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots, scope.limit)
        }
        &&& forall|i: int, j: int| 0 <= i < j < bindings.len() ==>
            (#[trigger] bindings[i]).selected.prepared.output_slot < (#[trigger] bindings[j]).selected.prepared.output_slot
        &&& forall|i: int| #[trigger] nor_binding_covers(bindings, i) <==> nor_covers(rows, i)
    }

    /// 変換で使った根 NOR の束縛と出力スロットを、参照評価が使う形にまとめる。
    #[verifier::spinoff_prover]
    proof fn expanded_body_nor_bindings_intro(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, rows: Seq<NorDefinition>, bindings: Seq<NorBinding>, slots: Seq<CheckedBitDefinition>,
    )
        requires
            self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings),
            forall|i: int| 0 <= i < bindings.len() ==> nor_binding_fits_body(
                #[trigger] bindings[i], scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots, scope.limit),
        ensures self.expanded_body_nor_bindings(scope, plan, table, prepared, rows, bindings, slots),
    {
        let arguments = prepared.projections.call_arguments.arguments@;
        assert(self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings));
        assert(rows.len() == bindings.len()) by { reveal(UseAliases::nor_expansion_selection_matches); };
        assert forall|i: int| 0 <= i < bindings.len() implies {
            let binding = #[trigger] bindings[i];
            &&& binding.selected.prepared.output_slot == rows[i].root.output_slot
            &&& binding.selected.prepared.output_slot < slots.len()
            &&& !call_covers(prepared.calls@, binding.selected.prepared.output_slot as int)
            &&& binding.candidate < prepared.nor_roots@.len()
            &&& *binding.selected.prepared == prepared.nor_roots@[binding.candidate as int]
            &&& binding.selected.prepared.root.expression.source == scope.source
            &&& binding.selected.prepared.definition < scope.parsed.definitions@.len()
            &&& *binding.references == scope.parsed.definitions@[binding.selected.prepared.definition as int].references
            &&& nor_definition_determined(binding.selected.prepared, arguments)
            &&& self.nor_binding_context(plan, table, scope.limit, arguments, binding)
            &&& nor_binding_fits_body(binding, scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots, scope.limit)
        } by {
            let binding = bindings[i];
            assert(nor_binding_fits_body(binding, scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots, scope.limit));
            self.expanded_nor_binding_evidence(scope, plan, table, prepared, rows, bindings, i);
        };
        assert forall|i: int, j: int| 0 <= i < j < bindings.len() implies
            (#[trigger] bindings[i]).selected.prepared.output_slot < (#[trigger] bindings[j]).selected.prepared.output_slot by {
            reveal(UseAliases::nor_expansion_selection_matches);
        };
        assert forall|i: int| #[trigger] nor_binding_covers(bindings, i) <==> nor_covers(rows, i) by {
            if nor_binding_covers(bindings, i) {
                let j = choose|j: int| 0 <= j < bindings.len() && (#[trigger] bindings[j]).selected.prepared.output_slot == i;
                assert(rows[j].root.output_slot == i);
            }
            if nor_covers(rows, i) {
                let j = choose|j: int| 0 <= j < rows.len() && (#[trigger] rows[j]).root.output_slot == i;
                assert(bindings[j].selected.prepared.output_slot == i);
            }
        };
        reveal(UseAliases::expanded_body_nor_bindings);
    }

    /// ポートの準備と定義の変換が参照した呼び出し先を、依存順に取り出す。
    #[verifier::spinoff_prover]
    proof fn expanded_success_call_selection<'w>(
        &self, plan: &FunctionExpansionOrder, table: &'w FunctionTemplates<'p, 'a>, caller: (usize, usize, u64),
        prepared: &'w PreparedExpansionBody<'p, 'a>, bit_limit: usize, gate_limit: usize, value: &'w ExpandedBody<'p, 'a>,
    ) -> (selected: Seq<ResolvedTemplateCall<'w, 'p, 'a>>)
        requires self.expanded_body_lowering_result(plan, table, caller, prepared, bit_limit, gate_limit, Ok(*value)),
        ensures
            self.expansion_selection_matches(plan, table, caller, prepared, selected),
            self.expanded_routine_ports_result(caller.0, caller.1, caller.2, &prepared.typed.literals.wiring->Checked_0,
                prepared.projections.layouts, selected, Ok(value.ports)),
            self.expanded_definition_lowering_result(&self.expanded_projection_scope(caller, prepared, &value.ports),
                plan, table, prepared, selected, bit_limit, gate_limit, Ok(*value)),
            value.has_structure_ports <==> has_structure_port(prepared.typed.literals.wiring->Checked_0.drivers.signature.inputs@)
                || has_structure_port(prepared.typed.literals.wiring->Checked_0.drivers.signature.outputs@),
    {
        let (file, entry, limit) = caller;
        let ports = &value.ports;
        let scope = self.expanded_projection_scope(caller, prepared, ports);
        let wiring = scope.wiring;
        reveal(UseAliases::expanded_body_lowering_result);
        let selected = choose|rows: Seq<ResolvedTemplateCall<'w, 'p, 'a>>|
            #[trigger] self.expansion_selection_matches(plan, table, caller, prepared, rows)
            && self.expanded_routine_ports_result(file, entry, limit, wiring, prepared.projections.layouts, rows, Ok(*ports))
            && self.expanded_definition_lowering_result(&scope, plan, table, prepared, rows, bit_limit, gate_limit, Ok(*value));
        selected
    }

    /// 展開結果から、その変換に使った定義列と NOR の束縛を取り出す。
    #[verifier::spinoff_prover]
    proof fn expanded_success_definition_selection<'w>(
        &self, scope: &FuncProjection<'w, 'p, 'a>, plan: &FunctionExpansionOrder, table: &'w FunctionTemplates<'p, 'a>,
        prepared: &'w PreparedExpansionBody<'p, 'a>, selected: Seq<ResolvedTemplateCall<'w, 'p, 'a>>,
        bit_limit: usize, gate_limit: usize, value: &ExpandedBody<'p, 'a>,
    ) -> (witness: (Seq<NorDefinition<'w, 'p, 'a>>, Seq<NorBinding<'w, 'p, 'a>>, Vec<CheckedBitDefinition<'p, 'a>>))
        requires self.expanded_definition_lowering_result(scope, plan, table, prepared, selected, bit_limit, gate_limit, Ok(*value)),
        ensures ({
            let (rows, bindings, slots) = witness;
            &&& self.projection_context(scope)
            &&& self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings)
            &&& self.prepared_definition_result(scope, prepared.calls@, selected, rows, Ok(slots))
            &&& self.expanded_slots_result(scope, selected, bindings, prepared.projections.call_arguments.arguments@,
                slots, bit_limit, gate_limit, Ok(*value))
        }),
    {
        let (rows, bindings) = choose|rows: Seq<NorDefinition<'w, 'p, 'a>>, bindings: Seq<NorBinding<'w, 'p, 'a>>|
            #[trigger] self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings)
            && self.expanded_bound_definitions_result(scope, prepared, selected, rows, bindings, bit_limit, gate_limit, Ok(*value));
        assert(self.projection_context(scope)
            && self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings)
            && self.expanded_bound_definitions_result(scope, prepared, selected, rows, bindings, bit_limit, gate_limit, Ok(*value))) by {
            reveal(UseAliases::expanded_definition_lowering_result);
        };
        let arguments = prepared.projections.call_arguments.arguments@;
        let slots = choose|slots: Vec<CheckedBitDefinition>|
            #[trigger] self.prepared_definition_result(scope, prepared.calls@, selected, rows, Ok(slots))
            && self.expanded_slots_result(scope, selected, bindings, arguments, slots, bit_limit, gate_limit, Ok(*value));
        assert(self.prepared_definition_result(scope, prepared.calls@, selected, rows, Ok(slots))
            && self.expanded_slots_result(scope, selected, bindings, arguments, slots, bit_limit, gate_limit, Ok(*value))) by {
            reveal(UseAliases::expanded_bound_definitions_result);
        };
        (rows, bindings, slots)
    }

    /// 展開結果から、元の宣言に対応するポートと、各定義の変換に使った呼び出しや出力スロットを取り出す。
    #[verifier::spinoff_prover]
    pub(super) proof fn expanded_body_success<'w>(
        &self, plan: &FunctionExpansionOrder, table: &'w FunctionTemplates<'p, 'a>, caller: (usize, usize, u64),
        prepared: &'w PreparedExpansionBody<'p, 'a>, bit_limit: usize, gate_limit: usize, value: &'w ExpandedBody<'p, 'a>,
    ) -> (witness: (FuncProjection<'w, 'p, 'a>, Seq<ResolvedTemplateCall<'w, 'p, 'a>>,
        Seq<NorDefinition<'w, 'p, 'a>>, Seq<NorBinding<'w, 'p, 'a>>, Vec<CheckedBitDefinition<'p, 'a>>))
        requires self.expanded_body_lowering_result(plan, table, caller, prepared, bit_limit, gate_limit, Ok(*value)),
        ensures ({
            let (scope, selected, rows, bindings, slots) = witness;
            let (file, entry, limit) = caller;
            let project = self.targets.project_model();
            let wiring = &prepared.typed.literals.wiring->Checked_0;
            let ports = &value.ports;
            let drivers = wiring.drivers.outputs@;
            &&& scope == (FuncProjection {
                file, entry, limit, source: &project.sources_model()[file as int],
                parsed: &project.circuits_model()[file as int], wiring, inputs: &ports.inputs, outputs: &ports.outputs,
                layouts: match &ports.layouts { Some(table) => Some(table), None => None },
                types: &prepared.typed.types, structures: &prepared.projections.entries,
            })
            &&& self.projection_context(&scope)
            &&& self.projection_port_widths_match(&scope)
            &&& self.prepared_expansion_body_matches(*plan, file, entry, limit, prepared)
                ==> self.projection_structures_match(&scope)
            &&& self.expansion_selection_matches(plan, table, caller, prepared, selected)
            &&& self.expanded_routine_ports_result(file, entry, limit, wiring, prepared.projections.layouts, selected, Ok(*ports))
            &&& self.prepared_definition_result(&scope, prepared.calls@, selected, rows, Ok(slots))
            &&& self.expanded_body_nor_bindings(&scope, plan, table, prepared, rows, bindings, slots@)
            &&& form_spans_valid(scope.source.text, scope.parsed.syntax.forms@, scope.source.text.spec_bytes().len() as int)
            &&& output_widths_before(ports.inputs@, ports.outputs@, slots@, drivers, drivers.len() as int)
            &&& projected_lowering_view(ports.inputs@, slots@, ports.outputs@, drivers, scope.parsed.syntax.forms@,
                selected, bindings, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, Ok(value.circuit))
            &&& value.has_structure_ports <==> has_structure_port(wiring.drivers.signature.inputs@)
                || has_structure_port(wiring.drivers.signature.outputs@)
        }),
    {
        let (file, entry, limit) = caller;
        let ports = &value.ports;
        let scope = self.expanded_projection_scope(caller, prepared, ports);
        let wiring = scope.wiring;
        let parsed = scope.parsed;
        let selected = self.expanded_success_call_selection(plan, table, caller, prepared, bit_limit, gate_limit, value);
        let (rows, bindings, slots) = self.expanded_success_definition_selection(
            &scope, plan, table, prepared, selected, bit_limit, gate_limit, value);
        let arguments = prepared.projections.call_arguments.arguments@;
        assert forall|i: int| 0 <= i < bindings.len() implies nor_binding_fits_body(
            #[trigger] bindings[i], scope.source, scope.parsed.syntax.forms@, scope.inputs@, slots@, limit) by {
            reveal(UseAliases::expanded_slots_result);
        };
        let drivers = wiring.drivers.outputs@;
        assert(output_widths_before(ports.inputs@, ports.outputs@, slots@, drivers, drivers.len() as int)
            && projected_lowering_view(ports.inputs@, slots@, ports.outputs@, drivers, parsed.syntax.forms@,
                selected, bindings, arguments, bit_limit, gate_limit, Ok(value.circuit))) by {
            reveal(UseAliases::expanded_slots_result);
        };
        assert(form_spans_valid(scope.source.text, scope.parsed.syntax.forms@, scope.source.text.spec_bytes().len() as int)) by {
            reveal(UseAliases::prepared_definition_result);
        };
        self.expanded_body_nor_bindings_intro(&scope, plan, table, prepared, rows, bindings, slots@);
        reveal(UseAliases::routine_ports_result);
        assert(self.projection_port_widths_match(&scope));
        assert(self.prepared_expansion_body_matches(*plan, file, entry, limit, prepared)
            ==> self.projection_structures_match(&scope)) by {
            if prepared.projections.layouts.is_none() {
                assert(self.prepared_expansion_body_matches(*plan, file, entry, limit, prepared)
                    ==> prepared.projections.entries@.len() == 0);
            }
        };
        (scope, selected, rows, bindings, slots)
    }

    pub(in crate::project::use_aliases::bit_func) closed spec fn expanded_gate_origin_link(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
        prepared: &PreparedExpansionBody, bit_limit: usize, gate_limit: usize, value: &ExpandedBody,
        gate: int, origin: FuncGateOrigin,
    ) -> bool {
        let parsed = self.targets.project_model().circuits_model()[caller.0 as int];
        let wiring = prepared.typed.literals.wiring->Checked_0;
        let ports = &value.ports;
        let forms = parsed.syntax.forms@;
        let arguments = prepared.projections.call_arguments.arguments@;
        exists|scope: FuncProjection, selected: Seq<ResolvedTemplateCall>, rows: Seq<NorDefinition>,
            bindings: Seq<NorBinding>, slots: Vec<CheckedBitDefinition>|
            #![trigger self.prepared_definition_result(&scope, prepared.calls@, selected, rows, Ok(slots)),
                projected_gate_origin_link(ports.inputs@, slots@, ports.outputs@, wiring.drivers.outputs@,
                    forms, selected, bindings, arguments, bit_limit, gate_limit, &value.circuit, gate, origin)]
            scope == self.expanded_projection_scope(caller, prepared, ports) && self.projection_context(&scope)
            && self.prepared_definition_result(&scope, prepared.calls@, selected, rows, Ok(slots))
            && self.expansion_selection_matches(plan, table, caller, prepared, selected)
            && self.expanded_body_nor_bindings(&scope, plan, table, prepared, rows, bindings, slots@)
            && projected_gate_origin_link(ports.inputs@, slots@, ports.outputs@, wiring.drivers.outputs@,
                forms, selected, bindings, arguments, bit_limit, gate_limit, &value.circuit, gate, origin)
    }

    spec fn gate_template_matches(
        plan: &FunctionExpansionOrder, table: &FunctionTemplates, target: FuncCallTarget,
        template: Option<&super::super::templates::FunctionTemplate>, rank: Option<int>,
    ) -> bool {
        match (rank, template, target) {
            (None, None, FuncCallTarget::Nor) => true,
            (Some(r), Some(value), FuncCallTarget::Function { file, entry, .. }) => {
                &&& 0 <= r < table.next_rank() && r < plan.order_model().len()
                &&& plan.position_model(r) == Some((file, entry))
                &&& plan.order_model()[r] < table.slots_model().len()
                &&& table.slots_model()[plan.order_model()[r] as int] == Some(*value)
            },
            _ => false,
        }
    }

    /// 展開したゲートに対応する厳格索引の呼び出し位置と、通常関数の展開順位を得る。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases::bit_func) proof fn expanded_body_gate_source<'w>(
        &self, plan: &FunctionExpansionOrder, table: &'w FunctionTemplates<'p, 'a>, caller: (usize, usize, u64),
        prepared: &'w PreparedExpansionBody<'p, 'a>, bit_limit: usize, gate_limit: usize,
        value: &'w ExpandedBody<'p, 'a>, gate: int,
    ) -> (result: (crate::project::DefinitionPosition, TypedFuncCall<'p, 'a>, Option<int>, FuncGateOrigin<'w, 'p, 'a>))
        requires
            self.can_resolve(), self.function_template_plan(*plan),
            plan.position_model(table.next_rank() as int) == Some((caller.0, caller.1)),
            table.slots_model().len() == plan.order_model().len(),
            self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
            self.expanded_body_lowering_result(plan, table, caller, prepared, bit_limit, gate_limit, Ok(*value)),
            0 <= gate < value.circuit.netlist_model().gates@.len(),
        ensures
            self.expanded_gate_origin_link(plan, table, caller, prepared, bit_limit, gate_limit, value, gate, result.3),
            ({
                let (site, signature, _, origin) = result;
                let parsed = self.targets.project_model().circuits_model()[caller.0 as int];
                let wiring = prepared.typed.literals.wiring->Checked_0;
                &&& site.file == caller.0 && site.entry == caller.1 && site.reference == origin.reference
                &&& origin.slot < wiring.drivers.definitions@.len()
                &&& parsed.entry_ranges@[caller.1 as int].definitions.start + site.definition
                    == wiring.drivers.definitions@[origin.slot as int].definition
                &&& self.func_call_signature_evidence(site.file, site.entry, site.definition, site.reference, caller.2, Ok(Some(signature)))
            }),
            ({
                let (_, signature, rank, origin) = result;
                match (rank, origin.template, signature.call.target) {
                    (None, None, FuncCallTarget::Nor) => gate == origin.base,
                    (Some(r), Some(template), FuncCallTarget::Function { file, entry, .. }) => {
                        let callee = template.circuit_model().netlist_model();
                        let parent = value.circuit.netlist_model().gates@;
                        let end = origin.base + callee.gates@.len();
                        &&& 0 <= r < table.next_rank() && r < plan.order_model().len()
                        &&& plan.position_model(r) == Some((file, entry))
                        &&& plan.order_model()[r] < table.slots_model().len()
                        &&& table.slots_model()[plan.order_model()[r] as int] == Some(*template)
                        &&& origin.base <= gate < end <= parent.len()
                        &&& crate::netlist::instances::instance_gates_match(parent.take(origin.base as int),
                            callee.gates@, origin.inputs, parent.take(end as int))
                    },
                    _ => false,
                }
            }),
    {
        self.function_template_indices(*plan);
        let (scope, selected, rows, bindings, slots) = self.expanded_body_success(
            plan, table, caller, prepared, bit_limit, gate_limit, value);
        let (file, entry, limit) = caller;
        let parsed = scope.parsed;
        let ports = &value.ports;
        let arguments = prepared.projections.call_arguments.arguments@;
        let origin = projected_lowering_gate_origin(ports.inputs@, slots@, ports.outputs@, scope.wiring.drivers.outputs@,
            parsed.syntax.forms@, selected, bindings, arguments, bit_limit, gate_limit, &value.circuit, gate);
        reveal(UseAliases::expanded_body_nor_bindings);
        assert(self.expanded_gate_origin_link(plan, table, caller, prepared, bit_limit, gate_limit, value, gate, origin));
        assert(self.expansion_selection_matches(plan, table, caller, prepared, selected));
        self.prepared_definition_width_evidence(&scope, prepared.calls@, selected, rows, slots);
        let slot = origin.slot as int;
        let absolute = scope.wiring.drivers.definitions@[slot].definition;
        let frame = parsed.entry_ranges@[entry as int].definitions;
        let definition = (absolute - frame.start) as usize;
        let site = crate::project::DefinitionPosition { file, entry, definition, reference: origin.reference };
        let (signature, rank) = match origin.expression {
            FuncGateExpression::Local => {
                assert(!call_covers(prepared.calls@, slot)) by {
                    if call_covers(prepared.calls@, slot) {
                        let group = choose|g: int| 0 <= g < prepared.calls@.len()
                            && (#[trigger] prepared.calls@[g]).outputs.start <= slot < prepared.calls@[g].outputs.end;
                        assert(*selected[group].group == prepared.calls@[group]);
                    }
                };
                let local = self.local_nor_source_site(&scope, prepared.calls@, selected, rows, slots, slot);
                assert(local.0 == site);
                assert(Self::gate_template_matches(plan, table, local.1.call.target, origin.template, None));
                (local.1, None)
            },
            FuncGateExpression::Function { group, child } => {
                let root = prepared.projections.calls@[group];
                let checked = prepared.calls@[group];
                let chosen = selected[group];
                assert(0 <= group < selected.len() == prepared.calls@.len());
                assert(*chosen.group == checked);
                assert(origin.slot == checked.outputs.start);
                self.expansion_callee_template_evidence(*plan, caller, prepared, group);
                assert(checked.outputs.start <= slot < checked.outputs.end);
                self.prepared_call_matches_source_site(plan, caller, prepared, group);
                self.source_function_call_site_evidence(caller, scope.wiring, slot, root.definition,
                    checked._signature@, checked.outputs, (root.target_file, root.target_entry));
                assert(absolute == root.definition);
                if let Some(index) = child {
                    let expanded = chosen.children@[index];
                    assert(checked.postorder.is_some());
                    let children = checked.postorder->Some_0@;
                    assert(self.resolved_expression_calls_match(plan, table, limit, checked.postorder, arguments, chosen.children@));
                    assert(0 <= index < chosen.children@.len() == children.len());
                    let piece = children[index];
                    assert(self.resolved_expression_call_matches(plan, table, limit, arguments, piece, expanded));
                    self.expansion_child_template_evidence(*plan, caller, prepared, group, index);
                    assert(expanded.child.reference == chosen.group.references.start + origin.reference);
                    assert(*expanded.child == piece) by { reveal(UseAliases::resolved_expression_call_matches); };
                    assert(piece.reference == checked.references.start + origin.reference);
                    assert(origin.template == expanded.template);
                    assert(match piece._signature@.call.target {
                        FuncCallTarget::Nor => piece._rank@.is_none(),
                        FuncCallTarget::Function { file, entry, .. } =>
                            piece._rank@ matches Some(rank) && plan.position_model(rank) == Some((file, entry)),
                    });
                    assert(Self::gate_template_matches(plan, table, piece._signature@.call.target, origin.template, piece._rank@)) by {
                        reveal(UseAliases::resolved_expression_call_matches);
                    };
                    (piece._signature@, piece._rank@)
                } else {
                    self.function_template_rank_at(*plan, (file, entry), checked._order@.1, table.next_rank() as int);
                    assert(plan.order_model()[checked._order@.0] == checked.vertex);
                    assert(Self::gate_template_matches(plan, table, checked._signature@.call.target, origin.template,
                        Some(checked._order@.0)));
                    (checked._signature@, Some(checked._order@.0))
                }
            },
            FuncGateExpression::Nor { binding, index } => {
                let binding = bindings[binding];
                let candidate = binding.candidate as int;
                let root = prepared.nor_roots@[candidate];
                assert(*binding.selected.prepared == root);
                self.prepared_nor_output_evidence(*plan, caller, prepared, candidate);
                self.nor_root_template_evidence(*plan, caller, prepared, candidate);
                assert(absolute == root.definition);
                let children = root.postorder@;
                assert(self.nor_binding_context(plan, table, limit, arguments, binding));
                assert(self.resolved_expression_calls_match(plan, table, limit, Some(root.postorder), arguments, binding.selected.children@));
                assert(binding.selected.children@.len() == children.len());
                self.prepared_nor_arguments_in_source_order(*plan, caller, prepared, candidate, index);
                if index == children.len() {
                    assert(Self::gate_template_matches(plan, table, root.root._signature@.call.target, origin.template, None));
                    (root.root._signature@, None)
                } else {
                    let expanded = binding.selected.children@[index];
                    let piece = children[index];
                    assert(self.resolved_expression_call_matches(plan, table, limit, arguments, piece, expanded));
                    assert(*expanded.child == piece) by { reveal(UseAliases::resolved_expression_call_matches); };
                    assert(piece.reference == binding.references.start + origin.reference);
                    assert(origin.template == expanded.template);
                    assert(match piece._signature@.call.target {
                        FuncCallTarget::Nor => piece._rank@.is_none(),
                        FuncCallTarget::Function { file, entry, .. } =>
                            piece._rank@ matches Some(rank) && plan.position_model(rank) == Some((file, entry)),
                    });
                    assert(Self::gate_template_matches(plan, table, piece._signature@.call.target, origin.template, piece._rank@)) by {
                        reveal(UseAliases::resolved_expression_call_matches);
                    };
                    (piece._signature@, piece._rank@)
                }
            },
        };
        assert(self.func_call_signature_evidence(site.file, site.entry, site.definition, site.reference, limit, Ok(Some(signature))));
        self.typed_call_arguments_ready(site.file, site.entry, site.definition, site.reference, limit, signature);
        assert(Self::gate_template_matches(plan, table, signature.call.target, origin.template, rank));
        if let Some(r) = rank {
            assert(origin.template.is_some());
            let template = origin.template->Some_0;
            assert(signature.call.target is Function);
            assert(0 <= r < table.next_rank());
            assert(r < plan.order_model().len());
            assert(plan.position_model(r) == Some((signature.call.target->Function_file, signature.call.target->Function_entry)));
            assert(plan.order_model()[r] < table.slots_model().len());
            assert(table.slots_model()[plan.order_model()[r] as int] == Some(*template));
            let callee = template.circuit_model().netlist_model();
            let parent = value.circuit.netlist_model().gates@;
            let end = origin.base + callee.gates@.len();
            assert(origin.base <= gate < end <= parent.len());
            assert(crate::netlist::instances::instance_gates_match(parent.take(origin.base as int),
                callee.gates@, origin.inputs, parent.take(end as int)));
        } else {
            assert(origin.template.is_none());
            assert(signature.call.target is Nor);
            assert(gate == origin.base);
        }
        (site, signature, rank, origin)
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
        let (scope, selected, _, bindings, slots) = self.expanded_body_success(plan, table, caller, prepared, bit_limit, gate_limit, value);
        let wiring = scope.wiring;
        let ports = &value.ports;
        let drivers = wiring.drivers.outputs@;
        self.checked_wiring_is_func(file, entry, limit, *wiring);
        reveal(UseAliases::routine_ports_result);
        reveal(UseAliases::template_port_widths_match);
        projected_lowering_ports(ports.inputs@, slots@, ports.outputs@, drivers, scope.parsed.syntax.forms@,
            selected, bindings, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, &value.circuit);
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
        let (scope, selected, _, bindings, slots) = self.expanded_body_success(plan, table, caller, prepared, bit_limit, gate_limit, value);
        let circuit = &value.circuit;
        let netlist = circuit.netlist_model();
        let drivers = scope.wiring.drivers.outputs@;
        projected_lowering_ports(scope.inputs@, slots@, scope.outputs@, drivers, scope.parsed.syntax.forms@,
            selected, bindings, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, circuit);
        reveal(UseAliases::routine_ports_result);
        reveal(nor_evaluation);
        vstd::std_specs::vec::axiom_spec_len(&netlist.gates);
        let gates = choose|gates: Seq<bool>| #[trigger] gate_values_match(input, netlist.gates@, gates)
            && gates.len() == netlist.gates@.len() && output_values_match(input, gates, netlist.outputs@, output);
        reveal(UseAliases::template_port_widths_match);
        projected_lowering_output_values(scope.inputs@, slots@, scope.outputs@, drivers, scope.parsed.syntax.forms@,
            selected, bindings, prepared.projections.call_arguments.arguments@, bit_limit, gate_limit, circuit, input, gates, output);
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
        let (scope, selected, rows, bindings, slots) = self.expanded_body_success(plan, table, caller, prepared, bit_limit, gate_limit, value);
        let call = selected[index];
        let root = prepared.projections.calls@[index];
        let forms = scope.parsed.syntax.forms@;
        let drivers = scope.wiring.drivers.outputs@;
        let values = expanded_definition_values(&value.circuit, input, gates);
        self.prepared_call_matches_source_site(plan, caller, prepared, index);
        reveal(UseAliases::routine_ports_result);
        reveal(UseAliases::template_port_widths_match);
        reveal(UseAliases::prepared_definition_result);
        assert(!nor_binding_covers(bindings, call.group.outputs.start as int)) by {
            reveal(UseAliases::expanded_body_nor_bindings);
            assert(self.expanded_body_nor_bindings(&scope, plan, table, prepared, rows, bindings, slots@));
            let at = call.group.outputs.start as int;
            if nor_binding_covers(bindings, at) {
                let i = choose|i: int| 0 <= i < bindings.len() && (#[trigger] bindings[i]).selected.prepared.output_slot == at;
                assert(call.group.outputs.start < call.group.outputs.end);
                assert(*call.group == prepared.calls@[index]);
                assert(call_covers(prepared.calls@, at));
                assert(!call_covers(prepared.calls@, bindings[i].selected.prepared.output_slot as int));
            }
        };
        let evidence = projected_lowering_call_evaluation(self, plan, caller, prepared, scope.inputs@,
            slots@, scope.outputs@, drivers, forms, selected, bindings, index, bit_limit, gate_limit, &value.circuit, input, gates);
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

    /// 型検査を済ませた定義に対応する根 NOR の入力と出力を、配線の契約に結び付ける。
    #[verifier::spinoff_prover]
    proof fn prepared_nor_bindings_fit_slots(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, selected: Seq<ResolvedTemplateCall>, rows: Seq<NorDefinition>, bindings: Seq<NorBinding>,
        definitions: Vec<CheckedBitDefinition>,
    )
        requires
            self.projection_context(scope), self.projection_port_widths_match(scope),
            self.structure_layout_for_ports(scope.limit, scope.layouts),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings),
            self.prepared_definition_result(scope, prepared.calls@, selected, rows, Ok(definitions)),
        ensures
            forall|i: int| 0 <= i < bindings.len() ==> nor_binding_fits_body(
                #[trigger] bindings[i], scope.source, scope.parsed.syntax.forms@, scope.inputs@, definitions@, scope.limit),
            forall|at: int| 0 <= at < definitions@.len() && !nor_binding_covers(bindings, at) && !call_covers(prepared.calls@, at) ==>
                bit_definition_matches(scope.inputs@, definitions@.take(at), #[trigger] definitions@[at]),
    {
        let slots = definitions@;
        assert(slots.len() == scope.wiring.drivers.definitions@.len()
            && self.expansion_definition_prefix(scope, prepared.calls@, rows, slots)
            && self.definition_widths_match(scope, slots)) by {
            reveal(UseAliases::prepared_definition_result);
        };
        assert(self.body_nor_slots_match(scope, prepared.calls@, rows, prepared.projections.concats@)
            && rows.len() == bindings.len()) by {
            reveal(UseAliases::nor_expansion_selection_matches);
        };
        assert forall|i: int| 0 <= i < rows.len() implies {
            let row = #[trigger] rows[i];
            row.index < prepared.nor_roots@.len() && *row.root == prepared.nor_roots@[row.index as int]
        } by {
            reveal(UseAliases::nor_expansion_selection_matches);
            reveal(nor_selection_prefix);
        };
        assert forall|i: int| 0 <= i < bindings.len() implies self.nor_binding_matches(plan, table, scope.limit, scope.parsed,
            prepared.projections.call_arguments.arguments@, rows[i], #[trigger] bindings[i]) by {
            reveal(UseAliases::nor_expansion_selection_matches);
            assert(i < rows.len());
            assert(rows[i].index < prepared.nor_roots@.len());
        };
        self.nor_bindings_fit_projection(scope, plan, table, prepared, rows, bindings, slots);
        assert forall|at: int| 0 <= at < slots.len()
            && !nor_binding_covers(bindings, at) && !call_covers(prepared.calls@, at) implies
            bit_definition_matches(scope.inputs@, slots.take(at), #[trigger] slots[at]) by {
            let definition = slots[at];
            assert((definition.rhs is NorCallOutput) == nor_binding_covers(bindings, at));
            assert(bit_definition_matches(scope.inputs@, slots.take(at), definition));
        };
    }

    /// 展開できる根 NOR がすべて選ばれ、一つずつ対応する束縛を持つことを示す。
    #[verifier::spinoff_prover]
    proof fn nor_expansion_selection_intro(
        &self, scope: &FuncProjection, plan: &FunctionExpansionOrder, table: &FunctionTemplates,
        prepared: &PreparedExpansionBody, rows: Seq<NorDefinition>, bindings: Seq<NorBinding>,
    )
        requires
            rows.len() == bindings.len(),
            self.body_nor_slots_match(scope, prepared.calls@, rows, prepared.projections.concats@),
            nor_selection_prefix(prepared, prepared.nor_roots@.len() as int, rows),
            forall|i: int| 0 <= i < bindings.len() ==> self.nor_binding_matches(plan, table, scope.limit, scope.parsed,
                prepared.projections.call_arguments.arguments@, rows[i], #[trigger] bindings[i]),
            nor_selection_covers(prepared, prepared.nor_roots@.len() as int, nor_selection_indices(rows)),
            forall|i: int, j: int| 0 <= i < j < bindings.len() ==>
                (#[trigger] bindings[i]).selected.prepared.output_slot < (#[trigger] bindings[j]).selected.prepared.output_slot,
        ensures self.nor_expansion_selection_matches(scope, plan, table, prepared, rows, bindings),
    {
        reveal(UseAliases::nor_expansion_selection_matches);
    }

    /// 展開できる根 NOR を選び、厳格解析で得た呼び出し元の位置と依存先を確定する。
    #[verifier::spinoff_prover]
    fn select_expansion_nor_bindings<'s>(
        &self, scope: &FuncProjection<'_, 'p, 'a>, plan: &FunctionExpansionOrder<'p, 'a>,
        table: &'s FunctionTemplates<'p, 'a>, candidates: &'s [PreparedNorRoot<'p, 'a>],
        arguments: &'s [ProjectedCallArgument], Ghost(prepared): Ghost<&PreparedExpansionBody<'p, 'a>>,
    ) -> (selection: (Vec<NorDefinition<'s, 'p, 'a>>, Vec<NorBinding<'s, 'p, 'a>>))
        requires
            self.projection_context(scope), self.projection_structures_match(scope),
            self.can_resolve(), self.function_template_plan(*plan),
            self.function_templates_match(plan, scope.limit, table),
            plan.position_model(table.next_rank() as int) == Some((scope.file, scope.entry)),
            self.prepared_expansion_body_matches(*plan, scope.file, scope.entry, scope.limit, prepared),
            prepared.typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prepared.typed.types@ == scope.types@,
            candidates@ == prepared.nor_roots@,
            arguments@ == prepared.projections.call_arguments.arguments@,
        ensures
            self.body_nor_slots_match(scope, prepared.calls@, selection.0@, prepared.projections.concats@),
            self.nor_expansion_selection_matches(scope, plan, table, prepared, selection.0@, selection.1@),
            forall|i: int, j: int| 0 <= i < j < selection.1@.len() ==>
                (#[trigger] selection.1@[i]).selected.prepared.output_slot < (#[trigger] selection.1@[j]).selected.prepared.output_slot,
    {
        let ghost caller = (scope.file, scope.entry, scope.limit);
        let rows = self.select_nor_definitions(candidates, arguments, Ghost(prepared), Ghost(*plan), Ghost(caller));
        let bindings = self.resolve_selected_nor_roots(plan, table, arguments, rows.as_slice(), scope.parsed,
            Ghost(prepared), Ghost(caller));
        proof {
            self.prepared_nor_slots_fit_body(scope, *plan, prepared, rows@);
            self.nor_expansion_selection_intro(scope, plan, table, prepared, rows@, bindings@);
        }
        (rows, bindings)
    }

    /// 検査済みの定義に対し、出力幅を確認してからネットリストを組み立てる。
    ///
    /// # Errors
    ///
    /// 出力幅に不一致があれば、その診断を返す。
    /// 幅が一致した場合は、ビット範囲の割り当てや配線変換に失敗したときに診断を返す。
    #[verifier::spinoff_prover]
    fn lower_expanded_slots<'w>(
        &self, scope: &FuncProjection<'w, 'p, 'a>, ports: &'w PreparedBitFuncPorts<'p, 'a>,
        selected: &[ResolvedTemplateCall<'w, 'p, 'a>], roots: &[NorBinding<'w, 'p, 'a>],
        definitions: &Vec<CheckedBitDefinition<'p, 'a>>, layout_limit: usize, gate_limit: usize,
        Ghost(context): Ghost<(&FunctionExpansionOrder<'p, 'a>, &FunctionTemplates<'p, 'a>, (usize, usize, u64),
            &PreparedExpansionBody<'p, 'a>, Seq<NorDefinition<'w, 'p, 'a>>)>,
    ) -> (result: Result<LoweredBitFunc, ExpandedBodyError<'p, 'a>>)
        requires ({
            let (plan, templates, caller, prepared, rows) = context;
            &&& self.projection_context(scope)
            &&& self.projection_port_widths_match(scope)
            &&& *scope == self.expanded_projection_scope(caller, prepared, ports)
            &&& self.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared)
            &&& self.expansion_selection_matches(plan, templates, caller, prepared, selected@)
            &&& self.nor_expansion_selection_matches(scope, plan, templates, prepared, rows, roots@)
            &&& self.prepared_definition_result(scope, prepared.calls@, selected@, rows, Ok(*definitions))
            &&& forall|i: int| 0 <= i < roots@.len() ==> nor_binding_fits_body(
                #[trigger] roots@[i], scope.source, scope.parsed.syntax.forms@, scope.inputs@, definitions@, scope.limit)
            &&& forall|a: int, b: int| 0 <= a < b < roots@.len() ==>
                (#[trigger] roots@[a]).selected.prepared.output_slot < (#[trigger] roots@[b]).selected.prepared.output_slot
            &&& forall|slot: int| 0 <= slot < definitions@.len() && !call_covers(prepared.calls@, slot)
                && !nor_binding_covers(roots@, slot) ==>
                    bit_definition_matches(scope.inputs@, definitions@.take(slot), #[trigger] definitions@[slot])
        }),
        ensures result matches Err(error) ==> error is Output || error is Lowering,
        ({
            let prepared = context.3;
            let wiring = scope.wiring;
            let has_structures = has_structure_port(wiring.drivers.signature.inputs@)
                || has_structure_port(wiring.drivers.signature.outputs@);
            let expanded = match result {
                Ok(circuit) => Ok(ExpandedBody { circuit, ports: *ports, has_structure_ports: has_structures }),
                Err(error) => Err(error),
            };
            self.expanded_slots_result(scope, selected@, roots@, prepared.projections.call_arguments.arguments@,
                *definitions, layout_limit, gate_limit, expanded)
        }),
    {
        let ghost (plan, templates, caller, prepared, rows) = context;
        let ghost limit = scope.limit;
        let ghost arguments = prepared.projections.call_arguments.arguments@;
        let wiring = scope.wiring;
        let ghost source = scope.source;
        let ghost has_structures = has_structure_port(wiring.drivers.signature.inputs@)
            || has_structure_port(wiring.drivers.signature.outputs@);
        assert(form_spans_valid(source.text, scope.parsed.syntax.forms@, source.text.spec_bytes().len() as int)) by {
            reveal(UseAliases::prepared_definition_result);
        };
        proof { reveal(UseAliases::prepared_definition_result); }
        if let Err(error) = check_output_widths(wiring, ports.inputs.as_slice(), ports.outputs.as_slice(), definitions.as_slice()) {
            let diagnostic = ExpandedBodyError::Output(error);
            assert(self.expanded_slots_result(scope, selected@, roots@, arguments, *definitions,
                layout_limit, gate_limit, Err(diagnostic))) by { reveal(UseAliases::expanded_slots_result); };
            return Err(diagnostic);
        }
        let forms = scope.parsed.syntax.forms.as_slice();
        proof {
            assert forall|g: int| 0 <= g < selected@.len() implies
                resolved_call_fits_body(#[trigger] selected@[g], ports.inputs@, definitions@, forms@, limit) by {
                assert(*selected@[g].group.expression.source == *source);
            };
        }
        assert forall|i: int| 0 <= i < roots@.len() implies {
            let binding = #[trigger] roots@[i];
            let origin = binding.selected.prepared.root.expression.source;
            &&& !call_covers(prepared.calls@, binding.selected.prepared.output_slot as int)
            &&& nor_binding_fits_body(binding, origin, forms@, ports.inputs@, definitions@, limit)
            &&& self.nor_binding_context(plan, templates, limit, arguments, binding)
            &&& form_spans_valid(origin.text, forms@, origin.text.spec_bytes().len() as int)
        } by {
            let binding = roots@[i];
            assert(nor_binding_fits_body(binding, source, forms@, ports.inputs@, definitions@, limit));
            self.expanded_nor_binding_evidence(scope, plan, templates, prepared, rows, roots@, i);
        };
        let lowered = lower_projected_expansion(self, ports.inputs.as_slice(), definitions.as_slice(),
            ports.outputs.as_slice(), wiring.drivers.outputs.as_slice(), forms, selected, roots,
            layout_limit, gate_limit, Ghost((plan, caller, prepared)), Ghost(templates));
        let result = match lowered {
            Ok(circuit) => Ok(circuit),
            Err(error) => Err(ExpandedBodyError::Lowering(error)),
        };
        assert(self.expanded_slots_result(scope, selected@, roots@, arguments, *definitions,
            layout_limit, gate_limit, match result {
                Ok(circuit) => Ok(ExpandedBody { circuit, ports: *ports, has_structure_ports: has_structures }),
                Err(error) => Err(error),
            })) by {
            reveal(UseAliases::expanded_slots_result);
        };
        result
    }

    /// 厳格解析と型検査を終えた本体を、先行する関数のネットリストを使って配線へ変換する。
    ///
    /// # Errors
    ///
    /// ポート、定義の右辺、出力幅、ビット範囲と配線の順に検査し、失敗した段階の診断を返す。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases::bit_func) fn lower_expanded_body(
        &self, plan: &FunctionExpansionOrder<'p, 'a>, templates: &FunctionTemplates<'p, 'a>,
        caller: (usize, usize, u64), prepared: PreparedExpansionBody<'p, 'a>, layout_limit: usize, gate_limit: usize,
    ) -> (result: Result<ExpandedBody<'p, 'a>, ExpandedBodyError<'p, 'a>>)
        requires
            self.can_resolve(), self.function_template_plan(*plan),
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
            Err(error) => {
                let result = Err(ExpandedBodyError::Ports(error));
                assert(self.expanded_body_lowering_result(plan, templates, caller, &original, layout_limit, gate_limit, result)) by {
                    reveal(UseAliases::expanded_body_lowering_result);
                };
                return result;
            },
        };
        let ghost checked_ports = ports;
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
            assert(scope == self.expanded_projection_scope(caller, &original, &checked_ports));
            assert(self.projection_context(&scope));
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
        let (nor_rows, roots) = self.select_expansion_nor_bindings(&scope, plan, templates, prepared.nor_roots.as_slice(),
            prepared.projections.call_arguments.arguments.as_slice(), Ghost(&original));
        let definitions = match self.project_prepared_definition_body(&scope, prepared.calls.as_slice(),
            selected.as_slice(), nor_rows.as_slice(), prepared.typed.literals.widths.as_slice(), prepared.projections.concats,
            Ghost(*plan), Ghost(original), Ghost(templates)) {
            Ok(definitions) => definitions,
            Err(error) => {
                let result = Err(ExpandedBodyError::Definition(error));
                assert(self.expanded_bound_definitions_result(&scope, &original, selected@, nor_rows@, roots@,
                    layout_limit, gate_limit, result)) by {
                    reveal(UseAliases::expanded_bound_definitions_result);
                };
                proof {
                    self.expanded_definition_result_intro(&scope, plan, templates, &original, selected@, nor_rows@, roots@,
                        layout_limit, gate_limit, result);
                    self.expanded_body_result_from_ports(plan, templates, caller, &original, &checked_ports, selected@,
                        layout_limit, gate_limit, result);
                }
                return result;
            },
        };
        proof {
            self.prepared_nor_bindings_fit_slots(&scope, plan, templates, &original, selected@, nor_rows@, roots@, definitions);
        }
        let lowered = self.lower_expanded_slots(&scope, &ports, selected.as_slice(), roots.as_slice(), &definitions,
            layout_limit, gate_limit, Ghost((plan, templates, caller, &original, nor_rows@)));
        let has_structure_ports = contains_structure_port(wiring.drivers.signature.inputs.as_slice())
            || contains_structure_port(wiring.drivers.signature.outputs.as_slice());
        let result = match lowered {
            Ok(circuit) => Ok(ExpandedBody { circuit, ports, has_structure_ports }),
            Err(error) => Err(error),
        };
        assert(self.expanded_bound_definitions_result(&scope, &original, selected@, nor_rows@, roots@,
            layout_limit, gate_limit, result)) by {
            reveal(UseAliases::expanded_bound_definitions_result);
        };
        proof {
            self.expanded_definition_result_intro(&scope, plan, templates, &original, selected@, nor_rows@, roots@,
                layout_limit, gate_limit, result);
            self.expanded_body_result_from_ports(plan, templates, caller, &original, &checked_ports, selected@,
                layout_limit, gate_limit, result);
        }
        result
    }
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn projects_ready_nor_roots_and_preserves_unsupported_definition_order() {
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    let text = "(using nor) (func id (in a) (out a))
        (func supported (in a) (out y)
            (def p (id a)) (def x (nor (nor p a) a)) (def y x))
        (func unsupported (in a) (out y)
            (def x (nor (id (bit a 0)) a))
            (def y (nor (nor x a) a)))";
    let project = parse_circuit_project(&[SourceSnapshot { path: "nor-definitions.ncg2", revision: 1, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    for entry in [2usize, 3usize] {
        let prepared = aliases.prepare_expansion_body(&plan, 0, entry, 8).unwrap();
        let FuncWiringResult::Checked(wiring) = &prepared.typed.literals.wiring else {
            panic!("expected checked wiring");
        };
        let ports = aliases.prepare_expanded_routine_ports(0, entry, 8, wiring, None, &[]).unwrap();
        let scope = FuncProjection { file: 0, entry, limit: 8, source: &project.sources()[0],
            parsed: &project.circuits()[0], wiring, inputs: &ports.inputs, outputs: &ports.outputs,
            structures: &prepared.projections.entries };
        let roots = aliases.select_nor_definitions(&prepared.nor_roots, &prepared.projections.call_arguments.arguments,
            Ghost(&prepared), Ghost(plan), Ghost((0usize, entry, 8u64)));
        let [row] = roots.as_slice() else { panic!("expected one ready root"); };
        let widths: &[&[u64]] = if entry == 2 { &[&[1]] } else { &[] };
        let result = aliases.project_definition_body(&scope, &prepared.calls, &roots, widths,
            &prepared.typed.literals.widths, Vec::new(), Ghost(prepared.typed));
        if entry == 2 {
            let id = plan.get(0).unwrap();
            let checked = aliases.check_bit_func(id.0, id.1, 8).unwrap();
            let circuit = checked.lower_bit_func(8).unwrap();
            let template = aliases.standalone_function_template(id, 8, checked, circuit, 8);
            let mut templates = aliases.new_function_templates(&plan, Ghost(8u64));
            aliases.insert_function_template(&plan, &mut templates, template, Ghost(8u64));
            let bindings = aliases.resolve_selected_nor_roots(&plan, &templates, &prepared.projections.call_arguments.arguments, &roots,
                scope.parsed, Ghost(&prepared), Ghost((0usize, entry, 8u64)));
            let [binding] = bindings.as_slice() else { panic!("expected one resolved root"); };
            assert_eq!(binding.candidate, row.index);
            assert_eq!(binding.selected.prepared.output_slot, row.root.output_slot);
            assert_eq!(*binding.references, scope.parsed.definitions[row.root.definition].references);
            assert_eq!(binding.selected.children.len(), 1);
            let slots = result.unwrap();
            assert_eq!((row.index, row.root.output_slot), (0, 1));
            assert!(matches!(slots[0].rhs, BitFuncRhs::CallOutput { group: 0, port: 0 }));
            assert!(matches!(slots[1].rhs, BitFuncRhs::NorCallOutput { root: 0 }));
            assert_eq!(slots[1].width, 1);
            assert!(matches!(slots[2].rhs, BitFuncRhs::Driver(OutputDriver::Definition(1))));
        } else {
            assert_eq!((row.index, row.root.output_slot), (1, 1));
            let Err(BitFuncError::Unsupported(_, site)) = result else {
                panic!("expected the preceding unsupported definition");
            };
            assert_eq!(&text[site.span], "(nor (id (bit a 0)) a)");
        }
    }
}

} // verus!
