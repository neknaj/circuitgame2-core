//! 型付きの定義をビット単位の配線に変換する。

#[cfg(verus_only)]
mod evaluation;
mod call_arguments;
#[cfg(verus_only)]
pub(super) use call_arguments::literal_argument_matches_width;
mod call_group;
mod mixed;
#[cfg(verus_only)]
pub(super) use mixed::{EvaluatedCallBits, EvaluatedNestedCall, MixedCallEvaluation, evaluated_flat_call_matches,
    evaluated_expression_child_matches, evaluated_nested_call_matches, evaluated_nor_call_matches,
    evaluated_nor_root_port_matches, nor_children_have_single_output};
#[cfg(verus_only)]
pub(super) use mixed::resolved_call_fits_body;
pub(super) use call_group::CallGroupError;
pub(super) use mixed::{MixedWiringError, arguments_are_determined_exec};
#[cfg(verus_only)]
pub(super) use mixed::arguments_are_determined;
use mixed::lower_resolved_function;
use super::templates::{FunctionTemplates, NorBinding, ResolvedTemplateCall};
use super::expansion::PreparedExpansionBody;
use super::super::{FunctionExpansionOrder, UseAliases};
use crate::syntax::Form;
#[cfg(verus_only)]
use super::frontend::{call_covers, nor_binding_covers, nor_binding_fits_body, nor_definition_determined};
#[cfg(verus_only)]
use crate::syntax::form_spans_valid;
#[cfg(verus_only)]
use mixed::{CallBinding, WiringStep, binding_covers, bindings_match_calls, bindings_preserve_definition_order,
    mixed_function_call_evaluation, mixed_function_local_value, mixed_function_result, nor_source_binding_matches,
    rooted_nor_source_arguments, mixed_function_gate_origin, mixed_gate_origin_link};
#[cfg(verus_only)]
pub(super) use mixed::{FuncGateExpression, FuncGateOrigin, func_gate_origin_matches};
#[cfg(verus_only)]
use super::super::call_arity::ProjectedCallArgument;
#[cfg(verus_only)]
use super::expansion::CheckedExpansionCall;
#[cfg(verus_only)]
use super::super::FuncWiringResult;
#[cfg(verus_only)]
use super::semantics::{checked_definition_values, driver_values};
#[cfg(verus_only)]
use crate::netlist::{gate_values_match, output_values_match};
#[cfg(verus_only)]
pub use evaluation::{bit_func_lowering_preserves_evaluation, port_values};

use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

use super::{BitFuncRhs, CheckedBitDefinition, CheckedBitFunc, OutputDriver, SingleBitOperand};
use super::super::function_atoms::copy_location;
use crate::project::LocatedName;
use crate::netlist::{NorGate, NorNetlist, PortBitLayout, PortBitLayoutError, Wire};
use crate::syntax::{BitLiteral, read_bit_literal};
use crate::project::circuits::read_source_span;

#[cfg(verus_only)]
use super::{bit_definition_matches, bit_driver_width, checked_bit_func_available, literal_bytes, nor_operand_matches};
#[cfg(verus_only)]
use crate::project::declarations::located_name_bounds;
#[cfg(verus_only)]
use crate::netlist::{
    gates_available, nor_evaluation_ready, output_ports_available, port_bit_layout_port, port_bit_layout_result,
    port_bit_layout_size, preceding_port_bits, preceding_port_bits_grow, wire_available,
};
#[cfg(verus_only)]
use crate::project::selected_bit_in_range;
#[cfg(verus_only)]
use crate::syntax::bit_literal_value_at;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use crate::project::{
    concat_prefix_width,
    concatenation::{concat_flatten_prefix_len, concat_prefix_width_bounds, concat_prefix_width_step},
};

verus! {

/// 平坦な配線配列を作るための幅の検査で検出した違反。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BitFuncLowerError {
    /// 入力ポートの宣言順で最初に見つかった違反。
    Input(PortBitLayoutError),
    /// 定義順で最初に見つかった違反。
    Definition(PortBitLayoutError),
    /// 出力ポートの宣言順で最初に見つかった違反。
    Output(PortBitLayoutError),
}

#[derive(Debug)]
struct Layouts {
    inputs: PortBitLayout,
    definitions: PortBitLayout,
    outputs: PortBitLayout,
}

struct LoweringBody<'s, 'p, 'a> {
    input_widths: &'s [u64],
    definitions: &'s [CheckedBitDefinition<'p, 'a>],
}

spec fn body_definition_layouts(input_widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, capacity: usize, layouts: &Layouts) -> bool {
    &&& widths_layout(input_widths, capacity, &layouts.inputs)
    &&& widths_layout(definition_widths(definitions), capacity, &layouts.definitions)
}

proof fn body_inputs_end_within_layout(body: &LoweringBody, capacity: usize, layouts: &Layouts)
    requires body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
    ensures forall|i: int| 0 <= i < layouts.inputs.ranges_model().len()
        ==> (#[trigger] layouts.inputs.ranges_model()[i]).end <= layouts.inputs.total_bits_model(),
{
}

spec fn definition_widths(definitions: Seq<CheckedBitDefinition>) -> Seq<u64> {
    Seq::new(definitions.len(), |i: int| definitions[i].width)
}

spec fn width_entries_fit(widths: Seq<u64>, ranges: Seq<Range<usize>>, total: usize) -> bool {
    &&& widths.len() == ranges.len()
    &&& forall|i: int| 0 <= i < ranges.len() ==> {
        let range = #[trigger] ranges[i];
        &&& range.start < range.end <= total
        &&& range.end - range.start == widths[i]
    }
}

spec fn widths_layout(widths: Seq<u64>, capacity: usize, layout: &PortBitLayout) -> bool {
    &&& port_bit_layout_result(widths, capacity, Ok(*layout))
    &&& width_entries_fit(widths, layout.ranges_model(), layout.total_bits_model())
}

proof fn layout_entries_fit(widths: Seq<u64>, capacity: usize, layout: &PortBitLayout)
    requires port_bit_layout_result(widths, capacity, Ok(*layout)),
    ensures widths_layout(widths, capacity, layout),
{
    port_bit_layout_size(widths, capacity, layout);
    assert forall|i: int| 0 <= i < widths.len() implies {
        let range = #[trigger] layout.ranges_model()[i];
        &&& range.start < range.end <= layout.total_bits_model()
        &&& range.end - range.start == widths[i]
    } by {
        port_bit_layout_port(widths, capacity, *layout, i as usize);
    };
}

#[verifier::opaque]
spec fn layouts_result(
    source: &CheckedBitFunc, capacity: usize, result: Result<Layouts, BitFuncLowerError>,
) -> bool {
    body_layouts_result(source.input_widths@, source.definitions@, source.output_widths@, capacity, result)
}

spec fn body_layouts_result(
    inputs: Seq<u64>, slots: Seq<CheckedBitDefinition>, outputs: Seq<u64>,
    capacity: usize, result: Result<Layouts, BitFuncLowerError>,
) -> bool {
    let definitions = definition_widths(slots);
    match result {
        Ok(layouts) => widths_layout(inputs, capacity, &layouts.inputs)
            && widths_layout(definitions, capacity, &layouts.definitions)
            && widths_layout(outputs, capacity, &layouts.outputs),
        Err(BitFuncLowerError::Input(error)) => port_bit_layout_result(inputs, capacity, Err(error)),
        Err(BitFuncLowerError::Definition(error)) =>
            (exists|layout: PortBitLayout| #[trigger] port_bit_layout_result(inputs, capacity, Ok(layout)))
            && port_bit_layout_result(definitions, capacity, Err(error)),
        Err(BitFuncLowerError::Output(error)) =>
            (exists|layout: PortBitLayout| #[trigger] port_bit_layout_result(inputs, capacity, Ok(layout)))
            && (exists|layout: PortBitLayout| #[trigger] port_bit_layout_result(definitions, capacity, Ok(layout)))
            && port_bit_layout_result(outputs, capacity, Err(error)),
    }
}

/// ビット範囲の割り当てと、定義順の配線変換の診断。
#[derive(Debug)]
pub(super) enum ProjectedLoweringError<'p, 'a> {
    Layout(BitFuncLowerError),
    Wiring(MixedWiringError<'p, 'a>),
}

pub(super) closed spec fn projected_lowering_result(
    inputs: &[u64], definitions: &[CheckedBitDefinition], outputs: &[u64], drivers: &[OutputDriver],
    forms: Seq<Form>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, arguments: Seq<ProjectedCallArgument>, layout_limit: usize, gate_limit: usize,
    result: Result<LoweredBitFunc, ProjectedLoweringError>,
) -> bool {
    let body = LoweringBody { input_widths: inputs, definitions };
    match result {
        Err(ProjectedLoweringError::Layout(error)) =>
            body_layouts_result(inputs@, definitions@, outputs@, layout_limit, Err(error)),
        _ => exists|layouts: Layouts, bindings: Seq<CallBinding>|
            #![trigger body_layouts_result(inputs@, definitions@, outputs@, layout_limit, Ok(layouts)), bindings_match_calls(bindings, selected)]
        {
            &&& body_layouts_result(inputs@, definitions@, outputs@, layout_limit, Ok(layouts))
            &&& bindings_match_calls(bindings, selected)
            &&& projected_wiring_result(&body, &layouts, forms, bindings, roots, outputs@, drivers@, arguments, gate_limit, result)
        },
    }
}

spec fn projected_wiring_result(
    body: &LoweringBody, layouts: &Layouts, forms: Seq<Form>, bindings: Seq<CallBinding>, roots: Seq<NorBinding>,
    outputs: Seq<u64>, drivers: Seq<OutputDriver>, arguments: Seq<ProjectedCallArgument>, gate_limit: usize,
    result: Result<LoweredBitFunc, ProjectedLoweringError>,
) -> bool {
    exists|lowered: Result<(LoweredBitFunc, Ghost<Seq<WiringStep>>), MixedWiringError>|
        #[trigger] mixed_function_result(body, layouts, forms, bindings, roots, outputs, drivers, arguments, gate_limit, lowered)
        && result == match lowered {
            Ok((value, _)) => Ok(value),
            Err(error) => Err(ProjectedLoweringError::Wiring(error)),
        }
}

pub(super) open spec fn projected_lowering_view(
    inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>, outputs: Seq<u64>, drivers: Seq<OutputDriver>,
    forms: Seq<Form>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, arguments: Seq<ProjectedCallArgument>, layout_limit: usize, gate_limit: usize,
    result: Result<LoweredBitFunc, ProjectedLoweringError>,
) -> bool {
    exists|a: &[u64], b: &[CheckedBitDefinition], c: &[u64], d: &[OutputDriver]|
        a@ == inputs && b@ == definitions && c@ == outputs && d@ == drivers
        && #[trigger] projected_lowering_result(a, b, c, d, forms, selected, roots, arguments, layout_limit, gate_limit, result)
}

/// 同じ変換結果から、型付きの本体、配置、呼び出しの束縛、変換履歴を取り出す。
proof fn projected_lowering_success<'s, 'p, 'a>(
    inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition<'p, 'a>>, outputs: Seq<u64>, drivers: Seq<OutputDriver>,
    forms: Seq<Form>, selected: Seq<ResolvedTemplateCall<'s, 'p, 'a>>, roots: Seq<NorBinding<'s, 'p, 'a>>, arguments: Seq<ProjectedCallArgument>,
    layout_limit: usize, gate_limit: usize,
    value: &LoweredBitFunc,
) -> (witness: (LoweringBody<'s, 'p, 'a>, Layouts, Seq<CallBinding<'s, 'p, 'a>>, Ghost<Seq<WiringStep>>))
    requires projected_lowering_view(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, layout_limit, gate_limit, Ok(*value)),
    ensures
        witness.0.input_widths@ == inputs && witness.0.definitions@ == definitions,
        body_layouts_result(inputs, definitions, outputs, layout_limit, Ok(witness.1)),
        bindings_match_calls(witness.2, selected),
        mixed_function_result(&witness.0, &witness.1, forms, witness.2, roots, outputs, drivers, arguments, gate_limit, Ok((*value, witness.3))),
{
    let (a, b, c, d) = choose|a: &'s [u64], b: &'s [CheckedBitDefinition<'p, 'a>], c: &[u64], d: &[OutputDriver]|
        a@ == inputs && b@ == definitions && c@ == outputs && d@ == drivers
        && #[trigger] projected_lowering_result(a, b, c, d, forms, selected, roots, arguments, layout_limit, gate_limit, Ok(*value));
    let body = LoweringBody { input_widths: a, definitions: b };
    let (layouts, bindings) = choose|layouts: Layouts, bindings: Seq<CallBinding<'s, 'p, 'a>>| {
        &&& #[trigger] body_layouts_result(inputs, definitions, outputs, layout_limit, Ok(layouts))
        &&& #[trigger] bindings_match_calls(bindings, selected)
        &&& projected_wiring_result(&body, &layouts, forms, bindings, roots, outputs, drivers, arguments, gate_limit, Ok(*value))
    };
    let steps = choose|steps: Ghost<Seq<WiringStep>>|
        #[trigger] mixed_function_result(&body, &layouts, forms, bindings, roots, outputs, drivers, arguments, gate_limit, Ok((*value, steps)));
    (body, layouts, bindings, steps)
}

pub(super) closed spec fn projected_gate_origin_link(
    inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>, outputs: Seq<u64>, drivers: Seq<OutputDriver>,
    forms: Seq<Form>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>,
    arguments: Seq<ProjectedCallArgument>, bit_limit: usize, gate_limit: usize, value: &LoweredBitFunc, gate: int,
    origin: FuncGateOrigin,
) -> bool {
    exists|body: LoweringBody, layouts: Layouts, bindings: Seq<CallBinding>, steps: Ghost<Seq<WiringStep>>|
        #![trigger mixed_gate_origin_link(&body, &layouts, forms, bindings, roots, gate_limit, value, steps@, gate, origin)]
        body.input_widths@ == inputs && body.definitions@ == definitions
        && body_layouts_result(inputs, definitions, outputs, bit_limit, Ok(layouts))
        && bindings_match_calls(bindings, selected)
        && mixed_function_result(&body, &layouts, forms, bindings, roots, outputs, drivers, arguments, gate_limit, Ok((*value, steps)))
        && mixed_gate_origin_link(&body, &layouts, forms, bindings, roots, gate_limit, value, steps@, gate, origin)
}

/// 変換したゲートに対応する展開前の式と、呼び出した回路内での位置を得る。
pub(super) proof fn projected_lowering_gate_origin<'s, 'p, 'a>(
    inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition<'p, 'a>>, outputs: Seq<u64>, drivers: Seq<OutputDriver>,
    forms: Seq<Form>, selected: Seq<ResolvedTemplateCall<'s, 'p, 'a>>, roots: Seq<NorBinding<'s, 'p, 'a>>,
    arguments: Seq<ProjectedCallArgument>, bit_limit: usize, gate_limit: usize, value: &LoweredBitFunc, gate: int,
) -> (origin: FuncGateOrigin<'s, 'p, 'a>)
    requires
        projected_lowering_view(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, bit_limit, gate_limit, Ok(*value)),
        0 <= gate < value.netlist_model().gates@.len(),
    ensures
        func_gate_origin_matches(origin, definitions, selected, roots, value.netlist_model().gates@, gate),
        projected_gate_origin_link(inputs, definitions, outputs, drivers, forms, selected, roots, arguments,
            bit_limit, gate_limit, value, gate, origin),
{
    let (body, layouts, bindings, steps) = projected_lowering_success(inputs, definitions, outputs, drivers,
        forms, selected, roots, arguments, bit_limit, gate_limit, value);
    mixed_function_gate_origin(&body, &layouts, forms, bindings, selected, roots, outputs, drivers,
        gate_limit, value, steps@, gate)
}

/// 展開した回路の入力・出力の配置と、評価に必要な配線の条件を取り出す。
pub(super) proof fn projected_lowering_ports(
    inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>, outputs: Seq<u64>, drivers: Seq<OutputDriver>,
    forms: Seq<Form>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, arguments: Seq<ProjectedCallArgument>, layout_limit: usize, gate_limit: usize, value: &LoweredBitFunc,
)
    requires projected_lowering_view(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, layout_limit, gate_limit, Ok(*value)),
    ensures
        port_bit_layout_result(inputs, layout_limit, Ok(*value.input_layout_model())),
        port_bit_layout_result(outputs, layout_limit, Ok(*value.output_layout_model())),
        nor_evaluation_ready(value.netlist_model(), value.input_layout_model().total_bits_model() as nat),
        value.netlist_model().outputs@.len() == value.output_layout_model().total_bits_model(),
{
    let _ = projected_lowering_success(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, layout_limit, gate_limit, value);
}

/// 展開した関数の定義値を、最終配線と評価済みのゲート値から得る。
pub(super) closed spec fn expanded_definition_values(
    function: &LoweredBitFunc, inputs: Seq<bool>, gates: Seq<bool>,
) -> Seq<Seq<bool>> {
    evaluation::definition_values_from_wires(&function.layouts.definitions, function.definition_wires@, inputs, gates)
}

/// 展開した関数の通常の定義が、最終配線を評価したときに右辺の値を保つことを示す。
pub(super) proof fn projected_lowering_local_values(
    inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>, outputs: Seq<u64>, drivers: Seq<OutputDriver>,
    forms: Seq<Form>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, calls: Seq<CheckedExpansionCall>, arguments: Seq<ProjectedCallArgument>,
    layout_limit: usize, gate_limit: usize, value: &LoweredBitFunc, input: Seq<bool>, gates: Seq<bool>,
)
    requires
        projected_lowering_view(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, layout_limit, gate_limit, Ok(*value)),
        calls.len() == selected.len(),
        forall|g: int| 0 <= g < selected.len() ==> *(#[trigger] selected[g]).group == calls[g],
        forall|a: int, b: int| 0 <= a < b < calls.len()
            ==> (#[trigger] calls[a]).outputs.end <= (#[trigger] calls[b]).outputs.start,
        forall|i: int| 0 <= i < definitions.len() && !call_covers(calls, i) && !nor_binding_covers(roots, i) ==>
            bit_definition_matches(inputs, definitions.take(i), #[trigger] definitions[i]),
        input.len() == value.input_layout_model().total_bits_model(),
        gate_values_match(input, value.netlist_model().gates@, gates),
        gates.len() == value.netlist_model().gates@.len(),
    ensures ({
        let values = expanded_definition_values(value, input, gates);
        let incoming = port_values(value.input_layout_model(), input);
        &&& incoming.len() == inputs.len()
        &&& forall|i: int| 0 <= i < incoming.len() ==> (#[trigger] incoming[i]).len() == inputs[i]
        &&& values.len() == definitions.len()
        &&& forall|i: int| 0 <= i < values.len() ==> (#[trigger] values[i]).len() == definitions[i].width
        &&& forall|i: int| 0 <= i < values.len() && !call_covers(calls, i) && !nor_binding_covers(roots, i) ==>
            (#[trigger] values[i]) == checked_definition_values(definitions[i], incoming, values.take(i))
    }),
{
    let (body, layouts, bindings, steps) =
        projected_lowering_success(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, layout_limit, gate_limit, value);
    assert forall|g: int| 0 <= g < bindings.len() implies *(#[trigger] bindings[g]).group == calls[g] by {
        assert(*bindings[g].group == *selected[g].group);
    };
    bindings_preserve_definition_order(bindings, calls);

    reveal(port_values);
    let incoming = port_values(value.input_layout_model(), input);
    let values = expanded_definition_values(value, input, gates);
    let widths = definition_widths(definitions);
    port_bit_layout_size(inputs, layout_limit, &layouts.inputs);
    port_bit_layout_size(widths, layout_limit, &layouts.definitions);
    assert forall|i: int| 0 <= i < incoming.len() implies (#[trigger] incoming[i]).len() == inputs[i] by {
        port_bit_layout_port(inputs, layout_limit, layouts.inputs, i as usize);
    };
    assert forall|i: int| 0 <= i < values.len() implies (#[trigger] values[i]).len() == definitions[i].width by {
        port_bit_layout_port(widths, layout_limit, layouts.definitions, i as usize);
    };
    assert forall|i: int| 0 <= i < values.len() && !call_covers(calls, i) && !nor_binding_covers(roots, i) implies
        (#[trigger] values[i]) == checked_definition_values(definitions[i], incoming, values.take(i)) by {
        mixed_function_local_value(&body, &layouts, forms, bindings, roots, outputs, drivers, layout_limit, gate_limit,
            value, steps, i, input, gates);
    };
}

/// 展開後のネットリストの出力を、宣言順に各駆動元の値へ対応付ける。
pub(super) proof fn projected_lowering_output_values(
    inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>, outputs: Seq<u64>, drivers: Seq<OutputDriver>,
    forms: Seq<Form>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, arguments: Seq<ProjectedCallArgument>, layout_limit: usize, gate_limit: usize,
    value: &LoweredBitFunc, input: Seq<bool>, gates: Seq<bool>, output: Seq<bool>,
)
    requires
        projected_lowering_view(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, layout_limit, gate_limit, Ok(*value)),
        outputs.len() == drivers.len(),
        forall|i: int| 0 <= i < drivers.len() ==>
            bit_driver_width(inputs, definitions, #[trigger] drivers[i]) == Some(outputs[i]),
        input.len() == value.input_layout_model().total_bits_model(),
        gates.len() == value.netlist_model().gates@.len(),
        output.len() == value.netlist_model().outputs@.len(),
        output_values_match(input, gates, value.netlist_model().outputs@, output),
    ensures ({
        let incoming = port_values(value.input_layout_model(), input);
        let values = expanded_definition_values(value, input, gates);
        let outgoing = port_values(value.output_layout_model(), output);
        &&& incoming.len() == inputs.len()
        &&& values.len() == definitions.len()
        &&& outgoing.len() == drivers.len()
        &&& forall|i: int| 0 <= i < outgoing.len() ==>
            (#[trigger] outgoing[i]) == driver_values(incoming, values, drivers[i])
    }),
{
    let (_, layouts, _, _) =
        projected_lowering_success(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, layout_limit, gate_limit, value);
    evaluation::output_ports_follow_drivers(inputs, definitions, outputs, drivers, layout_limit, &layouts,
        value.definition_wires@, value.netlist.outputs@, input, gates, output);
}

/// 展開結果から、元の引数と左辺に対応する呼び出し先の評価を取り出す。
pub(super) proof fn projected_lowering_call_evaluation(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, caller: (usize, usize, u64), prepared: &PreparedExpansionBody,
    inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>, outputs: Seq<u64>, drivers: Seq<OutputDriver>,
    forms: Seq<Form>, selected: Seq<ResolvedTemplateCall>, roots: Seq<NorBinding>, index: int, layout_limit: usize, gate_limit: usize,
    value: &LoweredBitFunc, input: Seq<bool>, gates: Seq<bool>,
) -> (result: MixedCallEvaluation)
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
        prepared.typed.literals.wiring matches FuncWiringResult::Checked(wiring)
            && inputs.len() == wiring.drivers.signature.inputs@.len(),
        ({
            let project = aliases.targets.project_model();
            &&& caller.0 < project.circuits_model().len() && caller.0 < project.sources_model().len()
            &&& forms == project.circuits_model()[caller.0 as int].syntax.forms@
        }),
        projected_lowering_view(inputs, definitions, outputs, drivers, forms, selected, roots,
            prepared.projections.call_arguments.arguments@, layout_limit, gate_limit, Ok(*value)),
        selected.len() == prepared.calls@.len(),
        forall|i: int| 0 <= i < selected.len() ==>
            aliases.resolved_template_call_matches(plan, caller, prepared, i, #[trigger] selected[i]),
        0 <= index < selected.len(),
        !nor_binding_covers(roots, selected[index].group.outputs.start as int),
        resolved_call_fits_body(selected[index], inputs, definitions, forms, caller.2),
        input.len() == value.input_layout_model().total_bits_model(),
        gate_values_match(input, value.netlist_model().gates@, gates),
        gates.len() == value.netlist_model().gates@.len() <= usize::MAX,
    ensures ({
        let call = selected[index];
        let definitions = expanded_definition_values(value, input, gates);
        let incoming = port_values(value.input_layout_model(), input);
        &&& call.group.outputs.end <= definitions.len()
        &&& match result {
            MixedCallEvaluation::Flat(arguments, outputs) =>
                evaluated_flat_call_matches(aliases, caller, prepared, index, call, incoming, definitions, arguments, outputs),
            MixedCallEvaluation::Nested(evaluation) =>
                evaluated_nested_call_matches(aliases, caller, prepared, index, &call, incoming, definitions, evaluation),
        }
    }),
{
    let arguments = prepared.projections.call_arguments.arguments@;
    let (body, layouts, bindings, steps) =
        projected_lowering_success(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, layout_limit, gate_limit, value);
    assert forall|i: int| 0 <= i < bindings.len() implies *(#[trigger] bindings[i]).group == prepared.calls@[i] by {
        assert(*bindings[i].group == *selected[i].group);
    };
    bindings_preserve_definition_order(bindings, prepared.calls@);
    mixed_function_call_evaluation(aliases, plan, caller, prepared, selected[index], index, &body, &layouts, forms,
        bindings, roots, outputs, drivers, layout_limit, gate_limit, value, steps, input, gates)
}

/// 配線を評価し、根 NOR と子の実引数および出力を元の厳格構文木に結び付ける。
#[verifier::spinoff_prover]
pub(super) proof fn projected_lowering_nor_evaluation(
    aliases: &UseAliases, plan: &FunctionExpansionOrder, table: &FunctionTemplates, caller: (usize, usize, u64),
    prepared: &PreparedExpansionBody, inputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>,
    outputs: Seq<u64>, drivers: Seq<OutputDriver>, forms: Seq<Form>, selected: Seq<ResolvedTemplateCall>,
    roots: Seq<NorBinding>, index: int, layout_limit: usize, gate_limit: usize,
    value: &LoweredBitFunc, input: Seq<bool>, gates: Seq<bool>,
) -> (evaluation: EvaluatedNestedCall)
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*plan, caller.0, caller.1, caller.2, prepared),
        prepared.typed.literals.wiring matches FuncWiringResult::Checked(wiring)
            && inputs.len() == wiring.drivers.signature.inputs@.len(),
        projected_lowering_view(inputs, definitions, outputs, drivers, forms, selected, roots,
            prepared.projections.call_arguments.arguments@, layout_limit, gate_limit, Ok(*value)),
        0 <= index < roots.len(),
        forall|i: int, j: int| 0 <= i < j < roots.len() ==>
            (#[trigger] roots[i]).selected.prepared.output_slot < (#[trigger] roots[j]).selected.prepared.output_slot,
        ({
            let project = aliases.targets.project_model();
            let binding = roots[index];
            let root = binding.selected.prepared;
            let source = &project.sources_model()[caller.0 as int];
            let parsed = &project.circuits_model()[caller.0 as int];
            let arguments = prepared.projections.call_arguments.arguments@;
            &&& caller.0 < project.sources_model().len() && caller.0 < project.circuits_model().len()
            &&& binding.candidate < prepared.nor_roots@.len() && *root == prepared.nor_roots@[binding.candidate as int]
            &&& root.definition < parsed.definitions@.len()
            &&& *binding.references == parsed.definitions@[root.definition as int].references
            &&& forms == parsed.syntax.forms@ && root.root.expression.source == source
            &&& form_spans_valid(source.text, forms, source.text.spec_bytes().len() as int)
            &&& aliases.nor_binding_context(plan, table, caller.2, arguments, binding)
            &&& nor_definition_determined(root, arguments)
            &&& nor_binding_fits_body(binding, source, forms, inputs, definitions, caller.2)
        }),
        input.len() == value.input_layout_model().total_bits_model(),
        gate_values_match(input, value.netlist_model().gates@, gates),
        gates.len() == value.netlist_model().gates@.len() <= usize::MAX,
    ensures evaluated_nor_call_matches(aliases, caller, prepared, &roots[index],
        port_values(value.input_layout_model(), input), expanded_definition_values(value, input, gates), evaluation),
{
    let arguments = prepared.projections.call_arguments.arguments@;
    let (body, layouts, bindings, steps) =
        projected_lowering_success(inputs, definitions, outputs, drivers, forms, selected, roots, arguments, layout_limit, gate_limit, value);
    let wiring = call_group::WiringView { definitions: value.definition_wires@,
        gates: value.netlist.gates@, origins: value.gate_definitions@ };
    vstd::slice::axiom_spec_len(body.definitions);
    assert(nor_source_binding_matches(aliases, plan, table, caller, prepared, &roots[index], forms));
    reveal(expanded_definition_values);
    rooted_nor_source_arguments(aliases, plan, table, caller, prepared, &body, &layouts, forms, bindings, roots,
        gate_limit, layout_limit, steps@, definitions.len() as usize, bindings.len() as usize, roots.len() as usize,
        wiring, index, input, gates)
}

/// 検査済みの本体にビット範囲を割り当て、呼び出しと通常の定義を配線へ変換する。
///
/// # Errors
///
/// 範囲を割り当てられない場合はその診断を返す。割り当てが成功した場合は定義順に配線を変換する。
pub(super) fn lower_projected_expansion<'s, 'p, 'a>(
    aliases: &UseAliases<'_, 'p, 'a>, inputs: &'s [u64], definitions: &'s [CheckedBitDefinition<'p, 'a>],
    outputs: &[u64], drivers: &[OutputDriver], forms: &[Form], selected: &[ResolvedTemplateCall<'s, 'p, 'a>],
    roots: &[NorBinding<'s, 'p, 'a>],
    layout_limit: usize, gate_limit: usize,
    Ghost(context): Ghost<(&FunctionExpansionOrder<'p, 'a>, (usize, usize, u64), &PreparedExpansionBody<'p, 'a>)>,
    Ghost(templates): Ghost<&FunctionTemplates<'p, 'a>>,
) -> (result: Result<LoweredBitFunc, ProjectedLoweringError<'p, 'a>>)
    requires
        aliases.can_resolve(),
        aliases.prepared_expansion_body_matches(*context.0, context.1.0, context.1.1, context.1.2, context.2),
        outputs@.len() == drivers@.len(),
        forall|p: int| 0 <= p < outputs@.len() ==>
            bit_driver_width(inputs@, definitions@, #[trigger] drivers@[p]) == Some(outputs@[p]),
        aliases.expansion_selection_matches(context.0, templates, context.1, context.2, selected@),
        forall|g: int| 0 <= g < selected@.len() ==>
            resolved_call_fits_body(#[trigger] selected@[g], inputs@, definitions@, forms@, context.1.2),
        forall|i: int| 0 <= i < roots@.len() ==> {
            let binding = #[trigger] roots@[i];
            let source = binding.selected.prepared.root.expression.source;
            &&& !call_covers(context.2.calls@, binding.selected.prepared.output_slot as int)
            &&& nor_binding_fits_body(binding, source, forms@, inputs@, definitions@, context.1.2)
            &&& aliases.nor_binding_context(context.0, templates, context.1.2, context.2.projections.call_arguments.arguments@, binding)
            &&& form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int)
        },
        forall|i: int, j: int| 0 <= i < j < roots@.len() ==>
            (#[trigger] roots@[i]).selected.prepared.output_slot < (#[trigger] roots@[j]).selected.prepared.output_slot,
        forall|slot: int| 0 <= slot < definitions@.len() && !call_covers(context.2.calls@, slot)
            && !nor_binding_covers(roots@, slot) ==>
            bit_definition_matches(inputs@, definitions@.take(slot), #[trigger] definitions@[slot]),
    ensures projected_lowering_result(inputs, definitions, outputs, drivers, forms@, selected@, roots@,
        context.2.projections.call_arguments.arguments@, layout_limit, gate_limit, result),
{
    reveal(projected_lowering_result);
    let layouts = match prepare_body_layouts(inputs, definitions, outputs, layout_limit) {
        Ok(layouts) => layouts,
        Err(error) => return Err(ProjectedLoweringError::Layout(error)),
    };
    let body = LoweringBody { input_widths: inputs, definitions };
    let ghost arguments = context.2.projections.call_arguments.arguments@;
    let lowered = lower_resolved_function(aliases, &body, layouts, forms, selected, roots, outputs, drivers,
        layout_limit, gate_limit, Ghost(context), Ghost(templates));
    let result = match lowered {
        Ok((value, _)) => Ok(value),
        Err(error) => Err(ProjectedLoweringError::Wiring(error)),
    };
    assert(projected_lowering_result(inputs, definitions, outputs, drivers, forms@, selected@, roots@, arguments, layout_limit, gate_limit, result)) by {
        let bindings = choose|bindings: Seq<CallBinding>| #[trigger] bindings_match_calls(bindings, selected@)
            && mixed_function_result(&body, &layouts, forms@, bindings, roots@, outputs@, drivers@, arguments, gate_limit, lowered);
        assert(body_layouts_result(inputs@, definitions@, outputs@, layout_limit, Ok(layouts)));
        assert(projected_wiring_result(&body, &layouts, forms@, bindings, roots@, outputs@, drivers@, arguments, gate_limit, result)) by {
            assert(result == match lowered {
                Ok((value, _)) => Ok(value),
                Err(error) => Err(ProjectedLoweringError::Wiring(error)),
            });
            assert(mixed_function_result(&body, &layouts, forms@, bindings, roots@, outputs@, drivers@, arguments, gate_limit, lowered));
        };
    };
    result
}

fn collect_definition_widths(definitions: &[CheckedBitDefinition]) -> (widths: Vec<u64>)
    ensures widths@ == definition_widths(definitions@),
{
    let mut widths = Vec::new();
    let mut i = 0;
    while i < definitions.len()
        invariant
            i == widths@.len() <= definitions@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] widths@[j]) == definitions@[j].width,
        decreases definitions@.len() - i,
    {
        let ghost prior = widths@;
        widths.push(definitions[i].width);
        assert forall|j: int| 0 <= j < widths@.len() implies
            (#[trigger] widths@[j]) == definitions@[j].width by {
            if j < i { assert(widths@[j] == prior[j]); }
        };
        i += 1;
    }
    assert(widths@ =~= definition_widths(definitions@));
    widths
}

fn prepare_layouts(source: &CheckedBitFunc, capacity: usize) -> (result: Result<Layouts, BitFuncLowerError>)
    ensures layouts_result(source, capacity, result),
{
    let result = prepare_body_layouts(
        source.input_widths.as_slice(), source.definitions.as_slice(), source.output_widths.as_slice(), capacity,
    );
    assert(layouts_result(source, capacity, result)) by { reveal(layouts_result); };
    result
}

/// 入力、定義、出力それぞれのビット範囲を、並び順に割り当てる。
///
/// # Errors
///
/// 入力、定義、出力の順に調べ、各列で最初に見つかった幅または容量の違反を返す。
fn prepare_body_layouts(
    input_widths: &[u64], slots: &[CheckedBitDefinition], output_widths: &[u64], capacity: usize,
) -> (result: Result<Layouts, BitFuncLowerError>)
    ensures body_layouts_result(input_widths@, slots@, output_widths@, capacity, result),
{
    let inputs = match PortBitLayout::from_widths(input_widths, capacity) {
        Ok(layout) => layout,
        Err(error) => {
            let result = Err(BitFuncLowerError::Input(error));
            assert(body_layouts_result(input_widths@, slots@, output_widths@, capacity, result));
            return result;
        },
    };
    let local_widths = collect_definition_widths(slots);
    let definitions = match PortBitLayout::from_widths(local_widths.as_slice(), capacity) {
        Ok(layout) => layout,
        Err(error) => {
            let result = Err(BitFuncLowerError::Definition(error));
            assert(body_layouts_result(input_widths@, slots@, output_widths@, capacity, result)) by {
                assert(port_bit_layout_result(input_widths@, capacity, Ok(inputs)));
            };
            return result;
        },
    };
    let outputs = match PortBitLayout::from_widths(output_widths, capacity) {
        Ok(layout) => layout,
        Err(error) => {
            let result = Err(BitFuncLowerError::Output(error));
            assert(body_layouts_result(input_widths@, slots@, output_widths@, capacity, result)) by {
                assert(port_bit_layout_result(input_widths@, capacity, Ok(inputs)));
                assert(port_bit_layout_result(local_widths@, capacity, Ok(definitions)));
            };
            return result;
        },
    };
    proof {
        layout_entries_fit(input_widths@, capacity, &inputs);
        layout_entries_fit(local_widths@, capacity, &definitions);
        layout_entries_fit(output_widths@, capacity, &outputs);
    }
    let result = Ok(Layouts { inputs, definitions, outputs });
    assert(body_layouts_result(input_widths@, slots@, output_widths@, capacity, result));
    result
}

proof fn use_layouts(source: &CheckedBitFunc, capacity: usize, layouts: &Layouts)
    requires layouts_result(source, capacity, Ok(*layouts)),
    ensures
        port_bit_layout_result(source.input_widths@, capacity, Ok(layouts.inputs)),
        port_bit_layout_result(definition_widths(source.definitions@), capacity, Ok(layouts.definitions)),
        port_bit_layout_result(source.output_widths@, capacity, Ok(layouts.outputs)),
        layouts.definitions.ranges_model().len() == source.definitions@.len(),
        layouts.outputs.ranges_model().len() == source.output_widths@.len(),
        forall|i: int| 0 <= i < layouts.inputs.ranges_model().len()
            ==> (#[trigger] layouts.inputs.ranges_model()[i]).end <= layouts.inputs.total_bits_model(),
{
    reveal(layouts_result);
}

proof fn use_bit_definition(source: &CheckedBitFunc, index: int)
    requires checked_bit_func_available(source), 0 <= index < source.definitions@.len(),
    ensures bit_definition_matches(source.input_widths@, source.definitions@.take(index), source.definitions@[index]),
{
    reveal(checked_bit_func_available);
}

proof fn use_bit_output(source: &CheckedBitFunc, port: int)
    requires checked_bit_func_available(source), 0 <= port < source.output_widths@.len(),
    ensures
        source.output_widths@.len() == source.output_drivers@.len(),
        bit_driver_width(source.input_widths@, source.definitions@, source.output_drivers@[port])
            == Some(source.output_widths@[port]),
{
    reveal(checked_bit_func_available);
}

spec fn driver_bit_available(
    inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>, used: int, driver: OutputDriver, bit: int,
) -> bool {
    &&& 0 <= bit
    &&& match driver {
        OutputDriver::Input(port) => port < inputs.len()
            && inputs[port as int].start + bit < inputs[port as int].end,
        OutputDriver::Definition(port) => port < definitions.len()
            && definitions[port as int].start + bit < definitions[port as int].end
            && definitions[port as int].end <= used,
    }
}

spec fn driver_wire(
    inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>, wires: Seq<Wire>, driver: OutputDriver, bit: int,
) -> Wire {
    match driver {
        OutputDriver::Input(port) => Wire::Input((inputs[port as int].start + bit) as usize),
        OutputDriver::Definition(port) => wires[definitions[port as int].start + bit],
    }
}

fn lower_driver_bit(
    inputs: &[Range<usize>], definitions: &[Range<usize>], wires: &[Wire], driver: OutputDriver, bit: usize,
) -> (wire: Wire)
    requires driver_bit_available(inputs@, definitions@, wires@.len() as int, driver, bit as int),
    ensures wire == driver_wire(inputs@, definitions@, wires@, driver, bit as int),
{
    match driver {
        OutputDriver::Input(port) => Wire::Input(inputs[port].start + bit),
        OutputDriver::Definition(port) => wires[definitions[port].start + bit],
    }
}

#[derive(Clone, Copy)]
enum Projection {
    Wire(Wire),
    Driver { source: OutputDriver, start: u64, stride: u64 },
}

spec fn projected_bit_available(
    inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>, used: int, projection: Projection, bit: int,
) -> bool {
    &&& 0 <= bit <= usize::MAX
    &&& match projection {
        Projection::Wire(_) => true,
        Projection::Driver { source, start, stride } => {
            let index = start + bit * stride;
            &&& index <= u64::MAX
            &&& driver_bit_available(inputs, definitions, used, source, index)
        },
    }
}

spec fn projected_wire(
    inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>, wires: Seq<Wire>, projection: Projection, bit: int,
) -> Wire {
    match projection {
        Projection::Wire(wire) => wire,
        Projection::Driver { source, start, stride } =>
            driver_wire(inputs, definitions, wires, source, start + bit * stride),
    }
}

fn lower_projected_bit(
    inputs: &[Range<usize>], definitions: &[Range<usize>], wires: &[Wire], projection: Projection, bit: usize,
) -> (wire: Wire)
    requires projected_bit_available(inputs@, definitions@, wires@.len() as int, projection, bit as int),
    ensures wire == projected_wire(inputs@, definitions@, wires@, projection, bit as int),
{
    match projection {
        Projection::Wire(wire) => wire,
        Projection::Driver { source, start, stride } => {
            let index = start + bit as u64 * stride;
            assert(index <= usize::MAX);
            lower_driver_bit(inputs, definitions, wires, source, index as usize)
        },
    }
}

proof fn projected_wire_keeps_prefix(
    inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>, old: Seq<Wire>, new: Seq<Wire>,
    projection: Projection, bit: int,
)
    requires
        old.len() <= new.len(), new.take(old.len() as int) == old,
        projected_bit_available(inputs, definitions, old.len() as int, projection, bit),
    ensures
        projected_bit_available(inputs, definitions, new.len() as int, projection, bit),
        projected_wire(inputs, definitions, old, projection, bit)
            == projected_wire(inputs, definitions, new, projection, bit),
{
    if let Projection::Driver { source: OutputDriver::Definition(index), start, stride } = projection {
        let offset = definitions[index as int].start + start + bit * stride;
        assert(new.take(old.len() as int)[offset] == new[offset]);
    }
}

/// 既存配線を保持し、指定した順序の配線を末尾へ追加する。
fn append_projected_bits(
    inputs: &[Range<usize>], definitions: &[Range<usize>], wires: &mut Vec<Wire>, projection: Projection, width: usize,
)
    requires
        old(wires)@.len() + width <= usize::MAX,
        forall|bit: int| 0 <= bit < width ==>
            #[trigger] projected_bit_available(inputs@, definitions@, old(wires)@.len() as int, projection, bit),
    ensures
        final(wires)@.len() == old(wires)@.len() + width,
        final(wires)@.len() >= old(wires)@.len(),
        final(wires)@.take(old(wires)@.len() as int) == old(wires)@,
        forall|j: int| old(wires)@.len() <= j < final(wires)@.len() ==> (#[trigger] final(wires)@[j])
            == projected_wire(inputs@, definitions@, old(wires)@, projection, j - old(wires)@.len()),
{
    let ghost prior = old(wires)@;
    assert(wires@.take(prior.len() as int) =~= prior);
    let mut bit = 0;
    while bit < width
        invariant
            bit <= width,
            prior.len() + width <= usize::MAX,
            wires@.len() == prior.len() + bit,
            wires@.take(prior.len() as int) == prior,
            forall|j: int| 0 <= j < width ==>
                #[trigger] projected_bit_available(inputs@, definitions@, prior.len() as int, projection, j),
            forall|j: int| prior.len() <= j < wires@.len() ==> (#[trigger] wires@[j])
                == projected_wire(inputs@, definitions@, prior, projection, j - prior.len()),
        decreases width - bit,
    {
        proof { projected_wire_keeps_prefix(inputs@, definitions@, prior, wires@, projection, bit as int); }
        let wire = lower_projected_bit(inputs, definitions, wires.as_slice(), projection, bit);
        let ghost previous = wires@;
        wires.push(wire);
        assert(wires@.take(prior.len() as int) =~= prior);
        assert forall|j: int| prior.len() <= j < wires@.len() implies (#[trigger] wires@[j])
            == projected_wire(inputs@, definitions@, prior, projection, j - prior.len()) by {
            if j < previous.len() { assert(wires@[j] == previous[j]); }
        };
        bit += 1;
    }
}

/// 既存の配線を保ち、検査済みの幅だけリテラルの定数配線を低位順に追加する。
fn append_bit_literal_wires(literal: &BitLiteral<'_>, width: usize, wires: &mut Vec<Wire>)
    requires old(wires)@.len() + width <= usize::MAX,
    ensures
        final(wires)@.len() == old(wires)@.len() + width,
        final(wires)@.take(old(wires)@.len() as int) == old(wires)@,
        forall|bit: int| 0 <= bit < width ==>
            (#[trigger] final(wires)@[old(wires)@.len() + bit])
                == Wire::Constant(bit_literal_value_at(literal.word_model().spec_bytes(), bit as nat)),
{
    let ghost prior = old(wires)@;
    let mut bit = 0usize;
    assert(wires@.take(prior.len() as int) =~= prior);
    while bit < width
        invariant
            bit <= width,
            prior.len() + width <= usize::MAX,
            wires@.len() == prior.len() + bit,
            wires@.take(prior.len() as int) == prior,
            forall|index: int| 0 <= index < bit ==>
                (#[trigger] wires@[prior.len() + index])
                    == Wire::Constant(bit_literal_value_at(literal.word_model().spec_bytes(), index as nat)),
        decreases width - bit,
    {
        assert(bit <= u64::MAX);
        let wire = Wire::Constant(literal.bit(bit as u64));
        let ghost previous = wires@;
        wires.push(wire);
        assert(wires@.take(prior.len() as int) =~= prior);
        assert forall|index: int| 0 <= index <= bit implies
            (#[trigger] wires@[prior.len() + index])
                == Wire::Constant(bit_literal_value_at(literal.word_model().spec_bytes(), index as nat)) by {
            if index < bit {
                assert(wires@[prior.len() + index] == previous[prior.len() + index]);
            }
        };
        bit += 1;
    }
}

proof fn driver_bits_fit_layout(
    source: &CheckedBitFunc, layouts: &Layouts, capacity: usize, scope: int, used: int,
    driver: OutputDriver, width: u64, bit: int,
)
    requires
        layouts_result(source, capacity, Ok(*layouts)),
        0 <= scope <= source.definitions@.len(),
        used == preceding_port_bits(definition_widths(source.definitions@), scope as nat),
        bit_driver_width(source.input_widths@, source.definitions@.take(scope), driver) == Some(width),
        0 <= bit < width,
    ensures driver_bit_available(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), used, driver, bit),
{
    reveal(layouts_result);
    body_driver_bits_fit_layout(source.input_widths@, source.definitions@, layouts, capacity, scope, used, driver, width, bit);
}

proof fn body_driver_bits_fit_layout(
    input_widths: Seq<u64>, definitions: Seq<CheckedBitDefinition>, layouts: &Layouts, capacity: usize, scope: int, used: int,
    driver: OutputDriver, width: u64, bit: int,
)
    requires
        body_definition_layouts(input_widths, definitions, capacity, layouts),
        0 <= scope <= definitions.len(),
        used == preceding_port_bits(definition_widths(definitions), scope as nat),
        bit_driver_width(input_widths, definitions.take(scope), driver) == Some(width),
        0 <= bit < width,
    ensures driver_bit_available(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), used, driver, bit),
{
    match driver {
        OutputDriver::Input(port) => {
            let widths = input_widths;
            let range = layouts.inputs.ranges_model()[port as int];
            assert(widths[port as int] == width);
            assert(range.end - range.start == widths[port as int]);
        },
        OutputDriver::Definition(index) => {
            let widths = definition_widths(definitions);
            let range = layouts.definitions.ranges_model()[index as int];
            assert(widths[index as int] == width);
            assert(range.end - range.start == widths[index as int]);
            port_bit_layout_port(widths, capacity, layouts.definitions, index);
            preceding_port_bits_grow(widths, (index + 1) as nat, scope as nat);
        },
    }
}

spec fn concat_operand_projection(operand: SingleBitOperand) -> Projection {
    match operand {
        SingleBitOperand::Constant(bit) => Projection::Wire(Wire::Constant(bit)),
        SingleBitOperand::Driver(source) => Projection::Driver { source, start: 0, stride: 1 },
    }
}

/// 引数を低位から並べて追加し、先行する引数と定義の配線を保持する。
fn append_concat_operand(
    _source: &LoweringBody, layouts: &Layouts, _capacity: usize, _scope: usize,
    wires: &mut Vec<Wire>, operand: SingleBitOperand, width: usize,
)
    requires
        body_definition_layouts(_source.input_widths@, _source.definitions@, _capacity, layouts),
        _scope < _source.definitions@.len(),
        preceding_port_bits(definition_widths(_source.definitions@), _scope as nat) <= old(wires)@.len(),
        old(wires)@.len() + width <= usize::MAX,
        0 < width <= u64::MAX,
        match operand {
            SingleBitOperand::Constant(_) => width == 1,
            SingleBitOperand::Driver(driver) =>
                bit_driver_width(_source.input_widths@, _source.definitions@.take(_scope as int), driver) == Some(width as u64),
        },
    ensures
        final(wires)@.len() == old(wires)@.len() + width,
        final(wires)@.take(old(wires)@.len() as int) == old(wires)@,
        forall|j: int| old(wires)@.len() <= j < final(wires)@.len() ==> (#[trigger] final(wires)@[j])
            == projected_wire(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
                old(wires)@, concat_operand_projection(operand), j - old(wires)@.len()),
{
    let projection = match operand {
        SingleBitOperand::Constant(bit) => Projection::Wire(Wire::Constant(bit)),
        SingleBitOperand::Driver(source) => Projection::Driver { source, start: 0, stride: 1 },
    };
    proof {
        let inputs = layouts.inputs.ranges_model();
        let definitions = layouts.definitions.ranges_model();
        assert forall|bit: int| 0 <= bit < width implies
            #[trigger] projected_bit_available(inputs, definitions, wires@.len() as int, projection, bit) by {
            if let SingleBitOperand::Driver(driver) = operand {
                let used = preceding_port_bits(definition_widths(_source.definitions@), _scope as nat) as int;
                body_driver_bits_fit_layout(_source.input_widths@, _source.definitions@, layouts, _capacity, _scope as int, used, driver, width as u64, bit);
                assert(driver_bit_available(inputs, definitions, wires@.len() as int, driver, bit));
            }
        };
    }
    append_projected_bits(layouts.inputs.ranges(), layouts.definitions.ranges(), wires, projection, width);
}

spec fn concat_operand_wires(
    inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>, prior: Seq<Wire>,
    operands: Seq<(SingleBitOperand, u64)>,
) -> Seq<Seq<Wire>> {
    operands.map_values(|item: (SingleBitOperand, u64)| Seq::new(item.1 as nat, |bit: int|
        projected_wire(inputs, definitions, prior, concat_operand_projection(item.0), bit)))
}

/// 引数順に配線を連接する。幅と開始位置には、型検査で得た各引数の幅を使う。
fn append_concat_operands(
    source: &LoweringBody, layouts: &Layouts, capacity: usize, scope: usize,
    wires: &mut Vec<Wire>, operands: &[(SingleBitOperand, u64)], Ghost(gates): Ghost<nat>,
)
    requires
        body_definition_layouts(source.input_widths@, source.definitions@, capacity, layouts),
        scope < source.definitions@.len(),
        old(wires)@.len() == preceding_port_bits(definition_widths(source.definitions@), scope as nat),
        wires_available(old(wires)@, layouts.inputs.total_bits_model(), gates),
        old(wires)@.len() + concat_prefix_width(
            operands@.map_values(|item: (SingleBitOperand, u64)| item.1), operands@.len()) <= usize::MAX,
        forall|i: int| 0 <= i < operands@.len() ==> {
            let (operand, width) = #[trigger] operands@[i];
            &&& 0 < width
            &&& match operand {
                SingleBitOperand::Constant(_) => width == 1,
                SingleBitOperand::Driver(driver) =>
                    bit_driver_width(source.input_widths@, source.definitions@.take(scope as int), driver) == Some(width),
            }
        },
    ensures
        final(wires)@ == old(wires)@ + concat_operand_wires(
            layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), old(wires)@, operands@).flatten(),
        wires_available(final(wires)@, layouts.inputs.total_bits_model(), gates),
{
    let ghost initial = wires@;
    let ghost inputs = layouts.inputs.ranges_model();
    let ghost definitions = layouts.definitions.ranges_model();
    let ghost input_bits = layouts.inputs.total_bits_model();
    let ghost widths = operands@.map_values(|item: (SingleBitOperand, u64)| item.1);
    let ghost parts = concat_operand_wires(inputs, definitions, initial, operands@);
    assert forall|i: int| 0 <= i < operands@.len() implies (#[trigger] parts[i]).len() == widths[i] by {
        assert(widths[i] == operands@[i].1);
    };
    proof {
        body_inputs_end_within_layout(source, capacity, layouts);
        concat_flatten_prefix_len(parts, widths, 0);
    }
    let mut i: usize = 0;
    while i < operands.len()
        invariant
            i <= operands@.len() == widths.len() == parts.len(),
            body_definition_layouts(source.input_widths@, source.definitions@, capacity, layouts),
            scope < source.definitions@.len(),
            inputs == layouts.inputs.ranges_model(), definitions == layouts.definitions.ranges_model(),
            input_bits == layouts.inputs.total_bits_model(),
            forall|j: int| 0 <= j < inputs.len() ==> (#[trigger] inputs[j]).end <= input_bits,
            wires_available(initial, input_bits, gates), wires_available(wires@, input_bits, gates),
            initial.len() == preceding_port_bits(definition_widths(source.definitions@), scope as nat),
            widths == operands@.map_values(|item: (SingleBitOperand, u64)| item.1),
            parts == concat_operand_wires(inputs, definitions, initial, operands@),
            initial.len() + concat_prefix_width(widths, widths.len()) <= usize::MAX,
            wires@ == initial + parts.take(i as int).flatten(),
            wires@.len() == initial.len() + concat_prefix_width(widths, i as nat),
            forall|j: int| 0 <= j < operands@.len() ==> (#[trigger] parts[j]).len() == widths[j],
            forall|j: int| 0 <= j < operands@.len() ==> {
                let (operand, width) = #[trigger] operands@[j];
                &&& 0 < width
                &&& match operand {
                    SingleBitOperand::Constant(_) => width == 1,
                    SingleBitOperand::Driver(driver) =>
                        bit_driver_width(source.input_widths@, source.definitions@.take(scope as int), driver) == Some(width),
                }
            },
        decreases operands@.len() - i,
    {
        let (operand, width) = operands[i];
        proof {
            concat_prefix_width_step(widths, i as nat);
            concat_prefix_width_bounds(widths, i as nat, (i + 1) as nat);
            concat_prefix_width_bounds(widths, (i + 1) as nat, widths.len());
            assert(widths[i as int] == width);
            assert(wires@.len() + width <= usize::MAX);
        }
        let ghost before = wires@;
        append_concat_operand(source, layouts, capacity, scope, wires, operand, width as usize);
        proof {
            let projection = concat_operand_projection(operand);
            assert(before.take(initial.len() as int) =~= initial);
            assert(parts[i as int].len() == width);
            assert(wires@.len() == before.len() + width);
            let extended = before + parts[i as int];
            reveal(wires_available);
            assert forall|j: int| 0 <= j < wires@.len() implies
                (#[trigger] wires@[j]) == extended[j] && wire_available(wires@[j], input_bits as nat, gates) by {
                if j < before.len() {
                    assert(wires@[j] == before[j]);
                } else {
                    let bit = j - before.len();
                    assert(0 <= bit < width <= usize::MAX);
                    match operand {
                        SingleBitOperand::Driver(driver) => {
                            body_driver_bits_fit_layout(source.input_widths@, source.definitions@, layouts, capacity, scope as int, initial.len() as int, driver, width, bit);
                            driver_wire_is_available(inputs, definitions, initial, driver, bit, input_bits, gates);
                            assert(projection == Projection::Driver { source: driver, start: 0, stride: 1 });
                            assert(bit <= u64::MAX);
                            assert(driver_bit_available(inputs, definitions, initial.len() as int, driver, bit));
                            assert(0 <= 0 + bit * 1 == bit);
                            assert(projected_bit_available(inputs, definitions, initial.len() as int, projection, bit));
                        },
                        SingleBitOperand::Constant(value) => {
                            assert(projection == Projection::Wire(Wire::Constant(value)));
                            assert(projected_bit_available(inputs, definitions, initial.len() as int, projection, bit));
                        },
                    }
                    assert(projected_bit_available(inputs, definitions, initial.len() as int, projection, bit));
                    projected_wire_keeps_prefix(inputs, definitions, initial, before, projection, bit);
                    assert(wires@[j] == projected_wire(inputs, definitions, before, projection, bit));
                    assert(parts[i as int][bit] == projected_wire(inputs, definitions, initial, projection, bit));
                }
            };
            assert(wires@ =~= extended);
            let earlier = parts.take(i as int);
            assert(earlier.push(parts[i as int]) =~= parts.take(i + 1));
            earlier.lemma_flatten_push(parts[i as int]);
            assert(wires@ =~= initial + parts.take(i + 1).flatten());
        }
        i += 1;
    }
    assert(parts.take(i as int) =~= parts);
}

proof fn rhs_projection_is_available(
    source: &LoweringBody, layouts: &Layouts, capacity: usize, scope: int, used: int,
    definition: CheckedBitDefinition, projection: Projection, bit: int,
)
    requires
        body_definition_layouts(source.input_widths@, source.definitions@, capacity, layouts),
        0 <= scope < source.definitions@.len(),
        used == preceding_port_bits(definition_widths(source.definitions@), scope as nat),
        bit_definition_matches(source.input_widths@, source.definitions@.take(scope), definition),
        0 <= bit < definition.width,
        0 <= bit <= usize::MAX,
        match definition.rhs {
            BitFuncRhs::Driver(driver) => projection == Projection::Driver { source: driver, start: 0, stride: 1 },
            BitFuncRhs::Selection { input, selection } =>
                projection == Projection::Driver { source: input, start: selection.start, stride: selection.stride },
            _ => projection is Wire,
        },
    ensures projected_bit_available(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), used, projection, bit),
{
    match definition.rhs {
        BitFuncRhs::Driver(driver) => {
            body_driver_bits_fit_layout(source.input_widths@, source.definitions@, layouts, capacity, scope, used, driver, definition.width, bit);
        },
        BitFuncRhs::Selection { input, selection } => {
            let width = bit_driver_width(source.input_widths@, source.definitions@.take(scope), input)->Some_0;
            selected_bit_in_range(width, selection.start, selection.count, selection.stride, selection.last, bit);
            body_driver_bits_fit_layout(source.input_widths@, source.definitions@, layouts, capacity, scope, used, input, width,
                selection.start + bit * selection.stride);
        },
        _ => {},
    }
}

#[verifier::opaque]
spec fn wires_available(wires: Seq<Wire>, input_bits: usize, gates: nat) -> bool {
    forall|i: int| 0 <= i < wires.len() ==> wire_available(#[trigger] wires[i], input_bits as nat, gates)
}

proof fn driver_wire_is_available(
    inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>, wires: Seq<Wire>, driver: OutputDriver,
    bit: int, input_bits: usize, gates: nat,
)
    requires
        driver_bit_available(inputs, definitions, wires.len() as int, driver, bit),
        forall|i: int| 0 <= i < inputs.len() ==> (#[trigger] inputs[i]).end <= input_bits,
        wires_available(wires, input_bits, gates),
    ensures wire_available(driver_wire(inputs, definitions, wires, driver, bit), input_bits as nat, gates),
{
    if let OutputDriver::Definition(index) = driver {
        assert(wire_available(wires[definitions[index as int].start + bit], input_bits as nat, gates)) by {
            reveal(wires_available);
        };
    }
}

proof fn existing_wires_keep_availability(wires: Seq<Wire>, input_bits: usize, before: nat, after: nat)
    requires wires_available(wires, input_bits, before), before <= after,
    ensures wires_available(wires, input_bits, after),
{
    reveal(wires_available);
    assert forall|i: int| 0 <= i < wires.len() implies
        wire_available(#[trigger] wires[i], input_bits as nat, after) by {
        assert(wire_available(wires[i], input_bits as nat, before));
    };
}

spec fn operand_wire(
    inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>, wires: Seq<Wire>, operand: SingleBitOperand,
) -> Wire {
    match operand {
        SingleBitOperand::Constant(bit) => Wire::Constant(bit),
        SingleBitOperand::Driver(driver) => driver_wire(inputs, definitions, wires, driver, 0),
    }
}

fn lower_nor_operand(
    _source: &LoweringBody, layouts: &Layouts, _capacity: usize, _scope: usize, wires: &[Wire], _gate_count: usize,
    operand: SingleBitOperand,
) -> (wire: Wire)
    requires
        body_definition_layouts(_source.input_widths@, _source.definitions@, _capacity, layouts),
        _scope <= _source.definitions@.len(),
        wires@.len() == preceding_port_bits(definition_widths(_source.definitions@), _scope as nat),
        nor_operand_matches(_source.input_widths@, _source.definitions@.take(_scope as int), operand),
        wires_available(wires@, layouts.inputs.total_bits_model(), _gate_count as nat),
    ensures
        wire == operand_wire(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), wires@, operand),
        wire_available(wire, layouts.inputs.total_bits_model() as nat, _gate_count as nat),
{
    match operand {
        SingleBitOperand::Constant(bit) => Wire::Constant(bit),
        SingleBitOperand::Driver(driver) => {
            proof {
                body_inputs_end_within_layout(_source, _capacity, layouts);
                body_driver_bits_fit_layout(_source.input_widths@, _source.definitions@, layouts, _capacity, _scope as int, wires@.len() as int, driver, 1, 0);
                driver_wire_is_available(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
                    wires@, driver, 0, layouts.inputs.total_bits_model(), _gate_count as nat);
            }
            lower_driver_bit(layouts.inputs.ranges(), layouts.definitions.ranges(), wires, driver, 0)
        },
    }
}


spec fn rhs_projection(rhs: BitFuncRhs, gate: usize) -> Projection {
    match rhs {
        BitFuncRhs::Driver(source) => Projection::Driver { source, start: 0, stride: 1 },
        BitFuncRhs::Selection { input: source, selection } => Projection::Driver {
            source, start: selection.start, stride: selection.stride,
        },
        BitFuncRhs::Constant(bit) => Projection::Wire(Wire::Constant(bit)),
        BitFuncRhs::Nor { .. } => Projection::Wire(Wire::Gate(gate)),
        BitFuncRhs::Concat | BitFuncRhs::BitVector | BitFuncRhs::CallOutput { .. } | BitFuncRhs::NorCallOutput { .. } => arbitrary(),
    }
}

spec fn rhs_gate(
    inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>, wires: Seq<Wire>, rhs: BitFuncRhs,
) -> Option<NorGate> {
    match rhs {
        BitFuncRhs::Nor { left, right } => Some(NorGate {
            left: operand_wire(inputs, definitions, wires, left),
            right: operand_wire(inputs, definitions, wires, right),
        }),
        _ => None,
    }
}

#[verifier::opaque]
spec fn gate_step_matches(
    layouts: &Layouts, wires: Seq<Wire>, rhs: BitFuncRhs, index: usize,
    prior_gates: Seq<NorGate>, next_gates: Seq<NorGate>,
    prior_origins: Seq<usize>, next_origins: Seq<usize>,
) -> bool {
    match rhs_gate(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), wires, rhs) {
        Some(gate) => next_gates == prior_gates.push(gate) && next_origins == prior_origins.push(index),
        None => next_gates == prior_gates && next_origins == prior_origins,
    }
}

fn lower_rhs(
    source: &LoweringBody, layouts: &Layouts, capacity: usize, _gate_limit: usize, index: usize,
    wires: &[Wire], gates: &mut Vec<NorGate>, origins: &mut Vec<usize>,
) -> (projection: Projection)
    requires
        body_definition_layouts(source.input_widths@, source.definitions@, capacity, layouts),
        index < source.definitions@.len(),
        bit_definition_matches(source.input_widths@, source.definitions@.take(index as int),
            source.definitions@[index as int]),
        !(source.definitions@[index as int].rhs is Concat || source.definitions@[index as int].rhs is BitVector),
        wires@.len() == preceding_port_bits(definition_widths(source.definitions@), index as nat),
        wires_available(wires@, layouts.inputs.total_bits_model(), old(gates)@.len()),
        gates_available(old(gates)@, layouts.inputs.total_bits_model() as nat, old(gates)@.len() as int),
        old(gates)@.len() == old(origins)@.len(),
        old(gates)@.len() + (if source.definitions@[index as int].rhs is Nor { 1int } else { 0int }) <= _gate_limit,
    ensures
        projection == rhs_projection(source.definitions@[index as int].rhs, old(gates)@.len() as usize),
        gate_step_matches(layouts, wires@, source.definitions@[index as int].rhs, index,
            old(gates)@, final(gates)@, old(origins)@, final(origins)@),
        wires_available(wires@, layouts.inputs.total_bits_model(), final(gates)@.len()),
        gates_available(final(gates)@, layouts.inputs.total_bits_model() as nat, final(gates)@.len() as int),
        final(gates)@.len() == final(origins)@.len() <= _gate_limit,
        final(gates)@.len() == old(gates)@.len() + (if source.definitions@[index as int].rhs is Nor { 1int } else { 0int }),
        final(gates)@.len() >= old(gates)@.len(),
        if let Projection::Wire(wire) = projection {
            wire_available(wire, layouts.inputs.total_bits_model() as nat, final(gates)@.len())
        } else { true },
{
    let rhs = source.definitions[index].rhs;
    let gate = gates.len();
    let ghost before = gates@;
    let ghost before_origins = origins@;
    let ghost input_bits = layouts.inputs.total_bits_model();
    let projection = match rhs {
        BitFuncRhs::Driver(source) => Projection::Driver { source, start: 0, stride: 1 },
        BitFuncRhs::Selection { input: source, selection } => Projection::Driver {
            source, start: selection.start, stride: selection.stride,
        },
        BitFuncRhs::Constant(bit) => Projection::Wire(Wire::Constant(bit)),
        BitFuncRhs::Nor { left, right } => {
            let left_wire = lower_nor_operand(source, layouts, capacity, index, wires, gate, left);
            let right_wire = lower_nor_operand(source, layouts, capacity, index, wires, gate, right);
            gates.push(NorGate { left: left_wire, right: right_wire });
            origins.push(index);
            assert forall|j: int| 0 <= j < gates@.len() implies {
                &&& wire_available((#[trigger] gates@[j]).left, input_bits as nat, j as nat)
                &&& wire_available(gates@[j].right, input_bits as nat, j as nat)
            } by {
                if j < gate { assert(gates@[j] == before[j]); }
            };
            proof { existing_wires_keep_availability(wires@, input_bits, gate as nat, gates@.len()); }
            Projection::Wire(Wire::Gate(gate))
        },
        BitFuncRhs::Concat | BitFuncRhs::BitVector | BitFuncRhs::CallOutput { .. } | BitFuncRhs::NorCallOutput { .. } => {
            proof { assert(false); }
            Projection::Wire(Wire::Constant(false))
        },
    };
    assert(gate_step_matches(layouts, wires@, rhs, index, before, gates@, before_origins, origins@))
        by { reveal(gate_step_matches); };
    projection
}

#[verifier::opaque]
spec fn definition_wiring_matches(
    source: &CheckedBitFunc, layouts: &Layouts, wires: Seq<Wire>, gates: Seq<NorGate>, origins: Seq<usize>, i: int,
) -> bool {
    slot_wiring_matches(source.definitions@[i], layouts, wires, gates, origins, i)
}

spec fn slot_wiring_matches(
    slot: CheckedBitDefinition, layouts: &Layouts, wires: Seq<Wire>, gates: Seq<NorGate>, origins: Seq<usize>, i: int,
) -> bool {
    let range = layouts.definitions.ranges_model()[i];
    let prefix = wires.take(range.start as int);
    let rhs = slot.rhs;
    let gate = if rhs is Nor { wires[range.start as int]->Gate_0 } else { 0usize };
    &&& !(rhs is CallOutput) && !(rhs is NorCallOutput)
    &&& range.start < range.end <= wires.len()
    &&& match rhs_gate(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), prefix, rhs) {
        Some(expected) => wires[range.start as int] == Wire::Gate(gate)
            && gate < gates.len() == origins.len() && gates[gate as int] == expected && origins[gate as int] == i,
        None => true,
    }
    &&& if rhs is BitVector {
        forall|bit: int| 0 <= bit < range.end - range.start ==>
            (#[trigger] wires[range.start + bit]) == Wire::Constant(
                bit_literal_value_at(literal_bytes(slot.expression), bit as nat))
    } else if rhs is Concat {
        wires.subrange(range.start as int, range.end as int)
            == concat_operand_wires(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), prefix,
                slot.operands@).flatten()
    } else {
        forall|j: int| range.start <= j < range.end ==> (#[trigger] wires[j]) == projected_wire(layouts.inputs.ranges_model(),
            layouts.definitions.ranges_model(), prefix, rhs_projection(rhs, gate), j - range.start)
    }
}

proof fn slot_wiring_is_preserved(
    slot: CheckedBitDefinition, layouts: &Layouts, i: int, before_wires: Seq<Wire>, after_wires: Seq<Wire>,
    before_gates: Seq<NorGate>, after_gates: Seq<NorGate>, before_origins: Seq<usize>, after_origins: Seq<usize>,
)
    requires
        slot_wiring_matches(slot, layouts, before_wires, before_gates, before_origins, i),
        before_wires.len() <= after_wires.len(),
        before_gates.len() <= after_gates.len(),
        before_origins.len() <= after_origins.len(),
        after_wires.take(before_wires.len() as int) == before_wires,
        after_gates.take(before_gates.len() as int) == before_gates,
        after_origins.take(before_origins.len() as int) == before_origins,
        after_gates.len() == after_origins.len(),
    ensures slot_wiring_matches(slot, layouts, after_wires, after_gates, after_origins, i),
{
    let range = layouts.definitions.ranges_model()[i];
    assert(after_wires.take(range.start as int) =~= before_wires.take(range.start as int));
    assert(after_wires[range.start as int] == before_wires[range.start as int]);
    let rhs = slot.rhs;
    if rhs is Concat {
        assert(after_wires.subrange(range.start as int, range.end as int)
            =~= before_wires.subrange(range.start as int, range.end as int));
    }
    let gate = if rhs is Nor { before_wires[range.start as int]->Gate_0 } else { 0usize };
    if rhs is Nor {
        assert(after_gates[gate as int] == before_gates[gate as int]);
        assert(after_origins[gate as int] == before_origins[gate as int]);
    }
    if rhs is BitVector {
        assert forall|bit: int| 0 <= bit < range.end - range.start implies
            (#[trigger] after_wires[range.start + bit]) == Wire::Constant(
                bit_literal_value_at(literal_bytes(slot.expression), bit as nat)) by {
            assert(after_wires[range.start + bit] == before_wires[range.start + bit]);
        };
    } else if !(rhs is Concat) {
        assert forall|j: int| range.start <= j < range.end implies
            (#[trigger] after_wires[j]) == projected_wire(layouts.inputs.ranges_model(),
                layouts.definitions.ranges_model(), after_wires.take(range.start as int), rhs_projection(rhs, gate), j - range.start) by {
            assert(after_wires[j] == before_wires[j]);
        };
    }
}

#[verifier::opaque]
spec fn gate_origins_in_definition_order(
    source: &CheckedBitFunc, layouts: &Layouts, wires: Seq<Wire>, origins: Seq<usize>, end: int,
) -> bool {
    &&& forall|k: int| 0 <= k < origins.len() ==> {
        let i = (#[trigger] origins[k]) as int;
        let range = layouts.definitions.ranges_model()[i];
        &&& 0 <= i < end
        &&& source.definitions@[i].rhs is Nor
        &&& range.start < wires.len()
        &&& wires[range.start as int] == Wire::Gate(k as usize)
    }
    &&& forall|p: int, k: int| 0 <= p < k < origins.len() ==>
        (#[trigger] origins[p]) < (#[trigger] origins[k])
}

proof fn gate_origins_preserved(
    source: &CheckedBitFunc, layouts: &Layouts, index: usize,
    wires: Seq<Wire>, gates: Seq<NorGate>, origins: Seq<usize>,
    next_wires: Seq<Wire>, next_gates: Seq<NorGate>, next_origins: Seq<usize>,
)
    requires
        index < source.definitions@.len(),
        index < layouts.definitions.ranges_model().len(),
        wires.len() == layouts.definitions.ranges_model()[index as int].start,
        wires.len() < next_wires.len(),
        wires == next_wires.take(wires.len() as int),
        next_gates.len() == next_origins.len(),
        gates.len() == origins.len() <= index,
        gate_origins_in_definition_order(source, layouts, wires, origins, index as int),
        gate_step_matches(layouts, wires, source.definitions@[index as int].rhs, index,
            gates, next_gates, origins, next_origins),
        source.definitions@[index as int].rhs is Nor ==>
            next_wires[wires.len() as int] == Wire::Gate(gates.len() as usize),
    ensures gate_origins_in_definition_order(source, layouts, next_wires, next_origins, index + 1),
{
    reveal(gate_step_matches);
    reveal(gate_origins_in_definition_order);
    let rhs = source.definitions@[index as int].rhs;
    assert(next_origins == if rhs is Nor { origins.push(index) } else { origins });
    assert forall|k: int| 0 <= k < next_origins.len() implies {
        let i = (#[trigger] next_origins[k]) as int;
        let range = layouts.definitions.ranges_model()[i];
        &&& 0 <= i < index + 1
        &&& source.definitions@[i].rhs is Nor
        &&& range.start < next_wires.len()
        &&& next_wires[range.start as int] == Wire::Gate(k as usize)
    } by {
        if k < origins.len() {
            assert(next_origins[k] == origins[k]);
            let range = layouts.definitions.ranges_model()[origins[k] as int];
            assert(next_wires[range.start as int] == wires[range.start as int]);
        } else {
            assert(next_origins[k] == index);
        }
    };
    assert forall|p: int, k: int| 0 <= p < k < next_origins.len() implies
        (#[trigger] next_origins[p]) < (#[trigger] next_origins[k]) by {
        assert(next_origins[p] == origins[p]);
        if k < origins.len() {
            assert(next_origins[k] == origins[k]);
        } else {
            assert(origins[p] < index);
            assert(next_origins[k] == index);
        }
    };
}

/// 通常の定義を1件だけ配線に変換し、既存の配線とゲートを保つ。
///
/// NOR のときだけゲートを1個追加する。
///
/// # Errors
///
/// ゲート数が上限に達しているときに NOR を追加しようとすると、元の右辺の範囲を返す。
/// 失敗時は配線、ゲート、ゲートと定義の対応を保つ。
fn lower_definition<'p, 'a>(
    source: &LoweringBody<'_, 'p, 'a>, layouts: &Layouts, capacity: usize, gate_limit: usize, i: usize,
    wires: &mut Vec<Wire>, gates: &mut Vec<NorGate>, gate_definitions: &mut Vec<usize>,
) -> (result: Result<(), LocatedName<'p, 'a>>)
    requires
        body_definition_layouts(source.input_widths@, source.definitions@, capacity, layouts),
        i < source.definitions@.len(),
        bit_definition_matches(source.input_widths@, source.definitions@.take(i as int),
            source.definitions@[i as int]),
        old(wires)@.len() == preceding_port_bits(definition_widths(source.definitions@), i as nat),
        wires_available(old(wires)@, layouts.inputs.total_bits_model(), old(gates)@.len()),
        gates_available(old(gates)@, layouts.inputs.total_bits_model() as nat, old(gates)@.len() as int),
        old(gates)@.len() == old(gate_definitions)@.len(),
        old(gates)@.len() <= gate_limit,
    ensures match result {
        Err(site) => {
            &&& source.definitions@[i as int].rhs is Nor
            &&& old(gates)@.len() == gate_limit
            &&& site == source.definitions@[i as int].expression
            &&& final(wires)@ == old(wires)@
            &&& final(gates)@ == old(gates)@
            &&& final(gate_definitions)@ == old(gate_definitions)@
        },
        Ok(()) => {
            &&& final(wires)@.len() == preceding_port_bits(definition_widths(source.definitions@), (i + 1) as nat)
            &&& wires_available(final(wires)@, layouts.inputs.total_bits_model(), final(gates)@.len())
            &&& gates_available(final(gates)@, layouts.inputs.total_bits_model() as nat, final(gates)@.len() as int)
            &&& final(gates)@.len() == final(gate_definitions)@.len() <= gate_limit
            &&& final(gates)@.len() == old(gates)@.len() + (if source.definitions@[i as int].rhs is Nor { 1int } else { 0int })
            &&& slot_wiring_matches(source.definitions@[i as int], layouts, final(wires)@, final(gates)@, final(gate_definitions)@, i as int)
            &&& final(gates)@.take(old(gates)@.len() as int) == old(gates)@
            &&& final(gate_definitions)@.take(old(gate_definitions)@.len() as int) == old(gate_definitions)@
            &&& final(gates)@.len() >= old(gates)@.len()
            &&& gate_step_matches(layouts, old(wires)@, source.definitions@[i as int].rhs, i,
                old(gates)@, final(gates)@, old(gate_definitions)@, final(gate_definitions)@)
            &&& old(wires)@.len() == layouts.definitions.ranges_model()[i as int].start
            &&& final(wires)@.len() > old(wires)@.len()
            &&& source.definitions@[i as int].rhs is Nor ==>
                final(wires)@[old(wires)@.len() as int] == Wire::Gate(old(gates)@.len() as usize)
            &&& final(wires)@.take(old(wires)@.len() as int) == old(wires)@
            &&& !(source.definitions@[i as int].rhs is Concat || source.definitions@[i as int].rhs is BitVector)
                ==> forall|bit: int| 0 <= bit < source.definitions@[i as int].width ==>
                (#[trigger] final(wires)@[old(wires)@.len() + bit]) == projected_wire(
                    layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), old(wires)@,
                    rhs_projection(source.definitions@[i as int].rhs, old(gates)@.len() as usize), bit,
                )
        },
    },
{
    if gates.len() == gate_limit && matches!(source.definitions[i].rhs, BitFuncRhs::Nor { .. }) {
        return Err(copy_location(&source.definitions[i].expression));
    }
    proof { body_inputs_end_within_layout(source, capacity, layouts); }
    let ghost input_bits = layouts.inputs.total_bits_model();
    let inputs = layouts.inputs.ranges();
    let ranges = layouts.definitions.ranges();

    let ghost definition = &source.definitions@[i as int];
    let range = &ranges[i];
    proof {
        port_bit_layout_port(definition_widths(source.definitions@), capacity, layouts.definitions, i);
    }
    let width = range.end - range.start;
    let ghost prior = wires@;
    let ghost before_gates = gates@;
    let ghost before_origins = gate_definitions@;
    let ghost gate = gates@.len() as usize;
    if matches!(source.definitions[i].rhs, BitFuncRhs::BitVector) {
        let expression = &source.definitions[i].expression;
        proof { located_name_bounds(*expression); }
        let text = read_source_span(expression.source.text, expression.span.start, expression.span.end);
        assert(text.spec_bytes() == literal_bytes(*expression));
        let Some(literal) = read_bit_literal(text) else {
            proof { assert(false); }
            return Ok(());
        };
        append_bit_literal_wires(&literal, width, wires);
        proof {
            reveal(wires_available);
            assert forall|j: int| 0 <= j < wires@.len()
                implies wire_available(#[trigger] wires@[j], input_bits as nat, gates@.len()) by {
                if j < prior.len() {
                    assert(wires@[j] == prior[j]);
                } else {
                    let bit = j - prior.len();
                    assert(wires@[prior.len() + bit] is Constant);
                }
            };
            reveal(slot_wiring_matches);
            reveal(gate_step_matches);
        }
        return Ok(());
    }
    if matches!(source.definitions[i].rhs, BitFuncRhs::Concat) {
        let operands = source.definitions[i].operands.as_slice();
        append_concat_operands(source, layouts, capacity, i, wires, operands, Ghost(gate as nat));
        proof {
            let parts = concat_operand_wires(inputs@, ranges@, prior, operands@);
            let widths = operands@.map_values(|item: (SingleBitOperand, u64)| item.1);
            assert forall|j: int| 0 <= j < operands@.len() implies (#[trigger] parts[j]).len() == widths[j] by {
                assert(widths[j] == operands@[j].1);
            };
            concat_flatten_prefix_len(parts, widths, widths.len());
            assert(parts.take(widths.len() as int) =~= parts);
            assert(parts.flatten().len() == width);
            assert(wires@.subrange(range.start as int, range.end as int) =~= parts.flatten());
            assert(wires@.take(prior.len() as int) =~= prior);
            reveal(slot_wiring_matches);
            reveal(gate_step_matches);
        }
        return Ok(());
    }
    let projection = lower_rhs(source, layouts, capacity, gate_limit, i, wires.as_slice(), gates, gate_definitions);
    assert(projection == rhs_projection(definition.rhs, gate));
    assert forall|bit: int| 0 <= bit < width implies
        #[trigger] projected_bit_available(inputs@, ranges@, prior.len() as int, projection, bit) by {
        rhs_projection_is_available(source, layouts, capacity, i as int, prior.len() as int,
            *definition, projection, bit);
    };
    assert forall|bit: int| 0 <= bit < width implies
        wire_available(#[trigger] projected_wire(inputs@, ranges@, prior, projection, bit), input_bits as nat, gates@.len()) by {
        if let Projection::Driver { source, start, stride } = projection {
            assert(projected_bit_available(inputs@, ranges@, prior.len() as int, projection, bit));
            driver_wire_is_available(inputs@, ranges@, prior, source, start + bit * stride, input_bits, gates@.len());
        }
    };
    append_projected_bits(inputs, ranges, wires, projection, width);
    assert forall|j: int| 0 <= j < wires@.len() implies
        wire_available(#[trigger] wires@[j], input_bits as nat, gates@.len()) by {
        if j < prior.len() {
            assert(wires@[j] == prior[j]);
            assert(wire_available(prior[j], input_bits as nat, gates@.len())) by { reveal(wires_available); };
        }
        else {
            let bit = j - prior.len();
            assert(0 <= bit < width);
            assert(wires@[prior.len() + bit] == projected_wire(inputs@, ranges@, prior, projection, bit));
            assert(prior.len() + bit == j);
        }
    };
    assert(wires_available(wires@, input_bits, gates@.len())) by { reveal(wires_available); };
    proof {
        reveal(gate_step_matches);
        assert(gates@.take(before_gates.len() as int) =~= before_gates);
        assert(gate_definitions@.take(before_origins.len() as int) =~= before_origins);
        if definition.rhs is Nor {
            assert(width == 1);
            assert(wires@[prior.len() as int] == Wire::Gate(gate));
            assert(gates@[gate as int] == rhs_gate(inputs@, ranges@, prior, definition.rhs)->Some_0);
        }
        assert(slot_wiring_matches(*definition, layouts, wires@, gates@, gate_definitions@, i as int)) by {
            reveal(slot_wiring_matches);
            assert forall|j: int| range.start <= j < range.end implies
                (#[trigger] wires@[j]) == projected_wire(inputs@, ranges@, prior,
                    rhs_projection(definition.rhs, if definition.rhs is Nor { gate } else { 0usize }), j - range.start) by {
                assert(wires@[j] == projected_wire(inputs@, ranges@, prior, projection, j - prior.len()));
            };
        };
    }
    Ok(())
}

#[verifier::opaque]
spec fn output_wiring_matches(
    source: &CheckedBitFunc, layouts: &Layouts, wires: Seq<Wire>, outputs: Seq<Wire>, end_port: int,
) -> bool {
    body_output_wiring_matches(source.output_drivers@, layouts, wires, outputs, end_port)
}

spec fn body_output_wiring_matches(
    drivers: Seq<OutputDriver>, layouts: &Layouts, wires: Seq<Wire>, outputs: Seq<Wire>, end_port: int,
) -> bool {
    forall|port: int, bit: int| {
        let range = layouts.outputs.ranges_model()[port];
        0 <= port < end_port && 0 <= bit < range.end - range.start
    } ==> (#[trigger] outputs[layouts.outputs.ranges_model()[port].start + bit])
        == driver_wire(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), wires,
            drivers[port], bit)
}

proof fn output_port_preserves_wiring(
    widths: Seq<u64>, drivers: Seq<OutputDriver>, layouts: &Layouts, capacity: usize, wires: Seq<Wire>,
    prior: Seq<Wire>, outputs: Seq<Wire>, port: usize,
)
    requires
        port_bit_layout_result(widths, capacity, Ok(layouts.outputs)),
        port < widths.len(),
        port < layouts.outputs.ranges_model().len(),
        port < drivers.len(),
        prior.len() == layouts.outputs.ranges_model()[port as int].start,
        layouts.outputs.ranges_model()[port as int].end <= outputs.len(),
        outputs.take(prior.len() as int) == prior,
        body_output_wiring_matches(drivers, layouts, wires, prior, port as int),
        forall|bit: int| 0 <= bit < layouts.outputs.ranges_model()[port as int].end
                - layouts.outputs.ranges_model()[port as int].start ==>
            (#[trigger] outputs[prior.len() + bit]) == driver_wire(
                layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), wires,
                drivers[port as int], bit),
    ensures body_output_wiring_matches(drivers, layouts, wires, outputs, port + 1),
{
    let ranges = layouts.outputs.ranges_model();
    port_bit_layout_port(widths, capacity, layouts.outputs, port);
    assert forall|p: int, b: int| 0 <= p < port + 1 && 0 <= b < ranges[p].end - ranges[p].start implies
        (#[trigger] outputs[ranges[p].start + b])
            == driver_wire(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), wires,
                drivers[p], b) by {
        if p < port {
            port_bit_layout_port(widths, capacity, layouts.outputs, p as usize);
            preceding_port_bits_grow(widths, (p + 1) as nat, port as nat);
            let i = ranges[p].start + b;
            assert(outputs[i] == prior[i]);
            assert(prior[ranges[p].start + b] == driver_wire(
                layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), wires, drivers[p], b));
        } else {
            assert(p == port);
            assert(outputs[prior.len() + b] == driver_wire(layouts.inputs.ranges_model(),
                layouts.definitions.ranges_model(), wires, drivers[p], b));
        }
    };
}

fn lower_outputs(
    source: &CheckedBitFunc, layouts: &Layouts, _capacity: usize, wires: &[Wire], _gate_count: usize,
) -> (outputs: Vec<Wire>)
    requires
        checked_bit_func_available(source),
        layouts_result(source, _capacity, Ok(*layouts)),
        wires@.len() == preceding_port_bits(definition_widths(source.definitions@), source.definitions@.len()),
        wires_available(wires@, layouts.inputs.total_bits_model(), _gate_count as nat),
    ensures
        outputs@.len() == layouts.outputs.total_bits_model(),
        output_wiring_matches(source, layouts, wires@, outputs@, source.output_widths@.len() as int),
        output_ports_available(outputs@, layouts.inputs.total_bits_model() as nat, _gate_count as nat, outputs@.len() as int),
{
    proof {
        reveal(layouts_result);
        assert forall|p: int| 0 <= p < source.output_widths@.len() implies
            bit_driver_width(source.input_widths@, source.definitions@, #[trigger] source.output_drivers@[p])
                == Some(source.output_widths@[p]) by {
            use_bit_output(source, p);
        };
        use_type_invariant(source);
        reveal(checked_bit_func_available);
    }
    let body = LoweringBody { input_widths: source.input_widths.as_slice(), definitions: source.definitions.as_slice() };
    let outputs = lower_body_outputs(&body, source.output_widths.as_slice(), source.output_drivers.as_slice(),
        layouts, _capacity, wires, _gate_count);
    assert(output_wiring_matches(source, layouts, wires@, outputs@, source.output_widths@.len() as int)) by {
        reveal(output_wiring_matches);
    };
    outputs
}

fn lower_body_outputs(
    body: &LoweringBody, widths: &[u64], drivers: &[OutputDriver],
    layouts: &Layouts, _capacity: usize, wires: &[Wire], _gate_count: usize,
) -> (outputs: Vec<Wire>)
    requires
        widths@.len() == drivers@.len(),
        forall|p: int| 0 <= p < widths@.len() ==>
            bit_driver_width(body.input_widths@, body.definitions@, #[trigger] drivers@[p]) == Some(widths@[p]),
        body_definition_layouts(body.input_widths@, body.definitions@, _capacity, layouts),
        widths_layout(widths@, _capacity, &layouts.outputs),
        wires@.len() == preceding_port_bits(definition_widths(body.definitions@), body.definitions@.len()),
        wires_available(wires@, layouts.inputs.total_bits_model(), _gate_count as nat),
    ensures
        outputs@.len() == layouts.outputs.total_bits_model(),
        body_output_wiring_matches(drivers@, layouts, wires@, outputs@, widths@.len() as int),
        output_ports_available(outputs@, layouts.inputs.total_bits_model() as nat, _gate_count as nat, outputs@.len() as int),
{
    proof { body_inputs_end_within_layout(body, _capacity, layouts); }
    let ghost input_bits = layouts.inputs.total_bits_model();
    let inputs = layouts.inputs.ranges();
    let ranges = layouts.definitions.ranges();

    let ports = layouts.outputs.ranges();
    let mut outputs = Vec::new();
    let mut port = 0;
    assert(body_output_wiring_matches(drivers@, layouts, wires@, outputs@, 0));
    assert(preceding_port_bits(widths@, 0) == 0) by { reveal(preceding_port_bits); };
    while port < ports.len()
        invariant
            widths@.len() == drivers@.len(),
            forall|p: int| 0 <= p < widths@.len() ==>
                bit_driver_width(body.input_widths@, body.definitions@, #[trigger] drivers@[p]) == Some(widths@[p]),
            body_definition_layouts(body.input_widths@, body.definitions@, _capacity, layouts),
            inputs@ == layouts.inputs.ranges_model(),
            ranges@ == layouts.definitions.ranges_model(),
            ports@ == layouts.outputs.ranges_model(),
            ports@.len() == widths@.len(),
            port_bit_layout_result(widths@, _capacity, Ok(layouts.outputs)),
            input_bits == layouts.inputs.total_bits_model(),
            forall|j: int| 0 <= j < inputs@.len() ==> (#[trigger] inputs@[j]).end <= input_bits,
            wires@.len() == preceding_port_bits(definition_widths(body.definitions@), body.definitions@.len()),
            wires_available(wires@, input_bits, _gate_count as nat),
            port <= ports@.len(),
            body_output_wiring_matches(drivers@, layouts, wires@, outputs@, port as int),
            outputs@.len() == preceding_port_bits(widths@, port as nat),
            output_ports_available(outputs@, input_bits as nat, _gate_count as nat, outputs@.len() as int),
        decreases ports@.len() - port,
    {
        proof {
            port_bit_layout_port(widths@, _capacity, layouts.outputs, port);
        }
        let range = &ports[port];
        let width = range.end - range.start;
        let driver = drivers[port];
        let ghost prior = outputs@;
        assert(outputs@.take(range.start as int) =~= prior);
        let mut bit = 0;
        while bit < width
            invariant
                body_definition_layouts(body.input_widths@, body.definitions@, _capacity, layouts),
                inputs@ == layouts.inputs.ranges_model(), ranges@ == layouts.definitions.ranges_model(),
                input_bits == layouts.inputs.total_bits_model(),
                forall|j: int| 0 <= j < inputs@.len() ==> (#[trigger] inputs@[j]).end <= input_bits,
                port < widths@.len() == drivers@.len(),
                driver == drivers@[port as int],
                width == widths@[port as int],
                bit_driver_width(body.input_widths@, body.definitions@, driver) == Some(width as u64),
                wires@.len() == preceding_port_bits(definition_widths(body.definitions@), body.definitions@.len()),
                wires_available(wires@, input_bits, _gate_count as nat),
                bit <= width,
                outputs@.len() == range.start + bit,
                prior.len() == range.start,
                outputs@.take(range.start as int) == prior,
                forall|j: int| 0 <= j < bit ==> (#[trigger] outputs@[range.start + j])
                    == driver_wire(inputs@, ranges@, wires@, driver, j),
                output_ports_available(outputs@, input_bits as nat, _gate_count as nat, outputs@.len() as int),
            decreases width - bit,
        {
            proof {
                body_driver_bits_fit_layout(body.input_widths@, body.definitions@, layouts, _capacity, body.definitions@.len() as int,
                    wires@.len() as int, driver, width as u64, bit as int);
                driver_wire_is_available(inputs@, ranges@, wires@, driver, bit as int, input_bits, _gate_count as nat);
            }
            let wire = lower_driver_bit(inputs, ranges, wires, driver, bit);
            let ghost previous = outputs@;
            outputs.push(wire);
            assert(outputs@.take(range.start as int) =~= prior);
            assert forall|j: int| 0 <= j <= bit implies (#[trigger] outputs@[range.start + j])
                == driver_wire(inputs@, ranges@, wires@, driver, j) by {
                if j < bit { assert(outputs@[range.start + j] == previous[range.start + j]); }
            };
            assert forall|j: int| 0 <= j < outputs@.len() implies
                wire_available(#[trigger] outputs@[j], input_bits as nat, _gate_count as nat) by {
                if j < previous.len() { assert(outputs@[j] == previous[j]); }
            };
            bit += 1;
        }
        proof { output_port_preserves_wiring(widths@, drivers@, layouts, _capacity, wires@, prior, outputs@, port); }
        port += 1;
    }
    proof { port_bit_layout_size(widths@, _capacity, &layouts.outputs); }
    outputs
}

/// 宣言順の入出力配置と、組み合わせ回路の平坦な配線を保持する。
#[derive(Debug)]
pub struct LoweredBitFunc {
    netlist: NorNetlist,
    layouts: Layouts,
    definition_wires: Vec<Wire>,
    gate_definitions: Vec<usize>,
}

impl LoweredBitFunc {
    /// 評価する NOR ネットリストを返す。
    pub fn netlist(&self) -> (netlist: &NorNetlist)
        ensures *netlist == *self.netlist_model(),
    { &self.netlist }

    /// 宣言順の入力ポートのビット配置を返す。
    pub fn inputs(&self) -> (layout: &PortBitLayout)
        ensures *layout == *self.input_layout_model(),
    { &self.layouts.inputs }

    /// 宣言順の出力ポートのビット配置を返す。
    pub fn outputs(&self) -> (layout: &PortBitLayout)
        ensures *layout == *self.output_layout_model(),
    { &self.layouts.outputs }

    /// ゲート順に元の定義の添字を返す。
    ///
    /// 左辺に複数の結果がある場合は、結果ごとに添字を割り当てる。
    /// 呼び出し先から展開したゲートには、呼び出し元の左辺の最初の結果の添字を返す。
    pub fn gate_definitions(&self) -> (definitions: &[usize])
        ensures definitions@ == self.gate_definitions_model(),
    { self.gate_definitions.as_slice() }

    /// 各定義の配線を返す。定義順、各定義内では最下位ビットから並ぶ。
    pub fn definition_wires(&self) -> (wires: &[Wire])
        ensures wires@ == self.definition_wires_model(),
    { self.definition_wires.as_slice() }

    /// 宣言順とポート内のビット順で定まる入力配置を表す。
    pub closed spec fn input_layout_model(&self) -> &PortBitLayout { &self.layouts.inputs }

    /// 宣言順とポート内のビット順で定まる出力配置を表す。
    pub closed spec fn output_layout_model(&self) -> &PortBitLayout { &self.layouts.outputs }

    /// ゲート順に変換前の定義の添字を並べた列を表す。
    pub closed spec fn gate_definitions_model(&self) -> Seq<usize> { self.gate_definitions@ }

    /// 定義順と各定義の最下位ビット順に並ぶ配線を表す。
    pub closed spec fn definition_wires_model(&self) -> Seq<Wire> { self.definition_wires@ }

    /// 平坦なネットリストを表す。
    pub closed spec fn netlist_model(&self) -> &NorNetlist { &self.netlist }
}

/// 配置の違反、または入出力と各定義の配線が関数本体に対応する変換結果を表す。
pub closed spec fn lowered_bit_func_result(
    source: &CheckedBitFunc, capacity: usize, result: Result<LoweredBitFunc, BitFuncLowerError>,
) -> bool {
    match result {
        Err(error) => layouts_result(source, capacity, Err(error)),
        Ok(value) => layouts_result(source, capacity, Ok(value.layouts))
            && nor_evaluation_ready(&value.netlist, value.layouts.inputs.total_bits_model() as nat)
            && value.netlist.outputs@.len() == value.layouts.outputs.total_bits_model()
            && value.definition_wires@.len() == value.layouts.definitions.total_bits_model()
            && wires_available(value.definition_wires@, value.layouts.inputs.total_bits_model(), value.netlist.gates@.len())
            && value.gate_definitions@.len() == value.netlist.gates@.len()
            && gate_origins_in_definition_order(source, &value.layouts, value.definition_wires@,
                value.gate_definitions@, source.definitions@.len() as int)
            && (forall|i: int| 0 <= i < source.definitions@.len() ==>
                #[trigger] definition_wiring_matches(source, &value.layouts, value.definition_wires@,
                    value.netlist.gates@, value.gate_definitions@, i))
            && output_wiring_matches(source, &value.layouts, value.definition_wires@,
                value.netlist.outputs@, source.output_widths@.len() as int),
    }
}

/// 単独関数の変換結果から、再利用するネットリストの入出力配置を取り出す。
pub(super) proof fn standalone_template_layouts(source: &CheckedBitFunc, limit: usize, lowered: &LoweredBitFunc)
    requires lowered_bit_func_result(source, limit, Ok(*lowered)),
    ensures
        port_bit_layout_result(source.input_widths@, limit, Ok(*lowered.input_layout_model())),
        port_bit_layout_result(source.output_widths@, limit, Ok(*lowered.output_layout_model())),
        nor_evaluation_ready(lowered.netlist_model(), lowered.input_layout_model().total_bits_model() as nat),
        lowered.netlist_model().outputs@.len() == lowered.output_layout_model().total_bits_model(),
{
    reveal(lowered_bit_func_result);
    reveal(layouts_result);
}

impl<'p, 'a> CheckedBitFunc<'p, 'a> {
    /// 入出力のポートを宣言順に配置し、定義順に配線とゲートへ変換する。
    ///
    /// 各ポートと定義の平坦配列は最下位ビットから並ぶ。入力、定義、出力の各配列に
    /// 同じビット数の上限を適用する。この上限は論理ビット数を数える。
    ///
    /// # Examples
    ///
    /// ポートのビット幅に合わせて入力を並べ、出力ポートの配置から評価値を取り出す。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    ///
    /// let text = "(using nor)
    ///     (func f (in x (a (bits 256))) (out (even (bits 4)) y)
    ///         (def even (slice a 0 4 2))
    ///         (def hi (bit a 255))
    ///         (def y (nor x hi)))";
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "main.ncg2", revision: 1, text,
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let checked = aliases.check_bit_func(0, 1, 512).unwrap();
    /// let lowered = checked.lower_bit_func(512).unwrap();
    ///
    /// let mut input = vec![false; lowered.inputs().total_bits()];
    /// input[lowered.inputs().bit_index(1, 0).unwrap()] = true;
    /// input[lowered.inputs().bit_index(1, 4).unwrap()] = true;
    /// input[lowered.inputs().bit_index(1, 255).unwrap()] = true;
    /// let output = lowered.netlist().evaluate(&input).unwrap();
    /// assert_eq!(&output[lowered.outputs().ranges()[0].clone()], &[true, false, true, false]);
    /// assert!(!output[lowered.outputs().bit_index(1, 0).unwrap()]);
    /// assert_eq!(lowered.gate_definitions(), &[2]);
    /// ```
    ///
    /// # Errors
    ///
    /// 入力、定義、出力の順に幅を確認し、最初の配置違反を返す。
    pub fn lower_bit_func(&self, capacity: usize) -> (result: Result<LoweredBitFunc, BitFuncLowerError>)
        ensures lowered_bit_func_result(self, capacity, result),
    {
        let layouts = match prepare_layouts(self, capacity) {
            Ok(layouts) => layouts,
            Err(error) => {
                let result = Err(error);
                assert(lowered_bit_func_result(self, capacity, result)) by { reveal(lowered_bit_func_result); };
                return result;
            },
        };
        proof {
            use_type_invariant(self);
            use_layouts(self, capacity, &layouts);
        }
        let input_bits = layouts.inputs.total_bits();
        let ghost inputs = layouts.inputs.ranges_model();
        let ghost ranges = layouts.definitions.ranges_model();
        let mut wires = Vec::new();
        let mut gates = Vec::new();
        let mut gate_definitions = Vec::new();
        let mut i = 0;
        assert(gate_origins_in_definition_order(self, &layouts, wires@, gate_definitions@, 0))
            by { reveal(gate_origins_in_definition_order); };
        assert(wires_available(wires@, input_bits, 0)) by { reveal(wires_available); };
        assert(preceding_port_bits(definition_widths(self.definitions@), 0) == 0) by { reveal(preceding_port_bits); };
        while i < self.definitions.len()
            invariant
                checked_bit_func_available(self),
                layouts_result(self, capacity, Ok(layouts)),
                inputs == layouts.inputs.ranges_model(),
                ranges == layouts.definitions.ranges_model(),
                input_bits == layouts.inputs.total_bits_model(),
                ranges.len() == self.definitions@.len(),
                port_bit_layout_result(definition_widths(self.definitions@), capacity, Ok(layouts.definitions)),
                forall|j: int| 0 <= j < inputs.len() ==> (#[trigger] inputs[j]).end <= input_bits,
                i <= self.definitions@.len(),
                wires@.len() == preceding_port_bits(definition_widths(self.definitions@), i as nat),
                wires_available(wires@, input_bits, gates@.len()),
                gates_available(gates@, input_bits as nat, gates@.len() as int),
                gates@.len() == gate_definitions@.len() <= i,
                gate_origins_in_definition_order(self, &layouts, wires@, gate_definitions@, i as int),
                forall|j: int| 0 <= j < i ==>
                    #[trigger] definition_wiring_matches(self, &layouts, wires@, gates@, gate_definitions@, j),
            decreases self.definitions@.len() - i,
        {
            let ghost prior = wires@;
            let ghost prior_gates = gates@;
            let ghost prior_origins = gate_definitions@;
            let body = LoweringBody { input_widths: self.input_widths.as_slice(), definitions: self.definitions.as_slice() };
            proof {
                reveal(layouts_result);
                use_bit_definition(self, i as int);
            }
            let _lowered = lower_definition(&body, &layouts, capacity, usize::MAX, i,
                &mut wires, &mut gates, &mut gate_definitions);
            proof { assert(_lowered.is_ok()); }
            assert(definition_wiring_matches(self, &layouts, wires@, gates@, gate_definitions@, i as int))
                by { reveal(definition_wiring_matches); };
            proof {
                gate_origins_preserved(self, &layouts, i, prior, prior_gates, prior_origins,
                    wires@, gates@, gate_definitions@);
            }
            assert forall|j: int| 0 <= j <= i implies
                #[trigger] definition_wiring_matches(self, &layouts, wires@, gates@, gate_definitions@, j) by {
                if j < i {
                    assert(definition_wiring_matches(self, &layouts, prior, prior_gates, prior_origins, j));
                    reveal(definition_wiring_matches);
                    slot_wiring_is_preserved(self.definitions@[j], &layouts, j, prior, wires@,
                        prior_gates, gates@, prior_origins, gate_definitions@);
                }
            };
            i += 1;
        }
        proof { port_bit_layout_size(definition_widths(self.definitions@), capacity, &layouts.definitions); }

        let outputs = lower_outputs(self, &layouts, capacity, wires.as_slice(), gates.len());
        let result = Ok(LoweredBitFunc {
            netlist: NorNetlist { input_count: input_bits, gates, outputs },
            layouts, definition_wires: wires, gate_definitions,
        });
        assert(lowered_bit_func_result(self, capacity, result)) by { reveal(lowered_bit_func_result); };
        result
    }
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn local_nor_reports_a_full_gate_budget_at_its_source() {
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    let text = "(using nor) (func invert (in a) (out y) (def t a) (def y (nor t t)))";
    let project = parse_circuit_project(&[SourceSnapshot { path: "invert.ncg2", revision: 1, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let checked = aliases.check_bit_func(0, 1, 8).unwrap();
    let layout = prepare_layouts(&checked, 8).unwrap();
    let body = LoweringBody { input_widths: checked.input_widths.as_slice(), definitions: checked.definitions.as_slice() };
    let mut wires = Vec::new();
    let mut gates = Vec::new();
    let mut origins = Vec::new();

    lower_definition(&body, &layout, 8, 0, 0, &mut wires, &mut gates, &mut origins).unwrap();
    let error = lower_definition(&body, &layout, 8, 0, 1, &mut wires, &mut gates, &mut origins).unwrap_err();
    assert_eq!(&text[error.span], "(nor t t)");
    assert_eq!(wires.as_slice(), &[Wire::Input(0)]);
    assert!(gates.is_empty() && origins.is_empty());
}

} // verus!
