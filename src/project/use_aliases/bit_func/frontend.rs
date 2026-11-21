//! 検査済みの構文、結線、型からビット列の組み合わせ回路を取り出す。

#[cfg(verus_only)]
mod source_evaluation;
mod body;
pub(super) use body::{ExpandedBody, ExpandedBodyError};
#[cfg(verus_only)]
pub(super) use body::{argument_matches_width, call_covers};

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{BitFuncRhs, CheckedBitDefinition, CheckedBitFunc};
use super::expansion::CheckedExpansionCall;
use super::templates::ResolvedTemplateCall;
#[cfg(verus_only)]
use super::templates::call_ports_need_structure_layout;
use super::super::{
    FuncCallSignatureError, FuncCallTarget, FuncSignalTypeError, FuncSignalTypes, FuncWiring, FuncWiringResult, OutputDriver,
    ResolvedPortType, SelectionArgumentError, SingleBitOperand, StructureLayouts, StructureTypeError,
    TypedPort, TypedRoutineSignature, UseAliases,
};
use super::super::function_atoms::{ConcatProjection, StructureProjection, copy_location, named_selection};
#[cfg(verus_only)]
use super::super::function_atoms::SignalType;
use super::super::selection_arguments::{
    check_selection_arguments, check_selection_chain, compose_selections, nested_named_selection,
    select_contiguous_range,
};
use crate::project::{LocatedName, ProjectSource};
use crate::project::circuits::form_location;
use crate::syntax::{AtomKind, Form, circuit::{NamedBuildCircuit, definition_target_atoms}};

#[cfg(verus_only)]
use super::{bit_definition_matches, bit_driver_width, bit_vector_token, checked_bit_func_available,
    concat_operands_fit, literal_bytes, nor_operand_matches};
#[cfg(verus_only)]
use crate::project::literal_width::circuit_bit_literal_boundary;
#[cfg(verus_only)]
use crate::project::circuit_literal_width_matches;
#[cfg(verus_only)]
use super::super::{
    FuncCallOutputTypes, TypedFuncCall, function_atoms::named_selection_matches,
    function_drivers::{checked_ports_and_output_bounds, expected_output_context, indexed_driver_site},
    port_types::typed_name_sites, selection_arguments::selection_arguments_match, single_bit_func::{bare_rhs_driver_matches, constant_operand_literal, no_operand, operand_matches, selection_rhs_driver_matches},
};
#[cfg(verus_only)]
use super::super::function_atoms::{
    concat_projection_evidence, concat_projection_matches, concat_projection_required, concat_projections_complete,
    concat_projections_order, signal_type_at,
    structure_projection_matches, structure_projection_required, structure_projections_in_order,
};
#[cfg(verus_only)]
use super::super::selection_arguments::{
    CheckedBitSelection, contiguous_selection, field_and_named_selection_disjoint, nested_named_selection_matches,
    selection_chain_arguments_match, selection_chain_success_excludes_error, selection_composition,
    successful_selection_chain_counts_agree,
};
#[cfg(verus_only)]
use super::super::single_bit_func::nested_selection_rhs_driver_matches;
#[cfg(verus_only)]
use crate::project::location_in_source;
#[cfg(verus_only)]
use super::semantics::contiguous_rhs_matches;
#[cfg(verus_only)]
use crate::project::circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::syntax::{form_spans_valid, circuit::{
    BitSelectionShape, bit_selection_shape_positions, build_definition_scope_evidence,
    StructureExpressionShape, bit_selection_shapes_agree, build_field_selection_signal, definition_target_range,
    field_selection_root, field_selection_shape_matches, indexed_entry_evidence,
}};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 現段階のビット列の回路へ取り出せない構文または型。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedBitFunc {
    /// 入力または出力のビット列型の幅が0である。
    PortType,
    /// 出力ポートがない。
    OutputCount,
    /// 左辺に複数の結果が並んでいる。
    DefinitionOutputCount,
    /// 右辺が対応する構文に収まらない。
    Expression,
}

/// 幅付きの組み合わせ回路を取り出すときの診断。
#[derive(Debug)]
pub enum BitFuncError<'p, 'a> {
    /// 指定された項目が関数ではない。
    NotFunc,
    /// 展開が必要な箇所。
    NeedsExpansion(LocatedName<'p, 'a>),
    /// 既存の型・結線検査で見つかった違反。
    Check(FuncSignalTypeError<'p, 'a>),
    /// 構造体ポートの幅を取り出す前に、宣言の配置または循環検査で見つかった違反。
    PortLayout(StructureTypeError<'p, 'a>),
    /// 定義内の呼び出し先の検査で見つかった違反。
    Call(usize, FuncCallSignatureError<'p, 'a>),
    /// ビット選択の引数の違反。
    Selection(SelectionArgumentError<'p, 'a>),
    /// 基底 NOR の入力幅の違反。
    NorInputWidth {
        /// 当該引数の位置。
        argument: LocatedName<'p, 'a>,
        /// 入力の幅。
        actual: u64,
    },
    /// 出力宣言と出力を駆動する値の幅が異なる。
    OutputWidth {
        /// 出力の宣言型を指定した位置。
        annotation: LocatedName<'p, 'a>,
        /// 宣言された幅。
        expected: u64,
        /// 駆動元の幅。
        actual: u64,
    },

    /// 正規化の対象に含まれない箇所。
    Unsupported(UnsupportedBitFunc, LocatedName<'p, 'a>),
}

/// 入出力ポートの宣言順の幅と、構造体型を展開するときの配置表。
#[derive(Debug)]
pub(super) struct PreparedBitFuncPorts<'p, 'a> {
    pub(super) inputs: Vec<u64>,
    pub(super) outputs: Vec<u64>,
    pub(super) layouts: Option<StructureLayouts<'p, 'a>>,
}

struct FuncProjection<'w, 'p, 'a> {
    file: usize,
    entry: usize,
    limit: u64,
    source: &'p ProjectSource<'a>,
    parsed: &'p NamedBuildCircuit<'a>,
    wiring: &'w FuncWiring<'p, 'a>,
    inputs: &'w Vec<u64>,
    outputs: &'w Vec<u64>,
    #[cfg(verus_only)]
    layouts: Option<&'w StructureLayouts<'p, 'a>>,
    #[cfg(verus_only)]
    types: &'w Vec<Option<SignalType<'p, 'a>>>,
    structures: &'w Vec<StructureProjection>,
}

pub(super) open spec fn has_structure_port(ports: Seq<TypedPort>) -> bool {
    exists|i: int| 0 <= i < ports.len() && (#[trigger] ports[i]).ty is Struct
}

pub(super) fn contains_structure_port(ports: &[TypedPort]) -> (has_structure: bool)
    ensures has_structure == has_structure_port(ports@),
{
    let mut i = 0;
    while i < ports.len()
        invariant
            i <= ports@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] ports@[j]).ty is Bits,
        decreases ports@.len() - i,
    {
        if matches!(ports[i].ty, ResolvedPortType::Struct { .. }) {
            assert(has_structure_port(ports@));
            return true;
        }
        i += 1;
    }
    false
}

spec fn supported_ports(ports: Seq<TypedPort>) -> bool {
    forall|i: int| 0 <= i < ports.len() ==>
        (#[trigger] ports[i]).ty != ResolvedPortType::Bits(0)
}

spec fn unsupported_port(source: &ProjectSource, forms: Seq<Form>, ports: Seq<TypedPort>, site: LocatedName) -> bool {
    exists|i: int| 0 <= i < ports.len()
        && (#[trigger] ports[i]).ty == ResolvedPortType::Bits(0)
        && is_form_location(source, forms[ports[i].declared.site.name as int], site)
        && forall|j: int| 0 <= j < i ==>
            (#[trigger] ports[j]).ty != ResolvedPortType::Bits(0)
}

fn check_ports<'p, 'a>(source: &'p ProjectSource<'a>, forms: &[Form], ports: &[TypedPort<'p,'a>])
    -> (result: Result<(), LocatedName<'p, 'a>>)
    requires
        typed_name_sites(forms@, ports@),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> supported_ports(ports@),
        result matches Err(location) ==> unsupported_port(source, forms@, ports@, location),
{
    let mut i = 0;
    while i < ports.len()
        invariant
            i <= ports@.len(),
            typed_name_sites(forms@, ports@),
            form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
            forall|j: int| 0 <= j < i ==>
                (#[trigger] ports@[j]).ty != ResolvedPortType::Bits(0),
        decreases ports@.len() - i,
    {
        let port = &ports[i];
        if matches!(port.ty, ResolvedPortType::Bits(0)) {
            return Err(form_location(source, forms, port.declared.site.name));
        }
        i += 1;
    }
    Ok(())
}

spec fn driver_width_origin<'p, 'a>(
    signature: &TypedRoutineSignature<'p, 'a>, prior: Seq<CheckedBitDefinition<'p, 'a>>, driver: OutputDriver,
) -> LocatedName<'p, 'a> {
    match driver {
        OutputDriver::Input(i) => signature.inputs@[i as int].annotation,
        OutputDriver::Definition(i) => prior[i as int].expression,
    }
}

fn driver_type<'w, 'p, 'a>(
    signature: &'w TypedRoutineSignature<'p, 'a>, inputs: &[u64],
    prior: &'w [CheckedBitDefinition<'p, 'a>], driver: OutputDriver,
) -> (ty: (u64, &'w LocatedName<'p, 'a>))
    requires
        inputs@.len() == signature.inputs@.len(),
        match driver {
            OutputDriver::Input(i) => i < signature.inputs@.len(),
            OutputDriver::Definition(i) => i < prior@.len(),
        },
    ensures
        bit_driver_width(inputs@, prior@, driver) == Some(ty.0),
        *ty.1 == driver_width_origin(signature, prior@, driver),
{
    match driver {
        OutputDriver::Input(i) => {
            let port = &signature.inputs[i];
            (inputs[i], &port.annotation)
        },
        OutputDriver::Definition(i) => (prior[i].width, &prior[i].expression),
    }
}

/// 検査済みの半開区間を、直結または刻み1のビット選択に変換する。
fn contiguous_rhs(input: OutputDriver, start: u64, end: u64, input_width: u64) -> (rhs: BitFuncRhs)
    requires start < end <= input_width,
    ensures contiguous_rhs_matches(rhs, input, start, end, input_width),
{
    if start == 0 && end == input_width {
        BitFuncRhs::Driver(input)
    } else {
        let selection = select_contiguous_range(start, end, input_width);
        BitFuncRhs::Selection { input, selection }
    }
}

/// 構造体式の区間と、その結果から選んだビットを元の入力上の配線に対応させる。
spec fn structure_rhs_matches(rhs: BitFuncRhs, projection: StructureProjection) -> bool {
    let range = projection.operation.range;
    if let Some(outer) = projection.selection {
        rhs matches BitFuncRhs::Selection { input, selection }
            && input == projection.input
            && selection_composition(contiguous_selection(range.start, range.end), outer, selection)
            && selection.fits(projection.input_width)
    } else {
        contiguous_rhs_matches(rhs, projection.input, range.start, range.end, projection.input_width)
    }
}

/// 現在の定義に対応する行を取り出し、次の未処理行へ進める。
fn next_structure_projection(rows: &[StructureProjection], cursor: usize, target: usize)
    -> (result: (usize, Option<usize>))
    requires
        cursor <= rows@.len(),
        forall|j: int| 0 <= j < cursor ==> (#[trigger] rows@[j]).target < target,
        forall|j: int| cursor <= j < rows@.len() ==> target <= (#[trigger] rows@[j]).target,
        forall|a: int, b: int| 0 <= a < b < rows@.len() ==> (#[trigger] rows@[a]).target < (#[trigger] rows@[b]).target,
    ensures
        result.0 <= rows@.len(),
        forall|j: int| 0 <= j < result.0 ==> (#[trigger] rows@[j]).target <= target,
        forall|j: int| result.0 <= j < rows@.len() ==> target < (#[trigger] rows@[j]).target,
        result.1 matches Some(at) ==> at < rows@.len() && rows@[at as int].target == target,
        result.1.is_none() ==> forall|j: int| 0 <= j < rows@.len() ==> (#[trigger] rows@[j]).target != target,
{
    if cursor < rows.len() && rows[cursor].target == target {
        assert forall|j: int| cursor < j < rows@.len() implies target < (#[trigger] rows@[j]).target by {
            assert(rows@[cursor as int].target < rows@[j].target);
        };
        (cursor + 1, Some(cursor))
    } else {
        assert forall|j: int| cursor <= j < rows@.len() implies target < (#[trigger] rows@[j]).target by {
            if cursor < j { assert(rows@[cursor as int].target < rows@[j].target); }
        };
        (cursor, None)
    }
}

#[verifier::opaque]
spec fn concat_cursor_ready(rows: Seq<ConcatProjection>, model: Seq<ConcatProjection>, cursor: usize, target: int) -> bool {
    &&& cursor <= rows.len() == model.len()
    &&& forall|j: int| 0 <= j < cursor ==> (#[trigger] model[j]).target < target
    &&& forall|j: int| cursor <= j < rows.len() ==> (#[trigger] rows[j]) == model[j] && target <= model[j].target
}

/// 定義順に走査し、対象の連接に保存した引数列を移す。
fn take_concat_projection(
    rows: &mut Vec<ConcatProjection>, cursor: usize, target: usize, Ghost(model): Ghost<Seq<ConcatProjection>>,
) -> (result: (usize, Option<ConcatProjection>))
    requires
        concat_cursor_ready(old(rows)@, model, cursor, target as int),
        forall|a: int, b: int| 0 <= a < b < model.len() ==> (#[trigger] model[a]).target < (#[trigger] model[b]).target,
    ensures
        concat_cursor_ready(final(rows)@, model, result.0, target as int + 1),
        result.1 matches Some(row) ==> cursor < model.len() && row == model[cursor as int]
            && row.target == target && result.0 == cursor + 1,
        result.1.is_none() ==> result.0 == cursor,
        result.1.is_none() ==> forall|j: int| 0 <= j < model.len() ==> (#[trigger] model[j]).target != target,
{
    reveal(concat_cursor_ready);
    if cursor < rows.len() && rows[cursor].target == target {
        let mut row = ConcatProjection { target, width: 0, _arguments: Ghost(arbitrary()), operands: Vec::new() };
        let ghost original = rows@[cursor as int];
        assert(original == model[cursor as int]);
        rows.set_and_swap(cursor, &mut row);
        (cursor + 1, Some(row))
    } else {
        (cursor, None)
    }
}

spec fn concat_type_ready(scope: &FuncProjection, index: int) -> bool {
    let driver = scope.wiring.drivers.definitions@[index];
    let root = scope.parsed.definitions@[driver.definition as int].expression.start;
    &&& 0 <= index < scope.types@.len() && index < scope.wiring.drivers.definitions@.len()
    &&& driver.result_index == 0
    &&& scope.types@[index] matches Some(ty) && ty.ty is Bits
    &&& exists|args: core::ops::Range<usize>|
        #[trigger] crate::syntax::circuit::concat_arguments_match(scope.source.text, scope.parsed.syntax.forms@, root as int, args)
}

spec fn bit_vector_form(form: Form) -> bool {
    form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal)
}

fn operand_width(
    signature: &TypedRoutineSignature, inputs: &[u64], prior: &[CheckedBitDefinition], operand: SingleBitOperand,
) -> (width: u64)
    requires
        inputs@.len() == signature.inputs@.len(),
        super::super::single_bit_func::single_bit_operand_available(operand, signature.inputs@.len(), prior@.len()),
    ensures
        nor_operand_matches(inputs@, prior@, operand) <==> width == 1,
        operand is Constant ==> width == 1,
        operand matches SingleBitOperand::Driver(driver) ==> bit_driver_width(inputs@, prior@, driver) == Some(width),
{
    match operand {
        SingleBitOperand::Constant(_) => 1,
        SingleBitOperand::Driver(driver) => driver_type(signature, inputs, prior, driver).0,
    }
}

spec fn output_widths_before(
    inputs: Seq<u64>, outputs: Seq<u64>, definitions: Seq<CheckedBitDefinition>, drivers: Seq<OutputDriver>, stop: int,
) -> bool {
    forall|j: int| 0 <= j < stop ==> bit_driver_width(inputs, definitions, #[trigger] drivers[j]) == Some(outputs[j])
}

spec fn output_width_failure(
    signature: &TypedRoutineSignature, inputs: Seq<u64>, outputs: Seq<u64>,
    definitions: Seq<CheckedBitDefinition>, drivers: Seq<OutputDriver>, error: BitFuncError,
) -> bool {
    error matches BitFuncError::OutputWidth { annotation, expected, actual }
        && (exists|port: int| 0 <= port < drivers.len()
            && bit_driver_width(inputs, definitions, #[trigger] drivers[port]) == Some(actual)
            && outputs[port] == expected
            && actual != expected && signature.outputs@[port].annotation == annotation
            && output_widths_before(inputs, outputs, definitions, drivers, port))
}

fn check_output_widths<'p, 'a>(
    wiring: &FuncWiring<'p, 'a>, inputs: &[u64], outputs: &[u64], definitions: &[CheckedBitDefinition<'p, 'a>],
) -> (result: Result<(), BitFuncError<'p, 'a>>)
    requires
        inputs@.len() == wiring.drivers.signature.inputs@.len(),
        outputs@.len() == wiring.drivers.signature.outputs@.len(),
        wiring.drivers.outputs@.len() == wiring.drivers.signature.outputs@.len(),
        forall|i: int| 0 <= i < wiring.drivers.outputs@.len() ==> match #[trigger] wiring.drivers.outputs@[i] {
            OutputDriver::Input(i) => i < wiring.drivers.signature.inputs@.len(),
            OutputDriver::Definition(i) => i < definitions@.len(),
        },
    ensures match result {
        Ok(()) => output_widths_before(inputs@, outputs@, definitions@, wiring.drivers.outputs@,
            wiring.drivers.outputs@.len() as int),
        Err(error) => output_width_failure(&wiring.drivers.signature, inputs@, outputs@, definitions@, wiring.drivers.outputs@, error),
    },
{
    let signature = &wiring.drivers.signature;
    let mut i = 0usize;
    while i < wiring.drivers.outputs.len()
        invariant
            *signature == wiring.drivers.signature,
            inputs@.len() == signature.inputs@.len(),
            outputs@.len() == signature.outputs@.len(),
            i <= wiring.drivers.outputs@.len() == signature.outputs@.len(),
            forall|j: int| 0 <= j < wiring.drivers.outputs@.len() ==> match #[trigger] wiring.drivers.outputs@[j] {
                OutputDriver::Input(i) => i < signature.inputs@.len(),
                OutputDriver::Definition(i) => i < definitions@.len(),
            },
            output_widths_before(inputs@, outputs@, definitions@, wiring.drivers.outputs@, i as int),
        decreases wiring.drivers.outputs@.len() - i,
    {
        let port = &signature.outputs[i];
        let expected = outputs[i];
        let (actual, _) = driver_type(signature, inputs, definitions, wiring.drivers.outputs[i]);
        if actual != expected {
            return Err(BitFuncError::OutputWidth { annotation: copy_location(&port.annotation), expected, actual });
        }
        i += 1;
    }
    Ok(())
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn port_preparation_error(
        &self, source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, limit: u64,
        signature: &TypedRoutineSignature, error: BitFuncError,
    ) -> bool {
        let forms = parsed.syntax.forms@;
        match error {
            BitFuncError::Unsupported(UnsupportedBitFunc::OutputCount, location) =>
                signature.outputs@.len() == 0
                && is_form_location(source, forms[parsed.syntax.entries@[entry as int].form as int], location),
            BitFuncError::Unsupported(UnsupportedBitFunc::PortType, location) => signature.outputs@.len() > 0
                && (unsupported_port(source, forms, signature.outputs@, location)
                    || (supported_ports(signature.outputs@) && unsupported_port(source, forms, signature.inputs@, location))),
            BitFuncError::PortLayout(error) => signature.outputs@.len() > 0
                && supported_ports(signature.outputs@) && supported_ports(signature.inputs@)
                && (has_structure_port(signature.outputs@) || has_structure_port(signature.inputs@))
                && self.structure_types_match(limit, Err(error)),
            _ => false,
        }
    }

    #[verifier::opaque]
    pub(super) closed spec fn routine_ports_result(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, original: Option<StructureLayouts>,
        result: Result<PreparedBitFuncPorts, BitFuncError>,
    ) -> bool {
        let signature = &wiring.drivers.signature;
        match result {
            Ok(ports) => {
                let layouts = match &ports.layouts { Some(table) => Some(table), None => None };
                &&& 0 < signature.outputs@.len()
                &&& supported_ports(signature.outputs@) && supported_ports(signature.inputs@)
                &&& self.port_widths_match(signature.inputs@, ports.inputs@, layouts)
                &&& self.port_widths_match(signature.outputs@, ports.outputs@, layouts)
                &&& self.structure_layout_for_ports(limit, layouts)
                &&& original.is_some() ==> original == ports.layouts
            },
            Err(error) => {
                let project = self.targets.project_model();
                self.port_preparation_error(&project.sources_model()[file as int], &project.circuits_model()[file as int],
                    entry, limit, signature, error)
            },
        }
    }

    /// 宣言順の入出力ポートの幅を求め、既存の構造体配置があれば再利用する。
    ///
    /// # Errors
    ///
    /// 出力ポートがない場合、ポート幅が対応範囲外の場合、配置表の検査に失敗した場合の順に診断する。
    pub(super) fn prepare_routine_ports(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring<'p, 'a>,
        mut layouts: Option<StructureLayouts<'p, 'a>>,
    ) -> (result: Result<PreparedBitFuncPorts<'p, 'a>, BitFuncError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))),
            layouts matches Some(table) ==> self.structure_types_match(limit, Ok(table)),
        ensures
            self.routine_ports_result(file, entry, limit, wiring, layouts, result),
            result matches Ok(ports) ==> (ports.layouts.is_some() <==> layouts.is_some()
                || has_structure_port(wiring.drivers.signature.inputs@)
                || has_structure_port(wiring.drivers.signature.outputs@)),
    {
        reveal(UseAliases::routine_ports_result);
        let ghost original = layouts;
        proof { self.checked_wiring_is_func(file, entry, limit, *wiring); }
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let forms = parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*source, *parsed);
            indexed_entry_evidence(source.text, forms@, parsed.syntax.entries@, entry as int);
        }
        let signature = &wiring.drivers.signature;
        if signature.outputs.is_empty() {
            let site = form_location(source, forms, parsed.syntax.entries[entry].form);
            return Err(BitFuncError::Unsupported(UnsupportedBitFunc::OutputCount, site));
        }
        if let Err(location) = check_ports(source, forms, signature.outputs.as_slice()) {
            return Err(BitFuncError::Unsupported(UnsupportedBitFunc::PortType, location));
        }
        if let Err(location) = check_ports(source, forms, signature.inputs.as_slice()) {
            return Err(BitFuncError::Unsupported(UnsupportedBitFunc::PortType, location));
        }
        if layouts.is_none() && (contains_structure_port(signature.outputs.as_slice())
            || contains_structure_port(signature.inputs.as_slice()))
        {
            match self.check_structure_types(limit) {
                Ok(table) => layouts = Some(table),
                Err(error) => return Err(BitFuncError::PortLayout(error)),
            }
        }
        let inputs = self.collect_port_widths(signature.inputs.as_slice(), layouts.as_ref(), limit);
        let outputs = self.collect_port_widths(signature.outputs.as_slice(), layouts.as_ref(), limit);
        Ok(PreparedBitFuncPorts { inputs, outputs, layouts })
    }

    pub(super) closed spec fn expanded_routine_ports_result(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, layouts: Option<StructureLayouts>,
        selected: Seq<ResolvedTemplateCall>, result: Result<PreparedBitFuncPorts, BitFuncError>,
    ) -> bool {
        match result {
            Ok(ports) => self.routine_ports_result(file, entry, limit, wiring, layouts, Ok(ports))
                && (ports.layouts.is_some() <==> layouts.is_some()
                    || has_structure_port(wiring.drivers.signature.inputs@)
                    || has_structure_port(wiring.drivers.signature.outputs@)
                    || call_ports_need_structure_layout(selected)),
            Err(error) => self.routine_ports_result(file, entry, limit, wiring, layouts, Err(error))
                || (error matches BitFuncError::PortLayout(diagnostic) && exists|ports: PreparedBitFuncPorts|
                    #[trigger] self.routine_ports_result(file, entry, limit, wiring, layouts, Ok(ports))
                    && self.called_structure_layout_result(selected, limit, ports.layouts, Err(diagnostic))),
        }
    }

    /// 呼び出し元のポートを検査し、呼び出し先の署名を扱うために必要な構造体配置も確保する。
    ///
    /// # Errors
    ///
    /// 呼び出し元のポート検査が失敗した場合はその診断を返す。
    /// ポートが妥当で、呼び出し先に必要な構造体配置の検査が失敗した場合は、その診断を返す。
    pub(super) fn prepare_expanded_routine_ports(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring<'p, 'a>,
        layouts: Option<StructureLayouts<'p, 'a>>, selected: &[ResolvedTemplateCall<'_, 'p, 'a>],
    ) -> (result: Result<PreparedBitFuncPorts<'p, 'a>, BitFuncError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))),
            layouts matches Some(table) ==> self.structure_types_match(limit, Ok(table)),
        ensures self.expanded_routine_ports_result(file, entry, limit, wiring, layouts, selected@, result),
    {
        reveal(UseAliases::routine_ports_result);
        let mut ports = match self.prepare_routine_ports(file, entry, limit, wiring, layouts) {
            Ok(ports) => ports,
            Err(error) => return Err(error),
        };
        if ports.layouts.is_some() {
            return Ok(ports);
        }
        let ghost original = ports;
        let table = match self.prepare_called_structure_layout(selected, limit, ports.layouts) {
            Ok(table) => table,
            Err(error) => {
                assert(exists|before: PreparedBitFuncPorts| #[trigger] self.routine_ports_result(file, entry, limit, wiring,
                    layouts, Ok(before)) && self.called_structure_layout_result(selected@, limit, before.layouts, Err(error)));
                return Err(BitFuncError::PortLayout(error));
            },
        };
        ports.layouts = table;
        proof {

            let new_table = match &ports.layouts { Some(table) => Some(table), None => None };
            self.widths_without_structure_layout(wiring.drivers.signature.inputs@, original.inputs@, new_table);
            self.widths_without_structure_layout(wiring.drivers.signature.outputs@, original.outputs@, new_table);
        }
        Ok(ports)
    }

    proof fn widths_without_structure_layout(
        &self, ports: Seq<TypedPort>, widths: Seq<u64>, layouts: Option<&StructureLayouts>,
    )
        requires self.port_widths_match(ports, widths, None),
        ensures self.port_widths_match(ports, widths, layouts),
    {
        assert forall|i: int| 0 <= i < widths.len() implies
            self.port_width_matches(ports[i].ty, #[trigger] widths[i], layouts) by {
            assert(self.port_width_matches(ports[i].ty, widths[i], None));
        };
    }

    spec fn port_width_matches(
        &self, ty: ResolvedPortType, width: u64, layouts: Option<&StructureLayouts>,
    ) -> bool {
        &&& width > 0
        &&& match ty {
            ResolvedPortType::Bits(bits) => width == bits,
            ResolvedPortType::Struct { .. } => layouts matches Some(table)
                && self.layout_port_width_matches(table, ty, width as int),
        }
    }

    /// 比較した二つのポート型が、同じ配置表で同じ表現幅を持つことを示す。
    proof fn equivalent_port_widths(
        &self, layouts: Option<&StructureLayouts>, left: ResolvedPortType, left_width: u64,
        right: ResolvedPortType, right_width: u64,
    )
        requires
            self.can_resolve(),
            self.port_width_matches(left, left_width, layouts),
            self.port_width_matches(right, right_width, layouts),
            crate::project::port_types_equal(left, right),
        ensures left_width == right_width,
    {
        if let ResolvedPortType::Struct { .. } = left {
            let table = layouts->Some_0;
            self.layout_port_is_declared(table, left, left_width as int);
            self.layout_port_is_declared(table, right, right_width as int);
            self.equivalent_declared_port_types(left, right);
            self.layout_port_widths_agree(table, left, left_width as int, right_width as int);
        }
    }

    spec fn port_widths_match(&self, ports: Seq<TypedPort>, widths: Seq<u64>, layouts: Option<&StructureLayouts>) -> bool {
        &&& widths.len() == ports.len()
        &&& forall|i: int| 0 <= i < widths.len() ==> self.port_width_matches(ports[i].ty, #[trigger] widths[i], layouts)
    }

    fn collect_port_widths(
        &self, ports: &[TypedPort<'p, 'a>], layouts: Option<&StructureLayouts<'p, 'a>>, limit: u64,
    ) -> (widths: Vec<u64>)
        requires
            self.can_resolve(),
            supported_ports(ports@),
            forall|i: int| 0 <= i < ports@.len() ==> self.declared_port_type((#[trigger] ports@[i]).ty),
            has_structure_port(ports@) ==> layouts.is_some(),
            layouts matches Some(table) ==> self.structure_types_match(limit, Ok(*table)),
        ensures self.port_widths_match(ports@, widths@, layouts),
    {
        let mut widths = Vec::new();
        let mut i = 0;
        while i < ports.len()
            invariant
                self.can_resolve(),
                supported_ports(ports@),
                forall|j: int| 0 <= j < ports@.len() ==> self.declared_port_type((#[trigger] ports@[j]).ty),
                has_structure_port(ports@) ==> layouts.is_some(),
                layouts matches Some(table) ==> self.structure_types_match(limit, Ok(*table)),
                i == widths@.len() <= ports@.len(),
                forall|j: int| 0 <= j < i ==> self.port_width_matches(ports@[j].ty, #[trigger] widths@[j], layouts),
            decreases ports@.len() - i,
        {
            let ty = ports[i].ty;
            let width = match ty {
                ResolvedPortType::Bits(width) => width,
                ResolvedPortType::Struct { source, form } => {
                    assert(has_structure_port(ports@));
                    let Some(table) = layouts else { unreachable!() };
                    self.structure_port_width(source, form, table, limit)
                },
            };
            let ghost prior = widths@;
            widths.push(width);
            assert forall|j: int| 0 <= j < widths@.len() implies
                self.port_width_matches(ports@[j].ty, #[trigger] widths@[j], layouts) by {
                if j < i { assert(widths@[j] == prior[j]); }
            };
            i += 1;
        }
        widths
    }

    spec fn projection_port_widths_match(&self, scope: &FuncProjection) -> bool {
        let signature = &scope.wiring.drivers.signature;
        &&& self.port_widths_match(signature.inputs@, scope.inputs@, scope.layouts)
        &&& self.port_widths_match(signature.outputs@, scope.outputs@, scope.layouts)
        &&& self.structure_layout_for_ports(scope.limit, scope.layouts)
    }

    spec fn projection_structures_match(&self, scope: &FuncProjection) -> bool {
        &&& scope.types@.len() == scope.wiring.drivers.definitions@.len()
        &&& structure_projections_in_order(scope.structures@, scope.types@.len() as int, scope.inputs@.len() as int)
        &&& scope.layouts.is_none() ==> scope.structures@.len() == 0
        &&& scope.layouts matches Some(table) ==> forall|j: int| 0 <= j < scope.structures@.len() ==>
            structure_projection_matches(self, scope.file, scope.entry, scope.limit, scope.wiring,
                *table, scope.types@, #[trigger] scope.structures@[j])
    }

    spec fn structure_layout_for_ports(&self, limit: u64, layouts: Option<&StructureLayouts>) -> bool {
        layouts matches Some(table) ==> self.structure_types_match(limit, Ok(*table))
    }
    spec fn projection_context(&self, scope: &FuncProjection) -> bool {
        let project = self.targets.project_model();
        &&& self.can_resolve()
        &&& self.func_wiring_evidence(scope.file, scope.entry, scope.limit, Ok(FuncWiringResult::Checked(*scope.wiring)))
        &&& scope.file < project.sources_model().len() && scope.file < project.circuits_model().len()
        &&& *scope.source == project.sources_model()[scope.file as int]
        &&& *scope.parsed == project.circuits_model()[scope.file as int]
        &&& parsed_circuit_matches(*scope.source, *scope.parsed)
        &&& scope.entry < scope.parsed.syntax.entries@.len()
        &&& expected_output_context(scope.source, scope.parsed, scope.entry as int, scope.wiring.drivers)
        &&& checked_ports_and_output_bounds(scope.parsed.syntax.forms@, scope.wiring.drivers)
    }

    spec fn bit_rhs_from_source(&self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, i: int,
        rhs: BitFuncRhs, operands: Seq<(SingleBitOperand, u64)>) -> bool {
        let parsed = scope.parsed;
        let forms = parsed.syntax.forms@;
        let definition = scope.wiring.drivers.definitions@[i].definition;
        let row = parsed.definitions@[definition as int];
        let root = row.expression.start as int;
        let entry = scope.entry;
        let local = (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let signature = &scope.wiring.drivers.signature;
        if exists|j: int| 0 <= j < scope.structures@.len() && (#[trigger] scope.structures@[j]).target == i {
            exists|j: int| 0 <= j < scope.structures@.len() && {
            let projection = #[trigger] scope.structures@[j];
            &&& projection.target == i
            &&& bit_driver_width(scope.inputs@, prior, projection.input) matches Some(width)
            &&& width == projection.input_width
            &&& structure_rhs_matches(rhs, projection)
            }
        } else { match rhs {
            BitFuncRhs::Driver(driver) =>
                operand_matches(scope.source, parsed, entry, definition, root, scope.wiring, i, SingleBitOperand::Driver(driver)),
            BitFuncRhs::Constant(bit) =>
                operand_matches(scope.source, parsed, entry, definition, root, scope.wiring, i, SingleBitOperand::Constant(bit)),
            BitFuncRhs::Nor { left, right } => {
                &&& forms[root] is List && row.expression.end == root + 4
                &&& operand_matches(scope.source, parsed, entry, definition, root + 2, scope.wiring, i, left)
                &&& operand_matches(scope.source, parsed, entry, definition, root + 3, scope.wiring, i, right)
                &&& exists|call: TypedFuncCall| #[trigger] self.func_call_signature_evidence(
                    scope.file, entry, local, 0, scope.limit, Ok(Some(call)),
                ) && call.call.call.form == root && call.call.call.arguments == 2 && call.call.target is Nor
            },
            BitFuncRhs::Selection { input, selection } => (exists|shape: BitSelectionShape|
                #[trigger] named_selection_matches(scope.source.text, forms, root, shape)
                && (bit_driver_width(scope.inputs@, prior, input) matches Some(width)
                && operand_matches(scope.source, parsed, entry, definition, shape.input.start as int, scope.wiring, i,
                    SingleBitOperand::Driver(input))
                && selection_arguments_match(scope.source, forms, &shape, width, &driver_width_origin(signature, prior, input),
                    Ok(selection)))) || Self::nested_selection_projection(scope, prior, i, input, selection),
            BitFuncRhs::Concat => exists|concat: ConcatProjection|
                #[trigger] concat_projection_matches(scope.file, entry, scope.limit, scope.source, parsed, scope.wiring,
                    scope.types@, concat)
                && concat.target == i && concat.operands@ == operands,
            BitFuncRhs::BitVector => bit_vector_form(forms[root]),
            BitFuncRhs::CallOutput { .. } => false,
        } }
    }

    #[verifier::opaque]
    spec fn nested_selection_projection(
        scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, i: int,
        input: OutputDriver, selection: CheckedBitSelection,
    ) -> bool {
        let parsed = scope.parsed;
        let definition = scope.wiring.drivers.definitions@[i].definition;
        let root = parsed.definitions@[definition as int].expression.start;
        let forms = parsed.syntax.forms@;
        exists|steps: Seq<BitSelectionShape>, leaf: usize|
            #[trigger] nested_named_selection_matches(scope.source.text, forms, root, steps, leaf)
            && operand_matches(scope.source, parsed, scope.entry, definition, leaf as int, scope.wiring, i,
                SingleBitOperand::Driver(input))
            && (bit_driver_width(scope.inputs@, prior, input) matches Some(width)
                && selection_chain_arguments_match(scope.source, forms, steps, width,
                    driver_width_origin(&scope.wiring.drivers.signature, prior, input), Ok(selection)))
    }

    spec fn bit_definition_from_source(
        &self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, i: int, checked: CheckedBitDefinition,
    ) -> bool {
        let parsed = scope.parsed;
        let row = parsed.definitions@[scope.wiring.drivers.definitions@[i].definition as int];
        let forms = parsed.syntax.forms@;
        let (first, end) = definition_target_range(forms, row);
        &&& end - first == 1
        &&& is_form_location(scope.source, forms[row.expression.start as int], checked.expression)
        &&& self.bit_rhs_from_source(scope, prior, i, checked.rhs, checked.operands@)
        &&& bit_definition_matches(scope.inputs@, prior, checked)
        &&& checked.rhs is BitVector ==> (scope.types@[i] matches Some(ty) && ty.ty == ResolvedPortType::Bits(checked.width))
    }

    #[verifier::opaque]
    spec fn definition_prefix(&self, scope: &FuncProjection, definitions: Seq<CheckedBitDefinition>) -> bool {
        &&& definitions.len() <= scope.wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < definitions.len() ==>
            self.bit_definition_from_source(scope, definitions.take(i), i, #[trigger] definitions[i])
    }

    proof fn extend_definition_prefix(
        &self, scope: &FuncProjection, previous: Seq<CheckedBitDefinition>, checked: CheckedBitDefinition,
    )
        requires
            self.definition_prefix(scope, previous),
            previous.len() < scope.wiring.drivers.definitions@.len(),
            self.bit_definition_from_source(scope, previous, previous.len() as int, checked),
        ensures self.definition_prefix(scope, previous.push(checked)),
    {
        reveal(UseAliases::definition_prefix);
        let next = previous.push(checked);
        assert forall|j: int| 0 <= j < next.len() implies
            self.bit_definition_from_source(scope, next.take(j), j, #[trigger] next[j]) by {
            if j < previous.len() {
                assert(next[j] == previous[j]);
                assert(next.take(j) =~= previous.take(j));
            } else {
                assert(next.take(j) =~= previous);
            }
        };
    }

    /// 入出力ポート、定義順、右辺の各参照が、検査した元の関数と対応することを表す。
    pub closed spec fn checked_bit_func_matches(&self, file: usize, entry: usize, limit: u64, checked: &CheckedBitFunc) -> bool {
        exists|typed: FuncSignalTypes, layouts: Option<&StructureLayouts>, structures: Vec<StructureProjection>|
            #![trigger self.func_signal_types_evidence(file, entry, limit, Ok(typed)), self.structure_layout_for_ports(limit, layouts), structures@]
            self.checked_bit_func_projection(file, entry, limit, checked, typed, layouts, structures)
    }

    pub(super) closed spec fn template_port_widths_match(
        &self, signature: TypedRoutineSignature, limit: u64, inputs: Seq<u64>, outputs: Seq<u64>,
        layouts: Option<StructureLayouts>,
    ) -> bool {
        let table = match &layouts { Some(table) => Some(table), None => None };
        &&& self.structure_layout_for_ports(limit, table)
        &&& self.port_widths_match(signature.inputs@, inputs, table)
        &&& self.port_widths_match(signature.outputs@, outputs, table)
    }

    pub(super) proof fn template_port_counts(
        &self, signature: TypedRoutineSignature, limit: u64, inputs: Seq<u64>, outputs: Seq<u64>,
        layouts: Option<StructureLayouts>,
    )
        requires self.template_port_widths_match(signature, limit, inputs, outputs, layouts),
        ensures inputs.len() == signature.inputs@.len(), outputs.len() == signature.outputs@.len(),
    {
        reveal(UseAliases::template_port_widths_match);
    }

    /// 呼び出し先のポート幅を、呼び出し元で使う検査済みの配置表へ引き継ぐ。
    proof fn template_widths_in_caller_layout(
        &self, signature: TypedRoutineSignature, limit: u64, inputs: Seq<u64>, outputs: Seq<u64>,
        from: Option<StructureLayouts>, to: Option<&StructureLayouts>,
    )
        requires
            self.can_resolve(),
            self.template_port_widths_match(signature, limit, inputs, outputs, from),
            to matches Some(table) ==> self.structure_types_match(limit, Ok(*table)),
            to.is_none() ==> !has_structure_port(signature.inputs@) && !has_structure_port(signature.outputs@),
        ensures
            self.port_widths_match(signature.inputs@, inputs, to),
            self.port_widths_match(signature.outputs@, outputs, to),
    {
        let source = match &from { Some(table) => Some(table), None => None };
        self.port_widths_in_caller_layout(signature.inputs@, inputs, limit, source, to);
        self.port_widths_in_caller_layout(signature.outputs@, outputs, limit, source, to);
    }

    proof fn port_widths_in_caller_layout(
        &self, ports: Seq<TypedPort>, widths: Seq<u64>, limit: u64,
        from: Option<&StructureLayouts>, to: Option<&StructureLayouts>,
    )
        requires
            self.can_resolve(),
            self.port_widths_match(ports, widths, from),
            self.structure_layout_for_ports(limit, from),
            self.structure_layout_for_ports(limit, to),
            to.is_none() ==> !has_structure_port(ports),
        ensures self.port_widths_match(ports, widths, to),
    {
        assert forall|i: int| 0 <= i < widths.len() implies
            self.port_width_matches(ports[i].ty, #[trigger] widths[i], to) by {
            let ty = ports[i].ty;
            assert(self.port_width_matches(ty, widths[i], from));
            if ty is Struct {
                let origin = from->Some_0;
                let table = to->Some_0;
                self.layout_port_width_transfers(limit, origin, table, ty, widths[i] as int);
            }
        };
    }

    /// 単独関数で検査したポート幅を、同じ宣言と構造体配置に結び付ける。
    pub(super) proof fn standalone_template_ports(
        &self, file: usize, entry: usize, limit: u64, checked: &CheckedBitFunc,
    ) -> (layouts: Option<StructureLayouts<'p, 'a>>)
        requires
            self.can_resolve(),
            self.checked_bit_func_matches(file, entry, limit, checked),
        ensures
            self.typed_signature_evidence(file, entry, limit, Ok(Some(checked.signature))),
            self.template_port_widths_match(checked.signature, limit, checked.input_widths@, checked.output_widths@, layouts),
    {
        reveal(UseAliases::checked_bit_func_matches);
        let (typed, table, structures) = choose|typed: FuncSignalTypes, table: Option<&StructureLayouts>, structures: Vec<StructureProjection>|
            #![trigger self.func_signal_types_evidence(file, entry, limit, Ok(typed)), self.structure_layout_for_ports(limit, table), structures@]
            self.checked_bit_func_projection(file, entry, limit, checked, typed, table, structures);
        let wiring = typed.literals.wiring->Checked_0;
        self.checked_types_keep_wiring(file, entry, limit, typed, wiring);
        self.checked_wiring_is_func(file, entry, limit, wiring);
        let model = match table { Some(table) => Some(*table), None => None };
        assert(self.template_port_widths_match(checked.signature, limit, checked.input_widths@, checked.output_widths@, model)) by {
            reveal(UseAliases::template_port_widths_match);
        };
        model
    }

    spec fn checked_bit_func_projection(
        &self, file: usize, entry: usize, limit: u64, checked: &CheckedBitFunc,
        typed: FuncSignalTypes, layouts: Option<&StructureLayouts>, structures: Vec<StructureProjection>,
    ) -> bool {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        &&& self.func_signal_types_evidence(file, entry, limit, Ok(typed))
        &&& self.structure_layout_for_ports(limit, layouts)
        &&& typed.literals.wiring matches FuncWiringResult::Checked(wiring) && {
            let scope = FuncProjection { file, entry, limit, source, parsed, wiring: &wiring,
                inputs: &checked.input_widths, outputs: &checked.output_widths, layouts, types: &typed.types, structures: &structures };
            &&& self.projection_context(&scope)
            &&& self.projection_port_widths_match(&scope)
            &&& self.projection_structures_match(&scope)
            &&& self.func_structure_projections_complete(file, entry, limit, typed, &wiring, structures@)
            &&& checked.signature == wiring.drivers.signature
            &&& checked.definitions@.len() == wiring.drivers.definitions@.len()
            &&& self.definition_prefix(&scope, checked.definitions@)
            &&& self.definition_widths_match(&scope, checked.definitions@)
            &&& checked.output_drivers@ == wiring.drivers.outputs@
        }
    }

    spec fn definition_error(
        &self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, error: BitFuncError,
    ) -> bool {
        let parsed = scope.parsed;
        let entry = scope.entry;
        let wiring = scope.wiring;
        let signature = &wiring.drivers.signature;
        let source = scope.source;
        let forms = parsed.syntax.forms@;
        let i = prior.len() as int;
        let definition = wiring.drivers.definitions@[i].definition;
        let row = parsed.definitions@[definition as int];
        let root = row.expression.start as int;
        let (first, end) = definition_target_range(forms, row);
        let local = (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;

        let call_candidate = row.expression.end == root + 4 && forms[root] is List
            && (forall|shape: BitSelectionShape| !#[trigger] named_selection_matches(source.text, forms, root, shape))
            && (forall|steps: Seq<BitSelectionShape>, leaf: usize|
                !#[trigger] nested_named_selection_matches(source.text, forms, root as usize, steps, leaf));
        &&& i < wiring.drivers.definitions@.len()
        &&& (!(error matches BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, _))
            ==> forall|j: int| 0 <= j < scope.structures@.len() ==> (#[trigger] scope.structures@[j]).target != i)
        &&& (!(error matches BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, _))
            ==> end - first == 1 && no_operand(source, parsed, entry, definition, root, wiring, i))
        &&& (!(error matches BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, _))
            ==> !concat_type_ready(scope, i))
        &&& (!(error matches BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, _))
            ==> !bit_vector_form(forms[root]))
        &&& (!(error matches BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, _))
            ==> forall|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
                !#[trigger] field_selection_shape_matches(source.text, forms, root as usize, steps, at, shape))
        &&& match error {
            BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, site) =>
                end - first != 1 && is_form_location(source, forms[root], site),
            BitFuncError::Unsupported(UnsupportedBitFunc::Expression, site) => {
                if exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root, shape) {
                    exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root, shape)
                        && no_operand(source, parsed, entry, definition, shape.input.start as int, wiring, i)
                        && is_form_location(source, forms[root], site)
                } else {
                    (forall|steps: Seq<BitSelectionShape>, leaf: usize|
                        !#[trigger] nested_named_selection_matches(source.text, forms, root as usize, steps, leaf))
                    && self.unsupported_expression(scope.file, entry, scope.limit, wiring, i, site)
                }
            },
            BitFuncError::Call(position, error) => call_candidate && position == local
                && self.func_call_signature_evidence(scope.file, entry, position, 0, scope.limit, Err(error)),
            BitFuncError::Selection(error) => exists|shape: BitSelectionShape, driver: OutputDriver|
                #![trigger named_selection_matches(source.text, forms, root, shape),
                    bit_driver_width(scope.inputs@, prior, driver)]
                named_selection_matches(source.text, forms, root, shape)
                && operand_matches(source, parsed, entry, definition, shape.input.start as int, wiring, i, SingleBitOperand::Driver(driver))
                && (bit_driver_width(scope.inputs@, prior, driver) matches Some(width)
                    && selection_arguments_match(source, forms, &shape, width, &driver_width_origin(signature, prior, driver), Err(error))),
            BitFuncError::NorInputWidth { argument, actual } => call_candidate && actual != 1
                && (exists|left: SingleBitOperand, right: SingleBitOperand| #![trigger
                    operand_matches(source, parsed, entry, definition, root + 2, wiring, i, left),
                    operand_matches(source, parsed, entry, definition, root + 3, wiring, i, right)]
                    operand_matches(source, parsed, entry, definition, root + 2, wiring, i, left)
                    && operand_matches(source, parsed, entry, definition, root + 3, wiring, i, right)
                    && ((left matches SingleBitOperand::Driver(driver)
                            && bit_driver_width(scope.inputs@, prior, driver) == Some(actual)
                            && is_form_location(source, forms[root + 2], argument))
                        || (nor_operand_matches(scope.inputs@, prior, left)
                            && (right matches SingleBitOperand::Driver(driver)
                                && bit_driver_width(scope.inputs@, prior, driver) == Some(actual)
                                && is_form_location(source, forms[root + 3], argument)))))
                && (exists|call: TypedFuncCall| #[trigger] self.func_call_signature_evidence(
                    scope.file, entry, local, 0, scope.limit, Ok(Some(call)),
                ) && call.call.call.form == root && call.call.call.arguments == 2 && call.call.target is Nor),
            _ => false,
        }
    }

    spec fn projection_failure(&self, scope: &FuncProjection, error: BitFuncError) -> bool {
        let signature = &scope.wiring.drivers.signature;
        match error {
            BitFuncError::Unsupported(UnsupportedBitFunc::OutputCount | UnsupportedBitFunc::PortType, _)
            | BitFuncError::PortLayout(_) =>
                self.port_preparation_error(scope.source, scope.parsed, scope.entry, scope.limit, signature, error),
            _ => {
                &&& signature.outputs@.len() > 0
                &&& supported_ports(signature.outputs@) && supported_ports(signature.inputs@)
                &&& self.projection_port_widths_match(scope)
                &&& self.projection_structures_match(scope)
                &&& exists|prior: Seq<CheckedBitDefinition>| #[trigger] self.definition_prefix(scope, prior) && {
                    match error {
                        BitFuncError::OutputWidth { .. } =>
                            prior.len() == scope.wiring.drivers.definitions@.len()
                            && output_width_failure(signature, scope.inputs@, scope.outputs@, prior, scope.wiring.drivers.outputs@, error),
                        _ => self.definition_error(scope, prior, error),
                    }
                }
            },
        }
    }

    /// 診断が、型・結線検査または元ソースの対応範囲、右辺、出力型に根拠を持つことを表す。
    pub closed spec fn checked_bit_func_error(
        &self, file: usize, entry: usize, limit: u64, error: BitFuncError,
    ) -> bool {
        if let BitFuncError::Check(error) = error {
            self.func_signal_types_evidence(file, entry, limit, Err(error))
        } else {
            exists|typed: FuncSignalTypes|
                #[trigger] self.func_signal_types_evidence(file, entry, limit, Ok(typed))
                && match (error, typed.literals.wiring) {
                    (BitFuncError::NotFunc, FuncWiringResult::NotFunc) => true,
                    (BitFuncError::NeedsExpansion(site), FuncWiringResult::NeedsExpansion(expansion)) => site == expansion,
                    (_, FuncWiringResult::Checked(wiring)) =>
                        exists|scope: FuncProjection| #[trigger] self.projection_failure(&scope, error)
                            && scope.file == file && scope.entry == entry && scope.limit == limit
                            && *scope.wiring == wiring && scope.types@ == typed.types@ && self.projection_context(&scope),
                    _ => false,
                }
        }
    }

    proof fn projected_error(
        &self, scope: &FuncProjection, typed: FuncSignalTypes, error: BitFuncError,
    )
        requires
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            typed.types@ == scope.types@,
            self.projection_context(scope),
            self.projection_failure(scope, error),
        ensures self.checked_bit_func_error(scope.file, scope.entry, scope.limit, error),
    {
    }

    proof fn constant_definition_type(
        &self, scope: &FuncProjection, typed: FuncSignalTypes, prior: Seq<CheckedBitDefinition>,
        index: int, checked: CheckedBitDefinition, bit: bool,
    )
        requires
            self.projection_context(scope),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            0 <= index < scope.wiring.drivers.definitions@.len(),
            index < typed.types@.len(),
            !(exists|j: int| 0 <= j < scope.structures@.len() && (#[trigger] scope.structures@[j]).target == index),
            self.bit_definition_from_source(scope, prior, index, checked),
            checked.rhs == BitFuncRhs::Constant(bit),
        ensures typed.types@[index] matches Some(ty) && ty.ty == ResolvedPortType::Bits(checked.width),
    {
        let wiring = scope.wiring;
        let driver = wiring.drivers.definitions@[index];
        self.checked_wiring_is_func(scope.file, scope.entry, scope.limit, *wiring);
        assert(indexed_driver_site(scope.source, scope.parsed, scope.entry as int, driver));
        let row = scope.parsed.definitions@[driver.definition as int];
        constant_operand_literal(scope.source, scope.parsed, scope.entry, driver.definition,
            row.expression.start as int, wiring, index, bit);
        self.checked_types_keep_wiring(scope.file, scope.entry, scope.limit, typed, *wiring);
        self.fixed_bit_definition_has_unit_width(scope.file, scope.entry, scope.limit,
            &typed.literals, wiring, index, bit);
        self.checked_literal_type(scope.file, scope.entry, scope.limit, typed, *wiring, index, 1);
    }

    proof fn bare_definition_type(
        &self, scope: &FuncProjection, typed: FuncSignalTypes, prior: Seq<CheckedBitDefinition>,
        index: int, checked: CheckedBitDefinition, driver: OutputDriver,
    )
        requires
            self.projection_context(scope),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            0 <= index < scope.wiring.drivers.definitions@.len(),
            index < typed.types@.len(),
            !(exists|j: int| 0 <= j < scope.structures@.len() && (#[trigger] scope.structures@[j]).target == index),
            self.bit_definition_from_source(scope, prior, index, checked),
            checked.rhs == BitFuncRhs::Driver(driver),
        ensures
            typed.types@[index] == signal_type_at(scope.wiring, typed.types@.take(index), driver),
            bit_driver_width(scope.inputs@, prior, driver) == Some(checked.width),
    {
        let wiring = scope.wiring;
        let site = wiring.drivers.definitions@[index];
        self.checked_wiring_is_func(scope.file, scope.entry, scope.limit, *wiring);
        assert(indexed_driver_site(scope.source, scope.parsed, scope.entry as int, site));
        bare_rhs_driver_matches(scope.source, scope.parsed, scope.entry, site.definition, wiring, index, driver);
        self.checked_bare_rhs_inherits(scope.file, scope.entry, scope.limit, typed, *wiring, index);
    }

    proof fn selection_definition_type(
        &self, scope: &FuncProjection, typed: FuncSignalTypes, prior: Seq<CheckedBitDefinition>,
        index: int, checked: CheckedBitDefinition, driver: OutputDriver, selection: CheckedBitSelection,
    )
        requires
            self.projection_context(scope),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            0 <= index < scope.wiring.drivers.definitions@.len(),
            index < typed.types@.len(),
            !(exists|j: int| 0 <= j < scope.structures@.len() && (#[trigger] scope.structures@[j]).target == index),
            self.bit_definition_from_source(scope, prior, index, checked),
            checked.rhs == (BitFuncRhs::Selection { input: driver, selection }),
            signal_type_at(scope.wiring, typed.types@.take(index), driver).is_some(),
        ensures typed.types@[index] matches Some(ty) && ty.ty == ResolvedPortType::Bits(checked.width),
    {
        let wiring = scope.wiring;
        let parsed = scope.parsed;
        let source = scope.source;
        let forms = parsed.syntax.forms@;
        let site = wiring.drivers.definitions@[index];
        let row = parsed.definitions@[site.definition as int];
        let width = bit_driver_width(scope.inputs@, prior, driver)->Some_0;
        let origin = driver_width_origin(&wiring.drivers.signature, prior, driver);
        self.checked_wiring_is_func(scope.file, scope.entry, scope.limit, *wiring);
        assert(indexed_driver_site(source, parsed, scope.entry as int, site));
        let input = signal_type_at(wiring, typed.types@.take(index), driver)->Some_0;
        if Self::nested_selection_projection(scope, prior, index, driver, selection) {
            reveal(UseAliases::nested_selection_projection);
            let (steps, leaf) = choose|steps: Seq<BitSelectionShape>, leaf: usize|
                #[trigger] nested_named_selection_matches(source.text, forms, row.expression.start, steps, leaf)
                && operand_matches(source, parsed, scope.entry, site.definition, leaf as int, wiring,
                    index, SingleBitOperand::Driver(driver))
                && selection_chain_arguments_match(source, forms, steps, width, origin, Ok(selection));
            nested_selection_rhs_driver_matches(source, parsed, scope.entry, site.definition, wiring, index, steps, leaf, driver);
            let (inferred_width, inferred_origin, inferred) = self.checked_nested_selection_type(
                scope.file, scope.entry, scope.limit, typed, *wiring, index, steps, leaf,
            );
            successful_selection_chain_counts_agree(source, forms, steps, inferred_width, inferred_origin, inferred,
                width, origin, selection);
        } else {
            let shape = choose|shape: BitSelectionShape|
                #[trigger] named_selection_matches(source.text, forms, row.expression.start as int, shape)
                && operand_matches(source, parsed, scope.entry, site.definition, shape.input.start as int, wiring,
                    index, SingleBitOperand::Driver(driver))
                && selection_arguments_match(source, forms, &shape, width, &origin, Ok(selection));
            selection_rhs_driver_matches(source, parsed, scope.entry, site.definition, wiring, index, shape, driver);
            self.checked_selection_type(scope.file, scope.entry, scope.limit, typed, *wiring,
                index, shape, input, width, origin, selection);
        }
    }

    proof fn nor_definition_type(
        &self, scope: &FuncProjection, typed: FuncSignalTypes, prior: Seq<CheckedBitDefinition>,
        index: int, checked: CheckedBitDefinition,
    )
        requires
            self.projection_context(scope),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            0 <= index < scope.wiring.drivers.definitions@.len(),
            index < typed.types@.len(),
            !(exists|j: int| 0 <= j < scope.structures@.len() && (#[trigger] scope.structures@[j]).target == index),
            self.bit_definition_from_source(scope, prior, index, checked),
            checked.rhs is Nor,
        ensures typed.types@[index] matches Some(ty) && ty.ty == ResolvedPortType::Bits(checked.width),
    {
        let wiring = scope.wiring;
        let parsed = scope.parsed;
        let driver = wiring.drivers.definitions@[index];
        let row = parsed.definitions@[driver.definition as int];
        let local = (driver.definition - parsed.entry_ranges@[scope.entry as int].definitions.start) as usize;
        self.checked_wiring_is_func(scope.file, scope.entry, scope.limit, *wiring);
        assert(indexed_driver_site(scope.source, parsed, scope.entry as int, driver));
        let builtin = choose|call: TypedFuncCall| #[trigger] self.func_call_signature_evidence(
            scope.file, scope.entry, local, 0, scope.limit, Ok(Some(call)),
        ) && call.call.call.form == row.expression.start && call.call.call.arguments == 2 && call.call.target is Nor;
        self.checked_nor_type(scope.file, scope.entry, scope.limit, typed, *wiring, index, builtin);
    }

    #[verifier::opaque]
    spec fn definition_widths_match(&self, scope: &FuncProjection, definitions: Seq<CheckedBitDefinition>) -> bool {
        &&& definitions.len() <= scope.types@.len()
        &&& forall|i: int| 0 <= i < definitions.len() ==> {
            let definition = #[trigger] definitions[i];
            scope.types@[i] matches Some(ty)
                && self.port_width_matches(ty.ty, definition.width, scope.layouts)
        }
    }

    proof fn driver_type_matches_width(
        &self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, driver: OutputDriver, width: u64,
    )
        requires
            self.projection_port_widths_match(scope),
            self.definition_widths_match(scope, prior),
            bit_driver_width(scope.inputs@, prior, driver) == Some(width),
        ensures signal_type_at(scope.wiring, scope.types@.take(prior.len() as int), driver) matches Some(ty)
            && self.port_width_matches(ty.ty, width, scope.layouts),
    {
        match driver {
            OutputDriver::Input(port) => {
                assert(self.port_width_matches(scope.wiring.drivers.signature.inputs@[port as int].ty,
                    scope.inputs@[port as int], scope.layouts));
            },
            OutputDriver::Definition(index) => {
                reveal(UseAliases::definition_widths_match);
                assert(prior[index as int].width == width);
            },
        }
    }

    /// 次の右辺を追加しても、定義ごとに型の表現幅と変換後の幅が一致することを示す。
    proof fn extend_definition_widths(
        &self, scope: &FuncProjection, typed: FuncSignalTypes, prior: Seq<CheckedBitDefinition>,
        checked: CheckedBitDefinition, projection: Option<usize>,
    )
        requires
            self.projection_context(scope),
            self.projection_port_widths_match(scope),
            self.projection_structures_match(scope),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.types@ == scope.types@,
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            prior.len() < scope.wiring.drivers.definitions@.len(),
            self.definition_widths_match(scope, prior),
            self.bit_definition_from_source(scope, prior, prior.len() as int, checked),
            projection matches Some(at) ==> at < scope.structures@.len() && scope.structures@[at as int].target == prior.len(),
            projection.is_none() ==> forall|j: int| 0 <= j < scope.structures@.len()
                ==> (#[trigger] scope.structures@[j]).target != prior.len(),
        ensures self.definition_widths_match(scope, prior.push(checked)),
    {
        let index = prior.len() as int;
        if let Some(at) = projection {
            let data = scope.structures@[at as int];
            let table = scope.layouts->Some_0;
            let j = choose|j: int| 0 <= j < scope.structures@.len() && {
                let projected = #[trigger] scope.structures@[j];
                &&& projected.target == index
                &&& bit_driver_width(scope.inputs@, prior, projected.input) == Some(projected.input_width)
                &&& structure_rhs_matches(checked.rhs, projected)
            };
            assert(j == at);
            assert(structure_projection_matches(self, scope.file, scope.entry, scope.limit, scope.wiring,
                *table, scope.types@, data));
            if let Some(outer) = data.selection {
                self.field_projection_evidence(scope.file, scope.entry, scope.limit, scope.wiring, *table, scope.types@, data);
                assert(checked.width == outer.count);
            } else {
                self.structure_projection_widths(scope.file, scope.entry, scope.limit, scope.wiring, *table, scope.types@, data);
                assert(checked.width == data.operation.range.end - data.operation.range.start);
                if let ResolvedPortType::Bits(width) = scope.types@[index]->Some_0.ty {
                    self.layout_bits_port_width(table, width, checked.width as int);
                }
            }
        } else {
            assert(!(exists|j: int| 0 <= j < scope.structures@.len() && (#[trigger] scope.structures@[j]).target == index));
            match checked.rhs {
                BitFuncRhs::Constant(bit) => self.constant_definition_type(scope, typed, prior, index, checked, bit),
                BitFuncRhs::Nor { .. } => self.nor_definition_type(scope, typed, prior, index, checked),
                BitFuncRhs::Driver(driver) => {
                    self.bare_definition_type(scope, typed, prior, index, checked, driver);
                    self.driver_type_matches_width(scope, prior, driver, checked.width);
                },
                BitFuncRhs::Selection { input, selection } => {
                    self.driver_type_matches_width(scope, prior, input, bit_driver_width(scope.inputs@, prior, input)->Some_0);
                    self.selection_definition_type(scope, typed, prior, index, checked, input, selection);
                },
                BitFuncRhs::Concat => {
                    let row = choose|concat: ConcatProjection|
                        #[trigger] concat_projection_matches(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                            scope.wiring, scope.types@, concat)
                        && concat.target == index && concat.operands@ == checked.operands@;
                    let bits = concat_projection_evidence(scope.file, scope.entry, scope.limit, scope.source, scope.parsed,
                        scope.wiring, scope.types@, row);
                    assert(bits == checked.width);
                },
                BitFuncRhs::BitVector => {},
                BitFuncRhs::CallOutput { .. } => { assert(false); },
            }
        }
        assert(scope.types@[index] matches Some(ty) && self.port_width_matches(ty.ty, checked.width, scope.layouts));
        self.push_definition_width(scope, prior, checked);
    }

    proof fn push_definition_width(
        &self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, checked: CheckedBitDefinition,
    )
        requires
            self.definition_widths_match(scope, prior),
            prior.len() < scope.types@.len(),
            scope.types@[prior.len() as int] matches Some(ty) && self.port_width_matches(ty.ty, checked.width, scope.layouts),
        ensures self.definition_widths_match(scope, prior.push(checked)),
    {
        reveal(UseAliases::definition_widths_match);
        let next = prior.push(checked);
        assert forall|j: int| 0 <= j < next.len() implies scope.types@[j] matches Some(ty)
            && self.port_width_matches(ty.ty, (#[trigger] next[j]).width, scope.layouts) by {
            if j < prior.len() { assert(next[j] == prior[j]); }
        };
    }

    #[verifier::opaque]
    spec fn call_definition_widths_match(
        &self, scope: &FuncProjection, start: usize, widths: Seq<u64>,
    ) -> bool {
        &&& start + widths.len() <= scope.types@.len()
        &&& forall|port: int| 0 <= port < widths.len() ==> (
            scope.types@[start + port] matches Some(ty)
                && self.port_width_matches(ty.ty, #[trigger] widths[port], scope.layouts)
        )
    }

    /// 呼び出し先の宣言から求めた出力幅が、呼び出し元の各左辺の型にも合うことを示す。
    proof fn call_definition_widths_from_signature(
        &self, scope: &FuncProjection, call: &CheckedExpansionCall, widths: Seq<u64>,
    )
        requires
            call._signature@.signature is Function,
            call.outputs.start <= call.outputs.end <= scope.types@.len(),
            call.outputs.end - call.outputs.start == widths.len(),
            self.port_widths_match(call._signature@.signature->Function_0.outputs@, widths, scope.layouts),
            forall|port: int| 0 <= port < widths.len() ==> {
                let expected = call._signature@.signature->Function_0.outputs@[port];
                (#[trigger] scope.types@[call.outputs.start + port]) == Some(SignalType {
                    ty: expected.ty, origin: expected.annotation,
                })
            },
        ensures self.call_definition_widths_match(scope, call.outputs.start, widths),
    {
        reveal(UseAliases::call_definition_widths_match);
        assert forall|port: int| 0 <= port < widths.len() implies (
            scope.types@[call.outputs.start + port] matches Some(ty)
                && self.port_width_matches(ty.ty, #[trigger] widths[port], scope.layouts)
        ) by {
            let expected = call._signature@.signature->Function_0.outputs@[port];
            assert(scope.types@[call.outputs.start + port] == Some(SignalType {
                ty: expected.ty, origin: expected.annotation,
            }));
        };
    }

    /// 呼び出しの出力をポート順に登録し、後続の定義から参照できるようにする。
    ///
    /// 各出力には呼び出し式の元ソース範囲を保持する。
    fn append_call_definitions(
        &self, scope: &FuncProjection<'_, 'p, 'a>, call: &CheckedExpansionCall<'p, 'a>, group: usize,
        widths: &[u64], definitions: &mut Vec<CheckedBitDefinition<'p, 'a>>,
    )
        requires
            self.definition_widths_match(scope, old(definitions)@),
            old(definitions)@.len() == call.outputs.start <= call.outputs.end <= scope.types@.len(),
            widths@.len() == call.outputs.end - call.outputs.start,
            location_in_source(call.expression),
            self.call_definition_widths_match(scope, call.outputs.start, widths@),
        ensures
            self.definition_widths_match(scope, final(definitions)@),
            final(definitions)@.len() == call.outputs.end,
            final(definitions)@.take(call.outputs.start as int) == old(definitions)@,
            forall|port: int| 0 <= port < widths@.len() ==> {
                let slot = #[trigger] final(definitions)@[call.outputs.start + port];
                &&& slot.rhs == BitFuncRhs::CallOutput { group, port: port as usize }
                &&& slot.expression == call.expression
                &&& slot.width == widths@[port] > 0
                &&& slot.operands@.len() == 0
            },
    {
        let ghost before = definitions@;
        let mut port = 0;
        while port < widths.len()
            invariant
                call.outputs.start <= call.outputs.end <= scope.types@.len(),
                widths@.len() == call.outputs.end - call.outputs.start,
                port <= widths@.len(),
                location_in_source(call.expression),
                definitions@.len() == call.outputs.start + port,
                definitions@.take(call.outputs.start as int) == before,
                self.definition_widths_match(scope, definitions@),
                self.call_definition_widths_match(scope, call.outputs.start, widths@),
                forall|j: int| 0 <= j < port ==> {
                    let slot = #[trigger] definitions@[call.outputs.start + j];
                    &&& slot.rhs == BitFuncRhs::CallOutput { group, port: j as usize }
                    &&& slot.expression == call.expression
                    &&& slot.width == widths@[j] > 0
                    &&& slot.operands@.len() == 0
                },
            decreases widths@.len() - port,
        {
            let width = widths[port];
            let slot = CheckedBitDefinition { expression: copy_location(&call.expression), width,
                rhs: BitFuncRhs::CallOutput { group, port }, operands: Vec::new() };
            let ghost previous = definitions@;
            proof {
                reveal(UseAliases::call_definition_widths_match);
                self.push_definition_width(scope, previous, slot);
            }
            definitions.push(slot);
            assert(definitions@.take(call.outputs.start as int) =~= previous.take(call.outputs.start as int));
            assert forall|j: int| 0 <= j <= port implies {
                let slot = #[trigger] definitions@[call.outputs.start + j];
                &&& slot.rhs == BitFuncRhs::CallOutput { group, port: j as usize }
                &&& slot.expression == call.expression
                &&& slot.width == widths@[j] > 0
                &&& slot.operands@.len() == 0
            } by {
                if j < port { assert(definitions@[call.outputs.start + j] == previous[call.outputs.start + j]); }
            };
            port += 1;
        }
    }

    proof fn structure_input_width_matches(
        &self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, at: usize,
    )
        requires
            self.projection_context(scope),
            self.projection_port_widths_match(scope),
            self.projection_structures_match(scope),
            self.definition_widths_match(scope, prior),
            at < scope.structures@.len(),
            scope.structures@[at as int].target == prior.len(),
        ensures ({
            let projection = scope.structures@[at as int];
            &&& bit_driver_width(scope.inputs@, prior, projection.input) == Some(projection.input_width)
            &&& projection.selection matches Some(outer) ==>
                outer.fits((projection.operation.range.end - projection.operation.range.start) as u64)
        }),
    {
        let projection = scope.structures@[at as int];
        let layout = scope.layouts->Some_0;
        let actual = bit_driver_width(scope.inputs@, prior, projection.input);
        assert(actual.is_some());
        self.driver_type_matches_width(scope, prior, projection.input, actual->Some_0);
        assert(structure_projection_matches(self, scope.file, scope.entry, scope.limit, scope.wiring,
            *layout, scope.types@, projection));
        if projection.selection.is_some() {
            self.field_projection_evidence(scope.file, scope.entry, scope.limit, scope.wiring, *layout,
                scope.types@, projection);
        } else {
            self.structure_projection_widths(scope.file, scope.entry, scope.limit, scope.wiring, *layout,
                scope.types@, projection);
        }
        let ty = signal_type_at(scope.wiring, scope.types@.take(prior.len() as int), projection.input)->Some_0.ty;
        match ty {
            ResolvedPortType::Bits(bits) => self.layout_bits_port_width(layout, bits, projection.input_width as int),
            ResolvedPortType::Struct { .. } =>
                self.layout_port_widths_agree(layout, ty, projection.input_width as int, actual->Some_0 as int),
        }
    }

    fn project_structure_definition(
        &self, scope: &FuncProjection<'_, 'p, 'a>, _prior: &[CheckedBitDefinition<'p, 'a>],
        _index: usize, at: usize, expression: LocatedName<'p, 'a>,
    ) -> (checked: CheckedBitDefinition<'p, 'a>)
        requires
            self.projection_context(scope),
            self.projection_port_widths_match(scope),
            self.projection_structures_match(scope),
            self.definition_widths_match(scope, _prior@),
            _index == _prior@.len() < scope.wiring.drivers.definitions@.len(),
            at < scope.structures@.len(),
            scope.structures@[at as int].target == _index,
            ({
                let row = scope.parsed.definitions@[scope.wiring.drivers.definitions@[_index as int].definition as int];
                let forms = scope.parsed.syntax.forms@;
                let (start, end) = definition_target_range(forms, row);
                end - start == 1 && is_form_location(scope.source, forms[row.expression.start as int], expression)
            }),
        ensures self.bit_definition_from_source(scope, _prior@, _index as int, checked),
    {
        proof { self.structure_input_width_matches(scope, _prior@, at); }
        let project = &scope.structures[at];
        let range = &project.operation.range;
        let (width, rhs) = if let Some(outer) = project.selection {
            let field = select_contiguous_range(range.start, range.end, project.input_width);
            let selection = compose_selections(project.input_width, field, outer);
            (selection.count, BitFuncRhs::Selection { input: project.input, selection })
        } else {
            (range.end - range.start, contiguous_rhs(project.input, range.start, range.end, project.input_width))
        };
        assert(self.bit_rhs_from_source(scope, _prior@, _index as int, rhs, Seq::empty()));
        CheckedBitDefinition { expression, width, rhs, operands: Vec::new() }
    }

    /// 選択列の入力を結線から取り出し、合成した選択を一つの右辺にする。
    fn project_nested_definition(
        &self, scope: &FuncProjection<'_, 'p, 'a>, prior: &[CheckedBitDefinition<'p, 'a>], index: usize,
        steps: &[crate::syntax::circuit::BitSelectionShape], leaf: usize, expression: LocatedName<'p, 'a>,
        Ghost(typed): Ghost<FuncSignalTypes<'p, 'a>>,
    ) -> (checked: CheckedBitDefinition<'p, 'a>)
        requires
            self.projection_context(scope),
            self.projection_port_widths_match(scope),
            self.definition_widths_match(scope, prior@),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            typed.types@ == scope.types@,
            typed.types@.len() == scope.wiring.drivers.definitions@.len(),
            index == prior@.len() < scope.wiring.drivers.definitions@.len(),
            forall|i: int| 0 <= i < prior@.len() ==>
                location_in_source((#[trigger] prior@[i]).expression) && prior@[i].width > 0,
            forall|j: int| 0 <= j < scope.structures@.len() ==> (#[trigger] scope.structures@[j]).target != index,
            ({
                let definition = scope.wiring.drivers.definitions@[index as int].definition;
                let row = scope.parsed.definitions@[definition as int];
                let root = row.expression.start;
                let forms = scope.parsed.syntax.forms@;
                let (first, end) = definition_target_range(forms, row);
                &&& end - first == 1
                &&& root < forms.len()
                &&& is_form_location(scope.source, forms[root as int], expression)
                &&& nested_named_selection_matches(scope.source.text, forms, root, steps@, leaf)
            }),
        ensures self.bit_definition_from_source(scope, prior@, index as int, checked),
    {
        let source = scope.source;
        let parsed = scope.parsed;
        let wiring = scope.wiring;
        let definition = wiring.drivers.definitions[index].definition;
        let row = &parsed.definitions[definition];
        let root = row.expression.start;
        let forms = parsed.syntax.forms.as_slice();
        proof {
            reveal(nested_named_selection_matches);
            self.checked_wiring_is_func(scope.file, scope.entry, scope.limit, *wiring);
            parsed_index_evidence(*source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(), scope.entry as int, definition as int);
            self.checked_nested_selection_driver(scope.file, scope.entry, scope.limit, source, parsed, wiring, index, steps@, leaf);
            let site = wiring.drivers.definitions@[index as int];
            assert(indexed_driver_site(source, parsed, scope.entry as int, site));
            assert(site.result_index == 0);
        }
        let at = row.signals.start - parsed.entry_ranges[scope.entry].signals.start;
        let input = wiring.signals[at].driver;
        let (width, origin) = driver_type(&wiring.drivers.signature, scope.inputs.as_slice(), prior, input);
        let ghost (inferred_width, inferred_origin, inferred) = {
            self.driver_type_matches_width(scope, prior@, input, width);
            assert(signal_type_at(wiring, typed.types@.take(index as int), input).is_some());
            let evidence = self.checked_nested_selection_type(
                scope.file, scope.entry, scope.limit, typed, *wiring, index as int, steps@, leaf,
            );
            assert(evidence.0 == width);
            evidence
        };
        let selection = match check_selection_chain(source, forms, root, steps, leaf, width, origin) {
            Ok(checked) => checked,
            Err(_error) => {
                proof { selection_chain_success_excludes_error(
                    source, forms@, steps@, inferred_width, inferred_origin, inferred, *origin, _error,
                ); }
                unreachable!()
            }
        };
        assert(Self::nested_selection_projection(scope, prior@, index as int, input, selection)) by {
            reveal(UseAliases::nested_selection_projection);
            assert(nested_named_selection_matches(source.text, forms@, root, steps@, leaf));
        };
        let rhs = BitFuncRhs::Selection { input, selection };
        CheckedBitDefinition { expression, width: selection.count, rhs, operands: Vec::new() }
    }

    /// 型検査を終えたフィールド選択には、対応する変換用の行が存在する。
    proof fn field_selection_requires_projection(
        &self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, typed: FuncSignalTypes,
        steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape,
    )
        requires
            self.projection_context(scope),
            self.projection_port_widths_match(scope),
            self.definition_widths_match(scope, prior),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            typed.types@ == scope.types@,
            typed.types@.len() == scope.wiring.drivers.definitions@.len(),
            self.func_structure_projections_complete(scope.file, scope.entry, scope.limit, typed, scope.wiring, scope.structures@),
            prior.len() < scope.wiring.drivers.definitions@.len(),
            ({
                let site = scope.wiring.drivers.definitions@[prior.len() as int];
                let row = scope.parsed.definitions@[site.definition as int];
                let forms = scope.parsed.syntax.forms@;
                let (first, end) = definition_target_range(forms, row);
                &&& end - first == 1
                &&& field_selection_shape_matches(scope.source.text, forms, row.expression.start, steps, at, shape)
            }),
        ensures exists|j: int| 0 <= j < scope.structures@.len() && (#[trigger] scope.structures@[j]).target == prior.len(),
    {
        let index = prior.len() as int;
        let wiring = scope.wiring;
        let parsed = scope.parsed;
        let source = scope.source;
        let forms = parsed.syntax.forms@;
        self.checked_wiring_is_func(scope.file, scope.entry, scope.limit, *wiring);
        let site = wiring.drivers.definitions@[index];
        assert(indexed_driver_site(source, parsed, scope.entry as int, site));
        assert(site.result_index == 0);
        let row = parsed.definitions@[site.definition as int];
        let root = row.expression.start;
        field_selection_root(source.text, forms, root, steps, at, shape);
        self.checked_types_keep_wiring(scope.file, scope.entry, scope.limit, typed, *wiring);
        self.nonliteral_definition_has_no_literal_width(scope.file, scope.entry, scope.limit, &typed.literals, wiring, index);
        if exists|direct: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root as int, direct) {
            let direct = choose|direct: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root as int, direct);
            bit_selection_shapes_agree(source.text, forms, root as int, steps[0], direct);
            assert(false);
        }
        if exists|other: Seq<BitSelectionShape>, name: usize|
            #[trigger] nested_named_selection_matches(source.text, forms, root, other, name)
        {
            let (other, name) = choose|other: Seq<BitSelectionShape>, name: usize|
                #[trigger] nested_named_selection_matches(source.text, forms, root, other, name);
            field_and_named_selection_disjoint(source.text, forms, root, steps, at, shape, other, name);
        }
        parsed_index_evidence(*source, *parsed);
        build_field_selection_signal(source.text, &parsed.build_model(), scope.entry as int, site.definition as int, steps, at, shape);
        self.checked_signal_driver(scope.file, scope.entry, scope.limit, *wiring, site.definition, row.signals.start);
        let first = row.signals.start - parsed.entry_ranges@[scope.entry as int].signals.start;
        if let OutputDriver::Definition(before) = wiring.signals@[first].driver {
            assert(before < index) by {
                if index < before {
                    assert(wiring.drivers.definitions@[index].definition <= wiring.drivers.definitions@[before as int].definition);
                }
            };
            self.driver_type_matches_width(scope, prior, OutputDriver::Definition(before), prior[before as int].width);
            assert(typed.types@[before as int].is_some());
        }
        let project = self.targets.project_model();
        let roots = choose|roots: FuncCallOutputTypes|
            #[trigger] self.signal_type_sources(scope.file, scope.entry, scope.limit, typed.literals, wiring, roots)
            && roots.types@.len() == wiring.drivers.definitions@.len()
            && (forall|target: int| 0 <= target < typed.types@.len() &&
                #[trigger] structure_projection_required(
                    &project.sources_model()[scope.file as int], &project.circuits_model()[scope.file as int],
                    scope.entry, wiring, typed.literals.widths@, roots.types@, typed.types@, target,
                ) ==> exists|j: int| 0 <= j < scope.structures@.len() && (#[trigger] scope.structures@[j]).target == target);
        assert(structure_projection_required(source, parsed, scope.entry, wiring, typed.literals.widths@,
            roots.types@, typed.types@, index)) by { reveal(structure_projection_required); };
    }

    fn project_definition(
        &self, scope: &FuncProjection<'_, 'p, 'a>, prior: &[CheckedBitDefinition<'p, 'a>], index: usize,
        projection: Option<usize>, concat: Option<ConcatProjection>, literal_width: Option<u64>,
        Ghost(typed): Ghost<FuncSignalTypes<'p, 'a>>,
    ) -> (result: Result<CheckedBitDefinition<'p, 'a>, BitFuncError<'p, 'a>>)
        requires
            self.projection_context(scope),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            typed.types@ == scope.types@,
            typed.types@.len() == scope.wiring.drivers.definitions@.len(),
            literal_width == typed.literals.widths@[index as int],
            self.func_structure_projections_complete(scope.file, scope.entry, scope.limit, typed, scope.wiring, scope.structures@),
            index == prior@.len() < scope.wiring.drivers.definitions@.len(),
            self.projection_port_widths_match(scope),
            self.projection_structures_match(scope),
            self.definition_widths_match(scope, prior@),
            projection matches Some(at) ==> at < scope.structures@.len() && scope.structures@[at as int].target == index,
            projection.is_none() ==> forall|j: int| 0 <= j < scope.structures@.len()
                ==> (#[trigger] scope.structures@[j]).target != index,
            concat matches Some(row) ==> row.target == index && concat_projection_matches(scope.file, scope.entry, scope.limit,
                scope.source, scope.parsed, scope.wiring, scope.types@, row),
            concat.is_none() ==> !concat_type_ready(scope, index as int),
            forall|i: int| 0 <= i < prior@.len() ==>
                location_in_source((#[trigger] prior@[i]).expression) && prior@[i].width > 0,
        ensures
            result matches Ok(checked) ==> self.bit_definition_from_source(scope, prior@, index as int, checked),
            result matches Err(error) ==> self.definition_error(scope, prior@, error),
    {
        let file = scope.file;
        let entry = scope.entry;
        let limit = scope.limit;
        let source = scope.source;
        let parsed = scope.parsed;
        let wiring = scope.wiring;
        let signature = &wiring.drivers.signature;
        let definition = wiring.drivers.definitions[index].definition;
        let row = &parsed.definitions[definition];
        let root = row.expression.start;
        let end = row.expression.end;
        let forms = parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, definition as int);
        }
        let expression = form_location(source, forms, root);
        let targets = definition_target_atoms(forms, row);
        if targets.end - targets.start != 1 {
            return Err(BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, expression));
        }
        if let Some(at) = projection {
            return Ok(self.project_structure_definition(scope, prior, index, at, expression));
        }
        if let Some(concat) = concat {
            proof {
                concat_projection_evidence(file, entry, limit, source, parsed, wiring, scope.types@, concat);
                assert forall|j: int| 0 <= j < concat.operands@.len() implies {
                    let (operand, width) = #[trigger] concat.operands@[j];
                    &&& width > 0
                    &&& match operand {
                        SingleBitOperand::Constant(_) => width == 1,
                        SingleBitOperand::Driver(driver) =>
                            bit_driver_width(scope.inputs@, prior@, driver) == Some(width),
                    }
                } by {
                    if let SingleBitOperand::Driver(driver) = concat.operands@[j].0 {
                        let width = bit_driver_width(scope.inputs@, prior@, driver)->Some_0;
                        self.driver_type_matches_width(scope, prior@, driver, width);
                    }
                };
                assert(concat_operands_fit(scope.inputs@, prior@, concat.operands@));
            }
            let checked = CheckedBitDefinition { expression, width: concat.width, rhs: BitFuncRhs::Concat,
                operands: concat.operands };
            assert(self.bit_definition_from_source(scope, prior@, index as int, checked));
            return Ok(checked);
        }
        if matches!(forms[root], Form::Atom { kind: AtomKind::Binary | AtomKind::Hexadecimal, .. }) {
            let ghost bytes = literal_bytes(expression);
            proof {
                self.checked_wiring_is_func(file, entry, limit, *wiring);
                self.checked_types_keep_wiring(file, entry, limit, typed, *wiring);
                assert(indexed_driver_site(source, parsed, entry as int, wiring.drivers.definitions@[index as int]));
                assert(wiring.drivers.definitions@[index as int].result_index == 0);
                let bits = self.bit_vector_definition_width(file, entry, limit, &typed.literals, wiring, index as int);
                assert(literal_width == Some(bits));
                self.checked_literal_type(file, entry, limit, typed, *wiring, index as int, bits);
                assert(bit_vector_token(bytes)) by { reveal(form_spans_valid); };
                crate::syntax::bit_literal_kind_has_digits(bytes);
                let expected = choose|expected: Option<u64>|
                    #[trigger] circuit_literal_width_matches(bytes, expected, limit, Ok(bits));
                circuit_bit_literal_boundary(bytes, expected, limit, Ok(bits));
            }
            let Some(width) = literal_width else {
                proof { assert(false); }
                return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, expression));
            };
            let checked = CheckedBitDefinition { expression, width, rhs: BitFuncRhs::BitVector, operands: Vec::new() };
            assert(self.bit_definition_from_source(scope, prior@, index as int, checked));
            return Ok(checked);
        }
        assert forall|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
            !#[trigger] field_selection_shape_matches(source.text, forms@, root, steps, at, shape) by {
            if field_selection_shape_matches(source.text, forms@, root, steps, at, shape) {
                self.field_selection_requires_projection(scope, prior@, typed, steps, at, shape);
                assert(false);
            }
        };
        let (width, rhs) = if let Some(operand) = self.read_single_bit_operand(file, entry, limit, source, parsed, root, wiring, definition, index) {
            match operand {
                SingleBitOperand::Constant(bit) => (1, BitFuncRhs::Constant(bit)),
                SingleBitOperand::Driver(driver) => (driver_type(signature, scope.inputs.as_slice(), prior, driver).0, BitFuncRhs::Driver(driver)),
            }
        } else if let Some(shape) = named_selection(source.text, forms, root) {
            proof { bit_selection_shape_positions(source.text, forms@, root as int, shape); }
            let Some(SingleBitOperand::Driver(input)) = self.read_single_bit_operand(
                file, entry, limit, source, parsed, shape.input.start, wiring, definition, index,
            ) else { return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, expression)); };
            let (width, origin) = driver_type(signature, scope.inputs.as_slice(), prior, input);
            let selection = match check_selection_arguments(source, forms, root, &shape, width, origin) {
                Ok(checked) => checked,
                Err(error) => return Err(BitFuncError::Selection(error)),
            };
            (selection.count, BitFuncRhs::Selection { input, selection })
        } else if let Some((steps, leaf)) = nested_named_selection(source.text, forms, root) {
            return Ok(self.project_nested_definition(scope, prior, index, steps.as_slice(), leaf, expression, Ghost(typed)));
        } else if end - root == 4 && matches!(forms[root], Form::List { .. }) {
            let local = definition - parsed.entry_ranges[entry].definitions.start;
            let call = match self.resolve_func_call_signature(file, entry, local, 0, limit) {
                Ok(Some(call)) => call,
                Ok(None) => return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, expression)),
                Err(error) => return Err(BitFuncError::Call(local, error)),
            };
            if call.call.call.form != root || call.call.call.arguments != 2 || !matches!(call.call.target, FuncCallTarget::Nor) {
                return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, expression));
            }
            let Some(left) = self.read_single_bit_operand(file, entry, limit, source, parsed, root + 2, wiring, definition, index) else {
                return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, form_location(source, forms, root + 2)));
            };
            let Some(right) = self.read_single_bit_operand(file, entry, limit, source, parsed, root + 3, wiring, definition, index) else {
                return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, form_location(source, forms, root + 3)));
            };
            let left_width = operand_width(signature, scope.inputs.as_slice(), prior, left);
            if left_width != 1 {
                return Err(BitFuncError::NorInputWidth { argument: form_location(source, forms, root + 2), actual: left_width });
            }
            let right_width = operand_width(signature, scope.inputs.as_slice(), prior, right);
            if right_width != 1 {
                return Err(BitFuncError::NorInputWidth { argument: form_location(source, forms, root + 3), actual: right_width });
            }
            (1, BitFuncRhs::Nor { left, right })
        } else {
            return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, expression));
        };
        let checked = CheckedBitDefinition { expression, width, rhs, operands: Vec::new() };
        Ok(checked)
    }

    /// 型が確定した連接を未対応と判定する経路がないことを示す。
    proof fn ready_concat_has_row(
        &self, scope: &FuncProjection, typed: FuncSignalTypes, rows: Seq<ConcatProjection>, target: int,
    )
        requires
            self.projection_context(scope),
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            typed.types@ == scope.types@,
            self.func_concat_projections_complete(scope.file, scope.entry, scope.limit, typed, scope.wiring, rows),
            concat_type_ready(scope, target),
        ensures exists|j: int| 0 <= j < rows.len() && (#[trigger] rows[j]).target == target,
    {
        let (file, entry, limit) = (scope.file, scope.entry, scope.limit);
        let wiring = scope.wiring;
        let parsed = scope.parsed;
        let source = scope.source;
        let driver = wiring.drivers.definitions@[target];
        let root = parsed.definitions@[driver.definition as int].expression.start;
        let args = choose|args: core::ops::Range<usize>|
            #[trigger] crate::syntax::circuit::concat_arguments_match(source.text, parsed.syntax.forms@, root as int, args);
        crate::syntax::circuit::concat_excludes_other_shapes(source.text, parsed.syntax.forms@, root as int, args);
        self.checked_types_keep_wiring(file, entry, limit, typed, *wiring);
        self.literal_widths_fit_wiring(file, entry, limit, &typed.literals, wiring);
        self.nonliteral_definition_has_no_literal_width(file, entry, limit, &typed.literals, wiring, target);
        let roots = choose|roots: FuncCallOutputTypes|
            #[trigger] self.signal_type_sources(file, entry, limit, typed.literals, wiring, roots)
            && roots.types@.len() == wiring.drivers.definitions@.len()
            && concat_projections_complete(source, parsed, wiring, typed.literals.widths@, roots.types@, typed.types@, rows);
        assert(concat_projection_required(source, parsed, wiring, typed.literals.widths@, roots.types@, typed.types@, target));
    }

    /// 組み合わせ関数から、ポートの幅と定義順の右辺を取り出す。
    ///
    /// 信号の転送、定数 `0`・`1`、基底 NOR を扱う。
    /// 最内段の入力が裸の信号名か、その信号を参照する `field` である `bit`・`slice` を扱う。
    /// 入れ子の選択は配線上で一段にまとめる。
    /// `field`・`as`・`raw` は、裸の信号名を入力に取る式を扱う。
    /// 構造体型のポート間で同じ型の信号を転送するときは、宣言の総幅を使う。
    ///
    /// `concat` は、型が確定した裸のビット列信号と定数 `0`・`1` を引数に取れる。
    /// 二進・十六進リテラルを単独の右辺に置くと、型検査で決まった幅の定数配線になる。
    ///
    /// # Examples
    ///
    /// 構造体ポートを直結すると、フィールドの間や末尾の空きビットも出力に残る。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "main.ncg2", revision: 1,
    ///     text: "(using nor)
    ///            (struct Packet (width 8) (tag (bits 3) (at 2)))
    ///            (func forward (in (word Packet)) (out (result Packet)) (def result word))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let checked = aliases.check_bit_func(0, 2, 8).unwrap();
    /// let lowered = checked.lower_bit_func(8).unwrap();
    /// let input = [true, false, false, true, false, false, true, true];
    /// assert_eq!(lowered.netlist().evaluate(&input).unwrap(), input);
    /// assert!(lowered.netlist().gates.is_empty());
    /// ```
    ///
    /// フィールドのビットだけを一方の出力に渡し、もう一方には空きビットを含む全体を返す。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "main.ncg2", revision: 1,
    ///     text: "(using nor)
    ///            (struct Packet (width 8) (tag (bits 3) (at 2)))
    ///            (func unpack (in (bus (bits 8))) (out (tag (bits 3)) (raw-bus (bits 8)))
    ///                (def packet (as Packet bus))
    ///                (def tag (field packet tag))
    ///                (def raw-bus (raw packet)))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let checked = aliases.check_bit_func(0, 2, 19).unwrap();
    /// let lowered = checked.lower_bit_func(19).unwrap();
    /// let bits = [true, false, false, true, true, false, true, true];
    /// let outputs = lowered.netlist().evaluate(&bits).unwrap();
    /// assert_eq!(&outputs[lowered.outputs().ranges()[0].clone()], &[false, true, true]);
    /// assert_eq!(&outputs[lowered.outputs().ranges()[1].clone()], &bits);
    /// assert!(lowered.netlist().gates.is_empty());
    /// ```
    ///
    /// # Errors
    ///
    /// 型・結線と出力数を先に検査する。構造体型のポートに使う配置表がなければ、
    /// 定義を配線に変換する前に配置と循環を検査する。
    /// 対応範囲外の場合は、ポートや右辺の元ソース位置を返す。
    /// 内部で求めた二つの入力幅が一致しない場合は、構造体式の位置と両方の幅を返す。
    pub fn check_bit_func(
        &self, file: usize, entry: usize, limit: u64,
    ) -> (result: Result<CheckedBitFunc<'p, 'a>, BitFuncError<'p, 'a>>)
        requires self.can_resolve(),
        ensures match result {
            Ok(checked) => checked_bit_func_available(&checked) && self.checked_bit_func_matches(file, entry, limit, &checked),
            Err(error) => self.checked_bit_func_error(file, entry, limit, error),
        },
    {
        let (typed, projections) = match self.check_func_signal_projections(file, entry, limit, true, false) {
            Ok(checked) => checked,
            Err(error) => return Err(BitFuncError::Check(error)),
        };
        let ghost typed_model = typed;
        let wiring = match typed.literals.wiring {
            FuncWiringResult::Checked(wiring) => wiring,
            FuncWiringResult::NotFunc => return Err(BitFuncError::NotFunc),
            FuncWiringResult::NeedsExpansion(site) => return Err(BitFuncError::NeedsExpansion(site)),
        };
        proof {
            self.checked_types_keep_wiring(file, entry, limit, typed_model, wiring);
            self.literal_widths_fit_wiring(file, entry, limit, &typed_model.literals, &wiring);
            self.checked_wiring_is_func(file, entry, limit, wiring);
            self.targets.parsed_project_model();
        }
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let ghost original_layouts = projections.layouts;
        reveal(UseAliases::routine_ports_result);
        let PreparedBitFuncPorts { inputs: input_widths, outputs: output_widths, layouts } =
            match self.prepare_routine_ports(file, entry, limit, &wiring, projections.layouts) {
                Ok(ports) => ports,
                Err(error) => {
                    let _empty: Vec<u64> = Vec::new();
                    let ghost early_scope = FuncProjection { file, entry, limit, source, parsed, wiring: &wiring,
                        inputs: &_empty, outputs: &_empty, layouts: None, types: &typed.types, structures: &projections.entries };
                    assert(self.projection_failure(&early_scope, error));
                    proof { self.projected_error(&early_scope, typed_model, error); }
                    return Err(error);
                },
            };
        let layout_ref = layouts.as_ref();
        let scope = FuncProjection { file, entry, limit, source, parsed, wiring: &wiring,
            inputs: &input_widths, outputs: &output_widths,
            #[cfg(verus_only)]
            layouts: layout_ref,
            #[cfg(verus_only)]
            types: &typed.types,
            structures: &projections.entries };
        assert(self.projection_port_widths_match(&scope));
        assert(self.projection_structures_match(&scope)) by {
            if original_layouts.is_some() {
                assert(layouts == original_layouts);
            } else {
                assert(projections.entries@.len() == 0);
            }
        };
        let definitions = match self.project_standalone_definitions(
            &scope, typed.literals.widths.as_slice(), projections.concats, Ghost(typed_model),
        ) {
            Ok(definitions) => definitions,
            Err(error) => {
                proof { self.projected_error(&scope, typed_model, error); }
                return Err(error);
            },
        };
        if let Err(error) = check_output_widths(&wiring, scope.inputs.as_slice(), scope.outputs.as_slice(), definitions.as_slice()) {
            assert(self.definition_prefix(&scope, definitions@));
            assert(self.projection_failure(&scope, error));
            proof { self.projected_error(&scope, typed_model, error); }
            return Err(error);
        }
        let ghost layout_model = scope.layouts;
        let ghost structures_model = projections.entries;
        proof {
            reveal(checked_bit_func_available);
            reveal(UseAliases::definition_prefix);
        }
        let checked = CheckedBitFunc { signature: wiring.drivers.signature, input_widths, output_widths,
            definitions, output_drivers: wiring.drivers.outputs };
        assert(checked_bit_func_available(&checked));
        assert(self.checked_bit_func_projection(file, entry, limit, &checked, typed_model, layout_model, structures_model));
        assert(self.checked_bit_func_matches(file, entry, limit, &checked));
        Ok(checked)
    }
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn expands_successive_functions_in_dependency_order() {
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    let project = parse_circuit_project(&[SourceSnapshot {
        path: "calls.ncg2",
        revision: 1,
        text: "(using nor)
               (struct Word (width 4))
               (func pair (in (a (bits 4)) b) (out (a (bits 4)) b (boxed Word))
                   (def boxed (as Word a)))
               (func caller (in (a (bits 4)) b) (out y)
                   (def (word passthrough unused) (pair a b))
                   (def joined (concat word passthrough))
                   (def y (bit joined 3)))
               (func top (in (a (bits 4)) b) (out y)
                   (def y (caller a b)))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let templates = aliases.expand_templates_in_order(&plan, 8, 16, 0).unwrap();
    assert_eq!(templates.next_index(), plan.len());
    let caller_vertex = plan.template_vertex((0, 3)).unwrap();
    assert_eq!(templates.circuit_at_vertex(caller_vertex).unwrap().definition_wires().len(), 15);
    let result = templates.circuit_at_vertex(plan.template_vertex((0, 4)).unwrap()).unwrap();
    assert!(result.gate_definitions().is_empty());
    assert_eq!(result.netlist().evaluate(&[false, true, false, true, false]).unwrap(), [true]);
    assert_eq!(result.netlist().evaluate(&[false, true, false, false, true]).unwrap(), [false]);
}

} // verus!
