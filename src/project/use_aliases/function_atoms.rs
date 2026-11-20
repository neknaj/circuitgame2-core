//! 定数と裸の信号名から、関数の左辺に対応する型を求める。

use super::function_literals::index_outputs;
use super::function_types::FuncSignalTypeError;
use super::selection_arguments::check_selection_arguments;
use super::structure_types::{StructureExpressionContext, StructureLayouts, TypedStructureOperation};
#[cfg(verus_only)]
use super::selection_arguments::{CheckedBitSelection, selection_arguments_match, successful_selections_agree};
#[cfg(verus_only)]
use super::function_literals::{output_indices, output_indices_agree};
#[cfg(verus_only)]
use super::function_drivers::same_definition_driver;
#[cfg(verus_only)]
use super::function_drivers::expected_output_context;
use super::{FuncLiteralError, FuncLiteralWidths, FuncWiring, FuncWiringResult, OutputDriver, ResolvedPortType, UseAliases};
use crate::project::{LocatedName, ProjectSource, TypedPort};
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::{
    circuits::{parsed_circuit_matches, parsed_index_evidence, is_form_location},
    location_in_source, port_types_equal,
};
use crate::syntax::{AtomKind, Form};
use crate::syntax::circuit::{BitSelectionShape, StructureExpressionShape, bit_selection_shape, structure_expression_shape};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    NamedBuildCircuit, bit_selection_shape_matches, bit_selection_shape_positions, bit_selection_shapes_agree, build_bare_signal_position,
    build_definition_scope_evidence, build_selection_input_position, build_structure_input_position,
    ordinary_call_at, ordinary_call_excludes_special_forms, structure_expression_matches, structure_expression_positions,
};
#[cfg(verus_only)]
use crate::syntax::form_spans_valid;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 確定した信号型と、その根拠となるソース位置。
#[derive(Debug)]
pub struct SignalType<'p, 'a> {
    /// 入力宣言または右辺から得た型。
    pub ty: ResolvedPortType<'p, 'a>,
    /// 型を与えたポートの注釈、定数、または組み込み呼び出しの範囲。信号名を介しても元の範囲を保つ。
    pub origin: LocatedName<'p, 'a>,
}

/// 構造体式の駆動元と、型検査で決めたビット区間。
#[derive(Debug)]
pub(super) struct StructureProjection {
    pub(super) target: usize,
    pub(super) input: OutputDriver,
    pub(super) operation: TypedStructureOperation,
    pub(super) input_width: u64,
}

/// 定義順に集めた構造体式と、共通の配置表。
#[derive(Debug)]
pub(super) struct StructureProjections<'p, 'a> {
    pub(super) entries: Vec<StructureProjection>,
    pub(super) layouts: Option<StructureLayouts<'p, 'a>>,
}

pub(super) open spec fn structure_projections_in_order(rows: Seq<StructureProjection>, count: int, inputs: int) -> bool {
    &&& forall|j: int| 0 <= j < rows.len() ==> {
        let row = #[trigger] rows[j];
        &&& row.target < count
        &&& row.operation.range.start < row.operation.range.end <= row.input_width
        &&& match row.input {
            OutputDriver::Input(port) => port < inputs,
            OutputDriver::Definition(prior) => prior < row.target,
        }
    }
    &&& forall|a: int, b: int| 0 <= a < b < rows.len() ==> (#[trigger] rows[a]).target < (#[trigger] rows[b]).target
}

#[verifier::opaque]
pub(super) closed spec fn structure_projection_matches(
    aliases: &UseAliases, file: usize, entry: usize, limit: u64, wiring: &FuncWiring,
    layouts: StructureLayouts, types: Seq<Option<SignalType>>, projection: StructureProjection,
) -> bool {
    let project = aliases.targets.project_model();
    let source = &project.sources_model()[file as int];
    let parsed = &project.circuits_model()[file as int];
    let target = projection.target as int;
    let definition = wiring.drivers.definitions@[target].definition;
    let row = parsed.definitions@[definition as int];
    let frame = parsed.entry_ranges@[entry as int];
    let context = StructureExpressionContext { file, entry, limit, source, parsed,
        definition: (definition - frame.definitions.start) as usize };
    let forms = parsed.syntax.forms@;
    let first = row.signals.start - frame.signals.start;
    &&& target < types.len() && target < wiring.drivers.definitions@.len()
    &&& frame.definitions.start <= definition < frame.definitions.end
    &&& 0 <= first < wiring.signals@.len()
    &&& wiring.signals@[first].definition == definition
    &&& wiring.signals@[first].driver == projection.input
    &&& signal_type_at(wiring, types.take(target), projection.input) matches Some(input)
    &&& types[target] matches Some(signal)
    &&& exists|shape: StructureExpressionShape|
        #[trigger] named_structure_expression_matches(source.text, forms, row.expression.start as int, shape)
        && is_form_location(source, forms[shape.input.start as int], wiring.signals@[first].site)
        && aliases.structure_expression_type_matches(&context, shape, &layouts, input,
            Ok((signal, projection.operation, projection.input_width)))
}

#[verifier::opaque]
pub(super) open spec fn structure_projection_required(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, types: Seq<Option<SignalType>>, target: int,
) -> bool {
    let driver = wiring.drivers.definitions@[target];
    let row = parsed.definitions@[driver.definition as int];
    let root = row.expression.start as int;
    let forms = parsed.syntax.forms@;
    let first = row.signals.start - parsed.entry_ranges@[entry as int].signals.start;
    &&& roots.len() > 0 && widths[target].is_none() && driver.result_index == 0 && forms[root] is List
    &&& !(exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root, shape))
    &&& (exists|shape: StructureExpressionShape| #[trigger] named_structure_expression_matches(source.text, forms, root, shape))
    &&& 0 <= first < wiring.signals@.len()
    &&& signal_type_at(wiring, types.take(target), wiring.signals@[first].driver).is_some()
}

/// 配線、定数の幅、および定数や裸の信号参照から確定した型。
#[derive(Debug)]
pub struct FuncAtomTypes<'p, 'a> {
    /// 配線と定数の右辺の検査結果。
    pub literals: FuncLiteralWidths<'p, 'a>,
    /// 駆動元の左辺一覧と同じ順に並ぶ型。式の型が未確定なら `None`。
    /// 対象外や展開待ちでは空になる。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

/// 定数の幅、または右辺と出力の型の不一致に関する診断。
#[derive(Debug)]
pub enum FuncAtomTypeError<'p, 'a> {
    /// 配線、個数または定数の右辺の違反。
    Literal(FuncLiteralError<'p, 'a>),
    /// 右辺の型と、駆動先の出力の宣言型が異なる。
    OutputType {
        /// 右辺の信号名またはビット選択式の範囲。
        reference: LocatedName<'p, 'a>,
        /// 出力が要求する型と、その注釈位置。
        expected: SignalType<'p, 'a>,
        /// 信号の型と、その型の根拠となる位置。
        actual: SignalType<'p, 'a>,
    },
}

pub(super) fn copy_location<'p, 'a>(location: &LocatedName<'p, 'a>) -> (copy: LocatedName<'p, 'a>)
    ensures copy == *location,
{
    LocatedName { source: location.source, span: location.span.start..location.span.end }
}

fn copy_signal_type<'p, 'a>(signal: &Option<SignalType<'p, 'a>>) -> (copy: Option<SignalType<'p, 'a>>)
    ensures copy == *signal,
{
    match signal {
        Some(known) => Some(SignalType { ty: known.ty, origin: copy_location(&known.origin) }),
        None => None,
    }
}

pub(super) open spec fn signal_type_at<'p, 'a>(
    wiring: &FuncWiring<'p, 'a>, types: Seq<Option<SignalType<'p, 'a>>>, origin: OutputDriver,
) -> Option<SignalType<'p, 'a>>
{
    match origin {
        OutputDriver::Input(input) => {
            let port = wiring.drivers.signature.inputs@[input as int];
            Some(SignalType { ty: port.ty, origin: port.annotation })
        },
        OutputDriver::Definition(definition) => types[definition as int],
    }
}

pub(super) fn inherit_type<'p, 'a>(
    wiring: &FuncWiring<'p, 'a>, types: &[Option<SignalType<'p, 'a>>], origin: OutputDriver,
) -> (ty: Option<SignalType<'p, 'a>>)
    requires match origin {
        OutputDriver::Input(i) => i < wiring.drivers.signature.inputs@.len(),
        OutputDriver::Definition(i) => i < types@.len(),
    },
    ensures ty == signal_type_at(wiring, types@, origin),
{
    match origin {
        OutputDriver::Input(i) => {
            let port = &wiring.drivers.signature.inputs[i];
            Some(SignalType { ty: port.ty, origin: copy_location(&port.annotation) })
        },
        OutputDriver::Definition(i) => copy_signal_type(&types[i]),
    }
}

pub(super) open spec fn named_selection_matches(source: &str, forms: Seq<Form>, index: int, shape: BitSelectionShape) -> bool {
    &&& bit_selection_shape_matches(source, forms, index, shape)
    &&& shape.input.end == shape.input.start + 1
    &&& forms[shape.input.start as int] is Atom
    &&& forms[shape.input.start as int]->Atom_kind is Name
}

pub(super) fn named_selection(source: &str, forms: &[Form], index: usize) -> (result: Option<BitSelectionShape>)
    ensures
        result matches Some(shape) ==> named_selection_matches(source, forms@, index as int, shape),
        forall|shape: BitSelectionShape| #[trigger] named_selection_matches(source, forms@, index as int, shape)
            <==> result == Some(shape),
{
    let Some(shape) = bit_selection_shape(source, forms, index) else { return None; };
    proof { bit_selection_shape_positions(source, forms@, index as int, shape); }
    if shape.input.end - shape.input.start == 1
        && matches!(forms[shape.input.start], Form::Atom { kind: AtomKind::Name, .. })
    {
        Some(shape)
    } else { None }
}

pub(super) open spec fn named_structure_expression_matches(
    source: &str, forms: Seq<Form>, index: int, shape: StructureExpressionShape,
) -> bool {
    &&& structure_expression_matches(source, forms, index, shape)
    &&& shape.input.end == shape.input.start + 1
    &&& forms[shape.input.start as int] is Atom
    &&& forms[shape.input.start as int]->Atom_kind is Name
}

pub(super) fn named_structure_expression(
    source: &str, forms: &[Form], index: usize,
) -> (result: Option<StructureExpressionShape>)
    ensures
        result matches Some(shape) ==> named_structure_expression_matches(source, forms@, index as int, shape),
        forall|shape: StructureExpressionShape| #[trigger] named_structure_expression_matches(source, forms@, index as int, shape)
            <==> result == Some(shape),
{
    let Some(shape) = structure_expression_shape(source, forms, index) else { return None; };
    proof { structure_expression_positions(source, forms@, index as int, shape); }
    if shape.input.end - shape.input.start == 1
        && matches!(forms[shape.input.start], Form::Atom { kind: AtomKind::Name, .. })
    {
        Some(shape)
    } else {
        None
    }
}

spec fn structure_atom_step(
    aliases: &UseAliases, context: &StructureExpressionContext, shape: StructureExpressionShape,
    input: Option<SignalType>, expected: Option<TypedPort>, result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    if let Some(input) = input {
        match result {
            Err(FuncSignalTypeError::StructureLayout(error)) => aliases.structure_types_match(context.limit, Err(error)),
            _ => exists|layouts: super::StructureLayouts| #[trigger] aliases.structure_types_match(context.limit, Ok(layouts))
                && match result {
                    Err(FuncSignalTypeError::StructureExpression(error)) =>
                        aliases.structure_expression_type_matches(context, shape, &layouts, input, Err(error)),
                    _ => exists|checked: super::structure_types::CheckedStructureExpression|
                        #[trigger] aliases.structure_expression_type_matches(context, shape, &layouts, input, Ok(checked))
                        && {
                            let actual = checked.0;
                            if let Some(port) = expected {
                                if port_types_equal(actual.ty, port.ty) {
                                    result == Ok(Some(actual))
                                } else {
                                    result == Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                                        reference: actual.origin,
                                        expected: SignalType { ty: port.ty, origin: port.annotation }, actual,
                                    }))
                                }
                            } else {
                                result == Ok(Some(actual))
                            }
                        },
                },
        }
    } else {
        result == Ok(None)
    }
}

spec fn selection_type_matches(
    source: &ProjectSource, forms: Seq<Form>, root: usize, shape: BitSelectionShape,
    input: Option<SignalType>, expected: Option<TypedPort>, result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    match input {
        None => result == Ok(None),
        Some(input) => match input.ty {
            ResolvedPortType::Bits(width) => match result {
                Err(FuncSignalTypeError::SelectionArgument(error)) =>
                    selection_arguments_match(source, forms, &shape, width, &input.origin, Err(error)),
                _ => exists|selection: super::selection_arguments::CheckedBitSelection, expression: LocatedName|
                    #[trigger] selection_arguments_match(source, forms, &shape, width, &input.origin, Ok(selection))
                    && #[trigger] is_form_location(source, forms[root as int], expression)
                    && {
                        let actual = SignalType { ty: ResolvedPortType::Bits(selection.count), origin: expression };
                        if let Some(port) = expected {
                            if port_types_equal(actual.ty, port.ty) {
                                result == Ok(Some(actual))
                            } else {
                                result == Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                                    reference: expression,
                                    expected: SignalType { ty: port.ty, origin: port.annotation },
                                    actual,
                                }))
                            }
                        } else {
                            result == Ok(Some(actual))
                        }
                    },
            },
            _ => result matches Err(FuncSignalTypeError::SelectionInputType { reference, actual })
                && actual == input && is_form_location(source, forms[shape.input.start as int], reference),
        },
    }
}

proof fn selection_type_successes_agree(
    source: &ProjectSource, forms: Seq<Form>, root: usize, shape: BitSelectionShape,
    input: Option<SignalType>, expected: Option<TypedPort>, first: Option<SignalType>, second: Option<SignalType>,
)
    requires
        selection_type_matches(source, forms, root, shape, input, expected, Ok(first)),
        selection_type_matches(source, forms, root, shape, input, expected, Ok(second)),
    ensures first == second,
{
    if let Some(input) = input {
        assert(input.ty is Bits);
        let width = input.ty->Bits_0;
        let (a, origin_a) = choose|selection: CheckedBitSelection, expression: LocatedName|
            #[trigger] selection_arguments_match(source, forms, &shape, width, &input.origin, Ok(selection))
            && #[trigger] is_form_location(source, forms[root as int], expression)
            && first == Some(SignalType { ty: ResolvedPortType::Bits(selection.count), origin: expression });
        let (b, origin_b) = choose|selection: CheckedBitSelection, expression: LocatedName|
            #[trigger] selection_arguments_match(source, forms, &shape, width, &input.origin, Ok(selection))
            && #[trigger] is_form_location(source, forms[root as int], expression)
            && second == Some(SignalType { ty: ResolvedPortType::Bits(selection.count), origin: expression });
        successful_selections_agree(source, forms, &shape, width, &input.origin, a, width, &input.origin, b);
        assert(origin_a == origin_b);
    }
}

fn check_selection_type<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], root: usize, shape: &BitSelectionShape,
    input: Option<SignalType<'p, 'a>>, expected: Option<&TypedPort<'p, 'a>>,
) -> (result: Result<Option<SignalType<'p, 'a>>, FuncSignalTypeError<'p, 'a>>)
    requires
        named_selection_matches(source.text, forms@, root as int, *shape),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
        input matches Some(ty) ==> location_in_source(ty.origin),
    ensures
        selection_type_matches(source, forms@, root, *shape, input,
            match expected { Some(port) => Some(*port), None => None }, result),
        result matches Ok(Some(ty)) ==> location_in_source(ty.origin),
        result matches Err(error) ==> (error is Signal || error is SelectionInputType || error is SelectionArgument),
        result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
{
    let Some(input) = input else { return Ok(None); };
    proof { bit_selection_shape_positions(source.text, forms@, root as int, *shape); }
    let ResolvedPortType::Bits(width) = input.ty else {
        let reference = form_location(source, forms, shape.input.start);
        return Err(FuncSignalTypeError::SelectionInputType { reference, actual: input });
    };
    let checked = match check_selection_arguments(source, forms, root, shape, width, &input.origin) {
        Ok(checked) => checked,
        Err(error) => return Err(FuncSignalTypeError::SelectionArgument(error)),
    };
    let expression = form_location(source, forms, root);
    let actual = SignalType { ty: ResolvedPortType::Bits(checked.count), origin: copy_location(&expression) };
    if let Some(port) = expected {
        if !actual.ty.is_same_type(&port.ty) {
            return Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                reference: expression,
                expected: SignalType { ty: port.ty, origin: copy_location(&port.annotation) },
                actual,
            }));
        }
    }
    Ok(Some(actual))
}

#[verifier::opaque]
spec fn atom_type_step(
    aliases: &UseAliases, file: usize, limit: u64,
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, outputs: Seq<Option<usize>>, roots: Seq<Option<SignalType>>,
    prior: Seq<Option<SignalType>>, i: int,
    result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    let driver = wiring.drivers.definitions@[i];
    let row = parsed.definitions@[driver.definition as int];
    let root = parsed.syntax.forms@[row.expression.start as int];
    &&& 0 <= entry < parsed.entry_ranges@.len()
    &&& 0 <= i < wiring.drivers.definitions@.len()
    &&& i < widths.len() && i < outputs.len()
    &&& driver.definition < parsed.definitions@.len()
    &&& row.expression.start < parsed.syntax.forms@.len()
    &&& if let Some(width) = widths[i] {
        result matches Ok(Some(ty)) && ty.ty == ResolvedPortType::Bits(width)
            && is_form_location(source, root, ty.origin)
    } else if driver.result_index == 0 && root is Atom && root->Atom_kind is Name {
        let first = parsed.entry_ranges@[entry].signals.start;
        let bound = wiring.signals@[row.signals.start - first];
        let actual = signal_type_at(wiring, prior, bound.driver);
        &&& first <= row.signals.start < first + wiring.signals@.len()
        &&& bound.definition == driver.definition && is_form_location(source, root, bound.site)
        &&& match bound.driver {
            OutputDriver::Input(input) => input < wiring.drivers.signature.inputs@.len(),
            OutputDriver::Definition(i) => i < prior.len(),
        }
        &&& match (actual, outputs[i]) {
            (Some(actual), Some(output)) => {
                let port = wiring.drivers.signature.outputs@[output as int];
                &&& output < wiring.drivers.signature.outputs@.len()
                &&& if port_types_equal(actual.ty, port.ty) {
                    result == Ok(Some(actual))
                } else {
                    result == Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                        reference: bound.site, expected: SignalType { ty: port.ty, origin: port.annotation }, actual,
                    }))
                }
            },
            _ => result == Ok(actual),
        }
    } else if roots.len() > 0 && driver.result_index == 0 && exists|shape: BitSelectionShape|
        #[trigger] named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape)
    {
        let shape = choose|shape: BitSelectionShape|
            #[trigger] named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape);
        let first = parsed.entry_ranges@[entry].signals.start;
        let bound = wiring.signals@[row.signals.start - first];
        let expected = if let Some(output) = outputs[i] {
            Some(wiring.drivers.signature.outputs@[output as int])
        } else { None };
        &&& first <= row.signals.start < first + wiring.signals@.len()
        &&& bound.definition == driver.definition
        &&& is_form_location(source, parsed.syntax.forms@[shape.input.start as int], bound.site)
        &&& match bound.driver {
            OutputDriver::Input(input) => input < wiring.drivers.signature.inputs@.len(),
            OutputDriver::Definition(prior_index) => prior_index < prior.len(),
        }
        &&& outputs[i] matches Some(output) ==> output < wiring.drivers.signature.outputs@.len()
        &&& selection_type_matches(source, parsed.syntax.forms@, row.expression.start, shape,
            signal_type_at(wiring, prior, bound.driver), expected, result)
    } else if roots.len() > 0 && driver.result_index == 0 && exists|shape: StructureExpressionShape|
        #[trigger] named_structure_expression_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape)
    {
        let shape = choose|shape: StructureExpressionShape|
            #[trigger] named_structure_expression_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape);
        let first = parsed.entry_ranges@[entry].signals.start;
        let bound = wiring.signals@[row.signals.start - first];
        let expected = if let Some(output) = outputs[i] {
            Some(wiring.drivers.signature.outputs@[output as int])
        } else { None };
        let context = StructureExpressionContext { file, entry: entry as usize, limit, source, parsed,
            definition: (driver.definition - parsed.entry_ranges@[entry].definitions.start) as usize };
        &&& first <= row.signals.start < first + wiring.signals@.len()
        &&& bound.definition == driver.definition
        &&& is_form_location(source, parsed.syntax.forms@[shape.input.start as int], bound.site)
        &&& match bound.driver {
            OutputDriver::Input(input) => input < wiring.drivers.signature.inputs@.len(),
            OutputDriver::Definition(prior_index) => prior_index < prior.len(),
        }
        &&& outputs[i] matches Some(output) ==> output < wiring.drivers.signature.outputs@.len()
        &&& structure_atom_step(aliases, &context, shape, signal_type_at(wiring, prior, bound.driver), expected, result)
    } else {
        result == Ok(if roots.len() == 0 { None } else { roots[i] })
    }
}

#[verifier::opaque]
spec fn typed_prefix(
    aliases: &UseAliases, file: usize, limit: u64,
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, outputs: Seq<Option<usize>>, roots: Seq<Option<SignalType>>, types: Seq<Option<SignalType>>,
) -> bool {
    &&& types.len() <= wiring.drivers.definitions@.len()
    &&& forall|i: int| 0 <= i < types.len() ==>
        #[trigger] atom_type_step(aliases, file, limit, source, parsed, entry, wiring, widths, outputs, roots, types.take(i), i, Ok(types[i]))
}

pub(super) closed spec fn atoms_match(
    aliases: &UseAliases, file: usize, limit: u64,
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, result: Result<Vec<Option<SignalType>>, FuncSignalTypeError>,
) -> bool {
    exists|outputs: Seq<Option<usize>>| #[trigger] output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, outputs)
        && match result {
            Ok(types) => types@.len() == wiring.drivers.definitions@.len()
                && typed_prefix(aliases, file, limit, source, parsed, entry, wiring, widths, outputs, roots, types@),
            Err(error) => exists|prior: Seq<Option<SignalType>>| prior.len() < wiring.drivers.definitions@.len()
                && #[trigger] typed_prefix(aliases, file, limit, source, parsed, entry, wiring, widths, outputs, roots, prior)
                && atom_type_step(aliases, file, limit, source, parsed, entry, wiring, widths, outputs, roots, prior, prior.len() as int, Err(error)),
        }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) proof fn checked_function_atom_types_agree(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        left: &FuncWiring, right: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>,
        a: Vec<Option<SignalType>>, b: Vec<Option<SignalType>>,
    )
        requires
            self.can_resolve(),
            left.drivers.signature.inputs@ == right.drivers.signature.inputs@,
            left.drivers.signature.outputs@ == right.drivers.signature.outputs@,
            left.drivers.definitions@.len() == right.drivers.definitions@.len(),
            forall|i: int| 0 <= i < left.drivers.definitions@.len() ==> same_definition_driver(
                #[trigger] left.drivers.definitions@[i], #[trigger] right.drivers.definitions@[i]),
            left.drivers.outputs@ == right.drivers.outputs@,
            left.signals@ == right.signals@,
            atoms_match(self, file, limit, source, parsed, entry as int, left, widths, roots, Ok(a)),
            atoms_match(self, file, limit, source, parsed, entry as int, right, widths, roots, Ok(b)),
        ensures a@ == b@,
    {
        let x = self.successful_atom_outputs(file, entry, limit, source, parsed, left, widths, roots, a);
        let y = self.successful_atom_outputs(file, entry, limit, source, parsed, right, widths, roots, b);
        output_indices_agree(&left.drivers, &right.drivers, x, y);
        self.atom_types_prefix_agrees(file, entry, limit, source, parsed, left, right, widths, roots, x, a@, b@, a@.len());
        assert(a@ =~= b@);
    }

    proof fn successful_atom_outputs(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        wiring: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, types: Vec<Option<SignalType>>,
    ) -> (outputs: Seq<Option<usize>>)
        requires atoms_match(self, file, limit, source, parsed, entry as int, wiring, widths, roots, Ok(types)),
        ensures
            output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, outputs),
            types@.len() == wiring.drivers.definitions@.len(),
            typed_prefix(self, file, limit, source, parsed, entry as int, wiring, widths, outputs, roots, types@),
    {
        choose|outputs: Seq<Option<usize>>|
            #[trigger] output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, outputs)
            && typed_prefix(self, file, limit, source, parsed, entry as int, wiring, widths, outputs, roots, types@)
    }

    proof fn atom_types_prefix_agrees(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        left: &FuncWiring, right: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>,
        outputs: Seq<Option<usize>>, a: Seq<Option<SignalType>>, b: Seq<Option<SignalType>>, end: nat,
    )
        requires
            self.can_resolve(),
            left.drivers.signature.inputs@ == right.drivers.signature.inputs@,
            left.drivers.signature.outputs@ == right.drivers.signature.outputs@,
            left.signals@ == right.signals@,
            forall|i: int| 0 <= i < a.len() ==> same_definition_driver(
                #[trigger] left.drivers.definitions@[i], #[trigger] right.drivers.definitions@[i]),
            typed_prefix(self, file, limit, source, parsed, entry as int, left, widths, outputs, roots, a),
            typed_prefix(self, file, limit, source, parsed, entry as int, right, widths, outputs, roots, b),
            end <= a.len() == b.len(),
        ensures forall|i: int| 0 <= i < end ==> (#[trigger] a[i]) == (#[trigger] b[i]),
        decreases end,
    {
        if end > 0 {
            let i = (end - 1) as int;
            self.atom_types_prefix_agrees(file, entry, limit, source, parsed, left, right, widths, roots, outputs, a, b, i as nat);
            assert(a.take(i) =~= b.take(i));
            reveal(typed_prefix);
            assert(same_definition_driver(left.drivers.definitions@[i], right.drivers.definitions@[i]));
            self.atom_types_at_agree(file, entry, limit, source, parsed, left, right, widths, roots, outputs,
                a.take(i), i, a[i], b[i]);
            assert forall|j: int| 0 <= j < end implies (#[trigger] a[j]) == (#[trigger] b[j]) by {
                if j < i { assert(a[j] == b[j]); }
            };
        }
    }

    proof fn atom_types_at_agree(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        left: &FuncWiring, right: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>,
        outputs: Seq<Option<usize>>, prior: Seq<Option<SignalType>>, i: int,
        a: Option<SignalType>, b: Option<SignalType>,
    )
        requires
            self.can_resolve(),
            left.drivers.signature.inputs@ == right.drivers.signature.inputs@,
            left.drivers.signature.outputs@ == right.drivers.signature.outputs@,
            left.signals@ == right.signals@,
            same_definition_driver(left.drivers.definitions@[i], right.drivers.definitions@[i]),
            atom_type_step(self, file, limit, source, parsed, entry as int, left, widths, outputs, roots, prior, i, Ok(a)),
            atom_type_step(self, file, limit, source, parsed, entry as int, right, widths, outputs, roots, prior, i, Ok(b)),
        ensures a == b,
    {
        reveal(atom_type_step);
        let driver = left.drivers.definitions@[i];
        let row = parsed.definitions@[driver.definition as int];
        let forms = parsed.syntax.forms@;
        let root = forms[row.expression.start as int];
        if widths[i].is_some() {
            assert(a->Some_0.origin == b->Some_0.origin);
        } else if driver.result_index == 0 && root is Atom && root->Atom_kind is Name {
            // 裸の信号名はどちらの検査でも同じ駆動元の型を引き継ぐ。
        } else if roots.len() > 0 && driver.result_index == 0 {
            let frame = parsed.entry_ranges@[entry as int];
            let bound = left.signals@[row.signals.start - frame.signals.start];
            let input = signal_type_at(left, prior, bound.driver);
            let expected = if let Some(output) = outputs[i] {
                Some(left.drivers.signature.outputs@[output as int])
            } else { None };
            if exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, row.expression.start as int, shape) {
                let shape = choose|shape: BitSelectionShape|
                    #[trigger] named_selection_matches(source.text, forms, row.expression.start as int, shape);
                selection_type_successes_agree(source, forms, row.expression.start, shape, input, expected, a, b);
            } else if exists|shape: StructureExpressionShape|
                #[trigger] named_structure_expression_matches(source.text, forms, row.expression.start as int, shape)
            {
                let shape = choose|shape: StructureExpressionShape|
                    #[trigger] named_structure_expression_matches(source.text, forms, row.expression.start as int, shape);
                let context = StructureExpressionContext { file, entry, limit, source, parsed,
                    definition: (driver.definition - frame.definitions.start) as usize };
                self.structure_atom_successes_agree(&context, shape, input, expected, a, b);
            }
        }
    }

    proof fn structure_atom_successes_agree(
        &self, context: &StructureExpressionContext, shape: StructureExpressionShape,
        input: Option<SignalType>, expected: Option<TypedPort>, a: Option<SignalType>, b: Option<SignalType>,
    )
        requires
            self.can_resolve(),
            structure_atom_step(self, context, shape, input, expected, Ok(a)),
            structure_atom_step(self, context, shape, input, expected, Ok(b)),
        ensures a == b,
    {
        if let Some(input) = input {
            let (left, x) = choose|layouts: StructureLayouts, value: super::structure_types::CheckedStructureExpression|
                #[trigger] self.structure_types_match(context.limit, Ok(layouts))
                && #[trigger] self.structure_expression_type_matches(context, shape, &layouts, input, Ok(value))
                && a == Some(value.0);
            let (right, y) = choose|layouts: StructureLayouts, value: super::structure_types::CheckedStructureExpression|
                #[trigger] self.structure_types_match(context.limit, Ok(layouts))
                && #[trigger] self.structure_expression_type_matches(context, shape, &layouts, input, Ok(value))
                && b == Some(value.0);
            self.checked_structure_expressions_agree(context, shape, &left, &right, input, x, y);
        }
    }

    proof fn successful_atom_step(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        wiring: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>,
        types: Vec<Option<SignalType>>, i: int,
    ) -> (outputs: Seq<Option<usize>>)
        requires
            atoms_match(self, file, limit, source, parsed, entry as int, wiring, widths, roots, Ok(types)),
            0 <= i < types@.len(),
        ensures
            atom_type_step(self, file, limit, source, parsed, entry as int,
                wiring, widths, outputs, roots, types@.take(i), i, Ok(types@[i])),
    {
        let outputs = self.successful_atom_outputs(file, entry, limit, source, parsed, wiring, widths, roots, types);
        reveal(typed_prefix);
        outputs
    }

    pub(super) proof fn atom_literal_type(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        wiring: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>,
        types: Vec<Option<SignalType>>, i: int, width: u64,
    )
        requires
            atoms_match(self, file, limit, source, parsed, entry as int, wiring, widths, roots, Ok(types)),
            0 <= i < types@.len(),
            widths[i] == Some(width),
        ensures types@[i] matches Some(ty) && ty.ty == ResolvedPortType::Bits(width),
    {
        let outputs = self.successful_atom_step(file, entry, limit, source, parsed, wiring, widths, roots, types, i);
        assert(atom_type_step(self, file, limit, source, parsed, entry as int,
            wiring, widths, outputs, roots, types@.take(i), i, Ok(types@[i])));
        reveal(atom_type_step);
    }

    pub(super) proof fn atom_call_inherits_output_type(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        wiring: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>,
        types: Vec<Option<SignalType>>, index: int,
    )
        requires
            atoms_match(self, file, limit, source, parsed, entry as int, wiring, widths, roots, Ok(types)),
            0 <= index < types@.len() && index < roots.len(),
            widths[index].is_none(),
            ({
                let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
                ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int)
            }),
        ensures types@[index] == roots[index],
    {
        let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
        ordinary_call_excludes_special_forms(source.text, parsed.syntax.forms@,
            row.expression.start as int, row.expression.end as int);
        let outputs = self.successful_atom_step(file, entry, limit, source, parsed, wiring, widths, roots, types, index);
        assert(atom_type_step(self, file, limit, source, parsed, entry as int,
            wiring, widths, outputs, roots, types@.take(index), index, Ok(types@[index])));
        reveal(atom_type_step);
    }

    pub(super) proof fn successful_selection_type(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        wiring: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>,
        types: Vec<Option<SignalType>>, index: int, shape: BitSelectionShape,
        input: SignalType, width: u64, origin: LocatedName, selection: CheckedBitSelection,
    )
        requires
            atoms_match(self, file, limit, source, parsed, entry as int, wiring, widths, roots, Ok(types)),
            0 <= index < types@.len(),
            widths[index].is_none(),
            roots.len() > 0,
            ({
                let driver = wiring.drivers.definitions@[index];
                let row = parsed.definitions@[driver.definition as int];
                let first = row.signals.start - parsed.entry_ranges@[entry as int].signals.start;
                &&& driver.result_index == 0
                &&& named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape)
                &&& signal_type_at(wiring, types@.take(index), wiring.signals@[first].driver) == Some(input)
            }),
            selection_arguments_match(source, parsed.syntax.forms@, &shape, width, &origin, Ok(selection)),
        ensures types@[index] matches Some(ty) && ty.ty == ResolvedPortType::Bits(selection.count),
    {
        let outputs = self.successful_atom_step(file, entry, limit, source, parsed, wiring, widths, roots, types, index);
        assert(atom_type_step(self, file, limit, source, parsed, entry as int,
            wiring, widths, outputs, roots, types@.take(index), index, Ok(types@[index])));
        reveal(atom_type_step);
        let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
        let root = row.expression.start;
        let forms = parsed.syntax.forms@;
        bit_selection_shape_positions(source.text, forms, root as int, shape);
        let inferred_shape = choose|candidate: BitSelectionShape|
            #[trigger] named_selection_matches(source.text, forms, root as int, candidate);
        bit_selection_shapes_agree(source.text, forms, root as int, inferred_shape, shape);
        assert(input.ty is Bits);
        let input_width = input.ty->Bits_0;
        let (inferred, _expression) = choose|inferred: CheckedBitSelection, expression: LocatedName|
            #[trigger] selection_arguments_match(source, forms, &inferred_shape, input_width, &input.origin, Ok(inferred))
            && #[trigger] is_form_location(source, forms[root as int], expression)
            && types@[index] == Some(SignalType { ty: ResolvedPortType::Bits(inferred.count), origin: expression });
        successful_selections_agree(source, forms, &shape, input_width, &input.origin, inferred,
            width, &origin, selection);
    }

    /// 裸の信号名の結果型がその駆動元の型を引き継ぐことを示す。
    pub(super) proof fn atom_bare_rhs_inherits(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        wiring: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>,
        types: Vec<Option<SignalType>>, i: int,
    )
        requires
            atoms_match(self, file, limit, source, parsed, entry as int, wiring, widths, roots, Ok(types)),
            0 <= i < types@.len(),
            ({
                let driver = wiring.drivers.definitions@[i];
                let row = parsed.definitions@[driver.definition as int];
                let root = parsed.syntax.forms@[row.expression.start as int];
                widths[i].is_none() && driver.result_index == 0 && root is Atom && root->Atom_kind is Name
            }),
        ensures ({
            let row = parsed.definitions@[wiring.drivers.definitions@[i].definition as int];
            let index = row.signals.start - parsed.entry_ranges@[entry as int].signals.start;
            &&& 0 <= index < wiring.signals@.len()
            &&& types@[i] == signal_type_at(wiring, types@.take(i), wiring.signals@[index].driver)
        }),
    {
        let outputs = self.successful_atom_step(file, entry, limit, source, parsed, wiring, widths, roots, types, i);
        assert(atom_type_step(self, file, limit, source, parsed, entry as int,
            wiring, widths, outputs, roots, types@.take(i), i, Ok(types@[i])));
        reveal(atom_type_step);
    }

    /// 保存した区間の長さが結果幅に一致し、選択範囲が入力幅に収まることを示す。
    pub(super) proof fn structure_projection_widths(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring,
        layouts: StructureLayouts, types: Seq<Option<SignalType>>, projection: StructureProjection,
    ) -> (shape: StructureExpressionShape)
        requires structure_projection_matches(self, file, entry, limit, wiring, layouts, types, projection),
        ensures ({
            let target = projection.target as int;
            let range = projection.operation.range;
            let input = signal_type_at(wiring, types.take(target), projection.input);
            let project = self.targets.project_model();
            let source = &project.sources_model()[file as int];
            let parsed = &project.circuits_model()[file as int];
            let definition = wiring.drivers.definitions@[target].definition;
            let row = parsed.definitions@[definition as int];
            let frame = parsed.entry_ranges@[entry as int];
            let first = row.signals.start - frame.signals.start;
            let forms = parsed.syntax.forms@;
            let context = StructureExpressionContext { file, entry, limit, source, parsed,
                definition: (definition - frame.definitions.start) as usize };
            &&& input.is_some() && types[target].is_some()
            &&& 0 <= first < wiring.signals@.len()
            &&& wiring.signals@[first].definition == definition && wiring.signals@[first].driver == projection.input
            &&& named_structure_expression_matches(source.text, forms, row.expression.start as int, shape)
            &&& is_form_location(source, forms[shape.input.start as int], wiring.signals@[first].site)
            &&& self.structure_expression_type_matches(&context, shape, &layouts, input->Some_0,
                Ok((types[target]->Some_0, projection.operation, projection.input_width)))
            &&& range.start < range.end <= projection.input_width
            &&& self.layout_port_width_matches(&layouts, types[target]->Some_0.ty, range.end - range.start)
            &&& self.layout_port_width_matches(&layouts, input->Some_0.ty, projection.input_width as int)
            &&& (!(shape.kind is Field) ==> range.start == 0 && range.end == projection.input_width)
        }),
    {
        reveal(structure_projection_matches);
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let target = projection.target as int;
        let definition = wiring.drivers.definitions@[target].definition;
        let row = parsed.definitions@[definition as int];
        let frame = parsed.entry_ranges@[entry as int];
        let context = StructureExpressionContext { file, entry, limit, source, parsed,
            definition: (definition - frame.definitions.start) as usize };
        let input = signal_type_at(wiring, types.take(target), projection.input)->Some_0;
        let checked = (types[target]->Some_0, projection.operation, projection.input_width);
        let shape = choose|shape: StructureExpressionShape|
            #[trigger] named_structure_expression_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape)
            && is_form_location(source, parsed.syntax.forms@[shape.input.start as int],
                wiring.signals@[row.signals.start - frame.signals.start].site)
            && self.structure_expression_type_matches(&context, shape, &layouts, input, Ok(checked));
        self.structure_expression_width_evidence(&context, shape, &layouts, input, checked);
        shape
    }

    pub(super) proof fn atom_types_keep_wiring(
        &self, file: usize, entry: usize, limit: u64, typed: FuncAtomTypes, wiring: FuncWiring,
    )
        requires
            self.func_atom_type_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
        ensures
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
            typed.types@.len() == wiring.drivers.definitions@.len(),
    {
        self.literals_preserve_arity(file, entry, limit, typed.literals);
        self.arity_preserves_wiring(file, entry, limit, typed.literals.wiring);
    }
    pub(super) fn check_atoms(
        &self, file: usize, entry: usize, _limit: u64, literals: &FuncLiteralWidths<'p, 'a>, wiring: &FuncWiring<'p, 'a>,
        roots: &[Option<SignalType<'p, 'a>>],
    ) -> (result: Result<(Vec<Option<SignalType<'p, 'a>>>, StructureProjections<'p, 'a>), FuncSignalTypeError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, _limit, Ok(FuncWiringResult::Checked(*wiring))),
            ({
                let project = self.targets.project_model();
                &&& file < project.circuits_model().len() && file < project.sources_model().len()
                &&& entry < project.circuits_model()[file as int].syntax.entries@.len()
                &&& expected_output_context(&project.sources_model()[file as int],
                    &project.circuits_model()[file as int], entry as int, wiring.drivers)
            }),
            literals.widths@.len() == wiring.drivers.definitions@.len(),
            roots@.len() == 0 || roots@.len() == wiring.drivers.definitions@.len(),
            forall|i: int| 0 <= i < roots@.len() && (#[trigger] roots@[i]).is_some()
                ==> location_in_source(roots@[i]->Some_0.origin) && self.declared_port_type(roots@[i]->Some_0.ty),
        ensures
            ({
                let project = self.targets.project_model();
                atoms_match(self, file, _limit, &project.sources_model()[file as int], &project.circuits_model()[file as int],
                    entry as int, wiring, literals.widths@, roots@, match result {
                        Ok((types, _)) => Ok(types),
                        Err(error) => Err(error),
                    })
            }),
            result matches Ok((types, projections)) ==> {
                &&& types@.len() == wiring.drivers.definitions@.len()
                &&& projections.layouts matches Some(layouts) ==> self.structure_types_match(_limit, Ok(layouts))
                &&& projections.layouts.is_none() ==> projections.entries@.len() == 0
                &&& structure_projections_in_order(projections.entries@, types@.len() as int,
                    wiring.drivers.signature.inputs@.len() as int)
                &&& projections.layouts matches Some(table) ==> forall|j: int| 0 <= j < projections.entries@.len()
                    ==> structure_projection_matches(self, file, entry, _limit, wiring, table, types@,
                        #[trigger] projections.entries@[j])
                &&& forall|target: int| 0 <= target < types@.len() &&
                    #[trigger] structure_projection_required(
                        &self.targets.project_model().sources_model()[file as int],
                        &self.targets.project_model().circuits_model()[file as int],
                        entry, wiring, literals.widths@, roots@, types@, target,
                    ) ==> exists|j: int| 0 <= j < projections.entries@.len()
                        && (#[trigger] projections.entries@[j]).target == target
            },
            result matches Err(error) ==> error is Signal
                || (roots@.len() > 0 && (error is SelectionInputType || error is SelectionArgument
                    || error is StructureLayout || error is StructureExpression)),
            result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
    {
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let outputs = index_outputs(&wiring.drivers);
        let mut layouts = None;
        let mut projections = Vec::new();
        let mut types: Vec<Option<SignalType>> = Vec::new();
        let mut i = 0;
        proof {
            reveal(typed_prefix);
            self.checked_wiring_is_func(file, entry, _limit, *wiring);
        }
        while i < wiring.drivers.definitions.len()
            invariant
                self.can_resolve(), self.func_wiring_evidence(file, entry, _limit, Ok(FuncWiringResult::Checked(*wiring))),
                *project == self.targets.project_model(),
                file < project.sources_model().len(), file < project.circuits_model().len(),
                *source == project.sources_model()[file as int], *parsed == project.circuits_model()[file as int],
                parsed_circuit_matches(*source, *parsed), entry < parsed.syntax.entries@.len(),
                expected_output_context(source, parsed, entry as int, wiring.drivers),
                output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, outputs@),
                literals.widths@.len() == wiring.drivers.definitions@.len(),
                roots@.len() == 0 || roots@.len() == wiring.drivers.definitions@.len(),
                forall|j: int| 0 <= j < roots@.len() && (#[trigger] roots@[j]).is_some()
                    ==> location_in_source(roots@[j]->Some_0.origin) && self.declared_port_type(roots@[j]->Some_0.ty),
                super::function_drivers::checked_ports_and_output_bounds(parsed.syntax.forms@, wiring.drivers),
                forall|j: int| 0 <= j < wiring.drivers.signature.inputs@.len()
                    ==> self.declared_port_type((#[trigger] wiring.drivers.signature.inputs@[j]).ty),
                forall|j: int| 0 <= j < types@.len() && (#[trigger] types@[j]).is_some()
                    ==> location_in_source(types@[j]->Some_0.origin) && self.declared_port_type(types@[j]->Some_0.ty),
                layouts matches Some(table) ==> self.structure_types_match(_limit, Ok(table)),
                layouts.is_none() ==> projections@.len() == 0,
                structure_projections_in_order(projections@, i as int, wiring.drivers.signature.inputs@.len() as int),
                layouts matches Some(table) ==> forall|j: int| 0 <= j < projections@.len()
                    ==> structure_projection_matches(self, file, entry, _limit, wiring, table, types@, #[trigger] projections@[j]),
                forall|target: int| 0 <= target < i &&
                    #[trigger] structure_projection_required(source, parsed, entry, wiring, literals.widths@, roots@, types@, target)
                    ==> exists|j: int| 0 <= j < projections@.len() && (#[trigger] projections@[j]).target == target,
                i == types@.len() <= wiring.drivers.definitions@.len(),
                typed_prefix(self, file, _limit, source, parsed, entry as int, wiring, literals.widths@, outputs@, roots@, types@),
            decreases wiring.drivers.definitions@.len() - i,
        {
            let driver = &wiring.drivers.definitions[i];
            let row = &parsed.definitions[driver.definition];
            let root = row.expression.start;
            let forms = parsed.syntax.forms.as_slice();
            let mut projection = None;
            let ghost prior_layouts = layouts;
            proof {
                reveal(atom_type_step);
                reveal(output_indices);
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, driver.definition as int);
            }
            let next = if let Some(width) = literals.widths[i] {
                Some(SignalType { ty: ResolvedPortType::Bits(width), origin: form_location(source, forms, root) })
            } else if driver.result_index == 0 && matches!(forms[root], Form::Atom { kind: AtomKind::Name, .. }) {
                proof {
                    build_bare_signal_position(source.text, &parsed.build_model(), entry as int, driver.definition as int);
                    self.checked_signal_driver(file, entry, _limit, *wiring, driver.definition, row.signals.start);
                }
                let position = row.signals.start - parsed.entry_ranges[entry].signals.start;
                let bound = &wiring.signals[position];
                proof {
                    if let OutputDriver::Definition(prior) = bound.driver {
                        assert(prior < i) by {
                            if i < prior {
                                assert(wiring.drivers.definitions@[i as int].definition
                                    <= wiring.drivers.definitions@[prior as int].definition);
                            }
                        };
                    }
                }
                let actual = inherit_type(wiring, types.as_slice(), bound.driver);
                if let (Some(resolved), Some(output)) = (&actual, outputs[i]) {
                    let port = &wiring.drivers.signature.outputs[output];
                    if !resolved.ty.is_same_type(&port.ty) {
                        let error = FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                            reference: copy_location(&bound.site),
                            expected: SignalType { ty: port.ty, origin: copy_location(&port.annotation) },
                            actual: SignalType { ty: resolved.ty, origin: copy_location(&resolved.origin) },
                        });
                        assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring, literals.widths@,
                            outputs@, roots@, types@, i as int, Err(error)));
                        return Err(error);
                    }
                }
                actual
            } else if roots.is_empty() {
                None
            } else if driver.result_index == 0 {
                if let Some(shape) = named_selection(source.text, forms, root) {
                    proof {
                        assert(named_selection_matches(source.text, forms@, root as int, shape));
                        build_selection_input_position(source.text, &parsed.build_model(), entry as int,
                            driver.definition as int, shape);
                        self.checked_signal_driver(file, entry, _limit, *wiring, driver.definition, row.signals.start);
                    }
                    let position = row.signals.start - parsed.entry_ranges[entry].signals.start;
                    let bound = &wiring.signals[position];
                    proof {
                        if let OutputDriver::Definition(prior) = bound.driver {
                            assert(prior < i) by {
                                if i < prior {
                                    assert(wiring.drivers.definitions@[i as int].definition
                                        <= wiring.drivers.definitions@[prior as int].definition);
                                }
                            };
                        }
                    }
                    let input = inherit_type(wiring, types.as_slice(), bound.driver);
                    let expected = match outputs[i] {
                        Some(output) => Some(&wiring.drivers.signature.outputs[output]),
                        None => None,
                    };
                    match check_selection_type(source, forms, root, &shape, input, expected) {
                        Ok(ty) => ty,
                        Err(error) => {
                            assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring, literals.widths@,
                                outputs@, roots@, types@, i as int, Err(error)));
                            return Err(error);
                        },
                    }
                } else if let Some(shape) = named_structure_expression(source.text, forms, root) {
                    proof {
                        assert(named_structure_expression_matches(source.text, forms@, root as int, shape));
                        build_structure_input_position(source.text, &parsed.build_model(), entry as int,
                            driver.definition as int, shape);
                        self.checked_signal_driver(file, entry, _limit, *wiring, driver.definition, row.signals.start);
                    }
                    let position = row.signals.start - parsed.entry_ranges[entry].signals.start;
                    let bound = &wiring.signals[position];
                    proof {
                        if let OutputDriver::Definition(prior) = bound.driver {
                            assert(prior < i) by {
                                if i < prior {
                                    assert(wiring.drivers.definitions@[i as int].definition
                                        <= wiring.drivers.definitions@[prior as int].definition);
                                }
                            };
                        }
                    }
                    let input = inherit_type(wiring, types.as_slice(), bound.driver);
                    let expected = match outputs[i] {
                        Some(output) => Some(&wiring.drivers.signature.outputs[output]),
                        None => None,
                    };
                    let context = StructureExpressionContext {
                        file, entry, limit: _limit, source, parsed,
                        definition: driver.definition - parsed.entry_ranges[entry].definitions.start,
                    };
                    let ghost expected_type = match expected { Some(port) => Some(*port), None => None };
                    if let Some(input) = input {
                        if layouts.is_none() {
                            match self.check_structure_types(context.limit) {
                                Ok(table) => layouts = Some(table),
                                Err(error) => {
                                    let error = FuncSignalTypeError::StructureLayout(error);
                                    assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring,
                                        literals.widths@, outputs@, roots@, types@, i as int, Err(error)));
                                    return Err(error);
                                }
                            }
                        }
                        let Some(table) = &layouts else { unreachable!() };
                        assert(self.structure_types_match(context.limit, Ok(*table)));
                        let checked = match self.check_structure_expression_type(&context, &shape, table, input) {
                            Ok(checked) => checked,
                            Err(error) => {
                                let error = FuncSignalTypeError::StructureExpression(error);
                                assert(structure_atom_step(self, &context, shape, Some(input), expected_type, Err(error))) by {
                                    assert(self.structure_expression_type_matches(&context, shape, table, input, Err(error->StructureExpression_0)));
                                };
                                assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring,
                                    literals.widths@, outputs@, roots@, types@, i as int, Err(error)));
                                return Err(error);
                            },
                        };
                        let actual = checked.0;
                        if let Some(port) = expected {
                            if !actual.ty.is_same_type(&port.ty) {
                                let error = FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                                    reference: copy_location(&actual.origin),
                                    expected: SignalType { ty: port.ty, origin: copy_location(&port.annotation) },
                                    actual,
                                });
                                assert(structure_atom_step(self, &context, shape, Some(input), expected_type, Err(error))) by {
                                    assert(self.structure_expression_type_matches(&context, shape, table, input, Ok(checked)));
                                };
                                assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring,
                                    literals.widths@, outputs@, roots@, types@, i as int, Err(error)));
                                return Err(error);
                            }
                        }
                        assert(structure_atom_step(self, &context, shape, Some(input), expected_type, Ok(Some(actual)))) by {
                            assert(self.structure_expression_type_matches(&context, shape, table, input, Ok(checked)));
                        };
                        let stored = StructureProjection {
                            target: i, input: bound.driver, operation: checked.1, input_width: checked.2,
                        };
                        assert(structure_projection_matches(
                            self, file, entry, _limit, wiring, *table, types@.push(Some(actual)), stored,
                        )) by {
                            reveal(structure_projection_matches);
                            assert(types@.push(Some(actual)).take(i as int) =~= types@);
                        };
                        projection = Some(stored);
                        Some(actual)
                    } else {
                        None
                    }
                } else {
                    copy_signal_type(&roots[i])
                }
            } else {
                copy_signal_type(&roots[i])
            };
            assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring, literals.widths@,
                outputs@, roots@, types@, i as int, Ok(next)));
            assert(next matches Some(ty) ==> location_in_source(ty.origin) && self.declared_port_type(ty.ty));
            assert(structure_projection_required(source, parsed, entry, wiring, literals.widths@, roots@, types@, i as int)
                ==> projection.is_some()) by {
                reveal(structure_projection_required);
            };
            let ghost before = types@;
            let ghost prior = projections@;
            types.push(next);
            if let Some(row) = projection {
                projections.push(row);
                assert(structure_projections_in_order(projections@, i + 1, wiring.drivers.signature.inputs@.len() as int)) by {
                    assert(projections@ =~= prior.push(row));
                };
            }
            proof {
                assert forall|target: int| 0 <= target <= i &&
                    #[trigger] structure_projection_required(source, parsed, entry, wiring, literals.widths@, roots@, types@, target)
                    implies exists|j: int| 0 <= j < projections@.len() && (#[trigger] projections@[j]).target == target by {
                    assert(types@.take(target) =~= before.take(target));
                    assert(structure_projection_required(source, parsed, entry, wiring, literals.widths@, roots@, before, target)) by {
                        reveal(structure_projection_required);
                    };
                    if target < i {
                        let j = choose|j: int| 0 <= j < prior.len() && (#[trigger] prior[j]).target == target;
                        assert(projections@[j] == prior[j]);
                    } else {
                        assert(projection.is_some());
                        assert(projections@[prior.len() as int].target == i);
                    }
                };
                assert forall|j: int| 0 <= j < projections@.len() && layouts.is_some()
                    implies structure_projection_matches(self, file, entry, _limit, wiring,
                        layouts->Some_0, types@, #[trigger] projections@[j]) by {
                    if j < prior.len() {
                        assert(prior_layouts == layouts);
                        let old_row = prior[j];
                        assert(structure_projection_matches(self, file, entry, _limit, wiring, layouts->Some_0, before, old_row));
                        assert(structure_projection_matches(self, file, entry, _limit, wiring, layouts->Some_0, types@, old_row)) by {
                            reveal(structure_projection_matches);
                            assert(types@.take(old_row.target as int) =~= before.take(old_row.target as int));
                        };
                    } else {
                        assert(types@ =~= before.push(next));
                    }
                };
                reveal(typed_prefix);
                assert forall|j: int| 0 <= j < types@.len() && (#[trigger] types@[j]).is_some()
                    implies location_in_source(types@[j]->Some_0.origin) && self.declared_port_type(types@[j]->Some_0.ty) by {
                    if j < i { assert(types@[j] == before[j]); }
                };
                assert forall|j: int| 0 <= j < types@.len() implies
                    #[trigger] atom_type_step(self, file, _limit, source, parsed, entry as int, wiring, literals.widths@,
                        outputs@, roots@, types@.take(j), j, Ok(types@[j])) by {
                    if j < i {
                        assert(types@.take(j) =~= before.take(j));
                        assert(types@[j] == before[j]);
                    } else {
                        assert(j == i && types@[j] == next);
                        assert(types@.take(j) =~= before);
                    }
                };
            }
            i += 1;
        }
        Ok((types, StructureProjections { entries: projections, layouts }))
    }

    /// 検査結果が定数の型と信号の束縛に対応することを表す。
    pub closed spec fn func_atom_type_evidence(
        &self, file: usize, entry: usize, limit: u64, result: Result<FuncAtomTypes, FuncAtomTypeError>,
    ) -> bool {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        match result {
            Err(FuncAtomTypeError::Literal(error)) => self.func_literal_evidence(file, entry, limit, Err(error)),
            Ok(typed) => self.func_literal_evidence(file, entry, limit, Ok(typed.literals))
                && match typed.literals.wiring {
                    FuncWiringResult::Checked(wiring) => atoms_match(self, file, limit, source, parsed, entry as int, &wiring,
                        typed.literals.widths@, Seq::empty(), Ok(typed.types)),
                    _ => typed.types@.len() == 0,
                },
            Err(error) => exists|literals: FuncLiteralWidths| literals.wiring is Checked
                && #[trigger] self.func_literal_evidence(file, entry, limit, Ok(literals))
                && atoms_match(self, file, limit, source, parsed, entry as int, &literals.wiring->Checked_0, literals.widths@,
                    Seq::empty(), Err(FuncSignalTypeError::Signal(error))),
        }
    }

    /// `func` の定数と裸の信号参照の型を、定義順に求める。
    ///
    /// 信号の型は入力や先行定義から引き継ぐ。呼び出しや専用フォームから来る型は未確定のまま返す。
    ///
    /// # Errors
    ///
    /// 定数までの検査で見つかった診断を先に返す。その後、既知の型を持つ裸の信号参照を出力の
    /// 宣言型と照合し、定義順で最初の違反に参照・要求型・実測型の位置を添える。
    pub fn check_func_atom_types(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncAtomTypes<'p, 'a>, FuncAtomTypeError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_atom_type_evidence(file, entry, max_width, result),
    {
        let literals = match self.check_func_literal_widths(file, entry, max_width) {
            Ok(literals) => literals,
            Err(error) => return Err(FuncAtomTypeError::Literal(error)),
        };
        let FuncWiringResult::Checked(ref wiring) = literals.wiring else {
            return Ok(FuncAtomTypes { literals, types: Vec::new() });
        };
        proof {
            self.literals_preserve_arity(file, entry, max_width, literals);
            self.arity_preserves_wiring(file, entry, max_width, literals.wiring);
            self.checked_wiring_is_func(file, entry, max_width, *wiring);
        }
        let roots: &[Option<SignalType>] = &[];
        assert(roots@ =~= Seq::empty());
        match self.check_atoms(file, entry, max_width, &literals, wiring, roots) {
            Ok((types, _)) => Ok(FuncAtomTypes { literals, types }),
            Err(FuncSignalTypeError::Signal(error)) => {
                assert(self.func_atom_type_evidence(file, entry, max_width, Err(error))) by {
                    assert(self.func_literal_evidence(file, entry, max_width, Ok(literals)));
                };
                Err(error)
            },
            Err(_) => {
                proof { assert(false); }
                unreachable!()
            },
        }
    }
}

} // verus!
