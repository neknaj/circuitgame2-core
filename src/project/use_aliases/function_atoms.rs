//! 定数と裸の信号名から、関数の左辺に対応する型を求める。

mod field_selection;
mod concat;

use concat::ConcatContext;
#[cfg(verus_only)]
use concat::{concat_atom_step, concat_successes_agree};
use super::function_literals::index_outputs;
use super::function_types::FuncSignalTypeError;
use super::selection_arguments::{CheckedBitSelection, check_selection_arguments, check_selection_chain, nested_named_selection};
use super::structure_types::{StructureExpressionContext, StructureLayouts, TypedStructureOperation};
#[cfg(verus_only)]
use super::selection_arguments::{
    nested_named_selection_matches, nested_named_selection_root, nested_named_selections_agree,
    selection_arguments_match, selection_chain_arguments_match,
    successful_selection_chain_counts_agree, successful_selections_agree,
};
#[cfg(verus_only)]
use super::function_literals::{output_indices, output_indices_agree};
#[cfg(verus_only)]
use super::function_drivers::same_definition_driver;
#[cfg(verus_only)]
use super::function_drivers::expected_output_context;
use super::{FuncLiteralError, FuncLiteralWidths, FuncWiring, FuncWiringResult, OutputDriver, ResolvedPortType, SingleBitOperand, UseAliases};
use crate::project::{LocatedName, ProjectSource, TypedPort};
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::{
    circuits::{parsed_circuit_matches, parsed_index_evidence, is_form_location},
    location_in_source, port_types_equal,
};
use crate::syntax::{AtomKind, Form};
use crate::syntax::circuit::{BitSelectionShape, NamedBuildCircuit, StructureExpressionShape, bit_selection_shape, structure_expression_shape};
use crate::syntax::circuit::field_selection_shape;
use crate::syntax::circuit::concat_argument_range;
#[cfg(verus_only)]
use crate::syntax::circuit::{
    bit_selection_excludes_structure, bit_selection_shape_matches, bit_selection_shape_positions, bit_selection_shapes_agree,
    build_bare_signal_position,
    bit_selection_path, bit_selection_step_root, build_definition_scope_evidence, build_field_selection_signal,
    build_selection_chain_signal, build_selection_input_position, build_structure_input_position,
    field_selection_root, field_selection_shape_matches, field_selection_shapes_agree,
    ordinary_call_at, ordinary_call_excludes_special_forms, structure_expression_matches, structure_expression_positions,
    concat_argument_ranges_agree, concat_arguments_match, concat_excludes_other_shapes,
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
    /// フィールド内の位置で指定した選択。定義の右辺全体が構造体式なら省略する。
    pub(super) selection: Option<CheckedBitSelection>,
}

/// 定義の添字と、連接する引数の構文範囲および駆動元を保持する。
pub(super) struct ConcatProjection {
    pub(super) target: usize,
    pub(super) width: u64,
    pub(super) _arguments: Ghost<core::ops::Range<usize>>,
    pub(super) operands: Vec<(SingleBitOperand, u64)>,
}

/// 定義順に集めた配線変換用の情報と、構造体の配置表。
pub(super) struct FuncProjections<'p, 'a> {
    pub(super) entries: Vec<StructureProjection>,
    pub(super) layouts: Option<StructureLayouts<'p, 'a>>,
    pub(super) concats: Vec<ConcatProjection>,
    pub(super) calls: Vec<super::call_arity::RootFunctionCall>,
    pub(super) call_arguments: super::call_arity::CallArgumentProjections,
}

pub(super) closed spec fn concat_projection_matches(
    file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
    wiring: &FuncWiring, types: Seq<Option<SignalType>>, row: ConcatProjection,
) -> bool {
    let index = row.target;
    let context = ConcatContext { file, entry, limit, source, parsed, wiring, index };
    let definition = wiring.drivers.definitions@[index as int].definition;
    let root = parsed.definitions@[definition as int].expression.start;
    &&& index < types.len() && index < wiring.drivers.definitions@.len()
    &&& wiring.drivers.definitions@[index as int].result_index == 0
    &&& definition < parsed.definitions@.len() && root < parsed.syntax.forms@.len()
    &&& types[index as int] matches Some(ty)
    &&& ty.ty matches ResolvedPortType::Bits(width)
    &&& row.width == width
    &&& is_form_location(source, parsed.syntax.forms@[root as int], ty.origin)
    &&& concat::concat_operands_match(&context, types.take(index as int), row._arguments@, row.operands@, width)
}

/// 連接行を構成する各引数の幅と、使用できる駆動元を取り出す。
pub(super) proof fn concat_projection_evidence(
    file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
    wiring: &FuncWiring, types: Seq<Option<SignalType>>, row: ConcatProjection,
) -> (bits: u64)
    requires
        concat_projection_matches(file, entry, limit, source, parsed, wiring, types, row),
    ensures ({
        let target = row.target as int;
        &&& bits == row.width
        &&& bits > 0
        &&& target < types.len() && target < wiring.drivers.definitions@.len()
        &&& types[target] matches Some(ty) && ty.ty == ResolvedPortType::Bits(bits)
        &&& row.operands@.len() > 0
        &&& crate::project::concat_prefix_width(
            row.operands@.map_values(|item: (SingleBitOperand, u64)| item.1), row.operands@.len()) == bits
        &&& forall|i: int| 0 <= i < row.operands@.len() ==> {
            let (operand, width) = #[trigger] row.operands@[i];
            &&& width > 0
            &&& super::single_bit_func::single_bit_operand_available(operand, wiring.drivers.signature.inputs@.len(), target as nat)
            &&& match operand {
                SingleBitOperand::Constant(_) => width == 1,
                SingleBitOperand::Driver(driver) =>
                    signal_type_at(wiring, types.take(target), driver) matches Some(ty) && ty.ty == ResolvedPortType::Bits(width),
            }
        }
    }),
{
    let context = ConcatContext { file, entry, limit, source, parsed, wiring, index: row.target };
    let bits = types[row.target as int]->Some_0.ty->Bits_0;
    concat::concat_operands_evidence(&context, types.take(row.target as int), row._arguments@, row.operands@, bits);
    let widths = row.operands@.map_values(|item: (SingleBitOperand, u64)| item.1);
    crate::project::concatenation::concat_prefix_width_step(widths, 0);
    crate::project::concatenation::concat_prefix_width_bounds(widths, 0, 1);
    crate::project::concatenation::concat_prefix_width_bounds(widths, 1, widths.len());
    assert(widths[0] > 0);
    bits
}

pub(super) proof fn concat_projections_order(
    file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
    wiring: &FuncWiring, types: Seq<Option<SignalType>>, rows: Seq<ConcatProjection>,
)
    requires concat_projections_match(file, entry, limit, source, parsed, wiring, types, rows),
    ensures
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).target < types.len()
            && concat_projection_matches(file, entry, limit, source, parsed, wiring, types, rows[i]),
        forall|a: int, b: int| 0 <= a < b < rows.len() ==> (#[trigger] rows[a]).target < (#[trigger] rows[b]).target,
{
}

/// 連接の引数列を厳格構文上の区間と、各位置の束縛に結び付ける。
pub(super) proof fn concat_projection_positions(
    file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
    wiring: &FuncWiring, types: Seq<Option<SignalType>>, row: ConcatProjection,
) -> (arguments: core::ops::Range<usize>)
    requires concat_projection_matches(file, entry, limit, source, parsed, wiring, types, row),
    ensures ({
        let target = row.target as int;
        let definition = wiring.drivers.definitions@[target].definition;
        let root = parsed.definitions@[definition as int].expression.start;
        &&& concat_arguments_match(source.text, parsed.syntax.forms@, root as int, arguments)
        &&& row.operands@.len() == arguments.end - arguments.start
        &&& forall|j: int| 0 <= j < row.operands@.len() ==>
            super::single_bit_func::operand_matches(source, parsed, entry, definition, arguments.start + j,
                wiring, target, (#[trigger] row.operands@[j]).0)
    }),
{
    let context = ConcatContext { file, entry, limit, source, parsed, wiring, index: row.target };
    let arguments = row._arguments@;
    concat::concat_operand_positions(&context, types.take(row.target as int), arguments, row.operands@, row.width);
    arguments
}

pub(super) closed spec fn concat_projections_match(
    file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
    wiring: &FuncWiring, types: Seq<Option<SignalType>>, rows: Seq<ConcatProjection>,
) -> bool {
    &&& forall|j: int| 0 <= j < rows.len() ==>
        concat_projection_matches(file, entry, limit, source, parsed, wiring, types, #[trigger] rows[j])
    &&& forall|a: int, b: int| 0 <= a < b < rows.len() ==> (#[trigger] rows[a]).target < (#[trigger] rows[b]).target
}

/// 型が確定した連接式だけが配線変換用の引数列を持つ。
pub(super) open spec fn concat_projection_required(
    source: &ProjectSource, parsed: &NamedBuildCircuit, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, types: Seq<Option<SignalType>>, target: int,
) -> bool {
    let driver = wiring.drivers.definitions@[target];
    let root = parsed.definitions@[driver.definition as int].expression.start;
    &&& 0 <= target < types.len() && target < wiring.drivers.definitions@.len() && target < widths.len()
    &&& driver.result_index == 0 && widths[target].is_none() && roots.len() > 0
    &&& (types[target] matches Some(ty) && ty.ty is Bits)
    &&& exists|arguments: core::ops::Range<usize>|
        #[trigger] concat_arguments_match(source.text, parsed.syntax.forms@, root as int, arguments)
}

pub(super) open spec fn concat_projections_complete(
    source: &ProjectSource, parsed: &NamedBuildCircuit, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, types: Seq<Option<SignalType>>, rows: Seq<ConcatProjection>,
) -> bool {
    forall|target: int| #[trigger] concat_projection_required(source, parsed, wiring, widths, roots, types, target)
        ==> exists|j: int| 0 <= j < rows.len() && (#[trigger] rows[j]).target == target
}

proof fn concat_root_excludes_other_atoms(source: &str, forms: Seq<Form>, root: usize, arguments: core::ops::Range<usize>)
    requires concat_arguments_match(source, forms, root as int, arguments),
    ensures
        forms[root as int] is List,
        !(exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source, forms, root as int, shape)),
        !(exists|shape: StructureExpressionShape| #[trigger] named_structure_expression_matches(source, forms, root as int, shape)),
        !(exists|steps: Seq<BitSelectionShape>, leaf: usize| #[trigger] nested_named_selection_matches(source, forms, root, steps, leaf)),
        !(exists|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
            #[trigger] field_selection_shape_matches(source, forms, root, steps, at, shape)),
{
    concat_excludes_other_shapes(source, forms, root as int, arguments);
    if exists|steps: Seq<BitSelectionShape>, leaf: usize| #[trigger] nested_named_selection_matches(source, forms, root, steps, leaf) {
        let (steps, leaf) = choose|steps: Seq<BitSelectionShape>, leaf: usize|
            #[trigger] nested_named_selection_matches(source, forms, root, steps, leaf);
        nested_named_selection_root(source, forms, root, steps, leaf);
    }
    if exists|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
        #[trigger] field_selection_shape_matches(source, forms, root, steps, at, shape)
    {
        let (steps, at, shape) = choose|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
            #[trigger] field_selection_shape_matches(source, forms, root, steps, at, shape);
        field_selection_root(source, forms, root, steps, at, shape);
    }
}

proof fn concat_projections_keep_prefix(
    file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
    wiring: &FuncWiring, types: Seq<Option<SignalType>>, next: Option<SignalType>, rows: Seq<ConcatProjection>,
)
    requires concat_projections_match(file, entry, limit, source, parsed, wiring, types, rows),
    ensures concat_projections_match(file, entry, limit, source, parsed, wiring, types.push(next), rows),
{
    assert forall|j: int| 0 <= j < rows.len() implies
        concat_projection_matches(file, entry, limit, source, parsed, wiring, types.push(next), #[trigger] rows[j]) by {
        let i = rows[j].target as int;
        assert(types.push(next).take(i) =~= types.take(i));
    };
}

fn retain_concat_projection<'p, 'a>(
    context: &ConcatContext<'_, 'p, 'a>, Ghost(prior): Ghost<Seq<Option<SignalType<'p, 'a>>>>,
    ty: &Option<SignalType<'p, 'a>>, operands: Vec<(SingleBitOperand, u64)>,
    Ghost(arguments): Ghost<core::ops::Range<usize>>, retain: bool,
) -> (row: Option<ConcatProjection>)
    requires
        context.index == prior.len() < context.wiring.drivers.definitions@.len(),
        context.wiring.drivers.definitions@[context.index as int].result_index == 0,
        ({
            let definition = context.wiring.drivers.definitions@[context.index as int].definition;
            let root = context.parsed.definitions@[definition as int].expression.start;
            &&& definition < context.parsed.definitions@.len() && root < context.parsed.syntax.forms@.len()
            &&& *ty matches Some(signal) ==> signal.ty is Bits
                && is_form_location(context.source, context.parsed.syntax.forms@[root as int], signal.origin)
                && (retain ==> concat::concat_operands_match(context, prior, arguments, operands@, signal.ty->Bits_0))
        }),
    ensures
        row.is_some() <==> retain && ty.is_some(),
        row matches Some(entry) ==> entry.target == context.index
            && concat_projection_matches(context.file, context.entry, context.limit, context.source, context.parsed,
                context.wiring, prior.push(*ty), entry),
{
    if !retain { return None; }
    if let Some(SignalType { ty: ResolvedPortType::Bits(width), .. }) = ty {
        let row = ConcatProjection { target: context.index, width: *width, _arguments: Ghost(arguments), operands };
        assert(prior.push(*ty).take(context.index as int) =~= prior);
        Some(row)
    } else {
        None
    }
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

proof fn append_structure_projection(
    rows: Seq<StructureProjection>, next: StructureProjection, count: int, inputs: int,
)
    requires
        structure_projections_in_order(rows, count, inputs),
        next.target == count,
        structure_projections_in_order(seq![next], count + 1, inputs),
    ensures structure_projections_in_order(rows.push(next), count + 1, inputs),
{
    let updated = rows.push(next);
    assert forall|j: int| 0 <= j < updated.len() implies {
        let row = #[trigger] updated[j];
        &&& row.target < count + 1
        &&& row.operation.range.start < row.operation.range.end <= row.input_width
        &&& match row.input {
            OutputDriver::Input(port) => port < inputs,
            OutputDriver::Definition(prior) => prior < row.target,
        }
    } by {
        if j < rows.len() {
            assert(updated[j] == rows[j]);
        } else {
            assert(updated[j] == seq![next][0]);
        }
    };
    assert forall|a: int, b: int| 0 <= a < b < updated.len()
        implies (#[trigger] updated[a]).target < (#[trigger] updated[b]).target by {
        if b == rows.len() {
            assert(updated[a] == rows[a] && updated[b] == next);
        } else {
            assert(updated[a] == rows[a] && updated[b] == rows[b]);
        }
    };
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
    &&& if let Some(outer) = projection.selection {
        &&& outer.fits((projection.operation.range.end - projection.operation.range.start) as u64)
        &&& exists|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape, field: SignalType|
            #![trigger field_selection_shape_matches(source.text, forms, row.expression.start, steps, at, shape),
                aliases.structure_expression_type_at_matches(&context, at, shape, &layouts, input,
                    Ok((field, projection.operation, projection.input_width)))]
            field_selection_shape_matches(source.text, forms, row.expression.start, steps, at, shape)
            && is_form_location(source, forms[shape.input.start as int], wiring.signals@[first].site)
            && aliases.structure_expression_type_at_matches(&context, at, shape, &layouts, input,
                Ok((field, projection.operation, projection.input_width)))
            && (field.ty matches ResolvedPortType::Bits(width)
                && width == projection.operation.range.end - projection.operation.range.start
                && selection_chain_arguments_match(source, forms, steps, width, field.origin, Ok(outer)))
            && signal.ty == ResolvedPortType::Bits(outer.count)
            && is_form_location(source, forms[row.expression.start as int], signal.origin)
    } else {
        exists|shape: StructureExpressionShape|
            #[trigger] named_structure_expression_matches(source.text, forms, row.expression.start as int, shape)
            && is_form_location(source, forms[shape.input.start as int], wiring.signals@[first].site)
            && aliases.structure_expression_type_matches(&context, shape, &layouts, input,
                Ok((signal, projection.operation, projection.input_width)))
    }
}

/// 通常呼び出しの右辺は、構造体式やフィールドを含む選択式として扱われない。
pub(super) proof fn ordinary_call_excludes_structure_projection(
    aliases: &UseAliases, file: usize, entry: usize, limit: u64, wiring: &FuncWiring,
    layouts: StructureLayouts, types: Seq<Option<SignalType>>, row: StructureProjection,
)
    requires ({
        let project = aliases.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let definition = wiring.drivers.definitions@[row.target as int].definition;
        let expression = parsed.definitions@[definition as int].expression;
        ordinary_call_at(source.text, parsed.syntax.forms@, expression.start as int, expression.end as int)
    }),
    ensures !structure_projection_matches(aliases, file, entry, limit, wiring, layouts, types, row),
{
    let project = aliases.targets.project_model();
    let parsed = &project.circuits_model()[file as int];
    let source = &project.sources_model()[file as int];
    let definition = wiring.drivers.definitions@[row.target as int].definition;
    let expression = parsed.definitions@[definition as int].expression;
    let forms = parsed.syntax.forms@;
    ordinary_call_excludes_special_forms(source.text, forms, expression.start as int, expression.end as int);
    reveal(structure_projection_matches);
    if structure_projection_matches(aliases, file, entry, limit, wiring, layouts, types, row) {
        if row.selection.is_some() {
            let (steps, at, shape) = choose|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
                #[trigger] field_selection_shape_matches(source.text, forms, expression.start, steps, at, shape);
            field_selection_root(source.text, forms, expression.start, steps, at, shape);
        } else {
            let shape = choose|shape: StructureExpressionShape|
                #[trigger] named_structure_expression_matches(source.text, forms, expression.start as int, shape);
            assert(structure_expression_matches(source.text, forms, expression.start as int, shape));
        }
        assert(false);
    }
}

proof fn structure_projection_survives_append(
    aliases: &UseAliases, file: usize, entry: usize, limit: u64, wiring: &FuncWiring,
    layouts: StructureLayouts, types: Seq<Option<SignalType>>, next: Option<SignalType>, projection: StructureProjection,
)
    requires structure_projection_matches(aliases, file, entry, limit, wiring, layouts, types, projection),
    ensures structure_projection_matches(aliases, file, entry, limit, wiring, layouts, types.push(next), projection),
{
    reveal(structure_projection_matches);
    assert(types.push(next).take(projection.target as int) =~= types.take(projection.target as int));
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
    &&& ((exists|shape: StructureExpressionShape| #[trigger] named_structure_expression_matches(source.text, forms, root, shape))
        || (!(exists|steps: Seq<BitSelectionShape>, leaf: usize|
                #[trigger] nested_named_selection_matches(source.text, forms, row.expression.start, steps, leaf))
            && (exists|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
                #[trigger] field_selection_shape_matches(source.text, forms, row.expression.start, steps, at, shape))))
    &&& 0 <= first < wiring.signals@.len()
    &&& signal_type_at(wiring, types.take(target), wiring.signals@[first].driver).is_some()
}

proof fn structure_requirement_survives_append(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, types: Seq<Option<SignalType>>,
    next: Option<SignalType>, target: int,
)
    requires 0 <= target <= types.len(),
    ensures structure_projection_required(source, parsed, entry, wiring, widths, roots, types, target)
        == structure_projection_required(source, parsed, entry, wiring, widths, roots, types.push(next), target),
{
    reveal(structure_projection_required);
    assert(types.push(next).take(target) =~= types.take(target));
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

pub(super) fn copy_signal_type<'p, 'a>(signal: &Option<SignalType<'p, 'a>>) -> (copy: Option<SignalType<'p, 'a>>)
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

pub(super) closed spec fn selection_type_matches(
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

pub(super) fn check_selection_type<'p, 'a>(
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
pub(super) closed spec fn nested_selection_type_matches(
    source: &ProjectSource, forms: Seq<Form>, root: usize, steps: Seq<BitSelectionShape>, leaf: usize,
    input: Option<SignalType>, expected: Option<TypedPort>, result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    match input {
        None => result == Ok(None),
        Some(input) => match input.ty {
            ResolvedPortType::Bits(width) => match result {
                Err(FuncSignalTypeError::SelectionArgument(error)) =>
                    selection_chain_arguments_match(source, forms, steps, width, input.origin, Err(error)),
                _ => exists|selection: CheckedBitSelection, expression: LocatedName|
                    #[trigger] selection_chain_arguments_match(source, forms, steps, width, input.origin, Ok(selection))
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
                && actual == input && is_form_location(source, forms[leaf as int], reference),
        },
    }
}

proof fn nested_selection_type_successes_agree(
    source: &ProjectSource, forms: Seq<Form>, root: usize, steps: Seq<BitSelectionShape>, leaf: usize,
    input: Option<SignalType>, expected: Option<TypedPort>, left: Option<SignalType>, right: Option<SignalType>,
)
    requires
        nested_selection_type_matches(source, forms, root, steps, leaf, input, expected, Ok(left)),
        nested_selection_type_matches(source, forms, root, steps, leaf, input, expected, Ok(right)),
    ensures left == right,
{
    reveal(nested_selection_type_matches);
    if let Some(input) = input {
        assert(input.ty is Bits);
        let width = input.ty->Bits_0;
        let (a, a_origin) = choose|selection: CheckedBitSelection, expression: LocatedName|
            #[trigger] selection_chain_arguments_match(source, forms, steps, width, input.origin, Ok(selection))
            && #[trigger] is_form_location(source, forms[root as int], expression)
            && left == Some(SignalType { ty: ResolvedPortType::Bits(selection.count), origin: expression });
        let (b, b_origin) = choose|selection: CheckedBitSelection, expression: LocatedName|
            #[trigger] selection_chain_arguments_match(source, forms, steps, width, input.origin, Ok(selection))
            && #[trigger] is_form_location(source, forms[root as int], expression)
            && right == Some(SignalType { ty: ResolvedPortType::Bits(selection.count), origin: expression });
        successful_selection_chain_counts_agree(source, forms, steps, width, input.origin, a, width, input.origin, b);
        assert(a_origin == b_origin);
    }
}

/// 最内段の信号型を確認し、最外段の幅を出力ポートの型と照合する。
pub(super) fn check_nested_selection_type<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], root: usize, steps: &[BitSelectionShape], leaf: usize,
    input: Option<SignalType<'p, 'a>>, expected: Option<&TypedPort<'p, 'a>>,
) -> (result: Result<Option<(SignalType<'p, 'a>, CheckedBitSelection)>, FuncSignalTypeError<'p, 'a>>)
    requires
        steps@.len() > 0,
        bit_selection_path(source.text, forms@, root, steps@, leaf),
        leaf < forms@.len(),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
        input matches Some(ty) ==> location_in_source(ty.origin),
    ensures
        nested_selection_type_matches(source, forms@, root, steps@, leaf, input,
            match expected { Some(port) => Some(*port), None => None }, match result {
                Ok(Some((ty, _))) => Ok(Some(ty)),
                Ok(None) => Ok(None),
                Err(error) => Err(error),
            }),
        result matches Ok(Some((ty, selection))) ==> {
            &&& location_in_source(ty.origin) && ty.ty == ResolvedPortType::Bits(selection.count)
            &&& is_form_location(source, forms@[root as int], ty.origin)
            &&& input matches Some(base)
            &&& base.ty matches ResolvedPortType::Bits(width)
            &&& selection_chain_arguments_match(source, forms@, steps@, width, base.origin, Ok(selection))
            &&& selection.fits(width)
        },
        result == Ok(None) ==> input.is_none(),
        result matches Err(error) ==> (error is Signal || error is SelectionInputType || error is SelectionArgument),
        result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
{
    reveal(nested_selection_type_matches);
    let Some(input) = input else { return Ok(None); };
    let ResolvedPortType::Bits(width) = input.ty else {
        let reference = form_location(source, forms, leaf);
        return Err(FuncSignalTypeError::SelectionInputType { reference, actual: input });
    };
    let checked = match check_selection_chain(source, forms, root, steps, leaf, width, &input.origin) {
        Ok(checked) => checked,
        Err(error) => return Err(FuncSignalTypeError::SelectionArgument(error)),
    };
    proof {
        assert(bit_selection_shape_matches(source.text, forms@, bit_selection_step_root(root, steps@, 0), steps@[0]));
        bit_selection_shape_positions(source.text, forms@, root as int, steps@[0]);
    }
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
    Ok(Some((actual, checked)))
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
    } else if roots.len() > 0 && driver.result_index == 0 && exists|steps: Seq<BitSelectionShape>, leaf: usize|
        #[trigger] nested_named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, leaf)
    {
        let (steps, leaf) = choose|steps: Seq<BitSelectionShape>, leaf: usize|
            #[trigger] nested_named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, leaf);
        let first = parsed.entry_ranges@[entry].signals.start;
        let bound = wiring.signals@[row.signals.start - first];
        let expected = if let Some(output) = outputs[i] {
            Some(wiring.drivers.signature.outputs@[output as int])
        } else { None };
        &&& first <= row.signals.start < first + wiring.signals@.len()
        &&& bound.definition == driver.definition
        &&& is_form_location(source, parsed.syntax.forms@[leaf as int], bound.site)
        &&& match bound.driver {
            OutputDriver::Input(input) => input < wiring.drivers.signature.inputs@.len(),
            OutputDriver::Definition(prior_index) => prior_index < prior.len(),
        }
        &&& outputs[i] matches Some(output) ==> output < wiring.drivers.signature.outputs@.len()
        &&& nested_selection_type_matches(source, parsed.syntax.forms@, row.expression.start, steps, leaf,
            signal_type_at(wiring, prior, bound.driver), expected, result)
    } else if roots.len() > 0 && driver.result_index == 0 && exists|
        steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
        #[trigger] field_selection_shape_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, at, shape)
    {
        let (steps, at, shape) = choose|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
            #[trigger] field_selection_shape_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, at, shape);
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
        &&& aliases.field_selection_atom_step(&context, row.expression.start, steps, at, shape,
            signal_type_at(wiring, prior, bound.driver), expected, result)
    } else if roots.len() > 0 && driver.result_index == 0 && exists|arguments: core::ops::Range<usize>|
        #[trigger] concat_arguments_match(source.text, parsed.syntax.forms@, row.expression.start as int, arguments)
    {
        let arguments = choose|arguments: core::ops::Range<usize>|
            #[trigger] concat_arguments_match(source.text, parsed.syntax.forms@, row.expression.start as int, arguments);
        let expected = if let Some(output) = outputs[i] {
            Some(wiring.drivers.signature.outputs@[output as int])
        } else { None };
        let context = ConcatContext { file, entry: entry as usize, limit, source, parsed, wiring, index: i as usize };
        &&& parsed_circuit_matches(*source, *parsed)
        &&& entry < parsed.syntax.entries@.len()
        &&& parsed.entry_ranges@[entry].definitions.start <= driver.definition < parsed.entry_ranges@[entry].definitions.end
        &&& outputs[i] matches Some(output) ==> output < wiring.drivers.signature.outputs@.len()
        &&& concat_atom_step(&context, prior, row.expression.start, arguments, expected, result)
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
        vstd::std_specs::vec::axiom_spec_len(&left.drivers.definitions);
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
            } else if exists|steps: Seq<BitSelectionShape>, leaf: usize|
                #[trigger] nested_named_selection_matches(source.text, forms, row.expression.start, steps, leaf)
            {
                let (steps, leaf) = choose|steps: Seq<BitSelectionShape>, leaf: usize|
                    #[trigger] nested_named_selection_matches(source.text, forms, row.expression.start, steps, leaf);
                nested_selection_type_successes_agree(source, forms, row.expression.start, steps, leaf, input, expected, a, b);
            } else if exists|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
                #[trigger] field_selection_shape_matches(source.text, forms, row.expression.start, steps, at, shape)
            {
                let (steps, at, shape) = choose|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
                    #[trigger] field_selection_shape_matches(source.text, forms, row.expression.start, steps, at, shape);
                let context = StructureExpressionContext { file, entry, limit, source, parsed,
                    definition: (driver.definition - frame.definitions.start) as usize };
                self.field_selection_types_agree(&context, row.expression.start, input, expected, steps, at, shape, a, b);
            } else if exists|arguments: core::ops::Range<usize>|
                #[trigger] concat_arguments_match(source.text, forms, row.expression.start as int, arguments)
            {
                let arguments = choose|arguments: core::ops::Range<usize>|
                    #[trigger] concat_arguments_match(source.text, forms, row.expression.start as int, arguments);
                assert(0 <= i < left.drivers.definitions@.len() <= usize::MAX);
                assert((i as usize) as int == i);
                assert(left.drivers.definitions@[i].definition == right.drivers.definitions@[i].definition);
                let l = ConcatContext { file, entry, limit, source, parsed, wiring: left, index: i as usize };
                let r = ConcatContext { file, entry, limit, source, parsed, wiring: right, index: i as usize };
                concat_successes_agree(&l, &r, prior, row.expression.start, arguments, expected, a, b);
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
        if exists|steps: Seq<BitSelectionShape>, leaf: usize|
            #[trigger] nested_named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, leaf)
        {
            let (steps, leaf) = choose|steps: Seq<BitSelectionShape>, leaf: usize|
                #[trigger] nested_named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, leaf);
            nested_named_selection_root(source.text, parsed.syntax.forms@, row.expression.start, steps, leaf);
            assert(false);
        }
        if exists|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
            #[trigger] field_selection_shape_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, at, shape)
        {
            let (steps, at, shape) = choose|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
                #[trigger] field_selection_shape_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, at, shape);
            field_selection_root(source.text, parsed.syntax.forms@, row.expression.start, steps, at, shape);
            assert(false);
        }
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

    /// 型検査に成功した選択列から、入力型と各段の検査の根拠を取り出す。
    pub(super) proof fn successful_nested_selection_type(
        &self, file: usize, entry: usize, limit: u64, source: &ProjectSource, parsed: &NamedBuildCircuit,
        wiring: &FuncWiring, widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>,
        types: Vec<Option<SignalType>>, index: int, steps: Seq<BitSelectionShape>, leaf: usize,
    ) -> (evidence: (u64, LocatedName<'p, 'a>, CheckedBitSelection))
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
                &&& nested_named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start, steps, leaf)
                &&& signal_type_at(wiring, types@.take(index), wiring.signals@[first].driver).is_some()
            }),
        ensures ({
            let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
            let first = row.signals.start - parsed.entry_ranges@[entry as int].signals.start;
            let (width, origin, selection) = evidence;
            &&& signal_type_at(wiring, types@.take(index), wiring.signals@[first].driver)
                == Some(SignalType { ty: ResolvedPortType::Bits(width), origin })
            &&& selection_chain_arguments_match(source, parsed.syntax.forms@, steps, width, origin, Ok(selection))
            &&& types@[index] matches Some(ty) && ty.ty == ResolvedPortType::Bits(selection.count)
        }),
    {
        let outputs = self.successful_atom_step(file, entry, limit, source, parsed, wiring, widths, roots, types, index);
        assert(atom_type_step(self, file, limit, source, parsed, entry as int,
            wiring, widths, outputs, roots, types@.take(index), index, Ok(types@[index])));
        reveal(atom_type_step);
        let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
        let root = row.expression.start;
        let forms = parsed.syntax.forms@;
        nested_named_selection_root(source.text, forms, root, steps, leaf);
        bit_selection_excludes_structure(source.text, forms, root as int, steps[0]);
        if exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root as int, shape) {
            let shape = choose|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root as int, shape);
            bit_selection_shapes_agree(source.text, forms, root as int, steps[0], shape);
            assert(false);
        }
        let (actual, at) = choose|actual: Seq<BitSelectionShape>, at: usize|
            #[trigger] nested_named_selection_matches(source.text, forms, root, actual, at);
        nested_named_selections_agree(source.text, forms, root, steps, leaf, actual, at);
        reveal(nested_selection_type_matches);
        let first = row.signals.start - parsed.entry_ranges@[entry as int].signals.start;
        let input = signal_type_at(wiring, types@.take(index), wiring.signals@[first].driver)->Some_0;
        assert(types@[index].is_some());
        assert(input.ty is Bits);
        let input_width = input.ty->Bits_0;
        let (inferred, _expression) = choose|inferred: CheckedBitSelection, expression: LocatedName|
            #[trigger] selection_chain_arguments_match(source, forms, steps, input_width, input.origin, Ok(inferred))
            && #[trigger] is_form_location(source, forms[root as int], expression)
            && types@[index] == Some(SignalType { ty: ResolvedPortType::Bits(inferred.count), origin: expression });
        (input_width, input.origin, inferred)
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
        requires
            structure_projection_matches(self, file, entry, limit, wiring, layouts, types, projection),
            projection.selection.is_none(),
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

    /// フィールドの配置、選択の値、元の駆動元の型が、保存した行に対応することを示す。
    pub(super) proof fn field_projection_evidence(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring,
        layouts: StructureLayouts, types: Seq<Option<SignalType>>, projection: StructureProjection,
    ) -> (evidence: (Seq<BitSelectionShape>, usize, StructureExpressionShape, SignalType<'p, 'a>))
        requires
            structure_projection_matches(self, file, entry, limit, wiring, layouts, types, projection),
            projection.selection.is_some(),
        ensures ({
            let (steps, at, shape, field) = evidence;
            let target = projection.target as int;
            let range = projection.operation.range;
            let project = self.targets.project_model();
            let source = &project.sources_model()[file as int];
            let parsed = &project.circuits_model()[file as int];
            let definition = wiring.drivers.definitions@[target].definition;
            let row = parsed.definitions@[definition as int];
            let frame = parsed.entry_ranges@[entry as int];
            let forms = parsed.syntax.forms@;
            let context = StructureExpressionContext { file, entry, limit, source, parsed,
                definition: (definition - frame.definitions.start) as usize };
            let outer = projection.selection->Some_0;
            let first = row.signals.start - frame.signals.start;
            &&& signal_type_at(wiring, types.take(target), projection.input) matches Some(input)
            &&& types[target] matches Some(signal) && signal.ty == ResolvedPortType::Bits(outer.count)
            &&& 0 <= first < wiring.signals@.len()
            &&& wiring.signals@[first].definition == definition && wiring.signals@[first].driver == projection.input
            &&& is_form_location(source, forms[shape.input.start as int], wiring.signals@[first].site)
            &&& field_selection_shape_matches(source.text, forms, row.expression.start, steps, at, shape)
            &&& self.structure_expression_type_at_matches(&context, at, shape, &layouts, input,
                Ok((field, projection.operation, projection.input_width)))
            &&& range.start < range.end <= projection.input_width
            &&& self.layout_port_width_matches(&layouts, input.ty, projection.input_width as int)
            &&& field.ty == ResolvedPortType::Bits((range.end - range.start) as u64)
            &&& outer.fits((range.end - range.start) as u64)
            &&& selection_chain_arguments_match(source, forms, steps, (range.end - range.start) as u64, field.origin, Ok(outer))
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
        let forms = parsed.syntax.forms@;
        let context = StructureExpressionContext { file, entry, limit, source, parsed,
            definition: (definition - frame.definitions.start) as usize };
        let input = signal_type_at(wiring, types.take(target), projection.input)->Some_0;
        let range = projection.operation.range;
        let outer = projection.selection->Some_0;
        let (steps, at, shape, field) = choose|
            steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape, field: SignalType|
            #![trigger field_selection_shape_matches(source.text, forms, row.expression.start, steps, at, shape),
                self.structure_expression_type_at_matches(&context, at, shape, &layouts, input,
                    Ok((field, projection.operation, projection.input_width)))]
            field_selection_shape_matches(source.text, forms, row.expression.start, steps, at, shape)
            && is_form_location(source, forms[shape.input.start as int], wiring.signals@[row.signals.start - frame.signals.start].site)
            && self.structure_expression_type_at_matches(&context, at, shape, &layouts, input,
                Ok((field, projection.operation, projection.input_width)))
            && field.ty == ResolvedPortType::Bits((range.end - range.start) as u64)
            && selection_chain_arguments_match(source, forms, steps, (range.end - range.start) as u64, field.origin, Ok(outer));
        self.structure_expression_width_at(&context, at, shape, &layouts, input,
            (field, projection.operation, projection.input_width));
        (steps, at, shape, field)
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
    /// 検査済みの先行定義から、次の定義の型と変換に使う区間を求める。
    fn check_atom_definition(
        &self, file: usize, entry: usize, _limit: u64, source: &'p ProjectSource<'a>, parsed: &'p NamedBuildCircuit<'a>,
        literals: &FuncLiteralWidths<'p, 'a>, wiring: &FuncWiring<'p, 'a>, outputs: &[Option<usize>],
        roots: &[Option<SignalType<'p, 'a>>], types: &[Option<SignalType<'p, 'a>>], i: usize,
        layouts: &mut Option<StructureLayouts<'p, 'a>>, retain_concat: bool,
    ) -> (result: Result<(Option<SignalType<'p, 'a>>, Option<StructureProjection>, Option<ConcatProjection>), FuncSignalTypeError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, _limit, Ok(FuncWiringResult::Checked(*wiring))),
            ({
                let project = self.targets.project_model();
                &&& file < project.circuits_model().len() && file < project.sources_model().len()
                &&& *source == project.sources_model()[file as int] && *parsed == project.circuits_model()[file as int]
            }),
            parsed_circuit_matches(*source, *parsed),
            entry < parsed.syntax.entries@.len(),
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
            *old(layouts) matches Some(table) ==> self.structure_types_match(_limit, Ok(table)),
            i == types@.len() < wiring.drivers.definitions@.len(),
        ensures
            old(layouts).is_some() ==> *final(layouts) == *old(layouts),
            *final(layouts) matches Some(table) ==> self.structure_types_match(_limit, Ok(table)),
            atom_type_step(self, file, _limit, source, parsed, entry as int, wiring, literals.widths@,
                outputs@, roots@, types@, i as int, match result { Ok((ty, _, _)) => Ok(ty), Err(error) => Err(error) }),
            result matches Ok((next, projection, concatenation)) ==> {
                &&& next matches Some(ty) ==> location_in_source(ty.origin) && self.declared_port_type(ty.ty)
                &&& structure_projection_required(source, parsed, entry, wiring, literals.widths@, roots@, types@, i as int)
                    ==> projection.is_some()
                &&& projection matches Some(row) ==> {
                    &&& row.target == i
                    &&& structure_projections_in_order(seq![row], i + 1, wiring.drivers.signature.inputs@.len() as int)
                    &&& *final(layouts) matches Some(table)
                    &&& structure_projection_matches(self, file, entry, _limit, wiring, table, types@.push(next), row)
                }
                &&& !retain_concat ==> concatenation.is_none()
                &&& retain_concat && concat_projection_required(source, parsed, wiring,
                    literals.widths@, roots@, types@.push(next), i as int) ==> concatenation.is_some()
                &&& concatenation matches Some(row) ==> row.target == i
                    && concat_projection_matches(file, entry, _limit, source, parsed, wiring, types@.push(next), row)
            },
            result matches Err(error) ==> error is Signal
                || (roots@.len() > 0 && (error is SelectionInputType || error is SelectionArgument || error is ConcatInputType || error is ConcatWidth
                    || error is StructureLayout || error is StructureExpression)),
            result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
    {
        let driver = &wiring.drivers.definitions[i];
        let row = &parsed.definitions[driver.definition];
        let root = row.expression.start;
        let forms = parsed.syntax.forms.as_slice();
        let mut projection = None;
        let mut concatenation = None;
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
            let actual = inherit_type(wiring, types, bound.driver);
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
                let input = inherit_type(wiring, types, bound.driver);
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
                let input = inherit_type(wiring, types, bound.driver);
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
                            Ok(table) => *layouts = Some(table),
                            Err(error) => {
                                let error = FuncSignalTypeError::StructureLayout(error);
                                assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring,
                                    literals.widths@, outputs@, roots@, types@, i as int, Err(error)));
                                return Err(error);
                            }
                        }
                    }
                    let Some(table) = &*layouts else { unreachable!() };
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
                        target: i, input: bound.driver, operation: checked.1, input_width: checked.2, selection: None,
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
            } else if let Some((steps, leaf)) = nested_named_selection(source.text, forms, root) {
                proof {
                    let (spec_steps, spec_leaf) = choose|candidate: Seq<BitSelectionShape>, at: usize|
                        #[trigger] nested_named_selection_matches(source.text, forms@, root, candidate, at);
                    assert(spec_steps == steps@ && spec_leaf == leaf);
                    reveal(nested_named_selection_matches);
                    build_selection_chain_signal(source.text, &parsed.build_model(), entry as int,
                        driver.definition as int, steps@, leaf);
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
                let input = inherit_type(wiring, types, bound.driver);
                let expected = match outputs[i] {
                    Some(output) => Some(&wiring.drivers.signature.outputs[output]),
                    None => None,
                };
                match check_nested_selection_type(source, forms, root, steps.as_slice(), leaf, input, expected) {
                    Ok(Some((ty, _))) => Some(ty),
                    Ok(None) => None,
                    Err(error) => {
                        assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring, literals.widths@,
                            outputs@, roots@, types@, i as int, Err(error)));
                        return Err(error);
                    },
                }
            } else if let Some(field) = field_selection_shape(source.text, forms, root) {
                proof {
                    let (steps, at, shape) = choose|steps: Seq<BitSelectionShape>, at: usize, shape: StructureExpressionShape|
                        #[trigger] field_selection_shape_matches(source.text, forms@, root, steps, at, shape);
                    field_selection_shapes_agree(source.text, forms@, root,
                        field.steps@, field.field, field.shape, steps, at, shape);
                }
                let expected = match outputs[i] {
                    Some(output) => Some(&wiring.drivers.signature.outputs[output]),
                    None => None,
                };
                let context = StructureExpressionContext {
                    file, entry, limit: _limit, source, parsed,
                    definition: driver.definition - parsed.entry_ranges[entry].definitions.start,
                };
                match self.check_indexed_field_selection(&context, wiring, i, types, &field, layouts, expected) {
                    Ok(Some((ty, stored))) => {
                        projection = Some(stored);
                        Some(ty)
                    },
                    Ok(None) => None,
                    Err(error) => {
                        assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring,
                            literals.widths@, outputs@, roots@, types@, i as int, Err(error)));
                        return Err(error);
                    }
                }
            } else if let Some(arguments) = concat_argument_range(source.text, forms, root) {
                proof {
                    let selected = choose|range: core::ops::Range<usize>|
                        #[trigger] concat_arguments_match(source.text, forms@, root as int, range);
                    concat_argument_ranges_agree(source.text, forms@, root as int, arguments, selected);
                }
                let expected = match outputs[i] {
                    Some(output) => Some(&wiring.drivers.signature.outputs[output]),
                    None => None,
                };
                let context = ConcatContext { file, entry, limit: _limit, source, parsed, wiring, index: i };
                let ghost argument_range = arguments;
                match self.check_concat_type(&context, types, root, Ghost(row.expression.end), arguments, expected, retain_concat) {
                    Ok((ty, operands)) => {
                        concatenation = retain_concat_projection(&context, Ghost(types@), &ty, operands, Ghost(argument_range), retain_concat);
                        ty
                    },
                    Err(error) => {
                        assert(atom_type_step(self, file, _limit, source, parsed, entry as int, wiring,
                            literals.widths@, outputs@, roots@, types@, i as int, Err(error)));
                        return Err(error);
                    },
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
        proof {
            if retain_concat && concat_projection_required(source, parsed, wiring,
                literals.widths@, roots@, types@.push(next), i as int)
            {
                let args = choose|args: core::ops::Range<usize>|
                    #[trigger] concat_arguments_match(source.text, forms@, root as int, args);
                concat_root_excludes_other_atoms(source.text, forms@, root, args);
                assert(concatenation.is_some());
            }
            if let Some(row) = &projection {
                assert(structure_projections_in_order(seq![*row], i + 1, wiring.drivers.signature.inputs@.len() as int));
            }
        }
        Ok((next, projection, concatenation))
    }

    pub(super) fn check_atoms(
        &self, file: usize, entry: usize, _limit: u64, literals: &FuncLiteralWidths<'p, 'a>, wiring: &FuncWiring<'p, 'a>,
        roots: &[Option<SignalType<'p, 'a>>], retain_concat: bool,
    ) -> (result: Result<(Vec<Option<SignalType<'p, 'a>>>, FuncProjections<'p, 'a>), FuncSignalTypeError<'p, 'a>>)
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
                &&& !retain_concat ==> projections.concats@.len() == 0
                &&& concat_projections_match(file, entry, _limit, &self.targets.project_model().sources_model()[file as int],
                    &self.targets.project_model().circuits_model()[file as int], wiring, types@, projections.concats@)
                &&& retain_concat ==> concat_projections_complete(
                    &self.targets.project_model().sources_model()[file as int], &self.targets.project_model().circuits_model()[file as int],
                    wiring, literals.widths@, roots@, types@, projections.concats@)
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
                || (roots@.len() > 0 && (error is SelectionInputType || error is SelectionArgument || error is ConcatInputType || error is ConcatWidth
                    || error is StructureLayout || error is StructureExpression)),
            result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
    {
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let outputs = index_outputs(&wiring.drivers);
        let mut layouts = None;
        let mut projections = Vec::new();
        let mut concats = Vec::new();
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
                !retain_concat ==> concats@.len() == 0,
                concat_projections_match(file, entry, _limit, source, parsed, wiring, types@, concats@),
                retain_concat ==> concat_projections_complete(source, parsed, wiring, literals.widths@, roots@, types@, concats@),
                typed_prefix(self, file, _limit, source, parsed, entry as int, wiring, literals.widths@, outputs@, roots@, types@),
            decreases wiring.drivers.definitions@.len() - i,
        {
            let ghost prior_layouts = layouts;
            let (next, projection, concatenation) = self.check_atom_definition(
                file, entry, _limit, source, parsed, literals, wiring, outputs.as_slice(),
                roots, types.as_slice(), i, &mut layouts, retain_concat,
            )?;
            let ghost before = types@;
            let ghost prior = projections@;
            let ghost previous_concats = concats@;
            types.push(next);
            proof { concat_projections_keep_prefix(file, entry, _limit, source, parsed, wiring, before, next, previous_concats); }
            if let Some(row) = concatenation {
                concats.push(row);
                proof {
                    assert forall|a: int, b: int| 0 <= a < b < concats@.len() implies
                        (#[trigger] concats@[a]).target < (#[trigger] concats@[b]).target by {
                        if b == previous_concats.len() {
                            assert(concats@[a] == previous_concats[a]);
                            assert(concat_projection_matches(file, entry, _limit, source, parsed, wiring, before, previous_concats[a]));
                        }
                    };
                    assert forall|j: int| 0 <= j < concats@.len() implies
                        concat_projection_matches(file, entry, _limit, source, parsed, wiring, types@, #[trigger] concats@[j]) by {
                        if j < previous_concats.len() { assert(concats@[j] == previous_concats[j]); }
                    };
                }
            }
            if let Some(row) = projection {
                projections.push(row);
                assert(structure_projections_in_order(projections@, i + 1, wiring.drivers.signature.inputs@.len() as int)) by {
                    assert(projections@ =~= prior.push(row));
                    assert(structure_projections_in_order(seq![row], i + 1, wiring.drivers.signature.inputs@.len() as int));
                    append_structure_projection(prior, row, i as int, wiring.drivers.signature.inputs@.len() as int);
                };
            }
            proof {
                if retain_concat {
                    assert forall|target: int| #[trigger] concat_projection_required(
                        source, parsed, wiring, literals.widths@, roots@, types@, target)
                        implies exists|j: int| 0 <= j < concats@.len() && (#[trigger] concats@[j]).target == target by {
                        assert(types@ =~= before.push(next));
                        if target < i {
                            assert(concat_projection_required(source, parsed, wiring, literals.widths@, roots@, before, target));
                            let j = choose|j: int| 0 <= j < previous_concats.len()
                                && (#[trigger] previous_concats[j]).target == target;
                            assert(concats@[j] == previous_concats[j]);
                        } else {
                            assert(target == i && concatenation.is_some());
                            assert(concats@[previous_concats.len() as int].target == target);
                        }
                    };
                }
                assert forall|target: int| 0 <= target <= i &&
                    #[trigger] structure_projection_required(source, parsed, entry, wiring, literals.widths@, roots@, types@, target)
                    implies exists|j: int| 0 <= j < projections@.len() && (#[trigger] projections@[j]).target == target by {
                    assert(types@ =~= before.push(next));
                    structure_requirement_survives_append(source, parsed, entry, wiring, literals.widths@, roots@, before, next, target);
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
                        assert(types@ =~= before.push(next));
                        structure_projection_survives_append(self, file, entry, _limit, wiring, layouts->Some_0, before, next, old_row);
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
        Ok((types, FuncProjections {
            entries: projections, layouts, concats, calls: Vec::new(),
            call_arguments: super::call_arity::CallArgumentProjections::new(),
        }))
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
        match self.check_atoms(file, entry, max_width, &literals, wiring, roots, false) {
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
