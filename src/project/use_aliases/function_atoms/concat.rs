//! 連接の直下の引数を型検査し、連接式の合計幅を求める。

use super::*;
use crate::project::{ConcatResultWidthError, check_concat_result_width};
use crate::syntax::circuit::next_call_argument;
use super::super::SingleBitOperand;

#[cfg(verus_only)]
use crate::project::{concat_result_width_matches, concat_result_widths_agree};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    concat_arguments_evidence, concat_arguments_match, direct_form_in_range, expression_forest,
    expression_region, following_concat_argument, indexed_concat_argument_signal,
};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, nested_list_indices};
#[cfg(verus_only)]
use super::super::single_bit_func::{
    indexed_name_is_operand, no_operand, operand_excludes_missing, operand_matches, operand_transfers,
    single_bit_driver_available, single_bit_operand_available, source_operand_is_atom, source_operands_agree,
};

verus! {

/// 同じスナップショットの定義と、先行する駆動元を指定する。
pub(super) struct ConcatContext<'w, 'p, 'a> {
    pub(super) file: usize,
    pub(super) entry: usize,
    pub(super) limit: u64,
    pub(super) source: &'p ProjectSource<'a>,
    pub(super) parsed: &'p NamedBuildCircuit<'a>,
    pub(super) wiring: &'w FuncWiring<'p, 'a>,
    pub(super) index: usize,
}

spec fn argument_type(
    context: &ConcatContext, prior: Seq<Option<SignalType>>, at: int, result: Result<Option<u64>, SignalType>,
) -> bool {
    let definition = context.wiring.drivers.definitions@[context.index as int].definition;
    let source = context.source;
    let parsed = context.parsed;
    let wiring = context.wiring;
    let entry = context.entry;
    ||| !(parsed.syntax.forms@[at] matches Form::Atom { kind: AtomKind::Name, .. })
        && no_operand(source, parsed, entry, definition, at, wiring, context.index as int) && result == Ok(None)
    ||| exists|operand: SingleBitOperand|
        #[trigger] operand_matches(source, parsed, entry, definition, at, wiring, context.index as int, operand)
        && result == type_for_argument(context, prior, operand)
}

spec fn type_for_argument<'p, 'a>(
    context: &ConcatContext<'_, 'p, 'a>, prior: Seq<Option<SignalType<'p, 'a>>>, operand: SingleBitOperand,
) -> Result<Option<u64>, SignalType<'p, 'a>> {
    match operand {
        SingleBitOperand::Constant(_) => Ok(Some(1)),
        SingleBitOperand::Driver(driver) => match signal_type_at(context.wiring, prior, driver) {
            None => Ok(None),
            Some(signal) => match signal.ty {
                ResolvedPortType::Bits(width) => Ok(Some(width)),
                _ => Err(signal),
            },
        },
    }
}

type ConcatArgument<'p, 'a> = Result<Option<(SingleBitOperand, u64)>, SignalType<'p, 'a>>;

spec fn argument_width<'p, 'a>(result: ConcatArgument<'p, 'a>) -> Result<Option<u64>, SignalType<'p, 'a>> {
    match result {
        Ok(Some((_, width))) => Ok(Some(width)),
        Ok(None) => Ok(None),
        Err(actual) => Err(actual),
    }
}

spec fn argument_projection(
    context: &ConcatContext, prior: Seq<Option<SignalType>>, at: int, item: (SingleBitOperand, u64),
) -> bool {
    let definition = context.wiring.drivers.definitions@[context.index as int].definition;
    &&& operand_matches(context.source, context.parsed, context.entry, definition, at,
        context.wiring, context.index as int, item.0)
    &&& single_bit_operand_available(item.0, context.wiring.drivers.signature.inputs@.len(), context.index as nat)
    &&& type_for_argument(context, prior, item.0) == Ok(Some(item.1))
}

proof fn argument_types_agree(
    left: &ConcatContext, right: &ConcatContext, prior: Seq<Option<SignalType>>, at: int,
    a: Result<Option<u64>, SignalType>, b: Result<Option<u64>, SignalType>,
)
    requires
        left.source == right.source, left.parsed == right.parsed, left.entry == right.entry, left.index == right.index,
        left.wiring.drivers.definitions@[left.index as int].definition
            == right.wiring.drivers.definitions@[right.index as int].definition,
        left.wiring.drivers.signature.inputs@ == right.wiring.drivers.signature.inputs@,
        left.wiring.signals@ == right.wiring.signals@,
        parsed_circuit_matches(*left.source, *left.parsed),
        left.entry < left.parsed.syntax.entries@.len(), left.entry < left.parsed.entry_ranges@.len(),
        left.parsed.entry_ranges@[left.entry as int].definitions.start
            <= left.wiring.drivers.definitions@[left.index as int].definition
            < left.parsed.entry_ranges@[left.entry as int].definitions.end,
        argument_type(left, prior, at, a), argument_type(right, prior, at, b),
    ensures a == b,
{
    let source = left.source;
    let parsed = left.parsed;
    let entry = left.entry;
    let definition = left.wiring.drivers.definitions@[left.index as int].definition;
    let i = left.index as int;
    if a != b {
        if no_operand(source, parsed, entry, definition, at, left.wiring, i) && a == Ok(None) {
            let operand = choose|operand: SingleBitOperand|
                #[trigger] operand_matches(source, parsed, entry, definition, at, right.wiring, i, operand)
                && b == type_for_argument(right, prior, operand);
            operand_transfers(source, parsed, entry, definition, at, right.wiring, left.wiring, i, operand);
            operand_excludes_missing(source, parsed, entry, definition, at, left.wiring, i, operand);
        } else if no_operand(source, parsed, entry, definition, at, right.wiring, i) && b == Ok(None) {
            let operand = choose|operand: SingleBitOperand|
                #[trigger] operand_matches(source, parsed, entry, definition, at, left.wiring, i, operand)
                && a == type_for_argument(left, prior, operand);
            operand_transfers(source, parsed, entry, definition, at, left.wiring, right.wiring, i, operand);
            operand_excludes_missing(source, parsed, entry, definition, at, right.wiring, i, operand);
        } else {
            let x = choose|operand: SingleBitOperand|
                #[trigger] operand_matches(source, parsed, entry, definition, at, left.wiring, i, operand)
                && a == type_for_argument(left, prior, operand);
            let y = choose|operand: SingleBitOperand|
                #[trigger] operand_matches(source, parsed, entry, definition, at, right.wiring, i, operand)
                && b == type_for_argument(right, prior, operand);
            source_operands_agree(source, parsed, entry, definition, at, left.wiring, right.wiring, i, x, y);
        }
    }
}

/// 引数の区間を飛ばすと、次の直下の引数または引数列の末尾に進む。
spec fn argument_end(forms: Seq<Form>, index: int) -> int {
    match forms[index] {
        Form::Atom { .. } => index + 1,
        Form::List { end, .. } => end as int,
    }
}

#[verifier::opaque]
spec fn checked_prefix(
    context: &ConcatContext, prior: Seq<Option<SignalType>>, arguments: core::ops::Range<usize>,
    cursor: usize, starts: Seq<usize>, widths: Seq<Option<u64>>,
) -> bool {
    let forms = context.parsed.syntax.forms@;
    &&& arguments.start <= cursor <= arguments.end <= forms.len()
    &&& starts.len() == widths.len()
    &&& cursor == if starts.len() == 0 { arguments.start as int } else { argument_end(forms, starts.last() as int) }
    &&& starts.len() > 0 ==> starts[0] == arguments.start
    &&& forall|i: int| 0 <= i < starts.len() ==> {
        let at = #[trigger] starts[i] as int;
        &&& arguments.start <= at < argument_end(forms, at) <= cursor
        &&& i + 1 < starts.len() ==> argument_end(forms, at) == starts[i + 1]
        &&& argument_type(context, prior, at, Ok(widths[i]))
    }
}

pub(super) closed spec fn concat_operands_match(
    context: &ConcatContext, prior: Seq<Option<SignalType>>, arguments: core::ops::Range<usize>,
    operands: Seq<(SingleBitOperand, u64)>, width: u64,
) -> bool {
    let definition = context.wiring.drivers.definitions@[context.index as int].definition;
    let root = context.parsed.definitions@[definition as int].expression.start;
    &&& concat_arguments_match(context.source.text, context.parsed.syntax.forms@, root as int, arguments)
    &&& 0 < operands.len()
    &&& crate::project::concat_prefix_width(operands.map_values(|item: (SingleBitOperand, u64)| item.1),
        operands.len()) == width
    &&& exists|starts: Seq<usize>, known: Seq<Option<u64>>|
        #[trigger] checked_prefix(context, prior, arguments, arguments.end, starts, known)
        && operands.len() == starts.len()
        && (forall|j: int| 0 <= j < operands.len() ==> {
            let item = #[trigger] operands[j];
            item.1 > 0 && known[j] == Some(item.1) && argument_projection(context, prior, starts[j] as int, item)
        })
}

pub(super) proof fn concat_operands_evidence(
    context: &ConcatContext, prior: Seq<Option<SignalType>>, arguments: core::ops::Range<usize>,
    operands: Seq<(SingleBitOperand, u64)>, width: u64,
)
    requires concat_operands_match(context, prior, arguments, operands, width),
    ensures
        operands.len() > 0,
        crate::project::concat_prefix_width(operands.map_values(|item: (SingleBitOperand, u64)| item.1), operands.len()) == width,
        forall|i: int| 0 <= i < operands.len() ==> {
            let (operand, bits) = #[trigger] operands[i];
            &&& bits > 0
            &&& single_bit_operand_available(operand, context.wiring.drivers.signature.inputs@.len(), context.index as nat)
            &&& match operand {
                SingleBitOperand::Constant(_) => bits == 1,
                SingleBitOperand::Driver(driver) =>
                    signal_type_at(context.wiring, prior, driver) matches Some(ty) && ty.ty == ResolvedPortType::Bits(bits),
            }
        },
{
    let (starts, known) = choose|starts: Seq<usize>, known: Seq<Option<u64>>|
        #[trigger] checked_prefix(context, prior, arguments, arguments.end, starts, known)
        && operands.len() == starts.len()
        && (forall|j: int| 0 <= j < operands.len() ==> {
            let item = #[trigger] operands[j];
            item.1 > 0 && known[j] == Some(item.1) && argument_projection(context, prior, starts[j] as int, item)
        });
    assert forall|i: int| 0 <= i < operands.len() implies {
        let (operand, bits) = #[trigger] operands[i];
        &&& bits > 0
        &&& single_bit_operand_available(operand, context.wiring.drivers.signature.inputs@.len(), context.index as nat)
        &&& match operand {
            SingleBitOperand::Constant(_) => bits == 1,
            SingleBitOperand::Driver(driver) =>
                signal_type_at(context.wiring, prior, driver) matches Some(ty) && ty.ty == ResolvedPortType::Bits(bits),
        }
    } by {
        let item = operands[i];
        assert(argument_projection(context, prior, starts[i] as int, item));
    };
}

proof fn atom_argument_position(forms: Seq<Form>, starts: Seq<usize>, first: usize, i: int)
    requires
        0 <= i < starts.len(), starts[0] == first,
        forall|j: int| 0 <= j < starts.len() ==> forms[(#[trigger] starts[j]) as int] is Atom,
        forall|j: int| 0 <= j && j + 1 < starts.len() ==> argument_end(forms, #[trigger] starts[j] as int) == starts[j + 1],
    ensures starts[i] == first + i,
    decreases i,
{
    if i > 0 {
        atom_argument_position(forms, starts, first, i - 1);
        assert(argument_end(forms, starts[i - 1] as int) == starts[i]);
    }
}

/// 保持した各引数が、元の連接式のどのアトムに対応するかを示す。
pub(super) proof fn concat_operand_positions(
    context: &ConcatContext, prior: Seq<Option<SignalType>>, arguments: core::ops::Range<usize>,
    operands: Seq<(SingleBitOperand, u64)>, width: u64,
)
    requires concat_operands_match(context, prior, arguments, operands, width),
    ensures
        concat_arguments_match(context.source.text, context.parsed.syntax.forms@,
            context.parsed.definitions@[context.wiring.drivers.definitions@[context.index as int].definition as int].expression.start as int,
            arguments),
        operands.len() == arguments.end - arguments.start,
        forall|j: int| 0 <= j < operands.len() ==>
            operand_matches(context.source, context.parsed, context.entry,
                context.wiring.drivers.definitions@[context.index as int].definition,
                arguments.start + j, context.wiring, context.index as int, (#[trigger] operands[j]).0),
{
    let (starts, known) = choose|starts: Seq<usize>, known: Seq<Option<u64>>|
        #[trigger] checked_prefix(context, prior, arguments, arguments.end, starts, known)
        && operands.len() == starts.len()
        && (forall|j: int| 0 <= j < operands.len() ==> {
            let item = #[trigger] operands[j];
            item.1 > 0 && known[j] == Some(item.1) && argument_projection(context, prior, starts[j] as int, item)
        });
    reveal(checked_prefix);
    let forms = context.parsed.syntax.forms@;
    let definition = context.wiring.drivers.definitions@[context.index as int].definition;
    assert forall|j: int| 0 <= j < starts.len() implies forms[(#[trigger] starts[j]) as int] is Atom by {
        let item = operands[j];
        assert(argument_projection(context, prior, starts[j] as int, item));
        source_operand_is_atom(context.source, context.parsed, context.entry, definition, starts[j] as int,
            context.wiring, context.index as int, item.0);
    };
    assert forall|j: int| 0 <= j && j + 1 < starts.len() implies
        argument_end(forms, #[trigger] starts[j] as int) == starts[j + 1] by {};
    assert forall|j: int| 0 <= j < operands.len() implies
        operand_matches(context.source, context.parsed, context.entry, definition, arguments.start + j,
            context.wiring, context.index as int, (#[trigger] operands[j]).0) by {
        atom_argument_position(forms, starts, arguments.start, j);
    };
    let last = (starts.len() - 1) as int;
    atom_argument_position(forms, starts, arguments.start, last);
    assert(starts[last] == starts.last());
    assert(forms[starts[last] as int] is Atom);
}

/// 各開始位置は、その直前のフォームの末尾から一意に決まる。
proof fn concat_prefix_position_agrees(
    context: &ConcatContext, other: &ConcatContext, prior: Seq<Option<SignalType>>, arguments: core::ops::Range<usize>,
    cursor: usize, left: Seq<usize>, left_widths: Seq<Option<u64>>,
    right: Seq<usize>, right_widths: Seq<Option<u64>>, i: int,
)
    requires
        checked_prefix(context, prior, arguments, cursor, left, left_widths),
        checked_prefix(other, prior, arguments, cursor, right, right_widths),
        context.parsed == other.parsed,
        0 <= i < left.len(), i < right.len(),
    ensures left[i] == right[i],
    decreases i,
{
    reveal(checked_prefix);
    let forms = context.parsed.syntax.forms@;
    if i > 0 {
        concat_prefix_position_agrees(context, other, prior, arguments, cursor, left, left_widths, right, right_widths, i - 1);
        assert(left[i] == argument_end(forms, left[i - 1] as int));
        assert(right[i] == argument_end(forms, right[i - 1] as int));
    }
}

/// 同じ位置まで走査すると、直下の引数の開始位置と個数が一致する。
proof fn concat_prefix_positions_agree(
    context: &ConcatContext, other: &ConcatContext, prior: Seq<Option<SignalType>>, arguments: core::ops::Range<usize>,
    cursor: usize, left: Seq<usize>, left_widths: Seq<Option<u64>>,
    right: Seq<usize>, right_widths: Seq<Option<u64>>,
)
    requires
        checked_prefix(context, prior, arguments, cursor, left, left_widths),
        checked_prefix(other, prior, arguments, cursor, right, right_widths),
        context.parsed == other.parsed,
    ensures left == right,
{
    reveal(checked_prefix);
    let forms = context.parsed.syntax.forms@;
    let i = if left.len() <= right.len() { left.len() as int } else { right.len() as int };
    if i == left.len() && i < right.len() {
        if i > 0 {
            concat_prefix_position_agrees(context, other, prior, arguments, cursor, left, left_widths, right, right_widths, i - 1);
            assert(right[i] == argument_end(forms, right[i - 1] as int));
        }
        assert(right[i] == cursor);
        assert(right[i] < cursor);
    } else if i == right.len() && i < left.len() {
        if i > 0 {
            concat_prefix_position_agrees(context, other, prior, arguments, cursor, left, left_widths, right, right_widths, i - 1);
            assert(left[i] == argument_end(forms, left[i - 1] as int));
        }
        assert(left[i] == cursor);
        assert(left[i] < cursor);
    }
    assert forall|j: int| 0 <= j < left.len() implies #[trigger] left[j] == right[j] by {
        concat_prefix_position_agrees(context, other, prior, arguments, cursor, left, left_widths, right, right_widths, j);
    };
    assert(left =~= right);
}

pub(super) open spec fn expected_value<'p, 'a>(expected: Option<&TypedPort<'p, 'a>>) -> Option<TypedPort<'p, 'a>> {
    match expected { Some(port) => Some(*port), None => None }
}

/// 同じ結線から得た幅を照合し、連接式の結果型が一致することを示す。
pub(super) proof fn concat_successes_agree(
    left: &ConcatContext, right: &ConcatContext, prior: Seq<Option<SignalType>>,
    root: usize, arguments: core::ops::Range<usize>, expected: Option<TypedPort>,
    a: Option<SignalType>, b: Option<SignalType>,
)
    requires
        left.source == right.source, left.parsed == right.parsed, left.entry == right.entry,
        left.index == right.index, left.limit == right.limit,
        left.wiring.drivers.definitions@[left.index as int].definition
            == right.wiring.drivers.definitions@[right.index as int].definition,
        left.wiring.drivers.signature.inputs@ == right.wiring.drivers.signature.inputs@,
        left.wiring.signals@ == right.wiring.signals@,
        parsed_circuit_matches(*left.source, *left.parsed),
        left.entry < left.parsed.syntax.entries@.len(), left.entry < left.parsed.entry_ranges@.len(),
        left.parsed.entry_ranges@[left.entry as int].definitions.start
            <= left.wiring.drivers.definitions@[left.index as int].definition
            < left.parsed.entry_ranges@[left.entry as int].definitions.end,
        concat_atom_step(left, prior, root, arguments, expected, Ok(a)),
        concat_atom_step(right, prior, root, arguments, expected, Ok(b)),
    ensures a == b,
{
    reveal(concat_atom_step);
    let (ls, lw) = choose|s: Seq<usize>, w: Seq<Option<u64>>|
        #[trigger] checked_prefix(left, prior, arguments, arguments.end, s, w)
        && completed_arguments(left, expected, w, root, Ok(a));
    let (rs, rw) = choose|s: Seq<usize>, w: Seq<Option<u64>>|
        #[trigger] checked_prefix(right, prior, arguments, arguments.end, s, w)
        && completed_arguments(right, expected, w, root, Ok(b));
    concat_prefix_positions_agree(left, right, prior, arguments, arguments.end, ls, lw, rs, rw);
    reveal(checked_prefix);
    assert forall|i: int| 0 <= i < lw.len() implies #[trigger] lw[i] == rw[i] by {
        assert(ls[i] == rs[i]);
        argument_types_agree(left, right, prior, ls[i] as int, Ok(lw[i]), Ok(rw[i]));
    };
    assert(lw =~= rw);
    if !(exists|i: int| 0 <= i < lw.len() && (#[trigger] lw[i]).is_none()) {
        let widths = Seq::new(lw.len(), |i: int| lw[i]->Some_0);
        let requested = expected_width(expected);
        let limit = width_limit(expected, left.limit);
        let form = left.parsed.syntax.forms@[root as int];
        let (x, xsite) = choose|width: Result<u64, ConcatResultWidthError>, site: LocatedName|
            #[trigger] concat_result_width_matches(widths, requested, limit, width)
            && #[trigger] is_form_location(left.source, form, site)
            && type_for_width(expected, width, site, Ok(a));
        let (y, ysite) = choose|width: Result<u64, ConcatResultWidthError>, site: LocatedName|
            #[trigger] concat_result_width_matches(widths, requested, limit, width)
            && #[trigger] is_form_location(left.source, form, site)
            && type_for_width(expected, width, site, Ok(b));
        concat_result_widths_agree(widths, requested, limit, x, y);
        assert(xsite == ysite);
    }
}

spec fn expected_width(expected: Option<TypedPort>) -> Option<u64> {
    match expected {
        Some(port) => match port.ty { ResolvedPortType::Bits(width) => Some(width), _ => None },
        None => None,
    }
}

spec fn width_limit(expected: Option<TypedPort>, limit: u64) -> u64 {
    if expected matches Some(port) && !(port.ty is Bits) { u64::MAX } else { limit }
}

spec fn finished_type_matches(
    context: &ConcatContext, expected: Option<TypedPort>, widths: Seq<u64>, root: usize,
    result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    let form = context.parsed.syntax.forms@[root as int];
    exists|width: Result<u64, ConcatResultWidthError>, site: LocatedName|
        #[trigger] concat_result_width_matches(widths, expected_width(expected), width_limit(expected, context.limit), width)
        && #[trigger] is_form_location(context.source, form, site)
        && type_for_width(expected, width, site, result)
}

spec fn type_for_width(
    expected: Option<TypedPort>, width: Result<u64, ConcatResultWidthError>, site: LocatedName,
    result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    match width {
        Err(ConcatResultWidthError::Mismatch { actual, .. }) =>
            expected matches Some(port) && result == Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                reference: site, actual: SignalType { ty: ResolvedPortType::Bits(actual), origin: site },
                expected: SignalType { ty: port.ty, origin: port.annotation },
            })),
        Err(reason) => result == Err(FuncSignalTypeError::ConcatWidth { expression: site, reason }),
        Ok(actual) => {
            let value = SignalType { ty: ResolvedPortType::Bits(actual), origin: site };
            match expected {
                Some(port) if !port_types_equal(value.ty, port.ty) =>
                    result == Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                        reference: site, actual: value, expected: SignalType { ty: port.ty, origin: port.annotation },
                    })),
                _ => result == Ok(Some(value)),
            }
        },
    }
}

#[verifier::opaque]
pub(super) closed spec fn concat_atom_step(
    context: &ConcatContext, prior: Seq<Option<SignalType>>, root: usize, arguments: core::ops::Range<usize>,
    expected: Option<TypedPort>, result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    match result {
        Err(FuncSignalTypeError::ConcatInputType { reference, actual }) =>
            exists|cursor: usize, starts: Seq<usize>, widths: Seq<Option<u64>>|
                cursor < arguments.end && #[trigger] checked_prefix(context, prior, arguments, cursor, starts, widths)
                && argument_type(context, prior, cursor as int, Err(actual))
                && is_form_location(context.source, context.parsed.syntax.forms@[cursor as int], reference),
        _ => exists|starts: Seq<usize>, widths: Seq<Option<u64>>|
            #[trigger] checked_prefix(context, prior, arguments, arguments.end, starts, widths)
            && completed_arguments(context, expected, widths, root, result),
    }
}

spec fn completed_arguments(
    context: &ConcatContext, expected: Option<TypedPort>, widths: Seq<Option<u64>>, root: usize,
    result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    if exists|i: int| 0 <= i < widths.len() && (#[trigger] widths[i]).is_none() {
        result == Ok(None)
    } else {
        finished_type_matches(context, expected, Seq::new(widths.len(), |i: int| widths[i]->Some_0), root, result)
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) open spec fn concat_context_valid(&self, context: &ConcatContext<'_, 'p, 'a>, n: int) -> bool {
        &&& self.can_resolve()
        &&& self.func_wiring_evidence(context.file, context.entry, context.limit,
            Ok(FuncWiringResult::Checked(*context.wiring)))
        &&& context.file < self.targets.project_model().sources_model().len()
        &&& context.file < self.targets.project_model().circuits_model().len()
        &&& *context.source == self.targets.project_model().sources_model()[context.file as int]
        &&& *context.parsed == self.targets.project_model().circuits_model()[context.file as int]
        &&& parsed_circuit_matches(*context.source, *context.parsed)
        &&& context.entry < context.parsed.syntax.entries@.len()
        &&& context.entry < context.parsed.entry_ranges@.len()
        &&& context.index == n < context.wiring.drivers.definitions@.len()
        &&& context.parsed.entry_ranges@[context.entry as int].definitions.start
            <= context.wiring.drivers.definitions@[context.index as int].definition
            < context.parsed.entry_ranges@[context.entry as int].definitions.end <= context.parsed.definitions@.len()
    }

    /// 直下の裸の信号名は、この定義の信号索引から駆動元を引ける。
    proof fn concat_name_is_bound(
        &self, context: &ConcatContext, arguments: core::ops::Range<usize>, at: usize,
    )
        requires
            self.concat_context_valid(context, context.index as int),
            concat_arguments_match(context.source.text, context.parsed.syntax.forms@,
                context.parsed.definitions@[context.wiring.drivers.definitions@[context.index as int].definition as int].expression.start as int,
                arguments),
            direct_form_in_range(context.parsed.syntax.forms@, arguments.start as int, arguments.end as int, at as int),
            at < context.parsed.syntax.forms@.len(),
            context.parsed.syntax.forms@[at as int] matches Form::Atom { kind: AtomKind::Name, .. },
        ensures !no_operand(context.source, context.parsed, context.entry,
            context.wiring.drivers.definitions@[context.index as int].definition, at as int, context.wiring, context.index as int),
    {
        let parsed = context.parsed;
        let source = context.source;
        let wiring = context.wiring;
        let entry = context.entry;
        let definition = wiring.drivers.definitions@[context.index as int].definition;
        parsed_index_evidence(*source, *parsed);
        let position = indexed_concat_argument_signal(source.text, &parsed.build_model(), entry as int, definition as int,
            arguments, at);
        self.checked_signal_driver(context.file, entry, context.limit, *wiring, definition, position as usize);
        self.checked_wiring_is_func(context.file, entry, context.limit, *wiring);
        let offset = position - parsed.entry_ranges@[entry as int].signals.start;
        let driver = wiring.signals@[offset].driver;
        if let OutputDriver::Definition(previous) = driver {
            if previous > context.index {
                assert(wiring.drivers.definitions@[context.index as int].definition
                    <= wiring.drivers.definitions@[previous as int].definition);
            }
            assert(previous < context.index);
        }
        assert(single_bit_driver_available(driver, wiring.drivers.signature.inputs@.len(), context.index as nat));
        indexed_name_is_operand(source, parsed, entry, definition, at as int, wiring, context.index as int, position);
        if no_operand(source, parsed, entry, definition, at as int, wiring, context.index as int) {
            operand_excludes_missing(source, parsed, entry, definition, at as int, wiring, context.index as int,
                SingleBitOperand::Driver(driver));
        }
    }

    /// 直下の引数の幅を求める。幅がまだ得られない引数では、型検査を後段に委ねる。
    fn check_concat_argument(
        &self, context: &ConcatContext<'_, 'p, 'a>, prior: &[Option<SignalType<'p, 'a>>], at: usize,
        Ghost(arguments): Ghost<core::ops::Range<usize>>,
    ) -> (result: ConcatArgument<'p, 'a>)
        requires
            self.concat_context_valid(context, prior@.len() as int),
            concat_arguments_match(context.source.text, context.parsed.syntax.forms@,
                context.parsed.definitions@[context.wiring.drivers.definitions@[context.index as int].definition as int].expression.start as int,
                arguments),
            direct_form_in_range(context.parsed.syntax.forms@, arguments.start as int, arguments.end as int, at as int),
            at < context.parsed.syntax.forms@.len(),
        ensures
            argument_type(context, prior@, at as int, argument_width(result)),
            result matches Ok(Some(item)) ==> argument_projection(context, prior@, at as int, item),
    {
        let definition = context.wiring.drivers.definitions[context.index].definition;
        let operand = self.read_single_bit_operand(
            context.file, context.entry, context.limit, context.source,
            context.parsed, at, context.wiring, definition, context.index,
        );
        proof {
            if context.parsed.syntax.forms@[at as int] matches Form::Atom { kind: AtomKind::Name, .. } {
                self.concat_name_is_bound(context, arguments, at);
                assert(operand.is_some());
            }
        }
        let result = match operand {
            None => Ok(None),
            Some(value @ SingleBitOperand::Constant(_)) => Ok(Some((value, 1))),
            Some(SingleBitOperand::Driver(driver)) => match inherit_type(context.wiring, prior, driver) {
                None => Ok(None),
                Some(signal) => match signal.ty {
                    ResolvedPortType::Bits(width) => Ok(Some((SingleBitOperand::Driver(driver), width))),
                    _ => Err(signal),
                },
            },
        };
        proof {
            if let Some(operand) = operand {
                assert(operand_matches(context.source, context.parsed, context.entry,
                    definition, at as int, context.wiring, context.index as int, operand));
            }
        }
        result
    }

    /// 合計幅が確定した連接式を出力ポートと照合する。
    fn finish_concat_type(
        &self, context: &ConcatContext<'_, 'p, 'a>, expected: Option<&TypedPort<'p, 'a>>,
        widths: &[u64], root: usize,
    ) -> (result: Result<Option<SignalType<'p, 'a>>, FuncSignalTypeError<'p, 'a>>)
        requires
            root < context.parsed.syntax.forms@.len(),
            form_spans_valid(context.source.text, context.parsed.syntax.forms@,
                context.source.text.spec_bytes().len() as int),
        ensures
            finished_type_matches(context, expected_value(expected), widths@, root, result),
            result matches Ok(Some(ty)) ==> ty.ty is Bits && location_in_source(ty.origin)
                && is_form_location(context.source, context.parsed.syntax.forms@[root as int], ty.origin)
                && ty.ty->Bits_0 == crate::project::concat_prefix_width(widths@, widths@.len()),
            result matches Ok(Some(_)) ==> forall|i: int| 0 <= i < widths@.len() ==> (#[trigger] widths@[i]) > 0,
            result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
    {
        let expression = form_location(context.source, context.parsed.syntax.forms.as_slice(), root);
        let (expected_bits, limit) = match expected {
            Some(port) => match port.ty {
                ResolvedPortType::Bits(width) => (Some(width), context.limit),
                _ => (None, u64::MAX),
            },
            None => (None, context.limit),
        };
        let measured = check_concat_result_width(widths, expected_bits, limit);
        let ghost requested = expected_value(expected);
        let ghost site = expression;
        let result = match measured {
            Err(ConcatResultWidthError::Mismatch { actual, .. }) => {
                let Some(port) = expected else { proof { assert(false); } return Ok(None); };
                Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                    reference: copy_location(&expression),
                    actual: SignalType { ty: ResolvedPortType::Bits(actual), origin: expression },
                    expected: SignalType { ty: port.ty, origin: copy_location(&port.annotation) },
                }))
            },
            Err(reason) => Err(FuncSignalTypeError::ConcatWidth { expression, reason }),
            Ok(width) => {
                let actual = SignalType { ty: ResolvedPortType::Bits(width), origin: copy_location(&expression) };
                match expected {
                    Some(port) if !matches!(port.ty, ResolvedPortType::Bits(_)) =>
                        Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                            reference: expression, actual,
                            expected: SignalType { ty: port.ty, origin: copy_location(&port.annotation) },
                        })),
                    _ => Ok(Some(actual)),
                }
            },
        };
        assert(type_for_width(requested, measured, site, result));
        assert(concat_result_width_matches(widths@, expected_width(requested), width_limit(requested, context.limit), measured));
        assert(is_form_location(context.source, context.parsed.syntax.forms@[root as int], site));
        result
    }

    /// 引数をソース順に調べ、ビット列以外の型は該当する引数の位置で報告する。
    /// 幅が未確定の引数があっても残りを調べ、既知の型に対する診断を拾う。
    pub(super) fn check_concat_type(
        &self, context: &ConcatContext<'_, 'p, 'a>, prior: &[Option<SignalType<'p, 'a>>],
        root: usize, Ghost(rhs_end): Ghost<usize>, arguments: core::ops::Range<usize>,
        expected: Option<&TypedPort<'p, 'a>>, retain: bool,
    ) -> (result: Result<(Option<SignalType<'p, 'a>>, Vec<(SingleBitOperand, u64)>), FuncSignalTypeError<'p, 'a>>)
        requires
            self.concat_context_valid(context, prior@.len() as int),
            ({
                let definition = context.wiring.drivers.definitions@[context.index as int].definition;
                let row = context.parsed.definitions@[definition as int];
                root == row.expression.start && rhs_end == row.expression.end
            }),
            root < rhs_end <= context.parsed.syntax.forms@.len(),
            expression_forest(context.source.text, context.parsed.syntax.forms@, root as int, rhs_end as int),
            concat_arguments_match(context.source.text, context.parsed.syntax.forms@, root as int, arguments),
        ensures
            concat_atom_step(context, prior@, root, arguments, expected_value(expected),
                match result { Ok((ty, _)) => Ok(ty), Err(error) => Err(error) }),
            result matches Ok((Some(ty), operands)) ==> {
                &&& ty.ty is Bits && location_in_source(ty.origin)
                    && is_form_location(context.source, context.parsed.syntax.forms@[root as int], ty.origin)
                &&& retain ==> concat_operands_match(context, prior@, arguments, operands@, ty.ty->Bits_0)
                &&& !retain ==> operands@.len() == 0
            },
            result matches Ok((None, operands)) ==> operands@.len() == 0,
            result matches Err(error) ==> error is Signal || error is ConcatInputType || error is ConcatWidth,
            result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
    {
        let forms = context.parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*context.source, *context.parsed);
            concat_arguments_evidence(context.source.text, forms@, root as int, rhs_end as int, arguments);
            reveal(checked_prefix);
            reveal(concat_atom_step);
        }
        let mut cursor = arguments.start;
        let mut deferred = false;
        let mut widths: Vec<u64> = Vec::new();
        let mut operands = Vec::<(SingleBitOperand, u64)>::new();
        let ghost mut starts = Seq::<usize>::empty();
        let ghost mut known = Seq::<Option<u64>>::empty();
        assert(checked_prefix(context, prior@, arguments, cursor, starts, known));
        while cursor < arguments.end
            invariant
                self.concat_context_valid(context, prior@.len() as int),
                forms@ == context.parsed.syntax.forms@,
                root < rhs_end <= forms@.len(),
                root == context.parsed.definitions@[context.wiring.drivers.definitions@[context.index as int].definition as int].expression.start,
                concat_arguments_match(context.source.text, forms@, root as int, arguments),
                nested_list_indices(forms@), complete_list_indices(forms@),
                form_spans_valid(context.source.text, forms@, context.source.text.spec_bytes().len() as int),
                arguments.start <= cursor <= arguments.end <= forms@.len(),
                arguments.start < arguments.end,
                cursor < arguments.end ==> direct_form_in_range(forms@, arguments.start as int, arguments.end as int, cursor as int),
                expression_region(forms@, cursor as int, arguments.end as int),
                checked_prefix(context, prior@, arguments, cursor, starts, known),
                widths@.len() == known.len(),
                forall|i: int| 0 <= i < known.len() && (#[trigger] known[i]).is_some() ==> widths@[i] == known[i]->Some_0,
                deferred <==> exists|i: int| 0 <= i < known.len() && (#[trigger] known[i]).is_none(),
                !retain ==> operands@.len() == 0,
                retain && !deferred ==> {
                    &&& operands@.len() == starts.len()
                    &&& forall|j: int| 0 <= j < operands@.len() ==> {
                        let item = #[trigger] operands@[j];
                        known[j] == Some(item.1) && argument_projection(context, prior@, starts[j] as int, item)
                    }
                },
            decreases arguments.end - cursor,
        {
            proof {
                reveal(checked_prefix);
                reveal(concat_atom_step);
            }
            let Some(argument) = next_call_argument(forms, cursor..arguments.end) else {
                proof { assert(false); }
                return Ok((None, Vec::new()));
            };
            let ghost previous_operands = operands@;
            let width = match self.check_concat_argument(context, prior, cursor, Ghost(arguments)) {
                Err(actual) => {
                    let reference = form_location(context.source, forms, cursor);
                    let ghost site = reference;
                    let ghost invalid = actual;
                    let error = FuncSignalTypeError::ConcatInputType { reference, actual };
                    assert(checked_prefix(context, prior@, arguments, cursor, starts, known)
                        && argument_type(context, prior@, cursor as int, Err(invalid))
                        && is_form_location(context.source, context.parsed.syntax.forms@[cursor as int], site));
                    assert(concat_atom_step(context, prior@, root, arguments, expected_value(expected), Err(error)));
                    return Err(error);
                },
                Ok(Some(item)) => {
                    if retain && !deferred { operands.push(item); }
                    Some(item.1)
                },
                Ok(None) => None,
            };
            let ghost was_deferred = deferred;
            if width.is_none() { deferred = true; }
            widths.push(width.unwrap_or(0));
            proof {
                following_concat_argument(context.source.text, forms@, root as int, arguments, cursor, argument.end);
                let previous = starts;
                let previous_widths = known;
                starts = starts.push(cursor);
                known = known.push(width);
                assert(known.len() == starts.len());
                assert forall|i: int| 0 <= i < starts.len() implies {
                    let at = #[trigger] starts[i] as int;
                    &&& arguments.start <= at < argument_end(forms@, at) <= argument.end
                    &&& i + 1 < starts.len() ==> argument_end(forms@, at) == starts[i + 1]
                    &&& argument_type(context, prior@, at, Ok(known[i]))
                } by {
                    if i < previous.len() {
                        assert(starts[i] == previous[i]);
                        assert(known[i] == previous_widths[i]);
                        if i + 1 == previous.len() {
                            assert(previous[i] == previous.last());
                            assert(argument_end(forms@, previous[i] as int) == cursor);
                        } else {
                            assert(starts[i + 1] == previous[i + 1]);
                        }
                    } else {
                        assert(starts[i] == cursor && known[i] == width);
                    }
                };
                if deferred {
                    let unknown = if width.is_none() { previous_widths.len() as int } else {
                        assert(was_deferred);
                        choose|i: int| 0 <= i < previous_widths.len() && (#[trigger] previous_widths[i]).is_none()
                    };
                    assert(0 <= unknown < known.len() && known[unknown].is_none());
                } else {
                    assert forall|i: int| 0 <= i < known.len() implies (#[trigger] known[i]).is_some() by {
                        if i < previous_widths.len() { assert(known[i] == previous_widths[i]); }
                    };
                    if retain {
                        assert forall|j: int| 0 <= j < operands@.len() implies {
                            let item = #[trigger] operands@[j];
                            known[j] == Some(item.1) && argument_projection(context, prior@, starts[j] as int, item)
                        } by {
                            if j < previous_operands.len() {
                                assert(operands@[j] == previous_operands[j]);
                                assert(starts[j] == previous[j] && known[j] == previous_widths[j]);
                            }
                        };
                    }
                }
                assert(checked_prefix(context, prior@, arguments, argument.end, starts, known));
            }
            cursor = argument.end;
        }
        if deferred { return Ok((None, Vec::new())); }
        let ghost requested = expected_value(expected);
        let result = self.finish_concat_type(context, expected, &widths, root);
        proof {
            assert(widths@ =~= Seq::new(known.len(), |i: int| known[i]->Some_0));
            assert(finished_type_matches(context, requested, Seq::new(known.len(), |i: int| known[i]->Some_0), root, result));
        }
        match result {
            Ok(ty) => {
                proof {
                    if retain && ty.is_some() {
                        let operand_widths = operands@.map_values(|item: (SingleBitOperand, u64)| item.1);
                        assert(operand_widths =~= widths@);
                        assert forall|j: int| 0 <= j < operands@.len() implies (#[trigger] operands@[j]).1 > 0 by {
                            assert(operands@[j].1 == widths@[j]);
                        };
                        assert(concat_operands_match(context, prior@, arguments, operands@, ty->Some_0.ty->Bits_0));
                    }
                }
                Ok((ty, operands))
            },
            Err(error) => Err(error),
        }
    }
}

} // verus!
