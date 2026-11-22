//! 展開に渡す実引数を、呼び出し先の入力ポート順で配線に変換する。

pub(super) mod child_calls;
#[cfg(verus_only)]
pub(super) mod source_wires;
#[cfg(verus_only)]
pub(in crate::project::use_aliases::bit_func) use source_wires::SourceChildModel;

use super::{append_bit_literal_wires, lower_driver_bit};
use super::super::instances::{append_instance, append_instance_to};
#[cfg(verus_only)]
use super::super::expansion::call_literal_bit;
#[cfg(verus_only)]
use super::super::instances::instance_wire_values;
#[cfg(verus_only)]
use super::port_values;
#[cfg(verus_only)]
use super::super::instances::{instance_gates_match, instance_outputs_match};
#[cfg(verus_only)]
use super::{driver_bit_available, driver_wire, driver_wire_is_available, wires_available};
#[cfg(verus_only)]
use super::{Layouts, LoweringBody, body_definition_layouts, body_driver_bits_fit_layout, definition_widths};
#[cfg(verus_only)]
use super::super::frontend::argument_matches_width;
use crate::project::use_aliases::call_arity::{CallArgumentSource, ProjectedCallArgument};
use crate::project::circuits::{form_location, read_indexed_atom};
use crate::project::{LocatedName, ProjectSource};
use crate::project::use_aliases::function_atoms::copy_location;
#[cfg(verus_only)]
use crate::project::location_in_source;
#[cfg(verus_only)]
use crate::project::circuits::is_form_location;
use crate::netlist::{NorGate, NorNetlist, PortBitLayout, Wire};
#[cfg(verus_only)]
use crate::netlist::{
    gates_available, nor_evaluation_ready, output_ports_available, port_bit_layout_port, port_bit_layout_result,
    port_bit_layout_size, preceding_port_bits, wire_available, wire_value,
};
use crate::syntax::{Form, read_bit_literal};
#[cfg(verus_only)]
use crate::syntax::{AtomKind, bare_atom_kind, bit_literal_kind_has_digits, form_span, form_spans_valid};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 実引数を変換する際に参照できる、呼び出し元の既存配線と構文木。
pub(super) struct CallerArguments<'s, 'p, 'a> {
    pub(super) source: &'p ProjectSource<'a>,
    pub(super) forms: &'s [Form],
    pub(super) inputs: &'s [Range<usize>],
    pub(super) definitions: &'s [Range<usize>],
    pub(super) wires: &'s [Wire],
    /// 定義内の参照添字ごとに、展開済みの子の出力配線範囲を保持する。
    pub(super) child_ranges: &'s [Option<Range<usize>>],
    pub(super) child_wires: &'s [Wire],
}

/// 一つの定義内で展開した子の出力を、参照添字で引くための表。
pub(super) struct ChildOutputWires {
    pub(super) ranges: Vec<Option<Range<usize>>>,
    pub(super) wires: Vec<Wire>,
}

#[cfg(verus_only)]
pub(super) open spec fn child_outputs_appended(
    before: &ChildOutputWires, after: &ChildOutputWires, reference: usize, callee: &NorNetlist,
    arguments: Seq<Wire>, old_gates: Seq<NorGate>, new_gates: Seq<NorGate>, input_bits: usize,
) -> bool {
    let start = before.wires@.len();
    let end = after.wires@.len();
    &&& reference < before.ranges@.len() && before.ranges@[reference as int].is_none()
    &&& end == start + callee.outputs@.len() <= usize::MAX
    &&& after.ranges@ == before.ranges@.update(reference as int, Some((start as usize)..(end as usize)))
    &&& after.wires@.take(start as int) == before.wires@
    &&& instance_outputs_match(callee.outputs@, arguments, old_gates.len() as usize,
        after.wires@.subrange(start as int, end as int))
    &&& instance_gates_match(old_gates, callee.gates@, arguments, new_gates)
    &&& gates_available(new_gates, input_bits as nat, new_gates.len() as int)
    &&& wires_available(after.wires@, input_bits, new_gates.len())
}

impl ChildOutputWires {
    /// 定義に属する参照数に合わせて、空の枠を用意する。
    pub(super) fn new(references: usize) -> (table: Self)
        ensures
            table.ranges@.len() == references,
            forall|i: int| 0 <= i < references ==> (#[trigger] table.ranges@[i]).is_none(),
            table.wires@.len() == 0,
    {
        let mut ranges: Vec<Option<Range<usize>>> = Vec::new();
        while ranges.len() < references
            invariant
                ranges@.len() <= references,
                forall|i: int| 0 <= i < ranges@.len() ==> (#[trigger] ranges@[i]).is_none(),
            decreases references - ranges@.len(),
        {
            let ghost previous = ranges@;
            ranges.push(None);
            assert forall|i: int| 0 <= i < ranges@.len() implies (#[trigger] ranges@[i]).is_none() by {
                if i < previous.len() { assert(ranges@[i] == previous[i]); }
            };
        }
        Self { ranges, wires: Vec::new() }
    }

    /// 子のゲートを展開し、出力の半開範囲を対応する空の枠に記録する。
    /// ゲート上限を超える場合は、ゲート列と一時配線表を保つ。
    pub(super) fn append(
        &mut self, reference: usize, gates: &mut Vec<NorGate>, callee: &NorNetlist, arguments: &[Wire],
        capacity: usize, Ghost(input_bits): Ghost<usize>,
    ) -> (added: bool)
        requires
            reference < old(self).ranges@.len(), old(self).ranges@[reference as int].is_none(),
            old(self).wires@.len() + callee.outputs@.len() <= usize::MAX,
            old(gates)@.len() <= capacity,
            gates_available(old(gates)@, input_bits as nat, old(gates)@.len() as int),
            nor_evaluation_ready(callee, arguments@.len()),
            wires_available(old(self).wires@, input_bits, old(gates)@.len()),
            wires_available(arguments@, input_bits, old(gates)@.len()),
        ensures
            added <==> old(gates)@.len() + callee.gates@.len() <= capacity,
            !added ==> final(self).ranges@ == old(self).ranges@ && final(self).wires@ == old(self).wires@
                && final(gates)@ == old(gates)@,
            added ==> child_outputs_appended(old(self), final(self), reference, callee, arguments@,
                old(gates)@, final(gates)@, input_bits),
    {
        let start = self.wires.len();
        proof { reveal(wires_available); }
        if !append_instance_to(gates, callee, arguments, &mut self.wires, capacity, Ghost(input_bits as nat)) {
            return false;
        }
        let end = self.wires.len();
        self.ranges.set(reference, Some(start..end));
        true
    }
}

pub(super) open spec fn argument_source_available(caller: &CallerArguments, source: CallArgumentSource) -> bool {
    projected_source_available(caller.child_ranges@, source)
}

pub(super) open spec fn projected_source_available(ranges: Seq<Option<Range<usize>>>, source: CallArgumentSource) -> bool {
    match source {
        CallArgumentSource::NestedCall(reference) =>
            reference < ranges.len() && ranges[reference as int].is_some(),
        _ => source.has_direct_wires(),
    }
}

pub(super) open spec fn literal_word(caller: &CallerArguments, form: usize) -> Seq<u8> {
    let span = form_span(caller.forms@[form as int]);
    caller.source.text.spec_bytes()[span.start as int..span.end as int]
}

#[verifier::opaque]
pub(super) open spec fn argument_wires_ready(caller: &CallerArguments, argument: ProjectedCallArgument, width: usize) -> bool {
    &&& layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
        caller.wires@.len() as int, argument, width)
    &&& child_argument_width_ready(caller.child_ranges@, caller.child_wires@.len(), argument.source, width)
}

pub(super) open spec fn child_argument_width_ready(
    ranges: Seq<Option<Range<usize>>>, wires: nat, source: CallArgumentSource, width: usize,
) -> bool {
    if let CallArgumentSource::NestedCall(reference) = source {
        projected_source_available(ranges, source) ==> {
            let range = ranges[reference as int]->Some_0;
            range.start <= range.end <= wires && range.end - range.start == width
        }
    } else { true }
}

pub(in crate::project::use_aliases::bit_func) open spec fn literal_argument_matches_width(
    source: &ProjectSource, forms: Seq<Form>, form: usize, width: int,
) -> bool {
    let span = form_span(forms[form as int]);
    let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
    &&& forms[form as int] is Atom
    &&& ((width == 1 && bytes.len() == 1 && (bytes[0] == b'0' || bytes[0] == b'1'))
        || bare_atom_kind(bytes) == Some(AtomKind::Binary) || bare_atom_kind(bytes) == Some(AtomKind::Hexadecimal))
}

pub(super) open spec fn layout_argument_ready(
    source: &ProjectSource, forms: Seq<Form>, inputs: Seq<Range<usize>>, definitions: Seq<Range<usize>>,
    used: int, argument: ProjectedCallArgument, width: usize,
) -> bool {
    &&& argument.form < forms.len()
    &&& match argument.source {
        CallArgumentSource::Driver(driver) => forall|bit: int| 0 <= bit < width ==>
            #[trigger] driver_bit_available(inputs, definitions, used, driver, bit),
        CallArgumentSource::Literal(bits) => width == bits
            && literal_argument_matches_width(source, forms, argument.form, width as int),
        CallArgumentSource::Deferred | CallArgumentSource::NestedCall(_) => true,
    }
}

/// 型検査で得た実引数の幅を、割り当て済みのポート範囲と先行配線に対応付ける。
pub(super) proof fn layout_argument_from_width(
    body: &LoweringBody, layouts: &Layouts, capacity: usize, first: usize, source: &ProjectSource,
    forms: Seq<Form>, argument: ProjectedCallArgument, width: u64, width_limit: u64,
)
    requires
        body_definition_layouts(body.input_widths@, body.definitions@, capacity, layouts),
        first <= body.definitions@.len(), width <= usize::MAX,
        argument_matches_width(source, forms, body.input_widths@, body.definitions@.take(first as int),
            argument, width, width_limit),
    ensures layout_argument_ready(source, forms, layouts.inputs.ranges_model(), layouts.definitions.ranges_model(),
        preceding_port_bits(definition_widths(body.definitions@), first as nat) as int, argument, width as usize),
{
    if let CallArgumentSource::Driver(driver) = argument.source {
        let used = preceding_port_bits(definition_widths(body.definitions@), first as nat) as int;
        assert forall|bit: int| 0 <= bit < width implies
            #[trigger] driver_bit_available(layouts.inputs.ranges_model(), layouts.definitions.ranges_model(), used, driver, bit) by {
            body_driver_bits_fit_layout(body.input_widths@, body.definitions@, layouts, capacity, first as int, used, driver, width, bit);
        };
    }
}

pub(super) closed spec fn argument_wire(caller: &CallerArguments, argument: ProjectedCallArgument, bit: int) -> Wire {
    match argument.source {
        CallArgumentSource::Driver(driver) =>
            driver_wire(caller.inputs@, caller.definitions@, caller.wires@, driver, bit),
        CallArgumentSource::Literal(_) => {
            let bytes = literal_word(caller, argument.form);
            Wire::Constant(call_literal_bit(bytes, bit as nat))

        },
        CallArgumentSource::NestedCall(reference) =>
            caller.child_wires@[caller.child_ranges@[reference as int]->Some_0.start + bit],
        CallArgumentSource::Deferred => arbitrary(),
    }
}

proof fn append_argument_contract(
    caller: &CallerArguments, arguments: Seq<ProjectedCallArgument>, ranges: Seq<Range<usize>>,
    previous: Seq<Wire>, after: Seq<Wire>, port: int,
)
    requires
        0 <= port < ranges.len() == arguments.len(),
        previous.len() == ranges[port].start,
        after.len() == ranges[port].end,
        previous.len() <= after.len(),
        after.take(previous.len() as int) == previous,
        argument_prefix_wires(caller, arguments, ranges, port, previous),
        argument_source_available(caller, arguments[port].source),
        forall|bit: int| 0 <= bit < ranges[port].end - ranges[port].start
            ==> (#[trigger] after[ranges[port].start + bit]) == argument_wire(caller, arguments[port], bit),
    ensures argument_prefix_wires(caller, arguments, ranges, port + 1, after),
{
    reveal(argument_prefix_wires);
    assert forall|i: int| 0 <= i < port + 1 implies {
        let range = #[trigger] ranges[i];
        &&& argument_source_available(caller, arguments[i].source)
        &&& range.end <= after.len()
        &&& forall|bit: int| 0 <= bit < range.end - range.start
            ==> (#[trigger] after[range.start + bit]) == argument_wire(caller, arguments[i], bit)
    } by {
        if i < port {
            let range = ranges[i];
            assert(range.end <= previous.len());
            assert forall|bit: int| 0 <= bit < range.end - range.start implies
                (#[trigger] after[range.start + bit]) == argument_wire(caller, arguments[i], bit) by {
                assert(after.take(previous.len() as int)[range.start + bit] == after[range.start + bit]);
            };
        }
    };
}

#[verifier::opaque]
pub(super) open spec fn argument_prefix_wires(
    caller: &CallerArguments, arguments: Seq<ProjectedCallArgument>, ranges: Seq<Range<usize>>, ports: int, wires: Seq<Wire>,
) -> bool {
    &&& 0 <= ports <= ranges.len() == arguments.len()
    &&& forall|i: int| 0 <= i < ports ==> {
        let range = #[trigger] ranges[i];
        &&& argument_source_available(caller, arguments[i].source)
        &&& range.end <= wires.len()
        &&& forall|bit: int| 0 <= bit < range.end - range.start
            ==> (#[trigger] wires[range.start + bit]) == argument_wire(caller, arguments[i], bit)
    }
}

/// 呼び出し元の一つの駆動元から、宣言幅のビット列を読み取る。
pub(super) open spec fn argument_driver_value(
    caller: &CallerArguments, inputs: Seq<bool>, gates: Seq<bool>, driver: crate::project::OutputDriver,
) -> Seq<bool> {
    match driver {
        crate::project::OutputDriver::Input(port) => {
            let range = caller.inputs@[port as int];
            inputs.subrange(range.start as int, range.end as int)
        },
        crate::project::OutputDriver::Definition(index) => {
            let range = caller.definitions@[index as int];
            Seq::new((range.end - range.start) as nat,
                |bit: int| wire_value(caller.wires@[range.start + bit], inputs, gates))
        },
    }
}

/// 子を指す実引数の入力値は、その参照枠にある出力配線を読んだ値と一致する。
pub(super) proof fn lowered_nested_argument_port_value(
    caller: &CallerArguments, arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout,
    widths: Seq<u64>, limit: usize, mapped: Seq<Wire>, inputs: Seq<bool>, gates: Seq<bool>,
    port: usize, reference: usize,
)
    requires
        port_bit_layout_result(widths, limit, Ok(*layout)),
        argument_prefix_wires(caller, arguments, layout.ranges_model(), arguments.len() as int, mapped),
        mapped.len() == layout.total_bits_model(),
        port < widths.len(), port < arguments.len(),
        arguments[port as int].source == CallArgumentSource::NestedCall(reference),
        reference < caller.child_ranges@.len(),
        caller.child_ranges@[reference as int] matches Some(range)
            && range.start <= range.end <= caller.child_wires@.len()
            && range.end - range.start == widths[port as int],
    ensures ({
        let range = caller.child_ranges@[reference as int]->Some_0;
        let value = port_values(layout, instance_wire_values(mapped, inputs, gates))[port as int];
        &&& value.len() == widths[port as int]
        &&& value == instance_wire_values(
            caller.child_wires@.subrange(range.start as int, range.end as int), inputs, gates)
    }),
{
    port_bit_layout_port(widths, limit, *layout, port);
    reveal(port_values);
    reveal(argument_prefix_wires);
    reveal(argument_wire);
    let destination = layout.ranges_model()[port as int];
    let range = caller.child_ranges@[reference as int]->Some_0;
    let child = caller.child_wires@.subrange(range.start as int, range.end as int);
    let value = port_values(layout, instance_wire_values(mapped, inputs, gates))[port as int];
    let expected = instance_wire_values(child, inputs, gates);
    assert forall|bit: int| 0 <= bit < value.len() implies (#[trigger] value[bit]) == expected[bit] by {
        assert(mapped[destination.start + bit] == argument_wire(caller, arguments[port as int], bit));
        assert(mapped[destination.start + bit] == child[bit]);
    };
    assert(value =~= expected);
}

/// 実引数から作った配線を読むと、その駆動元またはリテラルの値が一つの入力ポートに入る。
pub(super) proof fn lowered_argument_port_value(
    caller: &CallerArguments, arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout,
    widths: Seq<u64>, limit: usize, mapped: Seq<Wire>, inputs: Seq<bool>, gates: Seq<bool>, port: usize,
)
    requires
        port_bit_layout_result(widths, limit, Ok(*layout)),
        argument_prefix_wires(caller, arguments, layout.ranges_model(), arguments.len() as int, mapped),
        mapped.len() == layout.total_bits_model(),
        port < widths.len(), port < arguments.len(),
        arguments[port as int].source.has_direct_wires(),
        ({
            let argument = arguments[port as int];
            match argument.source {
                CallArgumentSource::Driver(crate::project::OutputDriver::Input(i)) => {
                    let range = caller.inputs@[i as int];
                    &&& i < caller.inputs@.len() && range.end <= inputs.len()
                    &&& range.end - range.start == widths[port as int]
                },
                CallArgumentSource::Driver(crate::project::OutputDriver::Definition(i)) => {
                    let range = caller.definitions@[i as int];
                    &&& i < caller.definitions@.len() && range.end <= caller.wires@.len()
                    &&& range.end - range.start == widths[port as int]
                    &&& forall|at: int| range.start <= at < range.end ==>
                        wire_available(#[trigger] caller.wires@[at], inputs.len(), gates.len())
                },
                CallArgumentSource::Literal(bits) => {
                    let form = argument.form;
                    let span = form_span(caller.forms@[form as int]);
                    &&& form < caller.forms@.len()
                    &&& span.start < span.end <= caller.source.text.spec_bytes().len()
                    &&& bits == widths[port as int]
                    &&& literal_argument_matches_width(caller.source, caller.forms@, form, bits as int)
                },
                CallArgumentSource::Deferred | CallArgumentSource::NestedCall(_) => true,
            }
        }),
    ensures ({
        let value = port_values(layout, instance_wire_values(mapped, inputs, gates))[port as int];
        let argument = arguments[port as int];
        &&& value.len() == widths[port as int]
        &&& match argument.source {
            CallArgumentSource::Driver(driver) => value == argument_driver_value(caller, inputs, gates, driver),
            CallArgumentSource::Literal(bits) =>
                bits == widths[port as int]
                && value == Seq::new(bits as nat, |bit: int| call_literal_bit(literal_word(caller, argument.form), bit as nat)),
            CallArgumentSource::Deferred | CallArgumentSource::NestedCall(_) => false,
        }
    }),
{
    port_bit_layout_port(widths, limit, *layout, port);
    reveal(port_values);
    reveal(argument_prefix_wires);
    reveal(argument_wire);
    let range = layout.ranges_model()[port as int];
    let value = port_values(layout, instance_wire_values(mapped, inputs, gates))[port as int];
    let argument = arguments[port as int];
    let expected = match argument.source {
        CallArgumentSource::Driver(driver) => argument_driver_value(caller, inputs, gates, driver),
        CallArgumentSource::Literal(bits) =>
            Seq::new(bits as nat, |bit: int| call_literal_bit(literal_word(caller, argument.form), bit as nat)),
        CallArgumentSource::Deferred | CallArgumentSource::NestedCall(_) => arbitrary(),
    };
    assert(argument.source.has_direct_wires());
    assert forall|bit: int| 0 <= bit < value.len() implies #[trigger] value[bit] == expected[bit] by {
        assert(mapped[range.start + bit] == argument_wire(caller, argument, bit));
        let wire = mapped[range.start + bit];
        match argument.source {
            CallArgumentSource::Driver(crate::project::OutputDriver::Input(i)) => {
                let caller_range = caller.inputs@[i as int];
                assert(wire == Wire::Input((caller_range.start + bit) as usize));
                assert(caller_range.start + bit < inputs.len());
            },
            CallArgumentSource::Driver(crate::project::OutputDriver::Definition(i)) => {
                let caller_range = caller.definitions@[i as int];
                assert(wire == caller.wires@[caller_range.start + bit]);
            },
            CallArgumentSource::Literal(_) => {
                assert(wire == Wire::Constant(call_literal_bit(literal_word(caller, argument.form), bit as nat)));
            },
            CallArgumentSource::Deferred | CallArgumentSource::NestedCall(_) => {},
        }
        assert(value[bit] == wire_value(wire, inputs, gates));
    };
    assert(value =~= expected);
}

fn append_argument_driver(
    caller: &CallerArguments, arguments: &mut Vec<Wire>, driver: crate::project::OutputDriver, width: usize,
    Ghost(input_bits): Ghost<usize>, Ghost(gates): Ghost<nat>,
)
    requires
        old(arguments)@.len() + width <= usize::MAX,
        forall|bit: int| 0 <= bit < width ==>
            #[trigger] driver_bit_available(caller.inputs@, caller.definitions@, caller.wires@.len() as int, driver, bit),
        forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
        wires_available(caller.wires@, input_bits, gates),
        wires_available(old(arguments)@, input_bits, gates),
    ensures
        final(arguments)@.len() == old(arguments)@.len() + width,
        final(arguments)@.take(old(arguments)@.len() as int) == old(arguments)@,
        wires_available(final(arguments)@, input_bits, gates),
        forall|j: int| 0 <= j < width ==> (#[trigger] final(arguments)@[old(arguments)@.len() + j])
            == driver_wire(caller.inputs@, caller.definitions@, caller.wires@, driver, j),
{
    let ghost initial = arguments@;
    assert(initial.take(initial.len() as int) =~= initial);
    let mut bit = 0;
    while bit < width
        invariant
            initial == old(arguments)@, bit <= width, initial.len() + width <= usize::MAX,
            arguments@.len() == initial.len() + bit,
            arguments@.take(initial.len() as int) == initial,
            forall|j: int| 0 <= j < bit ==> (#[trigger] arguments@[initial.len() + j])
                == driver_wire(caller.inputs@, caller.definitions@, caller.wires@, driver, j),
            forall|j: int| 0 <= j < width ==>
                #[trigger] driver_bit_available(caller.inputs@, caller.definitions@, caller.wires@.len() as int, driver, j),
            forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
            wires_available(caller.wires@, input_bits, gates),
            wires_available(arguments@, input_bits, gates),
        decreases width - bit,
    {
        let wire = lower_driver_bit(caller.inputs, caller.definitions, caller.wires, driver, bit);
        let ghost previous = arguments@;
        proof { driver_wire_is_available(caller.inputs@, caller.definitions@, caller.wires@, driver, bit as int, input_bits, gates); }
        arguments.push(wire);
        proof {
            assert(arguments@.take(initial.len() as int) =~= initial);
            reveal(wires_available);
            assert forall|j: int| 0 <= j < arguments@.len() implies wire_available(#[trigger] arguments@[j], input_bits as nat, gates) by {
                if j < previous.len() { assert(arguments@[j] == previous[j]); }
            };
        }
        bit += 1;
    }
}

fn append_argument_literal(
    caller: &CallerArguments, arguments: &mut Vec<Wire>, argument: &ProjectedCallArgument, width: usize,
    Ghost(input_bits): Ghost<usize>, Ghost(gates): Ghost<nat>,
)
    requires
        argument.source is Literal, argument_wires_ready(caller, *argument, width),
        form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
        old(arguments)@.len() + width <= usize::MAX, wires_available(old(arguments)@, input_bits, gates),
    ensures
        final(arguments)@.len() == old(arguments)@.len() + width,
        final(arguments)@.take(old(arguments)@.len() as int) == old(arguments)@,
        wires_available(final(arguments)@, input_bits, gates),
        forall|bit: int| 0 <= bit < width ==> (#[trigger] final(arguments)@[old(arguments)@.len() + bit])
            == argument_wire(caller, *argument, bit),
{
    reveal(argument_wires_ready);
    let (word, _) = read_indexed_atom(caller.source.text, caller.forms, argument.form);
    let ghost previous = arguments@;
    proof {
        assert(word.spec_bytes() == literal_word(caller, argument.form));
        if bare_atom_kind(word.spec_bytes()) == Some(AtomKind::Binary)
            || bare_atom_kind(word.spec_bytes()) == Some(AtomKind::Hexadecimal)
        {
            bit_literal_kind_has_digits(word.spec_bytes());
        }
    }
    if word.len() == 1 {
        assert(width == 1);
        let value = word.as_bytes()[0] == b'1';
        arguments.push(Wire::Constant(value));
        assert(arguments@.take(previous.len() as int) =~= previous);
    } else {
        let Some(literal) = read_bit_literal(word) else {
            proof { assert(false); }
            unreachable!()
        };
        append_bit_literal_wires(&literal, width, arguments);
    }
    proof {
        assert(arguments@.len() == previous.len() + width);
        assert forall|bit: int| 0 <= bit < width implies
            (#[trigger] arguments@[previous.len() + bit]) == argument_wire(caller, *argument, bit) by {};
        reveal(wires_available);
        assert forall|i: int| 0 <= i < arguments@.len() implies wire_available(#[trigger] arguments@[i], input_bits as nat, gates) by {
            if i < previous.len() { assert(arguments@[i] == previous[i]); }
            else {
                let bit = i - previous.len();
                assert(0 <= bit < width && previous.len() + bit == i);
                assert(arguments@[previous.len() + bit] == argument_wire(caller, *argument, bit));
                assert(arguments@[i] is Constant);
            }
        };
    }
}

/// 子の出力範囲を低位ビットから順に実引数へ追加する。
fn append_child_wires(
    source: &[Wire], range: &Range<usize>, arguments: &mut Vec<Wire>,
    Ghost(input_bits): Ghost<usize>, Ghost(gates): Ghost<nat>,
)
    requires
        range.start <= range.end <= source@.len(),
        old(arguments)@.len() + (range.end - range.start) <= usize::MAX,
        wires_available(source@, input_bits, gates),
        wires_available(old(arguments)@, input_bits, gates),
    ensures
        final(arguments)@ == old(arguments)@ + source@.subrange(range.start as int, range.end as int),
        wires_available(final(arguments)@, input_bits, gates),
{
    let ghost before = arguments@;
    let mut index = range.start;
    assert(source@.subrange(range.start as int, index as int) =~= Seq::<Wire>::empty());
    while index < range.end
        invariant
            range.start <= index <= range.end <= source@.len(),
            before.len() + (range.end - range.start) <= usize::MAX,
            arguments@ == before + source@.subrange(range.start as int, index as int),
            wires_available(source@, input_bits, gates),
            wires_available(arguments@, input_bits, gates),
        decreases range.end - index,
    {
        let wire = source[index];
        let ghost previous = arguments@;
        arguments.push(wire);
        proof {
            assert(source@.subrange(range.start as int, index + 1)
                =~= source@.subrange(range.start as int, index as int).push(wire));
            assert(arguments@ =~= before + source@.subrange(range.start as int, index + 1));
            reveal(wires_available);
            assert forall|i: int| 0 <= i < arguments@.len()
                implies wire_available(#[trigger] arguments@[i], input_bits as nat, gates) by {
                if i < previous.len() { assert(arguments@[i] == previous[i]); }
            };
        }
        index += 1;
    }
}

/// 実引数を入力ポート順に展開する。未確定の最初の引数は元ソース範囲を返す。
pub(super) fn lower_call_arguments<'s, 'p, 'a>(
    caller: &CallerArguments<'s, 'p, 'a>, arguments: &[ProjectedCallArgument], callee: &PortBitLayout,
    Ghost(widths): Ghost<Seq<u64>>, Ghost(limit): Ghost<usize>, Ghost(input_bits): Ghost<usize>, Ghost(gates): Ghost<nat>,
) -> (result: Result<Vec<Wire>, LocatedName<'p, 'a>>)
    requires
        form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
        port_bit_layout_result(widths, limit, Ok(*callee)), arguments@.len() == widths.len(),
        forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
        wires_available(caller.wires@, input_bits, gates),
        wires_available(caller.child_wires@, input_bits, gates),
        forall|port: int| 0 <= port < arguments@.len() ==> argument_wires_ready(caller, #[trigger] arguments@[port],
            (callee.ranges_model()[port].end - callee.ranges_model()[port].start) as usize),
    ensures match result {
        Ok(wires) => wires@.len() == callee.total_bits_model() && wires_available(wires@, input_bits, gates)
            && argument_prefix_wires(caller, arguments@, callee.ranges_model(), arguments@.len() as int, wires@),
        Err(site) => exists|port: int| 0 <= port < arguments@.len()
            && !argument_source_available(caller, (#[trigger] arguments@[port]).source)
            && is_form_location(caller.source, caller.forms@[arguments@[port].form as int], site)
            && forall|earlier: int| 0 <= earlier < port ==> argument_source_available(caller, (#[trigger] arguments@[earlier]).source),
    },
{
    let ranges = callee.ranges();
    let mut wires: Vec<Wire> = Vec::new();
    let mut port = 0;
    proof {
        port_bit_layout_size(widths, limit, callee);
        reveal(preceding_port_bits);
        reveal(wires_available);
        reveal(argument_prefix_wires);
    }
    while port < arguments.len()
        invariant
            port <= arguments@.len() == widths.len() == ranges@.len(),
            ranges@ == callee.ranges_model(),
            port_bit_layout_result(widths, limit, Ok(*callee)),
            form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
            wires@.len() == preceding_port_bits(widths, port as nat),
            wires_available(wires@, input_bits, gates),
            wires_available(caller.wires@, input_bits, gates),
            wires_available(caller.child_wires@, input_bits, gates),
            forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
            forall|i: int| 0 <= i < arguments@.len() ==> argument_wires_ready(caller, #[trigger] arguments@[i],
                (ranges@[i].end - ranges@[i].start) as usize),
            argument_prefix_wires(caller, arguments@, ranges@, port as int, wires@),
        decreases arguments@.len() - port,
    {
        proof { port_bit_layout_port(widths, limit, *callee, port); reveal(argument_wires_ready); }
        let argument = &arguments[port];
        let range = &ranges[port];
        let width = range.end - range.start;
        let ghost previous = wires@;
        match argument.source {
            CallArgumentSource::Driver(driver) =>
                append_argument_driver(caller, &mut wires, driver, width, Ghost(input_bits), Ghost(gates)),
            CallArgumentSource::Literal(_) =>
                append_argument_literal(caller, &mut wires, argument, width, Ghost(input_bits), Ghost(gates)),
            CallArgumentSource::NestedCall(reference) => {
                let child = if reference < caller.child_ranges.len() { caller.child_ranges[reference].as_ref() } else { None };
                let Some(child) = child else {
                    proof {
                        assert(reference >= caller.child_ranges@.len() || caller.child_ranges@[reference as int].is_none());
                        assert(!argument_source_available(caller, argument.source));
                        reveal(argument_prefix_wires);
                    }
                    return Err(form_location(caller.source, caller.forms, argument.form));
                };
                append_child_wires(caller.child_wires, child, &mut wires, Ghost(input_bits), Ghost(gates));
                proof {
                    reveal(argument_wire);
                    assert(wires@.take(previous.len() as int) =~= previous);
                    assert forall|bit: int| 0 <= bit < width implies
                        (#[trigger] wires@[previous.len() + bit]) == argument_wire(caller, *argument, bit) by {};
                }
            },
            CallArgumentSource::Deferred => {
                proof { reveal(argument_prefix_wires); }
                return Err(form_location(caller.source, caller.forms, argument.form));
            },
        }
        proof { append_argument_contract(caller, arguments@, ranges@, previous, wires@, port as int); }
        port += 1;
    }
    proof { port_bit_layout_size(widths, limit, callee); }
    Ok(wires)
}

/// 展開時に使える配線が未確定か、呼び出しを展開するためのゲート上限を超えた。
#[derive(Debug)]
pub(super) enum CallWiringError<'p, 'a> {
    /// 配線を確定できなかった最初の引数の範囲。
    DeferredArgument(LocatedName<'p, 'a>),
    /// 呼び出し先の追加でゲート数の上限を超える。
    GateCapacity,
}

/// 後順の子を展開する途中で発生した診断。
#[derive(Debug)]
pub(super) enum ChildCallWiringError<'p, 'a> {
    /// 配線を確定できなかった最初の引数の範囲。
    DeferredArgument(LocatedName<'p, 'a>),
    /// ゲート数の上限を超えた子の呼び出し式全体の範囲。
    GateCapacity(LocatedName<'p, 'a>),
    /// 子の出力を一時配線表に追加すると上限を超える。値の単位は配線の本数。
    OutputCapacity { site: LocatedName<'p, 'a>, used: usize, width: usize, capacity: usize },
}

pub(super) open spec fn builtin_nor_call_matches(builtin: &(NorNetlist, PortBitLayout)) -> bool {
    &&& nor_evaluation_ready(&builtin.0, 2)
    &&& builtin.0.gates@ == seq![NorGate { left: Wire::Input(0), right: Wire::Input(1) }]
    &&& builtin.0.outputs@ == seq![Wire::Gate(0)]
    &&& builtin.1.total_bits_model() == 2
    &&& port_bit_layout_result(seq![1u64, 1u64], 2, Ok(builtin.1))
}

/// 基底 NOR の評価結果を、宣言順の入力ポートと NOR の真理値に結び付ける。
pub(super) proof fn builtin_nor_evaluation(
    builtin: &(NorNetlist, PortBitLayout), input: Seq<bool>, output: Seq<bool>,
)
    requires
        builtin_nor_call_matches(builtin),
        crate::netlist::nor_evaluation(&builtin.0, input, output),
    ensures
        input.len() == 2,
        port_values(&builtin.1, input) == seq![seq![input[0]], seq![input[1]]],
        output == seq![!(input[0] || input[1])],
{
    reveal(crate::netlist::nor_evaluation);
    let netlist = &builtin.0;
    let values = choose|values: Seq<bool>| #[trigger] crate::netlist::gate_values_match(input, netlist.gates@, values)
        && values.len() == netlist.gates@.len()
        && crate::netlist::output_values_match(input, values, netlist.outputs@, output);
    reveal(crate::netlist::gate_values_match);
    assert(values[0] == !(input[0] || input[1]));
    assert(output[0] == values[0]);
    assert(output =~= seq![!(input[0] || input[1])]);

    let widths = seq![1u64, 1u64];
    port_bit_layout_port(widths, 2, builtin.1, 0);
    port_bit_layout_port(widths, 2, builtin.1, 1);
    reveal_with_fuel(preceding_port_bits, 3);
    reveal(port_values);
    let ports = port_values(&builtin.1, input);
    assert(ports[0] =~= seq![input[0]]);
    assert(ports[1] =~= seq![input[1]]);
    assert(ports =~= seq![seq![input[0]], seq![input[1]]]);
}

/// 基底 NOR を入力2本、出力1本の呼び出しとして扱うための回路と入力配置。
///
/// 呼び出し元のビット上限が1でも同じ信号を両入力に渡せるよう、入力配置の容量は2とする。
pub(super) fn builtin_nor_call() -> (builtin: (NorNetlist, PortBitLayout))
    ensures builtin_nor_call_matches(&builtin),
{
    let widths: &[u64] = &[1, 1];
    proof {
        assert(widths@ =~= seq![1u64, 1u64]);
        reveal_with_fuel(preceding_port_bits, 3);
        assert(preceding_port_bits(widths@, 2) == 2);
        assert(crate::netlist::port_widths_fit(widths@, 2, 2));
    }
    let Ok(layout) = PortBitLayout::from_widths(widths, 2) else {
        proof { assert(false); }
        unreachable!()
    };
    let mut gates = Vec::new();
    gates.push(NorGate { left: Wire::Input(0), right: Wire::Input(1) });
    let mut outputs = Vec::new();
    outputs.push(Wire::Gate(0));
    (NorNetlist { input_count: 2, gates, outputs }, layout)
}

/// 更新前の配線表から得た実引数で、同じ呼び出しのゲートと出力範囲を作ったことを表す。
#[verifier::opaque]
pub(super) open spec fn child_instance_matches(
    caller: &CallerArguments, arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout,
    callee: &NorNetlist, before: &ChildOutputWires, after: &ChildOutputWires, reference: usize,
    old_gates: Seq<NorGate>, new_gates: Seq<NorGate>, input_bits: usize,
) -> bool {
    exists|invocation: CallerArguments, mapped: Seq<Wire>|
        #[trigger] argument_prefix_wires(&invocation, arguments, layout.ranges_model(), arguments.len() as int, mapped)
        && invocation.source == caller.source && invocation.forms@ == caller.forms@
        && invocation.inputs@ == caller.inputs@ && invocation.definitions@ == caller.definitions@
        && invocation.wires@ == caller.wires@
        && invocation.child_ranges@ == before.ranges@ && invocation.child_wires@ == before.wires@
        && mapped.len() == layout.total_bits_model()
        && wires_available(mapped, input_bits, old_gates.len())
        && child_outputs_appended(before, after, reference, callee, mapped, old_gates, new_gates, input_bits)
}

/// 先に展開した子の配線を実引数から参照し、この呼び出しの出力を一時配線表へ登録する。
///
/// # Errors
///
/// 引数順に配線を確定してから、ゲート上限、一時配線表の上限の順で検査する。
/// 失敗時は既存のゲート列と一時配線表を保つ。
pub(super) fn lower_child_call<'s, 'p, 'a>(
    caller: &CallerArguments<'s, 'p, 'a>, arguments: &[ProjectedCallArgument], layout: &PortBitLayout,
    callee: &NorNetlist, children: &mut ChildOutputWires, reference: usize, gates: &mut Vec<NorGate>, capacity: usize,
    output_capacity: usize, expression: &LocatedName<'p, 'a>,
    Ghost(widths): Ghost<Seq<u64>>, Ghost(limit): Ghost<usize>, Ghost(input_bits): Ghost<usize>,
) -> (result: Result<(), ChildCallWiringError<'p, 'a>>)
    requires
        form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
        location_in_source(*expression), *expression.source == *caller.source,
        port_bit_layout_result(widths, limit, Ok(*layout)), arguments@.len() == widths.len() == layout.ranges_model().len(),
        nor_evaluation_ready(callee, layout.total_bits_model() as nat),
        reference < old(children).ranges@.len(), old(children).ranges@[reference as int].is_none(),
        old(children).wires@.len() <= output_capacity,
        old(gates)@.len() <= capacity,
        gates_available(old(gates)@, input_bits as nat, old(gates)@.len() as int),
        wires_available(caller.wires@, input_bits, old(gates)@.len()),
        wires_available(old(children).wires@, input_bits, old(gates)@.len()),
        forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
        forall|i: int| 0 <= i < arguments@.len() ==> {
            let argument = #[trigger] arguments@[i];
            let range = layout.ranges_model()[i];
            let width = (range.end - range.start) as usize;
            &&& layout_argument_ready(caller.source, caller.forms@, caller.inputs@, caller.definitions@,
                caller.wires@.len() as int, argument, width)
            &&& child_argument_width_ready(old(children).ranges@, old(children).wires@.len(), argument.source, width)
        },
    ensures
        result.is_ok() ==> old(gates)@.len() + callee.gates@.len() <= capacity,
        result.is_ok() ==> final(gates)@.len() == old(gates)@.len() + callee.gates@.len(),
        result.is_ok() ==> final(gates)@.take(old(gates)@.len() as int) == old(gates)@,
        result.is_ok() ==> gates_available(final(gates)@, input_bits as nat, final(gates)@.len() as int),
        result.is_ok() ==> final(children).wires@.len() == old(children).wires@.len() + callee.outputs@.len() <= output_capacity,
        result.is_ok() ==> wires_available(final(children).wires@, input_bits, final(gates)@.len()),
        result.is_ok() ==> final(children).ranges@ == old(children).ranges@.update(reference as int,
            Some((old(children).wires@.len() as usize)..(final(children).wires@.len() as usize))),
        result.is_ok() ==> forall|i: int| 0 <= i < arguments@.len() ==>
            projected_source_available(old(children).ranges@, (#[trigger] arguments@[i]).source),
        result.is_ok() ==> child_instance_matches(caller, arguments@, layout, callee, old(children), final(children),
            reference, old(gates)@, final(gates)@, input_bits),
        result matches Err(error) ==> {
            let ranges = old(children).ranges@;
            &&& final(children).ranges@ == ranges && final(children).wires@ == old(children).wires@
            &&& final(gates)@ == old(gates)@
            &&& match error {
                ChildCallWiringError::DeferredArgument(site) => exists|i: int| 0 <= i < arguments@.len()
                    && !projected_source_available(ranges, (#[trigger] arguments@[i]).source)
                    && is_form_location(caller.source, caller.forms@[arguments@[i].form as int], site)
                    && forall|j: int| 0 <= j < i ==> projected_source_available(ranges, (#[trigger] arguments@[j]).source),
                ChildCallWiringError::GateCapacity(site) => site == *expression
                    && old(gates)@.len() + callee.gates@.len() > capacity
                    && forall|i: int| 0 <= i < arguments@.len() ==>
                        projected_source_available(ranges, (#[trigger] arguments@[i]).source),
                ChildCallWiringError::OutputCapacity { site, used, width, capacity: available } => {
                    &&& site == *expression
                    &&& used == old(children).wires@.len() && width == callee.outputs@.len()
                    &&& available == output_capacity && used + width > available
                    &&& old(gates)@.len() + callee.gates@.len() <= capacity
                    &&& forall|i: int| 0 <= i < arguments@.len() ==>
                        projected_source_available(ranges, (#[trigger] arguments@[i]).source)
                },
            }
        },
{
    let ghost before = *children;
    let ghost old_gates = gates@;
    let invocation = CallerArguments {
        child_ranges: children.ranges.as_slice(), child_wires: children.wires.as_slice(), ..*caller
    };
    let ghost invoked = invocation;
    proof { reveal(argument_wires_ready); }
    let mapped = match lower_call_arguments(&invocation, arguments, layout, Ghost(widths), Ghost(limit),
        Ghost(input_bits), Ghost(old_gates.len())) {
        Ok(mapped) => mapped,
        Err(site) => return Err(ChildCallWiringError::DeferredArgument(site)),
    };
    proof {
        reveal(argument_prefix_wires);
        assert forall|i: int| 0 <= i < arguments@.len()
            implies projected_source_available(before.ranges@, (#[trigger] arguments@[i]).source) by {
            assert(argument_source_available(&invoked, arguments@[i].source));
        };
    }
    if callee.gates.len() > capacity - gates.len() {
        return Err(ChildCallWiringError::GateCapacity(copy_location(expression)));
    }
    let used = children.wires.len();
    let width = callee.outputs.len();
    if width > output_capacity - used {
        return Err(ChildCallWiringError::OutputCapacity {
            site: copy_location(expression), used, width, capacity: output_capacity,
        });
    }
    let _added = children.append(reference, gates, callee, mapped.as_slice(), capacity, Ghost(input_bits));
    proof {
        assert(_added);
        assert(child_outputs_appended(&before, children, reference, callee, mapped@, old_gates, gates@, input_bits));
    }
    assert(child_instance_matches(caller, arguments@, layout, callee, &before, children, reference,
        old_gates, gates@, input_bits)) by {
        reveal(child_instance_matches);
        assert(argument_prefix_wires(&invoked, arguments@, layout.ranges_model(), arguments@.len() as int, mapped@));
    };
    Ok(())
}

/// 実引数を配線に変換し、呼び出し先を一度追加して出力列を得る。
///
/// # Errors
///
/// 配線を確定できない引数があれば、引数順で最初の元ソース範囲を返す。
/// すべての引数の配線が確定している場合は、追加後のゲート数が上限を超えるとエラーを返す。
/// どちらのエラーでも既存のゲート列を保つ。
pub(super) fn lower_projected_call<'s, 'p, 'a>(
    caller: &CallerArguments<'s, 'p, 'a>, arguments: &[ProjectedCallArgument], layout: &PortBitLayout,
    callee: &NorNetlist, gates: &mut Vec<NorGate>, capacity: usize,
    Ghost(widths): Ghost<Seq<u64>>, Ghost(layout_limit): Ghost<usize>, Ghost(input_bits): Ghost<usize>,
) -> (result: Result<Vec<Wire>, CallWiringError<'p, 'a>>)
    requires
        form_spans_valid(caller.source.text, caller.forms@, caller.source.text.spec_bytes().len() as int),
        port_bit_layout_result(widths, layout_limit, Ok(*layout)), arguments@.len() == widths.len(),
        nor_evaluation_ready(callee, layout.total_bits_model() as nat),
        old(gates)@.len() <= capacity,
        gates_available(old(gates)@, input_bits as nat, old(gates)@.len() as int),
        forall|i: int| 0 <= i < caller.inputs@.len() ==> (#[trigger] caller.inputs@[i]).end <= input_bits,
        wires_available(caller.wires@, input_bits, old(gates)@.len()),
        wires_available(caller.child_wires@, input_bits, old(gates)@.len()),
        forall|port: int| 0 <= port < arguments@.len() ==> argument_wires_ready(caller, #[trigger] arguments@[port],
            (layout.ranges_model()[port].end - layout.ranges_model()[port].start) as usize),
    ensures match result {
        Ok(outputs) => {
            &&& old(gates)@.len() + callee.gates@.len() <= capacity
            &&& gates_available(final(gates)@, input_bits as nat, final(gates)@.len() as int)
            &&& output_ports_available(outputs@, input_bits as nat, final(gates)@.len(), outputs@.len() as int)
            &&& exists|mapped: Seq<Wire>| #[trigger] argument_prefix_wires(caller, arguments@, layout.ranges_model(),
                arguments@.len() as int, mapped)
                && mapped.len() == layout.total_bits_model()
                && wires_available(mapped, input_bits, old(gates)@.len())
                && instance_gates_match(old(gates)@, callee.gates@, mapped, final(gates)@)
                && instance_outputs_match(callee.outputs@, mapped, old(gates)@.len() as usize, outputs@)
        },
        Err(error) => final(gates)@ == old(gates)@ && match error {
            CallWiringError::DeferredArgument(site) =>
                exists|port: int| 0 <= port < arguments@.len()
                    && !argument_source_available(caller, (#[trigger] arguments@[port]).source)
                    && is_form_location(caller.source, caller.forms@[arguments@[port].form as int], site)
                    && forall|earlier: int| 0 <= earlier < port ==>
                        argument_source_available(caller, (#[trigger] arguments@[earlier]).source),
            CallWiringError::GateCapacity => old(gates)@.len() + callee.gates@.len() > capacity
                && forall|port: int| 0 <= port < arguments@.len() ==>
                    argument_source_available(caller, (#[trigger] arguments@[port]).source),
        },
    },
{
    let ghost before = gates@;
    let argument_wires = match lower_call_arguments(caller, arguments, layout, Ghost(widths), Ghost(layout_limit),
        Ghost(input_bits), Ghost(before.len())) {
        Ok(wires) => wires,
        Err(site) => return Err(CallWiringError::DeferredArgument(site)),
    };
    proof { reveal(wires_available); }
    match append_instance(gates, callee, argument_wires.as_slice(), capacity, Ghost(input_bits as nat)) {
        Some(outputs) => Ok(outputs),
        None => {
            proof { reveal(argument_prefix_wires); }
            Err(CallWiringError::GateCapacity)
        },
    }
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn checked_group_wires_a_wide_and_a_single_bit_output() {
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};
    use super::call_group::{BodyWiring, CallGroupError, lower_call_group};

    let project = parse_circuit_project(&[SourceSnapshot {
        path: "calls.ncg2",
        revision: 1,
        text: "(using nor)
               (func pair (in (a (bits 4)) b) (out (a (bits 4)) inverted)
                   (def inverted (nor b b)))
               (func caller (in (a (bits 4)) b) (out (word (bits 4)) bit)
                   (def (word bit) (pair a b)))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, 0, 2, 8).unwrap();
    assert_eq!(prepared.calls.len(), 1);
    let group = &prepared.calls[0];
    assert_eq!(group.outputs, 0..2);
    let ordinal = (0..plan.len()).find(|&ordinal| plan.template_at(ordinal) == Some(group.vertex)).unwrap();
    let (file, entry) = plan.get(ordinal).unwrap();
    let callee = aliases.check_bit_func(file, entry, 8).unwrap().lower_bit_func(8).unwrap();
    let layouts = super::Layouts {
        inputs: PortBitLayout::from_widths(&[4, 1], 8).unwrap(),
        definitions: PortBitLayout::from_widths(&[4, 1], 8).unwrap(),
        outputs: PortBitLayout::from_widths(&[4, 1], 8).unwrap(),
    };
    let forms = project.circuits()[0].syntax.forms.as_slice();
    let arguments = &prepared.projections.call_arguments.arguments[group.arguments.clone()];
    let mut state = BodyWiring { definitions: Vec::new(), gates: Vec::new(), origins: Vec::new() };
    let error = lower_call_group(group, forms, arguments, &layouts, &callee, &mut state, 0,
        Ghost(seq![4u64, 1u64]), Ghost(seq![4u64, 1u64]), Ghost(seq![4u64, 1u64]), Ghost(8usize), Ghost(8usize),
    ).unwrap_err();
    let CallGroupError::GateCapacity(site) = error else { panic!("expected a gate limit error"); };
    assert_eq!(&site.source.text[site.span], "(pair a b)");
    assert!(state.definitions.is_empty() && state.gates.is_empty() && state.origins.is_empty());

    lower_call_group(group, forms, arguments, &layouts, &callee, &mut state, 8,
        Ghost(seq![4u64, 1u64]), Ghost(seq![4u64, 1u64]), Ghost(seq![4u64, 1u64]), Ghost(8usize), Ghost(8usize),
    ).unwrap();
    let netlist = NorNetlist { input_count: 5, gates: state.gates, outputs: state.definitions };
    assert_eq!(state.origins, [group.outputs.start]);
    assert_eq!(netlist.evaluate(&[true, false, true, true, true]).unwrap(), [true, false, true, true, false]);
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn nested_argument_uses_the_saved_child_output_range() {
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    let project = parse_circuit_project(&[SourceSnapshot {
        path: "calls.ncg2",
        revision: 1,
        text: "(using nor) (func id (in (a (bits 2))) (out (a (bits 2))))
               (func caller (in (a (bits 2))) (out (y (bits 2))) (def y (id (id a))))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, 0, 2, 8).unwrap();
    let arguments = &prepared.projections.call_arguments.arguments[prepared.calls[0].arguments.clone()];
    let CallArgumentSource::NestedCall(reference) = arguments[0].source else { panic!("expected a child call"); };
    let mut children = ChildOutputWires::new(2);
    let mut gates = Vec::new();
    let instance = NorNetlist {
        input_count: 2,
        gates: alloc::vec![NorGate { left: Wire::Input(0), right: Wire::Input(0) }],
        outputs: alloc::vec![Wire::Input(1), Wire::Gate(0)],
    };
    let child_arguments = [Wire::Input(0), Wire::Input(1)];
    let added = children.append(reference, &mut gates, &instance, &child_arguments, 0, Ghost(2usize));
    assert!(!added);
    assert!(children.ranges[reference].is_none() && children.wires.is_empty() && gates.is_empty());
    let added = children.append(reference, &mut gates, &instance, &child_arguments, 1, Ghost(2usize));
    assert!(added);
    assert_eq!(children.ranges[reference], Some(0..2));

    let mut caller = CallerArguments {
        source: &project.sources()[0], forms: &project.circuits()[0].syntax.forms,
        inputs: &[], definitions: &[], wires: &[], child_ranges: &children.ranges,
        child_wires: &children.wires,
    };
    let layout = PortBitLayout::from_widths(&[2], 8).unwrap();
    let wires = lower_call_arguments(&caller, arguments, &layout,
        Ghost(seq![2u64]), Ghost(8usize), Ghost(2usize), Ghost(1nat)).unwrap();
    assert!(matches!(wires.as_slice(), [Wire::Input(1), Wire::Gate(0)]));
    let parent_wiring = NorNetlist { input_count: 2, gates, outputs: wires };
    assert_eq!(parent_wiring.evaluate(&[true, true]).unwrap(), [true, false]);
    caller.child_ranges = &[None, None];
    let site = lower_call_arguments(&caller, arguments, &layout,
        Ghost(seq![2u64]), Ghost(8usize), Ghost(2usize), Ghost(1nat)).unwrap_err();
    assert_eq!(&site.source.text[site.span], "(id a)");
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn selected_children_feed_the_parent_with_a_one_bit_limit() {
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};
    use super::super::{BitFuncRhs, CheckedBitDefinition};
    use super::{LoweringBody, prepare_body_layouts};
    use super::call_group::{BodyWiring, lower_nested_call_group};
    use child_calls::{NestedCallWiringError, bind_child_calls, lower_root_with_children};

    let project = parse_circuit_project(&[SourceSnapshot {
        path: "calls.ncg2",
        revision: 1,
        text: "(using nor) (func id (in a) (out a))
               (func caller (in a) (out y)
                   (def earlier (id 0))
                   (def y (id (id (nor (nor earlier a) 0)))))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let mut templates = aliases.new_function_templates(&plan, Ghost(1u64));
    let position = plan.get(0).unwrap();
    let checked = aliases.check_bit_func(position.0, position.1, 1).unwrap();
    let circuit = checked.lower_bit_func(1).unwrap();
    let template = aliases.standalone_function_template(position, 1, checked, circuit, 1);
    aliases.insert_function_template(&plan, &mut templates, template, Ghost(1u64));

    let position = plan.get(1).unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, position.0, position.1, 1).unwrap();
    let selected = aliases.resolve_template_calls(&plan, &templates, &prepared.calls,
        &prepared.projections.call_arguments.arguments, Ghost(prepared), Ghost((position.0, position.1, 1u64)));
    let parent = &selected[1];
    let parsed = &project.circuits()[position.0];
    let definitions: Vec<_> = selected.iter().enumerate().map(|(group, call)| CheckedBitDefinition {
        expression: copy_location(&call.group.expression), width: 1,
        rhs: BitFuncRhs::CallOutput { group, port: 0 }, operands: Vec::new(),
    }).collect();
    let layouts = prepare_body_layouts(&[1], &definitions, &[1], 2).unwrap();
    let _body = LoweringBody { input_widths: &[1], definitions: definitions.as_slice() };
    let base = CallerArguments {
        source: &project.sources()[position.0], forms: &parsed.syntax.forms,
        inputs: layouts.inputs.ranges(), definitions: layouts.definitions.ranges(),
        wires: &[Wire::Constant(false)], child_ranges: &[], child_wires: &[],
    };
    let builtin = builtin_nor_call();
    let (count, calls) = bind_child_calls(&parent.group.references, parent.children.as_slice(),
        &builtin, Ghost(&aliases),
        Ghost((&plan, &templates, 1u64, prepared.projections.call_arguments.arguments@)),
        Ghost(parent.group.expression.source), Ghost(parent.group.postorder));
    assert!(parent.group.references.start > 0);
    assert_eq!(count, 4);
    assert_eq!(calls.iter().map(|call| call.reference).collect::<Vec<_>>(), [3, 2, 1]);
    let prefix = NorGate { left: Wire::Constant(false), right: Wire::Constant(false) };
    let mut gates = alloc::vec![prefix];
    let parent_circuit = parent.template.circuit();
    let at_limit = lower_root_with_children(&base, &calls, count, parent.arguments, parent_circuit.inputs(),
        parent_circuit.netlist(), &mut gates, 2, 1, Ghost((seq![1u64], 1usize)), Ghost(1usize));
    let Err(NestedCallWiringError::Child(1, ChildCallWiringError::GateCapacity(site))) = at_limit
        else { panic!("expected a child gate limit error"); };
    assert_eq!(&site.source.text[site.span], "(nor (nor earlier a) 0)");
    assert!(matches!(gates.as_slice(), [NorGate { left: Wire::Constant(false), right: Wire::Constant(false) }]));
    let output_limit = lower_root_with_children(&base, &calls, count, parent.arguments, parent_circuit.inputs(),
        parent_circuit.netlist(), &mut gates, 3, 1, Ghost((seq![1u64], 1usize)), Ghost(1usize));
    let Err(NestedCallWiringError::Child(1, ChildCallWiringError::OutputCapacity { site, used: 1, width: 1, capacity: 1 })) = output_limit
        else { panic!("expected a child wiring limit error"); };
    assert_eq!(&site.source.text[site.span], "(nor (nor earlier a) 0)");
    assert!(matches!(gates.as_slice(), [NorGate { left: Wire::Constant(false), right: Wire::Constant(false) }]));
    let deferred = [ProjectedCallArgument { form: parent.arguments[0].form, source: CallArgumentSource::Deferred }];
    let root_failure = lower_root_with_children(&base, &calls, count, &deferred, parent_circuit.inputs(),
        parent_circuit.netlist(), &mut gates, 3, 3, Ghost((seq![1u64], 1usize)), Ghost(1usize));
    let Err(NestedCallWiringError::Root(CallWiringError::DeferredArgument(site))) = root_failure
        else { panic!("expected a root argument error"); };
    assert_eq!(&site.source.text[site.span], "(id (nor (nor earlier a) 0))");
    assert!(matches!(gates.as_slice(), [NorGate { left: Wire::Constant(false), right: Wire::Constant(false) }]));
    let mut state = BodyWiring {
        definitions: alloc::vec![Wire::Constant(false)], gates, origins: alloc::vec![0],
    };
    let failed = lower_nested_call_group(parent, &parsed.syntax.forms, &layouts, &builtin,
        &mut state, 2, 3, Ghost(&_body), Ghost(&aliases),
        Ghost((&plan, &templates, 1u64, prepared.projections.call_arguments.arguments@)), Ghost(2usize));
    assert!(matches!(failed, Err(NestedCallWiringError::Child(1, ChildCallWiringError::GateCapacity(_)))));
    assert!(matches!(state.definitions.as_slice(), [Wire::Constant(false)]));
    assert!(matches!(state.gates.as_slice(), [NorGate { left: Wire::Constant(false), right: Wire::Constant(false) }]));
    assert_eq!(state.origins, [0]);
    lower_nested_call_group(parent, &parsed.syntax.forms, &layouts, &builtin, &mut state, 3, 3,
        Ghost(&_body), Ghost(&aliases), Ghost((&plan, &templates, 1u64, prepared.projections.call_arguments.arguments@)),
        Ghost(2usize)).unwrap();
    assert_eq!(state.origins, [0, 1, 1]);
    assert!(matches!(state.definitions.as_slice(), [Wire::Constant(false), Wire::Gate(2)]));
    let result = NorNetlist { input_count: 1, gates: state.gates, outputs: state.definitions.split_off(1) };
    assert_eq!(result.evaluate(&[false]).unwrap(), [false]);
    assert_eq!(result.evaluate(&[true]).unwrap(), [true]);
}

#[cfg(all(test, not(verus_only)))]
#[test]
fn adds_the_nor_root_output_and_rolls_back_at_its_gate_limit() {
    use super::{LoweringBody, prepare_body_layouts};
    use super::super::{BitFuncRhs, CheckedBitDefinition};
    use super::call_group::{BodyWiring, lower_nor_call_group};
    use child_calls::NestedCallWiringError;
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

    let project = parse_circuit_project(&[SourceSnapshot {
        path: "nor-root.ncg2",
        revision: 1,
        text: "(using nor) (func id (in a) (out a))
               (func caller (in a) (out y) (def y (nor (id (nor a a)) 0)))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    let mut templates = aliases.new_function_templates(&plan, Ghost(1u64));
    let position = plan.get(0).unwrap();
    let checked = aliases.check_bit_func(position.0, position.1, 1).unwrap();
    let circuit = checked.lower_bit_func(1).unwrap();
    let template = aliases.standalone_function_template(position, 1, checked, circuit, 1);
    aliases.insert_function_template(&plan, &mut templates, template, Ghost(1u64));

    let position = plan.get(1).unwrap();
    let prepared = aliases.prepare_expansion_body(&plan, position.0, position.1, 1).unwrap();
    let root = &prepared.nor_roots[0];
    let arguments = prepared.projections.call_arguments.arguments.as_slice();
    let selected = aliases.resolve_nor_root(&plan, &templates, root, arguments,
        Ghost((position.0, position.1, 1u64)), Ghost(&prepared), Ghost(0int));
    let parsed = &project.circuits()[position.0];
    let refs = &parsed.definitions[root.definition].references;
    let definitions = [CheckedBitDefinition {
        expression: copy_location(&root.root.expression), width: 1, rhs: BitFuncRhs::NorCallOutput { root: 0 },
        operands: Vec::new(),
    }];
    let layouts = prepare_body_layouts(&[1], &definitions, &[1], 1).unwrap();
    let _body = LoweringBody { input_widths: &[1], definitions: &definitions };
    let builtin = builtin_nor_call();
    let prefix = NorGate { left: Wire::Constant(false), right: Wire::Constant(false) };
    let mut state = BodyWiring { definitions: Vec::new(), gates: alloc::vec![prefix], origins: alloc::vec![7] };
    let limited = lower_nor_call_group(&selected, refs, &parsed.syntax.forms, &layouts, &builtin, &mut state, 2, 2,
        Ghost(&_body), Ghost(&aliases), Ghost((&plan, &templates, 1u64, arguments@)), Ghost(1usize));
    assert!(matches!(limited, Err(NestedCallWiringError::Root(CallWiringError::GateCapacity))));
    assert!(state.definitions.is_empty());
    assert_eq!(state.gates, [prefix]);
    assert_eq!(state.origins, [7]);
    lower_nor_call_group(&selected, refs, &parsed.syntax.forms, &layouts, &builtin, &mut state, 3, 2,
        Ghost(&_body), Ghost(&aliases), Ghost((&plan, &templates, 1u64, arguments@)), Ghost(1usize)).unwrap();
    assert_eq!(state.definitions, [Wire::Gate(2)]);
    assert_eq!(state.origins, [7, 0, 0]);
    let circuit = NorNetlist { input_count: 1, gates: state.gates, outputs: state.definitions };
    assert_eq!(circuit.evaluate(&[false]).unwrap(), [false]);
    assert_eq!(circuit.evaluate(&[true]).unwrap(), [true]);
}

} // verus!
