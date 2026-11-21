//! 展開に渡す実引数を、呼び出し先の入力ポート順で配線に変換する。

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
use crate::project::use_aliases::call_arity::{CallArgumentSource, ProjectedCallArgument};
use crate::project::circuits::{form_location, read_indexed_atom};
use crate::project::{LocatedName, ProjectSource};
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
            added ==> {
                let start = old(self).wires@.len() as usize;
                let end = final(self).wires@.len() as usize;
                &&& end == start + callee.outputs@.len()
                &&& final(self).ranges@ == old(self).ranges@.update(reference as int, Some(start..end))
                &&& final(self).wires@.take(start as int) == old(self).wires@
                &&& instance_outputs_match(callee.outputs@, arguments@, old(gates)@.len() as usize,
                    final(self).wires@.subrange(start as int, end as int))
                &&& instance_gates_match(old(gates)@, callee.gates@, arguments@, final(gates)@)
                &&& gates_available(final(gates)@, input_bits as nat, final(gates)@.len() as int)
                &&& wires_available(final(self).wires@, input_bits, final(gates)@.len())
            },
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
    match source {
        CallArgumentSource::NestedCall(reference) =>
            reference < caller.child_ranges@.len() && caller.child_ranges@[reference as int].is_some(),
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
    &&& if let CallArgumentSource::NestedCall(reference) = argument.source {
        argument_source_available(caller, argument.source) ==> {
            let range = caller.child_ranges@[reference as int]->Some_0;
            range.start <= range.end <= caller.child_wires@.len() && range.end - range.start == width
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

/// 実引数から作った配線を読むと、その駆動元またはリテラルの値が一つの入力ポートに入る。
pub(super) proof fn lowered_argument_port_value(
    caller: &CallerArguments, arguments: Seq<ProjectedCallArgument>, layout: &PortBitLayout,
    widths: Seq<u64>, limit: usize, mapped: Seq<Wire>, inputs: Seq<bool>, gates: Seq<bool>, port: usize,
)
    requires
        caller.child_ranges@.len() == 0,
        port_bit_layout_result(widths, limit, Ok(*layout)),
        argument_prefix_wires(caller, arguments, layout.ranges_model(), arguments.len() as int, mapped),
        mapped.len() == layout.total_bits_model(),
        port < widths.len(),
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

} // verus!
