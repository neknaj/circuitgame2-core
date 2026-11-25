//! 連接の引数を低位から配線に展開し、循環を構成するビットを元の引数に戻す。

use super::{ClockedEndpointError, ClockedModuleOutputs, ClockedWireDriver, ModuleCalls, UseAliases};
use crate::project::{LocatedName, ModuleBodyPosition, circuits::read_indexed_atom};
use alloc::vec::Vec;
use vstd::prelude::*;
use super::super::{ModuleConcatOperand, argument_wiring::wire_literal, clocked_driver_bits};
#[cfg(verus_only)]
use super::super::{argument_wiring::literal_wires, clocked_driver_bits_result, driver_bits::{checked_whole_port_wiring_error, clocked_whole_port_bits}};
#[cfg(verus_only)]
use crate::project::{OutputDriver, PortDirection, ProjectSource, concat_prefix_width,
    concatenation::{concat_prefix_width_bounds, concat_prefix_width_step, concat_prefix_width_zero},
    circuits::parsed_index_evidence, literal_width::inferred_literal_width_is_accepted};
#[cfg(verus_only)]
use crate::syntax::{Form, form_span};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

spec fn operand_widths(operands: Seq<ModuleConcatOperand>) -> Seq<u64> {
    operands.map_values(|item: ModuleConcatOperand| item.width)
}

closed spec fn concat_operand_owns(operands: Seq<ModuleConcatOperand>, index: int, bit: int) -> bool {
    &&& 0 <= index < operands.len()
    &&& concat_prefix_width(operand_widths(operands), index as nat) <= bit
        < concat_prefix_width(operand_widths(operands), (index + 1) as nat)
}

spec fn operand_wires(
    ports: &ClockedModuleOutputs, source: &ProjectSource, forms: Seq<Form>, operand: ModuleConcatOperand,
    row: Vec<ClockedWireDriver>,
) -> bool {
    &&& row@.len() == operand.width
    &&& match operand.driver {
        Some(driver) => clocked_driver_bits_result(&ports.inputs, &ports.definitions, driver, None, Ok(row)),
        None => {
            let span = form_span(forms[operand.form as int]);
            literal_wires(source.text.spec_bytes()[span.start as int..span.end as int], operand.width, Ok(row))
        },
    }
}

#[verifier::opaque]
spec fn concat_wires_prefix(
    ports: &ClockedModuleOutputs, source: &ProjectSource, forms: Seq<Form>, operands: Seq<ModuleConcatOperand>,
    count: int, bits: Seq<ClockedWireDriver>,
) -> bool {
    let widths = operand_widths(operands);
    &&& 0 <= count <= operands.len()
    &&& bits.len() == concat_prefix_width(widths, count as nat)
    &&& forall|i: int| 0 <= i < count ==> {
        let operand = #[trigger] operands[i];
        let start = concat_prefix_width(widths, i as nat);
        let end = concat_prefix_width(widths, (i + 1) as nat);
        exists|row: Vec<ClockedWireDriver>| #[trigger] operand_wires(ports, source, forms, operand, row)
            && 0 <= start <= end <= bits.len() && bits.subrange(start, end) == row@
    }
}

proof fn append_concat_operand(
    ports: &ClockedModuleOutputs, source: &ProjectSource, forms: Seq<Form>, operands: Seq<ModuleConcatOperand>,
    i: int, prefix: Seq<ClockedWireDriver>, row: Vec<ClockedWireDriver>,
)
    requires
        concat_wires_prefix(ports, source, forms, operands, i, prefix),
        0 <= i < operands.len(),
        operand_wires(ports, source, forms, operands[i], row),
    ensures concat_wires_prefix(ports, source, forms, operands, i + 1, prefix + row@),
{
    reveal(concat_wires_prefix);
    let widths = operand_widths(operands);
    concat_prefix_width_step(widths, i as nat);
    let bits = prefix + row@;
    assert(bits.subrange(prefix.len() as int, bits.len() as int) =~= row@);
    assert forall|j: int| 0 <= j <= i implies {
        let operand = #[trigger] operands[j];
        let start = concat_prefix_width(widths, j as nat);
        let end = concat_prefix_width(widths, (j + 1) as nat);
        exists|wires: Vec<ClockedWireDriver>| #[trigger] operand_wires(ports, source, forms, operand, wires)
            && 0 <= start <= end <= bits.len() && bits.subrange(start, end) == wires@
    } by {
        if j < i {
            let operand = operands[j];
            let start = concat_prefix_width(widths, j as nat);
            let end = concat_prefix_width(widths, (j + 1) as nat);
            let prior = choose|wires: Vec<ClockedWireDriver>| #[trigger] operand_wires(ports, source, forms, operand, wires)
                && 0 <= start <= end <= prefix.len() && prefix.subrange(start, end) == wires@;
            assert(bits.subrange(start, end) =~= prior@);
        } else {
            assert(operand_wires(ports, source, forms, operands[j], row));
        }
    };
}

proof fn concat_alias_operand(
    ports: &ClockedModuleOutputs, source: &ProjectSource, forms: Seq<Form>, operands: Seq<ModuleConcatOperand>,
    bits: Seq<ClockedWireDriver>, index: int, bit: int,
)
    requires
        concat_wires_prefix(ports, source, forms, operands, operands.len() as int, bits),
        concat_operand_owns(operands, index, bit),
        bits[bit] is Alias,
    ensures operands[index].driver.is_some(),
{
    reveal(concat_wires_prefix);
    let widths = operand_widths(operands);
    let operand = operands[index];
    let start = concat_prefix_width(widths, index as nat);
    let end = concat_prefix_width(widths, (index + 1) as nat);
    let row = choose|row: Vec<ClockedWireDriver>| #[trigger] operand_wires(ports, source, forms, operand, row)
        && 0 <= start <= end <= bits.len() && bits.subrange(start, end) == row@;
    assert(row@[bit - start] == bits[bit]);
    if operand.driver.is_none() {
        assert(row@[bit - start] is Terminal);
    }
}

fn concat_operand_at_bit(operands: &[ModuleConcatOperand], bit: usize) -> (index: usize)
    requires bit < concat_prefix_width(operand_widths(operands@), operands@.len()),
    ensures concat_operand_owns(operands@, index as int, bit as int),
{
    let mut left = bit as u64;
    let mut i = 0;
    let ghost widths = operand_widths(operands@);
    proof { concat_prefix_width_zero(widths); }
    while i < operands.len()
        invariant
            i <= operands@.len(), widths == operand_widths(operands@),
            bit == concat_prefix_width(widths, i as nat) + left,
            bit < concat_prefix_width(widths, operands@.len()),
        decreases operands@.len() - i,
    {
        let width = operands[i].width;
        proof { concat_prefix_width_step(widths, i as nat); }
        if left < width { return i; }
        left -= width;
        i += 1;
    }
    unreachable!()
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) closed spec fn endpoint_concat_wires(
        &self, checked: &ModuleCalls, ports: &ClockedModuleOutputs, slot: int, bits: Seq<ClockedWireDriver>,
    ) -> bool {
        let project = self.targets.project_model();
        let file = checked.module.expressions.typed.sources.roots.wiring.drivers.origins@[slot].file as int;
        let concat = checked.module.expressions.concats@[slot]->Some_0;
        &&& checked.module.expressions.concats@[slot].is_some()
        &&& concat_wires_prefix(ports, &project.sources_model()[file], project.circuits_model()[file].syntax.forms@,
            concat.operands@, concat.operands@.len() as int, bits)
    }

    /// 引数の配線をソース順につなぎ、連接式の幅と同じ長さの配線を返す。
    pub(super) fn wire_concat_definition(
        &self, owner: ModuleBodyPosition, limit: u64, _capacity: usize, checked: &ModuleCalls<'p, 'a>,
        ports: &ClockedModuleOutputs, slot: usize,
    ) -> (result: Result<Vec<ClockedWireDriver>, ClockedEndpointError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*ports)),
            slot < checked.module.expressions.concats@.len(),
            checked.module.expressions.concats@[slot as int].is_some(),
        ensures
            result matches Ok(wires) ==> self.endpoint_concat_wires(checked, ports, slot as int, wires@)
                && wires@.len() == ports.definitions.ranges_model()[slot as int].end
                    - ports.definitions.ranges_model()[slot as int].start,
            result matches Err(error) ==> error is Allocation || error is AliasBits,
            result matches Err(ClockedEndpointError::AliasBits { reference, reason }) ==>
                (reason is Allocation || reason is Capacity)
                && exists|i: int| #[trigger] self.module_concat_operand_site_at(&checked.module.expressions, slot as int, i, reference),
    {
        let expressions = &checked.module.expressions;
        let drivers = &expressions.typed.sources.roots.wiring.drivers;
        proof {
            self.module_calls_type_evidence(owner, limit, checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            self.module_selections_evidence(owner, limit, *expressions);
            self.module_driver_sites(owner, limit, *drivers, slot as int);
            self.clocked_output_layouts(&checked.module, limit, _capacity, ports);
            self.clocked_definition_layout_evidence(expressions, limit, _capacity, &ports.definitions, slot);
            self.module_concat_slot(owner, limit, *expressions, slot);
        }
        let Some(concat) = &expressions.concats[slot] else { unreachable!() };
        let Some(range) = ports.definitions.range(slot) else { unreachable!() };
        let total = range.end - range.start;
        let file = drivers.origins[slot].file;
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        proof { parsed_index_evidence(*source, *parsed); }
        let forms = parsed.syntax.forms.as_slice();
        let mut wires = Vec::new();
        if wires.try_reserve_exact(total).is_err() { return Err(ClockedEndpointError::Allocation); }
        let ghost operands = concat.operands@;
        let ghost widths = operand_widths(operands);
        proof { concat_prefix_width_zero(widths); }
        assert(concat_wires_prefix(ports, source, forms@, operands, 0, wires@)) by { reveal(concat_wires_prefix); };
        let mut i = 0;
        while i < concat.operands.len()
            invariant
                i <= operands.len(), operands == concat.operands@, widths == operand_widths(operands),
                concat_wires_prefix(ports, source, forms@, operands, i as int, wires@),
                total == concat_prefix_width(widths, operands.len()),
                *expressions == checked.module.expressions,
                *drivers == expressions.typed.sources.roots.wiring.drivers,
                slot < expressions.concats@.len() && slot < drivers.origins@.len(),
                expressions.concats@[slot as int] == Some(*concat),
                file == drivers.origins@[slot as int].file,
                file < self.targets.project_model().sources_model().len(),
                file < self.targets.project_model().circuits_model().len(),
                ports.inputs.ranges_model().len() == drivers.signature.inputs@.len(),
                ports.definitions.ranges_model().len() == expressions.types@.len() == drivers.definitions@.len(),
                slot < ports.definitions.ranges_model().len(),
                *source == self.targets.project_model().sources_model()[file as int],
                forms@ == self.targets.project_model().circuits_model()[file as int].syntax.forms@,
                total == ports.definitions.ranges_model()[slot as int].end - ports.definitions.ranges_model()[slot as int].start,
                self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
                self.module_selections_result(owner, limit, Ok(Some(*expressions))),
                self.outputs_on_checked(&checked.module, limit, _capacity, Ok(*ports)),
            decreases operands.len() - i,
        {
            let operand = &concat.operands[i];
            proof { self.module_concat_operand_evidence(owner, limit, *expressions, slot, i); }
            let row = match operand.driver {
                Some(driver) => clocked_driver_bits(&ports.inputs, &ports.definitions, driver, None),
                None => {
                    let (word, _) = read_indexed_atom(source.text, forms, operand.form);
                    proof { inferred_literal_width_is_accepted(word.spec_bytes(), limit, operand.width); }
                    wire_literal(word, operand.width, limit)
                },
            };
            let row = match row {
                Ok(row) => row,
                Err(reason) => {
                    proof {
                        if let Some(driver) = operand.driver {
                            checked_whole_port_wiring_error(&ports.inputs, &ports.definitions, driver, reason);
                        }
                    }
                    let reference = self.module_concat_operand_site(owner, limit, expressions, slot, i);
                    assert(exists|j: int| #[trigger]
                        self.module_concat_operand_site_at(&checked.module.expressions, slot as int, j, reference)) by {
                        assert(self.module_concat_operand_site_at(expressions, slot as int, i as int, reference));
                    };
                    return Err(ClockedEndpointError::AliasBits { reference, reason });
                },
            };
            proof {
                if let Some(driver) = operand.driver {
                    self.clocked_output_layouts(&checked.module, limit, _capacity, ports);
                    match driver {
                        OutputDriver::Input(port) => self.routine_bit_layout_port(drivers.signature, limit, _capacity,
                            &ports.inputs, &ports.outputs, PortDirection::Input, port),
                        OutputDriver::Definition(definition) => self.clocked_definition_layout_evidence(
                            expressions, limit, _capacity, &ports.definitions, definition),
                    }
                    clocked_whole_port_bits(&ports.inputs, &ports.definitions, driver, row);
                }
                assert(operand_wires(ports, source, forms@, operands[i as int], row));
                concat_prefix_width_step(widths, i as nat);
                concat_prefix_width_bounds(widths, (i + 1) as nat, widths.len());
                assert(wires@.len() == concat_prefix_width(widths, i as nat)) by {
                    reveal(concat_wires_prefix);
                };
            }
            let ghost before = wires@;
            self.append_definition_wires(&mut wires, row.as_slice());
            proof { append_concat_operand(ports, source, forms@, operands, i as int, before, row); }
            i += 1;
        }
        assert(wires@.len() == total) by { reveal(concat_wires_prefix); };
        assert(self.endpoint_concat_wires(checked, ports, slot as int, wires@));
        Ok(wires)
    }

    pub(super) closed spec fn endpoint_concat_site_at(
        &self, checked: &ModuleCalls, slot: int, bit: int, site: LocatedName,
    ) -> bool {
        let expressions = checked.module.expressions;
        let operands = expressions.concats@[slot]->Some_0.operands@;
        &&& expressions.concats@[slot].is_some()
        &&& exists|index: int| #[trigger] concat_operand_owns(operands, index, bit)
            && operands[index].driver.is_some()
            && self.module_concat_operand_site_at(&expressions, slot, index, site)
    }

    /// 閉路上のビットを担当する引数を特定し、その信号名の範囲を返す。
    pub(super) fn endpoint_concat_site(
        &self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls<'p, 'a>, _ports: &ClockedModuleOutputs,
        slot: usize, bit: usize, Ghost(bits): Ghost<Seq<ClockedWireDriver>>,
    ) -> (site: LocatedName<'p, 'a>)
        requires
            self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            slot < checked.module.expressions.concats@.len(),
            self.endpoint_concat_wires(checked, _ports, slot as int, bits),
            bit < bits.len(), bits[bit as int] is Alias,
        ensures self.endpoint_concat_site_at(checked, slot as int, bit as int, site),
    {
        let expressions = &checked.module.expressions;
        proof {
            self.module_calls_type_evidence(owner, limit, checked);
            self.module_output_types_evidence(owner, limit, checked.module);
            reveal(concat_wires_prefix);
        }
        let Some(concat) = &expressions.concats[slot] else { unreachable!() };
        let index = concat_operand_at_bit(concat.operands.as_slice(), bit);
        proof {
            let project = self.targets.project_model();
            let file = expressions.typed.sources.roots.wiring.drivers.origins@[slot as int].file as int;
            concat_alias_operand(_ports, &project.sources_model()[file], project.circuits_model()[file].syntax.forms@,
                concat.operands@, bits, index as int, bit as int);
        }
        self.module_concat_operand_site(owner, limit, expressions, slot, index)
    }
}

} // verus!
