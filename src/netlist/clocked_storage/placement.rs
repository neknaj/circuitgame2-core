//! 子回路にある状態素子の入力配線を親回路へ移す。

use super::{ClockedStorageInputs, StateAllocationError, Wire, invalid_wire, wire_within};
use crate::netlist::instances::instantiate_wire;
#[cfg(verus_only)]
use crate::netlist::{instance_outputs_match, instance_wire, output_ports_available, wire_available};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

fn place_pin(wire: Wire, arguments: &[Wire], base: usize, _child_gates: usize,
    _parent_inputs: usize, _parent_gates: usize,
) -> (mapped: Wire)
    requires
        wire_available(wire, arguments@.len(), _child_gates as nat),
        base + _child_gates <= _parent_gates,
        output_ports_available(arguments@, _parent_inputs as nat, _parent_gates as nat, arguments@.len() as int),
    ensures mapped == instance_wire(wire, arguments@, base),
        wire_available(mapped, _parent_inputs as nat, _parent_gates as nat),
{
    instantiate_wire(wire, arguments, base)
}

fn place_pins(pins: &[Wire], arguments: &[Wire], base: usize, child_gates: usize,
    parent_inputs: usize, parent_gates: usize,
) -> (result: Result<Vec<Wire>, StateAllocationError>)
    requires
        output_ports_available(pins@, arguments@.len(), child_gates as nat, pins@.len() as int),
        base + child_gates <= parent_gates,
        output_ports_available(arguments@, parent_inputs as nat, parent_gates as nat, arguments@.len() as int),
    ensures match result {
        Ok(mapped) => instance_outputs_match(pins@, arguments@, base, mapped@)
            && output_ports_available(mapped@, parent_inputs as nat, parent_gates as nat, mapped@.len() as int),
        Err(error) => error == StateAllocationError::Allocation,
    },
{
    let mut mapped = Vec::new();
    if mapped.try_reserve_exact(pins.len()).is_err() {
        return Err(StateAllocationError::Allocation);
    }
    let mut i = 0;
    while i < pins.len()
        invariant
            i <= pins@.len(),
            instance_outputs_match(pins@.take(i as int), arguments@, base, mapped@),
            output_ports_available(mapped@, parent_inputs as nat, parent_gates as nat, mapped@.len() as int),
            output_ports_available(pins@, arguments@.len(), child_gates as nat, pins@.len() as int),
            output_ports_available(arguments@, parent_inputs as nat, parent_gates as nat, arguments@.len() as int),
            base + child_gates <= parent_gates,
        decreases pins@.len() - i,
    {
        let pin = place_pin(pins[i], arguments, base, child_gates, parent_inputs, parent_gates);
        let ghost before = mapped@;
        mapped.push(pin);
        assert forall|j: int| 0 <= j < mapped@.len() implies
            (#[trigger] mapped@[j]) == instance_wire(pins@.take(i + 1)[j], arguments@, base)
        by {
            if j < i {
                assert(mapped@[j] == before[j]);
                assert(pins@.take(i as int)[j] == pins@.take(i + 1)[j]);
            }
        };
        i += 1;
    }
    assert(pins@.take(i as int) =~= pins@);
    Ok(mapped)
}

impl ClockedStorageInputs {
    /// すべての入力端子が指定した回路の範囲内にあることを表す。
    pub(crate) open spec fn pins_available(&self, inputs: nat, gates: nat) -> bool {
        &&& (self.address matches Some(address) ==>
            output_ports_available(address@, inputs, gates, address@.len() as int))
        &&& output_ports_available(self.data@, inputs, gates, self.data@.len() as int)
        &&& wire_available(self.enable, inputs, gates)
    }

    /// アドレス、データ、許可の各端子が指定した回路の配線を参照できるか調べる。
    pub(crate) fn pin_wiring_in_range(&self, inputs: usize, gates: usize) -> (valid: bool)
        ensures valid <==> self.pins_available(inputs as nat, gates as nat),
    {
        if let Some(address) = &self.address {
            if let Some(_i) = invalid_wire(address.as_slice(), inputs, gates) {
                assert(!wire_available(address@[_i as int], inputs as nat, gates as nat));
                return false;
            }
        }
        if let Some(_i) = invalid_wire(self.data.as_slice(), inputs, gates) {
            assert(!wire_available(self.data@[_i as int], inputs as nat, gates as nat));
            return false;
        }
        wire_within(self.enable, inputs, gates)
    }

    /// 素子の種類と入力ビット順を保ち、各端子を親回路の配線に対応させる。
    pub open spec fn parent_placement_matches(&self, arguments: Seq<Wire>, base: usize, mapped: &Self) -> bool {
        &&& match (self.address, mapped.address) {
            (Some(source), Some(dest)) => instance_outputs_match(source@, arguments, base, dest@),
            (None, None) => true,
            _ => false,
        }
        &&& instance_outputs_match(self.data@, arguments, base, mapped.data@)
        &&& mapped.enable == instance_wire(self.enable, arguments, base)
    }

    /// 子の状態素子の入力端子を親回路へ移し、素子の種類、幅、ビット順を保つ。
    ///
    /// `arguments` には子回路の外部入力と状態素子の出力を、この順で並べる。
    /// 子回路のゲート番号に、親回路で予約した区間の先頭 `base` を加える。
    ///
    /// # Errors
    ///
    /// アドレスまたはデータの配線列の領域を確保できないときは、割り当てエラーを返す。
    pub(crate) fn place_in_parent(
        &self, arguments: &[Wire], base: usize, child_gates: usize, parent_inputs: usize, parent_gates: usize,
    ) -> (result: Result<Self, StateAllocationError>)
        requires
            self.pins_available(arguments@.len(), child_gates as nat),
            base + child_gates <= parent_gates,
            output_ports_available(arguments@, parent_inputs as nat, parent_gates as nat, arguments@.len() as int),
        ensures match result {
            Ok(mapped) => self.parent_placement_matches(arguments@, base, &mapped)
                && mapped.pins_available(parent_inputs as nat, parent_gates as nat),
            Err(error) => error == StateAllocationError::Allocation,
        },
    {
        let address = if let Some(address) = &self.address {
            Some(place_pins(address.as_slice(), arguments, base, child_gates, parent_inputs, parent_gates)?)
        } else {
            None
        };
        let data = place_pins(self.data.as_slice(), arguments, base, child_gates, parent_inputs, parent_gates)?;
        let enable = place_pin(self.enable, arguments, base, child_gates, parent_inputs, parent_gates);
        Ok(Self { address, data, enable })
    }
}

} // verus!
