//! 同じポート区画と回路構成では正準配線表のバイト列が一致する。

use super::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

verus! {

proof fn word_bytes_agree(first: Seq<u8>, second: Seq<u8>)
    requires first.len() == 8, second.len() == 8, word_at(first, 0) == word_at(second, 0),
    ensures first == second,
{
    let a0 = first[0];
    let a1 = first[1];
    let a2 = first[2];
    let a3 = first[3];
    let a4 = first[4];
    let a5 = first[5];
    let a6 = first[6];
    let a7 = first[7];
    let b0 = second[0];
    let b1 = second[1];
    let b2 = second[2];
    let b3 = second[3];
    let b4 = second[4];
    let b5 = second[5];
    let b6 = second[6];
    let b7 = second[7];
    let x = word_at(first, 0);
    let y = word_at(second, 0);
    assert(a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7) by (bit_vector)
        requires
            x == y,
            x == ((a0 as u64)
            | ((a1 as u64) << 8)
            | ((a2 as u64) << 16)
            | ((a3 as u64) << 24)
            | ((a4 as u64) << 32)
            | ((a5 as u64) << 40)
            | ((a6 as u64) << 48)
            | ((a7 as u64) << 56)),
            y == ((b0 as u64)
            | ((b1 as u64) << 8)
            | ((b2 as u64) << 16)
            | ((b3 as u64) << 24)
            | ((b4 as u64) << 32)
            | ((b5 as u64) << 40)
            | ((b6 as u64) << 48)
            | ((b7 as u64) << 56)),
    {
    }
    assert(first =~= second);
}

proof fn fixed_records_agree(first: Seq<u8>, second: Seq<u8>, width: int, records: int)
    requires
        0 < width, 0 <= records,
        first.len() == width * records, second.len() == first.len(),
        forall|i: int| 0 <= i < records ==>
            #[trigger] first.subrange(width * i, width * (i + 1))
                == second.subrange(width * i, width * (i + 1)),
    ensures first == second,
{
    assert forall|i: int| 0 <= i < first.len() implies #[trigger] first[i] == second[i] by {
        let record = i / width;
        let offset = i % width;
        lemma_fundamental_div_mod(i, width);
        assert(0 <= record < records) by (nonlinear_arith)
            requires
                0 < width,
                0 <= offset < width,
                0 <= i < width * records,
                i == width * record + offset,
        {
        }
        let begin = width * record;
        let end = width * (record + 1);
        assert(0 <= begin <= i < end <= first.len()) by (nonlinear_arith)
            requires 0 < width, 0 <= record < records, 0 <= offset < width,
                i == width * record + offset, first.len() == width * records,
                begin == width * record, end == width * (record + 1),
        {
        }
        assert(i == begin + offset);
        assert(first[i] == first.subrange(begin, end)[offset]);
        assert(second[i] == second.subrange(begin, end)[offset]);
    }
    assert(first =~= second);
}

proof fn ports_agree(ports: Seq<Range<usize>>, total: int, first: Seq<u8>, second: Seq<u8>)
    requires ports_match(ports, total, first), ports_match(ports, total, second),
    ensures first == second,
{
    hide(word_at);
    assert forall|i: int| 0 <= i <= ports.len() implies
        #[trigger] first.subrange(8 * i, 8 * (i + 1)) == second.subrange(8 * i, 8 * (i + 1)) by {
        if i > 0 {
            let port = ports[i - 1];
            assert(word_at(first.subrange(8 * i, 8 * (i + 1)), 0) == (port.end - port.start) as u64);
            assert(word_at(second.subrange(8 * i, 8 * (i + 1)), 0) == (port.end - port.start) as u64);
        }
        word_bytes_agree(first.subrange(8 * i, 8 * (i + 1)), second.subrange(8 * i, 8 * (i + 1)));
    }
    fixed_records_agree(first, second, 8, ports.len() as int + 1);
}

proof fn wire_agrees(wire: Wire, first: Seq<u8>, second: Seq<u8>)
    requires wire_layout_record(wire, first), wire_layout_record(wire, second),
    ensures first == second,
{
    assert(first[0] == second[0]);
    assert(word_at(first.skip(1), 0) == word_at(first, 1));
    assert(word_at(second.skip(1), 0) == word_at(second, 1));
    word_bytes_agree(first.skip(1), second.skip(1));
    assert(first =~= seq![first[0]] + first.skip(1));
    assert(second =~= seq![second[0]] + second.skip(1));
}

proof fn counted_wires_agree(wires: Seq<Wire>, first: Seq<u8>, second: Seq<u8>)
    requires counted_wires(wires, first), counted_wires(wires, second),
    ensures first == second,
{
    hide(word_at);
    word_bytes_agree(first.take(8), second.take(8));
    let a = first.skip(8);
    let b = second.skip(8);
    assert forall|i: int| 0 <= i < wires.len() implies
        #[trigger] a.subrange(9 * i, 9 * (i + 1)) == b.subrange(9 * i, 9 * (i + 1)) by {
        wire_agrees(wires[i], a.subrange(9 * i, 9 * (i + 1)), b.subrange(9 * i, 9 * (i + 1)));
    }
    fixed_records_agree(a, b, 9, wires.len() as int);
    assert(first =~= first.take(8) + a);
    assert(second =~= second.take(8) + b);
}

proof fn gate_layout_agrees(gates: Seq<NorGate>, first: Seq<u8>, second: Seq<u8>)
    requires ordered_gate_layout(gates, first), ordered_gate_layout(gates, second),
    ensures first == second,
{
    assert forall|i: int| 0 <= i < gates.len() implies
        #[trigger] first.subrange(18 * i, 18 * (i + 1)) == second.subrange(18 * i, 18 * (i + 1)) by {
        let gate = gates[i];
        let left = first.subrange(18 * i, 18 * i + 9);
        let right = first.subrange(18 * i + 9, 18 * (i + 1));
        wire_agrees(gate.left, left, second.subrange(18 * i, 18 * i + 9));
        wire_agrees(gate.right, right, second.subrange(18 * i + 9, 18 * (i + 1)));
        assert(first.subrange(18 * i, 18 * (i + 1)) =~= left + right);
        assert(second.subrange(18 * i, 18 * (i + 1)) =~= left + right);
    }
    fixed_records_agree(first, second, 18, gates.len() as int);
}

proof fn storage_record_agrees(
    wiring: &ClockedStorageInputs, memory: Option<usize>, first: Seq<u8>, second: Seq<u8>,
)
    requires storage_record(wiring, memory, first), storage_record(wiring, memory, second),
    ensures first == second,
{
    hide(word_at);
    reveal(storage_record);
    reveal(storage_address_record);
    let address_end = storage_address_end(wiring);
    let data_end = address_end + 8 + 9 * wiring.data@.len();
    if let Some(address) = &wiring.address {
        let a = first.take(address_end);
        let b = second.take(address_end);
        counted_wires_agree(address@, a.subrange(1, address_end - 8), b.subrange(1, address_end - 8));
        word_bytes_agree(a.skip(address_end - 8), b.skip(address_end - 8));
        assert(a[0] == b[0]);
        assert(a =~= seq![a[0]] + a.subrange(1, address_end - 8) + a.skip(address_end - 8));
        assert(b =~= seq![b[0]] + b.subrange(1, address_end - 8) + b.skip(address_end - 8));
        assert(a == b);
    } else {
        assert(first.take(address_end) =~= second.take(address_end));
    }
    counted_wires_agree(wiring.data@, first.subrange(address_end, data_end), second.subrange(address_end, data_end));
    wire_agrees(wiring.enable, first.skip(data_end), second.skip(data_end));
    assert(first =~= first.take(address_end) + first.subrange(address_end, data_end) + first.skip(data_end));
    assert(second =~= second.take(address_end) + second.subrange(address_end, data_end) + second.skip(data_end));
}

proof fn storage_tables_agree(
    first_devices: Seq<ClockedStorage>, second_devices: Seq<ClockedStorage>,
    count: nat, first: Seq<u8>, second: Seq<u8>,
)
    requires
        count <= first_devices.len(), count <= second_devices.len(),
        forall|i: int| 0 <= i < count ==> (#[trigger] first_devices[i]).wiring_model()
            == second_devices[i].wiring_model()
            && storage_memory_len(&first_devices[i]) == storage_memory_len(&second_devices[i]),
        storage_records(first_devices, count, first),
        storage_records(second_devices, count, second),
    ensures first == second,
    decreases count,
{
    if count > 0 {
        let last = (count - 1) as int;
        let a = &first_devices[last];
        let b = &second_devices[last];
        let length = storage_record_len(&a.wiring_model());
        assert(a.wiring_model() == b.wiring_model());
        let first_split = first.len() - length;
        let second_split = second.len() - length;
        assert(
            0 <= first_split <= first.len()
            && 0 <= second_split <= second.len()
            && storage_records(first_devices, last as nat, first.take(first_split))
            && storage_records(second_devices, last as nat, second.take(second_split))
            && storage_record(&a.wiring_model(), storage_memory_len(a), first.skip(first_split))
            && storage_record(&b.wiring_model(), storage_memory_len(b), second.skip(second_split))
        ) by { reveal(storage_records); }
        storage_tables_agree(
            first_devices, second_devices, last as nat, first.take(first_split), second.take(second_split),
        );
        storage_record_agrees(
            &a.wiring_model(), storage_memory_len(a), first.skip(first_split), second.skip(second_split),
        );
        assert(first =~= first.take(first_split) + first.skip(first_split));
        assert(second =~= second.take(second_split) + second.skip(second_split));
    } else {
        assert(first.len() == 0 && second.len() == 0) by { reveal(storage_records); }
        assert(first =~= second);
    }
}

#[verifier::opaque]
spec fn wiring_pieces(
    bytes: Seq<u8>, inputs_end: int, ports_end: int, gates_start: int, gates_end: int, outputs_end: int,
) -> Seq<u8> {
    bytes.take(inputs_end)
        + bytes.subrange(inputs_end, ports_end)
        + bytes.subrange(ports_end, ports_end + 8)
        + bytes.subrange(ports_end + 8, gates_start)
        + bytes.subrange(gates_start, gates_end)
        + bytes.subrange(gates_end, outputs_end)
        + bytes.skip(outputs_end)
}

proof fn wiring_pieces_join(
    bytes: Seq<u8>, inputs_end: int, ports_end: int, gates_start: int, gates_end: int, outputs_end: int,
)
    requires 0 <= inputs_end <= ports_end <= ports_end + 8 <= gates_start <= gates_end <= outputs_end <= bytes.len(),
    ensures wiring_pieces(bytes, inputs_end, ports_end, gates_start, gates_end, outputs_end) == bytes,
{
    reveal(wiring_pieces);
    assert(wiring_pieces(bytes, inputs_end, ports_end, gates_start, gates_end, outputs_end) =~= bytes);
}


proof fn wiring_prefix_agrees(
    first_vm: &ClockedVm, second_vm: &ClockedVm,
    inputs: Seq<Range<usize>>, outputs: Seq<Range<usize>>, first: Seq<u8>, second: Seq<u8>,
)
    requires
        first_vm.netlist_model() == second_vm.netlist_model(),
        first_vm.external_count() == second_vm.external_count(),
        first_vm.storage_model().len() == second_vm.storage_model().len(),
        wiring_prefix(first_vm, inputs, outputs, first), wiring_prefix(second_vm, inputs, outputs, second),
    ensures first == second,
{
    hide(word_at);
    hide(ports_match);
    hide(counted_wires);
    hide(ordered_gate_layout);
    reveal(wiring_prefix);
    let netlist = first_vm.netlist_model();
    let inputs_end = port_table_len(inputs);
    let ports_end = inputs_end + port_table_len(outputs);
    let gates_start = ports_end + 16;
    let gates_end = gates_start + 18 * netlist.gates@.len();
    let outputs_end = gates_end + 8 + 9 * netlist.outputs@.len();
    ports_agree(inputs, first_vm.external_count() as int, first.take(inputs_end), second.take(inputs_end));
    ports_agree(outputs, netlist.outputs@.len() as int,
        first.subrange(inputs_end, ports_end), second.subrange(inputs_end, ports_end));
    word_bytes_agree(first.subrange(ports_end, ports_end + 8), second.subrange(ports_end, ports_end + 8));
    word_bytes_agree(first.subrange(ports_end + 8, gates_start), second.subrange(ports_end + 8, gates_start));
    gate_layout_agrees(netlist.gates@, first.subrange(gates_start, gates_end), second.subrange(gates_start, gates_end));
    counted_wires_agree(netlist.outputs@, first.subrange(gates_end, outputs_end), second.subrange(gates_end, outputs_end));
    word_bytes_agree(first.skip(outputs_end), second.skip(outputs_end));
    wiring_pieces_join(first, inputs_end, ports_end, gates_start, gates_end, outputs_end);
    wiring_pieces_join(second, inputs_end, ports_end, gates_start, gates_end, outputs_end);
    assert(wiring_pieces(first, inputs_end, ports_end, gates_start, gates_end, outputs_end)
        == wiring_pieces(second, inputs_end, ports_end, gates_start, gates_end, outputs_end)) by {
        reveal(wiring_pieces);
    }
}

proof fn storage_record_transfers(
    source: &ClockedStorageInputs, target: &ClockedStorageInputs, memory: Option<usize>, record: Seq<u8>,
)
    requires
        same_ordered_storage_wiring(source, target),
        storage_record(source, memory, record),
    ensures
        storage_record_len(source) == storage_record_len(target),
        storage_record(target, memory, record),
{
    hide(word_at);
    reveal(storage_record);
    reveal(storage_address_record);
    match (&source.address, &target.address) {
        (Some(first), Some(second)) => assert(first@ == second@),
        (None, None) => {},
        _ => assert(false),
    }
}

proof fn storage_table_transfers(
    source: Seq<ClockedStorage>, target: Seq<ClockedStorage>, count: nat, bytes: Seq<u8>,
)
    requires
        count <= source.len(), count <= target.len(),
        forall|i: int| 0 <= i < count ==> {
            let device = #[trigger] source[i];
            let next = target[i];
            &&& same_ordered_storage_wiring(&device.wiring_model(), &next.wiring_model())
            &&& storage_memory_len(&device) == storage_memory_len(&next)
        },
        storage_records(source, count, bytes),
    ensures storage_records(target, count, bytes),
    decreases count,
{
    if count > 0 {
        let previous = (count - 1) as nat;
        let device = &source[previous as int];
        let next = &target[previous as int];
        let split = bytes.len() - storage_record_len(&device.wiring_model());
        assert(
            0 <= split <= bytes.len()
            && storage_records(source, previous, bytes.take(split))
            && storage_record(&device.wiring_model(), storage_memory_len(device), bytes.skip(split))
        ) by { reveal(storage_records); }
        storage_record_transfers(&device.wiring_model(), &next.wiring_model(), storage_memory_len(device), bytes.skip(split));
        storage_table_transfers(source, target, previous, bytes.take(split));
    }
    reveal(storage_records);
}

/// 構成が適合する VM では、状態値に関係なく同じ正準配線表が使える。
pub proof fn canonical_vm_layout_transfers(
    source: &ClockedVm, target: &ClockedVm,
    inputs: Seq<Range<usize>>, outputs: Seq<Range<usize>>, bytes: Seq<u8>,
)
    requires checkpoint_vms_compatible(source, target), canonical_vm_layout(source, inputs, outputs, bytes),
    ensures canonical_vm_layout(target, inputs, outputs, bytes),
{
    hide(word_at);
    hide(ports_match);
    hide(counted_wires);
    hide(ordered_gate_layout);
    reveal(canonical_vm_layout);
    let prefix = wiring_prefix_len(source, inputs, outputs);
    assert(prefix == wiring_prefix_len(target, inputs, outputs));
    assert(wiring_prefix(target, inputs, outputs, bytes.take(prefix))) by { reveal(wiring_prefix); }
    let first = source.storage_model();
    let second = target.storage_model();
    assert forall|i: int| 0 <= i < first.len() implies {
        let device = #[trigger] first[i];
        let next = second[i];
        &&& same_ordered_storage_wiring(&device.wiring_model(), &next.wiring_model())
        &&& storage_memory_len(&device) == storage_memory_len(&next)
    } by {
        assert(source.storage_model()[i] == first[i]);
    }
    storage_table_transfers(first, second, first.len(), bytes.skip(prefix));
}

/// ポートの区画と配線が同じ VM では、現在の状態値に関わらず配線表は一致する。
pub proof fn canonical_vm_layout_agrees(
    first_vm: &ClockedVm, second_vm: &ClockedVm,
    inputs: Seq<Range<usize>>, outputs: Seq<Range<usize>>, first: Seq<u8>, second: Seq<u8>,
)
    requires
        checkpoint_vms_compatible(first_vm, second_vm),
        canonical_vm_layout(first_vm, inputs, outputs, first),
        canonical_vm_layout(second_vm, inputs, outputs, second),
    ensures first == second,
{
    canonical_vm_layout_transfers(first_vm, second_vm, inputs, outputs, first);
    reveal(canonical_vm_layout);
    let devices = second_vm.storage_model();
    let prefix = wiring_prefix_len(second_vm, inputs, outputs);
    wiring_prefix_agrees(second_vm, second_vm, inputs, outputs, first.take(prefix), second.take(prefix));
    storage_tables_agree(devices, devices, devices.len(), first.skip(prefix), second.skip(prefix));
    assert(first =~= first.take(prefix) + first.skip(prefix));
    assert(second =~= second.take(prefix) + second.skip(prefix));
}

} // verus!
