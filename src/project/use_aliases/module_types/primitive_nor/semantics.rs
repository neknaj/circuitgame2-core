//! 展開前の束縛からソース回路を定め、tick 実行用ネットリストと照合する。

use super::{ClockedNor, ModuleCalls, ModuleBodyPosition, NorNetlist, OutputDriver, PrimitiveOperand, UseAliases, Wire, driver_wire, one_bit_ports};
use crate::netlist::{
    SourceGateId, SourceNor, SourceTickCircuit, SourceTickFrame, SourceWire, TickFrame, nor_trace,
    source_clocked_layout, source_clocked_layout_from_pairs, source_output_pair_at, source_output_pairs, source_tick_trace, source_trace_from_flat,
    source_wire_pair, wire_available,
};
use vstd::prelude::*;
use vstd::{string::StringSliceAdditionalSpecFns, utf8::encode_utf8_decode_utf8};

verus! {

spec fn gate_sites(checked: &ModuleCalls) -> Seq<SourceGateId> {
    let n = checked.module.expressions.typed.sources.roots.wiring.drivers.definitions@.len();
    Seq::new(n, |i: int| SourceGateId { instance: Seq::empty(), gate: checked.calls@[i].at })
}

spec fn gate_index(sites: Seq<SourceGateId>) -> Map<SourceGateId, int> {
    Map::new(sites.to_set(), |site: SourceGateId| sites.index_of(site))
}

spec fn source_driver(sites: Seq<SourceGateId>, driver: OutputDriver) -> SourceWire {
    match driver {
        OutputDriver::Input(i) => SourceWire::Input(i),
        OutputDriver::Definition(i) => SourceWire::Gate(sites[i as int]),
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn source_operand(&self, checked: &ModuleCalls, i: int, arg: int) -> SourceWire {
        let operand = choose|operand: PrimitiveOperand| #[trigger] self.primitive_operand_resolves(checked, i, arg, operand);
        match operand {
            PrimitiveOperand::Driver(driver) => source_driver(gate_sites(checked), driver),
            PrimitiveOperand::Literal(bit) => SourceWire::Constant(bit),
        }
    }

    spec fn primitive_source_graph(&self, checked: &ModuleCalls) -> SourceTickCircuit {
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        let sites = gate_sites(checked);
        let index = gate_index(sites);
        SourceTickCircuit {
            input_count: drivers.signature.inputs@.len() as usize,
            gates: Map::new(index.dom(), |site: SourceGateId| SourceNor {
                left: self.source_operand(checked, index[site], 0),
                right: self.source_operand(checked, index[site], 1),
            }),
            outputs: Seq::new(drivers.outputs@.len(), |i: int| source_driver(sites, drivers.outputs@[i])),
        }
    }

    spec fn primitive_source_supported(&self, checked: &ModuleCalls) -> bool {
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        &&& one_bit_ports(drivers.signature.inputs@, drivers.signature.inputs@.len() as int)
        &&& one_bit_ports(drivers.signature.outputs@, drivers.signature.outputs@.len() as int)
        &&& forall|i: int| 0 <= i < drivers.definitions@.len() ==> #[trigger] self.primitive_definition_supported(checked, i)
            && exists|a: PrimitiveOperand, b: PrimitiveOperand|
                #![trigger self.primitive_operand_resolves(checked, i, 0, a), self.primitive_operand_resolves(checked, i, 1, b)]
                self.primitive_operand_resolves(checked, i, 0, a) && self.primitive_operand_resolves(checked, i, 1, b)
    }

    /// 展開前の束縛、定数、出力宣言からソース回路が得られることを表す。
    pub closed spec fn primitive_module_source(&self, owner: ModuleBodyPosition, limit: u64, source: SourceTickCircuit) -> bool {
        exists|checked: ModuleCalls| #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
            && self.primitive_source_supported(&checked)
            && source == self.primitive_source_graph(&checked)
    }

    proof fn primitive_operands_agree(&self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls,
        index: int, arg: int, first: PrimitiveOperand, second: PrimitiveOperand,
    )
        requires
            self.can_resolve(),
            self.module_calls_result(owner, limit, Ok(Some(*checked))),
            0 <= index < checked.calls@.len(),
            self.primitive_operand_resolves(checked, index, arg, first),
            self.primitive_operand_resolves(checked, index, arg, second),
        ensures first == second,
    {
        let call = checked.calls@[index];
        let parsed = self.targets.project_model().circuits_model()[call.at.file as int];
        let root = call.inputs.ports.arguments@[arg];
        let form = parsed.syntax.forms@[root as int];
        if form is Atom && form->Atom_kind is Name {
            self.module_argument_bindings_agree(owner, limit, checked, index, arg, first->Driver_0, second->Driver_0);
        } else {
            reveal_strlit("0");
            reveal_strlit("1");
            assert("0"@ != "1"@);
            encode_utf8_decode_utf8("0"@);
            encode_utf8_decode_utf8("1"@);
            assert("0".spec_bytes() != "1".spec_bytes());
        }
    }

    proof fn primitive_source_operand_pair(&self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls,
        index: int, arg: int, wire: Wire,
    )
        requires
            self.can_resolve(),
            self.module_calls_result(owner, limit, Ok(Some(*checked))), 0 <= index < checked.calls@.len(),
            self.primitive_operand_matches(checked, index, arg, wire),
            wire_available(wire, checked.module.expressions.typed.sources.roots.wiring.drivers.signature.inputs@.len(),
                gate_sites(checked).len()),
        ensures source_wire_pair(gate_sites(checked), self.source_operand(checked, index, arg), wire),
    {
        let operand = choose|operand: PrimitiveOperand| #[trigger] self.primitive_operand_resolves(checked, index, arg, operand)
            && wire == match operand {
                PrimitiveOperand::Driver(driver) => driver_wire(driver),
                PrimitiveOperand::Literal(bit) => Wire::Constant(bit),
            };
        let source = choose|operand: PrimitiveOperand| #[trigger] self.primitive_operand_resolves(checked, index, arg, operand);
        self.primitive_operands_agree(owner, limit, checked, index, arg, operand, source);
    }

    proof fn primitive_layout_from_checked(&self, owner: ModuleBodyPosition, limit: u64, checked: &ModuleCalls,
        netlist: &NorNetlist,
    )
        requires self.can_resolve(), self.module_calls_result(owner, limit, Ok(Some(*checked))),
            self.primitive_netlist_matches(checked, netlist),
        ensures source_clocked_layout(&self.primitive_source_graph(checked), netlist, gate_sites(checked),
            gate_index(gate_sites(checked))),
            self.primitive_source_supported(checked),
    {
        self.module_calls_type_evidence(owner, limit, checked);
        self.module_output_types_evidence(owner, limit, checked.module);
        self.module_selections_evidence(owner, limit, checked.module.expressions);
        reveal(UseAliases::primitive_gate_prefix);
        let drivers = &checked.module.expressions.typed.sources.roots.wiring.drivers;
        let sites = gate_sites(checked);
        let index = gate_index(sites);
        let source = self.primitive_source_graph(checked);
        assert forall|i: int, j: int| #![trigger sites[i], sites[j]]
            0 <= i < j < sites.len() implies sites[i] != sites[j] by {
            assert(self.primitive_gate_matches(checked, i, netlist.gates@[i]));
            assert(self.primitive_gate_matches(checked, j, netlist.gates@[j]));
            if sites[i] == sites[j] {
                self.module_driver_origins_distinct(owner, limit, *drivers, i, j);
            }
        };
        assert forall|i: int| 0 <= i < drivers.definitions@.len() implies
            #[trigger] self.primitive_definition_supported(checked, i)
                && exists|a: PrimitiveOperand, b: PrimitiveOperand|
                    #![trigger self.primitive_operand_resolves(checked, i, 0, a), self.primitive_operand_resolves(checked, i, 1, b)]
                    self.primitive_operand_resolves(checked, i, 0, a) && self.primitive_operand_resolves(checked, i, 1, b) by {
            let flat = netlist.gates@[i];
            assert(self.primitive_gate_matches(checked, i, flat));
            let a = choose|v: PrimitiveOperand| #[trigger] self.primitive_operand_resolves(checked, i, 0, v);
            let b = choose|v: PrimitiveOperand| #[trigger] self.primitive_operand_resolves(checked, i, 1, v);
            assert(self.primitive_operand_resolves(checked, i, 0, a) && self.primitive_operand_resolves(checked, i, 1, b));
        };
        sites.to_set_ensures();
        assert forall|site: SourceGateId| index.dom().contains(site) implies
            0 <= #[trigger] index[site] < sites.len() && sites[index[site]] == site by {
            assert(sites.contains(site));
        };
        assert forall|i: int| 0 <= i < sites.len() implies {
            let site = #[trigger] sites[i];
            let flat = netlist.gates@[i];
            &&& index.dom().contains(site) && index[site] == i
            &&& wire_available(flat.left, netlist.input_count as nat, sites.len())
            &&& wire_available(flat.right, netlist.input_count as nat, sites.len())
            &&& source_wire_pair(sites, source.gates[site].left, flat.left)
            &&& source_wire_pair(sites, source.gates[site].right, flat.right)
        } by {
            let site = sites[i];
            assert(index.dom().contains(site));
            assert(sites[index[site]] == site);
            assert(index[site] == i);
            let flat = netlist.gates@[i];
            assert(self.primitive_gate_matches(checked, i, flat));
            self.primitive_source_operand_pair(owner, limit, checked, i, 0, flat.left);
            self.primitive_source_operand_pair(owner, limit, checked, i, 1, flat.right);
        };
        assert(source_output_pairs(&source, netlist, sites)) by {
            reveal(source_output_pairs);
            assert(source.outputs.len() == netlist.outputs@.len());
            assert forall|i: int| 0 <= i < source.outputs.len() implies
                #[trigger] source_output_pair_at(&source, netlist, sites, i) by {
                self.module_output_driver(owner, limit, *drivers, i);
                assert(netlist.outputs@[i] == driver_wire(drivers.outputs@[i]));
                assert(source.outputs[i] == source_driver(sites, drivers.outputs@[i]));
            };
        };
        source_clocked_layout_from_pairs(&source, netlist, sites, index);
    }

    /// 変換済みの回路から、ソース回路とゲート番号の対応を取り出す。
    pub proof fn primitive_module_layout(
        &self, owner: ModuleBodyPosition, limit: u64, circuit: &ClockedNor,
    ) -> (layout: (SourceTickCircuit, Seq<SourceGateId>, Map<SourceGateId, int>))
        requires self.can_resolve(), self.primitive_module_result(owner, limit, Ok(Some(*circuit))),
        ensures self.primitive_module_source(owner, limit, layout.0),
            source_clocked_layout(&layout.0, &circuit.netlist_model(), layout.1, layout.2),
    {
        let netlist = circuit.netlist_model();
        let checked = choose|checked: ModuleCalls| #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
            && self.primitive_netlist_matches(&checked, &netlist);
        let source = self.primitive_source_graph(&checked);
        self.primitive_layout_from_checked(owner, limit, &checked, &netlist);
        (source, gate_sites(&checked), gate_index(gate_sites(&checked)))
    }

    /// ソースからの変換に成功した回路は、同じ有限入力列に対する公開出力を保存する。
    pub proof fn primitive_module_trace_preserved(
        &self, owner: ModuleBodyPosition, limit: u64, circuit: &ClockedNor, inputs: Seq<Seq<bool>>, trace: Seq<TickFrame>,
    ) -> (source_trace: (SourceTickCircuit, Seq<SourceTickFrame>))
        requires self.can_resolve(), self.primitive_module_result(owner, limit, Ok(Some(*circuit))),
            nor_trace(&circuit.netlist_model(), inputs, trace),
        ensures
            self.primitive_module_source(owner, limit, source_trace.0),
            source_tick_trace(&source_trace.0, inputs, source_trace.1),
            source_trace.1.len() == trace.len(),
            forall|i: int| 0 <= i < trace.len() ==> (#[trigger] source_trace.1[i]).outputs == trace[i].outputs@,
    {
        let (source, sites, index) = self.primitive_module_layout(owner, limit, circuit);
        let frames = source_trace_from_flat(&source, &circuit.netlist_model(), sites, index, inputs, trace);
        (source, frames)
    }
}

} // verus!
