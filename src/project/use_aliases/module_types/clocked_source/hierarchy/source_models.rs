//! 到達する宣言のソース回路と、より先に定まる子回路の関係を表す。

use super::{ModuleBodyPosition, ModuleCallTarget, ModuleCalls, ModuleSourceLayout, UseAliases};
use crate::netlist::{NorNetlist, SourceGateId, SourceTickCircuit, SourceTickFrame, TickFrame, nor_trace,
    source_clocked_layout, source_tick_trace, source_trace_from_flat};
use vstd::prelude::*;

verus! {

pub(super) open spec fn child_source_at(positions: Seq<ModuleBodyPosition>, rank: Seq<nat>,
    table: Seq<Option<ModuleSourceLayout>>, parent: int, expected: ModuleBodyPosition, source: SourceTickCircuit,
    child: int) -> bool
{
    &&& 0 <= child < table.len()
    &&& positions[child] == expected && rank[child] < rank[parent]
    &&& table[child] matches Some(layout) && layout.circuit == source
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) open spec fn source_function_in_layer(&self, limit: u64, position: ModuleBodyPosition,
        layout: ModuleSourceLayout, call: int) -> bool {
        exists|order: Seq<SourceGateId>| #[trigger] self.reachable_function_source_circuit(
            (position.file, position.entry), limit, layout.layer.children_model()[call], order)
    }

    pub(super) open spec fn source_call_in_table(&self, checked: &ModuleCalls, limit: u64, layout: ModuleSourceLayout,
        positions: Seq<ModuleBodyPosition>, rank: Seq<nat>, table: Seq<Option<ModuleSourceLayout>>, node: int, call: int,
    ) -> bool {
        let target = checked.calls@[call].inputs.ports.signature.target;
        match target {
            ModuleCallTarget::Routine { position, .. } => self.source_function_in_layer(limit, position, layout, call)
                || (exists|i: int| #[trigger]
                    child_source_at(positions, rank, table, node, position, layout.layer.children_model()[call], i)),
            ModuleCallTarget::Nor => true,
            ModuleCallTarget::StateElement { .. } => false,
        }
    }

    spec fn source_table_entry(&self, owner: ModuleBodyPosition, limit: u64, checked: Option<ModuleCalls>,
        layout: ModuleSourceLayout) -> bool
    {
        &&& layout.owner == owner
        &&& checked matches Some(calls) && self.module_calls_result(owner, limit, Ok(Some(calls)))
            && self.module_source_layer(&calls, &layout.circuit, &layout.layer)
            && layout.layer.children_model().len() == calls.calls@.len()
    }

    pub(super) closed spec fn source_model_table(&self, positions: Seq<ModuleBodyPosition>, limit: u64,
        modules: Seq<Option<ModuleCalls>>, rank: Seq<nat>, table: Seq<Option<ModuleSourceLayout>>) -> bool
    {
        &&& positions.len() == table.len() == rank.len() == modules.len()
        &&& forall|i: int| 0 <= i < table.len() && (#[trigger] table[i]).is_some() ==>
            self.source_table_entry(positions[i], limit, modules[i], table[i]->Some_0)
        &&& forall|i: int, c: int| 0 <= i < table.len() && table[i].is_some() && 0 <= c < modules[i]->Some_0.calls@.len() ==>
            #[trigger] self.source_call_in_table(&modules[i]->Some_0, limit, table[i]->Some_0, positions, rank, table, i, c)
    }

    pub(super) proof fn empty_source_table(&self, positions: Seq<ModuleBodyPosition>, limit: u64,
        modules: Seq<Option<ModuleCalls>>, rank: Seq<nat>, table: Seq<Option<ModuleSourceLayout>>)
        requires positions.len() == table.len() == rank.len() == modules.len(),
            forall|i: int| 0 <= i < table.len() ==> (#[trigger] table[i]).is_none(),
        ensures self.source_model_table(positions, limit, modules, rank, table),
    {
    }

    pub(super) proof fn source_call_for_child(&self, checked: &ModuleCalls, limit: u64, layout: ModuleSourceLayout,
        positions: Seq<ModuleBodyPosition>, rank: Seq<nat>, table: Seq<Option<ModuleSourceLayout>>, node: int,
        call: int, child: int)
        requires
            0 <= node < table.len() == positions.len() == rank.len(),
            0 <= call < checked.calls@.len() == layout.layer.children_model().len(),
            0 <= child < table.len(), rank[child] < rank[node],
            checked.calls@[call].inputs.ports.signature.target matches ModuleCallTarget::Routine { position, .. }
                && positions[child] == position,
            table[child] matches Some(prior) && prior.circuit == layout.layer.children_model()[call],
        ensures self.source_call_in_table(checked, limit, layout, positions, rank, table, node, call),
    {
        assert(child_source_at(positions, rank, table, node, positions[child], layout.layer.children_model()[call], child));
    }

    // 既存の宣言が参照する子は、どれも追加前の表で確定している。
    pub(super) proof fn extend_source_table(&self, positions: Seq<ModuleBodyPosition>, limit: u64,
        modules: Seq<Option<ModuleCalls>>, rank: Seq<nat>, table: Seq<Option<ModuleSourceLayout>>,
        node: int, layout: ModuleSourceLayout)
        requires
            self.source_model_table(positions, limit, modules, rank, table),
            0 <= node < table.len(), table[node].is_none(),
            modules[node].is_some(),
            self.module_calls_result(positions[node], limit, Ok(modules[node])),
            layout.owner == positions[node],
            self.module_source_layer(&modules[node]->Some_0, &layout.circuit, &layout.layer),
            layout.layer.children_model().len() == modules[node]->Some_0.calls@.len(),
            forall|c: int| 0 <= c < modules[node]->Some_0.calls@.len() ==>
                #[trigger] self.source_call_in_table(&modules[node]->Some_0, limit, layout, positions, rank, table, node, c),
        ensures self.source_model_table(positions, limit, modules, rank, table.update(node, Some(layout))),
    {
        let next = table.update(node, Some(layout));
        assert forall|i: int| 0 <= i < next.len() && (#[trigger] next[i]).is_some() implies
            self.source_table_entry(positions[i], limit, modules[i], next[i]->Some_0) by {
            if i != node {
                assert(next[i] == table[i]);
            }
        };
        assert forall|i: int, c: int| 0 <= i < next.len() && next[i].is_some() && 0 <= c < modules[i]->Some_0.calls@.len()
            implies #[trigger] self.source_call_in_table(&modules[i]->Some_0, limit, next[i]->Some_0, positions, rank, next, i, c) by {
            let checked = &modules[i]->Some_0;
            let parent = next[i]->Some_0;
            if i != node { assert(next[i] == table[i]); }
            assert(self.source_call_in_table(checked, limit, parent, positions, rank, table, i, c));
            if let ModuleCallTarget::Routine { position, .. } = checked.calls@[c].inputs.ports.signature.target {
                if !self.source_function_in_layer(limit, position, parent, c) {
                    let child = choose|j: int| #[trigger]
                        child_source_at(positions, rank, table, i, position, parent.layer.children_model()[c], j);
                    assert(child != node);
                    assert(next[child] == table[child]);
                    assert(child_source_at(positions, rank, next, i, position, parent.layer.children_model()[c], child));
                }
            }
        };
    }

    /// 宣言の呼び出しと配線に従って、ルートの参照回路が組み立てられていることを表す。
    pub closed spec fn clocked_module_source(&self, owner: ModuleBodyPosition, width_limit: u64,
        source: &SourceTickCircuit) -> bool
    {
        exists|positions: Seq<ModuleBodyPosition>, modules: Seq<Option<ModuleCalls>>, rank: Seq<nat>,
            table: Seq<Option<ModuleSourceLayout>>|
            #[trigger] self.source_model_table(positions, width_limit, modules, rank, table)
            && table.len() > 0 && positions[0] == owner && table[0].is_some() && table[0]->Some_0.circuit == *source
            && (forall|i: int, j: int| 0 <= i < j < positions.len() ==> #[trigger] positions[i] != #[trigger] positions[j])
    }

    /// ネットリストの配線が、ソース上のゲートと公開出力に対応することを表す。
    pub closed spec fn clocked_module_source_layout(&self, owner: ModuleBodyPosition, width_limit: u64,
        netlist: &NorNetlist) -> bool
    {
        exists|source: SourceTickCircuit, order: Seq<SourceGateId>, index: Map<SourceGateId, int>|
            #[trigger] source_clocked_layout(&source, netlist, order, index)
            && self.clocked_module_source(owner, width_limit, &source)
    }

    pub(super) proof fn source_model_for_root(&self, owner: ModuleBodyPosition, limit: u64,
        positions: Seq<ModuleBodyPosition>, modules: Seq<Option<ModuleCalls>>, rank: Seq<nat>,
        table: Seq<Option<ModuleSourceLayout>>, netlist: &NorNetlist)
        requires
            self.source_model_table(positions, limit, modules, rank, table),
            0 < positions.len(), positions[0] == owner, 0 < table.len(),
            forall|i: int, j: int| 0 <= i < j < positions.len() ==> #[trigger] positions[i] != #[trigger] positions[j],
            table[0] matches Some(layout) ==> source_clocked_layout(&layout.circuit, netlist, layout.order, layout.index),
            table[0].is_some(),
        ensures self.clocked_module_source_layout(owner, limit, netlist),
    {
        let layout = table[0]->Some_0;
        assert(self.clocked_module_source(owner, limit, &layout.circuit)) by {
            assert(self.source_model_table(positions, limit, modules, rank, table));
        };
        assert(source_clocked_layout(&layout.circuit, netlist, layout.order, layout.index));
    }

    /// reset 直後と、任意の有限入力列を適用した各 tick で、ソースと VM の公開出力が一致することを示す。
    pub proof fn clocked_module_trace_preserved(&self, owner: ModuleBodyPosition, width_limit: u64, netlist: &NorNetlist,
        inputs: Seq<Seq<bool>>, trace: Seq<TickFrame>) -> (result: (SourceTickCircuit, Seq<SourceTickFrame>))
        requires self.clocked_module_source_layout(owner, width_limit, netlist), nor_trace(netlist, inputs, trace),
        ensures self.clocked_module_source(owner, width_limit, &result.0), source_tick_trace(&result.0, inputs, result.1),
            result.1.len() == trace.len(),
            forall|i: int| 0 <= i < trace.len() ==> (#[trigger] result.1[i]).outputs == trace[i].outputs@,
    {
        let (source, order, index) = choose|source: SourceTickCircuit, order: Seq<SourceGateId>, index: Map<SourceGateId, int>|
            #[trigger] source_clocked_layout(&source, netlist, order, index)
            && self.clocked_module_source(owner, width_limit, &source);
        let frames = source_trace_from_flat(&source, netlist, order, index, inputs, trace);
        (source, frames)
    }
}

} // verus!
