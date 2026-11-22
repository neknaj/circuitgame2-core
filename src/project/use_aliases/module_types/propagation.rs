//! 裸の信号参照を依存順にたどり、型と型を決めた位置を引き継ぐ。

use super::{ModuleAliasSource, ModuleRootTypesError, ModuleTypeSources, UseAliases};
use crate::project::{LocatedName, ModuleBodyPosition, OutputDriver, SignalType, TypedPort};
use crate::project::use_aliases::{dependency_order::{DependencyEdge, check_dependency_order}, function_atoms::{copy_location, copy_signal_type}};
#[cfg(verus_only)]
use crate::project::use_aliases::dependency_order::{complete_dependency_order, completion_order_matches,
    dependencies_in_order, dependency_cycle, dependency_edge, dependency_graph_valid, graph_has_cycle};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 裸の信号参照だけで閉じる循環を構成する一つの参照。
#[derive(Debug)]
pub struct ModuleAliasCycleStep<'p, 'a> {
    /// 参照を書いた定義の左辺。全断片の駆動元を並べた列の添字。
    pub definition: usize,
    /// 右辺に信号名を書いた範囲。
    pub reference: LocatedName<'p, 'a>,
}

/// 型が決まった式や入力から、裸の信号参照を介して得られた型。
#[derive(Debug)]
pub struct ModuleAliasTypes<'p, 'a> {
    /// 型伝播の起点と、全断片の配線・依存先。
    pub sources: ModuleTypeSources<'p, 'a>,
    /// 左辺の駆動元順の型。型が決まっていない式に依存する場合は `None`。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

/// 裸の信号参照を介した型伝播までに見つかった違反。
#[derive(Debug)]
pub enum ModuleAliasTypesError<'p, 'a> {
    /// 配線、通常呼び出し、またはビット選択の診断。
    Sources(ModuleRootTypesError<'p, 'a>),
    /// 裸の信号参照だけで閉じる循環。末尾の参照は先頭の定義へ戻る。
    Cycle(Vec<ModuleAliasCycleStep<'p, 'a>>),
}

spec fn definition_dependency(alias: Option<ModuleAliasSource>) -> Option<usize> {
    match alias {
        Some(alias) => match alias.driver { OutputDriver::Definition(index) => Some(index), _ => None },
        None => None,
    }
}

#[verifier::opaque]
spec fn graph_matches(aliases: Seq<Option<ModuleAliasSource>>, graph: Seq<Vec<Option<usize>>>) -> bool {
    &&& graph.len() <= aliases.len()
    &&& forall|i: int| 0 <= i < graph.len() ==> {
        let row = #[trigger] graph[i];
        row@ == seq![definition_dependency(aliases[i])]
    }
}

fn alias_graph(aliases: &[Option<ModuleAliasSource>]) -> (graph: Vec<Vec<Option<usize>>>)
    requires forall|i: int| 0 <= i < aliases@.len() ==>
        (definition_dependency(#[trigger] aliases@[i]) matches Some(dependency) ==> dependency < aliases@.len()),
    ensures graph@.len() == aliases@.len(), graph_matches(aliases@, graph@), dependency_graph_valid(graph@),
{
    let mut graph = Vec::new();
    assert(graph_matches(aliases@, graph@)) by { reveal(graph_matches); };
    let mut i = 0;
    while i < aliases.len()
        invariant i == graph@.len() <= aliases@.len(), graph_matches(aliases@, graph@),
        decreases aliases@.len() - i,
    {
        let target = match &aliases[i] {
            Some(alias) => match alias.driver { OutputDriver::Definition(index) => Some(index), OutputDriver::Input(_) => None },
            None => None,
        };
        let mut row = Vec::new();
        row.push(target);
        assert(row@ =~= seq![definition_dependency(aliases@[i as int])]);
        let ghost prior = graph@;
        graph.push(row);
        assert(graph_matches(aliases@, graph@)) by {
            reveal(graph_matches);
            assert forall|j: int| 0 <= j < graph@.len() implies
                (#[trigger] graph@[j])@ == seq![definition_dependency(aliases@[j])] by {
                    if j < i { assert(graph@[j] == prior[j]); }
            };
        };
        i += 1;
    }
    reveal(graph_matches);
    assert forall|row: int, field: int| 0 <= row < graph@.len() && 0 <= field < graph@[row]@.len()
        implies ((#[trigger] graph@[row]@[field]) matches Some(target) ==> target < graph@.len()) by {
        assert(field == 0 && graph@[row]@[field] == definition_dependency(aliases@[row]));
    };
    graph
}

spec fn inherited_type<'p, 'a>(
    inputs: Seq<TypedPort<'p, 'a>>, seeds: Seq<Option<SignalType<'p, 'a>>>, aliases: Seq<Option<ModuleAliasSource<'p, 'a>>>,
    types: Seq<Option<SignalType<'p, 'a>>>, index: int,
) -> Option<SignalType<'p, 'a>> {
    match aliases[index] {
        None => seeds[index],
        Some(alias) => match alias.driver {
            OutputDriver::Input(index) => {
                let port = inputs[index as int];
                Some(SignalType { ty: port.ty, origin: port.annotation })
            },
            OutputDriver::Definition(index) => types[index as int],
        },
    }
}

#[verifier::opaque]
spec fn visited_types(
    inputs: Seq<TypedPort>, seeds: Seq<Option<SignalType>>, aliases: Seq<Option<ModuleAliasSource>>,
    rank: Seq<nat>, stop: int, types: Seq<Option<SignalType>>,
) -> bool {
    &&& types.len() == aliases.len() && types.len() == seeds.len()
    &&& forall|i: int| 0 <= i < types.len() && rank[i] < stop ==>
        #[trigger] types[i] == inherited_type(inputs, seeds, aliases, types, i)
}

proof fn dependency_precedes(
    aliases: Seq<Option<ModuleAliasSource>>, graph: Seq<Vec<Option<usize>>>, rank: Seq<nat>, node: usize, target: usize,
)
    requires
        graph_matches(aliases, graph), graph.len() == aliases.len(), node < graph.len(), target < graph.len(),
        definition_dependency(aliases[node as int]) == Some(target), dependencies_in_order(graph, rank),
    ensures rank[target as int] < rank[node as int],
{
    reveal(graph_matches);
    let edge = DependencyEdge { from: node, field: 0, to: target };
    assert(dependency_edge(graph, edge));
}

fn propagate_types<'p, 'a>(inputs: &[TypedPort<'p, 'a>], seeds: &[Option<SignalType<'p, 'a>>],
    aliases: &[Option<ModuleAliasSource<'p, 'a>>], _graph: &[Vec<Option<usize>>], order: &[usize],
) -> (types: Vec<Option<SignalType<'p, 'a>>>)
    requires
        aliases@.len() == seeds@.len(),
        graph_matches(aliases@, _graph@), _graph@.len() == aliases@.len(),
        complete_dependency_order(_graph@, order@),
        forall|i: int| 0 <= i < aliases@.len() ==>
            ((#[trigger] aliases@[i]) matches Some(alias) ==> match alias.driver {
                OutputDriver::Input(index) => index < inputs@.len(),
                OutputDriver::Definition(index) => index < aliases@.len(),
            }),
    ensures
        types@.len() == seeds@.len(),
        forall|i: int| 0 <= i < types@.len() ==> #[trigger] types@[i] == inherited_type(inputs@, seeds@, aliases@, types@, i),
{
    let ghost rank = choose|rank: Seq<nat>| #[trigger] dependencies_in_order(_graph@, rank)
        && completion_order_matches(order@, rank) && (forall|node: int| #![trigger rank[node]] 0 <= node < _graph@.len()
            ==> rank[node] < order@.len() && order@[rank[node] as int] == node);
    let mut types = Vec::new();
    let mut i = 0;
    while i < seeds.len()
        invariant i == types@.len() <= seeds@.len(),
        decreases seeds@.len() - i,
    {
        types.push(None);
        i += 1;
    }
    assert(visited_types(inputs@, seeds@, aliases@, rank, 0, types@)) by { reveal(visited_types); };
    i = 0;
    while i < order.len()
        invariant
            i <= order@.len() == aliases@.len() == types@.len() == seeds@.len(),
            graph_matches(aliases@, _graph@), _graph@.len() == aliases@.len(),
            dependencies_in_order(_graph@, rank), completion_order_matches(order@, rank),
            forall|node: int| #![trigger rank[node]] 0 <= node < aliases@.len()
                ==> rank[node] < order@.len() && order@[rank[node] as int] == node,
            forall|j: int| 0 <= j < aliases@.len() ==>
                ((#[trigger] aliases@[j]) matches Some(alias) ==> match alias.driver {
                    OutputDriver::Input(index) => index < inputs@.len(),
                    OutputDriver::Definition(index) => index < aliases@.len(),
                }),
            visited_types(inputs@, seeds@, aliases@, rank, i as int, types@),
        decreases order@.len() - i,
    {
        let node = order[i];
        assert(node < types@.len() && rank[node as int] == i);
        let ty = match &aliases[node] {
            None => copy_signal_type(&seeds[node]),
            Some(alias) => match alias.driver {
                OutputDriver::Input(index) => {
                    let input = &inputs[index];
                    Some(SignalType { ty: input.ty, origin: copy_location(&input.annotation) })
                },
                OutputDriver::Definition(index) => copy_signal_type(&types[index]),
            },
        };
        assert(ty == inherited_type(inputs@, seeds@, aliases@, types@, node as int));
        let ghost prior = types@;
        types.set(node, ty);
        assert(visited_types(inputs@, seeds@, aliases@, rank, i + 1, types@)) by {
            reveal(visited_types);
            assert forall|j: int| 0 <= j < types@.len() && rank[j] <= i implies
                #[trigger] types@[j] == inherited_type(inputs@, seeds@, aliases@, types@, j) by {
                if let Some(target) = definition_dependency(aliases@[j]) {
                    let alias = aliases@[j]->Some_0;
                    assert(alias.driver == OutputDriver::Definition(target));
                    dependency_precedes(aliases@, _graph@, rank, j as usize, target);
                    assert(target != node && types@[target as int] == prior[target as int]);
                }
                if j != node {
                    assert(rank[j] < i) by {
                        assert(order@[rank[j] as int] == j);
                    };
                    assert(types@[j] == prior[j]);
                }
            };
        };
        i += 1;
    }
    reveal(visited_types);
    types
}

spec fn cycle_at(aliases: Seq<Option<ModuleAliasSource>>, steps: Seq<ModuleAliasCycleStep>, index: int) -> bool {
    let step = steps[index];
    let successor = if index + 1 < steps.len() { index + 1 } else { 0 };
    let next = steps[successor];
    &&& step.definition < aliases.len()
    &&& aliases[step.definition as int] matches Some(alias)
    &&& alias.driver == OutputDriver::Definition(next.definition)
    &&& alias.reference == step.reference
}

spec fn source_cycle(aliases: Seq<Option<ModuleAliasSource>>, steps: Seq<ModuleAliasCycleStep>) -> bool {
    &&& 0 < steps.len()
    &&& forall|i: int| 0 <= i < steps.len() ==> #[trigger] cycle_at(aliases, steps, i)
}

fn locate_cycle<'p, 'a>(aliases: &[Option<ModuleAliasSource<'p, 'a>>], _graph: &[Vec<Option<usize>>], cycle: &[DependencyEdge])
    -> (steps: Vec<ModuleAliasCycleStep<'p, 'a>>)
    requires graph_matches(aliases@, _graph@), _graph@.len() == aliases@.len(), dependency_cycle(_graph@, cycle@),
    ensures source_cycle(aliases@, steps@),
{
    let mut steps: Vec<ModuleAliasCycleStep<'p, 'a>> = Vec::new();
    let mut i = 0;
    while i < cycle.len()
        invariant
            graph_matches(aliases@, _graph@), _graph@.len() == aliases@.len(), dependency_cycle(_graph@, cycle@),
            i == steps@.len() <= cycle@.len(),
            forall|j: int| 0 <= j < i ==> {
                let step = #[trigger] steps@[j];
                &&& step.definition == cycle@[j].from < aliases@.len()
                &&& aliases@[step.definition as int] matches Some(alias)
                &&& alias.driver == OutputDriver::Definition(cycle@[j].to) && alias.reference == step.reference
            },
        decreases cycle@.len() - i,
    {
        let edge = cycle[i];
        proof {
            reveal(graph_matches);
            assert(dependency_edge(_graph@, edge));
            assert(_graph@[edge.from as int]@ == seq![definition_dependency(aliases@[edge.from as int])]);
        }
        let Some(alias) = &aliases[edge.from] else {
            proof { assert(false); }
            unreachable!()
        };
        let step = ModuleAliasCycleStep { definition: edge.from, reference: copy_location(&alias.reference) };
        let ghost prior = steps@;
        steps.push(step);
        assert forall|j: int| 0 <= j <= i implies {
            let step = #[trigger] steps@[j];
            &&& step.definition == cycle@[j].from < aliases@.len()
            &&& aliases@[step.definition as int] matches Some(alias)
            &&& alias.driver == OutputDriver::Definition(cycle@[j].to) && alias.reference == step.reference
        } by { if j < i { assert(steps@[j] == prior[j]); } };
        i += 1;
    }
    assert forall|j: int| 0 <= j < steps@.len() implies #[trigger] cycle_at(aliases@, steps@, j) by {
        let next = if j + 1 < steps@.len() { j + 1 } else { 0 };
        assert(cycle@[j].to == cycle@[next].from);
    };
    steps
}

spec fn alias_types_match(sources: ModuleTypeSources, types: Seq<Option<SignalType>>) -> bool {
    let inputs = sources.roots.wiring.drivers.signature.inputs@;
    let seeds = sources.roots.types@;
    let aliases = sources.aliases@;
    &&& types.len() == seeds.len() == aliases.len()
    &&& forall|i: int| 0 <= i < types.len() ==> #[trigger] types[i] == inherited_type(inputs, seeds, aliases, types, i)
    &&& exists|graph: Vec<Vec<Option<usize>>>| #[trigger] graph_matches(aliases, graph@)
        && graph@.len() == aliases.len() && !graph_has_cycle(graph@)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 伝播の結果または循環の各辺を、元の配線に対応付ける。
    pub closed spec fn module_alias_types_result(
        &self, owner: ModuleBodyPosition, limit: u64, result: Result<Option<ModuleAliasTypes>, ModuleAliasTypesError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_type_sources_result(owner, limit, Ok(None)),
            Err(ModuleAliasTypesError::Sources(error)) => self.module_type_sources_result(owner, limit, Err(error)),
            Ok(Some(checked)) => self.module_type_sources_result(owner, limit, Ok(Some(checked.sources)))
                && alias_types_match(checked.sources, checked.types@),
            Err(ModuleAliasTypesError::Cycle(steps)) => exists|sources: ModuleTypeSources|
                #[trigger] self.module_type_sources_result(owner, limit, Ok(Some(sources)))
                && source_cycle(sources.aliases@, steps@),
        }
    }

    /// 全断片で、裸の信号参照を介して入力や右辺から型を引き継ぐ。
    ///
    /// 型の根拠には、引き継ぐ前の宣言や式の範囲が残る。型が未確定の式は後段で扱う。
    ///
    /// # Errors
    ///
    /// 配線、通常呼び出し、ビット選択の違反を先に返す。裸の信号参照だけで閉じる循環があれば、
    /// 参照の範囲を閉路の順に返す。
    pub fn resolve_module_alias_types(&self, owner: ModuleBodyPosition, limit: u64)
        -> (result: Result<Option<ModuleAliasTypes<'p, 'a>>, ModuleAliasTypesError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_alias_types_result(owner, limit, result),
    {
        let sources = match self.check_module_type_sources(owner, limit) {
            Ok(Some(sources)) => sources,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleAliasTypesError::Sources(error)),
        };
        proof { self.module_type_sources_bounds(owner, limit, sources); }
        let aliases = sources.aliases.as_slice();
        let graph = alias_graph(aliases);
        let order = match check_dependency_order(graph.as_slice(), true) {
            Ok(order) => order,
            Err(cycle) => return Err(ModuleAliasTypesError::Cycle(locate_cycle(aliases, graph.as_slice(), cycle.as_slice()))),
        };
        let types = propagate_types(sources.roots.wiring.drivers.signature.inputs.as_slice(), sources.roots.types.as_slice(),
            aliases, graph.as_slice(), order.as_slice());
        Ok(Some(ModuleAliasTypes { sources, types }))
    }
}

} // verus!
