//! プロジェクトの関数宣言に頂点番号を割り当てる。

use crate::project::CircuitProject;
use crate::syntax::circuit::Head;
#[cfg(verus_only)]
use crate::syntax::circuit::NamedBuildCircuit;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::laws_cmp::obeys_cmp;

verus! {

type Position = (usize, usize);

/// 関数宣言をファイル順と厳格索引順に並べた頂点索引。
#[derive(Debug)]
pub(super) struct FunctionVertices {
    positions: Vec<Position>,
    by_position: BTreeMap<Position, usize>,
}

spec fn before(left: Position, right: Position) -> bool {
    left.0 < right.0 || (left.0 == right.0 && left.1 < right.1)
}

/// 位置がプロジェクトの関数宣言を指すことを表す。
pub(super) open spec fn function_position(circuits: Seq<NamedBuildCircuit>, position: Position) -> bool {
    &&& position.0 < circuits.len()
    &&& position.1 < circuits[position.0 as int].syntax.entries@.len()
    &&& circuits[position.0 as int].syntax.entries@[position.1 as int].head is Func
}

proof fn function_set_before(circuits: Seq<NamedBuildCircuit>, file: usize, entry: usize) -> (found: Set<Position>)
    requires file <= circuits.len(), if file == circuits.len() { entry == 0 }
        else { entry <= circuits[file as int].syntax.entries@.len() },
    ensures forall|at: Position| #[trigger] found.contains(at) <==>
        function_position(circuits, at) && before(at, (file, entry)),
    decreases file, entry,
{
    if entry > 0 {
        let next = (file, (entry - 1) as usize);
        let old = function_set_before(circuits, next.0, next.1);
        let found = if function_position(circuits, next) { old.insert(next) } else { old };
        assert forall|at: Position| #[trigger] found.contains(at) <==>
            function_position(circuits, at) && before(at, (file, entry)) by {
            assert(old.contains(at) == (function_position(circuits, at) && before(at, next)));
            if at != next { assert(before(at, next) == before(at, (file, entry))); }
        };
        found
    } else if file > 0 {
        let prior = (file - 1) as usize;
        let entries = &circuits[prior as int].syntax.entries;
        vstd::std_specs::vec::axiom_spec_len(entries);
        let end = entries@.len() as usize;
        let found = function_set_before(circuits, prior, end);
        assert forall|at: Position| #[trigger] found.contains(at) <==>
            function_position(circuits, at) && before(at, (file, entry)) by {
            if function_position(circuits, at) {
                assert(before(at, (prior, end)) == before(at, (file, entry)));
            }
        };
        found
    } else {
        Set::empty()
    }
}

/// 探索の減少量を定めるため、関数宣言の有限集合を証明内で作る。
pub(super) proof fn project_function_set(project: &CircuitProject) -> (found: Set<Position>)
    ensures forall|at: Position| #[trigger] found.contains(at) <==> function_position(project.circuits_model(), at),
{
    project.circuit_count_fits();
    let circuits = project.circuits_model();
    let found = function_set_before(circuits, circuits.len() as usize, 0);
    assert forall|at: Position| #[trigger] found.contains(at) <==> function_position(circuits, at) by {
        if function_position(circuits, at) { assert(before(at, (circuits.len() as usize, 0))); }
    };
    found
}

spec fn positions_before(circuits: Seq<NamedBuildCircuit>, positions: Seq<Position>, stop: Position) -> bool {
    &&& forall|i: int| 0 <= i < positions.len() ==> {
        let position = #[trigger] positions[i];
        function_position(circuits, position) && before(position, stop)
    }
    &&& forall|a: int, b: int| 0 <= a < b < positions.len() ==>
        before(#[trigger] positions[a], #[trigger] positions[b])
    &&& forall|position: Position| #[trigger] function_position(circuits, position) && before(position, stop)
        ==> exists|i: int| 0 <= i < positions.len() && (#[trigger] positions[i]) == position
}

spec fn index_matches(positions: Seq<Position>, map: Map<Position, usize>) -> bool {
    &&& forall|i: int| 0 <= i < positions.len() ==> {
        let position = #[trigger] positions[i];
        map.contains_key(position) && map[position] == i
    }
    &&& forall|position: Position| #[trigger] map.contains_key(position) ==> {
        let vertex = map[position];
        vertex < positions.len() && positions[vertex as int] == position
    }
}

proof fn advance_entry(
    circuits: Seq<NamedBuildCircuit>, positions: Seq<Position>, at: Position, added: bool,
)
    requires
        at.1 < usize::MAX,
        positions_before(circuits, positions, at),
        added == function_position(circuits, at),
    ensures positions_before(circuits, if added { positions.push(at) } else { positions },
        (at.0, (at.1 + 1) as usize)),
{
    let next: Position = (at.0, (at.1 + 1) as usize);
    let updated = if added { positions.push(at) } else { positions };
    assert forall|i: int| 0 <= i < updated.len() implies {
        let position = #[trigger] updated[i];
        function_position(circuits, position) && before(position, next)
    } by {
        if i < positions.len() { assert(updated[i] == positions[i]); }
    };
    assert forall|a: int, b: int| 0 <= a < b < updated.len() implies
        before(#[trigger] updated[a], #[trigger] updated[b]) by {
        assert(updated[a] == positions[a]);
        if b < positions.len() { assert(updated[b] == positions[b]); }
    };
    assert forall|position: Position| #[trigger] function_position(circuits, position) && before(position, next)
        implies exists|i: int| 0 <= i < updated.len() && (#[trigger] updated[i]) == position by {
        if position == at {
            assert(updated[positions.len() as int] == at);
        } else {
            assert(before(position, at));
            let i = choose|i: int| 0 <= i < positions.len() && (#[trigger] positions[i]) == position;
            assert(updated[i] == positions[i]);
        }
    };
}

proof fn advance_file(circuits: Seq<NamedBuildCircuit>, positions: Seq<Position>, file: usize, end: usize)
    requires
        file < circuits.len(), file < usize::MAX,
        end == circuits[file as int].syntax.entries@.len(),
        positions_before(circuits, positions, (file, end)),
    ensures positions_before(circuits, positions, ((file + 1) as usize, 0)),
{
    assert forall|position: Position| #[trigger] function_position(circuits, position)
        && before(position, ((file + 1) as usize, 0)) implies
        exists|i: int| 0 <= i < positions.len() && (#[trigger] positions[i]) == position by {
        assert(before(position, (file, end)));
    };
}

proof fn insert_position(positions: Seq<Position>, map: Map<Position, usize>, position: Position, vertex: usize)
    requires index_matches(positions, map), !map.contains_key(position), vertex == positions.len(),
    ensures index_matches(positions.push(position), map.insert(position, vertex)),
{
    let updated = positions.push(position);
    let index = map.insert(position, vertex);
    assert forall|i: int| 0 <= i < updated.len() implies {
        let at = #[trigger] updated[i];
        index.contains_key(at) && index[at] == i
    } by {
        if i < positions.len() {
            assert(updated[i] == positions[i]);
            assert(map.contains_key(positions[i]));
        }
    };
}

impl FunctionVertices {
    #[verifier::type_invariant]
    spec fn well_formed(&self) -> bool {
        index_matches(self.positions@, self.by_position@)
    }

    /// 頂点をまだ登録していない索引を作る。
    pub(super) fn empty() -> (vertices: Self)
        ensures vertices.positions_model().len() == 0,
    {
        Self { positions: Vec::new(), by_position: BTreeMap::new() }
    }

    /// 未登録の関数宣言を末尾に加え、既存の頂点番号を保つ。
    pub(super) fn with_new(self, position: Position) -> (updated: Self)
        requires !self.positions_model().contains(position),
        ensures updated.positions_model() == self.positions_model().push(position),
    {
        proof {
            use_type_invariant(&self);
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<Position>());
            assert(!self.by_position@.contains_key(position)) by {
                if self.by_position@.contains_key(position) {
                    let found = self.by_position@[position] as int;
                    assert(0 <= found < self.positions_model().len());
                    assert(self.positions_model()[found] == position);
                    assert(self.positions_model().contains(position));
                }
            };
        }
        let (mut positions, mut by_position) = (self.positions, self.by_position);
        let vertex = positions.len();
        proof { insert_position(positions@, by_position@, position, vertex); }
        by_position.insert(position, vertex);
        positions.push(position);
        Self { positions, by_position }
    }

    /// 頂点番号順の宣言位置を表す。
    pub(super) closed spec fn positions_model(&self) -> Seq<Position> { self.positions@ }

    /// すべての関数宣言が一度ずつ厳格索引順に並ぶことを表す。
    pub(super) closed spec fn matches(&self, project: &CircuitProject) -> bool {
        let circuits = project.circuits_model();
        positions_before(circuits, self.positions_model(), (circuits.len() as usize, 0))
    }

    /// 頂点と元の関数宣言が漏れなく対応し、元の順序を保つことを示す。
    pub(super) proof fn project_evidence(&self, project: &CircuitProject)
        requires self.matches(project),
        ensures
            self.positions_model().len() <= usize::MAX,
            forall|i: int| 0 <= i < self.positions_model().len() ==>
                function_position(project.circuits_model(), #[trigger] self.positions_model()[i]),
            forall|position: Position| #[trigger] function_position(project.circuits_model(), position)
                ==> exists|i: int| 0 <= i < self.positions_model().len()
                    && (#[trigger] self.positions_model()[i]) == position,
            forall|a: int, b: int| 0 <= a < b < self.positions_model().len() ==> {
                let left = #[trigger] self.positions_model()[a];
                let right = #[trigger] self.positions_model()[b];
                left.0 < right.0 || (left.0 == right.0 && left.1 < right.1)
            },
    {
        vstd::std_specs::vec::axiom_spec_len(&self.positions);
        let circuits = project.circuits_model();
        project.circuit_count_fits();
        assert forall|position: Position| #[trigger] function_position(circuits, position) implies
            exists|i: int| 0 <= i < self.positions_model().len()
                && (#[trigger] self.positions_model()[i]) == position by {
            assert(before(position, (circuits.len() as usize, 0)));
        };
    }

    /// 検索結果が頂点番号順の列に対応することを表す。
    pub(super) open spec fn vertex_at(&self, position: Position, result: Option<usize>) -> bool {
        match result {
            Some(vertex) => vertex < self.positions_model().len() && self.positions_model()[vertex as int] == position
                && (forall|i: int| 0 <= i < self.positions_model().len()
                    && (#[trigger] self.positions_model()[i]) == position ==> i == vertex),
            None => forall|i: int| 0 <= i < self.positions_model().len() ==>
                (#[trigger] self.positions_model()[i]) != position,
        }
    }

    /// 解析済みプロジェクトから関数宣言の頂点索引を作る。
    pub(super) fn from_project(project: &CircuitProject<'_>) -> (vertices: Self)
        ensures vertices.matches(project),
    {
        let circuits = project.circuits();
        let mut positions = Vec::new();
        let mut by_position = BTreeMap::new();
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<Position>());
        }
        let mut file = 0;
        while file < circuits.len()
            invariant
                file <= circuits@.len(), circuits@ == project.circuits_model(),
                positions_before(circuits@, positions@, (file, 0)),
                index_matches(positions@, by_position@),
                obeys_cmp::<Position>(),
            decreases circuits@.len() - file,
        {
            let entries = circuits[file].syntax.entries.as_slice();
            let mut entry = 0;
            while entry < entries.len()
                invariant
                    file < circuits@.len(), entries@ == circuits@[file as int].syntax.entries@,
                    entry <= entries@.len(),
                    positions_before(circuits@, positions@, (file, entry)),
                    index_matches(positions@, by_position@),
                    obeys_cmp::<Position>(),
                decreases entries@.len() - entry,
            {
                let position = (file, entry);
                let is_function = matches!(entries[entry].head, Head::Func);
                proof { advance_entry(circuits@, positions@, position, is_function); }
                if is_function {
                    let vertex = positions.len();
                    proof {
                        if by_position@.contains_key(position) {
                            let found = by_position@[position] as int;
                            assert(positions@[found] == position);
                            assert(before(position, position));
                        }
                        insert_position(positions@, by_position@, position, vertex);
                    }
                    let _ = by_position.insert(position, vertex);
                    positions.push(position);
                }
                entry += 1;
            }
            proof { advance_file(circuits@, positions@, file, entry); }
            file += 1;
        }
        Self { positions, by_position }
    }

    /// 頂点番号順に宣言位置を返す。
    pub(super) fn positions(&self) -> (positions: &[Position])
        ensures positions@ == self.positions_model(),
    {
        self.positions.as_slice()
    }

    /// 宣言位置の頂点番号を返す。索引にない位置では `None` を返す。
    pub(super) fn get(&self, position: Position) -> (vertex: Option<usize>)
        ensures self.vertex_at(position, vertex),
    {
        proof {
            use_type_invariant(self);
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<Position>());
        }
        self.by_position.get(&position).copied()
    }
}

} // verus!
