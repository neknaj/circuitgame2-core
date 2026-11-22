//! 起点から到達した関数の呼び出し先を調べる。

use super::{FunctionCallSite, UseAliases};
use super::vertices::FunctionVertices;
use super::super::{DefinitionBatchError, DefinitionPosition, DefinitionReferenceError};
use crate::syntax::circuit::ExpressionReferenceKind;
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use super::vertices::{function_position, project_function_set};
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence};

verus! {

spec fn before(a: DefinitionPosition, b: DefinitionPosition) -> bool {
    a.definition < b.definition || a.definition == b.definition && a.reference < b.reference
}

spec fn same_declaration(a: DefinitionPosition, b: DefinitionPosition) -> bool {
    a.file == b.file && a.entry == b.entry
}

spec fn source_call_position(cursor: DefinitionPosition, definition: usize, reference: usize) -> DefinitionPosition {
    DefinitionPosition { definition, reference, ..cursor }
}

type Position = (usize, usize);

pub(super) struct ReachableFunctionCalls<'p, 'a> {
    pub(super) vertices: FunctionVertices,
    pub(super) rows: Vec<Vec<FunctionCallSite<'p, 'a>>>,
}

#[verifier::opaque]
spec fn queue_after_calls(start: Seq<Position>, calls: Seq<FunctionCallSite>, end: int) -> Seq<Position>
    decreases end,
{
    if end <= 0 {
        start
    } else {
        let before = queue_after_calls(start, calls, end - 1);
        let target = calls[end - 1].target;
        if before.contains(target) { before } else { before.push(target) }
    }
}

#[verifier::opaque]
spec fn queue_after_rows(root: Position, rows: Seq<Vec<FunctionCallSite>>, end: int) -> Seq<Position>
    decreases end,
{
    if end <= 0 { seq![root] }
    else { queue_after_calls(queue_after_rows(root, rows, end - 1), rows[end - 1]@, rows[end - 1]@.len() as int) }
}

proof fn same_row_prefix_has_same_queue(root: Position, before: Seq<Vec<FunctionCallSite>>, after: Seq<Vec<FunctionCallSite>>,
    end: int)
    requires 0 <= end <= before.len(), end <= after.len(), before.take(end) == after.take(end),
    ensures queue_after_rows(root, before, end) == queue_after_rows(root, after, end),
    decreases end,
{
    reveal(queue_after_rows);
    if end > 0 {
        assert(before.take(end - 1) =~= after.take(end - 1));
        same_row_prefix_has_same_queue(root, before, after, end - 1);
        assert(before.take(end)[end - 1] == before[end - 1]);
        assert(after.take(end)[end - 1] == after[end - 1]);
        assert(before[end - 1] == after[end - 1]);
    }
}

spec fn available_positions(all: Set<Position>, found: Seq<Position>, remaining: Set<Position>) -> bool {
    &&& forall|position: Position| #[trigger] remaining.contains(position) == (all.contains(position) && !found.contains(position))
    &&& forall|position: Position| #[trigger] found.contains(position) ==> all.contains(position)
}

spec fn discovered_from_root(root: Position, found: Seq<Position>, via: Seq<Option<FunctionCallSite>>, aliases: &UseAliases) -> bool {
    &&& 0 < found.len() == via.len()
    &&& found[0] == root && via[0].is_none()
    &&& forall|i: int| 0 < i < via.len() ==> ((#[trigger] via[i]) matches Some(site)
        && aliases.function_call_site_matches(site)
        && site.target == found[i]
        && exists|parent: int| 0 <= parent < i && #[trigger] found[parent] == (site.position.file, site.position.entry))
}

proof fn record_discovery(all: Set<Position>, found: Seq<Position>, remaining: Set<Position>, position: Position)
    requires available_positions(all, found, remaining), all.contains(position), !found.contains(position),
    ensures
        available_positions(all, found.push(position), remaining.remove(position)),
        remaining.remove(position).len() + 1 == remaining.len(),
{
    assert(remaining.contains(position));
    vstd::set::lemma_set_remove_len(remaining, position);
    let updated = found.push(position);
    let rest = remaining.remove(position);
    assert forall|other: Position| #[trigger] rest.contains(other)
        == (all.contains(other) && !updated.contains(other)) by {
        vstd::seq_lib::lemma_seq_contains_after_push(found, position, other);
    };
    assert forall|other: Position| #[trigger] found.push(position).contains(other)
        implies all.contains(other) by {
        vstd::seq_lib::lemma_seq_contains_after_push(found, position, other);
        if other != position {
            assert(found.contains(other));
        }
    };
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn scanned_callee(&self, at: DefinitionPosition, sites: Seq<FunctionCallSite>) -> bool {
        let key = (at.file, at.entry, at.definition, at.reference);
        ||| self.call_dependency_matches(key, Ok(None))
        ||| exists|i: int| 0 <= i < sites.len() && (#[trigger] sites[i]).position == at
    }

    #[verifier::opaque]
    pub(super) closed spec fn scanned_function_calls(&self, cursor: DefinitionPosition, sites: Seq<FunctionCallSite>) -> bool {
        &&& forall|i: int| 0 <= i < sites.len() ==> {
            let site = #[trigger] sites[i];
            same_declaration(site.position, cursor) && before(site.position, cursor) && self.function_call_site_matches(site)
        }
        &&& forall|i: int, j: int| 0 <= i < j < sites.len() ==>
            before((#[trigger] sites[i]).position, (#[trigger] sites[j]).position)
        &&& forall|def: usize, reference: usize|
            #[trigger] self.func_call_at(cursor.file, cursor.entry, def, reference)
                && before(source_call_position(cursor, def, reference), cursor)
            ==> self.scanned_callee(source_call_position(cursor, def, reference), sites)
    }

    pub(super) closed spec fn complete_function_call_row(&self, owner: Position, sites: Seq<FunctionCallSite>) -> bool {
        let parsed = self.targets.project_model().circuits_model()[owner.0 as int];
        let range = parsed.entry_ranges@[owner.1 as int].definitions;
        self.scanned_function_calls(DefinitionPosition {
            file: owner.0, entry: owner.1, definition: (range.end - range.start) as usize, reference: 0,
        }, sites)
    }

    pub(super) closed spec fn function_call_scan_failure(&self, owner: Position, error: DefinitionBatchError) -> bool {
        let at = error.position;
        &&& at.file == owner.0 && at.entry == owner.1
        &&& self.func_call_at(owner.0, owner.1, at.definition, at.reference)
        &&& self.definition_resolution_evidence(owner.0, owner.1, at.definition, at.reference,
            Err(DefinitionReferenceError::Rejected { site: error.site, reason: error.reason }))
        &&& exists|prior: Seq<FunctionCallSite>| #[trigger] self.scanned_function_calls(at, prior)
    }

    proof fn row_is_from_source(&self, owner: Position, sites: Seq<FunctionCallSite>, i: int)
        requires self.complete_function_call_row(owner, sites), 0 <= i < sites.len(),
        ensures self.function_call_site_matches(sites[i]),
            (sites[i].position.file, sites[i].position.entry) == owner,
    {
        reveal(UseAliases::scanned_function_calls);
    }

    proof fn advance_function_calls(&self, cursor: DefinitionPosition, next: DefinitionPosition,
        sites: Seq<FunctionCallSite>, added: Option<FunctionCallSite>)
        requires
            self.scanned_function_calls(cursor, sites),
            same_declaration(cursor, next), before(cursor, next),
            forall|d: usize, r: usize| #[trigger] self.func_call_at(cursor.file, cursor.entry, d, r)
                && before(source_call_position(cursor, d, r), next)
                && !before(source_call_position(cursor, d, r), cursor)
                ==> d == cursor.definition && r == cursor.reference,
            added matches Some(site) ==> site.position == cursor && self.function_call_site_matches(site),
            !self.func_call_at(cursor.file, cursor.entry, cursor.definition, cursor.reference)
                || added.is_some()
                || self.call_dependency_matches((cursor.file, cursor.entry, cursor.definition, cursor.reference), Ok(None)),
        ensures self.scanned_function_calls(next, match added { Some(site) => sites.push(site), None => sites }),
    {
        reveal(UseAliases::scanned_function_calls);
        let updated = match added { Some(site) => sites.push(site), None => sites };
        assert forall|i: int| 0 <= i < updated.len() implies {
            let site = #[trigger] updated[i];
            same_declaration(site.position, next) && before(site.position, next) && self.function_call_site_matches(site)
        } by {
            if i < sites.len() { assert(updated[i] == sites[i]); }
        };
        assert forall|i: int, j: int| 0 <= i < j < updated.len() implies
            before((#[trigger] updated[i]).position, (#[trigger] updated[j]).position) by {
            assert(updated[i] == sites[i]);
            if j < sites.len() { assert(updated[j] == sites[j]); }
        };
        assert forall|d: usize, r: usize| #[trigger] self.func_call_at(next.file, next.entry, d, r)
            && before(source_call_position(next, d, r), next)
            implies self.scanned_callee(source_call_position(next, d, r), updated) by {
            let at = source_call_position(next, d, r);
            assert(at == source_call_position(cursor, d, r));
            if before(at, cursor) {
                assert(self.scanned_callee(at, sites));
                if !self.call_dependency_matches((at.file, at.entry, d, r), Ok(None)) {
                    let i = choose|i: int| 0 <= i < sites.len() && (#[trigger] sites[i]).position == at;
                    assert(updated[i] == sites[i]);
                }
            } else {
                assert(at == cursor);
                if added.is_some() {
                    assert(updated[sites.len() as int].position == at);
                }
            }
        };
    }

    /// 一つの関数の厳格索引から、通常呼び出しをソース順に取り出す。
    ///
    /// 入れ子の呼び出しも含める。基底 NOR はその場で解決し、依存先の一覧から除く。
    /// 解決に失敗した場合は、この関数で最初に失敗した呼び出しの位置を返す。
    pub(super) fn scan_function_calls(&self, owner: (usize, usize))
        -> (result: Result<Vec<FunctionCallSite<'p, 'a>>, DefinitionBatchError<'p, 'a>>)
        requires self.can_resolve(), function_position(self.targets.project_model().circuits_model(), owner),
        ensures match result {
            Ok(sites) => self.complete_function_call_row(owner, sites@),
            Err(error) => self.function_call_scan_failure(owner, error),
        },
    {
        proof { self.targets.parsed_project_model(); }
        let project = self.targets.project();
        let (file, entry) = owner;
        let parsed = &project.circuits()[file];
        let ghost source = project.sources_model()[file as int];
        proof {
            parsed_index_evidence(source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let definitions = &parsed.entry_ranges[entry].definitions;
        let mut cursor = DefinitionPosition { file, entry, definition: 0, reference: 0 };
        let mut sites: Vec<FunctionCallSite> = Vec::new();
        assert(self.scanned_function_calls(cursor, sites@)) by { reveal(UseAliases::scanned_function_calls); };
        while cursor.definition < definitions.end - definitions.start
            invariant
                self.can_resolve(), function_position(self.targets.project_model().circuits_model(), owner),
                owner == (file, entry), file < self.targets.project_model().circuits_model().len(),
                cursor.file == file && cursor.entry == entry,
                *parsed == self.targets.project_model().circuits_model()[file as int],
                entry < parsed.syntax.entries@.len() && entry < parsed.entry_ranges@.len(),
                parsed.syntax.entries@[entry as int].head is Func,
                *definitions == parsed.entry_ranges@[entry as int].definitions,
                crate::project::parsed_circuit_matches(source, *parsed),
                definitions.start <= definitions.end <= parsed.definitions@.len(),
                cursor.definition <= definitions.end - definitions.start,
                cursor.definition == definitions.end - definitions.start ==> cursor.reference == 0,
                self.scanned_function_calls(cursor, sites@),
            decreases definitions.end - definitions.start - cursor.definition,
                if cursor.definition < definitions.end - definitions.start {
                    let refs = parsed.definitions@[definitions.start + cursor.definition].references;
                    refs.end - refs.start - cursor.reference
                } else { 0 },
        {
            let absolute = definitions.start + cursor.definition;
            let refs = &parsed.definitions[absolute].references;
            proof {
                parsed_index_evidence(source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
            }
            if cursor.reference >= refs.end - refs.start {
                let next = DefinitionPosition { definition: cursor.definition + 1, reference: 0, ..cursor };
                proof { self.advance_function_calls(cursor, next, sites@, None); }
                cursor = next;
                continue;
            }
            let next = DefinitionPosition { reference: cursor.reference + 1, ..cursor };
            if matches!(parsed.references[refs.start + cursor.reference].kind, ExpressionReferenceKind::Callee) {
                assert(self.func_call_at(file, entry, cursor.definition, cursor.reference));
                let binding = match self.resolve_definition_reference(file, entry, cursor.definition, cursor.reference) {
                    Ok(binding) => binding,
                    Err(DefinitionReferenceError::Rejected { site, reason }) => {
                        let error = DefinitionBatchError { position: cursor, site, reason };
                        assert(self.function_call_scan_failure(owner, error)) by {
                            assert(self.definition_resolution_evidence(file, entry, cursor.definition, cursor.reference,
                                Err(DefinitionReferenceError::Rejected { site, reason })));
                            assert(self.scanned_function_calls(cursor, sites@));
                        };
                        return Err(error);
                    },
                    Err(DefinitionReferenceError::UnknownPosition) => {
                        proof { self.valid_position_is_not_unknown(file, entry, cursor.definition, cursor.reference); }
                        unreachable!()
                    },
                };
                let dependency = self.call_dependency_from_binding(
                    Ghost((file, entry, cursor.definition, cursor.reference)), &binding);
                match dependency {
                    Some(edge) => {
                        let site = FunctionCallSite { position: cursor, target: edge.target, location: edge.reference };
                        proof {
                            assert(self.function_call_site_matches(site)) by { reveal(UseAliases::function_call_site_matches); };
                            self.advance_function_calls(cursor, next, sites@, Some(site));
                        }
                        sites.push(site);
                    },
                    None => proof { self.advance_function_calls(cursor, next, sites@, None); },
                }
            } else {
                proof { self.advance_function_calls(cursor, next, sites@, None); }
            }
            cursor = next;
        }
        Ok(sites)
    }

    pub(super) closed spec fn reachable_function_rows(&self, root: Position, found: Seq<Position>,
        rows: Seq<Vec<FunctionCallSite>>) -> bool
    {
        &&& 0 < found.len() == rows.len() && found[0] == root
        &&& self.completed_discovery_rows(root, found, rows)
        &&& exists|via: Seq<Option<FunctionCallSite>>| #[trigger] discovered_from_root(root, found, via, self)
        &&& forall|i: int| 0 <= i < rows.len() ==>
            self.complete_function_call_row(found[i], (#[trigger] rows[i])@)
        &&& forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows[i]@.len()
            ==> found.contains((#[trigger] rows[i]@[j]).target)
    }

    pub(super) proof fn reachable_call_evidence(&self, root: Position, found: Seq<Position>, rows: Seq<Vec<FunctionCallSite>>,
        i: int, j: int)
        requires self.reachable_function_rows(root, found, rows),
            0 <= i < rows.len(), 0 <= j < rows[i]@.len(),
        ensures ({
            let call = rows[i]@[j];
            &&& self.function_call_site_matches(call)
            &&& (call.position.file, call.position.entry) == found[i]
            &&& found.contains((call.position.file, call.position.entry))
            &&& found.contains(call.target)
        }),
    {
        self.row_is_from_source(found[i], rows[i]@, j);
        assert(found.contains(found[i]));
    }

    pub(super) closed spec fn reachable_function_scan_failure(&self, root: Position, error: DefinitionBatchError) -> bool {
        let owner = (error.position.file, error.position.entry);
        &&& self.function_call_scan_failure(owner, error)
        &&& exists|found: Seq<Position>, via: Seq<Option<FunctionCallSite>>, rows: Seq<Vec<FunctionCallSite>>|
            #![trigger discovered_from_root(root, found, via, self), self.completed_discovery_rows(root, found, rows)]
            discovered_from_root(root, found, via, self) && self.completed_discovery_rows(root, found, rows)
                && rows.len() < found.len() && found[rows.len() as int] == owner
    }

    spec fn completed_discovery_rows(&self, root: Position, found: Seq<Position>, rows: Seq<Vec<FunctionCallSite>>) -> bool {
        &&& rows.len() <= found.len()
        &&& found == queue_after_rows(root, rows, rows.len() as int)
        &&& forall|i: int| 0 <= i < rows.len() ==> {
            let before = #[trigger] queue_after_rows(root, rows, i);
            i < before.len() && self.complete_function_call_row(before[i], rows[i]@)
        }
    }

    /// 起点から見つけた関数だけを検査し、発見順の頂点と呼び出し列を返す。
    ///
    /// 各関数の呼び出しをソース順に処理し、新たな呼び出し先は列の末尾に加える。
    /// # Errors
    ///
    /// この順序で最初に解決できなかった呼び出しの元の位置を返す。
    pub(super) fn discover_function_calls(&self, root: Position)
        -> (result: Result<ReachableFunctionCalls<'p, 'a>, DefinitionBatchError<'p, 'a>>)
        requires self.can_resolve(), function_position(self.targets.project_model().circuits_model(), root),
        ensures match result {
            Ok(reached) => self.reachable_function_rows(root, reached.vertices.positions_model(), reached.rows@),
            Err(error) => self.reachable_function_scan_failure(root, error),
        },
    {
        let ghost universe = project_function_set(&self.targets.project_model());
        assert(universe.contains(root));
        let empty = FunctionVertices::empty();
        let ghost none = empty.positions_model();
        proof {
            assert(available_positions(universe, none, universe)) by {
                assert forall|pos: Position| #[trigger] universe.contains(pos)
                    == (universe.contains(pos) && !none.contains(pos)) by {};
            };
            record_discovery(universe, none, universe, root);
        }
        let mut selected = empty.with_new(root);
        let ghost mut remaining = universe.remove(root);
        let ghost mut via = seq![None::<FunctionCallSite>];
        let mut rows: Vec<Vec<FunctionCallSite>> = Vec::new();
        assert(self.completed_discovery_rows(root, selected.positions_model(), rows@)) by {
            reveal(queue_after_rows);
            assert(selected.positions_model() =~= seq![root]);
        };
        let mut i = 0;
        while i < selected.positions().len()
            invariant
                self.can_resolve(),
                forall|pos: Position| #[trigger] universe.contains(pos)
                    <==> function_position(self.targets.project_model().circuits_model(), pos),
                i == rows@.len() <= selected.positions_model().len(),
                available_positions(universe, selected.positions_model(), remaining),
                discovered_from_root(root, selected.positions_model(), via, self),
                self.completed_discovery_rows(root, selected.positions_model(), rows@),
                forall|r: int| 0 <= r < rows@.len() ==>
                    self.complete_function_call_row(selected.positions_model()[r], (#[trigger] rows@[r])@),
                forall|r: int, j: int| 0 <= r < rows@.len() && 0 <= j < rows@[r]@.len()
                    ==> selected.positions_model().contains((#[trigger] rows@[r]@[j]).target),
            decreases remaining.len() + selected.positions_model().len() - i,
        {
            let owner = selected.positions()[i];
            proof {
                assert(selected.positions_model().contains(owner));
                assert(universe.contains(owner));
            }
            let calls = match self.scan_function_calls(owner) {
                Ok(row) => row,
                Err(error) => {
                    assert(self.reachable_function_scan_failure(root, error)) by {
                        assert((error.position.file, error.position.entry) == owner) by {
                            reveal(UseAliases::function_call_scan_failure);
                        };
                        assert(discovered_from_root(root, selected.positions_model(), via, self));
                        assert(self.completed_discovery_rows(root, selected.positions_model(), rows@));
                    };
                    return Err(error);
                },
            };
            let ghost remaining_work = remaining.len() + selected.positions_model().len();
            let ghost start = selected.positions_model();
            let mut c = 0;
            assert(selected.positions_model() == queue_after_calls(start, calls@, 0)) by { reveal(queue_after_calls); };
            while c < calls.len()
                invariant
                    self.can_resolve(),
                    forall|pos: Position| #[trigger] universe.contains(pos)
                        <==> function_position(self.targets.project_model().circuits_model(), pos),
                    i < start.len() <= selected.positions_model().len(), start[i as int] == owner,
                    selected.positions_model().take(start.len() as int) == start,
                    available_positions(universe, selected.positions_model(), remaining),
                    discovered_from_root(root, selected.positions_model(), via, self),
                    self.complete_function_call_row(owner, calls@),
                    remaining.len() + selected.positions_model().len() == remaining_work,
                    c <= calls@.len(),
                    selected.positions_model() == queue_after_calls(start, calls@, c as int),
                    forall|j: int| 0 <= j < c ==> selected.positions_model().contains((#[trigger] calls@[j]).target),
                decreases calls@.len() - c,
            {
                let target = calls[c].target;
                let ghost site = calls@[c as int];
                let ghost before = selected.positions_model();
                if selected.get(target).is_none() {
                    let ghost earlier_via = via;
                    proof {
                        self.row_is_from_source(owner, calls@, c as int);
                        self.function_call_endpoints(site);
                        assert(universe.contains(target));
                        assert(!before.contains(target));
                        record_discovery(universe, before, remaining, target);
                        remaining = remaining.remove(target);
                    }
                    selected = selected.with_new(target);
                    proof {
                        via = via.push(Some(site));
                        assert forall|j: int| 0 < j < via.len() implies ((#[trigger] via[j]) matches Some(referrer)
                            && self.function_call_site_matches(referrer)
                            && referrer.target == selected.positions_model()[j]
                            && exists|p: int| 0 <= p < j && #[trigger] selected.positions_model()[p]
                                == (referrer.position.file, referrer.position.entry)) by {
                            if j < before.len() {
                                assert(via[j] == earlier_via[j]);
                                assert(selected.positions_model()[j] == before[j]);
                                let old = earlier_via[j]->Some_0;
                                let parent = choose|p: int| 0 <= p < j && #[trigger] before[p]
                                    == (old.position.file, old.position.entry);
                                assert(selected.positions_model()[parent] == before[parent]);
                            } else {
                                assert(selected.positions_model()[i as int] == owner);
                            }
                        };
                        assert(selected.positions_model().take(start.len() as int) =~= start);
                        assert forall|j: int| 0 <= j < c implies selected.positions_model().contains((#[trigger] calls@[j]).target) by {
                            assert(before.contains(calls@[j].target));
                            vstd::seq_lib::lemma_seq_contains_after_push(before, target, calls@[j].target);
                        };
                    }
                } else {
                    assert(before.contains(target));
                }
                assert(selected.positions_model() == queue_after_calls(start, calls@, c + 1)) by { reveal(queue_after_calls); };
                assert(selected.positions_model().contains(target));
                assert forall|j: int| 0 <= j <= c implies selected.positions_model().contains((#[trigger] calls@[j]).target) by {
                    if j == c { assert(calls@[j].target == target); }
                };
                c += 1;
            }
            let ghost previous_rows = rows@;
            rows.push(calls);
            proof {
                assert(previous_rows.take(i as int) =~= rows@.take(i as int));
                same_row_prefix_has_same_queue(root, previous_rows, rows@, i as int);
                assert(queue_after_rows(root, rows@, i + 1) == selected.positions_model()) by {
                    reveal(queue_after_rows);
                };
                assert forall|r: int| 0 <= r < rows@.len() implies {
                    let before = #[trigger] queue_after_rows(root, rows@, r);
                    r < before.len() && self.complete_function_call_row(before[r], rows@[r]@)
                } by {
                    if r < i {
                        assert(previous_rows.take(r) =~= rows@.take(r));
                        same_row_prefix_has_same_queue(root, previous_rows, rows@, r);
                        assert(rows@[r] == previous_rows[r]);
                    } else {
                        assert(queue_after_rows(root, rows@, r) == start);
                    }
                };
            }
            assert forall|r: int| 0 <= r < rows@.len() implies
                self.complete_function_call_row(selected.positions_model()[r], (#[trigger] rows@[r])@) by {
                if r < i {
                    assert(rows@[r] == previous_rows[r]);
                    assert(selected.positions_model()[r] == start[r]);
                }
            };
            assert forall|r: int, j: int| 0 <= r < rows@.len() && 0 <= j < rows@[r]@.len()
                implies selected.positions_model().contains((#[trigger] rows@[r]@[j]).target) by {
                if r < i {
                    assert(rows@[r] == previous_rows[r]);
                    assert(start.contains(previous_rows[r]@[j].target));
                    let p = choose|p: int| 0 <= p < start.len() && #[trigger] start[p] == previous_rows[r]@[j].target;
                    assert(selected.positions_model()[p] == start[p]);
                }
            };
            i += 1;
        }
        assert(self.reachable_function_rows(root, selected.positions_model(), rows@)) by {
            assert(discovered_from_root(root, selected.positions_model(), via, self));
        };
        Ok(ReachableFunctionCalls { vertices: selected, rows })
    }
}

} // verus!
