//! 一つのモジュールに属する定義を、元のファイルと索引位置を保って集める。

use super::{ModuleBodyPosition, ModulePartsError, UseTargets};
#[cfg(verus_only)]
use super::ModulePartBinding;
use crate::project::CircuitProject;
use crate::syntax::circuit::Head;
#[cfg(verus_only)]
use crate::{project::circuits::parsed_index_evidence, syntax::circuit::build_entry_ranges_evidence};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// モジュールまたは断片の本体にある定義の位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ModuleDefinition {
    /// 定義が現れた本体。宣言参照は、この本体のファイルとブロックで解決する。
    pub body: ModuleBodyPosition,
    /// 本体内の定義の添字。参照解決に使う相対添字。
    pub local: usize,
}

/// モジュールのポート宣言位置と、全断片から集めた定義の位置。
#[derive(Debug)]
pub struct ModuleBody {
    /// ポートを宣言したモジュールの位置。
    pub owner: ModuleBodyPosition,
    /// モジュール自身に続き、同じモジュールに属する断片をプロジェクト順に並べた位置。
    pub members: Vec<ModuleBodyPosition>,
    /// モジュール自身の定義、その後に断片をプロジェクト順に並べた定義列。
    pub definitions: Vec<ModuleDefinition>,
}

#[verifier::opaque]
spec fn member_positions(owner: ModuleBodyPosition, parts: Seq<ModulePartBinding>, count: nat)
    -> Seq<ModuleBodyPosition>
    decreases count,
{
    if count == 0 {
        seq![owner]
    } else {
        let prior = member_positions(owner, parts, (count - 1) as nat);
        let part = parts[(count - 1) as int];
        if part.module_position == owner { prior.push(part.part_position) } else { prior }
    }
}

spec fn has_body(project: &CircuitProject, position: ModuleBodyPosition, head: Head) -> bool {
    let circuits = project.circuits_model();
    &&& position.file < circuits.len()
    &&& position.entry < circuits[position.file as int].syntax.entries@.len()
    &&& circuits[position.file as int].syntax.entries@[position.entry as int].head == head
}

proof fn selected_part_at(owner: ModuleBodyPosition, parts: Seq<ModulePartBinding>, count: nat, i: int)
    -> (part: int)
    requires count <= parts.len(), 0 < i < member_positions(owner, parts, count).len(),
    ensures 0 <= part < count,
        i == member_positions(owner, parts, part as nat).len(),
        parts[part].part_position == member_positions(owner, parts, count)[i],
    decreases count,
{
    reveal(member_positions);
    if count == 0 {
        assert(false);
        0
    } else {
        let end = (count - 1) as nat;
        let prior = member_positions(owner, parts, end);
        if i < prior.len() {
            selected_part_at(owner, parts, end, i)
        } else {
            end as int
        }
    }
}

spec fn body_definitions(project: &CircuitProject, position: ModuleBodyPosition) -> Seq<ModuleDefinition> {
    let defs = project.circuits_model()[position.file as int].entry_ranges@[position.entry as int].definitions;
    Seq::new((defs.end - defs.start) as nat, |i: int| ModuleDefinition { body: position, local: i as usize })
}

#[verifier::opaque]
spec fn definitions_from_parts(
    project: &CircuitProject, owner: ModuleBodyPosition, parts: Seq<ModulePartBinding>, count: nat,
) -> Seq<ModuleDefinition>
    decreases count,
{
    if count == 0 {
        body_definitions(project, owner)
    } else {
        let prior = definitions_from_parts(project, owner, parts, (count - 1) as nat);
        let part = parts[(count - 1) as int];
        if part.module_position == owner {
            prior + body_definitions(project, part.part_position)
        } else {
            prior
        }
    }
}

fn extend_from_body(project: &CircuitProject, position: ModuleBodyPosition, rows: &mut Vec<ModuleDefinition>)
    requires
        project.has_parsed_sources(),
        has_body(project, position, Head::Module) || has_body(project, position, Head::ModulePart),
    ensures final(rows)@ == old(rows)@ + body_definitions(project, position),
{
    let parsed = &project.circuits()[position.file];
    proof {
        let origin = project.sources_model()[position.file as int];
        parsed_index_evidence(origin, *parsed);
        build_entry_ranges_evidence(origin.text, &parsed.build_model(), position.entry as int);
    }
    let definitions = &parsed.entry_ranges[position.entry].definitions;
    let count = definitions.end - definitions.start;
    let ghost prior = rows@;
    let ghost expected = body_definitions(project, position);
    let mut local = 0;
    while local < count
        invariant
            count == expected.len(),
            expected == body_definitions(project, position),
            local <= count,
            rows@ == prior + expected.take(local as int),
        decreases count - local,
    {
        let row = ModuleDefinition { body: position, local };
        assert(row == expected[local as int]);
        rows.push(row);
        assert(expected.take(local as int).push(row) =~= expected.take(local + 1));
        assert(rows@ =~= prior + expected.take(local + 1));
        local += 1;
    }
    assert(expected.take(local as int) =~= expected);
}

impl<'p, 'a> UseTargets<'p, 'a> {
    /// 本体の組み立て結果が、同じ所有先の全断片の定義を保持することを表す。
    pub closed spec fn module_body_result(
        &self, owner: ModuleBodyPosition, result: Result<Option<ModuleBody>, ModulePartsError<'p, 'a>>,
    ) -> bool {
        let project = self.project_model();
        if !has_body(&project, owner, Head::Module) {
            result == Ok(None)
        } else {
            match result {
                Ok(Some(body)) => body.owner == owner && exists|parts: Vec<ModulePartBinding>|
                    #[trigger] self.module_parts_result(Ok(parts))
                    && body.members@ == member_positions(owner, parts@, parts@.len())
                    && body.definitions@ == definitions_from_parts(&project, owner, parts@, parts@.len())
                    && 0 < body.members@.len() && body.members@[0] == owner
                    && (forall|i: int| 0 <= i < body.members@.len() ==>
                        has_body(&project, #[trigger] body.members@[i], if i == 0 { Head::Module } else { Head::ModulePart })),
                Err(error) => self.module_parts_result(Err(error)),
                _ => false,
            }
        }
    }

    /// 所有するモジュールが組み立てた本体の先頭にあることを示す。
    pub proof fn module_body_owner(&self, owner: ModuleBodyPosition, body: &ModuleBody)
        requires self.module_body_result(owner, Ok(Some(*body))),
        ensures body.owner == owner, 0 < body.members@.len(), body.members@[0] == owner,
    {
    }

    /// 組み立てた本体の各位置が、元のモジュールか断片を指すことを示す。
    pub(in crate::project) proof fn module_body_member(&self, body: &ModuleBody, index: int)
        requires self.module_body_result(body.owner, Ok(Some(*body))), 0 <= index < body.members@.len(),
        ensures ({
            let position = body.members@[index];
            let circuits = self.project_model().circuits_model();
            &&& position.file < circuits.len()
            &&& position.entry < circuits[position.file as int].syntax.entries@.len()
            &&& circuits[position.file as int].syntax.entries@[position.entry as int].head
                == if index == 0 { Head::Module } else { Head::ModulePart }
        }),
    {
    }

    /// 各断片の位置が、組み立てた本体に一度だけ現れることを示す。
    pub(in crate::project) proof fn module_body_members_distinct(&self, body: &ModuleBody, i: int, j: int)
        requires self.covers_project(), self.module_body_result(body.owner, Ok(Some(*body))),
            0 <= i < j < body.members@.len(),
        ensures body.members@[i] != body.members@[j],
    {
        if i == 0 {
            self.module_body_member(body, i);
            self.module_body_member(body, j);
        } else {
            let parts = choose|parts: Vec<ModulePartBinding>| #[trigger] self.module_parts_result(Ok(parts))
                && body.members@ == member_positions(body.owner, parts@, parts@.len());
            let a = selected_part_at(body.owner, parts@, parts@.len(), i);
            let b = selected_part_at(body.owner, parts@, parts@.len(), j);
            if a < b {
                self.module_part_positions_distinct(&parts, a, b);
            } else if b < a {
                self.module_part_positions_distinct(&parts, b, a);
            } else {
                // 同じ断片より前に選んだ断片の数が等しければ、本体内の添字も等しい。
                assert(false);
            }
        }
    }

    /// 指定したモジュールの定義を全断片から集める。
    ///
    /// 位置がモジュールを指さなければ `None` を返す。各定義には元のファイルと本体内の位置が残る。
    ///
    /// # Errors
    ///
    /// 所有先が見つからない断片や、別の種別の宣言を指定する断片があれば、
    /// プロジェクト内で最初に見つかった断片の診断を返す。
    pub fn module_body(&self, owner: ModuleBodyPosition)
        -> (result: Result<Option<ModuleBody>, ModulePartsError<'p, 'a>>)
        requires self.covers_project(),
        ensures self.module_body_result(owner, result),
    {
        let project = self.project();
        let circuits = project.circuits();
        if owner.file >= circuits.len() {
            return Ok(None);
        }
        let entries = &circuits[owner.file].syntax.entries;
        if owner.entry >= entries.len() || !matches!(entries[owner.entry].head, Head::Module) {
            return Ok(None);
        }
        let parts = match self.collect_module_parts() {
            Ok(parts) => parts,
            Err(error) => return Err(error),
        };
        let mut members = Vec::new();
        members.push(owner);
        assert(members@ == member_positions(owner, parts@, 0)) by {
            reveal(member_positions);
        };
        let mut definitions = Vec::new();
        extend_from_body(project, owner, &mut definitions);
        assert(definitions@ == definitions_from_parts(project, owner, parts@, 0)) by {
            reveal(definitions_from_parts);
            assert(Seq::<ModuleDefinition>::empty() + body_definitions(project, owner) =~= body_definitions(project, owner));
        };
        let mut i = 0;
        while i < parts.len()
            invariant
                *project == self.project_model(), project.has_parsed_sources(),
                self.module_parts_result(Ok(parts)),
                i <= parts@.len(),
                has_body(project, owner, Head::Module),
                0 < members@.len() && members@[0] == owner,
                forall|j: int| 0 <= j < members@.len() ==>
                    has_body(project, #[trigger] members@[j], if j == 0 { Head::Module } else { Head::ModulePart }),
                members@ == member_positions(owner, parts@, i as nat),
                definitions@ == definitions_from_parts(project, owner, parts@, i as nat),
            decreases parts@.len() - i,
        {
            let part = &parts[i];
            let ghost previous = definitions@;
            if part.module_position.file == owner.file && part.module_position.entry == owner.entry {
                proof {
                    reveal(UseTargets::bindings_before);
                    let file = part.part_position.file;
                    let name = part.part_name;
                    assert(self.module_part_resolution(file, name, Ok(*part)));
                    assert(has_body(project, part.part_position, Head::ModulePart));
                }
                extend_from_body(project, part.part_position, &mut definitions);
                let ghost older_members = members@;
                members.push(part.part_position);
                assert forall|j: int| 0 <= j < members@.len() implies
                    has_body(project, #[trigger] members@[j], if j == 0 { Head::Module } else { Head::ModulePart }) by {
                    if j < older_members.len() { assert(members@[j] == older_members[j]); }
                };
            }
            assert(members@ == member_positions(owner, parts@, (i + 1) as nat)) by { reveal(member_positions); };
            assert(definitions@ == definitions_from_parts(project, owner, parts@, (i + 1) as nat)) by {
                reveal(definitions_from_parts);
                assert(previous == definitions_from_parts(project, owner, parts@, i as nat));
            };
            i += 1;
        }
        Ok(Some(ModuleBody { owner, members, definitions }))
    }
}

} // verus!
