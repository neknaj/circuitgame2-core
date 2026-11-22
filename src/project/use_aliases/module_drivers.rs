//! モジュールと全断片の左辺を集め、共有する局所信号を確定する。

use super::{DefinitionDriver, FuncDriverError, OutputDriver, UseAliases};
use super::local_signal_index::LocalSignalIndex;
use super::function_drivers::{
    check_definition_bindings, check_outputs, collect_drivers, name_location, typed_port_names,
};
#[cfg(verus_only)]
use super::function_drivers::{
    definition_binding_conflict, drivers_before, indexed_driver_site, is_location, missing_output_error,
    names_match_ports, optional_local_index, output_drivers_before, single_drivers_before,
};
use crate::project::{
    LocatedName, ModuleBody, ModuleBodyPosition, ModulePartsError, TypedRoutineSignature,
    TypedSignatureError,
};
#[cfg(verus_only)]
use crate::project::{CircuitProject, ProjectSource, circuits::parsed_index_evidence, declarations::located_name_evidence};
use crate::syntax::circuit::{NameSite, first_routine_expansion};
#[cfg(verus_only)]
use crate::syntax::circuit::{NamedBuildCircuit, routine_expansion_evidence};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 署名と全断片の左辺を照合したモジュールの駆動元。
#[derive(Debug)]
pub struct ModuleDrivers<'p, 'a> {
    /// ポート宣言位置と、元の本体に対応する定義の一覧。
    pub body: ModuleBody,
    /// 型名を元のモジュールのスコープで解決した署名。
    pub signature: TypedRoutineSignature<'p, 'a>,
    /// 定義順と左辺の出力順を保った駆動元。
    pub definitions: Vec<DefinitionDriver<'a>>,
    /// 各駆動元が属する本体の位置。`definitions` と同じ順。
    pub origins: Vec<ModuleBodyPosition>,
    /// 出力宣言順の駆動元。`Definition` の添字は `definitions` を指す。
    pub outputs: Vec<OutputDriver>,
}

pub(super) struct IndexedModuleDrivers<'p, 'a> {
    pub(super) drivers: ModuleDrivers<'p, 'a>,
    pub(super) inputs: Vec<NameSite<'a>>,
    pub(super) index: Option<LocalSignalIndex>,
}

/// モジュールの駆動元を確定できなかった理由。
#[derive(Debug)]
pub enum ModuleDriverError<'p, 'a> {
    /// 断片の所有先を確定できない。
    Parts(ModulePartsError<'p, 'a>),
    /// モジュールの署名の幅、名前、または型に問題がある。
    Signature(TypedSignatureError<'p, 'a>),
    /// 本体または断片に未展開のマクロ呼び出しがある。
    NeedsExpansion(LocatedName<'p, 'a>),
    /// 入力への再駆動、定義の多重駆動、または未駆動の出力。
    Signals(FuncDriverError<'p, 'a>),
}

#[verifier::opaque]
spec fn joined_targets(groups: Seq<Seq<DefinitionDriver>>, count: nat) -> Seq<DefinitionDriver>
    decreases count,
{
    if count == 0 { Seq::empty() }
    else { joined_targets(groups, (count - 1) as nat) + groups[(count - 1) as int] }
}

spec fn repeated_position(position: ModuleBodyPosition, count: nat) -> Seq<ModuleBodyPosition> {
    Seq::new(count, |i: int| position)
}

#[verifier::opaque]
spec fn joined_origins(
    members: Seq<ModuleBodyPosition>, groups: Seq<Seq<DefinitionDriver>>, count: nat,
) -> Seq<ModuleBodyPosition>
    decreases count,
{
    if count == 0 { Seq::empty() }
    else {
        let i = (count - 1) as int;
        joined_origins(members, groups, (count - 1) as nat) + repeated_position(members[i], groups[i].len())
    }
}

#[verifier::opaque]
spec fn target_groups_match(project: &CircuitProject, members: Seq<ModuleBodyPosition>, groups: Seq<Seq<DefinitionDriver>>) -> bool {
    &&& groups.len() <= members.len()
    &&& forall|i: int| 0 <= i < groups.len() ==> {
        let group = #[trigger] groups[i];
        let position = members[i];
        let source = &project.sources_model()[position.file as int];
        let parsed = &project.circuits_model()[position.file as int];
        let range = parsed.entry_ranges@[position.entry as int].definitions;
        drivers_before(source.text, parsed.syntax.forms@, parsed.definitions@, range.start as int,
            range.end as int, range.end as int, 0, group)
    }
}

proof fn extend_target_groups(
    project: &CircuitProject, members: Seq<ModuleBodyPosition>, groups: Seq<Seq<DefinitionDriver>>, index: int,
    next: Seq<DefinitionDriver>,
)
    requires
        target_groups_match(project, members, groups), index == groups.len() < members.len(),
        ({
            let position = members[index];
            let source = &project.sources_model()[position.file as int];
            let parsed = &project.circuits_model()[position.file as int];
            let range = parsed.entry_ranges@[position.entry as int].definitions;
            drivers_before(source.text, parsed.syntax.forms@, parsed.definitions@, range.start as int,
                range.end as int, range.end as int, 0, next)
        }),
    ensures
        target_groups_match(project, members, groups.push(next)),
        joined_targets(groups.push(next), (index + 1) as nat) == joined_targets(groups, index as nat) + next,
        joined_origins(members, groups.push(next), (index + 1) as nat)
            == joined_origins(members, groups, index as nat) + repeated_position(members[index], next.len()),
{
    reveal(target_groups_match);
    let updated = groups.push(next);
    assert forall|i: int| 0 <= i < updated.len() implies {
        let group = #[trigger] updated[i];
        let position = members[i];
        let source = &project.sources_model()[position.file as int];
        let parsed = &project.circuits_model()[position.file as int];
        let range = parsed.entry_ranges@[position.entry as int].definitions;
        drivers_before(source.text, parsed.syntax.forms@, parsed.definitions@, range.start as int,
            range.end as int, range.end as int, 0, group)
    } by {
        if i < index { assert(updated[i] == groups[i]); }
    };
    reveal_with_fuel(joined_targets, 2);
    reveal_with_fuel(joined_origins, 2);
    if index > 0 {
        common_group_prefix(members, updated, groups, index as nat);
    }
}

proof fn common_group_prefix(
    members: Seq<ModuleBodyPosition>, left: Seq<Seq<DefinitionDriver>>, right: Seq<Seq<DefinitionDriver>>, count: nat,
)
    requires count <= left.len() && count <= right.len(),
        forall|i: int| 0 <= i < count ==> #[trigger] left[i] == #[trigger] right[i],
    ensures joined_targets(left, count) == joined_targets(right, count),
        joined_origins(members, left, count) == joined_origins(members, right, count),
    decreases count,
{
    reveal(joined_targets);
    reveal(joined_origins);
    if count > 0 { common_group_prefix(members, left, right, (count - 1) as nat); }
}

fn append_targets<'a>(
    from: &[DefinitionDriver<'a>], origin: ModuleBodyPosition, names: &mut Vec<DefinitionDriver<'a>>,
    origins: &mut Vec<ModuleBodyPosition>,
)
    ensures final(names)@ == old(names)@ + from@,
        final(origins)@ == old(origins)@ + repeated_position(origin, from@.len()),
{
    let ghost earlier = names@;
    let ghost prior_origins = origins@;
    let ghost repeated = repeated_position(origin, from@.len());
    let mut i = 0;
    while i < from.len()
        invariant
            i <= from@.len(), names@ == earlier + from@.take(i as int),
            repeated == repeated_position(origin, from@.len()),
            origins@ == prior_origins + repeated.take(i as int),
        decreases from@.len() - i,
    {
        let driver = &from[i];
        let copy = DefinitionDriver { name: NameSite { word: driver.name.word, span: driver.name.span.start..driver.name.span.end },
            definition: driver.definition, result_index: driver.result_index };
        assert(copy == *driver);
        names.push(copy);
        origins.push(origin);
        assert(from@.take(i as int).push(copy) =~= from@.take(i + 1));
        assert(repeated.take(i as int).push(origin) =~= repeated.take(i + 1));
        assert(names@ =~= earlier + from@.take(i + 1));
        assert(origins@ =~= prior_origins + repeated.take(i + 1));
        i += 1;
    }
    assert(from@.take(i as int) =~= from@);
    assert(repeated.take(i as int) =~= repeated);
}

spec fn no_expansions_before(project: &CircuitProject, members: Seq<ModuleBodyPosition>, stop: int) -> bool {
    forall|i: int| 0 <= i < stop ==> {
        let position = #[trigger] members[i];
        routine_expansion_evidence(project.sources_model()[position.file as int].text,
            &project.circuits_model()[position.file as int].syntax, position.entry as int, None)
    }
}

#[verifier::opaque]
spec fn target_origin_matches(
    sources: Seq<ProjectSource>, circuits: Seq<NamedBuildCircuit>, row: DefinitionDriver, position: ModuleBodyPosition,
) -> bool {
    &&& position.file < sources.len() && position.file < circuits.len()
    &&& position.entry < circuits[position.file as int].syntax.entries@.len()
    &&& (circuits[position.file as int].syntax.entries@[position.entry as int].head is Module
        || circuits[position.file as int].syntax.entries@[position.entry as int].head is ModulePart)
    &&& indexed_driver_site(&sources[position.file as int], &circuits[position.file as int], position.entry as int, row)
}

#[verifier::opaque]
spec fn target_origins_match(
    sources: Seq<ProjectSource>, circuits: Seq<NamedBuildCircuit>,
    rows: Seq<DefinitionDriver>, origins: Seq<ModuleBodyPosition>,
) -> bool {
    &&& origins.len() == rows.len()
    &&& forall|j: int| 0 <= j < rows.len() ==> #[trigger] target_origin_matches(sources, circuits, rows[j], origins[j])
}

proof fn joined_origin_is_member(
    members: Seq<ModuleBodyPosition>, groups: Seq<Seq<DefinitionDriver>>, count: nat, index: int,
)
    requires count <= members.len() && count <= groups.len(), 0 <= index < joined_origins(members, groups, count).len(),
    ensures members.contains(joined_origins(members, groups, count)[index]),
    decreases count,
{
    reveal(joined_origins);
    assert(count > 0);
    let prior = joined_origins(members, groups, (count - 1) as nat);
    if index < prior.len() {
        joined_origin_is_member(members, groups, (count - 1) as nat, index);
    } else {
        let i = (count - 1) as int;
        assert(joined_origins(members, groups, count)[index] == members[i]);
        assert(members.contains(members[i]));
    }
}

proof fn extend_target_origins(
    sources: Seq<ProjectSource>, circuits: Seq<NamedBuildCircuit>, earlier: Seq<DefinitionDriver>,
    prior_origins: Seq<ModuleBodyPosition>, position: ModuleBodyPosition, next: Seq<DefinitionDriver>,
)
    requires
        target_origins_match(sources, circuits, earlier, prior_origins),
        position.file < sources.len() && position.file < circuits.len(),
        position.entry < circuits[position.file as int].syntax.entries@.len(),
        circuits[position.file as int].syntax.entries@[position.entry as int].head is Module
            || circuits[position.file as int].syntax.entries@[position.entry as int].head is ModulePart,
        forall|j: int| 0 <= j < next.len() ==> indexed_driver_site(
            &sources[position.file as int], &circuits[position.file as int], position.entry as int, #[trigger] next[j]),
    ensures target_origins_match(sources, circuits, earlier + next,
        prior_origins + repeated_position(position, next.len())),
{
    reveal(target_origins_match);
    let rows = earlier + next;
    let origins = prior_origins + repeated_position(position, next.len());
    assert(origins.len() == rows.len());
    assert forall|j: int| 0 <= j < rows.len() implies
        #[trigger] target_origin_matches(sources, circuits, rows[j], origins[j]) by {
        if j < earlier.len() {
            assert(rows[j] == earlier[j] && origins[j] == prior_origins[j]);
            assert(target_origin_matches(sources, circuits, earlier[j], prior_origins[j]));
        } else {
            assert(rows[j] == next[j - earlier.len()] && origins[j] == position);
            reveal(target_origin_matches);
        }
    };
    assert(target_origins_match(sources, circuits, rows, origins));
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 駆動元の検査後も、本体と断片の所属関係が同じことを示す。
    pub(super) proof fn checked_module_driver_body(&self, owner: ModuleBodyPosition, limit: u64, drivers: ModuleDrivers)
        requires self.module_drivers_result(owner, limit, Ok(Some(drivers))),
        ensures self.targets.module_body_result(drivers.body.owner, Ok(Some(drivers.body))), drivers.body.owner == owner,
    {
        assert(self.targets.module_body_result(owner, Ok(Some(drivers.body))));
        self.targets.module_body_owner(owner, &drivers.body);
    }

    /// 出力宣言と駆動元の並びが対応し、各添字が型表を参照できることを示す。
    pub(super) proof fn module_output_driver(&self, owner: ModuleBodyPosition, limit: u64, drivers: ModuleDrivers, index: int)
        requires self.module_drivers_result(owner, limit, Ok(Some(drivers))),
        ensures
            drivers.outputs@.len() == drivers.signature.outputs@.len(),
            0 <= index < drivers.outputs@.len() ==> {
                let port = drivers.signature.outputs@[index];
                &&& crate::project::location_in_source(port.annotation)
                &&& match drivers.outputs@[index] {
                    OutputDriver::Input(input) => input < drivers.signature.inputs@.len(),
                    OutputDriver::Definition(definition) => definition < drivers.definitions@.len(),
                }
            },
    {
        assert(self.typed_signature_evidence(owner.file, owner.entry, limit, Ok(Some(drivers.signature))));
        self.typed_signature_sites(owner.file, owner.entry, limit, drivers.signature);
        let names = choose|names: Seq<NameSite>| names.len() == drivers.outputs@.len()
            && #[trigger] output_drivers_before(drivers.signature.output_inputs@, names, drivers.definitions@, drivers.outputs@);
        if 0 <= index < drivers.outputs@.len() {
            let driver = drivers.outputs@[index];
            if let OutputDriver::Input(input) = driver {
                assert(drivers.signature.output_inputs@[index] == Some(input));
            }
        }
    }

    /// モジュールの入力型を決めた注釈が、元のソース内にあることを示す。
    pub(super) proof fn module_input_sites(&self, owner: ModuleBodyPosition, limit: u64, drivers: ModuleDrivers)
        requires self.module_drivers_result(owner, limit, Ok(Some(drivers))),
        ensures forall|i: int| 0 <= i < drivers.signature.inputs@.len() ==>
            crate::project::location_in_source((#[trigger] drivers.signature.inputs@[i]).annotation),
    {
        assert(self.typed_signature_evidence(owner.file, owner.entry, limit, Ok(Some(drivers.signature))));
        self.typed_signature_sites(owner.file, owner.entry, limit, drivers.signature);
    }

    /// 各駆動元が、元の本体にある定義と左辺の出力順に対応することを取り出す。
    pub(super) proof fn module_driver_sites(
        &self, owner: ModuleBodyPosition, max_width: u64, drivers: ModuleDrivers, index: int,
    )
        requires self.module_drivers_result(owner, max_width, Ok(Some(drivers))), 0 <= index < drivers.definitions@.len(),
        ensures
            drivers.origins@.len() == drivers.definitions@.len(),
            drivers.body.members@.contains(drivers.origins@[index]),
            ({
                let row = drivers.definitions@[index];
                let at = drivers.origins@[index];
                let project = self.targets.project_model();
                &&& at.file < project.sources_model().len() && at.file < project.circuits_model().len()
                &&& at.entry < project.circuits_model()[at.file as int].syntax.entries@.len()
                &&& (project.circuits_model()[at.file as int].syntax.entries@[at.entry as int].head is Module
                    || project.circuits_model()[at.file as int].syntax.entries@[at.entry as int].head is ModulePart)
                &&& indexed_driver_site(&project.sources_model()[at.file as int], &project.circuits_model()[at.file as int], at.entry as int, row)
            }),
    {
        let project = self.targets.project_model();
        assert(target_origins_match(project.sources_model(), project.circuits_model(), drivers.definitions@, drivers.origins@));
        reveal(target_origins_match);
        let at = drivers.origins@[index];
        assert(target_origin_matches(project.sources_model(), project.circuits_model(), drivers.definitions@[index], at));
        reveal(target_origin_matches);
        let groups = choose|groups: Seq<Seq<DefinitionDriver>>|
            groups.len() == drivers.body.members@.len()
            && drivers.origins@ == joined_origins(drivers.body.members@, groups, groups.len());
        joined_origin_is_member(drivers.body.members@, groups, groups.len(), index);
    }

    /// 署名と本体の定義から駆動元を取り出す処理の結果を表す。
    pub closed spec fn module_drivers_result(
        &self, owner: ModuleBodyPosition, max_width: u64, result: Result<Option<ModuleDrivers<'p, 'a>>, ModuleDriverError<'p, 'a>>,
    ) -> bool {
        let project = self.targets.project_model();
        match result {
            Ok(None) => self.targets.module_body_result(owner, Ok(None)),
            Err(ModuleDriverError::Parts(error)) => self.targets.module_body_result(owner, Err(error)),
            Err(ModuleDriverError::Signature(error)) =>
                self.typed_signature_evidence(owner.file, owner.entry, max_width, Err(error))
                && (exists|body: ModuleBody| #[trigger] self.targets.module_body_result(owner, Ok(Some(body)))),
            Err(ModuleDriverError::NeedsExpansion(location)) =>
                (exists|signature: TypedRoutineSignature|
                    #[trigger] self.typed_signature_evidence(owner.file, owner.entry, max_width, Ok(Some(signature))))
                && (exists|body: ModuleBody, i: int|
                #[trigger] self.targets.module_body_result(owner, Ok(Some(body))) && 0 <= i < body.members@.len()
                && {
                    let position = #[trigger] body.members@[i];
                    let parsed = &project.circuits_model()[position.file as int];
                    *location.source == project.sources_model()[position.file as int]
                        && routine_expansion_evidence(location.source.text, &parsed.syntax, position.entry as int, Some(location.span))
                        && no_expansions_before(&project, body.members@, i)
                }),
            _ => exists|body: ModuleBody, signature: TypedRoutineSignature, inputs: Seq<NameSite>, outputs: Seq<NameSite>,
                groups: Seq<Seq<DefinitionDriver>>|
                #![trigger self.targets.module_body_result(owner, Ok(Some(body))), self.typed_signature_evidence(owner.file, owner.entry, max_width, Ok(Some(signature))),
                    names_match_ports(project.sources_model()[owner.file as int].text, project.circuits_model()[owner.file as int].syntax.forms@, signature.inputs@, inputs),
                    names_match_ports(project.sources_model()[owner.file as int].text, project.circuits_model()[owner.file as int].syntax.forms@, signature.outputs@, outputs),
                    target_groups_match(&project, body.members@, groups)]
                {
                    let source = &project.sources_model()[owner.file as int];
                    let forms = project.circuits_model()[owner.file as int].syntax.forms@;
                    let definitions = joined_targets(groups, groups.len());
                    let origins = joined_origins(body.members@, groups, groups.len());
                    &&& self.targets.module_body_result(owner, Ok(Some(body)))
                    &&& self.typed_signature_evidence(owner.file, owner.entry, max_width, Ok(Some(signature)))
                    &&& names_match_ports(source.text, forms, signature.inputs@, inputs) && inputs.len() == signature.inputs@.len()
                    &&& names_match_ports(source.text, forms, signature.outputs@, outputs) && outputs.len() == signature.outputs@.len()
                    &&& target_groups_match(&project, body.members@, groups) && groups.len() == body.members@.len()
                    &&& target_origins_match(project.sources_model(), project.circuits_model(), definitions, origins)
                    &&& no_expansions_before(&project, body.members@, body.members@.len() as int)
                    &&& match result {
                        Ok(Some(drivers)) => drivers.body == body && drivers.signature == signature
                            && drivers.definitions@ == definitions && drivers.origins@ == origins
                            && single_drivers_before(inputs, definitions, definitions.len() as int)
                            && drivers.outputs@.len() == outputs.len()
                            && output_drivers_before(signature.output_inputs@, outputs, definitions, drivers.outputs@),
                        Err(ModuleDriverError::Signals(error)) =>
                            (single_drivers_before(inputs, definitions, definitions.len() as int)
                                && missing_output_error(source, signature.output_inputs@, outputs, definitions, error))
                            || (exists|conflict: super::function_drivers::DriverConflict|
                                #[trigger] definition_binding_conflict(inputs, definitions, conflict) && {
                                    let current = definitions[conflict.at as int].name;
                                    let body = origins[conflict.at as int];
                                    let later = &project.sources_model()[body.file as int];
                                    match (conflict.previous, error) {
                                        (OutputDriver::Input(i), FuncDriverError::DrivesInput { target, input }) =>
                                            is_location(later, current, target) && is_location(source, inputs[i as int], input),
                                        (OutputDriver::Definition(i), FuncDriverError::MultipleDrivers { later: site, first }) => {
                                            let early = &project.sources_model()[origins[i as int].file as int];
                                            is_location(later, current, site) && is_location(early, definitions[i as int].name, first)
                                        },
                                        _ => false,
                                    }
                                }),
                        _ => false,
                    }
                },
        }
    }

    /// 全断片の左辺から駆動元を確定し、出力宣言と照合する。
    ///
    /// # Errors
    ///
    /// 断片の所有先と署名を検査した後、未展開のマクロ、駆動元の衝突、未駆動の出力を順に検査する。
    /// 多重駆動の診断では後から現れた左辺と、最初の左辺のソース範囲を返す。
    pub fn check_module_drivers(&self, owner: ModuleBodyPosition, max_width: u64)
        -> (result: Result<Option<ModuleDrivers<'p, 'a>>, ModuleDriverError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_drivers_result(owner, max_width, result),
    {
        match self.index_module_drivers(owner, max_width) {
            Ok(Some(prepared)) => Ok(Some(prepared.drivers)),
            Ok(None) => Ok(None),
            Err(error) => Err(error),
        }
    }

    pub(super) closed spec fn indexed_module_drivers_result(
        &self, owner: ModuleBodyPosition, max_width: u64,
        result: Result<Option<IndexedModuleDrivers<'p, 'a>>, ModuleDriverError<'p, 'a>>,
    ) -> bool {
        match result {
            Ok(Some(prepared)) => {
                let drivers = prepared.drivers;
                let project = self.targets.project_model();
                &&& self.module_drivers_result(owner, max_width, Ok(Some(drivers)))
                &&& self.targets.module_body_result(owner, Ok(Some(drivers.body)))
                &&& drivers.body.owner == owner
                &&& prepared.inputs@.len() == drivers.signature.inputs@.len()
                &&& names_match_ports(project.sources_model()[owner.file as int].text,
                    project.circuits_model()[owner.file as int].syntax.forms@, drivers.signature.inputs@, prepared.inputs@)
                &&& (prepared.index matches Some(index) ==> optional_local_index(
                    Some(&index), prepared.inputs@, drivers.definitions@, drivers.definitions@.len() as int))
                &&& target_origins_match(project.sources_model(), project.circuits_model(),
                    drivers.definitions@, drivers.origins@)
            },
            Ok(None) => self.module_drivers_result(owner, max_width, Ok(None)),
            Err(error) => self.module_drivers_result(owner, max_width, Err(error)),
        }
    }

    /// 後続の右辺検査に、駆動元と元の本体の対応を渡す。
    pub(super) proof fn indexed_module_drivers_evidence(
        &self, owner: ModuleBodyPosition, max_width: u64, prepared: &IndexedModuleDrivers,
    )
        requires self.indexed_module_drivers_result(owner, max_width, Ok(Some(*prepared))),
        ensures
            self.module_drivers_result(owner, max_width, Ok(Some(prepared.drivers))),
            self.targets.module_body_result(owner, Ok(Some(prepared.drivers.body))),
            prepared.drivers.body.owner == owner,
            prepared.inputs@.len() == prepared.drivers.signature.inputs@.len(),
            optional_local_index(match &prepared.index { Some(index) => Some(index), None => None },
                prepared.inputs@, prepared.drivers.definitions@, prepared.drivers.definitions@.len() as int),
    {
    }

    pub(super) fn index_module_drivers(&self, owner: ModuleBodyPosition, max_width: u64)
        -> (result: Result<Option<IndexedModuleDrivers<'p, 'a>>, ModuleDriverError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.indexed_module_drivers_result(owner, max_width, result),
    {
        let body = match self.targets.module_body(owner) {
            Ok(Some(body)) => body,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleDriverError::Parts(error)),
        };
        proof {
            self.targets.module_body_owner(owner, &body);
            self.targets.module_body_member(&body, 0);
        }
        let signature = match self.resolve_routine_signature(owner.file, owner.entry, max_width) {
            Ok(Some(signature)) => signature,
            Ok(None) => {
                proof {
                    self.typed_signature_skips_non_routines(owner.file, owner.entry, max_width);
                    assert(false);
                }
                unreachable!()
            },
            Err(error) => return Err(ModuleDriverError::Signature(error)),
        };
        let project = self.targets.project();
        let circuits = project.circuits();
        let sources = project.sources();
        let source = &sources[owner.file];
        let parsed = &circuits[owner.file];
        proof {
            self.typed_signature_sites(owner.file, owner.entry, max_width, signature);
            parsed_index_evidence(*source, *parsed);
        }
        let inputs = typed_port_names(source.text, parsed.syntax.forms.as_slice(), signature.inputs.as_slice());
        let outputs = typed_port_names(source.text, parsed.syntax.forms.as_slice(), signature.outputs.as_slice());
        let mut rows = Vec::new();
        let mut origins = Vec::new();
        assert(target_origins_match(sources@, circuits@, rows@, origins@)) by { reveal(target_origins_match); };
        let ghost mut groups: Seq<Seq<DefinitionDriver>> = Seq::empty();
        assert(target_groups_match(project, body.members@, groups)) by { reveal(target_groups_match); };
        assert(rows@ == joined_targets(groups, 0) && origins@ == joined_origins(body.members@, groups, 0)) by {
            reveal(joined_targets);
            reveal(joined_origins);
        };
        let mut i = 0;
        while i < body.members.len()
            invariant
                self.can_resolve(), project.has_parsed_sources(), *project == self.targets.project_model(),
                self.targets.module_body_result(owner, Ok(Some(body))), body.owner == owner,
                self.typed_signature_evidence(owner.file, owner.entry, max_width, Ok(Some(signature))),
                sources@ == project.sources_model(), circuits@ == project.circuits_model(),
                i <= body.members@.len(), groups.len() == i,
                target_groups_match(project, body.members@, groups),
                no_expansions_before(project, body.members@, i as int),
                rows@ == joined_targets(groups, i as nat),
                origins@ == joined_origins(body.members@, groups, i as nat),
                target_origins_match(sources@, circuits@, rows@, origins@),
            decreases body.members@.len() - i,
        {
            proof { self.targets.module_body_member(&body, i as int); }
            let position = body.members[i];
            let origin = &sources[position.file];
            let fragment = &circuits[position.file];
            proof { parsed_index_evidence(*origin, *fragment); }
            if let Some(span) = first_routine_expansion(origin.text, &fragment.syntax, position.entry) {
                let location = LocatedName { source: origin, span };
                proof { located_name_evidence(location); }
                return Err(ModuleDriverError::NeedsExpansion(location));
            }
            assert(no_expansions_before(project, body.members@, i + 1)) by {
                assert forall|j: int| 0 <= j <= i implies {
                    let at = #[trigger] body.members@[j];
                    routine_expansion_evidence(project.sources_model()[at.file as int].text,
                        &project.circuits_model()[at.file as int].syntax, at.entry as int, None)
                } by {
                    self.targets.module_body_member(&body, j);
                    if j == i { assert(body.members@[j] == position); }
                };
            };
            let definitions = collect_drivers(origin.text, fragment, position.entry);
            let ghost before = rows@;
            let ghost earlier_origins = origins@;
            append_targets(definitions.as_slice(), position, &mut rows, &mut origins);
            proof {
                extend_target_groups(project, body.members@, groups, i as int, definitions@);
                groups = groups.push(definitions@);
                assert forall|j: int| 0 <= j < definitions@.len() implies indexed_driver_site(
                    &sources@[position.file as int], &circuits@[position.file as int], position.entry as int,
                    #[trigger] definitions@[j],
                ) by {
                    assert(*origin == sources@[position.file as int] && *fragment == circuits@[position.file as int]);
                };
                extend_target_origins(sources@, circuits@, before, earlier_origins, position, definitions@);
            }
            i += 1;
        }
        let index = match check_definition_bindings(inputs.as_slice(), rows.as_slice(), true) {
            Ok(index) => index,
            Err(conflict) => {
                proof {
                    reveal(target_origins_match);
                    reveal(target_origin_matches);
                    assert(target_origin_matches(sources@, circuits@, rows@[conflict.at as int], origins@[conflict.at as int]));
                }
                let origin = origins[conflict.at];
                let target = name_location(&sources[origin.file], &rows[conflict.at].name);
                let error = match conflict.previous {
                    OutputDriver::Input(input) => FuncDriverError::DrivesInput {
                        target, input: name_location(source, &inputs[input]),
                    },
                    OutputDriver::Definition(first) => {
                        assert(target_origin_matches(sources@, circuits@, rows@[first as int], origins@[first as int]));
                        let origin = origins[first];
                        FuncDriverError::MultipleDrivers {
                            later: target, first: name_location(&sources[origin.file], &rows[first].name),
                        }
                    },
                };
                return Err(ModuleDriverError::Signals(error));
            },
        };
        let drivers = match check_outputs(source, signature.output_inputs.as_slice(), outputs.as_slice(),
            rows.as_slice(), inputs.as_slice(), index.as_ref()) {
            Ok(drivers) => drivers,
            Err(error) => return Err(ModuleDriverError::Signals(error)),
        };
        let drivers = ModuleDrivers { body, signature, definitions: rows, origins, outputs: drivers };
        assert(self.module_drivers_result(owner, max_width, Ok(Some(drivers))));
        Ok(Some(IndexedModuleDrivers { drivers, inputs, index }))
    }
}

} // verus!
