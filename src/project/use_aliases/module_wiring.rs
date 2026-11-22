//! 右辺の信号を、モジュール全体で共有する駆動元に結び付ける。

use super::{ModuleDriverError, ModuleDrivers, OutputDriver, UseAliases};
use super::function_drivers::{lookup_local_name, name_location};
#[cfg(verus_only)]
use super::{
    function_drivers::{is_location, local_lookup_matches, optional_local_index},
    function_wiring::signal_site,
};
use super::module_drivers::IndexedModuleDrivers;
use crate::project::{LocatedName, ModuleBodyPosition, ModuleDefinition, ProjectSource, circuits::read_indexed_atom};
#[cfg(verus_only)]
use crate::project::{CircuitProject, circuits::{parsed_circuit_matches, parsed_index_evidence}};
use crate::syntax::circuit::{NameSite, NamedBuildCircuit};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence, build_signal_cursor_evidence, build_signal_evidence};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 右辺にある信号名と、その値を供給する駆動元。
#[derive(Debug)]
pub struct BoundModuleSignal<'p, 'a> {
    /// 信号名を書いた元ソースの範囲。
    pub site: LocatedName<'p, 'a>,
    /// 信号名を使った定義の位置。
    pub definition: ModuleDefinition,
    /// 信号名を表す構文木の添字。
    pub form: usize,
    /// モジュールの入力、または全断片から集めた左辺の添字。
    pub driver: OutputDriver,
}

/// モジュールの入出力と、各本体の右辺にある信号の束縛。
#[derive(Debug)]
pub struct ModuleWiring<'p, 'a> {
    /// ポート宣言と、全断片から集めた駆動元。
    pub drivers: ModuleDrivers<'p, 'a>,
    /// `drivers.body.members` と同じ順に並んだ右辺の束縛。各列は本体の構文順。
    pub signals: Vec<Vec<BoundModuleSignal<'p, 'a>>>,
}

/// モジュールの信号を解決できなかった理由。
#[derive(Debug)]
pub enum ModuleWiringError<'p, 'a> {
    /// 左辺の駆動元または署名を検査したときの診断。
    Drivers(ModuleDriverError<'p, 'a>),
    /// モジュールの入力にも定義の左辺にもない名前を参照した箇所。
    Undefined(LocatedName<'p, 'a>),
}

spec fn member_signal_matches(
    source: &ProjectSource, parsed: &NamedBuildCircuit, body: ModuleBodyPosition, cursor: int,
    prepared: &IndexedModuleDrivers, bound: BoundModuleSignal,
) -> bool {
    let row = parsed.entry_ranges@[body.entry as int].definitions;
    let absolute = row.start as int + bound.definition.local as int;
    &&& bound.definition.body == body
    &&& 0 <= absolute <= usize::MAX
    &&& bound.form == parsed.signals@[cursor]
    &&& exists|name: NameSite| #[trigger] signal_site(source, parsed, body.entry as int, cursor, absolute as usize, name)
        && is_location(source, name, bound.site)
        && local_lookup_matches(prepared.inputs@, prepared.drivers.definitions@, prepared.drivers.definitions@.len() as int,
            name.word.spec_bytes(), Some(bound.driver))
}

#[verifier::opaque]
spec fn bound_signals_before(
    source: &ProjectSource, parsed: &NamedBuildCircuit, body: ModuleBodyPosition, stop: int,
    prepared: &IndexedModuleDrivers, signals: Seq<BoundModuleSignal>,
) -> bool {
    let start = parsed.entry_ranges@[body.entry as int].signals.start;
    &&& start <= stop && signals.len() == stop - start
    &&& forall|i: int| 0 <= i < signals.len() ==>
        member_signal_matches(source, parsed, body, start + i, prepared, #[trigger] signals[i])
}

spec fn missing_signal(
    source: &ProjectSource, parsed: &NamedBuildCircuit, body: ModuleBodyPosition, cursor: int,
    prepared: &IndexedModuleDrivers, site: LocatedName,
) -> bool {
    exists|definition: usize, name: NameSite| #[trigger] signal_site(source, parsed, body.entry as int, cursor, definition, name)
        && is_location(source, name, site)
        && local_lookup_matches(prepared.inputs@, prepared.drivers.definitions@, prepared.drivers.definitions@.len() as int,
            name.word.spec_bytes(), None)
}

spec fn member_signal_result(
    source: &ProjectSource, parsed: &NamedBuildCircuit, body: ModuleBodyPosition, prepared: &IndexedModuleDrivers,
    result: Result<Vec<BoundModuleSignal>, LocatedName>,
) -> bool {
    let frame = parsed.entry_ranges@[body.entry as int].signals;
    match result {
        Ok(signals) => bound_signals_before(source, parsed, body, frame.end as int, prepared, signals@),
        Err(site) => exists|cursor: int, prior: Seq<BoundModuleSignal>| frame.start <= cursor < frame.end
            && #[trigger] bound_signals_before(source, parsed, body, cursor, prepared, prior)
            && missing_signal(source, parsed, body, cursor, prepared, site),
    }
}

fn bind_member_signals<'p, 'a>(
    source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>, body: ModuleBodyPosition,
    prepared: &IndexedModuleDrivers<'p, 'a>,
) -> (result: Result<Vec<BoundModuleSignal<'p, 'a>>, LocatedName<'p, 'a>>)
    requires
        parsed_circuit_matches(*source, *parsed),
        body.entry < parsed.syntax.entries@.len(),
        optional_local_index(match &prepared.index { Some(index) => Some(index), None => None }, prepared.inputs@,
            prepared.drivers.definitions@, prepared.drivers.definitions@.len() as int),
    ensures member_signal_result(source, parsed, body, prepared, result),
{
    let ghost model = parsed.build_model();
    proof {
        parsed_index_evidence(*source, *parsed);
        build_entry_ranges_evidence(source.text, &model, body.entry as int);
        reveal(bound_signals_before);
    }
    let range = &parsed.entry_ranges[body.entry];
    let rows = prepared.drivers.definitions.as_slice();
    let inputs = prepared.inputs.as_slice();
    let index = prepared.index.as_ref();
    let mut position = range.signals.start;
    let mut definition = range.definitions.start;
    let mut signals = Vec::new();
    proof {
        build_signal_cursor_evidence(source.text, &model, body.entry as int, definition as int);
        if definition < range.definitions.end {
            build_definition_scope_evidence(source.text, &model, body.entry as int, definition as int);
        }
    }
    while definition < range.definitions.end
        invariant
            parsed_circuit_matches(*source, *parsed),
            optional_local_index(index, inputs@, rows@, rows@.len() as int),
            rows@ == prepared.drivers.definitions@, inputs@ == prepared.inputs@,
            model == parsed.build_model(), range == &parsed.entry_ranges@[body.entry as int],
            body.entry < parsed.syntax.entries@.len(), body.entry < parsed.entry_ranges@.len(),
            range.definitions.start <= definition <= range.definitions.end <= parsed.definitions@.len(),
            range.signals.start <= position <= range.signals.end <= parsed.signals@.len(),
            definition == range.definitions.end ==> position == range.signals.end,
            definition < range.definitions.end ==> parsed.definitions@[definition as int].signals.start
                <= position <= parsed.definitions@[definition as int].signals.end <= range.signals.end,
            bound_signals_before(source, parsed, body, position as int, prepared, signals@),
        decreases range.definitions.end - definition, range.signals.end - position,
    {
        let row = &parsed.definitions[definition];
        if position == row.signals.end {
            proof {
                parsed_index_evidence(*source, *parsed);
                build_signal_cursor_evidence(source.text, &model, body.entry as int, definition + 1);
                if definition + 1 < range.definitions.end {
                    build_definition_scope_evidence(source.text, &model, body.entry as int, definition + 1);
                }
            }
            definition += 1;
            continue;
        }
        proof {
            parsed_index_evidence(*source, *parsed);
            build_signal_evidence(source.text, &model, body.entry as int, definition as int, position as int);
        }
        let form = parsed.signals[position];
        let (word, span) = read_indexed_atom(source.text, parsed.syntax.forms.as_slice(), form);
        let name = NameSite { word, span };
        assert(signal_site(source, parsed, body.entry as int, position as int, definition, name));
        let site = name_location(source, &name);
        let lookup = lookup_local_name(index, inputs, rows, rows.len(), word);
        let Some(driver) = lookup else {
            assert(missing_signal(source, parsed, body, position as int, prepared, site));
            return Err(site);
        };
        let bound = BoundModuleSignal {
            site, definition: ModuleDefinition { body, local: definition - range.definitions.start }, form, driver,
        };
        assert(member_signal_matches(source, parsed, body, position as int, prepared, bound)) by {
            let absolute = parsed.entry_ranges@[body.entry as int].definitions.start as int + bound.definition.local as int;
            assert(absolute == definition as int);
            assert(bound.definition.body == body);
            assert(bound.form == parsed.signals@[position as int]);
            assert(signal_site(source, parsed, body.entry as int, position as int, absolute as usize, name));
            assert(is_location(source, name, bound.site));
            assert(local_lookup_matches(prepared.inputs@, prepared.drivers.definitions@,
                prepared.drivers.definitions@.len() as int, name.word.spec_bytes(), Some(bound.driver)));
            assert(exists|candidate: NameSite| #[trigger] signal_site(source, parsed, body.entry as int,
                position as int, absolute as usize, candidate)
                && is_location(source, candidate, bound.site)
                && local_lookup_matches(prepared.inputs@, prepared.drivers.definitions@,
                    prepared.drivers.definitions@.len() as int, candidate.word.spec_bytes(), Some(bound.driver)));
        };
        let ghost old = signals@;
        signals.push(bound);
        assert(bound_signals_before(source, parsed, body, position + 1, prepared, signals@)) by {
            reveal(bound_signals_before);
            assert forall|i: int| 0 <= i < signals@.len() implies member_signal_matches(
                source, parsed, body, range.signals.start + i, prepared, #[trigger] signals@[i]) by {
                if i < old.len() { assert(signals@[i] == old[i]); }
            };
        };
        position += 1;
    }
    Ok(signals)
}

#[verifier::opaque]
spec fn module_signals_prefix(
    project: &CircuitProject, prepared: &IndexedModuleDrivers, groups: Seq<Vec<BoundModuleSignal>>,
) -> bool {
    let members = prepared.drivers.body.members@;
    &&& groups.len() <= members.len()
    &&& forall|i: int| 0 <= i < groups.len() ==> {
        let body = members[i];
        member_signal_result(&project.sources_model()[body.file as int], &project.circuits_model()[body.file as int],
            body, prepared, Ok(#[trigger] groups[i]))
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 型検査が使う駆動元を、配線検査の成功結果から取り出す。
    pub(super) proof fn module_wiring_keeps_drivers(&self, owner: ModuleBodyPosition, max_width: u64, wiring: ModuleWiring)
        requires self.module_wiring_result(owner, max_width, Ok(Some(wiring))),
        ensures self.module_drivers_result(owner, max_width, Ok(Some(wiring.drivers))),
    {
        let project = self.targets.project_model();
        let prepared = choose|prepared: IndexedModuleDrivers|
            #[trigger] self.indexed_module_drivers_result(owner, max_width, Ok(Some(prepared)))
            && wiring.drivers == prepared.drivers && wiring.signals@.len() == prepared.drivers.body.members@.len()
            && module_signals_prefix(&project, &prepared, wiring.signals@);
        self.indexed_module_drivers_evidence(owner, max_width, &prepared);
    }

    /// 本体ごとの束縛、または定義と信号名の順で最初に見つかった違反を表す。
    pub closed spec fn module_wiring_result(
        &self, owner: ModuleBodyPosition, max_width: u64,
        result: Result<Option<ModuleWiring<'p, 'a>>, ModuleWiringError<'p, 'a>>,
    ) -> bool {
        let project = self.targets.project_model();
        match result {
            Ok(None) => self.indexed_module_drivers_result(owner, max_width, Ok(None)),
            Err(ModuleWiringError::Drivers(error)) => self.indexed_module_drivers_result(owner, max_width, Err(error)),
            _ => exists|prepared: IndexedModuleDrivers|
                #[trigger] self.indexed_module_drivers_result(owner, max_width, Ok(Some(prepared)))
                && match result {
                    Ok(Some(wiring)) => wiring.drivers == prepared.drivers
                        && wiring.signals@.len() == prepared.drivers.body.members@.len()
                        && module_signals_prefix(&project, &prepared, wiring.signals@),
                    Err(ModuleWiringError::Undefined(site)) => exists|before: Seq<Vec<BoundModuleSignal>>|
                        #[trigger] module_signals_prefix(&project, &prepared, before)
                        && before.len() < prepared.drivers.body.members@.len()
                        && {
                            let body = prepared.drivers.body.members@[before.len() as int];
                            member_signal_result(&project.sources_model()[body.file as int],
                                &project.circuits_model()[body.file as int], body, &prepared, Err(site))
                        },
                    _ => false,
                },
        }
    }

    /// 全断片の右辺にある信号を、共有する入力と左辺に結び付ける。
    ///
    /// 同じモジュール内の後続定義も参照できる。保存した構文位置は型と配線の検査に使う。
    ///
    /// # Errors
    ///
    /// 駆動元を検査した後、最初に見つかった未定義信号を元のソース範囲で返す。
    pub fn check_module_wiring(&self, owner: ModuleBodyPosition, max_width: u64)
        -> (result: Result<Option<ModuleWiring<'p, 'a>>, ModuleWiringError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_wiring_result(owner, max_width, result),
    {
        let prepared = match self.index_module_drivers(owner, max_width) {
            Ok(Some(prepared)) => prepared,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleWiringError::Drivers(error)),
        };
        proof { self.indexed_module_drivers_evidence(owner, max_width, &prepared); }
        let project = self.targets.project();
        let circuits = project.circuits();
        let sources = project.sources();
        let members = prepared.drivers.body.members.as_slice();
        let mut signals = Vec::new();
        let mut i = 0;
        assert(module_signals_prefix(project, &prepared, signals@)) by { reveal(module_signals_prefix); };
        while i < members.len()
            invariant
                self.can_resolve(), project.has_parsed_sources(), *project == self.targets.project_model(),
                circuits@ == project.circuits_model(), sources@ == project.sources_model(),
                members@ == prepared.drivers.body.members@, i == signals@.len() <= members@.len(),
                self.indexed_module_drivers_result(owner, max_width, Ok(Some(prepared))),
                self.targets.module_body_result(prepared.drivers.body.owner, Ok(Some(prepared.drivers.body))),
                module_signals_prefix(project, &prepared, signals@),
            decreases members@.len() - i,
        {
            proof {
                self.targets.module_body_member(&prepared.drivers.body, i as int);
                self.indexed_module_drivers_evidence(owner, max_width, &prepared);
            }
            let body = members[i];
            let source = &sources[body.file];
            let parsed = &circuits[body.file];
            let group = match bind_member_signals(source, parsed, body, &prepared) {
                Ok(group) => group,
                Err(site) => return Err(ModuleWiringError::Undefined(site)),
            };
            let ghost prior = signals@;
            signals.push(group);
            assert(module_signals_prefix(project, &prepared, signals@)) by {
                reveal(module_signals_prefix);
                assert forall|j: int| 0 <= j < signals@.len() implies {
                    let position = members@[j];
                    member_signal_result(&project.sources_model()[position.file as int],
                        &project.circuits_model()[position.file as int], position, &prepared, Ok(#[trigger] signals@[j]))
                } by {
                    if j < i { assert(signals@[j] == prior[j]); }
                };
            };
            i += 1;
        }
        Ok(Some(ModuleWiring { drivers: prepared.drivers, signals }))
    }
}

} // verus!
