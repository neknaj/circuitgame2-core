//! 組み合わせ回路の右辺で使う信号を、入力または先行する定義に結び付ける。

use super::function_drivers::{lookup_local_name, name_location};
use super::local_signal_index::LocalSignalIndex;
#[cfg(verus_only)]
use super::function_drivers::{disjoint_input, is_location, names_match_ports, optional_local_index, same_word};
#[cfg(verus_only)]
use super::function_drivers::{expected_output_context, indexed_driver_site, same_definition_driver};
use super::{DefinitionDriver, FuncDriverError, FuncDriverResult, FuncDrivers, OutputDriver, UseAliases};
use crate::project::circuits::read_indexed_atom;
#[cfg(verus_only)]
use crate::project::circuits::{name_in_source, parsed_circuit_matches, parsed_index_evidence};
use crate::project::{LocatedName, ProjectSource};
#[cfg(verus_only)]
use crate::project::location_in_source;
use crate::syntax::circuit::{NameSite, NamedBuildCircuit};
#[cfg(verus_only)]
use crate::syntax::{
    circuit::{build_definition_scope_evidence, build_entry_ranges_evidence, build_signal_cursor_evidence, build_signal_evidence, definition_target_range,
        build_signal_owner_unique},
    form_span,
};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 右辺にある一つの信号参照と、その値を供給する入力または定義。
#[derive(Debug)]
pub struct BoundFuncSignal<'p, 'a> {
    /// 参照元の文書版と UTF-8 半開バイト範囲。
    pub site: LocatedName<'p, 'a>,
    /// この参照を含む、ファイル全体の定義配列の添字。
    pub definition: usize,
    /// 入力一覧または [定義の左辺一覧](FuncDrivers::definitions)を指す。
    pub driver: OutputDriver,
}

/// 組み合わせ回路の出力駆動元と、右辺にある信号参照の束縛。
#[derive(Debug)]
pub struct FuncWiring<'p, 'a> {
    /// 型名を解決した署名と、明示的な出力の駆動元。
    pub drivers: FuncDrivers<'p, 'a>,
    /// 対象の関数で値として参照する信号を、同じ綴りの再出現も含めて元ソース順に並べた一覧。
    pub signals: Vec<BoundFuncSignal<'p, 'a>>,
}

/// 組み合わせ回路の右辺を束縛した結果。
#[derive(Debug)]
pub enum FuncWiringResult<'p, 'a> {
    /// 指定位置に `func` がない。
    NotFunc,
    /// 先に展開が必要な、最初のマクロ呼び出しの範囲。
    NeedsExpansion(LocatedName<'p, 'a>),
    /// 明示的な駆動元が決まり、右辺の信号参照をすべて束縛できた。
    Checked(FuncWiring<'p, 'a>),
}

/// 組み合わせ回路の右辺で信号を束縛できなかった理由。
#[derive(Debug)]
pub enum FuncSignalReason<'p, 'a> {
    /// 関数の入力にも定義の左辺にも、対応する名前がない。
    Undefined,
    /// 同じ `def` で定義する信号を参照した。対応する左辺の名前を示す。
    SelfReference(LocatedName<'p, 'a>),
    /// 後続の `def` で定義する信号を参照した。対応する左辺の名前を示す。
    ForwardReference(LocatedName<'p, 'a>),
}

/// 組み合わせ回路の駆動元または信号参照の違反。
#[derive(Debug)]
pub enum FuncWiringError<'p, 'a> {
    /// 署名または明示的な駆動元に違反がある。
    Driver(FuncDriverError<'p, 'a>),
    /// 右辺の信号参照を束縛できない。
    Signal {
        /// 診断の主範囲となる右辺の名前。
        site: LocatedName<'p, 'a>,
        /// 束縛できない理由と、定義がある場合は左辺の名前の範囲。
        reason: FuncSignalReason<'p, 'a>,
    },
}

spec fn local_binding(
    inputs: Seq<NameSite>, definitions: Seq<DefinitionDriver>, current: usize,
    name: NameSite, driver: OutputDriver,
) -> bool {
    match driver {
        OutputDriver::Input(i) => i < inputs.len() && same_word(inputs[i as int], name),
        OutputDriver::Definition(i) => i < definitions.len()
            && same_word(definitions[i as int].name, name)
            && definitions[i as int].definition < current
            && disjoint_input(inputs, name),
    }
}

proof fn local_bindings_agree(
    left_inputs: Seq<NameSite>, right_inputs: Seq<NameSite>,
    left_defs: Seq<DefinitionDriver>, right_defs: Seq<DefinitionDriver>,
    current: usize, left_name: NameSite, right_name: NameSite, left: OutputDriver, right: OutputDriver,
)
    requires
        left_inputs.len() == right_inputs.len(),
        left_defs.len() == right_defs.len(),
        forall|i: int| 0 <= i < left_inputs.len() ==> same_word(#[trigger] left_inputs[i], #[trigger] right_inputs[i]),
        forall|i: int| 0 <= i < left_defs.len() ==> same_definition_driver(#[trigger] left_defs[i], #[trigger] right_defs[i]),
        forall|i: int, j: int| 0 <= i < j < left_inputs.len() ==> !same_word(#[trigger] left_inputs[i], #[trigger] left_inputs[j]),
        forall|i: int, j: int| 0 <= i < j < left_defs.len() ==>
            !same_word((#[trigger] left_defs[i]).name, (#[trigger] left_defs[j]).name),
        same_word(left_name, right_name),
        local_binding(left_inputs, left_defs, current, left_name, left),
        local_binding(right_inputs, right_defs, current, right_name, right),
    ensures left == right,
{
    match (left, right) {
        (OutputDriver::Input(a), OutputDriver::Input(b)) => {
            assert(same_word(left_inputs[b as int], right_inputs[b as int]));
            assert(same_word(left_inputs[a as int], left_inputs[b as int]));
        },
        (OutputDriver::Definition(a), OutputDriver::Definition(b)) => {
            assert(same_definition_driver(left_defs[b as int], right_defs[b as int]));
            assert(same_word(left_defs[a as int].name, left_defs[b as int].name));
        },
        (OutputDriver::Input(a), OutputDriver::Definition(_)) => {
            assert(same_word(left_inputs[a as int], right_inputs[a as int]));
            assert(!same_word(right_inputs[a as int], right_name));
        },
        (OutputDriver::Definition(_), OutputDriver::Input(b)) => {
            assert(same_word(left_inputs[b as int], right_inputs[b as int]));
            assert(!same_word(left_inputs[b as int], left_name));
        },
    }
}

spec fn unavailable_signal(
    source: &ProjectSource, inputs: Seq<NameSite>, definitions: Seq<DefinitionDriver>,
    current: usize, name: NameSite, reason: FuncSignalReason,
) -> bool {
    &&& disjoint_input(inputs, name)
    &&& match reason {
        FuncSignalReason::Undefined =>
            forall|i: int| 0 <= i < definitions.len() ==> !same_word((#[trigger] definitions[i]).name, name),
        FuncSignalReason::SelfReference(site) =>
            exists|i: int| 0 <= i < definitions.len() && same_word((#[trigger] definitions[i]).name, name)
                && definitions[i].definition == current && is_location(source, definitions[i].name, site),
        FuncSignalReason::ForwardReference(site) =>
            exists|i: int| 0 <= i < definitions.len() && same_word((#[trigger] definitions[i]).name, name)
                && definitions[i].definition > current && is_location(source, definitions[i].name, site),
    }
}

fn bind_signal<'p, 'a>(
    source: &'p ProjectSource<'a>, inputs: &[NameSite], definitions: &[DefinitionDriver],
    current: usize, name: &NameSite, index: Option<&LocalSignalIndex>,
) -> (result: Result<OutputDriver, FuncSignalReason<'p, 'a>>)
    requires
        forall|i: int| 0 <= i < definitions@.len()
            ==> name_in_source(source.text, (#[trigger] definitions@[i]).name),
        optional_local_index(index, inputs@, definitions@, definitions@.len() as int),
    ensures
        match result {
            Ok(driver) => local_binding(inputs@, definitions@, current, *name, driver),
            Err(reason) => unavailable_signal(source, inputs@, definitions@, current, *name, reason),
        },
{
    let i = match lookup_local_name(index, inputs, definitions, definitions.len(), name.word) {
        Some(OutputDriver::Input(i)) => return Ok(OutputDriver::Input(i)),
        Some(OutputDriver::Definition(i)) => i,
        None => return Err(FuncSignalReason::Undefined),
    };
    assert(disjoint_input(inputs@, *name));
    let driver = &definitions[i];
    if driver.definition < current {
        return Ok(OutputDriver::Definition(i));
    }
    let site = name_location(source, &driver.name);
    if driver.definition == current {
        Err(FuncSignalReason::SelfReference(site))
    } else {
        Err(FuncSignalReason::ForwardReference(site))
    }
}

pub(super) open spec fn signal_site(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, position: int,
    definition: usize, name: NameSite,
) -> bool {
    let row = parsed.definitions@[definition as int];
    let form = parsed.signals@[position] as int;
    &&& 0 <= entry < parsed.entry_ranges@.len()
    &&& parsed.entry_ranges@[entry].definitions.start <= definition
        < parsed.entry_ranges@[entry].definitions.end <= parsed.definitions@.len()
    &&& row.signals.start <= position < row.signals.end <= parsed.signals@.len()
    &&& row.expression.start <= form < row.expression.end <= parsed.syntax.forms@.len()
    &&& parsed.syntax.forms@[form] is Atom && parsed.syntax.forms@[form]->Atom_kind is Name
    &&& name.span == form_span(parsed.syntax.forms@[form])
    &&& name_in_source(source.text, name)
}

spec fn binding_at(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, position: int,
    inputs: Seq<NameSite>, definitions: Seq<DefinitionDriver>, bound: BoundFuncSignal,
) -> bool {
    exists|name: NameSite| #[trigger] signal_site(source, parsed, entry, position, bound.definition, name)
        && is_location(source, name, bound.site)
        && local_binding(inputs, definitions, bound.definition, name, bound.driver)
}

#[verifier::opaque]
spec fn bound_prefix(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, inputs: Seq<NameSite>,
    definitions: Seq<DefinitionDriver>, start: int, stop: int, signals: Seq<BoundFuncSignal>,
) -> bool {
    &&& start <= stop && signals.len() == stop - start
    &&& forall|i: int| 0 <= i < signals.len() ==>
        binding_at(source, parsed, entry, start + i, inputs, definitions, #[trigger] signals[i])
}

spec fn signal_error_at(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, position: int,
    inputs: Seq<NameSite>, definitions: Seq<DefinitionDriver>, error: FuncWiringError,
) -> bool {
    error matches FuncWiringError::Signal { site, reason }
        && exists|definition: usize, name: NameSite|
            #[trigger] signal_site(source, parsed, entry, position, definition, name)
                && is_location(source, name, site)
                && unavailable_signal(source, inputs, definitions, definition, name, reason)
}

spec fn signal_sequence_result(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, inputs: Seq<NameSite>,
    definitions: Seq<DefinitionDriver>, result: Result<Vec<BoundFuncSignal>, FuncWiringError>,
) -> bool {
    let frame = parsed.entry_ranges@[entry].signals;
    let start = frame.start as int;
    let stop = frame.end as int;
    match result {
        Ok(signals) => bound_prefix(source, parsed, entry, inputs, definitions, start, stop, signals@),
        Err(error) => exists|position: int, prefix: Seq<BoundFuncSignal>| start <= position < stop
            && #[trigger] bound_prefix(source, parsed, entry, inputs, definitions, start, position, prefix)
            && signal_error_at(source, parsed, entry, position, inputs, definitions, error),
    }
}

fn bind_signals<'p, 'a>(
    source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit<'a>, entry: usize,
    inputs: &[NameSite], definitions: &[DefinitionDriver], index: Option<&LocalSignalIndex>,
) -> (result: Result<Vec<BoundFuncSignal<'p, 'a>>, FuncWiringError<'p, 'a>>)
    requires
        parsed_circuit_matches(*source, *parsed),
        entry < parsed.syntax.entries@.len(),
        optional_local_index(index, inputs@, definitions@, definitions@.len() as int),
        forall|i: int| 0 <= i < definitions@.len()
            ==> name_in_source(source.text, (#[trigger] definitions@[i]).name),
    ensures signal_sequence_result(source, parsed, entry as int, inputs@, definitions@, result),
{
    let ghost model = parsed.build_model();
    proof {
        parsed_index_evidence(*source, *parsed);
        build_entry_ranges_evidence(source.text, &model, entry as int);
        reveal(bound_prefix);
    }
    let frame = &parsed.entry_ranges[entry];
    let mut position = frame.signals.start;
    let mut current = frame.definitions.start;
    let mut signals: Vec<BoundFuncSignal> = Vec::new();
    proof {
        build_signal_cursor_evidence(source.text, &model, entry as int, current as int);
        if current < frame.definitions.end {
            build_definition_scope_evidence(source.text, &model, entry as int, current as int);
        }
    }
    while current < frame.definitions.end
        invariant
            parsed_circuit_matches(*source, *parsed),
            optional_local_index(index, inputs@, definitions@, definitions@.len() as int),
            model == parsed.build_model(),
            frame == &parsed.entry_ranges@[entry as int],
            entry < parsed.syntax.entries@.len(), entry < parsed.entry_ranges@.len(),
            frame.definitions.start <= current <= frame.definitions.end <= parsed.definitions@.len(),
            frame.signals.start <= position <= frame.signals.end <= parsed.signals@.len(),
            current == frame.definitions.end ==> position == frame.signals.end,
            current < frame.definitions.end ==> parsed.definitions@[current as int].signals.start
                <= position <= parsed.definitions@[current as int].signals.end <= frame.signals.end,
            forall|i: int| 0 <= i < definitions@.len()
                ==> name_in_source(source.text, (#[trigger] definitions@[i]).name),
            bound_prefix(source, parsed, entry as int, inputs@, definitions@,
                frame.signals.start as int, position as int, signals@),
        decreases frame.definitions.end - current, frame.signals.end - position,
    {
        proof { reveal(bound_prefix); }
        let row = &parsed.definitions[current];
        if position == row.signals.end {
            proof {
                parsed_index_evidence(*source, *parsed);
                build_signal_cursor_evidence(source.text, &model, entry as int, current + 1);
                if current + 1 < frame.definitions.end {
                    build_definition_scope_evidence(source.text, &model, entry as int, current + 1);
                }
            }
            current += 1;
            continue;
        }
        proof {
            parsed_index_evidence(*source, *parsed);
            build_signal_evidence(source.text, &model, entry as int, current as int, position as int);
        }
        let (word, span) = read_indexed_atom(source.text, parsed.syntax.forms.as_slice(), parsed.signals[position]);
        let name = NameSite { word, span };
        assert(name_in_source(source.text, name));
        assert(signal_site(source, parsed, entry as int, position as int, current, name));
        let site = name_location(source, &name);
        let result = bind_signal(source, inputs, definitions, current, &name, index);
        let driver = match result {
            Ok(driver) => driver,
            Err(reason) => {
                let error = FuncWiringError::Signal { site, reason };
                assert(signal_error_at(source, parsed, entry as int, position as int, inputs@, definitions@, error));
                return Err(error);
            },
        };
        assert(local_binding(inputs@, definitions@, current, name, driver));
        let bound = BoundFuncSignal { site, definition: current, driver };
        assert(is_location(source, name, bound.site));
        assert(signal_site(source, parsed, entry as int, position as int, bound.definition, name));
        assert(binding_at(source, parsed, entry as int, position as int, inputs@, definitions@, bound));
        let ghost before = signals@;
        signals.push(bound);
        assert forall|i: int| 0 <= i < signals@.len()
            implies binding_at(source, parsed, entry as int, frame.signals.start + i, inputs@,
                definitions@, #[trigger] signals@[i]) by {
            if i < before.len() {
                assert(signals@[i] == before[i]);
                assert(binding_at(source, parsed, entry as int, frame.signals.start + i,
                    inputs@, definitions@, before[i]));
            } else {
                assert(i == before.len() && signals@[i] == bound);
            }
        };
        position += 1;
    }
    Ok(signals)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 同じ関数の検査に成功した配線は、各参照位置と出力で同じ駆動元を指す。
    pub(super) proof fn checked_func_wiring_agrees(
        &self, file: usize, entry: usize, limit: u64, left: FuncWiring, right: FuncWiring,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(left))),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(right))),
        ensures
            left.drivers.signature.inputs@ == right.drivers.signature.inputs@,
            left.drivers.signature.outputs@ == right.drivers.signature.outputs@,
            left.drivers.definitions@.len() == right.drivers.definitions@.len(),
            forall|i: int| 0 <= i < left.drivers.definitions@.len() ==> same_definition_driver(
                #[trigger] left.drivers.definitions@[i], #[trigger] right.drivers.definitions@[i]),
            left.drivers.outputs@ == right.drivers.outputs@,
            left.signals@ == right.signals@,
    {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        self.checked_wiring_is_func(file, entry, limit, left);
        self.targets.parsed_project_model();
        parsed_index_evidence(*source, *parsed);
        let a = self.checked_wiring_input_names(file, entry, limit, left);
        let b = self.checked_wiring_input_names(file, entry, limit, right);
        self.checked_func_drivers_agree(file, entry, limit, left.drivers, right.drivers);
        self.typed_signature_input_names_unique(file, entry, limit, left.drivers.signature, a);
        assert forall|i: int| 0 <= i < a.len() implies same_word(#[trigger] a[i], #[trigger] b[i]) by {
            assert(a[i].span == b[i].span);
        };
        let first = parsed.entry_ranges@[entry as int].signals.start as int;
        reveal(bound_prefix);
        assert(left.signals@.len() == right.signals@.len());
        assert forall|i: int| 0 <= i < left.signals@.len() implies
            (#[trigger] left.signals@[i]) == (#[trigger] right.signals@[i]) by {
            let position = first + i;
            let l = left.signals@[i];
            let r = right.signals@[i];
            let l_name = choose|name: NameSite| #[trigger] signal_site(source, parsed, entry as int, position, l.definition, name)
                && is_location(source, name, l.site)
                && local_binding(a, left.drivers.definitions@, l.definition, name, l.driver);
            let r_name = choose|name: NameSite| #[trigger] signal_site(source, parsed, entry as int, position, r.definition, name)
                && is_location(source, name, r.site)
                && local_binding(b, right.drivers.definitions@, r.definition, name, r.driver);
            build_signal_owner_unique(source.text, &parsed.build_model(), entry as int,
                l.definition as int, r.definition as int, position);
            assert(l_name.span == r_name.span);
            local_bindings_agree(a, b, left.drivers.definitions@, right.drivers.definitions@,
                l.definition, l_name, r_name, l.driver, r.driver);
        };
        assert(left.signals@ =~= right.signals@);
    }

    proof fn checked_wiring_input_names(
        &self, file: usize, entry: usize, limit: u64, wiring: FuncWiring,
    ) -> (inputs: Seq<NameSite<'a>>)
        requires self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
        ensures ({
            let project = self.targets.project_model();
            let parsed = &project.circuits_model()[file as int];
            let source = &project.sources_model()[file as int];
            self.func_driver_evidence(file, entry, limit, Ok(FuncDriverResult::Checked(wiring.drivers)))
                && inputs.len() == wiring.drivers.signature.inputs@.len()
                && names_match_ports(source.text, parsed.syntax.forms@, wiring.drivers.signature.inputs@, inputs)
                && signal_sequence_result(source, parsed, entry as int, inputs, wiring.drivers.definitions@, Ok(wiring.signals))
        }),
    {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let (drivers, inputs) = choose|drivers: FuncDrivers, inputs: Seq<NameSite>|
            #[trigger] self.func_driver_evidence(file, entry, limit, Ok(FuncDriverResult::Checked(drivers)))
                && #[trigger] names_match_ports(source.text, parsed.syntax.forms@, drivers.signature.inputs@, inputs)
                && inputs.len() == drivers.signature.inputs@.len()
                && wiring.drivers == drivers
                && signal_sequence_result(source, parsed, entry as int, inputs, drivers.definitions@, Ok(wiring.signals));
        inputs
    }

    pub(super) proof fn checked_signal_driver(
        &self, file: usize, entry: usize, limit: u64, wiring: FuncWiring, definition: usize, position: usize,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
            ({
                let project = self.targets.project_model();
                let parsed = project.circuits_model()[file as int];
                let frame = parsed.entry_ranges@[entry as int].definitions;
                &&& file < project.circuits_model().len()
                &&& entry < parsed.syntax.entries@.len() && entry < parsed.entry_ranges@.len()
                &&& frame.start <= definition < frame.end <= parsed.definitions@.len()
                &&& parsed.definitions@[definition as int].signals.start <= position
                    < parsed.definitions@[definition as int].signals.end
            }),
        ensures ({
            let project = self.targets.project_model();
            let parsed = project.circuits_model()[file as int];
            let source = project.sources_model()[file as int];
            let first = parsed.entry_ranges@[entry as int].signals.start;
            let bound = wiring.signals@[position - first];
            &&& first <= position && position - first < wiring.signals@.len()
            &&& bound.definition == definition
            &&& *bound.site.source == source && location_in_source(bound.site)
            &&& bound.site.span == form_span(parsed.syntax.forms@[parsed.signals@[position as int] as int])
            &&& match bound.driver {
                OutputDriver::Input(i) => i < wiring.drivers.signature.inputs@.len(),
                OutputDriver::Definition(i) => i < wiring.drivers.definitions@.len()
                    && wiring.drivers.definitions@[i as int].definition < definition,
            }
        }),
    {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        self.targets.parsed_project_model();
        parsed_index_evidence(*source, *parsed);
        let model = parsed.build_model();
        build_definition_scope_evidence(source.text, &model, entry as int, definition as int);
        let drivers = wiring.drivers;
        let inputs = self.checked_wiring_input_names(file, entry, limit, wiring);
        reveal(bound_prefix);
        let first = parsed.entry_ranges@[entry as int].signals.start;
        let bound = wiring.signals@[position - first];
        let name = choose|name: NameSite|
            #[trigger] signal_site(source, parsed, entry as int, position as int, bound.definition, name)
                && is_location(source, name, bound.site)
                && local_binding(inputs, drivers.definitions@, bound.definition, name, bound.driver);
        build_signal_owner_unique(source.text, &model, entry as int, definition as int,
            bound.definition as int, position as int);
    }

    pub(super) proof fn checked_wiring_is_func(
        &self, file: usize, entry: usize, max_width: u64, wiring: FuncWiring,
    )
        requires self.can_resolve(), self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(wiring))),
        ensures ({
            let project = self.targets.project_model();
            let circuits = project.circuits_model();
            &&& file < circuits.len() && file < project.sources_model().len()
            &&& entry < circuits[file as int].syntax.entries@.len()
            &&& circuits[file as int].syntax.entries@[entry as int].head is Func
            &&& expected_output_context(&project.sources_model()[file as int], &circuits[file as int], entry as int, wiring.drivers)
            &&& super::function_drivers::checked_ports_and_output_bounds(circuits[file as int].syntax.forms@, wiring.drivers)
            &&& self.typed_signature_evidence(file, entry, max_width, Ok(Some(wiring.drivers.signature)))
            &&& forall|i: int| 0 <= i < wiring.drivers.signature.inputs@.len()
                ==> self.declared_port_type((#[trigger] wiring.drivers.signature.inputs@[i]).ty)
            &&& forall|i: int| 0 <= i < wiring.drivers.signature.outputs@.len()
                ==> self.declared_port_type((#[trigger] wiring.drivers.signature.outputs@[i]).ty)
            &&& forall|i: int| 0 <= i < wiring.drivers.definitions@.len()
                ==> indexed_driver_site(&project.sources_model()[file as int], &circuits[file as int],
                    entry as int, #[trigger] wiring.drivers.definitions@[i])
            &&& forall|i: int, j: int| 0 <= i < j < wiring.drivers.definitions@.len()
                ==> {
                    let first = #[trigger] wiring.drivers.definitions@[i];
                    let last = #[trigger] wiring.drivers.definitions@[j];
                    first.definition < last.definition
                        || (first.definition == last.definition && first.result_index < last.result_index)
                }
        }),
    {
        let drivers = wiring.drivers;
        self.checked_driver_sources(file, entry, max_width, drivers);
        assert forall|i: int, j: int| 0 <= i < j < wiring.drivers.definitions@.len() implies {
            let first = #[trigger] wiring.drivers.definitions@[i];
            let last = #[trigger] wiring.drivers.definitions@[j];
            first.definition < last.definition
                || (first.definition == last.definition && first.result_index < last.result_index)
        } by {
            assert(wiring.drivers.definitions@[i] == drivers.definitions@[i]);
            assert(wiring.drivers.definitions@[j] == drivers.definitions@[j]);
        };
    }

    /// 定義の最初の左辺を、結線検査で保持した駆動元一覧に対応付ける。
    pub(super) proof fn checked_wiring_first_definition_driver(
        &self, file: usize, entry: usize, limit: u64, wiring: FuncWiring, definition: usize,
    ) -> (first: int)
        requires
            self.can_resolve(), self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
            ({
                let parsed = self.targets.project_model().circuits_model()[file as int];
                let frame = parsed.entry_ranges@[entry as int].definitions;
                let (start, end) = definition_target_range(parsed.syntax.forms@, parsed.definitions@[definition as int]);
                &&& frame.start <= definition < frame.end <= parsed.definitions@.len()
                &&& start < end
            }),
        ensures
            0 <= first < wiring.drivers.definitions@.len(),
            wiring.drivers.definitions@[first].definition == definition,
            wiring.drivers.definitions@[first].result_index == 0,
    {
        self.checked_first_definition_driver(file, entry, limit, wiring.drivers, definition)
    }

    pub(super) proof fn checked_wiring_output_group(
        &self, file: usize, entry: usize, limit: u64, wiring: FuncWiring, first: int,
    ) -> (count: nat)
        requires
            self.can_resolve(), self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
            0 <= first < wiring.drivers.definitions@.len(), wiring.drivers.definitions@[first].result_index == 0,
        ensures ({
            let parsed = self.targets.project_model().circuits_model()[file as int];
            let drivers = wiring.drivers.definitions@;
            let definition = drivers[first].definition;
            let (start, end) = definition_target_range(parsed.syntax.forms@, parsed.definitions@[definition as int]);
            &&& count == end - start && count > 0 && first + count <= drivers.len()
            &&& forall|j: int| 0 <= j < count ==> {
                let driver = #[trigger] drivers[first + j];
                &&& driver.definition == definition && driver.result_index == j
            }
        }),
    {
        self.checked_driver_output_group(file, entry, limit, wiring.drivers, first)
    }

    /// 束縛の結果または最初の診断が、同じ関数の駆動元と右辺の参照順に対応することを表す。
    pub closed spec fn func_wiring_evidence(
        &self, file: usize, entry: usize, max_width: u64,
        result: Result<FuncWiringResult, FuncWiringError>,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        match result {
            Ok(FuncWiringResult::NotFunc) => self.func_driver_evidence(file, entry, max_width, Ok(FuncDriverResult::NotFunc)),
            Ok(FuncWiringResult::NeedsExpansion(site)) =>
                self.func_driver_evidence(file, entry, max_width, Ok(FuncDriverResult::NeedsExpansion(site))),
            Err(FuncWiringError::Driver(error)) => self.func_driver_evidence(file, entry, max_width, Err(error)),
            _ => exists|drivers: FuncDrivers, inputs: Seq<NameSite>|
                #[trigger] self.func_driver_evidence(file, entry, max_width, Ok(FuncDriverResult::Checked(drivers)))
                    && #[trigger] names_match_ports(source.text, parsed.syntax.forms@, drivers.signature.inputs@, inputs)
                    && file < project.circuits_model().len() && file < project.sources_model().len()
                    && entry < parsed.entry_ranges@.len()
                    && inputs.len() == drivers.signature.inputs@.len()
                    && match result {
                        Ok(FuncWiringResult::Checked(wiring)) => wiring.drivers == drivers
                            && signal_sequence_result(source, parsed, entry as int, inputs,
                                drivers.definitions@, Ok(wiring.signals)),
                        Err(error) => signal_sequence_result(source, parsed, entry as int, inputs, drivers.definitions@, Err(error)),
                        _ => false,
                    },
        }
    }

    /// `func` の出力駆動元を検査し、右辺の信号を入力または先行する `def` に結び付ける。
    ///
    /// 対象外と展開待ちは駆動元の検査結果を引き継ぐ。右辺の出力数と型は後続の検査で確かめる。
    ///
    /// # Errors
    ///
    /// 署名と出力駆動元の違反を先に返す。それらが確定した場合は、右辺の参照を元ソース順に調べる。
    /// 未定義と自己・前方参照を区別し、定義があれば診断に左辺の範囲も含める。
    pub fn check_func_wiring(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncWiringResult<'p, 'a>, FuncWiringError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_wiring_evidence(file, entry, max_width, result),
    {
        self.check_func_wiring_mode(file, entry, max_width, None)
    }

    fn check_func_wiring_mode(
        &self, file: usize, entry: usize, max_width: u64, index_override: Option<bool>,
    ) -> (result: Result<FuncWiringResult<'p, 'a>, FuncWiringError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_wiring_evidence(file, entry, max_width, result),
    {
        let (drivers, inputs, index) = match self.prepare_func_drivers(file, entry, max_width, index_override) {
            Ok((FuncDriverResult::NotFunc, _, _)) => return Ok(FuncWiringResult::NotFunc),
            Ok((FuncDriverResult::NeedsExpansion(site), _, _)) => return Ok(FuncWiringResult::NeedsExpansion(site)),
            Ok((FuncDriverResult::Checked(drivers), inputs, index)) => (drivers, inputs, index),
            Err(error) => return Err(FuncWiringError::Driver(error)),
        };
        proof { self.checked_driver_sources(file, entry, max_width, drivers); }
        let project = self.targets.project();
        let parsed = &project.circuits()[file];
        let source = &project.sources()[file];
        proof {
            assert(parsed_circuit_matches(*source, *parsed));
            parsed_index_evidence(*source, *parsed);
        }
        let result = bind_signals(source, parsed, entry, inputs.as_slice(), drivers.definitions.as_slice(), index.as_ref());
        match result {
            Ok(signals) => Ok(FuncWiringResult::Checked(FuncWiring { drivers, signals })),
            Err(error) => Err(error),
        }
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{FuncDriverError, FuncSignalReason, FuncWiringError, FuncWiringResult};
    use crate::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};
    use alloc::format;

    #[test]
    fn indexed_wiring_matches_linear_wiring_at_source_boundaries() {
        for (source, expected) in [
            ("(func f (in a) (out x) (def xy a))", &["MissingOutput"][..]),
            ("(func f (in a) (out y) (def xy a) (def y x))", &["Undefined"][..]),
            ("(func f (in a) (out x X xy) (def x a) (def X x) (def xy X))", &["Checked"][..]),
            ("(func f (in a) (out a) (def x a) (def x a) (def a x))", &["MultipleDrivers"][..]),
            ("(func f (in a) (out a) (def x y) (def y a))", &["ForwardReference"][..]),
            ("(func f (in a) (out a) (def (x y) (pair a y)))", &["SelfReference"][..]),
            ("(func a (in x) (out local) (def local x)) (func b (in) (out y) (def y local))", &["Checked", "Undefined"][..]),
        ] {
            let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 7, text: source }]).unwrap();
            let targets = index_use_targets(&project).unwrap();
            let aliases = check_use_aliases(&targets).unwrap();
            assert_eq!(project.circuits()[0].syntax.entries.len(), expected.len());
            for (entry, expected) in expected.iter().enumerate() {
                let linear = aliases.check_func_wiring_mode(0, entry, 64, Some(false));
                let indexed = aliases.check_func_wiring_mode(0, entry, 64, Some(true));
                assert_eq!(format!("{linear:?}"), format!("{indexed:?}"), "{source}");
                let outcome = match indexed {
                    Ok(FuncWiringResult::Checked(_)) => "Checked",
                    Err(FuncWiringError::Driver(FuncDriverError::MissingOutput(_))) => "MissingOutput",
                    Err(FuncWiringError::Driver(FuncDriverError::MultipleDrivers { .. })) => "MultipleDrivers",
                    Err(FuncWiringError::Signal { reason: FuncSignalReason::Undefined, .. }) => "Undefined",
                    Err(FuncWiringError::Signal { reason: FuncSignalReason::ForwardReference(_), .. }) => "ForwardReference",
                    Err(FuncWiringError::Signal { reason: FuncSignalReason::SelfReference(_), .. }) => "SelfReference",
                    other => panic!("unexpected wiring outcome: {other:?}"),
                };
                assert_eq!(outcome, *expected, "{source}");
            }
        }
    }
}
