//! 組み合わせ回路の右辺で使う信号を、入力または先行する定義に結び付ける。

use super::function_drivers::{find_driver, name_location, typed_port_names};
#[cfg(verus_only)]
use super::function_drivers::{disjoint_input, is_location, names_match_ports, same_word};
use super::{DefinitionDriver, FuncDriverError, FuncDriverResult, FuncDrivers, OutputDriver, UseAliases};
use crate::project::circuits::read_indexed_atom;
#[cfg(verus_only)]
use crate::project::circuits::{name_in_source, parsed_circuit_matches, parsed_index_evidence};
use crate::project::signatures::first_matching_name;
use crate::project::{LocatedName, ProjectSource};
use crate::syntax::circuit::{NameSite, NamedBuildCircuit};
#[cfg(verus_only)]
use crate::syntax::{
    circuit::{build_definition_scope_evidence, build_entry_ranges_evidence, build_signal_cursor_evidence, build_signal_evidence},
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
    current: usize, name: &NameSite,
) -> (result: Result<OutputDriver, FuncSignalReason<'p, 'a>>)
    requires
        forall|i: int| 0 <= i < definitions@.len()
            ==> name_in_source(source.text, (#[trigger] definitions@[i]).name),
    ensures
        match result {
            Ok(driver) => local_binding(inputs@, definitions@, current, *name, driver),
            Err(reason) => unavailable_signal(source, inputs@, definitions@, current, *name, reason),
        },
{
    if let Some(i) = first_matching_name(inputs, inputs.len(), name.word) {
        return Ok(OutputDriver::Input(i));
    }
    assert(disjoint_input(inputs@, *name));
    let Some(i) = find_driver(definitions, definitions.len(), name.word) else {
        return Err(FuncSignalReason::Undefined);
    };
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

spec fn signal_site(
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
    inputs: &[NameSite], definitions: &[DefinitionDriver],
) -> (result: Result<Vec<BoundFuncSignal<'p, 'a>>, FuncWiringError<'p, 'a>>)
    requires
        parsed_circuit_matches(*source, *parsed),
        entry < parsed.syntax.entries@.len(),
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
        let result = bind_signal(source, inputs, definitions, current, &name);
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
    pub(super) proof fn checked_wiring_is_func(
        &self, file: usize, entry: usize, max_width: u64, wiring: FuncWiring,
    )
        requires self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(wiring))),
        ensures ({
            let project = self.targets.project_model();
            let circuits = project.circuits_model();
            &&& file < circuits.len() && file < project.sources_model().len()
            &&& entry < circuits[file as int].syntax.entries@.len()
            &&& circuits[file as int].syntax.entries@[entry as int].head is Func
        }),
    {
        self.checked_driver_sources(file, entry, max_width, wiring.drivers);
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
        let drivers = match self.check_func_drivers(file, entry, max_width) {
            Ok(FuncDriverResult::NotFunc) => return Ok(FuncWiringResult::NotFunc),
            Ok(FuncDriverResult::NeedsExpansion(site)) => return Ok(FuncWiringResult::NeedsExpansion(site)),
            Ok(FuncDriverResult::Checked(drivers)) => drivers,
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
        let inputs = typed_port_names(source.text, parsed.syntax.forms.as_slice(), drivers.signature.inputs.as_slice());
        let result = bind_signals(source, parsed, entry, inputs.as_slice(), drivers.definitions.as_slice());
        match result {
            Ok(signals) => Ok(FuncWiringResult::Checked(FuncWiring { drivers, signals })),
            Err(error) => Err(error),
        }
    }
}

} // verus!
