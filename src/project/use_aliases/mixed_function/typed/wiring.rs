//! 混在プロジェクトの関数で右辺の信号を束縛する。

use super::{FuncDriverResult, LocatedName, MixedFuncDriverError, MixedUseAliases, ProjectSourceIndex};
use crate::project::use_aliases::function_wiring::bind_signals;
use crate::project::{FuncSignalReason, FuncWiring, FuncWiringError, FuncWiringResult};
#[cfg(verus_only)]
use super::{has_mixed_func, mixed_use_targets_match, project_source_index_evidence, NameSite};
#[cfg(verus_only)]
use crate::project::FuncDrivers;
#[cfg(verus_only)]
use crate::project::use_aliases::{function_drivers::names_match_ports,
    function_wiring::{indexed_signal_driver, indexed_signal_driver_matches, signal_sequence_result}};
use vstd::prelude::*;

verus! {

/// 混在プロジェクトの関数にある駆動元または信号参照の違反。
#[derive(Debug)]
pub enum MixedFuncWiringError<'p, 'a> {
    /// 署名または駆動元に違反がある。
    Driver(MixedFuncDriverError<'p, 'a>),
    /// 右辺の信号の駆動元を決められない。
    Signal {
        /// 右辺の信号名の位置と文書版。
        site: LocatedName<'p, 'a>,
        /// 束縛できない理由と、定義がある場合は左辺の名前の位置。
        reason: FuncSignalReason<'p, 'a>,
    },
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// 混在プロジェクトの `func` の右辺にある信号を、入力または先行する `def` に結び付ける。
    ///
    /// `file` は正規化済みのソース一覧の添字で、`entry` はそのファイルの厳格索引の添字。
    /// 関数以外の場合は [`FuncWiringResult::NotFunc`] を返す。展開が必要な場合は
    /// [`FuncWiringResult::NeedsExpansion`] を返す。呼び出しのポート数と型は後続の検査で確かめる。
    ///
    /// # Errors
    ///
    /// 署名と駆動元の違反を先に返し、その後、元ソース順で最初の信号参照の違反を返す。
    /// 自己参照と前方参照では、左辺の位置も返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{FuncSignalReason, FuncWiringResult, MixedFuncWiringError,
    ///     OutputDriver, SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources};
    ///
    /// let circuit = "(func wired (in a) (out z) (def t a) (def z (nor t a)))
    ///     (func invalid (in a) (out z) (def z later) (def later a))";
    /// let project = parse_project_sources(&[
    ///     SourceSnapshot { path: "example.ncg2", revision: 7, text: circuit },
    ///     SourceSnapshot { path: "helper.ncg2m", revision: 4,
    ///         text: "(defn ready (as-type (Fn () Bool) (fn () true)))" },
    /// ]).unwrap();
    /// let targets = index_mixed_use_targets(&project).unwrap();
    /// let aliases = check_mixed_use_aliases(&targets).unwrap();
    /// let Ok(FuncWiringResult::Checked(wiring)) = aliases.check_mixed_func_wiring(0, 0, 64)
    ///     else { panic!() };
    /// assert_eq!(wiring.signals.len(), 3);
    /// assert!(matches!(wiring.signals[0].driver, OutputDriver::Input(0)));
    /// assert!(matches!(wiring.signals[1].driver, OutputDriver::Definition(0)));
    /// assert!(matches!(wiring.signals[2].driver, OutputDriver::Input(0)));
    /// let Err(MixedFuncWiringError::Signal { site, reason: FuncSignalReason::ForwardReference(origin) }) =
    ///     aliases.check_mixed_func_wiring(0, 1, 64) else { panic!() };
    /// assert_eq!(site.span.start, circuit.find("later").unwrap());
    /// assert_eq!(origin.span.start, circuit.rfind("later").unwrap());
    /// assert_eq!((site.source.revision, origin.source.revision), (7, 7));
    /// ```
    pub fn check_mixed_func_wiring(&self, file: usize, entry: usize, max_width: u64)
        -> (result: Result<FuncWiringResult<'p, 'a>, MixedFuncWiringError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures self.mixed_func_wiring_matches(file, entry, max_width, result),
    {
        let (drivers, inputs, index) = match self.prepare_mixed_func_drivers(file, entry, max_width) {
            Ok((FuncDriverResult::NotFunc, _, _)) => return Ok(FuncWiringResult::NotFunc),
            Ok((FuncDriverResult::NeedsExpansion(site), _, _)) => return Ok(FuncWiringResult::NeedsExpansion(site)),
            Ok((FuncDriverResult::Checked(drivers), inputs, index)) => (drivers, inputs, index),
            Err(error) => return Err(MixedFuncWiringError::Driver(error)),
        };
        let project = self.targets().project();
        let source = &project.sources()[file];
        let indexed = &project.indexes()[file];
        let ProjectSourceIndex::Circuit(parsed) = indexed else { unreachable!() };
        proof { project_source_index_evidence(*source, *indexed); }
        match bind_signals(source, parsed, entry, inputs.as_slice(), drivers.definitions.as_slice(), index.as_ref()) {
            Ok(signals) => Ok(FuncWiringResult::Checked(FuncWiring { drivers, signals })),
            Err(FuncWiringError::Signal { site, reason }) => Err(MixedFuncWiringError::Signal { site, reason }),
            Err(FuncWiringError::Driver(_)) => { proof { assert(false); } unreachable!() },
        }
    }

    /// 結線と最初の違反が、同じ関数の駆動元と右辺の参照順に対応することを表す。
    pub closed spec fn mixed_func_wiring_matches(
        &self, file: usize, entry: usize, max_width: u64,
        result: Result<FuncWiringResult, MixedFuncWiringError>,
    ) -> bool {
        match result {
            Ok(FuncWiringResult::NotFunc) => self.mixed_func_driver_matches(file, entry, max_width, Ok(FuncDriverResult::NotFunc)),
            Ok(FuncWiringResult::NeedsExpansion(site)) =>
                self.mixed_func_driver_matches(file, entry, max_width, Ok(FuncDriverResult::NeedsExpansion(site))),
            Err(MixedFuncWiringError::Driver(error)) => self.mixed_func_driver_matches(file, entry, max_width, Err(error)),
            _ => {
                let project = self.targets_model().project_model();
                let source = &project.sources_model()[file as int];
                let parsed = &project.indexes_model()[file as int]->Circuit_0;
                &&& project.has_source_indexes()
                &&& has_mixed_func(&project, file, entry)
                &&& exists|drivers: FuncDrivers, inputs: Seq<NameSite>|
                    #[trigger] self.mixed_func_driver_matches(file, entry, max_width, Ok(FuncDriverResult::Checked(drivers)))
                    && #[trigger] names_match_ports(source.text, parsed.syntax.forms@, drivers.signature.inputs@, inputs)
                    && inputs.len() == drivers.signature.inputs@.len()
                    && match result {
                        Ok(FuncWiringResult::Checked(wiring)) => wiring.drivers == drivers
                            && signal_sequence_result(source, parsed, entry as int, inputs, drivers.definitions@, Ok(wiring.signals)),
                        Err(MixedFuncWiringError::Signal { site, reason }) => signal_sequence_result(
                            source, parsed, entry as int, inputs, drivers.definitions@, Err(FuncWiringError::Signal { site, reason })),
                        _ => false,
                    }
            },
        }
    }

    /// 検査済みの結線から、同じ関数の駆動元の契約を取り出す。
    pub proof fn mixed_wiring_driver_evidence(&self, file: usize, entry: usize, max_width: u64, wiring: FuncWiring)
        requires self.mixed_func_wiring_matches(file, entry, max_width, Ok(FuncWiringResult::Checked(wiring))),
        ensures self.mixed_func_driver_matches(file, entry, max_width, Ok(FuncDriverResult::Checked(wiring.drivers))),
    {}

    /// 厳格索引上の信号参照と、検査済み結線の駆動元を対応付ける。
    pub proof fn mixed_wiring_signal_driver(
        &self, file: usize, entry: usize, max_width: u64, wiring: FuncWiring, definition: usize, position: usize,
    )
        requires
            self.mixed_func_wiring_matches(file, entry, max_width, Ok(FuncWiringResult::Checked(wiring))),
            ({
                let project = self.targets_model().project_model();
                let parsed = project.indexes_model()[file as int]->Circuit_0;
                &&& entry < parsed.entry_ranges@.len()
                &&& {
                    let frame = parsed.entry_ranges@[entry as int].definitions;
                    &&& frame.start <= definition < frame.end <= parsed.definitions@.len()
                    &&& parsed.definitions@[definition as int].signals.start <= position
                        < parsed.definitions@[definition as int].signals.end
                }
            }),
        ensures (indexed_signal_driver_matches(
            &self.targets_model().project_model().sources_model()[file as int],
            &self.targets_model().project_model().indexes_model()[file as int]->Circuit_0,
            entry, wiring, definition, position)),
    {
        let project = self.targets_model().project_model();
        let source = &project.sources_model()[file as int];
        let index = &project.indexes_model()[file as int];
        let parsed = &index->Circuit_0;
        assert(project.has_source_indexes());
        project_source_index_evidence(*source, *index);
        let (_, inputs) = choose|drivers: FuncDrivers, inputs: Seq<NameSite>|
            #[trigger] self.mixed_func_driver_matches(file, entry, max_width, Ok(FuncDriverResult::Checked(drivers)))
            && #[trigger] names_match_ports(source.text, parsed.syntax.forms@, drivers.signature.inputs@, inputs)
            && inputs.len() == drivers.signature.inputs@.len() && wiring.drivers == drivers
            && signal_sequence_result(source, parsed, entry as int, inputs, drivers.definitions@, Ok(wiring.signals));
        indexed_signal_driver(source, parsed, entry, wiring, inputs, definition, position);
    }
}

}
