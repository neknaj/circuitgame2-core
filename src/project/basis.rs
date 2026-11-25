//! 構文解析を終えた回路ソース集合に共通の基底を検査する。

#[cfg(verus_only)]
use super::circuits::parsed_index_evidence;
use super::circuits::read_indexed_atom;
#[cfg(verus_only)]
use super::declarations::located_name_evidence;
#[cfg(verus_only)]
use super::location_in_source;
use super::{CircuitProject, LocatedName, ParsedProjectSources, ProjectSource, ProjectSourceIndex};
#[cfg(verus_only)]
use super::{parsed_circuit_matches, project_source_index_matches, source_indexes::project_source_index_evidence};
use crate::syntax::circuit::{Head, NamedBuildCircuit};
#[cfg(verus_only)]
use crate::syntax::{circuit::basis_entry_evidence, form_span};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 回路ソース集合の基底指定に関する診断。
#[derive(Debug)]
pub enum CircuitBasisError<'p, 'a> {
    /// 回路ソースに基底の指定がない。
    Missing,
    /// 基底の指定が複数ある。
    Duplicate {
        /// 二つ目の指定にある `nor` の範囲。診断の主範囲に使う。
        later: LocatedName<'p, 'a>,
        /// 最初の指定にある `nor` の範囲。診断の関連範囲に使う。
        first: LocatedName<'p, 'a>,
    },
}

struct BasisSite<'p, 'a> {
    _file: usize,
    _entry: usize,
    location: LocatedName<'p, 'a>,
}

// 収集済みの順序を保ち、基底を持てない関数型ソースの位置も残す。
enum BasisProject<'p, 'a> {
    Circuit(&'p CircuitProject<'a>),
    Mixed(&'p ParsedProjectSources<'a>),
}

impl<'p, 'a> BasisProject<'p, 'a> {
    spec fn valid(&self) -> bool {
        match self {
            Self::Circuit(project) => project.has_parsed_sources(),
            Self::Mixed(project) => project.has_source_indexes(),
        }
    }

    spec fn sources_model(&self) -> Seq<ProjectSource<'a>> {
        match self {
            Self::Circuit(project) => project.sources_model(),
            Self::Mixed(project) => project.sources_model(),
        }
    }

    spec fn circuit_model(&self, file: int) -> Option<NamedBuildCircuit<'a>> {
        match self {
            Self::Circuit(project) => Some(project.circuits_model()[file]),
            Self::Mixed(project) => match project.indexes_model()[file] {
                ProjectSourceIndex::Circuit(parsed) => Some(parsed),
                ProjectSourceIndex::Functional(_) => None,
            },
        }
    }

    spec fn entry_count(&self, file: int) -> nat {
        match self.circuit_model(file) {
            Some(parsed) => parsed.syntax.entries@.len(),
            None => 0,
        }
    }

    fn sources(&self) -> (sources: &'p [ProjectSource<'a>])
        ensures sources@ == self.sources_model(),
    {
        match self {
            Self::Circuit(project) => project.sources(),
            Self::Mixed(project) => project.sources(),
        }
    }

    fn circuit(&self, file: usize) -> (parsed: Option<&'p NamedBuildCircuit<'a>>)
        requires self.valid(), file < self.sources_model().len(),
        ensures parsed matches Some(parsed) ==> self.circuit_model(file as int) == Some(*parsed)
            && parsed_circuit_matches(self.sources_model()[file as int], *parsed),
            parsed is None ==> self.circuit_model(file as int).is_none(),
    {
        match self {
            Self::Circuit(project) => {
                let parsed = &project.circuits()[file];
                assert(parsed_circuit_matches(project.sources_model()[file as int], *parsed));
                Some(parsed)
            },
            Self::Mixed(project) => {
                let index = &project.indexes()[file];
                match index {
                    ProjectSourceIndex::Circuit(parsed) => {
                        proof {
                            let source = project.sources_model()[file as int];
                            assert(project_source_index_matches(source, *index));
                            project_source_index_evidence(source, *index);
                        }
                        Some(parsed)
                    },
                    ProjectSourceIndex::Functional(_) => None,
                }
            },
        }
    }
}

spec fn has_circuit_before(project: &BasisProject, end: int) -> bool {
    exists|f: int| 0 <= f < end && (#[trigger] project.circuit_model(f)).is_some()
}

proof fn extend_circuit_prefix(project: &BasisProject, file: int)
    requires 0 <= file,
    ensures has_circuit_before(project, file + 1)
        == (has_circuit_before(project, file) || project.circuit_model(file).is_some()),
{
    if has_circuit_before(project, file + 1) {
        let f = choose|f: int| 0 <= f < file + 1 && (#[trigger] project.circuit_model(f)).is_some();
        if f < file {
            assert(has_circuit_before(project, file));
        }
    } else {
        assert(!project.circuit_model(file).is_some());
        if has_circuit_before(project, file) {
            let f = choose|f: int| 0 <= f < file && (#[trigger] project.circuit_model(f)).is_some();
            assert(0 <= f < file + 1);
        }
    }
}

spec fn basis_at(project: &BasisProject, file: int, entry: int) -> bool {
    &&& 0 <= file < project.sources_model().len()
    &&& project.circuit_model(file) matches Some(parsed)
    &&& 0 <= entry < parsed.syntax.entries@.len()
    &&& parsed.syntax.entries@[entry].head is Using
}

spec fn before(file: int, entry: int, stop_file: int, stop_entry: int) -> bool {
    file < stop_file || (file == stop_file && entry < stop_entry)
}

spec fn basis_location(project: &BasisProject, file: int, entry: int, location: LocatedName) -> bool {
    &&& basis_at(project, file, entry)
    &&& file < project.sources_model().len()
    &&& *location.source == project.sources_model()[file]
    &&& location_in_source(location)
    &&& project.circuit_model(file) matches Some(parsed) && {
        let arg = parsed.syntax.entries@[entry].form + 2;
        &&& parsed.syntax.entries@[entry].namespace is None
        &&& arg < parsed.syntax.forms@.len()
        &&& location.span == form_span(parsed.syntax.forms@[arg])
        &&& location.source.text.spec_bytes()[location.span.start as int..location.span.end as int] == "nor".spec_bytes()
    }
}

spec fn only_before(
    project: &BasisProject, stop_file: int, stop_entry: int, file: int, entry: int,
) -> bool {
    forall|f: int, e: int| #[trigger] basis_at(project, f, e) && before(f, e, stop_file, stop_entry)
        ==> f == file && e == entry
}

spec fn basis_prefix(project: &BasisProject, file: int, entry: int, seen: Option<BasisSite>) -> bool {
    match seen {
        None => only_before(project, file, entry, -1, -1),
        Some(site) => basis_location(project, site._file as int, site._entry as int, site.location)
            && before(site._file as int, site._entry as int, file, entry)
            && only_before(project, file, entry, site._file as int, site._entry as int),
    }
}

/// 回路ソースが一件もないか、基底の指定が全ソースで一件だけであることを表す。
spec fn whole_basis_valid(project: &BasisProject) -> bool {
    let end = project.sources_model().len() as int;
    !has_circuit_before(project, end) || exists|file: int, entry: int| #[trigger] basis_at(project, file, entry)
        && only_before(project, end, 0, file, entry)
}

/// 基底の位置または診断が、厳格索引にある指定の件数と出現順に対応することを表す。
spec fn whole_basis_result(
    project: &BasisProject, result: Result<Option<LocatedName>, CircuitBasisError>,
) -> bool {
    let end = project.sources_model().len() as int;
    match result {
        Ok(None) => !has_circuit_before(project, end),
        Ok(Some(location)) => exists|file: int, entry: int| #[trigger] basis_location(project, file, entry, location)
            && only_before(project, end, 0, file, entry),
        Err(CircuitBasisError::Missing) => has_circuit_before(project, end) && only_before(project, end, 0, -1, -1),
        Err(CircuitBasisError::Duplicate { later, first }) =>
            exists|f: int, e: int, nf: int, ne: int|
                #![trigger basis_location(project, f, e, first), basis_location(project, nf, ne, later)]
                basis_location(project, f, e, first) && basis_location(project, nf, ne, later)
                && before(f, e, nf, ne) && only_before(project, nf, ne, f, e),
    }
}

proof fn next_entry(
    project: &BasisProject, file: int, entry: int, old: Option<BasisSite>, new: Option<BasisSite>,
)
    requires
        basis_prefix(project, file, entry, old),
        match new {
            Some(site) if old is None => basis_location(project, file, entry, site.location)
                && site._file == file && site._entry == entry,
            _ => new == old && !basis_at(project, file, entry),
        },
    ensures basis_prefix(project, file, entry + 1, new),
{
    assert forall|f: int, e: int| #[trigger] basis_at(project, f, e) && before(f, e, file, entry + 1)
        implies before(f, e, file, entry) || (f == file && e == entry) by {};
}

proof fn next_file(project: &BasisProject, file: int, entry: int, seen: Option<BasisSite>)
    requires
        0 <= file < project.sources_model().len(),
        entry == project.entry_count(file as int),
        basis_prefix(project, file, entry, seen),
    ensures basis_prefix(project, file + 1, 0, seen),
{
    assert forall|f: int, e: int| #[trigger] basis_at(project, f, e) && before(f, e, file + 1, 0)
        implies before(f, e, file, entry) by {};
}

/// 回路ソースが一件もないか、基底指定が全ソースで一件だけであることを表す。
pub closed spec fn circuit_basis_valid(project: &CircuitProject) -> bool {
    whole_basis_valid(&BasisProject::Circuit(project))
}

/// 検査結果が回路ソース中の基底の件数と位置に対応することを表す。
pub closed spec fn basis_result_evidence(
    project: &CircuitProject, result: Result<Option<LocatedName>, CircuitBasisError>,
) -> bool {
    whole_basis_result(&BasisProject::Circuit(project), result)
}

/// 混在ソース集合に回路がなければ成立し、回路があれば基底指定が一件のときだけ成立する。
pub closed spec fn mixed_circuit_basis_valid(project: &ParsedProjectSources) -> bool {
    whole_basis_valid(&BasisProject::Mixed(project))
}

/// 関数型ソースを読み飛ばし、残る基底の位置か最初の二箇所の診断を返すことを表す。
pub closed spec fn mixed_basis_result_evidence(
    project: &ParsedProjectSources, result: Result<Option<LocatedName>, CircuitBasisError>,
) -> bool {
    whole_basis_result(&BasisProject::Mixed(project), result)
}

/// 正規化と構文解析を終えた回路ソース集合の基底を検査する。
///
/// 指定が一件であれば `nor` の範囲を返す。回路ソースが一件もなければ `Ok(None)` を返す。
/// 複数の入力が同じファイルに正規化された場合は、収集済みのファイルを一度検査する。
///
/// # Errors
///
/// 回路ソースがあり、指定がなければ欠落を返す。複数あればソース集合の順序で最初の二件を示す。
pub fn validate_circuit_basis<'p, 'a>(project: &'p CircuitProject<'a>)
    -> (result: Result<Option<LocatedName<'p, 'a>>, CircuitBasisError<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures
        result.is_ok() <==> circuit_basis_valid(project),
        basis_result_evidence(project, result),
{
    validate_basis(&BasisProject::Circuit(project))
}

/// 関数型ソースと回路ソースが混在するプロジェクトの基底を検査する。
///
/// `.ncg2` の厳格索引を調べる。`.ncg2m` しかない場合は `Ok(None)` を返す。
/// 同じファイルに正規化された複数の入力は一件として扱う。
///
/// # Errors
///
/// 回路ソースがあり、指定がなければ欠落を返す。複数あればソース集合の順序で最初の二件を示す。
pub fn validate_mixed_circuit_basis<'p, 'a>(project: &'p ParsedProjectSources<'a>)
    -> (result: Result<Option<LocatedName<'p, 'a>>, CircuitBasisError<'p, 'a>>)
    requires project.has_source_indexes(),
    ensures
        result.is_ok() <==> mixed_circuit_basis_valid(project),
        mixed_basis_result_evidence(project, result),
{
    validate_basis(&BasisProject::Mixed(project))
}

fn validate_basis<'p, 'a>(project: &BasisProject<'p, 'a>)
    -> (result: Result<Option<LocatedName<'p, 'a>>, CircuitBasisError<'p, 'a>>)
    requires project.valid(),
    ensures result.is_ok() <==> whole_basis_valid(project), whole_basis_result(project, result),
{
    let sources = project.sources();
    let mut seen: Option<BasisSite> = None;
    let mut has_circuit = false;
    let mut file = 0;
    while file < sources.len()
        invariant
            sources@ == project.sources_model(), project.valid(),
            file <= sources@.len(),
            has_circuit == has_circuit_before(project, file as int),
            basis_prefix(project, file as int, 0, seen),
        decreases sources@.len() - file,
    {
        let circuit = project.circuit(file);
        let mut entry = 0;
        if let Some(parsed) = circuit {
            let source = &sources[file];
            let entries = &parsed.syntax.entries;
            while entry < entries.len()
                invariant
                    file < sources@.len(),
                    sources@ == project.sources_model(),
                    *source == project.sources_model()[file as int],
                    project.circuit_model(file as int) == Some(*parsed),
                    parsed_circuit_matches(*source, *parsed),
                    entries@ == parsed.syntax.entries@,
                    entry <= entries@.len(),
                    basis_prefix(project, file as int, entry as int, seen),
                decreases entries@.len() - entry,
            {
                let root = &entries[entry];
                let ghost prior = seen;
                if matches!(root.head, Head::Using) {
                    let forms = &parsed.syntax.forms;
                    proof {
                        parsed_index_evidence(*source, *parsed);
                        basis_entry_evidence(source.text, forms@, entries@, entry as int);
                    }
                    let _form_count = forms.len();
                    assert(root.form + 2 < _form_count);
                    let (_, span) = read_indexed_atom(source.text, forms, root.form + 2);
                    let location = LocatedName { source, span };
                    proof { located_name_evidence(location); }
                    assert(basis_location(project, file as int, entry as int, location));
                    if let Some(first) = seen {
                        let result = Err(CircuitBasisError::Duplicate { first: first.location, later: location });
                        assert(whole_basis_result(project, result));
                        return result;
                    }
                    seen = Some(BasisSite { _file: file, _entry: entry, location });
                }
                proof { next_entry(project, file as int, entry as int, prior, seen); }
                entry += 1;
            }
        }
        proof {
            next_file(project, file as int, entry as int, seen);
            extend_circuit_prefix(project, file as int);
        }
        has_circuit = has_circuit || circuit.is_some();
        file += 1;
    }
    match seen {
        Some(site) => Ok(Some(site.location)),
        None if !has_circuit => Ok(None),
        None => Err(CircuitBasisError::Missing),
    }
}

} // verus!
