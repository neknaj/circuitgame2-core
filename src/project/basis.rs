//! 構文解析を終えた回路ソース集合に共通の基底を検査する。

#[cfg(verus_only)]
use super::circuits::parsed_index_evidence;
use super::circuits::read_indexed_atom;
#[cfg(verus_only)]
use super::declarations::located_name_evidence;
#[cfg(verus_only)]
use super::location_in_source;
use super::{CircuitProject, LocatedName};
use crate::syntax::circuit::Head;
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

spec fn basis_at(project: &CircuitProject, file: int, entry: int) -> bool {
    let circuits = project.circuits_model();
    &&& 0 <= file < circuits.len()
    &&& 0 <= entry < circuits[file].syntax.entries@.len()
    &&& circuits[file].syntax.entries@[entry].head is Using
}

spec fn before(file: int, entry: int, stop_file: int, stop_entry: int) -> bool {
    file < stop_file || (file == stop_file && entry < stop_entry)
}

spec fn basis_location(project: &CircuitProject, file: int, entry: int, location: LocatedName) -> bool {
    &&& basis_at(project, file, entry)
    &&& file < project.sources_model().len()
    &&& *location.source == project.sources_model()[file]
    &&& location_in_source(location)
    &&& {
        let parsed = project.circuits_model()[file];
        let arg = parsed.syntax.entries@[entry].form + 2;
        &&& parsed.syntax.entries@[entry].namespace is None
        &&& arg < parsed.syntax.forms@.len()
        &&& location.span == form_span(parsed.syntax.forms@[arg])
        &&& location.source.text.spec_bytes()[location.span.start as int..location.span.end as int] == "nor".spec_bytes()
    }
}

spec fn only_before(
    project: &CircuitProject, stop_file: int, stop_entry: int, file: int, entry: int,
) -> bool {
    forall|f: int, e: int| #[trigger] basis_at(project, f, e) && before(f, e, stop_file, stop_entry)
        ==> f == file && e == entry
}

spec fn basis_prefix(project: &CircuitProject, file: int, entry: int, seen: Option<BasisSite>) -> bool {
    match seen {
        None => only_before(project, file, entry, -1, -1),
        Some(site) => basis_location(project, site._file as int, site._entry as int, site.location)
            && before(site._file as int, site._entry as int, file, entry)
            && only_before(project, file, entry, site._file as int, site._entry as int),
    }
}

/// 回路ソースが一件もないか、基底の指定が全ソースで一件だけであることを表す。
pub closed spec fn circuit_basis_valid(project: &CircuitProject) -> bool {
    let end = project.circuits_model().len() as int;
    end == 0 || exists|file: int, entry: int| #[trigger] basis_at(project, file, entry)
        && only_before(project, end, 0, file, entry)
}

/// 基底の位置または診断が、厳格索引にある指定の件数と出現順に対応することを表す。
pub closed spec fn basis_result_evidence(
    project: &CircuitProject, result: Result<Option<LocatedName>, CircuitBasisError>,
) -> bool {
    let end = project.circuits_model().len() as int;
    match result {
        Ok(None) => end == 0,
        Ok(Some(location)) => exists|file: int, entry: int| #[trigger] basis_location(project, file, entry, location)
            && only_before(project, end, 0, file, entry),
        Err(CircuitBasisError::Missing) => end > 0 && only_before(project, end, 0, -1, -1),
        Err(CircuitBasisError::Duplicate { later, first }) =>
            exists|f: int, e: int, nf: int, ne: int|
                #![trigger basis_location(project, f, e, first), basis_location(project, nf, ne, later)]
                basis_location(project, f, e, first) && basis_location(project, nf, ne, later)
                && before(f, e, nf, ne) && only_before(project, nf, ne, f, e),
    }
}

proof fn next_entry(
    project: &CircuitProject, file: int, entry: int, old: Option<BasisSite>, new: Option<BasisSite>,
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

proof fn next_file(project: &CircuitProject, file: int, entry: int, seen: Option<BasisSite>)
    requires
        0 <= file < project.circuits_model().len(),
        entry == project.circuits_model()[file].syntax.entries@.len(),
        basis_prefix(project, file, entry, seen),
    ensures basis_prefix(project, file + 1, 0, seen),
{
    assert forall|f: int, e: int| #[trigger] basis_at(project, f, e) && before(f, e, file + 1, 0)
        implies before(f, e, file, entry) by {};
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
    let circuits = project.circuits();
    let sources = project.sources();
    let mut seen: Option<BasisSite> = None;
    let mut file = 0;
    let mut index = 0;
    while file < circuits.len()
        invariant
            circuits@ == project.circuits_model(), sources@ == project.sources_model(),
            project.has_parsed_sources(),
            file <= circuits@.len(),
            file < circuits@.len() ==> index <= circuits@[file as int].syntax.entries@.len(),
            file == circuits@.len() ==> index == 0,
            basis_prefix(project, file as int, index as int, seen),
        decreases circuits@.len() - file,
            if file < circuits@.len() { circuits@[file as int].syntax.entries@.len() - index } else { 0 },
    {
        let parsed = &circuits[file];
        let entries = &parsed.syntax.entries;
        if index == entries.len() {
            proof { next_file(project, file as int, index as int, seen); }
            file += 1;
            index = 0;
            continue;
        }
        let root = &entries[index];
        let ghost prior = seen;
        if matches!(root.head, Head::Using) {
            let source = &sources[file];
            let forms = &parsed.syntax.forms;
            proof {
                parsed_index_evidence(*source, *parsed);
                basis_entry_evidence(source.text, forms@, entries@, index as int);
            }
            let _form_count = forms.len();
            assert(root.form + 2 < _form_count);
            let (_, span) = read_indexed_atom(source.text, forms, root.form + 2);
            let location = LocatedName { source, span };
            proof { located_name_evidence(location); }
            assert(basis_location(project, file as int, index as int, location));
            if let Some(first) = seen {
                let result = Err(CircuitBasisError::Duplicate { first: first.location, later: location });
                assert(basis_result_evidence(project, result));
                return result;
            }
            seen = Some(BasisSite { _file: file, _entry: index, location });
        }
        proof { next_entry(project, file as int, index as int, prior, seen); }
        index += 1;
    }
    match seen {
        Some(site) => Ok(Some(site.location)),
        None if circuits.is_empty() => Ok(None),
        None => Err(CircuitBasisError::Missing),
    }
}

} // verus!
