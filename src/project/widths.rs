//! 構文解析済みのポートから、回路の型検査に使う幅と型参照を取り出す。

use super::circuits::read_indexed_atom;
#[cfg(verus_only)]
use super::circuits::{parsed_circuit_matches, parsed_index_evidence};
use super::{CircuitProject, ProjectSource};
use crate::syntax::circuit::{CircuitForms, PortSite, PortTypeSite, RoutinePorts, routine_ports};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    RoutineArity, port_site_evidence, routine_arity_matches, routine_arity_port_counts,
    routine_ports_agree, routine_ports_availability, routine_ports_match,
};
#[cfg(verus_only)]
use crate::syntax::{
    AtomKind, bare_atom_kind, decimal_natural_value, form_span, form_spans_valid,
    natural_atom_has_value,
};
use crate::syntax::{NaturalRangeError, read_natural_u64};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// ポートが指定する型。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeclaredPortType {
    /// 指定に従って範囲を検査した正のビット幅。裸のポート名では 1。
    Bits(u64),
    /// 解決すべき型への参照。
    Named {
        /// 元の構文木で型名の字句を指す添字。
        form: usize,
    },
}

/// ポートの構文位置と、その宣言が指定する型。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CheckedPort {
    /// 厳格な構文木を参照するポートの位置。
    pub site: PortSite,
    /// 数値化した幅または型参照。
    pub ty: DeclaredPortType,
}

/// 数値で指定したビット幅を検査した署名。
#[derive(Debug, Eq, PartialEq)]
pub struct RoutinePortWidths {
    /// 宣言順の入力ポート。
    pub inputs: Vec<CheckedPort>,
    /// 宣言順の出力ポート。
    pub outputs: Vec<CheckedPort>,
}

/// ポートのビット幅が使えない理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PortWidthErrorKind {
    /// ビット幅は正でなければならない。
    Zero,
    /// 数字列が表す値が `u64::MAX` を超えている。
    NumericRange,
    /// 表現できる幅が呼び出し側の資源上限を超えている。
    LimitExceeded {
        /// 宣言された幅。裸のポート名では 1。
        width: u64,
        /// 呼び出し側が指定した幅の上限。
        limit: u64,
    },
}

/// ポートのビット幅に関する診断。
#[derive(Debug)]
pub struct PortWidthError<'p, 'a> {
    /// ファイル識別子と文書バージョンを持つソース。
    pub source: &'p ProjectSource<'a>,
    /// 幅を指定した自然数の UTF-8 半開バイト範囲。型を省略した場合はポート名の範囲。
    pub span: Range<usize>,
    /// 幅の違反の種別。
    pub kind: PortWidthErrorKind,
}

pub(super) open spec fn natural_width_value(source: &str, form: crate::syntax::Form) -> int {
    let span = form_span(form);
    decimal_natural_value(source.spec_bytes()[span.start as int..span.end as int])->Some_0
}

pub(super) open spec fn width_number_result(value: int, max_width: u64) -> Result<u64, PortWidthErrorKind> {
    if value > u64::MAX {
        Err(PortWidthErrorKind::NumericRange)
    } else if value <= 0 {
        Err(PortWidthErrorKind::Zero)
    } else if value > max_width {
        Err(PortWidthErrorKind::LimitExceeded { width: value as u64, limit: max_width })
    } else {
        Ok(value as u64)
    }
}

// 明示したポート幅と状態素子の幅は同じ規則で検査する。
pub(super) fn read_explicit_width<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[crate::syntax::Form], atom: usize, max_width: u64,
) -> (result: Result<(u64, Range<usize>), PortWidthError<'p, 'a>>)
    requires
        atom < forms@.len(), forms@[atom as int] is Atom && forms@[atom as int]->Atom_kind is Natural,
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures ({
        let value = natural_width_value(source.text, forms@[atom as int]);
        let span = form_span(forms@[atom as int]);
        &&& value >= 0
        &&& match result {
            Ok((width, found)) => width_number_result(value, max_width) == Ok(width) && found == span
                && super::location_in_source(super::LocatedName { source, span: found }),
            Err(error) => width_number_result(value, max_width) == Err(error.kind)
                && *error.source == *source && error.span == span,
        }
    }),
{
    let (word, span) = read_indexed_atom(source.text, forms, atom);
    proof {
        natural_atom_has_value(word.spec_bytes());
        super::declarations::located_name_evidence(super::LocatedName { source, span });
    }
    let width = match read_natural_u64(word) {
        Ok(width) => width,
        Err(NaturalRangeError::OutOfRange) =>
            return Err(PortWidthError { source, span, kind: PortWidthErrorKind::NumericRange }),
        Err(NaturalRangeError::InvalidDigits) => {
            proof { assert(false); }
            unreachable!()
        },
    };
    if width == 0 {
        Err(PortWidthError { source, span, kind: PortWidthErrorKind::Zero })
    } else if width > max_width {
        let kind = PortWidthErrorKind::LimitExceeded { width, limit: max_width };
        Err(PortWidthError { source, span, kind })
    } else {
        Ok((width, span))
    }
}

spec fn port_spec_value(source: &str, syntax: &CircuitForms, site: PortSite) -> int {
    match site.ty {
        PortTypeSite::ImplicitBit => 1,
        PortTypeSite::Bits { width } => natural_width_value(source, syntax.forms@[width as int]),
        PortTypeSite::Named { .. } => 0,
    }
}

spec fn supported_width(value: int, max_width: u64) -> bool {
    0 < value <= max_width
}

spec fn port_ok(source: &str, syntax: &CircuitForms, site: PortSite, max_width: u64) -> bool {
    site.ty is Named || supported_width(port_spec_value(source, syntax, site), max_width)
}

spec fn port_matches(source: &str, syntax: &CircuitForms, site: PortSite, max_width: u64, checked: CheckedPort) -> bool {
    &&& checked.site == site
    &&& match site.ty {
        PortTypeSite::Named { form } => checked.ty == DeclaredPortType::Named { form },
        _ => {
            let value = port_spec_value(source, syntax, site);
            supported_width(value, max_width) && checked.ty == DeclaredPortType::Bits(value as u64)
        },
    }
}

spec fn that_width_failed(
    source: &ProjectSource, syntax: &CircuitForms, site: PortSite, max_width: u64, error: PortWidthError,
) -> bool {
    let value = port_spec_value(source.text, syntax, site);
    let atom = match site.ty { PortTypeSite::Bits { width } => width, _ => site.name };
    &&& *error.source == *source && !(site.ty is Named)
    &&& error.span == form_span(syntax.forms@[atom as int])
    &&& match error.kind {
        PortWidthErrorKind::Zero => value == 0,
        PortWidthErrorKind::NumericRange => value > u64::MAX,
        PortWidthErrorKind::LimitExceeded { width, limit } =>
            value == width && width > limit && limit == max_width,
    }
}

spec fn checked_before(
    source: &str, syntax: &CircuitForms, ports: Seq<PortSite>, checked: Seq<CheckedPort>, max_width: u64,
) -> bool {
    &&& checked.len() <= ports.len()
    &&& forall|i: int| 0 <= i < checked.len() ==>
        port_matches(source, syntax, ports[i], max_width, #[trigger] checked[i])
}

spec fn error_in_ports(
    source: &ProjectSource, syntax: &CircuitForms, ports: Seq<PortSite>, max_width: u64, error: PortWidthError,
) -> bool {
    exists|i: int| 0 <= i < ports.len()
        && #[trigger] that_width_failed(source, syntax, ports[i], max_width, error)
        && forall|prior: int| 0 <= prior < i ==> port_ok(source.text, syntax, #[trigger] ports[prior], max_width)
}

spec fn all_ports_ok(source: &str, syntax: &CircuitForms, ports: Seq<PortSite>, max_width: u64) -> bool {
    forall|i: int| 0 <= i < ports.len() ==> port_ok(source, syntax, #[trigger] ports[i], max_width)
}

/// 検査結果が元の署名と幅上限に対応することを表す。
pub closed spec fn routine_port_widths_evidence(
    project: &CircuitProject, file: int, entry: int, max_width: u64,
    result: Result<Option<RoutinePortWidths>, PortWidthError>,
) -> bool {
    let circuits = project.circuits_model();
    let sources = project.sources_model();
    if 0 <= file < circuits.len() {
        let syntax = &circuits[file].syntax;
        let source = &sources[file];
        match result {
            Ok(None) => routine_ports_match(source.text, syntax, entry, None),
            _ => 0 <= entry < syntax.entries@.len()
                && exists|ports: RoutinePorts| #[trigger] routine_ports_match(source.text, syntax, entry, Some(ports))
                && match result {
                    Ok(Some(widths)) =>
                        widths.inputs@.len() == ports.inputs@.len()
                            && widths.outputs@.len() == ports.outputs@.len()
                            && checked_before(source.text, syntax, ports.inputs@, widths.inputs@, max_width)
                            && checked_before(source.text, syntax, ports.outputs@, widths.outputs@, max_width),
                    Err(error) => error_in_ports(source, syntax, ports.inputs@, max_width, error)
                        || (all_ports_ok(source.text, syntax, ports.inputs@, max_width)
                            && error_in_ports(source, syntax, ports.outputs@, max_width, error)),
                    Ok(None) => false,
                },
        }
    } else {
        result == Ok(None)
    }
}

proof fn checked_ports_agree(
    source: &str, syntax: &CircuitForms, ports: Seq<PortSite>, max_width: u64,
    left: Seq<CheckedPort>, right: Seq<CheckedPort>,
)
    requires
        left.len() == right.len(),
        checked_before(source, syntax, ports, left, max_width),
        checked_before(source, syntax, ports, right, max_width),
    ensures left == right,
{
    assert forall|i: int| 0 <= i < left.len() implies (#[trigger] left[i]) == (#[trigger] right[i]) by {
        assert(port_matches(source, syntax, ports[i], max_width, left[i]));
        assert(port_matches(source, syntax, ports[i], max_width, right[i]));
    };
    assert(left =~= right);
}

/// 同じ宣言と幅上限で検査したポートは、元の添字と幅または型参照が一致する。
pub(super) proof fn routine_port_widths_agree(
    project: &CircuitProject, file: int, entry: int, max_width: u64,
    left: RoutinePortWidths, right: RoutinePortWidths,
)
    requires
        routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(left))),
        routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(right))),
    ensures left.inputs@ == right.inputs@, left.outputs@ == right.outputs@,
{
    let source = &project.sources_model()[file];
    let syntax = &project.circuits_model()[file].syntax;
    let a = choose|ports: RoutinePorts| #[trigger] routine_ports_match(source.text, syntax, entry, Some(ports))
        && left.inputs@.len() == ports.inputs@.len() && left.outputs@.len() == ports.outputs@.len()
        && checked_before(source.text, syntax, ports.inputs@, left.inputs@, max_width)
        && checked_before(source.text, syntax, ports.outputs@, left.outputs@, max_width);
    let b = choose|ports: RoutinePorts| #[trigger] routine_ports_match(source.text, syntax, entry, Some(ports))
        && right.inputs@.len() == ports.inputs@.len() && right.outputs@.len() == ports.outputs@.len()
        && checked_before(source.text, syntax, ports.inputs@, right.inputs@, max_width)
        && checked_before(source.text, syntax, ports.outputs@, right.outputs@, max_width);
    routine_ports_agree(source.text, syntax, entry, a, b);
    checked_ports_agree(source.text, syntax, a.inputs@, max_width, left.inputs@, right.inputs@);
    checked_ports_agree(source.text, syntax, a.outputs@, max_width, left.outputs@, right.outputs@);
}

proof fn checked_ports_exclude_width_error(
    source: &ProjectSource, syntax: &CircuitForms, ports: Seq<PortSite>, max_width: u64,
    checked: Seq<CheckedPort>, error: PortWidthError,
)
    requires
        checked.len() == ports.len(),
        checked_before(source.text, syntax, ports, checked, max_width),
    ensures !error_in_ports(source, syntax, ports, max_width, error),
{
    if error_in_ports(source, syntax, ports, max_width, error) {
        let index = choose|i: int| 0 <= i < ports.len()
            && #[trigger] that_width_failed(source, syntax, ports[i], max_width, error)
            && forall|prior: int| 0 <= prior < i ==> port_ok(source.text, syntax, #[trigger] ports[prior], max_width);
        assert(port_matches(source.text, syntax, ports[index], max_width, checked[index]));
        assert(port_ok(source.text, syntax, ports[index], max_width));
        assert(false);
    }
}

/// 同じ宣言と幅上限で幅検査に成功したとき、対象外や幅の診断の根拠は成立しない。
pub(super) proof fn routine_widths_success_excludes_other(
    project: &CircuitProject, file: int, entry: int, max_width: u64,
    success: RoutinePortWidths, other: Result<Option<RoutinePortWidths>, PortWidthError>,
)
    requires
        routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(success))),
        routine_port_widths_evidence(project, file, entry, max_width, other),
    ensures other is Ok && other->Ok_0 is Some,
{
    let source = &project.sources_model()[file];
    let syntax = &project.circuits_model()[file].syntax;
    let ports = choose|ports: RoutinePorts| #[trigger] routine_ports_match(source.text, syntax, entry, Some(ports))
        && success.inputs@.len() == ports.inputs@.len() && success.outputs@.len() == ports.outputs@.len()
        && checked_before(source.text, syntax, ports.inputs@, success.inputs@, max_width)
        && checked_before(source.text, syntax, ports.outputs@, success.outputs@, max_width);
    match other {
        Ok(Some(_)) => {},
        Ok(None) => {
            routine_ports_availability(source.text, syntax, entry, Some(ports));
            routine_ports_availability(source.text, syntax, entry, None);
        },
        Err(error) => {
            let failing = choose|failing: RoutinePorts|
                #[trigger] routine_ports_match(source.text, syntax, entry, Some(failing))
                && (error_in_ports(source, syntax, failing.inputs@, max_width, error)
                    || (all_ports_ok(source.text, syntax, failing.inputs@, max_width)
                        && error_in_ports(source, syntax, failing.outputs@, max_width, error)));
            routine_ports_agree(source.text, syntax, entry, ports, failing);
            checked_ports_exclude_width_error(source, syntax, ports.inputs@, max_width, success.inputs@, error);
            checked_ports_exclude_width_error(source, syntax, ports.outputs@, max_width, success.outputs@, error);
        },
    }
}

pub(super) proof fn checked_width_entry_exists(
    project: &CircuitProject, file: int, entry: int, max_width: u64, widths: RoutinePortWidths,
)
    requires routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(widths))),
    ensures
        0 <= file < project.circuits_model().len(),
        0 <= entry < project.circuits_model()[file].syntax.entries@.len(),
{
}

pub(super) proof fn checked_width_counts(
    project: &CircuitProject, file: int, entry: int, max_width: u64, widths: RoutinePortWidths, arity: RoutineArity,
)
    requires
        0 <= file < project.circuits_model().len(), file < project.sources_model().len(),
        routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(widths))),
        routine_arity_matches(project.sources_model()[file].text, &project.circuits_model()[file].syntax, entry, Some(arity)),
    ensures widths.inputs@.len() == arity.inputs, widths.outputs@.len() == arity.outputs,
{
    let source = &project.sources_model()[file];
    let syntax = &project.circuits_model()[file].syntax;
    let ports = choose|ports: RoutinePorts| #[trigger] routine_ports_match(source.text, syntax, entry, Some(ports))
        && widths.inputs@.len() == ports.inputs@.len() && widths.outputs@.len() == ports.outputs@.len()
        && checked_before(source.text, syntax, ports.inputs@, widths.inputs@, max_width)
        && checked_before(source.text, syntax, ports.outputs@, widths.outputs@, max_width);
    routine_arity_port_counts(source.text, syntax, entry, arity, ports);
}

pub(super) proof fn width_check_skips_non_routines(
    project: &CircuitProject, file: int, entry: int, max_width: u64,
)
    requires routine_port_widths_evidence(project, file, entry, max_width, Ok(None)),
    ensures 0 <= file < project.circuits_model().len()
        && 0 <= entry < project.circuits_model()[file].syntax.entries@.len()
        ==> !(project.circuits_model()[file].syntax.entries@[entry].head is Func)
            && !(project.circuits_model()[file].syntax.entries@[entry].head is Module),
{
    if 0 <= file < project.circuits_model().len() {
        routine_ports_availability(project.sources_model()[file].text,
            &project.circuits_model()[file].syntax, entry, None);
    }
}

pub(super) proof fn checked_width_sites(
    project: &CircuitProject, file: int, entry: int, max_width: u64, widths: RoutinePortWidths,
)
    requires
        routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(widths))),
    ensures
        0 <= file < project.circuits_model().len(),
        checked_name_sites(project.circuits_model()[file].syntax.forms@, widths.inputs@),
        checked_name_sites(project.circuits_model()[file].syntax.forms@, widths.outputs@),
        forall|i: int| 0 <= i < widths.inputs@.len() ==>
            ((#[trigger] widths.inputs@[i]).ty matches DeclaredPortType::Bits(width) ==> 0 < width <= max_width),
        forall|i: int| 0 <= i < widths.outputs@.len() ==>
            ((#[trigger] widths.outputs@[i]).ty matches DeclaredPortType::Bits(width) ==> 0 < width <= max_width),
{
    assert(0 <= file < project.circuits_model().len());
    let source = &project.sources_model()[file];
    let syntax = &project.circuits_model()[file].syntax;
    let ports = choose|ports: RoutinePorts| #[trigger] routine_ports_match(source.text, syntax, entry, Some(ports))
        && widths.inputs@.len() == ports.inputs@.len() && widths.outputs@.len() == ports.outputs@.len()
        && checked_before(source.text, syntax, ports.inputs@, widths.inputs@, max_width)
        && checked_before(source.text, syntax, ports.outputs@, widths.outputs@, max_width);
    sites_for_direction(source.text, syntax, entry, max_width, ports, true, widths.inputs@);
    sites_for_direction(source.text, syntax, entry, max_width, ports, false, widths.outputs@);
}

proof fn sites_for_direction(
    source: &str, syntax: &CircuitForms, entry: int, max_width: u64,
    ports: RoutinePorts, input: bool, selected: Seq<CheckedPort>,
)
    requires
        routine_ports_match(source, syntax, entry, Some(ports)),
        checked_before(source, syntax, if input { ports.inputs@ } else { ports.outputs@ }, selected, max_width),
    ensures checked_name_sites(syntax.forms@, selected),
{
    assert forall|i: int| 0 <= i < selected.len() implies {
        let site = (#[trigger] selected[i]).site;
        &&& site.name < syntax.forms@.len()
        &&& syntax.forms@[site.name as int] is Atom
        &&& site.ty matches PortTypeSite::Bits { width } ==>
            width < syntax.forms@.len() && syntax.forms@[width as int] is Atom
        &&& site.ty matches PortTypeSite::Named { form } ==>
            form < syntax.forms@.len() && syntax.forms@[form as int] is Atom
                && reference_kind(syntax.forms@[form as int]->Atom_kind)
        &&& match site.ty {
            PortTypeSite::Named { form } => selected[i].ty == DeclaredPortType::Named { form },
            _ => selected[i].ty is Bits,
        }
    } by {
        port_site_evidence(source, syntax, entry, ports, input, i);
    };
}

pub(super) open spec fn reference_kind(kind: AtomKind) -> bool {
    kind is Name || kind is RelativePath || kind is AbsolutePath
}

pub(super) open spec fn checked_name_sites(forms: Seq<crate::syntax::Form>, ports: Seq<CheckedPort>) -> bool {
    forall|i: int| 0 <= i < ports.len() ==> {
        let site = (#[trigger] ports[i]).site;
        &&& site.name < forms.len() && forms[site.name as int] is Atom
        &&& site.ty matches PortTypeSite::Bits { width } ==>
            width < forms.len() && forms[width as int] is Atom
        &&& site.ty matches PortTypeSite::Named { form } ==>
            form < forms.len() && forms[form as int] is Atom
                && reference_kind(forms[form as int]->Atom_kind)
        &&& match site.ty {
            PortTypeSite::Named { form } => ports[i].ty == DeclaredPortType::Named { form },
            _ => ports[i].ty is Bits,
        }
    }
}

fn check_ports<'p, 'a>(
    source: &'p ProjectSource<'a>, syntax: &CircuitForms, _entry: usize, ports: &RoutinePorts,
    input: bool, max_width: u64,
) -> (result: Result<Vec<CheckedPort>, PortWidthError<'p, 'a>>)
    requires
        routine_ports_match(source.text, syntax, _entry as int, Some(*ports)),
        form_spans_valid(source.text, syntax.forms@, source.text.spec_bytes().len() as int),
    ensures ({
        let sites = if input { ports.inputs@ } else { ports.outputs@ };
        match result {
            Ok(checked) => checked@.len() == sites.len() && checked_before(source.text, syntax, sites, checked@, max_width)
                && all_ports_ok(source.text, syntax, sites, max_width),
            Err(error) => error_in_ports(source, syntax, sites, max_width, error),
        }
    }),
{
    let sites = if input { ports.inputs.as_slice() } else { ports.outputs.as_slice() };
    let mut checked: Vec<CheckedPort> = Vec::new();
    let mut i = 0;
    while i < sites.len()
        invariant
            routine_ports_match(source.text, syntax, _entry as int, Some(*ports)),
            form_spans_valid(source.text, syntax.forms@, source.text.spec_bytes().len() as int),
            sites@ == if input { ports.inputs@ } else { ports.outputs@ },
            i == checked@.len() <= sites@.len(),
            checked_before(source.text, syntax, sites@, checked@, max_width),
            forall|at: int| 0 <= at < i ==> port_ok(source.text, syntax, #[trigger] sites@[at], max_width),
        decreases sites@.len() - i,
    {
        let site = sites[i];
        proof { port_site_evidence(source.text, syntax, _entry as int, *ports, input, i as int); }
        let ty = match site.ty {
            PortTypeSite::Named { form } => DeclaredPortType::Named { form },
            PortTypeSite::Bits { width: atom } => {
                match read_explicit_width(source, syntax.forms.as_slice(), atom, max_width) {
                    Ok((width, _)) => DeclaredPortType::Bits(width),
                    Err(error) => {
                        assert(that_width_failed(source, syntax, site, max_width, error));
                        return Err(error);
                    },
                }
            },
            PortTypeSite::ImplicitBit => {
                if max_width == 0 {
                    let (_, span) = read_indexed_atom(source.text, syntax.forms.as_slice(), site.name);
                    let kind = PortWidthErrorKind::LimitExceeded { width: 1, limit: max_width };
                    let error = PortWidthError { source, span, kind };
                    assert(that_width_failed(source, syntax, site, max_width, error));
                    return Err(error);
                }
                DeclaredPortType::Bits(1)
            },
        };
        let port = CheckedPort { site, ty };
        assert(port_matches(source.text, syntax, site, max_width, port));
        checked.push(port);
        i += 1;
    }
    Ok(checked)
}

/// 構文解析済みの `func` または `module` のポート幅を検査する。
///
/// `file` は収集済みソース一覧、`entry` はそのファイルの厳格索引の添字。
/// 存在しない項目や他の種別は `Ok(None)`。型への参照は名前解決用に保持する。
/// `max_width` は呼び出し側の資源上限であり、数値と比較する。配線はここでは割り当てない。
///
/// # Errors
///
/// 入力、出力の順に検査し、幅 0、表現範囲外、資源上限超過のうち最初に確認した違反を返す。
pub fn check_routine_port_widths<'p, 'a>(
    project: &'p CircuitProject<'a>, file: usize, entry: usize, max_width: u64,
) -> (result: Result<Option<RoutinePortWidths>, PortWidthError<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures routine_port_widths_evidence(project, file as int, entry as int, max_width, result),
{
    let circuits = project.circuits();
    if file >= circuits.len() { return Ok(None); }
    let source = &project.sources()[file];
    let parsed = &circuits[file];
    proof {
        assert(parsed_circuit_matches(*source, *parsed));
        parsed_index_evidence(*source, *parsed);
    }
    let Some(ports) = routine_ports(source.text, &parsed.syntax, entry) else { return Ok(None); };
    let ghost sites = ports;
    let inputs = check_ports(source, &parsed.syntax, entry, &ports, true, max_width)?;
    let outputs = check_ports(source, &parsed.syntax, entry, &ports, false, max_width)?;
    assert(routine_ports_match(source.text, &parsed.syntax, entry as int, Some(sites)));
    Ok(Some(RoutinePortWidths { inputs, outputs }))
}

} // verus!
