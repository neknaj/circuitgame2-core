//! ラッチと RAM の宣言にある幅を数値化する。

use super::circuits::read_indexed_atom;
use super::widths::read_explicit_width;
use super::{CircuitProject, DeclaredPortType, LocatedName, PortWidthError};
#[cfg(verus_only)]
use super::{circuits::{parsed_circuit_matches, parsed_index_evidence}, ProjectSource};
#[cfg(verus_only)]
use super::widths::{natural_width_value, width_number_result};
use crate::syntax::circuit::{FieldTypeSite, StorageSites, storage_sites};
#[cfg(verus_only)]
use crate::syntax::circuit::{Head, storage_site_evidence, storage_sites_match};
#[cfg(verus_only)]
use crate::syntax::{Form, form_span};
use vstd::prelude::*;

verus! {

/// 自然数で指定された幅を検査した状態素子の宣言。
#[derive(Debug)]
pub enum StorageDeclaration<'p, 'a> {
    /// ラッチが保持するビット列。
    Latch {
        /// 入力と出力で共通の幅。
        width: u64,
        /// 幅の字句と、そのファイルおよび文書版。
        annotation: LocatedName<'p, 'a>,
    },
    /// RAM のアドレスとデータの指定。
    Memory {
        /// アドレス入力のビット幅。
        address: u64,
        /// アドレス幅の字句と、そのファイルおよび文書版。
        address_annotation: LocatedName<'p, 'a>,
        /// データ入力と出力で共通の型。構造体名の解決は後段で行う。
        data: DeclaredPortType,
        /// データ幅または型名の字句と、そのファイルおよび文書版。
        data_annotation: LocatedName<'p, 'a>,
    },
}

spec fn explicit_width(
    source: &ProjectSource, forms: Seq<Form>, atom: usize, limit: u64,
) -> Result<u64, super::PortWidthErrorKind> {
    width_number_result(natural_width_value(source.text, forms[atom as int]), limit)
}

spec fn annotation_at(source: &ProjectSource, forms: Seq<Form>, atom: usize, annotation: LocatedName) -> bool {
    *annotation.source == *source && annotation.span == form_span(forms[atom as int])
}

spec fn storage_width_error(source: &ProjectSource, forms: Seq<Form>, atom: usize, limit: u64, error: PortWidthError) -> bool {
    *error.source == *source && error.span == form_span(forms[atom as int])
        && explicit_width(source, forms, atom, limit) == Err(error.kind)
}

spec fn storage_numbers_match(
    source: &ProjectSource, forms: Seq<Form>, sites: StorageSites, limit: u64,
    result: Result<Option<StorageDeclaration>, PortWidthError>,
) -> bool {
    match sites {
        StorageSites::Latch { width: atom } => match result {
            Ok(Some(StorageDeclaration::Latch { width, annotation })) =>
                explicit_width(source, forms, atom, limit) == Ok(width)
                    && annotation_at(source, forms, atom, annotation),
            Err(error) => storage_width_error(source, forms, atom, limit, error),
            _ => false,
        },
        StorageSites::Memory { address: atom, data: data_site } => match result {
            Ok(Some(StorageDeclaration::Memory { address, address_annotation, data, data_annotation })) => {
                &&& explicit_width(source, forms, atom, limit) == Ok(address)
                &&& annotation_at(source, forms, atom, address_annotation)
                &&& match data_site {
                    FieldTypeSite::Bits { width } => data is Bits
                        && explicit_width(source, forms, width, limit) == Ok(data->Bits_0)
                        && annotation_at(source, forms, width, data_annotation),
                    FieldTypeSite::Named { form } => data == DeclaredPortType::Named { form }
                        && annotation_at(source, forms, form, data_annotation),
                }
            },
            Err(error) => storage_width_error(source, forms, atom, limit, error)
                || (explicit_width(source, forms, atom, limit).is_ok()
                    && (data_site matches FieldTypeSite::Bits { width }
                    && storage_width_error(source, forms, width, limit, error))),
            _ => false,
        },
    }
}

spec fn storage_entry(project: &CircuitProject, file: usize, entry: usize) -> bool {
    let circuits = project.circuits_model();
    &&& file < circuits.len()
    &&& entry < circuits[file as int].syntax.entries@.len()
    &&& {
        let head = circuits[file as int].syntax.entries@[entry as int].head;
        head is Latch || head is Memory
    }
}

/// 幅の数値化結果または最初の幅違反を、元の宣言と上限に対応付ける。
pub closed spec fn storage_declaration_result(
    project: &CircuitProject, file: usize, entry: usize, limit: u64,
    result: Result<Option<StorageDeclaration>, PortWidthError>,
) -> bool {
    if storage_entry(project, file, entry) {
        let source = &project.sources_model()[file as int];
        let syntax = &project.circuits_model()[file as int].syntax;
        file < project.sources_model().len()
            && exists|sites: StorageSites| #[trigger] storage_sites_match(source.text, syntax, entry as int, Some(sites))
                && storage_numbers_match(source, syntax.forms@, sites, limit, result)
    } else {
        result == Ok(None)
    }
}

/// ラッチまたは RAM に明記された幅を検査する。
///
/// `file` はソース一覧、`entry` はそのファイルの厳格索引の添字。範囲外や他の宣言は
/// `Ok(None)` を返す。RAM の型名は名前解決用に保持する。RAM の容量は後段で検査する。
///
/// # Errors
///
/// 幅がゼロ、`u64` の表現範囲外、または `limit` を超える場合に、該当する字句の範囲を返す。
/// RAM ではアドレス幅、データ幅の順に検査し、最初の違反を返す。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::project::{
///     SourceSnapshot, StorageDeclaration, check_storage_declaration, parse_circuit_project,
/// };
///
/// let text = "(latch reg (width 8)) (memory ram (address 4) (data Word))";
/// let project = parse_circuit_project(&[SourceSnapshot { path: "vm.ncg2", revision: 1, text }]).unwrap();
/// let latch = check_storage_declaration(&project, 0, 0, 16).unwrap().unwrap();
/// assert!(matches!(latch, StorageDeclaration::Latch { width: 8, .. }));
/// let ram = check_storage_declaration(&project, 0, 1, 16).unwrap().unwrap();
/// let StorageDeclaration::Memory { address, data_annotation, .. } = ram else { panic!() };
/// assert_eq!(address, 4);
/// assert_eq!(&text[data_annotation.span], "Word");
/// ```
pub fn check_storage_declaration<'p, 'a>(
    project: &'p CircuitProject<'a>, file: usize, entry: usize, limit: u64,
) -> (result: Result<Option<StorageDeclaration<'p, 'a>>, PortWidthError<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures storage_declaration_result(project, file, entry, limit, result),
{
    let circuits = project.circuits();
    if file >= circuits.len() {
        return Ok(None);
    }
    let source = &project.sources()[file];
    let parsed = &circuits[file];
    proof {
        assert(parsed_circuit_matches(*source, *parsed));
        parsed_index_evidence(*source, *parsed);
    }
    let Some(sites) = storage_sites(source.text, &parsed.syntax, entry) else {
        return Ok(None);
    };
    proof { storage_site_evidence(source.text, &parsed.syntax, entry as int, sites); }
    let forms = parsed.syntax.forms.as_slice();
    let declaration = match sites {
        StorageSites::Latch { width } => {
            let (width, span) = read_explicit_width(source, forms, width, limit)?;
            StorageDeclaration::Latch { width, annotation: LocatedName { source, span } }
        },
        StorageSites::Memory { address, data } => {
            let (address, span) = read_explicit_width(source, forms, address, limit)?;
            let address_annotation = LocatedName { source, span };
            let (data, span) = match data {
                FieldTypeSite::Bits { width } => {
                    let (width, span) = read_explicit_width(source, forms, width, limit)?;
                    (DeclaredPortType::Bits(width), span)
                },
                FieldTypeSite::Named { form } => {
                    let (_, span) = read_indexed_atom(source.text, forms, form);
                    (DeclaredPortType::Named { form }, span)
                },
            };
            StorageDeclaration::Memory { address, address_annotation, data, data_annotation: LocatedName { source, span } }
        },
    };
    Ok(Some(declaration))
}

} // verus!
