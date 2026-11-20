//! 構造体の総幅、フィールド幅、オフセットを数値化する。

use super::circuits::read_indexed_atom;
use super::{CircuitProject, ProjectSource};
use crate::syntax::circuit::{CircuitForms, FieldSite, FieldTypeSite, StructureSites, structure_sites};
use crate::syntax::{NaturalRangeError, read_natural_u64};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::circuits::{parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    reference_atom, structure_field_site_evidence, structure_sites_match, structure_width_site_evidence,
};
#[cfg(verus_only)]
use crate::syntax::{AtomKind, Form, decimal_natural_value, form_span, form_spans_valid, natural_atom_has_value};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 構造体フィールドの数値化済みの幅、または未解決の型名。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeclaredFieldType {
    /// ビット列の正の幅。
    Bits(u64),
    /// 型名の字句を指す構文木の添字。
    Named {
        /// 型名の字句を指す添字。
        form: usize,
    },
}

/// 構文位置と数値を対応付けたフィールド。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DeclaredField {
    /// フィールド宣言を構成する字句の位置。
    pub site: FieldSite,
    /// 幅を検査した型指定、または解決する型名。
    pub ty: DeclaredFieldType,
    /// 最下位ビットを起点とするオフセット。
    pub offset: u64,
}

/// 幅とオフセットの数値を検査した構造体宣言。
#[derive(Debug, Eq, PartialEq)]
pub struct StructureDeclaration {
    /// 構造体全体のビット幅。
    pub width: u64,
    /// 宣言順のフィールド。
    pub fields: Vec<DeclaredField>,
}

/// 検査する自然数の役割。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructureNumber {
    /// 構造体全体のビット幅。
    TotalWidth,
    /// ビット列フィールドの幅。
    FieldWidth,
    /// フィールドのオフセット。
    FieldOffset,
}

/// 構造体の幅またはオフセットが使えない理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructureNumberErrorKind {
    /// 自然数が `u64` の上限を超えている。
    NumericRange,
    /// ビット幅が0である。
    ZeroWidth,
    /// ビット幅が呼び出し側の資源上限を超えている。
    WidthLimit {
        /// 宣言された幅。
        width: u64,
        /// 呼び出し側が指定した上限。
        limit: u64,
    },
}

/// 構造体宣言の数値に関する診断。
#[derive(Debug)]
pub struct StructureNumberError<'p, 'a> {
    /// ファイル識別子と文書版を含むソース。
    pub source: &'p ProjectSource<'a>,
    /// 違反した自然数の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 自然数を解釈する箇所。
    pub number: StructureNumber,
    /// 数値を使えない理由。
    pub kind: StructureNumberErrorKind,
}

spec fn number_result(
    source: &str, forms: Seq<Form>, index: usize, number: StructureNumber, width_limit: u64,
) -> Result<u64, StructureNumberErrorKind> {
    let span = form_span(forms[index as int]);
    let value = decimal_natural_value(source.spec_bytes()[span.start as int..span.end as int])->Some_0;
    if value < 0 || value > u64::MAX {
        Err(StructureNumberErrorKind::NumericRange)
    } else if number is FieldOffset {
        Ok(value as u64)
    } else if value == 0 {
        Err(StructureNumberErrorKind::ZeroWidth)
    } else if value > width_limit {
        Err(StructureNumberErrorKind::WidthLimit { width: value as u64, limit: width_limit })
    } else {
        Ok(value as u64)
    }
}

spec fn number_error(
    source: &ProjectSource, forms: Seq<Form>, index: usize, number: StructureNumber, width_limit: u64,
    error: StructureNumberError,
) -> bool {
    &&& error.source == source
    &&& error.span == form_span(forms[index as int])
    &&& error.number == number
    &&& number_result(source.text, forms, index, number, width_limit) == Err(error.kind)
}

fn read_structure_number<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[crate::syntax::Form], index: usize, number: StructureNumber,
    width_limit: u64,
) -> (result: Result<u64, StructureNumberError<'p, 'a>>)
    requires
        index < forms@.len(),
        forms@[index as int] is Atom && forms@[index as int]->Atom_kind is Natural,
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures match result {
        Ok(value) => number_result(source.text, forms@, index, number, width_limit) == Ok(value),
        Err(error) => number_error(source, forms@, index, number, width_limit, error),
    },
{
    let (word, span) = read_indexed_atom(source.text, forms, index);
    proof { natural_atom_has_value(word.spec_bytes()); }
    let value = match read_natural_u64(word) {
        Ok(value) => value,
        Err(NaturalRangeError::OutOfRange) => {
            return Err(StructureNumberError { source, span, number, kind: StructureNumberErrorKind::NumericRange });
        },
        Err(NaturalRangeError::InvalidDigits) => {
            proof { assert(false); }
            unreachable!()
        },
    };
    if !matches!(number, StructureNumber::FieldOffset) {
        if value == 0 {
            return Err(StructureNumberError { source, span, number, kind: StructureNumberErrorKind::ZeroWidth });
        }
        if value > width_limit {
            let kind = StructureNumberErrorKind::WidthLimit { width: value, limit: width_limit };
            return Err(StructureNumberError { source, span, number, kind });
        }
    }
    Ok(value)
}

spec fn field_type(
    source: &str, forms: Seq<Form>, site: FieldSite, limit: u64,
) -> Result<DeclaredFieldType, StructureNumberErrorKind> {
    match site.ty {
        FieldTypeSite::Named { form } => Ok(DeclaredFieldType::Named { form }),
        FieldTypeSite::Bits { width } => match number_result(source, forms, width, StructureNumber::FieldWidth, limit) {
            Ok(width) => Ok(DeclaredFieldType::Bits(width)),
            Err(error) => Err(error),
        },
    }
}

spec fn field_numbers_match(
    source: &str, forms: Seq<Form>, site: FieldSite, limit: u64, field: DeclaredField,
) -> bool {
    &&& field.site == site
    &&& field_type(source, forms, site, limit) == Ok(field.ty)
    &&& number_result(source, forms, site.offset, StructureNumber::FieldOffset, limit) == Ok(field.offset)
}

spec fn field_numbers_valid(source: &str, forms: Seq<Form>, site: FieldSite, limit: u64) -> bool {
    field_type(source, forms, site, limit).is_ok()
        && number_result(source, forms, site.offset, StructureNumber::FieldOffset, limit).is_ok()
}

spec fn field_number_error(
    source: &ProjectSource, forms: Seq<Form>, site: FieldSite, limit: u64, error: StructureNumberError,
) -> bool {
    (site.ty matches FieldTypeSite::Bits { width }
        && number_error(source, forms, width, StructureNumber::FieldWidth, limit, error))
    || (field_type(source.text, forms, site, limit).is_ok()
        && number_error(source, forms, site.offset, StructureNumber::FieldOffset, limit, error))
}

spec fn declaration_numbers_match(
    source: &ProjectSource, forms: Seq<Form>, sites: StructureSites, limit: u64,
    result: Result<StructureDeclaration, StructureNumberError>,
) -> bool {
    let width = number_result(source.text, forms, sites.width, StructureNumber::TotalWidth, limit);
    &&& (result.is_ok() <==> (width.is_ok() && forall|i: int| 0 <= i < sites.fields@.len()
        ==> field_numbers_valid(source.text, forms, #[trigger] sites.fields@[i], limit)))
    &&& match result {
        Ok(declaration) =>
            width == Ok(declaration.width) && declaration.fields@.len() == sites.fields@.len()
            && (forall|i: int| 0 <= i < sites.fields@.len() ==> field_numbers_match(
                source.text, forms, sites.fields@[i], limit, #[trigger] declaration.fields@[i])),
        Err(error) => number_error(source, forms, sites.width, StructureNumber::TotalWidth, limit, error)
            || (width.is_ok() && exists|i: int| 0 <= i < sites.fields@.len()
                && #[trigger] field_number_error(source, forms, sites.fields@[i], limit, error)
                && (forall|j: int| 0 <= j < i ==> field_numbers_valid(source.text, forms, #[trigger] sites.fields@[j], limit))),
    }
}

fn read_structure_declaration<'p, 'a>(
    source: &'p ProjectSource<'a>, syntax: &CircuitForms, _entry: usize, sites: &StructureSites, limit: u64,
) -> (result: Result<StructureDeclaration, StructureNumberError<'p, 'a>>)
    requires
        structure_sites_match(source.text, syntax, _entry as int, Some(*sites)),
        form_spans_valid(source.text, syntax.forms@, source.text.spec_bytes().len() as int),
    ensures declaration_numbers_match(source, syntax.forms@, *sites, limit, result),
{
    proof { structure_width_site_evidence(source.text, syntax, _entry as int, *sites); }
    let forms = syntax.forms.as_slice();
    let width = read_structure_number(source, forms, sites.width, StructureNumber::TotalWidth, limit)?;
    let mut fields = Vec::new();
    let mut i = 0;
    while i < sites.fields.len()
        invariant
            structure_sites_match(source.text, syntax, _entry as int, Some(*sites)),
            form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
            forms@ == syntax.forms@,
            number_result(source.text, forms@, sites.width, StructureNumber::TotalWidth, limit) == Ok(width),
            i == fields@.len() <= sites.fields@.len(),
            forall|j: int| 0 <= j < i ==>
                field_numbers_match(source.text, forms@, sites.fields@[j], limit, #[trigger] fields@[j]),
            forall|j: int| 0 <= j < i ==> field_numbers_valid(source.text, forms@, #[trigger] sites.fields@[j], limit),
        decreases sites.fields@.len() - i,
    {
        proof { structure_field_site_evidence(source.text, syntax, _entry as int, *sites, i as int); }
        let site = sites.fields[i];
        let ty = match site.ty {
            FieldTypeSite::Named { form } => DeclaredFieldType::Named { form },
            FieldTypeSite::Bits { width: atom } => {
                let value = match read_structure_number(source, forms, atom, StructureNumber::FieldWidth, limit) {
                    Ok(value) => value,
                    Err(error) => {
                        assert(field_number_error(source, forms@, site, limit, error));
                        return Err(error);
                    },
                };
                DeclaredFieldType::Bits(value)
            },
        };
        assert(field_type(source.text, forms@, site, limit) == Ok(ty));
        let offset = match read_structure_number(source, forms, site.offset, StructureNumber::FieldOffset, limit) {
            Ok(value) => value,
            Err(error) => {
                assert(field_number_error(source, forms@, site, limit, error));
                return Err(error);
            },
        };
        let field = DeclaredField { site, ty, offset };
        assert(field_numbers_match(source.text, forms@, site, limit, field));
        fields.push(field);
        i += 1;
    }
    Ok(StructureDeclaration { width, fields })
}

/// 対象の厳格索引項目と、総幅およびフィールドの数値検査結果を結び付ける。
pub closed spec fn structure_declaration_result(
    project: &CircuitProject, file: int, entry: int, limit: u64,
    result: Result<Option<StructureDeclaration>, StructureNumberError>,
) -> bool {
    if 0 <= file < project.circuits_model().len()
        && 0 <= entry < project.circuits_model()[file].syntax.entries@.len()
        && project.circuits_model()[file].syntax.entries@[entry].head is Struct {
        let source = &project.sources_model()[file];
        let syntax = &project.circuits_model()[file].syntax;
        exists|sites: StructureSites| #[trigger] structure_sites_match(source.text, syntax, entry, Some(sites))
            && match result {
                Ok(Some(declaration)) => declaration_numbers_match(source, syntax.forms@, sites, limit, Ok(declaration)),
                Err(error) => declaration_numbers_match(source, syntax.forms@, sites, limit, Err(error)),
                Ok(None) => false,
            }
    } else {
        result == Ok(None)
    }
}

/// 数値検査に成功した宣言が、元の索引と幅の上限に対応することを示す。
pub(super) proof fn checked_structure_fields(
    project: &CircuitProject, file: usize, entry: usize, limit: u64, declaration: StructureDeclaration,
)
    requires
        project.has_parsed_sources(),
        structure_declaration_result(project, file as int, entry as int, limit, Ok(Some(declaration))),
    ensures
        file < project.circuits_model().len(),
        entry < project.circuits_model()[file as int].syntax.entries@.len(),
        project.circuits_model()[file as int].syntax.entries@[entry as int].head is Struct,
        0 < declaration.width <= limit,
        forall|i: int| 0 <= i < declaration.fields@.len() ==> {
            let field = #[trigger] declaration.fields@[i];
            let forms = project.circuits_model()[file as int].syntax.forms@;
            &&& field.site.name < forms.len()
            &&& forms[field.site.name as int] is Atom
            &&& forms[field.site.name as int]->Atom_kind is Name
            &&& field.site.offset < forms.len()
            &&& forms[field.site.offset as int] is Atom
            &&& forms[field.site.offset as int]->Atom_kind is Natural
            &&& match field.ty {
                DeclaredFieldType::Bits(width) => 0 < width <= limit,
                DeclaredFieldType::Named { form } =>
                    form < forms.len() && forms[form as int] is Atom && reference_atom(forms[form as int]->Atom_kind),
            }
        },
{
    reveal(structure_declaration_result);
    let source = &project.sources_model()[file as int];
    let syntax = &project.circuits_model()[file as int].syntax;
    let forms = syntax.forms@;
    let sites = choose|sites: StructureSites| #[trigger] structure_sites_match(source.text, syntax, entry as int, Some(sites))
        && declaration_numbers_match(source, forms, sites, limit, Ok(declaration));
    assert(number_result(source.text, forms, sites.width, StructureNumber::TotalWidth, limit) == Ok(declaration.width));
    assert forall|i: int| 0 <= i < declaration.fields@.len() implies {
        let field = #[trigger] declaration.fields@[i];
        &&& field.site.name < forms.len()
        &&& forms[field.site.name as int] is Atom
        &&& forms[field.site.name as int]->Atom_kind is Name
        &&& field.site.offset < forms.len()
        &&& forms[field.site.offset as int] is Atom
        &&& forms[field.site.offset as int]->Atom_kind is Natural
        &&& match field.ty {
            DeclaredFieldType::Bits(width) => 0 < width <= limit,
            DeclaredFieldType::Named { form } =>
                form < forms.len() && forms[form as int] is Atom && reference_atom(forms[form as int]->Atom_kind),
        }
    } by {
        let field = declaration.fields@[i];
        assert(field_numbers_match(source.text, forms, sites.fields@[i], limit, field));
        structure_field_site_evidence(source.text, syntax, entry as int, sites, i);
    };
}

/// 総幅、フィールドの幅とオフセットを検査して宣言順に返す。
///
/// `file` と `entry` にはソース一覧と厳格索引の添字を渡す。対象外は `Ok(None)` を返す。
/// 型名は後段の名前解決用に保持する。`limit` は幅の上限であり、オフセットは総幅と照合する段階で検査する。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::project::{
///     SourceSnapshot, StructureNumber, StructureNumberErrorKind, check_structure_declaration, parse_circuit_project,
/// };
/// let text = "(struct Word (width 8) (lo (bits 4) (at 0)))";
/// let project = parse_circuit_project(&[SourceSnapshot {
///     path: "layout.ncg2", revision: 1, text,
/// }]).unwrap();
/// let word = check_structure_declaration(&project, 0, 0, 8).unwrap().unwrap();
/// assert_eq!(word.width, 8);
/// assert_eq!(word.fields[0].offset, 0);
/// let failure = check_structure_declaration(&project, 0, 0, 7).unwrap_err();
/// assert_eq!(failure.number, StructureNumber::TotalWidth);
/// assert_eq!(failure.kind, StructureNumberErrorKind::WidthLimit { width: 8, limit: 7 });
/// assert_eq!(&text[failure.span], "8");
/// ```
///
/// # Errors
///
/// 総幅の後でフィールドを宣言順に確認する。各フィールドでは幅指定とオフセットの順に確認し、
/// 最初の数値違反を返す。
pub fn check_structure_declaration<'p, 'a>(
    project: &'p CircuitProject<'a>, file: usize, entry: usize, limit: u64,
) -> (result: Result<Option<StructureDeclaration>, StructureNumberError<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures structure_declaration_result(project, file as int, entry as int, limit, result),
{
    let circuits = project.circuits();
    if file >= circuits.len() { return Ok(None); }
    let source = &project.sources()[file];
    let parsed = &circuits[file];
    proof {
        assert(parsed_circuit_matches(*source, *parsed));
        parsed_index_evidence(*source, *parsed);
    }
    let Some(sites) = structure_sites(source.text, &parsed.syntax, entry) else { return Ok(None); };
    let declaration = read_structure_declaration(source, &parsed.syntax, entry, &sites, limit)?;
    Ok(Some(declaration))
}

} // verus!
