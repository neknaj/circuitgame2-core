//! NCG2M の宣言から、式の型検査で使う型と束縛を取り出す。

use alloc::vec::Vec;
use core::ops::Range;
use crate::project::read_source_span;
use super::defn::{DataTypeName, DataTypeSyntax, DefnHeader, DefnHeaderError, parse_defn_header_with_spans};
#[cfg(verus_only)]
use super::defn::{DefnParameter, defn_header_matches, readable_span, signature_spans_valid, type_spans_valid, valid_defn_header};
use super::integers::IntegerType;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// すべての実行段階で使える基本データ型。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuiltinDataType {
    /// 真偽値。
    Bool,
    /// 64ビット整数。符号の有無は整数型が表す。
    Integer(IntegerType),
    /// 名前を持つデータ。
    Symbol,
    /// 位置と束縛情報を持つ構文オブジェクト。
    Syntax,
}

/// データ型の最も内側にある型の種類。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DataTypeAtom<'a> {
    /// すべての実行段階に共通する型。
    Builtin(BuiltinDataType),
    /// 実行段階に応じて解決する、元ソース上の型名。
    Named(&'a str),
}

/// 型の検査に使うデータ型の参照。
///
/// 例えば `(List (List Nat))` は `Nat` と深さ2で表す。比較には型名の綴りと深さを使う。
/// 段階固有の型名が指す型は、実行段階が決まってから解決する。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DataType<'a> {
    /// 型を構成する最も内側の基本型または型名。
    pub atom: DataTypeAtom<'a>,
    /// 最も内側の型を包む `List` の数。
    pub list_depth: usize,
}

impl<'a> DataType<'a> {
    /// リスト型の要素型を返す。基本型や単独の型名では `None` を返す。
    pub fn element(self) -> (element: Option<DataType<'a>>)
        ensures element == if self.list_depth == 0 {
            None
        } else {
            Some(DataType { atom: self.atom, list_depth: (self.list_depth - 1) as usize })
        },
    {
        if self.list_depth == 0 {
            None
        } else {
            Some(DataType { atom: self.atom, list_depth: self.list_depth - 1 })
        }
    }
}

/// 元ソースの範囲を持つ型参照。
#[derive(Debug, Eq, PartialEq)]
pub struct LocatedDataType<'a> {
    /// 型の検査に使う型参照。
    pub ty: DataType<'a>,
    /// 型全体の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 最も内側の型名の UTF-8 半開バイト範囲。
    pub name_span: Range<usize>,
}

/// 宣言された仮引数とその型。
#[derive(Debug, Eq, PartialEq)]
pub struct SignatureParameter<'a> {
    /// 元ソースから借りた仮引数名。
    pub name: &'a str,
    /// 仮引数名の UTF-8 半開バイト範囲。
    pub name_span: Range<usize>,
    /// 仮引数に指定された型。
    pub ty: LocatedDataType<'a>,
}

/// `defn` の本体を型検査するときに使う署名。
#[derive(Debug, Eq, PartialEq)]
pub struct DefnSignature<'a> {
    /// 宣言全体の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 宣言名の UTF-8 半開バイト範囲。
    pub name_span: Range<usize>,
    /// `fn` に書かれた順に並ぶ仮引数と型。
    pub parameters: Vec<SignatureParameter<'a>>,
    /// 本体に要求される戻り値型。
    pub result_type: LocatedDataType<'a>,
    /// 本体の共通 S 式1個の UTF-8 半開バイト範囲。
    pub body_span: Range<usize>,
}

spec fn source_spelling(source: &str, span: Range<usize>) -> Seq<u8> {
    source.spec_bytes()[span.start as int..span.end as int]
}

/// 型参照の基本型または型名、リストの深さ、両方の範囲が構文に対応することを表す。
pub open spec fn data_type_matches(source: &str, syntax: DataTypeSyntax, value: LocatedDataType) -> bool {
    &&& value.ty.list_depth == syntax.list_depth
    &&& value.span == syntax.span
    &&& value.name_span == syntax.name_span
    &&& match syntax.name {
        DataTypeName::Bool => value.ty.atom == DataTypeAtom::Builtin(BuiltinDataType::Bool),
        DataTypeName::Nat => value.ty.atom == DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Nat)),
        DataTypeName::Int => value.ty.atom == DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Int)),
        DataTypeName::Symbol => value.ty.atom == DataTypeAtom::Builtin(BuiltinDataType::Symbol),
        DataTypeName::Syntax => value.ty.atom == DataTypeAtom::Builtin(BuiltinDataType::Syntax),
        DataTypeName::Deferred => value.ty.atom matches DataTypeAtom::Named(word)
            && word.spec_bytes() == source.spec_bytes()[syntax.name_span.start as int..syntax.name_span.end as int],
    }
}

fn read_type_value<'a>(source: &'a str, syntax: &DataTypeSyntax) -> (value: LocatedDataType<'a>)
    requires type_spans_valid(source, *syntax),
    ensures data_type_matches(source, *syntax, value),
{
    let atom = match syntax.name {
        DataTypeName::Bool => DataTypeAtom::Builtin(BuiltinDataType::Bool),
        DataTypeName::Nat => DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Nat)),
        DataTypeName::Int => DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Int)),
        DataTypeName::Symbol => DataTypeAtom::Builtin(BuiltinDataType::Symbol),
        DataTypeName::Syntax => DataTypeAtom::Builtin(BuiltinDataType::Syntax),
        DataTypeName::Deferred => {
            let word = read_source_span(source, syntax.name_span.start, syntax.name_span.end);
            DataTypeAtom::Named(word)
        }
    };
    LocatedDataType {
        ty: DataType { atom, list_depth: syntax.list_depth },
        span: syntax.span.start..syntax.span.end,
        name_span: syntax.name_span.start..syntax.name_span.end,
    }
}

spec fn parameter_matches(source: &str, parameter: DefnParameter, value: SignatureParameter) -> bool {
    &&& value.name_span == parameter.name_span
    &&& value.name.spec_bytes() == source_spelling(source, parameter.name_span)
    &&& data_type_matches(source, parameter.ty, value.ty)
}

/// `defn` の構文から署名の型と束縛を位置順に取り出したことを表す。
pub closed spec fn signature_matches_header(source: &str, header: DefnHeader, signature: DefnSignature) -> bool {
    &&& signature.span == header.span && signature.name_span == header.name_span && signature.body_span == header.body_span
    &&& data_type_matches(source, header.result_type, signature.result_type)
    &&& signature.parameters@.len() == header.parameters@.len()
    &&& forall|i: int| 0 <= i < signature.parameters@.len() ==>
        #[trigger] parameter_matches(source, header.parameters@[i], signature.parameters@[i])
}


/// 署名の戻り値型、仮引数の個数、宣言と本体の範囲が元のヘッダーに対応することを示す。
pub proof fn signature_result_origin(source: &str, header: DefnHeader, signature: DefnSignature)
    requires signature_matches_header(source, header, signature),
    ensures
        signature.span == header.span,
        signature.name_span == header.name_span,
        signature.body_span == header.body_span,
        signature.parameters@.len() == header.parameters@.len(),
        data_type_matches(source, header.result_type, signature.result_type),
{}

/// 署名の仮引数名と型が、元の宣言の同じ位置にある仮引数に対応することを示す。
pub proof fn signature_parameter_origin(source: &str, header: DefnHeader, signature: DefnSignature, at: int)
    requires signature_matches_header(source, header, signature), 0 <= at < signature.parameters@.len(),
    ensures
        at < header.parameters@.len(),
        signature.parameters@[at].name_span == header.parameters@[at].name_span,
        signature.parameters@[at].name.spec_bytes()
            == source.spec_bytes()[header.parameters@[at].name_span.start as int
                ..header.parameters@[at].name_span.end as int],
        data_type_matches(source, header.parameters@[at].ty, signature.parameters@[at].ty),
{
    assert(parameter_matches(source, header.parameters@[at], signature.parameters@[at]));
}

pub(crate) fn read_header_signature<'a>(source: &'a str, header: &DefnHeader) -> (value: DefnSignature<'a>)
    requires signature_spans_valid(source, *header),
    ensures signature_matches_header(source, *header, value),
{
    let mut parameters = Vec::new();
    let mut index = 0;
    while index < header.parameters.len()
        invariant
            signature_spans_valid(source, *header),
            index == parameters@.len() <= header.parameters@.len(),
            forall|i: int| 0 <= i < index ==>
                #[trigger] parameter_matches(source, header.parameters@[i], parameters@[i]),
        decreases header.parameters@.len() - index,
    {
        let parameter = &header.parameters[index];
        let name = read_source_span(source, parameter.name_span.start, parameter.name_span.end);
        let ty = read_type_value(source, &parameter.ty);
        parameters.push(SignatureParameter {
            name, name_span: parameter.name_span.start..parameter.name_span.end, ty,
        });
        index += 1;
    }
    DefnSignature {
        span: header.span.start..header.span.end,
        name_span: header.name_span.start..header.name_span.end,
        parameters,
        result_type: read_type_value(source, &header.result_type),
        body_span: header.body_span.start..header.body_span.end,
    }
}

/// 署名または診断が、元ソースに対応することを表す。
pub closed spec fn defn_signature_matches(source: &str, result: Result<DefnSignature, DefnHeaderError>) -> bool {
    match result {
        Ok(signature) => exists|header: DefnHeader| #[trigger] defn_header_matches(source, Ok(header))
            && signature_matches_header(source, header, signature),
        Err(error) => defn_header_matches(source, Err(error)),
    }
}

/// 単独の `defn` を検査し、本体の型検査で使う署名を返す。
///
/// 元ソースから型名と仮引数名を借りる。実行段階で参照できる型の判定と本体の型検査は後段で行う。
///
/// # Errors
///
/// ヘッダー解析の最初の違反と範囲を返す。データ型の位置では `Fn` の署名も拒否する。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::ncg2m::data_types::{DataTypeAtom, parse_defn_signature};
///
/// let signature = parse_defn_signature(
///     "(defn forward (as-type (Fn ((List (List HostEvent))) (List HostEvent)) (fn (events) (head events))))",
/// )?;
/// let argument = signature.parameters[0].ty.ty;
/// assert_eq!(signature.parameters[0].name, "events");
/// assert_eq!(argument.element(), Some(signature.result_type.ty));
/// assert_eq!(argument.atom, DataTypeAtom::Named("HostEvent"));
/// # Ok::<(), circuitgame2_core::ncg2m::defn::DefnHeaderError>(())
/// ```
pub fn parse_defn_signature(source: &str) -> (result: Result<DefnSignature<'_>, DefnHeaderError>)
    ensures result.is_ok() == valid_defn_header(source), defn_signature_matches(source, result),
{
    let header = parse_defn_header_with_spans(source)?;
    let signature = read_header_signature(source, &header);
    Ok(signature)
}

}
