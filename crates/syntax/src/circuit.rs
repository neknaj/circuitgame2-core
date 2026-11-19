//! S 式を回路文法に照らして検査し、宣言の位置を取り出す。

use crate::{AtomKind, Error, Form, parse};
#[cfg(verus_only)]
use crate::{
    complete_list_indices, form_span, form_spans_valid, list_delimited, list_source_delimiters,
};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::{
    encode_utf8_decode_utf8, encode_utf8_valid_utf8, is_char_boundary,
    is_char_boundary_iff_not_is_continuation_byte,
};

verus! {

/// 先頭語で識別される回路フォームの種別。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Head {
    /// 基底を選ぶ `using`。
    Using,
    /// 名前空間を宣言する `namespace`。
    Namespace,
    /// 完全修飾名に別名を与える `use`。
    Use,
    /// 名前を公開する `export`。
    Export,
    /// 組み合わせ回路を宣言する `func`。
    Func,
    /// 状態を持てる回路を宣言する `module`。
    Module,
    /// モジュールの断片を宣言する `module-part`。
    ModulePart,
    /// ビット列上のフィールド配置を宣言する `struct`。
    Struct,
    /// ラッチを宣言する `latch`。
    Latch,
    /// メモリを宣言する `memory`。
    Memory,
    /// 回路のテストを宣言する `test`。
    Test,
}

} // verus!

/// 回路フォームと、それを含む名前空間の位置。
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry {
    /// フォームの種別。
    pub head: Head,
    /// フォームを指す、[`CircuitForms::forms`] 内の添字。
    pub form: usize,
    /// 囲んでいる名前空間フォームの添字。トップレベルのフォームでは `None`。
    pub namespace: Option<usize>,
}

/// 回路文法に従う構文木と、回路フォームを参照するための索引。
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CircuitForms {
    /// S 式の全要素を先行順に並べた構文木。
    pub forms: Vec<Form>,
    /// トップレベルのフォームと名前空間の直下にあるフォームを元入力順に並べた索引。
    pub entries: Vec<Entry>,
}

verus! {

/// 回路フォームの構文検査で判明した文法上の誤り。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeaderError {
    /// フォームを表すリストが必要である。
    ExpectedList,
    /// リストの先頭にフォームを識別する名前が必要である。
    ExpectedHead,
    /// 先頭語が回路フォームの種別を表していない。
    UnknownHead,
    /// この位置には指定した種別のフォームを置けない。
    MisplacedHead(Head),
    /// 名前空間を示す名前または相対パスが不足しているか、文法に合わない。
    ExpectedNamespacePath,
    /// 基底の指定には `nor` が必要である。
    ExpectedNor,
    /// 指定した位置に完全修飾名がない。
    ExpectedAbsolutePath,
    /// 修飾子を含まない名前が必要である。
    ExpectedName,
    /// 名前、相対パス、完全修飾名のいずれかが必要である。
    ExpectedReference,
    /// 自然数が必要である。
    ExpectedNatural,
    /// ポート名または型付きポートが必要である。
    ExpectedPort,
    /// 型への参照またはビット幅を指定する型が必要である。
    ExpectedType,
    /// 回路本体の項目には `def` または `expand` が必要である。
    ExpectedBodyItem,
    /// `def` の出力先を示す名前または名前のリストが必要である。
    ExpectedTarget,
    /// 回路式が必要である。
    ExpectedExpression,
    /// テスト本体に `case` または操作が必要である。
    ExpectedTestItem,
    /// 一つのテストに `case` と操作が混在している。
    MixedTestItems {
        /// 最初の項目の先頭語を指す、元入力の半開バイト範囲の両端。
        first_head: (usize, usize),
    },
    /// テスト用のリテラルまたは型を指定したリテラルが必要である。
    ExpectedTestValue,
    /// 期待値にはテスト用の値または `any` が必要である。
    ExpectedTestValueOrAny,
    /// 必須の節がないか、先頭語が期待するものと異なる。
    ExpectedClause(Clause),
    /// この位置には引数を追加できない。
    UnexpectedArgument,
}

/// 宣言やテストの内部で期待される節の先頭語。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Clause {
    /// 入力の節 `in`。
    In,
    /// 出力の節 `out`。
    Out,
    /// 期待値の節 `expect`。
    Expect,
    /// ビット幅を指定する `bits`。
    Bits,
    /// 構造体またはラッチの幅を指定する `width`。
    Width,
    /// メモリのアドレス幅を指定する `address`。
    Address,
    /// メモリのデータ型を指定する `data`。
    Data,
    /// 構造体のフィールドの位置を指定する `at`。
    At,
}

} // verus!

impl Clause {
    fn spelling(self) -> &'static str {
        match self {
            Self::In => "in",
            Self::Out => "out",
            Self::Expect => "expect",
            Self::Bits => "bits",
            Self::Width => "width",
            Self::Address => "address",
            Self::Data => "data",
            Self::At => "at",
        }
    }
}

/// S 式解析または回路フォームの構文検査で失敗した理由。
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitFormError {
    /// 回路フォームを調べる前に見つかった字句または S 式の誤り。
    Syntax(Error),
    /// S 式として読める入力に含まれる回路文法の誤り。
    Header {
        /// 期待する構文と、必要に応じてその関連位置。
        kind: HeaderError,
        /// 元入力の UTF-8 半開バイト範囲。要素の挿入位置は長さ0となる。
        span: Range<usize>,
    },
}

/// 回路フォームの宣言位置を構文木の添字で返す。
///
/// 単一ソースの宣言シグネチャ、回路本体、テスト本体を検査する。
/// `(using nor)` を一度だけ指定する要件は、名前解決と同様にソース集合を対象とする後続の検査で扱う。
/// 型と結線の検査も後続の処理で扱う。
///
/// # Errors
///
/// 字句、S 式、検査対象の回路フォームに誤りがあれば、元入力の UTF-8 バイト範囲をエラーに含める。
/// 回路フォームに必須の要素がなければ、挿入位置を長さ0の範囲で示す。
/// テストで `case` と操作が混在すると、最初と種類が異なる項目の先頭語を主範囲とする。最初の項目についても先頭語の範囲をエラーに含める。
///
/// # Examples
///
/// ```
/// use circuitgame2_syntax::circuit::{Head, index_headers};
///
/// let result = index_headers("(namespace gates (func f (in) (out y) (def y 0)))")?;
/// assert_eq!(result.entries[1].head, Head::Func);
/// assert_eq!(result.entries[1].namespace, Some(result.entries[0].form));
/// # Ok::<(), circuitgame2_syntax::circuit::CircuitFormError>(())
/// ```
pub fn index_headers(source: &str) -> Result<CircuitForms, CircuitFormError> {
    let forms = parse(source).map_err(CircuitFormError::Syntax)?;
    let mut entries = Vec::new();
    let mut root = 0;
    while root < forms.len() {
        let (head, end) = read_header(source, &forms, root, false)?;
        entries.push(Entry {
            head,
            form: root,
            namespace: None,
        });
        if head == Head::Namespace {
            let mut item = root + 3;
            while item < end {
                let (head, next) = read_header(source, &forms, item, true)?;
                entries.push(Entry {
                    head,
                    form: item,
                    namespace: Some(root),
                });
                item = next;
            }
        }
        root = end;
    }
    Ok(CircuitForms { forms, entries })
}

fn read_header(
    source: &str,
    forms: &[Form],
    index: usize,
    in_namespace: bool,
) -> Result<(Head, usize), CircuitFormError> {
    let (head, end, closing) = read_form_head(source, forms, index, in_namespace)
        .map_err(|(kind, span)| header_error(kind, span))?;
    let argument = index + 2;
    match head {
        Head::Using => {
            let nor = require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedNor,
                |kind| kind == AtomKind::Name,
            )?;
            if &source[nor.clone()] != "nor" {
                return Err(header_error(HeaderError::ExpectedNor, nor));
            }
            require_end(forms, argument + 1, end)?;
        }
        Head::Namespace => {
            require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedNamespacePath,
                |kind| matches!(kind, AtomKind::Name | AtomKind::RelativePath),
            )?;
        }
        Head::Use => {
            require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedAbsolutePath,
                |kind| kind == AtomKind::AbsolutePath,
            )?;
            require_atom(
                forms,
                argument + 1,
                end,
                closing,
                HeaderError::ExpectedName,
                |kind| kind == AtomKind::Name,
            )?;
            require_end(forms, argument + 2, end)?;
        }
        Head::Export => {
            require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedName,
                |kind| kind == AtomKind::Name,
            )?;
            for item in argument + 1..end {
                require_atom(
                    forms,
                    item,
                    end,
                    closing,
                    HeaderError::ExpectedName,
                    |kind| kind == AtomKind::Name,
                )?;
            }
        }
        Head::Test => {
            require_atom(
                forms,
                argument,
                end,
                closing,
                HeaderError::ExpectedReference,
                is_reference,
            )?;
            test_body(source, forms, argument + 1, end, closing)?;
        }
        Head::Func
        | Head::Module
        | Head::ModulePart
        | Head::Struct
        | Head::Latch
        | Head::Memory => {
            require_name(forms, argument, end, closing)?;
            declaration_signature(source, forms, head, argument + 1, end, closing)?;
        }
    }
    Ok((head, end))
}

fn test_body(
    source: &str,
    forms: &[Form],
    mut item: usize,
    end: usize,
    closing: usize,
) -> Result<(), CircuitFormError> {
    if item == end {
        return Err(header_error(
            HeaderError::ExpectedTestItem,
            closing..closing,
        ));
    }

    let mut first: Option<(TestHead, Range<usize>)> = None;
    while item < end {
        let expected = HeaderError::ExpectedTestItem;
        let (item_end, item_close) = list_at(forms, item, end, closing, expected)?;
        let name = require_atom(forms, item + 1, item_end, item_close, expected, |kind| {
            kind == AtomKind::Name
        })?;
        let Some(head) = recognize_test_head(&source[name.clone()]) else {
            return Err(header_error(expected, name));
        };
        if let Some((first_head, first_span)) = &first {
            if !same_test_item_kind(*first_head, head) {
                return Err(header_error(
                    HeaderError::MixedTestItems {
                        first_head: (first_span.start, first_span.end),
                    },
                    name,
                ));
            }
        } else {
            first = Some((head, name));
        }

        let argument = item + 2;
        match head {
            TestHead::Case => {
                let (inputs_end, _) =
                    named_clause(source, forms, argument, item_end, item_close, Clause::In)?;
                test_values(source, forms, argument + 2, inputs_end, false)?;
                let (expects_end, _) = named_clause(
                    source,
                    forms,
                    inputs_end,
                    item_end,
                    item_close,
                    Clause::Expect,
                )?;
                test_values(source, forms, inputs_end + 2, expects_end, true)?;
                require_end(forms, expects_end, item_end)?;
            }
            TestHead::Reset => require_end(forms, argument, item_end)?,
            TestHead::Drive => test_values(source, forms, argument, item_end, false)?,
            TestHead::Tick => {
                let next = natural_at(forms, argument, item_end, item_close)?;
                require_end(forms, next, item_end)?;
            }
            TestHead::Expect => test_values(source, forms, argument, item_end, true)?,
        }
        item = item_end;
    }

    Ok(())
}

fn test_values(
    source: &str,
    forms: &[Form],
    mut index: usize,
    end: usize,
    allow_any: bool,
) -> Result<(), CircuitFormError> {
    let expected = if allow_any {
        HeaderError::ExpectedTestValueOrAny
    } else {
        HeaderError::ExpectedTestValue
    };

    while index < end {
        index = match &forms[index] {
            Form::Atom { kind, span } if test_atom(*kind, &source[span.clone()], allow_any) => {
                index + 1
            }
            Form::List {
                span: list_span,
                end,
            } => {
                let closing = list_span.end - 1;
                let head = require_atom(forms, index + 1, *end, closing, expected, |kind| {
                    kind == AtomKind::Name
                })?;
                if recognize_expression_head(&source[head.clone()]) != Some(ExpressionHead::As) {
                    return Err(header_error(expected, head));
                }
                require_atom(
                    forms,
                    index + 2,
                    *end,
                    closing,
                    HeaderError::ExpectedReference,
                    is_reference,
                )?;
                let value = index + 3;
                let error = HeaderError::ExpectedTestValue;
                if value >= *end {
                    return Err(header_error(error, closing..closing));
                }
                match &forms[value] {
                    Form::Atom { kind, span } if circuit_value(*kind, &source[span.clone()]) => {}
                    form => return Err(header_error(error, span(form))),
                }
                require_end(forms, value + 1, *end)?;
                *end
            }
            form => return Err(header_error(expected, span(form))),
        };
    }

    Ok(())
}

fn declaration_signature(
    source: &str,
    forms: &[Form],
    head: Head,
    argument: usize,
    end: usize,
    closing: usize,
) -> Result<(), CircuitFormError> {
    match head {
        Head::Func | Head::Module => {
            let out = ports(source, forms, argument, end, closing, Clause::In)?;
            let first_body = ports(source, forms, out, end, closing, Clause::Out)?;
            routine_body(source, forms, first_body, end, closing)?;
        }
        Head::ModulePart => routine_body(source, forms, argument, end, closing)?,
        Head::Struct | Head::Latch => {
            let mut field = natural_clause(source, forms, argument, end, closing, Clause::Width)?;
            if head == Head::Latch {
                return require_end(forms, field, end);
            }
            while field < end {
                let (field_end, field_close) =
                    list_at(forms, field, end, closing, HeaderError::ExpectedList)?;
                require_name(forms, field + 1, field_end, field_close)?;
                let at = type_at(source, forms, field + 2, field_end, field_close)?;
                let next = natural_clause(source, forms, at, field_end, field_close, Clause::At)?;
                require_end(forms, next, field_end)?;
                field = field_end;
            }
        }
        Head::Memory => {
            let data = natural_clause(source, forms, argument, end, closing, Clause::Address)?;
            let (data_end, data_close) =
                named_clause(source, forms, data, end, closing, Clause::Data)?;
            let next = type_at(source, forms, data + 2, data_end, data_close)?;
            require_end(forms, next, data_end)?;
            require_end(forms, data_end, end)?;
        }
        _ => {}
    }
    Ok(())
}

fn routine_body(
    source: &str,
    forms: &[Form],
    mut item: usize,
    end: usize,
    closing: usize,
) -> Result<(), CircuitFormError> {
    while item < end {
        let (item_end, item_close) =
            list_at(forms, item, end, closing, HeaderError::ExpectedBodyItem)?;
        let head = require_atom(
            forms,
            item + 1,
            item_end,
            item_close,
            HeaderError::ExpectedBodyItem,
            |kind| kind == AtomKind::Name,
        )?;
        let first = item + 2;
        match recognize_body_head(&source[head.clone()]) {
            Some(BodyHead::Expand) => {
                require_atom(
                    forms,
                    first,
                    item_end,
                    item_close,
                    HeaderError::ExpectedReference,
                    is_reference,
                )?;
            }
            Some(BodyHead::Def) => {
                let value = targets(forms, first, item_end, item_close)?;
                let after_value = expression_end(forms, value, item_end, item_close)?;
                require_end(forms, after_value, item_end)?;
                expressions(source, forms, value..after_value)?;
            }
            None => return Err(header_error(HeaderError::ExpectedBodyItem, head)),
        }
        item = item_end;
    }
    Ok(())
}

fn targets(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<usize, CircuitFormError> {
    if index >= end {
        return Err(header_error(HeaderError::ExpectedTarget, closing..closing));
    }
    match &forms[index] {
        Form::Atom {
            kind: AtomKind::Name,
            ..
        } => Ok(index + 1),
        Form::List { span, end } => {
            let closing = span.end - 1;
            let first = index + 1;
            require_name(forms, first, *end, closing)?;
            for name in first + 1..*end {
                require_name(forms, name, *end, closing)?;
            }
            Ok(*end)
        }
        form => Err(header_error(HeaderError::ExpectedTarget, span(form))),
    }
}

fn expression_end(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<usize, CircuitFormError> {
    if index >= end {
        return Err(header_error(
            HeaderError::ExpectedExpression,
            closing..closing,
        ));
    }
    Ok(match &forms[index] {
        Form::Atom { .. } => index + 1,
        Form::List { end, .. } => *end,
    })
}

fn expressions(source: &str, forms: &[Form], roots: Range<usize>) -> Result<(), CircuitFormError> {
    let mut pending = Vec::new();
    pending.push(roots);
    while let Some(mut sequence) = pending.pop() {
        while sequence.start < sequence.end {
            let index = sequence.start;
            match &forms[index] {
                Form::Atom { kind, span } => {
                    if !expression_atom(*kind, &source[span.clone()]) {
                        return Err(header_error(HeaderError::ExpectedExpression, span.clone()));
                    }
                    sequence.start += 1;
                }
                Form::List { span, end } => {
                    let children = expression_children(source, forms, index, *end, span.end - 1)?;
                    if *end < sequence.end {
                        pending.push(*end..sequence.end);
                    }
                    sequence = children;
                }
            }
        }
    }
    Ok(())
}

fn expression_children(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<Range<usize>, CircuitFormError> {
    let head = require_atom(
        forms,
        index + 1,
        end,
        closing,
        HeaderError::ExpectedReference,
        is_reference,
    )?;
    let first = index + 2;
    let builtin = recognize_expression_head(&source[head]);
    match builtin {
        Some(ExpressionHead::As) => {
            require_atom(
                forms,
                first,
                end,
                closing,
                HeaderError::ExpectedReference,
                is_reference,
            )?;
            let value = first + 1;
            let next = expression_end(forms, value, end, closing)?;
            require_end(forms, next, end)?;
            Ok(value..next)
        }
        Some(
            ExpressionHead::Bit
            | ExpressionHead::Slice
            | ExpressionHead::Field
            | ExpressionHead::Raw,
        ) => {
            let next = expression_end(forms, first, end, closing)?;
            let after = match builtin {
                Some(ExpressionHead::Bit) => natural_at(forms, next, end, closing)?,
                Some(ExpressionHead::Slice) => {
                    let length = natural_at(forms, next, end, closing)?;
                    let after_length = natural_at(forms, length, end, closing)?;
                    if after_length < end {
                        natural_at(forms, after_length, end, closing)?
                    } else {
                        after_length
                    }
                }
                Some(ExpressionHead::Field) => {
                    require_name(forms, next, end, closing)?;
                    next + 1
                }
                _ => next,
            };
            require_end(forms, after, end)?;
            Ok(first..next)
        }
        Some(ExpressionHead::Concat) => {
            expression_end(forms, first, end, closing)?;
            Ok(first..end)
        }
        None => Ok(first..end),
    }
}

fn natural_at(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<usize, CircuitFormError> {
    require_atom(
        forms,
        index,
        end,
        closing,
        HeaderError::ExpectedNatural,
        |kind| kind == AtomKind::Natural,
    )?;
    Ok(index + 1)
}

fn ports(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    clause: Clause,
) -> Result<usize, CircuitFormError> {
    let (port_end, port_close) = named_clause(source, forms, index, end, closing, clause)?;
    let mut port = index + 2;
    if clause == Clause::Out && port == port_end {
        return Err(header_error(
            HeaderError::ExpectedPort,
            port_close..port_close,
        ));
    }
    while port < port_end {
        port = match &forms[port] {
            Form::Atom {
                kind: AtomKind::Name,
                ..
            } => port + 1,
            Form::List { .. } => {
                let (typed_end, typed_close) =
                    list_at(forms, port, port_end, port_close, HeaderError::ExpectedPort)?;
                require_name(forms, port + 1, typed_end, typed_close)?;
                let next = type_at(source, forms, port + 2, typed_end, typed_close)?;
                require_end(forms, next, typed_end)?;
                typed_end
            }
            form => return Err(header_error(HeaderError::ExpectedPort, span(form))),
        };
    }
    Ok(port_end)
}

fn type_at(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<usize, CircuitFormError> {
    if index >= end {
        return Err(header_error(HeaderError::ExpectedType, closing..closing));
    }
    match &forms[index] {
        Form::Atom { kind, .. } if is_reference(*kind) => Ok(index + 1),
        Form::List { .. } => natural_clause(source, forms, index, end, closing, Clause::Bits),
        form => Err(header_error(HeaderError::ExpectedType, span(form))),
    }
}

fn natural_clause(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    clause: Clause,
) -> Result<usize, CircuitFormError> {
    let (clause_end, clause_close) = named_clause(source, forms, index, end, closing, clause)?;
    let next = natural_at(forms, index + 2, clause_end, clause_close)?;
    require_end(forms, next, clause_end)?;
    Ok(clause_end)
}

fn named_clause(
    source: &str,
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    clause: Clause,
) -> Result<(usize, usize), CircuitFormError> {
    let expected = HeaderError::ExpectedClause(clause);
    let (clause_end, clause_close) = list_at(forms, index, end, closing, expected)?;
    let head = require_atom(
        forms,
        index + 1,
        clause_end,
        clause_close,
        expected,
        |kind| kind == AtomKind::Name,
    )?;
    if &source[head.clone()] != clause.spelling() {
        return Err(header_error(expected, head));
    }
    Ok((clause_end, clause_close))
}

fn list_at(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    expected: HeaderError,
) -> Result<(usize, usize), CircuitFormError> {
    if index >= end {
        return Err(header_error(expected, closing..closing));
    }
    match &forms[index] {
        Form::List { span, end } => Ok((*end, span.end - 1)),
        form => Err(header_error(expected, span(form))),
    }
}

fn require_name(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
) -> Result<(), CircuitFormError> {
    require_atom(
        forms,
        index,
        end,
        closing,
        HeaderError::ExpectedName,
        |kind| kind == AtomKind::Name,
    )?;
    Ok(())
}

fn is_reference(kind: AtomKind) -> bool {
    matches!(
        kind,
        AtomKind::Name | AtomKind::RelativePath | AtomKind::AbsolutePath
    )
}

fn require_atom(
    forms: &[Form],
    index: usize,
    end: usize,
    closing: usize,
    expected: HeaderError,
    accepts: impl FnOnce(AtomKind) -> bool,
) -> Result<Range<usize>, CircuitFormError> {
    if index >= end {
        return Err(header_error(expected, closing..closing));
    }
    match &forms[index] {
        Form::Atom { kind, span } if accepts(*kind) => Ok(span.clone()),
        form => Err(header_error(expected, span(form))),
    }
}

fn require_end(forms: &[Form], at: usize, end: usize) -> Result<(), CircuitFormError> {
    if at < end {
        Err(header_error(
            HeaderError::UnexpectedArgument,
            span(&forms[at]),
        ))
    } else {
        Ok(())
    }
}

fn span(form: &Form) -> Range<usize> {
    match form {
        Form::Atom { span, .. } | Form::List { span, .. } => span.clone(),
    }
}

fn header_error(kind: HeaderError, span: Range<usize>) -> CircuitFormError {
    CircuitFormError::Header { kind, span }
}

verus! {

pub open spec fn head_spelling(head: Head) -> &'static str {
    match head {
        Head::Using => "using",
        Head::Namespace => "namespace",
        Head::Use => "use",
        Head::Export => "export",
        Head::Func => "func",
        Head::Module => "module",
        Head::ModulePart => "module-part",
        Head::Struct => "struct",
        Head::Latch => "latch",
        Head::Memory => "memory",
        Head::Test => "test",
    }
}

/// 元入力の綴りがフォームの先頭語と一致する名前アトムを判定する。
#[verifier::opaque]
pub open spec fn head_word_matches(source: &str, node: Form, head: Head) -> bool {
    let span = form_span(node);
    &&& node is Atom
    &&& node->Atom_kind == AtomKind::Name
    &&& source.spec_bytes()[span.start as int..span.end as int] == head_spelling(head).spec_bytes()
}

/// リストの最初の直接子が、現在の文脈に置ける先頭語であることを表す。
pub open spec fn form_has_head(
    source: &str, forms: Seq<Form>, index: int, in_namespace: bool, head: Head,
) -> bool {
    &&& 0 <= index < forms.len()
    &&& forms[index] is List
    &&& index + 1 < forms[index]->List_end <= forms.len()
    &&& head_word_matches(source, forms[index + 1], head)
    &&& head_in_context(head, in_namespace)
}

/// フォームの先頭語を検査した結果のエラー種別と、その診断範囲の根拠を表す。
pub open spec fn form_head_error_evidence(
    source: &str, forms: Seq<Form>, index: int, in_namespace: bool, kind: HeaderError, span: Range<usize>,
) -> bool {
    &&& 0 <= index < forms.len()
    &&& {
        let form = forms[index];
        let list_span = form_span(form);
        let child = forms[index + 1];
        let has_child = form is List && index + 1 < form->List_end <= forms.len();
        match kind {
            HeaderError::ExpectedList => !(form is List) && span == list_span,
            HeaderError::ExpectedHead => form is List && (
                (form->List_end == index + 1 && list_span.end > 0
                    && list_span.end <= source.spec_bytes().len()
                    && source.spec_bytes()[list_span.end - 1] == 41
                    && span.start == list_span.end - 1 && span.end == span.start)
                || (has_child && !(child is Atom && child->Atom_kind == AtomKind::Name)
                    && span == form_span(child))),
            HeaderError::UnknownHead => has_child && child is Atom && child->Atom_kind == AtomKind::Name
                && span == form_span(child)
                && (forall|head: Head| !#[trigger] head_word_matches(source, child, head)),
            HeaderError::MisplacedHead(head) => has_child && head_word_matches(source, child, head)
                && !head_in_context(head, in_namespace) && span == form_span(child),
            _ => false,
        }
    }
}

fn form_span_exec(form: &Form) -> (span: Range<usize>)
    ensures span == form_span(*form),
{
    match form {
        Form::Atom { span, .. } | Form::List { span, .. } => span.start..span.end,
    }
}

fn source_span(source: &str, start: usize, end: usize) -> (word: &str)
    requires
        start < end <= source.spec_bytes().len(),
        is_char_boundary(source.spec_bytes(), start as int),
        is_char_boundary(source.spec_bytes(), end as int),
    ensures word.spec_bytes() == source.spec_bytes()[start as int..end as int],
{
    let (prefix, _) = source.split_at(end);
    proof {
        encode_utf8_valid_utf8(source@);
        encode_utf8_valid_utf8(prefix@);
        assert(prefix.spec_bytes()[start as int] == source.spec_bytes()[start as int]);
        is_char_boundary_iff_not_is_continuation_byte(source.spec_bytes(), start as int);
        is_char_boundary_iff_not_is_continuation_byte(prefix.spec_bytes(), start as int);
    }
    let (_, word) = prefix.split_at(start);
    assert(word.spec_bytes() =~= source.spec_bytes()[start as int..end as int]);
    word
}

fn read_form_head(
    source: &str, forms: &[Form], index: usize, in_namespace: bool,
) -> (result: Result<(Head, usize, usize), (HeaderError, Range<usize>)>)
    requires
        index < forms@.len(),
        complete_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        list_source_delimiters(source, forms@, false),
    ensures
        forall|head: Head| #[trigger] form_has_head(source, forms@, index as int, in_namespace, head)
            <==> (result matches Ok((observed, _, _)) && observed == head),
        match result {
            Ok((_, end, closing)) => {
                &&& forms@[index as int] is List
                &&& end == forms@[index as int]->List_end
                &&& closing + 1 == form_span(forms@[index as int]).end
            },
            Err((kind, span)) => form_head_error_evidence(source, forms@, index as int, in_namespace, kind, span),
        },
{
    let form = &forms[index];
    let Form::List { span: list_span, end: list_end } = form else {
        return Err((HeaderError::ExpectedList, form_span_exec(form)));
    };
    let end = *list_end;
    let head_index = index + 1;
    assert(list_delimited(source.spec_bytes(), *form, false)) by {
        reveal(list_source_delimiters);
    };
    let closing = list_span.end - 1;
    if head_index == end {
        return Err((HeaderError::ExpectedHead, closing..closing));
    }
    let child = &forms[head_index];
    let Form::Atom { kind: AtomKind::Name, span: word_span } = child else {
        assert forall|head: Head| !#[trigger] head_word_matches(source, *child, head) by {
            reveal(head_word_matches);
        };
        return Err((HeaderError::ExpectedHead, form_span_exec(child)));
    };
    proof { encode_utf8_valid_utf8(source@); }
    assert(word_span.start < word_span.end <= source.spec_bytes().len()
        && is_char_boundary(source.spec_bytes(), word_span.start as int)
        && is_char_boundary(source.spec_bytes(), word_span.end as int)) by {
        reveal(form_spans_valid);
        assert(form_span(*child) == *word_span);
    };
    let word = source_span(source, word_span.start, word_span.end);
    let recognized = recognize_head(word);
    assert forall|head: Head| #[trigger] head_word_matches(source, *child, head)
        <==> recognized == Some(head) by {
        reveal(head_word_matches);
        assert(head_spelling(head).spec_bytes() == word.spec_bytes()
            <==> head_spelling(head)@ == word@) by {
            encode_utf8_decode_utf8(head_spelling(head)@);
            encode_utf8_decode_utf8(word@);
        };
        assert(word.spec_bytes() == source.spec_bytes()[word_span.start as int..word_span.end as int]);
        assert(head_spelling(head)@ == word@ <==> recognized == Some(head));
    };
    let Some(head) = recognized else {
        return Err((HeaderError::UnknownHead, word_span.start..word_span.end));
    };
    if !head_allowed(head, in_namespace) {
        return Err((HeaderError::MisplacedHead(head), word_span.start..word_span.end));
    }
    Ok((head, end, closing))
}

fn recognize_head(word: &str) -> (head: Option<Head>)
    ensures
        forall|candidate: Head| #[trigger] head_spelling(candidate)@ == word@
            <==> head == Some(candidate),
{
    let head = if word == "using" { Some(Head::Using) }
        else if word == "namespace" { Some(Head::Namespace) }
        else if word == "use" { Some(Head::Use) }
        else if word == "export" { Some(Head::Export) }
        else if word == "func" { Some(Head::Func) }
        else if word == "module" { Some(Head::Module) }
        else if word == "module-part" { Some(Head::ModulePart) }
        else if word == "struct" { Some(Head::Struct) }
        else if word == "latch" { Some(Head::Latch) }
        else if word == "memory" { Some(Head::Memory) }
        else if word == "test" { Some(Head::Test) }
        else { None };
    assert forall|candidate: Head| #[trigger] head_spelling(candidate)@ == word@
        <==> head == Some(candidate) by {
    };
    head
}

pub open spec fn head_in_context(head: Head, in_namespace: bool) -> bool {
    !in_namespace || !(head is Using || head is Namespace)
}

fn head_allowed(head: Head, in_namespace: bool) -> (allowed: bool)
    ensures allowed == head_in_context(head, in_namespace),
{
    !in_namespace || !matches!(head, Head::Using | Head::Namespace)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BodyHead {
    Def,
    Expand,
}

spec fn body_head_spelling(head: BodyHead) -> &'static str {
    match head {
        BodyHead::Def => "def",
        BodyHead::Expand => "expand",
    }
}

fn recognize_body_head(word: &str) -> (head: Option<BodyHead>)
    ensures
        forall|candidate: BodyHead| #[trigger] body_head_spelling(candidate)@ == word@
            <==> head == Some(candidate),
{
    if word == "def" {
        Some(BodyHead::Def)
    } else if word == "expand" {
        Some(BodyHead::Expand)
    } else {
        None
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExpressionHead {
    Bit,
    Slice,
    Concat,
    Field,
    As,
    Raw,
}

spec fn expression_head_spelling(head: ExpressionHead) -> &'static str {
    match head {
        ExpressionHead::Bit => "bit",
        ExpressionHead::Slice => "slice",
        ExpressionHead::Concat => "concat",
        ExpressionHead::Field => "field",
        ExpressionHead::As => "as",
        ExpressionHead::Raw => "raw",
    }
}

fn recognize_expression_head(word: &str) -> (head: Option<ExpressionHead>)
    ensures
        forall|candidate: ExpressionHead| #[trigger] expression_head_spelling(candidate)@ == word@
            <==> head == Some(candidate),
{
    let head = if word == "bit" { Some(ExpressionHead::Bit) }
        else if word == "slice" { Some(ExpressionHead::Slice) }
        else if word == "concat" { Some(ExpressionHead::Concat) }
        else if word == "field" { Some(ExpressionHead::Field) }
        else if word == "as" { Some(ExpressionHead::As) }
        else if word == "raw" { Some(ExpressionHead::Raw) }
        else { None };
    assert forall|candidate: ExpressionHead|
        #[trigger] expression_head_spelling(candidate)@ == word@
        <==> head == Some(candidate) by {
    };
    head
}

#[derive(Clone, Copy)]
enum TestHead {
    Case,
    Reset,
    Drive,
    Tick,
    Expect,
}

spec fn test_head_spelling(head: TestHead) -> &'static str {
    match head {
        TestHead::Case => "case",
        TestHead::Reset => "reset",
        TestHead::Drive => "drive",
        TestHead::Tick => "tick",
        TestHead::Expect => "expect",
    }
}

fn recognize_test_head(word: &str) -> (head: Option<TestHead>)
    ensures
        forall|candidate: TestHead| #[trigger] test_head_spelling(candidate)@ == word@
            <==> head == Some(candidate),
{
    let head = if word == "case" { Some(TestHead::Case) }
        else if word == "reset" { Some(TestHead::Reset) }
        else if word == "drive" { Some(TestHead::Drive) }
        else if word == "tick" { Some(TestHead::Tick) }
        else if word == "expect" { Some(TestHead::Expect) }
        else { None };
    assert forall|candidate: TestHead| #[trigger] test_head_spelling(candidate)@ == word@
        <==> head == Some(candidate) by {
    };
    head
}

fn same_test_item_kind(first: TestHead, next: TestHead) -> (same: bool)
    ensures same == ((first is Case) == (next is Case)),
{
    matches!(first, TestHead::Case) == matches!(next, TestHead::Case)
}

spec fn is_circuit_value(kind: AtomKind, word: &str) -> bool {
    kind is Binary || kind is Hexadecimal
        || (kind is Natural && (word@ == "0"@ || word@ == "1"@))
}

fn circuit_value(kind: AtomKind, word: &str) -> (accepted: bool)
    ensures accepted == is_circuit_value(kind, word),
{
    matches!(kind, AtomKind::Binary | AtomKind::Hexadecimal)
        || (matches!(kind, AtomKind::Natural) && (word == "0" || word == "1"))
}

spec fn is_expression_atom(kind: AtomKind, word: &str) -> bool {
    kind is Name || is_circuit_value(kind, word)
}

fn expression_atom(kind: AtomKind, word: &str) -> (accepted: bool)
    ensures accepted == is_expression_atom(kind, word),
{
    matches!(kind, AtomKind::Name) || circuit_value(kind, word)
}

spec fn is_test_atom(kind: AtomKind, word: &str, allow_any: bool) -> bool {
    is_circuit_value(kind, word) || (allow_any && kind is Name && word@ == "any"@)
}

fn test_atom(kind: AtomKind, word: &str, allow_any: bool) -> (accepted: bool)
    ensures accepted == is_test_atom(kind, word, allow_any),
{
    circuit_value(kind, word) || (allow_any && matches!(kind, AtomKind::Name) && word == "any")
}

} // verus!
