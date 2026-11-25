//! NCG2M の補助関数宣言から署名、仮引数の束縛、本体の位置を取り出す。

use alloc::vec::Vec;
use core::ops::Range;
use crate::syntax::{self, AtomKind, Form};
#[cfg(verus_only)]
use crate::syntax::{
    complete_list_indices, form_span, form_spans_valid, nested_list_indices, sexpr_form_model,
    strict_syntax_rejection, strict_token_errors_agree, structural_error_location,
    syntax_error_evidence, well_formed_sexpr,
};
use super::forms::{is_spelling, source_word, subtree_end};
#[cfg(verus_only)]
use super::forms::{spelling, subtree_limit};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// データ型の最も内側に書かれた名前の分類。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DataTypeName {
    /// 真偽値。
    Bool,
    /// 符号なし64ビット整数。
    Nat,
    /// 符号付き64ビット整数。
    Int,
    /// 名前を持つデータ。
    Symbol,
    /// 位置と束縛情報を持つ構文オブジェクト。
    Syntax,
    /// 実行段階が確定してから解決する型名。
    Deferred,
}

/// 宣言に書かれたデータ型。
///
/// 範囲は元ソースの UTF-8 半開バイト範囲。リストの入れ子は深さとして保持する。
#[derive(Debug, Eq, PartialEq)]
pub struct DataTypeSyntax {
    /// 型全体の範囲。
    pub span: Range<usize>,
    /// 最も内側にある型名の範囲。
    pub name_span: Range<usize>,
    /// 最も内側にある型名の分類。
    pub name: DataTypeName,
    /// 型名を包む `(List ...)` の数。単独の名前では0。
    pub list_depth: usize,
}

/// 署名の引数型と位置順に対応する仮引数。
#[derive(Debug, Eq, PartialEq)]
pub struct DefnParameter {
    /// 仮引数名の UTF-8 半開バイト範囲。
    pub name_span: Range<usize>,
    /// 同じ位置の引数型。
    pub ty: DataTypeSyntax,
}

/// 補助関数1個の宣言ヘッダー。
///
/// 範囲はすべて同じ UTF-8 ソースに対する半開バイト範囲。本体の範囲は後段の型検査で使う。
#[derive(Debug, Eq, PartialEq)]
pub struct DefnHeader {
    /// 宣言全体の範囲。
    pub span: Range<usize>,
    /// 宣言名の範囲。
    pub name_span: Range<usize>,
    /// 引数を宣言順に並べた列。
    pub parameters: Vec<DefnParameter>,
    /// 本体に要求する型。
    pub result_type: DataTypeSyntax,
    /// 本体を構成する1個の共通 S 式の範囲。
    /// NCG2M の式の文法に適合するか、その型が何かは後段で検査する。
    pub body_span: Range<usize>,
}

/// 宣言ヘッダーで求める構文上の部分。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DefnPart {
    /// `(defn name ...)` の形。
    Declaration,
    /// 1個の無修飾な宣言名。
    DeclarationName,
    /// `(as-type signature function)` の形。
    Annotation,
    /// `(Fn (ArgType ...) ResultType)` の形。
    Signature,
    /// 署名の引数型リスト。
    ArgumentTypes,
    /// `(fn (parameter ...) expr)` の形。
    Function,
    /// 関数リテラルの仮引数リスト。
    ParameterNames,
    /// 1個の無修飾な仮引数名。
    ParameterName,
    /// データ型名または `(List T)` の形。
    DataType,
}

/// 単独の補助関数宣言を検査できなかった理由。
///
/// 範囲は元ソースの UTF-8 半開バイト範囲。
#[derive(Debug, Eq, PartialEq)]
pub enum DefnHeaderError {
    /// 共通の字句または S 式解析の違反。
    Syntax(syntax::Error),
    /// 宣言がなければ入力末尾の空範囲、複数あれば2個目の S 式の範囲。
    ExpectedOneDeclaration(Range<usize>),
    /// その位置に必要な文法上の部分がなかった。
    Expected {
        /// 適合しなかった入力部分の範囲。
        span: Range<usize>,
        /// その位置に必要な形式。
        part: DefnPart,
    },
    /// 同じ仮引数名が同じ宣言に複数現れた。
    DuplicateParameter {
        /// 重複した仮引数名の範囲。
        duplicate: Range<usize>,
        /// 最初に現れた仮引数名の範囲。
        first: Range<usize>,
    },
    /// 引数型列と仮引数列を対応付けられない。
    ParameterCount {
        /// 署名に書かれた引数型リストの範囲。
        arguments: Range<usize>,
        /// 関数リテラルに書かれた仮引数リストの範囲。
        parameters: Range<usize>,
    },
}

spec fn usable_forms(source: &str, forms: Seq<Form>) -> bool {
    complete_list_indices(forms) && nested_list_indices(forms)
        && form_spans_valid(source, forms, source.spec_bytes().len() as int)
}

spec fn plain_name(form: Form) -> bool {
    form matches Form::Atom { kind: AtomKind::Name, .. }
}

fn is_name(form: &Form) -> (result: bool)
    ensures result == plain_name(*form),
{
    matches!(form, Form::Atom { kind: AtomKind::Name, .. })
}

fn span_of(form: &Form) -> (span: Range<usize>)
    ensures span == form_span(*form),
{
    match form {
        Form::Atom { span, .. } | Form::List { span, .. } => span.start..span.end,
    }
}

spec fn expected_at(forms: Seq<Form>, at: usize, part: DefnPart) -> DefnHeaderError {
    DefnHeaderError::Expected { span: form_span(forms[at as int]), part }
}

fn expected(forms: &[Form], at: usize, part: DefnPart) -> (error: DefnHeaderError)
    requires at < forms@.len(),
    ensures error == expected_at(forms@, at, part),
{
    DefnHeaderError::Expected { span: span_of(&forms[at]), part }
}

spec fn tagged_arguments(
    source: &str, forms: Seq<Form>, at: usize, tag: &str, has_second: bool,
) -> Option<(usize, usize)> {
    let end = subtree_limit(forms, at);
    let arg = (at + 2) as usize;
    let next = subtree_limit(forms, arg);
    if forms[at as int] is List && at + 2 < end <= forms.len()
        && plain_name(forms[at + 1]) && spelling(source, forms[at + 1]) == tag.spec_bytes()
        && arg < next <= end
        && (if has_second { next < end && subtree_limit(forms, next) == end } else { next == end })
    {
        Some((arg, next))
    } else {
        None
    }
}

fn tagged(
    source: &str, forms: &[Form], at: usize, tag: &str, has_second: bool,
) -> (result: Option<(usize, usize)>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures result == tagged_arguments(source, forms@, at, tag, has_second),
{
    let Form::List { end: list_end, .. } = &forms[at] else { return None; };
    let end = *list_end;
    assert(at < end <= forms@.len());
    if end - at <= 2 { return None; }
    let head = at + 1;
    if !is_name(&forms[head]) || !is_spelling(source_word(source, forms, head), tag) {
        return None;
    }
    let arg = at + 2;
    let next = subtree_end(forms, arg);
    if next <= arg || next > end { return None; }
    if has_second {
        if next == end || subtree_end(forms, next) != end { return None; }
    } else if next != end {
        return None;
    }
    Some((arg, next))
}

spec fn data_name(word: Seq<u8>) -> Option<DataTypeName> {
    if word == "Bool".spec_bytes() { Some(DataTypeName::Bool) }
    else if word == "Nat".spec_bytes() { Some(DataTypeName::Nat) }
    else if word == "Int".spec_bytes() { Some(DataTypeName::Int) }
    else if word == "Symbol".spec_bytes() { Some(DataTypeName::Symbol) }
    else if word == "Syntax".spec_bytes() { Some(DataTypeName::Syntax) }
    else if word == "Fn".spec_bytes() || word == "List".spec_bytes() { None }
    else { Some(DataTypeName::Deferred) }
}

fn read_data_name(word: &str) -> (name: Option<DataTypeName>)
    ensures name == data_name(word.spec_bytes()),
{
    if is_spelling(word, "Bool") { Some(DataTypeName::Bool) }
    else if is_spelling(word, "Nat") { Some(DataTypeName::Nat) }
    else if is_spelling(word, "Int") { Some(DataTypeName::Int) }
    else if is_spelling(word, "Symbol") { Some(DataTypeName::Symbol) }
    else if is_spelling(word, "Syntax") { Some(DataTypeName::Syntax) }
    else if is_spelling(word, "Fn") || is_spelling(word, "List") { None }
    else { Some(DataTypeName::Deferred) }
}

// リスト型の引数は1個なので、型名とリスト型の入れ子の深さで型の形を表せる。
spec fn type_at(
    source: &str, forms: Seq<Form>, root: usize, at: usize, depth: usize,
) -> Result<DataTypeSyntax, DefnHeaderError>
    decreases forms.len() - at,
{
    let bad = Err(expected_at(forms, at, DefnPart::DataType));
    if at >= forms.len() {
        bad
    } else if plain_name(forms[at as int]) {
        match data_name(spelling(source, forms[at as int])) {
            Some(name) => Ok(DataTypeSyntax {
                span: form_span(forms[root as int]),
                name_span: form_span(forms[at as int]),
                name,
                list_depth: depth,
            }),
            None => bad,
        }
    } else {
        match tagged_arguments(source, forms, at, "List", false) {
            Some((arg, _)) if at < arg < forms.len() && depth < usize::MAX =>
                type_at(source, forms, root, arg, (depth + 1) as usize),
            _ => bad,
        }
    }
}

fn read_type(source: &str, forms: &[Form], root: usize) -> (result: Result<DataTypeSyntax, DefnHeaderError>)
    requires usable_forms(source, forms@), root < forms@.len(),
    ensures result == type_at(source, forms@, root, root, 0),
{
    let mut at = root;
    let mut depth = 0;
    loop
        invariant
            usable_forms(source, forms@),
            root <= at < forms@.len(),
            depth <= at - root,
            type_at(source, forms@, root, root, 0) == type_at(source, forms@, root, at, depth),
        decreases forms@.len() - at,
    {
        reveal_with_fuel(type_at, 2);
        if is_name(&forms[at]) {
            let Some(name) = read_data_name(source_word(source, forms, at)) else {
                return Err(expected(forms, at, DefnPart::DataType));
            };
            return Ok(DataTypeSyntax {
                span: span_of(&forms[root]),
                name_span: span_of(&forms[at]),
                name,
                list_depth: depth,
            });
        }
        let Some((child, _)) = tagged(source, forms, at, "List", false) else {
            return Err(expected(forms, at, DefnPart::DataType));
        };
        at = child;
        depth += 1;
    }
}

// ヘッダー内に入れ子の子があっても、それぞれの直下だけを数える。
spec fn sites_model(source: &str, forms: Seq<Form>) -> Result<(usize, usize, usize, usize, usize), DefnHeaderError> {
    let declaration = tagged_arguments(source, forms, 0, "defn", true);
    if declaration.is_none() {
        Err(expected_at(forms, 0, DefnPart::Declaration))
    } else {
        let (name, annotation) = declaration->Some_0;
        if !plain_name(forms[name as int]) {
            Err(expected_at(forms, name, DefnPart::DeclarationName))
        } else {
            match tagged_arguments(source, forms, annotation, "as-type", true) {
                None => Err(expected_at(forms, annotation, DefnPart::Annotation)),
                Some((signature, function)) => match tagged_arguments(source, forms, signature, "Fn", true) {
                    None => Err(expected_at(forms, signature, DefnPart::Signature)),
                    Some((types, output)) if !(forms[types as int] is List) =>
                        Err(expected_at(forms, types, DefnPart::ArgumentTypes)),
                    Some((types, output)) => match tagged_arguments(source, forms, function, "fn", true) {
                        None => Err(expected_at(forms, function, DefnPart::Function)),
                        Some((names, body)) if !(forms[names as int] is List) =>
                            Err(expected_at(forms, names, DefnPart::ParameterNames)),
                        Some((names, body)) => Ok((name, types, output, names, body)),
                    },
                },
            }
        }
    }
}

fn header_sites(source: &str, forms: &[Form]) -> (result: Result<(usize, usize, usize, usize, usize), DefnHeaderError>)
    requires usable_forms(source, forms@), forms@.len() > 0,
    ensures
        result == sites_model(source, forms@),
        result matches Ok((name, types, output, names, body))
            ==> name < forms@.len() && types < forms@.len() && output < forms@.len()
                && names < forms@.len() && body < forms@.len()
                && forms@[types as int] is List && forms@[names as int] is List,
{
    let Some((name, declaration)) = tagged(source, forms, 0, "defn", true) else {
        return Err(expected(forms, 0, DefnPart::Declaration));
    };
    if !is_name(&forms[name]) {
        return Err(expected(forms, name, DefnPart::DeclarationName));
    }
    let Some((signature, function)) = tagged(source, forms, declaration, "as-type", true) else {
        return Err(expected(forms, declaration, DefnPart::Annotation));
    };
    let Some((types, output)) = tagged(source, forms, signature, "Fn", true) else {
        return Err(expected(forms, signature, DefnPart::Signature));
    };
    if !matches!(&forms[types], Form::List { .. }) {
        return Err(expected(forms, types, DefnPart::ArgumentTypes));
    }
    let Some((names, body)) = tagged(source, forms, function, "fn", true) else {
        return Err(expected(forms, function, DefnPart::Function));
    };
    if !matches!(&forms[names], Form::List { .. }) {
        return Err(expected(forms, names, DefnPart::ParameterNames));
    }
    Ok((name, types, output, names, body))
}


spec fn span_bytes(source: &str, span: Range<usize>) -> Seq<u8> {
    source.spec_bytes()[span.start as int..span.end as int]
}

spec fn readable_span(source: &str, span: Range<usize>) -> bool {
    let bytes = source.spec_bytes();
    span.start < span.end <= bytes.len()
        && vstd::utf8::is_char_boundary(bytes, span.start as int)
        && vstd::utf8::is_char_boundary(bytes, span.end as int)
}

proof fn form_span_readable(source: &str, forms: Seq<Form>, at: usize)
    requires usable_forms(source, forms), at < forms.len(),
    ensures readable_span(source, form_span(forms[at as int])),
{
    reveal(form_spans_valid);
}

spec fn earlier_parameter(
    source: &str, prior: Seq<DefnParameter>, from: nat, name: Range<usize>,
) -> Option<Range<usize>>
    decreases prior.len() - from,
{
    if from >= prior.len() {
        None
    } else {
        let earlier = prior[from as int].name_span;
        if span_bytes(source, earlier) == span_bytes(source, name) {
            Some(earlier)
        } else {
            earlier_parameter(source, prior, from + 1, name)
        }
    }
}

fn first_duplicate(source: &str, prior: &[DefnParameter], name: &Range<usize>) -> (result: Option<Range<usize>>)
    requires
        readable_span(source, *name),
        forall|i: int| 0 <= i < prior@.len() ==> readable_span(source, #[trigger] prior@[i].name_span),
    ensures result == earlier_parameter(source, prior@, 0, *name),
{
    let word = crate::project::read_source_span(source, name.start, name.end);
    let mut from = 0;
    while from < prior.len()
        invariant
            from <= prior@.len(),
            word.spec_bytes() == span_bytes(source, *name),
            forall|i: int| 0 <= i < prior@.len() ==> readable_span(source, #[trigger] prior@[i].name_span),
            earlier_parameter(source, prior@, 0, *name) == earlier_parameter(source, prior@, from as nat, *name),
        decreases prior@.len() - from,
    {
        reveal_with_fuel(earlier_parameter, 2);
        let span = &prior[from].name_span;
        let earlier = crate::project::read_source_span(source, span.start, span.end);
        if is_spelling(earlier, word) {
            return Some(span.start..span.end);
        }
        from += 1;
    }
    None
}

spec fn count_error(forms: Seq<Form>, lists: (usize, usize)) -> DefnHeaderError {
    DefnHeaderError::ParameterCount {
        arguments: form_span(forms[lists.0 as int]),
        parameters: form_span(forms[lists.1 as int]),
    }
}

spec fn parameter_model(
    source: &str, forms: Seq<Form>, lists: (usize, usize),
    type_index: usize, name_index: usize, prior: Seq<DefnParameter>,
) -> Result<Seq<DefnParameter>, DefnHeaderError>
    decreases subtree_limit(forms, lists.0) - type_index,
{
    let types_end = subtree_limit(forms, lists.0);
    let names_end = subtree_limit(forms, lists.1);
    if type_index == types_end && name_index == names_end {
        Ok(prior)
    } else if type_index >= types_end || name_index >= names_end {
        Err(count_error(forms, lists))
    } else {
        match type_at(source, forms, type_index, type_index, 0) {
            Err(error) => Err(error),
            Ok(ty) => {
                if !plain_name(forms[name_index as int]) {
                    Err(expected_at(forms, name_index, DefnPart::ParameterName))
                } else {
                    let name_span = form_span(forms[name_index as int]);
                    match earlier_parameter(source, prior, 0, name_span) {
                        Some(first) => Err(DefnHeaderError::DuplicateParameter { duplicate: name_span, first }),
                        None => {
                            let next = subtree_limit(forms, type_index);
                            if type_index < next <= types_end {
                                parameter_model(source, forms, lists, next, (name_index + 1) as usize,
                                    prior.push(DefnParameter { name_span, ty }))
                            } else {
                                Err(count_error(forms, lists))
                            }
                        }
                    }
                }
            }
        }
    }
}

proof fn child_stays_inside(forms: Seq<Form>, parent: usize, child: usize)
    requires
        complete_list_indices(forms), nested_list_indices(forms),
        parent < child < subtree_limit(forms, parent) <= forms.len(),
        forms[parent as int] is List,
    ensures child < subtree_limit(forms, child) <= subtree_limit(forms, parent),
{
    reveal(nested_list_indices);
    assert(forms[parent as int] is List);
    if forms[child as int] is List {
        assert(forms[child as int] is List);
    }
}

spec fn collected_parameters(
    result: Result<Vec<DefnParameter>, DefnHeaderError>,
) -> Result<Seq<DefnParameter>, DefnHeaderError> {
    match result {
        Ok(parameters) => Ok(parameters@),
        Err(error) => Err(error),
    }
}

fn read_parameters(source: &str, forms: &[Form], lists: (usize, usize))
    -> (result: Result<Vec<DefnParameter>, DefnHeaderError>)
    requires
        usable_forms(source, forms@),
        lists.0 < forms@.len(),
        lists.1 < forms@.len(),
        forms@[lists.0 as int] is List,
        forms@[lists.1 as int] is List,
    ensures collected_parameters(result) == parameter_model(
        source, forms@, lists, (lists.0 + 1) as usize, (lists.1 + 1) as usize, Seq::empty(),
    ),
{
    let types_end = subtree_end(forms, lists.0);
    let names_end = subtree_end(forms, lists.1);
    assert(lists.0 < types_end <= forms@.len());
    assert(lists.1 < names_end <= forms@.len());
    let mut type_index = lists.0 + 1;
    let mut name_index = lists.1 + 1;
    let mut prior = Vec::<DefnParameter>::new();
    loop
        invariant
            usable_forms(source, forms@),
            forms@[lists.0 as int] is List,
            lists.0 < type_index <= types_end <= forms@.len(),
            lists.1 < name_index <= names_end <= forms@.len(),
            types_end == subtree_limit(forms@, lists.0),
            names_end == subtree_limit(forms@, lists.1),
            forall|i: int| 0 <= i < prior@.len() ==> readable_span(source, #[trigger] prior@[i].name_span),
            parameter_model(source, forms@, lists, (lists.0 + 1) as usize, (lists.1 + 1) as usize, Seq::empty())
                == parameter_model(source, forms@, lists, type_index, name_index, prior@),
        decreases types_end - type_index,
    {
        reveal_with_fuel(parameter_model, 2);
        if type_index == types_end && name_index == names_end {
            return Ok(prior);
        }
        if type_index == types_end || name_index == names_end {
            return Err(DefnHeaderError::ParameterCount {
                arguments: span_of(&forms[lists.0]),
                parameters: span_of(&forms[lists.1]),
            });
        }
        let ty = read_type(source, forms, type_index)?;
        if !is_name(&forms[name_index]) {
            return Err(expected(forms, name_index, DefnPart::ParameterName));
        }
        proof { form_span_readable(source, forms@, name_index); }
        let name_span = span_of(&forms[name_index]);
        if let Some(first) = first_duplicate(source, &prior, &name_span) {
            return Err(DefnHeaderError::DuplicateParameter { duplicate: name_span, first });
        }
        let next = subtree_end(forms, type_index);
        proof { child_stays_inside(forms@, lists.0, type_index); }
        prior.push(DefnParameter { name_span, ty });
        type_index = next;
        name_index += 1;
    }
}

#[cfg(verus_only)]
type HeaderContents = (Range<usize>, Range<usize>, Seq<DefnParameter>, DataTypeSyntax, Range<usize>);

spec fn header_contents(header: DefnHeader) -> HeaderContents {
    (header.span, header.name_span, header.parameters@, header.result_type, header.body_span)
}

// 共通 S 式が消費した入力から、ヘッダーが表す宣言を位置付きで定める。
spec fn header_model(source: &str, forms: Seq<Form>) -> Result<HeaderContents, DefnHeaderError> {
    if forms.len() == 0 {
        let end = source.spec_bytes().len() as usize;
        Err(DefnHeaderError::ExpectedOneDeclaration(end..end))
    } else if subtree_limit(forms, 0) != forms.len() {
        let extra = subtree_limit(forms, 0);
        Err(DefnHeaderError::ExpectedOneDeclaration(form_span(forms[extra as int])))
    } else {
        match sites_model(source, forms) {
            Err(error) => Err(error),
            Ok((name, types, output, names, body)) => {
                match parameter_model(source, forms, (types, names), (types + 1) as usize, (names + 1) as usize, Seq::empty()) {
                    Err(error) => Err(error),
                    Ok(parameters) => match type_at(source, forms, output, output, 0) {
                        Err(error) => Err(error),
                        Ok(result_type) => Ok((form_span(forms[0]), form_span(forms[name as int]),
                            parameters, result_type, form_span(forms[body as int]))),
                    },
                }
            }
        }
    }
}

/// 補助関数のヘッダーが単独の宣言として文法を満たすことを表す。
///
/// 未解決の型名や本体は、ヘッダーを検査した段階では受理する。
pub closed spec fn valid_defn_header(source: &str) -> bool {
    well_formed_sexpr(source) && (sexpr_form_model(source) matches Some(forms)
        && header_model(source, forms).is_ok())
}

/// 厳格なヘッダー検査の結果と元ソースが対応することを表す。
///
/// S 式が妥当なら、署名と本体の位置、または規定順の最初のヘッダーエラーが一意に決まる。
pub closed spec fn defn_header_matches(source: &str, result: Result<DefnHeader, DefnHeaderError>) -> bool {
    if !well_formed_sexpr(source) {
        result matches Err(DefnHeaderError::Syntax(error)) && strict_syntax_rejection(source, error)
            && syntax_error_evidence(source, error)
    } else {
        sexpr_form_model(source) matches Some(forms) && match result {
            Ok(header) => header_model(source, forms) == Ok(header_contents(header)),
            Err(error) => header_model(source, forms) == Err(error),
        }
    }
}


/// 同じソースを検査した結果は、宣言の各項目またはエラー全体が一致する。
pub proof fn defn_headers_agree(
    source: &str, left: Result<DefnHeader, DefnHeaderError>, right: Result<DefnHeader, DefnHeaderError>,
)
    requires defn_header_matches(source, left), defn_header_matches(source, right),
    ensures
        match (left, right) {
            (Ok(a), Ok(b)) => a.span == b.span && a.name_span == b.name_span
                && a.parameters@ == b.parameters@ && a.result_type == b.result_type && a.body_span == b.body_span,
            (Err(a), Err(b)) => a == b,
            _ => false,
        },
{
    if !well_formed_sexpr(source) {
        let a = left->Err_0->Syntax_0;
        let b = right->Err_0->Syntax_0;
        reveal(syntax_error_evidence);
        assert(structural_error_location(source, a) && structural_error_location(source, b));
        strict_token_errors_agree(source, a, b);
    }
}
/// 単独の `defn` 宣言を検査し、署名、引数の束縛、本体の位置を取り出す。
///
/// `(List T)` の入れ子に深さの制限はない。追加の型名は元ソース上の位置を保ち、実行段階ごとの型検査に渡す。
///
/// # Errors
///
/// 字句と S 式、単一宣言の外形、引数列、戻り値型の順に検査する。引数列では前から対応を取り、
/// 各位置で引数型、仮引数名、重複の順に検査する。途中で片方の列が尽きたときは個数の違いを返す。
///
/// # Examples
///
/// ```
/// use circuitgame2_core::ncg2m::defn::{DataTypeName, parse_defn_header};
///
/// let source = "(defn tally (as-type (Fn ((List Event)) Nat) (fn (events) (count events))))";
/// let header = parse_defn_header(source)?;
/// assert_eq!(header.parameters[0].ty.name, DataTypeName::Deferred);
/// assert_eq!(header.parameters[0].ty.list_depth, 1);
/// assert_eq!(&source[header.parameters[0].ty.name_span.clone()], "Event");
/// assert_eq!(&source[header.body_span], "(count events)");
/// # Ok::<(), circuitgame2_core::ncg2m::defn::DefnHeaderError>(())
/// ```
pub fn parse_defn_header(source: &str) -> (result: Result<DefnHeader, DefnHeaderError>)
    ensures result.is_ok() == valid_defn_header(source), defn_header_matches(source, result),
{
    let forms = match syntax::parse(source) {
        Ok(forms) => forms,
        Err(error) => return Err(DefnHeaderError::Syntax(error)),
    };
    if forms.is_empty() {
        let end = source.len();
        return Err(DefnHeaderError::ExpectedOneDeclaration(end..end));
    }
    let limit = subtree_end(&forms, 0);
    assert(0 < limit <= forms@.len());
    if limit < forms.len() {
        return Err(DefnHeaderError::ExpectedOneDeclaration(span_of(&forms[limit])));
    }

    let (name, types, output, names, body) = header_sites(source, &forms)?;
    let parameters = read_parameters(source, &forms, (types, names))?;
    let result_type = read_type(source, &forms, output)?;
    Ok(DefnHeader {
        span: span_of(&forms[0]),
        name_span: span_of(&forms[name]),
        parameters,
        result_type,
        body_span: span_of(&forms[body]),
    })
}

}
