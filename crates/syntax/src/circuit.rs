//! S 式を回路文法に照らして検査し、宣言の位置を取り出す。

use crate::{AtomKind, Error, Form, parse};
#[cfg(verus_only)]
use crate::{
    complete_list_indices, form_span, form_spans_valid, list_delimited, list_source_delimiters,
    nested_list_indices,
};
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;

mod body;
mod clauses;
mod expression_forest;
mod expressions;
mod index;
mod names;
mod ports;
mod structure;
mod test_items;
mod test_values;
use body::validate_routine_arguments;
pub use expression_forest::{
    ExpressionReference, ExpressionReferenceKind, index_expression_references,
};
#[cfg(verus_only)]
pub use expression_forest::{expression_reference_in_source, expression_source_reference_result};
pub use index::index_headers;
#[cfg(verus_only)]
pub use index::{
    circuit_index_matches, circuit_source_error, circuit_source_matches, export_entry_evidence,
    indexed_location, use_entry_evidence,
};
pub use names::{NameSite, NamedCircuit, NamedForm, index_named_forms};
#[cfg(verus_only)]
pub use names::{name_site_matches, named_form_matches, named_forms_match, named_head};
#[cfg(verus_only)]
pub use ports::{
    port_error_evidence, port_matches, ports_clause_matches, ports_error_evidence,
    routine_signature_error_evidence, routine_signature_matches,
};
use structure::validate_structure_arguments;
#[cfg(verus_only)]
pub use structure::{
    field_error_evidence, field_matches, structure_arguments_match, structure_error_evidence,
};

#[cfg(verus_only)]
pub use clauses::{
    clause_fits_region, clause_spelling, clause_word_matches, named_clause_error_span,
    named_clause_matches, natural_argument_at, natural_clause_error_evidence,
    natural_clause_matches, reference_atom, storage_arguments_match, storage_error_evidence,
    type_error_evidence, type_matches,
};
use clauses::{is_reference, validate_storage_arguments};
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

/// 回路フォームと、それを含む名前空間の位置。
#[verifier::allow(autoderive_clone_without_spec)]
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
#[verifier::allow(autoderive_clone_without_spec)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CircuitForms {
    /// S 式の全要素を先行順に並べた構文木。
    pub forms: Vec<Form>,
    /// トップレベルのフォームと名前空間の直下にあるフォームを元入力順に並べた索引。
    pub entries: Vec<Entry>,
}

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

/// S 式解析または回路フォームの構文検査で失敗した理由。
#[verifier::allow(autoderive_clone_without_spec)]
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

/// 宣言の種類ごとに、先頭語に続く引数と本文の文法を定める。
///
/// 名前空間の直下にあるフォームは、索引を作るときに個別に調べる。
pub closed spec fn header_arguments_match(
    source: &str, forms: Seq<Form>, first: int, end: int, head: Head,
) -> bool {
    match head {
        Head::Using | Head::Namespace | Head::Use | Head::Export =>
            directive_arguments_match(source, forms, first, end, head),
        Head::Struct => structure_arguments_match(source, forms, first, end),
        Head::Test => test_items::test_arguments_match(source, forms, first, end),
        Head::Func | Head::Module | Head::ModulePart => body::routine_arguments_match(source, forms, first, end, head),
        Head::Latch | Head::Memory => directive_word_at(source, forms, first, end, HeaderError::ExpectedName)
            && storage_arguments_match(source, forms, first + 1, end, head),
    }
}

/// 宣言の先頭語を認識した後の、最初の引数または本文の違反を表す。
pub closed spec fn header_arguments_error(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, head: Head,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    match head {
        Head::Using | Head::Namespace | Head::Use | Head::Export =>
            directive_error_evidence(source, forms, first, end, closing, head, kind, span),
        Head::Struct => structure_error_evidence(source, forms, first, end, closing, kind, span),
        Head::Test => test_items::test_arguments_error(source, forms, first, end, closing, (kind, span)),
        Head::Func | Head::Module | Head::ModulePart =>
            body::routine_arguments_error(source, forms, first, end, closing, head, (kind, span)),
        Head::Latch | Head::Memory => {
            if directive_word_at(source, forms, first, end, HeaderError::ExpectedName) {
                storage_error_evidence(source, forms, first + 1, end, closing, head, kind, span)
            } else {
                kind == HeaderError::ExpectedName && directive_argument_error_span(forms, first, end, closing, span)
            }
        },
    }
}

/// フォームの先頭語、配置文脈、引数と本文が文法に従うことを表す。
pub open spec fn header_matches(
    source: &str, forms: Seq<Form>, index: int, in_namespace: bool, head: Head,
) -> bool {
    form_has_head(source, forms, index, in_namespace, head)
        && header_arguments_match(source, forms, index + 2, forms[index]->List_end as int, head)
}

/// 先頭語や配置の違反を先に調べ、続いて引数や本文の違反の根拠を与える。
pub open spec fn header_error_evidence(
    source: &str, forms: Seq<Form>, index: int, in_namespace: bool, kind: HeaderError, span: Range<usize>,
) -> bool {
    form_head_error_evidence(source, forms, index, in_namespace, kind, span)
    || (exists|head: Head| #[trigger] form_has_head(source, forms, index, in_namespace, head)
        && form_span(forms[index]).end > 0
        && header_arguments_error(source, forms, index + 2, forms[index]->List_end as int,
            (form_span(forms[index]).end - 1) as usize, head, kind, span))
}

/// 一つの回路フォームを検査し、種別と次の直接兄弟の添字を返す。
///
/// # Errors
///
/// 先頭語と配置を検査し、続いて引数と本文の最初の違反を返す。
fn read_header(
    source: &str, forms: &[Form], index: usize, in_namespace: bool,
) -> (result: Result<(Head, usize), (HeaderError, Range<usize>)>)
    requires
        index < forms@.len(),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        list_source_delimiters(source, forms@, false),
    ensures
        forall|head: Head| #[trigger] header_matches(source, forms@, index as int, in_namespace, head)
            <==> (result matches Ok((actual, _)) && actual == head),
        match result {
            Ok((head, next)) => {
                &&& forms@[index as int] is List
                &&& next == forms@[index as int]->List_end
                &&& index < next <= forms@.len()
                &&& following_direct_form(forms@, index as int, next as int)
                &&& (forall|candidate: Head| #[trigger] form_has_head(source, forms@, index as int, in_namespace, candidate)
                    <==> candidate == head)
                &&& head == Head::Namespace ==> (index + 3 <= next
                    && forms@[index + 1] is Atom && forms@[index + 2] is Atom)
            },
            Err((kind, span)) => header_error_evidence(source, forms@, index as int, in_namespace, kind, span),
        },
{
    let (head, end, closing) = read_form_head(source, forms, index, in_namespace)?;
    assert(form_has_head(source, forms@, index as int, in_namespace, head));
    let first = index + 2;
    assert(form_region_ends_at(forms@, first as int, end as int));
    proof {
        reveal(list_source_delimiters);
        assert(list_delimited(source.spec_bytes(), forms@[index as int], false));
    }
    let checked = match head {
        Head::Using | Head::Namespace | Head::Use | Head::Export => validate_directive(source, forms, first, end, closing, head),
        Head::Struct => validate_structure_arguments(source, forms, first, end, closing),
        Head::Test => test_items::validate_test_arguments(source, forms, first, end, closing),
        Head::Func | Head::Module | Head::ModulePart => validate_routine_arguments(source, forms, first, end, closing, head),
        Head::Latch | Head::Memory => {
            check_directive_word(source, forms, first, end, closing, HeaderError::ExpectedName)?;
            assert(form_region_ends_at(forms@, first + 1, end as int));
            validate_storage_arguments(source, forms, first + 1, end, closing, head)
        },
    };
    assert(checked.is_ok() <==> header_arguments_match(source, forms@, first as int, end as int, head));
    checked?;
    if matches!(head, Head::Namespace) {
        proof { reveal(head_word_matches); }
    }
    Ok((head, end))
}

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

/// 区間内で、先行するリストの部分木に属さないフォームの位置を表す。
#[verifier::opaque]
pub open spec fn direct_form_in_range(forms: Seq<Form>, start: int, limit: int, index: int) -> bool {
    &&& 0 <= start <= index < limit <= forms.len()
    &&& forall|earlier: int| start <= earlier < index && #[trigger] forms[earlier] is List
        ==> forms[earlier]->List_end <= index
}

/// 構文木全体または、走査開始位置を囲むリストの末尾を表す。
pub open spec fn form_region_ends_at(forms: Seq<Form>, first: int, limit: int) -> bool {
    limit == forms.len() || exists|parent: int| 0 <= parent < first
        && #[trigger] forms[parent] is List && forms[parent]->List_end == limit
}

/// 現在のフォームと次の直接子の間に、他の直接子がないことを表す。
///
/// `next` が区間末尾に等しければ、次の直接子は存在しない。
#[verifier::opaque]
pub open spec fn following_direct_form(forms: Seq<Form>, index: int, next: int) -> bool {
    forall|first: int, limit: int| #[trigger] direct_form_in_range(forms, first, limit, index)
        && form_region_ends_at(forms, first, limit) ==> {
        &&& index < next <= limit
        &&& (next < limit ==> direct_form_in_range(forms, first, limit, next))
        &&& forall|skipped: int| index < skipped < next
            ==> !#[trigger] direct_form_in_range(forms, first, limit, skipped)
    }
}

proof fn node_end_is_following_direct_form(forms: Seq<Form>, index: int, next: int)
    requires
        0 <= index < next <= forms.len(),
        if forms[index] is List { forms[index]->List_end == next } else { next == index + 1 },
        nested_list_indices(forms),
    ensures following_direct_form(forms, index, next),
{
    reveal(following_direct_form);
    assert forall|first: int, limit: int| #[trigger] direct_form_in_range(forms, first, limit, index)
        && form_region_ends_at(forms, first, limit) implies {
        &&& index < next <= limit
        &&& (next < limit ==> direct_form_in_range(forms, first, limit, next))
        &&& forall|skipped: int| index < skipped < next
            ==> !#[trigger] direct_form_in_range(forms, first, limit, skipped)
    } by {
        reveal(direct_form_in_range);
        reveal(nested_list_indices);
        if limit < forms.len() && forms[index] is List {
            let parent = choose|parent: int| 0 <= parent < first
                && #[trigger] forms[parent] is List && forms[parent]->List_end == limit;
            assert(parent < index < forms[parent]->List_end);
            assert(next <= limit);
        }
        if next < limit {
            assert forall|earlier: int| first <= earlier < next && #[trigger] forms[earlier] is List
                implies forms[earlier]->List_end <= next by {
                if earlier < index {
                    assert(forms[earlier]->List_end <= index);
                } else if earlier > index {
                    assert(index + 1 < next);
                    assert(forms[index] is List && earlier < forms[index]->List_end);
                }
            };
        }
        assert forall|skipped: int| index < skipped < next
            implies !#[trigger] direct_form_in_range(forms, first, limit, skipped) by {
            reveal(direct_form_in_range);
            assert(first <= index < skipped);
            assert(index + 1 < next);
            assert(forms[index] is List && forms[index]->List_end > skipped);
        };
    };
}

fn read_form_head(
    source: &str, forms: &[Form], index: usize, in_namespace: bool,
) -> (result: Result<(Head, usize, usize), (HeaderError, Range<usize>)>)
    requires
        index < forms@.len(),
        complete_list_indices(forms@),
        nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        list_source_delimiters(source, forms@, false),
    ensures
        forall|head: Head| #[trigger] form_has_head(source, forms@, index as int, in_namespace, head)
            <==> (result matches Ok((observed, _, _)) && observed == head),
        match result {
            Ok((_, end, closing)) => {
                &&& forms@[index as int] is List
                &&& end == forms@[index as int]->List_end
                &&& following_direct_form(forms@, index as int, end as int)
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
    proof { node_end_is_following_direct_form(forms@, index as int, end as int); }
    Ok((head, end, closing))
}

/// 対象フォームの引数に許される字句種別と綴りを表す。
pub open spec fn directive_word_matches(source: &str, form: Form, expected: HeaderError) -> bool {
    let span = form_span(form);
    &&& form is Atom
    &&& match expected {
        HeaderError::ExpectedNor => form->Atom_kind == AtomKind::Name
            && source.spec_bytes()[span.start as int..span.end as int] == "nor".spec_bytes(),
        HeaderError::ExpectedNamespacePath =>
            form->Atom_kind == AtomKind::Name || form->Atom_kind == AtomKind::RelativePath,
        HeaderError::ExpectedAbsolutePath => form->Atom_kind == AtomKind::AbsolutePath,
        HeaderError::ExpectedName => form->Atom_kind == AtomKind::Name,
        _ => false,
    }
}

/// フォームの引数の範囲内に、指定された字句があることを表す。
pub open spec fn directive_word_at(
    source: &str, forms: Seq<Form>, index: int, end: int, expected: HeaderError,
) -> bool {
    0 <= index < end <= forms.len() && directive_word_matches(source, forms[index], expected)
}

/// 基底・別名・公開名の引数列と、名前空間の先頭パスの構文を定める。名前空間の配下は別の走査で検査する。
pub open spec fn directive_arguments_match(
    source: &str, forms: Seq<Form>, first: int, end: int, head: Head,
) -> bool {
    let name = HeaderError::ExpectedName;
    match head {
        Head::Using => end == first + 1
            && directive_word_at(source, forms, first, end, HeaderError::ExpectedNor),
        Head::Namespace => directive_word_at(source, forms, first, end, HeaderError::ExpectedNamespacePath),
        Head::Use => end == first + 2
            && directive_word_at(source, forms, first, end, HeaderError::ExpectedAbsolutePath)
            && directive_word_at(source, forms, first + 1, end, name),
        Head::Export => first < end && (forall|i: int| first <= i < end
            ==> #[trigger] directive_word_at(source, forms, i, end, name)),
        _ => false,
    }
}

/// 引数があればその範囲、引数が欠けていれば閉じ括弧上の長さ0の範囲を表す。
pub open spec fn directive_argument_error_span(
    forms: Seq<Form>, index: int, end: int, closing: usize, span: Range<usize>,
) -> bool {
    if index == end {
        span.start == closing && span.end == closing
    } else {
        0 <= index < end <= forms.len() && span == form_span(forms[index])
    }
}

/// 対象フォームの引数を順に検査したとき、最初の違反が診断の種別と範囲に対応することを表す。
pub open spec fn directive_error_evidence(
    source: &str, forms: Seq<Form>, first: int, end: int, closing: usize, head: Head,
    kind: HeaderError, span: Range<usize>,
) -> bool {
    let nor = HeaderError::ExpectedNor;
    let path = HeaderError::ExpectedAbsolutePath;
    let name = HeaderError::ExpectedName;
    let namespace_path = HeaderError::ExpectedNamespacePath;
    &&& closing < source.spec_bytes().len()
    &&& source.spec_bytes()[closing as int] == 41
    &&& match head {
        Head::Using =>
            (kind == nor && !directive_word_at(source, forms, first, end, nor)
                && directive_argument_error_span(forms, first, end, closing, span))
            || (kind == HeaderError::UnexpectedArgument && first + 1 < end
                && directive_word_at(source, forms, first, end, nor)
                && span == form_span(forms[first + 1])),
        Head::Namespace => kind == namespace_path
            && !directive_word_at(source, forms, first, end, namespace_path)
            && directive_argument_error_span(forms, first, end, closing, span),
        Head::Use =>
            (kind == path && !directive_word_at(source, forms, first, end, path)
                && directive_argument_error_span(forms, first, end, closing, span))
            || (directive_word_at(source, forms, first, end, path) && (
                (kind == name && !directive_word_at(source, forms, first + 1, end, name)
                    && directive_argument_error_span(forms, first + 1, end, closing, span))
                || (kind == HeaderError::UnexpectedArgument && first + 2 < end
                    && directive_word_at(source, forms, first + 1, end, name)
                    && span == form_span(forms[first + 2])))),
        Head::Export => kind == name && (exists|i: int| first <= i <= end
            && (i < end || i == first)
            && !#[trigger] directive_word_at(source, forms, i, end, name)
            && directive_argument_error_span(forms, i, end, closing, span)
            && (forall|j: int| first <= j < i ==> #[trigger] directive_word_at(source, forms, j, end, name))),
        _ => false,
    }
}

fn check_directive_word(
    source: &str, forms: &[Form], index: usize, end: usize, closing: usize, expected: HeaderError,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        index <= end <= forms@.len(),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        expected is ExpectedNor || expected is ExpectedNamespacePath
            || expected is ExpectedAbsolutePath || expected is ExpectedName,
    ensures
        result.is_ok() == directive_word_at(source, forms@, index as int, end as int, expected),
        result matches Err((kind, span)) ==> kind == expected
            && directive_argument_error_span(forms@, index as int, end as int, closing, span),
{
    if index == end {
        return Err((expected, closing..closing));
    }
    let form = &forms[index];
    let Form::Atom { kind: atom_kind, span: word_span } = form else {
        return Err((expected, form_span_exec(form)));
    };
    let accepted = match expected {
        HeaderError::ExpectedNor => {
            if !matches!(atom_kind, AtomKind::Name) {
                false
            } else {
                proof { encode_utf8_valid_utf8(source@); }
                assert(word_span.start < word_span.end <= source.spec_bytes().len()
                    && is_char_boundary(source.spec_bytes(), word_span.start as int)
                    && is_char_boundary(source.spec_bytes(), word_span.end as int)) by {
                    reveal(form_spans_valid);
                    assert(form_span(*form) == *word_span);
                };
                let word = source_span(source, word_span.start, word_span.end);
                assert(word@ == "nor"@ <==> word.spec_bytes() == "nor".spec_bytes()) by {
                    encode_utf8_decode_utf8(word@);
                    encode_utf8_decode_utf8("nor"@);
                };
                word == "nor"
            }
        }
        HeaderError::ExpectedNamespacePath => matches!(atom_kind, AtomKind::Name | AtomKind::RelativePath),
        HeaderError::ExpectedAbsolutePath => matches!(atom_kind, AtomKind::AbsolutePath),
        HeaderError::ExpectedName => matches!(atom_kind, AtomKind::Name),
        _ => false,
    };
    if accepted { Ok(()) } else { Err((expected, word_span.start..word_span.end)) }
}

fn validate_directive(
    source: &str, forms: &[Form], first: usize, end: usize, closing: usize, head: Head,
) -> (result: Result<(), (HeaderError, Range<usize>)>)
    requires
        first <= end <= forms@.len(),
        closing < source.spec_bytes().len(),
        source.spec_bytes()[closing as int] == 41,
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        head is Using || head is Namespace || head is Use || head is Export,
    ensures
        result.is_ok() == directive_arguments_match(source, forms@, first as int, end as int, head),
        result matches Err((kind, span)) ==>
            directive_error_evidence(source, forms@, first as int, end as int, closing, head, kind, span),
{
    let after = match head {
        Head::Using => {
            check_directive_word(source, forms, first, end, closing, HeaderError::ExpectedNor)?;
            first + 1
        }
        Head::Namespace => {
            return check_directive_word(source, forms, first, end, closing, HeaderError::ExpectedNamespacePath);
        }
        Head::Use => {
            check_directive_word(source, forms, first, end, closing, HeaderError::ExpectedAbsolutePath)?;
            check_directive_word(source, forms, first + 1, end, closing, HeaderError::ExpectedName)?;
            first + 2
        }
        Head::Export => {
            check_directive_word(source, forms, first, end, closing, HeaderError::ExpectedName)?;
            let mut index = first + 1;
            while index < end
                invariant
                    first < index <= end <= forms@.len(),
                    head == Head::Export,
                    closing < source.spec_bytes().len(),
                    source.spec_bytes()[closing as int] == 41,
                    form_spans_valid(source, forms@, source.spec_bytes().len() as int),
                    forall|i: int| first <= i < index ==>
                        #[trigger] directive_word_at(source, forms@, i, end as int, HeaderError::ExpectedName),
                decreases end - index,
            {
                if let Err(error) = check_directive_word(
                    source, forms, index, end, closing, HeaderError::ExpectedName,
                ) {
                    assert(exists|i: int| first <= i < end
                        && !#[trigger] directive_word_at(source, forms@, i, end as int, HeaderError::ExpectedName)
                        && directive_argument_error_span(forms@, i, end as int, closing, error.1)
                        && (forall|j: int| first <= j < i ==> #[trigger]
                            directive_word_at(source, forms@, j, end as int, HeaderError::ExpectedName)));
                    return Err(error);
                }
                index += 1;
            }
            return Ok(());
        }
        _ => unreachable!(),
    };
    if after < end {
        Err((HeaderError::UnexpectedArgument, form_span_exec(&forms[after])))
    } else {
        Ok(())
    }
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
