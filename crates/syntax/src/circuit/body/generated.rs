//! 展開で生成した定義を通常の回路文法に照らして検査する。

use super::*;

verus! {

/// 生成した一つの定義の左辺、右辺、参照、右辺の信号名。
#[derive(Debug)]
pub struct GeneratedDefinition {
    /// 左辺に現れる名前の構文木上の半開区間。
    pub targets: Range<usize>,
    /// 右辺の式全体が占める、構文木上の半開区間。
    pub expression: Range<usize>,
    /// 右辺の回路名と型名を構文順に並べた一覧。
    pub references: Vec<ExpressionReference>,
    /// 右辺にある信号名を指す構文木の添字の一覧。
    pub signals: Vec<usize>,
}

/// 生成した回路式に置けないフォームの先頭語。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForbiddenGeneratedHead {
    /// `expand`。
    Expand,
    /// `use`。
    Use,
    /// `namespace`。
    Namespace,
    /// `defmacro`。
    Defmacro,
}

/// 生成した一つの定義の検査で最初に見つかった違反。
#[derive(Debug, Eq, PartialEq)]
pub enum GeneratedDefinitionError {
    /// 生成された構文に根がない。
    Empty,
    /// 一つ目の根に続く、余分な根の UTF-8 半開バイト範囲。
    ExtraRoot(Range<usize>),
    /// 根が `def` でない。先頭語など該当箇所の UTF-8 半開バイト範囲。
    ExpectedDefinition(Range<usize>),
    /// `def` の左辺または右辺が回路文法に適合しない。
    Invalid {
        /// 通常の本体検査で得た違反の種別。
        kind: HeaderError,
        /// 該当箇所の UTF-8 半開バイト範囲。欠落なら閉じ括弧の位置で長さが0。
        span: Range<usize>,
    },
    /// 生成結果で禁止する先頭語が右辺の式に現れた。
    ForbiddenHead {
        /// 禁止した先頭語の種別。
        head: ForbiddenGeneratedHead,
        /// 先頭語の UTF-8 半開バイト範囲。
        span: Range<usize>,
    },
}

spec fn generated_forbidden_head(word: Seq<u8>) -> Option<ForbiddenGeneratedHead> {
    if word == "expand".spec_bytes() { Some(ForbiddenGeneratedHead::Expand) }
    else if word == "use".spec_bytes() { Some(ForbiddenGeneratedHead::Use) }
    else if word == "namespace".spec_bytes() { Some(ForbiddenGeneratedHead::Namespace) }
    else if word == "defmacro".spec_bytes() { Some(ForbiddenGeneratedHead::Defmacro) }
    else { None }
}

fn read_generated_forbidden_head(word: &str) -> (head: Option<ForbiddenGeneratedHead>)
    ensures head == generated_forbidden_head(word.spec_bytes()),
{
    proof {
        encode_utf8_decode_utf8(word@);
        encode_utf8_decode_utf8("expand"@);
        encode_utf8_decode_utf8("use"@);
        encode_utf8_decode_utf8("namespace"@);
        encode_utf8_decode_utf8("defmacro"@);
    }
    if word == "expand" { Some(ForbiddenGeneratedHead::Expand) }
    else if word == "use" { Some(ForbiddenGeneratedHead::Use) }
    else if word == "namespace" { Some(ForbiddenGeneratedHead::Namespace) }
    else if word == "defmacro" { Some(ForbiddenGeneratedHead::Defmacro) }
    else { None }
}

spec fn forbidden_generated_reference(source: &str, reference: ExpressionReference) -> Option<ForbiddenGeneratedHead> {
    if reference.kind is Callee {
        generated_forbidden_head(source.spec_bytes()[reference.span.start as int..reference.span.end as int])
    } else { None }
}

spec fn forbidden_generated_head_at(
    source: &str, references: Seq<ExpressionReference>, at: int,
    head: ForbiddenGeneratedHead, span: Range<usize>,
) -> bool {
    &&& 0 <= at < references.len()
    &&& forbidden_generated_reference(source, references[at]) == Some(head)
    &&& span == references[at].span
    &&& forall|i: int| 0 <= i < at ==> forbidden_generated_reference(source, #[trigger] references[i]).is_none()
}

#[verifier::opaque]
spec fn generated_forbidden_diagnosis(
    source: &str, references: Seq<ExpressionReference>, head: ForbiddenGeneratedHead, span: Range<usize>,
) -> bool {
    exists|at: int| #[trigger] forbidden_generated_head_at(source, references, at, head, span)
}

fn first_forbidden_generated_head(
    source: &str, _forms: &[Form], references: &[ExpressionReference],
) -> (result: Option<(usize, ForbiddenGeneratedHead, Range<usize>)>)
    requires forall|i: int| 0 <= i < references@.len()
        ==> expression_reference_in_source(source, _forms@, #[trigger] references@[i]),
    ensures
        match result {
            Some((at, head, span)) => forbidden_generated_head_at(source, references@, at as int, head, span),
            None => forall|i: int| 0 <= i < references@.len() ==>
                forbidden_generated_reference(source, #[trigger] references@[i]).is_none(),
        },
{
    let mut i = 0;
    while i < references.len()
        invariant i <= references@.len(),
            forall|j: int| 0 <= j < references@.len()
                ==> expression_reference_in_source(source, _forms@, #[trigger] references@[j]),
            forall|j: int| 0 <= j < i ==> forbidden_generated_reference(source, #[trigger] references@[j]).is_none(),
        decreases references@.len() - i,
    {
        let reference = &references[i];
        if matches!(reference.kind, ExpressionReferenceKind::Callee) {
            let word = source_span(source, reference.span.start, reference.span.end);
            if let Some(head) = read_generated_forbidden_head(word) {
                let span = reference.span.start..reference.span.end;
                assert(forbidden_generated_head_at(source, references@, i as int, head, span));
                return Some((i, head, span));
            }
        }
        i += 1;
    }
    None
}

spec fn generated_definition_shape(source: &str, forms: Seq<Form>) -> bool {
    &&& forms.len() > 0
    &&& forms[0] matches Form::List { end, .. }
    &&& end == forms.len()
    &&& body_head_at(source, forms, 1, end as int, BodyHead::Def)
    &&& body_arguments_match(source, forms, 2, end as int, BodyHead::Def)
}

/// 入力が一つの `def` であり、右辺に生成時の禁止フォームがないことを表す。
pub closed spec fn generated_definition_valid(source: &str, forms: Seq<Form>) -> bool {
    &&& generated_definition_shape(source, forms)
    &&& {
        let value = after_form(forms, 2);
        let references = expression_references(source, forms, value, forms.len() as int);
        forall|i: int| 0 <= i < references.len() ==> forbidden_generated_reference(source, #[trigger] references[i]).is_none()
    }
}

/// 検査結果の左辺、右辺、参照、信号名が入力の構文木と対応することを表す。
pub closed spec fn generated_definition_matches(source: &str, forms: Seq<Form>, result: GeneratedDefinition) -> bool {
    let value = after_form(forms, 2);
    let stop = forms.len() as int;
    &&& generated_definition_valid(source, forms)
    &&& 2 <= result.targets.start < result.targets.end <= result.expression.start < result.expression.end <= forms.len()
    &&& result.targets.start == if forms[2] is List { 3usize } else { 2usize }
    &&& result.targets.end == value
    &&& forall|i: int| result.targets.start <= i < result.targets.end
        ==> (#[trigger] forms[i]) is Atom && forms[i]->Atom_kind is Name
    &&& result.expression.start == value && result.expression.end == stop
    &&& result.references@ == expression_references(source, forms, value, stop)
    &&& result.signals@ == expression_signals(source, forms, value, stop)
}

/// 結果の各添字から、入力の構文木と出典の範囲を安全に参照できることを表す。
pub open spec fn generated_definition_sites(source: &str, forms: Seq<Form>, row: GeneratedDefinition) -> bool {
    &&& row.targets.start < row.targets.end == row.expression.start < row.expression.end == forms.len()
    &&& forall|i: int| row.targets.start <= i < row.targets.end
        ==> (#[trigger] forms[i]) is Atom && forms[i]->Atom_kind is Name
    &&& forall|i: int| 0 <= i < row.references@.len()
        ==> expression_reference_in_source(source, forms, #[trigger] row.references@[i])
    &&& forall|i: int| 0 <= i < row.signals@.len() ==> {
        let at = #[trigger] row.signals@[i];
        &&& row.expression.start <= at < row.expression.end
        &&& forms[at as int] is Atom && forms[at as int]->Atom_kind is Name
    }
}

/// 根の個数、先頭語、通常の構文違反、禁止フォームの順に診断を選ぶ。
pub closed spec fn generated_definition_error(
    source: &str, forms: Seq<Form>, error: GeneratedDefinitionError,
) -> bool {
    if forms.len() == 0 {
        error == GeneratedDefinitionError::Empty
    } else {
        let end = after_form(forms, 0);
        if end < forms.len() {
            error == GeneratedDefinitionError::ExtraRoot(form_span(forms[end]))
        } else if let Form::List { span, .. } = forms[0] {
            let closing = (span.end - 1) as usize;
            if !body_head_at(source, forms, 1, end, BodyHead::Def) {
                error matches GeneratedDefinitionError::ExpectedDefinition(span)
                    && directive_argument_error_span(forms, 1, end, closing, span)
            } else if !body_arguments_match(source, forms, 2, end, BodyHead::Def) {
                error matches GeneratedDefinitionError::Invalid { kind, span }
                    && body_arguments_error(source, forms, 2, end, closing, BodyHead::Def, (kind, span))
            } else {
                let references = expression_references(source, forms, after_form(forms, 2), end);
                error matches GeneratedDefinitionError::ForbiddenHead { head, span }
                    && generated_forbidden_diagnosis(source, references, head, span)
            }
        } else {
            error == GeneratedDefinitionError::ExpectedDefinition(form_span(forms[0]))
        }
    }
}

/// 展開から得た構文木を一つの `def` として検査し、左辺、右辺、回路名、型名、信号名を返す。
///
/// 展開で生成した本文と、その本文上の範囲を持つ平坦な構文木を渡す。
/// 左辺や通常の信号名の綴りは、禁止するフォームの先頭語として扱わない。
///
/// # Errors
///
/// 根の個数と先頭語を検査し、続けて普通の `def` と同じ順序で診断する。
/// 右辺が回路文法に適合した場合は、最初の禁止フォームの先頭語を診断する。
/// 診断範囲は渡した本文上の UTF-8 半開バイト範囲である。
///
/// # Panics
///
/// 渡した構文木の添字、バイト範囲、字句種別や括弧が本文に対応しない場合は、パニックすることがある。
///
/// # Examples
///
/// ```
/// use circuitgame2_syntax::{circuit::{GeneratedDefinitionError, ForbiddenGeneratedHead, check_generated_definition}, parse};
///
/// let text = "(def (expand use) (logic namespace))";
/// let forms = parse(text)?;
/// let row = check_generated_definition(text, &forms).unwrap();
/// assert_eq!(row.targets.len(), 2);
/// assert_eq!(row.references.len(), 1);
/// assert_eq!(row.signals.len(), 1);
///
/// let text = "(def y (nor (expand lib) x))";
/// let forms = parse(text)?;
/// assert!(matches!(check_generated_definition(text, &forms),
///     Err(GeneratedDefinitionError::ForbiddenHead { head: ForbiddenGeneratedHead::Expand, span })
///         if &text[span.clone()] == "expand"));
/// # Ok::<(), circuitgame2_syntax::Error>(())
/// ```
pub fn check_generated_definition(source: &str, forms: &[Form])
    -> (result: Result<GeneratedDefinition, GeneratedDefinitionError>)
    requires
        complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
        list_source_delimiters(source, forms@, false),
    ensures
        result.is_ok() <==> generated_definition_valid(source, forms@),
        result matches Ok(row) ==> generated_definition_matches(source, forms@, row)
            && generated_definition_sites(source, forms@, row),
        result matches Err(error) ==> generated_definition_error(source, forms@, error),
{
    let Some(root) = forms.first() else { return Err(GeneratedDefinitionError::Empty); };
    let end = match root { Form::List { end, .. } => *end, Form::Atom { .. } => 1 };
    proof { reveal(complete_list_indices); }
    if end < forms.len() {
        return Err(GeneratedDefinitionError::ExtraRoot(form_span_exec(&forms[end])));
    }
    let Form::List { span, .. } = root else {
        return Err(GeneratedDefinitionError::ExpectedDefinition(form_span_exec(root)));
    };
    proof {
        reveal(list_source_delimiters);
        assert(list_delimited(source.spec_bytes(), *root, false));
    }
    let closing = span.end - 1;
    match read_body_item_head(source, forms, 1, end, closing) {
        Ok(BodyHead::Def) => {
            assert(body_head_at(source, forms@, 1, end as int, BodyHead::Def));
        },
        Ok(BodyHead::Expand) => {
            assert(body_head_at(source, forms@, 1, end as int, BodyHead::Expand));
            assert(!body_head_at(source, forms@, 1, end as int, BodyHead::Def));
            return Err(GeneratedDefinitionError::ExpectedDefinition(form_span_exec(&forms[1])));
        },
        Err((_, span)) => {
            assert(!body_head_at(source, forms@, 1, end as int, BodyHead::Def));
            return Err(GeneratedDefinitionError::ExpectedDefinition(span));
        },
    }
    let mut references = Vec::new();
    let mut signals = Vec::new();
    let expression = match inspect_body_arguments(
        source, forms, 2, end, closing, BodyHead::Def, true, &mut references, &mut signals,
    ) {
        Ok(Some(expression)) => expression,
        Ok(None) => unreachable!(),
        Err((kind, span)) => return Err(GeneratedDefinitionError::Invalid { kind, span }),
    };
    if let Some((_at, head, span)) = first_forbidden_generated_head(source, forms, &references) {
        proof {
            let indexed = expression_references(source, forms@, after_form(forms@, 2), end as int);
            assert(indexed == references@);
            assert(generated_forbidden_diagnosis(source, indexed, head, span)) by {
                reveal(generated_forbidden_diagnosis);
                assert(forbidden_generated_head_at(source, indexed, _at as int, head, span));
            };
        }
        return Err(GeneratedDefinitionError::ForbiddenHead { head, span });
    }
    let start = if matches!(forms[2], Form::List { .. }) { 3 } else { 2 };
    let targets = start..expression.start;
    proof {
        assert forall|i: int| 0 <= i < signals@.len() implies {
            let at = #[trigger] signals@[i];
            &&& expression.start <= at < expression.end
            &&& forms@[at as int] is Atom && forms@[at as int]->Atom_kind is Name
        } by {
            super::super::expression_forest::expression_signal_evidence(
                source, forms@, expression.start as int, expression.end as int, i,
            );
        };
        assert forall|i: int| targets.start <= i < targets.end implies
            (#[trigger] forms@[i]) is Atom && forms@[i]->Atom_kind is Name by {
            if forms@[2] is List {
                assert(argument_matches(forms@, i, targets.end as int, HeaderError::ExpectedName));
            }
        };
    }
    Ok(GeneratedDefinition { targets, expression, references, signals })
}

} // verus!
