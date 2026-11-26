//! マクロ本体のリストと、テンプレート内で評価する式を検査する。

use super::*;
#[cfg(verus_only)]
use crate::ncg2m::defn::readable_span;
use crate::ncg2m::template::{InsertionKind, TemplateError, TemplatePart, read_syntax_template, walk_template};
#[cfg(verus_only)]
use crate::ncg2m::template::{syntax_template, template_part};
use crate::project::{DefmacroBody, ParsedProjectSources, ResolvedDefmacro, read_source_span};

verus! {

/// マクロ本体の型検査で最初に見つかった違反または保留。
#[derive(Debug, Eq, PartialEq)]
pub enum MacroBodyError<'a> {
    /// この経路が扱うリストの外側にある式。
    Deferred(DeferredExpression),
    /// `syntax`、`unsyntax`、`splice` の構造に関する違反。
    Template(TemplateError),
    /// リスト要素または挿入式の検査結果。
    Expression {
        /// 検査した式全体が占める元ソースの UTF-8 半開バイト範囲。
        span: Range<usize>,
        /// 既存の式の型判断が返した最初の診断。
        error: ExpressionCheckFailure<'a>,
    },
}

/// 型検査を通った挿入式の位置と期待型。
#[derive(Debug, Eq, PartialEq)]
pub struct MacroInsertion {
    /// 挿入フォーム全体の UTF-8 半開バイト範囲。
    pub span: Range<usize>,
    /// 元の構文木内で挿入式の根を指す添字。
    pub expression: usize,
    /// 挿入式全体の UTF-8 半開バイト範囲。
    pub expression_span: Range<usize>,
    /// 式の検査で要求した型。
    pub expected: InsertionKind,
}

/// 元のリスト順に並ぶ、型検査済みの本体の一要素。
#[derive(Debug)]
pub struct CheckedMacroElement {
    /// 要素の式の根を指す元の構文木の添字。
    pub at: usize,
    /// `syntax` の場合、そのテンプレートの根を指す元の構文木の添字。
    pub template: Option<usize>,
    /// テンプレートで実際に型検査した挿入式。元ソース順に並ぶ。
    pub insertions: Vec<MacroInsertion>,
}

/// `(List Syntax)` として検査した、元ソースと本体。
#[derive(Debug)]
pub struct CheckedMacroBody<'p, 'a> {
    /// 元ソース、保持済みの構文木と本体式。
    pub body: DefmacroBody<'p, 'a>,
    /// 宣言順の仮引数。暗黙の型 `Syntax` には仮引数名の範囲を使う。
    pub parameters: Vec<SignatureParameter<'a>>,
    /// `list` の要素を検査した順に並べた結果。
    pub elements: Vec<CheckedMacroElement>,
}

spec fn syntax_type(depth: usize) -> TypeShape {
    TypeShape { builtin: Some(BuiltinDataType::Syntax), list_depth: depth }
}

fn required_type(kind: InsertionKind) -> (ty: TypeShape)
    ensures ty == syntax_type(if kind is Syntax { 0 } else { 1 }),
{
    let list_depth = if matches!(kind, InsertionKind::Syntax) { 0 } else { 1 };
    TypeShape { builtin: Some(BuiltinDataType::Syntax), list_depth }
}

/// 仮引数の名前と宣言順を保存し、全てを `Syntax` として環境に入れる。
pub open spec fn macro_parameter_environment(
    source: &str, spans: Seq<Range<usize>>, parameters: Seq<SignatureParameter>,
) -> bool {
    &&& spans.len() == parameters.len()
    &&& forall|i: int| 0 <= i < spans.len() ==> {
        let parameter = #[trigger] parameters[i];
        let span = spans[i];
        &&& parameter.name_span == span
        &&& parameter.name.spec_bytes() == source.spec_bytes()[span.start as int..span.end as int]
        &&& parameter.ty.ty == (DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Syntax), list_depth: 0 })
        &&& parameter.ty.span == span && parameter.ty.name_span == span
    }
}

fn parameters_from_spans<'a>(source: &'a str, spans: &[Range<usize>])
    -> (parameters: Vec<SignatureParameter<'a>>)
    requires forall|i: int| 0 <= i < spans@.len() ==> readable_span(source, #[trigger] spans@[i]),
    ensures macro_parameter_environment(source, spans@, parameters@),
{
    let mut parameters = Vec::with_capacity(spans.len());
    let mut i = 0;
    while i < spans.len()
        invariant i <= spans@.len(),
            macro_parameter_environment(source, spans@.take(i as int), parameters@),
            forall|j: int| 0 <= j < spans@.len() ==> readable_span(source, #[trigger] spans@[j]),
        decreases spans@.len() - i,
    {
        let span = &spans[i];
        let ghost previous = parameters@;
        let name = read_source_span(source, span.start, span.end);
        let ty = super::super::data_types::LocatedDataType {
            ty: DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Syntax), list_depth: 0 },
            span: span.start..span.end,
            name_span: span.start..span.end,
        };
        parameters.push(SignatureParameter { name, name_span: span.start..span.end, ty });
        assert forall|j: int| 0 <= j <= i implies {
            let parameter = #[trigger] parameters@[j];
            let span = spans@[j];
            &&& parameter.name_span == span
            &&& parameter.name.spec_bytes() == source.spec_bytes()[span.start as int..span.end as int]
            &&& parameter.ty.ty == (DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Syntax), list_depth: 0 })
            &&& parameter.ty.span == span && parameter.ty.name_span == span
        } by {
            if j < i {
                assert(parameters@[j] == previous[j]);
                assert(spans@.take(i as int)[j] == spans@[j]);
            }
        };
        assert(macro_parameter_environment(source, spans@.take((i + 1) as int), parameters@));
        i += 1;
    }
    assert(spans@.take(i as int) =~= spans@);
    parameters
}

spec fn macro_list_arguments(source: &str, forms: Seq<Form>, at: usize) -> Option<Range<usize>> {
    match forms[at as int] {
        Form::List { end, .. } if at + 1 < end && plain_name(forms[at + 1])
            && spelling(source, forms[at + 1]) == "list".spec_bytes() =>
            Some((at + 2) as usize..end),
        _ => None,
    }
}

fn read_macro_list(source: &str, forms: &[Form], at: usize) -> (args: Option<Range<usize>>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures args == macro_list_arguments(source, forms@, at),
        args matches Some(range) ==> range.start <= range.end <= forms@.len() && range.end == subtree_limit(forms@, at),
{
    let Form::List { end, .. } = &forms[at] else { return None; };
    proof { reveal(complete_list_indices); }
    if at + 1 == *end || !is_name(&forms[at + 1]) || !is_spelling(source_word(source, forms, at + 1), "list") {
        return None;
    }
    Some(at + 2..*end)
}


spec fn append_success<T, E>(prefix: Seq<T>, suffix: Result<Seq<T>, E>) -> Result<Seq<T>, E> {
    match suffix { Ok(items) => Ok(prefix + items), Err(error) => Err(error) }
}

proof fn append_step<T, E>(prefix: Seq<T>, item: T, suffix: Result<Seq<T>, E>)
    ensures append_success(prefix, append_success(seq![item], suffix))
        == append_success(prefix.push(item), suffix),
{
    if let Ok(items) = suffix {
        assert((prefix + (seq![item] + items)) =~= (prefix.push(item) + items));
    }
}

spec fn typed_insertions_tail<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>, root: usize,
    current: usize, stop: usize,
) -> Result<Seq<MacroInsertion>, MacroBodyError<'a>>
    decreases stop - current,
{
    if current >= stop {
        Ok(Seq::empty())
    } else {
        match template_part(source, forms, current, current == root) {
            Err(error) => Err(MacroBodyError::Template(error)),
            Ok(TemplatePart::Insertion { kind, expression, next }) => {
                let expected = syntax_type(if kind is Syntax { 0 } else { 1 });
                match typed_body(source, forms, environment_view(parameters), expression, expected) {
                    BodyVerdict::Rejected(error) => Err(MacroBodyError::Expression {
                        span: form_span(forms[expression as int]), error,
                    }),
                    BodyVerdict::Accepted if current < next <= stop => {
                        let insertion = MacroInsertion {
                            span: form_span(forms[current as int]), expression,
                            expression_span: form_span(forms[expression as int]), expected: kind,
                        };
                        append_success(seq![insertion],
                            typed_insertions_tail(source, forms, parameters, root, next, stop))
                    },
                    BodyVerdict::Accepted => Err(MacroBodyError::Deferred(DeferredExpression::Form(
                        form_span(forms[current as int])))),
                }
            },
            Ok(_) => typed_insertions_tail(source, forms, parameters, root, (current + 1) as usize, stop),
        }
    }
}

/// 挿入位置と式の元範囲が、同じテンプレートの構文木に対応する。
pub open spec fn macro_insertion_origin(source: &str, forms: Seq<Form>, root: usize, row: MacroInsertion) -> bool {
    let at = row.expression - 2;
    &&& root <= at && row.expression < forms.len()
    &&& forms[at] matches Form::List { end, span }
        && row.span == span && row.expression < end <= forms.len()
        && template_part(source, forms, at as usize, at == root) ==
            Ok(TemplatePart::Insertion { kind: row.expected, expression: row.expression, next: end })
    &&& row.expression_span == form_span(forms[row.expression as int])
}

/// 挿入式が、その構文に対応する型を持つことを表す。
pub closed spec fn macro_insertion_is_typed(
    source: &str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, row: MacroInsertion,
) -> bool {
    typed_body(source, forms, environment_view(parameters), row.expression,
        syntax_type(if row.expected is Syntax { 0 } else { 1 })) == BodyVerdict::Accepted
}

fn check_insertions<'a>(source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], root: usize)
    -> (result: Result<Vec<MacroInsertion>, MacroBodyError<'a>>)
    requires usable_forms(source, forms@), root < forms@.len(),
    ensures match result {
        Ok(rows) => typed_insertions_tail(source, forms@, parameters@, root, root, subtree_limit(forms@, root)) == Ok(rows@)
            && forall|i: int| 0 <= i < rows@.len() ==>
                macro_insertion_origin(source, forms@, root, #[trigger] rows@[i])
                && macro_insertion_is_typed(source, forms@, parameters@, rows@[i]),
        Err(error) => typed_insertions_tail(source, forms@, parameters@, root, root, subtree_limit(forms@, root)) == Err(error),
    },
{
    let Some(mut walk) = walk_template(source, forms, root) else { unreachable!() };
    let ghost stop = walk.range_model().end;
    let mut rows = Vec::new();
    loop
        invariant
            usable_forms(source, forms@), walk.valid(), walk.source_model() == source,
            walk.forms_model() == forms@, walk.range_model() == (root..stop),
            root < stop <= forms@.len(), stop == subtree_limit(forms@, root),
            root <= walk.position_model() <= stop,
            typed_insertions_tail(source, forms@, parameters@, root, root, stop)
                == append_success(rows@, typed_insertions_tail(
                    source, forms@, parameters@, root, walk.position_model(), stop)),
            forall|i: int| 0 <= i < rows@.len() ==>
                macro_insertion_origin(source, forms@, root, #[trigger] rows@[i])
                && macro_insertion_is_typed(source, forms@, parameters@, rows@[i]),
        decreases stop - walk.position_model(),
    {
        let ghost current = walk.position_model();
        let ghost prefix = rows@;
        let next_part = walk.next_part();
        let ghost next_at = walk.position_model();
        proof { reveal_with_fuel(typed_insertions_tail, 1); }
        let Some((at, part)) = next_part else {
            assert(current == stop);
            assert(prefix + Seq::<MacroInsertion>::empty() =~= prefix);
            return Ok(rows);
        };
        assert(at == current);
        match part {
            Err(error) => return Err(MacroBodyError::Template(error)),
            Ok(TemplatePart::Insertion { kind, expression, next }) => {
                assert(current < next <= stop && next == next_at);
                assert(expression < forms@.len()) by {
                    // 挿入式は挿入フォームの内側に一つだけある。
                    assert(at != stop);
                    reveal(complete_list_indices);
                    assert(at + 2 < next);
                };
                let span = span_of(&forms[expression]);
                if let BodyVerdict::Rejected(error) = check_typed_body(source, forms, parameters, expression, required_type(kind)) {
                    return Err(MacroBodyError::Expression { span, error });
                }
                let row = MacroInsertion {
                    span: span_of(&forms[at]), expression, expression_span: span, expected: kind,
                };
                proof {
                    assert(macro_insertion_origin(source, forms@, root, row));
                    assert(macro_insertion_is_typed(source, forms@, parameters@, row));
                    append_step(prefix, row, typed_insertions_tail(source, forms@, parameters@, root, next_at, stop));
                }
                rows.push(row);
            },
            Ok(_) => {},
        }
    }
}

type MacroElementModel = (usize, Option<usize>, Seq<MacroInsertion>);

spec fn element_model(element: CheckedMacroElement) -> MacroElementModel {
    (element.at, element.template, element.insertions@)
}

spec fn macro_element_check<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>, at: usize,
) -> Result<MacroElementModel, MacroBodyError<'a>> {
    match syntax_template(source, forms, at) {
        Err(error) => Err(MacroBodyError::Template(error)),
        Ok(Some(root)) => match typed_insertions_tail(source, forms, parameters, root, root, subtree_limit(forms, root)) {
            Ok(insertions) => Ok((at, Some(root), insertions)),
            Err(error) => Err(error),
        },
        Ok(None) => match typed_body(source, forms, environment_view(parameters), at, syntax_type(0)) {
            BodyVerdict::Accepted => Ok((at, None, Seq::empty())),
            BodyVerdict::Rejected(error) => Err(MacroBodyError::Expression { span: form_span(forms[at as int]), error }),
        },
    }
}

/// 要素とその挿入式が元の構文木に対応し、要求された型の検査を通っている。
pub open spec fn macro_element_origin(
    source: &str, forms: Seq<Form>, parameters: Seq<SignatureParameter>, element: CheckedMacroElement,
) -> bool {
    &&& element.at < forms.len()
    &&& syntax_template(source, forms, element.at) == Ok(element.template)
    &&& match element.template {
        Some(root) => root < forms.len() && forall|i: int| 0 <= i < element.insertions@.len() ==>
            macro_insertion_origin(source, forms, root, #[trigger] element.insertions@[i])
            && macro_insertion_is_typed(source, forms, parameters, element.insertions@[i]),
        None => element.insertions@.len() == 0,
    }
}

fn check_element<'a>(source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], at: usize)
    -> (result: Result<CheckedMacroElement, MacroBodyError<'a>>)
    requires usable_forms(source, forms@), at < forms@.len(),
    ensures macro_element_check(source, forms@, parameters@, at) == match result {
        Ok(element) => Ok(element_model(element)), Err(error) => Err(error),
    },
        result matches Ok(element) ==> macro_element_origin(source, forms@, parameters@, element),
{
    let maybe = match read_syntax_template(source, forms, at) {
        Ok(root) => root,
        Err(error) => return Err(MacroBodyError::Template(error)),
    };
    if let Some(root) = maybe {
        return match check_insertions(source, forms, parameters, root) {
            Ok(insertions) => Ok(CheckedMacroElement { at, template: Some(root), insertions }),
            Err(error) => Err(error),
        };
    }
    let expected = TypeShape { builtin: Some(BuiltinDataType::Syntax), list_depth: 0 };
    match check_typed_body(source, forms, parameters, at, expected) {
        BodyVerdict::Accepted => Ok(CheckedMacroElement { at, template: None, insertions: Vec::new() }),
        BodyVerdict::Rejected(error) => Err(MacroBodyError::Expression { span: span_of(&forms[at]), error }),
    }
}

spec fn typed_elements_tail<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>, current: usize, stop: usize,
) -> Result<Seq<MacroElementModel>, MacroBodyError<'a>>
    decreases stop - current,
{
    if current >= stop {
        Ok(Seq::empty())
    } else {
        match macro_element_check(source, forms, parameters, current) {
            Err(error) => Err(error),
            Ok(row) => {
                let next = subtree_limit(forms, current);
                if current < next <= stop {
                    append_success(seq![row], typed_elements_tail(source, forms, parameters, next, stop))
                } else {
                    Err(MacroBodyError::Deferred(DeferredExpression::Form(form_span(forms[current as int]))))
                }
            },
        }
    }
}

spec fn macro_body_verdict<'a>(
    source: &'a str, forms: Seq<Form>, parameters: Seq<SignatureParameter<'a>>, root: usize,
) -> Result<Seq<MacroElementModel>, MacroBodyError<'a>> {
    match macro_list_arguments(source, forms, root) {
        Some(args) => typed_elements_tail(source, forms, parameters, args.start, args.end),
        None => Err(MacroBodyError::Deferred(DeferredExpression::Form(form_span(forms[root as int])))),
    }
}

fn check_elements<'a>(source: &'a str, forms: &[Form], parameters: &[SignatureParameter<'a>], root: usize)
    -> (result: Result<Vec<CheckedMacroElement>, MacroBodyError<'a>>)
    requires usable_forms(source, forms@), root < forms@.len(),
    ensures macro_body_verdict(source, forms@, parameters@, root) == match result {
        Ok(elements) => Ok(elements@.map_values(|row: CheckedMacroElement| element_model(row))),
        Err(error) => Err(error),
    },
        result matches Ok(elements) ==> forall|i: int| 0 <= i < elements@.len() ==>
            macro_element_origin(source, forms@, parameters@, #[trigger] elements@[i]),
{
    let Some(args) = read_macro_list(source, forms, root) else {
        return Err(MacroBodyError::Deferred(DeferredExpression::Form(span_of(&forms[root]))));
    };
    let mut current = args.start;
    let mut elements = Vec::new();
    while current < args.end
        invariant
            usable_forms(source, forms@), root < args.start <= current <= args.end <= forms@.len(),
            args.end == subtree_limit(forms@, root),
            forall|i: int| 0 <= i < elements@.len() ==>
                macro_element_origin(source, forms@, parameters@, #[trigger] elements@[i]),
            macro_body_verdict(source, forms@, parameters@, root)
                == append_success(elements@.map_values(|row: CheckedMacroElement| element_model(row)),
                    typed_elements_tail(source, forms@, parameters@, current, args.end)),
        decreases args.end - current,
    {
        let ghost prefix = elements@.map_values(|row: CheckedMacroElement| element_model(row));
        let checked = check_element(source, forms, parameters, current);
        proof { reveal_with_fuel(typed_elements_tail, 1); }
        let row = match checked {
            Ok(row) => row,
            Err(error) => return Err(error),
        };
        proof { super::super::forms::child_stays_inside(forms@, root, current); }
        let next = subtree_end(forms, current);
        proof {
            append_step(prefix, element_model(row),
                typed_elements_tail(source, forms@, parameters@, next, args.end));
        }
        elements.push(row);
        assert(elements@.map_values(|row: CheckedMacroElement| element_model(row))
            =~= prefix.push(element_model(row)));
        current = next;
    }
    proof { reveal_with_fuel(typed_elements_tail, 1); }
    let ghost rows = elements@.map_values(|row: CheckedMacroElement| element_model(row));
    assert(rows + Seq::<MacroElementModel>::empty() =~= rows);
    Ok(elements)
}

/// 検査結果が保持済みの本体式と仮引数に対する判定に一致する。
pub closed spec fn defmacro_body_check<'p, 'a>(
    project: &ParsedProjectSources, definition: &ResolvedDefmacro<'_, 'a>,
    result: Option<Result<CheckedMacroBody<'p, 'a>, MacroBodyError<'a>>>,
) -> bool {
    let file = definition.declaration.file;
    let source = project.sources_model()[file as int];
    if !project.contains_defmacro(definition) {
        result.is_none()
    } else if let Some(forms) = project.functional_forms_model(file) {
        match result {
            Some(Ok(checked)) => {
                let at = checked.body.at;
                &&& *checked.body.source == source && checked.body.forms@ == forms
                &&& at < forms.len() && form_span(forms[at as int]) == *definition.body
                &&& macro_parameter_environment(source.text_model(), definition.parameters@, checked.parameters@)
                &&& macro_body_verdict(source.text_model(), forms, checked.parameters@, at)
                    == Ok(checked.elements@.map_values(|row: CheckedMacroElement| element_model(row)))
            },
            Some(Err(error)) => exists|at: usize, parameters: Seq<SignatureParameter<'a>>|
                macro_parameter_environment(source.text_model(), definition.parameters@, parameters)
                && at < forms.len() && form_span(forms[at as int]) == *definition.body
                && #[trigger] macro_body_verdict(source.text_model(), forms, parameters, at) == Err(error),
            None => false,
        }
    } else { false }
}

impl<'a> ParsedProjectSources<'a> {
    /// 元の構文木で、マクロ本体の `list` とその要素を `(List Syntax)` として検査する。
    ///
    /// 要素の `syntax` では、挿入式だけを元ソース順に検査する。宣言がこのプロジェクトの索引に
    /// なければ `None`。リスト以外の本体式は後段の検査に回す。
    ///
    /// # Errors
    ///
    /// 検査順で最初に現れるテンプレートの構造違反、式の型違反または保留を返す。
    pub fn check_defmacro_body<'p>(&'p self, definition: &ResolvedDefmacro<'_, 'a>)
        -> (result: Option<Result<CheckedMacroBody<'p, 'a>, MacroBodyError<'a>>>)
        ensures result.is_some() <==> self.contains_defmacro(definition),
            defmacro_body_check(self, definition, result),
            result matches Some(Ok(checked)) ==> {
                let source = checked.body.source.text_model();
                &&& macro_parameter_environment(source, definition.parameters@, checked.parameters@)
                &&& *checked.body.source == self.sources_model()[definition.declaration.file as int]
                &&& self.functional_forms_model(definition.declaration.file) == Some(checked.body.forms@)
                &&& checked.body.at < checked.body.forms@.len()
                &&& form_span(checked.body.forms@[checked.body.at as int]) == *definition.body
                &&& complete_list_indices(checked.body.forms@) && nested_list_indices(checked.body.forms@)
                &&& form_spans_valid(source, checked.body.forms@, source.spec_bytes().len() as int)
                &&& forall|i: int| 0 <= i < checked.elements@.len() ==>
                    macro_element_origin(source, checked.body.forms@, checked.parameters@, #[trigger] checked.elements@[i])
            },
    {
        let body = self.defmacro_body(definition)?;
        let source = body.source.text();
        let parameters = parameters_from_spans(source, definition.parameters);
        match check_elements(source, body.forms, parameters.as_slice(), body.at) {
            Ok(elements) => Some(Ok(CheckedMacroBody { body, parameters, elements })),
            Err(error) => Some(Err(error)),
        }
    }
}

} // verus!
