//! 型検査を通ったマクロ呼び出しの仮引数を、元の実引数の構文に束縛する。

use alloc::vec::Vec;
use core::ops::Range;
use crate::ncg2m::data_types::SignatureParameter;
use crate::ncg2m::expression_types::CheckedMacroBody;
use crate::ncg2m::{defn::{is_name, span_of}, forms::{is_spelling, source_word}};
use crate::project::{MacroArgument, MacroArgumentScope, MacroArguments, ResolvedDefmacro};
use crate::syntax::{Form, circuit::RoutineExpansionSite};
#[cfg(verus_only)]
use crate::syntax::{AtomKind, form_span, form_spans_valid};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::checked_macro_body_layout;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

mod expression;
pub use expression::{MacroExpressionEvaluation, MacroExpressionStep};
#[cfg(verus_only)]
pub use expression::{
    macro_expression_evaluation_result, macro_expression_expected, macro_expression_start_matches,
    macro_expression_starts_agree, macro_expression_states_agree, macro_expression_step_matches,
    macro_expression_step_results_agree, macro_expression_steps_agree,
};

verus! {

/// 型検査で確定した、マクロ内の一つの式の位置。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MacroExpressionSite {
    /// マクロが返すリストの要素番号。
    Element(usize),
    /// リストの要素番号と、そのテンプレートで評価する挿入式の番号。
    Insertion {
        /// マクロが返すリストの要素番号。
        element: usize,
        /// テンプレートの挿入式を元ソース順に並べた番号。
        insertion: usize,
    },
}

/// 引数の構文を返すところまで進めなかった理由。
#[derive(Debug, Eq, PartialEq)]
pub enum MacroArgumentError {
    /// 指定されたリスト要素または挿入式がない。
    NoExpression,
    /// 仮引数として束縛されていない名前の UTF-8 半開バイト範囲。
    Unbound(Range<usize>),
    /// 仮引数名の参照以外の式。後の評価段階に渡す元範囲。
    Deferred(Range<usize>),
}

/// 同じマクロ呼び出しから取り出した型検査済み本体と束縛。
#[derive(Debug)]
pub struct BoundMacroCall<'p, 'a> {
    site: RoutineExpansionSite,
    scope: MacroArgumentScope<'p, 'a>,
    definition: ResolvedDefmacro<'p, 'a>,
    body: CheckedMacroBody<'p, 'a>,
    arguments: Vec<MacroArgument<'p, 'a>>,
}

impl<'p, 'a> BoundMacroCall<'p, 'a> {
    /// 元の展開呼び出しの位置を表す。
    pub closed spec fn site_model(&self) -> RoutineExpansionSite { self.site }

    /// 実引数を解釈する呼び出し側のスコープを表す。
    pub closed spec fn scope_model(&self) -> MacroArgumentScope<'p, 'a> { self.scope }

    /// 呼び出しが解決した元の宣言を表す。
    pub closed spec fn definition_model(&self) -> ResolvedDefmacro<'p, 'a> { self.definition }

    /// 引数を束縛する側の型検査済み本体を表す。
    pub closed spec fn body_model(&self) -> CheckedMacroBody<'p, 'a> { self.body }

    /// 仮引数と同じ順序の実引数を表す。
    pub closed spec fn arguments_model(&self) -> Seq<MacroArgument<'p, 'a>> { self.arguments@ }

    /// 仮引数と実引数の個数が合い、本体の各要素と挿入式が保持した構文木に対応する。
    pub open spec fn valid(&self) -> bool {
        &&& self.body_model().parameters_model().len() == self.arguments_model().len()
        &&& checked_macro_body_layout(&self.body_model())
    }

    /// 呼び出し位置を、元のソースと構文木の範囲で借りる。
    pub fn site(&self) -> (site: &RoutineExpansionSite)
        ensures *site == self.site_model(),
    {
        &self.site
    }

    /// 実引数に含まれる識別子を解決するときのスコープを返す。
    pub fn scope(&self) -> (scope: MacroArgumentScope<'p, 'a>)
        ensures scope == self.scope_model(),
    {
        self.scope
    }

    /// 呼び出しが解決した元のマクロ宣言を借りる。
    pub fn definition(&self) -> (definition: &ResolvedDefmacro<'p, 'a>)
        ensures *definition == self.definition_model(),
    {
        &self.definition
    }

    /// 型検査済みのマクロ本体を借りる。
    pub fn body(&self) -> (body: &CheckedMacroBody<'p, 'a>)
        ensures *body == self.body_model(),
    {
        &self.body
    }

    /// 実引数の構文を、対応する仮引数と同じ順序で借りる。
    pub fn arguments(&self) -> (arguments: &[MacroArgument<'p, 'a>])
        ensures arguments@ == self.arguments_model(),
    {
        self.arguments.as_slice()
    }

    fn expression_at(&self, site: MacroExpressionSite) -> (at: Option<usize>)
        ensures at == macro_expression_position(&self.body_model(), site),
    {
        let elements = self.body.elements();
        match site {
            MacroExpressionSite::Element(index) => {
                let element = elements.get(index)?;
                Some(element.at())
            },
            MacroExpressionSite::Insertion { element, insertion } => {
                let row = elements.get(element)?.insertions().get(insertion)?;
                Some(row.expression)
            },
        }
    }

    /// 型検査済みの式が仮引数名なら、対応する実引数の構文を借りる。
    ///
    /// 同名の仮引数は宣言順の先頭を選ぶ。出典・回路本体のスコープと構文木は、
    /// 元の展開呼び出しの実引数からそのまま引き継ぐ。
    ///
    /// # Errors
    ///
    /// 式の番号が範囲外、名前が仮引数にない、または式が仮引数名の参照以外なら診断を返す。
    pub fn argument_expression(&self, site: MacroExpressionSite)
        -> (result: Result<&MacroArgument<'p, 'a>, MacroArgumentError>)
        requires self.valid(),
        ensures macro_argument_expression_result(self, site, result),
    {
        let Some(at) = self.expression_at(site) else { return Err(MacroArgumentError::NoExpression); };
        let body = self.body.body();
        let Some(form) = body.forms.get(at) else { return Err(MacroArgumentError::NoExpression); };
        let span = span_of(form);
        let Some(name) = read_macro_direct_name(body.source.text(), body.forms, at) else {
            return Err(MacroArgumentError::Deferred(span));
        };
        let Some(index) = find_macro_parameter(self.body.parameters(), name) else {
            proof {
                macro_argument_result_by_selection(self, site, at, name.spec_bytes(), None,
                    Err(MacroArgumentError::Unbound(span)));
            }
            return Err(MacroArgumentError::Unbound(span));
        };
        let argument = &self.arguments[index];
        proof { macro_argument_result_by_selection(self, site, at, name.spec_bytes(), Some(index), Ok(argument)); }
        Ok(argument)
    }
}

/// 型検査済みの要素または挿入式の位置を、元の構文木の添字に対応付ける。
pub open spec fn macro_expression_position(body: &CheckedMacroBody, site: MacroExpressionSite) -> Option<usize> {
    let elements = body.elements_model();
    match site {
        MacroExpressionSite::Element(index) =>
            if index < elements.len() { Some(elements[index as int].at_model()) } else { None },
        MacroExpressionSite::Insertion { element, insertion } =>
            if element < elements.len() {
                let rows = elements[element as int].insertions_model();
                if insertion < rows.len() { Some(rows[insertion as int].expression) } else { None }
            } else { None },
    }
}

/// 仮引数の宣言順に、綴りが最初に一致する添字を選ぶ。
pub open spec fn macro_parameter_selection(
    parameters: Seq<SignatureParameter>, name: Seq<u8>, index: Option<usize>,
) -> bool {
    match index {
        Some(index) => {
            &&& index < parameters.len() && parameters[index as int].name.spec_bytes() == name
            &&& forall|i: int| 0 <= i < index ==> (#[trigger] parameters[i]).name.spec_bytes() != name
        },
        None => forall|i: int| 0 <= i < parameters.len() ==> (#[trigger] parameters[i]).name.spec_bytes() != name,
    }
}

fn find_macro_parameter(parameters: &[SignatureParameter], name: &str) -> (index: Option<usize>)
    ensures macro_parameter_selection(parameters@, name.spec_bytes(), index),
{
    let mut i = 0;
    while i < parameters.len()
        invariant i <= parameters@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] parameters@[j]).name.spec_bytes() != name.spec_bytes(),
        decreases parameters@.len() - i,
    {
        let parameter = parameters[i].name;
        if is_spelling(parameter, name) { return Some(i); }
        i += 1;
    }
    None
}

/// 仮引数の参照として評価できるフォームの綴りを返す。
pub open spec fn macro_direct_name(source: &str, forms: Seq<Form>, at: usize) -> Option<Seq<u8>> {
    let form = forms[at as int];
    let span = form_span(form);
    let word = source.spec_bytes()[span.start as int..span.end as int];
    if (form matches Form::Atom { kind: AtomKind::Name, .. })
        && word != "true".spec_bytes() && word != "false".spec_bytes()
    {
        Some(word)
    } else {
        None
    }
}

fn read_macro_direct_name<'a>(source: &'a str, forms: &[Form], at: usize)
    -> (name: Option<&'a str>)
    requires at < forms@.len(), form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures (match name { Some(name) => Some(name.spec_bytes()), None => None })
        == macro_direct_name(source, forms@, at),
{
    if !is_name(&forms[at]) {
        return None;
    }
    let name = source_word(source, forms, at);
    if is_spelling(name, "true") || is_spelling(name, "false") { None } else { Some(name) }
}

/// 仮引数の名前を宣言順で照合し、実引数または未束縛の診断を返す。
#[verifier::opaque]
pub open spec fn macro_named_argument_result(
    bound: &BoundMacroCall, name: Seq<u8>, span: Range<usize>,
    result: Result<&MacroArgument, MacroArgumentError>,
) -> bool {
    exists|index: Option<usize>| #[trigger] macro_parameter_selection(bound.body_model().parameters_model(), name, index)
        && match index {
            Some(i) => i < bound.arguments_model().len()
                && (result matches Ok(argument) && *argument == bound.arguments_model()[i as int]),
            None => result == Err(MacroArgumentError::Unbound(span)),
        }
}

/// 仮引数名だけを評価し、選んだ位置の元の構文を返す。
pub open spec fn macro_argument_expression_result(
    bound: &BoundMacroCall, site: MacroExpressionSite, result: Result<&MacroArgument, MacroArgumentError>,
) -> bool {
    let body = bound.body_model();
    let forms = body.body_model().forms@;
    let source = body.body_model().source.text_model();
    if let Some(at) = macro_expression_position(&body, site) {
        if at >= forms.len() {
            result == Err(MacroArgumentError::NoExpression)
        } else {
            let span = form_span(forms[at as int]);
            if let Some(name) = macro_direct_name(source, forms, at) {
                macro_named_argument_result(bound, name, span, result)
            } else {
                result == Err(MacroArgumentError::Deferred(span))
            }
        }
    } else {
        result == Err(MacroArgumentError::NoExpression)
    }
}

// 照合で決めた添字を、実引数または未束縛の診断を返す仕様の証人にする。
proof fn macro_argument_result_by_selection(
    bound: &BoundMacroCall, site: MacroExpressionSite, at: usize, name: Seq<u8>, index: Option<usize>,
    result: Result<&MacroArgument, MacroArgumentError>,
)
    requires
        macro_expression_position(&bound.body_model(), site) == Some(at),
        at < bound.body_model().body_model().forms@.len(),
        macro_direct_name(bound.body_model().body_model().source.text_model(),
            bound.body_model().body_model().forms@, at) == Some(name),
        macro_parameter_selection(bound.body_model().parameters_model(), name, index),
        match index {
            Some(i) => i < bound.arguments_model().len()
                && (result matches Ok(argument) && *argument == bound.arguments_model()[i as int]),
            None => result == Err(MacroArgumentError::Unbound(form_span(bound.body_model().body_model().forms@[at as int]))),
        },
    ensures macro_argument_expression_result(bound, site, result),
{
    let body = bound.body_model();
    let span = form_span(body.body_model().forms@[at as int]);
    assert(macro_named_argument_result(bound, name, span, result)) by {
        reveal(macro_named_argument_result);
    };
}

/// 実引数が同じスコープ・構文木を保ち、引数の元範囲を順につなぎ合わせる。
pub open spec fn macro_arguments_cover(
    scope: MacroArgumentScope, forms: Seq<Form>, extent: Range<usize>, arguments: Seq<MacroArgument>,
) -> bool {
    &&& extent.start <= extent.end <= forms.len()
    &&& if arguments.len() == 0 { extent.start == extent.end }
        else { arguments.last().nodes_model().end == extent.end }
    &&& forall|i: int| 0 <= i < arguments.len() ==> {
        let argument = #[trigger] arguments[i];
        let nodes = argument.nodes_model();
        &&& argument.scope_model() == scope && argument.forms_model() == forms
        &&& extent.start <= nodes.start < nodes.end <= extent.end
        &&& nodes.start == if i == 0 { extent.start } else { arguments[i - 1].nodes_model().end }
        &&& nodes.end == match forms[nodes.start as int] {
            Form::Atom { .. } => nodes.start + 1,
            Form::List { end, .. } => end as int,
        }
    }
}

// 呼び出しカーソルが同じ解決先に対して取得した型検査結果と引数列を結び付ける。
pub(crate) fn bind_macro_call<'p, 'a>(
    site: RoutineExpansionSite, definition: ResolvedDefmacro<'p, 'a>,
    body: CheckedMacroBody<'p, 'a>, mut pending: MacroArguments<'p, 'a>,
) -> (bound: BoundMacroCall<'p, 'a>)
    requires pending.valid(),
        pending.count_model() == body.parameters_model().len(),
        pending.remaining_model() == site.arguments,
        checked_macro_body_layout(&body),
    ensures bound.valid(), bound.site_model() == site, bound.scope_model() == pending.scope_model(),
        bound.definition_model() == definition, bound.body_model() == body,
        macro_arguments_cover(bound.scope_model(), pending.forms_model(), site.arguments, bound.arguments_model()),
{
    proof { pending.remaining_bounds(); }
    let scope = pending.scope();
    let ghost forms = pending.forms_model();
    let mut arguments = Vec::with_capacity(pending.remaining_count());
    while pending.remaining_count() > 0
        invariant
            pending.valid(), pending.scope_model() == scope, pending.forms_model() == forms,
            site.arguments.start <= pending.remaining_model().start <= pending.remaining_model().end == site.arguments.end,
            pending.count_model() + arguments@.len() == body.parameters_model().len(),
            macro_arguments_cover(scope, forms, site.arguments.start..pending.remaining_model().start, arguments@),
        decreases pending.count_model(),
    {
        let ghost start = pending.remaining_model().start;
        let ghost prefix = arguments@;
        let Some(argument) = pending.next_argument() else { unreachable!() };
        arguments.push(argument);
        let ghost end = pending.remaining_model().start;
        assert(macro_arguments_cover(scope, forms, site.arguments.start..end, arguments@)) by {
            assert forall|i: int| 0 <= i < arguments@.len() implies {
                let row = #[trigger] arguments@[i];
                let nodes = row.nodes_model();
                &&& row.scope_model() == scope && row.forms_model() == forms
                &&& site.arguments.start <= nodes.start < nodes.end <= end
                &&& nodes.start == if i == 0 { site.arguments.start } else { arguments@[i - 1].nodes_model().end }
                &&& nodes.end == match forms[nodes.start as int] {
                    Form::Atom { .. } => nodes.start + 1,
                    Form::List { end, .. } => end as int,
                }
            } by {
                if i < prefix.len() {
                    assert(arguments@[i] == prefix[i]);
                    assert(macro_arguments_cover(scope, forms, site.arguments.start..start, prefix));
                }
            };
        };
    }
    let _tail = pending.next_argument();
    assert(_tail.is_none() && pending.remaining_model().start == site.arguments.end);
    BoundMacroCall { site, scope, definition, body, arguments }
}

} // verus!
