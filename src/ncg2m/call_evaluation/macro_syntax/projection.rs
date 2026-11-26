//! 展開済みテンプレートを、元の構文木と名前の出典を保ったイベント列として読む。

use super::{ArgumentSyntax, ArgumentSyntaxToken};
use super::super::{
    macro_binding::BoundMacroCall,
    macro_expansion::{MacroExpandedBody, MacroExpandedElement},
};
use crate::ncg2m::template::{ExpandedTemplate, TemplateEmission};
use crate::project::{MacroArgument, ProjectSource};
use crate::syntax::Form;
#[cfg(verus_only)]
use crate::syntax::form_spans_valid;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use crate::ncg2m::template::{TemplateAssembly, TemplateAssemblySlice, TemplateEmitter, template_assembly_trace_result};
#[cfg(verus_only)]
use super::super::macro_expansion::macro_expanded_element_matches;
#[cfg(verus_only)]
use super::argument_syntax_step;
use vstd::prelude::*;

verus! {

/// 構文の項目が現れた文書と、識別子を解決する位置。
#[derive(Clone, Copy, Debug)]
pub enum MacroSyntaxOrigin<'b, 'p, 'a> {
    /// テンプレートの元構文木と、定義を導入した展開呼び出し。
    Template(&'b BoundMacroCall<'p, 'a>),
    /// 呼び出し元の構文木と、引数に含まれる名前を読む範囲。
    Argument(&'b MacroArgument<'p, 'a>),
}

impl<'b, 'p, 'a> MacroSyntaxOrigin<'b, 'p, 'a> {
    /// 項目の元文書と文書版を表す。
    pub open spec fn source_model(self) -> &'p ProjectSource<'a> {
        match self {
            Self::Template(call) => call.body_model().body_model().source,
            Self::Argument(argument) => argument.scope_model().source,
        }
    }

    /// 項目の添字が指す元の構文木を表す。
    pub open spec fn forms_model(self) -> Seq<Form> {
        match self {
            Self::Template(call) => call.body_model().body_model().forms@,
            Self::Argument(argument) => argument.forms_model(),
        }
    }

    /// 元文書を返す。テンプレートでは定義側、挿入断片では実引数の文書を返す。
    pub fn source(self) -> (source: &'p ProjectSource<'a>)
        ensures source == self.source_model(),
    {
        match self {
            Self::Template(call) => call.body().body().source,
            Self::Argument(argument) => argument.scope().source,
        }
    }

    /// 元の構文木を借りる。添字の付け替えや再解析を行わない。
    pub fn forms(self) -> (forms: &'p [Form])
        ensures forms@ == self.forms_model(),
    {
        match self {
            Self::Template(call) => call.body().body().forms,
            Self::Argument(argument) => argument.forms(),
        }
    }
}

/// 元の添字と名前解決の位置を持つ一つの構文イベント。
#[derive(Clone, Copy, Debug)]
pub struct MacroSyntaxEvent<'b, 'p, 'a> {
    /// 添字を解釈する文書と構文木。
    pub origin: MacroSyntaxOrigin<'b, 'p, 'a>,
    /// リストの開始、アトム、またはリストの終了。添字を変更しない。
    pub token: ArgumentSyntaxToken,
}

/// トークンの添字が元の構文木にあり、リストまたはアトムの種別が一致する。
pub open spec fn syntax_token_matches_forms(forms: Seq<Form>, token: ArgumentSyntaxToken) -> bool {
    match token {
        ArgumentSyntaxToken::Atom(at) => at < forms.len() && forms[at as int] is Atom,
        ArgumentSyntaxToken::Open(at) | ArgumentSyntaxToken::Close(at) =>
            at < forms.len() && forms[at as int] is List,
    }
}

/// イベントの添字が元の構文木にあり、リストまたはアトムの種別が一致することを表す。
pub open spec fn syntax_event_in_source(event: MacroSyntaxEvent) -> bool {
    let forms = event.origin.forms_model();
    let text = event.origin.source_model().text_model();
    &&& syntax_token_matches_forms(forms, event.token)
    &&& form_spans_valid(text, forms, text.spec_bytes().len() as int)
}

/// テンプレートの走査時に、出力項目を元の構文木に結び付けられなかった。
#[derive(Debug)]
pub struct MacroTemplateSyntaxError<'b, 'p, 'a> {
    /// 主範囲を持つ展開呼び出し。
    pub call: &'b BoundMacroCall<'p, 'a>,
    /// 展開結果での要素番号。
    pub element: usize,
    /// 元の構文木で参照できなかった項目。
    pub token: ArgumentSyntaxToken,
}

/// 一つの実行ステップで得た構文と再開位置。
pub enum MacroTemplateSyntaxStep<'s, 'b, 'p, 'a> {
    /// このテンプレートの末尾に達した。
    Complete,
    /// 途中まで進んだ。引数の開始と終了のステップではイベントがない。
    Continue {
        /// 次に構文組み立てへ渡すイベント。
        event: Option<MacroSyntaxEvent<'b, 'p, 'a>>,
        /// 実行を再開するための状態。
        next: MacroTemplateSyntax<'s, 'b, 'p, 'a>,
    },
}

type Emission<'b, 'p, 'a> = TemplateEmission<'b, MacroArgument<'p, 'a>>;

/// 展開済みテンプレートと、途中の挿入断片を一つずつ走査する。
pub struct MacroTemplateSyntax<'s, 'b, 'p, 'a> {
    call: &'b BoundMacroCall<'p, 'a>,
    element: usize,
    parts: &'s [Emission<'b, 'p, 'a>],
    at: usize,
    splice: &'b [MacroArgument<'p, 'a>],
    splice_at: usize,
    argument: Option<ArgumentSyntax<'b, 'p, 'a>>,
}

impl<'s, 'b, 'p, 'a> MacroTemplateSyntax<'s, 'b, 'p, 'a> {
    /// 元の展開呼び出しを表す。
    pub closed spec fn call_model(&self) -> &'b BoundMacroCall<'p, 'a> { self.call }

    /// 展開結果の要素番号を表す。
    pub closed spec fn element_model(&self) -> usize { self.element }

    /// 評価済みテンプレートの項目を表す。
    pub closed spec fn parts_model(&self) -> Seq<Emission<'b, 'p, 'a>> { self.parts@ }

    /// テンプレート内の次の項目を表す。
    pub closed spec fn at_model(&self) -> usize { self.at }

    /// 現在の挿入リストを表す。
    pub closed spec fn splice_model(&self) -> Seq<MacroArgument<'p, 'a>> { self.splice@ }

    /// 挿入リストの次の実引数を表す。
    pub closed spec fn splice_at_model(&self) -> usize { self.splice_at }

    /// 現在走査している実引数の部分木を表す。
    pub closed spec fn argument_model(&self) -> Option<ArgumentSyntax<'b, 'p, 'a>> { self.argument }

    /// 項目の添字が有効であり、途中の引数から走査を再開できる。
    pub open spec fn valid(&self) -> bool {
        &&& self.call_model().valid()
        &&& self.at_model() <= self.parts_model().len()
        &&& self.splice_at_model() <= self.splice_model().len()
        &&& (self.argument_model() matches Some(argument) ==> argument.valid())
    }

    /// 残りのテンプレート項目、挿入リストの要素、現在の引数の走査量を表す。
    pub open spec fn remaining(&self) -> (nat, nat, nat) {
        let argument = match self.argument_model() {
            Some(argument) => argument.remaining_bound() + 1,
            None => 0,
        };
        ((self.parts_model().len() - self.at_model()) as nat,
            (self.splice_model().len() - self.splice_at_model()) as nat, argument)
    }

    /// テンプレート、挿入リスト、引数の順に残りの作業が減る。
    pub open spec fn advances(&self, previous: &Self) -> bool {
        let (parts, splice, argument) = self.remaining();
        let (before_parts, before_splice, before_argument) = previous.remaining();
        parts < before_parts || parts == before_parts && (
            splice < before_splice || splice == before_splice && argument < before_argument)
    }

    fn emit_literal(self, token: ArgumentSyntaxToken)
        -> (result: Result<MacroTemplateSyntaxStep<'s, 'b, 'p, 'a>, MacroTemplateSyntaxError<'b, 'p, 'a>>)
        requires self.valid(), self.at_model() < self.parts_model().len(),
        ensures literal_transition(self, token, result),
            result matches Ok(MacroTemplateSyntaxStep::Continue { event, next }) ==>
                next.valid() && next.advances(&self) && (event matches Some(event) && syntax_event_in_source(event)),
    {
        let origin = MacroSyntaxOrigin::Template(self.call);
        let forms = origin.forms();
        let accepted = match token {
            ArgumentSyntaxToken::Atom(at) => matches!(forms.get(at), Some(Form::Atom { .. })),
            ArgumentSyntaxToken::Open(at) | ArgumentSyntaxToken::Close(at) =>
                matches!(forms.get(at), Some(Form::List { .. })),
        };
        if !accepted {
            return Err(MacroTemplateSyntaxError { call: self.call, element: self.element, token });
        }
        let event = MacroSyntaxEvent { origin, token };
        let _length = self.parts.len();
        let next = Self { at: self.at + 1, ..self };
        Ok(MacroTemplateSyntaxStep::Continue { event: Some(event), next })
    }

    /// コンパイル済みのテンプレートから一歩だけ構文を読む。
    ///
    /// 一歩ではテンプレートの項目を一件進めるか、挿入する引数の部分木を一件進める。
    /// リスト全体をコピーせず、各項目は元の文書と構文木を参照する。
    ///
    /// # Errors
    ///
    /// テンプレートのリテラルが同じ種類の元フォームを指さなければ、その項目を診断する。
    pub fn step(mut self)
        -> (result: Result<MacroTemplateSyntaxStep<'s, 'b, 'p, 'a>, MacroTemplateSyntaxError<'b, 'p, 'a>>)
        requires self.valid(),
        ensures macro_template_syntax_step_matches(self, result),
            result matches Ok(MacroTemplateSyntaxStep::Continue { event, next }) ==>
                next.valid() && next.advances(&self) && (event matches Some(event) ==> syntax_event_in_source(event)),
    {
        if let Some(ref mut argument) = self.argument {
            let origin = MacroSyntaxOrigin::Argument(argument.argument());
            let ghost before = *argument;
            if let Some(token) = argument.next() {
                proof { argument_event_in_source(&before, argument, token); }
                return Ok(MacroTemplateSyntaxStep::Continue {
                    event: Some(MacroSyntaxEvent { origin, token }), next: self,
                });
            }
            self.argument = None;
            return Ok(MacroTemplateSyntaxStep::Continue { event: None, next: self });
        }
        if self.splice_at < self.splice.len() {
            let argument = &self.splice[self.splice_at];
            let _ = argument.forms();
            self.argument = Some(argument.walk_syntax());
            self.splice_at += 1;
            return Ok(MacroTemplateSyntaxStep::Continue { event: None, next: self });
        }
        let _length = self.parts.len();
        let Some(part) = self.parts.get(self.at) else { return Ok(MacroTemplateSyntaxStep::Complete); };
        match part {
            TemplateEmission::Atom(at) => self.emit_literal(ArgumentSyntaxToken::Atom(*at)),
            TemplateEmission::Open(at) => self.emit_literal(ArgumentSyntaxToken::Open(*at)),
            TemplateEmission::Close(at) => self.emit_literal(ArgumentSyntaxToken::Close(*at)),
            TemplateEmission::Insert(argument) => {
                let _ = argument.forms();
                self.argument = Some(argument.walk_syntax());
                self.at += 1;
                Ok(MacroTemplateSyntaxStep::Continue { event: None, next: self })
            },
            TemplateEmission::Splice(arguments) => {
                self.splice = arguments;
                self.splice_at = 0;
                self.at += 1;
                Ok(MacroTemplateSyntaxStep::Continue { event: None, next: self })
            },
        }
    }
}

proof fn argument_event_in_source(before: &ArgumentSyntax, after: &ArgumentSyntax, token: ArgumentSyntaxToken)
    requires before.valid(), argument_syntax_step(before, after, Some(token)),
    ensures syntax_event_in_source(MacroSyntaxEvent {
        origin: MacroSyntaxOrigin::Argument(before.argument_model()), token,
    }),
{
    reveal(ArgumentSyntax::valid);
    let open = before.open_model();
    if open.len() > 0 && open.last().end == before.at_model() {
        assert(open.last() == open[open.len() - 1]);
    }
}

spec fn same_projection_input(a: &MacroTemplateSyntax, b: &MacroTemplateSyntax) -> bool {
    a.call_model() == b.call_model() && a.element_model() == b.element_model() && a.parts_model() == b.parts_model()
}

spec fn same_splice(a: &MacroTemplateSyntax, b: &MacroTemplateSyntax) -> bool {
    a.splice_model() == b.splice_model() && a.splice_at_model() == b.splice_at_model()
}

spec fn argument_begins(walker: Option<ArgumentSyntax>, argument: &MacroArgument) -> bool {
    walker matches Some(walker) && walker.argument_model() == argument
        && walker.at_model() == argument.nodes_model().start && walker.open_model().len() == 0
}

spec fn literal_transition(
    previous: MacroTemplateSyntax, token: ArgumentSyntaxToken,
    result: Result<MacroTemplateSyntaxStep, MacroTemplateSyntaxError>,
) -> bool {
    let origin = MacroSyntaxOrigin::Template(previous.call_model());
    if syntax_token_matches_forms(origin.forms_model(), token) {
        result matches Ok(MacroTemplateSyntaxStep::Continue { event, next })
            && event == Some(MacroSyntaxEvent { origin, token }) && same_projection_input(&previous, &next)
            && next.at_model() == previous.at_model() + 1 && same_splice(&previous, &next)
            && next.argument_model() == previous.argument_model()
    } else {
        result == Err(MacroTemplateSyntaxError {
            call: previous.call_model(), element: previous.element_model(), token,
        })
    }
}

/// 構文走査の一歩を、元の項目順、挿入リストと引数の走査位置から定める。
pub closed spec fn macro_template_syntax_step_matches(
    previous: MacroTemplateSyntax, result: Result<MacroTemplateSyntaxStep, MacroTemplateSyntaxError>,
) -> bool {
    if let Some(argument) = previous.argument_model() {
        &&& result matches Ok(MacroTemplateSyntaxStep::Continue { event, next })
        &&& same_projection_input(&previous, &next) && same_splice(&previous, &next)
        &&& next.at_model() == previous.at_model()
        &&& match event {
            Some(event) => event.origin == MacroSyntaxOrigin::Argument(argument.argument_model())
                && (next.argument_model() matches Some(later)
                    && argument_syntax_step(&argument, &later, Some(event.token))),
            None => argument.remaining_bound() == 0 && next.argument_model().is_none(),
        }
    } else if previous.splice_at_model() < previous.splice_model().len() {
        &&& result matches Ok(MacroTemplateSyntaxStep::Continue { event: None, next })
        &&& same_projection_input(&previous, &next) && next.at_model() == previous.at_model()
        &&& next.splice_model() == previous.splice_model() && next.splice_at_model() == previous.splice_at_model() + 1
        &&& argument_begins(next.argument_model(), &previous.splice_model()[previous.splice_at_model() as int])
    } else if previous.at_model() >= previous.parts_model().len() {
        result is Ok && result->Ok_0 is Complete
    } else {
        match previous.parts_model()[previous.at_model() as int] {
            TemplateEmission::Atom(at) => literal_transition(previous, ArgumentSyntaxToken::Atom(at), result),
            TemplateEmission::Open(at) => literal_transition(previous, ArgumentSyntaxToken::Open(at), result),
            TemplateEmission::Close(at) => literal_transition(previous, ArgumentSyntaxToken::Close(at), result),
            TemplateEmission::Insert(argument) => {
                &&& result matches Ok(MacroTemplateSyntaxStep::Continue { event: None, next })
                &&& same_projection_input(&previous, &next) && next.at_model() == previous.at_model() + 1
                &&& same_splice(&previous, &next) && argument_begins(next.argument_model(), argument)
            },
            TemplateEmission::Splice(arguments) => {
                &&& result matches Ok(MacroTemplateSyntaxStep::Continue { event: None, next })
                &&& same_projection_input(&previous, &next) && next.at_model() == previous.at_model() + 1
                &&& next.splice_model() == arguments@ && next.splice_at_model() == 0 && next.argument_model().is_none()
            },
        }
    }
}

proof fn template_matches_definition<'b, 'p, 'a>(
    call: &'b BoundMacroCall<'p, 'a>, element: usize,
    syntax: ExpandedTemplate<'p, 'b, MacroArgument<'p, 'a>>,
    history: Ghost<(TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>, nat)>,
)
    requires macro_expanded_element_matches(call, element, MacroExpandedElement::Template { syntax, history }),
    ensures
        syntax.source_model() == MacroSyntaxOrigin::Template(call).source_model().text_model(),
        syntax.forms_model() == MacroSyntaxOrigin::Template(call).forms_model(),
{
    let (initial, fuel) = history@;
    let (states, parts) = choose|states: Seq<TemplateEmitter<'p, 'b, MacroArgument<'p, 'a>>>,
        parts: Seq<Emission<'b, 'p, 'a>>| #[trigger]
            template_assembly_trace_result(initial, fuel, states, parts, Ok(TemplateAssemblySlice::Complete(syntax)));
}

/// カーソルが選んだテンプレートの先頭から、挿入を開始していない状態にある。
pub open spec fn macro_template_syntax_starts_at(
    cursor: &MacroTemplateSyntax, body: &MacroExpandedBody, element: usize,
) -> bool {
    &&& cursor.valid() && cursor.call_model() == body.call_model()
    &&& element < body.elements_model().len()
    &&& body.elements_model()[element as int] is Template
    &&& cursor.element_model() == element && cursor.at_model() == 0
    &&& cursor.splice_at_model() == 0 && cursor.splice_model().len() == 0 && cursor.argument_model().is_none()
    &&& cursor.parts_model() == body.elements_model()[element as int]->Template_syntax.parts_model()
}

/// 終端には、テンプレート本体、挿入列と引数のすべてを消費して到達する。
pub proof fn completed_macro_template_syntax_consumed(cursor: MacroTemplateSyntax)
    requires cursor.valid(), macro_template_syntax_step_matches(cursor, Ok(MacroTemplateSyntaxStep::Complete)),
    ensures cursor.at_model() == cursor.parts_model().len(),
        cursor.splice_at_model() == cursor.splice_model().len(), cursor.argument_model().is_none(),
{}

impl<'b, 'p, 'a> MacroExpandedBody<'b, 'p, 'a> {
    /// 指定したテンプレートの元構文と挿入断片を、展開順に読む。
    ///
    /// 範囲外または直接の実引数を返す要素には `None` を返す。
    pub fn template_syntax<'s>(&'s self, element: usize)
        -> (result: Option<MacroTemplateSyntax<'s, 'b, 'p, 'a>>)
        ensures result.is_some() <==> element < self.elements_model().len()
            && self.elements_model()[element as int] is Template,
            result matches Some(state) ==> macro_template_syntax_starts_at(&state, self, element),
    {
        let elements = self.elements();
        let MacroExpandedElement::Template { syntax, history } = elements.get(element)? else { return None; };
        let call = self.call();
        proof { template_matches_definition(call, element, *syntax, *history); }
        Some(MacroTemplateSyntax {
            call, element, parts: syntax.parts(), at: 0, splice: &[], splice_at: 0, argument: None,
        })
    }
}

} // verus!
