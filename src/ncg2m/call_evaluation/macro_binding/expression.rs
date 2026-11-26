//! マクロの仮引数への参照を、仮引数一つずつ実引数に対応付ける。

use core::ops::Range;

use super::{BoundMacroCall, MacroArgumentError, MacroExpressionSite, read_macro_direct_name};
use crate::ncg2m::{
    defn::span_of,
    forms::is_spelling,
    template::InsertionKind,
};
use crate::project::MacroArgument;
#[cfg(verus_only)]
use super::{
    macro_argument_expression_result, macro_argument_result_by_selection, macro_direct_name, macro_expression_position,
    macro_parameter_selection,
};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::{CheckedMacroBody, macro_element_origin};
#[cfg(verus_only)]
use crate::syntax::form_span;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 一つのリスト要素または挿入式を評価する途中状態。
pub struct MacroExpressionEvaluation<'b, 'p, 'a> {
    bound: &'b BoundMacroCall<'p, 'a>,
    site: MacroExpressionSite,
    expected: InsertionKind,
    at: usize,
    span: Range<usize>,
    name: Option<&'a str>,
    next: usize,
}

/// 指定した式の評価が一段進んだ結果。
pub enum MacroExpressionStep<'b, 'p, 'a> {
    /// 元の回路本体から借りた構文値。
    Value(&'b MacroArgument<'p, 'a>),
    /// 次の仮引数から照合を続ける。
    Continue(MacroExpressionEvaluation<'b, 'p, 'a>),
}

impl<'b, 'p, 'a> MacroExpressionEvaluation<'b, 'p, 'a> {
    /// 対象の実引数と型検査済み本体を表す。
    pub closed spec fn bound_model(&self) -> &'b BoundMacroCall<'p, 'a> { self.bound }

    /// この評価が対象とするリスト要素または挿入式を表す。
    pub closed spec fn site_model(&self) -> MacroExpressionSite { self.site }

    /// 式の構文木上の根を表す。
    pub closed spec fn position_model(&self) -> usize { self.at }

    /// 型検査で式に求めた値の形を表す。
    pub closed spec fn expected_model(&self) -> InsertionKind { self.expected }

    /// 式全体の元範囲を表す。
    pub closed spec fn span_model(&self) -> Range<usize> { self.span }

    /// 仮引数を照合する式の綴りを表す。
    pub closed spec fn name_model(&self) -> Option<&str> { self.name }

    /// まだ照合していない最初の仮引数の添字を表す。
    pub closed spec fn next_model(&self) -> usize { self.next }

    /// 照合を始めた式の出典と、これまでに照合した仮引数の条件を表す。
    pub open spec fn ready(&self) -> bool {
        let bound = self.bound_model();
        let body = bound.body_model();
        let retained = body.body_model();
        let at = self.position_model();
        let parameters = body.parameters_model();
        &&& bound.valid()
        &&& macro_expression_position(&body, self.site_model()) == Some(at)
        &&& macro_expression_expected(&body, self.site_model()) == Some(self.expected_model())
        &&& at < retained.forms@.len() && self.span_model() == form_span(retained.forms@[at as int])
        &&& (match self.name_model() { Some(name) => Some(name.spec_bytes()), None => None })
            == if self.expected_model() is Syntax {
                macro_direct_name(retained.source.text_model(), retained.forms@, at)
            } else { None }
        &&& self.next_model() <= parameters.len()
        &&& if let Some(name) = self.name_model() {
            forall|i: int| 0 <= i < self.next_model() ==> (#[trigger] parameters[i]).name.spec_bytes() != name.spec_bytes()
        } else { self.next_model() == 0 }
    }

    /// 残りの照合回数と、仮引数が尽きたことを確認する1回の合計を表す。
    pub open spec fn remaining_bound(&self) -> nat {
        (1 + self.bound_model().body_model().parameters_model().len() - self.next_model()) as nat
    }

    /// 式全体の定義側ソースにおける UTF-8 半開バイト範囲を返す。
    pub fn span(&self) -> (span: Range<usize>)
        ensures span == self.span_model(),
    {
        self.span.start..self.span.end
    }

    /// 仮引数を一つ照合するか、対応する元の構文または診断を返す。
    ///
    /// 先行する仮引数が一致しなければ、照合を続ける状態が返る。
    ///
    /// # Errors
    ///
    /// 仮引数が見つからない場合は定義側の式の元範囲を返す。
    /// 仮引数参照以外の式やリスト値は後続の評価に保留する。
    pub fn step(self) -> (result: Result<MacroExpressionStep<'b, 'p, 'a>, MacroArgumentError>)
        requires self.ready(),
        ensures macro_expression_step_matches(self, result),
            result matches Ok(MacroExpressionStep::Continue(next)) ==>
                next.ready() && next.remaining_bound() < self.remaining_bound(),
    {
        let Some(name) = self.name else { return Err(MacroArgumentError::Deferred(self.span)); };
        let checked = self.bound.body();
        let parameters = checked.parameters();
        if self.next == parameters.len() {
            proof {
                assert(macro_parameter_selection(parameters@, name.spec_bytes(), None));
                macro_argument_result_by_selection(self.bound, self.site, self.at, name.spec_bytes(), None,
                    Err(MacroArgumentError::Unbound(self.span)));
            }
            return Err(MacroArgumentError::Unbound(self.span));
        }
        if is_spelling(parameters[self.next].name, name) {
            let value = &self.bound.arguments()[self.next];
            proof {
                assert(macro_parameter_selection(parameters@, name.spec_bytes(), Some(self.next)));
                macro_argument_result_by_selection(self.bound, self.site, self.at, name.spec_bytes(),
                    Some(self.next), Ok(value));
            }
            return Ok(MacroExpressionStep::Value(value));
        }
        let next = self.next + 1;
        let later = Self { next, ..self };
        proof {
            assert forall|i: int| 0 <= i < next implies
                (#[trigger] parameters@[i]).name.spec_bytes() != name.spec_bytes() by {};
        }
        Ok(MacroExpressionStep::Continue(later))
    }
}

/// 型検査で指定した式に求めた値の形を返す。
pub open spec fn macro_expression_expected(
    body: &CheckedMacroBody, site: MacroExpressionSite,
) -> Option<InsertionKind> {
    let elements = body.elements_model();
    match site {
        MacroExpressionSite::Element(element) =>
            if element < elements.len() { Some(InsertionKind::Syntax) } else { None },
        MacroExpressionSite::Insertion { element, insertion } =>
            if element < elements.len() && insertion < elements[element as int].insertions_model().len() {
                Some(elements[element as int].insertions_model()[insertion as int].expected)
            } else { None },
    }
}

/// 仮引数の式の意味と、対応する元ソースの構文値または診断を結び付ける。
pub open spec fn macro_expression_evaluation_result<'b, 'p, 'a>(
    bound: &'b BoundMacroCall<'p, 'a>, site: MacroExpressionSite,
    outcome: Result<&'b MacroArgument<'p, 'a>, MacroArgumentError>,
) -> bool {
    let body = bound.body_model();
    if macro_expression_expected(&body, site) == Some(InsertionKind::List) {
        if let Some(at) = macro_expression_position(&body, site) {
            let forms = body.body_model().forms@;
            at < forms.len() && outcome == Err(MacroArgumentError::Deferred(form_span(forms[at as int])))
        } else { false }
    } else {
        macro_argument_expression_result(bound, site, outcome)
    }
}

/// 照合一回分の進捗、値、診断を決める。
pub open spec fn macro_expression_step_matches<'b, 'p, 'a>(
    state: MacroExpressionEvaluation<'b, 'p, 'a>,
    result: Result<MacroExpressionStep<'b, 'p, 'a>, MacroArgumentError>,
) -> bool {
    let parameters = state.bound_model().body_model().parameters_model();
    let next = state.next_model();
    let bound = state.bound_model();
    let site = state.site_model();
    &&& state.ready()
    &&& if let Some(name) = state.name_model() {
        if next == parameters.len() {
            result == Err(MacroArgumentError::Unbound(state.span_model()))
                && macro_expression_evaluation_result(bound, site, Err(MacroArgumentError::Unbound(state.span_model())))
        } else if parameters[next as int].name.spec_bytes() == name.spec_bytes() {
            result matches Ok(MacroExpressionStep::Value(argument))
                && *argument == bound.arguments_model()[next as int]
                && macro_expression_evaluation_result(bound, site, Ok(argument))
        } else {
            result matches Ok(MacroExpressionStep::Continue(after))
                && after.bound_model() == state.bound_model() && after.site_model() == state.site_model()
                && after.expected_model() == state.expected_model() && after.position_model() == state.position_model()
                && after.span_model() == state.span_model() && after.name_model() == state.name_model()
                && after.next_model() == next + 1
        }
    } else {
        result == Err(MacroArgumentError::Deferred(state.span_model()))
            && macro_expression_evaluation_result(bound, site, Err(MacroArgumentError::Deferred(state.span_model())))
    }
}

/// 同じ束縛の同じ式を、同じ仮引数から照合する状態である。
pub open spec fn macro_expression_states_agree<'b, 'p, 'a>(
    a: &MacroExpressionEvaluation<'b, 'p, 'a>, b: &MacroExpressionEvaluation<'b, 'p, 'a>,
) -> bool {
    &&& a.bound_model() == b.bound_model()
    &&& a.site_model() == b.site_model()
    &&& a.next_model() == b.next_model()
}

/// 一遷移で同じ元の実引数、診断、または再開状態を得ることを表す。
pub open spec fn macro_expression_step_results_agree<'b, 'p, 'a>(
    a: Result<MacroExpressionStep<'b, 'p, 'a>, MacroArgumentError>,
    b: Result<MacroExpressionStep<'b, 'p, 'a>, MacroArgumentError>,
) -> bool {
    match (a, b) {
        (Ok(MacroExpressionStep::Value(a)), Ok(MacroExpressionStep::Value(b))) => *a == *b,
        (Ok(MacroExpressionStep::Continue(a)), Ok(MacroExpressionStep::Continue(b))) =>
            macro_expression_states_agree(&a, &b),
        (Err(a), Err(b)) => a == b,
        _ => false,
    }
}

/// 同じ位置からの照合は、生成する値、診断、次の照合位置を一意に決める。
pub proof fn macro_expression_steps_agree<'b, 'p, 'a>(
    a: &MacroExpressionEvaluation<'b, 'p, 'a>, b: &MacroExpressionEvaluation<'b, 'p, 'a>,
    result_a: Result<MacroExpressionStep<'b, 'p, 'a>, MacroArgumentError>,
    result_b: Result<MacroExpressionStep<'b, 'p, 'a>, MacroArgumentError>,
)
    requires macro_expression_states_agree(a, b),
        macro_expression_step_matches(*a, result_a), macro_expression_step_matches(*b, result_b),
    ensures macro_expression_step_results_agree(result_a, result_b),
{
    assert(a.ready() && b.ready());
    assert(a.position_model() == b.position_model());
    assert(a.expected_model() == b.expected_model());
    assert(a.span_model() == b.span_model());
    if let Some(a_name) = a.name_model() {
        assert(b.name_model() is Some);
        assert(a_name.spec_bytes() == b.name_model()->Some_0.spec_bytes());
    } else {
        assert(b.name_model() is None);
    }
}

/// 指定した式が本体にあれば、同じ束縛と式を先頭の仮引数から評価し始める。
pub open spec fn macro_expression_start_matches<'b, 'p, 'a>(
    bound: &'b BoundMacroCall<'p, 'a>, site: MacroExpressionSite,
    state: Option<MacroExpressionEvaluation<'b, 'p, 'a>>,
) -> bool {
    &&& state.is_some() <==> macro_expression_position(&bound.body_model(), site).is_some()
    &&& state matches Some(state) ==> state.ready() && state.bound_model() == bound
        && state.site_model() == site && state.next_model() == 0
}

/// 同じ呼び出しの同じ式から開始すると、式が存在しないか同じ照合位置に決まる。
pub proof fn macro_expression_starts_agree<'b, 'p, 'a>(
    bound: &'b BoundMacroCall<'p, 'a>, site: MacroExpressionSite,
    a: Option<MacroExpressionEvaluation<'b, 'p, 'a>>,
    b: Option<MacroExpressionEvaluation<'b, 'p, 'a>>,
)
    requires macro_expression_start_matches(bound, site, a), macro_expression_start_matches(bound, site, b),
    ensures match (a, b) {
        (Some(a), Some(b)) => macro_expression_states_agree(&a, &b),
        (None, None) => true,
        _ => false,
    },
{}

impl<'p, 'a> BoundMacroCall<'p, 'a> {
    /// 型検査済みのリスト要素またはテンプレートの挿入式の評価を始める。
    ///
    /// 式の位置が元の本体の範囲外なら `None`。呼び出し側の構文を借りたまま評価を進める。
    pub fn start_expression<'b>(&'b self, site: MacroExpressionSite)
        -> (state: Option<MacroExpressionEvaluation<'b, 'p, 'a>>)
        requires self.valid(),
        ensures macro_expression_start_matches(self, site, state),
    {
        let checked = self.body();
        let body = checked.body();
        let elements = checked.elements();
        let (at, expected) = match site {
            MacroExpressionSite::Element(index) => {
                let element = elements.get(index)?;
                proof { assert(macro_element_origin(body.source.text_model(), body.forms@,
                    checked.parameters_model(), *element)); }
                (element.at(), InsertionKind::Syntax)
            },
            MacroExpressionSite::Insertion { element, insertion } => {
                let current = elements.get(element)?;
                let row = current.insertions().get(insertion)?;
                proof { assert(macro_element_origin(body.source.text_model(), body.forms@,
                    checked.parameters_model(), *current)); }
                (row.expression, row.expected)
            },
        };
        let form = &body.forms[at];
        let source = body.source.text();
        let span = span_of(form);
        let name = if matches!(expected, InsertionKind::Syntax) {
            read_macro_direct_name(source, body.forms, at)
        } else { None };
        Some(MacroExpressionEvaluation { bound: self, site, expected, at, span, name, next: 0 })
    }
}

} // verus!
