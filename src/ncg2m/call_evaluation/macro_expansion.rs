//! 束縛済みのマクロ本体を、要素と挿入式の順に評価する。

use alloc::vec::Vec;
use core::num::NonZeroUsize;
use core::ops::Range;
use crate::ncg2m::template::{
    ExpandedTemplate, TemplateAssembly, TemplateAssemblySlice, TemplateEmissionError,
    TemplateSubstitution, assemble_owned_template,
};
use crate::project::{MacroArgument, ProjectSource};
use super::macro_binding::{
    BoundMacroCall, MacroArgumentError, MacroExpressionEvaluation, MacroExpressionSite, MacroExpressionStep,
};
#[cfg(verus_only)]
use super::macro_binding::{
    macro_expression_evaluation_result, macro_expression_position, macro_expression_step_matches,
};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::{CheckedMacroElement, macro_element_origin};
#[cfg(verus_only)]
use crate::syntax::form_span;
#[cfg(verus_only)]
use crate::ncg2m::template::{
    resumed_template_assembly_matches, template_assembly_matches, template_assembly_start,
    template_assembly_trace_result,
};
use vstd::prelude::*;

verus! {

/// リストの一要素を評価して得た構文。挿入した断片と定義由来の構文を区別する。
pub enum MacroExpandedElement<'b, 'p, 'a> {
    /// 呼び出し側の構文を、その位置とスコープを保持したまま使う。
    Argument(&'b MacroArgument<'p, 'a>),
    /// 定義側のテンプレートに、評価済みの構文を挿入した結果。
    Template {
        /// 元ソースと引数への参照を持つ展開済みの構文。
        syntax: ExpandedTemplate<'p, 'b, MacroArgument<'p, 'a>>,
        /// 展開の開始状態と、完了までに進めた遷移数の証明用記録。
        history: Ghost<(TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>, nat)>,
    },
}

/// 型検査済みの一つの呼び出しから得た、元のリスト順の構文。
///
/// 呼び出しと定義の出典を保持する。回路フォームの検査と新しい束縛の付与は後段で行う。
pub struct MacroExpandedBody<'b, 'p, 'a> {
    call: &'b BoundMacroCall<'p, 'a>,
    elements: Vec<MacroExpandedElement<'b, 'p, 'a>>,
}

impl<'b, 'p, 'a> MacroExpandedBody<'b, 'p, 'a> {
    /// 呼び出しと定義に対応する元の構文を指す。
    pub closed spec fn call_model(&self) -> &'b BoundMacroCall<'p, 'a> { self.call }

    /// 確定した要素を本体の順序で表す。
    pub closed spec fn elements_model(&self) -> Seq<MacroExpandedElement<'b, 'p, 'a>> { self.elements@ }

    /// 展開結果の各要素が、元の呼び出しの対応する式から得られたことを表す。
    pub open spec fn valid(&self) -> bool {
        let elements = self.elements_model();
        &&& self.call_model().valid()
        &&& elements.len() == self.call_model().body_model().elements_model().len()
        &&& forall|i: int| 0 <= i < elements.len() ==>
            macro_expanded_element_matches(self.call_model(), i as usize, #[trigger] elements[i])
    }

    #[verifier::type_invariant]
    spec fn expansion_invariant(&self) -> bool { self.valid() }

    /// 呼び出し位置、引数のスコープ、マクロの定義を保持した元の呼び出しを返す。
    pub fn call(&self) -> (call: &'b BoundMacroCall<'p, 'a>)
        ensures call == self.call_model(),
    {
        self.call
    }

    /// 評価済みの構文を、マクロ本体のリスト順で借りる。
    pub fn elements(&self) -> (elements: &[MacroExpandedElement<'b, 'p, 'a>])
        ensures elements@ == self.elements_model(), self.valid(),
    {
        proof { use_type_invariant(self); }
        self.elements.as_slice()
    }
}

/// マクロの要素を評価できなかった理由と、その元の呼び出し。
#[derive(Debug)]
pub struct MacroExpansionError<'b, 'p, 'a> {
    /// 主範囲と文書版を保持する元の呼び出し。
    pub call: &'b BoundMacroCall<'p, 'a>,
    /// 関連範囲を指す、マクロ定義の元の文書。
    pub definition: &'p ProjectSource<'a>,
    /// マクロ定義の本文を参照する UTF-8 半開バイト範囲。
    pub related: Range<usize>,
    /// 診断が発生した本体リストの要素番号。
    pub element: usize,
    /// 同じ呼び出しの中で最初に止まった原因。
    pub kind: MacroExpansionErrorKind,
}

/// マクロ本体を先へ進められなかった理由。
#[derive(Debug)]
pub enum MacroExpansionErrorKind {
    /// 現在の評価範囲では扱えない式、または引数束縛の診断。
    Expression {
        /// 評価できなかった要素または挿入式。
        site: MacroExpressionSite,
        /// 位置付きの評価診断。
        error: MacroArgumentError,
    },
    /// テンプレートの構文と挿入値の対応に関する診断。
    ///
    /// 関連範囲はテンプレートを含むリスト要素全体を指す。
    Template(TemplateEmissionError),
}

struct PendingTemplate<'b, 'p, 'a> {
    root: usize,
    values: Vec<TemplateSubstitution<'b, MacroArgument<'p, 'a>>>,
}

enum ExpansionPhase<'b, 'p, 'a> {
    Select,
    Insertions(PendingTemplate<'b, 'p, 'a>),
    Expression {
        expression: MacroExpressionEvaluation<'b, 'p, 'a>,
        template: Option<PendingTemplate<'b, 'p, 'a>>,
    },
    Assemble {
        current: TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>,
        history: Ghost<(TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>, nat)>,
    },
}

/// 確定前の展開状態。枠の間で中断する場合はこの値を破棄する。
pub struct MacroExpansion<'b, 'p, 'a> {
    call: &'b BoundMacroCall<'p, 'a>,
    completed: Vec<MacroExpandedElement<'b, 'p, 'a>>,
    phase: ExpansionPhase<'b, 'p, 'a>,
}

/// 一つの実行枠で到達した結果。
pub enum MacroExpansionSlice<'b, 'p, 'a> {
    /// リストの末尾に達したため、全要素を公開できる。
    Complete(MacroExpandedBody<'b, 'p, 'a>),
    /// 実行枠を使い切った。完成前の要素を保持して次の枠へ進む。
    Suspended(MacroExpansion<'b, 'p, 'a>),
}

/// テンプレートの挿入値が、元の式の評価結果を順に保持することを表す。
pub open spec fn macro_insertion_values<'b, 'p, 'a>(
    call: &'b BoundMacroCall<'p, 'a>, index: usize, count: nat,
    values: Seq<TemplateSubstitution<'b, MacroArgument<'p, 'a>>>,
) -> bool {
    &&& values.len() <= count
    &&& forall|i: int| 0 <= i < values.len() ==> {
        &&& (#[trigger] values[i]) matches TemplateSubstitution::One(value)
        &&& macro_expression_evaluation_result(call,
            MacroExpressionSite::Insertion { element: index, insertion: i as usize }, Ok(value))
    }
}

impl<'b, 'p, 'a> PendingTemplate<'b, 'p, 'a> {
    spec fn ready(&self, element: CheckedMacroElement, call: &'b BoundMacroCall<'p, 'a>, index: usize) -> bool {
        &&& element.template_model() == Some(self.root)
        &&& macro_insertion_values(call, index, element.insertions_model().len(), self.values@)
    }
}

/// 組み立ての開始状態が、指定した要素と全挿入式に対応することを表す。
pub open spec fn macro_template_origin<'b, 'p, 'a>(
    call: &'b BoundMacroCall<'p, 'a>, index: usize,
    initial: TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>,
) -> bool {
    let checked = call.body_model();
    let body = checked.body_model();
    let elements = checked.elements_model();
    &&& index < elements.len()
    &&& elements[index as int].template_model() matches Some(root)
    &&& initial.emitter_model().values_model().len() == elements[index as int].insertions_model().len()
    &&& macro_insertion_values(call, index, elements[index as int].insertions_model().len(),
        initial.emitter_model().values_model())
    &&& template_assembly_start(body.source.text_model(), body.forms@, root,
        initial.emitter_model().values_model(), Some(initial))
}

/// 展開した一要素が、対応する元の要素の評価で得られることを表す。
pub open spec fn macro_expanded_element_matches<'b, 'p, 'a>(
    call: &'b BoundMacroCall<'p, 'a>, index: usize, output: MacroExpandedElement<'b, 'p, 'a>,
) -> bool {
    let elements = call.body_model().elements_model();
    &&& index < elements.len()
    &&& match output {
        MacroExpandedElement::Argument(value) => elements[index as int].template_model().is_none()
            && macro_expression_evaluation_result(call, MacroExpressionSite::Element(index), Ok(value)),
        MacroExpandedElement::Template { syntax, history } =>
            macro_template_origin(call, index, history@.0)
                && template_assembly_matches(history@.0, history@.1, Ok(TemplateAssemblySlice::Complete(syntax))),
    }
}

proof fn retain_elements<'b, 'p, 'a>(
    call: &'b BoundMacroCall<'p, 'a>, prefix: Seq<MacroExpandedElement<'b, 'p, 'a>>,
    output: MacroExpandedElement<'b, 'p, 'a>,
)
    requires
        forall|i: int| 0 <= i < prefix.len() ==> macro_expanded_element_matches(call, i as usize, #[trigger] prefix[i]),
        prefix.len() < call.body_model().elements_model().len(),
        macro_expanded_element_matches(call, prefix.len() as usize, output),
    ensures forall|i: int| 0 <= i < prefix.push(output).len() ==>
        macro_expanded_element_matches(call, i as usize, #[trigger] prefix.push(output)[i]),
{
    assert forall|i: int| 0 <= i < prefix.push(output).len() implies
        macro_expanded_element_matches(call, i as usize, #[trigger] prefix.push(output)[i]) by {
        if i < prefix.len() {
            assert(prefix.push(output)[i] == prefix[i]);
        } else {
            assert(prefix.push(output)[i] == output);
        }
    };
}

proof fn retain_insertions<'b, 'p, 'a>(
    call: &'b BoundMacroCall<'p, 'a>, index: usize, count: nat,
    prefix: Seq<TemplateSubstitution<'b, MacroArgument<'p, 'a>>>, value: &'b MacroArgument<'p, 'a>,
)
    requires macro_insertion_values(call, index, count, prefix), prefix.len() < count,
        macro_expression_evaluation_result(call,
            MacroExpressionSite::Insertion { element: index, insertion: prefix.len() as usize }, Ok(value)),
    ensures macro_insertion_values(call, index, count, prefix.push(TemplateSubstitution::One(value))),
{
    let values = prefix.push(TemplateSubstitution::One(value));
    assert forall|i: int| 0 <= i < values.len() implies {
        &&& (#[trigger] values[i]) matches TemplateSubstitution::One(argument)
        &&& macro_expression_evaluation_result(call,
            MacroExpressionSite::Insertion { element: index, insertion: i as usize }, Ok(argument))
    } by {
        if i < prefix.len() {
            assert(values[i] == prefix[i]);
        } else {
            assert(values[i] == TemplateSubstitution::One(value));
        }
    };
}

proof fn initial_assembly_matches<'s, 'v, T>(state: TemplateAssembly<'s, 'v, T>)
    requires state.ready(),
    ensures template_assembly_matches(state, 0, Ok(TemplateAssemblySlice::Suspended(state))),
{
    assert(template_assembly_trace_result(state, 0, seq![state.emitter_model()], Seq::empty(),
        Ok(TemplateAssemblySlice::Suspended(state))));
}

type ExpansionResult<'b, 'p, 'a> =
    Result<MacroExpansionSlice<'b, 'p, 'a>, MacroExpansionError<'b, 'p, 'a>>;

spec fn begins_expression<'b, 'p, 'a>(
    phase: ExpansionPhase<'b, 'p, 'a>, call: &'b BoundMacroCall<'p, 'a>,
    site: MacroExpressionSite, pending: Option<PendingTemplate<'b, 'p, 'a>>,
) -> bool {
    &&& phase matches ExpansionPhase::Expression { expression, template }
    &&& template == pending
    &&& expression.ready() && expression.bound_model() == call
    &&& expression.site_model() == site && expression.next_model() == 0
}

/// 型検査済みの本体に対する、1回分の展開遷移を表す。
pub closed spec fn macro_expansion_step_matches<'b, 'p, 'a>(
    state: MacroExpansion<'b, 'p, 'a>, result: ExpansionResult<'b, 'p, 'a>,
) -> bool {
    let call = state.call_model();
    let body = call.body_model();
    let elements = body.elements_model();
    let index = state.position_model() as usize;
    let prefix = state.completed@;
    &&& state.ready()
    &&& state.slice_preserves_call(result)
    &&& match state.phase {
        ExpansionPhase::Select => {
            if index == elements.len() {
                result matches Ok(MacroExpansionSlice::Complete(output)) && output.elements_model() == prefix
            } else {
                &&& result matches Ok(MacroExpansionSlice::Suspended(next))
                &&& next.completed@ == prefix
                &&& match elements[index as int].template_model() {
                    Some(root) => next.phase matches ExpansionPhase::Insertions(pending)
                        && pending.root == root && pending.values@.len() == 0,
                    None => begins_expression(next.phase, call, MacroExpressionSite::Element(index), None),
                }
            }
        },
        ExpansionPhase::Insertions(pending) => {
            let offset = pending.values@.len();
            &&& result matches Ok(MacroExpansionSlice::Suspended(next))
            &&& next.completed@ == prefix
            &&& if offset == elements[index as int].insertions_model().len() {
                &&& next.phase matches ExpansionPhase::Assemble { current, history }
                &&& history@ == (current, 0nat)
                &&& current.emitter_model().values_model() == pending.values@
            } else {
                begins_expression(next.phase, call, MacroExpressionSite::Insertion {
                    element: index, insertion: offset as usize,
                }, Some(pending))
            }
        },
        ExpansionPhase::Expression { expression, template } => match result {
            Err(failure) => {
                &&& failure.element == index
                &&& failure.kind matches MacroExpansionErrorKind::Expression { site, error }
                &&& site == expression.site_model()
                &&& macro_expression_step_matches(expression, Err(error))
            },
            Ok(MacroExpansionSlice::Suspended(next)) => match next.phase {
                ExpansionPhase::Expression { expression: later, template: pending } =>
                    next.completed@ == prefix && pending == template
                        && macro_expression_step_matches(expression, Ok(MacroExpressionStep::Continue(later))),
                ExpansionPhase::Insertions(pending) => {
                    &&& template matches Some(prior)
                    &&& next.completed@ == prefix && pending.root == prior.root
                    &&& pending.values@.len() == prior.values@.len() + 1
                    &&& pending.values@.last() matches TemplateSubstitution::One(value)
                    &&& pending.values@ == prior.values@.push(TemplateSubstitution::One(value))
                    &&& macro_expression_step_matches(expression, Ok(MacroExpressionStep::Value(value)))
                },
                ExpansionPhase::Select => {
                    &&& template.is_none()
                    &&& next.completed@.len() == prefix.len() + 1
                    &&& next.completed@.last() matches MacroExpandedElement::Argument(value)
                    &&& next.completed@ == prefix.push(MacroExpandedElement::Argument(value))
                    &&& macro_expression_step_matches(expression, Ok(MacroExpressionStep::Value(value)))
                },
                ExpansionPhase::Assemble { .. } => false,
            },
            Ok(MacroExpansionSlice::Complete(_)) => false,
        },
        ExpansionPhase::Assemble { current, history } => match result {
            Err(failure) => {
                &&& failure.element == index
                &&& failure.kind matches MacroExpansionErrorKind::Template(error)
                &&& template_assembly_matches(current, 1, Err(error))
            },
            Ok(MacroExpansionSlice::Suspended(next)) => match next.phase {
                ExpansionPhase::Assemble { current: later, history: updated } =>
                    next.completed@ == prefix && updated@ == (history@.0, history@.1 + 1)
                        && template_assembly_matches(current, 1, Ok(TemplateAssemblySlice::Suspended(later))),
                ExpansionPhase::Select => {
                    &&& next.completed@.len() == prefix.len() + 1
                    &&& next.completed@.last() matches MacroExpandedElement::Template { syntax, history: final_history }
                    &&& next.completed@ == prefix.push(MacroExpandedElement::Template { syntax, history: final_history })
                    &&& final_history@ == (history@.0, history@.1 + 1)
                    &&& template_assembly_matches(current, 1, Ok(TemplateAssemblySlice::Complete(syntax)))
                },
                _ => false,
            },
            Ok(MacroExpansionSlice::Complete(_)) => false,
        },
    }
}

spec fn macro_expansion_prefix<'b, 'p, 'a>(
    start: MacroExpansion<'b, 'p, 'a>, states: Seq<MacroExpansion<'b, 'p, 'a>>,
) -> bool {
    &&& states.len() > 0 && states[0] == start
    &&& forall|i: int| 0 <= i < states.len() - 1 ==>
        #[trigger] macro_expansion_step_matches(states[i], Ok(MacroExpansionSlice::Suspended(states[i + 1])))
}

spec fn macro_expansion_trace<'b, 'p, 'a>(
    start: MacroExpansion<'b, 'p, 'a>, fuel: nat, states: Seq<MacroExpansion<'b, 'p, 'a>>,
    result: ExpansionResult<'b, 'p, 'a>,
) -> bool {
    &&& macro_expansion_prefix(start, states)
    &&& match result {
        Ok(MacroExpansionSlice::Suspended(next)) => states.len() == fuel + 1 && states.last() == next,
        _ => states.len() <= fuel && macro_expansion_step_matches(states.last(), result),
    }
}

/// 実行枠が一歩ずつ進み、枠を使い切るか、最初の完了または診断で止まることを表す。
pub closed spec fn macro_expansion_slice_matches<'b, 'p, 'a>(
    start: MacroExpansion<'b, 'p, 'a>, fuel: nat, result: ExpansionResult<'b, 'p, 'a>,
) -> bool {
    exists|states: Seq<MacroExpansion<'b, 'p, 'a>>|
        #[trigger] macro_expansion_trace(start, fuel, states, result)
}

/// 展開が実行枠で消費した遷移数を表す。完了または診断を返す遷移も数える。
pub closed spec fn macro_expansion_slice_steps<'b, 'p, 'a>(
    start: MacroExpansion<'b, 'p, 'a>, fuel: nat, result: ExpansionResult<'b, 'p, 'a>,
) -> nat {
    let states = choose|states: Seq<MacroExpansion<'b, 'p, 'a>>|
        #[trigger] macro_expansion_trace(start, fuel, states, result);
    if result matches Ok(MacroExpansionSlice::Suspended(_)) { fuel } else { states.len() }
}

/// 一時停止までに枠を使い切り、完了や診断までの遷移数が枠内に収まることを示す。
pub proof fn macro_expansion_slice_steps_in_fuel<'b, 'p, 'a>(
    start: MacroExpansion<'b, 'p, 'a>, fuel: nat, result: ExpansionResult<'b, 'p, 'a>,
)
    requires macro_expansion_slice_matches(start, fuel, result),
    ensures macro_expansion_slice_steps(start, fuel, result) <= fuel,
        result matches Ok(MacroExpansionSlice::Suspended(_)) ==>
            macro_expansion_slice_steps(start, fuel, result) == fuel,
        !(result matches Ok(MacroExpansionSlice::Suspended(_))) ==>
            0 < macro_expansion_slice_steps(start, fuel, result),
{}

proof fn macro_expansion_trace_witness<'b, 'p, 'a>(
    start: MacroExpansion<'b, 'p, 'a>, fuel: nat, states: Seq<MacroExpansion<'b, 'p, 'a>>,
    result: ExpansionResult<'b, 'p, 'a>,
)
    requires macro_expansion_trace(start, fuel, states, result),
    ensures macro_expansion_slice_matches(start, fuel, result),
{}

proof fn extend_macro_expansion_prefix<'b, 'p, 'a>(
    start: MacroExpansion<'b, 'p, 'a>, states: Seq<MacroExpansion<'b, 'p, 'a>>,
    next: MacroExpansion<'b, 'p, 'a>,
)
    requires macro_expansion_prefix(start, states),
        macro_expansion_step_matches(states.last(), Ok(MacroExpansionSlice::Suspended(next))),
    ensures macro_expansion_prefix(start, states.push(next)),
{
    let longer = states.push(next);
    assert forall|i: int| 0 <= i < longer.len() - 1 implies
        #[trigger] macro_expansion_step_matches(longer[i], Ok(MacroExpansionSlice::Suspended(longer[i + 1]))) by {
        if i == states.len() - 1 {
            assert(longer[i] == states.last() && longer[i + 1] == next);
        } else {
            assert(macro_expansion_step_matches(states[i], Ok(MacroExpansionSlice::Suspended(states[i + 1]))));
        }
    };
}

/// 一時停止後に進めた展開は、二つの実行枠の合計で進めた展開に対応する。
pub proof fn resumed_macro_expansion_matches<'b, 'p, 'a>(
    start: MacroExpansion<'b, 'p, 'a>, first: nat,
    suspended: MacroExpansion<'b, 'p, 'a>, next: nat, result: ExpansionResult<'b, 'p, 'a>,
)
    requires macro_expansion_slice_matches(start, first, Ok(MacroExpansionSlice::Suspended(suspended))),
        macro_expansion_slice_matches(suspended, next, result),
    ensures macro_expansion_slice_matches(start, first + next, result),
{
    let earlier = choose|states: Seq<MacroExpansion<'b, 'p, 'a>>|
        #[trigger] macro_expansion_trace(start, first, states, Ok(MacroExpansionSlice::Suspended(suspended)));
    let later = choose|states: Seq<MacroExpansion<'b, 'p, 'a>>|
        #[trigger] macro_expansion_trace(suspended, next, states, result);
    let states = earlier + later.subrange(1, later.len() as int);
    assert(states.last() == later.last());
    assert forall|i: int| 0 <= i < states.len() - 1 implies
        #[trigger] macro_expansion_step_matches(states[i], Ok(MacroExpansionSlice::Suspended(states[i + 1]))) by {
        if i < earlier.len() - 1 {
            assert(macro_expansion_step_matches(earlier[i], Ok(MacroExpansionSlice::Suspended(earlier[i + 1]))));
        } else {
            let index = i - (earlier.len() as int - 1);
            assert(0 <= index < later.len() - 1);
            if index == 0 {
                assert(states[i] == later[0]);
            }
            assert(macro_expansion_step_matches(later[index], Ok(MacroExpansionSlice::Suspended(later[index + 1]))));
        }
    };
    macro_expansion_trace_witness(start, first + next, states, result);
}

impl<'p, 'a> BoundMacroCall<'p, 'a> {
    /// 型検査した本体の先頭から展開を始める。
    ///
    /// リスト本体の直接の仮引数参照と、テンプレート内の仮引数を指す `unsyntax` を評価できる。
    /// `splice` で使うリスト値や一般式は、式の範囲を付けて評価を保留する。
    pub fn start_expansion<'b>(&'b self) -> (state: MacroExpansion<'b, 'p, 'a>)
        requires self.valid(),
        ensures state.ready(), state.call_model() == self, state.position_model() == 0, state.initial_for(self),
    {
        MacroExpansion { call: self, completed: Vec::new(), phase: ExpansionPhase::Select }
    }
}

impl<'b, 'p, 'a> MacroExpansion<'b, 'p, 'a> {
    /// 元の呼び出しを表す。
    pub closed spec fn call_model(&self) -> &'b BoundMacroCall<'p, 'a> { self.call }

    /// 確定前の要素を本体の先頭から何個組み立てたかを表す。
    pub closed spec fn position_model(&self) -> nat { self.completed@.len() }

    /// 呼び出しの先頭で、最初の要素をまだ選んでいないことを表す。
    pub closed spec fn initial_for(&self, call: &'b BoundMacroCall<'p, 'a>) -> bool {
        &&& self.call_model() == call
        &&& self.completed@.len() == 0
        &&& self.phase is Select
    }

    /// 状態が型検査済み本体の途中または末尾にあり、式と挿入値が位置に対応することを表す。
    pub closed spec fn ready(&self) -> bool {
        let call = self.call_model();
        let body = call.body_model();
        let elements = body.elements_model();
        let i = self.position_model();
        &&& call.valid()
        &&& i <= elements.len()
        &&& forall|j: int| 0 <= j < self.completed@.len() ==>
            macro_expanded_element_matches(call, j as usize, #[trigger] self.completed@[j])
        &&& match self.phase {
            ExpansionPhase::Select => true,
            ExpansionPhase::Insertions(pending) =>
                i < elements.len() && pending.ready(elements[i as int], call, i as usize),
            ExpansionPhase::Expression { expression, template } => {
                &&& i < elements.len() && expression.ready() && expression.bound_model() == call
                &&& match template {
                    None => elements[i as int].template_model().is_none()
                        && expression.site_model() == MacroExpressionSite::Element(i as usize),
                    Some(pending) => pending.ready(elements[i as int], call, i as usize)
                        && pending.values@.len() < elements[i as int].insertions_model().len()
                        && expression.site_model() == (MacroExpressionSite::Insertion {
                            element: i as usize, insertion: pending.values@.len() as usize,
                        }),
                }
            },
            ExpansionPhase::Assemble { current, history } =>
                current.ready()
                    && macro_template_origin(call, i as usize, history@.0)
                    && template_assembly_matches(history@.0, history@.1, Ok(TemplateAssemblySlice::Suspended(current))),
        }
    }

    /// 要素の選択、式の評価、構文の組み立ての順に減る値を表す。
    pub closed spec fn stage(&self) -> nat {
        match self.phase {
            ExpansionPhase::Select => 3,
            ExpansionPhase::Insertions(_) | ExpansionPhase::Expression { .. } => 2,
            ExpansionPhase::Assemble { .. } => 1,
        }
    }

    /// 同じ要素で、まだ値を得ていない挿入式の数を表す。
    pub closed spec fn insertions_remaining(&self) -> nat {
        let count = self.call_model().body_model().elements_model()[self.position_model() as int].insertions_model().len();
        match self.phase {
            ExpansionPhase::Insertions(template)
            | ExpansionPhase::Expression { template: Some(template), .. } => (count - template.values@.len()) as nat,
            _ => 0,
        }
    }

    /// 同じ挿入式の照合、または値を得た後の構文走査で残る遷移数の上界を表す。
    pub closed spec fn stage_remaining(&self) -> nat {
        match self.phase {
            ExpansionPhase::Select => 0,
            ExpansionPhase::Insertions(_) => self.call_model().body_model().parameters_model().len() + 2,
            ExpansionPhase::Expression { expression, .. } => expression.remaining_bound(),
            ExpansionPhase::Assemble { current, .. } => current.emitter_model().remaining_bound(),
        }
    }

    /// 同じマクロの後続状態で、要素またはその内部の評価が進んだことを表す。
    pub open spec fn advanced(&self, start: &Self) -> bool {
        &&& self.call_model() == start.call_model()
        &&& self.position_model() >= start.position_model()
        &&& (self.position_model() > start.position_model()
            || self.stage() < start.stage()
            || self.stage() == start.stage() && (
                self.insertions_remaining() < start.insertions_remaining()
                || self.insertions_remaining() == start.insertions_remaining()
                    && self.stage_remaining() < start.stage_remaining()))
    }

    /// 組み立て中の要素番号、型付き診断、元の位置が評価の結果に対応することを表す。
    pub open spec fn failure_matches(
        &self, failure: MacroExpansionError<'b, 'p, 'a>,
    ) -> bool {
        let call = self.call_model();
        let checked = call.body_model();
        let body = checked.body_model();
        let elements = checked.elements_model();
        let index = failure.element;
        &&& self.position_model() <= index < elements.len()
        &&& failure.call == call
        &&& failure.definition == body.source
        &&& match failure.kind {
            MacroExpansionErrorKind::Expression { site, error } => {
                &&& macro_expression_evaluation_result(call, site, Err(error))
                &&& macro_expression_position(&checked, site) matches Some(at)
                &&& at < body.forms@.len()
                &&& failure.related == form_span(body.forms@[at as int])
                &&& match site {
                    MacroExpressionSite::Element(element) =>
                        element == index && elements[index as int].template_model().is_none(),
                    MacroExpressionSite::Insertion { element, insertion } =>
                        element == index && insertion < elements[index as int].insertions_model().len(),
                }
            },
            MacroExpansionErrorKind::Template(error) => {
                let at = elements[index as int].at_model();
                &&& at < body.forms@.len()
                &&& failure.related == form_span(body.forms@[at as int])
                &&& exists|initial: TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>, used: nat|
                    macro_template_origin(call, index, initial)
                        && #[trigger] template_assembly_matches(initial, used, Err(error))
            },
        }
    }

    /// 通常の実行枠で観測できる確定結果、診断の出典、進捗を表す。
    pub open spec fn slice_preserves_call(
        &self, result: Result<MacroExpansionSlice<'b, 'p, 'a>, MacroExpansionError<'b, 'p, 'a>>,
    ) -> bool {
        match result {
            Ok(MacroExpansionSlice::Complete(body)) => body.call_model() == self.call_model()
                && body.elements_model().len() == self.call_model().body_model().elements_model().len()
                && forall|i: int| 0 <= i < body.elements_model().len() ==>
                    macro_expanded_element_matches(body.call_model(), i as usize, #[trigger] body.elements_model()[i]),
            Ok(MacroExpansionSlice::Suspended(state)) => state.ready() && state.advanced(self),
            Err(error) => self.failure_matches(error),
        }
    }

    /// 要素の評価とテンプレート展開を、指定した遷移数を上限として進める。
    ///
    /// 枠を使い切ると一時停止状態を返す。要素の選択、仮引数一つの照合、テンプレートの
    /// 構文項目一つの生成はそれぞれ1遷移。完了を確定する末尾の確認も枠に数える。
    ///
    /// # Errors
    ///
    /// 最初に処理できなかった式またはテンプレートの診断を返す。途中の生成物は公開しない。
    pub fn run_slice(self, fuel: NonZeroUsize)
        -> (result: Result<MacroExpansionSlice<'b, 'p, 'a>, MacroExpansionError<'b, 'p, 'a>>)
        requires self.ready(),
        ensures self.slice_preserves_call(result), macro_expansion_slice_matches(self, fuel@ as nat, result),
    {
        let mut state = self;
        let mut remaining = fuel.get();
        let ghost mut states = seq![state];
        while remaining > 0
            invariant
                state.ready(),
                state.call_model() == self.call_model(),
                remaining <= fuel@,
                remaining == fuel@ ==> state == self,
                remaining < fuel@ ==> state.advanced(&self),
                states.len() == fuel@ - remaining + 1,
                states.last() == state,
                macro_expansion_prefix(self, states),
            decreases remaining,
        {
            let outcome = state.step();
            match outcome {
                Ok(MacroExpansionSlice::Suspended(next)) => {
                    proof {
                        extend_macro_expansion_prefix(self, states, next);
                        states = states.push(next);
                    }
                    state = next;
                },
                Ok(MacroExpansionSlice::Complete(result)) => {
                    let done = Ok(MacroExpansionSlice::Complete(result));
                    proof { macro_expansion_trace_witness(self, fuel@ as nat, states, done); }
                    return done;
                },
                Err(error) => {
                    let done = Err(error);
                    proof { macro_expansion_trace_witness(self, fuel@ as nat, states, done); }
                    return done;
                },
            }
            remaining -= 1;
        }
        let suspended = Ok(MacroExpansionSlice::Suspended(state));
        proof { macro_expansion_trace_witness(self, fuel@ as nat, states, suspended); }
        suspended
    }

    fn step(self) -> (result: ExpansionResult<'b, 'p, 'a>)
        requires self.ready(),
        ensures macro_expansion_step_matches(self, result),
    {
        let ghost old_phase = self.phase;
        let Self { call, mut completed, phase } = self;
        let checked = call.body();
        let body = checked.body();
        let index = completed.len();
        proof {
            if index < checked.elements_model().len() {
                assert(macro_element_origin(body.source.text_model(), body.forms@,
                    checked.parameters_model(), checked.elements_model()[index as int]));
            }
        }
        let phase = match phase {
            ExpansionPhase::Select => {
                let Some(element) = checked.elements().get(index) else {
                    return Ok(MacroExpansionSlice::Complete(MacroExpandedBody {
                        call, elements: completed,
                    }));
                };
                match element.template() {
                    Some(root) => ExpansionPhase::Insertions(PendingTemplate { root, values: Vec::new() }),
                    None => {
                        let site = MacroExpressionSite::Element(index);
                        assert(macro_expression_position(&call.body_model(), site).is_some());
                        let expression = call.start_expression(site).unwrap();
                        ExpansionPhase::Expression { expression, template: None }
                    },
                }
            },
            ExpansionPhase::Insertions(template) => {
                let insertion = template.values.len();
                let element = &checked.elements()[index];
                if insertion == element.insertions().len() {
                    let assembly = assemble_owned_template(body.source.text(), body.forms, template.root, template.values).unwrap();
                    proof {
                        assert(macro_template_origin(call, index, assembly));
                        initial_assembly_matches(assembly);
                    }
                    ExpansionPhase::Assemble { current: assembly, history: Ghost((assembly, 0nat)) }
                } else {
                    let site = MacroExpressionSite::Insertion { element: index, insertion };
                    assert(macro_expression_position(&call.body_model(), site).is_some());
                    let expression = call.start_expression(site).unwrap();
                    ExpansionPhase::Expression { expression, template: Some(template) }
                }
            },
            ExpansionPhase::Expression { expression, template } => {
                let related = expression.span();
                let site = expression.site();
                match expression.step() {
                    Err(error) => return Err(MacroExpansionError {
                        call, definition: body.source, related, element: index,
                        kind: MacroExpansionErrorKind::Expression { site, error },
                    }),
                    Ok(MacroExpressionStep::Continue(expression)) => ExpansionPhase::Expression { expression, template },
                    Ok(MacroExpressionStep::Value(value)) => match template {
                        Some(mut template) => {
                            proof {
                                let element = checked.elements_model()[index as int];
                                retain_insertions(call, index, element.insertions_model().len(),
                                    template.values@, value);
                            }
                            template.values.push(TemplateSubstitution::One(value));
                            ExpansionPhase::Insertions(template)
                        },
                        None => {
                            let out = MacroExpandedElement::Argument(value);
                            proof { retain_elements(call, completed@, out); }
                            completed.push(out);
                            ExpansionPhase::Select
                        },
                    },
                }
            },
            ExpansionPhase::Assemble { current, history } => {
                let ghost (initial, used) = history@;
                let ghost before = current;
                let result = current.run_slice(NonZeroUsize::new(1).unwrap());
                proof { resumed_template_assembly_matches(initial, used, before, 1, result); }
                match result {
                    Err(error) => {
                        let related = super::super::defn::span_of(&body.forms[checked.elements()[index].at()]);
                        return Err(MacroExpansionError {
                            call, definition: body.source, related, element: index,
                            kind: MacroExpansionErrorKind::Template(error),
                        });
                    },
                    Ok(TemplateAssemblySlice::Suspended(current)) =>
                        ExpansionPhase::Assemble { current, history: Ghost((initial, used + 1)) },
                    Ok(TemplateAssemblySlice::Complete(template)) => {
                        let out = MacroExpandedElement::Template {
                            syntax: template, history: Ghost((initial, used + 1)),
                        };
                        proof { retain_elements(call, completed@, out); }
                        completed.push(out);
                        ExpansionPhase::Select
                    },
                }
            },
        };
        let next = Self { call, completed, phase };
        assert(next.ready());
        assert(next.call_model() == self.call_model());
        assert(next.completed@.len() == self.completed@.len()
            || next.completed@.len() == self.completed@.len() + 1);
        assert(next.position_model() >= self.position_model());
        let ghost new_phase = next.phase;
        proof {
            if next.position_model() == self.position_model() {
                match (old_phase, new_phase) {
                    (ExpansionPhase::Insertions(prior), ExpansionPhase::Expression { expression, template: Some(later) }) => {
                        assert(later.values@.len() == prior.values@.len());
                        assert(expression.remaining_bound() <= checked.parameters_model().len() + 1);
                    },
                    (ExpansionPhase::Expression { template: Some(prior), .. }, ExpansionPhase::Insertions(later)) => {
                        assert(later.values@.len() == prior.values@.len() + 1);
                        assert(later.values@.len() <= checked.elements_model()[index as int].insertions_model().len());
                        assert(next.insertions_remaining() < self.insertions_remaining());
                    },
                    (ExpansionPhase::Expression { expression: prior, template: p1 },
                        ExpansionPhase::Expression { expression: later, template: p2 }) => {
                        assert(p1 == p2);
                        assert(later.remaining_bound() < prior.remaining_bound());
                    },
                    (ExpansionPhase::Assemble { current: prior, .. }, ExpansionPhase::Assemble { current: later, .. }) => {
                        assert(later.emitter_model().remaining_bound() < prior.emitter_model().remaining_bound());
                    },
                    _ => assert(next.stage() < self.stage()),
                }
            }
        }
        assert(next.advanced(&self));
        Ok(MacroExpansionSlice::Suspended(next))
    }
}

/// 一要素の構文と出典が一致することを表す。
pub open spec fn macro_expanded_elements_agree<'b, 'p, 'a>(
    a: MacroExpandedElement<'b, 'p, 'a>, b: MacroExpandedElement<'b, 'p, 'a>,
) -> bool {
    match (a, b) {
        (MacroExpandedElement::Argument(a), MacroExpandedElement::Argument(b)) => *a == *b,
        (MacroExpandedElement::Template { syntax: a, .. }, MacroExpandedElement::Template { syntax: b, .. }) =>
            a.source_model() == b.source_model()
                && a.forms_model() == b.forms_model() && a.parts_model() == b.parts_model(),
        _ => false,
    }
}

/// 同じ順序で、同じ構文と出典を持つ要素が並ぶことを表す。
pub open spec fn macro_expanded_prefixes_agree<'b, 'p, 'a>(
    a: Seq<MacroExpandedElement<'b, 'p, 'a>>, b: Seq<MacroExpandedElement<'b, 'p, 'a>>,
) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> macro_expanded_elements_agree(#[trigger] a[i], b[i])
}

proof fn macro_expanded_prefixes_append<'b, 'p, 'a>(
    a: Seq<MacroExpandedElement<'b, 'p, 'a>>, b: Seq<MacroExpandedElement<'b, 'p, 'a>>,
    left: MacroExpandedElement<'b, 'p, 'a>, right: MacroExpandedElement<'b, 'p, 'a>,
)
    requires macro_expanded_prefixes_agree(a, b), macro_expanded_elements_agree(left, right),
    ensures macro_expanded_prefixes_agree(a.push(left), b.push(right)),
{
    let next_a = a.push(left);
    let next_b = b.push(right);
    assert forall|i: int| 0 <= i < next_a.len() implies macro_expanded_elements_agree(#[trigger] next_a[i], next_b[i]) by {
        if i < a.len() {
            assert(macro_expanded_elements_agree(a[i], b[i]));
        }
    };
}

spec fn macro_assemblies_agree<'b, 'p, 'a>(
    a: TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>, b: TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>,
) -> bool {
    crate::ncg2m::template::template_emitters_agree(&a.emitter_model(), &b.emitter_model())
        && a.parts_model() == b.parts_model()
}

spec fn macro_pending_templates_agree<'b, 'p, 'a>(
    a: PendingTemplate<'b, 'p, 'a>, b: PendingTemplate<'b, 'p, 'a>,
) -> bool {
    a.root == b.root && a.values@ == b.values@
}

/// 同じ呼び出しについて、確定前の要素と次に実行する処理が一致することを表す。
pub closed spec fn macro_expansion_states_agree<'b, 'p, 'a>(
    a: &MacroExpansion<'b, 'p, 'a>, b: &MacroExpansion<'b, 'p, 'a>,
) -> bool {
    &&& a.call_model() == b.call_model()
    &&& macro_expanded_prefixes_agree(a.completed@, b.completed@)
    &&& match (a.phase, b.phase) {
        (ExpansionPhase::Select, ExpansionPhase::Select) => true,
        (ExpansionPhase::Insertions(a), ExpansionPhase::Insertions(b)) => macro_pending_templates_agree(a, b),
        (ExpansionPhase::Expression { expression: a, template: left },
         ExpansionPhase::Expression { expression: b, template: right }) => {
            &&& super::macro_binding::macro_expression_states_agree(&a, &b)
            &&& match (left, right) {
                (Some(left), Some(right)) => macro_pending_templates_agree(left, right),
                (None, None) => true,
                _ => false,
            }
        },
        (ExpansionPhase::Assemble { current: a, .. }, ExpansionPhase::Assemble { current: b, .. }) =>
            macro_assemblies_agree(a, b),
        _ => false,
    }
}

/// 一遷移の出力、診断、または次の実行枠へ渡す状態が一致することを表す。
pub open spec fn macro_expansion_step_results_agree<'b, 'p, 'a>(
    a: ExpansionResult<'b, 'p, 'a>, b: ExpansionResult<'b, 'p, 'a>,
) -> bool {
    match (a, b) {
        (Ok(MacroExpansionSlice::Complete(a)), Ok(MacroExpansionSlice::Complete(b))) =>
            a.call_model() == b.call_model() && macro_expanded_prefixes_agree(a.elements_model(), b.elements_model()),
        (Ok(MacroExpansionSlice::Suspended(a)), Ok(MacroExpansionSlice::Suspended(b))) =>
            macro_expansion_states_agree(&a, &b),
        (Err(a), Err(b)) => a.call == b.call && a.definition == b.definition
            && a.related == b.related && a.element == b.element && a.kind == b.kind,
        _ => false,
    }
}

// 展開の一遷移から、その場で行った式評価の結果を取り出す。
spec fn expansion_expression_step<'b, 'p, 'a>(
    result: ExpansionResult<'b, 'p, 'a>,
) -> Option<Result<MacroExpressionStep<'b, 'p, 'a>, MacroArgumentError>> {
    match result {
        Err(error) => match error.kind {
            MacroExpansionErrorKind::Expression { error, .. } => Some(Err(error)),
            _ => None,
        },
        Ok(MacroExpansionSlice::Suspended(next)) => match next.phase {
            ExpansionPhase::Expression { expression, .. } => Some(Ok(MacroExpressionStep::Continue(expression))),
            ExpansionPhase::Insertions(pending) if pending.values@.len() > 0 =>
                if let TemplateSubstitution::One(value) = pending.values@.last() {
                    Some(Ok(MacroExpressionStep::Value(value)))
                } else { None },
            ExpansionPhase::Select if next.completed@.len() > 0 =>
                if let MacroExpandedElement::Argument(value) = next.completed@.last() {
                    Some(Ok(MacroExpressionStep::Value(value)))
                } else { None },
            _ => None,
        },
        _ => None,
    }
}

// 展開の一遷移から、その場で行ったテンプレートの組み立て結果を取り出す。
spec fn expansion_assembly_step<'b, 'p, 'a>(
    result: ExpansionResult<'b, 'p, 'a>,
) -> Option<Result<TemplateAssemblySlice<'p, 'b, MacroArgument<'p, 'a>>, TemplateEmissionError>> {
    match result {
        Err(error) => match error.kind {
            MacroExpansionErrorKind::Template(error) => Some(Err(error)),
            _ => None,
        },
        Ok(MacroExpansionSlice::Suspended(next)) => match next.phase {
            ExpansionPhase::Assemble { current, .. } => Some(Ok(TemplateAssemblySlice::Suspended(current))),
            ExpansionPhase::Select if next.completed@.len() > 0 =>
                if let MacroExpandedElement::Template { syntax, .. } = next.completed@.last() {
                    Some(Ok(TemplateAssemblySlice::Complete(syntax)))
                } else { None },
            _ => None,
        },
        _ => None,
    }
}

proof fn same_assembly_start<'b, 'p, 'a>(
    call: &'b BoundMacroCall<'p, 'a>, index: usize,
    a: TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>, b: TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>,
)
    requires macro_template_origin(call, index, a), macro_template_origin(call, index, b),
        a.emitter_model().values_model() == b.emitter_model().values_model(),
    ensures macro_assemblies_agree(a, b),
{
    assert(a.parts_model() =~= b.parts_model());
    assert(a.emitter_model().lists_model() =~= b.emitter_model().lists_model());
}

proof fn expansion_expression_steps_agree<'b, 'p, 'a>(
    a: &MacroExpansion<'b, 'p, 'a>, b: &MacroExpansion<'b, 'p, 'a>,
    expression_a: MacroExpressionEvaluation<'b, 'p, 'a>, expression_b: MacroExpressionEvaluation<'b, 'p, 'a>,
    out_a: ExpansionResult<'b, 'p, 'a>, out_b: ExpansionResult<'b, 'p, 'a>,
)
    requires macro_expansion_states_agree(a, b),
        a.phase matches ExpansionPhase::Expression { expression, .. } && expression == expression_a,
        b.phase matches ExpansionPhase::Expression { expression, .. } && expression == expression_b,
        macro_expansion_step_matches(*a, out_a), macro_expansion_step_matches(*b, out_b),
    ensures macro_expansion_step_results_agree(out_a, out_b),
{
    let left = expansion_expression_step(out_a);
    let right = expansion_expression_step(out_b);
    assert(left is Some && right is Some);
    let left = left->Some_0;
    let right = right->Some_0;
    assert(macro_expression_step_matches(expression_a, left));
    assert(macro_expression_step_matches(expression_b, right));
    super::macro_binding::macro_expression_steps_agree(&expression_a, &expression_b, left, right);
    if let (Ok(MacroExpansionSlice::Suspended(next_a)), Ok(MacroExpansionSlice::Suspended(next_b))) = (out_a, out_b) {
        if let (ExpansionPhase::Select, ExpansionPhase::Select) = (next_a.phase, next_b.phase) {
            macro_expanded_prefixes_append(a.completed@, b.completed@, next_a.completed@.last(), next_b.completed@.last());
        }
    }
}

proof fn expansion_assembly_steps_agree<'b, 'p, 'a>(
    a: &MacroExpansion<'b, 'p, 'a>, b: &MacroExpansion<'b, 'p, 'a>,
    current_a: TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>,
    current_b: TemplateAssembly<'p, 'b, MacroArgument<'p, 'a>>,
    out_a: ExpansionResult<'b, 'p, 'a>, out_b: ExpansionResult<'b, 'p, 'a>,
)
    requires macro_expansion_states_agree(a, b),
        a.phase matches ExpansionPhase::Assemble { current, .. } && current == current_a,
        b.phase matches ExpansionPhase::Assemble { current, .. } && current == current_b,
        macro_expansion_step_matches(*a, out_a), macro_expansion_step_matches(*b, out_b),
    ensures macro_expansion_step_results_agree(out_a, out_b),
{
    let left = expansion_assembly_step(out_a);
    let right = expansion_assembly_step(out_b);
    assert(left is Some && right is Some);
    let left = left->Some_0;
    let right = right->Some_0;
    assert(template_assembly_matches(current_a, 1, left));
    assert(template_assembly_matches(current_b, 1, right));
    crate::ncg2m::template::template_assembly_results_from_equivalent_states(current_a, current_b, 1, left, right);
    if let (Ok(MacroExpansionSlice::Suspended(next_a)), Ok(MacroExpansionSlice::Suspended(next_b))) = (out_a, out_b) {
        if let (ExpansionPhase::Select, ExpansionPhase::Select) = (next_a.phase, next_b.phase) {
            macro_expanded_prefixes_append(a.completed@, b.completed@, next_a.completed@.last(), next_b.completed@.last());
        }
    }
}

/// 同じ途中状態からは、同じ診断、出力、または再開状態を一意に得る。
pub proof fn macro_expansion_steps_agree<'b, 'p, 'a>(
    a: &MacroExpansion<'b, 'p, 'a>, b: &MacroExpansion<'b, 'p, 'a>,
    out_a: ExpansionResult<'b, 'p, 'a>, out_b: ExpansionResult<'b, 'p, 'a>,
)
    requires macro_expansion_states_agree(a, b),
        macro_expansion_step_matches(*a, out_a), macro_expansion_step_matches(*b, out_b),
    ensures macro_expansion_step_results_agree(out_a, out_b),
{
    assert(a.position_model() == b.position_model());
    match (a.phase, b.phase) {
        (ExpansionPhase::Select, ExpansionPhase::Select) => {
            if let (Ok(MacroExpansionSlice::Suspended(next_a)), Ok(MacroExpansionSlice::Suspended(next_b))) = (out_a, out_b) {
                if let (ExpansionPhase::Insertions(left), ExpansionPhase::Insertions(right)) = (next_a.phase, next_b.phase) {
                    assert(left.values@ =~= right.values@);
                }
            }
        },
        (ExpansionPhase::Insertions(_), ExpansionPhase::Insertions(_)) => {
            if let (Ok(MacroExpansionSlice::Suspended(next_a)), Ok(MacroExpansionSlice::Suspended(next_b))) = (out_a, out_b) {
                if let (ExpansionPhase::Assemble { current: left, .. }, ExpansionPhase::Assemble { current: right, .. }) =
                    (next_a.phase, next_b.phase)
                {
                    same_assembly_start(a.call_model(), a.position_model() as usize, left, right);
                }
            }
        },
        (ExpansionPhase::Expression { expression: left, .. }, ExpansionPhase::Expression { expression: right, .. }) =>
            expansion_expression_steps_agree(a, b, left, right, out_a, out_b),
        (ExpansionPhase::Assemble { current: left, .. }, ExpansionPhase::Assemble { current: right, .. }) =>
            expansion_assembly_steps_agree(a, b, left, right, out_a, out_b),
        _ => assert(false),
    }
}

/// 同じ呼び出しの先頭から始めた二つの状態は、同じ構文を同じ順に処理する。
pub proof fn macro_expansion_starts_agree<'b, 'p, 'a>(
    call: &'b BoundMacroCall<'p, 'a>,
    a: MacroExpansion<'b, 'p, 'a>, b: MacroExpansion<'b, 'p, 'a>,
)
    requires a.initial_for(call), b.initial_for(call),
    ensures macro_expansion_states_agree(&a, &b),
{}

proof fn macro_expansion_common_prefix_agrees<'b, 'p, 'a>(
    start_a: MacroExpansion<'b, 'p, 'a>, start_b: MacroExpansion<'b, 'p, 'a>,
    left: Seq<MacroExpansion<'b, 'p, 'a>>, right: Seq<MacroExpansion<'b, 'p, 'a>>,
    index: int,
)
    requires macro_expansion_states_agree(&start_a, &start_b),
        macro_expansion_prefix(start_a, left), macro_expansion_prefix(start_b, right),
        0 <= index < left.len(), index < right.len(),
    ensures macro_expansion_states_agree(&left[index], &right[index]),
    decreases index,
{
    if index > 0 {
        let previous = index - 1;
        macro_expansion_common_prefix_agrees(start_a, start_b, left, right, previous);
        let a = Ok(MacroExpansionSlice::Suspended(left[previous + 1]));
        let b = Ok(MacroExpansionSlice::Suspended(right[previous + 1]));
        assert(macro_expansion_step_matches(left[previous], a));
        assert(macro_expansion_step_matches(right[previous], b));
        macro_expansion_steps_agree(&left[previous], &right[previous], a, b);
    }
}

proof fn macro_expansion_trace_does_not_end_early<'b, 'p, 'a>(
    start_a: MacroExpansion<'b, 'p, 'a>, start_b: MacroExpansion<'b, 'p, 'a>, fuel: nat,
    left: Seq<MacroExpansion<'b, 'p, 'a>>, right: Seq<MacroExpansion<'b, 'p, 'a>>,
    a: ExpansionResult<'b, 'p, 'a>, b: ExpansionResult<'b, 'p, 'a>,
)
    requires macro_expansion_states_agree(&start_a, &start_b),
        macro_expansion_trace(start_a, fuel, left, a), macro_expansion_trace(start_b, fuel, right, b),
    ensures left.len() >= right.len(),
{
    if left.len() < right.len() {
        let index = left.len() - 1;
        assert(left.len() <= fuel);
        assert(left[index] == left.last());
        macro_expansion_common_prefix_agrees(start_a, start_b, left, right, index);
        let later = Ok(MacroExpansionSlice::Suspended(right[index + 1]));
        assert(macro_expansion_step_matches(right[index], later));
        macro_expansion_steps_agree(&left[index], &right[index], a, later);
    }
}

/// 続きが等しい開始状態と同じ枠からは、同じ構文、診断、または同等の再開状態が得られる。
///
/// 分けた枠を `resumed_macro_expansion_matches` で合成すると、一括実行との比較にも使える。
pub proof fn macro_expansion_slice_results_agree<'b, 'p, 'a>(
    start_a: MacroExpansion<'b, 'p, 'a>, start_b: MacroExpansion<'b, 'p, 'a>, fuel: nat,
    a: ExpansionResult<'b, 'p, 'a>, b: ExpansionResult<'b, 'p, 'a>,
)
    requires macro_expansion_states_agree(&start_a, &start_b),
        macro_expansion_slice_matches(start_a, fuel, a), macro_expansion_slice_matches(start_b, fuel, b),
    ensures macro_expansion_step_results_agree(a, b),
        macro_expansion_slice_steps(start_a, fuel, a) == macro_expansion_slice_steps(start_b, fuel, b),
{
    let left = choose|states: Seq<MacroExpansion<'b, 'p, 'a>>| #[trigger] macro_expansion_trace(start_a, fuel, states, a);
    let right = choose|states: Seq<MacroExpansion<'b, 'p, 'a>>| #[trigger] macro_expansion_trace(start_b, fuel, states, b);
    macro_expansion_trace_does_not_end_early(start_a, start_b, fuel, left, right, a, b);
    assert(macro_expansion_states_agree(&start_b, &start_a));
    macro_expansion_trace_does_not_end_early(start_b, start_a, fuel, right, left, b, a);
    let index = left.len() - 1;
    macro_expansion_common_prefix_agrees(start_a, start_b, left, right, index);
    assert(left[index] == left.last() && right[index] == right.last());
    if left.len() <= fuel {
        macro_expansion_steps_agree(&left.last(), &right.last(), a, b);
    }
}

} // verus!
