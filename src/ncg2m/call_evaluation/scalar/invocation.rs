//! 本体直下の宣言呼び出しを、引数の評価から呼び出し先の環境へつなぐ。

use super::*;
use super::super::{CallArgumentStep, CallArguments};
#[cfg(verus_only)]
use super::atom::{scalar_atom_matches, scalar_atom_results_agree};
use crate::ncg2m::defn::span_of;
#[cfg(verus_only)]
use crate::project::{DefnCallEdge, defn_call_argument_origin, defn_call_arguments};

mod slice;
pub use slice::ScalarInvocationSlice;
#[cfg(verus_only)]
pub use slice::{
    invocation_slice_is_deterministic, invocation_slice_matches, invocation_slice_reaches_terminal,
    invocation_slice_results_agree,
    invocation_terminal_slice_extends, resumed_invocation_slices_match,
};

verus! {

/// 引数を一つ評価して継続するか、呼び出し先の本体へ進む。
pub enum ScalarInvocationStep<'plan, 'p, 'a> {
    /// 左側の引数の値を保持した、再開可能な呼び出し。
    Continue(ScalarInvocation<'plan, 'p, 'a>),
    /// 全引数を束縛した呼び出し先の環境。
    Enter {
        /// 呼び出し先の評価順の順位。
        rank: usize,
        /// 呼び出し先の本体と新しい仮引数環境。
        frame: ScalarCallFrame<'p, 'a>,
    },
}

/// 引数の評価で呼び出しを進められなかった理由。
#[derive(Debug)]
pub enum ScalarInvocationError<'p, 'a> {
    /// 元の位置のまま返す整数リテラルの診断。
    Literal(ScalarLiteralError<'p, 'a>),
    /// この段階で扱うアトム評価から先へ進む必要がある引数。
    Deferred {
        /// 呼び出し元のソースと文書版。
        source: &'p ProjectSource<'a>,
        /// 次に評価する式の元範囲。
        span: Range<usize>,
    },
}

/// 呼び出し元の仮引数と、左から評価した引数の値を保持する。
pub struct ScalarInvocation<'plan, 'p, 'a> {
    caller: ScalarCallFrame<'p, 'a>,
    caller_rank: usize,
    callee: DefnEvaluationBody<'p, 'a>,
    callee_rank: usize,
    waiting: CallArguments<'plan, 'p, 'a, ScalarValue>,
}

impl<'plan, 'p, 'a> ScalarInvocation<'plan, 'p, 'a> {
    /// 継続で保持している、型と値を持つ呼び出し元。
    pub closed spec fn caller_model(&self) -> ScalarCallFrame<'p, 'a> { self.caller }

    /// 引数に対応する元の呼び出し位置を表す。
    pub closed spec fn edge_model(&self) -> DefnCallEdge<'p, 'a> { *self.waiting.model().0 }

    /// 現在までに左から評価した値を表す。
    pub closed spec fn arguments_model(&self) -> Seq<ScalarValue> { self.waiting.model().1 }

    /// 呼び出し先の本体を表す。
    pub closed spec fn callee_model(&self) -> DefnEvaluationBody<'p, 'a> { self.callee }

    /// 呼び出し辺の始点と終点の順位を表す。
    pub closed spec fn ranks_model(&self) -> (usize, usize) { (self.caller_rank, self.callee_rank) }

    #[verifier::type_invariant]
    spec fn ready(&self) -> bool {
        let values = self.arguments_model();
        let edge = self.edge_model();
        let body = self.callee_model();
        &&& self.callee_rank < self.caller_rank
        &&& edge.at == self.caller_model().body_model().at
        &&& *edge.call.source == *self.caller_model().body_model().source
        &&& forall|i: int| 0 <= i < edge.arguments@.len() ==>
            (#[trigger] edge.arguments@[i]) < self.caller_model().body_model().forms@.len()
        &&& body.at < body.forms@.len()
        &&& form_spans_valid(body.source.text_model(), body.forms@, body.source.text_model().spec_bytes().len() as int)
        &&& values.len() <= edge.arguments@.len() == body.signature.parameters@.len()
        &&& forall|i: int| 0 <= i < values.len() ==> {
            let value = #[trigger] values[i];
            let parameter = body.signature.parameters@[i].ty.ty;
            scalar_fits(value, parameter)
                && scalar_atom_matches(&self.caller, edge.arguments@[i], parameter, Ok(Some(value)))
        }
    }

    /// 左から次の引数を評価する。全引数がそろっていれば呼び出し先の環境を作る。
    ///
    /// # Errors
    ///
    /// 最初に評価できない引数の診断を返す。アトム以外の式を評価する必要がある場合は、
    /// 保留した式の元の位置を返す。
    pub fn advance(self) -> (result: Result<ScalarInvocationStep<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>)
        ensures self.advance_matches(result),
    {
        proof { use_type_invariant(&self); }
        let ghost previous = self;
        let Self { caller, caller_rank, callee, callee_rank, waiting } = self;
        match waiting.next() {
            CallArgumentStep::Invoke { values, .. } => {
                assert(parameters_match(callee.signature, values@));
                let entered = ScalarInvocationStep::Enter { rank: callee_rank, frame: ScalarCallFrame { body: callee, values, fold_bindings: None } };
                assert(previous.advance_matches(Ok(entered)));
                Ok(entered)
            }
            CallArgumentStep::Evaluate(pending) => {
                let slot = pending.slot();
                let at = pending.expression();
                let expected = callee.signature.parameters[slot].ty.ty;
                let value = match caller.evaluate_atom(at, expected) {
                    Err(error) => return Err(ScalarInvocationError::Literal(error)),
                    Ok(None) => {
                        let body = caller.body();
                        let span = span_of(&body.forms[at]);
                        return Err(ScalarInvocationError::Deferred { source: body.source, span });
                    }
                    Ok(Some(value)) => value,
                };
                let Ok(waiting) = pending.resume::<ScalarLiteralError>(Ok(value)) else { unreachable!() };
                proof {
                    let values = waiting.model().1;
                    let edge = *waiting.model().0;
                    assert forall|i: int| 0 <= i < values.len() implies {
                        let argument = #[trigger] values[i];
                        let parameter = callee.signature.parameters@[i].ty.ty;
                        scalar_fits(argument, parameter)
                            && scalar_atom_matches(&caller, edge.arguments@[i], parameter, Ok(Some(argument)))
                    } by {
                        if i < slot { assert(values[i] == previous.arguments_model()[i]); }
                        else { assert(i == slot && values[i] == value); }
                    };
                }
                let after = Self { caller, caller_rank, callee, callee_rank, waiting };
                proof {
                    assert(after.arguments_model().take(slot as int) =~= previous.arguments_model());
                    assert(after.arguments_model().last() == value);
                    assert(previous.advance_matches(Ok(ScalarInvocationStep::Continue(after))));
                }
                Ok(ScalarInvocationStep::Continue(after))
            }
        }
    }

    /// 引数評価で保存する値の順序と、最初の失敗で返す元位置を表す。
    pub closed spec fn advance_matches(
        &self, result: Result<ScalarInvocationStep<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>,
    ) -> bool {
        let values = self.arguments_model();
        let slot = values.len() as int;
        let edge = self.edge_model();
        let callee = self.callee_model();
        let state = self.caller_model();
        let source = state.body_model().source;
        let forms = state.body_model().forms@;
        &&& self.ready()
        &&& if slot == edge.arguments@.len() {
            result matches Ok(ScalarInvocationStep::Enter { rank, frame })
                && rank == self.callee_rank && frame.body_model() == callee && frame.parameter_values_model() == values
        } else {
            let argument = edge.arguments@[slot];
            let expected = callee.signature.parameters@[slot].ty.ty;
            match result {
                Ok(ScalarInvocationStep::Continue(after)) => {
                    &&& after.ranks_model() == self.ranks_model()
                    &&& after.caller_model() == state
                    &&& after.callee_model() == callee
                    &&& after.edge_model() == edge
                    &&& after.arguments_model().len() == values.len() + 1
                    &&& after.arguments_model().take(slot) == values
                    &&& scalar_atom_matches(&self.caller, argument, expected, Ok(Some(after.arguments_model().last())))
                }
                Err(ScalarInvocationError::Literal(error)) =>
                    scalar_atom_matches(&self.caller, argument, expected, Err(error)),
                Err(ScalarInvocationError::Deferred { source: failed_source, span }) => {
                    &&& *failed_source == *source
                    &&& span == form_span(forms[argument as int])
                    &&& scalar_atom_matches(&self.caller, argument, expected, Ok(None))
                }
                _ => false,
            }
        }
    }
}

/// 呼び出し元、呼び出し先、引数の値列が同じ再開状態を表す。
pub open spec fn invocation_states_agree(
    first: ScalarInvocation, second: ScalarInvocation,
) -> bool {
    &&& first.caller_model() == second.caller_model()
    &&& first.callee_model() == second.callee_model()
    &&& first.ranks_model() == second.ranks_model()
    &&& first.edge_model() == second.edge_model()
    &&& first.arguments_model() == second.arguments_model()
}

/// 診断が同じ元文書・範囲・理由を表す。
pub open spec fn invocation_errors_agree(
    first: ScalarInvocationError, second: ScalarInvocationError,
) -> bool {
    match (first, second) {
        (ScalarInvocationError::Literal(a), ScalarInvocationError::Literal(b)) =>
            *a.source == *b.source && a.span == b.span && a.error == b.error,
        (ScalarInvocationError::Deferred { source: a, span: left },
            ScalarInvocationError::Deferred { source: b, span: right }) => *a == *b && left == right,
        _ => false,
    }
}

spec fn invocation_step_atom<'plan, 'p, 'a>(
    result: Result<ScalarInvocationStep<'plan, 'p, 'a>, ScalarInvocationError<'p, 'a>>,
) -> Result<Option<ScalarValue>, ScalarLiteralError<'p, 'a>> {
    match result {
        Ok(ScalarInvocationStep::Continue(after)) => Ok(Some(after.arguments_model().last())),
        Err(ScalarInvocationError::Literal(error)) => Err(error),
        _ => Ok(None),
    }
}

proof fn continuation_consumes_argument(before: ScalarInvocation, after: ScalarInvocation)
    requires before.advance_matches(Ok(ScalarInvocationStep::Continue(after))),
    ensures after.edge_model() == before.edge_model(),
        after.arguments_model().len() == before.arguments_model().len() + 1,
        after.arguments_model().len() <= before.edge_model().arguments@.len(),
{
}

proof fn invocation_steps_agree(
    first: ScalarInvocation, second: ScalarInvocation,
    a: Result<ScalarInvocationStep, ScalarInvocationError>,
    b: Result<ScalarInvocationStep, ScalarInvocationError>,
)
    requires invocation_states_agree(first, second), first.advance_matches(a), second.advance_matches(b),
    ensures match (a, b) {
        (Ok(ScalarInvocationStep::Continue(left)), Ok(ScalarInvocationStep::Continue(right))) =>
            invocation_states_agree(left, right),
        (Ok(ScalarInvocationStep::Enter { rank: left, frame: a }), Ok(ScalarInvocationStep::Enter { rank: right, frame: b })) =>
            left == right && a.body_model() == b.body_model() && a.parameter_values_model() == b.parameter_values_model(),
        (Err(left), Err(right)) => invocation_errors_agree(left, right),
        _ => false,
    },
{
    let slot = first.arguments_model().len() as int;
    let edge = first.edge_model();
    let callee = first.callee_model();
    if slot != edge.arguments@.len() {
        let argument = edge.arguments@[slot];
        let expected = callee.signature.parameters@[slot].ty.ty;
        scalar_atom_results_agree(&first.caller_model(), argument, expected,
            invocation_step_atom(a), invocation_step_atom(b));
        if let (Ok(ScalarInvocationStep::Continue(left)), Ok(ScalarInvocationStep::Continue(right))) = (a, b) {
            let before = first.arguments_model();
            let left_values = left.arguments_model();
            let right_values = right.arguments_model();
            assert(left_values.take(slot) == before && right_values.take(slot) == before);
            assert(left_values.last() == right_values.last());
            assert forall|i: int| 0 <= i < left_values.len()
                implies (#[trigger] left_values[i]) == (#[trigger] right_values[i]) by {
                if i < slot {
                    assert(left_values[i] == left_values.take(slot)[i]);
                    assert(right_values[i] == right_values.take(slot)[i]);
                } else {
                    assert(i == slot && i == left_values.len() - 1 && i == right_values.len() - 1);
                }
            };
            assert(left_values =~= right_values);
        }
    }
}

/// 指定した辺が本体直下にあり、順位と引数個数が呼び出し先の宣言に対応することを表す。
pub open spec fn scalar_invocation_applicable(
    plan: &DefnCallPlan, caller_rank: usize, site: usize, caller: DefnEvaluationBody,
) -> bool {
    let project = plan.project_model();
    let order = plan.order_model();
    plan.calls_model_at_rank(caller_rank) matches Some(edges) && site < edges.len() && {
        let edge = edges[site as int];
        &&& edge.at == caller.at
        &&& order.contains(edge.to) && order.index_of(edge.to) < caller_rank
        &&& project.indexed_defn(edge.to.file, edge.to.item) matches Some(header)
            && header.parameters@.len() == edge.arguments@.len()
    }
}

fn prepare_bound_invocation<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, caller_rank: usize, site: usize, caller: ScalarCallFrame<'p, 'a>,
) -> (result: Option<ScalarInvocation<'plan, 'p, 'a>>)
    requires plan.body_matches_at_rank(caller_rank, caller.body_model()),
    ensures result.is_some() == scalar_invocation_applicable(plan, caller_rank, site, caller.body_model()),
        result matches Some(invocation) ==> {
            &&& invocation.ranks_model().0 == caller_rank
            &&& invocation.ranks_model().1 < caller_rank
            &&& invocation.arguments_model().len() == 0
            &&& invocation.caller_model() == caller
            &&& plan.body_matches_at_rank(invocation.ranks_model().1, invocation.callee_model())
            &&& plan.calls_model_at_rank(caller_rank) matches Some(edges)
                && site < edges.len() && edges[site as int] == invocation.edge_model()
            &&& plan.order_model()[invocation.ranks_model().1 as int] == invocation.edge_model().to
        },
{
    let edges = plan.calls_at_rank(caller_rank)?;
    let edge = edges.get(site)?;
    if edge.at != caller.body().at { return None; }
    let Some(args) = prepare_scalar_arguments(plan, caller_rank, site) else { return None; };
    proof {
        assert(args.model().0 == *edge);
        let project = plan.project_model();
        let target = args.model().2;
        let rank = args.ranks_model().1;
        assert(plan.order_model()[rank as int] == edge.to);
        project.indexed_defn_signature_origin(edge.to.file, edge.to.item, Some(target.signature));
        let header = project.indexed_defn(edge.to.file, edge.to.item)->Some_0;
        crate::ncg2m::data_types::signature_result_origin(target.source.text_model(), header, target.signature);
        assert(scalar_invocation_applicable(plan, caller_rank, site, caller.body_model()));
    }
    let (callee_rank, callee, waiting) = args.into_parts();
    #[cfg(verus_only)]
    let _argument_count = edge.arguments.len();
    proof {
        let forms = caller.body_model().forms@;
        assert(defn_call_arguments(forms, edge.at, edge.arguments@));
        assert forall|i: int| 0 <= i < edge.arguments@.len() implies (#[trigger] edge.arguments@[i]) < forms.len() by {
            assert(i < _argument_count);
            defn_call_argument_origin(forms, edge.at, edge.arguments@, i as usize);
        };
    }
    Some(ScalarInvocation { caller, caller_rank, callee, callee_rank, waiting })
}

/// 補助関数の本体直下にある宣言呼び出しについて、引数の評価を準備する。
///
/// 対応する呼び出しがなければ `Ok(None)` を返す。
///
/// # Errors
///
/// 呼び出し元の順位、引数の個数、または型が指定と一致しない場合に返す。
pub fn prepare_scalar_invocation<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, caller_rank: usize, site: usize, values: Vec<ScalarValue>,
) -> (result: Result<Option<ScalarInvocation<'plan, 'p, 'a>>, ScalarBindingError<'p, 'a>>)
    ensures match result {
        Err(error) => binding_at_rank_matches(plan, caller_rank, values@, Err(error)),
        Ok(None) => exists|caller: ScalarCallFrame<'p, 'a>|
            #[trigger] binding_at_rank_matches(plan, caller_rank, values@, Ok(caller))
                && !scalar_invocation_applicable(plan, caller_rank, site, caller.body_model()),
        Ok(Some(invocation)) => {
            &&& binding_at_rank_matches(plan, caller_rank, values@, Ok(invocation.caller_model()))
            &&& scalar_invocation_applicable(plan, caller_rank, site, invocation.caller_model().body_model())
            &&& invocation.ranks_model().0 == caller_rank
            &&& invocation.ranks_model().1 < caller_rank
            &&& invocation.arguments_model().len() == 0
            &&& plan.body_matches_at_rank(invocation.ranks_model().1, invocation.callee_model())
            &&& plan.calls_model_at_rank(caller_rank) matches Some(edges)
                && site < edges.len() && edges[site as int] == invocation.edge_model()
            &&& plan.order_model()[invocation.ranks_model().1 as int] == invocation.edge_model().to
        },
    },
{
    let caller = bind_scalar_call(plan, caller_rank, values)?;
    let ghost original = caller;
    let result = prepare_bound_invocation(plan, caller_rank, site, caller);
    assert(binding_at_rank_matches(plan, caller_rank, values@, Ok(original)));
    Ok(result)
}

}
