//! 複合式を含む引数を一つずつ受け取り、呼び出し先の環境を作る。

use alloc::vec::Vec;
use super::{
    DefnCallPlan, DefnEvaluationBody, ProjectSource, ScalarCallFrame, ScalarExpressionSite,
    ScalarValue, scalar_matches,
};
use super::super::{CallArgumentStep, CallArguments, PendingCallArgument};
#[cfg(verus_only)]
use super::{parameters_match, scalar_fits};
#[cfg(verus_only)]
use crate::project::{DefnCallEdge, defn_call_arguments};
#[cfg(verus_only)]
use crate::syntax::form_spans_valid;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

struct Callee<'p, 'a> {
    body: DefnEvaluationBody<'p, 'a>,
    from: usize,
    to: usize,
}

spec fn typed_arguments(
    signature: super::DefnSignature, values: Seq<ScalarValue>,
) -> bool {
    &&& values.len() <= signature.parameters@.len()
    &&& forall|i: int| 0 <= i < values.len() ==>
        scalar_fits(#[trigger] values[i], signature.parameters@[i].ty.ty)
}

spec fn arguments_ready(callee: Callee, edge: DefnCallEdge, values: Seq<ScalarValue>) -> bool {
    let body = callee.body;
    &&& callee.to < callee.from
    &&& body.at < body.forms@.len()
    &&& form_spans_valid(body.source.text_model(), body.forms@, body.source.text_model().spec_bytes().len() as int)
    &&& edge.arguments@.len() == body.signature.parameters@.len()
    &&& typed_arguments(body.signature, values)
}

/// ある呼び出しで、左から受け取った引数を保持する。
pub struct ScalarArguments<'plan, 'p, 'a> {
    callee: Callee<'p, 'a>,
    waiting: CallArguments<'plan, 'p, 'a, ScalarValue>,
}

/// 次の引数の評価位置、または引数を束縛した呼び出し先。
pub enum ScalarArgumentsStep<'plan, 'p, 'a> {
    /// 呼び出し元の環境で次の引数を評価する。
    Argument(PendingScalarArgument<'plan, 'p, 'a>),
    /// 引数がそろったため、呼び出し先の本体へ移る。
    Enter {
        /// 呼び出し先の評価順の順位。
        rank: usize,
        /// 呼び出し先の本体と仮引数の環境。
        frame: ScalarCallFrame<'p, 'a>,
    },
}

/// 呼び出し元の構文木にある、次の引数の評価結果を待つ。
pub struct PendingScalarArgument<'plan, 'p, 'a> {
    callee: Callee<'p, 'a>,
    pending: PendingCallArgument<'plan, 'p, 'a, ScalarValue>,
}

impl<'plan, 'p, 'a> ScalarArguments<'plan, 'p, 'a> {
    #[verifier::type_invariant]
    spec fn ready(&self) -> bool {
        arguments_ready(self.callee, *self.waiting.model().0, self.waiting.model().1)
    }

    /// 呼び出し辺、受け取った値、呼び出し先の本体を表す。
    pub closed spec fn model(&self) -> (DefnCallEdge<'p, 'a>, Seq<ScalarValue>, DefnEvaluationBody<'p, 'a>) {
        (*self.waiting.model().0, self.waiting.model().1, self.callee.body)
    }

    /// 呼び出し元と呼び出し先の順位を表す。
    pub closed spec fn ranks_model(&self) -> (usize, usize) { (self.callee.from, self.callee.to) }

    pub(super) fn result_type(&self) -> (ty: super::DataType<'a>)
        ensures ty == self.model().2.signature.result_type.ty,
    {
        self.callee.body.signature.result_type.ty
    }

    pub(super) fn into_parts(self)
        -> (parts: (usize, DefnEvaluationBody<'p, 'a>, CallArguments<'plan, 'p, 'a, ScalarValue>))
        ensures
            parts.0 == self.ranks_model().1,
            parts.1 == self.model().2,
            *parts.2.model().0 == self.model().0,
            parts.2.model().1 == self.model().1,
            parts.1.signature.parameters@.len() == parts.2.model().0.arguments@.len(),
    {
        proof { use_type_invariant(&self); }
        (self.callee.to, self.callee.body, self.waiting)
    }

    /// 次の引数の位置を確定する。値がそろっていれば呼び出し先の環境を作る。
    pub fn next(self) -> (step: ScalarArgumentsStep<'plan, 'p, 'a>)
        ensures match step {
            ScalarArgumentsStep::Argument(pending) => {
                &&& pending.model() == self.model()
                &&& pending.ranks_model() == self.ranks_model()
                &&& self.model().1.len() < self.model().0.arguments@.len()
            },
            ScalarArgumentsStep::Enter { rank, frame } => {
                &&& rank == self.ranks_model().1 && rank < self.ranks_model().0
                &&& frame.body_model() == self.model().2
                &&& frame.parameter_values_model() == self.model().1
                &&& !frame.has_scoped_bindings()
                &&& parameters_match(frame.body_model().signature, frame.parameter_values_model())
                &&& self.model().1.len() == self.model().0.arguments@.len()
            },
        },
    {
        proof { use_type_invariant(&self); }
        let Self { callee, waiting } = self;
        match waiting.next() {
            CallArgumentStep::Evaluate(pending) => ScalarArgumentsStep::Argument(PendingScalarArgument { callee, pending }),
            CallArgumentStep::Invoke { values, .. } => {
                let frame = ScalarCallFrame { body: callee.body, values, fold_bindings: None, locals: Vec::new() };
                ScalarArgumentsStep::Enter { rank: callee.to, frame }
            }
        }
    }
}

impl<'plan, 'p, 'a> PendingScalarArgument<'plan, 'p, 'a> {
    #[verifier::type_invariant]
    spec fn ready(&self) -> bool {
        &&& arguments_ready(self.callee, *self.pending.model().0, self.pending.model().1)
        &&& self.pending.model().1.len() < self.pending.model().0.arguments@.len()
    }

    /// 呼び出し辺、左から受け取った値、呼び出し先の本体を表す。
    pub closed spec fn model(&self) -> (DefnCallEdge<'p, 'a>, Seq<ScalarValue>, DefnEvaluationBody<'p, 'a>) {
        (*self.pending.model().0, self.pending.model().1, self.callee.body)
    }

    /// 呼び出し元と呼び出し先の順位を表す。
    pub closed spec fn ranks_model(&self) -> (usize, usize) { (self.callee.from, self.callee.to) }

    pub(super) fn expression_in(&self, Ghost(forms): Ghost<Seq<crate::syntax::Form>>)
        -> (site: ScalarExpressionSite<'a>)
        requires defn_call_arguments(forms, self.model().0.at, self.model().0.arguments@),
        ensures
            site.at < forms.len(),
            self.model().1.len() < self.model().2.signature.parameters@.len(),
            site.at == self.model().0.arguments@[self.model().1.len() as int],
            site.expected == self.model().2.signature.parameters@[self.model().1.len() as int].ty.ty,
    {
        let site = self.expression();
        let _slot = self.pending.slot();
        proof {
            crate::project::defn_call_argument_origin(forms, self.model().0.at, self.model().0.arguments@, _slot);
        }
        site
    }

    /// 次の引数の位置と、呼び出し先の署名が要求する型を返す。
    pub fn expression(&self) -> (site: ScalarExpressionSite<'a>)
        ensures {
            let (edge, values, callee) = self.model();
            let slot = values.len() as int;
            &&& slot < edge.arguments@.len()
            &&& slot < callee.signature.parameters@.len()
            &&& site.at == edge.arguments@[slot]
            &&& site.expected == callee.signature.parameters@[slot].ty.ty
        },
    {
        proof { use_type_invariant(self); }
        let slot = self.pending.slot();
        ScalarExpressionSite { at: self.pending.expression(), expected: self.callee.body.signature.parameters[slot].ty.ty }
    }

    /// 次の引数が書かれた文書と、その版を返す。
    pub fn source(&self) -> (source: &'p ProjectSource<'a>)
        ensures source == self.model().0.call.source,
    {
        self.pending.source()
    }

    /// 次の引数の値を受け取る。署名の型と一致しない場合は元の継続を返す。
    ///
    /// # Errors
    ///
    /// 呼び出し先の仮引数型と、渡した値の型が異なる場合に返す。
    pub fn resume(self, value: ScalarValue) -> (next: Result<ScalarArguments<'plan, 'p, 'a>, Self>)
        ensures {
            let (edge, before, callee) = self.model();
            let slot = before.len() as int;
            &&& edge.arguments@.len() == callee.signature.parameters@.len()
            &&& slot < callee.signature.parameters@.len()
            &&& next.is_ok() == scalar_fits(value, callee.signature.parameters@[slot].ty.ty)
            &&& match next {
                Ok(next) => next.model() == (edge, before.push(value), callee)
                    && next.ranks_model() == self.ranks_model(),
                Err(pending) => pending == self,
            }
        },
    {
        proof { use_type_invariant(&self); }
        let site = self.expression();
        if !scalar_matches(value, site.expected) { return Err(self); }
        let ghost before = self.model().1;
        let Self { callee, pending } = self;
        let Ok(waiting) = pending.resume::<()>(Ok(value)) else { unreachable!() };
        proof {
            let values = waiting.model().1;
            let signature = callee.body.signature;
            assert forall|i: int| 0 <= i < values.len() implies
                scalar_fits(#[trigger] values[i], signature.parameters@[i].ty.ty) by {
                if i < before.len() { assert(values[i] == before[i]); }
                else { assert(i == before.len() && values[i] == value); }
            };
        }
        Ok(ScalarArguments { callee, waiting })
    }
}

/// 取得した引数継続と、計画内の元の呼び出しとの対応を表す。
pub open spec fn prepared_arguments_match<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, site: usize,
    args: Option<ScalarArguments<'plan, 'p, 'a>>,
) -> bool {
    let ranked = plan.order_model();
    let calls = plan.calls_model_at_rank(rank);
    &&& args.is_some() == (calls matches Some(edges) && site < edges.len())
    &&& match args {
        Some(args) => {
            let (edge, values, body) = args.model();
            let (from, to) = args.ranks_model();
            let project = plan.project_model();
            &&& edge == calls->Some_0[site as int]
            &&& values.len() == 0
            &&& edge.arguments@.len() == body.signature.parameters@.len()
            &&& from == rank && to < from < ranked.len()
            &&& edge.from == ranked[rank as int]
            &&& ranked.contains(edge.to) && ranked.index_of(edge.to) == to
            &&& plan.body_matches_at_rank(to, body)
            &&& edge.from.file < project.sources_model().len()
            &&& *edge.call.source == project.sources_model()[edge.from.file as int]
            &&& project.functional_forms_model(edge.from.file) matches Some(forms)
                && defn_call_arguments(forms, edge.at, edge.arguments@)
        },
        None => true,
    }
}

/// 型検査で得た呼び出しの辺から、引数を左から受け取る状態を作る。
///
/// 呼び出し元の順位または呼び出し列の添字が範囲外なら `None` を返す。
/// 計画の各辺について、引数の個数は呼び出し先の署名と一致する。
pub fn prepare_scalar_arguments<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, site: usize,
) -> (args: Option<ScalarArguments<'plan, 'p, 'a>>)
    ensures prepared_arguments_match(plan, rank, site, args),
{
    let edge = plan.calls_at_rank(rank)?.get(site)?;
    let Some(waiting) = plan.call_arguments(rank, site) else { unreachable!() };
    let Some(to) = plan.rank_of(edge.to) else { unreachable!() };
    let Some(body) = plan.body_at_rank(to) else { unreachable!() };
    proof {
        let project = plan.project_model();
        project.indexed_defn_signature_origin(edge.to.file, edge.to.item, Some(body.signature));
        let header = project.indexed_defn(edge.to.file, edge.to.item)->Some_0;
        crate::ncg2m::data_types::signature_result_origin(body.source.text_model(), header, body.signature);
    }
    Some(ScalarArguments { callee: Callee { body, from: rank, to }, waiting })
}

}
