//! 解析した二つの補助関数が対応断片に属することを示し、評価を始める例。

use super::*;
use crate::syntax::{AtomKind, Form};
use core::num::NonZeroUsize;
#[cfg(verus_only)]
use crate::ncg2m::call_evaluation::{DefnEvaluationBody, scalar::binding_matches};
#[cfg(verus_only)]
use crate::ncg2m::data_types::{signature_result_types_agree, signatures_from_header_agree};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::{scalar_syntax_atom_from_kind, scalar_syntax_call_from_arguments};
use crate::project::MixedUseAliases;
#[cfg(verus_only)]
use crate::project::{defn_call_plan_matches, defn_call_plan_site_at_rank};

verus! {

proof fn zero_arguments_bind_to_empty_signature<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, body: DefnEvaluationBody<'p, 'a>, error: ScalarBindingError<'p, 'a>,
)
    requires
        plan.order_nodes_valid(), plan.body_matches_at_rank(rank, body), body.signature.parameters@.len() == 0,
        binding_at_rank_matches(plan, rank, Seq::empty(), Err(error)),
    ensures false,
{
    let project = plan.project_model();
    let defn = plan.order_model()[rank as int];
    project.indexed_defn_signature_origin(defn.file, defn.item, Some(body.signature));
    if !(error is Rank) {
        let values = Seq::<ScalarValue>::empty();
        let origin = choose|origin: DefnEvaluationBody<'p, 'a>| #[trigger] binding_matches(origin, values, Err(error))
            && *origin.source == project.sources_model()[defn.file as int]
            && project.defn_signature_matches_index(defn.file, defn.item, Some(origin.signature));
        project.indexed_defn_signature_origin(defn.file, defn.item, Some(origin.signature));
        let header = project.indexed_defn(defn.file, defn.item)->Some_0;
        signatures_from_header_agree(body.source.text_model(), header, body.signature, origin.signature);
        signature_result_types_agree(body.signature, origin.signature);
        assert(parameters_match(origin.signature, values));
    }
}

proof fn close_the_two_helper_ranks<'p, 'a>(
    plan: &DefnCallPlan<'p, 'a>, caller: DefnEvaluationBody<'p, 'a>, callee: DefnEvaluationBody<'p, 'a>,
)
    requires
        plan.scalar_fragment_body(1, caller), plan.scalar_fragment_body(0, callee),
        plan.calls_model_at_rank(0) matches Some(row) && row.len() == 0,
        plan.calls_model_at_rank(1) matches Some(row) && row.len() == 1
            && plan.order_model().contains(row[0].to) && plan.order_model().index_of(row[0].to) == 0,
    ensures plan.scalar_fragment_is_closed(1),
{
    let ranks = Set::<usize>::empty().insert(0).insert(1);
    assert forall|rank: usize| #[trigger] ranks.contains(rank) implies {
        &&& exists|body: DefnEvaluationBody<'p, 'a>| #[trigger] plan.scalar_fragment_body(rank, body)
        &&& plan.calls_model_at_rank(rank) matches Some(row) && {
            let order = plan.order_model();
            forall|i: int| 0 <= i < row.len() ==> {
                let edge = #[trigger] row[i];
                &&& order.contains(edge.to)
                &&& 0 <= order.index_of(edge.to) < rank
                &&& ranks.contains(order.index_of(edge.to) as usize)
            }
        }
    } by {
        assert(rank == 0 || rank == 1);
    };
    plan.scalar_fragment_is_closed_over(1, ranks);
}

#[allow(dead_code)]
fn evaluate_two_int_helpers<'plan, 'p, 'a>(
    _aliases: &MixedUseAliases<'_, 'p, 'a>, plan: &'plan DefnCallPlan<'p, 'a>, fuel: NonZeroUsize,
) -> (result: Option<Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>>)
    requires defn_call_plan_matches(_aliases, plan),
    ensures
        result matches Some(run) ==> {
            &&& plan.scalar_fragment_is_closed(1)
            &&& !(run matches Err(ScalarExecutionError::Deferred { .. }))
            &&& (run matches Ok(ScalarExecutionSlice::Suspended(after)) ==> after.preserves_supported_fragment(_aliases))
        },
{
    if plan.len() != 2 { return None; }
    let callee = plan.body_at_rank(0)?;
    let caller = plan.body_at_rank(1)?;
    let callee_sites = plan.calls_at_rank(0)?;
    let caller_sites = plan.calls_at_rank(1)?;
    if !callee_sites.is_empty() || caller_sites.len() != 1
        || !callee.signature.parameters.is_empty() || !caller.signature.parameters.is_empty() {
        return None;
    }
    let int_type = DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Int)), list_depth: 0 };
    if !same_scalar_type(callee.signature.result_type.ty, int_type) || !same_scalar_type(caller.signature.result_type.ty, int_type) {
        return None;
    }
    let edge = &caller_sites[0];
    if edge.at != caller.at || !edge.arguments.is_empty() { return None; }
    if !matches!(callee.forms.get(callee.at), Some(Form::Atom { kind: AtomKind::Natural | AtomKind::NegativeInteger, .. })) {
        return None;
    }
    proof {
        plan.recorded_call_at_rank_has_syntax(_aliases, 1, caller, 0);
        defn_call_plan_site_at_rank(_aliases, plan, 1, 0);
        scalar_syntax_call_from_arguments(caller.source.text_model(), caller.forms@, caller.at, edge.arguments@);
        scalar_syntax_atom_from_kind(callee.source.text_model(), callee.forms@, callee.at);
        close_the_two_helper_ranks(plan, caller, callee);
    }
    let values = Vec::new();
    let ghost supplied = values@;
    assert(supplied =~= Seq::<ScalarValue>::empty());
    let state = match ScalarExecution::start(plan, 1, values) {
        Ok(state) => state,
        Err(error) => {
            proof { zero_arguments_bind_to_empty_signature(plan, 1, caller, error); }
            unreachable!()
        },
    };
    let ghost before = state;
    proof {
        before.starting_execution_preserves_supported_fragment(_aliases, 1, supplied);
    }
    let run = state.run_slice(fuel);
    proof { before.supported_slice_does_not_defer(_aliases, fuel.get() as nat, run); }
    Some(run)
}

}

#[cfg(test)]
#[test]
fn runs_two_parsed_helpers_with_a_supported_fragment() {
    use crate::ncg2m::integers::IntegerValue;
    use crate::project::{SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources};

    let snapshots = [SourceSnapshot {
        path: "scalar-closure.ncg2m", revision: 1,
        text: "(defn entry (as-type (Fn () Int) (fn () (leaf))))
               (defn leaf (as-type (Fn () Int) (fn () 42)))",
    }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let plan = aliases.plan_defn_calls().unwrap();
    let result = evaluate_two_int_helpers(&aliases, &plan, NonZeroUsize::new(64).unwrap()).unwrap().unwrap();
    assert!(matches!(result, ScalarExecutionSlice::Complete(ScalarValue::Integer(IntegerValue::Int(42)))));
}
