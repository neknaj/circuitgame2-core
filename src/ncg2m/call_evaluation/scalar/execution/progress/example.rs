//! 整数を渡す既存の統合例を、評価器の開始と実行枠の契約に結び付ける。

use super::*;
use crate::ncg2m::call_evaluation::DefnEvaluationBody;
use crate::ncg2m::call_evaluation::scalar::{binding_matches, parameters_match};
use crate::ncg2m::data_types::{
    signature_parameter_types_agree, signature_result_types_agree, signatures_from_header_agree,
};
use crate::ncg2m::integers::IntegerValue;
use core::num::NonZeroUsize;

verus! {

spec fn int_type<'a>() -> DataType<'a> {
    DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Int)), list_depth: 0 }
}

proof fn one_int_argument_fits_declared_signature<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, rank: usize, body: DefnEvaluationBody<'p, 'a>,
    values: Seq<ScalarValue>, error: ScalarBindingError<'p, 'a>,
)
    requires
        plan.body_matches_at_rank(rank, body), plan.order_nodes_valid(),
        body.signature.parameters@.len() == 1, body.signature.parameters@[0].ty.ty == int_type(),
        values == seq![ScalarValue::Integer(IntegerValue::Int(25))],
        binding_at_rank_matches(plan, rank, values, Err(error)),
    ensures false,
{
    let project = plan.project_model();
    let defn = plan.order_model()[rank as int];
    project.indexed_defn_signature_origin(defn.file, defn.item, Some(body.signature));
    if !(error is Rank) {
        let origin = choose|origin: DefnEvaluationBody<'p, 'a>|
            #[trigger] binding_matches(origin, values, Err(error))
                && *origin.source == project.sources_model()[defn.file as int]
                && project.defn_signature_matches_index(defn.file, defn.item, Some(origin.signature));
        project.indexed_defn_signature_origin(defn.file, defn.item, Some(origin.signature));
        let header = project.indexed_defn(defn.file, defn.item)->Some_0;
        signatures_from_header_agree(body.source.text_model(), header, body.signature, origin.signature);
        signature_result_types_agree(body.signature, origin.signature);
        signature_parameter_types_agree(body.signature, origin.signature, 0);
        assert(origin.signature.parameters@.len() == 1);
        assert(origin.signature.parameters@[0].ty.ty == int_type());
        assert(parameters_match(origin.signature, values));
    }
}

// 統合テストの forward と同じく Int の仮引数に 25 を渡し、本体直下の宣言呼び出しに進む。
#[allow(dead_code)]
fn integer_example_takes_the_root_call_path<'plan, 'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, plan: &'plan DefnCallPlan<'p, 'a>,
    rank: usize, site: usize, Ghost(body): Ghost<DefnEvaluationBody<'p, 'a>>,
) -> (result: Result<ScalarExecutionSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>)
    requires
        defn_call_plan_matches(aliases, plan), plan.body_matches_at_rank(rank, body),
        body.signature.parameters@.len() == 1, body.signature.parameters@[0].ty.ty == int_type(),
        body.signature.result_type.ty == int_type(),
        plan.calls_model_at_rank(rank) matches Some(row) && site < row.len() && row[site as int].at == body.at,
    ensures result is Ok && result->Ok_0 is Suspended,
{
    let actual = plan.body_at_rank(rank);
    assert(actual.is_some());
    let mut values = Vec::new();
    values.push(ScalarValue::Integer(IntegerValue::Int(25)));
    let ghost supplied = values@;
    let executing = ScalarExecution::start(plan, rank, values);
    let state = match executing {
        Ok(state) => state,
        Err(error) => {
            proof { one_int_argument_fits_declared_signature(plan, rank, body, supplied, error); }
            unreachable!()
        },
    };
    let ghost beginning = state;
    let one = NonZeroUsize::new(1).unwrap();
    let first = state.run_slice(one);
    proof {
        let frame = choose|frame: ScalarCallFrame<'p, 'a>|
            #[trigger] binding_at_rank_matches(plan, rank, supplied, Ok(frame))
                && beginning.starts_with(plan, rank, frame);
        plan.bodies_at_rank_agree(rank, body, frame.body_model());
        signature_result_types_agree(body.signature, frame.body_model().signature);
        beginning.first_slice_dispatches_scalar_root_call(aliases, plan, rank, frame, site, first);
    }
    let Ok(ScalarExecutionSlice::Suspended(lookup)) = first else { unreachable!() };
    let ghost search = lookup;
    let result = lookup.run_slice(one);
    proof {
        search.one_step_slice_matches(result);
        search.scalar_root_call_lookup_progress(aliases, result);
    }
    result
}
}
