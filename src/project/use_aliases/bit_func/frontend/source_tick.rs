//! 関数の展開順に、先行する関数のソース回路を組み立てる。

use super::*;
use super::body::prior_function_source_models;
use super::super::expansion::PreparedExpansionBody;
use super::super::lowering::SourceChildModel;
use super::super::templates::FunctionTemplates;
use super::super::super::FunctionExpansionOrder;

verus! {

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 指定順位の関数を、同じ計画の先行関数と型付き定義から構成したことを表す。
    spec fn function_source_layout_at(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, width_limit: u64,
        rank: int, models: Seq<SourceChildModel>,
    ) -> bool {
        let model = models[rank];
        &&& 0 <= rank < models.len() <= plan.order_model().len()
        &&& plan.position_model(rank) matches Some((file, entry))
        &&& exists|prior: FunctionTemplates, prepared: PreparedExpansionBody| {
            &&& prior.next_rank() == rank
            &&& prior.slots_model().len() == table.slots_model().len()
            &&& forall|i: int| 0 <= i < rank ==> {
                let earlier = #[trigger] plan.order_model()[i];
                prior.slots_model()[earlier as int] == table.slots_model()[earlier as int]
            }
            &&& #[trigger] self.prepared_expansion_body_matches(*plan, file, entry, width_limit, &prepared)
            &&& #[trigger] self.checked_function_source_layout(plan, &prior, (file, entry, width_limit), &prepared,
                models.take(rank), model)
        }
    }

    /// 展開順の各関数のソース回路が、同じ列の先行部分から構成されていることを表す。
    pub(in crate::project::use_aliases::bit_func) closed spec fn function_source_layout_prefix(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, width_limit: u64, models: Seq<SourceChildModel>,
    ) -> bool {
        &&& models.len() <= plan.order_model().len()
        &&& forall|rank: int| 0 <= rank < models.len() ==>
            #[trigger] self.function_source_layout_at(plan, table, width_limit, rank, models)
    }

    /// 各関数のソース回路を展開順に構成し、同じ順位のテンプレートと対応付ける。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases::bit_func) proof fn completed_function_source_layout_prefix(
        &self, plan: &FunctionExpansionOrder, table: &FunctionTemplates, width_limit: u64, bit_limit: usize,
        gate_limit: usize, count: nat,
    ) -> (models: Seq<SourceChildModel>)
        requires
            self.can_resolve(),
            self.function_template_plan(*plan),
            self.ordered_template_build_result(plan, width_limit, bit_limit, gate_limit, Ok(*table)),
            count <= plan.order_model().len(),
        ensures
            models.len() == count,
            self.function_source_layout_prefix(plan, table, width_limit, models),
            forall|rank: int| 0 <= rank < models.len() ==>
                function_source_model_matches(plan, table, rank, #[trigger] models[rank]),
        decreases count,
    {
        if count == 0 {
            return Seq::empty();
        }
        let rank = (count - 1) as int;
        let previous = self.completed_function_source_layout_prefix(plan, table, width_limit, bit_limit, gate_limit, rank as nat);
        let (template, prior, prepared, body) =
            self.completed_template_expansion_at(plan, width_limit, bit_limit, gate_limit, table, rank);
        let (file, entry) = plan.position_model(rank)->Some_0;
        assert(previous.len() == prior.next_rank() <= plan.order_model().len());
        assert forall|i: int| 0 <= i < previous.len() implies
            function_source_model_matches(plan, &prior, i, #[trigger] previous[i]) by {
            let vertex = plan.order_model()[i];
            assert(function_source_model_matches(plan, table, i, previous[i]));
            assert(prior.slots_model()[vertex as int] == table.slots_model()[vertex as int]);
        };
        assert(prior_function_source_models(plan, &prior, previous));
        let caller = (file, entry, width_limit);
        let model = self.expanded_function_source_layout(plan, &prior, caller, &prepared, bit_limit, gate_limit, &body, previous);
        let models = previous.push(model);
        assert(models.take(rank) =~= previous);
        assert(models[rank] == model);
        assert(self.function_source_layout_at(plan, table, width_limit, rank, models));
        assert forall|i: int| 0 <= i < models.len() implies
            #[trigger] self.function_source_layout_at(plan, table, width_limit, i, models) by {
            if i < rank {
                assert(models[i] == previous[i]);
                assert(models.take(i) =~= previous.take(i));
                assert(self.function_source_layout_at(plan, table, width_limit, i, previous));
            }
        };
        assert forall|i: int| 0 <= i < models.len() implies
            function_source_model_matches(plan, table, i, #[trigger] models[i]) by {
            if i < rank {
                assert(models[i] == previous[i]);
                assert(function_source_model_matches(plan, table, i, previous[i]));
            } else {
                assert(i == rank);
                assert(body.circuit == *template.circuit_model());
            }
        };
        models
    }
}

} // verus!
