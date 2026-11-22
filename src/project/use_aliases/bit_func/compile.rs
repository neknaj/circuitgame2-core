//! プロジェクトの関数を展開し、元の宣言位置からネットリストを取得する。

use super::super::{FunctionExpansionError, FunctionExpansionOrder, UseAliases};
#[cfg(verus_only)]
use super::super::call_dependencies::function_position;
use super::frontend::{BitFuncError, ExpandedBodyError};
use super::lowering::{BitFuncLowerError, CallGroupError, LoweredBitFunc, MixedWiringError, ProjectedLoweringError};
use super::templates::{FunctionTemplateBuildError, FunctionTemplates};
use crate::netlist::{ClockedNor, PortBitLayout};
use crate::project::{CircuitProject, LocatedName};
#[cfg(verus_only)]
use super::templates::complete_circuit_table;
#[cfg(verus_only)]
use super::frontend::function_source_model_matches;
#[cfg(verus_only)]
use crate::netlist::{NorEvaluationError, nor_evaluation_ready, nor_evaluation_result};
#[cfg(verus_only)]
use super::lowering::{SourceChildModel, port_values};
#[cfg(verus_only)]
use crate::netlist::{SourceGateId, SourceTickCircuit, source_clocked_layout};
#[cfg(verus_only)]
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 厳格解析済みのプロジェクトに含まれる、すべての組み合わせ関数のネットリスト。
pub struct ExpandedFunctions<'p, 'a> {
    plan: FunctionExpansionOrder<'p, 'a>,
    table: FunctionTemplates<'p, 'a>,
}

#[cfg(verus_only)]
type FunctionSource = (SourceTickCircuit, Seq<SourceGateId>, Map<SourceGateId, int>);
#[cfg(not(verus_only))]
type FunctionSource = ();

/// tick 回路と、呼び出しが使う入出力ポートのビット配置。
pub(in crate::project::use_aliases) struct ClockedFunctionTemplate {
    pub(in crate::project::use_aliases) circuit: ClockedNor,
    pub(in crate::project::use_aliases) inputs: PortBitLayout,
    pub(in crate::project::use_aliases) outputs: PortBitLayout,
    /// 厳格定義から組み立てた回路と、そのゲートを配列で引くための対応。
    pub(in crate::project::use_aliases) _source: Ghost<FunctionSource>,
}

/// 関数展開の計画または変換で見つかった診断。
#[derive(Debug)]
pub enum ExpandFunctionsError<'p, 'a> {
    /// 呼び出し先の解決に失敗したか、呼び出しに循環がある。
    Plan(FunctionExpansionError<'p, 'a>),
    /// 展開順で最初に変換できなかった関数。
    Function {
        /// 宣言を含むファイルと、そのファイルの厳格索引項目の添字。
        position: (usize, usize),
        /// 該当する検査段階の診断。
        diagnostic: FunctionBuildDiagnostic<'p, 'a>,
    },
}

/// 関数の型と結線を検査し、ネットリストを作るときの診断。
#[derive(Debug)]
pub enum FunctionBuildDiagnostic<'p, 'a> {
    /// 本体の型・結線検査で見つかった違反。
    Prepare(BitFuncError<'p, 'a>),
    /// 宣言したポートまたは構造体配置の違反。
    Ports(BitFuncError<'p, 'a>),
    /// 配線に変換できない定義の右辺。
    Definition(BitFuncError<'p, 'a>),
    /// 宣言した出力幅と実際の出力幅の不一致。
    Output(BitFuncError<'p, 'a>),
    /// 入力、定義、出力のいずれかにビット範囲を割り当てられない。
    Layout(BitFuncLowerError),
    /// 配線を確定できない実引数の範囲。
    Argument(LocatedName<'p, 'a>),
    /// 基底 NOR の追加でゲート数の上限を超えた右辺の範囲。
    LocalGateCapacity(LocatedName<'p, 'a>),
    /// 呼び出し先の展開でゲート数の上限を超えた呼び出し式の範囲。
    CallGateCapacity(LocatedName<'p, 'a>),
    /// 子の出力を保持する一時配線表の長さ上限を超えた。
    CallOutputCapacity {
        /// 出力の追加で上限を超えた子の呼び出し式の範囲。
        site: LocatedName<'p, 'a>,
        /// 追加前の配線本数。
        used: usize,
        /// 追加しようとした配線本数。
        width: usize,
        /// 一時配線表に保持できる配線本数の上限。
        capacity: usize,
    },
}

spec fn expansion_diagnostic<'p, 'a>(error: FunctionTemplateBuildError<'p, 'a>) -> ExpandFunctionsError<'p, 'a> {
    let (position, diagnostic) = match error {
        FunctionTemplateBuildError::Prepare(position, error) => (position, FunctionBuildDiagnostic::Prepare(error)),
        FunctionTemplateBuildError::Lower(position, error) => (position, match error {
            ExpandedBodyError::Ports(error) => FunctionBuildDiagnostic::Ports(error),
            ExpandedBodyError::Definition(error) => FunctionBuildDiagnostic::Definition(error),
            ExpandedBodyError::Output(error) => FunctionBuildDiagnostic::Output(error),
            ExpandedBodyError::Lowering(ProjectedLoweringError::Layout(error)) => FunctionBuildDiagnostic::Layout(error),
            ExpandedBodyError::Lowering(ProjectedLoweringError::Wiring(error)) => match error {
                MixedWiringError::LocalGateCapacity(site) => FunctionBuildDiagnostic::LocalGateCapacity(site),
                MixedWiringError::Call(CallGroupError::DeferredArgument(site)) => FunctionBuildDiagnostic::Argument(site),
                MixedWiringError::Call(CallGroupError::GateCapacity(site)) => FunctionBuildDiagnostic::CallGateCapacity(site),
                MixedWiringError::CallOutputCapacity { site, used, width, capacity } =>
                    FunctionBuildDiagnostic::CallOutputCapacity { site, used, width, capacity },
            },
        }),
    };
    ExpandFunctionsError::Function { position, diagnostic }
}

fn public_diagnostic<'p, 'a>(error: FunctionTemplateBuildError<'p, 'a>) -> (result: ExpandFunctionsError<'p, 'a>)
    ensures result == expansion_diagnostic(error),
{
    let (position, diagnostic) = match error {
        FunctionTemplateBuildError::Prepare(position, error) => (position, FunctionBuildDiagnostic::Prepare(error)),
        FunctionTemplateBuildError::Lower(position, error) => (position, match error {
            ExpandedBodyError::Ports(error) => FunctionBuildDiagnostic::Ports(error),
            ExpandedBodyError::Definition(error) => FunctionBuildDiagnostic::Definition(error),
            ExpandedBodyError::Output(error) => FunctionBuildDiagnostic::Output(error),
            ExpandedBodyError::Lowering(ProjectedLoweringError::Layout(error)) => FunctionBuildDiagnostic::Layout(error),
            ExpandedBodyError::Lowering(ProjectedLoweringError::Wiring(error)) => match error {
                MixedWiringError::LocalGateCapacity(site) => FunctionBuildDiagnostic::LocalGateCapacity(site),
                MixedWiringError::Call(CallGroupError::DeferredArgument(site)) => FunctionBuildDiagnostic::Argument(site),
                MixedWiringError::Call(CallGroupError::GateCapacity(site)) => FunctionBuildDiagnostic::CallGateCapacity(site),
                MixedWiringError::CallOutputCapacity { site, used, width, capacity } =>
                    FunctionBuildDiagnostic::CallOutputCapacity { site, used, width, capacity },
            },
        }),
    };
    ExpandFunctionsError::Function { position, diagnostic }
}

impl<'p, 'a> ExpandedFunctions<'p, 'a> {
    #[verifier::type_invariant]
    spec fn circuits_are_complete(&self) -> bool {
        &&& self.plan.source_positions_complete()
        &&& self.plan.source_vertices_match()
        &&& complete_circuit_table(&self.plan, &self.table)
    }

    /// 宣言位置が参照する元のプロジェクトを返す。
    pub fn project(&self) -> (project: &'p CircuitProject<'a>)
        ensures *project == self.project_model(),
    {
        self.plan.project()
    }

    /// 宣言位置を解釈するプロジェクトを表す。
    pub closed spec fn project_model(&self) -> CircuitProject<'a> { self.plan.project_model() }

    /// 元の厳格索引に関数宣言があることを表す。
    pub closed spec fn has_function_at(&self, file: usize, entry: usize) -> bool {
        self.plan.declares_function_at((file, entry))
    }

    /// 展開順の同じ宣言に格納したネットリストであることを表す。
    pub closed spec fn circuit_at(&self, file: usize, entry: usize, circuit: &LoweredBitFunc) -> bool {
        exists|i: int| {
            &&& 0 <= i < self.plan.order_model().len()
            &&& #[trigger] self.plan.position_model(i) == Some((file, entry))
            &&& self.plan.order_model()[i] < self.table.slots_model().len()
            &&& self.table.slots_model()[self.plan.order_model()[i] as int] matches Some(template)
            &&& circuit == template.circuit_model()
        }
    }

    /// 指定したファイルと厳格索引項目に対応するネットリストを返す。
    ///
    /// 添字には [Self::project] が返すプロジェクトのものを使う。
    /// 範囲外の添字と、関数以外の項目には `None` を返す。
    pub fn get(&self, file: usize, entry: usize) -> (result: Option<&LoweredBitFunc>)
        ensures
            result.is_some() <==> self.has_function_at(file, entry),
            result matches Some(circuit) ==> self.circuit_at(file, entry, circuit)
                && nor_evaluation_ready(circuit.netlist_model(), circuit.input_layout_model().total_bits_model() as nat)
                && circuit.netlist_model().outputs@.len() == circuit.output_layout_model().total_bits_model(),
    {
        proof { use_type_invariant(self); }
        let vertex = self.plan.template_vertex((file, entry));
        proof { self.plan.source_vertex_lookup((file, entry), vertex); }
        let Some(vertex) = vertex else { return None; };
        let result = self.table.circuit_at_vertex(vertex);
        assert(result matches Some(circuit) && self.circuit_at(file, entry, circuit)) by {
            let rank = choose|rank: int| 0 <= rank < self.plan.order_model().len()
                && #[trigger] self.plan.position_model(rank) == Some((file, entry))
                && self.plan.order_model()[rank] == vertex;
            assert(self.plan.order_model()[rank] < self.table.slots_model().len());
        };
        result
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 展開の結果が、指定した上限での展開計画と最初の失敗の根拠を保持することを表す。
    pub closed spec fn expand_functions_result(
        &self, width_limit: u64, bit_limit: usize, gate_limit: usize, result: Result<ExpandedFunctions, ExpandFunctionsError>,
    ) -> bool {
        match result {
            Ok(expanded) => self.function_expansion_evidence(Ok(expanded.plan))
                && self.ordered_template_build_result(&expanded.plan, width_limit, bit_limit, gate_limit, Ok(expanded.table))
                && expanded.project_model() == self.targets.project_model(),
            Err(ExpandFunctionsError::Plan(error)) => self.function_expansion_evidence(Err(error)),
            Err(error) => exists|plan: FunctionExpansionOrder, failure: FunctionTemplateBuildError|
                #![trigger self.function_expansion_evidence(Ok(plan)), expansion_diagnostic(failure)]
                self.function_expansion_evidence(Ok(plan))
                && self.ordered_template_build_result(&plan, width_limit, bit_limit, gate_limit, Err(failure))
                && expansion_diagnostic(failure) == error,
        }
    }

    /// 指定した関数とその依存先の展開結果に、返した回路または診断を対応付ける。
    pub closed spec fn expand_reachable_function_result(
        &self, root: (usize, usize), width_limit: u64, bit_limit: usize, gate_limit: usize,
        result: Result<Option<LoweredBitFunc>, ExpandFunctionsError>,
    ) -> bool {
        match result {
            Ok(None) => self.reachable_function_expansion_evidence(root, Ok(None)),
            Err(ExpandFunctionsError::Plan(error)) => self.reachable_function_expansion_evidence(root, Err(error)),
            Err(error) => exists|plan: FunctionExpansionOrder, failure: FunctionTemplateBuildError|
                #![trigger self.reachable_function_expansion_evidence(root, Ok(Some(plan))), expansion_diagnostic(failure)]
                self.reachable_function_expansion_evidence(root, Ok(Some(plan)))
                && self.ordered_template_build_result(&plan, width_limit, bit_limit, gate_limit, Err(failure))
                && expansion_diagnostic(failure) == error,
            Ok(Some(circuit)) => exists|plan: FunctionExpansionOrder, table: FunctionTemplates, rank: int|
                #![trigger self.ordered_template_build_result(&plan, width_limit, bit_limit, gate_limit, Ok(table)),
                    plan.position_model(rank)]
            {
                &&& self.reachable_function_expansion_evidence(root, Ok(Some(plan)))
                &&& self.ordered_template_build_result(&plan, width_limit, bit_limit, gate_limit, Ok(table))
                &&& 0 <= rank < plan.order_model().len()
                &&& plan.position_model(rank) == Some(root)
                &&& plan.order_model()[rank] < table.slots_model().len()
                &&& table.slots_model()[plan.order_model()[rank] as int] matches Some(template)
                &&& circuit == *template.circuit_model()
            },
        }
    }

    /// 到達展開の根に当たるソース回路とゲート順を、厳格定義から求めたことを表す。
    pub(in crate::project::use_aliases) closed spec fn reachable_function_source_circuit(
        &self, root: (usize, usize), width_limit: u64, circuit: SourceTickCircuit, order: Seq<SourceGateId>,
    ) -> bool {
        exists|plan: FunctionExpansionOrder, table: FunctionTemplates, rank: int, models: Seq<SourceChildModel>| {
            &&& #[trigger] self.reachable_function_expansion_evidence(root, Ok(Some(plan)))
            &&& #[trigger] self.function_source_layout_prefix(&plan, &table, width_limit, models)
            &&& 0 <= rank < models.len()
            &&& #[trigger] plan.position_model(rank) == Some(root)
            &&& models[rank].circuit == circuit && models[rank].order == order
        }
    }

    /// 到達展開で返した関数を、厳格定義から構成したソース回路と照合する。
    #[verifier::spinoff_prover]
    pub(in crate::project::use_aliases) proof fn reachable_function_source_layout(
        &self, root: (usize, usize), width_limit: u64, bit_limit: usize, gate_limit: usize, value: &LoweredBitFunc,
    ) -> (layout: (SourceTickCircuit, Seq<SourceGateId>, Map<SourceGateId, int>))
        requires
            self.can_resolve(),
            self.expand_reachable_function_result(root, width_limit, bit_limit, gate_limit, Ok(Some(*value))),
        ensures
            self.reachable_function_source_circuit(root, width_limit, layout.0, layout.1),
            source_clocked_layout(&layout.0, value.netlist_model(), layout.1, layout.2),
    {
        reveal(UseAliases::expand_reachable_function_result);
        let (plan, table, rank) = choose|plan: FunctionExpansionOrder, table: FunctionTemplates, rank: int| {
            &&& self.reachable_function_expansion_evidence(root, Ok(Some(plan)))
            &&& #[trigger] self.ordered_template_build_result(&plan, width_limit, bit_limit, gate_limit, Ok(table))
            &&& 0 <= rank < plan.order_model().len()
            &&& #[trigger] plan.position_model(rank) == Some(root)
            &&& plan.order_model()[rank] < table.slots_model().len()
            &&& table.slots_model()[plan.order_model()[rank] as int] matches Some(template)
            &&& *value == *template.circuit_model()
        };
        self.reachable_function_template_plan(root, plan);
        let models = self.completed_function_source_layout_prefix(&plan, &table, width_limit, bit_limit, gate_limit, (rank + 1) as nat);
        let model = models[rank];
        assert(function_source_model_matches(&plan, &table, rank, model));
        let vertex = plan.order_model()[rank];
        let template = table.slots_model()[vertex as int]->Some_0;
        assert(source_clocked_layout(&model.circuit, template.circuit_model().netlist_model(), model.order, model.index));
        reveal(UseAliases::reachable_function_source_circuit);
        assert(self.reachable_function_source_circuit(root, width_limit, model.circuit, model.order));
        (model.circuit, model.order, model.index)
    }

    /// 指定した宣言をソースの規則で評価したとき、入出力の値が対応することを表す。
    pub closed spec fn expanded_function_source_evaluation(
        &self, expanded: &ExpandedFunctions, file: usize, entry: usize, width_limit: u64,
        inputs: Seq<Seq<bool>>, outputs: Seq<Seq<bool>>,
    ) -> bool {
        exists|rank: int| 0 <= rank < expanded.plan.order_model().len()
            && #[trigger] expanded.plan.position_model(rank) == Some((file, entry))
            && self.project_source_func_evaluation(&expanded.plan, width_limit, rank, inputs, outputs)
    }

    /// 宣言された入力ビット数で評価した結果が、ソースの規則で一意に決まる出力と一致することを示す。
    pub proof fn expanded_function_evaluate_has_source_result(
        &self, expanded: &ExpandedFunctions, file: usize, entry: usize, circuit: &LoweredBitFunc,
        width_limit: u64, bit_limit: usize, gate_limit: usize, input: Seq<bool>, result: Result<Vec<bool>, NorEvaluationError>,
    )
        requires
            self.can_resolve(),
            self.expand_functions_result(width_limit, bit_limit, gate_limit, Ok(*expanded)),
            expanded.circuit_at(file, entry, circuit),
            input.len() == circuit.input_layout_model().total_bits_model(),
            nor_evaluation_result(circuit.netlist_model(), input, result),
        ensures result matches Ok(output) && {
            let inputs = port_values(circuit.input_layout_model(), input);
            let outputs = port_values(circuit.output_layout_model(), output@);
            &&& self.expanded_function_source_evaluation(expanded, file, entry, width_limit, inputs, outputs)
            &&& forall|expected: Seq<Seq<bool>>|
                #[trigger] self.expanded_function_source_evaluation(expanded, file, entry, width_limit, inputs, expected)
                    ==> expected == outputs
        },
    {
        self.whole_function_template_plan(expanded.plan);
        self.completed_templates_ready(&expanded.plan, width_limit, bit_limit, gate_limit, &expanded.table);
        let rank = choose|rank: int| {
            &&& 0 <= rank < expanded.plan.order_model().len()
            &&& #[trigger] expanded.plan.position_model(rank) == Some((file, entry))
            &&& expanded.plan.order_model()[rank] < expanded.table.slots_model().len()
            &&& expanded.table.slots_model()[expanded.plan.order_model()[rank] as int] matches Some(template)
            &&& circuit == template.circuit_model()
        };
        assert(nor_evaluation_ready(circuit.netlist_model(), input.len()));
        let output = result->Ok_0;
        self.completed_template_preserves_source_evaluation(&expanded.plan, width_limit, bit_limit, gate_limit,
            &expanded.table, rank, input, output@);
        let inputs = port_values(circuit.input_layout_model(), input);
        let outputs = port_values(circuit.output_layout_model(), output@);
        assert forall|expected: Seq<Seq<bool>>|
            #[trigger] self.expanded_function_source_evaluation(expanded, file, entry, width_limit, inputs, expected)
                implies expected == outputs by {
            let other = choose|other: int| 0 <= other < expanded.plan.order_model().len()
                && #[trigger] expanded.plan.position_model(other) == Some((file, entry))
                && self.project_source_func_evaluation(&expanded.plan, width_limit, other, inputs, expected);
            self.template_rank_from_position(expanded.plan, (file, entry), rank, other);
            self.project_source_func_evaluations_agree(&expanded.plan, width_limit, rank, inputs, expected, outputs);
        };
    }

    /// 指定した `func` とその呼び出し先だけを展開し、指定した関数のネットリストを返す。
    ///
    /// ファイルと厳格索引項目の添字が関数を指さない場合は `None` を返す。
    /// 上限の意味は [Self::expand_functions] と同じで、展開する各関数に適用する。
    /// 構造体型を使う場合は、プロジェクトの型宣言も検査する。
    ///
    /// # Errors
    ///
    /// 到達した呼び出しを解決できないか、そこに循環がある場合は計画の診断を返す。
    /// 計画ができた場合は、展開順で最初に変換できなかった関数の位置と診断を返す。
    pub fn expand_reachable_function(
        &self, root: (usize, usize), width_limit: u64, bit_limit: usize, gate_limit: usize,
    ) -> (result: Result<Option<LoweredBitFunc>, ExpandFunctionsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            self.expand_reachable_function_result(root, width_limit, bit_limit, gate_limit, result),
            result matches Ok(Some(circuit)) ==> nor_evaluation_ready(
                circuit.netlist_model(), circuit.input_layout_model().total_bits_model() as nat)
                && circuit.netlist_model().outputs@.len() == circuit.output_layout_model().total_bits_model(),
    {
        let plan = match self.prepare_reachable_function_expansion(root) {
            Ok(Some(plan)) => plan,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ExpandFunctionsError::Plan(error)),
        };
        let ghost rank = self.reachable_function_template_plan(root, plan);
        let table = match self.expand_templates_in_order(&plan, width_limit, bit_limit, gate_limit) {
            Ok(table) => table,
            Err(error) => return Err(public_diagnostic(error)),
        };
        proof { self.completed_templates_ready(&plan, width_limit, bit_limit, gate_limit, &table); }
        let vertex = plan.template_vertex(root);
        proof { plan.template_vertex_at_position(root, rank, vertex); }
        let Some(vertex) = vertex else {
            proof { assert(false); }
            unreachable!()
        };
        let ghost built = table;
        let circuit = table.into_circuit_at_vertex(vertex);
        assert(0 <= rank < plan.order_model().len());
        assert(built.slots_model()[vertex as int] matches Some(template) && circuit == Some(*template.circuit_model()));
        Ok(circuit)
    }

    /// tick 用の子回路が、指定した関数の展開結果と同じ配線を持つことを表す。
    pub(in crate::project::use_aliases) closed spec fn clocked_function_template_matches(
        &self, root: (usize, usize), width_limit: u64, bit_limit: usize, gate_limit: usize, template: &ClockedFunctionTemplate,
    ) -> bool {
        let (source, order, index) = template._source@;
        let netlist = &template.circuit.netlist_model();
        &&& self.reachable_function_source_circuit(root, width_limit, source, order)
        &&& source_clocked_layout(&source, netlist, order, index)
        &&& template.inputs.total_bits_model() == netlist.input_count
        &&& template.outputs.total_bits_model() == netlist.outputs@.len()
        &&& exists|value: LoweredBitFunc| {
            &&& #[trigger] self.expand_reachable_function_result(root, width_limit, bit_limit, gate_limit, Ok(Some(value)))
            &&& *value.netlist_model() == *netlist
            &&& *value.input_layout_model() == template.inputs
            &&& *value.output_layout_model() == template.outputs
        }
    }

    /// 関数の子回路を、呼び出し元で使うソース回路と配置の証拠に結び付ける。
    pub(in crate::project::use_aliases) proof fn clocked_function_template_evidence(
        &self, root: (usize, usize), width: u64, bits: usize, gates: usize, template: &ClockedFunctionTemplate,
    )
        requires self.clocked_function_template_matches(root, width, bits, gates, template),
        ensures
            self.reachable_function_source_circuit(root, width, template._source@.0, template._source@.1),
            source_clocked_layout(&template._source@.0, &template.circuit.netlist_model(), template._source@.1, template._source@.2),
    {
    }

    /// 指定した関数を展開し、各 NOR を保ったまま tick 実行用の子回路にする。
    ///
    /// # Errors
    ///
    /// 到達する関数の展開に失敗した場合は、元の展開診断を返す。
    pub(in crate::project::use_aliases) fn expand_clocked_function(
        &self, root: (usize, usize), width_limit: u64, bit_limit: usize, gate_limit: usize,
    ) -> (result: Result<ClockedFunctionTemplate, ExpandFunctionsError<'p, 'a>>)
        requires self.can_resolve(), function_position(self.targets.project_model().circuits_model(), root),
        ensures match result {
            Ok(template) => self.clocked_function_template_matches(root, width_limit, bit_limit, gate_limit, &template),
            Err(error) => self.expand_reachable_function_result(root, width_limit, bit_limit, gate_limit, Err(error)),
        },
    {
        let value = self.expand_reachable_function(root, width_limit, bit_limit, gate_limit)?;
        let Some(value) = value else {
            proof {
                reveal(UseAliases::expand_reachable_function_result);
                self.reachable_function_not_absent(root);
                assert(false);
            }
            unreachable!()
        };
        let ghost source = self.reachable_function_source_layout(root, width_limit, bit_limit, gate_limit, &value);
        let ghost expanded = value;
        let (circuit, inputs, outputs) = value.into_clocked();
        let template = ClockedFunctionTemplate { circuit, inputs, outputs, _source: Ghost(source) };
        assert(*expanded.netlist_model() == template.circuit.netlist_model());
        assert(self.clocked_function_template_matches(root, width_limit, bit_limit, gate_limit, &template));
        Ok(template)
    }

    /// プロジェクト内のすべての `func` を依存順にネットリストへ展開する。
    ///
    /// `width_limit` は型のビット幅の上限、`bit_limit` は入力・定義・出力それぞれの
    /// ビット配列の上限、`gate_limit` は呼び出しを展開した関数ごとの NOR ゲート数の上限。
    /// `def` の右辺で通常関数や基底 NOR を呼び出すときは、型が確定した信号名、
    /// 型に合うリテラル、出力が一つの通常関数や基底 NOR の呼び出しを引数に使える。
    /// 基底の宣言などプロジェクト全体の検査には [crate::project::analyze_definitions] を使う。
    ///
    /// # Errors
    ///
    /// 呼び出し先を解決できない場合や呼び出しに循環がある場合は、計画の診断を返す。
    /// 計画ができた場合は、展開順で最初に変換できなかった関数の位置と診断を返す。
    /// 子の出力を保持する一時配線表には、`bit_limit` と独立した実行環境ごとの長さ上限がある。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};
    ///
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "calls.ncg2",
    ///     revision: 1,
    ///     text: "(using nor)
    ///            (func inv (in a) (out y) (def y (nor a a)))
    ///            (func copy (in a) (out y) (def y (nor (inv a) (nor a a))))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let functions = aliases.expand_functions(8, 16, 4).unwrap();
    /// let copy = functions.get(0, 2).unwrap();
    /// assert_eq!(copy.netlist().evaluate(&[true]).unwrap(), [true]);
    /// assert_eq!(copy.netlist().evaluate(&[false]).unwrap(), [false]);
    /// assert!(functions.get(0, 0).is_none());
    /// ```
    pub fn expand_functions(
        &self, width_limit: u64, bit_limit: usize, gate_limit: usize,
    ) -> (result: Result<ExpandedFunctions<'p, 'a>, ExpandFunctionsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.expand_functions_result(width_limit, bit_limit, gate_limit, result),
    {
        let plan = match self.prepare_function_expansion() {
            Ok(plan) => plan,
            Err(error) => return Err(ExpandFunctionsError::Plan(error)),
        };
        proof { self.whole_function_template_plan(plan); }
        let table = match self.expand_templates_in_order(&plan, width_limit, bit_limit, gate_limit) {
            Ok(table) => table,
            Err(error) => return Err(public_diagnostic(error)),
        };
        proof {
            self.completed_templates_ready(&plan, width_limit, bit_limit, gate_limit, &table);
            self.template_index_evidence(plan);
        }
        Ok(ExpandedFunctions { plan, table })
    }
}

} // verus!
