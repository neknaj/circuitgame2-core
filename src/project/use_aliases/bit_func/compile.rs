//! プロジェクトの関数を展開し、元の宣言位置からネットリストを取得する。

use super::super::{FunctionExpansionError, FunctionExpansionOrder, UseAliases};
use super::frontend::{BitFuncError, ExpandedBodyError};
use super::lowering::{BitFuncLowerError, CallGroupError, LoweredBitFunc, MixedWiringError, ProjectedLoweringError};
use super::templates::{FunctionTemplateBuildError, FunctionTemplates};
use crate::project::{CircuitProject, LocatedName};
#[cfg(verus_only)]
use super::templates::complete_circuit_table;
#[cfg(verus_only)]
use crate::netlist::{NorEvaluationError, nor_evaluation_ready, nor_evaluation_result};
#[cfg(verus_only)]
use super::lowering::port_values;
#[cfg(verus_only)]
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 厳格解析済みのプロジェクトに含まれる、すべての組み合わせ関数のネットリスト。
pub struct ExpandedFunctions<'p, 'a> {
    plan: FunctionExpansionOrder<'p, 'a>,
    table: FunctionTemplates<'p, 'a>,
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

    /// プロジェクト内のすべての `func` を依存順にネットリストへ展開する。
    ///
    /// `width_limit` は型のビット幅の上限、`bit_limit` は入力・定義・出力それぞれの
    /// ビット配列の上限、`gate_limit` は呼び出しを展開した関数ごとの NOR ゲート数の上限。
    /// 通常の呼び出しは `def` の右辺全体で扱う。実引数には型が確定した信号名または
    /// 対応するリテラルを使う。配線を確定できない引数には診断を返す。
    /// 基底の宣言などプロジェクト全体の検査には [crate::project::analyze_definitions] を使う。
    ///
    /// # Errors
    ///
    /// 呼び出し先を解決できない場合や呼び出しに循環がある場合は、計画の診断を返す。
    /// 計画ができた場合は、展開順で最初に変換できなかった関数の位置と診断を返す。
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
    ///            (func twice (in a) (out y) (def t (inv a)) (def y (inv t)))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let functions = aliases.expand_functions(8, 16, 4).unwrap();
    /// let twice = functions.get(0, 2).unwrap();
    /// assert_eq!(twice.netlist().evaluate(&[true]).unwrap(), [true]);
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
