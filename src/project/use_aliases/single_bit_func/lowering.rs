//! 型と結線を検査した1ビット関数を組み合わせネットリストに変換する。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{CheckedSingleBitFunc, SingleBitOperand, SingleBitRhs};
use super::super::OutputDriver;
use crate::netlist::{NorGate, NorNetlist, Wire};
#[cfg(verus_only)]
use super::{
    SingleBitDefinition, single_bit_driver_available, single_bit_func_available, single_bit_operand_available,
    single_bit_rhs_available,
};
#[cfg(verus_only)]
use crate::netlist::{
    NorEvaluationError, gate_values_match, gates_available, nor_evaluation, nor_evaluation_ready,
    nor_evaluation_result, output_ports_available, output_values_match, wire_available, wire_value,
};

verus! {

/// 組み合わせネットリストと、変換前の定義との対応。
#[derive(Debug)]
pub struct LoweredSingleBitFunc {
    netlist: NorNetlist,
    definition_wires: Vec<Wire>,
    gate_definitions: Vec<usize>,
}

impl LoweredSingleBitFunc {
    /// 宣言順のポートと、各 NOR の配線を持つネットリストを返す。
    pub fn netlist(&self) -> (netlist: &NorNetlist)
        ensures *netlist == *self.netlist_model(),
    { &self.netlist }

    /// 元の定義順に、各定義の値を供給する配線を返す。
    pub fn definition_wires(&self) -> (wires: &[Wire])
        ensures wires@ == self.definition_wires_model(),
    { self.definition_wires.as_slice() }

    /// ゲート順に、変換元の定義の添字を返す。
    pub fn gate_definitions(&self) -> (definitions: &[usize])
        ensures definitions@ == self.gate_definitions_model(),
    { self.gate_definitions.as_slice() }

    /// 評価に使うネットリストを表す。
    pub closed spec fn netlist_model(&self) -> &NorNetlist { &self.netlist }

    /// 元の定義を配線へ対応付ける表を表す。
    pub closed spec fn definition_wires_model(&self) -> Seq<Wire> { self.definition_wires@ }

    /// 各ゲートを元の定義へ対応付ける表を表す。
    pub closed spec fn gate_definitions_model(&self) -> Seq<usize> { self.gate_definitions@ }
}

spec fn driver_wire(driver: OutputDriver, wires: Seq<Wire>) -> Wire {
    match driver {
        OutputDriver::Input(index) => Wire::Input(index),
        OutputDriver::Definition(index) => wires[index as int],
    }
}

spec fn operand_wire(operand: SingleBitOperand, wires: Seq<Wire>) -> Wire {
    match operand {
        SingleBitOperand::Driver(driver) => driver_wire(driver, wires),
        SingleBitOperand::Constant(value) => Wire::Constant(value),
    }
}

proof fn operand_wire_is_available(operand: SingleBitOperand, wires: Seq<Wire>, inputs: nat, gates: nat)
    requires
        single_bit_operand_available(operand, inputs, wires.len()),
        forall|i: int| 0 <= i < wires.len() ==> wire_available(#[trigger] wires[i], inputs, gates),
    ensures wire_available(operand_wire(operand, wires), inputs, gates),
{
    if let SingleBitOperand::Driver(OutputDriver::Definition(index)) = operand {
        assert(wire_available(wires[index as int], inputs, gates));
    }
}

spec fn definition_projects<'p, 'a>(
    definitions: Seq<SingleBitDefinition<'p, 'a>>, i: int,
    wires: Seq<Wire>, gates: Seq<NorGate>, origins: Seq<usize>,
) -> bool {
    match definitions[i].rhs {
        SingleBitRhs::Operand(operand) => wires[i] == operand_wire(operand, wires),
        SingleBitRhs::Nor { left, right } => {
            &&& wires[i] matches Wire::Gate(k)
            &&& k < gates.len()
            &&& origins[k as int] == i
            &&& gates[k as int] == NorGate { left: operand_wire(left, wires), right: operand_wire(right, wires) }
        },
    }
}

#[verifier::opaque]
spec fn lowering_prefix<'p, 'a>(
    definitions: Seq<SingleBitDefinition<'p, 'a>>, input_count: nat,
    wires: Seq<Wire>, gates: Seq<NorGate>, origins: Seq<usize>,
) -> bool {
    &&& wires.len() <= definitions.len()
    &&& gates.len() == origins.len()
    &&& gates_available(gates, input_count, gates.len() as int)
    &&& forall|i: int| 0 <= i < wires.len()
        ==> wire_available(#[trigger] wires[i], input_count, gates.len())
    &&& forall|i: int| 0 <= i < wires.len()
        ==> #[trigger] definition_projects(definitions, i, wires, gates, origins)
    &&& forall|k: int| 0 <= k < origins.len() ==> {
        let i = #[trigger] origins[k];
        &&& i < wires.len()
        &&& definitions[i as int].rhs is Nor
        &&& wires[i as int] == Wire::Gate(k as usize)
    }
    &&& forall|k: int, l: int| 0 <= k < l < origins.len() ==> (#[trigger] origins[k]) < (#[trigger] origins[l])
}

/// 各定義の駆動元と NOR の接続を保存し、ゲートは定義順、出力は宣言順に並べることを表す。
pub closed spec fn single_bit_lowering_outputs_match(source: &CheckedSingleBitFunc, result: &LoweredSingleBitFunc) -> bool {
    let definitions = source.definitions_model();
    let wires = result.definition_wires@;
    let gates = result.netlist.gates@;
    &&& single_bit_func_available(source)
    &&& wires.len() == definitions.len()
    &&& result.netlist.input_count == source.inputs_model().len()
    &&& nor_evaluation_ready(result.netlist_model(), source.inputs_model().len())
    &&& result.netlist.outputs@.len() == source.output_drivers_model().len()
    &&& output_wires_match(source.output_drivers_model(), wires, result.netlist.outputs@)
    &&& lowering_prefix(definitions, source.inputs_model().len(), wires, gates, result.gate_definitions@)
}

/// 出力が1本の関数について、各定義と唯一の出力の対応を表す。
pub open spec fn single_bit_lowering_matches(source: &CheckedSingleBitFunc, result: &LoweredSingleBitFunc) -> bool {
    source.output_drivers_model().len() == 1 && single_bit_lowering_outputs_match(source, result)
}

spec fn output_wires_match(drivers: Seq<OutputDriver>, wires: Seq<Wire>, outputs: Seq<Wire>) -> bool {
    &&& outputs.len() <= drivers.len()
    &&& forall|i: int| 0 <= i < outputs.len() ==> (#[trigger] outputs[i]) == driver_wire(drivers[i], wires)
}

proof fn preserve_lowering_prefix<'p, 'a>(
    definitions: Seq<SingleBitDefinition<'p, 'a>>, inputs: nat,
    previous: (Seq<Wire>, Seq<NorGate>, Seq<usize>), next: (Seq<Wire>, Seq<NorGate>, Seq<usize>),
)
    requires
        lowering_prefix(definitions, inputs, previous.0, previous.1, previous.2),
        previous.0.len() < definitions.len(),
        previous.0.len() < usize::MAX,
        previous.1.len() <= usize::MAX,
        ({
            let (wires, gates, origins) = previous;
            let i = wires.len() as int;
            match definitions[i].rhs {
                SingleBitRhs::Operand(operand) => next == (wires.push(operand_wire(operand, wires)), gates, origins),
                SingleBitRhs::Nor { left, right } => next == (
                    wires.push(Wire::Gate(gates.len() as usize)),
                    gates.push(NorGate { left: operand_wire(left, wires), right: operand_wire(right, wires) }),
                    origins.push(i as usize),
                ),
            }
        }),
        forall|i: int| 0 <= i <= previous.0.len()
            ==> single_bit_rhs_available((#[trigger] definitions[i]).rhs, inputs, i as nat),
    ensures lowering_prefix(definitions, inputs, next.0, next.1, next.2),
{
    reveal(lowering_prefix);
    let (wires, gates, origins) = previous;
    let (next_wires, next_gates, next_origins) = next;
    let index = wires.len() as int;
    match definitions[index].rhs {
        SingleBitRhs::Operand(operand) => operand_wire_is_available(operand, wires, inputs, gates.len()),
        SingleBitRhs::Nor { left, right } => {
            operand_wire_is_available(left, wires, inputs, gates.len());
            operand_wire_is_available(right, wires, inputs, gates.len());
        },
    }
    assert forall|i: int| 0 <= i < next_wires.len()
        implies wire_available(#[trigger] next_wires[i], inputs, next_gates.len()) by {
        if i < index {
            assert(next_wires[i] == wires[i]);
        }
    };
    assert forall|i: int| 0 <= i < next_wires.len()
        implies #[trigger] definition_projects(definitions, i, next_wires, next_gates, next_origins) by {
        if i < index {
            assert(definition_projects(definitions, i, wires, gates, origins));
        }
        match definitions[i].rhs {
            SingleBitRhs::Operand(operand) => {
                assert(operand_wire(operand, wires) == operand_wire(operand, next_wires));
            },
            SingleBitRhs::Nor { left, right } => {
                assert(operand_wire(left, wires) == operand_wire(left, next_wires));
                assert(operand_wire(right, wires) == operand_wire(right, next_wires));
            },
        }
    };
    assert forall|k: int| 0 <= k < next_gates.len() implies {
        &&& wire_available((#[trigger] next_gates[k]).left, inputs, k as nat)
        &&& wire_available(next_gates[k].right, inputs, k as nat)
    } by {
        if k < gates.len() {
            assert(next_gates[k] == gates[k]);
        }
    };
    assert forall|k: int| 0 <= k < next_origins.len() implies {
        let i = #[trigger] next_origins[k];
        &&& i < next_wires.len()
        &&& definitions[i as int].rhs is Nor
        &&& next_wires[i as int] == Wire::Gate(k as usize)
    } by {
        if k < origins.len() {
            assert(next_origins[k] == origins[k]);
            assert(next_wires[origins[k] as int] == wires[origins[k] as int]);
        }
    };
    assert forall|k: int, l: int| 0 <= k < l < next_origins.len()
        implies (#[trigger] next_origins[k]) < (#[trigger] next_origins[l]) by {
        assert(next_origins[k] == origins[k]);
        if l < origins.len() {
            assert(next_origins[l] == origins[l]);
        }
    };
}

spec fn source_driver_value(driver: OutputDriver, inputs: Seq<bool>, definitions: Seq<bool>) -> bool {
    match driver {
        OutputDriver::Input(index) => inputs[index as int],
        OutputDriver::Definition(index) => definitions[index as int],
    }
}

spec fn source_operand_value(operand: SingleBitOperand, inputs: Seq<bool>, definitions: Seq<bool>) -> bool {
    match operand {
        SingleBitOperand::Driver(driver) => source_driver_value(driver, inputs, definitions),
        SingleBitOperand::Constant(value) => value,
    }
}

spec fn source_rhs_value(rhs: SingleBitRhs, inputs: Seq<bool>, definitions: Seq<bool>) -> bool {
    match rhs {
        SingleBitRhs::Operand(operand) => source_operand_value(operand, inputs, definitions),
        SingleBitRhs::Nor { left, right } =>
            !(source_operand_value(left, inputs, definitions) || source_operand_value(right, inputs, definitions)),
    }
}

#[verifier::opaque]
spec fn source_definition_values_match(
    definitions: Seq<SingleBitDefinition>, inputs: Seq<bool>, values: Seq<bool>,
) -> bool {
    &&& values.len() == definitions.len()
    &&& forall|i: int| 0 <= i < values.len() ==>
        (#[trigger] values[i]) == source_rhs_value(definitions[i].rhs, inputs, values)
}

spec fn source_output_values_match(
    drivers: Seq<OutputDriver>, inputs: Seq<bool>, definitions: Seq<bool>, outputs: Seq<bool>,
) -> bool {
    &&& outputs.len() == drivers.len()
    &&& forall|i: int| 0 <= i < outputs.len()
        ==> (#[trigger] outputs[i]) == source_driver_value(drivers[i], inputs, definitions)
}

/// 解決済みの信号と右辺から、宣言順の組み合わせ出力を定める。
pub closed spec fn single_bit_source_outputs_evaluation(
    source: &CheckedSingleBitFunc, inputs: Seq<bool>, outputs: Seq<bool>,
) -> bool {
    &&& single_bit_func_available(source)
    &&& inputs.len() == source.inputs_model().len()
    &&& exists|values: Seq<bool>| #[trigger] source_definition_values_match(source.definitions_model(), inputs, values)
        && source_output_values_match(source.output_drivers_model(), inputs, values, outputs)
}

/// 出力が1本の関数について、唯一の出力値を定める。
pub closed spec fn single_bit_source_evaluation(source: &CheckedSingleBitFunc, inputs: Seq<bool>, output: bool) -> bool {
    single_bit_source_outputs_evaluation(source, inputs, seq![output])
}

proof fn source_value_agrees(
    source: &CheckedSingleBitFunc, inputs: Seq<bool>, left: Seq<bool>, right: Seq<bool>, i: nat,
)
    requires
        single_bit_func_available(source),
        inputs.len() == source.inputs_model().len(),
        i < source.definitions_model().len(),
        source_definition_values_match(source.definitions_model(), inputs, left),
        source_definition_values_match(source.definitions_model(), inputs, right),
    ensures left[i as int] == right[i as int],
    decreases i,
{
    let rhs = source.definitions_model()[i as int].rhs;
    assert(left[i as int] == source_rhs_value(rhs, inputs, left)) by { reveal(source_definition_values_match); };
    assert(right[i as int] == source_rhs_value(rhs, inputs, right)) by { reveal(source_definition_values_match); };
    assert(single_bit_rhs_available(rhs, inputs.len(), i));
    match rhs {
        SingleBitRhs::Operand(operand) => {
            if let SingleBitOperand::Driver(OutputDriver::Definition(index)) = operand {
                source_value_agrees(source, inputs, left, right, index as nat);
            }
        },
        SingleBitRhs::Nor { left: a, right: b } => {
            if let SingleBitOperand::Driver(OutputDriver::Definition(index)) = a {
                source_value_agrees(source, inputs, left, right, index as nat);
            }
            if let SingleBitOperand::Driver(OutputDriver::Definition(index)) = b {
                source_value_agrees(source, inputs, left, right, index as nat);
            }
        },
    }
}

/// 同じ型付きの関数と入力に対し、宣言順の出力列が一意に定まることを示す。
pub proof fn single_bit_source_outputs_evaluations_agree(
    source: &CheckedSingleBitFunc, inputs: Seq<bool>, left: Seq<bool>, right: Seq<bool>,
)
    requires
        single_bit_source_outputs_evaluation(source, inputs, left),
        single_bit_source_outputs_evaluation(source, inputs, right),
    ensures left == right,
{
    let definitions = source.definitions_model();
    let drivers = source.output_drivers_model();
    let a = choose|values: Seq<bool>| #[trigger] source_definition_values_match(definitions, inputs, values)
        && source_output_values_match(drivers, inputs, values, left);
    let b = choose|values: Seq<bool>| #[trigger] source_definition_values_match(definitions, inputs, values)
        && source_output_values_match(drivers, inputs, values, right);
    assert forall|i: int| 0 <= i < drivers.len() implies (#[trigger] left[i]) == (#[trigger] right[i]) by {
        let driver = drivers[i];
        if let OutputDriver::Definition(index) = driver {
            source_value_agrees(source, inputs, a, b, index as nat);
        }
    };
    assert(left =~= right);
}

/// 同じ型付きの関数と入力に対し、唯一の出力値が等しいことを示す。
pub proof fn single_bit_source_evaluations_agree(source: &CheckedSingleBitFunc, inputs: Seq<bool>, left: bool, right: bool)
    requires
        single_bit_source_evaluation(source, inputs, left),
        single_bit_source_evaluation(source, inputs, right),
    ensures left == right,
{
    let first = seq![left];
    let second = seq![right];
    single_bit_source_outputs_evaluations_agree(source, inputs, first, second);
    assert(first[0] == left);
    assert(second[0] == right);
}

spec fn wire_values_for_definitions(wires: Seq<Wire>, inputs: Seq<bool>, gates: Seq<bool>) -> Seq<bool> {
    Seq::new(wires.len(), |i: int| wire_value(wires[i], inputs, gates))
}

proof fn operand_value_is_projected(operand: SingleBitOperand, wires: Seq<Wire>, inputs: Seq<bool>, gates: Seq<bool>)
    requires
        single_bit_operand_available(operand, inputs.len(), wires.len()),
        forall|i: int| 0 <= i < wires.len() ==> wire_available(#[trigger] wires[i], inputs.len(), gates.len()),
    ensures wire_value(operand_wire(operand, wires), inputs, gates)
        == source_operand_value(operand, inputs, wire_values_for_definitions(wires, inputs, gates)),
{
    operand_wire_is_available(operand, wires, inputs.len(), gates.len());
    if let SingleBitOperand::Driver(OutputDriver::Definition(index)) = operand {
        assert(wire_values_for_definitions(wires, inputs, gates)[index as int]
            == wire_value(wires[index as int], inputs, gates));
    }
}

/// 任意の合法な入力について、ネットリストの出力列が元の定義から得た出力列と一致することを示す。
pub proof fn single_bit_lowering_preserves_outputs_evaluation(
    source: &CheckedSingleBitFunc, lowered: &LoweredSingleBitFunc, inputs: Seq<bool>, output: Seq<bool>,
)
    requires single_bit_lowering_outputs_match(source, lowered), nor_evaluation(lowered.netlist_model(), inputs, output),
    ensures single_bit_source_outputs_evaluation(source, inputs, output),
{
    reveal(lowering_prefix);
    reveal(nor_evaluation);
    reveal(gate_values_match);
    let definitions = source.definitions_model();
    let wires = lowered.definition_wires@;
    let gates = lowered.netlist.gates@;
    let ports = lowered.netlist.outputs@;
    let origins = lowered.gate_definitions@;
    let gate_values = choose|values: Seq<bool>| #[trigger] gate_values_match(inputs, gates, values)
        && values.len() == gates.len() && output_values_match(inputs, values, ports, output);
    // 各配線の値を元の定義順に並べ、ソースの右辺を満たす値列を得る。
    let values = wire_values_for_definitions(wires, inputs, gate_values);

    assert forall|i: int| 0 <= i < values.len() implies
        (#[trigger] values[i]) == source_rhs_value(definitions[i].rhs, inputs, values) by {
        assert(definition_projects(definitions, i, wires, gates, origins));
        assert(values[i] == wire_value(wires[i], inputs, gate_values));
        match definitions[i].rhs {
            SingleBitRhs::Operand(operand) => operand_value_is_projected(operand, wires, inputs, gate_values),
            SingleBitRhs::Nor { left, right } => {
                operand_value_is_projected(left, wires, inputs, gate_values);
                operand_value_is_projected(right, wires, inputs, gate_values);
                let k = (wires[i]->Gate_0) as int;
                assert(values[i] == gate_values[k]);
            },
        }
    };
    let drivers = source.output_drivers_model();
    assert forall|i: int| 0 <= i < output.len() implies
        (#[trigger] output[i]) == source_driver_value(drivers[i], inputs, values) by {
        let driver = drivers[i];
        assert(ports[i] == driver_wire(driver, wires));
        operand_value_is_projected(SingleBitOperand::Driver(driver), wires, inputs, gate_values);
    };
    assert(source_definition_values_match(definitions, inputs, values)) by { reveal(source_definition_values_match); };
}

/// 出力が1本の関数について、ネットリストの出力値が元の定義から得た値と一致することを示す。
pub proof fn single_bit_lowering_preserves_evaluation(
    source: &CheckedSingleBitFunc, lowered: &LoweredSingleBitFunc, inputs: Seq<bool>, output: Seq<bool>,
)
    requires
        single_bit_lowering_matches(source, lowered),
        nor_evaluation(lowered.netlist_model(), inputs, output),
    ensures output.len() == 1, single_bit_source_evaluation(source, inputs, output[0]),
{
    single_bit_lowering_preserves_outputs_evaluation(source, lowered, inputs, output);
    assert(output =~= seq![output[0]]);
}

/// 入力数が署名どおりなら評価は成功し、宣言順の出力列はソースの評価値に等しい。
pub proof fn single_bit_evaluation_outputs_agree(
    source: &CheckedSingleBitFunc, lowered: &LoweredSingleBitFunc, inputs: Seq<bool>,
    result: Result<Vec<bool>, NorEvaluationError>,
)
    requires
        single_bit_lowering_outputs_match(source, lowered),
        inputs.len() == source.inputs_model().len(),
        nor_evaluation_result(lowered.netlist_model(), inputs, result),
    ensures result matches Ok(outputs)
        && single_bit_source_outputs_evaluation(source, inputs, outputs@)
        && (forall|expected: Seq<bool>| #[trigger] single_bit_source_outputs_evaluation(source, inputs, expected)
            ==> expected == outputs@),
{
    if let Ok(outputs) = result {
        single_bit_lowering_preserves_outputs_evaluation(source, lowered, inputs, outputs@);
        assert forall|expected: Seq<bool>| #[trigger] single_bit_source_outputs_evaluation(source, inputs, expected)
            implies expected == outputs@ by {
            single_bit_source_outputs_evaluations_agree(source, inputs, expected, outputs@);
        };
    }
}

/// 入力数が署名どおりなら評価は成功し、唯一の出力はソースの評価値に等しい。
pub proof fn single_bit_evaluation_result_agrees(
    source: &CheckedSingleBitFunc, lowered: &LoweredSingleBitFunc, inputs: Seq<bool>,
    result: Result<Vec<bool>, NorEvaluationError>,
)
    requires
        single_bit_lowering_matches(source, lowered),
        inputs.len() == source.inputs_model().len(),
        nor_evaluation_result(lowered.netlist_model(), inputs, result),
    ensures result matches Ok(output)
        && output@.len() == 1
        && single_bit_source_evaluation(source, inputs, output@[0])
        && (forall|expected: bool| #[trigger] single_bit_source_evaluation(source, inputs, expected)
            ==> expected == output@[0]),
{
    if let Ok(output) = result {
        single_bit_lowering_preserves_evaluation(source, lowered, inputs, output@);
        assert forall|expected: bool| #[trigger] single_bit_source_evaluation(source, inputs, expected)
            implies expected == output@[0] by {
            single_bit_source_evaluations_agree(source, inputs, expected, output@[0]);
        };
    }
}

fn lower_driver(driver: OutputDriver, wires: &[Wire]) -> (wire: Wire)
    requires driver matches OutputDriver::Definition(i) ==> i < wires@.len(),
    ensures wire == driver_wire(driver, wires@),
{
    match driver {
        OutputDriver::Input(index) => Wire::Input(index),
        OutputDriver::Definition(index) => wires[index],
    }
}

fn lower_operand(operand: SingleBitOperand, wires: &[Wire]) -> (wire: Wire)
    requires operand matches SingleBitOperand::Driver(OutputDriver::Definition(i)) ==> i < wires@.len(),
    ensures wire == operand_wire(operand, wires@),
{
    match operand {
        SingleBitOperand::Driver(driver) => lower_driver(driver, wires),
        SingleBitOperand::Constant(value) => Wire::Constant(value),
    }
}

impl<'p, 'a> CheckedSingleBitFunc<'p, 'a> {
    /// 定義順に NOR を配置し、入出力と元の定義との対応を返す。
    ///
    /// 定数と信号の転送は、対応する配線をそのまま使う。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     SingleBitFuncError, SourceSnapshot, UnsupportedSingleBitFunc, check_use_aliases,
    ///     index_use_targets, parse_circuit_project,
    /// };
    ///
    /// let text = "(using nor)
    ///     (func buffer (in x) (out x))
    ///     (func twice (in x) (out y)
    ///         (def first (nor x 0)) (def alias first) (def y (nor alias 0)))
    ///     (func mixed (in x z) (out b x a z)
    ///         (def a 0) (def b (nor z z)))
    ///     (func wide (in (x (bits 8)) (y (bits 7))) (out (y (bits 7)) (x (bits 8))))";
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "main.ncg2", revision: 1, text,
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    ///
    /// let buffer = aliases.check_single_bit_func(0, 1, 8).unwrap().lower();
    /// assert!(buffer.gate_definitions().is_empty());
    /// assert_eq!(buffer.netlist().evaluate(&[true]).unwrap(), vec![true]);
    ///
    /// let twice = aliases.check_single_bit_func(0, 2, 8).unwrap().lower();
    /// assert_eq!(twice.gate_definitions(), &[0, 2]);
    /// assert_eq!(twice.netlist().evaluate(&[false]).unwrap(), vec![false]);
    /// assert_eq!(twice.netlist().evaluate(&[true]).unwrap(), vec![true]);
    ///
    /// let mixed = aliases.check_single_bit_func_outputs(0, 3, 8).unwrap().lower();
    /// assert_eq!(mixed.gate_definitions(), &[1]);
    /// assert_eq!(mixed.netlist().evaluate(&[true, false]).unwrap(), vec![true, true, false, false]);
    /// assert_eq!(mixed.netlist().evaluate(&[false, true]).unwrap(), vec![false, false, false, true]);
    ///
    /// assert!(matches!(aliases.check_single_bit_func(0, 4, 8),
    ///     Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::OutputCount, _))));
    /// let error = aliases.check_single_bit_func_outputs(0, 4, 8).unwrap_err();
    /// let SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::PortType, site) = error else {
    ///     panic!("{error:?}");
    /// };
    /// assert_eq!(&text[site.span.clone()], "y");
    /// assert!(site.span.start > text.rfind("(out").unwrap());
    /// ```
    pub fn lower(&self) -> (result: LoweredSingleBitFunc)
        ensures
            single_bit_lowering_outputs_match(self, &result),
            self.output_drivers_model().len() == 1 ==> single_bit_lowering_matches(self, &result),
            nor_evaluation_ready(result.netlist_model(), self.inputs_model().len()),
    {
        proof { use_type_invariant(self); }
        let definitions = self.definitions();
        let input_count = self.inputs().len();
        let mut wires = Vec::new();
        let mut gates = Vec::new();
        let mut origins = Vec::new();
        let mut i = 0;
        assert(lowering_prefix(definitions@, input_count as nat, wires@, gates@, origins@)) by {
            reveal(lowering_prefix);
        };
        while i < definitions.len()
            invariant
                definitions@ == self.definitions_model(),
                input_count == self.inputs_model().len(),
                single_bit_func_available(self),
                i == wires@.len(),
                i <= definitions@.len(),
                lowering_prefix(definitions@, input_count as nat, wires@, gates@, origins@),
            decreases definitions@.len() - i,
        {
            let gate_count = gates.len();
            let ghost previous = (wires@, gates@, origins@);
            let wire = match definitions[i].rhs {
                SingleBitRhs::Operand(operand) => lower_operand(operand, wires.as_slice()),
                SingleBitRhs::Nor { left, right } => {
                    let left = lower_operand(left, wires.as_slice());
                    let right = lower_operand(right, wires.as_slice());
                    gates.push(NorGate { left, right });
                    origins.push(i);
                    Wire::Gate(gate_count)
                },
            };
            wires.push(wire);
            proof {
                preserve_lowering_prefix(definitions@, input_count as nat, previous, (wires@, gates@, origins@));
            }
            i += 1;
        }
        proof {
            reveal(lowering_prefix);
            assert(gates_available(gates@, input_count as nat, gates@.len() as int));
        }
        let drivers = self.output_drivers();
        let mut outputs = Vec::new();
        let mut i = 0;
        while i < drivers.len()
            invariant
                drivers@ == self.output_drivers_model(),
                input_count == self.inputs_model().len(),
                single_bit_func_available(self),
                wires@.len() == definitions@.len() == self.definitions_model().len(),
                forall|j: int| 0 <= j < wires@.len()
                    ==> wire_available(#[trigger] wires@[j], input_count as nat, gates@.len()),
                i == outputs@.len() <= drivers@.len(),
                output_wires_match(drivers@, wires@, outputs@),
                output_ports_available(outputs@, input_count as nat, gates@.len(), i as int),
            decreases drivers@.len() - i,
        {
            let driver = drivers[i];
            let out = lower_driver(driver, wires.as_slice());
            proof { operand_wire_is_available(SingleBitOperand::Driver(driver), wires@, input_count as nat, gates@.len()); }
            let ghost previous = outputs@;
            outputs.push(out);
            assert forall|j: int| 0 <= j < outputs@.len()
                implies (#[trigger] outputs@[j]) == driver_wire(drivers@[j], wires@)
                    && wire_available(outputs@[j], input_count as nat, gates@.len()) by {
                if j < i {
                    assert(outputs@[j] == previous[j]);
                }
            };
            i += 1;
        }
        LoweredSingleBitFunc {
            netlist: NorNetlist { input_count, gates, outputs },
            definition_wires: wires,
            gate_definitions: origins,
        }
    }
}

} // verus!
