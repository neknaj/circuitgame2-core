use circuitgame2_core::netlist::{ClockedNor, NorGate, NorNetlist, Wire};
use circuitgame2_core::project::{ModuleBodyPosition, SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project};

#[test]
fn oscillator_and_constant_are_observed_from_reset() {
    let circuit = ClockedNor::check(NorNetlist {
        input_count: 0,
        gates: vec![NorGate { left: Wire::Gate(0), right: Wire::Gate(0) }],
        outputs: vec![Wire::Gate(0), Wire::Constant(true)],
    }).unwrap();
    let mut frame = circuit.reset();
    for bit in [false, true, false, true] {
        assert_eq!(frame.outputs, [bit, true]);
        frame = circuit.step(&frame.gates, &[]).unwrap();
    }
}

#[test]
fn cross_coupled_nor_updates_from_the_same_old_state() {
    let circuit = ClockedNor::check(NorNetlist {
        input_count: 2,
        gates: vec![
            NorGate { left: Wire::Input(1), right: Wire::Gate(1) },
            NorGate { left: Wire::Input(0), right: Wire::Gate(0) },
        ],
        outputs: vec![Wire::Gate(0), Wire::Gate(1)],
    }).unwrap();
    let mut frame = circuit.reset();
    assert_eq!(frame.outputs, [false, false]);
    for (input, expected) in [
        ([true, false], [true, false]),
        ([false, false], [true, false]),
        ([false, true], [false, false]),
        ([false, true], [false, true]),
        ([false, false], [false, true]),
    ] {
        frame = circuit.step(&frame.gates, &input).unwrap();
        assert_eq!(frame.outputs, expected);
    }
}

#[test]
fn lowers_a_source_oscillator_with_a_direct_output() {
    let project = parse_circuit_project(&[SourceSnapshot { path: "oscillator.ncg2", revision: 1,
        text: "(using nor) (module oscillator (in pin) (out q pin) (def q (nor q #x0)))" }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let circuit = aliases.lower_primitive_module(ModuleBodyPosition { file: 0, entry: 1 }, 16).unwrap().unwrap();
    let mut frame = circuit.reset();
    assert_eq!(frame.outputs, [false, false]);
    for (pin, q) in [(true, true), (false, false), (true, true)] {
        frame = circuit.step(&frame.gates, &[pin]).unwrap();
        assert_eq!(frame.outputs, [q, pin]);
    }
}

#[test]
fn lowers_a_source_sr_latch_across_module_parts() {
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "latch.ncg2", revision: 2,
            text: "(using nor) (module sr-latch (in set reset) (out q nq) (def q (nor reset nq)))" },
        SourceSnapshot { path: "other.ncg2", revision: 3,
            text: "(module-part sr-latch (def nq (nor set q)))" },
    ]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let parts = targets.collect_module_parts().unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let circuit = aliases.lower_primitive_module(parts[0].module_position, 16).unwrap().unwrap();
    let mut frame = circuit.reset();
    assert_eq!(frame.outputs, [false, false]);
    for (input, expected) in [
        ([true, false], [true, false]),
        ([false, false], [true, false]),
        ([false, true], [false, false]),
        ([false, true], [false, true]),
        ([false, false], [false, true]),
    ] {
        frame = circuit.step(&frame.gates, &input).unwrap();
        assert_eq!(frame.outputs, expected);
    }
}
