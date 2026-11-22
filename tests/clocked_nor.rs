use circuitgame2_core::netlist::{ClockedNor, NorGate, NorNetlist, Wire};

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
