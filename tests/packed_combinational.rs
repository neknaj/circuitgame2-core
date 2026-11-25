//! 組み合わせ回路の配線配置を、GPU 側が使う公開 API から確認する。

use circuitgame2_core::netlist::{
    GateInput, NorEvaluationError, NorGate, NorNetlist, PackedCombinationalError, Wire,
};

#[test]
fn combination_layout_preserves_inputs_gates_and_public_ports() {
    let netlist = NorNetlist {
        input_count: 1,
        gates: vec![
            NorGate { left: Wire::Input(0), right: Wire::Constant(false) },
            NorGate { left: Wire::Gate(0), right: Wire::Constant(true) },
        ],
        outputs: vec![Wire::Constant(true), Wire::Gate(1), Wire::Input(0)],
    };
    let checked = netlist.packed_combinational_layout32().unwrap();
    let layout = checked.layout();
    assert_eq!(layout.source_count(), 5);
    assert_eq!((layout.gates()[0].left, layout.gates()[0].right), (0, 3));
    assert_eq!((layout.gates()[1].left, layout.gates()[1].right), (1, 4));
    assert_eq!(layout.outputs(), [4, 2, 0]);
}

#[test]
fn combination_rejects_a_forward_read_before_a_later_invalid_output() {
    let netlist = NorNetlist {
        input_count: 0,
        gates: vec![NorGate { left: Wire::Gate(0), right: Wire::Constant(false) }],
        outputs: vec![Wire::Input(0)],
    };
    assert!(matches!(
        netlist.packed_combinational_layout32(),
        Err(PackedCombinationalError::Wiring(NorEvaluationError::GateInput {
            gate: 0, input: GateInput::Left
        }))
    ));
}
