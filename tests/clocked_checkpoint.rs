//! 公開 API から、確定 tick の回路状態を保存して再開する。

use circuitgame2_core::netlist::{
    ClockedCheckpointError, ClockedNor, ClockedStorageInputs, ClockedVm, NorGate, NorNetlist, Wire,
};

fn vm() -> ClockedVm {
    let circuit = ClockedNor::check(NorNetlist {
        input_count: 5,
        gates: vec![NorGate {
            left: Wire::Gate(0),
            right: Wire::Constant(false),
        }],
        outputs: vec![Wire::Input(0), Wire::Input(3), Wire::Input(4), Wire::Gate(0)],
    })
    .unwrap();
    let storage = vec![
        ClockedStorageInputs {
            address: None,
            data: vec![Wire::Input(1)],
            enable: Wire::Constant(true),
        },
        ClockedStorageInputs {
            address: Some(vec![Wire::Input(0)]),
            data: vec![Wire::Input(1)],
            enable: Wire::Input(2),
        },
    ];
    ClockedVm::new(circuit, 3, storage, 4).unwrap()
}

#[test]
fn restore_preserves_read_first_state_and_rejects_invalid_checkpoints() {
    let write = [true, true, true];
    let read = [true, false, false];
    let mut continuous = vm();
    let at_save = continuous.step(&write).unwrap();
    assert_eq!(at_save, [true, true, false, true]);
    assert_eq!(continuous.ram_memory(1), Some(&[false, true][..]));

    let mut resumed = vm();
    let mut saved = continuous.checkpoint();
    saved.netlist.outputs.swap(1, 2);
    assert_eq!(
        resumed.restore_checkpoint(&saved),
        Err(ClockedCheckpointError::Layout),
    );
    saved.netlist.outputs.swap(1, 2);
    saved.storage[1].memory.as_mut().unwrap().pop();
    assert_eq!(
        resumed.restore_checkpoint(&saved),
        Err(ClockedCheckpointError::StateShape),
    );
    assert_eq!(resumed.observe_current(&[false; 3]).unwrap(), [false; 4]);
    assert_eq!(resumed.ram_memory(1), Some(&[false; 2][..]));

    let saved = continuous.checkpoint();
    resumed.restore_checkpoint(&saved).unwrap();
    assert_eq!(resumed.observe_current(&write).unwrap(), at_save);
    assert_eq!(resumed.ram_memory(1), continuous.ram_memory(1));
    for input in [read, [false, true, true], read] {
        assert_eq!(resumed.step(&input), continuous.step(&input));
        assert_eq!(resumed.ram_memory(1), continuous.ram_memory(1));
    }
}
