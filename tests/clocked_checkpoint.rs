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

#[test]
fn snapshot_file_restores_the_visible_frame_and_checks_port_layout() {
    use circuitgame2_core::netlist::{
        CheckpointFileError, CheckpointHeader, VmCheckpointFileError, checkpoint_file_len,
        decode_vm_checkpoint, encode_vm_checkpoint,
    };
    let mut continuous = vm();
    let mut resumed = vm();
    let inputs = [0..1, 1..3];
    let outputs = [0..1, 1..4];
    let input = [true, true, true];
    let at_save = continuous.step(&input).unwrap();
    let header = CheckpointHeader {
        generation: 2,
        tick: 1,
        period_numerator: 10,
        period_denominator: 1,
    };
    let file = encode_vm_checkpoint(&continuous, &inputs, &outputs, header, &input).unwrap();
    assert_eq!(checkpoint_file_len(&resumed, &inputs, &outputs).unwrap(), file.len());
    assert_eq!(
        checkpoint_file_len(&resumed, &[0..0, 0..1, 1..3], &outputs),
        Err(VmCheckpointFileError::PortLayout),
    );
    assert!(matches!(
        decode_vm_checkpoint(&file, &resumed, &[0..2, 2..3], &outputs, (10, 1)),
        Err(VmCheckpointFileError::File(CheckpointFileError::Layout)),
    ));
    assert!(matches!(
        decode_vm_checkpoint(&file, &resumed, &inputs, &outputs, (9, 1)),
        Err(VmCheckpointFileError::PeriodMismatch),
    ));
    assert!(matches!(
        decode_vm_checkpoint(&file[..file.len() - 1], &resumed, &inputs, &outputs, (10, 1)),
        Err(VmCheckpointFileError::File(CheckpointFileError::Length)),
    ));
    let saved = decode_vm_checkpoint(&file, &resumed, &inputs, &outputs, (10, 1)).unwrap();
    assert_eq!(saved.header, header);
    assert_eq!(saved.input, input);
    resumed.restore_checkpoint(&saved.vm).unwrap();
    assert_eq!(resumed.observe_current(&saved.input).unwrap(), at_save);
    assert_eq!(resumed.ram_memory(1), continuous.ram_memory(1));
    for frame in [[true, false, false], [false, true, true]] {
        assert_eq!(resumed.step(&frame), continuous.step(&frame));
        assert_eq!(resumed.ram_memory(1), continuous.ram_memory(1));
    }
}
