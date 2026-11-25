use circuitgame2_packed_nor::{
    PackedNorGate32, PackedNorPlan32, PackedNorSizeError, PackedNorWireError,
};

#[test]
fn runs_feedback_and_keeps_output_on_a_bad_frame() {
    let gates = [
        PackedNorGate32 { left: 1, right: 1 },
        PackedNorGate32 { left: 0, right: 0 },
    ];
    let invalid = PackedNorPlan32::new(&gates, 1);
    assert_eq!(invalid.err(), Some(PackedNorWireError { gate: 0, wire: 1 }));

    let plan = PackedNorPlan32::new(&gates, 2).unwrap();
    let mut old = [1u32, 1 << 31];
    let mut next = [0xAAAA_AAAAu32, 0x5555_5555];
    assert_eq!(
        plan.step(&old[..1], &mut next),
        Err(PackedNorSizeError::Source)
    );
    assert_eq!(
        plan.step(&old, &mut next[..1]),
        Err(PackedNorSizeError::Destination)
    );
    assert_eq!(next, [0xAAAA_AAAA, 0x5555_5555]);

    plan.step(&old, &mut next).unwrap();
    assert_eq!(next, [0x7FFF_FFFF, 0xFFFF_FFFE]);
    core::mem::swap(&mut old, &mut next);
    plan.step(&old, &mut next).unwrap();
    assert_eq!(next, [1, 1 << 31]);
}
