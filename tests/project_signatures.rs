use circuitgame2_core::project::{
    OutputSource, PortDirection, PortWidthErrorKind, RoutineSignatureError, SharedPortType,
    SourceSnapshot, check_routine_signature, parse_circuit_project,
};

fn snapshot(text: &str) -> SourceSnapshot<'_> {
    SourceSnapshot {
        path: "./lib/tmp/../logic.ncg2",
        revision: 5,
        text,
    }
}

#[test]
fn records_which_outputs_share_input_wires_in_output_order() {
    let text = concat!(
        "(func buffer (in (x (bits 1)) (y Word) (z Word)) ",
        "(out Y (z Word) x (y (bits 32))))"
    );
    let project = parse_circuit_project(&[snapshot(text)]).unwrap();
    let signature = check_routine_signature(&project, 0, 0, 128)
        .unwrap()
        .unwrap();
    assert_eq!(
        signature.output_sources,
        [
            OutputSource::Body,
            OutputSource::Input {
                port: 2,
                ty: SharedPortType::PendingNamedType
            },
            OutputSource::Input {
                port: 0,
                ty: SharedPortType::EqualBits
            },
            OutputSource::Input {
                port: 1,
                ty: SharedPortType::PendingNamedType
            },
        ]
    );
    assert_eq!(signature.ports.inputs.len(), 3);
}

#[test]
fn diagnoses_the_first_repeated_name_in_each_direction() {
    for (text, direction) in [
        (
            "; 入力\n(func f (in a b b a) (out c c))",
            PortDirection::Input,
        ),
        ("; 出力\n(func f (in) (out a b b a))", PortDirection::Output),
    ] {
        let project = parse_circuit_project(&[snapshot(text)]).unwrap();
        let error = check_routine_signature(&project, 0, 0, 128).unwrap_err();
        let RoutineSignatureError::Duplicate {
            direction: reported,
            first,
            later,
        } = error
        else {
            panic!("expected a duplicate port: {error:?}");
        };
        assert_eq!(reported, direction);
        for location in [&first, &later] {
            assert_eq!(location.source.id.components(), ["lib", "logic.ncg2"]);
            assert_eq!(location.source.revision, 5);
            assert_eq!(&text[location.span.clone()], "b");
        }
        assert_eq!(first.span.start + 2, later.span.start);
    }
}

#[test]
fn reports_output_expectation_and_input_width_at_their_source_locations() {
    for (text, expected_width, actual_width, output_word, input_word) in [
        ("; 幅\n(func f (in (x (bits 02))) (out x))", 1, 2, "x", "02"),
        (
            "; 幅\n(module f (in x) (out (x (bits 02))))",
            2,
            1,
            "02",
            "x",
        ),
    ] {
        let project = parse_circuit_project(&[snapshot(text)]).unwrap();
        let error = check_routine_signature(&project, 0, 0, 128).unwrap_err();
        let RoutineSignatureError::SharedWidthMismatch {
            expected,
            actual,
            input,
            output,
        } = error
        else {
            panic!("expected incompatible shared wires: {error:?}");
        };
        assert_eq!((expected, actual), (expected_width, actual_width));
        assert_eq!(&text[input.span.clone()], input_word);
        assert_eq!(&text[output.span.clone()], output_word);
        assert!(input.span.end < output.span.start);
    }
}

#[test]
fn applies_width_and_duplicate_checks_before_shared_wire_checks() {
    let invalid_width = "(func f (in x x) (out (y (bits 0))))";
    let project = parse_circuit_project(&[snapshot(invalid_width)]).unwrap();
    assert!(matches!(
        check_routine_signature(&project, 0, 0, 128),
        Err(RoutineSignatureError::Width(error)) if error.kind == PortWidthErrorKind::Zero
    ));

    let duplicate_output = "(func f (in x) (out (x (bits 2)) y y))";
    let project = parse_circuit_project(&[snapshot(duplicate_output)]).unwrap();
    assert!(matches!(
        check_routine_signature(&project, 0, 0, 128),
        Err(RoutineSignatureError::Duplicate {
            direction: PortDirection::Output,
            ..
        })
    ));
}
