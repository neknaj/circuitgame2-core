use circuitgame2_core::project::{
    DeclaredPortType, PortWidthErrorKind, SourceSnapshot, check_routine_port_widths,
    parse_circuit_project,
};
use circuitgame2_core::syntax::circuit::PortTypeSite;
use circuitgame2_core::syntax::{NaturalRangeError, read_natural_u64};

#[test]
fn decimals_preserve_leading_zeroes_and_the_u64_boundary() {
    assert_eq!(read_natural_u64("0000"), Ok(0));
    assert_eq!(read_natural_u64("00018446744073709551615"), Ok(u64::MAX));
    assert_eq!(
        read_natural_u64("18446744073709551616"),
        Err(NaturalRangeError::OutOfRange)
    );
    assert_eq!(
        read_natural_u64("184467440737095516150"),
        Err(NaturalRangeError::OutOfRange)
    );
    for invalid in ["", "-0", "1_000", "１２", "184467440737095516160x"] {
        assert_eq!(
            read_natural_u64(invalid),
            Err(NaturalRangeError::InvalidDigits)
        );
    }
}

#[test]
fn checks_each_port_in_its_original_declaration_order() {
    let source =
        "(using nor) (namespace app (func f (in x (a (bits 000128)) (b ::types::word)) (out x)))";
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "main.ncg2",
        revision: 1,
        text: source,
    }])
    .unwrap();
    assert_eq!(
        check_routine_port_widths(&project, 0, 0, 128).unwrap(),
        None
    );
    assert_eq!(
        check_routine_port_widths(&project, usize::MAX, 2, 128).unwrap(),
        None
    );
    assert_eq!(
        check_routine_port_widths(&project, 0, usize::MAX, 128).unwrap(),
        None
    );
    let widths = check_routine_port_widths(&project, 0, 2, 128)
        .unwrap()
        .unwrap();
    assert_eq!(widths.inputs.len(), 3);
    assert_eq!(widths.inputs[0].ty, DeclaredPortType::Bits(1));
    assert_eq!(widths.inputs[1].ty, DeclaredPortType::Bits(128));
    let PortTypeSite::Named { form } = widths.inputs[2].site.ty else {
        panic!("expected a named type");
    };
    assert_eq!(widths.inputs[2].ty, DeclaredPortType::Named { form });
    assert_eq!(widths.outputs.len(), 1);
    assert_eq!(widths.outputs[0].ty, DeclaredPortType::Bits(1));
}

#[test]
fn distinguishes_width_errors_at_the_numeric_atom_from_resource_errors() {
    for (word, limit, kind) in [
        ("00", 128, PortWidthErrorKind::Zero),
        (
            "18446744073709551616",
            128,
            PortWidthErrorKind::NumericRange,
        ),
        (
            "00129",
            128,
            PortWidthErrorKind::LimitExceeded {
                width: 129,
                limit: 128,
            },
        ),
    ] {
        let text =
            format!("; 幅の指定\n(module f (in (bad (bits {word}))) (out (later (bits 0))))");
        let project = parse_circuit_project(&[SourceSnapshot {
            path: "./lib/tmp/../widths.ncg2",
            revision: 7,
            text: &text,
        }])
        .unwrap();
        let error = check_routine_port_widths(&project, 0, 0, limit).unwrap_err();
        assert_eq!(error.kind, kind);
        assert_eq!(error.source.id.components(), ["lib", "widths.ncg2"]);
        assert_eq!(error.source.revision, 7);
        assert_eq!(&text[error.span], word);
    }
}

#[test]
fn reports_the_port_name_when_the_implicit_width_exceeds_the_limit() {
    let text = "(func f (in) (out x))";
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "main.ncg2",
        revision: 3,
        text,
    }])
    .unwrap();
    let error = check_routine_port_widths(&project, 0, 0, 0).unwrap_err();
    assert_eq!(
        error.kind,
        PortWidthErrorKind::LimitExceeded { width: 1, limit: 0 }
    );
    assert_eq!(&text[error.span], "x");
}
