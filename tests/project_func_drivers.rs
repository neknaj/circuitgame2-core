use circuitgame2_core::project::{
    FuncDriverError, FuncDriverResult, OutputDriver, SourceSnapshot, check_use_aliases,
    index_use_targets, parse_circuit_project,
};

fn source(text: &str) -> SourceSnapshot<'_> {
    SourceSnapshot {
        path: "./lib/tmp/../logic.ncg2",
        revision: 11,
        text,
    }
}

#[test]
fn connects_outputs_to_inputs_and_ordered_definition_results() {
    let text = concat!(
        "(func pair (in a b) (out a b)) ",
        "(func route (in a b) (out y a x z) ",
        "  (def (x y) (pair a b)) (def z a))",
    );
    let project = parse_circuit_project(&[source(text)]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();

    let FuncDriverResult::Checked(buffer) = aliases.check_func_drivers(0, 0, 1).unwrap() else {
        panic!("expected a direct input connection");
    };
    assert!(buffer.definitions.is_empty());
    assert_eq!(
        buffer.outputs,
        [OutputDriver::Input(0), OutputDriver::Input(1)]
    );

    let FuncDriverResult::Checked(routed) = aliases.check_func_drivers(0, 1, 1).unwrap() else {
        panic!("expected mapped definition results");
    };
    assert_eq!(
        routed.outputs,
        [
            OutputDriver::Definition(1),
            OutputDriver::Input(0),
            OutputDriver::Definition(0),
            OutputDriver::Definition(2)
        ]
    );
    let got: Vec<_> = routed
        .definitions
        .iter()
        .map(|d| (d.name.word, d.definition, d.result_index))
        .collect();
    assert_eq!(got, [("x", 0, 0), ("y", 0, 1), ("z", 1, 0)]);
}

#[test]
fn reports_the_first_reused_driver_and_both_source_positions() {
    for (text, drives_input) in [
        ("; 入力\n(func f (in x) (out x) (def x 0))", true),
        ("; 定義\n(func f (in) (out x) (def (x x) (pair)))", false),
        ("; 定義\n(func f (in) (out x) (def x 0) (def x 1))", false),
    ] {
        let project = parse_circuit_project(&[source(text)]).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let aliases = check_use_aliases(&targets).unwrap();
        let error = aliases.check_func_drivers(0, 0, 1).unwrap_err();
        let (first, later) = match error {
            FuncDriverError::DrivesInput { target, input } if drives_input => (input, target),
            FuncDriverError::MultipleDrivers { later, first } if !drives_input => (first, later),
            _ => panic!("unexpected driver error: {error:?}"),
        };
        assert!(first.span.end < later.span.start);
        for location in [first, later] {
            assert_eq!(location.source.id.components(), ["lib", "logic.ncg2"]);
            assert_eq!(location.source.revision, 11);
            assert_eq!(&text[location.span], "x");
        }
    }
}

#[test]
fn reports_missing_outputs_only_after_explicit_definitions_can_be_checked() {
    let text = concat!(
        "(func missing (in x) (out x y z)) ",
        "(func expanded (in) (out y) (expand make (def y 1)) (expand again)) ",
        "(module sequential (in) (out y))",
        "(func pending (in x) (out y) (def x 0) (expand make)) ",
        "(func invalid (in (x (bits 0))) (out y) (expand make))",
    );
    let project = parse_circuit_project(&[source(text)]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let FuncDriverError::MissingOutput(location) = aliases.check_func_drivers(0, 0, 1).unwrap_err()
    else {
        panic!("expected the first undriven output");
    };
    assert_eq!(&text[location.span], "y");
    let FuncDriverResult::NeedsExpansion(location) = aliases.check_func_drivers(0, 1, 1).unwrap()
    else {
        panic!("expected a pending expansion");
    };
    assert_eq!(&text[location.span], "(expand make (def y 1))");
    assert!(matches!(
        aliases.check_func_drivers(0, 2, 1),
        Ok(FuncDriverResult::NotFunc)
    ));
    assert!(matches!(
        aliases.check_func_drivers(usize::MAX, 0, 1),
        Ok(FuncDriverResult::NotFunc)
    ));
    assert!(matches!(
        aliases.check_func_drivers(0, 3, 1),
        Ok(FuncDriverResult::NeedsExpansion(_))
    ));
    assert!(matches!(
        aliases.check_func_drivers(0, 4, 1),
        Err(FuncDriverError::Signature(_))
    ));
}
