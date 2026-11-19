use circuitgame2_core::project::{
    CircuitLiteralWidthError, FuncArityError, FuncCallTarget, FuncLiteralError, FuncWiringResult,
    ResolvedPortType, SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
};

fn source<'a>(path: &'a str, revision: u64, text: &'a str) -> SourceSnapshot<'a> {
    SourceSnapshot { path, revision, text }
}

#[test]
fn uses_the_output_annotation_for_its_driver_and_the_written_width_for_locals() {
    let first = "(func before (in) (out y) (def y 0))";
    let text = concat!(
        "; 日本語のコメント\n",
        "(func preceding (in) (out y) (def y 0)) ",
        "(func f (in direct) (out direct (wide (bits 12)) flag other) ",
        "  (def local #x01) (def flag #x01) (def wide #x01) (def other (raw local)))",
    );
    let project = parse_circuit_project(&[
        source("before.ncg2", 2, first),
        source("./files/../main.ncg2", 11, text),
    ])
    .unwrap();
    let table = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&table).unwrap();
    let result = aliases.check_func_literal_widths(1, 1, 16).unwrap();
    assert_eq!(result.widths, [Some(8), Some(1), Some(12), None]);
    let FuncWiringResult::Checked(wiring) = result.wiring else {
        panic!("expected checked wiring");
    };
    assert_eq!(wiring.drivers.definitions[0].definition, 1);
    assert_eq!(wiring.drivers.definitions[0].name.word, "local");
}

#[test]
fn reports_literal_and_expected_type_locations_for_the_first_violation() {
    let text = concat!(
        "; 日本語\n",
        "(struct Word (width 4)) ",
        "(func narrow (in) (out x y) (def y #x02) (def x #x03)) ",
        "(func fixed (in) (out (y (bits 8))) (def y 1)) ",
        "(func structure (in) (out (y Word)) (def y #x0)) ",
        "(func resource (in) (out y) (def local #x01) (def y 0))",
    );
    let project = parse_circuit_project(&[source("./main.ncg2", 6, text)]).unwrap();
    let table = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&table).unwrap();
    for (entry, value, annotation, expected_reason) in [
        (1, "#x02", "y", CircuitLiteralWidthError::DoesNotFit { expected: 1, required: 2 }),
        (2, "1", "8", CircuitLiteralWidthError::FixedBitWidth { expected: 8 }),
    ] {
        let error = aliases.check_func_literal_widths(0, entry, 16).unwrap_err();
        let FuncLiteralError::Width { literal, required_at: Some(required_at), reason } = error else {
            panic!("expected a width error: {error:?}");
        };
        assert_eq!(&text[literal.span], value);
        assert_eq!(&text[required_at.span], annotation);
        assert_eq!(reason, expected_reason);
        assert_eq!(literal.source.revision, 6);
        assert_eq!(required_at.source.id.components(), ["main.ncg2"]);
    }
    let error = aliases.check_func_literal_widths(0, 3, 16).unwrap_err();
    let FuncLiteralError::StructRequired { literal, type_at, ty: ResolvedPortType::Struct { form, .. } } = error else {
        panic!("expected a struct type mismatch: {error:?}");
    };
    assert_eq!(&text[literal.span], "#x0");
    assert_eq!(&text[type_at.span], "Word");
    assert_eq!(form.name.word, "Word");
    let error = aliases.check_func_literal_widths(0, 4, 7).unwrap_err();
    let FuncLiteralError::Width {
        literal, required_at: None, reason: CircuitLiteralWidthError::LimitExceeded { width: 8, limit: 7 },
    } = error else {
        panic!("expected a resource limit: {error:?}");
    };
    assert_eq!(&text[literal.span], "#x01");
}

#[test]
fn passes_through_arity_errors_and_expansion_pending() {
    let text = concat!(
        "(func bad (in a) (out y) (def too_big #xFF) (def y (nor a))) ",
        "(func later (in) (out y) (def local #xFF) (expand gen)) ",
        "(module m (in) (out y) (def y #xFF))",
    );
    let project = parse_circuit_project(&[source("main.ncg2", 4, text)]).unwrap();
    let table = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&table).unwrap();
    assert!(matches!(
        aliases.check_func_literal_widths(0, 0, 1),
        Err(FuncLiteralError::Arity(FuncArityError::ArgumentCount { target: FuncCallTarget::Nor, .. }))
    ));
    let waiting = aliases.check_func_literal_widths(0, 1, 1).unwrap();
    let FuncWiringResult::NeedsExpansion(site) = waiting.wiring else { panic!("expected expansion"); };
    assert_eq!(&text[site.span], "(expand gen)");
    assert!(waiting.widths.is_empty());
    let module = aliases.check_func_literal_widths(0, 2, 1).unwrap();
    assert!(matches!(module.wiring, FuncWiringResult::NotFunc));
    assert!(module.widths.is_empty());
}
