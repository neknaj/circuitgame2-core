use circuitgame2_core::project::{
    CallInputError, CallInputReason, FuncAtomTypeError, FuncCallInputsError, FuncSignalTypeError,
    FuncWiringResult, ResolvedPortType, SourceSnapshot, check_use_aliases, index_use_targets,
    parse_circuit_project,
};

#[test]
fn propagates_each_call_output_through_bare_signals() {
    let text = concat!(
        "(func pair (in (value (bits 8)) flag) (out (value (bits 8)) flag)) ",
        "(func f (in a (x (bits 8))) (out y (z (bits 8))) ",
        "  (def (word bit) (pair x a)) (def alias word) (def flag bit) ",
        "  (def z alias) (def y (nor flag a)))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 5, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let result = aliases.check_func_signal_types(0, 1, 8).unwrap();
    assert!(matches!(result.literals.wiring, FuncWiringResult::Checked(_)));
    assert_eq!(result.types.len(), 6);
    for (index, width, origin) in [
        (0, 8, "8"), (1, 1, "flag"), (2, 8, "8"), (3, 1, "flag"), (4, 8, "8"), (5, 1, "(nor flag a)"),
    ] {
        let signal = result.types[index].as_ref().unwrap();
        assert!(matches!(signal.ty, ResolvedPortType::Bits(actual) if actual == width));
        assert_eq!(&text[signal.origin.span.clone()], origin);
    }
    assert_eq!(result.types[0].as_ref().unwrap().origin.span, result.types[4].as_ref().unwrap().origin.span);
}

#[test]
fn reports_call_input_mismatch_with_the_original_callee_output_site() {
    let caller = concat!(
        "(func f (in (x (bits 8)) flag) (out y) ",
        "  (def (word bit) (::lib::Pair x flag)) (def alias word) (def y (nor alias bit)))",
    );
    let library = "(namespace lib (export Pair) (func Pair (in (word (bits 8)) bit) (out (word (bits 8)) bit)))";
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "main.ncg2", revision: 3, text: caller },
        SourceSnapshot { path: "types.ncg2", revision: 9, text: library },
    ]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let error = aliases.check_func_signal_types(0, 0, 8).unwrap_err();
    let FuncSignalTypeError::CallInput(FuncCallInputsError::Call {
        position,
        error: CallInputError::Argument {
            index: 0, argument, expected: ResolvedPortType::Bits(1),
            reason: CallInputReason::SignalType(actual), ..
        },
    }) = error else { panic!("expected a propagated type mismatch: {error:?}"); };
    assert_eq!((position.definition, position.reference), (2, 0));
    assert_eq!(&caller[argument.span], "alias");
    assert_eq!(&library[actual.origin.span], "8");
    assert_eq!(actual.origin.source.revision, 9);
}

#[test]
fn checks_forwarded_outputs_and_preserves_unknown_composite_results() {
    let text = concat!(
        "(func wide (in (x (bits 8))) (out (x (bits 8)))) ",
        "(func f (in (a (bits 8))) (out y) (def x (wide a)) (def y x)) ",
        "(func g (in a) (out y) (def x (raw (nor a a))) (def y x)) ",
        "(func waiting (in) (out y) (expand make))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 1, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let error = aliases.check_func_signal_types(0, 1, 8).unwrap_err();
    let FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType { reference, actual, .. }) = error else {
        panic!("expected an output type mismatch: {error:?}");
    };
    assert_eq!(&text[reference.span], "x");
    assert!(matches!(actual.ty, ResolvedPortType::Bits(8)));
    let unknown = aliases.check_func_signal_types(0, 2, 8).unwrap();
    assert_eq!(unknown.types.len(), 2);
    assert!(unknown.types.iter().all(Option::is_none));
    let waiting = aliases.check_func_signal_types(0, 3, 8).unwrap();
    let FuncWiringResult::NeedsExpansion(site) = waiting.literals.wiring else { panic!("expected expansion"); };
    assert_eq!(&text[site.span], "(expand make)");
    assert!(waiting.types.is_empty());
}
