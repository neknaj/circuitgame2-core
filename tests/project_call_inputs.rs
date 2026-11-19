use circuitgame2_core::project::{
    CallInputError, CallInputReason, CircuitLiteralWidthError, ResolvedPortType, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project,
};

#[test]
fn checks_literals_in_the_callee_context_and_preserves_inherited_signal_types() {
    let text = concat!(
        "; 日本語\n",
        "(func accept (in a) (out y) (def y (nor #x01 a))) ",
        "(func wide (in a) (out y) (def y (nor #x02 a))) ",
        "(func signal (in (a (bits 8))) (out y) (def b a) (def y (nor b 0)))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "./main.ncg2", revision: 13, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let accepted = aliases.check_func_call_inputs(0, 0, 0, 0, 8).unwrap().unwrap();
    assert_eq!(accepted.inputs.len(), 2);
    for (typed, spelling) in accepted.inputs.iter().zip(["#x01", "a"]) {
        let typed = typed.as_ref().unwrap();
        assert!(matches!(typed.ty, ResolvedPortType::Bits(1)));
        assert_eq!(&text[typed.origin.span.clone()], spelling);
    }
    let error = aliases.check_func_call_inputs(0, 1, 0, 0, 8).unwrap_err();
    let CallInputError::Argument {
        index: 0, argument, required_at: None,
        reason: CallInputReason::LiteralWidth(CircuitLiteralWidthError::DoesNotFit { expected: 1, required: 2 }),
        ..
    } = error else { panic!("expected a NOR literal error: {error:?}"); };
    assert_eq!(&text[argument.span], "#x02");
    let error = aliases.check_func_call_inputs(0, 2, 1, 0, 8).unwrap_err();
    let CallInputError::Argument {
        index: 0, argument, expected: ResolvedPortType::Bits(1),
        required_at: None, reason: CallInputReason::SignalType(actual),
    } = error else { panic!("expected a NOR signal error: {error:?}"); };
    assert_eq!(&text[argument.span], "b");
    assert_eq!(&text[actual.origin.span], "8");
    assert_eq!(argument.source.revision, 13);
    assert!(matches!(actual.ty, ResolvedPortType::Bits(8)));
}

#[test]
fn finds_direct_signal_bindings_on_either_side_of_a_nested_call() {
    let text = concat!(
        "(func f (in a (b (bits 8))) (out y) (def y (nor (nor a a) b))) ",
        "(func g (in a b) (out y) (def y (nor (nor a a) b)))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 2, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let outer = aliases.check_func_call_inputs(0, 0, 0, 0, 8).unwrap_err();
    let CallInputError::Argument { index: 1, argument, .. } = outer else {
        panic!("expected a mismatch after the nested call");
    };
    assert_eq!(&text[argument.span], "b");
    let inner = aliases.check_func_call_inputs(0, 0, 0, 1, 8).unwrap().unwrap();
    assert_eq!(inner.inputs.len(), 2);
    assert!(inner.inputs.iter().all(Option::is_some));
    let accepted = aliases.check_func_call_inputs(0, 1, 0, 0, 8).unwrap().unwrap();
    assert!(accepted.inputs[0].is_none());
    assert!(accepted.inputs[1].is_some());
}

#[test]
fn reports_the_callee_annotation_and_caller_origin_for_struct_mismatches() {
    let caller = concat!(
        "; 呼び出し元\n",
        "(func f (in (a ::types::Other)) (out y) (def y (::types::Id a)))",
    );
    let library = concat!(
        "; 型注釈\n",
        "(namespace types (struct Word (width 8)) (struct Other (width 8)) ",
        "  (export Other Id) (func Id (in (value Word)) (out (value Word))))",
    );
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "main.ncg2", revision: 2, text: caller },
        SourceSnapshot { path: "types.ncg2", revision: 7, text: library },
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let error = aliases.check_func_call_inputs(0, 0, 0, 0, 8).unwrap_err();
    let CallInputError::Argument {
        index: 0, argument, expected: ResolvedPortType::Struct { form, .. },
        required_at: Some(required_at), reason: CallInputReason::SignalType(actual),
    } = error else { panic!("expected a nominal type mismatch: {error:?}"); };
    assert_eq!(form.name.word, "Word");
    assert_eq!(&caller[argument.span], "a");
    assert_eq!(&caller[actual.origin.span], "::types::Other");
    assert_eq!(actual.origin.source.revision, 2);
    assert_eq!(&library[required_at.span], "Word");
    assert_eq!(required_at.source.revision, 7);
}
