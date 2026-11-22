use circuitgame2_core::project::{
    CallInputError, CallInputReason, CircuitLiteralWidthError, FuncCallInputsError, FuncWiringResult,
    ResolvedPortType, SourceSnapshot,
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
    let nested = accepted.inputs[0].as_ref().unwrap();
    assert!(matches!(nested.ty, ResolvedPortType::Bits(1)));
    assert_eq!(&text[nested.origin.span.clone()], "(nor a a)");
    assert!(accepted.inputs[1].is_some());
}

#[test]
fn reports_a_nested_call_output_type_from_the_callee_source() {
    let caller = "(func f (in) (out y) (def y (nor (::lib::Wide) 0)))";
    let library = "(namespace lib (export Wide) (func Wide (in) (out (out (bits 8))) (def out #x00)))";
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "main.ncg2", revision: 4, text: caller },
        SourceSnapshot { path: "library.ncg2", revision: 9, text: library },
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let error = aliases.check_all_func_call_inputs(0, 0, 8).unwrap_err();
    let FuncCallInputsError::Call {
        position,
        error: CallInputError::Argument {
            index: 0, argument, expected: ResolvedPortType::Bits(1), required_at: None,
            reason: CallInputReason::SignalType(actual),
        },
    } = error else { panic!("expected a nested output type mismatch: {error:?}"); };
    assert_eq!((position.definition, position.reference), (0, 0));
    assert_eq!(&caller[argument.span], "(::lib::Wide)");
    assert_eq!(argument.source.revision, 4);
    assert!(matches!(actual.ty, ResolvedPortType::Bits(8)));
    assert_eq!(&library[actual.origin.span], "8");
    assert_eq!(actual.origin.source.revision, 9);
}

#[test]
fn reports_a_nested_signature_error_at_the_child_reference() {
    let text = concat!(
        "(func f (in) (out y) (def y (nor (child) 0))) ",
        "(func child (in) (out (y Missing)) (def y 0))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 2, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let outer = aliases.check_func_call_inputs(0, 0, 0, 0, 8).unwrap().unwrap();
    assert!(outer.inputs[0].is_none());
    let error = aliases.check_all_func_call_inputs(0, 0, 8).unwrap_err();
    let FuncCallInputsError::Call {
        position,
        error: CallInputError::Signature(
            circuitgame2_core::project::FuncCallSignatureError::Signature { call, .. },
        ),
    } = error else { panic!("expected the child's signature diagnostic: {error:?}"); };
    assert_eq!(position.reference, 1);
    assert_eq!(&text[call.call.span], "(child)");
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

#[test]
fn checks_all_definitions_and_visits_calls_after_type_references() {
    let text = concat!(
        "(struct T (width 1)) ",
        "(func f (in a) (out y) (def x (nor a a)) (def y (as T (nor x #x02)))) ",
        "(func g (in a) (out y) (def x (nor a a)) (def y (as T (nor x #x01))))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 20, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let error = aliases.check_all_func_call_inputs(0, 1, 8).unwrap_err();
    let FuncCallInputsError::Call {
        position, error: CallInputError::Argument { index: 1, argument, .. },
    } = error else { panic!("expected an argument error after the type reference: {error:?}"); };
    assert_eq!((position.file, position.entry, position.definition, position.reference), (0, 1, 1, 1));
    assert_eq!(&text[argument.span], "#x02");
    assert_eq!(argument.source.revision, 20);
    let accepted = aliases.check_all_func_call_inputs(0, 2, 8).unwrap();
    assert!(matches!(accepted.literals.wiring, FuncWiringResult::Checked(_)));
}

#[test]
fn checks_the_outer_call_before_the_inner_call() {
    let text = "(func f (in a (b (bits 8))) (out y) (def y (nor (nor a #x02) b)))";
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 1, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    assert!(matches!(aliases.check_func_call_inputs(0, 0, 0, 1, 8),
        Err(CallInputError::Argument { index: 1, reason: CallInputReason::LiteralWidth(_), .. })));
    let error = aliases.check_all_func_call_inputs(0, 0, 8).unwrap_err();
    let FuncCallInputsError::Call {
        position, error: CallInputError::Argument { index: 1, argument, reason: CallInputReason::SignalType(_), .. },
    } = error else { panic!("expected the outer call's argument error: {error:?}"); };
    assert_eq!(position.reference, 0);
    assert_eq!(&text[argument.span], "b");
}

#[test]
fn retains_expansion_and_caller_diagnostic_priority() {
    let text = concat!(
        "(struct T (width 1)) ",
        "(func waiting (in) (out y) (expand gen)) ",
        "(func invalid (in a) (out y) (def y (nor a #x02)) (def x missing)) ",
        "(func empty (in a) (out a))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 1, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let not_func = aliases.check_all_func_call_inputs(0, 0, 8).unwrap();
    assert!(matches!(not_func.literals.wiring, FuncWiringResult::NotFunc));
    let waiting = aliases.check_all_func_call_inputs(0, 1, 8).unwrap();
    let FuncWiringResult::NeedsExpansion(site) = waiting.literals.wiring else {
        panic!("expected an expansion site");
    };
    assert_eq!(&text[site.span], "(expand gen)");
    assert!(matches!(aliases.check_all_func_call_inputs(0, 2, 8), Err(FuncCallInputsError::Caller(_))));
    let empty = aliases.check_all_func_call_inputs(0, 3, 8).unwrap();
    assert!(matches!(empty.literals.wiring, FuncWiringResult::Checked(_)));
}
