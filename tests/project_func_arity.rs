use circuitgame2_core::project::{
    DefinitionReferenceError, DefinitionReferenceReason, FuncArityError, FuncCallTarget,
    FuncSignalReason, FuncWiringError, FuncWiringResult, SourceSnapshot, check_use_aliases,
    index_use_targets, parse_circuit_project,
};

fn snapshot(text: &str) -> [SourceSnapshot<'_>; 1] {
    [SourceSnapshot {
        path: "./lib/../main.ncg2",
        revision: 19,
        text,
    }]
}

#[test]
fn matches_multiple_outputs_only_at_the_definition_root() {
    let text = concat!(
        "; 日本語のコメント\n",
        "(func good (in a b) (out x y) (def (x y) (pair a b))) ",
        "(func root (in a b) (out y) (def y (pair a b))) ",
        "(func nested (in a b) (out y) (def y (nor (pair a b) b))) ",
        "(func special (in a b) (out y) (def y (raw (pair a b)))) ",
        "(func pair (in a b) (out a b))",
    );
    let project = parse_circuit_project(&snapshot(text)).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    assert!(matches!(
        aliases.check_func_arity(0, 0, 1).unwrap(),
        FuncWiringResult::Checked(_)
    ));
    for entry in [1, 2, 3] {
        let result = aliases.check_func_arity(0, entry, 1).unwrap_err();
        let FuncArityError::OutputCount {
            expression,
            left,
            callee: Some(FuncCallTarget::Function { declaration, .. }),
            expected,
            actual,
        } = result else {
            panic!("expected an output count diagnostic: {result:?}");
        };
        assert_eq!((expected, actual), (1, 2));
        assert_eq!(&text[expression.span], "(pair a b)");
        assert_eq!(expression.source.id.components(), ["main.ncg2"]);
        assert_eq!(expression.source.revision, 19);
        assert_eq!(&text[declaration.span], "pair");
        assert_eq!(declaration.source.revision, 19);
        assert_eq!(left.map(|site| &text[site.span]), (entry == 1).then_some("y"));
    }
}

#[test]
fn reports_the_first_violation_in_definition_and_call_order() {
    let text = concat!(
        "(func first (in a) (out y) (def p a) (def y (nor (unknown p)))) ",
        "(func both (in a) (out x y) (def (x y) (nor a))) ",
        "(func excess (in a) (out y) (def y (nor a a a))) ",
        "(func root (in a) (out x y) (def (x y) (raw (unknown a)))) ",
        "(func missing (in a) (out y) (def y (unknown a))) ",
        "(func cast (in a) (out y) (def y (as Later a))) ",
        "(func fewer (in a) (out x y) (def (x y) (nor a a)))",
    );
    let project = parse_circuit_project(&snapshot(text)).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    for (entry, count, spelling) in [
        (0, 1, "(nor (unknown p))"),
        (1, 1, "(nor a)"),
        (2, 3, "(nor a a a)"),
    ] {
        let error = aliases.check_func_arity(0, entry, 1).unwrap_err();
        let FuncArityError::ArgumentCount { call, target: FuncCallTarget::Nor, expected, actual } = error else {
            panic!("expected a NOR input count diagnostic: {error:?}");
        };
        assert_eq!((expected, actual), (2, count));
        assert_eq!(&text[call.span], spelling);
    }
    let root = aliases.check_func_arity(0, 3, 1).unwrap_err();
    let FuncArityError::OutputCount { expression, left: Some(left), callee: None, expected: 2, actual: 1 } = root else {
        panic!("expected leaf or special-form output count: {root:?}");
    };
    assert_eq!(&text[expression.span], "(raw (unknown a))");
    assert_eq!(&text[left.span], "(x y)");
    let missing = aliases.check_func_arity(0, 4, 1).unwrap_err();
    let FuncArityError::Reference(DefinitionReferenceError::Rejected {
        site,
        reason: DefinitionReferenceReason::Missing,
    }) = missing else {
        panic!("expected the existing name diagnostic: {missing:?}");
    };
    assert_eq!(&text[site.name.span], "unknown");
    assert!(matches!(
        aliases.check_func_arity(0, 5, 1).unwrap(),
        FuncWiringResult::Checked(_)
    ));
    let fewer = aliases.check_func_arity(0, 6, 1).unwrap_err();
    let FuncArityError::OutputCount {
        expression, left: Some(left), callee: Some(FuncCallTarget::Nor), expected: 2, actual: 1,
    } = fewer else {
        panic!("expected a NOR output count diagnostic: {fewer:?}");
    };
    assert_eq!(&text[expression.span], "(nor a a)");
    assert_eq!(&text[left.span], "(x y)");
}

#[test]
fn keeps_wiring_diagnostics_and_expansion_ahead_of_count_checks() {
    let text = concat!(
        "(func bad (in a) (out y) (def y (nor missing))) ",
        "(func waiting (in a) (out y) (def y (nor a)) (expand make)) ",
        "(func direct (in a) (out a)) ",
        "(module m (in a) (out y) (def y (nor a)))",
    );
    let project = parse_circuit_project(&snapshot(text)).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    assert!(matches!(
        aliases.check_func_arity(0, 0, 1),
        Err(FuncArityError::Wiring(FuncWiringError::Signal { reason: FuncSignalReason::Undefined, .. }))
    ));
    let FuncWiringResult::NeedsExpansion(site) = aliases.check_func_arity(0, 1, 1).unwrap() else {
        panic!("expected pending expansion");
    };
    assert_eq!(&text[site.span], "(expand make)");
    assert!(matches!(aliases.check_func_arity(0, 2, 1).unwrap(), FuncWiringResult::Checked(_)));
    assert!(matches!(aliases.check_func_arity(0, 3, 1).unwrap(), FuncWiringResult::NotFunc));
}
