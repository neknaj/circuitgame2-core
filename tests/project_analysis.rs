use circuitgame2_core::project::{
    AliasConflict, AliasDisposition, CircuitBasisError, DefinitionAnalysisError, DefinitionBinding,
    DefinitionReferenceReason, FunctionExpansionError, SourceSnapshot, UseTargetError,
    analyze_definitions, check_use_aliases, index_use_targets, parse_circuit_project,
};

#[test]
fn prepares_nested_func_calls_in_dependency_order() {
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "caller.ncg2",
            revision: 10,
            text: "(func caller (in x) (out y) (def y (nor (::leaf x) x)))",
        },
        SourceSnapshot {
            path: "library.ncg2",
            revision: 20,
            text: "(using nor) (func leaf (in x) (out x))",
        },
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let plan = aliases.prepare_function_expansion().unwrap();
    assert!(core::ptr::eq(plan.project(), &project));
    assert_eq!(plan.len(), 2);
    let (callee, _) = plan.get(0).unwrap();
    let (caller, _) = plan.get(1).unwrap();
    assert_eq!(plan.project().sources()[callee].revision, 20);
    assert_eq!(plan.project().sources()[caller].revision, 10);
    assert_eq!(plan.get(plan.len()), None);
}

#[test]
fn expansion_cycle_diagnostic_uses_the_nested_callee_name() {
    let caller = "; 呼び出し元\n(func caller (in x) (out y) (def y (nor (::callee x) x)))";
    let callee = "(using nor) (func callee (in x) (out y) (def y (::caller x)))";
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "caller.ncg2", revision: 10, text: caller },
        SourceSnapshot { path: "library.ncg2", revision: 20, text: callee },
    ])
    .unwrap();
    assert!(analyze_definitions(&project).is_ok());
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let FunctionExpansionError::Cycle(cycle) = aliases.prepare_function_expansion().unwrap_err()
    else {
        panic!("expected a recursive call diagnostic");
    };
    let nested = cycle.iter().find(|site| site.location.source.revision == 10).unwrap();
    assert_eq!(&caller[nested.location.span.clone()], "::callee");
    assert_eq!(nested.position.reference, 1);
    let back = cycle.iter().find(|site| site.location.source.revision == 20).unwrap();
    assert_eq!(&callee[back.location.span.clone()], "::caller");
}

#[test]
fn analyzes_all_definition_references_and_retains_alias_warnings() {
    let caller = concat!(
        "(use ::primitive gate) (use ::primitive gate) ",
        "(module M (in x) (out y) (def tmp x) ",
        "  (def y (gate (nor x x))))"
    );
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "caller.ncg2",
            revision: 1,
            text: caller,
        },
        SourceSnapshot {
            path: "library.ncg2",
            revision: 2,
            text: "(using nor) (func primitive (in x) (out y) (def y (nor x x)))",
        },
    ])
    .unwrap();
    let analysis = analyze_definitions(&project).unwrap();
    assert_eq!(analysis.basis.unwrap().source.revision, 2);
    assert_eq!(
        analysis.aliases.dispositions,
        [
            AliasDisposition::Binding,
            AliasDisposition::Duplicate { first: 0 }
        ]
    );
    let references = analysis.definitions;
    assert_eq!(references.len(), 3);
    assert_eq!(references[0].position.file, 0);
    assert_eq!(references[0].position.definition, 1);
    assert_eq!(references[0].resolved.site.name.word, "gate");
    assert!(matches!(
        references[0].resolved.binding,
        DefinitionBinding::Declaration { form, .. } if form.name.word == "primitive"
    ));
    assert_eq!(references[1].position.reference, 1);
    assert_eq!(references[2].position.file, 1);
    assert!(matches!(
        references[1].resolved.binding,
        DefinitionBinding::Nor
    ));
    assert!(matches!(
        references[2].resolved.binding,
        DefinitionBinding::Nor
    ));
}

#[test]
fn retains_confirmed_alias_warnings_with_the_first_definition_error() {
    let first = concat!(
        "; 元のバイト範囲\n",
        "(using nor) (func target (in x) (out x)) ",
        "(use ::target a) (use ::target a) ",
        "(func caller (in x) (out y) (def y (a (bad x))) (def y (later x)))"
    );
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "z.ncg2",
            revision: 8,
            text: first,
        },
        SourceSnapshot {
            path: "a.ncg2",
            revision: 2,
            text: "(func other (in x) (out y) (def y (also-bad x)))",
        },
    ])
    .unwrap();
    let DefinitionAnalysisError::Definition { error, aliases } =
        analyze_definitions(&project).unwrap_err()
    else {
        panic!("expected the first invalid reference");
    };
    assert_eq!(error.position.file, 0);
    assert_eq!(error.position.reference, 1);
    assert_eq!(&first[error.site.name.span], "bad");
    assert!(matches!(error.reason, DefinitionReferenceReason::Missing));
    assert_eq!(
        aliases.dispositions[1],
        AliasDisposition::Duplicate { first: 0 }
    );
    assert_eq!(aliases.targets.directives()[0].site.source.revision, 8);
}

#[test]
fn checks_project_prerequisites_before_definition_references() {
    fn parse(text: &str) -> circuitgame2_core::project::CircuitProject<'_> {
        parse_circuit_project(&[SourceSnapshot {
            path: "main.ncg2",
            revision: 1,
            text,
        }])
        .unwrap()
    }

    let missing_basis = parse("(use ::missing x) (func f (in x) (out y) (def y (bad x)))");
    assert!(matches!(
        analyze_definitions(&missing_basis),
        Err(DefinitionAnalysisError::Basis(CircuitBasisError::Missing))
    ));
    let missing_target =
        parse("(using nor) (use ::missing x) (func f (in x) (out y) (def y (bad x)))");
    assert!(matches!(
        analyze_definitions(&missing_target),
        Err(DefinitionAnalysisError::UseTarget(UseTargetError::Missing(
            _
        )))
    ));
    let conflicting_uses = parse(concat!(
        "(using nor) (namespace lib) (namespace other) ",
        "(use ::lib x) (use ::other x) (func f (in x) (out y) (def y (bad x)))"
    ));
    let DefinitionAnalysisError::Alias(AliasConflict::BetweenUses { first, later }) =
        analyze_definitions(&conflicting_uses).unwrap_err()
    else {
        panic!("expected alias collision before definition resolution");
    };
    assert_eq!(first.site.reference.word, "::lib");
    assert_eq!(later.site.reference.word, "::other");
}
