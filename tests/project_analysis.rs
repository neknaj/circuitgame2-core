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
fn reachable_function_expansion_ignores_unrelated_bodies() {
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "caller.ncg2", revision: 10,
            text: "(func caller (in x) (out y) (def y (nor (::leaf x) x)))" },
        SourceSnapshot { path: "library.ncg2", revision: 20,
            text: "(using nor) (func leaf (in x) (out x))" },
        SourceSnapshot { path: "unrelated.ncg2", revision: 30,
            text: "(func broken (in x) (out y) (def y (::missing x)))
                   (func recursive (in x) (out y) (def y (::recursive x)))" },
    ]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();

    let scoped = aliases.prepare_reachable_function_expansion((0, 0)).unwrap().unwrap();
    assert_eq!(scoped.len(), 2);
    assert_eq!(scoped.get(0), Some((1, 1)));
    assert_eq!(scoped.get(1), Some((0, 0)));
    assert!(matches!(aliases.prepare_function_expansion(), Err(FunctionExpansionError::Reference(_))));

    let circuit = aliases.expand_reachable_function((0, 0), 8, 16, 1).unwrap().unwrap();
    assert_eq!(circuit.netlist().gates.len(), 1);
    assert_eq!(circuit.netlist().evaluate(&[false]).unwrap(), [true]);
    assert_eq!(circuit.netlist().evaluate(&[true]).unwrap(), [false]);
    assert!(aliases.expand_reachable_function((1, 0), 8, 16, 1).unwrap().is_none());

    let FunctionExpansionError::Cycle(cycle) = aliases.prepare_reachable_function_expansion((2, 1)).unwrap_err()
        else { panic!("reachable recursion must be diagnosed"); };
    assert_eq!(cycle.len(), 1);
    assert_eq!(&cycle[0].location.source.text[cycle[0].location.span.clone()], "::recursive");
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

#[test]
fn expands_functions_and_reports_the_call_that_exceeds_the_gate_limit() {
    use circuitgame2_core::project::{ExpandFunctionsError, FunctionBuildDiagnostic};

    let project = parse_circuit_project(&[SourceSnapshot {
        path: "calls.ncg2",
        revision: 7,
        text: "(using nor)
               (func twice (in a) (out y) (def t (inv a)) (def y (inv t)))
               (func inv (in a) (out y) (def y (nor a a)))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();

    let functions = aliases.expand_functions(8, 16, 2).unwrap();
    assert!(core::ptr::eq(functions.project(), &project));
    assert!(functions.get(0, 0).is_none());
    assert!(functions.get(0, usize::MAX).is_none());
    assert!(functions.get(usize::MAX, 1).is_none());
    assert_eq!(functions.get(0, 1).unwrap().netlist().evaluate(&[true]).unwrap(), [true]);

    let Err(ExpandFunctionsError::Function {
        position: (0, 1),
        diagnostic: FunctionBuildDiagnostic::CallGateCapacity(site),
    }) = aliases.expand_functions(8, 16, 1) else {
        panic!("expected the second invocation in twice to exceed the gate limit");
    };
    assert_eq!(site.source.revision, 7);
    assert_eq!(&site.source.text[site.span], "(inv t)");
}

#[test]
fn expands_a_cross_file_call_with_struct_ports_and_multiple_outputs() {
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "main.ncg2",
            revision: 1,
            text: "(using nor)
                   (func run (in (a (bits 8))) (out (copy (bits 8)) (picked (bits 2)))
                     (def word (as ::lib::Word a))
                     (def (keep picked) (::lib::split word))
                     (def copy (raw keep)))",
        },
        SourceSnapshot {
            path: "lib.ncg2",
            revision: 2,
            text: "(namespace lib
                     (export Word split)
                     (struct Word (width 8) (payload (bits 4) (at 2)))
                     (func split (in (w Word)) (out (w Word) (picked (bits 2)))
                       (def picked (slice (field w payload) 0 2 2))))",
        },
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let functions = aliases.expand_functions(8, 32, 0).unwrap();
    let circuit = functions.get(0, 1).unwrap();
    for bit in 0..8 {
        let input: [bool; 8] = core::array::from_fn(|index| index == bit);
        let output = circuit.netlist().evaluate(&input).unwrap();

        assert_eq!(output.len(), 10);
        assert_eq!(output[..8], input);
        assert_eq!(output[8..], [input[2], input[4]]);
    }
}

#[test]
fn expands_nested_calls_with_struct_values_and_no_gates() {
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "nested.ncg2",
        revision: 8,
        text: "(using nor)
               (struct Word (width 2) (payload (bits 1) (at 0)))
               (func run (in (a (bits 2))) (out (y (bits 2)))
                 (def y (id (unpack (pack a)))))
               (func id (in (a (bits 2))) (out (a (bits 2))))
               (func pack (in (a (bits 2))) (out (w Word)) (def w (as Word a)))
               (func unpack (in (w Word)) (out (a (bits 2))) (def a (raw w)))",
    }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let functions = aliases.expand_functions(2, 2, 0).unwrap();
    let circuit = functions.get(0, 2).unwrap();
    assert!(circuit.gate_definitions().is_empty());
    assert_eq!(circuit.netlist().evaluate(&[false, true]).unwrap(), [false, true]);
}

#[test]
fn locates_nested_gate_capacity_at_the_call_that_fails() {
    use circuitgame2_core::project::{ExpandFunctionsError, FunctionBuildDiagnostic};

    let cases = [
        (
            "(using nor) (func id (in a) (out a))
             (func run (in a) (out y) (def y (id (nor a a))))",
            0, "(nor a a)",
        ),
        (
            "(using nor) (func inv (in a) (out y) (def y (nor a a)))
             (func run (in a) (out y) (def y (inv (nor a a))))",
            1, "(inv (nor a a))",
        ),
        (
            "(using nor) (func id (in a) (out a))
             (func run (in a) (out y) (def y (nor (id a) (nor a a))))",
            0, "(nor a a)",
        ),
        (
            "(using nor) (func id (in a) (out a))
             (func run (in a) (out y) (def y (nor (id a) (nor a a))))",
            1, "(nor (id a) (nor a a))",
        ),
    ];
    for (text, limit, expression) in cases {
        let project = parse_circuit_project(&[SourceSnapshot {
            path: "nested.ncg2",
            revision: 8,
            text,
        }]).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let aliases = check_use_aliases(&targets).unwrap();
        let Err(ExpandFunctionsError::Function {
            position: (0, 2),
            diagnostic: FunctionBuildDiagnostic::CallGateCapacity(site),
        }) = aliases.expand_functions(1, 1, limit) else {
            panic!("expected the nested call to exceed the gate limit");
        };
        assert_eq!(site.source.revision, 8);
        assert_eq!(&text[site.span], expression);
    }
}
