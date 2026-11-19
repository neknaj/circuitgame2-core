use circuitgame2_core::project::{
    DefinitionReferenceError, DefinitionReferenceReason, FuncCallTarget, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project,
};
use circuitgame2_core::syntax::circuit::{Head, RoutineArity};

#[test]
fn projects_the_signature_selected_by_aliases_and_qualified_names() {
    let caller = concat!(
        "; 呼び出し元\n",
        "(namespace app ",
        "  (use ::lib gates) (use ::lib::Work invoke) ",
        "  (func Main (in x) (out y) ",
        "    (def y (invoke (nor x x))) ",
        "    (def a (gates::Work x)) ",
        "    (def b (::lib::Work x)) ",
        "    (def c (Local x)) ",
        "    (def d (gates::Hidden x)) ",
        "    (def e (as gates::Word x))) ",
        "  (func Local (in a) (out a)))",
    );
    let library = concat!(
        "; 宣言\n",
        "(namespace lib (export Work Word) ",
        "  (struct Word (width 1)) ",
        "  (func Hidden (in a) (out a)) ",
        "  (func Work (in a b) (out a b)))",
    );
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "./app.ncg2", revision: 9, text: caller },
        SourceSnapshot { path: "app.ncg2", revision: 9, text: caller },
        SourceSnapshot { path: "./lib.ncg2", revision: 17, text: library },
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let main = project.circuits()[0]
        .syntax.entries.iter().position(|entry| entry.head == Head::Func).unwrap();
    let work = project.circuits()[1]
        .syntax.entries.iter().rposition(|entry| entry.head == Head::Func).unwrap();
    for (def, spelling) in [
        (0, "(invoke (nor x x))"),
        (1, "(gates::Work x)"),
        (2, "(::lib::Work x)"),
    ] {
        let result = aliases.resolve_func_call_arity(0, main, def, 0).unwrap().unwrap();
        assert_eq!(result.source.id.components(), ["app.ncg2"]);
        assert_eq!(result.source.revision, 9);
        assert_eq!(&caller[result.call.span], spelling);
        assert_eq!(result.call.arguments, 1);
        assert_eq!(result.target.ports(), RoutineArity { inputs: 2, outputs: 2 });
        let FuncCallTarget::Function { file, entry, declaration, .. } = result.target else {
            panic!("expected the exported function");
        };
        assert_eq!((file, entry), (1, work));
        assert_eq!(&library[declaration.span], "Work");
        assert_eq!(declaration.source.revision, 17);
    }
    let builtin = aliases.resolve_func_call_arity(0, main, 0, 1).unwrap().unwrap();
    assert!(matches!(builtin.target, FuncCallTarget::Nor));
    assert_eq!(&caller[builtin.call.span], "(nor x x)");
    assert_eq!(builtin.target.ports(), RoutineArity { inputs: 2, outputs: 1 });
    let local = aliases.resolve_func_call_arity(0, main, 3, 0).unwrap().unwrap();
    assert!(matches!(local.target, FuncCallTarget::Function { file: 0, entry, .. } if entry > main));
    let error = aliases.resolve_func_call_arity(0, main, 4, 0).unwrap_err();
    let DefinitionReferenceError::Rejected { site, reason: DefinitionReferenceReason::Private(related) } = error else {
        panic!("expected a private declaration");
    };
    assert_eq!(&caller[site.name.span], "gates::Hidden");
    assert_eq!(&library[related.span], "Hidden");
    assert!(aliases.resolve_func_call_arity(0, main, 5, 0).unwrap().is_none());
    assert!(aliases.resolve_func_call_arity(0, main, 6, 0).unwrap().is_none());
    assert!(aliases.resolve_func_call_arity(0, main, 0, 2).unwrap().is_none());
}

#[test]
fn user_function_named_nor_has_its_own_signature() {
    let text = concat!(
        "(func f (in a) (out y) (def y (nor a))) ",
        "(func nor (in a) (out a)) ",
        "(module m (in a) (out y) (def y (nor a)))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 1, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let result = aliases.resolve_func_call_arity(0, 0, 0, 0).unwrap().unwrap();
    assert_eq!(result.target.ports(), RoutineArity { inputs: 1, outputs: 1 });
    assert!(matches!(result.target, FuncCallTarget::Function { file: 0, entry: 1, .. }));
    assert!(aliases.resolve_func_call_arity(0, 2, 0, 0).unwrap().is_none());
}
