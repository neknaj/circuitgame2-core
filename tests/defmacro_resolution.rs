use circuitgame2_core::project::{
    DefmacroNameError, MacroCallError, MixedFuncCalleeError, ProjectDeclarationKind, ProjectSourceIndex,
    SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources,
};
use circuitgame2_core::syntax::circuit::{Head, next_call_argument};

#[test]
fn resolves_macros_from_the_block_of_each_circuit_body() {
    let declarations = "; マクロ定義\n(namespace lib
        (export emit helper)
        (defmacro emit (out source) (list (syntax (def (unsyntax out) (unsyntax source)))))
        (defmacro hidden () (list))
        (defn helper (as-type (Fn () Bool) (fn () true))))";
    let circuit = "(using nor)
        (namespace app
            (use ::lib::emit make)
            (use ::lib lib)
            (func target (in x) (out y)
                (expand make y (expand ignored x))
                (expand make y)
                (expand lib::helper)
                (expand make y x))
            (module top (in x) (out y) (expand lib::emit y x)))
        (namespace app (module-part top (expand make y x)))
        (namespace lib (module private-caller (in) (out y) (expand hidden)))";
    let inputs = [
        SourceSnapshot {
            path: "macros.ncg2m",
            revision: 31,
            text: declarations,
        },
        SourceSnapshot {
            path: "main.ncg2",
            revision: 47,
            text: circuit,
        },
    ];
    let project = parse_project_sources(&inputs).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let ProjectSourceIndex::Circuit(parsed) = &project.indexes()[1] else {
        panic!();
    };
    let entries = &parsed.syntax.entries;
    let function = entries
        .iter()
        .position(|entry| entry.head == Head::Func)
        .unwrap();
    let module = entries
        .iter()
        .position(|entry| entry.head == Head::Module)
        .unwrap();
    let part = entries
        .iter()
        .position(|entry| entry.head == Head::ModulePart)
        .unwrap();
    let inside = entries
        .iter()
        .rposition(|entry| entry.head == Head::Module)
        .unwrap();
    for (caller, name) in [
        (function, "make"),
        (module, "lib::emit"),
        (part, "::lib::emit"),
    ] {
        let found = aliases.resolve_defmacro_name(1, caller, name).unwrap();
        assert_eq!(found.declaration.kind, ProjectDeclarationKind::Defmacro);
        assert_eq!(found.declaration.file, 0);
        assert_eq!(found.declaration.name.source.revision, 31);
        assert_eq!(&declarations[found.declaration.name.span], "emit");
        assert_eq!(&declarations[found.parameters[0].clone()], "out");
        assert_eq!(&declarations[found.parameters[1].clone()], "source");
        assert_eq!(
            &declarations[found.body.clone()],
            "(list (syntax (def (unsyntax out) (unsyntax source))))"
        );
    }
    let mut calls = aliases.macro_calls(1, function).unwrap();
    assert_eq!(calls.source().revision, 47);
    let syntax = calls.syntax();
    let first = calls.next_call().unwrap();
    assert_eq!(&circuit[first.site.callee], "make");
    assert_eq!(first.target.unwrap().declaration.name.source.revision, 31);
    let first_argument = next_call_argument(&syntax.forms, first.site.arguments.clone()).unwrap();
    let second_argument =
        next_call_argument(&syntax.forms, first_argument.end..first.site.arguments.end).unwrap();
    assert_eq!(second_argument.end, first.site.arguments.end);
    assert!(second_argument.end - second_argument.start > 1);
    let too_few = calls.next_call().unwrap();
    assert_eq!(&circuit[too_few.site.span], "(expand make y)");
    assert!(matches!(too_few.target, Err(MacroCallError::Arity { actual: 1, .. })));
    let wrong_kind = calls.next_call().unwrap();
    assert_eq!(&circuit[wrong_kind.site.callee], "lib::helper");
    assert!(matches!(
        wrong_kind.target,
        Err(MacroCallError::Name(DefmacroNameError::Reference(MixedFuncCalleeError::WrongDeclaration(_))))
    ));
    assert!(calls.next_call().unwrap().target.is_ok());
    assert!(calls.next_call().is_none());
    assert!(aliases.macro_calls(1, 0).is_none());

    assert!(matches!(
        aliases.resolve_defmacro_name(1, part, "make"),
        Err(DefmacroNameError::Reference(MixedFuncCalleeError::Missing)),
    ));
    let Err(DefmacroNameError::Reference(MixedFuncCalleeError::Private(location))) =
        aliases.resolve_defmacro_name(1, function, "lib::hidden")
    else {
        panic!()
    };
    assert_eq!(&declarations[location.span], "hidden");
    assert!(aliases.resolve_defmacro_name(1, inside, "hidden").is_ok());

    for (name, original, kind, source) in [
        (
            "lib::helper",
            "helper",
            ProjectDeclarationKind::Defn,
            declarations,
        ),
        (
            "target",
            "target",
            ProjectDeclarationKind::Circuit(Head::Func),
            circuit,
        ),
    ] {
        let Err(DefmacroNameError::Reference(MixedFuncCalleeError::WrongDeclaration(declaration))) =
            aliases.resolve_defmacro_name(1, function, name)
        else {
            panic!()
        };
        assert_eq!(declaration.kind, kind);
        assert_eq!(&source[declaration.name.span], original);
    }
    assert!(matches!(
        aliases.resolve_defmacro_name(1, 0, "make"),
        Err(DefmacroNameError::Caller)
    ));
    assert!(matches!(
        aliases.resolve_defmacro_name(1, module, "42"),
        Err(DefmacroNameError::InvalidName)
    ));
}
