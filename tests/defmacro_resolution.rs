use circuitgame2_core::project::{
    DefmacroNameError, MixedFuncCalleeError, ProjectDeclarationKind, ProjectSourceIndex,
    SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources,
};
use circuitgame2_core::syntax::circuit::Head;

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
            (func target (in x) (out y) (expand make y x))
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
