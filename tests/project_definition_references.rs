use circuitgame2_core::project::{
    DefinitionBinding, DefinitionLookupObservation, DefinitionReferenceError, DefinitionReferenceReason,
    OwnedUnqualifiedLookup, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project,
};
use circuitgame2_core::syntax::circuit::Head;

#[test]
fn resolves_real_references_and_keeps_diagnostic_ranges() {
    let app = concat!(
        "; 参照元の UTF-8 範囲を確認する\n",
        "(using nor) ",
        "(namespace app ",
        "  (use ::lib gates) (use ::lib::Work invoke) ",
        "  (module Main (in signal) (out y) ",
        "    (def y (as gates::T (invoke signal))) ",
        "    (def n (nor signal signal)) ",
        "    (def p (gates::Secret signal)) ",
        "    (def q (::lib::Secret signal)))) ",
        "(namespace app (module-part Main (def missing (invoke signal))))",
    );
    let library = concat!(
        "(namespace lib (export Work T M) ",
        "  (func Work (in x) (out x)) (func Secret (in x) (out x)) ",
        "  (struct T (width 1)) (module M (in x) (out x)) ",
        "  (func UsesPrivate (in x) (out y) (def y (::lib::Secret x))) ",
        "  (func WrongStage (in x) (out y) (def y (M x))))",
    );
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "app.ncg2",
            revision: 9,
            text: app,
        },
        SourceSnapshot {
            path: "lib.ncg2",
            revision: 2,
            text: library,
        },
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let app_entries = &project.circuits()[0].syntax.entries;
    let main = app_entries
        .iter()
        .position(|item| item.head == Head::Module)
        .unwrap();
    let part = app_entries
        .iter()
        .position(|item| item.head == Head::ModulePart)
        .unwrap();
    for (reference, expected) in [(0, "T"), (1, "Work")] {
        let value = aliases
            .resolve_definition_reference(0, main, 0, reference)
            .unwrap();
        assert!(
            matches!(value.binding, DefinitionBinding::Declaration { form, .. } if form.name.word == expected)
        );
        assert_eq!(value.site.source.revision, 9);
    }
    let builtin = aliases.resolve_definition_reference(0, main, 1, 0).unwrap();
    assert!(matches!(builtin.binding, DefinitionBinding::Nor));
    let (observed_builtin, builtin_observation) = aliases.observe_definition_reference(0, main, 1, 0);
    assert!(matches!(observed_builtin.unwrap().binding, DefinitionBinding::Nor));
    assert_eq!(builtin_observation, Some(DefinitionLookupObservation::Unqualified(OwnedUnqualifiedLookup::Missing)));
    for (definition, spelling) in [(2, "gates::Secret"), (3, "::lib::Secret")] {
        let error = aliases
            .resolve_definition_reference(0, main, definition, 0)
            .unwrap_err();
        let DefinitionReferenceError::Rejected {
            site,
            reason: DefinitionReferenceReason::Private(location),
        } = error
        else {
            panic!("expected a private target");
        };
        assert_eq!(&app[site.name.span], spelling);
        assert_eq!(&library[location.span], "Secret");
        assert_eq!(location.source.revision, 2);
    }
    let (reference, observation) = aliases.observe_definition_reference(0, main, 3, 0);
    let Err(DefinitionReferenceError::Rejected { site, reason: DefinitionReferenceReason::Private(location) }) = reference
        else { panic!("完全修飾名の診断には非公開の宣言位置が必要"); };
    assert_eq!(&app[site.name.span], "::lib::Secret");
    assert_eq!(&library[location.span], "Secret");
    assert!(matches!(observation, Some(DefinitionLookupObservation::Absolute(found)) if !found.visible_declaration));
    let (relative, observation) = aliases.observe_definition_reference(0, main, 2, 0);
    assert!(matches!(relative, Err(DefinitionReferenceError::Rejected { reason: DefinitionReferenceReason::Private(_), .. })));
    assert!(observation.is_none());
    assert!(matches!(
        aliases.resolve_definition_reference(0, part, 0, 0),
        Err(DefinitionReferenceError::Rejected {
            reason: DefinitionReferenceReason::Missing,
            ..
        })
    ));
    let owner = &project.circuits()[1];
    let inside = owner
        .syntax
        .entries
        .iter()
        .rposition(|item| item.head == Head::Func)
        .unwrap()
        - 1;
    assert!(matches!(
        aliases.resolve_definition_reference(1, inside, 0, 0).unwrap().binding,
        DefinitionBinding::Declaration { form, .. } if form.name.word == "Secret"
    ));
    assert!(matches!(
        aliases.resolve_definition_reference(1, inside + 1, 0, 0),
        Err(DefinitionReferenceError::Rejected { reason: DefinitionReferenceReason::WrongDeclaration { form, .. }, .. })
            if form.head == Head::Module
    ));
    for (entry, definition, reference) in [
        (usize::MAX, 0, 0),
        (main, usize::MAX, 0),
        (main, 0, usize::MAX),
    ] {
        assert!(matches!(
            aliases.resolve_definition_reference(0, entry, definition, reference),
            Err(DefinitionReferenceError::UnknownPosition)
        ));
    }
}

#[test]
fn a_wrong_kind_with_the_builtin_spelling_still_resolves_to_that_binding() {
    let text =
        "(struct nor (width 1)) (func f (in x) (out y) (def y (nor x x)) (def y (as nor x)))";
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "main.ncg2",
        revision: 1,
        text,
    }])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    assert!(matches!(
        aliases.resolve_definition_reference(0, 1, 0, 0),
        Err(DefinitionReferenceError::Rejected { reason: DefinitionReferenceReason::WrongDeclaration { form, .. }, .. })
            if form.head == Head::Struct
    ));
    assert!(matches!(
        aliases.resolve_definition_reference(0, 1, 1, 0).unwrap().binding,
        DefinitionBinding::Declaration { form, .. } if form.head == Head::Struct
    ));
}
