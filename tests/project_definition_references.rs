use circuitgame2_core::project::{
    DefinitionBinding, DefinitionLookupObservation, DefinitionPosition, DefinitionPositionStep, DefinitionReferenceError, DefinitionReferenceReason,
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
    for definition in [1, 2] {
        let at = DefinitionPosition { file: 0, entry: main, definition, reference: 0 };
        assert!(aliases.cache_absolute_reference_diagnostic(at).is_none());
    }
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

#[test]
fn reuses_a_cached_absolute_diagnostic_only_while_its_evidence_agrees() {
    fn with_project<T>(
        library: &str, revision: u64,
        check: impl FnOnce(&circuitgame2_core::project::UseAliases<'_, '_, '_>, DefinitionPosition) -> T,
    ) -> T {
        let app = "(using nor) (func Run (in x) (out y) (def y (::lib::Task x)))";
        let project = parse_circuit_project(&[
            SourceSnapshot { path: "app.ncg2", revision: 8, text: app },
            SourceSnapshot { path: "lib.ncg2", revision, text: library },
        ]).unwrap();
        let entry = project.circuits()[0].syntax.entries.iter().position(|row| row.head == Head::Func).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let aliases = check_use_aliases(&targets).unwrap();
        check(&aliases, DefinitionPosition { file: 0, entry, definition: 0, reference: 0 })
    }

    use circuitgame2_core::project::ReferenceDiagnosticKind;
    let private = "(namespace lib (func Task (in x) (out x)))";
    let cached = with_project(private, 1, |aliases, at| aliases.cache_absolute_reference_diagnostic(at).unwrap());
    assert_eq!(cached.word(), "::lib::Task");
    assert_eq!(cached.primary().file, [b"app.ncg2".to_vec()]);
    assert_eq!(cached.primary().span.len(), cached.word().len());
    assert_eq!(cached.problem().unwrap().kind, ReferenceDiagnosticKind::Private);

    with_project(&format!("{private} ; 変更"), 2, |aliases, at| {
        let reused = aliases.reuse_absolute_reference_diagnostic(at, &cached).unwrap();
        assert!(core::ptr::eq(reused, &cached));
        assert_eq!(reused.problem().unwrap().kind, ReferenceDiagnosticKind::Private);
    });
    for edited in [
        format!("; 先頭
{private}"),
        format!("{private} (namespace lib (export Task))"),
        "(namespace lib)".to_owned(),
    ] {
        with_project(&edited, 3, |aliases, at| {
            assert!(aliases.reuse_absolute_reference_diagnostic(at, &cached).is_none());
        });
    }
}

#[test]
fn scans_reference_positions_in_source_order_without_name_resolution() {
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "app.ncg2", revision: 1,
            text: "(using nor) (func Pass (in x) (out x)) (func Run (in x) (out y) (def n (nor x x)) (def y (unknown n)))",
        },
        SourceSnapshot { path: "empty.ncg2", revision: 1, text: "; 空の文書" },
        SourceSnapshot {
            path: "other.ncg2", revision: 1,
            text: "(func Other (in x) (out y) (def y (nor x x)))",
        },
    ]).unwrap();
    let mut cursor = project.definition_positions();
    let mut references = Vec::new();
    let mut advanced = 0;
    loop {
        match cursor.step() {
            DefinitionPositionStep::Reference(at) => references.push(at),
            DefinitionPositionStep::Advanced => advanced += 1,
            DefinitionPositionStep::Finished => break,
        }
    }
    assert!(advanced > 0);
    assert_eq!(references, [
        DefinitionPosition { file: 0, entry: 2, definition: 0, reference: 0 },
        DefinitionPosition { file: 0, entry: 2, definition: 1, reference: 0 },
        DefinitionPosition { file: 2, entry: 0, definition: 0, reference: 0 },
    ]);
    let stop = cursor.position();
    assert_eq!(stop.file, 3);
    assert_eq!(cursor.step(), DefinitionPositionStep::Finished);
    assert_eq!(cursor.position(), stop);
}
