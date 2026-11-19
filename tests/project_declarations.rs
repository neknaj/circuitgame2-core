use circuitgame2_core::project::{
    NameConflictKind, NameKey, SourceSnapshot, index_declarations, parse_circuit_project,
};
use circuitgame2_core::syntax::circuit::Head;

fn snapshot<'a>(path: &'a str, revision: u64, text: &'a str) -> SourceSnapshot<'a> {
    SourceSnapshot {
        path,
        revision,
        text,
    }
}

#[test]
fn shares_namespace_paths_and_finds_implicit_ancestors() {
    let project = parse_circuit_project(&[
        snapshot(
            "part.ncg2",
            3,
            "(namespace app::logic (module-part worker (def y 0)))",
        ),
        snapshot(
            "decl.ncg2",
            2,
            "(namespace app::logic (module worker (in) (out y)))",
        ),
        snapshot("empty.ncg2", 7, "(namespace app::other::empty)"),
    ])
    .unwrap();
    let table = index_declarations(&project).unwrap();
    let key = NameKey {
        parent: Some("app::logic"),
        name: "worker",
    };
    let (source, form) = table.declaration(key).unwrap();
    assert_eq!(source.id.components(), ["decl.ncg2"]);
    assert_eq!(form.head, Head::Module);
    assert_eq!(&source.text[form.name.span.clone()], "worker");
    assert!(
        table
            .declaration(NameKey {
                parent: None,
                name: "worker"
            })
            .is_none()
    );

    for (parent, name) in [
        (None, "app"),
        (Some("app"), "logic"),
        (Some("app"), "other"),
        (Some("app::other"), "empty"),
    ] {
        let location = table.namespace(NameKey { parent, name }).unwrap();
        assert_eq!(&location.source.text[location.span], name);
    }
    assert!(
        table
            .namespace(NameKey {
                parent: Some("app"),
                name: "log"
            })
            .is_none()
    );
    assert!(
        table
            .namespace(NameKey {
                parent: None,
                name: "app::logic"
            })
            .is_none()
    );
}

#[test]
fn keeps_name_identity_when_snapshots_are_reordered() {
    let left = "(namespace app (func evaluate (in) (out y)))";
    let right = "(namespace app (module evaluate (in) (out y)))";
    for reverse in [false, true] {
        let mut sources = [
            snapshot("a.ncg2", 4, left),
            snapshot("./a.ncg2", 4, left),
            snapshot("b.ncg2", 8, right),
        ];
        if reverse {
            sources.reverse();
        }
        let project = parse_circuit_project(&sources).unwrap();
        let error = index_declarations(&project).unwrap_err();
        assert_eq!(error.kind, NameConflictKind::DuplicateDeclaration);
        let expected = if reverse {
            [("b.ncg2", 8), ("a.ncg2", 4)]
        } else {
            [("a.ncg2", 4), ("b.ncg2", 8)]
        };
        for (location, (file, revision)) in [error.first, error.second].into_iter().zip(expected) {
            assert_eq!(location.source.id.components(), [file]);
            assert_eq!(location.source.revision, revision);
            assert_eq!(&location.source.text[location.span], "evaluate");
        }
    }
}

#[test]
fn points_to_the_conflicting_namespace_component() {
    let case = "; 名前空間\n(namespace app::logic::internal)";
    for (conflicting_decl, component) in [
        ("(struct app (width 1))", "app"),
        ("(namespace app (struct logic (width 1)))", "logic"),
    ] {
        for reverse in [false, true] {
            let mut sources = [
                snapshot("namespaces.ncg2", 8, case),
                snapshot("decls.ncg2", 3, conflicting_decl),
            ];
            if reverse {
                sources.reverse();
            }
            let project = parse_circuit_project(&sources).unwrap();
            let error = index_declarations(&project).unwrap_err();
            assert_eq!(error.kind, NameConflictKind::DeclarationAndNamespace);
            let (ns, decl) = if reverse {
                (error.second, error.first)
            } else {
                (error.first, error.second)
            };
            assert_eq!(ns.source.id.components(), ["namespaces.ncg2"]);
            assert_eq!(ns.source.revision, 8);
            let start = case.find(component).unwrap();
            assert_eq!(ns.span, start..start + component.len());
            assert_eq!(decl.source.id.components(), ["decls.ncg2"]);
            assert_eq!(decl.source.revision, 3);
            assert_eq!(&conflicting_decl[decl.span], component);
        }
    }

    let project = parse_circuit_project(&[
        snapshot(
            "decls.ncg2",
            3,
            "(namespace app (struct logic (width 1))) (struct ap (width 1))",
        ),
        snapshot(
            "namespaces.ncg2",
            8,
            "(namespace app::logic-extra) (namespace application)",
        ),
    ])
    .unwrap();
    assert!(index_declarations(&project).is_ok());
}

#[test]
fn orders_conflicts_by_first_occurrence_then_second_occurrence() {
    let first = "; 先行する宣言\n(struct a (width 1)) (struct b (width 1))";
    let first_start = first.find("a (width").unwrap();
    for (later, expected_kind, second_name) in [
        (
            "(struct b (width 1)) (namespace a::inner) (struct a (width 1))",
            NameConflictKind::DeclarationAndNamespace,
            "a::inner",
        ),
        (
            "(struct b (width 1)) (struct a (width 1)) (namespace a::inner)",
            NameConflictKind::DuplicateDeclaration,
            "a (width",
        ),
    ] {
        let project = parse_circuit_project(&[
            snapshot("first.ncg2", 2, first),
            snapshot("later.ncg2", 3, later),
        ])
        .unwrap();
        let error = index_declarations(&project).unwrap_err();
        assert_eq!(error.kind, expected_kind);
        assert_eq!(error.first.source.id.components(), ["first.ncg2"]);
        assert_eq!(error.second.source.id.components(), ["later.ncg2"]);
        let second_start = later.find(second_name).unwrap();
        assert_eq!(error.first.span, first_start..first_start + 1);
        assert_eq!(error.second.span, second_start..second_start + 1);
    }
}

#[test]
fn orders_conflicting_namespace_components_by_the_following_declaration() {
    let namespace = "; 名前空間の宣言\n(namespace a::b)";
    let child = "; 子名前空間と衝突する宣言\n(namespace a (struct b (width 1)))";
    let root = "(struct a (width 1))";
    let project = parse_circuit_project(&[
        snapshot("namespace.ncg2", 4, namespace),
        snapshot("child.ncg2", 5, child),
        snapshot("root.ncg2", 6, root),
    ])
    .unwrap();
    let error = index_declarations(&project).unwrap_err();
    assert_eq!(error.kind, NameConflictKind::DeclarationAndNamespace);
    assert_eq!(error.first.source.id.components(), ["namespace.ncg2"]);
    assert_eq!(error.first.source.revision, 4);
    assert_eq!(&namespace[error.first.span], "b");
    assert_eq!(error.second.source.id.components(), ["child.ncg2"]);
    assert_eq!(error.second.source.revision, 5);
    assert_eq!(&child[error.second.span], "b");
}

#[test]
fn keeps_the_first_two_of_three_declarations_of_one_name() {
    let text = "(struct word (width 1))";
    let project = parse_circuit_project(&[
        snapshot("early.ncg2", 7, text),
        snapshot("middle.ncg2", 8, text),
        snapshot("late.ncg2", 9, text),
    ])
    .unwrap();
    let error = index_declarations(&project).unwrap_err();
    assert_eq!(error.kind, NameConflictKind::DuplicateDeclaration);
    assert_eq!(error.first.source.id.components(), ["early.ncg2"]);
    assert_eq!(error.second.source.id.components(), ["middle.ncg2"]);
}
