use circuitgame2_core::project::{
    ExportError, NameKey, SourceSnapshot, index_exports, parse_circuit_project,
};

fn snapshot<'a>(path: &'a str, revision: u64, text: &'a str) -> SourceSnapshot<'a> {
    SourceSnapshot {
        path,
        revision,
        text,
    }
}

#[test]
fn publishes_shared_declarations_and_merges_repeated_directives() {
    for reverse in [false, true] {
        let mut files = [
            snapshot(
                "exports.ncg2",
                1,
                "(export root) (namespace app::logic (export f f) (export word f))",
            ),
            snapshot(
                "definitions.ncg2",
                2,
                "(func root (in) (out y)) (namespace app::logic (func f (in) (out y)) (struct word (width 1)) (struct private (width 1)))",
            ),
        ];
        if reverse {
            files.reverse();
        }
        let project = parse_circuit_project(&files).unwrap();
        let exports = index_exports(&project).unwrap();
        for (parent, name) in [
            (None, "root"),
            (Some("app::logic"), "f"),
            (Some("app::logic"), "word"),
        ] {
            let key = NameKey { parent, name };
            assert!(exports.is_public(key));
            let (source, _) = exports.declarations().declaration(key).unwrap();
            assert_eq!(source.id.components(), ["definitions.ncg2"]);
        }
        assert!(!exports.is_public(NameKey {
            parent: Some("app::logic"),
            name: "private"
        }));
        assert!(!exports.is_public(NameKey {
            parent: Some("app"),
            name: "logic"
        }));
    }
}

#[test]
fn points_to_the_first_unresolved_name_with_its_document_revision() {
    let text = "; 公開名\n(namespace app (export f absent later))";
    let project = parse_circuit_project(&[
        snapshot(
            "definitions.ncg2",
            2,
            "(namespace app (func f (in) (out y)))",
        ),
        snapshot("dir/./exports.ncg2", 7, text),
    ])
    .unwrap();
    let error = index_exports(&project).unwrap_err();
    let ExportError::MissingDeclaration(location) = error else {
        panic!("expected unresolved export: {error:?}");
    };
    assert_eq!(location.source.id.components(), ["dir", "exports.ncg2"]);
    assert_eq!(location.source.revision, 7);
    let start = text.find("absent").unwrap();
    assert_eq!(location.span, start..start + "absent".len());
}

#[test]
fn rejects_child_namespaces_aliases_and_module_fragments_as_export_targets() {
    for (text, name) in [
        (
            "(namespace lib::private) (namespace lib (export private))",
            "private",
        ),
        (
            "(namespace lib (struct internal (width 1))) (use ::lib::internal alias) (export alias)",
            "alias",
        ),
        ("(module-part fragment) (export fragment)", "fragment"),
        (
            "(struct root (width 1)) (namespace inner (export root))",
            "root",
        ),
    ] {
        let project = parse_circuit_project(&[snapshot("main.ncg2", 2, text)]).unwrap();
        let error = index_exports(&project).unwrap_err();
        let ExportError::MissingDeclaration(location) = error else {
            panic!("expected unresolved export: {error:?}");
        };
        let start = text.rfind(name).unwrap();
        assert_eq!(location.span, start..start + name.len());
    }
}

#[test]
fn validates_declaration_conflicts_before_applying_exports() {
    let project = parse_circuit_project(&[
        snapshot("export.ncg2", 1, "(export absent)"),
        snapshot(
            "duplicate.ncg2",
            2,
            "(struct word (width 1)) (struct word (width 2))",
        ),
    ])
    .unwrap();
    assert!(matches!(
        index_exports(&project),
        Err(ExportError::Conflict(_))
    ));
}
