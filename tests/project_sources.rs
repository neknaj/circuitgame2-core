use circuitgame2_core::project::{
    PathError, SourceKind, SourceSetError, SourceSnapshot, collect_sources, normalize_path,
};

#[test]
fn normalizes_virtual_file_identity_without_changing_case_or_unicode() {
    let path = normalize_path("./回路//補助/../Main.ncg2/").unwrap();
    assert_eq!(path.components(), ["回路", "Main.ncg2"]);
    assert_eq!(path.source_kind(), Some(SourceKind::Circuit));
    assert!(path.same_file(&normalize_path("回路/Main.ncg2").unwrap()));
    assert!(!path.same_file(&normalize_path("回路/main.ncg2").unwrap()));
    assert!(
        !normalize_path("é.ncg2")
            .unwrap()
            .same_file(&normalize_path("e\u{301}.ncg2").unwrap())
    );
}

#[test]
fn rejects_invalid_roots_and_classifies_normalized_extensions() {
    for (path, error) in [
        ("/main.ncg2", PathError::Absolute),
        ("C:main.ncg2", PathError::Absolute),
        ("a/../C:/main.ncg2", PathError::Absolute),
        (r"dir\main.ncg2", PathError::Backslash),
        ("a/../../main.ncg2", PathError::EscapesRoot),
        ("", PathError::Empty),
        ("a/../.", PathError::Empty),
    ] {
        assert_eq!(normalize_path(path), Err(error), "{path}");
    }

    for (path, kind) in [
        ("a.ncg2b/../.hidden.ncg2m", Some(SourceKind::Functional)),
        ("code.ncg2", Some(SourceKind::Circuit)),
        (".ncg2", None),
        ("code.NCG2", None),
        ("a.ncg2/b", None),
    ] {
        assert_eq!(normalize_path(path).unwrap().source_kind(), kind, "{path}");
    }
}

fn snapshot<'a>(path: &'a str, revision: u64, text: &'a str) -> SourceSnapshot<'a> {
    SourceSnapshot {
        path,
        revision,
        text,
    }
}

#[test]
fn deduplicates_alias_paths_but_keeps_distinct_files_with_identical_contents() {
    let first = collect_sources(&[
        snapshot("lib/main.ncg2", 7, "(using nor)"),
        snapshot("./lib//main.ncg2", 7, "(using nor)"),
        snapshot("Lib/main.ncg2", 7, "(using nor)"),
        snapshot("macro.ncg2m", 3, ""),
    ])
    .unwrap();
    let permuted = collect_sources(&[
        snapshot("macro.ncg2m", 3, ""),
        snapshot("Lib/main.ncg2", 7, "(using nor)"),
        snapshot("./lib//main.ncg2", 7, "(using nor)"),
    ])
    .unwrap();

    assert_eq!(first.len(), 3);
    assert_eq!(permuted.len(), 3);
    for (left, right) in first.iter().zip(permuted.iter().rev()) {
        assert!(left.id.same_file(&right.id));
        assert_eq!(
            (left.kind, left.revision, left.text),
            (right.kind, right.revision, right.text)
        );
    }
    assert_eq!(first[2].kind, SourceKind::Functional);
}

#[test]
fn reports_both_snapshots_when_a_normalized_id_conflicts() {
    for (revision, text) in [(3, "old"), (2, "new")] {
        let inputs = [
            snapshot("main.ncg2", 2, "old"),
            snapshot("./main.ncg2/", 2, "old"),
            snapshot("tmp/../main.ncg2", revision, text),
        ];
        assert_eq!(
            collect_sources(&inputs).unwrap_err(),
            SourceSetError::ConflictingSnapshot { first: 0, input: 2 }
        );
    }

    assert_eq!(
        collect_sources(&[snapshot("../bad.ncg2", 1, "")]).unwrap_err(),
        SourceSetError::Path {
            input: 0,
            error: PathError::EscapesRoot
        }
    );
    assert_eq!(
        collect_sources(&[snapshot("main.NCG2", 1, "")]).unwrap_err(),
        SourceSetError::UnsupportedExtension { input: 0 }
    );
}

#[test]
fn parses_each_circuit_snapshot_once_and_preserves_its_names() {
    use circuitgame2_core::project::parse_circuit_project;
    use circuitgame2_core::syntax::circuit::Head;

    let left = "(namespace app::logic (module worker (in) (out y)))";
    let same_text = left.to_string();
    let right = "(namespace app::logic (module-part worker (def y 0)))";
    let project = parse_circuit_project(&[
        snapshot("lib/worker.ncg2", 2, left),
        snapshot("./lib/tmp/../worker.ncg2", 2, &same_text),
        snapshot("part.ncg2", 4, right),
    ])
    .unwrap();

    assert_eq!(project.sources().len(), 2);
    assert_eq!(project.circuits().len(), 2);
    for (i, (kind, text, revision)) in [(Head::Module, left, 2), (Head::ModulePart, right, 4)]
        .into_iter()
        .enumerate()
    {
        let file = &project.sources()[i];
        let names = &project.circuits()[i].names;
        assert_eq!(file.text, text);
        assert_eq!(file.revision, revision);
        assert_eq!(names[1].head, kind);
        assert_eq!(names[1].name.word, "worker");
        assert_eq!(names[1].namespace.as_ref().unwrap().word, "app::logic");
        assert_eq!(names[1].block, Some(names[0].form));
    }
}

#[test]
fn attaches_the_file_identity_and_revision_to_circuit_diagnostics() {
    use circuitgame2_core::project::{CircuitProjectError, parse_circuit_project};
    use circuitgame2_core::syntax::circuit::{CircuitFormError, HeaderError};

    let invalid = "; 診断位置\n(test demo (reset) (case))";
    let error = parse_circuit_project(&[
        snapshot("valid.ncg2", 3, "(using nor)"),
        snapshot("./lib/temp/../bad.ncg2", 12, invalid),
    ])
    .unwrap_err();
    let CircuitProjectError::Syntax {
        id,
        revision,
        error,
    } = error
    else {
        panic!("expected a circuit syntax error: {error:?}");
    };
    assert_eq!(id.components(), ["lib", "bad.ncg2"]);
    assert_eq!(revision, 12);
    let CircuitFormError::Header {
        kind: HeaderError::MixedTestItems {
            first_head: (start, end),
        },
        span,
    } = error
    else {
        panic!("expected a mixed test item error: {error:?}");
    };
    assert_eq!(&invalid[start..end], "reset");
    assert_eq!(&invalid[span], "case");
}

#[test]
fn identifies_functional_sources_in_the_circuit_only_entry_point() {
    use circuitgame2_core::project::{CircuitProjectError, parse_circuit_project};

    let error = parse_circuit_project(&[snapshot("./lib//macros.ncg2m", 9, "")]).unwrap_err();
    let CircuitProjectError::UnsupportedLanguage { id, revision, kind } = error else {
        panic!("expected an unsupported language error: {error:?}");
    };
    assert_eq!(id.components(), ["lib", "macros.ncg2m"]);
    assert_eq!(revision, 9);
    assert_eq!(kind, SourceKind::Functional);
}

#[test]
fn validates_collection_before_parsing_and_parses_in_first_occurrence_order() {
    use circuitgame2_core::project::{CircuitProjectError, parse_circuit_project};

    let malformed = snapshot("bad.ncg2", 1, ")");
    let bad_id = snapshot("../escaping.ncg2", 2, "");
    let error = parse_circuit_project(&[malformed, bad_id]).unwrap_err();
    assert!(matches!(
        error,
        CircuitProjectError::Sources(SourceSetError::Path {
            input: 1,
            error: PathError::EscapesRoot,
        })
    ));

    let malformed = snapshot("bad.ncg2", 1, ")");
    let functional = snapshot("macros.ncg2m", 2, "");
    let error = parse_circuit_project(&[malformed, functional]).unwrap_err();
    assert!(
        matches!(error, CircuitProjectError::Syntax { id, .. } if id.components() == ["bad.ncg2"])
    );
}
