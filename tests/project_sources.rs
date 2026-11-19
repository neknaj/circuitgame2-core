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
