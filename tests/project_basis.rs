use circuitgame2_core::project::{
    CircuitBasisError, SourceSnapshot, parse_circuit_project, parse_project_sources,
    validate_circuit_basis, validate_mixed_circuit_basis,
};

#[test]
fn an_empty_project_needs_no_basis_but_an_empty_circuit_file_does() {
    let project = parse_circuit_project(&[]).unwrap();
    assert!(validate_circuit_basis(&project).unwrap().is_none());
    let project = parse_circuit_project(&[SourceSnapshot {
        path: "empty.ncg2",
        revision: 1,
        text: "; (using nor)",
    }])
    .unwrap();
    assert!(matches!(
        validate_circuit_basis(&project),
        Err(CircuitBasisError::Missing)
    ));
}

#[test]
fn counts_normalized_files_once_and_ignores_nested_s_expressions() {
    let declaration = "; 基底\n(using nor)";
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "main.ncg2",
            revision: 5,
            text: declaration,
        },
        SourceSnapshot {
            path: "lib/../main.ncg2",
            revision: 5,
            text: declaration,
        },
        SourceSnapshot {
            path: "part.ncg2",
            revision: 2,
            text: "(module-part M (expand ::meta (using nor)))",
        },
    ])
    .unwrap();
    let location = validate_circuit_basis(&project).unwrap().unwrap();
    assert_eq!(location.source.id.components(), ["main.ncg2"]);
    assert_eq!(location.source.revision, 5);
    assert_eq!(&declaration[location.span], "nor");
}

#[test]
fn locates_the_first_two_declarations_even_in_different_files() {
    let text = "(using nor)";
    let project = parse_circuit_project(&[
        SourceSnapshot {
            path: "z.ncg2",
            revision: 7,
            text,
        },
        SourceSnapshot {
            path: "a.ncg2",
            revision: 4,
            text,
        },
        SourceSnapshot {
            path: "third.ncg2",
            revision: 3,
            text,
        },
    ])
    .unwrap();
    let CircuitBasisError::Duplicate { first, later } =
        validate_circuit_basis(&project).unwrap_err()
    else {
        panic!("expected duplicate basis declarations");
    };
    assert_eq!(first.source.id.components(), ["z.ncg2"]);
    assert_eq!(later.source.id.components(), ["a.ncg2"]);
    assert_eq!(first.source.revision, 7);
    assert_eq!(later.source.revision, 4);
    assert_eq!(&text[first.span], "nor");
    assert_eq!(&text[later.span], "nor");
}

#[test]
fn mixed_basis_reports_locations_in_source_order() {
    let text = "(using nor)";
    let sources = [
        SourceSnapshot {
            path: "meta.ncg2m",
            revision: 6,
            text: "",
        },
        SourceSnapshot {
            path: "body.ncg2",
            revision: 7,
            text: "(func main (in x) (out x))",
        },
        SourceSnapshot {
            path: "first.ncg2",
            revision: 8,
            text,
        },
        SourceSnapshot {
            path: "./first.ncg2",
            revision: 8,
            text,
        },
        SourceSnapshot {
            path: "other.ncg2m",
            revision: 9,
            text: "",
        },
        SourceSnapshot {
            path: "last.ncg2",
            revision: 10,
            text,
        },
    ];
    let check = |end| parse_project_sources(&sources[..end]).unwrap();
    assert!(validate_mixed_circuit_basis(&check(1)).unwrap().is_none());
    assert!(matches!(
        validate_mixed_circuit_basis(&check(2)),
        Err(CircuitBasisError::Missing)
    ));

    let first = check(5);
    let found = validate_mixed_circuit_basis(&first).unwrap().unwrap();
    assert_eq!(found.source.id.components(), ["first.ncg2"]);
    assert_eq!(found.source.revision, 8);
    assert_eq!(found.span, 7..10);

    let duplicate = check(6);
    let Err(CircuitBasisError::Duplicate { first, later }) =
        validate_mixed_circuit_basis(&duplicate)
    else {
        panic!("最初の二件の基底を報告する")
    };
    assert_eq!(first.source.id.components(), ["first.ncg2"]);
    assert_eq!(first.source.revision, 8);
    assert_eq!(first.span, 7..10);
    assert_eq!(later.source.id.components(), ["last.ncg2"]);
    assert_eq!(later.source.revision, 10);
    assert_eq!(later.span, 7..10);
}
