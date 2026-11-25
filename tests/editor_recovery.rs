use circuitgame2_core::project::{
    ObservedCircuitBindingKind, RecoveredDeclarationQuery, SourceKind, SourceSnapshot,
    collect_sources, inspect_circuit_file, inspect_circuit_project, normalize_path,
};
use circuitgame2_core::syntax::circuit::{Head, RecoveredNamePosition};

#[test]
fn recovered_declaration_retains_the_collected_file_and_revision() {
    let text = concat!(
        "; 入力中の文書 🐈\n",
        ") (namespace app::logic (func inverter (in x) (out y) (def y (nor x x)))) ",
        "(namespace unfinished (func tentative (in) (out y) (def y 0))",
    );
    let snapshots = [
        SourceSnapshot { path: "logic/./main.ncg2", revision: 23, text },
        SourceSnapshot { path: "logic/main.ncg2", revision: 23, text },
        SourceSnapshot { path: "logic/macro.ncg2m", revision: 4, text: "" },
    ];
    let mut sources = collect_sources(&snapshots).unwrap();
    assert_eq!(sources.len(), 2);
    let file = inspect_circuit_file(&sources[0]).unwrap();
    let position = |fragment, item| RecoveredNamePosition::Original { fragment, item };
    let namespace = file.observed_binding_at(position(0, 0)).unwrap();
    assert!(matches!(namespace.kind, ObservedCircuitBindingKind::Namespace("app::logic")));
    let declaration = file.observed_binding_at(position(0, 1)).unwrap();
    assert!(matches!(
        declaration.kind,
        ObservedCircuitBindingKind::Declaration {
            head: Head::Func,
            key: circuitgame2_core::project::NameKey { parent: Some("app::logic"), name: "inverter" },
        },
    ));
    assert!(core::ptr::eq(declaration.location.source, file.source()));
    let id = normalize_path("logic/main.ncg2").unwrap();
    assert!(declaration.location.source.id.same_file(&id));
    assert_eq!(declaration.location.source.revision, 23);
    assert_eq!(&text[declaration.location.span], "inverter");
    assert!(file.observed_binding_at(position(1, 1)).is_none());
    assert!(inspect_circuit_file(&sources[1]).is_none());
    sources[1].kind = SourceKind::Circuit;
    assert!(inspect_circuit_file(&sources[1]).is_none());
}

#[test]
fn finds_all_observed_declarations_in_check_order() {
    let text = concat!(
        "(namespace app (bad) (func target (in) (out y) (def y 0)) ",
        "(func other (in) (out y) (def y 0)) (func target (in) (out y) (def y 1)))",
    );
    let input = [SourceSnapshot { path: "main.ncg2", revision: 7, text }];
    let sources = collect_sources(&input).unwrap();
    let file = inspect_circuit_file(&sources[0]).unwrap();
    let key = circuitgame2_core::project::NameKey { parent: Some("app"), name: "target" };
    let names = file.recovered_names();
    assert_eq!(names.position_group_count(), 1);
    let hits = file.declaration_candidates_in_group(key, 0);
    assert_eq!(hits.len(), 2);
    assert_eq!(hits[0].0, RecoveredNamePosition::File(2));
    assert_eq!(hits[1].0, RecoveredNamePosition::File(4));
    assert!(hits[0].1.location.span.end < hits[1].1.location.span.start);
    assert!(file.declaration_candidates_in_group(key, 1).is_empty());
}

#[test]
fn project_retains_candidates_from_each_file_when_a_source_is_incomplete() {
    let repaired = concat!(
        ") (namespace app (func target (in) (out y) (def y 0))) ",
        ") (namespace app (func target (in) (out y) (def y 1))) ",
        "(namespace app (func target (in) (out y) (def y 0))",
    );
    let sources = collect_sources(&[
        SourceSnapshot {
            path: "lib/valid.ncg2", revision: 8,
            text: "(namespace app (func target (in) (out y) (def y 0)))",
        },
        SourceSnapshot { path: "main.ncg2", revision: 9, text: repaired },
        SourceSnapshot { path: "macros.ncg2m", revision: 10, text: "" },
    ]).unwrap();
    let project = inspect_circuit_project(&sources);
    let key = circuitgame2_core::project::NameKey { parent: Some("app"), name: "target" };
    let rows = project.declaration_candidates(key).files;
    assert_eq!(rows.iter().map(Vec::len).collect::<Vec<_>>(), [1, 2, 0]);
    assert_eq!(rows[0][0].1.location.source.revision, 8);
    assert_eq!(rows[1][0].1.location.source.revision, 9);
    assert_eq!(rows[1][0].0, RecoveredNamePosition::Original { fragment: 0, item: 1 });
    assert_eq!(rows[1][1].0, RecoveredNamePosition::Original { fragment: 1, item: 1 });
    assert!(rows[1][0].1.location.span.end < rows[1][1].1.location.span.start);
}

#[test]
fn project_queries_a_prefix_in_original_forms_after_syntax_errors() {
    let sources = collect_sources(&[
        SourceSnapshot {
            path: "main.ncg2",
            revision: 7,
            text: concat!(
                "; コメント 🐈\n",
                ") (namespace app (func gate (in) (out y) (def y 0))) ",
                ") (namespace app (func gate-next (in) (out y) (def y 1))) ",
                "(namespace other (func gateway (in) (out y) (def y 0))) ",
                "(namespace app (func Gate-case (in) (out y) (def y 0))) ",
                "(namespace app (func gate-unfinished (in) (out y) (def y 0))",
            ),
        },
        SourceSnapshot {
            path: "lib.ncg2",
            revision: 8,
            text: "(namespace app (func gate-lib (in) (out y) (def y 0)))",
        },
    ]).unwrap();
    let editor = inspect_circuit_project(&sources);
    let result = editor.query_declarations(RecoveredDeclarationQuery::Prefix {
        parent: Some("app"),
        prefix: "gate",
        head: None,
    });
    let names: Vec<Vec<_>> = result
        .files
        .iter()
        .map(|rows| {
            rows.iter()
                .map(|(_, item)| {
                    (
                        &item.location.source.text()[item.location.span.clone()],
                        item.location.source.revision,
                    )
                })
                .collect()
        })
        .collect();
    assert_eq!(
        names,
        [vec![("gate", 7), ("gate-next", 7)], vec![("gate-lib", 8)]],
    );
}

#[test]
fn fragment_completion_uses_an_original_target_in_its_own_namespace() {
    let text = concat!(
        ") (namespace app (module gate (in x) (out y))) ",
        "(namespace app (func garden (in x) (out y) (def y x)) ",
        "(module-part ga (def y x))) ",
        "(namespace other (module gateway (in x) (out y))) ",
        "\x22(module-part ga",
    );
    let files = collect_sources(&[
        SourceSnapshot { path: "main.ncg2", revision: 11, text },
        SourceSnapshot {
            path: "lib.ncg2",
            revision: 12,
            text: "(namespace app (module gate-next (in x) (out y)))",
        },
    ]).unwrap();
    let project = inspect_circuit_project(&files);
    let target = text.find("ga (def").unwrap();
    let result = project.module_part_candidates(0, target + 2).unwrap();
    assert_eq!(result.replace.span, target..target + 2);
    assert_eq!(result.replace.source.revision, 11);
    assert_eq!(result.prefix, "ga");
    assert_eq!(result.namespace, Some("app"));
    let observed: Vec<_> = result.declarations.files.iter().flatten().map(|(_, item)| {
        &item.location.source.text()[item.location.span.clone()]
    }).collect();
    assert_eq!(observed, ["gate", "gate-next"]);
    assert!(project.module_part_candidates(0, target + 4).is_none());
    assert!(project.module_part_candidates(0, text.len()).is_none());
}
