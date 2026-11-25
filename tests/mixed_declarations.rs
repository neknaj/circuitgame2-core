use circuitgame2_core::project::{
    NameConflictKind, NameKey, ProjectDeclarationKind, SourceSnapshot, index_mixed_declarations,
    parse_project_sources,
};
use circuitgame2_core::syntax::circuit::Head;

#[test]
fn looks_up_both_languages_in_reopened_namespaces() {
    let circuit = "(namespace logic::gates (struct Bit (width 1)))";
    let meta = "; 宣言\n(namespace logic::gates (export build) (defmacro build () (list)))";
    let inputs = [
        SourceSnapshot { path: "gate.ncg2", revision: 6, text: circuit },
        SourceSnapshot { path: "./lib/../build.ncg2m", revision: 20, text: meta },
        SourceSnapshot { path: "build.ncg2m", revision: 20, text: meta },
    ];
    let project = parse_project_sources(&inputs).unwrap();
    let table = index_mixed_declarations(&project).unwrap();

    let entry = table.declaration(NameKey { parent: Some("logic::gates"), name: "Bit" }).unwrap();
    assert_eq!(entry.kind, ProjectDeclarationKind::Circuit(Head::Struct));
    assert_eq!(entry.file, 0);
    assert_eq!(&circuit[entry.name.span], "Bit");

    let entry = table.declaration(NameKey { parent: Some("logic::gates"), name: "build" }).unwrap();
    assert_eq!(entry.kind, ProjectDeclarationKind::Defmacro);
    assert_eq!(entry.file, 1);
    assert_eq!(entry.name.source.id.components(), &["build.ncg2m"]);
    assert_eq!(&meta[entry.name.span], "build");

    let parent = table.namespace(NameKey { parent: None, name: "logic" }).unwrap();
    assert_eq!(parent.source.revision, 6);
    assert_eq!(&circuit[parent.span], "logic");
}

#[test]
fn preserves_both_source_locations_for_cross_language_collisions() {
    let circuit = "; 回路\n(namespace shared (struct emit (width 1)))";
    let meta = "; マクロ\n(namespace shared (defmacro emit () (list)))";
    let inputs = [
        SourceSnapshot { path: "lib/./transform.ncg2m", revision: 90, text: meta },
        SourceSnapshot { path: "net.ncg2", revision: 32, text: circuit },
    ];
    let project = parse_project_sources(&inputs).unwrap();
    let error = index_mixed_declarations(&project).unwrap_err();
    assert_eq!(error.kind, NameConflictKind::DuplicateDeclaration);
    assert_eq!(error.first.source.id.components(), &["lib", "transform.ncg2m"]);
    assert_eq!(error.first.source.revision, 90);
    assert_eq!(&meta[error.first.span], "emit");
    assert_eq!(error.second.source.revision, 32);
    assert_eq!(&circuit[error.second.span], "emit");

    let circuit = "(struct shared (width 1))";
    let meta = "(namespace shared::tools)";
    let inputs = [
        SourceSnapshot { path: "tree.ncg2m", revision: 1, text: meta },
        SourceSnapshot { path: "name.ncg2", revision: 2, text: circuit },
    ];
    let project = parse_project_sources(&inputs).unwrap();
    let error = index_mixed_declarations(&project).unwrap_err();
    assert_eq!(error.kind, NameConflictKind::DeclarationAndNamespace);
    assert_eq!(&meta[error.first.span], "shared");
    assert_eq!(&circuit[error.second.span], "shared");
}
