use circuitgame2_core::project::{
    ObservedCircuitBindingKind, SourceKind, SourceSnapshot, collect_sources, inspect_circuit_file, normalize_path,
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
