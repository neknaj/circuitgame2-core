use circuitgame2_core::ncg2m::defn::{DefnHeaderError, DefnPart};
use circuitgame2_core::ncg2m::file::MetaFileError;
use circuitgame2_core::project::{
    ProjectFileSyntaxError, ProjectSourceParseError, SourceSetError, SourceSnapshot,
    parse_project_sources,
};

#[test]
fn reports_the_first_invalid_file_in_its_original_coordinates() {
    let meta = "; 前置き\n(defn f (as-type (Fn () (Fn () Int)) (fn () 0)))";
    let inputs = [
        SourceSnapshot { path: "./logic/probe.ncg2m", revision: 9, text: "" },
        SourceSnapshot { path: "logic/./probe.ncg2m", revision: 9, text: "" },
        SourceSnapshot { path: "logic/../typed.ncg2m", revision: 23, text: meta },
        SourceSnapshot { path: "main.ncg2", revision: 30, text: ")" },
    ];
    let error = parse_project_sources(&inputs).unwrap_err();
    let ProjectSourceParseError::File { input, id, revision, error } = error else {
        panic!("expected an error in the third input");
    };
    let start = meta.find("(Fn () Int)").unwrap();
    assert_eq!(input, 2);
    assert_eq!(id.components(), &["typed.ncg2m"]);
    assert_eq!(revision, 23);
    assert_eq!(
        error,
        ProjectFileSyntaxError::Functional(MetaFileError::Defn(DefnHeaderError::Expected {
            span: start..start + "(Fn () Int)".len(),
            part: DefnPart::DataType,
        })),
    );
}

#[test]
fn finishes_source_collection_before_attempting_to_parse_files() {
    let inputs = [
        SourceSnapshot { path: "logic.ncg2m", revision: 0, text: ")" },
        SourceSnapshot { path: "Main.NCG2", revision: 1, text: "" },
        SourceSnapshot { path: "./logic.ncg2m", revision: 2, text: "" },
    ];
    assert!(matches!(
        parse_project_sources(&inputs),
        Err(ProjectSourceParseError::Collection(SourceSetError::UnsupportedExtension { input: 1 })),
    ));
}
