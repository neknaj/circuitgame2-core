use circuitgame2_core::ncg2m::defn::{
    DataTypeName, DefnHeaderError, DefnPart, parse_defn_header,
};

#[test]
fn supports_deep_list_types_without_using_the_rust_stack() {
    let depth = 30_000;
    let mut source = "(defn identity (as-type (Fn () ".to_owned();
    source.push_str(&"(List ".repeat(depth));
    let name_start = source.len();
    source.push_str("State");
    let name_end = source.len();
    source.push_str(&")".repeat(depth));
    source.push_str(") (fn () state)))");

    let header = parse_defn_header(&source).unwrap();
    assert!(header.parameters.is_empty());
    assert_eq!(header.result_type.name, DataTypeName::Deferred);
    assert_eq!(header.result_type.name_span, name_start..name_end);
    assert_eq!(header.result_type.list_depth, depth);
    assert_eq!(&source[header.body_span], "state");
}

#[test]
fn reports_the_first_duplicate_parameter_with_both_sources() {
    let source = "(defn f (as-type (Fn (Bool Symbol Syntax Nat) Int) (fn (a b a b) a)))";
    let names = source.find("a b a b").unwrap();
    assert_eq!(
        parse_defn_header(source).unwrap_err(),
        DefnHeaderError::DuplicateParameter {
            first: names..names + 1,
            duplicate: names + 4..names + 5,
        },
    );
}

#[test]
fn leaves_the_single_body_to_the_stage_type_checker() {
    let source = "(defn f (as-type (Fn () Nat) (fn () (future-builtin 12))))";
    let header = parse_defn_header(source).unwrap();
    assert_eq!(&source[header.body_span], "(future-builtin 12)");

    let source = "(defn f (as-type (Fn () Nat) (fn () 0 1)))";
    let function = source.find("(fn").unwrap();
    assert_eq!(
        parse_defn_header(source).unwrap_err(),
        DefnHeaderError::Expected {
            span: function..function + "(fn () 0 1)".len(),
            part: DefnPart::Function,
        },
    );
}
