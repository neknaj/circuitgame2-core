use circuitgame2_core::ncg2m::data_types::{BuiltinDataType, DataType, DataTypeAtom};
use circuitgame2_core::ncg2m::expression_types::{
    DeferredExpression, DefnBodyError, ExpressionCheckFailure, ExpressionTypeError, check_defn_body,
};
use circuitgame2_core::ncg2m::integers::IntegerType;

#[test]
fn checks_an_unselected_if_branch_at_its_original_source_position() {
    let source = "; 検査\n(defn f (as-type (Fn (Nat) Nat) (fn (n) (if true (as-type Nat n) false))))";
    let start = source.find("false").unwrap();
    let error = check_defn_body(source).unwrap_err();
    assert_eq!(
        error,
        DefnBodyError::Body(ExpressionCheckFailure::Type(ExpressionTypeError::Mismatch {
            span: start..start + "false".len(),
            expected: DataType {
                atom: DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Nat)),
                list_depth: 0,
            },
            actual: DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Bool), list_depth: 0 },
        })),
    );
}

#[test]
fn distinguishes_deferred_syntax_from_a_type_error() {
    let expression = "(fold-nat 1 0 (i acc) acc)";
    let source = "(defn f (as-type (Fn () Nat) (fn () (fold-nat 1 0 (i acc) acc))))";
    let start = source.find(expression).unwrap();
    assert_eq!(
        check_defn_body(source).unwrap_err(),
        DefnBodyError::Body(ExpressionCheckFailure::Deferred(DeferredExpression::Form(
            start..start + expression.len(),
        ))),
    );
}

#[test]
fn contextual_lists_check_empty_nested_and_numeric_elements() {
    let source = "(defn f (as-type (Fn () (List (List Int))) (fn ()
        (list (list) (list 9223372036854775807 -9223372036854775808)))))";
    let checked = check_defn_body(source).unwrap();
    assert_eq!(
        checked.result_type.ty,
        DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Int)), list_depth: 2 },
    );

    let source = "; 範囲\n(defn f (as-type (Fn () (List (List Nat))) (fn ()
        (list (list 0) (list false) (list (fn () 0))))))";
    let start = source.find("false").unwrap();
    let error = check_defn_body(source).unwrap_err();
    let DefnBodyError::Body(ExpressionCheckFailure::Type(ExpressionTypeError::Mismatch { span, .. })) = error else {
        panic!("expected the first element type error");
    };
    assert_eq!(span, start..start + "false".len());
}

#[test]
fn diagnoses_a_list_in_a_scalar_context() {
    let source = "(defn f (as-type (Fn () Nat) (fn () (list false))))";
    let start = source.find("(list false)").unwrap();
    assert_eq!(
        check_defn_body(source).unwrap_err(),
        DefnBodyError::Body(ExpressionCheckFailure::Type(ExpressionTypeError::ListInScalarContext(
            start..start + "(list false)".len(),
        ))),
    );
}

#[test]
fn let_resolves_every_rhs_in_the_outer_scope_then_shadows_in_the_body() {
    let source = "(defn f (as-type (Fn (Bool) (List Bool)) (fn (x)
        (let ((x 1) (original x))
            (let ((shadow (as-type Nat x)))
                (if original (list) (list original)))))))";
    assert!(check_defn_body(source).is_ok());

    let source = "(defn f (as-type (Fn () Nat) (fn ()
        (let ((x 1) (y x)) y))))";
    let start = source.find("x))").unwrap();
    assert_eq!(
        check_defn_body(source).unwrap_err(),
        DefnBodyError::Body(ExpressionCheckFailure::Deferred(DeferredExpression::Name(start..start + 1))),
    );
}

#[test]
fn let_reports_both_duplicate_name_spans() {
    use circuitgame2_core::ncg2m::expression_types::LetSyntaxError;

    let source = "; 束縛\n(defn f (as-type (Fn () Nat) (fn () (let ((x 1) (x 2)) x))))";
    let first = source.find("x 1").unwrap();
    let duplicate = source.find("x 2").unwrap();
    assert_eq!(
        check_defn_body(source).unwrap_err(),
        DefnBodyError::Body(ExpressionCheckFailure::Type(ExpressionTypeError::Let(
            LetSyntaxError::Duplicate { first: first..first + 1, duplicate: duplicate..duplicate + 1 },
        ))),
    );
}

#[test]
fn let_requires_a_type_annotation_for_an_empty_rhs_list() {
    let source = "(defn f (as-type (Fn () (List Bool)) (fn () (let ((xs (list))) xs))))";
    let start = source.find("(list)").unwrap();
    assert_eq!(
        check_defn_body(source).unwrap_err(),
        DefnBodyError::Body(ExpressionCheckFailure::Type(ExpressionTypeError::ListNeedsAnnotation(
            start..start + "(list)".len(),
        ))),
    );
    let source = "(defn f (as-type (Fn () (List Bool)) (fn () (let ((xs (as-type (List Bool) (list)))) xs))))";
    assert!(check_defn_body(source).is_ok());
}

#[test]
fn checks_deep_annotations_without_using_the_host_call_stack() {
    let depth = 30_000;
    let mut source = "(defn f (as-type (Fn (Int) Int) (fn (x) ".to_owned();
    source.push_str(&"(as-type Int ".repeat(depth));
    source.push_str("(if true x -9223372036854775808)");
    source.push_str(&")".repeat(depth));
    source.push_str(")))");
    let checked = check_defn_body(&source).unwrap();
    assert_eq!(checked.parameters[0].name, "x");
    assert_eq!(checked.parameters[0].ty.ty, checked.result_type.ty);
}

#[test]
fn diagnoses_list_depth_before_resolving_the_stage_type() {
    for (source, expr, expected_depth, actual_depth) in [
        ("(defn f (as-type (Fn () (List HostEvent)) (fn () 0)))", "0", 1, 0),
        ("(defn f (as-type (Fn () Bool) (fn () (as-type (List HostEvent) 0))))", "(as-type (List HostEvent) 0)", 0, 1),
    ] {
        let start = source.find(expr).unwrap();
        assert_eq!(
            check_defn_body(source).unwrap_err(),
            DefnBodyError::Body(ExpressionCheckFailure::Type(ExpressionTypeError::ListDepthMismatch {
                span: start..start + expr.len(),
                expected_depth,
                actual_depth,
            })),
        );
    }
}

#[test]
fn distinguishes_misplaced_fn_and_a_boolean_spelling_shared_with_a_parameter() {
    let source = "(defn f (as-type (Fn () Nat) (fn () (fn () 0))))";
    let misplaced = "(fn () 0)";
    let start = source.find(misplaced).unwrap();
    assert_eq!(
        check_defn_body(source).unwrap_err(),
        DefnBodyError::Body(ExpressionCheckFailure::Type(ExpressionTypeError::FunctionLiteral(
            start..start + misplaced.len(),
        ))),
    );

    let source = "(defn f (as-type (Fn (Nat) Nat) (fn (true) true)))";
    let start = source.rfind("true").unwrap();
    assert_eq!(
        check_defn_body(source).unwrap_err(),
        DefnBodyError::Body(ExpressionCheckFailure::Deferred(DeferredExpression::BooleanBinding(
            start..start + "true".len(),
        ))),
    );
}

#[test]
fn verifies_an_indexed_body_in_the_original_file_coordinates() {
    use circuitgame2_core::project::{NameKey, SourceSnapshot, index_mixed_declarations, parse_project_sources};

    let text = "; 複数の宣言
(namespace logic
  (defmacro unused () (list))
  (defn valid (as-type (Fn (Nat) Nat) (fn (x) (if true x 1))))
  (defn invalid (as-type (Fn () Nat) (fn () (if true 0 false)))))
";
    let snapshots = [
        SourceSnapshot { path: "main.ncg2", revision: 1, text: "(using nor)" },
        SourceSnapshot { path: "logic.ncg2m", revision: 22, text },
    ];
    let project = parse_project_sources(&snapshots).unwrap();
    let declarations = index_mixed_declarations(&project).unwrap();
    let valid = declarations.declaration(NameKey { parent: Some("logic"), name: "valid" }).unwrap();
    let invalid = declarations.declaration(NameKey { parent: Some("logic"), name: "invalid" }).unwrap();

    let signature = project.check_defn_body(valid.file, valid.item).unwrap().unwrap();
    assert_eq!(&text[signature.body_span], "(if true x 1)");
    let error = project.check_defn_body(invalid.file, invalid.item).unwrap().unwrap_err();
    let ExpressionCheckFailure::Type(ExpressionTypeError::Mismatch { span, .. }) = error else {
        panic!("expected a type mismatch");
    };
    assert_eq!(&text[span.clone()], "false");
    assert_eq!(span.start, text.find("false").unwrap());
    assert_eq!(project.sources()[invalid.file].revision, 22);
    assert!(project.check_defn_body(0, 0).is_none());
    assert!(project.check_defn_body(1, 1).is_none());
    assert!(project.check_defn_body(usize::MAX, 0).is_none());
}

#[test]
fn agrees_with_the_standalone_entry_point() {
    use circuitgame2_core::project::{SourceSnapshot, parse_project_sources};

    for text in [
        "(defn f (as-type (Fn (Int) Int) (fn (x) (if true x -9223372036854775808))))",
        "(defn f (as-type (Fn () Nat) (fn () (if true 0 false))))",
        "(defn f (as-type (Fn () (List HostEvent)) (fn () (list))))",
        "(defn f (as-type (Fn (Nat) Nat) (fn (x) (let ((n x)) n))))",
    ] {
        let inputs = [SourceSnapshot { path: "helper.ncg2m", revision: 0, text }];
        let project = parse_project_sources(&inputs).unwrap();
        let indexed = project.check_defn_body(0, 0).unwrap().map_err(DefnBodyError::Body);
        assert_eq!(indexed, check_defn_body(text));
    }
}
