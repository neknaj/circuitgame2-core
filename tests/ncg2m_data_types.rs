use circuitgame2_core::ncg2m::data_types::{
    BuiltinDataType, DataTypeAtom, parse_defn_signature,
};
use circuitgame2_core::ncg2m::defn::{DefnHeaderError, DefnPart};
use circuitgame2_core::ncg2m::integers::IntegerType;
use circuitgame2_core::project::{
    NameKey, SourceSnapshot, index_mixed_declarations, parse_project_sources,
};

#[test]
fn reads_a_signature_at_its_source_positions_in_the_project() {
    let text = "; 型の位置
(namespace tests
  (defmacro unused () (list))
  (defn build (as-type (Fn (Bool (List (List State))) Nat)
    (fn (ready states) 42))))
";
    let inputs = [
        SourceSnapshot { path: "circuit.ncg2", revision: 2, text: "(using nor)" },
        SourceSnapshot { path: "./lib/../example.ncg2m", revision: 9, text },
    ];
    let project = parse_project_sources(&inputs).unwrap();
    let declarations = index_mixed_declarations(&project).unwrap();
    let found = declarations.declaration(NameKey { parent: Some("tests"), name: "build" }).unwrap();
    let signature = project.defn_signature(found.file, found.item).unwrap();

    assert_eq!(&text[signature.name_span], "build");
    assert_eq!(&text[signature.body_span], "42");
    assert_eq!(signature.parameters[0].name, "ready");
    assert_eq!(signature.parameters[0].ty.ty.atom, DataTypeAtom::Builtin(BuiltinDataType::Bool));
    let nested = &signature.parameters[1].ty;
    assert_eq!(&text[nested.span.clone()], "(List (List State))");
    assert_eq!(&text[nested.name_span.clone()], "State");
    assert_eq!(nested.ty.atom, DataTypeAtom::Named("State"));
    assert_eq!(nested.ty.list_depth, 2);
    assert_eq!(signature.result_type.ty.atom, DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Nat)));

    assert!(project.defn_signature(0, 0).is_none());
    assert!(project.defn_signature(found.file, found.item - 1).is_none());
    assert!(project.defn_signature(found.file, usize::MAX).is_none());
}

#[test]
fn rejects_a_function_signature_inside_a_list_data_type() {
    let text = "(defn f (as-type (Fn ((List (Fn () Nat))) Nat) (fn (x) 0)))";
    let first = text.find("(Fn () Nat)").unwrap();
    let second = first + "(Fn () Nat)".len();
    assert_eq!(
        parse_defn_signature(text).unwrap_err(),
        DefnHeaderError::Expected {
            span: first..second,
            part: DefnPart::DataType,
        },
    );
}
