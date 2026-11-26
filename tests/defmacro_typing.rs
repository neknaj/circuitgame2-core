use circuitgame2_core::ncg2m::data_types::{BuiltinDataType, DataTypeAtom};
use circuitgame2_core::ncg2m::expression_types::{DeferredExpression, ExpressionCheckFailure, MacroBodyError};
use circuitgame2_core::ncg2m::template::{InsertionKind, TemplateError};
use circuitgame2_core::project::{
    SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources,
};

#[test]
fn checks_macro_insertions_and_preserves_their_original_order() {
    let declarations = r#"(namespace lib
        (export build empty)
        (defmacro build (x y) (list
            (syntax (def tmp (nor (unsyntax (let ((alias x)) alias)) (splice (list y x)))))
            y
            (syntax (def y (unsyntax x)))))
        (defmacro empty () (list)))"#;
    let project = parse_project_sources(&[
        SourceSnapshot { path: "lib.ncg2m", revision: 31, text: declarations },
        SourceSnapshot { path: "top.ncg2", revision: 47, text: "(using nor) (func top (in) (out y))" },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let selected = aliases.resolve_defmacro_name(1, 1, "::lib::build").unwrap();
    let checked = project.check_defmacro_body(&selected).unwrap().unwrap();
    assert_eq!(checked.body.source.revision, 31);
    assert_eq!(checked.parameters.iter().map(|param| param.name).collect::<Vec<_>>(), ["x", "y"]);
    assert!(checked.parameters.iter().all(|param| param.ty.ty.atom == DataTypeAtom::Builtin(BuiltinDataType::Syntax)
        && param.ty.ty.list_depth == 0));
    assert_eq!(checked.elements.len(), 3);
    assert!(checked.elements[1].template.is_none());
    let insertions = checked.elements.iter().flat_map(|element| &element.insertions).collect::<Vec<_>>();
    assert_eq!(insertions.len(), 3);
    assert_eq!(insertions.iter().map(|row| row.expected).collect::<Vec<_>>(),
        [InsertionKind::Syntax, InsertionKind::List, InsertionKind::Syntax]);
    assert_eq!(insertions.iter().map(|row| &declarations[row.expression_span.clone()]).collect::<Vec<_>>(),
        ["(let ((alias x)) alias)", "(list y x)", "x"]);
    assert!(insertions.windows(2).all(|pair| pair[0].span.start < pair[1].span.start));
    let empty = aliases.resolve_defmacro_name(1, 1, "::lib::empty").unwrap();
    assert!(project.check_defmacro_body(&empty).unwrap().unwrap().elements.is_empty());
}

#[test]
fn distinguishes_the_first_macro_type_error_from_deferred_forms() {
    let declarations = r#"(namespace lib
        (export wrong-element wrong-splice first invalid-syntax invalid-root pending)
        (defmacro wrong-element () (list true))
        (defmacro wrong-splice (x) (list (syntax (head (splice x)))))
        (defmacro first () (list (syntax (head (unsyntax (helper)) (splice))) (syntax)))
        (defmacro invalid-syntax () (list (syntax one two)))
        (defmacro invalid-root () (list (syntax (splice (list)))))
        (defmacro pending () (helper)))"#;
    let project = parse_project_sources(&[
        SourceSnapshot { path: "lib.ncg2m", revision: 31, text: declarations },
        SourceSnapshot { path: "top.ncg2", revision: 47, text: "(using nor) (func top (in) (out y))" },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let check = |name| {
        let def = aliases.resolve_defmacro_name(1, 1, name).unwrap();
        project.check_defmacro_body(&def).unwrap().unwrap_err()
    };
    for (name, source) in [("::lib::wrong-element", "true"), ("::lib::wrong-splice", "x")] {
        let MacroBodyError::Expression { span, error: ExpressionCheckFailure::Type(_) } = check(name) else {
            panic!("型違反が必要です");
        };
        assert_eq!(&declarations[span], source);
    }
    let MacroBodyError::Expression { span, error: ExpressionCheckFailure::Deferred(_) } = check("::lib::first") else {
        panic!("最初の挿入式が保留になる必要があります");
    };
    assert_eq!(&declarations[span], "(helper)");
    assert!(matches!(check("::lib::invalid-syntax"), MacroBodyError::Template(TemplateError::SyntaxArity(_))));
    assert!(matches!(check("::lib::invalid-root"), MacroBodyError::Template(TemplateError::SpliceAtRoot(_))));
    assert!(matches!(check("::lib::pending"), MacroBodyError::Deferred(DeferredExpression::Form(_))));
}
