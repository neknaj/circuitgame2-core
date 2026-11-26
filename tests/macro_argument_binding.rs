use circuitgame2_core::ncg2m::call_evaluation::macro_binding::{
    MacroArgumentError, MacroExpressionSite,
};
use circuitgame2_core::project::{
    MacroArgument, MacroCallError, MacroPreparationFailure, SourceSnapshot, check_mixed_use_aliases,
    index_mixed_use_targets, parse_project_sources,
};
use circuitgame2_core::syntax::Form;

fn argument_text<'a>(argument: &MacroArgument<'_, 'a>) -> &'a str {
    let source = argument.scope().source.text();
    match &argument.forms()[argument.nodes().start] {
        Form::Atom { span, .. } | Form::List { span, .. } => &source[span.clone()],
    }
}

#[test]
fn binds_caller_arguments_in_declaration_order_after_the_cursor_advances() {
    let library = r#"(namespace lib
        (export pick)
        (defmacro pick (x y) (list
            y
            (syntax (def x (unsyntax x)))
            (if true x y)
            (let ((x y)) x))))"#;
    let circuit = r#"(using nor)
        (namespace design
            (module top (in x y) (out z)
                (expand ::lib::pick x (nor x y))
                (expand ::lib::pick y x)))"#;
    let project = parse_project_sources(&[
        SourceSnapshot { path: "lib.ncg2m", revision: 31, text: library },
        SourceSnapshot { path: "top.ncg2", revision: 47, text: circuit },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let mut calls = aliases.macro_calls(1, 2).unwrap();
    let first = calls.next_bound_macro().unwrap().unwrap();
    let second = calls.next_bound_macro().unwrap().unwrap();
    assert!(calls.next_bound_macro().is_none());

    assert_eq!(first.arguments().iter().map(argument_text).collect::<Vec<_>>(), ["x", "(nor x y)"]);
    assert_eq!(second.arguments().iter().map(argument_text).collect::<Vec<_>>(), ["y", "x"]);
    assert_eq!(&circuit[first.site().span.clone()], "(expand ::lib::pick x (nor x y))");
    assert_eq!(first.body().body().source.revision, 31);
    assert_eq!(first.scope().source.revision, 47);
    assert_eq!((first.scope().file, first.scope().entry), (1, 2));

    let reference = first.argument_expression(MacroExpressionSite::Element(0)).unwrap();
    assert!(core::ptr::eq(reference, &first.arguments()[1]));
    assert_eq!(reference.scope().source.revision, 47);
    assert_eq!((reference.scope().file, reference.scope().entry), (1, 2));
    assert_eq!(argument_text(reference), "(nor x y)");
    let insertion = MacroExpressionSite::Insertion { element: 1, insertion: 0 };
    assert_eq!(argument_text(first.argument_expression(insertion).unwrap()), "x");
    assert_eq!(argument_text(second.argument_expression(insertion).unwrap()), "y");
    assert!(matches!(first.argument_expression(MacroExpressionSite::Insertion { element: 1, insertion: 1 }),
        Err(MacroArgumentError::NoExpression)));

    for (element, text) in [(2, "(if true x y)"), (3, "(let ((x y)) x)")] {
        let Err(MacroArgumentError::Deferred(span)) = first.argument_expression(MacroExpressionSite::Element(element))
            else { panic!("未対応の式は保留される必要があります"); };
        assert_eq!(&library[span], text);
    }
}

#[test]
fn reports_call_errors_before_the_body_and_preserves_scope_for_empty_arguments() {
    let library = r#"(namespace lib
        (export bad empty)
        (defmacro bad () (list true))
        (defmacro empty () (list)))"#;
    let circuit = r#"(using nor)
        (func top (in) (out y)
            (expand ::lib::bad y)
            (expand ::lib::bad)
            (expand ::lib::empty))"#;
    let project = parse_project_sources(&[
        SourceSnapshot { path: "lib.ncg2m", revision: 31, text: library },
        SourceSnapshot { path: "top.ncg2", revision: 47, text: circuit },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let mut calls = aliases.macro_calls(1, 1).unwrap();
    let first = calls.next_bound_macro().unwrap().unwrap_err();
    assert!(matches!(first.kind, MacroPreparationFailure::Call(MacroCallError::Arity { actual: 1, .. })));
    assert_eq!(&circuit[first.site.span], "(expand ::lib::bad y)");
    let second = calls.next_bound_macro().unwrap().unwrap_err();
    assert!(matches!(second.kind, MacroPreparationFailure::Body { .. }));
    let empty = calls.next_bound_macro().unwrap().unwrap();
    assert_eq!(empty.scope().source.revision, 47);
    assert!(empty.arguments().is_empty());
    assert!(matches!(empty.argument_expression(MacroExpressionSite::Element(0)),
        Err(MacroArgumentError::NoExpression)));
    assert!(calls.next_bound_macro().is_none());
}
