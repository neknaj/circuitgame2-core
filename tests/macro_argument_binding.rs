use std::num::NonZeroUsize;
use circuitgame2_core::ncg2m::call_evaluation::macro_expansion::{
    MacroExpandedElement, MacroExpansionErrorKind, MacroExpansionSlice,
};
use circuitgame2_core::ncg2m::call_evaluation::macro_syntax::ArgumentSyntaxToken;
use circuitgame2_core::ncg2m::template::TemplateEmission;
use circuitgame2_core::ncg2m::call_evaluation::macro_binding::{
    MacroArgumentError, MacroExpressionSite, MacroExpressionStep,
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
            (syntax (def x (unsyntax x) (splice (list x y))))
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

    let state = first.start_expression(MacroExpressionSite::Element(0)).unwrap();
    assert_eq!(&library[state.span()], "y");
    let MacroExpressionStep::Continue(state) = state.step().unwrap()
        else { panic!("先頭の仮引数との照合後に再開できる必要があります"); };
    let MacroExpressionStep::Value(value) = state.step().unwrap()
        else { panic!("次の仮引数に対応する元の構文が必要です"); };
    assert!(core::ptr::eq(value, &first.arguments()[1]));

    let reference = first.argument_expression(MacroExpressionSite::Element(0)).unwrap();
    assert!(core::ptr::eq(reference, &first.arguments()[1]));
    assert_eq!(reference.scope().source.revision, 47);
    assert_eq!((reference.scope().file, reference.scope().entry), (1, 2));
    assert_eq!(argument_text(reference), "(nor x y)");
    let insertion = MacroExpressionSite::Insertion { element: 1, insertion: 0 };
    assert_eq!(argument_text(first.argument_expression(insertion).unwrap()), "x");
    assert_eq!(argument_text(second.argument_expression(insertion).unwrap()), "y");
    let state = second.start_expression(insertion).unwrap();
    assert_eq!(&library[state.span()], "x");
    let MacroExpressionStep::Value(value) = state.step().unwrap()
        else { panic!("挿入式に対応する元の構文が必要です"); };
    assert!(core::ptr::eq(value, &second.arguments()[0]));
    let splice = MacroExpressionSite::Insertion { element: 1, insertion: 1 };
    let Err(MacroArgumentError::Deferred(span)) = first.start_expression(splice).unwrap().step()
        else { panic!("リスト構文の評価は保留される必要があります"); };
    assert_eq!(&library[span], "(list x y)");
    let Err(failure) = first.start_expansion().run_slice(NonZeroUsize::new(64).unwrap())
        else { panic!("先に現れた挿入式で展開が止まる") };
    assert_eq!(failure.element, 1);
    assert_eq!(failure.definition.revision, 31);
    assert_eq!(failure.call.scope().source.revision, 47);
    assert_eq!(&library[failure.related], "(list x y)");
    assert!(matches!(failure.kind, MacroExpansionErrorKind::Expression {
        site: MacroExpressionSite::Insertion { element: 1, insertion: 1 },
        error: MacroArgumentError::Deferred(_),
    }));
    assert!(matches!(first.argument_expression(MacroExpressionSite::Insertion { element: 1, insertion: 2 }),
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
    assert!(empty.start_expression(MacroExpressionSite::Element(0)).is_none());
    assert!(matches!(empty.argument_expression(MacroExpressionSite::Element(0)),
        Err(MacroArgumentError::NoExpression)));
    assert!(calls.next_bound_macro().is_none());
}

#[test]
fn expands_the_bound_arguments_from_the_project_in_one_transition_slices() {
    let library = "(defmacro pick (x y) (list y (syntax (def out (unsyntax x)))))";
    let circuit = "(using nor) (func top (in x) (out out) (expand ::pick x (nor x x)))";
    let project = parse_project_sources(&[
        SourceSnapshot { path: "pick.ncg2m", revision: 31, text: library },
        SourceSnapshot { path: "top.ncg2", revision: 47, text: circuit },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let mut calls = aliases.macro_calls(1, 1).unwrap();
    let bound = calls.next_bound_macro().unwrap().unwrap();
    let mut state = bound.start_expansion();
    let mut completed = None;
    for _ in 0..32 {
        match state.run_slice(NonZeroUsize::MIN) {
            Ok(MacroExpansionSlice::Suspended(next)) => state = next,
            Ok(MacroExpansionSlice::Complete(output)) => {
                completed = Some(output);
                break;
            },
            Err(_) => panic!("マクロ展開が診断を返した"),
        }
    }
    let output = completed.expect("マクロ展開が32遷移以内に完了する");
    let [MacroExpandedElement::Argument(value), MacroExpandedElement::Template { syntax: template, .. }] =
        output.elements() else { panic!("リストの要素が元の順で展開される") };
    assert!(core::ptr::eq(*value, &bound.arguments()[1]));
    let mut inserted = value.walk_syntax();
    let root = value.nodes().start;
    let expected = [
        ArgumentSyntaxToken::Open(root),
        ArgumentSyntaxToken::Atom(root + 1),
        ArgumentSyntaxToken::Atom(root + 2),
        ArgumentSyntaxToken::Atom(root + 3),
        ArgumentSyntaxToken::Close(root),
    ];
    for token in expected {
        assert_eq!(inserted.next(), Some(token));
    }
    assert_eq!(inserted.next(), None);
    assert_eq!(inserted.argument().scope().source.revision, 47);
    assert!(template.parts().iter().any(|item|
        matches!(item, TemplateEmission::Insert(value) if core::ptr::eq(*value, &bound.arguments()[0]))));
    assert_eq!(output.call().scope().source.revision, 47);
    assert_eq!(template.source(), library);
}


#[test]
fn checks_direct_expansion_in_the_callers_original_subtree() {
    use circuitgame2_core::syntax::circuit::{ForbiddenGeneratedHead, GeneratedDefinitionError};
    let library = "(defmacro emit (item ignored) (list item))";
    let circuit = "(using nor) (func top (in x) (out y)
        (expand emit (def y (nor x x)) tail)
        (expand emit (def y (nor (expand emit x) x)) tail))";
    let project = parse_project_sources(&[
        SourceSnapshot { path: "lib.ncg2m", revision: 1, text: library },
        SourceSnapshot { path: "top.ncg2", revision: 5, text: circuit },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let mut calls = aliases.macro_calls(1, 1).unwrap();
    let first = calls.next_bound_macro().unwrap().unwrap();
    let second = calls.next_bound_macro().unwrap().unwrap();
    let fuel = NonZeroUsize::new(32).unwrap();
    let MacroExpansionSlice::Complete(first_output) = first.start_expansion().run_slice(fuel).unwrap()
        else { panic!("最初の展開が完了する必要があります"); };
    let checked = first_output.check_argument_definition(0).unwrap().unwrap();
    assert!(core::ptr::eq(checked.argument(), &first.arguments()[0]));
    assert_eq!(checked.argument().scope().source.revision, 5);
    assert_eq!((checked.argument().scope().file, checked.argument().scope().entry), (1, 1));
    assert_eq!(checked.row().targets.start, first.arguments()[0].nodes().start + 2);
    assert_eq!(checked.row().expression.end, first.arguments()[0].nodes().end);
    assert_eq!(&circuit[checked.row().references[0].span.clone()], "nor");
    assert!(first_output.check_argument_definition(1).is_none());

    let MacroExpansionSlice::Complete(second_output) = second.start_expansion().run_slice(fuel).unwrap()
        else { panic!("次の展開が完了する必要があります"); };
    let failure = second_output.check_argument_definition(0).unwrap().unwrap_err();
    assert!(core::ptr::eq(failure.call, &second));
    assert!(core::ptr::eq(failure.argument, &second.arguments()[0]));
    assert_eq!(failure.element, 0);
    let GeneratedDefinitionError::ForbiddenHead { head: ForbiddenGeneratedHead::Expand, span } = failure.kind
        else { panic!("入れ子の展開を診断する必要があります"); };
    assert_eq!(&circuit[span], "expand");
}
