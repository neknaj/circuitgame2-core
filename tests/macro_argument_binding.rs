use std::num::NonZeroUsize;
use circuitgame2_core::ncg2m::call_evaluation::macro_expansion::{
    MacroExpandedElement, MacroExpansionErrorKind, MacroExpansionSlice,
};
use circuitgame2_core::ncg2m::call_evaluation::macro_syntax::{
    ArgumentSyntaxToken, MacroSyntaxOrigin, MacroTemplateSyntaxStep,
};
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
    let library = "(defmacro pick (x y) (list y (syntax (def out (unsyntax y)))))";
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
        matches!(item, TemplateEmission::Insert(value) if core::ptr::eq(*value, &bound.arguments()[1]))));
    assert_eq!(output.call().scope().source.revision, 47);
    assert_eq!(template.source(), library);

    assert!(output.template_syntax(0).is_none());
    let mut syntax = output.template_syntax(1).unwrap();
    let mut completed = false;
    let mut observed = Vec::new();
    for _ in 0..32 {
        let MacroTemplateSyntaxStep::Continue { event, next } = syntax.step().unwrap() else {
            completed = true;
            break;
        };
        syntax = next;
        let Some(event) = event else { continue; };
        let source = event.origin.source();
        match event.origin {
            MacroSyntaxOrigin::Template(call) => assert!(core::ptr::eq(call, &bound)),
            MacroSyntaxOrigin::Argument(argument) =>
                assert!(core::ptr::eq(argument, &bound.arguments()[1])),
        }
        let (tag, word) = match event.token {
            ArgumentSyntaxToken::Open(_) => ('(', ""),
            ArgumentSyntaxToken::Close(_) => (')', ""),
            ArgumentSyntaxToken::Atom(at) => {
                let Form::Atom { span, .. } = &event.origin.forms()[at] else { unreachable!() };
                ('a', &source.text()[span.clone()])
            },
        };
        observed.push((source.revision, tag, word));
    }
    assert!(completed);
    assert_eq!(observed, [
        (31, '(', ""), (31, 'a', "def"), (31, 'a', "out"),
        (47, '(', ""), (47, 'a', "nor"), (47, 'a', "x"), (47, 'a', "x"), (47, ')', ""),
        (31, ')', ""),
    ]);
    assert!(output.check_template_definition(0).is_none());
    let checked = output.check_template_definition(1).unwrap().unwrap();
    let row = checked.row();
    assert_eq!(row.targets.len(), 1);
    assert_eq!(row.signals.len(), 2);
    let target = checked.origin(row.targets.start).unwrap();
    assert!(matches!(target.origin, MacroSyntaxOrigin::Template(call) if core::ptr::eq(call, &bound)));
    let reference = checked.origin(row.references[0].form).unwrap();
    assert!(matches!(reference.origin, MacroSyntaxOrigin::Argument(argument)
        if core::ptr::eq(argument, &bound.arguments()[1])));
    assert_eq!(&checked.text()[row.references[0].span.clone()], "nor");
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


#[test]
fn restores_the_source_of_a_template_definition_diagnostic() {
    use circuitgame2_core::ncg2m::call_evaluation::macro_syntax::TemplateDefinitionError;
    use circuitgame2_core::syntax::circuit::{ForbiddenGeneratedHead, GeneratedDefinitionError, HeaderError};
    let library = "(defmacro emit (expr) (list (syntax (def y (unsyntax expr)))))
        (defmacro missing () (list (syntax (def y))))";
    let circuit = "(using nor) (func top (in x) (out y)
        (expand emit (expand emit x)) (expand missing))";
    let project = parse_project_sources(&[
        SourceSnapshot { path: "lib.ncg2m", revision: 10, text: library },
        SourceSnapshot { path: "top.ncg2", revision: 15, text: circuit },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let mut calls = aliases.macro_calls(1, 1).unwrap();
    let bound = calls.next_bound_macro().unwrap().unwrap();
    let fuel = NonZeroUsize::new(64).unwrap();
    let MacroExpansionSlice::Complete(output) = bound.start_expansion().run_slice(fuel).unwrap()
        else { panic!("展開が完了する必要があります"); };
    let failure = output.check_template_definition(0).unwrap().err().unwrap();
    assert!(core::ptr::eq(failure.call, &bound));
    let TemplateDefinitionError::Definition {
        kind: GeneratedDefinitionError::ForbiddenHead { head: ForbiddenGeneratedHead::Expand, .. },
        related: Some(related),
    } = failure.error else { panic!("禁止した先頭語の元範囲が必要です"); };
    assert_eq!(related.origin.source().revision, 15);
    assert!(matches!(related.origin, MacroSyntaxOrigin::Argument(argument)
        if core::ptr::eq(argument, &bound.arguments()[0])));
    let ArgumentSyntaxToken::Atom(at) = related.token else { unreachable!() };
    let Form::Atom { span, .. } = &related.origin.forms()[at] else { unreachable!() };
    assert_eq!(&circuit[span.clone()], "expand");

    let bound = calls.next_bound_macro().unwrap().unwrap();
    let MacroExpansionSlice::Complete(output) = bound.start_expansion().run_slice(fuel).unwrap()
        else { panic!("展開が完了する必要があります"); };
    let failure = output.check_template_definition(0).unwrap().err().unwrap();
    let TemplateDefinitionError::Definition {
        kind: GeneratedDefinitionError::Invalid { kind: HeaderError::ExpectedExpression, span },
        related: Some(related),
    } = failure.error else { panic!("右辺の欠落を元のリストに対応付ける必要があります"); };
    assert!(span.is_empty());
    assert_eq!(related.origin.source().revision, 10);
    assert!(matches!(related.origin, MacroSyntaxOrigin::Template(call) if core::ptr::eq(call, &bound)));
    let ArgumentSyntaxToken::Open(at) = related.token else { unreachable!() };
    let Form::List { span, .. } = &related.origin.forms()[at] else { unreachable!() };
    assert_eq!(&library[span.clone()], "(def y)");
}


#[test]
fn expanded_wiring_keeps_temporary_names_distinct_from_caller_ports() {
    use circuitgame2_core::project::GeneratedWiringError;
    let library = "(defmacro connect (output input)
        (list (syntax (def tmp (unsyntax input)))
              (syntax (def (unsyntax output) tmp))))
        (defmacro unbound (output) (list (syntax (def (unsyntax output) tmp))))";
    let circuit = "(using nor)
        (func top (in (x (bits 2)) tmp) (out (y (bits 2)) z)
          (expand connect y x)
          (expand connect z tmp))
        (func bad (in (x (bits 2)) tmp) (out y)
          (expand connect y x))
        (func missing (in tmp) (out y)
          (expand unbound y))";
    let project = parse_project_sources(&[
        SourceSnapshot { path: "lib.ncg2m", revision: 63, text: library },
        SourceSnapshot { path: "top.ncg2", revision: 72, text: circuit },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let fuel = NonZeroUsize::new(128).unwrap();
    let checked = aliases.check_generated_alias_func(1, 1, 16, fuel).unwrap().unwrap();
    let [first, first_output, second, second_output] = checked.aliases() else {
        panic!("2件の展開がそれぞれ2件の結線を返す");
    };
    assert!(first.target().key().same(&first_output.reference().key()));
    assert!(second.target().key().same(&second_output.reference().key()));
    assert!(!first.target().key().same(&second.target().key()));
    assert!(!second.target().key().same(&second.reference().key()));
    assert_eq!(&circuit[second.reference().location().span.clone()], "tmp");
    assert_eq!(first.target().location().source.revision, 63);
    assert_eq!(second.reference().location().source.revision, 72);
    let wires = checked.bit_func().lower_bit_func(16).unwrap();
    let bits = [false, true, true];
    assert_eq!(wires.netlist().evaluate(&bits).unwrap(), bits);

    let Err(GeneratedWiringError::OutputWidth { site, expected: 1, actual: 2 }) =
        aliases.check_generated_alias_func(1, 2, 16, fuel) else { panic!("出力幅の不一致を診断する"); };
    assert_eq!(&circuit[site.span], "y");

    let Err(GeneratedWiringError::Unavailable(site)) = aliases.check_generated_alias_func(1, 3, 16, fuel)
        else { panic!("テンプレートの未束縛名が呼び出し側の入力に結び付いてはならない"); };
    assert_eq!(site.source.revision, 63);
    assert_eq!(&library[site.span], "tmp");
}


#[test]
fn wires_nor_and_ordinary_definitions_in_their_expanded_body_order() {
    use circuitgame2_core::project::ExpandedFuncWiringError;
    let library = "(defmacro invert (out input)
        (list (syntax (def tmp (nor (unsyntax input) 0)))
              (syntax (def (unsyntax out) tmp))))";
    let circuit = "(using nor)
        (func top (in x tmp) (out y z)
          (def seed (nor x 0))
          (expand invert y seed)
          (def z (nor y tmp)))
        (func wide (in (x (bits 2))) (out y) (expand invert y x))
        (func forward (in x) (out y) (expand invert y later) (def later x))";
    let project = parse_project_sources(&[
        SourceSnapshot { path: "lib.ncg2m", revision: 83, text: library },
        SourceSnapshot { path: "top.ncg2", revision: 94, text: circuit },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let fuel = NonZeroUsize::new(128).unwrap();
    let checked = aliases.check_expanded_bit_func(1, 1, 16, fuel).unwrap().unwrap();
    let lowered = checked.lower_bit_func(16).unwrap();
    assert_eq!(lowered.netlist().gates.len(), 3);
    for x in [false, true] {
        for other in [false, true] {
            assert_eq!(lowered.netlist().evaluate(&[x, other]).unwrap(), [x, !(x || other)]);
        }
    }
    let Err(ExpandedFuncWiringError::Generated { call, cause }) =
        aliases.check_expanded_bit_func(1, 2, 16, fuel)
        else { panic!("生成した NOR の入力幅違反には展開呼び出しの位置が必要です"); };
    assert_eq!((&circuit[call.span], call.source.revision), ("(expand invert y x)", 94));
    let ExpandedFuncWiringError::NorInputWidth { reference, width: 2 } = *cause
        else { panic!("基底 NOR の入力幅を検査する"); };
    assert_eq!((&circuit[reference.span], reference.source.revision), ("x", 94));
    let Err(ExpandedFuncWiringError::Generated { call, cause }) =
        aliases.check_expanded_bit_func(1, 3, 16, fuel)
        else { panic!("前方参照には展開呼び出しの位置が必要です"); };
    assert_eq!((&circuit[call.span], call.source.revision), ("(expand invert y later)", 94));
    let ExpandedFuncWiringError::UnavailableDefinition { reference, target } = *cause
        else { panic!("後続の通常定義を、先行する展開中の参照から使うことを拒否する"); };
    assert_eq!((&circuit[reference.span.clone()], &circuit[target.span.clone()]), ("later", "later"));
    assert!(reference.span.start < target.span.start);
}


#[test]
fn resolves_nor_in_the_scope_of_the_expression_origin() {
    use circuitgame2_core::project::ExpandedFuncWiringError;
    let library = "(namespace macros
        (export literal supplied)
        (defmacro literal (out input) (list (syntax (def (unsyntax out) (nor (unsyntax input) 0)))))
        (defmacro supplied (out expression) (list (syntax (def (unsyntax out) (unsyntax expression))))))";
    let circuit = "(using nor)
        (namespace gates (export nor) (func nor (in a b) (out y) (def y a)))
        (namespace app
          (use ::gates::nor nor)
          (func from-template (in x) (out y) (expand ::macros::literal y x))
          (func from-argument (in x) (out y) (expand ::macros::supplied y (nor x 0))))";
    let project = parse_project_sources(&[
        SourceSnapshot { path: "lib.ncg2m", revision: 89, text: library },
        SourceSnapshot { path: "top.ncg2", revision: 95, text: circuit },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let entries = aliases.targets().project().indexes();
    let circuitgame2_core::project::ProjectSourceIndex::Circuit(index) = &entries[1] else {
        panic!("回路索引が必要です");
    };
    let entry = |name: &str| {
        let form = index.names.iter().find(|item| item.name.word == name).unwrap().form;
        index.syntax.entries.iter().position(|item| item.form == form).unwrap()
    };
    let fuel = NonZeroUsize::new(128).unwrap();
    let checked = aliases.check_expanded_bit_func(1, entry("from-template"), 16, fuel).unwrap().unwrap();
    assert_eq!(checked.lower_bit_func(16).unwrap().netlist().evaluate(&[false]).unwrap(), [true]);
    let Err(ExpandedFuncWiringError::Generated { call, cause }) =
        aliases.check_expanded_bit_func(1, entry("from-argument"), 16, fuel)
        else { panic!("生成した呼び出しの診断に元の展開位置が必要です"); };
    assert_eq!((&circuit[call.span], call.source.revision), ("(expand ::macros::supplied y (nor x 0))", 95));
    let ExpandedFuncWiringError::NorResolvesToFunction { callee, declaration } = *cause
        else { panic!("呼び出し側の nor 別名に解決する"); };
    assert_eq!((&circuit[callee.span], callee.source.revision), ("nor", 95));
    assert_eq!((&circuit[declaration.name.span], declaration.name.source.revision), ("nor", 95));
}


#[test]
fn shared_template_diagnostics_identify_the_failing_expansion() {
    use circuitgame2_core::project::ExpandedFuncWiringError;
    let library = "(defmacro invert (out input)
        (list (syntax (def tmp (unsyntax input)))
              (syntax (def (unsyntax out) (nor tmp 0)))))
        (defmacro copy (out input)
          (list (syntax (def (unsyntax out) (unsyntax input)))))";
    let circuit = "(using nor)
        (func good (in a b) (out y z)
          (expand invert y a)
          (expand invert z b))
        (func bad-second (in one (wide (bits 2))) (out y z)
          (expand invert y one)
          (expand invert z wide))
        (func bad-first (in one (wide (bits 2))) (out y z)
          (expand invert y wide)
          (expand invert z one))
        (func ordinary (in (wide (bits 2))) (out y)
          (def y (nor wide 0)))
        (func output-width (in (wide (bits 2))) (out y)
          (expand copy y wide))";
    let project = parse_project_sources(&[
        SourceSnapshot { path: "shared.ncg2m", revision: 111, text: library },
        SourceSnapshot { path: "top.ncg2", revision: 222, text: circuit },
    ]).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let fuel = NonZeroUsize::new(128).unwrap();
    let checked = aliases.check_expanded_bit_func(1, 1, 16, fuel).unwrap().unwrap();
    let lowered = checked.lower_bit_func(16).unwrap();
    assert_eq!(lowered.netlist().gates.len(), 2);
    assert_eq!(lowered.netlist().evaluate(&[true, false]).unwrap(), [false, true]);

    let cause_at = |entry, expected_call| {
        let Err(ExpandedFuncWiringError::Generated { call, cause }) =
            aliases.check_expanded_bit_func(1, entry, 16, fuel)
            else { panic!("失敗した展開を特定できる診断が必要です"); };
        assert_eq!((&circuit[call.span], call.source.revision), (expected_call, 222));
        let ExpandedFuncWiringError::NorInputWidth { reference, width: 2 } = *cause
            else { panic!("テンプレートの NOR に幅の診断が必要です"); };
        assert_eq!((&library[reference.span.clone()], reference.source.revision), ("tmp", 111));
        reference.span
    };
    assert_eq!(
        cause_at(2, "(expand invert z wide)"),
        cause_at(3, "(expand invert y wide)"),
    );
    let Err(ExpandedFuncWiringError::NorInputWidth { reference, width: 2 }) =
        aliases.check_expanded_bit_func(1, 4, 16, fuel)
        else { panic!("通常の定義では右辺そのものの位置を診断する"); };
    assert_eq!((&circuit[reference.span], reference.source.revision), ("wide", 222));

    let Err(ExpandedFuncWiringError::Generated { call, cause }) =
        aliases.check_expanded_bit_func(1, 5, 16, fuel)
        else { panic!("生成した駆動元に由来する出力幅違反には展開位置が必要です"); };
    assert_eq!(&circuit[call.span.clone()], "(expand copy y wide)");
    let ExpandedFuncWiringError::OutputWidthFromDefinition { target, output, expected: 1, actual: 2 } = *cause
        else { panic!("生成定義と出力宣言の両方の位置が必要です"); };
    assert_eq!((&circuit[target.span.clone()], &circuit[output.span.clone()]), ("y", "y"));
    assert!(output.span.start < call.span.start && call.span.contains(&target.span.start));
}
