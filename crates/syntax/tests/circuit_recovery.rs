use circuitgame2_syntax::circuit::{
    CircuitFormError, CircuitRecovery, Head, HeaderError, RecoveredFormOutcome,
    RecoveredNamePosition, index_headers, recover_circuit_forms, recover_circuit_names,
};
use circuitgame2_syntax::{Form, Repair};

#[test]
fn recovered_names_use_original_file_ranges_and_skip_repaired_scopes() {
    let source = concat!(
        "; 日本語と絵文字 🐈\n",
        "(using nor) ) ",
        "(namespace app (bad) (func good (in) (out y) (def y 0))) ",
        "(namespace unfinished (func tentative (in) (out y) (def y 0))",
    );
    let recovered = recover_circuit_names(source);
    let position = |fragment, item| RecoveredNamePosition::Original { fragment, item };
    let name = recovered.name_at(position(1, 2)).unwrap();
    assert_eq!(name.head, Head::Func);
    assert_eq!(name.name.word, "good");
    assert_eq!(&source[name.name.span], "good");
    let namespace = name.namespace.unwrap();
    assert_eq!(namespace.word, "app");
    assert_eq!(&source[namespace.span], "app");
    assert_eq!(recovered.name_at(position(0, 0)), None);
    assert_eq!(recovered.name_at(position(1, 1)), None);
    assert_eq!(recovered.name_at(position(2, 1)), None);
    assert_eq!(recovered.name_at(RecoveredNamePosition::File(2)), None);
}

#[test]
fn continues_within_a_namespace_and_after_its_closing_delimiter() {
    let text = concat!(
        "; UTF-8 の前置き\n",
        "(unknown) (namespace app (bad) (export valid)) (using nor)"
    );
    let CircuitRecovery::Inspected { forms, checked } = recover_circuit_forms(text) else {
        panic!("expected recovered circuit forms");
    };
    assert_eq!(checked.len(), 5);
    for (item, expected) in [(&checked[0], "(unknown)"), (&checked[2], "(bad)")] {
        let RecoveredFormOutcome::Rejected {
            kind,
            span,
            skipped,
        } = &item.outcome
        else {
            panic!("expected a rejected form");
        };
        assert_eq!(*kind, HeaderError::UnknownHead);
        assert_eq!(&text[skipped.clone()], expected);
        assert_eq!(&text[span.clone()], &expected[1..expected.len() - 1]);
    }
    assert!(matches!(
        checked[1].outcome,
        RecoveredFormOutcome::Valid(Head::Namespace)
    ));
    assert_eq!(checked[2].namespace, Some(checked[1].form));
    assert_eq!(checked[3].namespace, Some(checked[1].form));
    assert!(matches!(
        checked[3].outcome,
        RecoveredFormOutcome::Valid(Head::Export)
    ));
    assert_eq!(checked[4].namespace, None);
    assert!(matches!(
        checked[4].outcome,
        RecoveredFormOutcome::Valid(Head::Using)
    ));
    assert!(matches!(forms[checked[4].form], Form::List { .. }));
}

#[test]
fn skips_the_contents_of_an_invalid_namespace_header() {
    let text = "(namespace 1 (export secret)) (func f (in) (out y) (def y 0))";
    let CircuitRecovery::Inspected { checked, .. } = recover_circuit_forms(text) else {
        panic!("expected recovered circuit forms");
    };
    assert_eq!(checked.len(), 2);
    assert!(matches!(
        checked[0].outcome,
        RecoveredFormOutcome::Rejected {
            kind: HeaderError::ExpectedNamespacePath,
            ..
        }
    ));
    assert!(matches!(
        checked[1].outcome,
        RecoveredFormOutcome::Valid(Head::Func)
    ));
    assert_eq!(checked[1].namespace, None);
}

#[test]
fn valid_input_returns_the_same_index_as_the_strict_parser() {
    for text in [
        "",
        "(using nor) (namespace app (func f (in) (out y) (def y 0)))",
    ] {
        let CircuitRecovery::Complete(index) = recover_circuit_forms(text) else {
            panic!("expected a complete circuit index");
        };
        assert_eq!(index, index_headers(text).unwrap());
    }
}

#[test]
fn keeps_s_expression_repairs_separate_from_circuit_diagnostics() {
    let CircuitRecovery::WithSyntaxRepairs {
        recovered,
        original,
    } = recover_circuit_forms("(namespace app (export visible)")
    else {
        panic!("expected tentative scope after a missing delimiter");
    };
    assert!(matches!(
        recovered.repairs.as_slice(),
        [Repair::InsertedClose { list: 0, .. }]
    ));
    assert!(original.is_empty());

    let CircuitRecovery::WithSyntaxRepairs {
        recovered,
        original,
    } = recover_circuit_forms("\"open (using nor)")
    else {
        panic!("expected a skipped unterminated string");
    };
    assert!(recovered.forms.is_empty());
    assert!(original.is_empty());
    assert!(matches!(
        recovered.repairs.as_slice(),
        [Repair::Skipped { .. }]
    ));
}

#[test]
fn checks_unrepaired_roots_before_and_after_repairs_in_source_order() {
    let source = concat!(
        "; 日本語の前置き\n",
        "(using nor) ) ",
        "(using #b102 nor) ",
        "(namespace app (export visible)) ",
        "(namespace unfinished (export tentative)",
    );
    let CircuitRecovery::WithSyntaxRepairs {
        recovered,
        original,
    } = recover_circuit_forms(source)
    else {
        panic!("expected recovered S expressions and original lists");
    };
    assert_eq!(recovered.original_lists.len(), 2);
    let [Some(first), Some(second)] = original.as_slice() else {
        panic!("expected exactly two independent lists");
    };
    assert_eq!(&source[first.span.clone()], "(using nor)");
    assert_eq!(
        &source[second.span.clone()],
        "(namespace app (export visible))"
    );
    assert!(first.span.end < second.span.start);
    assert!(matches!(
        first.checked[0].outcome,
        RecoveredFormOutcome::Valid(Head::Using)
    ));
    assert!(matches!(
        second.checked[0].outcome,
        RecoveredFormOutcome::Valid(Head::Namespace)
    ));
    assert!(matches!(
        second.checked[1].outcome,
        RecoveredFormOutcome::Valid(Head::Export)
    ));
    assert_eq!(second.checked[1].namespace, Some(second.checked[0].form));
    assert!(matches!(first.source_diagnostics(), [None]));
    assert!(matches!(second.source_diagnostics(), [None, None]));
    assert!(
        recovered
            .repairs
            .iter()
            .any(|repair| matches!(repair, Repair::InsertedClose { .. }))
    );
}

#[test]
fn identifies_primary_and_related_positions_in_the_original_fragment() {
    let source = "; 診断の前置き\n) (test demo (reset) (case)) (using)";
    let CircuitRecovery::WithSyntaxRepairs { original, .. } = recover_circuit_forms(source) else {
        panic!("expected a skipped right parenthesis");
    };
    let [Some(test), Some(using)] = original.as_slice() else {
        panic!("expected independent diagnostics for both lists");
    };
    let [
        Some(CircuitFormError::Header {
            kind:
                HeaderError::MixedTestItems {
                    first_head: (start, end),
                },
            span,
        }),
    ] = test.source_diagnostics()
    else {
        panic!("expected mixed test items");
    };
    assert_eq!(&source[*start..*end], "reset");
    assert_eq!(&source[span.clone()], "case");
    let [Some(CircuitFormError::Header { span, .. })] = using.source_diagnostics() else {
        panic!("expected a missing argument");
    };
    assert_eq!(span.start, span.end);
    assert_eq!(span.start, using.span.end - 1);
}

#[test]
fn excludes_the_root_that_needed_an_inserted_separator() {
    let source = "(using a\"b\") (using nor)";
    let CircuitRecovery::WithSyntaxRepairs {
        recovered,
        original,
    } = recover_circuit_forms(source)
    else {
        panic!("expected recovery after a missing separator");
    };
    assert!(matches!(
        recovered.repairs.as_slice(),
        [Repair::InsertedSeparator { .. }]
    ));
    let [Some(list)] = original.as_slice() else {
        panic!("expected only the following root to be checked");
    };
    assert_eq!(&source[list.span.clone()], "(using nor)");
    assert!(matches!(
        list.checked[0].outcome,
        RecoveredFormOutcome::Valid(Head::Using)
    ));
}
