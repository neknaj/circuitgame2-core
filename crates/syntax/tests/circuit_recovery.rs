use circuitgame2_syntax::circuit::{
    CircuitRecovery, Head, HeaderError, RecoveredFormOutcome, index_headers, recover_circuit_forms,
};
use circuitgame2_syntax::{Form, Repair};

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
    let CircuitRecovery::WithSyntaxRepairs(recovered) =
        recover_circuit_forms("(namespace app (export visible)")
    else {
        panic!("expected tentative scope after a missing delimiter");
    };
    assert!(matches!(
        recovered.repairs.as_slice(),
        [Repair::InsertedClose { list: 0, .. }]
    ));

    let CircuitRecovery::WithSyntaxRepairs(recovered) = recover_circuit_forms("\"open (using nor)")
    else {
        panic!("expected a skipped unterminated string");
    };
    assert!(recovered.forms.is_empty());
    assert!(matches!(
        recovered.repairs.as_slice(),
        [Repair::Skipped { .. }]
    ));
}
