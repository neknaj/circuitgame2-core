use circuitgame2_syntax::circuit::{
    CircuitFormError, ExpressionReferenceKind, HeaderError, index_expression_references,
};

#[test]
fn projects_only_call_and_cast_references_in_source_order() {
    let text = concat!(
        "; バイト範囲の確認\n",
        "(concat (ns::outer (as ::types::T (field (nor signal signal) f))) ",
        "        (raw (::raw signal)) (slice (inner signal) 0 1)) ",
        "(zero-args)"
    );
    let references = index_expression_references(text).unwrap();
    use ExpressionReferenceKind::{Callee, CastType};
    let spelled: Vec<_> = references
        .iter()
        .map(|item| (item.kind, &text[item.span.clone()]))
        .collect();
    assert_eq!(
        spelled,
        [
            (Callee, "ns::outer"),
            (CastType, "::types::T"),
            (Callee, "nor"),
            (Callee, "::raw"),
            (Callee, "inner"),
            (Callee, "zero-args"),
        ]
    );
    assert!(
        references
            .windows(2)
            .all(|pair| pair[0].form < pair[1].form && pair[0].span.end < pair[1].span.start)
    );
}

#[test]
fn rejects_invalid_expressions_at_the_first_grammar_violation() {
    let text = "(concat (call) (as Type) (field))";
    let CircuitFormError::Header { kind, span } = index_expression_references(text).unwrap_err()
    else {
        panic!("expected an expression error");
    };
    assert_eq!(kind, HeaderError::ExpectedExpression);
    let close = text.find("Type)").unwrap() + "Type".len();
    assert_eq!(span, close..close);
    assert!(matches!(
        index_expression_references("(as Type"),
        Err(CircuitFormError::Syntax(_))
    ));
}
