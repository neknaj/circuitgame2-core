use circuitgame2_syntax::Form;
use circuitgame2_syntax::circuit::{
    CircuitFormError, ExpressionReferenceKind, Head, index_definition_references, index_headers,
};

#[test]
fn indexes_definition_expressions_in_their_own_namespace_blocks() {
    let source = concat!(
        "; 断片のスコープと元ソースの範囲を検査する\n",
        "(namespace app ",
        "  (module M (in x) (out y) ",
        "    (def y (drive x)) ",
        "    (expand ::meta::emit (def y (phantom x)) (as Ignored x)))) ",
        "(namespace app ",
        "  (module-part M ",
        "    (def (a b) (as ::types::Pair (lib::split x))) ",
        "    (def c b))) ",
        "(func root (in x) (out y) (def y (finish x)))",
    );
    let index = index_definition_references(source).unwrap();
    let entries = &index.syntax.entries;
    let rows = &index.definitions_by_entry;
    assert_eq!(entries.len(), rows.len());
    assert_eq!(
        entries.iter().map(|entry| entry.head).collect::<Vec<_>>(),
        [
            Head::Namespace,
            Head::Module,
            Head::Namespace,
            Head::ModulePart,
            Head::Func,
        ]
    );
    assert_eq!(entries[1].namespace, Some(entries[0].form));
    assert_eq!(entries[3].namespace, Some(entries[2].form));
    assert_eq!(entries[4].namespace, None);
    assert!(rows[0].is_empty() && rows[2].is_empty());
    assert_eq!(rows[1].len(), 1);
    assert_eq!(rows[3].len(), 2);
    assert!(rows[3][1].references.is_empty());
    assert_eq!(rows[4].len(), 1);
    for (row, expected) in [
        (&rows[1][0], "(drive x)"),
        (&rows[3][0], "(as ::types::Pair (lib::split x))"),
        (&rows[4][0], "(finish x)"),
    ] {
        let Form::List { span, end } = &index.syntax.forms[row.expression.start] else {
            panic!("expected an expression list");
        };
        assert_eq!(&source[span.clone()], expected);
        assert_eq!(*end, row.expression.end);
    }
    let words: Vec<_> = rows
        .iter()
        .flatten()
        .flat_map(|definition| &definition.references)
        .map(|reference| (reference.kind, &source[reference.span.clone()]))
        .collect();
    use ExpressionReferenceKind::{Callee, CastType};
    assert_eq!(
        words,
        [
            (Callee, "drive"),
            (CastType, "::types::Pair"),
            (Callee, "lib::split"),
            (Callee, "finish"),
        ]
    );
}

#[test]
fn preserves_the_strict_indexers_error_priority() {
    for source in [
        "(unknown) (",
        "(unknown) (module M (in) (out y) (def y (as Type)))",
        "(module M (in) (out y) (def y (as Type)))",
    ] {
        let expected = index_headers(source).unwrap_err();
        let actual = index_definition_references(source).unwrap_err();
        match (expected, actual) {
            (CircuitFormError::Syntax(left), CircuitFormError::Syntax(right)) => {
                assert_eq!(left, right);
            }
            (
                CircuitFormError::Header {
                    kind: left,
                    span: left_span,
                },
                CircuitFormError::Header {
                    kind: right,
                    span: right_span,
                },
            ) => {
                assert_eq!(left, right);
                assert_eq!(left_span, right_span);
            }
            errors => panic!("different error variants: {errors:?}"),
        }
    }
}
