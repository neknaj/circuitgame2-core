use circuitgame2_core::syntax::circuit::{CircuitFormError, Head, HeaderError, index_headers};

#[test]
fn indexes_direct_headers_and_namespace_members() {
    let source = "(using nor) (namespace lib::gates (use ::other alias) (export reset) (module reset (in) (out reset))) (test reset)";
    let indexed = index_headers(source).unwrap();
    let heads: Vec<_> = indexed
        .entries
        .iter()
        .map(|entry| (entry.head, entry.namespace))
        .collect();
    let namespace = indexed.entries[1].form;
    assert_eq!(
        heads,
        [
            (Head::Using, None),
            (Head::Namespace, None),
            (Head::Use, Some(namespace)),
            (Head::Export, Some(namespace)),
            (Head::Module, Some(namespace)),
            (Head::Test, None),
        ]
    );
}

#[test]
fn rejects_invalid_and_misplaced_headers() {
    for (source, kind, text) in [
        ("func", HeaderError::ExpectedList, "func"),
        ("()", HeaderError::ExpectedHead, ""),
        ("(::func)", HeaderError::ExpectedHead, "::func"),
        ("(Func)", HeaderError::UnknownHead, "Func"),
        ("(using and)", HeaderError::ExpectedNor, "and"),
        (
            "(using nor extra)",
            HeaderError::UnexpectedArgument,
            "extra",
        ),
        ("(namespace ::n)", HeaderError::ExpectedNamespacePath, "::n"),
        (
            "(namespace n (using))",
            HeaderError::MisplacedHead(Head::Using),
            "using",
        ),
        (
            "(namespace n (namespace m))",
            HeaderError::MisplacedHead(Head::Namespace),
            "namespace",
        ),
        ("(use n alias)", HeaderError::ExpectedAbsolutePath, "n"),
        (
            "(export name (other))",
            HeaderError::ExpectedName,
            "(other)",
        ),
    ] {
        let CircuitFormError::Header { kind: actual, span } = index_headers(source).unwrap_err()
        else {
            panic!("expected header error for {source:?}");
        };
        assert_eq!(actual, kind, "{source:?}");
        assert_eq!(&source[span], text, "{source:?}");
    }
}

#[test]
fn validates_routine_and_storage_signatures() {
    let source = concat!(
        "(func f (in (x (bits 0008)) plain) (out (y ::ns::Word))) ",
        "(module-part m) (latch l (width 0)) ",
        "(memory mem (address 16) (data (bits 8))) ",
        "(struct Pair (width 16) (lo (bits 8) (at 0)) (hi ns::Byte (at 8))) ",
        "(test ::ns::f)"
    );
    assert_eq!(index_headers(source).unwrap().entries.len(), 6);
}

#[test]
fn reports_malformed_declaration_arguments() {
    use circuitgame2_core::syntax::circuit::Clause;

    for (source, kind, text) in [
        (
            "(module ::m (in) (out x))",
            HeaderError::ExpectedName,
            "::m",
        ),
        ("(func f (in) (out))", HeaderError::ExpectedPort, ""),
        (
            "(func f (out x) (in y))",
            HeaderError::ExpectedClause(Clause::In),
            "out",
        ),
        (
            "(func f (in (x (bits -1))) (out y))",
            HeaderError::ExpectedNatural,
            "-1",
        ),
        (
            "(func f (in (x 8)) (out y))",
            HeaderError::ExpectedType,
            "8",
        ),
        (
            "(latch l (width 1) extra)",
            HeaderError::UnexpectedArgument,
            "extra",
        ),
        (
            "(memory m (address 8) (width 1))",
            HeaderError::ExpectedClause(Clause::Data),
            "width",
        ),
        (
            "(struct s (width 8) (f (bits 8) (at 0) extra))",
            HeaderError::UnexpectedArgument,
            "extra",
        ),
        ("(test #b1)", HeaderError::ExpectedReference, "#b1"),
    ] {
        let CircuitFormError::Header { kind: actual, span } = index_headers(source).unwrap_err()
        else {
            panic!("expected header error for {source:?}");
        };
        assert_eq!(actual, kind, "{source:?}");
        assert_eq!(&source[span], text, "{source:?}");
    }
}
