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
