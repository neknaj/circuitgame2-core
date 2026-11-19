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

#[test]
fn accepts_routine_bodies_with_builtin_forms_and_calls() {
    let source = concat!(
        "(func f (in x) (out y z) ",
        "(def (y z) (::raw (bit x 00) (slice x 0 2) (slice x 0 2 1) ",
        "(concat (field x low) (as ns::Word (raw #xF)) #b1 0 1))) ",
        "(expand ::m () (bit) \"macro argument\")) ",
        "(module m (in x) (out y) (def y (ns::bit))) ",
        "(module-part m (def y (nor x x)))",
    );
    assert_eq!(index_headers(source).unwrap().entries.len(), 3);
}

#[test]
fn reports_malformed_routine_body_items_and_expressions() {
    for (body, kind, text) in [
        ("(call)", HeaderError::ExpectedBodyItem, "call"),
        (
            "(expand \"arg\")",
            HeaderError::ExpectedReference,
            "\"arg\"",
        ),
        ("(def)", HeaderError::ExpectedTarget, ""),
        ("(def () 1)", HeaderError::ExpectedName, ""),
        ("(def (y ns::z) 1)", HeaderError::ExpectedName, "ns::z"),
        ("(def y)", HeaderError::ExpectedExpression, ""),
        ("(def y 00)", HeaderError::ExpectedExpression, "00"),
        ("(def y ns::x)", HeaderError::ExpectedExpression, "ns::x"),
        ("(def y 1 extra)", HeaderError::UnexpectedArgument, "extra"),
        ("(def y ())", HeaderError::ExpectedReference, ""),
        ("(def y (bit))", HeaderError::ExpectedExpression, ""),
        ("(def y (bit x -1))", HeaderError::ExpectedNatural, "-1"),
        ("(def y (slice x 0))", HeaderError::ExpectedNatural, ""),
        (
            "(def y (slice x 0 1 2 3))",
            HeaderError::UnexpectedArgument,
            "3",
        ),
        ("(def y (concat))", HeaderError::ExpectedExpression, ""),
        (
            "(def y (field x ::low))",
            HeaderError::ExpectedName,
            "::low",
        ),
        ("(def y (as 1 x))", HeaderError::ExpectedReference, "1"),
        ("(def y (raw x y))", HeaderError::UnexpectedArgument, "y"),
        (
            "(def y (nor (raw 1) 00))",
            HeaderError::ExpectedExpression,
            "00",
        ),
    ] {
        let source = format!("(module-part m {body})");
        let CircuitFormError::Header { kind: actual, span } = index_headers(&source).unwrap_err()
        else {
            panic!("expected circuit form error for {body:?}");
        };
        assert_eq!(actual, kind, "{body:?}");
        assert_eq!(&source[span.clone()], text, "{body:?}");
        if text.is_empty() {
            assert_eq!(source.as_bytes()[span.start], b')', "{body:?}");
        }
    }
}

#[test]
fn validates_deep_expressions_with_pending_siblings() {
    let depth = 20_000;
    let source = format!(
        "(module-part m (def y {}0{}))",
        "(concat ".repeat(depth),
        " 1)".repeat(depth),
    );
    assert_eq!(index_headers(&source).unwrap().entries.len(), 1);
}
