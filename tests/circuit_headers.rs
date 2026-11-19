use circuitgame2_core::syntax::circuit::{CircuitFormError, Head, HeaderError, index_headers};

#[test]
fn indexes_direct_headers_and_namespace_members() {
    let source = "(using nor) (namespace lib::gates (use ::other alias) (export reset) (module reset (in) (out reset))) (test reset (reset))";
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
fn reports_head_errors_with_exact_ranges_and_preserves_validation_order() {
    for (source, kind, text) in [
        ("; 見出し\n()", HeaderError::ExpectedHead, ")"),
        ("(() x)", HeaderError::ExpectedHead, "()"),
        ("(using and) (unknown)", HeaderError::ExpectedNor, "and"),
    ] {
        let CircuitFormError::Header { kind: actual, span } = index_headers(source).unwrap_err()
        else {
            panic!("expected header error for {source:?}");
        };
        let start = source.find(text).unwrap();
        let end = if text == ")" {
            start
        } else {
            start + text.len()
        };
        assert_eq!(actual, kind, "{source:?}");
        assert_eq!(span, start..end, "{source:?}");
    }
}

#[test]
fn reports_the_first_invalid_or_missing_directive_argument() {
    for (source, expected) in [
        ("(using)", HeaderError::ExpectedNor),
        ("(namespace)", HeaderError::ExpectedNamespacePath),
        ("(use)", HeaderError::ExpectedAbsolutePath),
        ("(use ::a)", HeaderError::ExpectedName),
        ("(export)", HeaderError::ExpectedName),
    ] {
        let closing = source.len() - 1;
        assert_eq!(
            index_headers(source),
            Err(CircuitFormError::Header {
                kind: expected,
                span: closing..closing
            }),
            "{source:?}",
        );
    }
    for (source, kind, text) in [
        ("(using NOR extra)", HeaderError::ExpectedNor, "NOR"),
        (
            "(use a (bad) extra)",
            HeaderError::ExpectedAbsolutePath,
            "a",
        ),
        ("(use ::a (bad) extra)", HeaderError::ExpectedName, "(bad)"),
        (
            "(use ::a alias (extra))",
            HeaderError::UnexpectedArgument,
            "(extra)",
        ),
        ("(export a (bad) b)", HeaderError::ExpectedName, "(bad)"),
        (
            "(namespace ::a (using))",
            HeaderError::ExpectedNamespacePath,
            "::a",
        ),
    ] {
        let start = source.find(text).unwrap();
        assert_eq!(
            index_headers(source),
            Err(CircuitFormError::Header {
                kind,
                span: start..start + text.len()
            }),
            "{source:?}",
        );
    }
}

#[test]
fn validates_routine_and_storage_signatures() {
    let source = concat!(
        "(func f (in (x (bits 0008)) plain) (out (y ::ns::Word))) ",
        "(module-part m) (latch l (width 0)) ",
        "(memory mem (address 16) (data (bits 8))) ",
        "(struct Pair (width 16) (lo (bits 8) (at 0)) (hi ns::Byte (at 8))) ",
        "(test ::ns::f (case (in) (expect)))"
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

#[test]
fn accepts_test_cases_and_action_sequences() {
    let source = concat!(
        "(test ::gates::f ",
        "(case (in 0 1 #b01 (as ::Word #xF)) (expect any (as Word 0) #b1)) ",
        "(case (in) (expect))) ",
        "(test device (reset) (drive) (drive (as n::Word 1)) (tick 0) (tick 0012) ",
        "(expect any 0) (expect))",
    );
    assert_eq!(index_headers(source).unwrap().entries.len(), 2);
}

#[test]
fn reports_test_syntax_errors_at_the_offending_element_or_insertion_point() {
    use circuitgame2_core::syntax::circuit::Clause;

    for (body, kind, text) in [
        ("", HeaderError::ExpectedTestItem, ""),
        (" reset", HeaderError::ExpectedTestItem, "reset"),
        (" ()", HeaderError::ExpectedTestItem, ""),
        (" (::reset)", HeaderError::ExpectedTestItem, "::reset"),
        (" (Reset)", HeaderError::ExpectedTestItem, "Reset"),
        (" (reset 0)", HeaderError::UnexpectedArgument, "0"),
        (" (tick)", HeaderError::ExpectedNatural, ""),
        (" (tick -1)", HeaderError::ExpectedNatural, "-1"),
        (" (tick 0 1)", HeaderError::UnexpectedArgument, "1"),
        (" (drive any)", HeaderError::ExpectedTestValue, "any"),
        (" (drive 00)", HeaderError::ExpectedTestValue, "00"),
        (" (drive x)", HeaderError::ExpectedTestValue, "x"),
        (
            " (expect ns::any)",
            HeaderError::ExpectedTestValueOrAny,
            "ns::any",
        ),
        (
            " (expect (raw 1))",
            HeaderError::ExpectedTestValueOrAny,
            "raw",
        ),
        (
            " (expect (as T any))",
            HeaderError::ExpectedTestValue,
            "any",
        ),
        (
            " (expect (as T (as T 0)))",
            HeaderError::ExpectedTestValue,
            "(as T 0)",
        ),
        (" (drive (as 1 0))", HeaderError::ExpectedReference, "1"),
        (" (drive (as T))", HeaderError::ExpectedTestValue, ""),
        (" (drive (as T 1 0))", HeaderError::UnexpectedArgument, "0"),
        (
            " (case (expect) (in))",
            HeaderError::ExpectedClause(Clause::In),
            "expect",
        ),
        (
            " (case (in any) (expect))",
            HeaderError::ExpectedTestValue,
            "any",
        ),
        (
            " (case (in))",
            HeaderError::ExpectedClause(Clause::Expect),
            "",
        ),
        (
            " (case (in) (expect) (in))",
            HeaderError::UnexpectedArgument,
            "(in)",
        ),
    ] {
        let source = format!("(test f{body})");
        let CircuitFormError::Header { kind: actual, span } = index_headers(&source).unwrap_err()
        else {
            panic!("expected test form error for {source:?}");
        };
        assert_eq!(actual, kind, "{source:?}");
        assert_eq!(&source[span.clone()], text, "{source:?}");
        if text.is_empty() {
            assert_eq!(source.as_bytes()[span.start], b')', "{source:?}");
        }
    }
}

#[test]
fn reports_both_heads_when_cases_and_actions_are_mixed() {
    for (body, first, unexpected) in [
        ("(case (in) (expect)) (tick)", "case", "tick"),
        ("(reset) (drive) (case)", "reset", "case"),
    ] {
        let source = format!("(test f {body})");
        let CircuitFormError::Header {
            kind:
                HeaderError::MixedTestItems {
                    first_head: (start, end),
                },
            span,
        } = index_headers(&source).unwrap_err()
        else {
            panic!("expected mixed test item error for {source:?}");
        };
        assert_eq!(&source[start..end], first);
        assert_eq!(&source[span], unexpected);
    }
}
