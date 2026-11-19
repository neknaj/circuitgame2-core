use circuitgame2_core::syntax::{AtomKind, Error, ErrorKind, Form, parse};

#[test]
fn recognizes_atoms_and_keeps_utf8_byte_spans() {
    let source = "(logic::invert ::_gate 000 -07 #b001 #xFa \"日本語\\\"\\\\\")";
    let forms = parse(source).unwrap();
    assert_eq!(
        forms[0],
        Form::List {
            span: 0..source.len(),
            end: forms.len(),
        }
    );
    let expected = [
        (AtomKind::RelativePath, "logic::invert"),
        (AtomKind::AbsolutePath, "::_gate"),
        (AtomKind::Natural, "000"),
        (AtomKind::NegativeInteger, "-07"),
        (AtomKind::Binary, "#b001"),
        (AtomKind::Hexadecimal, "#xFa"),
        (AtomKind::String, "\"日本語\\\"\\\\\""),
    ];
    assert_eq!(forms.len(), expected.len() + 1);
    for (form, (expected_kind, expected_text)) in forms[1..].iter().zip(expected) {
        let Form::Atom { kind, span } = form else {
            panic!("expected an atom");
        };
        assert_eq!(*kind, expected_kind);
        assert_eq!(&source[span.clone()], expected_text);
    }
}

#[test]
fn handles_nested_lists_without_recursive_storage() {
    let depth = 20_000;
    let source = "(".repeat(depth) + &")".repeat(depth) + "; comment at EOF";
    let forms = parse(&source).unwrap();
    assert_eq!(forms.len(), depth);
    assert_eq!(
        forms[depth - 1],
        Form::List {
            span: depth - 1..depth + 1,
            end: depth,
        }
    );
}

#[test]
fn requires_valid_complete_input() {
    for (source, kind, span) in [
        ("12foo", ErrorKind::InvalidAtom, 0..5),
        ("#b102", ErrorKind::InvalidAtom, 0..5),
        ("a::", ErrorKind::InvalidAtom, 0..3),
        ("a\"b\"", ErrorKind::MissingSeparator, 1..1),
        ("\"a\"b", ErrorKind::MissingSeparator, 3..3),
        ("\"\\日\"", ErrorKind::InvalidEscape { opening: 0 }, 1..5),
        ("\"a\n\"", ErrorKind::NewlineInString { opening: 0 }, 2..3),
        ("\"a", ErrorKind::UnterminatedString, 0..2),
        ("() )", ErrorKind::UnexpectedClose, 3..4),
        ("(a", ErrorKind::UnclosedList { eof: 2 }, 0..1),
    ] {
        assert_eq!(parse(source), Err(Error { kind, span }), "{source:?}");
    }
    assert!(parse("; コメント\r\n").unwrap().is_empty());
    assert_eq!(parse("a; コメント\r\nb").unwrap().len(), 2);
}

#[test]
fn balances_only_parenthesis_tokens() {
    for (source, count) in [
        ("", 0),
        (";", 0),
        ("a(b)c", 4),
        ("(; )\r\n)", 1),
        (r#"("[)]")"#, 2),
        ("a; 日\r\n\"b\"", 2),
    ] {
        assert_eq!(parse(source).unwrap().len(), count, "{source:?}");
    }

    assert_eq!(
        parse(")(").unwrap_err(),
        Error {
            kind: ErrorKind::UnexpectedClose,
            span: 0..1
        },
    );
    assert_eq!(
        parse(r#""a""b""#).unwrap_err(),
        Error {
            kind: ErrorKind::MissingSeparator,
            span: 3..3
        },
    );
}

#[test]
fn recovering_parser_matches_strict_on_valid_source() {
    use circuitgame2_core::syntax::parse_recovering;
    let source = "(namespace logic (func invert (in x) (out y)))\r\n(\"日\")";
    let result = parse_recovering(source);
    assert_eq!(result.forms, parse(source).unwrap());
    assert!(result.repairs.is_empty());
}

#[test]
fn recovery_preserves_skips_and_nested_synthetic_closes() {
    use circuitgame2_core::syntax::{Repair, parse_recovering};
    let source = ")(a (b";
    let result = parse_recovering(source);
    assert_eq!(
        result.repairs,
        [
            Repair::Skipped {
                span: 0..1,
                error: Error {
                    kind: ErrorKind::UnexpectedClose,
                    span: 0..1
                },
            },
            Repair::InsertedClose {
                offset: 6,
                opening: 4..5,
                list: 2
            },
            Repair::InsertedClose {
                offset: 6,
                opening: 1..2,
                list: 0
            },
        ]
    );
    assert_eq!(result.forms[0], Form::List { span: 1..6, end: 4 });
    assert_eq!(result.forms[2], Form::List { span: 4..6, end: 4 });
}

#[test]
fn recovery_retains_both_errors_and_ignores_the_inner_close_in_a_string() {
    use circuitgame2_core::syntax::{Repair, parse_recovering};
    let source = "(a\"\\q)\" b)";
    let result = parse_recovering(source);
    assert_eq!(
        result.repairs,
        [
            Repair::InsertedSeparator { offset: 2 },
            Repair::Skipped {
                span: 2..7,
                error: Error {
                    kind: ErrorKind::InvalidEscape { opening: 2 },
                    span: 3..5
                },
            },
        ]
    );
    assert_eq!(
        result.forms[0],
        Form::List {
            span: 0..source.len(),
            end: 3
        }
    );
    assert_eq!(
        result.forms[2],
        Form::Atom {
            kind: AtomKind::Name,
            span: 8..9
        }
    );
}

#[test]
fn names_and_paths_require_nonempty_ascii_components() {
    for (source, expected) in [
        ("_", AtomKind::Name),
        ("Alpha_09-x", AtomKind::Name),
        ("_a::B-2", AtomKind::RelativePath),
        ("::a", AtomKind::AbsolutePath),
        ("::a::B", AtomKind::AbsolutePath),
    ] {
        assert_eq!(
            parse(source).unwrap(),
            [Form::Atom {
                kind: expected,
                span: 0..source.len()
            }]
        );
    }

    for source in [
        "::", "a::", "::a::", "a:::b", "::::a", "a:b", "a::1", "a::é", "-a",
    ] {
        assert_eq!(
            parse(source).unwrap_err(),
            Error {
                kind: ErrorKind::InvalidAtom,
                span: 0..source.len()
            }
        );
    }
}
