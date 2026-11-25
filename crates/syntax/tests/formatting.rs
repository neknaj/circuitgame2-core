use circuitgame2_syntax::{formatting::format_sexpr, parse};

#[test]
fn normalizes_separators_and_keeps_original_spelling() {
    let source = " \r\n (foo () ;内側 \t\r\n  \"漢;😀\\\"\\\\\" \r ) ;末尾\r(foo 01)\r";
    let expected = "(foo () ;内側 \t\n  \"漢;😀\\\"\\\\\"\n) ;末尾\n(foo 01)\n";
    let formatted = format_sexpr(source).unwrap();
    assert_eq!(formatted, expected);
    assert_eq!(format_sexpr(&formatted).unwrap(), expected);
}

#[test]
fn handles_empty_sources_and_comments_near_parentheses() {
    assert_eq!(format_sexpr(" \r\t\n").unwrap(), "");
    assert_eq!(format_sexpr(" ;コメント\t").unwrap(), ";コメント\t\n");
    assert_eq!(
        format_sexpr("(;行内\r\nx)()\r\n\r(;末尾\r)").unwrap(),
        "( ;行内\n  x)\n()\n( ;末尾\n)\n",
    );
}

#[test]
fn reports_the_original_strict_diagnostic() {
    for source in ["))", "(a", "\"a\\q\"", "a\"b\""] {
        assert_eq!(format_sexpr(source).unwrap_err(), parse(source).unwrap_err());
    }
}
