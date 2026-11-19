use circuitgame2_syntax::Form;
use circuitgame2_syntax::circuit::{
    RoutineArity, definition_root_is_call, index_build_forms, index_definition_references,
    indexed_call_shape, routine_arity,
};

#[test]
fn projects_call_positions_and_counts_only_direct_arguments() {
    let source = concat!(
        "; 入れ子\n",
        "(func f (in (a (bits 3)) b) (out x (y (bits 3))) ",
        "  (def (x y) (call (none) (as ::types::T a) (next b a))) ",
        "  (def tmp (raw (zero))) ",
        "  (def tail b)) ",
        "(func no-inputs (in) (out y) (def y 0)) ",
        "(using nor)",
    );
    let build = index_build_forms(source).unwrap();
    let forms = &build.syntax.forms;
    assert_eq!(
        routine_arity(source, &build.syntax, 0),
        Some(RoutineArity { inputs: 2, outputs: 2 })
    );
    assert_eq!(
        routine_arity(source, &build.syntax, 1),
        Some(RoutineArity { inputs: 0, outputs: 1 })
    );
    assert_eq!(routine_arity(source, &build.syntax, 2), None);
    assert_eq!(routine_arity(source, &build.syntax, 3), None);

    let root_calls: Vec<_> = build
        .definitions
        .iter()
        .map(|row| definition_root_is_call(source, forms, row, &build.references))
        .collect();
    assert_eq!(root_calls, [true, false, false, false]);

    let first = &build.definitions[0];
    let inner = &build.definitions[1];
    let mut calls = Vec::new();
    for row in [first, inner] {
        for position in row.references.clone() {
            let reference = &build.references[position];
            let shape = indexed_call_shape(source, forms, row, &build.references, position);
            let details = shape.map(|shape| {
                assert_eq!(shape.form + 1, reference.form);
                (&source[shape.span], shape.arguments)
            });
            calls.push((&source[reference.span.clone()], details));
        }
    }
    assert_eq!(
        calls,
        [
            ("call", Some(("(call (none) (as ::types::T a) (next b a))", 3))),
            ("none", Some(("(none)", 0))),
            ("::types::T", None),
            ("next", Some(("(next b a)", 2))),
            ("zero", Some(("(zero)", 0))),
        ]
    );
}

#[test]
fn indexes_only_signal_operands_in_source_order() {
    let source = concat!(
        "; 日本語のコメント\n",
        "(func one (in a b c) (out y) ",
        "  (def tmp (concat (field a member) (as ::lib::T b) ",
        "                  (slice c 0 1) 1 (raw b)))",
        "  (expand ::make (ignored a))",
        "  (def y (::lib::call tmp tmp))) ",
        "(func two (in u) (out y) (def y u)) ",
        "(func three (in) (out y) (def y 0))",
    );
    let build = index_build_forms(source).unwrap();
    let names = |range: std::ops::Range<usize>| {
        build.signals[range]
            .iter()
            .map(|&index| {
                let Form::Atom { span, .. } = &build.syntax.forms[index] else {
                    panic!("expected a signal atom");
                };
                &source[span.clone()]
            })
            .collect::<Vec<_>>()
    };
    let expected: [&[&str]; 4] = [&["a", "b", "c", "b"], &["tmp", "tmp"], &["u"], &[]];
    assert_eq!(build.definitions.len(), expected.len());
    for (row, expected) in build.definitions.iter().zip(expected) {
        assert_eq!(names(row.signals.clone()), expected);
    }
    assert_eq!(
        build
            .entry_ranges
            .iter()
            .map(|entry| entry.signals.clone())
            .collect::<Vec<_>>(),
        [0..6, 6..7, 7..7]
    );
    assert_eq!(build.signals.len(), 7);
}

fn compare_indexes(source: &str, valid: bool) {
    match (
        index_definition_references(source),
        index_build_forms(source),
    ) {
        (Ok(reference), Ok(build)) => {
            assert!(valid);
            assert_eq!(build.syntax, reference.syntax);
            assert_eq!(
                build.entry_ranges.len(),
                reference.definitions_by_entry.len()
            );
            let mut next_definition = 0;
            let mut next_reference = 0;
            for (ranges, definitions) in build
                .entry_ranges
                .iter()
                .zip(reference.definitions_by_entry)
            {
                assert_eq!(ranges.definitions.start, next_definition);
                assert_eq!(ranges.references.start, next_reference);
                let flat_definitions = &build.definitions[ranges.definitions.clone()];
                assert_eq!(flat_definitions.len(), definitions.len());
                for (flat, original) in flat_definitions.iter().zip(definitions) {
                    assert_eq!(flat.form, original.definition);
                    assert_eq!(flat.expression, original.expression);
                    assert_eq!(flat.references.start, next_reference);
                    assert_eq!(
                        &build.references[flat.references.clone()],
                        original.references.as_slice()
                    );
                    next_reference = flat.references.end;
                }
                assert_eq!(ranges.references.end, next_reference);
                next_definition = ranges.definitions.end;
            }
            assert_eq!(next_definition, build.definitions.len());
            assert_eq!(next_reference, build.references.len());
        }
        (Err(reference), Err(build)) => {
            assert!(!valid, "{reference:?}");
            assert_eq!(build, reference);
        }
        different => panic!("accepted different languages: {different:?}"),
    }
}

#[test]
fn matches_reference_for_mixed_forms_and_empty_ranges() {
    compare_indexes("", true);
    compare_indexes(
        concat!(
            "; UTF-8 の範囲を照合する\n",
            "(using nor) (namespace empty) ",
            "(struct T (width 3)) ",
            "(module Leading (in) (out y) (def y 0) (def z #b101)) ",
            "(namespace app ",
            "  (use ::T Type) ",
            "  (func f (in x) (out y) (def y (as Type (nor x x)))) ",
            "  (module-part M (expand ::tool (def x (ignored y))) (def q (g x)))) ",
            "(module-part M (def (a b) (::lib::split x)))",
        ),
        true,
    );
}

#[test]
fn matches_reference_for_generated_files_and_first_errors() {
    for count in [1, 4, 64] {
        let mut source = String::from("(using nor) ");
        for i in 0..count {
            source.push_str(&format!(
                "(func f{i} (in (x (bits 1))) (out y) (def y (nor x x))) "
            ));
        }
        compare_indexes(&source, true);
        source.push_str("(func broken (in) (out y) (def y (as T) extra))");
        compare_indexes(&source, false);
    }
    for source in [
        "(invalid) (",
        "(invalid) (func f (in) (out y) (def y (as T)))",
        "(namespace x (func f (in) (out y) (def y (as T))))",
    ] {
        compare_indexes(source, false);
    }
}
