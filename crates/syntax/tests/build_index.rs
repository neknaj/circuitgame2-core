use circuitgame2_syntax::Form;
use circuitgame2_syntax::circuit::{index_build_forms, index_definition_references};

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
