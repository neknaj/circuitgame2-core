use circuitgame2_core::project::{
    FuncDriverError, FuncSignalReason, FuncWiringError, FuncWiringResult, OutputDriver,
    SourceSnapshot, check_use_aliases, index_use_targets, parse_circuit_project,
};

fn source(text: &str) -> SourceSnapshot<'_> {
    SourceSnapshot {
        path: "./lib/tmp/../logic.ncg2",
        revision: 17,
        text,
    }
}

#[test]
fn binds_each_signal_to_its_input_or_earlier_definition() {
    let text = concat!(
        "; 日本語\n",
        "(func earlier (in i) (out o) (def o i)) ",
        "(func target (in a b) (out y a) ",
        "  (def (p q) (pair a b)) ",
        "  (def unused 0) ",
        "  (def y (other q (raw p) q))) ",
        "(func after (in i) (out o) (def o i))",
    );
    let project = parse_circuit_project(&[source(text)]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let FuncWiringResult::Checked(wiring) = aliases.check_func_wiring(0, 1, 1).unwrap() else {
        panic!("expected bound signals");
    };
    assert_eq!(
        wiring.drivers.outputs,
        [OutputDriver::Definition(3), OutputDriver::Input(0)]
    );
    let bindings: Vec<_> = wiring
        .signals
        .iter()
        .map(|signal| {
            let location = &signal.site;
            assert_eq!(location.source.id.components(), ["lib", "logic.ncg2"]);
            assert_eq!(location.source.revision, 17);
            (&text[location.span.clone()], signal.definition, signal.driver)
        })
        .collect();
    assert_eq!(
        bindings,
        [
            ("a", 1, OutputDriver::Input(0)),
            ("b", 1, OutputDriver::Input(1)),
            ("q", 3, OutputDriver::Definition(1)),
            ("p", 3, OutputDriver::Definition(0)),
            ("q", 3, OutputDriver::Definition(1)),
        ]
    );
    assert!(wiring.signals.windows(2).all(|pair| pair[0].site.span.end < pair[1].site.span.start));
}

#[test]
fn identifies_the_first_illegal_signal_use_and_its_definition() {
    for (text, word, definition_offset, self_reference) in [
        (
            "; 日本語\n(func f (in a) (out y) (def (p y) (combine a p missing)))",
            "p",
            Some("(p y)"),
            true,
        ),
        (
            "; 日本語\n(func f (in a) (out y) (def y (combine a late missing)) (def late 0))",
            "late",
            Some("late 0"),
            false,
        ),
        (
            "; 日本語\n(func missing (in a) (out a)) (func f (in a) (out y) (def y (missing a missing extra)))",
            "missing",
            None,
            false,
        ),
    ] {
        let project = parse_circuit_project(&[source(text)]).unwrap();
        let targets = index_use_targets(&project).unwrap();
        let aliases = check_use_aliases(&targets).unwrap();
        let entry = usize::from(definition_offset.is_none());
        let error = aliases.check_func_wiring(0, entry, 1).unwrap_err();
        let FuncWiringError::Signal { site, reason } = error else {
            panic!("expected a signal diagnostic, got {error:?}");
        };
        assert_eq!(&text[site.span.clone()], word);
        assert_eq!(site.source.id.components(), ["lib", "logic.ncg2"]);
        assert_eq!(site.source.revision, 17);
        let site_start = text.find(&format!("a {word} ")).unwrap() + 2;
        assert_eq!(site.span, site_start..site_start + word.len());
        match (reason, definition_offset) {
            (FuncSignalReason::Undefined, None) => {}
            (FuncSignalReason::SelfReference(related), Some(start)) if self_reference => {
                let expected = text.find(start).unwrap() + 1;
                assert_eq!(related.span, expected..expected + word.len());
                assert_eq!(related.source.revision, 17);
            }
            (FuncSignalReason::ForwardReference(related), Some(start)) if !self_reference => {
                let expected = text.find(start).unwrap();
                assert_eq!(related.span, expected..expected + word.len());
                assert_eq!(related.source.revision, 17);
            }
            (reason, _) => panic!("unexpected diagnostic: {reason:?}"),
        }
    }
}

#[test]
fn preserves_driver_diagnostics_expansion_and_empty_functions() {
    let text = concat!(
        "(func direct (in a) (out a)) ",
        "(func constant (in) (out a) (def a 1)) ",
        "(func unbound (in) (out a y) (def y missing)) ",
        "(func expanded (in) (out y) (def y pending) (expand ::make)) ",
        "(module forward (in) (out y) (def y later) (def later 0))",
    );
    let project = parse_circuit_project(&[source(text)]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    for entry in [0, 1] {
        let FuncWiringResult::Checked(wiring) = aliases.check_func_wiring(0, entry, 1).unwrap() else {
            panic!("expected wiring with no signal references");
        };
        assert!(wiring.signals.is_empty());
    }
    let error = aliases.check_func_wiring(0, 2, 1).unwrap_err();
    let FuncWiringError::Driver(FuncDriverError::MissingOutput(site)) = error else {
        panic!("expected missing output");
    };
    assert_eq!(&text[site.span], "a");
    let FuncWiringResult::NeedsExpansion(site) = aliases.check_func_wiring(0, 3, 1).unwrap() else {
        panic!("expected pending expansion");
    };
    assert_eq!(&text[site.span], "(expand ::make)");
    assert!(matches!(aliases.check_func_wiring(0, 4, 1).unwrap(), FuncWiringResult::NotFunc));
    assert!(matches!(aliases.check_func_wiring(usize::MAX, 0, 1).unwrap(), FuncWiringResult::NotFunc));
}
