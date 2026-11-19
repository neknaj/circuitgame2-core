use circuitgame2_core::project::{
    FuncArityError, FuncCallOutputError, FuncWiringResult, ResolvedPortType, SourceSnapshot,
    check_use_aliases, index_use_targets, parse_circuit_project,
};

#[test]
fn assigns_each_call_output_in_declaration_order() {
    let text = concat!(
        "(func pair (in (b (bits 8)) a) (out (b (bits 8)) a)) ",
        "(func f (in a (b (bits 8))) (out narrow (wide (bits 8)) tail) ",
        "  (def tmp (nor a a)) (def (wide narrow) (pair b a)) (def tail tmp))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 1, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let result = aliases.check_func_call_outputs(0, 1, 8).unwrap();
    let types = &result.types;
    assert_eq!(types.len(), 4);
    let nor = types[0].as_ref().unwrap();
    assert!(matches!(nor.ty, ResolvedPortType::Bits(1)));
    assert_eq!(&text[nor.origin.span.clone()], "(nor a a)");
    let wide = types[1].as_ref().unwrap();
    assert!(matches!(wide.ty, ResolvedPortType::Bits(8)));
    assert_eq!(&text[wide.origin.span.clone()], "8");
    let narrow = types[2].as_ref().unwrap();
    assert!(matches!(narrow.ty, ResolvedPortType::Bits(1)));
    assert_eq!(&text[narrow.origin.span.clone()], "a");
    assert!(types[3].is_none());
}

#[test]
fn reports_the_first_left_hand_mismatch_with_both_annotation_sites() {
    let caller = concat!(
        "; 呼び出し元\n",
        "(func f (in (a ::types::Word) b) (out (bad ::types::Other) (next (bits 2))) ",
        "  (def (bad next) (::types::Pair a b)))",
    );
    let library = concat!(
        "; 出力型の宣言\n",
        "(namespace types (struct Word (width 8)) (struct Other (width 8)) ",
        "  (export Word Other Pair) (func Pair (in (value Word) flag) (out (value Word) flag)))",
    );
    let project = parse_circuit_project(&[
        SourceSnapshot { path: "main.ncg2", revision: 2, text: caller },
        SourceSnapshot { path: "types.ncg2", revision: 7, text: library },
    ]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let error = aliases.check_func_call_outputs(0, 0, 8).unwrap_err();
    let FuncCallOutputError::OutputType { target, call, expected, actual } = error else {
        panic!("expected the first output type mismatch: {error:?}");
    };
    assert_eq!(&caller[target.span], "bad");
    assert_eq!(&caller[call.span], "(::types::Pair a b)");
    assert_eq!(&caller[expected.origin.span], "::types::Other");
    assert_eq!(expected.origin.source.revision, 2);
    assert_eq!(&library[actual.origin.span], "Word");
    assert_eq!(actual.origin.source.revision, 7);
}

#[test]
fn preserves_pending_expansion_and_reports_arity_before_output_types() {
    let text = concat!(
        "(func waiting (in) (out x) (expand make)) ",
        "(func invalid (in a) (out (x (bits 8))) (def (x y) (nor a a)))",
    );
    let project = parse_circuit_project(&[SourceSnapshot { path: "main.ncg2", revision: 1, text }]).unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let waiting = aliases.check_func_call_outputs(0, 0, 8).unwrap();
    let FuncWiringResult::NeedsExpansion(site) = waiting.wiring else {
        panic!("expected a pending expansion");
    };
    assert_eq!(&text[site.span], "(expand make)");
    assert!(waiting.types.is_empty());
    assert!(matches!(aliases.check_func_call_outputs(0, 1, 8),
        Err(FuncCallOutputError::Caller(FuncArityError::OutputCount { expected: 2, actual: 1, .. }))));
}
