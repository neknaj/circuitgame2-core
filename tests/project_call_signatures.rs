use circuitgame2_core::project::{
    FuncCallSignature, FuncCallSignatureError, PortDirection, ResolvedPortType, SourceSnapshot,
    TypedSignatureError, check_use_aliases, index_use_targets, parse_circuit_project,
};
use circuitgame2_core::syntax::circuit::{Head, call_argument_range, next_call_argument};

fn source<'a>(path: &'a str, revision: u64, text: &'a str) -> SourceSnapshot<'a> {
    SourceSnapshot { path, revision, text }
}

#[test]
fn projects_types_in_the_declaring_scope_and_arguments_in_caller_order() {
    let caller = concat!(
        "; 呼び出し元\n",
        "(namespace app (struct Fake (width 8)) (use ::app::Fake T) (use ::lib::Pair invoke) ",
        "  (func Main (in a b) (out x y) (def (x y) (invoke (nor a a) b)) ",
        "    (def z (::lib::Zero))))",
    );
    let library = concat!(
        "; 型注釈\n",
        "(namespace lib (struct Word (width 8)) (use ::lib::Word T) (export Pair Zero) ",
        "  (func Pair (in (a T) b) (out b (a T))) (func Zero (in) (out y) (def y 0)))",
    );
    let project = parse_circuit_project(&[
        source("app.ncg2", 2, caller),
        source("./lib/../types.ncg2", 11, library),
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let parsed = &project.circuits()[0];
    let main = parsed.syntax.entries.iter().position(|entry| entry.head == Head::Func).unwrap();
    let typed = aliases.resolve_func_call_signature(0, main, 0, 0, 8).unwrap().unwrap();
    assert_eq!(typed.call.call.arguments, 2);
    let mut remaining = call_argument_range(&parsed.syntax.forms, &typed.call.call);
    let mut found = Vec::new();
    while let Some(arg) = next_call_argument(&parsed.syntax.forms, remaining.clone()) {
        let span = match &parsed.syntax.forms[arg.start] {
            circuitgame2_core::syntax::Form::Atom { span, .. }
            | circuitgame2_core::syntax::Form::List { span, .. } => span,
        };
        found.push(&caller[span.clone()]);
        remaining.start = arg.end;
    }
    assert_eq!(found, ["(nor a a)", "b"]);

    for (direction, index) in [(PortDirection::Input, 0), (PortDirection::Output, 1)] {
        let port = typed.signature.port(direction, index).unwrap();
        assert!(matches!(port.ty, ResolvedPortType::Struct { form, .. } if form.name.word == "Word"));
        let annotation = port.annotation.unwrap();
        assert_eq!(&library[annotation.span.clone()], "T");
        assert_eq!(annotation.source.id.components(), ["types.ncg2"]);
        assert_eq!(annotation.source.revision, 11);
    }
    let first_output = typed.signature.port(PortDirection::Output, 0).unwrap();
    assert!(matches!(first_output.ty, ResolvedPortType::Bits(1)));
    assert_eq!(&library[first_output.annotation.unwrap().span.clone()], "b");
    assert!(typed.signature.port(PortDirection::Output, 2).is_none());
    let nor = aliases.resolve_func_call_signature(0, main, 0, 1, 0).unwrap().unwrap();
    assert!(matches!(nor.signature, FuncCallSignature::Nor));
    for index in [0, 1] {
        let port = nor.signature.port(PortDirection::Input, index).unwrap();
        assert!(matches!(port.ty, ResolvedPortType::Bits(1)));
        assert!(port.annotation.is_none());
    }
    assert!(nor.signature.port(PortDirection::Input, 2).is_none());
    assert!(nor.signature.port(PortDirection::Output, 1).is_none());
    let zero = aliases.resolve_func_call_signature(0, main, 1, 0, 8).unwrap().unwrap();
    assert!(zero.signature.port(PortDirection::Input, 0).is_none());
    let empty = call_argument_range(&parsed.syntax.forms, &zero.call.call);
    assert!(empty.is_empty());
    assert!(next_call_argument(&parsed.syntax.forms, empty).is_none());
}

#[test]
fn preserves_the_call_site_and_the_callee_signature_diagnostic() {
    let caller = "(func f (in a) (out y) (def y (::bad::Bad a)))";
    let library = "(namespace bad (export Bad) (func Bad (in (a Missing)) (out a)))";
    let project = parse_circuit_project(&[
        source("main.ncg2", 4, caller),
        source("bad.ncg2", 14, library),
    ])
    .unwrap();
    let targets = index_use_targets(&project).unwrap();
    let aliases = check_use_aliases(&targets).unwrap();
    let error = aliases.resolve_func_call_signature(0, 0, 0, 0, 8).unwrap_err();
    let FuncCallSignatureError::Signature {
        call,
        error: TypedSignatureError::TypeReference { reference, .. },
    } = error else {
        panic!("expected a signature diagnostic: {error:?}");
    };
    assert_eq!(&caller[call.call.span], "(::bad::Bad a)");
    assert_eq!(call.source.revision, 4);
    assert_eq!(&library[reference.span], "Missing");
    assert_eq!(reference.source.revision, 14);
}
