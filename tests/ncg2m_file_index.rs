use circuitgame2_core::ncg2m::defn::{DefnHeaderError, DefnPart};
use circuitgame2_core::ncg2m::file::{MetaFileError, MetaItemKind, index_meta_file};
use circuitgame2_core::syntax::circuit::HeaderError;

#[test]
fn preserves_file_order_and_distinguishes_blocks_with_the_same_path() {
    let source = "; コメント
(namespace logic::meta
  (use ::other::transform invoke)
  (export emit)
  (defmacro emit (out) (invoke out)))
(defn top (as-type (Fn () Nat) (fn () 0)))
(namespace logic::meta
  (defn next (as-type (Fn ((List Event)) Nat) (fn (xs) (count xs)))))
";
    let entries = index_meta_file(source).unwrap();
    let [namespace, alias, export, mac, top, next_namespace, next] = entries.as_slice() else {
        panic!("expected seven entries");
    };
    let MetaItemKind::Namespace { path } = &namespace.kind else {
        panic!("expected first namespace");
    };
    assert_eq!(&source[path.clone()], "logic::meta");
    assert_eq!(alias.namespace.as_ref(), Some(path));
    assert_eq!(export.namespace.as_ref(), Some(path));
    assert_eq!(mac.namespace.as_ref(), Some(path));
    assert_eq!(top.namespace, None);

    let MetaItemKind::Namespace { path: next_path } = &next_namespace.kind else {
        panic!("expected second namespace");
    };
    assert_eq!(&source[next_path.clone()], "logic::meta");
    assert_ne!(path, next_path);
    assert_eq!(next.namespace.as_ref(), Some(next_path));
    let MetaItemKind::Defn(header) = &next.kind else {
        panic!("expected function");
    };
    assert_eq!(&source[header.name_span.clone()], "next");
    assert_eq!(&source[header.parameters[0].ty.name_span.clone()], "Event");
    assert_eq!(&source[header.body_span.clone()], "(count xs)");
    assert!(entries.windows(2).all(|pair| pair[0].span.start < pair[1].span.start));
}

#[test]
fn preserves_the_first_diagnostic_and_its_file_range() {
    let source = "; 前置き\n(namespace lib (defn f (as-type (Fn () (Fn () Int)) (fn () 0)))) (use x y)";
    let start = source.find("(Fn () Int)").unwrap();
    assert_eq!(
        index_meta_file(source).unwrap_err(),
        MetaFileError::Defn(DefnHeaderError::Expected {
            span: start..start + "(Fn () Int)".len(),
            part: DefnPart::DataType,
        }),
    );

    let source = "(namespace lib (use ::x) (export 0))";
    let close = source.find(") ").unwrap();
    assert_eq!(
        index_meta_file(source).unwrap_err(),
        MetaFileError::Directive { span: close..close, kind: HeaderError::ExpectedName },
    );
}
