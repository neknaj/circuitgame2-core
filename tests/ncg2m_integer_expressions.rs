use circuitgame2_core::ncg2m::integer_expression::{
    IntegerCheckError, check_integer_expression,
};
use circuitgame2_core::ncg2m::integers::{IntegerType, IntegerValue};

#[test]
fn deep_integer_expressions_do_not_use_the_rust_stack() {
    let depth = 30_000;
    let mut source = "(add 1 ".repeat(depth);
    source.push('0');
    source.push_str(&")".repeat(depth));
    let checked = check_integer_expression(&source, None).unwrap();
    assert_eq!(checked.evaluate(), Ok(IntegerValue::Nat(depth as u64)));
}

#[test]
fn propagates_constraints_from_nested_operands() {
    let checked = check_integer_expression("(add (sub 0 2) (nat-to-int 1))", None).unwrap();
    assert_eq!(checked.evaluate(), Ok(IntegerValue::Int(-1)));

    let source = "(add (as-type Nat 1) (as-type Int 2))";
    assert_eq!(
        check_integer_expression(source, None).unwrap_err(),
        IntegerCheckError::TypeMismatch {
            span: 21..36,
            expected: IntegerType::Nat,
            actual: IntegerType::Int,
        },
    );
}
