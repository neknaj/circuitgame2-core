use std::num::NonZeroUsize;
use circuitgame2_core::ncg2m::call_evaluation::scalar::{
    ScalarArgumentsStep, ScalarBindingError, ScalarExpression, ScalarExpressionStep, ScalarInvocationError,
    ScalarInvocationSlice, ScalarValue, bind_scalar_call,
    prepare_scalar_arguments, prepare_scalar_invocation,
};
use circuitgame2_core::ncg2m::expression_types::{DefnBodyCallError, ExpressionCheckFailure};
use circuitgame2_core::ncg2m::integers::IntegerValue;
use circuitgame2_core::project::{
    DefnCallGraphError, DefnPosition, SourceSnapshot, check_mixed_use_aliases,
    index_mixed_use_targets, parse_project_sources,
};

#[test]
fn call_order_keeps_isolated_definitions_and_visits_both_branches() {
    let source = "(defn caller (as-type (Fn () Bool) (fn () (if false (callee) true))))
        (defn isolated (as-type (Fn () Int) (fn () -9223372036854775808)))
        (defn callee (as-type (Fn () Bool) (fn () true)))";
    let snapshots = [SourceSnapshot { path: "common.ncg2m", revision: 1, text: source }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let plan = aliases.plan_defn_calls().unwrap();
    let order = (0..plan.len()).map(|rank| plan.at_rank(rank).unwrap()).collect::<Vec<_>>();
    let rank = |item| plan.rank_of(DefnPosition { file: 0, item }).unwrap();
    assert_eq!(order[rank(2)], DefnPosition { file: 0, item: 2 });
    assert!(plan.rank_of(DefnPosition { file: 0, item: 3 }).is_none());
    assert_eq!(order.len(), 3);
    assert!(rank(2) < rank(0));
    assert!(plan.at_rank(3).is_none());
    let caller_frame = bind_scalar_call(&plan, rank(0), Vec::new()).unwrap();
    let state = ScalarExpression::start(caller_frame);
    let ScalarExpressionStep::Continue(condition) = state.advance().unwrap() else { panic!() };
    let ScalarExpressionStep::Continue(selected) = condition.advance().unwrap() else { panic!() };
    assert!(matches!(selected.advance().unwrap(), ScalarExpressionStep::Complete { value: ScalarValue::Bool(true), .. }));

    let frame = bind_scalar_call(&plan, rank(2), Vec::new()).unwrap();
    assert!(frame.parameters().is_empty());
    assert_eq!(frame.evaluate_atomic_body().unwrap(), Some(ScalarValue::Bool(true)));
    let isolated = bind_scalar_call(&plan, rank(1), Vec::new()).unwrap();
    assert_eq!(isolated.evaluate_atomic_body().unwrap(), Some(ScalarValue::Integer(IntegerValue::Int(i64::MIN))));
    assert_eq!(frame.body().source.revision, 1);
    assert_eq!(&source[frame.body().signature.body_span.clone()], "true");
    let Err(ScalarBindingError::Arity { source: callee_source, span, expected_count: 0, found_count: 1 }) =
        bind_scalar_call(&plan, rank(2), vec![ScalarValue::Bool(false)])
    else { panic!() };
    assert_eq!(callee_source.revision, 1);
    assert!(source[span].starts_with("(defn callee"));
}

#[test]
fn a_binding_with_a_function_name_does_not_add_a_call_edge() {
    let source = "(defn caller (as-type (Fn (Bool) Bool) (fn (x) (let ((callee x)) callee))))
        (defn callee (as-type (Fn (Bool) Bool) (fn (x) (caller x))))";
    let snapshots = [SourceSnapshot { path: "bindings.ncg2m", revision: 2, text: source }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let plan = aliases.plan_defn_calls().unwrap();
    let caller = DefnPosition { file: 0, item: 0 };
    let callee = DefnPosition { file: 0, item: 1 };
    assert_eq!(plan.at_rank(0), Some(caller));
    assert_eq!(plan.at_rank(1), Some(callee));
    assert!(plan.calls_at_rank(0).unwrap().is_empty());
    let [edge] = plan.calls_at_rank(1).unwrap() else { panic!() };
    assert_eq!((edge.from, edge.to), (callee, caller));
}

#[test]
fn a_call_in_a_zero_iteration_fold_is_a_cycle() {
    let source = "(defn repeat (as-type (Fn () Nat) (fn ()
        (fold-nat 0 0 (index acc) (repeat)))))";
    let snapshots = [SourceSnapshot { path: "fold.ncg2m", revision: 19, text: source }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let Err(DefnCallGraphError::Cycle(cycle)) = aliases.plan_defn_calls() else { panic!() };
    let [edge] = cycle.as_slice() else { panic!() };
    assert_eq!(edge.from, edge.to);
    assert_eq!(edge.call.source.revision, 19);
    assert_eq!(&source[edge.call.head.clone()], "repeat");
    assert_eq!(&source[edge.call.span.clone()], "(repeat)");
}

#[test]
fn a_cycle_through_aliases_reports_each_file_and_call() {
    let left = "(namespace left (use ::right::second b)
        (defn first (as-type (Fn () Bool) (fn () (b)))) (export first))";
    let right = "(namespace right (use ::left::first a)
        (defn second (as-type (Fn () Bool) (fn () (a)))) (export second))";
    let snapshots = [
        SourceSnapshot { path: "left.ncg2m", revision: 12, text: left },
        SourceSnapshot { path: "right.ncg2m", revision: 34, text: right },
    ];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let Err(DefnCallGraphError::Cycle(cycle)) = aliases.plan_defn_calls() else { panic!() };
    let [first, second] = cycle.as_slice() else { panic!() };
    assert_eq!(first.to, second.from);
    assert_eq!(second.to, first.from);
    for edge in cycle {
        let source = &snapshots[edge.from.file];
        assert_eq!(edge.call.source.revision, source.revision);
        assert_eq!(&source.text[edge.call.head], if source.revision == 12 { "b" } else { "a" });
    }
}

#[test]
fn an_unresolved_stage_does_not_get_an_acyclic_plan() {
    let source = "(defn staged (as-type (Fn () Syntax) (fn () (syntax (unsyntax (staged))))))";
    let snapshots = [SourceSnapshot { path: "staged.ncg2m", revision: 1, text: source }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    assert!(matches!(aliases.plan_defn_calls(),
        Err(DefnCallGraphError::Body { error: DefnBodyCallError::Expression(ExpressionCheckFailure::Deferred(_)), .. })));
}

#[test]
fn scalar_invocation_uses_argument_order_and_the_callee_frame() {
    let source = "(defn forward (as-type (Fn (Int) Int) (fn (x) (take-first x -2))))
        (defn take-first (as-type (Fn (Int Int) Int) (fn (a b) a)))
        (defn nested (as-type (Fn (Int) Int) (fn (x) (take-first (forward x) -2))))";
    let snapshots = [SourceSnapshot { path: "invoke.ncg2m", revision: 31, text: source }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let plan = aliases.plan_defn_calls().unwrap();
    let rank = |item| plan.rank_of(DefnPosition { file: 0, item }).unwrap();
    let value = ScalarValue::Integer(IntegerValue::Int(25));

    let call = prepare_scalar_invocation(&plan, rank(0), 0, vec![value]).unwrap().unwrap();
    let ScalarInvocationSlice::Suspended(call) = call.run_slice(NonZeroUsize::new(1).unwrap()).unwrap()
    else { panic!() };
    let ScalarInvocationSlice::Enter { rank: callee, frame } = call.run_slice(NonZeroUsize::new(2).unwrap()).unwrap()
    else { panic!() };
    assert_eq!(callee, rank(1));
    assert_eq!(frame.parameters(), &[value, ScalarValue::Integer(IntegerValue::Int(-2))]);
    assert_eq!(frame.evaluate_atomic_body().unwrap(), Some(value));

    let nested = prepare_scalar_invocation(&plan, rank(2), 0, vec![value]).unwrap().unwrap();
    let Err(ScalarInvocationError::Deferred { source: error_source, span }) = nested.run_slice(NonZeroUsize::new(3).unwrap())
    else { panic!() };
    assert_eq!(error_source.revision, 31);
    assert_eq!(&source[span], "(forward x)");

    let outer = prepare_scalar_arguments(&plan, rank(2), 0).unwrap();
    let ScalarArgumentsStep::Argument(first) = outer.next() else { panic!() };
    assert_eq!(first.source().revision, 31);
    assert_eq!(first.expression().at, plan.calls_at_rank(rank(2)).unwrap()[1].at);
    let Err(first) = first.resume(ScalarValue::Bool(true)) else { panic!() };
    let Ok(outer) = first.resume(value) else { panic!() };
    let ScalarArgumentsStep::Argument(second) = outer.next() else { panic!() };
    let Ok(outer) = second.resume(ScalarValue::Integer(IntegerValue::Int(-2))) else { panic!() };
    let ScalarArgumentsStep::Enter { rank: callee, frame } = outer.next() else { panic!() };
    assert_eq!(callee, rank(1));
    assert_eq!(frame.evaluate_atomic_body().unwrap(), Some(value));
}
