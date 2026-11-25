use std::num::NonZeroUsize;
use circuitgame2_core::ncg2m::call_evaluation::scalar::{
    ScalarArgumentsStep, ScalarBindingError, ScalarEntryError, ScalarExecution, ScalarExecutionError,
    ScalarExecutionSlice, ScalarExpression, ScalarExpressionStep, ScalarInvocationError, ScalarInvocationSlice,
    ScalarValue, bind_scalar_call, prepare_scalar_arguments, prepare_scalar_entry, prepare_scalar_invocation,
};
use circuitgame2_core::ncg2m::expression_types::{DefnBodyCallError, ExpressionCheckFailure};
use circuitgame2_core::ncg2m::integers::{IntegerOperation, IntegerValue};
use circuitgame2_core::project::{
    DefnCallError, DefnCallGraphError, DefnPosition, PreparedDefnCall, SourceSnapshot, check_mixed_use_aliases,
    index_mixed_use_targets, parse_project_sources,
};
use circuitgame2_core::syntax::{Form, parse};

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

    let one = NonZeroUsize::new(1).unwrap();
    let execution = ScalarExecution::start(&plan, rank(0), vec![value]).unwrap();
    let ScalarExecutionSlice::Suspended(lookup) = execution.run_slice(one).unwrap() else { panic!() };
    assert!(matches!(lookup.run_slice(one).unwrap(), ScalarExecutionSlice::Suspended(_)));

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

#[test]
fn slices_resume_nested_arguments_in_the_original_environment() {
    let source = "(defn entry (as-type (Fn (Bool Int) Int)
        (fn (choose value) (pick (if choose (check value) false)
            (if choose (identity value) (as-type Int -9))))))
        (defn pick (as-type (Fn (Bool Int) Int) (fn (flag data) (if flag data 0))))
        (defn check (as-type (Fn (Int) Bool) (fn (data) true)))
        (defn identity (as-type (Fn (Int) Int) (fn (data) data)))
        (defn blocked (as-type (Fn () Int) (fn ()
            (pick (as-type Bool true) (as-type Int -9)))))";
    let snapshots = [SourceSnapshot { path: "nested.ncg2m", revision: 52, text: source }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let plan = aliases.plan_defn_calls().unwrap();
    let rank = plan.rank_of(DefnPosition { file: 0, item: 0 }).unwrap();
    let expected = ScalarValue::Integer(IntegerValue::Int(-25));
    let start = || ScalarExecution::start(&plan, rank, vec![ScalarValue::Bool(true), expected]).unwrap();
    let whole = start().run_slice(NonZeroUsize::new(128).unwrap()).unwrap();
    assert!(matches!(whole, ScalarExecutionSlice::Complete(value) if value == expected));

    let mut state = start();
    let mut sliced = None;
    for _ in 0..128 {
        match state.run_slice(NonZeroUsize::new(1).unwrap()).unwrap() {
            ScalarExecutionSlice::Suspended(next) => state = next,
            ScalarExecutionSlice::Complete(value) => {
                sliced = Some(value);
                break;
            }
        }
    }
    assert_eq!(sliced, Some(expected));

    let blocked = plan.rank_of(DefnPosition { file: 0, item: 4 }).unwrap();
    let mut state = ScalarExecution::start(&plan, blocked, Vec::new()).unwrap();
    let whole = ScalarExecution::start(&plan, blocked, Vec::new()).unwrap()
        .run_slice(NonZeroUsize::new(128).unwrap());
    let Err(ScalarExecutionError::Deferred { source: whole_source, span: whole_span }) = whole else { panic!() };
    assert_eq!((whole_source.revision, &source[whole_span.clone()]), (52, "(as-type Bool true)"));
    for _ in 0..128 {
        match state.run_slice(NonZeroUsize::new(1).unwrap()) {
            Ok(ScalarExecutionSlice::Suspended(next)) => state = next,
            Err(ScalarExecutionError::Deferred { source, span }) => {
                assert_eq!((source.revision, span), (whole_source.revision, whole_span));
                return;
            }
            _ => panic!("the first unsupported argument should stop evaluation"),
        }
    }
    panic!("the small call graph should finish within the test's step limit");
}


#[test]
fn scalar_fragment_support_checks_bodies_reachable_through_either_branch() {
    let snapshots = [SourceSnapshot {
        path: "support.ncg2m", revision: 1,
        text: "(defn root (as-type (Fn () Bool) (fn () (if (pass (leaf)) true (pending)))))
               (defn pass (as-type (Fn (Bool) Bool) (fn (x) x)))
               (defn leaf (as-type (Fn () Bool) (fn () true)))
               (defn pending (as-type (Fn () Bool) (fn () (as-type Bool true))))
               (defn accepted (as-type (Fn () Bool) (fn () (if (pass (leaf)) true false))))",
    }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let plan = aliases.plan_defn_calls().unwrap();
    for (item, (body_support, fragment_support)) in
        [(true, false), (true, true), (true, true), (false, false), (true, true)]
            .into_iter()
            .enumerate()
    {
        let rank = plan.rank_of(DefnPosition { file: 0, item }).unwrap();
        assert_eq!(plan.scalar_body_support_at_rank(rank), Some(body_support));
        assert_eq!(plan.scalar_fragment_support_at_rank(rank), Some(fragment_support));
    }
    let accepted = plan.rank_of(DefnPosition { file: 0, item: 4 }).unwrap();
    let entry = prepare_scalar_entry(&plan, DefnPosition { file: 0, item: 4 }).unwrap();
    assert_eq!(entry.rank(), accepted);
    assert!(matches!(entry.start(vec![ScalarValue::Bool(false)]), Err(ScalarBindingError::Arity { .. })));
    let state = entry.start(Vec::new()).unwrap();
    let result = state.run_slice(NonZeroUsize::new(128).unwrap()).unwrap();
    assert!(matches!(result, ScalarExecutionSlice::Complete(ScalarValue::Bool(true))));
    assert!(matches!(prepare_scalar_entry(&plan, DefnPosition { file: 0, item: 0 }),
        Err(ScalarEntryError::UnsupportedFragment)));
    assert!(matches!(prepare_scalar_entry(&plan, DefnPosition { file: 1, item: 0 }),
        Err(ScalarEntryError::UnknownDefinition)));
    assert_eq!(plan.scalar_body_support_at_rank(usize::MAX), None);
    assert_eq!(plan.scalar_fragment_support_at_rank(usize::MAX), None);
}

#[test]
fn arithmetic_fallback_preserves_shadowing_and_operand_positions() {
    let source = "(defn add (as-type (Fn (Nat) Nat) (fn (x) x)))
        (use ::add mul)
        (defn caller (as-type (Fn () Nat)
            (fn () (if true (sub (add 1) (mul 0)) (sub 0)))))";
    let snapshots = [SourceSnapshot { path: "arithmetic.ncg2m", revision: 14, text: source }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let forms = parse(source).unwrap();
    let form_at = |prefix| {
        let first_byte = source.find(prefix).unwrap();
        forms.iter().position(|form| matches!(form, Form::List { span, .. } if span.start == first_byte)).unwrap()
    };
    let operation = aliases.prepare_defn_call(0, 2, form_at("(sub (add")).unwrap().unwrap();
    let PreparedDefnCall::Arithmetic { site, operation, arguments } = operation else { panic!() };
    assert_eq!(operation, IntegerOperation::Sub);
    assert_eq!(arguments, (form_at("(add 1)"), form_at("(mul 0)")));
    assert_eq!(site.source.revision, 14);
    assert_eq!(&source[site.head], "sub");
    assert_eq!(&source[site.span], "(sub (add 1) (mul 0))");
    for head in ["(add 1)", "(mul 0)"] {
        let resolved = aliases.prepare_defn_call(0, 2, form_at(head)).unwrap().unwrap();
        assert!(matches!(resolved, PreparedDefnCall::Declared { declaration, .. } if declaration.item == 0));
    }
    let malformed = aliases.prepare_defn_call(0, 2, form_at("(sub 0)")).unwrap();
    assert!(matches!(malformed, Err(DefnCallError::ArithmeticArity {
        operation: IntegerOperation::Sub, found: 1, ..
    })));
}

#[test]
fn declared_argument_type_selects_the_nested_arithmetic_signature() {
    let source = "(defn take-int (as-type (Fn (Int) Nat) (fn (value) 0)))
        (defn caller (as-type (Fn () Nat) (fn () (take-int (add -2 (mul 3 4))))))
        (defn natural (as-type (Fn () Nat) (fn () (sub 2 1))))";
    let snapshots = [SourceSnapshot { path: "integer-types.ncg2m", revision: 2, text: source }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    assert!(matches!(aliases.check_defn_body_with_calls(0, 1), Some(Ok(_))));
    assert!(matches!(aliases.check_defn_body_with_calls(0, 2), Some(Ok(_))));
}

#[test]
fn scalar_entry_evaluates_checked_arithmetic_in_operand_order() {
    let source = "(defn natural (as-type (Fn () Nat) (fn () (mul 2 (sub 5 1)))))
        (defn signed (as-type (Fn () Int) (fn () (add -9223372036854775808 0))))
        (defn choose (as-type (Fn () Nat) (fn () (if true 7 (sub 0 1)))))
        (defn first-failure (as-type (Fn () Nat)
            (fn () (add (sub 0 1) (mul 18446744073709551615 2)))))";
    let snapshots = [SourceSnapshot { path: "arithmetic-run.ncg2m", revision: 9, text: source }];
    let project = parse_project_sources(&snapshots).unwrap();
    let targets = index_mixed_use_targets(&project).unwrap();
    let aliases = check_mixed_use_aliases(&targets).unwrap();
    let plan = aliases.plan_defn_calls().unwrap();
    let run = |item, budget| {
        let entry = prepare_scalar_entry(&plan, DefnPosition { file: 0, item }).unwrap();
        let mut state = entry.start(Vec::new()).unwrap();
        let mut total = 0;
        for _ in 0..128 {
            let (result, steps) = state.run_slice_with_steps(NonZeroUsize::new(budget).unwrap());
            assert!((1..=budget).contains(&steps));
            total += steps;
            match result {
                Ok(ScalarExecutionSlice::Suspended(next)) => {
                    assert_eq!(steps, budget);
                    state = next;
                }
                Ok(ScalarExecutionSlice::Complete(value)) => return (Ok(value), total),
                Err(error) => return (Err(error), total),
            }
        }
        panic!()
    };
    for (item, expected) in [IntegerValue::Nat(8), IntegerValue::Int(i64::MIN), IntegerValue::Nat(7)]
        .into_iter().enumerate()
    {
        let (sliced, sliced_steps) = run(item, 1);
        let (whole, whole_steps) = run(item, 128);
        assert_eq!(sliced.unwrap(), ScalarValue::Integer(expected));
        assert_eq!(whole.unwrap(), ScalarValue::Integer(expected));
        assert_eq!(sliced_steps, whole_steps);
    }
    let (sliced, sliced_steps) = run(3, 1);
    let (whole, whole_steps) = run(3, 128);
    assert_eq!(sliced_steps, whole_steps);
    for result in [sliced, whole] {
        let Err(ScalarExecutionError::Arithmetic { source: origin, operation, error }) = result else {
            panic!()
        };
        assert_eq!(operation, IntegerOperation::Sub);
        assert_eq!(origin.revision, 9);
        assert_eq!(&source[error.span], "(sub 0 1)");
    }
}
