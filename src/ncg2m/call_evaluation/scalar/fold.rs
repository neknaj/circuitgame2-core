//! 自然数反復を、回数・初期値・本体の評価を中断できる形で実行する。

use super::*;
use super::super::nat_fold::{NatFold, NatFoldIteration, NatFoldNext, planned_nat_fold};
use crate::ncg2m::defn::span_of;
use crate::ncg2m::expression_types::{NatFoldTerms, named_call::check_scalar_body_syntax};
use crate::ncg2m::forms::{is_spelling, source_word};
use crate::syntax::{AtomKind, Form};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::{nat_fold_term_results_agree, nat_fold_terms_match, scalar_evaluator_syntax};
#[cfg(verus_only)]
use crate::ncg2m::data_types::signature_result_types_agree;
#[cfg(verus_only)]
use crate::ncg2m::forms::spelling;
#[cfg(verus_only)]
use crate::syntax::form_span;
#[cfg(verus_only)]
use super::atom::scalar_atom_matches;

verus! {

/// アトムを使う自然数反復の評価を開始するための、型検査済みの位置。
pub struct ScalarFoldEntry<'plan, 'p, 'a> {
    plan: &'plan DefnCallPlan<'p, 'a>,
    rank: usize,
    terms: NatFoldTerms,
    origin: Ghost<DefnEvaluationBody<'p, 'a>>,
}

/// 回数、初期値、反復本体のいずれかを評価する途中の状態。
///
/// 評価を完了するか状態を破棄するまで、型検査済みの呼び出し計画を借用する。
pub struct ScalarFoldExecution<'p, 'a> {
    plan: &'p DefnCallPlan<'p, 'a>,
    rank: usize,
    frame: Option<ScalarCallFrame<'p, 'a>>,
    terms: NatFoldTerms,
    phase: FoldPhase<'p, 'a>,
}

enum FoldPhase<'p, 'a> {
    Count,
    Initial(u64),
    Select(NatFold<ScalarValue>),
    Body(NatFoldIteration<ScalarValue>),
    Expression { state: ScalarExecution<'p, 'p, 'a>, iteration: NatFoldIteration<ScalarValue> },
}

/// 実行枠を使い切った状態か、反復式の結果。
pub enum ScalarFoldSlice<'p, 'a> {
    /// 次の遷移から再開できる。
    Suspended(ScalarFoldExecution<'p, 'a>),
    /// 最後の累積値。反復回数が0なら初期値である。
    Complete(ScalarValue),
}

spec fn nat_type<'a>() -> DataType<'a> {
    DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Nat)), list_depth: 0 }
}

fn count_type<'a>() -> (ty: DataType<'a>)
    ensures ty == nat_type(),
{
    DataType { atom: DataTypeAtom::Builtin(BuiltinDataType::Integer(IntegerType::Nat)), list_depth: 0 }
}

spec fn ordered_terms(terms: NatFoldTerms, body: DefnEvaluationBody) -> bool {
    body.at < terms.count < terms.initial < terms.index_binding
        < terms.accumulator_binding < terms.body < body.forms@.len()
}


spec fn atom_at(forms: Seq<Form>, at: usize) -> bool {
    at < forms.len() && forms[at as int] matches Form::Atom {
        kind: AtomKind::Name | AtomKind::Natural | AtomKind::NegativeInteger, ..
    }
}

spec fn atom_fold_at<'p, 'a>(body: DefnEvaluationBody<'p, 'a>, terms: NatFoldTerms) -> bool {
    &&& nat_fold_terms_match(body.source.text_model(), body.forms@, body.at, Some(terms))
    &&& atom_at(body.forms@, terms.count)
    &&& atom_at(body.forms@, terms.initial)
    &&& scalar_evaluator_syntax(body.source.text_model(), body.forms@, terms.body)
    &&& body.signature.result_type.ty.list_depth == 0
    &&& body.signature.result_type.ty.atom matches DataTypeAtom::Builtin(
        BuiltinDataType::Bool | BuiltinDataType::Integer(_)
    )
}

spec fn scalar_fold_witness<'p, 'a>(plan: &DefnCallPlan<'p, 'a>, rank: usize,
    body: DefnEvaluationBody<'p, 'a>, terms: NatFoldTerms) -> bool {
    plan.body_matches_at_rank(rank, body) && atom_fold_at(body, terms)
}

/// 指定した補助関数の反復が、アトムとスカラー型に限った評価規則の対象であることを表す。
pub closed spec fn scalar_fold_supported<'p, 'a>(plan: &DefnCallPlan<'p, 'a>, position: crate::project::DefnPosition) -> bool {
    &&& plan.order_model().contains(position)
    &&& exists|body: DefnEvaluationBody<'p, 'a>, terms: NatFoldTerms|
        #[trigger] scalar_fold_witness(plan, plan.order_model().index_of(position) as usize, body, terms)
}

proof fn supported_layout_agrees<'p, 'a>(plan: &DefnCallPlan<'p, 'a>, rank: usize,
    body: DefnEvaluationBody<'p, 'a>, terms: NatFoldTerms,
    other: DefnEvaluationBody<'p, 'a>, other_terms: NatFoldTerms)
    requires
        plan.body_matches_at_rank(rank, body),
        nat_fold_terms_match(body.source.text_model(), body.forms@, body.at, Some(terms)),
        scalar_fold_witness(plan, rank, other, other_terms),
    ensures atom_fold_at(body, terms),
{
    plan.bodies_at_rank_agree(rank, body, other);
    signature_result_types_agree(body.signature, other.signature);
    nat_fold_term_results_agree(body.source.text_model(), body.forms@, body.at, Some(terms), Some(other_terms));
}

proof fn reject_unsupported_layout<'p, 'a>(plan: &DefnCallPlan<'p, 'a>, position: crate::project::DefnPosition,
    rank: usize, body: DefnEvaluationBody<'p, 'a>, terms: NatFoldTerms)
    requires
        plan.order_model().contains(position), rank == plan.order_model().index_of(position),
        plan.body_matches_at_rank(rank, body),
        nat_fold_terms_match(body.source.text_model(), body.forms@, body.at, Some(terms)),
        !atom_fold_at(body, terms),
    ensures !scalar_fold_supported(plan, position),
{
    if scalar_fold_supported(plan, position) {
        let (other, other_terms) = choose|other: DefnEvaluationBody<'p, 'a>, other_terms: NatFoldTerms|
            #[trigger] scalar_fold_witness(plan, rank, other, other_terms);
        supported_layout_agrees(plan, rank, body, terms, other, other_terms);
    }
}
fn supported_atom(forms: &[Form], at: usize) -> (supported: bool)
    ensures supported == atom_at(forms@, at),
{
    matches!(forms.get(at), Some(Form::Atom {
        kind: AtomKind::Name | AtomKind::Natural | AtomKind::NegativeInteger, ..
    }))
}

/// 指定した補助関数が対応する形の自然数反復なら、評価に使う本体の位置を返す。
///
/// 回数は自然数のリテラルか仮引数から評価する。初期値には真偽値・整数・仮引数のアトムを使える。
/// 反復本体は添字と累積値を局所束縛に加えた環境で評価する。式の評価規則は補助関数と共通である。
/// 補助関数の本体の根にある反復だけを扱い、対応外の場合は `None` を返す。
pub fn prepare_scalar_fold<'plan, 'p, 'a>(
    plan: &'plan DefnCallPlan<'p, 'a>, position: crate::project::DefnPosition,
) -> (entry: Option<ScalarFoldEntry<'plan, 'p, 'a>>)
    ensures entry.is_some() == scalar_fold_supported(plan, position),
        entry matches Some(found) ==> {
        &&& found.position_matches(plan, position)
    },
{
    let rank = plan.rank_of(position)?;
    let Some((body, terms)) = planned_nat_fold(plan, rank) else {
        proof {
            if scalar_fold_supported(plan, position) {
                let (other, other_terms) = choose|other: DefnEvaluationBody<'p, 'a>, other_terms: NatFoldTerms|
                    #[trigger] scalar_fold_witness(plan, rank, other, other_terms);
                assert(nat_fold_terms_match(other.source.text_model(), other.forms@, other.at, None));
                nat_fold_term_results_agree(
                    other.source.text_model(), other.forms@, other.at, Some(other_terms), None,
                );
            }
        }
        return None;
    };
    if !supported_atom(body.forms, terms.count)
        || !supported_atom(body.forms, terms.initial)
        || !check_scalar_body_syntax(body.source.text(), body.forms, terms.body)
    {
        proof { reject_unsupported_layout(plan, position, rank, body, terms); }
        return None;
    }
    let ty = body.signature.result_type.ty;
    if ty.list_depth != 0 || !matches!(ty.atom, DataTypeAtom::Builtin(
        BuiltinDataType::Bool | BuiltinDataType::Integer(_),
    )) {
        proof { reject_unsupported_layout(plan, position, rank, body, terms); }
        return None;
    }
    proof {
        let selected = plan.order_model().index_of(position) as usize;
        assert(selected == rank);
        assert(scalar_fold_witness(plan, selected, body, terms));
        assert(scalar_fold_supported(plan, position));
    }
    Some(ScalarFoldEntry { plan, rank, terms, origin: Ghost(body) })
}

impl<'plan, 'p, 'a> ScalarFoldEntry<'plan, 'p, 'a> {
    /// 入口を選んだ宣言位置と型検査計画を表す。
    pub closed spec fn position_matches(&self, plan: &DefnCallPlan<'p, 'a>, position: crate::project::DefnPosition)
        -> bool
    {
        self.plan == plan && self.rank < plan.order_model().len()
            && plan.order_model()[self.rank as int] == position
    }


    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        &&& self.plan.body_matches_at_rank(self.rank, self.origin@)
        &&& nat_fold_terms_match(self.origin@.source.text_model(), self.origin@.forms@, self.origin@.at, Some(self.terms))
        &&& ordered_terms(self.terms, self.origin@)
    }


    /// 初期状態と診断が、対象の本体と仮引数に対応することを表す。
    pub closed spec fn start_matches(&self, values: Seq<ScalarValue>,
        result: Result<ScalarFoldExecution<'plan, 'a>, ScalarBindingError<'p, 'a>>) -> bool
    {
        match result {
            Ok(state) => state.is_initial() && state.terms == self.terms
                && binding_at_rank_matches(self.plan, self.rank, values, Ok(state.root_frame())),
            Err(error) => binding_at_rank_matches(self.plan, self.rank, values, Err(error)),
        }
    }
    /// 実引数を署名に照合し、回数を評価する状態を作る。
    ///
    /// # Errors
    ///
    /// 実引数の個数や型が署名に合わなければ、元の位置を持つ診断を返す。
    pub fn start(&self, values: Vec<ScalarValue>)
        -> (result: Result<ScalarFoldExecution<'plan, 'a>, ScalarBindingError<'p, 'a>>)
        ensures self.start_matches(values@, result),
    {
        proof { use_type_invariant(self); }
        let frame = bind_scalar_call(self.plan, self.rank, values)?;
        proof {
            self.plan.bodies_at_rank_agree(self.rank, self.origin@, frame.body_model());
        }
        Ok(ScalarFoldExecution { plan: self.plan, rank: self.rank, frame: Some(frame), terms: self.terms, phase: FoldPhase::Count })
    }
}

spec fn bound_value(terms: NatFoldTerms, frame: &ScalarCallFrame, at: usize, index: u64, acc: ScalarValue)
    -> Option<ScalarValue>
{
    let body = frame.body_model();
    let forms = body.forms@;
    let source = body.source.text_model();
    let word = spelling(source, forms[at as int]);
    if !(forms[at as int] matches Form::Atom { kind: AtomKind::Name, .. }) {
        None
    } else if word == spelling(source, forms[terms.index_binding as int]) {
        Some(ScalarValue::Integer(IntegerValue::Nat(index)))
    } else if word == spelling(source, forms[terms.accumulator_binding as int]) {
        Some(acc)
    } else {
        None
    }
}


fn fold_bindings<'p, 'a>(
    terms: NatFoldTerms, frame: &ScalarCallFrame<'p, 'a>, index: u64, acc: ScalarValue,
) -> (bindings: ScalarFoldBindings<'a>)
    requires ordered_terms(terms, frame.body_model()),
    ensures
        bindings.index_name.spec_bytes() == spelling(frame.body_model().source.text_model(),
            frame.body_model().forms@[terms.index_binding as int]),
        bindings.accumulator_name.spec_bytes() == spelling(frame.body_model().source.text_model(),
            frame.body_model().forms@[terms.accumulator_binding as int]),
        bindings.index == index && bindings.accumulator == acc,
{
    proof { use_type_invariant(frame); }
    let body = frame.body();
    let source = body.source.text();
    ScalarFoldBindings {
        index_name: source_word(source, body.forms, terms.index_binding),
        accumulator_name: source_word(source, body.forms, terms.accumulator_binding),
        index, accumulator: acc,
    }
}
fn iteration_binding(
    terms: NatFoldTerms, frame: &ScalarCallFrame, at: usize, index: u64, acc: ScalarValue,
) -> (value: Option<ScalarValue>)
    requires ordered_terms(terms, frame.body_model()), at < frame.body_model().forms@.len(),
    ensures value == bound_value(terms, frame, at, index, acc),
{
    proof { use_type_invariant(frame); }
    let body = frame.body();
    if !matches!(body.forms[at], Form::Atom { kind: AtomKind::Name, .. }) {
        return None;
    }
    let source = body.source.text();
    let word = source_word(source, body.forms, at);
    if is_spelling(word, source_word(source, body.forms, terms.index_binding)) {
        Some(ScalarValue::Integer(IntegerValue::Nat(index)))
    } else if is_spelling(word, source_word(source, body.forms, terms.accumulator_binding)) {
        Some(acc)
    } else {
        None
    }
}

spec fn operand_matches<'p, 'a>(
    frame: &ScalarCallFrame<'p, 'a>, at: usize, ty: DataType<'a>, local: Option<ScalarValue>,
    result: Result<ScalarValue, ScalarExecutionError<'p, 'a>>,
) -> bool {
    match local {
        Some(value) if scalar_fits(value, ty) => result == Ok(value),
        Some(_) => deferred(frame, at, result),
        None => {
            let converted = match result {
                Ok(value) => Ok(Some(value)),
                Err(ScalarExecutionError::Literal(error)) => Err(error),
                _ => Ok(None),
            };
            &&& scalar_atom_matches(frame, at, ty, converted)
            &&& result.is_ok() || result matches Err(ScalarExecutionError::Literal(_))
                || deferred(frame, at, result)
        },
    }
}

spec fn deferred<'p, 'a>(
    frame: &ScalarCallFrame<'p, 'a>, at: usize, result: Result<ScalarValue, ScalarExecutionError<'p, 'a>>,
) -> bool {
    let body = frame.body_model();
    result matches Err(ScalarExecutionError::Deferred { source, span }) && *source == *body.source
        && span == form_span(body.forms@[at as int])
}

fn evaluate_operand<'p, 'a>(
    frame: &ScalarCallFrame<'p, 'a>, at: usize, ty: DataType<'a>, local: Option<ScalarValue>,
) -> (result: Result<ScalarValue, ScalarExecutionError<'p, 'a>>)
    requires at < frame.body_model().forms@.len(),
    ensures operand_matches(frame, at, ty, local, result),
        result matches Ok(value) ==> scalar_fits(value, ty),
{
    let value = match local {
        Some(value) if scalar_matches(value, ty) => Some(value),
        Some(_) => None,
        None => match frame.evaluate_atom(at, ty) {
            Ok(value) => value,
            Err(error) => return Err(ScalarExecutionError::Literal(error)),
        },
    };
    match value {
        Some(value) => Ok(value),
        None => {
            let body = frame.body();
            Err(ScalarExecutionError::Deferred { source: body.source, span: span_of(&body.forms[at]) })
        },
    }
}

impl<'p, 'a> ScalarFoldExecution<'p, 'a> {

    spec fn root_frame(&self) -> ScalarCallFrame<'p, 'a> {
        match self.phase {
            FoldPhase::Expression { state, .. } => state.root_frame_model(),
            _ => self.frame->Some_0,
        }
    }

    /// 反復本体が単一のアトムで、複合式の評価状態を必要としないことを表す。
    pub closed spec fn atom_body(&self) -> bool {
        atom_at(self.root_frame().body_model().forms@, self.terms.body)
    }

    spec fn same_context(&self, next: &Self) -> bool {
        &&& next.plan == self.plan && next.rank == self.rank && next.terms == self.terms
        &&& next.root_frame().body_model() == self.root_frame().body_model()
        &&& next.root_frame().parameter_values_model() == self.root_frame().parameter_values_model()
    }

    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        &&& ordered_terms(self.terms, self.root_frame().body_model())
        &&& self.plan.body_matches_at_rank(self.rank, self.root_frame().body_model())
        &&& self.frame.is_none() == (self.phase is Expression)
        &&& (self.phase matches FoldPhase::Expression { state, .. } ==> state.plan_model() == self.plan && state.result_type_model() == self.result_type() && !self.atom_body())
        &&& match self.phase {
            FoldPhase::Select(fold) => scalar_fits(fold.model().2, self.result_type()),
            FoldPhase::Body(iteration) => scalar_fits(iteration.model().2, self.result_type()),
            _ => true,
        }
    }

    /// この状態が回数を評価する前の初期状態であることを表す。
    pub closed spec fn is_initial(&self) -> bool { self.phase is Count }

    /// 評価値が従う補助関数の戻り型。
    pub closed spec fn result_type(&self) -> DataType<'a> {
        self.root_frame().body_model().signature.result_type.ty
    }


    /// 本体がアトムの場合に、終了までに残る遷移数の上界を表す。
    pub closed spec fn remaining_steps_bound(&self) -> nat {
        match self.phase {
            FoldPhase::Count => 2 * u64::MAX as nat + 3,
            FoldPhase::Initial(count) => 2 * count as nat + 2,
            FoldPhase::Select(fold) => 2 * (fold.model().0 - fold.model().1) as nat + 1,
            FoldPhase::Body(iteration) => 2 * (iteration.model().0 - iteration.model().1) as nat,
            FoldPhase::Expression { .. } => 0,
        }
    }

    spec fn iteration_operand_matches(
        &self, iteration: NatFoldIteration<ScalarValue>, result: Result<ScalarValue, ScalarExecutionError<'p, 'a>>,
    ) -> bool {
        let frame = self.root_frame();
        let (_, at, acc) = iteration.model();
        let local = bound_value(self.terms, &frame, self.terms.body, at, acc);
        operand_matches(&frame, self.terms.body, self.result_type(), local, result)
    }

    spec fn receiving_body(&self, iteration: NatFoldIteration<ScalarValue>, value: ScalarValue, next: &Self) -> bool {
        let (count, at, _) = iteration.model();
        next.phase matches FoldPhase::Select(fold) && at < count
            && fold.model() == (count, (at + 1) as u64, value)
    }

    spec fn starts_body_expression(&self, before: NatFoldIteration<ScalarValue>, next: &Self) -> bool {
        let site = ScalarExpressionSite { at: self.terms.body, expected: self.result_type() };
        &&& !self.atom_body()
        &&& next.phase matches FoldPhase::Expression { state, iteration }
        &&& iteration == before
        &&& state.starts_expression(self.plan, self.rank, state.root_frame_model(), site)
        &&& state.root_frame_model().fold_bindings_model() matches Some(bindings)
        &&& bindings.index == iteration.model().1 && bindings.accumulator == iteration.model().2
        &&& bindings.index_name.spec_bytes() == spelling(self.root_frame().body_model().source.text_model(),
            self.root_frame().body_model().forms@[self.terms.index_binding as int])
        &&& bindings.accumulator_name.spec_bytes() == spelling(self.root_frame().body_model().source.text_model(),
            self.root_frame().body_model().forms@[self.terms.accumulator_binding as int])
    }
    /// 型付き環境で本体の値を求める一回の遷移を表す。
    pub closed spec fn step_matches(&self, result: FoldResult<'p, 'a>) -> bool {
        let frame = &self.root_frame();
        let terms = self.terms;
        let same_context = result matches Ok(ScalarFoldSlice::Suspended(next)) ==>
            self.same_context(&next);
        &&& same_context
        &&& match self.phase {
            FoldPhase::Count => match result {
                Ok(ScalarFoldSlice::Suspended(next)) => next.phase matches FoldPhase::Initial(n) &&
                    operand_matches(frame, terms.count, nat_type(), None, Ok(ScalarValue::Integer(IntegerValue::Nat(n)))),
                Err(error) => operand_matches(frame, terms.count, nat_type(), None, Err(error)),
                _ => false,
            },
            FoldPhase::Initial(count) => match result {
                Ok(ScalarFoldSlice::Suspended(next)) => next.phase matches FoldPhase::Select(fold) &&
                    fold.model().0 == count && fold.model().1 == 0 &&
                    operand_matches(frame, terms.initial, self.result_type(), None, Ok(fold.model().2)),
                Err(error) => operand_matches(frame, terms.initial, self.result_type(), None, Err(error)),
                _ => false,
            },
            FoldPhase::Select(fold) => {
                let (count, at, value) = fold.model();
                match result {
                    Ok(ScalarFoldSlice::Suspended(next)) => next.phase matches FoldPhase::Body(iteration) &&
                        at < count && iteration.model() == (count, at, value),
                    Ok(ScalarFoldSlice::Complete(last)) => at == count && last == value,
                    _ => false,
                }
            },

            FoldPhase::Body(iteration) => match result {
                Ok(ScalarFoldSlice::Suspended(next)) => {
                    if self.atom_body() {
                        next.phase matches FoldPhase::Select(fold)
                            && self.receiving_body(iteration, fold.model().2, &next)
                            && self.iteration_operand_matches(iteration, Ok(fold.model().2))
                    } else {
                        self.starts_body_expression(iteration, &next)
                    }
                },
                Err(error) => self.atom_body() && self.iteration_operand_matches(iteration, Err(error)),
                _ => false,
            },
            FoldPhase::Expression { state, iteration } => match result {
                Ok(ScalarFoldSlice::Suspended(next)) => match next.phase {
                    FoldPhase::Expression { state: after, iteration: pending } =>
                        pending == iteration && state.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
                    FoldPhase::Select(fold) => self.receiving_body(iteration, fold.model().2, &next)
                        && state.step_matches(Ok(ScalarExecutionSlice::Complete(fold.model().2))),
                    _ => false,
                },
                Err(error) => state.step_matches(Err(error)),
                _ => false,
            },
        }
    }

    fn step(self) -> (result: FoldResult<'p, 'a>)
        ensures self.step_matches(result),
            result matches Ok(ScalarFoldSlice::Suspended(next)) ==>
                next.result_type() == self.result_type() && next.atom_body() == self.atom_body()
                    && (self.atom_body() ==> next.remaining_steps_bound() < self.remaining_steps_bound()),
            result matches Ok(ScalarFoldSlice::Complete(value)) ==> scalar_fits(value, self.result_type()),
    {

        proof { use_type_invariant(&self); reveal(ScalarFoldExecution::step_matches); }
        let Self { plan, rank, frame, terms, phase } = self;
        if let FoldPhase::Expression { state, iteration } = phase {
            let (result, returned) = state.step_saving_frame();
            return match result? {
                ScalarExecutionSlice::Suspended(state) => Ok(ScalarFoldSlice::Suspended(Self {
                    plan, rank, frame: None, terms, phase: FoldPhase::Expression { state, iteration },
                })),
                ScalarExecutionSlice::Complete(value) => {
                    let Some(scoped) = returned else { unreachable!() };
                    let frame = Some(scoped.with_fold_bindings(None));
                    let phase = FoldPhase::Select(iteration.receive::<ScalarExecutionError>(Ok(value))?);
                    Ok(ScalarFoldSlice::Suspended(Self { plan, rank, frame, terms, phase }))
                },
            };
        }
        let Some(frame) = frame else { unreachable!() };
        let ty = frame.body().signature.result_type.ty;
        let phase = match phase {
            FoldPhase::Count => {
                let value = evaluate_operand(&frame, terms.count, count_type(), None)?;
                let ScalarValue::Integer(IntegerValue::Nat(count)) = value else { unreachable!() };
                FoldPhase::Initial(count)
            },
            FoldPhase::Initial(count) => FoldPhase::Select(NatFold::start(
                count, evaluate_operand(&frame, terms.initial, ty, None)?,
            )),
            FoldPhase::Select(fold) => match fold.next() {
                NatFoldNext::Evaluate(iteration) => FoldPhase::Body(iteration),
                NatFoldNext::Complete(value) => return Ok(ScalarFoldSlice::Complete(value)),
            },
            FoldPhase::Body(iteration) => {
                if !supported_atom(frame.body().forms, terms.body) {
                    let bindings = fold_bindings(terms, &frame, iteration.index(), *iteration.accumulator());
                    let scoped = frame.with_fold_bindings(Some(bindings));
                    let site = ScalarExpressionSite { at: terms.body, expected: ty };
                    let state = ScalarExecution::start_expression(plan, rank, scoped, site);
                    return Ok(ScalarFoldSlice::Suspended(Self {
                        plan, rank, frame: None, terms, phase: FoldPhase::Expression { state, iteration },
                    }));
                }
                let local = iteration_binding(terms, &frame, terms.body, iteration.index(), *iteration.accumulator());
                FoldPhase::Select(iteration.receive(evaluate_operand(&frame, terms.body, ty, local))?)
            },
            FoldPhase::Expression { .. } => unreachable!(),
        };
        Ok(ScalarFoldSlice::Suspended(Self { plan, rank, frame: Some(frame), terms, phase }))
    }
}

type FoldResult<'p, 'a> = Result<ScalarFoldSlice<'p, 'a>, ScalarExecutionError<'p, 'a>>;

spec fn fold_path<'p, 'a>(start: ScalarFoldExecution<'p, 'a>, states: Seq<ScalarFoldExecution<'p, 'a>>) -> bool {
    &&& states.len() > 0
    &&& states[0] == start
    &&& forall|i: int| 0 <= i < states.len() - 1 ==>
        (#[trigger] states[i]).step_matches(Ok(ScalarFoldSlice::Suspended(states[i + 1])))
}

spec fn fold_path_outcome<'p, 'a>(
    start: ScalarFoldExecution<'p, 'a>, states: Seq<ScalarFoldExecution<'p, 'a>>, result: FoldResult<'p, 'a>, used: nat,
) -> bool {
    &&& fold_path(start, states)
    &&& match result {
        Ok(ScalarFoldSlice::Suspended(next)) => states.last() == next && states.len() == used + 1,
        _ => states.last().step_matches(result) && states.len() == used,
    }
}

/// 実行した回数と、その中で通過した反復の遷移を表す。
pub closed spec fn scalar_fold_slice_matches<'p, 'a>(
    start: ScalarFoldExecution<'p, 'a>, fuel: nat, result: FoldResult<'p, 'a>, used: nat,
) -> bool {
    &&& 0 < used <= fuel
    &&& result matches Ok(ScalarFoldSlice::Suspended(_)) ==> used == fuel
    &&& exists|states: Seq<ScalarFoldExecution<'p, 'a>>|
        #[trigger] fold_path_outcome(start, states, result, used)
}

proof fn extend_fold_path<'p, 'a>(
    start: ScalarFoldExecution<'p, 'a>, states: Seq<ScalarFoldExecution<'p, 'a>>, next: ScalarFoldExecution<'p, 'a>,
)
    requires fold_path(start, states), states.last().step_matches(Ok(ScalarFoldSlice::Suspended(next))),
    ensures fold_path(start, states.push(next)),
{
    let after = states.push(next);
    assert forall|i: int| 0 <= i < after.len() - 1 implies
        (#[trigger] after[i]).step_matches(Ok(ScalarFoldSlice::Suspended(after[i + 1]))) by {
        if i + 1 < states.len() {
            assert(after[i] == states[i]);
            assert(after[i + 1] == states[i + 1]);
        }
    }
}

/// 一時停止した反復の実行枠を次の実行枠とつなぎ、値または診断までの遷移数を合成する。
pub proof fn resumed_scalar_fold_matches<'p, 'a>(
    start: ScalarFoldExecution<'p, 'a>, first: nat, suspended: ScalarFoldExecution<'p, 'a>,
    next: nat, result: FoldResult<'p, 'a>, used: nat,
)
    requires scalar_fold_slice_matches(start, first, Ok(ScalarFoldSlice::Suspended(suspended)), first),
        scalar_fold_slice_matches(suspended, next, result, used),
    ensures scalar_fold_slice_matches(start, first + next, result, first + used),
{
    let pre = choose|states: Seq<ScalarFoldExecution<'p, 'a>>|
        #[trigger] fold_path_outcome(start, states, Ok(ScalarFoldSlice::Suspended(suspended)), first);
    let post = choose|states: Seq<ScalarFoldExecution<'p, 'a>>|
        #[trigger] fold_path_outcome(suspended, states, result, used);
    let combined = pre + post.skip(1);
    assert forall|i: int| 0 <= i < combined.len() - 1 implies
        (#[trigger] combined[i]).step_matches(Ok(ScalarFoldSlice::Suspended(combined[i + 1]))) by {
        if i + 1 < pre.len() {
            assert(combined[i] == pre[i] && combined[i + 1] == pre[i + 1]);
        } else {
            let j = i - pre.len() + 1;
            assert(combined[i] == post[j]) by {
                if j == 0 { assert(i == pre.len() - 1); }
            }
            assert(combined[i + 1] == post[j + 1]);
        }
    }
    assert(combined.last() == post.last()) by {
        if post.len() == 1 { assert(post.last() == suspended); }
    }
    assert(fold_path_outcome(start, combined, result, first + used));
}

impl<'p, 'a> ScalarFoldExecution<'p, 'a> {
    /// 実行枠内で反復を進め、実行した遷移数を返す。
    ///
    /// 一時停止時は枠を使い切った状態を返す。完了や失敗を返す最後の遷移も数える。
    ///
    /// # Errors
    ///
    /// 整数リテラルや演算結果が型の範囲外の場合は、評価を止めた式の元の位置を持つ診断を返す。
    /// 未対応の式に到達した場合も、その式の位置を返す。
    pub fn run_slice_with_steps(self, fuel: core::num::NonZeroUsize) -> (outcome: (FoldResult<'p, 'a>, usize))
        ensures scalar_fold_slice_matches(self, fuel@ as nat, outcome.0, outcome.1 as nat),
            0 < outcome.1 <= fuel@,
            outcome.0 matches Ok(ScalarFoldSlice::Suspended(next)) ==> outcome.1 == fuel@
                && (self.atom_body() ==> next.remaining_steps_bound() + outcome.1 <= self.remaining_steps_bound()),
            outcome.0 matches Ok(ScalarFoldSlice::Complete(value)) ==> scalar_fits(value, self.result_type()),
    {
        let budget = fuel.get();
        let mut used = 0;
        let mut state = self;
        let ghost mut states = seq![self];
        while used < budget
            invariant
                used <= budget == fuel@,
                states.len() == used + 1,
                states.last() == state,
                state.result_type() == self.result_type(),
                state.atom_body() == self.atom_body(),
                self.atom_body() ==> state.remaining_steps_bound() + used <= self.remaining_steps_bound(),
                fold_path(self, states),
            decreases budget - used,
        {
            used += 1;
            match state.step() {
                Ok(ScalarFoldSlice::Suspended(next)) => {
                    proof { extend_fold_path(self, states, next); states = states.push(next); }
                    state = next;
                },
                result => {
                    assert(fold_path_outcome(self, states, result, used as nat));
                    return (result, used);
                },
            }
        }
        let result = Ok(ScalarFoldSlice::Suspended(state));
        assert(fold_path_outcome(self, states, result, used as nat));
        (result, used)
    }
}

} // verus!
