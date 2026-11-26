//! 複数の初期化式を元の環境で評価し、得られた束縛列で `let` の本体を評価する。

use super::*;
use crate::ncg2m::defn::span_of;
use crate::ncg2m::forms::source_word;
use crate::ncg2m::let_syntax::{LetHeader, read_let_structure};
use crate::project::DefnPosition;
#[cfg(verus_only)]
use crate::ncg2m::forms::spelling;
#[cfg(verus_only)]
use crate::ncg2m::let_syntax::{let_structure, valid_bindings};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::TypedLetInitializer;

verus! {

/// 補助関数の本体全体を `let` として評価するための呼び出し計画と構文位置。
pub struct ScalarLetEntry<'plan, 'p, 'a> {
    plan: &'plan DefnCallPlan<'p, 'a>,
    rank: usize,
    header: LetHeader,
    origin: Ghost<DefnEvaluationBody<'p, 'a>>,
}

/// 初期化式や本体の途中から再開できる評価状態。
pub struct ScalarLetExecution<'plan, 'p, 'a> {
    plan: &'plan DefnCallPlan<'p, 'a>,
    rank: usize,
    header: LetHeader,
    phase: LetPhase<'plan, 'p, 'a>,
}

enum LetPhase<'plan, 'p, 'a> {
    Select { frame: ScalarCallFrame<'p, 'a>, bindings: Vec<ScalarLocal<'a>> },
    Initializer {
        state: ScalarExecution<'plan, 'p, 'a>,
        bindings: Vec<ScalarLocal<'a>>,
        ty: Ghost<DataType<'a>>,
    },
    Body(ScalarExecution<'plan, 'p, 'a>),
}

/// 実行枠を使い切った状態か、`let` の本体の値。
pub enum ScalarLetSlice<'plan, 'p, 'a> {
    /// 次の遷移から再開できる。
    Suspended(ScalarLetExecution<'plan, 'p, 'a>),
    /// すべての初期化式と本体を評価した結果。
    Complete(ScalarValue),
}

type LetResult<'plan, 'p, 'a> = Result<ScalarLetSlice<'plan, 'p, 'a>, ScalarExecutionError<'p, 'a>>;

spec fn scalar_type_at(ty: DataType) -> bool {
    ty.list_depth == 0 && ty.atom matches DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_))
}

spec fn valid_let_root(body: DefnEvaluationBody, header: &LetHeader) -> bool {
    &&& let_structure(body.source.text_model(), body.forms@, body.at) == Ok((header.bindings@, header.body))
    &&& header.body < body.forms@.len()
    &&& valid_bindings(body.forms@, header.bindings@, body.at, header.body)
    &&& scalar_type_at(body.signature.result_type.ty)
}

impl<'plan, 'p, 'a> ScalarLetEntry<'plan, 'p, 'a> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        self.plan.body_matches_at_rank(self.rank, self.origin@) && valid_let_root(self.origin@, &self.header)
    }

    /// 指定された補助関数と呼び出し計画に対応することを表す。
    pub closed spec fn reaches(&self, plan: &DefnCallPlan<'p, 'a>, position: DefnPosition) -> bool {
        self.plan == plan && self.rank < plan.order_model().len() && plan.order_model()[self.rank as int] == position
    }

    /// 実引数を検査し、最初の初期化式から始める評価状態を返す。
    ///
    /// # Errors
    ///
    /// 個数や型が署名に合わない場合は、元の宣言位置を持つ診断を返す。
    pub fn start(self, values: Vec<ScalarValue>) -> (result: Result<ScalarLetExecution<'plan, 'p, 'a>, ScalarBindingError<'p, 'a>>)
        ensures self.start_matches(values@, result),
    {
        proof { use_type_invariant(&self); }
        let frame = bind_scalar_call(self.plan, self.rank, values)?;
        proof {
            let body = frame.body_model();
            self.plan.bodies_at_rank_agree(self.rank, self.origin@, body);
            crate::ncg2m::data_types::signature_result_types_agree(self.origin@.signature, body.signature);
            assert(valid_let_root(body, &self.header));
            reveal(initialized_values_match);
        }
        let Self { plan, rank, header, .. } = self;
        Ok(ScalarLetExecution { plan, rank, header, phase: LetPhase::Select { frame, bindings: Vec::new() } })
    }

    /// 初期状態が元の補助関数と実引数に対応することを表す。
    pub closed spec fn start_matches(
        &self, values: Seq<ScalarValue>, result: Result<ScalarLetExecution<'plan, 'p, 'a>, ScalarBindingError<'p, 'a>>,
    ) -> bool {
        match result {
            Ok(state) => {
                &&& state.plan == self.plan && state.rank == self.rank && state.header == self.header
                &&& state.phase matches LetPhase::Select { frame, bindings }
                &&& bindings@.len() == 0 && binding_at_rank_matches(self.plan, self.rank, values, Ok(frame))
            },
            Err(error) => binding_at_rank_matches(self.plan, self.rank, values, Err(error)),
        }
    }
}

spec fn scalar_let_candidate<'p, 'a>(plan: &DefnCallPlan<'p, 'a>, rank: usize, body: DefnEvaluationBody<'p, 'a>) -> bool {
    &&& plan.body_matches_at_rank(rank, body)
    &&& scalar_type_at(body.signature.result_type.ty)
    &&& let_structure(body.source.text_model(), body.forms@, body.at).is_ok()
}

/// 計画内で指定された補助関数の本体全体が `let` であり、戻り型がスカラー型であることを表す。
pub closed spec fn scalar_let_supported<'p, 'a>(plan: &DefnCallPlan<'p, 'a>, position: DefnPosition) -> bool {
    let rank = plan.order_model().index_of(position) as usize;
    &&& plan.order_model().contains(position)
    &&& exists|body: DefnEvaluationBody<'p, 'a>| #[trigger] scalar_let_candidate(plan, rank, body)
}

proof fn selected_let_root_agrees<'p, 'a>(
    plan: &DefnCallPlan<'p, 'a>, position: DefnPosition, rank: usize, body: DefnEvaluationBody<'p, 'a>,
)
    requires
        plan.order_model().contains(position), rank == plan.order_model().index_of(position),
        plan.body_matches_at_rank(rank, body),
    ensures scalar_let_supported(plan, position) == (
        scalar_type_at(body.signature.result_type.ty)
            && let_structure(body.source.text_model(), body.forms@, body.at).is_ok()),
{
    assert(rank == plan.order_model().index_of(position) as usize);
    if scalar_let_candidate(plan, rank, body) {
        assert(exists|origin: DefnEvaluationBody<'p, 'a>| #[trigger] scalar_let_candidate(plan, rank, origin));
        assert(scalar_let_supported(plan, position));
    }
    if scalar_let_supported(plan, position) {
        let other = choose|other: DefnEvaluationBody<'p, 'a>| #[trigger] scalar_let_candidate(plan, rank, other);
        plan.bodies_at_rank_agree(rank, body, other);
        crate::ncg2m::data_types::signature_result_types_agree(body.signature, other.signature);
        assert(scalar_let_candidate(plan, rank, body));
    }
}

/// 本体全体が `let` の補助関数から評価を始めるための情報を返す。
///
/// 根の形または戻り型が対象外の場合は `None` を返す。初期化式は評価時に一つずつ処理する。
pub fn prepare_scalar_let<'plan, 'p, 'a>(plan: &'plan DefnCallPlan<'p, 'a>, position: DefnPosition)
    -> (result: Option<ScalarLetEntry<'plan, 'p, 'a>>)
    ensures result.is_some() == scalar_let_supported(plan, position),
        result matches Some(entry) ==> entry.reaches(plan, position),
{
    let rank = plan.rank_of(position)?;
    let body = plan.body_at_rank(rank)?;
    proof { selected_let_root_agrees(plan, position, rank, body); }
    let ty = body.signature.result_type.ty;
    if ty.list_depth != 0 || !matches!(ty.atom, DataTypeAtom::Builtin(BuiltinDataType::Bool | BuiltinDataType::Integer(_))) {
        return None;
    }
    let header = read_let_structure(body.source.text(), body.forms, body.at).ok()?;
    Some(ScalarLetEntry { plan, rank, header, origin: Ghost(body) })
}

spec fn initializer_row_matches(
    at: usize, index: usize, name: usize, value: usize, row: TypedLetInitializer,
) -> bool {
    let (owner, i, word, expression, _) = row.model();
    owner == at && i == index && word == name && expression == value
}

#[verifier::opaque]
spec fn first_initializer_type(rows: Seq<TypedLetInitializer>, scan: nat,
    owner: usize, index: usize, name: usize, value: usize,
) -> Option<BuiltinDataType>
    decreases rows.len() - scan,
{
    if scan >= rows.len() {
        None
    } else if initializer_row_matches(owner, index, name, value, rows[scan as int]) {
        rows[scan as int].model().4
    } else {
        first_initializer_type(rows, scan + 1, owner, index, name, value)
    }
}

#[verifier::opaque]
spec fn initializer_type(
    plan: &DefnCallPlan, rank: usize, owner: usize, index: usize, name: usize, value: usize,
) -> Option<BuiltinDataType> {
    match plan.initializer_model_at_rank(rank) {
        Some(rows) => first_initializer_type(rows, 0, owner, index, name, value),
        None => None,
    }
}

fn read_initializer_type(
    plan: &DefnCallPlan, rank: usize, owner: usize, index: usize, name: usize, value: usize,
) -> (ty: Option<BuiltinDataType>)
    ensures ty == initializer_type(plan, rank, owner, index, name, value),
{
    proof { reveal(initializer_type); }
    let rows = plan.let_initializers_at_rank(rank)?;
    let mut at = 0;
    while at < rows.len()
        invariant
            plan.initializer_model_at_rank(rank) == Some(rows@), at <= rows@.len(),
            first_initializer_type(rows@, at as nat, owner, index, name, value)
                == initializer_type(plan, rank, owner, index, name, value),
        decreases rows@.len() - at,
    {
        proof { reveal(first_initializer_type); }
        let (from, i, word, expression, ty) = rows[at].binding_site();
        if from == owner && i == index && word == name && expression == value {
            return ty;
        }
        at += 1;
    }
    proof { reveal(first_initializer_type); }
    None
}

spec fn same_base(frame: ScalarCallFrame, after: ScalarCallFrame) -> bool {
    &&& frame.body_model() == after.body_model()
    &&& frame.parameter_values_model() == after.parameter_values_model()
    &&& frame.fold_bindings_model() == after.fold_bindings_model()
}

spec fn expression_type<'a>(builtin: BuiltinDataType) -> DataType<'a> {
    DataType { atom: DataTypeAtom::Builtin(builtin), list_depth: 0 }
}

fn runtime_type<'a>(builtin: BuiltinDataType) -> (ty: DataType<'a>)
    ensures ty == expression_type(builtin),
{
    DataType { atom: DataTypeAtom::Builtin(builtin), list_depth: 0 }
}

#[verifier::opaque]
spec fn initialized_values_match(
    plan: &DefnCallPlan, rank: usize, body: DefnEvaluationBody, header: &LetHeader, values: Seq<ScalarLocal>,
) -> bool {
    &&& values.len() <= header.bindings@.len()
    &&& forall|i: int| 0 <= i < values.len() ==> {
        let binding = header.bindings@[i];
        let local = #[trigger] values[i];
        &&& local.name.spec_bytes() == spelling(body.source.text_model(), body.forms@[binding.name as int])
        &&& match initializer_type(plan, rank, body.at, i as usize, binding.name, binding.value) {
            Some(builtin) => scalar_fits(local.value, expression_type(builtin)),
            None => false,
        }
    }
}

proof fn append_initialized_value(
    plan: &DefnCallPlan, rank: usize, body: DefnEvaluationBody, header: &LetHeader,
    current: Seq<ScalarLocal>, local: ScalarLocal, expected: DataType,
)
    requires
        initialized_values_match(plan, rank, body, header, current), current.len() < header.bindings@.len(),
        {
            let row = header.bindings@[current.len() as int];
            &&& local.name.spec_bytes() == spelling(body.source.text_model(), body.forms@[row.name as int])
            &&& initializer_type(plan, rank, body.at, current.len() as usize, row.name, row.value)
                matches Some(builtin) && expected == expression_type(builtin)
        },
        scalar_fits(local.value, expected),
    ensures initialized_values_match(plan, rank, body, header, current.push(local)),
{
    reveal(initialized_values_match);
    let grown = current.push(local);
    assert forall|i: int| 0 <= i < grown.len() implies {
        let binding = header.bindings@[i];
        let value = #[trigger] grown[i];
        &&& value.name.spec_bytes() == spelling(body.source.text_model(), body.forms@[binding.name as int])
        &&& match initializer_type(plan, rank, body.at, i as usize, binding.name, binding.value) {
            Some(builtin) => scalar_fits(value.value, expression_type(builtin)),
            None => false,
        }
    } by {
        if i < current.len() { assert(grown[i] == current[i]); }
        else { assert(i == current.len() && grown[i] == local); }
    };
}

impl<'plan, 'p, 'a> ScalarLetExecution<'plan, 'p, 'a> {
    spec fn frame(&self) -> ScalarCallFrame<'p, 'a> {
        match self.phase {
            LetPhase::Select { frame, .. } => frame,
            LetPhase::Initializer { state, .. } | LetPhase::Body(state) => state.root_frame_model(),
        }
    }

    spec fn binding_values(&self) -> Seq<ScalarLocal<'a>> {
        match self.phase {
            LetPhase::Select { bindings, .. } | LetPhase::Initializer { bindings, .. } => bindings@,
            LetPhase::Body(state) => state.root_frame_model().locals_model(),
        }
    }

    /// 本体の評価が成功した場合の戻り型。
    pub closed spec fn result_type(&self) -> DataType<'a> {
        self.frame().body_model().signature.result_type.ty
    }

    #[verifier::type_invariant]
    spec fn ready(&self) -> bool {
        let frame = self.frame();
        let body = frame.body_model();
        let values = self.binding_values();
        &&& self.plan.body_matches_at_rank(self.rank, body)
        &&& valid_let_root(body, &self.header)
        &&& initialized_values_match(self.plan, self.rank, body, &self.header, values)
        &&& match self.phase {
            LetPhase::Select { frame, .. } => !frame.has_scoped_bindings(),
            LetPhase::Initializer { state, ty, .. } => {
                &&& values.len() < self.header.bindings@.len()
                &&& state.plan_model() == self.plan && state.result_type_model() == ty@
                &&& !state.root_frame_model().has_scoped_bindings()
                &&& {
                    let binding = self.header.bindings@[values.len() as int];
                    initializer_type(self.plan, self.rank, body.at, values.len() as usize, binding.name, binding.value)
                        matches Some(builtin) && ty@ == expression_type(builtin)
                }
            },
            LetPhase::Body(state) => values.len() == self.header.bindings@.len()
                && state.plan_model() == self.plan && state.result_type_model() == self.result_type(),
        }
    }

    /// 元の環境で進める次の初期化式か、本体の遷移を表す。
    pub closed spec fn step_matches(&self, result: LetResult<'plan, 'p, 'a>) -> bool {
        let frame = self.frame();
        let body = frame.body_model();
        let values = self.binding_values();
        &&& (result matches Ok(ScalarLetSlice::Suspended(next)) ==>
            next.plan == self.plan && next.rank == self.rank && next.header == self.header && same_base(frame, next.frame()))
        &&& match self.phase {
            LetPhase::Select { .. } => if values.len() == self.header.bindings@.len() {
                &&& result matches Ok(ScalarLetSlice::Suspended(next))
                &&& next.phase matches LetPhase::Body(state)
                &&& next.binding_values() == values
                &&& state.starts_expression(self.plan, self.rank, next.frame(),
                        ScalarExpressionSite { at: self.header.body, expected: self.result_type() })
            } else {
                let binding = self.header.bindings@[values.len() as int];
                match initializer_type(self.plan, self.rank, body.at, values.len() as usize, binding.name, binding.value) {
                    Some(builtin) => {
                        &&& result matches Ok(ScalarLetSlice::Suspended(next))
                        &&& next.phase matches LetPhase::Initializer { state, bindings, .. }
                        &&& bindings@ == values && state.starts_expression(self.plan, self.rank, frame,
                            ScalarExpressionSite { at: binding.value, expected: expression_type(builtin) })
                    },
                    None => result matches Err(ScalarExecutionError::Deferred { source, span })
                        && *source == *body.source && span == form_span(body.forms@[binding.value as int]),
                }
            },
            LetPhase::Initializer { state, .. } => match result {
                Ok(ScalarLetSlice::Suspended(next)) => match next.phase {
                    LetPhase::Initializer { state: after, bindings, .. } =>
                        bindings@ == values && state.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
                    LetPhase::Select { frame: resumed, bindings } => {
                        let binding = self.header.bindings@[values.len() as int];
                        &&& resumed == frame
                        &&& bindings@.len() == values.len() + 1 && bindings@.drop_last() == values
                        &&& bindings@.last().name.spec_bytes() == spelling(body.source.text_model(),
                            body.forms@[binding.name as int])
                        &&& state.step_matches(Ok(ScalarExecutionSlice::Complete(bindings@.last().value)))
                    },
                    _ => false,
                },
                Err(error) => state.step_matches(Err(error)),
                _ => false,
            },
            LetPhase::Body(state) => match result {
                Ok(ScalarLetSlice::Suspended(next)) => next.phase matches LetPhase::Body(after)
                    && state.step_matches(Ok(ScalarExecutionSlice::Suspended(after))),
                Ok(ScalarLetSlice::Complete(value)) => state.step_matches(Ok(ScalarExecutionSlice::Complete(value))),
                Err(error) => state.step_matches(Err(error)),
            },
        }
    }

    spec fn result_allowed(&self, result: LetResult<'plan, 'p, 'a>) -> bool {
        &&& self.step_matches(result)
        &&& (result matches Ok(ScalarLetSlice::Suspended(next)) ==> next.result_type() == self.result_type())
        &&& (result matches Ok(ScalarLetSlice::Complete(value)) ==> scalar_fits(value, self.result_type()))
    }

    fn step(self) -> (result: LetResult<'plan, 'p, 'a>)
        ensures self.result_allowed(result),
    {
        match &self.phase {
            LetPhase::Select { .. } => self.select_initializer_or_body(),
            LetPhase::Initializer { .. } => self.step_initializer(),
            LetPhase::Body(_) => self.step_body(),
        }
    }

    #[verifier::spinoff_prover]
    fn select_initializer_or_body(self) -> (result: LetResult<'plan, 'p, 'a>)
        requires self.phase is Select,
        ensures self.result_allowed(result),
    {
        proof { use_type_invariant(&self); reveal(ScalarLetExecution::step_matches); }
        let Self { plan, rank, header, phase } = self;
        let LetPhase::Select { frame, bindings } = phase else { unreachable!() };
        let index = bindings.len();
        assert(bindings@.len() <= header.bindings@.len()) by { reveal(initialized_values_match); };
        let phase = if index == header.bindings.len() {
            let ty = frame.body().signature.result_type.ty;
            let frame = frame.with_let_bindings(bindings);
            let site = ScalarExpressionSite { at: header.body, expected: ty };
            LetPhase::Body(ScalarExecution::start_expression(plan, rank, frame, site))
        } else {
            let body = frame.body();
            let binding = header.bindings[index];
            let Some(builtin) = read_initializer_type(plan, rank, body.at, index, binding.name, binding.value) else {
                return Err(ScalarExecutionError::Deferred {
                    source: body.source,
                    span: span_of(&body.forms[binding.value]),
                });
            };
            let ty = runtime_type(builtin);
            let site = ScalarExpressionSite { at: binding.value, expected: ty };
            let state = ScalarExecution::start_expression(plan, rank, frame, site);
            LetPhase::Initializer { state, bindings, ty: Ghost(ty) }
        };
        Ok(ScalarLetSlice::Suspended(Self { plan, rank, header, phase }))
    }

    #[verifier::spinoff_prover]
    fn step_initializer(self) -> (result: LetResult<'plan, 'p, 'a>)
        requires self.phase is Initializer,
        ensures self.result_allowed(result),
    {
        proof { use_type_invariant(&self); reveal(ScalarLetExecution::step_matches); }
        let ghost previous = self;
        let Self { plan, rank, header, phase } = self;
        let LetPhase::Initializer { state, mut bindings, ty } = phase else { unreachable!() };
        let ghost init = state;
        let (result, returned) = state.step_saving_frame();
        match result? {
            ScalarExecutionSlice::Suspended(state) => {
                assert(init.step_matches(Ok(ScalarExecutionSlice::Suspended(state))));
                let next = Self { plan, rank, header, phase: LetPhase::Initializer { state, bindings, ty } };
                assert(previous.step_matches(Ok(ScalarLetSlice::Suspended(next))));
                Ok(ScalarLetSlice::Suspended(next))
            },
            ScalarExecutionSlice::Complete(value) => {
                let Some(frame) = returned else { unreachable!() };
                let body = frame.body();
                let binding = header.bindings[bindings.len()];
                let name = source_word(body.source.text(), body.forms, binding.name);
                let local = ScalarLocal { name, value };
                let ghost prior = bindings@;
                proof { append_initialized_value(plan, rank, *body, &header, prior, local, ty@); }
                bindings.push(local);
                assert(bindings@.drop_last() =~= prior && bindings@.last() == local);
                let next = Self { plan, rank, header, phase: LetPhase::Select { frame, bindings } };
                assert(previous.step_matches(Ok(ScalarLetSlice::Suspended(next))));
                Ok(ScalarLetSlice::Suspended(next))
            },
        }
    }

    fn step_body(self) -> (result: LetResult<'plan, 'p, 'a>)
        requires self.phase is Body,
        ensures self.result_allowed(result),
    {
        proof { use_type_invariant(&self); reveal(ScalarLetExecution::step_matches); }
        let Self { plan, rank, header, phase } = self;
        let LetPhase::Body(state) = phase else { unreachable!() };
        let (result, _) = state.step_saving_frame();
        match result? {
            ScalarExecutionSlice::Suspended(state) => Ok(ScalarLetSlice::Suspended(Self {
                plan, rank, header, phase: LetPhase::Body(state),
            })),
            ScalarExecutionSlice::Complete(value) => Ok(ScalarLetSlice::Complete(value)),
        }
    }

    /// 正の実行枠で評価を進め、失敗や完了を含めた遷移数を返す。
    ///
    /// # Errors
    ///
    /// 評価中に整数の値域を外れた場合や未対応の式に達した場合は、元の式の位置を返す。
    pub fn run_slice_with_steps(self, fuel: core::num::NonZeroUsize)
        -> (outcome: (LetResult<'plan, 'p, 'a>, usize))
        ensures scalar_let_slice_matches(self, fuel@ as nat, outcome.0, outcome.1 as nat),
            0 < outcome.1 <= fuel@,
            outcome.0 matches Ok(ScalarLetSlice::Suspended(_)) ==> outcome.1 == fuel@,
            outcome.0 matches Ok(ScalarLetSlice::Complete(value)) ==> scalar_fits(value, self.result_type()),
    {
        let budget = fuel.get();
        let mut used = 0;
        let mut state = self;
        let ghost mut trail = seq![self];
        while used < budget
            invariant
                used <= budget == fuel@, trail.len() == used + 1,
                trail.last() == state && state.result_type() == self.result_type(),
                let_path(self, trail),
            decreases budget - used,
        {
            used += 1;
            match state.step() {
                Ok(ScalarLetSlice::Suspended(next)) => {
                    proof { append_let_path(self, trail, next); }
                    proof { trail = trail.push(next); }
                    state = next;
                },
                result => {
                    assert(let_path_end(self, trail, result, used as nat));
                    assert(scalar_let_slice_matches(self, fuel@ as nat, result, used as nat));
                    return (result, used);
                },
            }
        }
        let result = Ok(ScalarLetSlice::Suspended(state));
        assert(let_path_end(self, trail, result, used as nat));
        (result, used)
    }
}

spec fn let_path<'plan, 'p, 'a>(start: ScalarLetExecution<'plan, 'p, 'a>, trail: Seq<ScalarLetExecution<'plan, 'p, 'a>>) -> bool {
    &&& trail.len() > 0 && trail[0] == start
    &&& forall|i: int| 0 <= i < trail.len() - 1 ==>
        (#[trigger] trail[i]).step_matches(Ok(ScalarLetSlice::Suspended(trail[i + 1])))
}

spec fn let_path_end<'plan, 'p, 'a>(
    start: ScalarLetExecution<'plan, 'p, 'a>, trail: Seq<ScalarLetExecution<'plan, 'p, 'a>>, result: LetResult<'plan, 'p, 'a>, used: nat,
) -> bool {
    &&& let_path(start, trail)
    &&& match result {
        Ok(ScalarLetSlice::Suspended(next)) => trail.last() == next && trail.len() == used + 1,
        _ => trail.last().step_matches(result) && trail.len() == used,
    }
}

proof fn append_let_path<'plan, 'p, 'a>(
    start: ScalarLetExecution<'plan, 'p, 'a>, trail: Seq<ScalarLetExecution<'plan, 'p, 'a>>, next: ScalarLetExecution<'plan, 'p, 'a>,
)
    requires let_path(start, trail), trail.last().step_matches(Ok(ScalarLetSlice::Suspended(next))),
    ensures let_path(start, trail.push(next)),
{
    let extended = trail.push(next);
    assert forall|i: int| 0 <= i < extended.len() - 1 implies
        (#[trigger] extended[i]).step_matches(Ok(ScalarLetSlice::Suspended(extended[i + 1]))) by {
        if i + 1 < trail.len() {
            assert(extended[i] == trail[i] && extended[i + 1] == trail[i + 1]);
        } else {
            assert(extended[i] == trail.last() && extended[i + 1] == next);
        }
    };
}

/// 実行枠で消費した数が元の状態からたどった遷移数と一致することを表す。
pub closed spec fn scalar_let_slice_matches<'plan, 'p, 'a>(
    start: ScalarLetExecution<'plan, 'p, 'a>, budget: nat, result: LetResult<'plan, 'p, 'a>, used: nat,
) -> bool {
    &&& 0 < used <= budget
    &&& (result matches Ok(ScalarLetSlice::Suspended(_)) ==> used == budget)
    &&& exists|trail: Seq<ScalarLetExecution<'plan, 'p, 'a>>| #[trigger] let_path_end(start, trail, result, used)
}

/// 途中まで評価して得た状態を続けると、二つの実行枠を合わせた遷移列に対応する。
pub proof fn resumed_scalar_let_matches<'plan, 'p, 'a>(
    start: ScalarLetExecution<'plan, 'p, 'a>, used_first: nat, suspended: ScalarLetExecution<'plan, 'p, 'a>,
    budget_next: nat, result: LetResult<'plan, 'p, 'a>, used_next: nat,
)
    requires scalar_let_slice_matches(start, used_first, Ok(ScalarLetSlice::Suspended(suspended)), used_first),
        scalar_let_slice_matches(suspended, budget_next, result, used_next),
    ensures scalar_let_slice_matches(start, used_first + budget_next, result, used_first + used_next),
{
    let first = choose|trail: Seq<ScalarLetExecution<'plan, 'p, 'a>>|
        #[trigger] let_path_end(start, trail, Ok(ScalarLetSlice::Suspended(suspended)), used_first);
    let second = choose|trail: Seq<ScalarLetExecution<'plan, 'p, 'a>>|
        #[trigger] let_path_end(suspended, trail, result, used_next);
    let joined = first + second.skip(1);
    assert forall|i: int| 0 <= i < joined.len() - 1 implies
        (#[trigger] joined[i]).step_matches(Ok(ScalarLetSlice::Suspended(joined[i + 1]))) by {
        if i + 1 < first.len() {
            assert(joined[i] == first[i] && joined[i + 1] == first[i + 1]);
        } else {
            let j = i - first.len() + 1;
            assert(joined[i] == second[j]) by {
                if j == 0 { assert(i == first.len() - 1); }
            }
            assert(joined[i + 1] == second[j + 1]);
        }
    };
    assert(joined.last() == second.last()) by {
        if second.len() == 1 { assert(second.last() == suspended); }
    }
    assert(let_path_end(start, joined, result, used_first + used_next));
}

}
