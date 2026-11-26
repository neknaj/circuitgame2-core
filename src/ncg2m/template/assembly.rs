//! 展開結果を実行枠ごとに組み立て、診断を伴わずに完了した構文だけを返す。

use alloc::vec::Vec;
use core::num::NonZeroUsize;

use crate::syntax::Form;
use super::{TemplateEmission, TemplateEmissionError, TemplateEmitter, TemplateSubstitution, emit_template};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, form_spans_valid, nested_list_indices};
#[cfg(verus_only)]
use super::{template_emission_step, template_emission_steps_agree, template_emitters_agree};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 末尾まで検査したテンプレートの展開結果。
pub struct ExpandedTemplate<'s, 'v, T> {
    source: &'s str,
    forms: &'s [Form],
    parts: Vec<TemplateEmission<'v, T>>,
}

impl<'s, 'v, T> ExpandedTemplate<'s, 'v, T> {
    /// リテラル部分が由来する元テキストを表す。
    pub closed spec fn source_model(&self) -> &str { self.source }

    /// リテラル部分が参照する元の構文木を表す。
    pub closed spec fn forms_model(&self) -> Seq<Form> { self.forms@ }

    /// 確定した構文項目を表す。
    pub closed spec fn parts_model(&self) -> Seq<TemplateEmission<'v, T>> { self.parts@ }

    /// リテラル部分の元ソースを借りる。
    pub fn source(&self) -> (source: &'s str)
        ensures source == self.source_model(),
    { self.source }

    /// リテラル部分の添字が参照する元の構文木を借りる。
    pub fn forms(&self) -> (forms: &'s [Form])
        ensures forms@ == self.forms_model(),
    { self.forms }

    /// リテラルと挿入値を展開順に並べた結果を借りる。
    pub fn parts(&self) -> (parts: &[TemplateEmission<'v, T>])
        ensures parts@ == self.parts_model(),
    { self.parts.as_slice() }
}

/// 実行枠が終わった時点の展開結果。
pub enum TemplateAssemblySlice<'s, 'v, T> {
    /// 末尾を確認した展開済みの構文。
    Complete(ExpandedTemplate<'s, 'v, T>),
    /// 続きから展開を再開できる状態。
    Suspended(TemplateAssembly<'s, 'v, T>),
}

/// 展開途中の状態。確定していない構文はこの状態に保持する。
pub struct TemplateAssembly<'s, 'v, T> {
    emitter: TemplateEmitter<'s, 'v, T>,
    parts: Vec<TemplateEmission<'v, T>>,
}

impl<'s, 'v, T> TemplateAssembly<'s, 'v, T> {
    /// 次の構文項目を作る状態を表す。
    pub closed spec fn emitter_model(&self) -> TemplateEmitter<'s, 'v, T> { self.emitter }

    /// 現時点までに作った未確定の項目を表す。
    pub closed spec fn parts_model(&self) -> Seq<TemplateEmission<'v, T>> { self.parts@ }

    /// 組み立てを続けられる途中状態であることを表す。
    pub open spec fn ready(&self) -> bool {
        self.emitter_model().valid() && !self.emitter_model().finished_model()
    }

    /// 指定した枠を上限として展開を進める。
    ///
    /// 一つの構文項目の生成、末尾の確認、診断のいずれも1遷移とする。
    /// 最後の項目を生成した後、完了には末尾を確認するもう1遷移が要る。
    /// 完了または診断に達する前に枠を使い切った場合は、一時停止状態を返す。
    /// `splice` の項目は挿入値の列を借りる。列の各要素をコピーしない。
    ///
    /// # Errors
    ///
    /// 展開で最初に見つかった診断を返す。診断に達した途中結果は公開しない。
    pub fn run_slice(self, fuel: NonZeroUsize)
        -> (result: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>)
        requires self.ready(),
        ensures template_assembly_matches(self, fuel@ as nat, result),
            result matches Ok(TemplateAssemblySlice::Suspended(next)) ==>
                next.ready() && next.emitter_model().remaining_bound() < self.emitter_model().remaining_bound(),
    {
        let mut state = self;
        let mut remaining = fuel.get();
        let ghost mut states = seq![state.emitter];
        let ghost mut appended = Seq::<TemplateEmission<'v, T>>::empty();
        while remaining > 0
            invariant
                state.ready(),
                template_emission_prefix(states, appended),
                states[0] == self.emitter_model(),
                states.last() == state.emitter_model(),
                state.parts@ =~= self.parts_model() + appended,
                remaining + appended.len() == fuel@,
                state.emitter_model().remaining_bound() + appended.len() <= self.emitter_model().remaining_bound(),
            decreases remaining,
        {
            let observed = state.emitter.next_emission();
            match observed {
                Some(Ok(part)) => {
                    let ghost after = state.emitter;
                    let ghost emitted = part;
                    state.parts.push(part);
                    proof {
                        extend_emission_prefix(states, appended, after, emitted);
                        states = states.push(after);
                        appended = appended.push(emitted);
                    }
                    remaining -= 1;
                },
                Some(Err(error)) => {
                    proof {
                        assert(template_assembly_trace_result(self, fuel@ as nat, states, appended, Err(error)));
                        assembly_result_witness(self, fuel@ as nat, states, appended, Err(error));
                    }
                    return Err(error);
                },
                None => {
                    let source = state.emitter.source();
                    let forms = state.emitter.forms();
                    let expansion = ExpandedTemplate { source, forms, parts: state.parts };
                    let done = Ok(TemplateAssemblySlice::Complete(expansion));
                    proof {
                        emission_prefix_origin(states, appended);
                        assert(template_assembly_trace_result(self, fuel@ as nat, states, appended, done));
                        assembly_result_witness(self, fuel@ as nat, states, appended, done);
                    }
                    return done;
                }
            }
        }
        let suspended = Ok(TemplateAssemblySlice::Suspended(state));
        proof { assembly_result_witness(self, fuel@ as nat, states, appended, suspended); }
        suspended
    }
}

/// 各項目が、連続する二状態間で生成された順に並ぶことを表す。
pub open spec fn template_emission_prefix<'s, 'v, T>(
    states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>,
) -> bool {
    &&& states.len() == parts.len() + 1
    &&& forall|i: int| 0 <= i < parts.len() ==>
        #[trigger] template_emission_step(&states[i], &states[i + 1], Some(Ok(parts[i])))
}

proof fn extend_emission_prefix<'s, 'v, T>(
    states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>,
    next: TemplateEmitter<'s, 'v, T>, part: TemplateEmission<'v, T>,
)
    requires template_emission_prefix(states, parts),
        template_emission_step(&states.last(), &next, Some(Ok(part))),
    ensures template_emission_prefix(states.push(next), parts.push(part)),
{
    let more_states = states.push(next);
    let more_parts = parts.push(part);
    assert forall|i: int| 0 <= i < more_parts.len() implies
        #[trigger] template_emission_step(&more_states[i], &more_states[i + 1], Some(Ok(more_parts[i]))) by {
        if i < parts.len() {
            assert(template_emission_step(&states[i], &states[i + 1], Some(Ok(parts[i]))));
        }
    };
}

proof fn emission_prefix_origin<'s, 'v, T>(
    states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>,
)
    requires template_emission_prefix(states, parts),
    ensures
        states.first().walk_model().source_model() == states.last().walk_model().source_model(),
        states.first().walk_model().forms_model() == states.last().walk_model().forms_model(),
    decreases parts.len(),
{
    if parts.len() > 0 {
        let prefix = states.drop_last();
        let prior = parts.drop_last();
        assert forall|i: int| 0 <= i < prior.len() implies
            #[trigger] template_emission_step(&prefix[i], &prefix[i + 1], Some(Ok(prior[i]))) by {
            assert(template_emission_step(&states[i], &states[i + 1], Some(Ok(parts[i]))));
        };
        emission_prefix_origin(prefix, prior);
        let i = parts.len() - 1;
        assert(template_emission_step(&states[i], &states[i + 1], Some(Ok(parts[i]))));
    }
}

/// 遷移列と項目列が、この実行枠の停止理由と結果に対応する。
pub open spec fn template_assembly_trace_result<'s, 'v, T>(
    start: TemplateAssembly<'s, 'v, T>, fuel: nat,
    states: Seq<TemplateEmitter<'s, 'v, T>>, appended: Seq<TemplateEmission<'v, T>>,
    result: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
) -> bool {
    &&& template_emission_prefix(states, appended)
    &&& states[0] == start.emitter_model()
    &&& match result {
        Ok(TemplateAssemblySlice::Suspended(next)) =>
            appended.len() == fuel && next.ready()
                && next.emitter_model() == states.last() && next.parts_model() =~= start.parts_model() + appended,
        Ok(TemplateAssemblySlice::Complete(output)) =>
            appended.len() < fuel
                && output.parts_model() =~= start.parts_model() + appended
                && output.source_model() == start.emitter_model().walk_model().source_model()
                && output.forms_model() == start.emitter_model().walk_model().forms_model()
                && (exists|last: TemplateEmitter<'s, 'v, T>|
                    #[trigger] template_emission_step(&states.last(), &last, None)),
        Err(error) => appended.len() < fuel
            && (exists|last: TemplateEmitter<'s, 'v, T>|
                #[trigger] template_emission_step(&states.last(), &last, Some(Err(error)))),
    }
}

/// 実行枠の結果が、同じ途中状態から出力遷移を適用した結果であることを表す。
pub open spec fn template_assembly_matches<'s, 'v, T>(
    start: TemplateAssembly<'s, 'v, T>, fuel: nat,
    result: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
) -> bool {
    exists|states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>|
        #[trigger] template_assembly_trace_result(start, fuel, states, parts, result)
}

proof fn assembly_result_witness<'s, 'v, T>(
    start: TemplateAssembly<'s, 'v, T>, fuel: nat,
    states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>,
    result: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
)
    requires template_assembly_trace_result(start, fuel, states, parts, result),
    ensures template_assembly_matches(start, fuel, result),
{}

/// 二つの実行枠を続けて実行した結果が、一つにまとめた枠にも対応することを示す。
pub proof fn resumed_template_assembly_matches<'s, 'v, T>(
    start: TemplateAssembly<'s, 'v, T>, first: nat, suspended: TemplateAssembly<'s, 'v, T>, next: nat,
    result: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
)
    requires
        template_assembly_matches(start, first, Ok(TemplateAssemblySlice::Suspended(suspended))),
        template_assembly_matches(suspended, next, result),
    ensures template_assembly_matches(start, first + next, result),
{
    let (earlier, left) = choose|states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>|
        #[trigger] template_assembly_trace_result(start, first, states, parts,
            Ok(TemplateAssemblySlice::Suspended(suspended)));
    let (later, right) = choose|states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>|
        #[trigger] template_assembly_trace_result(suspended, next, states, parts, result);
    let states = earlier + later.subrange(1, later.len() as int);
    let parts = left + right;
    assert(states.last() == later.last());
    assert forall|i: int| 0 <= i < parts.len() implies
        #[trigger] template_emission_step(&states[i], &states[i + 1], Some(Ok(parts[i]))) by {
        if i < left.len() {
            assert(template_emission_step(&earlier[i], &earlier[i + 1], Some(Ok(left[i]))));
        } else {
            let index = i - left.len();
            assert(template_emission_step(&later[index], &later[index + 1], Some(Ok(right[index]))));
        }
    };
    emission_prefix_origin(earlier, left);
    assert(template_assembly_trace_result(start, first + next, states, parts, result));
}

proof fn common_emission_prefix_agrees<'s, 'v, T>(
    a: Seq<TemplateEmitter<'s, 'v, T>>, left: Seq<TemplateEmission<'v, T>>,
    b: Seq<TemplateEmitter<'s, 'v, T>>, right: Seq<TemplateEmission<'v, T>>, n: int,
)
    requires template_emission_prefix(a, left), template_emission_prefix(b, right),
        template_emitters_agree(&a[0], &b[0]), 0 <= n <= left.len(), n <= right.len(),
    ensures template_emitters_agree(&a[n], &b[n]), n > 0 ==> left[n - 1] == right[n - 1],
    decreases n,
{
    if n > 0 {
        let i = n - 1;
        common_emission_prefix_agrees(a, left, b, right, i);
        assert(0 <= i < left.len() && i < right.len());
        assert(template_emission_step(&a[i], &a[i + 1], Some(Ok(left[i]))));
        assert(template_emission_step(&b[i], &b[i + 1], Some(Ok(right[i]))));
        assert(i + 1 == n);
        template_emission_steps_agree(&a[i], &b[i], &a[n], &b[n],
            Some(Ok(left[i])), Some(Ok(right[i])));
    }
}

spec fn terminal_emission<'s, 'v, T>(
    result: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
) -> Option<Result<TemplateEmission<'v, T>, TemplateEmissionError>> {
    match result { Err(error) => Some(Err(error)), _ => None }
}

proof fn terminal_emission_witness<'s, 'v, T>(
    start: TemplateAssembly<'s, 'v, T>, fuel: nat,
    states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>,
    result: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
) -> (next: TemplateEmitter<'s, 'v, T>)
    requires template_assembly_trace_result(start, fuel, states, parts, result), parts.len() < fuel,
    ensures template_emission_step(&states.last(), &next, terminal_emission(result)),
{
    choose|last: TemplateEmitter<'s, 'v, T>|
        #[trigger] template_emission_step(&states.last(), &last, terminal_emission(result))
}

proof fn emission_trace_has_no_early_end<'s, 'v, T>(
    start: TemplateAssembly<'s, 'v, T>, fuel: nat,
    a: Seq<TemplateEmitter<'s, 'v, T>>, left: Seq<TemplateEmission<'v, T>>,
    b: Seq<TemplateEmitter<'s, 'v, T>>, right: Seq<TemplateEmission<'v, T>>,
    r_a: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
    r_b: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
)
    requires template_assembly_trace_result(start, fuel, a, left, r_a),
        template_assembly_trace_result(start, fuel, b, right, r_b),
    ensures left.len() >= right.len(),
{
    if left.len() < right.len() {
        let i = left.len() as int;
        common_emission_prefix_agrees(a, left, b, right, i);
        let end_a = terminal_emission_witness(start, fuel, a, left, r_a);
        assert(a[i] == a.last());
        assert(template_emission_step(&b[i], &b[i + 1], Some(Ok(right[i]))));
        template_emission_steps_agree(&a[i], &b[i], &end_a, &b[i + 1],
            terminal_emission(r_a), Some(Ok(right[i])));
    }
}

/// 確定した構文、診断、または次の枠に渡す状態が等しいことを表す。
pub open spec fn template_assembly_outputs_agree<'s, 'v, T>(
    a: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
    b: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
) -> bool {
    match (a, b) {
        (Ok(TemplateAssemblySlice::Complete(a)), Ok(TemplateAssemblySlice::Complete(b))) =>
            a.source_model() == b.source_model() && a.forms_model() == b.forms_model()
                && a.parts_model() == b.parts_model(),
        (Ok(TemplateAssemblySlice::Suspended(a)), Ok(TemplateAssemblySlice::Suspended(b))) =>
            a.parts_model() == b.parts_model() && template_emitters_agree(&a.emitter_model(), &b.emitter_model()),
        (Err(a), Err(b)) => a == b,
        _ => false,
    }
}

/// 同じ開始状態と枠が仕様を満たすとき、観測できる結果は一意であることを示す。
pub proof fn template_assembly_results_agree<'s, 'v, T>(
    start: TemplateAssembly<'s, 'v, T>, fuel: nat,
    r_a: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
    r_b: Result<TemplateAssemblySlice<'s, 'v, T>, TemplateEmissionError>,
)
    requires template_assembly_matches(start, fuel, r_a), template_assembly_matches(start, fuel, r_b),
    ensures template_assembly_outputs_agree(r_a, r_b),
{
    let (a, left) = choose|states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>|
        #[trigger] template_assembly_trace_result(start, fuel, states, parts, r_a);
    let (b, right) = choose|states: Seq<TemplateEmitter<'s, 'v, T>>, parts: Seq<TemplateEmission<'v, T>>|
        #[trigger] template_assembly_trace_result(start, fuel, states, parts, r_b);
    emission_trace_has_no_early_end(start, fuel, a, left, b, right, r_a, r_b);
    emission_trace_has_no_early_end(start, fuel, b, right, a, left, r_b, r_a);
    let end = left.len() as int;
    common_emission_prefix_agrees(a, left, b, right, end);
    assert(left =~= right) by {
        assert forall|i: int| 0 <= i < left.len() implies left[i] == right[i] by {
            common_emission_prefix_agrees(a, left, b, right, i + 1);
        };
    };
    assert(a[end] == a.last() && b[end] == b.last());
    if left.len() < fuel {
        let end_a = terminal_emission_witness(start, fuel, a, left, r_a);
        let end_b = terminal_emission_witness(start, fuel, b, right, r_b);
        template_emission_steps_agree(&a.last(), &b.last(), &end_a, &end_b,
            terminal_emission(r_a), terminal_emission(r_b));
    }
}

/// 挿入値を借りて、まだ構文項目を生成していない途中状態を作る。
///
/// 元ソースから得た厳格構文木を渡す。根の添字が範囲外なら `None` を返す。
///
/// # Panics
///
/// 渡した本文と構文木が対応しない場合や、手動で作った構文木の添字に矛盾がある場合は、
/// 後続の実行でパニックすることがある。
///
/// # Examples
///
/// ```
/// use core::num::NonZeroUsize;
/// use circuitgame2_core::ncg2m::template::{TemplateAssemblySlice, TemplateEmission, TemplateSubstitution, assemble_template};
/// use circuitgame2_core::syntax::parse;
///
/// let text = "(nor (unsyntax input) (unsyntax input))";
/// let forms = parse(text)?;
/// let input = "caller-input";
/// let bindings = [TemplateSubstitution::One(&input), TemplateSubstitution::One(&input)];
/// let mut state = assemble_template(text, &forms, 0, &bindings).unwrap();
/// let output = loop {
///     match state.run_slice(NonZeroUsize::MIN).unwrap() {
///         TemplateAssemblySlice::Suspended(next) => state = next,
///         TemplateAssemblySlice::Complete(output) => break output,
///     }
/// };
/// assert_eq!(output.source(), text);
/// assert!(matches!(output.parts(), [TemplateEmission::Open(0), TemplateEmission::Atom(1),
///     TemplateEmission::Insert(a), TemplateEmission::Insert(b), TemplateEmission::Close(0)]
///     if *a == &input && *b == &input));
/// # Ok::<(), circuitgame2_core::syntax::Error>(())
/// ```
pub fn assemble_template<'s, 'v, T>(
    source: &'s str, forms: &'s [Form], root: usize, values: &'v [TemplateSubstitution<'v, T>],
) -> (result: Option<TemplateAssembly<'s, 'v, T>>)
    requires complete_list_indices(forms@), nested_list_indices(forms@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures result.is_some() <==> root < forms@.len(),
        result matches Some(result) ==> result.ready()
            && result.emitter_model().walk_model().source_model() == source
            && result.emitter_model().walk_model().forms_model() == forms@
            && result.emitter_model().walk_model().range_model().start == root
            && result.emitter_model().walk_model().range_model().end == match forms@[root as int] {
                Form::Atom { .. } => root + 1,
                Form::List { end, .. } => end as int,
            }
            && result.emitter_model().walk_model().position_model() == root
            && result.emitter_model().lists_model().len() == 0
            && result.emitter_model().used_model() == 0 && result.parts_model().len() == 0
            && result.emitter_model().values_model() == values@,
{
    let emitter = emit_template(source, forms, root, values)?;
    Some(TemplateAssembly { emitter, parts: Vec::new() })
}

} // verus!
