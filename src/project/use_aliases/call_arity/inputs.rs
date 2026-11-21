//! 呼び出しの直接の引数に、宣言順で対応する入力型を照合する。

use super::{CallPortType, FuncCallArity, FuncCallSignatureError, TypedFuncCall, UseAliases};
use super::{FuncCallSignature, FuncCallTarget};
use super::typed::{cached_signature, signature_port};
#[cfg(verus_only)]
use super::typed::cached_call_model;
use super::super::signature_cache::SignatureCache;
use super::super::OutputDriver;
use super::super::function_atoms::{copy_location, inherit_type};
#[cfg(verus_only)]
use super::super::function_atoms::signal_type_at;
#[cfg(verus_only)]
use super::super::function_drivers::expected_output_context;
use crate::project::{
    CircuitLiteralWidthError, FuncAtomTypeError, FuncAtomTypes, FuncWiring, FuncWiringResult,
    LocatedName, ProjectSource, PortDirection, ResolvedPortType, SignalType, check_circuit_literal_width,
};
use crate::project::circuits::{form_location, read_indexed_atom};
#[cfg(verus_only)]
use crate::project::{
    circuit_literal_width_matches, port_types_equal,
    circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence},
};
use crate::syntax::{
    AtomKind, Form, circuit::{call_argument_range, indexed_call_signal, next_call_argument},
};
#[cfg(verus_only)]
use crate::syntax::{
    form_span, form_spans_valid,
    circuit::{NamedBuildCircuit, build_definition_scope_evidence, build_entry_ranges_evidence, call_argument_sequence,
        direct_call_argument, exhausted_call_arguments, expression_region,
        first_call_argument_evidence, following_call_argument},
};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

mod batch;
#[cfg(verus_only)]
mod source_order;
pub use batch::FuncCallInputsError;
pub(in crate::project::use_aliases) use batch::CallArgumentProjections;

verus! {

/// 型検査で解決した呼び出し先。展開はこの位置からテンプレートを選ぶ。
#[derive(Clone, Copy, Debug)]
pub(in crate::project::use_aliases) enum RetainedCallTarget {
    /// 言語組み込みの一ビット NOR。
    Nor,
    /// プロジェクト内の関数宣言を指すファイル添字と索引項目。
    Function(usize, usize),
}

impl RetainedCallTarget {
    pub(in crate::project::use_aliases) open spec fn from_arity(arity: FuncCallArity) -> Self {
        match arity.target {
            FuncCallTarget::Nor => Self::Nor,
            FuncCallTarget::Function { file, entry, .. } => Self::Function(file, entry),
        }
    }
}

/// 展開に使う引数の元フォームと配線の取得方法。
#[derive(Debug)]
pub(in crate::project::use_aliases) struct ProjectedCallArgument {
    pub(in crate::project::use_aliases) form: usize,
    pub(in crate::project::use_aliases) source: CallArgumentSource,
}

/// 型検査後の実引数を、配線生成での扱いに応じて表す。
///
/// 専用フォームや信号のうち、型が確定しなかった実引数は保留する。
#[derive(Debug)]
pub(in crate::project::use_aliases) enum CallArgumentSource {
    Driver(OutputDriver),
    Literal(u64),
    /// 型が確定した単一出力の呼び出し。添字は同じ定義の参照区間を起点とする。
    NestedCall(usize),
    /// 型を保留した実引数。
    Deferred,
}

impl CallArgumentSource {
    /// 追加の式展開をせず、局所信号かリテラルから配線を取得できることを表す。
    pub(in crate::project::use_aliases) open spec fn has_direct_wires(self) -> bool {
        self is Driver || self is Literal
    }
}

/// 一つの呼び出しと、宣言順に対応する引数の確定型。
#[derive(Debug)]
pub struct CheckedCallInputs<'p, 'a> {
    /// 呼び出しの位置と、名前解決で選ばれた署名。
    pub call: TypedFuncCall<'p, 'a>,
    /// 直接の引数ごとの型。型を保留した引数は `None`。
    pub inputs: Vec<Option<SignalType<'p, 'a>>>,
}

/// 呼び出しの引数が入力ポートの型に合わなかった理由。
#[derive(Debug)]
pub enum CallInputReason<'p, 'a> {
    /// 二進・十六進または固定の 1 ビット定数に割り当てる幅の違反。
    LiteralWidth(CircuitLiteralWidthError),
    /// 構造体型の入力に裸の定数を渡した。
    StructRequired,
    /// 信号または子呼び出しの型が入力型と異なる。実際の型とその根拠を持つ。
    SignalType(SignalType<'p, 'a>),
}

/// 配線、呼び出し先の署名、または直接の引数に関する違反。
#[derive(Debug)]
pub enum CallInputError<'p, 'a> {
    /// 呼び出し元の配線・個数・定数・裸の信号参照の検査に違反がある。
    Caller(FuncAtomTypeError<'p, 'a>),
    /// 参照先の名前解決または署名に違反がある。
    Signature(FuncCallSignatureError<'p, 'a>),
    /// 取得した型付き署名の入力数を引数数と再照合した際に、個数が一致しなかった。
    Count(FuncCallArity<'p, 'a>),
    /// 呼び出しの直接の引数に違反がある。
    Argument {
        /// 対象の引数の位置。先頭を 0 と数える。
        index: usize,
        /// 違反のある引数全体の元ソース範囲。
        argument: LocatedName<'p, 'a>,
        /// 呼び出し先の入力が要求する型。
        expected: ResolvedPortType<'p, 'a>,
        /// 要求型の注釈。基底 NOR では `None`。
        required_at: Option<LocatedName<'p, 'a>>,
        /// 幅や型の不一致の根拠。
        reason: CallInputReason<'p, 'a>,
    },
}

spec fn leaf_result(
    source: &ProjectSource, form: Form, port: &CallPortType, known: Option<SignalType>, limit: u64,
    result: Result<Option<SignalType>, CallInputReason>,
) -> bool {
    if form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal || form->Atom_kind is Natural) {
        let span = form_span(form);
        let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
        match port.ty {
            ResolvedPortType::Struct { .. } => result is Err && result->Err_0 is StructRequired,
            ResolvedPortType::Bits(bits) => match result {
                Ok(Some(typed)) => typed.ty is Bits && is_form_location(source, form, typed.origin)
                    && circuit_literal_width_matches(bytes, Some(bits), limit, Ok(typed.ty->Bits_0)),
                Err(CallInputReason::LiteralWidth(error)) => circuit_literal_width_matches(bytes, Some(bits), limit, Err(error)),
                _ => false,
            },
        }
    } else if form is List || (form is Atom && form->Atom_kind is Name) {
        if let Some(ty) = known {
            if port_types_equal(ty.ty, port.ty) { result == Ok(Some(ty)) }
            else { result == Err(CallInputReason::SignalType(ty)) }
        } else { result == Ok(None) }
    } else {
        result == Ok(None)
    }
}

fn check_leaf<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], at: usize,
    port: &CallPortType<'_, 'p, 'a>, known: Option<SignalType<'p, 'a>>, limit: u64,
) -> (result: Result<Option<SignalType<'p, 'a>>, CallInputReason<'p, 'a>>)
    requires
        at < forms@.len(),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures leaf_result(source, forms@[at as int], port, known, limit, result),
{
    match forms[at] {
        Form::Atom { kind: AtomKind::Binary | AtomKind::Hexadecimal | AtomKind::Natural, .. } => {
            let ResolvedPortType::Bits(width) = port.ty else { return Err(CallInputReason::StructRequired); };
            let (word, _) = read_indexed_atom(source.text, forms, at);
            match check_circuit_literal_width(word, Some(width), limit) {
                Ok(bits) => Ok(Some(SignalType { ty: ResolvedPortType::Bits(bits), origin: form_location(source, forms, at) })),
                Err(error) => Err(CallInputReason::LiteralWidth(error)),
            }
        },
        Form::List { .. } | Form::Atom { kind: AtomKind::Name, .. } => {
            if let Some(ty) = known {
                if ty.ty.is_same_type(&port.ty) { Ok(Some(ty)) } else { Err(CallInputReason::SignalType(ty)) }
            } else { Ok(None) }
        },
        _ => Ok(None),
    }
}

spec fn input_port_matches(call: &TypedFuncCall, i: int, port: CallPortType) -> bool {
    match &call.signature {
        FuncCallSignature::Nor => 0 <= i < 2 && port.ty == ResolvedPortType::Bits(1) && port.annotation is None,
        FuncCallSignature::Function(signature) => 0 <= i < signature.inputs@.len()
            && port.ty == signature.inputs@[i].ty
            && (port.annotation matches Some(annotation) && *annotation == signature.inputs@[i].annotation),
    }
}

#[verifier::opaque]
spec fn nested_output_type(
    context: (&UseAliases, usize, usize, usize), form: usize, limit: u64, value: Option<SignalType>,
) -> bool {
    let (aliases, file, entry, definition) = context;
    exists|result: Result<Option<TypedFuncCall>, FuncCallSignatureError>|
        #[trigger] aliases.func_call_signature_at_form_evidence(file, entry, definition, form, limit, result)
        && value == nested_output_from_signature(result)
}

spec fn nested_output_from_signature<'p, 'a>(
    result: Result<Option<TypedFuncCall<'p, 'a>>, FuncCallSignatureError<'p, 'a>>,
) -> Option<SignalType<'p, 'a>> {
    match result {
        Ok(Some(call)) if call.call.target.port_counts().outputs == 1 => match call.signature {
            FuncCallSignature::Nor => Some(SignalType {
                ty: ResolvedPortType::Bits(1),
                origin: LocatedName { source: call.call.source, span: call.call.call.span },
            }),
            FuncCallSignature::Function(signature) => Some(SignalType {
                ty: signature.outputs@[0].ty,
                origin: signature.outputs@[0].annotation,
            }),
        },
        _ => None,
    }
}

proof fn record_nested_output_type(
    context: (&UseAliases, usize, usize, usize), form: usize, limit: u64,
    result: Result<Option<TypedFuncCall>, FuncCallSignatureError>, value: Option<SignalType>,
)
    requires
        context.0.func_call_signature_at_form_evidence(context.1, context.2, context.3, form, limit, result),
        value == nested_output_from_signature(result),
    ensures nested_output_type(context, form, limit, value),
{
    reveal(nested_output_type);
    let (aliases, file, entry, definition) = context;
    assert(exists|signature: Result<Option<TypedFuncCall>, FuncCallSignatureError>|
        #[trigger] aliases.func_call_signature_at_form_evidence(file, entry, definition, form, limit, signature)
        && value == nested_output_from_signature(signature)) by {
        assert(aliases.func_call_signature_at_form_evidence(file, entry, definition, form, limit, result));
    };
}

/// 子呼び出しの単一出力型を元の型注釈とともに取り出し、定義内の参照添字も返す。
fn nested_output_type_at<'p, 'a>(
    aliases: &UseAliases<'_, 'p, 'a>, file: usize, entry: usize, definition: usize, form: usize, limit: u64,
) -> (found: (Option<SignalType<'p, 'a>>, Option<usize>))
    requires aliases.can_resolve(),
    ensures
        nested_output_type((aliases, file, entry, definition), form, limit, found.0),
        found.0.is_some() ==> found.1.is_some(),
        found.1 matches Some(reference) ==> aliases.func_call_form_reference(file, entry, definition, form, reference),
{
    let (reference, result) = aliases.resolve_func_call_signature_with_reference(file, entry, definition, form, limit);
    // 署名を解決できない子は、その参照を検査する順番まで診断を保留する。
    let value = match &result {
        Ok(Some(call)) if call.call.target.ports().outputs == 1 => match &call.signature {
            FuncCallSignature::Nor => Some(SignalType {
                ty: ResolvedPortType::Bits(1),
                origin: LocatedName {
                    source: call.call.source,
                    span: call.call.call.span.start..call.call.call.span.end,
                },
            }),
            FuncCallSignature::Function(_) => {
                let Some(port) = call.signature.port(PortDirection::Output, 0) else {
                    proof { assert(false); }
                    unreachable!()
                };
                let Some(annotation) = port.annotation else {
                    proof { assert(false); }
                    unreachable!()
                };
                Some(SignalType { ty: port.ty, origin: copy_location(annotation) })
            },
        },
        _ => None,
    };
    proof { record_nested_output_type((aliases, file, entry, definition), form, limit, result, value); }
    (value, reference)
}

spec fn known_argument(
    context: (&UseAliases, usize, usize, usize), limit: u64, forms: Seq<Form>, scope: &FuncWiring, types: Seq<Option<SignalType>>, slots: Seq<usize>,
    signal_start: int, at: usize, known: Option<SignalType>,
) -> bool {
    match forms[at as int] {
        Form::List { .. } => nested_output_type(context, at, limit, known),
        Form::Atom { kind: AtomKind::Name, .. } => exists|s: int| 0 <= s < slots.len() && #[trigger] slots[s] == at
            && 0 <= signal_start + s < scope.signals@.len()
            && known == signal_type_at(scope, types, scope.signals@[signal_start + s].driver),
        _ => true,
    }
}

spec fn reported_argument(
    source: &ProjectSource, form: Form, ordinal: usize, port: CallPortType,
    leaf: Result<Option<SignalType>, CallInputReason>, result: Result<Option<SignalType>, CallInputError>,
) -> bool {
    match leaf {
        Ok(ty) => result == Ok(ty),
        Err(reason) => result matches Err(CallInputError::Argument {
            index, argument, expected, required_at, reason: found,
        }) && index == ordinal && is_form_location(source, form, argument)
            && expected == port.ty && found == reason
            && required_at == (if let Some(annotation) = port.annotation { Some(*annotation) } else { None }),
    }
}

#[verifier::opaque]
spec fn argument_result(
    context: (&UseAliases, usize, usize, usize), call: &TypedFuncCall, forms: Seq<Form>, scope: &FuncWiring, types: Seq<Option<SignalType>>,
    slots: Seq<usize>, signal_start: int, at: usize, ordinal: usize, limit: u64,
    result: Result<Option<SignalType>, CallInputError>,
) -> bool {
    &&& at < forms.len() && direct_call_argument(forms, call.call.call, at as int)
    &&& exists|port: CallPortType, known: Option<SignalType>, leaf: Result<Option<SignalType>, CallInputReason>|
        #[trigger] input_port_matches(call, ordinal as int, port)
        && #[trigger] leaf_result(call.call.source, forms[at as int], &port, known, limit, leaf)
        && known_argument(context, limit, forms, scope, types, slots, signal_start, at, known)
        && reported_argument(call.call.source, forms[at as int], ordinal, port, leaf, result)
}

proof fn record_argument(
    context: (&UseAliases, usize, usize, usize), call: &TypedFuncCall, forms: Seq<Form>, scope: &FuncWiring, types: Seq<Option<SignalType>>,
    slots: Seq<usize>, signal_start: int, at: usize, ordinal: usize, limit: u64,
    port: CallPortType, known: Option<SignalType>, leaf: Result<Option<SignalType>, CallInputReason>,
    result: Result<Option<SignalType>, CallInputError>,
)
    requires
        at < forms.len() && direct_call_argument(forms, call.call.call, at as int),
        input_port_matches(call, ordinal as int, port),
        known_argument(context, limit, forms, scope, types, slots, signal_start, at, known),
        leaf_result(call.call.source, forms[at as int], &port, known, limit, leaf),
        reported_argument(call.call.source, forms[at as int], ordinal, port, leaf, result),
    ensures argument_result(context, call, forms, scope, types, slots, signal_start, at, ordinal, limit, result),
{
    reveal(argument_result);
    assert(exists|p: CallPortType, k: Option<SignalType>, l: Result<Option<SignalType>, CallInputReason>|
        #[trigger] input_port_matches(call, ordinal as int, p)
        && #[trigger] leaf_result(call.call.source, forms[at as int], &p, k, limit, l)
        && known_argument(context, limit, forms, scope, types, slots, signal_start, at, k)
        && reported_argument(call.call.source, forms[at as int], ordinal, p, l, result)) by {
        assert(input_port_matches(call, ordinal as int, port));
        assert(leaf_result(call.call.source, forms[at as int], &port, known, limit, leaf));
    };
}

#[verifier::opaque]
spec fn argument_prefix(
    context: (&UseAliases, usize, usize, usize), call: &TypedFuncCall, forms: Seq<Form>, scope: &FuncWiring, types: Seq<Option<SignalType>>,
    slots: Seq<usize>, signal_start: int, limit: u64,
    visited: Seq<usize>, values: Seq<Option<SignalType>>, next: usize,
) -> bool {
    &&& values.len() == visited.len()
    &&& next as int == if visited.len() == 0 { call.call.call.form + 2 }
        else { after_argument(forms, visited.last() as int) }
    &&& forall|i: int| 0 <= i < visited.len() ==> {
        let this = #[trigger] visited[i] as int;
        &&& this == if i == 0 { call.call.call.form + 2 }
            else { after_argument(forms, visited[i - 1] as int) }
        &&& argument_result(context, call, forms, scope, types, slots, signal_start, this as usize, i as usize, limit, Ok(values[i]))
    }
}

spec fn after_argument(forms: Seq<Form>, at: int) -> int {
    if forms[at] is List { forms[at]->List_end as int } else { at + 1 }
}

#[verifier::opaque]
spec fn argument_projection_matches(
    context: (&UseAliases, usize, usize, usize),
    argument: ProjectedCallArgument, at: usize, forms: Seq<Form>, wiring: &FuncWiring,
    types: Seq<Option<SignalType>>, slots: Seq<usize>, start: int, value: Option<SignalType>,
) -> bool {
    &&& argument.form == at && at < forms.len()
    &&& match argument.source {
        CallArgumentSource::Driver(driver) =>
            value.is_some() && forms[at as int] is Atom && forms[at as int]->Atom_kind is Name
                && exists|s: int| 0 <= s < slots.len() && (#[trigger] slots[s]) == at
                    && 0 <= start + s < wiring.signals@.len()
                    && wiring.signals@[start + s].driver == driver
                    && value == signal_type_at(wiring, types, driver),
        CallArgumentSource::Literal(width) =>
            forms[at as int] is Atom && (forms[at as int]->Atom_kind is Natural
                || forms[at as int]->Atom_kind is Binary || forms[at as int]->Atom_kind is Hexadecimal)
                && (value matches Some(ty) && ty.ty == ResolvedPortType::Bits(width)),
        CallArgumentSource::NestedCall(reference) => forms[at as int] is List && value.is_some()
            && context.0.func_call_form_reference(context.1, context.2, context.3, at, reference),
        CallArgumentSource::Deferred => value.is_none(),
    }
}

#[verifier::opaque]
spec fn argument_projections_match(
    context: (&UseAliases, usize, usize, usize),
    forms: Seq<Form>, wiring: &FuncWiring, types: Seq<Option<SignalType>>, slots: Seq<usize>, start: int,
    visited: Seq<usize>, values: Seq<Option<SignalType>>, projected: Seq<ProjectedCallArgument>,
) -> bool {
    &&& projected.len() == visited.len() == values.len()
    &&& forall|i: int| 0 <= i < projected.len() ==>
        argument_projection_matches(context, #[trigger] projected[i], visited[i], forms, wiring, types, slots, start, values[i])
}

proof fn extend_argument_prefix(
    context: (&UseAliases, usize, usize, usize), call: &TypedFuncCall, forms: Seq<Form>, wiring: &FuncWiring, types: Seq<Option<SignalType>>,
    slots: Seq<usize>, start: int, limit: u64, visited: Seq<usize>, values: Seq<Option<SignalType>>,
    root: usize, next: usize, value: Option<SignalType>,
)
    requires
        argument_prefix(context, call, forms, wiring, types, slots, start, limit, visited, values, root),
        argument_result(context, call, forms, wiring, types, slots, start, root, visited.len() as usize, limit, Ok(value)),
        visited.len() <= usize::MAX,
        next == after_argument(forms, root as int),
    ensures argument_prefix(context, call, forms, wiring, types, slots, start, limit, visited.push(root), values.push(value), next),
{
    reveal(argument_prefix);
    let appended = visited.push(root);
    let results = values.push(value);
    assert forall|i: int| 0 <= i < appended.len() implies {
        let form = (#[trigger] appended[i]) as int;
        &&& form == if i == 0 { call.call.call.form + 2 } else { after_argument(forms, appended[i - 1] as int) }
        &&& argument_result(context, call, forms, wiring, types, slots, start, form as usize, i as usize, limit, Ok(results[i]))
    } by {
        if i < visited.len() { assert(appended[i] == visited[i] && results[i] == values[i]); }
    };
}

proof fn extend_argument_projections(
    context: (&UseAliases, usize, usize, usize),
    forms: Seq<Form>, wiring: &FuncWiring, types: Seq<Option<SignalType>>, slots: Seq<usize>, start: int,
    visited: Seq<usize>, values: Seq<Option<SignalType>>, projected: Seq<ProjectedCallArgument>,
    root: usize, value: Option<SignalType>, argument: ProjectedCallArgument,
)
    requires
        argument_projections_match(context, forms, wiring, types, slots, start, visited, values, projected),
        argument_projection_matches(context, argument, root, forms, wiring, types, slots, start, value),
    ensures argument_projections_match(context, forms, wiring, types, slots, start,
        visited.push(root), values.push(value), projected.push(argument)),
{
    reveal(argument_projections_match);
    let collected = projected.push(argument);
    let appended = visited.push(root);
    let results = values.push(value);
    assert forall|i: int| 0 <= i < collected.len() implies
        argument_projection_matches(context, #[trigger] collected[i], appended[i], forms, wiring, types, slots, start, results[i])
        by {
            if i < projected.len() { assert(collected[i] == projected[i] && appended[i] == visited[i] && results[i] == values[i]); }
        };
}

spec fn arguments_match(
    context: (&UseAliases, usize, usize, usize), parsed: &NamedBuildCircuit, scope: &FuncWiring,
    types: Seq<Option<SignalType>>, call: &TypedFuncCall, limit: u64, collect: bool,
    result: Result<Option<CheckedCallInputs>, CallInputError>,
) -> bool {
    let (_, _, entry, definition) = context;
    let forms = parsed.syntax.forms@;
    let frame = parsed.entry_ranges@[entry as int];
    let row = parsed.definitions@[frame.definitions.start + definition];
    let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
    let start = row.signals.start - frame.signals.start;
    let last = forms[call.call.call.form as int]->List_end;
    let count = call.call.call.arguments;
    &&& count == call.call.target.port_counts().inputs
    &&& match result {
        Ok(output) => exists|visited: Seq<usize>, values: Seq<Option<SignalType>>|
                #[trigger] argument_prefix(context, call, forms, scope, types, slots, start, limit, visited, values, last)
                    && values.len() == count && if collect {
                        output matches Some(output) && output.call == *call && output.inputs@ == values
                    } else { output.is_none() },
        Err(error) => exists|visited: Seq<usize>, values: Seq<Option<SignalType>>, at: usize|
            #[trigger] argument_prefix(context, call, forms, scope, types, slots, start, limit, visited, values, at)
                && visited.len() < count
                && argument_result(context, call, forms, scope, types, slots, start, at, visited.len() as usize, limit, Err(error)),
    }
}

proof fn record_failed_argument(
    context: (&UseAliases, usize, usize, usize), parsed: &NamedBuildCircuit, scope: &FuncWiring,
    types: Seq<Option<SignalType>>, call: &TypedFuncCall, limit: u64, collect: bool,
    error: CallInputError, visited: Seq<usize>, values: Seq<Option<SignalType>>, at: usize,
)
    requires
        call.call.call.arguments == call.call.target.port_counts().inputs,
        visited.len() < call.call.call.arguments,
        ({
            let (_, _, entry, definition) = context;
            let frame = parsed.entry_ranges@[entry as int];
            let row = parsed.definitions@[frame.definitions.start + definition];
            let forms = parsed.syntax.forms@;
            let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
            let start = row.signals.start - frame.signals.start;
            &&& argument_prefix(context, call, forms, scope, types, slots, start, limit, visited, values, at)
            &&& argument_result(context, call, forms, scope, types, slots, start, at, visited.len() as usize, limit, Err(error))
        }),
    ensures arguments_match(context, parsed, scope, types, call, limit, collect, Err(error)),
{
    let (_, _, entry, definition) = context;
    let frame = parsed.entry_ranges@[entry as int];
    let row = parsed.definitions@[frame.definitions.start + definition];
    let forms = parsed.syntax.forms@;
    let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
    let start = row.signals.start - frame.signals.start;
    assert(exists|positions: Seq<usize>, inferred: Seq<Option<SignalType>>, root: usize|
        #[trigger] argument_prefix(context, call, forms, scope, types, slots, start, limit, positions, inferred, root)
        && positions.len() < call.call.call.arguments
        && argument_result(context, call, forms, scope, types, slots, start, root, positions.len() as usize, limit, Err(error))) by {
        assert(argument_prefix(context, call, forms, scope, types, slots, start, limit, visited, values, at));
    };
}

proof fn record_completed_arguments(
    context: (&UseAliases, usize, usize, usize), parsed: &NamedBuildCircuit, scope: &FuncWiring,
    types: Seq<Option<SignalType>>, call: &TypedFuncCall, limit: u64, collect: bool,
    result: Option<CheckedCallInputs>, visited: Seq<usize>, values: Seq<Option<SignalType>>,
)
    requires
        ({
            let (_, _, entry, definition) = context;
            let frame = parsed.entry_ranges@[entry as int];
            let row = parsed.definitions@[frame.definitions.start + definition];
            let forms = parsed.syntax.forms@;
            let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
            argument_prefix(context, call, forms, scope, types, slots, row.signals.start - frame.signals.start,
                limit, visited, values, forms[call.call.call.form as int]->List_end)
        }),
        values.len() == call.call.call.arguments == call.call.target.port_counts().inputs,
        if collect {
            result matches Some(output) && output.call == *call && output.inputs@ == values
        } else { result.is_none() },
    ensures arguments_match(context, parsed, scope, types, call, limit, collect, Ok(result)),
{
    let (_, _, entry, definition) = context;
    let frame = parsed.entry_ranges@[entry as int];
    let row = parsed.definitions@[frame.definitions.start + definition];
    let forms = parsed.syntax.forms@;
    let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
    let start = row.signals.start - frame.signals.start;
    let last = forms[call.call.call.form as int]->List_end;
    assert(exists|positions: Seq<usize>, inferred: Seq<Option<SignalType>>|
        #[trigger] argument_prefix(context, call, forms, scope, types, slots, start, limit, positions, inferred, last)
        && inferred.len() == call.call.call.arguments && if collect {
            result matches Some(output) && output.call == *call && output.inputs@ == inferred
        } else { result.is_none() }) by {
        assert(argument_prefix(context, call, forms, scope, types, slots, start, limit, visited, values, last));
    };
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    #[verifier::opaque]
    pub(in crate::project::use_aliases) closed spec fn projected_input_arguments(
        &self, at: (usize, usize, usize, usize), limit: u64, types: Seq<Option<SignalType>>,
        wiring: &FuncWiring, projected: Seq<ProjectedCallArgument>,
    ) -> bool {
        let (file, entry, definition, reference) = at;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int];
        let row = parsed.definitions@[frame.definitions.start + definition];
        let forms = parsed.syntax.forms@;
        let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
        let start = row.signals.start - frame.signals.start;
        let context = (self, file, entry, definition);
        ||| projected.len() == 0 && self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(None))
        ||| exists|call: TypedFuncCall, visited: Seq<usize>, values: Seq<Option<SignalType>>|
            #![trigger self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call))),
                argument_projections_match(context, forms, wiring, types, slots, start, visited, values, projected)]
            self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call)))
                && values.len() == call.call.call.arguments
                && values.len() == call.call.target.port_counts().inputs
                && argument_prefix((self, file, entry, definition), &call, forms, wiring, types, slots, start, limit,
                    visited, values, forms[call.call.call.form as int]->List_end)
                && argument_projections_match(context, forms, wiring, types, slots, start, visited, values, projected)
    }

    proof fn record_projected_inputs(
        &self, at: (usize, usize, usize, usize), limit: u64, types: Seq<Option<SignalType>>,
        wiring: &FuncWiring, call: TypedFuncCall, visited: Seq<usize>, values: Seq<Option<SignalType>>,
        projected: Seq<ProjectedCallArgument>,
    )
        requires
            self.func_call_signature_evidence(at.0, at.1, at.2, at.3, limit, Ok(Some(call))),
            values.len() == call.call.call.arguments == call.call.target.port_counts().inputs,
            ({
                let parsed = &self.targets.project_model().circuits_model()[at.0 as int];
                let frame = parsed.entry_ranges@[at.1 as int];
                let row = parsed.definitions@[frame.definitions.start + at.2];
                let forms = parsed.syntax.forms@;
                let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
                let start = row.signals.start - frame.signals.start;
                &&& argument_prefix((self, at.0, at.1, at.2), &call, forms, wiring, types, slots, start, limit,
                    visited, values, forms[call.call.call.form as int]->List_end)
                &&& argument_projections_match((self, at.0, at.1, at.2), forms, wiring, types, slots, start, visited, values, projected)
            }),
        ensures self.projected_input_arguments(at, limit, types, wiring, projected),
    {
        reveal(UseAliases::projected_input_arguments);
    }

    proof fn projected_inputs_witness(
        &self, at: (usize, usize, usize, usize), limit: u64, types: Seq<Option<SignalType>>,
        wiring: &FuncWiring, projected: Seq<ProjectedCallArgument>,
    ) -> (witness: (TypedFuncCall<'p, 'a>, Seq<usize>, Seq<Option<SignalType<'p, 'a>>>))
        requires
            self.projected_input_arguments(at, limit, types, wiring, projected),
            projected.len() > 0 || !self.func_call_signature_evidence(at.0, at.1, at.2, at.3, limit, Ok(None)),
        ensures ({
            let (file, entry, definition, reference) = at;
            let parsed = &self.targets.project_model().circuits_model()[file as int];
            let frame = parsed.entry_ranges@[entry as int];
            let row = parsed.definitions@[frame.definitions.start + definition];
            let forms = parsed.syntax.forms@;
            let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
            let start = row.signals.start - frame.signals.start;
            let (call, visited, values) = witness;
            &&& self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call)))
            &&& values.len() == call.call.call.arguments == call.call.target.port_counts().inputs
            &&& argument_prefix((self, file, entry, definition), &call, forms, wiring, types, slots, start, limit,
                visited, values, forms[call.call.call.form as int]->List_end)
            &&& argument_projections_match((self, file, entry, definition), forms, wiring, types, slots, start, visited, values, projected)
        }),
    {
        let (file, entry, definition, reference) = at;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int];
        let row = parsed.definitions@[frame.definitions.start + definition];
        let forms = parsed.syntax.forms@;
        let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
        let start = row.signals.start - frame.signals.start;
        reveal(UseAliases::projected_input_arguments);
        choose|call: TypedFuncCall, visited: Seq<usize>, values: Seq<Option<SignalType>>|
            #![trigger self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call))),
                argument_projections_match((self, file, entry, definition), forms, wiring, types, slots, start, visited, values, projected)]
            self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call)))
                && values.len() == call.call.call.arguments
                && values.len() == call.call.target.port_counts().inputs
                && argument_prefix((self, file, entry, definition), &call, forms, wiring, types, slots, start, limit,
                    visited, values, forms[call.call.call.form as int]->List_end)
                && argument_projections_match((self, file, entry, definition), forms, wiring, types, slots, start, visited, values, projected)
    }

    proof fn projected_argument_leaf<'s>(
        context: (&UseAliases, usize, usize, usize), call: &'s TypedFuncCall<'p, 'a>, forms: Seq<Form>, wiring: &FuncWiring<'p, 'a>, types: Seq<Option<SignalType<'p, 'a>>>,
        slots: Seq<usize>, start: int, form: usize, index: usize, limit: u64, value: Option<SignalType<'p, 'a>>,
    ) -> (leaf: (CallPortType<'s, 'p, 'a>, Option<SignalType<'p, 'a>>))
        requires argument_result(context, call, forms, wiring, types, slots, start, form, index, limit, Ok(value)),
        ensures
            form < forms.len() && direct_call_argument(forms, call.call.call, form as int),
            input_port_matches(call, index as int, leaf.0),
            leaf_result(call.call.source, forms[form as int], &leaf.0, leaf.1, limit, Ok(value)),
            known_argument(context, limit, forms, wiring, types, slots, start, form, leaf.1),
    {
        reveal(argument_result);
        let (port, known, result) = choose|port: CallPortType, known: Option<SignalType>, result: Result<Option<SignalType>, CallInputReason>|
            #[trigger] input_port_matches(call, index as int, port)
            && #[trigger] leaf_result(call.call.source, forms[form as int], &port, known, limit, result)
            && known_argument(context, limit, forms, wiring, types, slots, start, form, known)
            && reported_argument(call.call.source, forms[form as int], index, port, result, Ok(value));
        assert(result == Ok(value));
        (port, known)
    }

    /// 引数がない場合も含め、保持した引数の個数が呼び出し先の入力数と一致することを示す。
    pub(in crate::project::use_aliases) proof fn checked_projected_input_count(
        &self, at: (usize, usize, usize, usize), limit: u64, types: Seq<Option<SignalType>>,
        wiring: &FuncWiring, call: TypedFuncCall, projected: Seq<ProjectedCallArgument>,
    )
        requires
            self.can_resolve(),
            self.projected_input_arguments(at, limit, types, wiring, projected),
            self.func_call_signature_evidence(at.0, at.1, at.2, at.3, limit, Ok(Some(call))),
            call.signature is Function,
        ensures projected.len() == call.signature->Function_0.inputs@.len(),
    {
        self.resolved_signature_excludes_no_call(at, limit, call);
        let (other, _, values) = self.projected_inputs_witness(at, limit, types, wiring, projected);
        self.successful_call_signatures_agree(at.0, at.1, at.2, at.3, limit, call, other);
        self.typed_call_arguments_ready(at.0, at.1, at.2, at.3, limit, other);
        reveal(argument_projections_match);
        assert(projected.len() == values.len());
    }

    /// 展開用に保存した引数から、元フォームと呼び出し先の入力型の対応を取り出す。
    pub(in crate::project::use_aliases) proof fn checked_projected_argument(
        &self, at: (usize, usize, usize, usize), limit: u64, types: Seq<Option<SignalType>>,
        wiring: &FuncWiring, call: TypedFuncCall, projected: Seq<ProjectedCallArgument>, index: int,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(at.0, at.1, limit, Ok(FuncWiringResult::Checked(*wiring))),
            self.projected_input_arguments(at, limit, types, wiring, projected),
            self.func_call_signature_evidence(at.0, at.1, at.2, at.3, limit, Ok(Some(call))),
            0 <= index < projected.len(),
        ensures ({
            let parsed = &self.targets.project_model().circuits_model()[at.0 as int];
            let absolute = parsed.entry_ranges@[at.1 as int].definitions.start + at.2;
            let form = projected[index].form;
            let expected = match call.signature {
                FuncCallSignature::Nor => ResolvedPortType::Bits(1),
                FuncCallSignature::Function(ports) => ports.inputs@[index].ty,
            };
            &&& projected.len() == call.call.target.port_counts().inputs
            &&& match call.signature {
                FuncCallSignature::Nor => projected.len() == 2,
                FuncCallSignature::Function(ports) => projected.len() == ports.inputs@.len(),
            }
            &&& form < parsed.syntax.forms@.len()
            &&& direct_call_argument(parsed.syntax.forms@, call.call.call, form as int)
            &&& match projected[index].source {
                CallArgumentSource::Driver(driver) => {
                    let ty = signal_type_at(wiring, types, driver);
                    &&& parsed.syntax.forms@[form as int] is Atom && parsed.syntax.forms@[form as int]->Atom_kind is Name
                    &&& ty matches Some(known)
                    &&& port_types_equal(known.ty, expected)
                    &&& exists|position: int| parsed.definitions@[absolute].signals.start <= position
                        < parsed.definitions@[absolute].signals.end
                        && (#[trigger] parsed.signals@[position]) == form
                        && 0 <= position - parsed.entry_ranges@[at.1 as int].signals.start < wiring.signals@.len()
                        && wiring.signals@[position - parsed.entry_ranges@[at.1 as int].signals.start].driver == driver
                    &&& match driver {
                        OutputDriver::Input(port) => port < wiring.drivers.signature.inputs@.len(),
                        OutputDriver::Definition(port) => port < wiring.drivers.definitions@.len()
                            && wiring.drivers.definitions@[port as int].definition < absolute,
                    }
                },
                CallArgumentSource::Literal(width) => {
                    let span = form_span(parsed.syntax.forms@[form as int]);
                    let source = &self.targets.project_model().sources_model()[at.0 as int];
                    &&& parsed.syntax.forms@[form as int] is Atom
                    &&& (parsed.syntax.forms@[form as int]->Atom_kind is Natural
                        || parsed.syntax.forms@[form as int]->Atom_kind is Binary
                        || parsed.syntax.forms@[form as int]->Atom_kind is Hexadecimal)
                    &&& expected == ResolvedPortType::Bits(width)
                    &&& span.start < span.end <= source.text.spec_bytes().len()
                    &&& {
                        let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
                        &&& circuit_literal_width_matches(bytes, Some(width), limit, Ok(width))
                        &&& ((width == 1 && bytes.len() == 1 && (bytes[0] == b'0' || bytes[0] == b'1'))
                            || crate::syntax::bare_atom_kind(bytes) == Some(AtomKind::Binary)
                            || crate::syntax::bare_atom_kind(bytes) == Some(AtomKind::Hexadecimal))
                    }
                },
                CallArgumentSource::NestedCall(reference) =>
                    self.func_call_form_reference(at.0, at.1, at.2, form, reference)
                        && self.projected_nested_call_has_type((at.0, at.1, at.2), limit, form, expected),
                CallArgumentSource::Deferred => true,
            }
        }),
    {
        let (file, entry, definition, reference) = at;
        self.typed_call_arguments_ready(file, entry, definition, reference, limit, call);
        self.checked_wiring_is_func(file, entry, limit, *wiring);
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let frame = parsed.entry_ranges@[entry as int];
        let absolute = frame.definitions.start + definition;
        parsed_index_evidence(*source, *parsed);
        build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute);
        let row = parsed.definitions@[absolute];
        let forms = parsed.syntax.forms@;
        let slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
        let start = row.signals.start - frame.signals.start;
        let (other, visited, values) = self.projected_inputs_witness(at, limit, types, wiring, projected);
        self.successful_call_signatures_agree(file, entry, definition, reference, limit, call, other);
        self.typed_call_arguments_ready(file, entry, definition, reference, limit, other);
        assert(projected.len() == values.len() == visited.len()) by { reveal(argument_projections_match); };
        assert(values.len() == other.call.call.arguments == call.call.call.arguments);
        assert(0 <= index < values.len() <= usize::MAX);
        assert(argument_projection_matches((self, file, entry, definition), projected[index], visited[index],
            forms, wiring, types, slots, start, values[index])) by {
            reveal(argument_projections_match);
        };
        let form = projected[index].form;
        let value = values[index];
        assert(visited[index] == form) by { reveal(argument_projection_matches); };
        assert(argument_result((self, file, entry, definition), &other, forms, wiring, types, slots, start, form, index as usize, limit, Ok(value))) by {
            reveal(argument_prefix);
        };
        let (port, known) = Self::projected_argument_leaf((self, file, entry, definition), &other, forms, wiring, types, slots, start,
            form, index as usize, limit, value);
        match (call.signature, other.signature) {
            (FuncCallSignature::Nor, FuncCallSignature::Nor) => {
                assert(projected.len() == 2 && port.ty == ResolvedPortType::Bits(1));
            },
            (FuncCallSignature::Function(ports), FuncCallSignature::Function(other_ports)) => {
                assert(ports.inputs@ == other_ports.inputs@);
                assert(projected.len() == ports.inputs@.len() && port.ty == ports.inputs@[index].ty);
            },
            _ => assert(false),
        }
        reveal(argument_projection_matches);
        match projected[index].source {
            CallArgumentSource::Driver(driver) => {
                assert(value.is_some() && known == value);
                assert(port_types_equal(value->Some_0.ty, port.ty));
                let slot = choose|s: int| 0 <= s < slots.len() && (#[trigger] slots[s]) == form
                    && 0 <= start + s < wiring.signals@.len() && wiring.signals@[start + s].driver == driver
                    && value == signal_type_at(wiring, types, driver);
                vstd::std_specs::vec::axiom_spec_len(&parsed.definitions);
                vstd::std_specs::vec::axiom_spec_len(&parsed.signals);
                assert(frame.definitions.start <= absolute < frame.definitions.end <= parsed.definitions@.len());
                assert(row.signals.start <= row.signals.start + slot < row.signals.end <= parsed.signals@.len());
                self.checked_signal_driver(file, entry, limit, *wiring, absolute as usize,
                    (row.signals.start + slot) as usize);
                assert(parsed.signals@[row.signals.start + slot] == form);
            },
            CallArgumentSource::Literal(width) => {
                assert(port.ty is Bits);
                let expected = port.ty->Bits_0;
                let span = form_span(forms[form as int]);
                assert(*other.call.source == *source);
                assert(span.start < span.end <= source.text.spec_bytes().len()) by { reveal(form_spans_valid); };
                let bytes = other.call.source.text.spec_bytes()[span.start as int..span.end as int];
                assert(circuit_literal_width_matches(bytes, Some(expected), limit, Ok(width)));
                crate::project::literal_width::checked_literal_for_port(bytes, expected, limit, width);
            },
            CallArgumentSource::NestedCall(_) => {
                assert(forms[form as int] is List && value == known);
                assert(nested_output_type((self, file, entry, definition), form, limit, value));
                assert(port_types_equal(value->Some_0.ty, port.ty));
            },
            CallArgumentSource::Deferred => {},
        }
    }

    /// 型が確定した子の出力型と、同じ位置に渡す入力型が一致することを表す。
    pub(in crate::project::use_aliases) closed spec fn projected_nested_call_has_type(
        &self, caller: (usize, usize, usize), limit: u64, form: usize, expected: ResolvedPortType,
    ) -> bool {
        let (file, entry, definition) = caller;
        let parsed = &self.targets.project_model().circuits_model()[file as int];
        &&& form < parsed.syntax.forms@.len() && parsed.syntax.forms@[form as int] is List
        &&& exists|actual: SignalType|
            #[trigger] nested_output_type((self, file, entry, definition), form, limit, Some(actual))
            && port_types_equal(actual.ty, expected)
    }

    /// 子を展開するときに使う参照添字と、出力型を照合した署名を取り出す。
    pub(in crate::project::use_aliases) proof fn projected_nested_call_signature(
        &self, caller: (usize, usize, usize), limit: u64, form: usize, expected: ResolvedPortType,
    ) -> (witness: (usize, TypedFuncCall<'p, 'a>))
        requires self.projected_nested_call_has_type(caller, limit, form, expected),
        ensures
            self.targets.project_model().circuits_model()[caller.0 as int].syntax.forms@[form as int] is List,
            self.func_call_form_reference(caller.0, caller.1, caller.2, form, witness.0),
            self.func_call_signature_evidence(caller.0, caller.1, caller.2, witness.0, limit, Ok(Some(witness.1))),
            witness.1.call.target.port_counts().outputs == 1,
            match witness.1.signature {
                FuncCallSignature::Nor => port_types_equal(ResolvedPortType::Bits(1), expected),
                FuncCallSignature::Function(signature) => port_types_equal(signature.outputs@[0].ty, expected),
            },
    {
        let (file, entry, definition) = caller;
        let context = (self, file, entry, definition);
        let actual = choose|actual: SignalType|
            #[trigger] nested_output_type(context, form, limit, Some(actual))
            && port_types_equal(actual.ty, expected);
        reveal(nested_output_type);
        let result = choose|result: Result<Option<TypedFuncCall>, FuncCallSignatureError>|
            #[trigger] self.func_call_signature_at_form_evidence(file, entry, definition, form, limit, result)
            && Some(actual) == nested_output_from_signature(result);
        assert(result matches Ok(Some(call)) && call.call.target.port_counts().outputs == 1);
        let call = result->Ok_0->Some_0;
        let reference = self.call_signature_at_form_reference(caller, form, limit, call);
        (reference, call)
    }

    spec fn scoped_input_result(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        types: Seq<Option<SignalType>>, scope: &FuncWiring, collect: bool,
        result: Result<Option<CheckedCallInputs>, CallInputError>,
    ) -> bool {
        match result {
            Ok(None) if collect => self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(None)),
            Err(CallInputError::Caller(_)) => false,
            Err(CallInputError::Signature(error)) =>
                self.func_call_signature_evidence(file, entry, definition, reference, limit, Err(error)),
            Err(CallInputError::Count(arity)) => arity.call.arguments != arity.target.port_counts().inputs
                && exists|call: TypedFuncCall| call.call == arity
                    && #[trigger] self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call))),
            _ => (result == Ok(None) && self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(None)))
                || exists|call: TypedFuncCall|
                #[trigger] self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call)))
                    && arguments_match((self, file, entry, definition), &self.targets.project_model().circuits_model()[file as int],
                        scope, types, &call, limit, collect, result),
        }
    }

    /// 引数の結果または最初の診断が、選んだ呼び出しと入力型に対応することを表す。
    pub closed spec fn func_call_input_evidence(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        result: Result<Option<CheckedCallInputs>, CallInputError>,
    ) -> bool {
        match result {
            Err(CallInputError::Caller(error)) => self.func_atom_type_evidence(file, entry, limit, Err(error)),
            _ => exists|typed: FuncAtomTypes| #[trigger] self.func_atom_type_evidence(file, entry, limit, Ok(typed))
                && if let FuncWiringResult::Checked(scope) = typed.literals.wiring {
                    self.scoped_input_result(file, entry, definition, reference, limit, typed.types@, &scope, true, result)
                } else { result == Ok(None) },
        }
    }
    /// 呼び出しを選び、定数と型が確定した裸の信号を入力型と照合する。
    ///
    /// 添字は [`Self::resolve_func_call_signature`] と同じ。呼び出し元の検査で違反がなければ、
    /// 型名の参照、対象外の添字、展開待ちには `None` を返す。
    /// 子呼び出しの単一出力型を入力型と照合する。子の署名を解決できない場合や、
    /// 信号の型が未確定の場合、型検査が未対応の専用フォームでは引数の型を保留する。
    ///
    /// # Errors
    ///
    /// 呼び出し元の検査、呼び出し先の署名、直接の引数の順に診断する。
    pub fn check_func_call_inputs(
        &self, file: usize, entry: usize, definition: usize, reference: usize, max_width: u64,
    ) -> (result: Result<Option<CheckedCallInputs<'p, 'a>>, CallInputError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_call_input_evidence(file, entry, definition, reference, max_width, result),
    {
        let typed = match self.check_func_atom_types(file, entry, max_width) {
            Ok(typed) => typed,
            Err(error) => return Err(CallInputError::Caller(error)),
        };
        let FuncWiringResult::Checked(ref wiring) = typed.literals.wiring else { return Ok(None); };
        proof { self.atom_types_keep_wiring(file, entry, max_width, typed, *wiring); }
        let mut signatures = SignatureCache::new();
        let mut projections = Vec::new();
        let mut target = None;
        self.check_call_inputs_with_types(file, entry, definition, reference, max_width, typed.types.as_slice(), wiring, true,
            &mut signatures, &mut projections, &mut target, false)
    }

    /// 保持した呼び出し先が、同じ参照添字で型検査を通った署名と対応することを表す。
    pub(in crate::project::use_aliases) closed spec fn retained_call_target_matches(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        target: Option<RetainedCallTarget>,
    ) -> bool {
        match target {
            None => self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(None)),
            Some(target) => exists|call: TypedFuncCall|
                #[trigger] self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call)))
                && target == RetainedCallTarget::from_arity(call.call),
        }
    }

    /// 保存した呼び出し先の根拠となった型付き署名を取り出す。
    pub(in crate::project::use_aliases) proof fn retained_callee_signature(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        target: Option<RetainedCallTarget>,
    ) -> (call: TypedFuncCall<'p, 'a>)
        requires
            self.func_call_at(file, entry, definition, reference),
            self.retained_call_target_matches(file, entry, definition, reference, limit, target),
        ensures
            self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call))),
            target == Some(RetainedCallTarget::from_arity(call.call)),
    {
        if target.is_none() {
            self.call_has_signature_result(file, entry, definition, reference, limit, Ok(None));
        }
        choose|typed: TypedFuncCall|
            #[trigger] self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(typed)))
            && target == Some(RetainedCallTarget::from_arity(typed.call))
    }

    /// 型検査で保持した呼び出し先と、指定した署名の参照先が一致することを示す。
    pub(in crate::project::use_aliases) proof fn retained_target_agrees_with_call(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        target: Option<RetainedCallTarget>, call: TypedFuncCall,
    )
        requires
            self.can_resolve(),
            self.retained_call_target_matches(file, entry, definition, reference, limit, target),
            self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call))),
        ensures target == Some(RetainedCallTarget::from_arity(call.call)),
    {
        self.typed_call_arguments_ready(file, entry, definition, reference, limit, call);
        let chosen = self.retained_callee_signature(file, entry, definition, reference, limit, target);
        self.successful_call_signatures_agree(file, entry, definition, reference, limit, call, chosen);
        self.typed_call_arguments_ready(file, entry, definition, reference, limit, chosen);
    }

    /// 呼び出し元の配線と型を再利用し、展開で使う引数と呼び出し先を必要に応じて保持する。
    fn check_call_inputs_with_types(
        &self, file: usize, entry: usize, definition: usize, reference: usize, max_width: u64,
        types: &[Option<SignalType<'p, 'a>>], wiring: &FuncWiring<'p, 'a>, collect: bool,
        signatures: &mut SignatureCache<'p, 'a>,
        projections: &mut Vec<ProjectedCallArgument>, target: &mut Option<RetainedCallTarget>, retain: bool,
    ) -> (result: Result<Option<CheckedCallInputs<'p, 'a>>, CallInputError<'p, 'a>>)
        requires
            self.can_resolve(), self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
            types@.len() == wiring.drivers.definitions@.len(),
            old(signatures).matches(self, max_width), old(target).is_none(),
        ensures self.scoped_input_result(file, entry, definition, reference, max_width, types@, wiring, collect, result),
            final(signatures).matches(self, max_width),
            result.is_ok() ==> old(projections)@.len() <= final(projections)@.len(),
            result.is_ok() ==> final(projections)@.take(old(projections)@.len() as int) == old(projections)@,
            result.is_ok() && !retain ==> final(projections)@ == old(projections)@,
            retain && result.is_ok() ==> self.retained_call_target_matches(file, entry, definition, reference, max_width, *final(target)),
            retain && result.is_ok() ==> self.projected_input_arguments((file, entry, definition, reference),
                max_width, types@, wiring, final(projections)@.skip(old(projections)@.len() as int)),
    {
        let ghost context = (self, file, entry, definition);
        let ghost initial = projections@;
        let ghost begin = initial.len() as int;
        assert(initial.take(begin) =~= initial);
        assert(initial.skip(begin) =~= Seq::empty());
        let (arity, owned) = if collect {
            match self.resolve_func_call_signature(file, entry, definition, reference, max_width) {
                Ok(Some(TypedFuncCall { call, signature })) => (call, Some(signature)),
                Ok(None) => {
                    assert(self.projected_input_arguments((file, entry, definition, reference),
                        max_width, types@, wiring, projections@.skip(begin))) by { reveal(UseAliases::projected_input_arguments); };
                    return Ok(None);
                },
                Err(error) => return Err(CallInputError::Signature(error)),
            }
        } else {
            match self.prepare_func_call_signature(file, entry, definition, reference, max_width, signatures) {
                Ok(Some(call)) => (call, None),
                Ok(None) => {
                    assert(self.projected_input_arguments((file, entry, definition, reference),
                        max_width, types@, wiring, projections@.skip(begin))) by { reveal(UseAliases::projected_input_arguments); };
                    return Ok(None);
                },
                Err(error) => return Err(CallInputError::Signature(error)),
            }
        };
        let ghost call = match &owned {
            Some(signature) => TypedFuncCall { call: arity, signature: *signature },
            None => cached_call_model(signatures, arity),
        };
        let count = arity.target.ports().inputs;
        if count != arity.call.arguments {
            return Err(CallInputError::Count(arity));
        }
        let signature = match &owned {
            Some(FuncCallSignature::Nor) => None,
            Some(FuncCallSignature::Function(signature)) => Some(signature),
            None => cached_signature(signatures, &arity),
        };
        let project = self.targets.project();
        proof {
            self.checked_wiring_is_func(file, entry, max_width, *wiring);
            self.typed_call_arguments_ready(file, entry, definition, reference, max_width, call);
        }
        let parsed = &project.circuits()[file];
        let source = &project.sources()[file];
        let forms = parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int,
                parsed.entry_ranges@[entry as int].definitions.start + definition);
        }
        let frame = &parsed.entry_ranges[entry];
        let absolute = frame.definitions.start + definition;
        let row = &parsed.definitions[absolute];
        let ref_pos = row.references.start + reference;
        let mut remaining = call_argument_range(forms, &arity.call);
        let mut ordinal = 0;
        let mut inputs: Vec<Option<SignalType>> = Vec::new();
        let ghost slots = parsed.signals@[row.signals.start as int..row.signals.end as int];
        let ghost start = row.signals.start - frame.signals.start;
        let ghost visited: Seq<usize> = Seq::empty();
        let ghost values: Seq<Option<SignalType>> = Seq::empty();
        proof {
            first_call_argument_evidence(forms@, call.call.call, remaining);
            assert(argument_prefix(context, &call, forms@, wiring, types@, slots, start,
                max_width, visited, values, remaining.start)) by { reveal(argument_prefix); };
            if retain {
                assert(argument_projections_match(context, forms@, wiring, types@, slots, start,
                    visited, values, projections@.skip(begin))) by { reveal(argument_projections_match); };
            }
        }
        while remaining.start < remaining.end
            invariant
                self.can_resolve(), *project == self.targets.project_model(),
                context == (self, file, entry, definition),
                signatures.matches(self, max_width),
                arity == call.call,
                owned.is_some() == collect,
                owned matches Some(signature) ==> signature == call.signature,
                match signature {
                    None => call.signature is Nor,
                    Some(signature) => call.signature == FuncCallSignature::Function(*signature),
                },
                file < project.circuits_model().len(), file < project.sources_model().len(),
                *source == project.sources_model()[file as int], *parsed == project.circuits_model()[file as int],
                *source == *call.call.source, forms@ == parsed.syntax.forms@,
                parsed_circuit_matches(*source, *parsed),
                entry < parsed.syntax.entries@.len(), entry < parsed.entry_ranges@.len(),
                *frame == parsed.entry_ranges@[entry as int],
                frame.definitions.start <= absolute < frame.definitions.end <= parsed.definitions@.len(),
                absolute == frame.definitions.start + definition, *row == parsed.definitions@[absolute as int],
                row.references.start <= ref_pos < row.references.end, ref_pos == row.references.start + reference,
                row.signals.start <= row.signals.end <= parsed.signals@.len(),
                slots == parsed.signals@[row.signals.start as int..row.signals.end as int],
                start == row.signals.start - frame.signals.start,
                self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
                self.func_call_signature_evidence(file, entry, definition, reference, max_width, Ok(Some(call))),
                types@.len() == wiring.drivers.definitions@.len(),
                ordinal == visited.len() == values.len(),
                ordinal <= count == call.call.call.arguments,
                if collect { values == inputs@ } else { inputs@.len() == 0 },
                initial == old(projections)@, begin == initial.len(), begin <= projections@.len(),
                projections@.take(begin) == initial,
                if retain { argument_projections_match(context, forms@, wiring, types@, slots, start, visited, values, projections@.skip(begin)) }
                    else { projections@ == initial },
                count == call.call.target.port_counts().inputs,
                remaining.start <= remaining.end <= forms@.len(),
                call.call.call.form < forms@.len(), forms@[call.call.call.form as int] is List,
                remaining.end == forms@[call.call.call.form as int]->List_end,
                expression_region(forms@, remaining.start as int, remaining.end as int),
                call_argument_sequence(forms@, remaining, count - ordinal),
                remaining.start < remaining.end ==> direct_call_argument(forms@, call.call.call, remaining.start as int),
                argument_prefix(context, &call, forms@, wiring, types@, slots, start, max_width, visited, values, remaining.start),
            decreases remaining.end - remaining.start,
        {
            proof {
                parsed_index_evidence(*source, *parsed);
                self.typed_call_arguments_ready(file, entry, definition, reference, max_width, call);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
            }
            let Some(argument) = next_call_argument(forms, remaining.start..remaining.end) else {
                proof { assert(false); }
                unreachable!()
            };
            let Some(port) = signature_port(signature, PortDirection::Input, ordinal) else {
                proof { assert(false); }
                unreachable!()
            };
            assert(input_port_matches(&call, ordinal as int, port));
            let root = argument.start;
            let (known, driver, nested_reference) = if matches!(forms[root], Form::Atom { kind: AtomKind::Name, .. }) {
                let pos = indexed_call_signal(source.text, forms, row, parsed.references.as_slice(), ref_pos, &arity.call,
                    parsed.signals.as_slice(), root);
                proof { self.checked_signal_driver(file, entry, max_width, *wiring, absolute, pos); }
                let bound = &wiring.signals[pos - frame.signals.start];
                assert(slots[pos - row.signals.start] == root);
                let ty = inherit_type(wiring, types, bound.driver);
                assert(known_argument(context, max_width, forms@, wiring, types@, slots, start, root, ty)) by {
                    let s = pos - row.signals.start;
                    assert(slots[s] == root);
                    assert(ty == signal_type_at(wiring, types@, wiring.signals@[start + s].driver));
                };
                (ty, Some(bound.driver), None)
            } else if matches!(forms[root], Form::List { .. }) {
                let (ty, reference) = nested_output_type_at(self, file, entry, definition, root, max_width);
                (ty, None, reference)
            } else { (None, None, None) };
            let ghost input = known;
            let leaf = check_leaf(source, forms, root, &port, known, max_width);
            let ghost checked = leaf;
            let value = match leaf {
                Ok(value) => value,
                Err(reason) => {
                    let error = CallInputError::Argument {
                        index: ordinal, argument: form_location(source, forms, root),
                        expected: port.ty,
                        required_at: if let Some(annotation) = port.annotation { Some(copy_location(annotation)) } else { None },
                        reason,
                    };
                    proof {
                        self::record_argument(context, &call, forms@, wiring, types@, slots, start,
                            root, ordinal, max_width, port, input, checked, Err(error));
                        reveal(argument_prefix);
                        assert(visited.len() == ordinal && ordinal < count);
                        assert(argument_prefix(context, &call, forms@, wiring, types@, slots, start,
                            max_width, visited, values, root));
                        record_failed_argument(context, parsed, wiring, types@, &call, max_width, collect,
                            error, visited, values, root);
                    }
                    return Err(error);
                }
            };
            proof {
                self::record_argument(context, &call, forms@, wiring, types@, slots, start,
                    root, ordinal, max_width, port, input, checked, Ok(value));
            }
            let ghost previous_projections = projections@;
            if retain {
                let source = if let Some(typed) = &value {
                    if matches!(forms[root], Form::List { .. }) {
                        let Some(reference) = nested_reference else {
                            proof { reveal(leaf_result); assert(false); }
                            unreachable!()
                        };
                        CallArgumentSource::NestedCall(reference)
                    } else if let Some(driver) = driver {
                        CallArgumentSource::Driver(driver)
                    } else if let ResolvedPortType::Bits(width) = typed.ty {
                        CallArgumentSource::Literal(width)
                    } else {
                        proof { assert(false); }
                        unreachable!()
                    }
                } else { CallArgumentSource::Deferred };
                let projection = ProjectedCallArgument { form: root, source };
                assert(argument_projection_matches(context, projection, root, forms@, wiring, types@, slots, start, value)) by {
                    reveal(argument_projection_matches);
                };
                projections.push(projection);
                assert(projections@.take(begin) =~= initial);
                proof {
                    assert(projections@.skip(begin) =~= previous_projections.skip(begin).push(projection));
                    extend_argument_projections(context, forms@, wiring, types@, slots, start,
                        visited, values, previous_projections.skip(begin), root, value, projection);
                }
            }
            proof {
                following_call_argument(forms@, call.call.call, root as int, argument.end as int);
                extend_argument_prefix(context, &call, forms@, wiring, types@, slots, start, max_width,
                    visited, values, root, argument.end, value);
                visited = visited.push(root);
                values = values.push(value);
            }
            if collect {
                inputs.push(value);
            }
            remaining.start = argument.end;
            ordinal += 1;
        }
        if retain {
            let chosen = match arity.target {
                FuncCallTarget::Nor => RetainedCallTarget::Nor,
                FuncCallTarget::Function { file, entry, .. } => RetainedCallTarget::Function(file, entry),
            };
            assert(chosen == RetainedCallTarget::from_arity(call.call));
            assert(self.retained_call_target_matches(file, entry, definition, reference, max_width, Some(chosen)));
            *target = Some(chosen);
        }
        let result = Ok(if let Some(signature) = owned {
            Some(CheckedCallInputs { call: TypedFuncCall { call: arity, signature }, inputs })
        } else { None });
        proof {
            exhausted_call_arguments(forms@, remaining, count - ordinal);
            assert(ordinal == count && remaining.start == remaining.end);
            let last = forms@[call.call.call.form as int]->List_end;
            assert(remaining.start == last);
            assert(result is Ok);
            record_completed_arguments(context, parsed, wiring, types@, &call, max_width, collect,
                result->Ok_0, visited, values);
            if retain {
                let retained = projections@.skip(begin);
                self.record_projected_inputs((file, entry, definition, reference), max_width, types@, wiring,
                    call, visited, values, retained);
            }
        }
        result
    }
}

} // verus!
