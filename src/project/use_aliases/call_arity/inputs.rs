//! 呼び出しの直接の引数に、宣言順で対応する入力型を照合する。

use super::{CallPortType, FuncCallArity, FuncCallSignatureError, TypedFuncCall, UseAliases};
use super::FuncCallSignature;
use super::typed::{cached_signature, signature_port};
#[cfg(verus_only)]
use super::typed::cached_call_model;
use super::super::signature_cache::SignatureCache;
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
pub use batch::FuncCallInputsError;

verus! {

/// 一つの呼び出しと、宣言順に対応する引数の確定型。
#[derive(Debug)]
pub struct CheckedCallInputs<'p, 'a> {
    /// 呼び出しの位置と、名前解決で選ばれた署名。
    pub call: TypedFuncCall<'p, 'a>,
    /// 直接の引数ごとの型。未検査の複合式や未確定の信号の型は `None`。
    pub inputs: Vec<Option<SignalType<'p, 'a>>>,
}

/// 呼び出しの引数が入力ポートの型に合わなかった理由。
#[derive(Debug)]
pub enum CallInputReason<'p, 'a> {
    /// 二進・十六進または固定の 1 ビット定数に割り当てる幅の違反。
    LiteralWidth(CircuitLiteralWidthError),
    /// 構造体型の入力に裸の定数を渡した。
    StructRequired,
    /// 確定した信号の型が入力型と異なる。型とその根拠を持つ。
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
    } else if form is Atom && form->Atom_kind is Name {
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
        Form::Atom { kind: AtomKind::Name, .. } => {
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

spec fn known_argument(
    forms: Seq<Form>, scope: &FuncWiring, types: Seq<Option<SignalType>>, slots: Seq<usize>,
    signal_start: int, at: usize, known: Option<SignalType>,
) -> bool {
    forms[at as int] is Atom && forms[at as int]->Atom_kind is Name
        ==> exists|s: int| 0 <= s < slots.len() && #[trigger] slots[s] == at
            && 0 <= signal_start + s < scope.signals@.len()
            && known == signal_type_at(scope, types, scope.signals@[signal_start + s].driver)
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
    call: &TypedFuncCall, forms: Seq<Form>, scope: &FuncWiring, types: Seq<Option<SignalType>>,
    slots: Seq<usize>, signal_start: int, at: usize, ordinal: usize, limit: u64,
    result: Result<Option<SignalType>, CallInputError>,
) -> bool {
    &&& at < forms.len() && direct_call_argument(forms, call.call.call, at as int)
    &&& exists|port: CallPortType, known: Option<SignalType>, leaf: Result<Option<SignalType>, CallInputReason>|
        #[trigger] input_port_matches(call, ordinal as int, port)
        && #[trigger] leaf_result(call.call.source, forms[at as int], &port, known, limit, leaf)
        && known_argument(forms, scope, types, slots, signal_start, at, known)
        && reported_argument(call.call.source, forms[at as int], ordinal, port, leaf, result)
}

proof fn record_argument(
    call: &TypedFuncCall, forms: Seq<Form>, scope: &FuncWiring, types: Seq<Option<SignalType>>,
    slots: Seq<usize>, signal_start: int, at: usize, ordinal: usize, limit: u64,
    port: CallPortType, known: Option<SignalType>, leaf: Result<Option<SignalType>, CallInputReason>,
    result: Result<Option<SignalType>, CallInputError>,
)
    requires
        at < forms.len() && direct_call_argument(forms, call.call.call, at as int),
        input_port_matches(call, ordinal as int, port),
        known_argument(forms, scope, types, slots, signal_start, at, known),
        leaf_result(call.call.source, forms[at as int], &port, known, limit, leaf),
        reported_argument(call.call.source, forms[at as int], ordinal, port, leaf, result),
    ensures argument_result(call, forms, scope, types, slots, signal_start, at, ordinal, limit, result),
{
    reveal(argument_result);
    assert(exists|p: CallPortType, k: Option<SignalType>, l: Result<Option<SignalType>, CallInputReason>|
        #[trigger] input_port_matches(call, ordinal as int, p)
        && #[trigger] leaf_result(call.call.source, forms[at as int], &p, k, limit, l)
        && known_argument(forms, scope, types, slots, signal_start, at, k)
        && reported_argument(call.call.source, forms[at as int], ordinal, p, l, result)) by {
        assert(input_port_matches(call, ordinal as int, port));
        assert(leaf_result(call.call.source, forms[at as int], &port, known, limit, leaf));
    };
}

#[verifier::opaque]
spec fn argument_prefix(
    call: &TypedFuncCall, forms: Seq<Form>, scope: &FuncWiring, types: Seq<Option<SignalType>>,
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
        &&& argument_result(call, forms, scope, types, slots, signal_start, this as usize, i as usize, limit, Ok(values[i]))
    }
}

spec fn after_argument(forms: Seq<Form>, at: int) -> int {
    if forms[at] is List { forms[at]->List_end as int } else { at + 1 }
}

spec fn arguments_match(
    parsed: &NamedBuildCircuit, entry: usize, definition: usize, scope: &FuncWiring,
    types: Seq<Option<SignalType>>, call: &TypedFuncCall, limit: u64, collect: bool,
    result: Result<Option<CheckedCallInputs>, CallInputError>,
) -> bool {
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
                #[trigger] argument_prefix(call, forms, scope, types, slots, start, limit, visited, values, last)
                    && values.len() == count && if collect {
                        output matches Some(output) && output.call == *call && output.inputs@ == values
                    } else { output.is_none() },
        Err(error) => exists|visited: Seq<usize>, values: Seq<Option<SignalType>>, at: usize|
            #[trigger] argument_prefix(call, forms, scope, types, slots, start, limit, visited, values, at)
                && visited.len() < count
                && argument_result(call, forms, scope, types, slots, start, at, visited.len() as usize, limit, Err(error)),
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
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
                    && arguments_match(&self.targets.project_model().circuits_model()[file as int], entry,
                        definition, scope, types, &call, limit, collect, result),
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
    /// 複合式や未確定の信号の型は保留する。
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
        self.check_call_inputs_with_types(file, entry, definition, reference, max_width, typed.types.as_slice(), wiring, true,
            &mut signatures)
    }

    /// 呼び出し元の配線と型を再利用し、必要な場合だけ引数の型を実行時の配列に残す。
    fn check_call_inputs_with_types(
        &self, file: usize, entry: usize, definition: usize, reference: usize, max_width: u64,
        types: &[Option<SignalType<'p, 'a>>], wiring: &FuncWiring<'p, 'a>, collect: bool,
        signatures: &mut SignatureCache<'p, 'a>,
    ) -> (result: Result<Option<CheckedCallInputs<'p, 'a>>, CallInputError<'p, 'a>>)
        requires
            self.can_resolve(), self.func_wiring_evidence(file, entry, max_width, Ok(FuncWiringResult::Checked(*wiring))),
            types@.len() == wiring.drivers.definitions@.len(),
            old(signatures).matches(self, max_width),
        ensures self.scoped_input_result(file, entry, definition, reference, max_width, types@, wiring, collect, result),
            final(signatures).matches(self, max_width),
    {
        let (arity, owned) = if collect {
            match self.resolve_func_call_signature(file, entry, definition, reference, max_width) {
                Ok(Some(TypedFuncCall { call, signature })) => (call, Some(signature)),
                Ok(None) => return Ok(None),
                Err(error) => return Err(CallInputError::Signature(error)),
            }
        } else {
            match self.prepare_func_call_signature(file, entry, definition, reference, max_width, signatures) {
                Ok(Some(call)) => (call, None),
                Ok(None) => return Ok(None),
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
            reveal(argument_prefix);
        }
        while remaining.start < remaining.end
            invariant
                self.can_resolve(), *project == self.targets.project_model(),
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
                ordinal == values.len() <= count == call.call.call.arguments,
                if collect { values == inputs@ } else { inputs@.len() == 0 },
                count == call.call.target.port_counts().inputs,
                remaining.start <= remaining.end <= forms@.len(),
                call.call.call.form < forms@.len(), forms@[call.call.call.form as int] is List,
                remaining.end == forms@[call.call.call.form as int]->List_end,
                expression_region(forms@, remaining.start as int, remaining.end as int),
                call_argument_sequence(forms@, remaining, count - ordinal),
                remaining.start < remaining.end ==> direct_call_argument(forms@, call.call.call, remaining.start as int),
                argument_prefix(&call, forms@, wiring, types@, slots, start, max_width, visited, values, remaining.start),
            decreases remaining.end - remaining.start,
        {
            proof {
                parsed_index_evidence(*source, *parsed);
                self.typed_call_arguments_ready(file, entry, definition, reference, max_width, call);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, absolute as int);
                reveal(argument_result);
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
            let known = if matches!(forms[root], Form::Atom { kind: AtomKind::Name, .. }) {
                let pos = indexed_call_signal(source.text, forms, row, parsed.references.as_slice(), ref_pos, &arity.call,
                    parsed.signals.as_slice(), root);
                proof { self.checked_signal_driver(file, entry, max_width, *wiring, absolute, pos); }
                let bound = &wiring.signals[pos - frame.signals.start];
                assert(slots[pos - row.signals.start] == root);
                let ty = inherit_type(wiring, types, bound.driver);
                assert(known_argument(forms@, wiring, types@, slots, start, root, ty)) by {
                    let s = pos - row.signals.start;
                    assert(slots[s] == root);
                    assert(ty == signal_type_at(wiring, types@, wiring.signals@[start + s].driver));
                };
                ty
            } else { None };
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
                        self::record_argument(&call, forms@, wiring, types@, slots, start,
                            root, ordinal, max_width, port, input, checked, Err(error));
                        reveal(argument_prefix);
                        assert(visited.len() == ordinal && ordinal < count);
                        assert(argument_prefix(&call, forms@, wiring, types@, slots, start,
                            max_width, visited, values, root));
                        assert(arguments_match(parsed, entry, definition, wiring, types@, &call, max_width, collect, Err(error)));
                    }
                    return Err(error);
                }
            };
            proof {
                self::record_argument(&call, forms@, wiring, types@, slots, start,
                    root, ordinal, max_width, port, input, checked, Ok(value));
            }
            let ghost before = values;
            let ghost prior = visited;
            proof {
                reveal(argument_prefix);
                following_call_argument(forms@, call.call.call, root as int, argument.end as int);
                visited = visited.push(root);
                values = values.push(value);
            }
            if collect {
                inputs.push(value);
            }
            proof {
                assert forall|i: int| 0 <= i < visited.len() implies {
                    let this = #[trigger] visited[i] as int;
                    &&& this == if i == 0 { call.call.call.form + 2 } else { after_argument(forms@, visited[i - 1] as int) }
                    &&& argument_result(&call, forms@, wiring, types@, slots, start, this as usize,
                        i as usize, max_width, Ok(values[i]))
                } by {
                    if i < ordinal { assert(visited[i] == prior[i] && values[i] == before[i]); }
                };
            }
            remaining.start = argument.end;
            ordinal += 1;
        }
        let result = Ok(if let Some(signature) = owned {
            Some(CheckedCallInputs { call: TypedFuncCall { call: arity, signature }, inputs })
        } else { None });
        proof {
            exhausted_call_arguments(forms@, remaining, count - ordinal);
            assert(arguments_match(parsed, entry, definition, wiring, types@, &call, max_width, collect, result));
        }
        result
    }
}

} // verus!
