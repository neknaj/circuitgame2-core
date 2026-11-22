//! 呼び出し先の宣言を、その宣言が属するスコープで型解決する。

use super::{DefinitionReferenceError, FuncCallArity, FuncCallTarget, UseAliases};
use super::super::signature_cache::SignatureCache;
#[cfg(verus_only)]
use super::{ResolvedDefinitionReference, target_ports_match};
use crate::project::{LocatedName, PortDirection, ResolvedPortType, TypedRoutineSignature, TypedSignatureError};
#[cfg(verus_only)]
use crate::project::{circuits::parsed_index_evidence, location_in_source};
#[cfg(verus_only)]
use crate::syntax::circuit::{Head, RoutineArity, call_arguments_match, call_shape_matches, routine_arity_matches};
#[cfg(verus_only)]
use crate::syntax::{complete_list_indices, nested_list_indices};
use vstd::prelude::*;

verus! {

/// 組み合わせ回路を呼び出すときに使う型付き署名。
#[derive(Debug)]
pub enum FuncCallSignature<'p, 'a> {
    /// 基底 NOR の 1 ビット入力 2 本と 1 ビット出力 1 本。
    Nor,
    /// 関数の宣言順の入出力型。型名は宣言元のスコープで解決済み。
    Function(TypedRoutineSignature<'p, 'a>),
}

/// 呼び出しに使うポート型と、その型を要求する注釈。
#[derive(Debug)]
pub struct CallPortType<'s, 'p, 'a> {
    /// ポートが受け取る、または返す型。
    pub ty: ResolvedPortType<'p, 'a>,
    /// 関数の元の型注釈。基底 NOR では `None`。
    pub annotation: Option<&'s LocatedName<'p, 'a>>,
}

impl<'p, 'a> FuncCallSignature<'p, 'a> {
    /// 入力または出力の宣言順にポート型を参照する。添字が範囲外なら `None`。
    pub fn port<'s>(&'s self, direction: PortDirection, index: usize) -> (port: Option<CallPortType<'s, 'p, 'a>>)
        ensures signature_port_matches(*self, direction, index, port),
    {
        match self {
            Self::Nor => signature_port(None, direction, index),
            Self::Function(signature) => signature_port(Some(signature), direction, index),
        }
    }
}

/// ポート型と注釈の参照が、宣言順の指定位置に対応することを表す。
pub open spec fn signature_port_matches(
    signature: FuncCallSignature, direction: PortDirection, index: usize, port: Option<CallPortType>,
) -> bool {
    match signature {
        FuncCallSignature::Nor =>
            if index < (if direction is Input { 2usize } else { 1usize }) {
                port == Some(CallPortType { ty: ResolvedPortType::Bits(1), annotation: None })
            } else { port.is_none() },
        FuncCallSignature::Function(signature) => {
            let ports = if direction is Input { signature.inputs@ } else { signature.outputs@ };
            if index < ports.len() {
                let selected = ports[index as int];
                port matches Some(port) && port.ty == selected.ty
                    && (port.annotation matches Some(annotation) && *annotation == selected.annotation)
            } else { port.is_none() }
        },
    }
}

/// 解決済みの署名からポートを借用する。`None` は基底 NOR の署名を表す。
pub(super) fn signature_port<'s, 'p, 'a>(
    signature: Option<&'s TypedRoutineSignature<'p, 'a>>, direction: PortDirection, index: usize,
) -> (port: Option<CallPortType<'s, 'p, 'a>>)
    ensures signature_port_matches(match signature {
        None => FuncCallSignature::Nor,
        Some(signature) => FuncCallSignature::Function(*signature),
    }, direction, index, port),
{
    let Some(signature) = signature else {
        let count = if matches!(direction, PortDirection::Input) { 2 } else { 1 };
        return if index < count {
            Some(CallPortType { ty: ResolvedPortType::Bits(1), annotation: None })
        } else { None };
    };
    let ports = match direction {
        PortDirection::Input => &signature.inputs,
        PortDirection::Output => &signature.outputs,
    };
    if index >= ports.len() {
        return None;
    }
    let selected = &ports[index];
    Some(CallPortType { ty: selected.ty, annotation: Some(&selected.annotation) })
}

/// 呼び出し元の式と、解決した参照先の型付き署名。
#[derive(Debug)]
pub struct TypedFuncCall<'p, 'a> {
    /// 呼び出し式の範囲、直接の引数数、名前解決で選んだ参照先。
    pub call: FuncCallArity<'p, 'a>,
    /// 参照先が宣言したポート型。
    pub signature: FuncCallSignature<'p, 'a>,
}

/// 組み合わせ回路の呼び出し先から型付き署名を得られなかった理由。
#[derive(Debug)]
pub enum FuncCallSignatureError<'p, 'a> {
    /// 呼び出し先の名前を解決できない。
    Reference(DefinitionReferenceError<'p, 'a>),
    /// 選ばれた関数の署名に違反がある。
    Signature {
        /// 診断を関連付ける呼び出し式と、その参照先の宣言。
        call: FuncCallArity<'p, 'a>,
        /// 署名の違反と、宣言側で該当する位置。
        error: TypedSignatureError<'p, 'a>,
    },
}

/// 再利用する署名の参照を、公開の呼び出し検査結果に対応づける。
pub(in crate::project::use_aliases) open spec fn cached_call_model<'p, 'a>(
    cache: &SignatureCache<'p, 'a>, call: FuncCallArity<'p, 'a>,
) -> TypedFuncCall<'p, 'a> {
    let signature = match call.target {
        FuncCallTarget::Nor => FuncCallSignature::Nor,
        FuncCallTarget::Function { file, entry, .. } =>
            FuncCallSignature::Function(cache.signatures()[(file, entry)]),
    };
    TypedFuncCall { call, signature }
}

/// 関数の署名が既に登録されているか、基底 NOR の呼び出しであることを表す。
pub(super) open spec fn cached_call_available(cache: &SignatureCache, call: FuncCallArity) -> bool {
    call.target matches FuncCallTarget::Function { file, entry, .. }
        ==> cache.signatures().contains_key((file, entry))
}

/// 登録済みの呼び出し先の署名を借用する。`None` は基底 NOR を表す。
pub(super) fn cached_signature<'s, 'p, 'a>(
    cache: &'s SignatureCache<'p, 'a>, call: &FuncCallArity<'p, 'a>,
) -> (signature: Option<&'s TypedRoutineSignature<'p, 'a>>)
    requires cached_call_available(cache, *call),
    ensures match signature {
        None => cached_call_model(cache, *call).signature is Nor,
        Some(signature) => cached_call_model(cache, *call).signature == FuncCallSignature::Function(*signature),
    },
{
    match &call.target {
        FuncCallTarget::Nor => None,
        FuncCallTarget::Function { file, entry, .. } => {
            let signature = cache.get(*file, *entry);
            assert(signature.is_some());
            signature
        },
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) proof fn call_has_signature_result(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        result: Result<Option<TypedFuncCall>, FuncCallSignatureError>,
    )
        requires
            self.func_call_at(file, entry, definition, reference),
            self.func_call_signature_evidence(file, entry, definition, reference, limit, result),
        ensures result != Ok(None),
    {
    }

    proof fn selected_function_arity(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        call: FuncCallArity, target_file: usize, target_entry: usize, arity: RoutineArity,
    )
        requires
            self.func_call_arity_evidence(file, entry, definition, reference, Ok(Some(call))),
            call.target matches FuncCallTarget::Function { arity: count, file: f, entry: e, .. }
                && count == arity && f == target_file && e == target_entry,
        ensures ({
            let project = self.targets.project_model();
            let source = project.sources_model()[target_file as int];
            let syntax = &project.circuits_model()[target_file as int].syntax;
            &&& target_file < project.circuits_model().len() && target_file < project.sources_model().len()
            &&& target_entry < syntax.entries@.len() && syntax.entries@[target_entry as int].head is Func
            &&& routine_arity_matches(source.text, syntax, target_entry as int, Some(arity))
        }),
    {
        let project = self.targets.project_model();
        let resolved = choose|resolved: ResolvedDefinitionReference|
            #[trigger] self.definition_resolution_evidence(file, entry, definition, reference, Ok(resolved))
                && target_ports_match(&project, resolved, call.target);
    }

    /// 出力型の注釈範囲が呼び出し先のソース内にあることを示す。
    pub(in crate::project::use_aliases) proof fn call_output_annotation_in_source(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        call: TypedFuncCall, output: int,
    )
        requires
            self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(call))),
            call.signature is Function,
            0 <= output < call.call.target.port_counts().outputs,
        ensures
            location_in_source(call.signature->Function_0.outputs@[output].annotation),
            self.declared_port_type(call.signature->Function_0.outputs@[output].ty),
    {
        if let FuncCallTarget::Function { file: target_file, entry: target_entry, .. } = call.call.target {
            self.typed_signature_sites(target_file, target_entry, limit, call.signature->Function_0);
            self.typed_signature_types_declared(target_file, target_entry, limit, call.signature->Function_0);
        }
    }

    /// 署名が同じ呼び出し先の宣言に対応し、入出力列の長さが個数の索引と一致することを表す。
    pub closed spec fn func_call_signature_evidence(
        &self, file: usize, entry: usize, definition: usize, reference: usize, max_width: u64,
        result: Result<Option<TypedFuncCall>, FuncCallSignatureError>,
    ) -> bool {
        match result {
            Ok(None) => self.func_call_arity_evidence(file, entry, definition, reference, Ok(None)),
            Err(FuncCallSignatureError::Reference(error)) =>
                self.func_call_arity_evidence(file, entry, definition, reference, Err(error)),
            Ok(Some(typed)) => self.func_call_arity_evidence(file, entry, definition, reference, Ok(Some(typed.call)))
                && match (typed.call.target, typed.signature) {
                    (FuncCallTarget::Nor, FuncCallSignature::Nor) => true,
                    (FuncCallTarget::Function { file, entry, arity, .. }, FuncCallSignature::Function(signature)) =>
                        signature.inputs@.len() == arity.inputs && signature.outputs@.len() == arity.outputs
                            && self.typed_signature_evidence(file, entry, max_width, Ok(Some(signature))),
                    _ => false,
                },
            Err(FuncCallSignatureError::Signature { call, error }) =>
                self.func_call_arity_evidence(file, entry, definition, reference, Ok(Some(call)))
                    && (call.target matches FuncCallTarget::Function { file, entry, .. }
                        && self.typed_signature_evidence(file, entry, max_width, Err(error))),
        }
    }

    pub(in crate::project::use_aliases) proof fn resolved_function_signature_evidence(
        &self, at: (usize, usize, usize, usize), limit: u64, call: TypedFuncCall,
    )
        requires
            self.func_call_signature_evidence(at.0, at.1, at.2, at.3, limit, Ok(Some(call))),
            call.call.target is Function,
        ensures
            call.signature matches FuncCallSignature::Function(signature)
                && self.typed_signature_evidence(call.call.target->Function_file, call.call.target->Function_entry,
                    limit, Ok(Some(signature))),
    {
    }

    /// 基底 NOR を解決できる参照では、成功した署名のどれからも同じ呼び出しを得る。
    pub(in crate::project::use_aliases) proof fn resolved_nor_call_agrees(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        builtin: TypedFuncCall, result: Option<TypedFuncCall>,
    )
        requires
            self.can_resolve(),
            self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(builtin))),
            self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(result)),
            builtin.call.target is Nor,
        ensures result matches Some(other) && other.call.call == builtin.call.call && other.call.target is Nor,
    {
        assert(self.func_call_at(file, entry, definition, reference));
        let other = result->Some_0;
        let project = self.targets.project_model();
        let parsed = project.circuits_model()[file as int];
        let forms = parsed.syntax.forms@;
        let row = parsed.definitions@[parsed.entry_ranges@[entry as int].definitions.start + definition];
        let indexed = parsed.references@[row.references.start + reference];
        let source = project.sources_model()[file as int];
        crate::syntax::circuit::indexed_call_shapes_agree(source.text, forms, row, indexed, builtin.call.call, other.call.call);
        if !(other.call.target is Nor) {
            let first = choose|resolved: ResolvedDefinitionReference|
                #[trigger] self.definition_resolution_evidence(file, entry, definition, reference, Ok(resolved))
                    && target_ports_match(&project, resolved, builtin.call.target);
            let second = choose|resolved: ResolvedDefinitionReference|
                #[trigger] self.definition_resolution_evidence(file, entry, definition, reference, Ok(resolved))
                    && target_ports_match(&project, resolved, other.call.target);
            self.nor_binding_excludes_declaration(file, entry, definition, reference, first, second);
        }
    }

    pub(in crate::project::use_aliases) proof fn resolved_signature_excludes_no_call(
        &self, at: (usize, usize, usize, usize), limit: u64, call: TypedFuncCall,
    )
        requires self.func_call_signature_evidence(at.0, at.1, at.2, at.3, limit, Ok(Some(call))),
        ensures !self.func_call_signature_evidence(at.0, at.1, at.2, at.3, limit, Ok(None)),
    {
        self.resolved_arity_excludes_no_call(at, call.call);
    }

    /// 同じ呼び出し位置で得た型付き署名は、宣言順の入出力型と注釈まで一致する。
    pub(in crate::project::use_aliases) proof fn successful_call_signatures_agree(
        &self, file: usize, entry: usize, definition: usize, reference: usize, limit: u64,
        left: TypedFuncCall, right: TypedFuncCall,
    )
        requires
            self.can_resolve(),
            self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(left))),
            self.func_call_signature_evidence(file, entry, definition, reference, limit, Ok(Some(right))),
        ensures
            left.call.call == right.call.call,
            left.call.target matches FuncCallTarget::Function { file, entry, .. } ==>
                (right.call.target matches FuncCallTarget::Function { file: other_file, entry: other_entry, .. }
                    && file == other_file && entry == other_entry),
            match (left.signature, right.signature) {
                (FuncCallSignature::Nor, FuncCallSignature::Nor) => true,
                (FuncCallSignature::Function(a), FuncCallSignature::Function(b)) =>
                    a.inputs@ == b.inputs@ && a.outputs@ == b.outputs@,
                _ => false,
            },
    {
        if left.call.target is Nor {
            self.resolved_nor_call_agrees(file, entry, definition, reference, limit, left, Some(right));
        } else if right.call.target is Nor {
            self.resolved_nor_call_agrees(file, entry, definition, reference, limit, right, Some(left));
        } else {
            let project = self.targets.project_model();
            let parsed = project.circuits_model()[file as int];
            let forms = parsed.syntax.forms@;
            let row = parsed.definitions@[parsed.entry_ranges@[entry as int].definitions.start + definition];
            let indexed = parsed.references@[row.references.start + reference];
            let source = project.sources_model()[file as int];
            crate::syntax::circuit::indexed_call_shapes_agree(source.text, forms, row, indexed, left.call.call, right.call.call);
            let a = choose|resolved: ResolvedDefinitionReference|
                #[trigger] self.definition_resolution_evidence(file, entry, definition, reference, Ok(resolved))
                    && target_ports_match(&project, resolved, left.call.target);
            let b = choose|resolved: ResolvedDefinitionReference|
                #[trigger] self.definition_resolution_evidence(file, entry, definition, reference, Ok(resolved))
                    && target_ports_match(&project, resolved, right.call.target);
            self.positioned_declarations_agree(file, entry, definition, reference, a, b);
            let left_file = left.call.target->Function_file;
            let left_entry = left.call.target->Function_entry;
            let right_file = right.call.target->Function_file;
            let right_entry = right.call.target->Function_entry;
            self.declaration_positions_agree(left_file, left_entry, right_file, right_entry);
            self.typed_routine_signatures_agree(left_file, left_entry, limit,
                left.signature->Function_0, right.signature->Function_0);
        }
    }

    /// 型付き署名の解決結果から、呼び出し元の構文木で引数をたどる根拠を取り出す。
    pub(in crate::project::use_aliases) proof fn typed_call_arguments_ready(
        &self, file: usize, entry: usize, definition: usize, reference: usize, max_width: u64, typed: TypedFuncCall,
    )
        requires
            self.can_resolve(),
            self.func_call_signature_evidence(file, entry, definition, reference, max_width, Ok(Some(typed))),
        ensures self.func_call_arity_evidence(file, entry, definition, reference, Ok(Some(typed.call))),
            self.func_call_at(file, entry, definition, reference), ({
            let project = self.targets.project_model();
            let parsed = project.circuits_model()[file as int];
            let forms = parsed.syntax.forms@;
            let def = parsed.entry_ranges@[entry as int].definitions.start + definition;
            let row = parsed.definitions@[def];
            let ref_pos = row.references.start + reference;
            &&& file < project.circuits_model().len()
            &&& entry < parsed.entry_ranges@.len() && entry < parsed.syntax.entries@.len()
            &&& definition < parsed.entry_ranges@[entry as int].definitions.end
                - parsed.entry_ranges@[entry as int].definitions.start
            &&& reference < row.references.end - row.references.start
            &&& *typed.call.source == project.sources_model()[file as int]
            &&& call_arguments_match(forms, typed.call.call)
            &&& call_shape_matches(typed.call.source.text, forms, row, parsed.references@[ref_pos], Some(typed.call.call))
            &&& complete_list_indices(forms) && nested_list_indices(forms)
            &&& match (typed.call.target, typed.signature) {
                (FuncCallTarget::Nor, FuncCallSignature::Nor) => true,
                (FuncCallTarget::Function { arity, .. }, FuncCallSignature::Function(signature)) =>
                    signature.inputs@.len() == arity.inputs && signature.outputs@.len() == arity.outputs,
                _ => false,
            }
        }),
    {
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        let parsed = project.circuits_model()[file as int];
        let source = project.sources_model()[file as int];
        parsed_index_evidence(source, parsed);
    }

    /// `func` の右辺にある呼び出しを解決し、参照先の入力型と出力型を取り出す。
    ///
    /// 添字は [`Self::resolve_func_call_arity`] と同じ。範囲外の添字、型名の参照、
    /// `func` 以外の項目には `None` を返す。
    /// 型名は呼び出し先の宣言を囲む名前空間で解決する。関数の署名には `max_width` を適用し、
    /// 基底 NOR の署名は言語で定めた 1 ビットの型を返す。
    ///
    /// # Errors
    ///
    /// 名前解決の違反を先に返す。参照先の署名に違反があれば、宣言側の診断と呼び出し位置を返す。
    pub fn resolve_func_call_signature(
        &self, file: usize, entry: usize, definition: usize, reference: usize, max_width: u64,
    ) -> (result: Result<Option<TypedFuncCall<'p, 'a>>, FuncCallSignatureError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_call_signature_evidence(file, entry, definition, reference, max_width, result),
    {
        let call = match self.resolve_func_call_arity(file, entry, definition, reference) {
            Ok(Some(call)) => call,
            Ok(None) => return Ok(None),
            Err(error) => return Err(FuncCallSignatureError::Reference(error)),
        };
        let signature = match &call.target {
            FuncCallTarget::Nor => FuncCallSignature::Nor,
            FuncCallTarget::Function { file: target_file, entry: target_entry, arity: _arity, .. } => {
                proof { self.selected_function_arity(file, entry, definition, reference, call,
                    *target_file, *target_entry, *_arity); }
                match self.resolve_routine_signature(*target_file, *target_entry, max_width) {
                    Ok(Some(signature)) => {
                        proof {
                            self.typed_signature_arity(*target_file, *target_entry, max_width, signature, *_arity);
                        }
                        FuncCallSignature::Function(signature)
                    },
                    Ok(None) => {
                        proof {
                            self.typed_signature_skips_non_routines(*target_file, *target_entry, max_width);
                            assert(false);
                        }
                        unreachable!()
                    },
                    Err(error) => return Err(FuncCallSignatureError::Signature { call, error }),
                }
            },
        };
        Ok(Some(TypedFuncCall { call, signature }))
    }

    /// 構文木の添字で `func` の呼び出しを選び、参照先の型付き署名を返す。
    ///
    /// `file`、`entry`、`definition` と `max_width` は
    /// [`Self::resolve_func_call_signature`] と同じ。`form` には、指定した定義の右辺にある
    /// 呼び出しリストの先頭の添字を渡す。右辺全体と子式のどちらの呼び出しも指定できる。
    /// 対象外の添字や専用フォームには `None` を返す。
    ///
    /// # Errors
    ///
    /// 名前解決の違反を先に返す。参照先の署名に違反があれば、宣言側の診断と呼び出し位置を返す。
    pub fn resolve_func_call_signature_at_form(
        &self, file: usize, entry: usize, definition: usize, form: usize, max_width: u64,
    ) -> (result: Result<Option<TypedFuncCall<'p, 'a>>, FuncCallSignatureError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            self.func_call_signature_at_form_evidence(file, entry, definition, form, max_width, result),
            result matches Ok(Some(call)) ==>
                call.call.call.form == form
                && (call.signature matches FuncCallSignature::Function(signature) ==>
                    signature.outputs@.len() == call.call.target.port_counts().outputs),
    {
        let (_, result) = self.resolve_func_call_signature_with_reference(file, entry, definition, form, max_width);
        result
    }

    /// 型付き署名を解決したときの定義内参照添字も返す。
    pub(super) fn resolve_func_call_signature_with_reference(
        &self, file: usize, entry: usize, definition: usize, form: usize, max_width: u64,
    ) -> (resolved: (Option<usize>, Result<Option<TypedFuncCall<'p, 'a>>, FuncCallSignatureError<'p, 'a>>))
        requires self.can_resolve(),
        ensures
            self.func_call_signature_at_form_evidence(file, entry, definition, form, max_width, resolved.1),
            resolved.0 matches Some(reference) ==> self.func_call_form_reference(file, entry, definition, form, reference)
                && self.func_call_signature_evidence(file, entry, definition, reference, max_width, resolved.1),
            resolved.1 matches Ok(Some(call)) ==> resolved.0.is_some() && call.call.call.form == form
                && (call.signature matches FuncCallSignature::Function(signature) ==>
                    signature.outputs@.len() == call.call.target.port_counts().outputs),
    {
        let Some(reference) = self.func_call_reference_at_form(file, entry, definition, form) else {
            return (None, Ok(None));
        };
        let result = self.resolve_func_call_signature(file, entry, definition, reference, max_width);
        proof {
            self.call_has_signature_result(file, entry, definition, reference, max_width, result);
            if let Ok(Some(call)) = &result {
                self.typed_call_arguments_ready(file, entry, definition, reference, max_width, *call);
            }
            assert(exists|r: usize| #[trigger] self.func_call_form_reference(file, entry, definition, form, r)
                && self.func_call_signature_evidence(file, entry, definition, r, max_width, result));
        }
        (Some(reference), result)
    }

    /// 構文木上で選んだ呼び出しと、同じ位置の参照から解決した署名または診断が対応することを表す。
    pub closed spec fn func_call_signature_at_form_evidence(
        &self, file: usize, entry: usize, definition: usize, form: usize, max_width: u64,
        result: Result<Option<TypedFuncCall>, FuncCallSignatureError>,
    ) -> bool {
        if result == Ok(None) {
            forall|r: usize| !#[trigger] self.func_call_form_reference(file, entry, definition, form, r)
        } else {
            exists|r: usize| #[trigger] self.func_call_form_reference(file, entry, definition, form, r)
                && self.func_call_signature_evidence(file, entry, definition, r, max_width, result)
        }
    }

    /// 成功した型付き署名が指す定義内の参照添字を取り出す。
    pub(super) proof fn call_signature_at_form_reference(
        &self, caller: (usize, usize, usize), form: usize, limit: u64, call: TypedFuncCall,
    ) -> (reference: usize)
        requires self.func_call_signature_at_form_evidence(caller.0, caller.1, caller.2, form, limit, Ok(Some(call))),
        ensures
            self.func_call_form_reference(caller.0, caller.1, caller.2, form, reference),
            self.func_call_signature_evidence(caller.0, caller.1, caller.2, reference, limit, Ok(Some(call))),
    {
        let (file, entry, definition) = caller;
        choose|r: usize| #[trigger] self.func_call_form_reference(file, entry, definition, form, r)
            && self.func_call_signature_evidence(file, entry, definition, r, limit, Ok(Some(call)))
    }

    /// 呼び出し先を解決し、関数の型付き署名を必要なときだけ登録する。
    ///
    /// # Errors
    ///
    /// 名前解決と署名検査は通常の呼び出し検査と同じ順に行い、診断には現在の呼び出し位置を使う。
    pub(in crate::project::use_aliases) fn prepare_func_call_signature(
        &self, file: usize, entry: usize, definition: usize, reference: usize, max_width: u64,
        cache: &mut SignatureCache<'p, 'a>,
    ) -> (result: Result<Option<FuncCallArity<'p, 'a>>, FuncCallSignatureError<'p, 'a>>)
        requires self.can_resolve(), old(cache).matches(self, max_width),
        ensures
            final(cache).matches(self, max_width),
            forall|place: (usize, usize)| #[trigger] old(cache).signatures().contains_key(place) ==>
                final(cache).signatures().contains_key(place)
                    && final(cache).signatures()[place] == old(cache).signatures()[place],
            match result {
                Ok(Some(call)) => {
                    &&& self.func_call_signature_evidence(file, entry, definition, reference, max_width,
                        Ok(Some(cached_call_model(final(cache), call))))
                    &&& call.target matches FuncCallTarget::Function { file, entry, .. }
                        ==> final(cache).signatures().contains_key((file, entry))
                },
                Ok(None) => self.func_call_signature_evidence(file, entry, definition, reference, max_width, Ok(None)),
                Err(error) => self.func_call_signature_evidence(file, entry, definition, reference, max_width, Err(error)),
            },
    {
        let call = match self.resolve_func_call_arity(file, entry, definition, reference) {
            Ok(Some(call)) => call,
            Ok(None) => return Ok(None),
            Err(error) => return Err(FuncCallSignatureError::Reference(error)),
        };
        if let FuncCallTarget::Function { file: target_file, entry: target_entry, arity: _arity, .. } = &call.target {
            proof { self.selected_function_arity(file, entry, definition, reference, call,
                *target_file, *target_entry, *_arity); }
            match cache.prepare(self, *target_file, *target_entry, max_width) {
                Ok(true) => {
                    proof {
                        let target = (*target_file, *target_entry);
                        let signature = cache.signatures()[target];
                        self.typed_signature_arity(*target_file, *target_entry, max_width, signature, *_arity);
                    }
                },
                Ok(false) => {
                    proof {
                        self.typed_signature_skips_non_routines(*target_file, *target_entry, max_width);
                        assert(false);
                    }
                    unreachable!()
                },
                Err(error) => return Err(FuncCallSignatureError::Signature { call, error }),
            }
        }
        Ok(Some(call))
    }
}

} // verus!
