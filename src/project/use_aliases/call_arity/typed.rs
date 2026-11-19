//! 呼び出し先の宣言を、その宣言が属するスコープで型解決する。

use super::{DefinitionReferenceError, FuncCallArity, FuncCallTarget, UseAliases};
#[cfg(verus_only)]
use super::{ResolvedDefinitionReference, target_ports_match};
use crate::project::{LocatedName, PortDirection, ResolvedPortType, TypedRoutineSignature, TypedSignatureError};
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::syntax::circuit::{Head, RoutineArity, call_arguments_match, routine_arity_matches};
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
        ensures match self {
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
        },
    {
        match self {
            Self::Nor => {
                let count = if matches!(direction, PortDirection::Input) { 2 } else { 1 };
                if index < count {
                    Some(CallPortType { ty: ResolvedPortType::Bits(1), annotation: None })
                } else {
                    None
                }
            },
            Self::Function(signature) => {
                let ports = match direction {
                    PortDirection::Input => &signature.inputs,
                    PortDirection::Output => &signature.outputs,
                };
                if index >= ports.len() {
                    return None;
                }
                let selected = &ports[index];
                Some(CallPortType { ty: selected.ty, annotation: Some(&selected.annotation) })
            },
        }
    }
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

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
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

    /// 型付き署名の解決結果から、呼び出し元の構文木で引数をたどる根拠を取り出す。
    pub(in crate::project::use_aliases) proof fn typed_call_arguments_ready(
        &self, file: usize, entry: usize, definition: usize, reference: usize, max_width: u64, typed: TypedFuncCall,
    )
        requires
            self.can_resolve(),
            self.func_call_signature_evidence(file, entry, definition, reference, max_width, Ok(Some(typed))),
        ensures ({
            let project = self.targets.project_model();
            let forms = project.circuits_model()[file as int].syntax.forms@;
            &&& file < project.circuits_model().len()
            &&& *typed.call.source == project.sources_model()[file as int]
            &&& call_arguments_match(forms, typed.call.call)
            &&& complete_list_indices(forms) && nested_list_indices(forms)
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
}

} // verus!
