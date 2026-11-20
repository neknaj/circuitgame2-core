//! ポートの型名を参照位置のスコープで解決し、共有配線の型を比較する。

use super::definitions::{ReferenceRequest, ReferenceUse};
use super::{DefinitionBinding, DefinitionReferenceReason, UseAliases};
#[cfg(verus_only)]
use crate::project::CheckedRoutineSignature;
use crate::project::circuits::read_indexed_atom;
#[cfg(verus_only)]
use crate::project::circuits::{parsed_circuit_matches, parsed_index_evidence};
use crate::project::declarations::key_of;
#[cfg(verus_only)]
use crate::project::declarations::{form_key, located_name_evidence};
#[cfg(verus_only)]
use crate::project::location_in_source;
#[cfg(verus_only)]
use crate::project::name_keys::key_view;
#[cfg(verus_only)]
use crate::project::signatures::{
    checked_routine_signatures_agree, checked_signature_ports, checked_signature_success_excludes_other,
    checked_signature_input_names_unique, routine_signature_evidence,
};
#[cfg(verus_only)]
use crate::project::widths::{checked_name_sites, checked_width_counts, checked_width_sites, reference_kind};
use crate::project::{
    CheckedPort, DeclaredPortType, LocatedName, OutputSource, PortDirection, ProjectSource,
    RoutineSignatureError, check_routine_signature,
};
use crate::syntax::Form;
use crate::syntax::circuit::{NamedForm, PortTypeSite};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    NameSite, RoutineArity, indexed_entry_evidence, named_forms_match, namespace_name_evidence, routine_arity_matches,
};
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::encode_utf8_decode_utf8;

verus! {

/// ポートの指定が解決した型。
#[derive(Clone, Copy, Debug)]
pub enum ResolvedPortType<'p, 'a> {
    /// 正のビット幅を持つビット列。
    Bits(u64),
    /// 共有宣言表にある構造体型。
    Struct {
        /// 構造体を宣言したファイルと文書バージョン。
        source: &'p ProjectSource<'a>,
        /// 構造体の宣言名と構文位置。
        form: &'p NamedForm<'a>,
    },
}

impl ResolvedPortType<'_, '_> {
    /// 同じ共有宣言表から得た二つの型を、ビット幅または構造体の同一性で比較する。
    pub fn is_same_type(&self, other: &ResolvedPortType) -> (same: bool)
        ensures same == port_types_equal(*self, *other),
    {
        match (*self, *other) {
            (Self::Bits(left), ResolvedPortType::Bits(right)) => left == right,
            (Self::Struct { form: left, .. }, ResolvedPortType::Struct { form: right, .. }) =>
                key_of(left).same_name(key_of(right)),
            _ => false,
        }
    }
}

/// ビット幅または完全修飾名で比較したポート型の同一性を表す。
pub open spec fn port_types_equal(left: ResolvedPortType, right: ResolvedPortType) -> bool {
    match (left, right) {
        (ResolvedPortType::Bits(left), ResolvedPortType::Bits(right)) => left == right,
        (ResolvedPortType::Struct { form: left, .. }, ResolvedPortType::Struct { form: right, .. }) =>
            key_view(form_key(*left)) == key_view(form_key(*right)),
        _ => false,
    }
}

/// 元のポート宣言と、解決した型。
#[derive(Debug)]
pub struct TypedPort<'p, 'a> {
    /// ポートの構文位置と宣言内容。
    pub declared: CheckedPort,
    /// 解決した型。
    pub ty: ResolvedPortType<'p, 'a>,
    /// 型名、幅の数字、または裸のポート名が元入力に現れた範囲。
    pub annotation: LocatedName<'p, 'a>,
}

/// ポート型を解決し、共有配線の型を照合した署名。
#[derive(Debug)]
pub struct TypedRoutineSignature<'p, 'a> {
    /// 宣言順の入力ポート。
    pub inputs: Vec<TypedPort<'p, 'a>>,
    /// 宣言順の出力ポート。
    pub outputs: Vec<TypedPort<'p, 'a>>,
    /// 出力ごとに対応する入力添字。本体で駆動元を調べる出力は `None`。
    pub output_inputs: Vec<Option<usize>>,
}

/// 署名またはポート型の検査で失敗した理由。
#[derive(Debug)]
pub enum TypedSignatureError<'p, 'a> {
    /// ポート幅、名前、または共有配線に関する署名診断。
    Signature(RoutineSignatureError<'p, 'a>),
    /// 参照した名前を構造体型として解決できない。
    TypeReference {
        /// 型名を指定したポートの方向。
        direction: PortDirection,
        /// 参照元の型名の範囲。
        reference: LocatedName<'p, 'a>,
        /// 名前解決に失敗した理由と、関連する宣言の位置。
        reason: DefinitionReferenceReason<'p, 'a>,
    },
    /// 同じ配線を使う入出力の型が一致しない。
    SharedTypeMismatch {
        /// 入力配線から得た型と、その宣言位置。
        input: TypedPort<'p, 'a>,
        /// 出力が要求する型と、その宣言位置。
        output: TypedPort<'p, 'a>,
    },
}

struct PortContext<'p, 'a> {
    file: usize,
    block: Option<usize>,
    namespace: Option<&'a str>,
    source: &'p ProjectSource<'a>,
    forms: &'p [Form],
}

spec fn same_port_context(left: &PortContext, right: &PortContext) -> bool {
    &&& left.file == right.file
    &&& left.block == right.block
    &&& left.namespace == right.namespace
    &&& left.source == right.source
    &&& left.forms@ == right.forms@
}

spec fn annotation_atom(port: CheckedPort) -> usize {
    match port.site.ty {
        PortTypeSite::ImplicitBit => port.site.name,
        PortTypeSite::Bits { width } => width,
        PortTypeSite::Named { form } => form,
    }
}

spec fn annotation_in_context(context: &PortContext, port: CheckedPort, annotation: LocatedName) -> bool {
    *annotation.source == *context.source && location_in_source(annotation)
        && annotation.span == form_span(context.forms@[annotation_atom(port) as int])
}

spec fn port_request(context: &PortContext, port: CheckedPort) -> bool {
    let at = annotation_atom(port);
    &&& at < context.forms@.len() && context.forms@[at as int] is Atom
    &&& port.ty is Named ==> reference_kind(context.forms@[at as int]->Atom_kind)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) open spec fn declared_port_type(&self, ty: ResolvedPortType) -> bool {
        match ty {
            ResolvedPortType::Bits(_) => true,
            ResolvedPortType::Struct { source, form } => form.head is Struct
                && self.targets.exports_model().declarations_model().declaration_at(form_key(*form), source, form),
        }
    }

    proof fn typed_ports_are_declared(&self, context: &PortContext, declared: Seq<CheckedPort>, types: Seq<TypedPort>)
        requires self.typed_ports_before(context, declared, types),
        ensures forall|i: int| 0 <= i < types.len() ==> self.declared_port_type((#[trigger] types[i]).ty),
    {
        assert forall|i: int| 0 <= i < types.len() implies self.declared_port_type((#[trigger] types[i]).ty) by {
            let port = declared[i];
            assert(self.typed_port_evidence(context, port, types[i]));
            if let ResolvedPortType::Struct { source, form } = types[i].ty {
                let atom = annotation_atom(port);
                let span = form_span(context.forms@[atom as int]);
                let kind = context.forms@[atom as int]->Atom_kind;
                let word = choose|word: &str| word.spec_bytes() == context.source.text.spec_bytes()[span.start as int..span.end as int]
                    && #[trigger] self.binding_evidence(context.file,
                        ReferenceRequest { block: context.block, word, role: ReferenceUse::StructType }, context.namespace, kind,
                        Ok(DefinitionBinding::Declaration { source, form }));
                let request = ReferenceRequest { block: context.block, word, role: ReferenceUse::StructType };
                self.binding_declaration_origin(context.file, request, context.namespace, kind, source, form);
            }
        };
    }

    /// 解決済みの署名に含まれる構造体型は、このプロジェクトの宣言表を指す。
    pub(super) proof fn typed_signature_types_declared(
        &self, file: usize, entry: usize, limit: u64, signature: TypedRoutineSignature,
    )
        requires self.typed_signature_evidence(file, entry, limit, Ok(Some(signature))),
        ensures
            forall|i: int| 0 <= i < signature.inputs@.len() ==> self.declared_port_type((#[trigger] signature.inputs@[i]).ty),
            forall|i: int| 0 <= i < signature.outputs@.len() ==> self.declared_port_type((#[trigger] signature.outputs@[i]).ty),
    {
        let project = self.targets.project_model();
        let (context, declared) = choose|context: PortContext, declared: CheckedRoutineSignature|
            #[trigger] self.port_context_evidence(file, entry, &context)
                && #[trigger] routine_signature_evidence(&project, file as int, entry as int, limit, Ok(Some(declared)))
                && self.typed_after_signature(&context, &declared, Ok(Some(signature)));
        self.typed_ports_are_declared(&context, declared.ports.inputs@, signature.inputs@);
        self.typed_ports_are_declared(&context, declared.ports.outputs@, signature.outputs@);
    }

    spec fn port_binding_evidence(
        &self, context: &PortContext, port: CheckedPort,
        binding: Result<DefinitionBinding, DefinitionReferenceReason>,
    ) -> bool {
        let at = annotation_atom(port);
        let span = form_span(context.forms@[at as int]);
        exists|word: &str| word.spec_bytes() == context.source.text.spec_bytes()[span.start as int..span.end as int]
            && #[trigger] self.binding_evidence(context.file,
                ReferenceRequest { block: context.block, word, role: ReferenceUse::StructType },
                context.namespace, context.forms@[at as int]->Atom_kind, binding)
    }

    spec fn typed_port_evidence(&self, context: &PortContext, port: CheckedPort, typed: TypedPort) -> bool {
        &&& typed.declared == port
        &&& annotation_in_context(context, port, typed.annotation)
        &&& match (port.ty, typed.ty) {
            (DeclaredPortType::Bits(value), ResolvedPortType::Bits(found)) => value == found,
            (DeclaredPortType::Named { .. }, ResolvedPortType::Struct { source, form }) =>
                form.head is Struct && self.port_binding_evidence(context, port,
                    Ok(DefinitionBinding::Declaration { source, form })),
            _ => false,
        }
    }

    spec fn type_error_evidence(
        &self, context: &PortContext, port: CheckedPort, direction: PortDirection, error: TypedSignatureError,
    ) -> bool {
        error matches TypedSignatureError::TypeReference { direction: reported, reference, reason }
            && port.ty is Named && reported == direction && annotation_in_context(context, port, reference)
            && self.port_binding_evidence(context, port, Err(reason))
    }

    fn resolve_port_type(
        &self, context: &PortContext<'p, 'a>, port: CheckedPort, direction: PortDirection,
    ) -> (result: Result<TypedPort<'p, 'a>, TypedSignatureError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.scope_matches(context.file, context.block, Ok(context.namespace)),
            port_request(context, port),
            form_spans_valid(context.source.text, context.forms@, context.source.text.spec_bytes().len() as int),
        ensures match result {
            Ok(typed) => self.typed_port_evidence(context, port, typed),
            Err(error) => self.type_error_evidence(context, port, direction, error),
        },
    {
        let form = match port.site.ty {
            PortTypeSite::ImplicitBit => port.site.name,
            PortTypeSite::Bits { width } => width,
            PortTypeSite::Named { form } => form,
        };
        let (word, span) = read_indexed_atom(context.source.text, context.forms, form);
        let annotation = LocatedName { source: context.source, span };
        proof { located_name_evidence(annotation); }
        let ty = match port.ty {
            DeclaredPortType::Bits(width) => ResolvedPortType::Bits(width),
            DeclaredPortType::Named { .. } => {
                let Form::Atom { kind: atom_kind, .. } = &context.forms[form] else {
                    proof { assert(false); }
                    unreachable!();
                };
                let request = ReferenceRequest { block: context.block, word, role: ReferenceUse::StructType };
                match self.resolve_scoped_binding(context.file, &request, context.namespace, *atom_kind) {
                    Ok(binding) => {
                        proof { self.struct_binding_is_struct(context.file, request, context.namespace, *atom_kind, binding); }
                        let DefinitionBinding::Declaration { source: declaration_source, form: declaration } = binding else {
                            proof { assert(false); }
                            unreachable!();
                        };
                        ResolvedPortType::Struct { source: declaration_source, form: declaration }
                    },
                    Err(reason) => return Err(TypedSignatureError::TypeReference {
                        direction, reference: annotation, reason,
                    }),
                }
            },
        };
        Ok(TypedPort { declared: port, ty, annotation })
    }

    spec fn typed_ports_before(&self, context: &PortContext, ports: Seq<CheckedPort>, typed: Seq<TypedPort>) -> bool {
        &&& typed.len() <= ports.len()
        &&& forall|i: int| 0 <= i < typed.len() ==>
            self.typed_port_evidence(context, ports[i], #[trigger] typed[i])
    }

    spec fn first_port_type_error(
        &self, context: &PortContext, ports: Seq<CheckedPort>, direction: PortDirection, error: TypedSignatureError,
    ) -> bool {
        exists|i: int, earlier: Seq<TypedPort>| 0 <= i < ports.len() && earlier.len() == i
            && #[trigger] self.type_error_evidence(context, ports[i], direction, error)
            && #[trigger] self.typed_ports_before(context, ports, earlier)
    }

    fn resolve_port_types(
        &self, context: &PortContext<'p, 'a>, ports: &[CheckedPort], direction: PortDirection,
    ) -> (result: Result<Vec<TypedPort<'p, 'a>>, TypedSignatureError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.scope_matches(context.file, context.block, Ok(context.namespace)),
            checked_name_sites(context.forms@, ports@),
            form_spans_valid(context.source.text, context.forms@, context.source.text.spec_bytes().len() as int),
        ensures match result {
            Ok(typed) => typed@.len() == ports@.len() && self.typed_ports_before(context, ports@, typed@),
            Err(error) => self.first_port_type_error(context, ports@, direction, error),
        },
    {
        let mut typed: Vec<TypedPort> = Vec::new();
        let mut at = 0;
        while at < ports.len()
            invariant
                self.can_resolve(),
                self.scope_matches(context.file, context.block, Ok(context.namespace)),
                checked_name_sites(context.forms@, ports@),
                form_spans_valid(context.source.text, context.forms@, context.source.text.spec_bytes().len() as int),
                at == typed@.len() <= ports@.len(),
                self.typed_ports_before(context, ports@, typed@),
            decreases ports@.len() - at,
        {
            let item = match self.resolve_port_type(context, ports[at], direction) {
                Ok(item) => item,
                Err(error) => {
                    assert(self.first_port_type_error(context, ports@, direction, error));
                    return Err(error);
                },
            };
            typed.push(item);
            at += 1;
        }
        Ok(typed)
    }

    spec fn port_context_evidence(&self, file: usize, entry: usize, context: &PortContext) -> bool {
        let project = self.targets.project_model();
        &&& file == context.file && file < project.circuits_model().len()
        &&& file < project.sources_model().len()
        &&& *context.source == project.sources_model()[file as int]
        &&& {
            let parsed = &project.circuits_model()[file as int];
            &&& context.forms@ == parsed.syntax.forms@
            &&& entry < parsed.syntax.entries@.len()
            &&& context.block == parsed.syntax.entries@[entry as int].namespace
            &&& self.scope_matches(file, context.block, Ok(context.namespace))
        }
    }

    /// 型解決と共有配線の診断が、指定した署名の名前解決と型の同一性に対応することを表す。
    pub closed spec fn typed_signature_evidence(
        &self, file: usize, entry: usize, max_width: u64,
        result: Result<Option<TypedRoutineSignature>, TypedSignatureError>,
    ) -> bool {
        let project = &self.targets.project_model();
        match result {
            Ok(None) => routine_signature_evidence(project, file as int, entry as int, max_width, Ok(None)),
            Err(TypedSignatureError::Signature(error)) =>
                routine_signature_evidence(project, file as int, entry as int, max_width, Err(error)),
            _ => exists|context: PortContext, signature: CheckedRoutineSignature|
                #[trigger] self.port_context_evidence(file, entry, &context)
                    && #[trigger] routine_signature_evidence(project, file as int, entry as int, max_width, Ok(Some(signature)))
                    && self.typed_after_signature(&context, &signature, result),
        }
    }

    pub(super) proof fn typed_signature_input_names_unique(
        &self, file: usize, entry: usize, limit: u64, typed: TypedRoutineSignature, names: Seq<NameSite>,
    )
        requires
            self.typed_signature_evidence(file, entry, limit, Ok(Some(typed))),
            names.len() == typed.inputs@.len(),
            super::function_drivers::names_match_ports(self.targets.project_model().sources_model()[file as int].text,
                self.targets.project_model().circuits_model()[file as int].syntax.forms@, typed.inputs@, names),
        ensures forall|i: int, j: int| 0 <= i < j < names.len() ==>
            (#[trigger] names[i]).word.spec_bytes() != (#[trigger] names[j]).word.spec_bytes(),
    {
        let project = &self.targets.project_model();
        let (context, signature) = choose|context: PortContext, signature: CheckedRoutineSignature|
            #[trigger] self.port_context_evidence(file, entry, &context)
            && #[trigger] routine_signature_evidence(project, file as int, entry as int, limit, Ok(Some(signature)))
            && self.typed_after_signature(&context, &signature, Ok(Some(typed)));
        reveal(UseAliases::typed_ports_before);
        let forms = project.circuits_model()[file as int].syntax.forms@;
        let source = &project.sources_model()[file as int];
        assert forall|i: int| 0 <= i < names.len() implies {
            let name = #[trigger] names[i];
            name.span == form_span(forms[signature.ports.inputs@[i].site.name as int])
                && crate::project::circuits::name_in_source(source.text, name)
        } by {
            assert(typed.inputs@[i].declared == signature.ports.inputs@[i]);
        };

        checked_signature_input_names_unique(project, file as int, entry as int, limit, signature, names);
    }

    proof fn port_contexts_agree(&self, file: usize, entry: usize, left: &PortContext, right: &PortContext)
        requires
            self.can_resolve(),
            self.port_context_evidence(file, entry, left),
            self.port_context_evidence(file, entry, right),
        ensures same_port_context(left, right),
    {
        if let Some(block) = left.block {
            let project = self.targets.project_model();
            let source = project.sources_model()[file as int];
            let parsed = project.circuits_model()[file as int];
            let names = parsed.names@;
            let left_path = left.namespace->Some_0;
            let right_path = right.namespace->Some_0;
            let a = choose|i: int| 0 <= i < names.len() && #[trigger] super::is_namespace_block(names[i], block)
                && names[i].name.word == left_path;
            let b = choose|i: int| 0 <= i < names.len() && #[trigger] super::is_namespace_block(names[i], block)
                && names[i].name.word == right_path;
            self.targets.parsed_project_model();
            parsed_index_evidence(source, parsed);
            reveal(named_forms_match);
            assert(a == b);
        }
    }

    proof fn typed_ports_agree(
        &self, left_context: &PortContext, right_context: &PortContext, ports: Seq<CheckedPort>,
        left: Seq<TypedPort>, right: Seq<TypedPort>,
    )
        requires
            self.can_resolve(),
            same_port_context(left_context, right_context),
            left.len() == right.len(),
            self.typed_ports_before(left_context, ports, left),
            self.typed_ports_before(right_context, ports, right),
        ensures left == right,
    {
        assert forall|i: int| 0 <= i < left.len() implies (#[trigger] left[i]) == (#[trigger] right[i]) by {
            let port = ports[i];
            assert(self.typed_port_evidence(left_context, port, left[i]));
            assert(self.typed_port_evidence(right_context, port, right[i]));
            if port.ty is Named {
                let at = annotation_atom(port);
                let span = form_span(left_context.forms@[at as int]);
                let bytes = left_context.source.text.spec_bytes()[span.start as int..span.end as int];
                let kind = left_context.forms@[at as int]->Atom_kind;
                let a = DefinitionBinding::Declaration { source: left[i].ty->Struct_source, form: left[i].ty->Struct_form };
                let b = DefinitionBinding::Declaration { source: right[i].ty->Struct_source, form: right[i].ty->Struct_form };
                let left_word = choose|word: &str| word.spec_bytes() == bytes
                    && #[trigger] self.binding_evidence(left_context.file,
                        ReferenceRequest { block: left_context.block, word, role: ReferenceUse::StructType },
                        left_context.namespace, kind, Ok(a));
                let right_word = choose|word: &str| word.spec_bytes() == bytes
                    && #[trigger] self.binding_evidence(right_context.file,
                        ReferenceRequest { block: right_context.block, word, role: ReferenceUse::StructType },
                        right_context.namespace, kind, Ok(b));
                encode_utf8_decode_utf8(left_word@);
                encode_utf8_decode_utf8(right_word@);
                assert(left_word@ == right_word@);
                self.declaration_bindings_agree(left_context.file,
                    ReferenceRequest { block: left_context.block, word: left_word, role: ReferenceUse::StructType },
                    ReferenceRequest { block: right_context.block, word: right_word, role: ReferenceUse::StructType },
                    left_context.namespace, right_context.namespace, kind, a->Declaration_source, a->Declaration_form,
                    b->Declaration_source, b->Declaration_form);
            }
        };
        assert(left =~= right);
    }

    /// 同じ解決環境と幅上限で署名の解決に成功した結果は、型、注釈範囲、共有配線まで一致する。
    pub(super) proof fn typed_routine_signatures_agree(
        &self, file: usize, entry: usize, max_width: u64, left: TypedRoutineSignature, right: TypedRoutineSignature,
    )
        requires
            self.can_resolve(),
            self.typed_signature_evidence(file, entry, max_width, Ok(Some(left))),
            self.typed_signature_evidence(file, entry, max_width, Ok(Some(right))),
        ensures
            left.inputs@ == right.inputs@,
            left.outputs@ == right.outputs@,
            left.output_inputs@ == right.output_inputs@,
    {
        let project = &self.targets.project_model();
        let (a_context, a_signature) = choose|context: PortContext, signature: CheckedRoutineSignature|
            #[trigger] self.port_context_evidence(file, entry, &context)
            && #[trigger] routine_signature_evidence(project, file as int, entry as int, max_width, Ok(Some(signature)))
            && self.typed_after_signature(&context, &signature, Ok(Some(left)));
        let (b_context, b_signature) = choose|context: PortContext, signature: CheckedRoutineSignature|
            #[trigger] self.port_context_evidence(file, entry, &context)
            && #[trigger] routine_signature_evidence(project, file as int, entry as int, max_width, Ok(Some(signature)))
            && self.typed_after_signature(&context, &signature, Ok(Some(right)));
        self.port_contexts_agree(file, entry, &a_context, &b_context);
        checked_routine_signatures_agree(project, file as int, entry as int, max_width, a_signature, b_signature);
        let ports = a_signature.ports;
        assert(self.typed_ports_before(&a_context, ports.inputs@, left.inputs@));
        assert(self.typed_ports_before(&b_context, ports.inputs@, right.inputs@));
        self.typed_ports_agree(&a_context, &b_context, ports.inputs@, left.inputs@, right.inputs@);
        assert(self.typed_ports_before(&a_context, ports.outputs@, left.outputs@));
        assert(self.typed_ports_before(&b_context, ports.outputs@, right.outputs@));
        self.typed_ports_agree(&a_context, &b_context, ports.outputs@, left.outputs@, right.outputs@);
        let a_connections = left.output_inputs@;
        let b_connections = right.output_inputs@;
        let sources = a_signature.output_sources@;
        assert(shared_types_before(sources, left.inputs@, left.outputs@, a_connections));
        assert(shared_types_before(sources, right.inputs@, right.outputs@, b_connections));
        assert forall|i: int| 0 <= i < a_connections.len() implies
            (#[trigger] a_connections[i]) == (#[trigger] b_connections[i]) by {
            match sources[i] {
                OutputSource::Body => assert(a_connections[i].is_none() && b_connections[i].is_none()),
                OutputSource::Input { port, .. } =>
                    assert(a_connections[i] == Some(port) && b_connections[i] == Some(port)),
            }
        };
        assert(a_connections =~= b_connections);
    }

    proof fn typed_port_excludes_error(
        &self, success_context: &PortContext, error_context: &PortContext, port: CheckedPort,
        success: TypedPort, direction: PortDirection, error: TypedSignatureError,
    )
        requires
            self.can_resolve(),
            same_port_context(success_context, error_context),
            self.typed_port_evidence(success_context, port, success),
        ensures !self.type_error_evidence(error_context, port, direction, error),
    {
        if self.type_error_evidence(error_context, port, direction, error) {
            let at = annotation_atom(port);
            let span = form_span(success_context.forms@[at as int]);
            let bytes = success_context.source.text.spec_bytes()[span.start as int..span.end as int];
            let kind = success_context.forms@[at as int]->Atom_kind;
            let source = success.ty->Struct_source;
            let form = success.ty->Struct_form;
            let reason = error->TypeReference_reason;
            let success_word = choose|word: &str| word.spec_bytes() == bytes
                && #[trigger] self.binding_evidence(success_context.file,
                    ReferenceRequest { block: success_context.block, word, role: ReferenceUse::StructType },
                    success_context.namespace, kind, Ok(DefinitionBinding::Declaration { source, form }));
            let error_word = choose|word: &str| word.spec_bytes() == bytes
                && #[trigger] self.binding_evidence(error_context.file,
                    ReferenceRequest { block: error_context.block, word, role: ReferenceUse::StructType },
                    error_context.namespace, kind, Err(reason));
            encode_utf8_decode_utf8(success_word@);
            encode_utf8_decode_utf8(error_word@);
            assert(success_word@ == error_word@);
            self.struct_binding_excludes_error(success_context.file,
                ReferenceRequest { block: success_context.block, word: success_word, role: ReferenceUse::StructType },
                ReferenceRequest { block: error_context.block, word: error_word, role: ReferenceUse::StructType },
                success_context.namespace, error_context.namespace, kind, source, form, reason);
        }
    }

    proof fn typed_ports_exclude_first_error(
        &self, success_context: &PortContext, error_context: &PortContext, ports: Seq<CheckedPort>,
        success: Seq<TypedPort>, direction: PortDirection, error: TypedSignatureError,
    )
        requires
            self.can_resolve(),
            same_port_context(success_context, error_context),
            success.len() == ports.len(),
            self.typed_ports_before(success_context, ports, success),
        ensures !self.first_port_type_error(error_context, ports, direction, error),
    {
        if self.first_port_type_error(error_context, ports, direction, error) {
            let (i, _) = choose|i: int, earlier: Seq<TypedPort>| 0 <= i < ports.len() && earlier.len() == i
                && #[trigger] self.type_error_evidence(error_context, ports[i], direction, error)
                && #[trigger] self.typed_ports_before(error_context, ports, earlier);
            self.typed_port_excludes_error(
                success_context, error_context, ports[i], success[i], direction, error,
            );
        }
    }

    /// 署名の型解決に成功すれば、対象外の結果と、署名・参照・共有配線の診断は成立しない。
    pub(super) proof fn typed_signature_success_excludes_other(
        &self, file: usize, entry: usize, max_width: u64, success: TypedRoutineSignature,
        other: Result<Option<TypedRoutineSignature>, TypedSignatureError>,
    )
        requires
            self.can_resolve(),
            self.typed_signature_evidence(file, entry, max_width, Ok(Some(success))),
            self.typed_signature_evidence(file, entry, max_width, other),
        ensures other is Ok && other->Ok_0 is Some,
    {
        let project = &self.targets.project_model();
        let (a_context, a_signature) = choose|context: PortContext, signature: CheckedRoutineSignature|
            #[trigger] self.port_context_evidence(file, entry, &context)
            && #[trigger] routine_signature_evidence(project, file as int, entry as int, max_width, Ok(Some(signature)))
            && self.typed_after_signature(&context, &signature, Ok(Some(success)));
        match other {
            Ok(None) => checked_signature_success_excludes_other(
                project, file as int, entry as int, max_width, a_signature, Ok(None),
            ),
            Err(TypedSignatureError::Signature(error)) => checked_signature_success_excludes_other(
                project, file as int, entry as int, max_width, a_signature, Err(error),
            ),
            Err(error) => {
                let (b_context, b_signature) = choose|context: PortContext, signature: CheckedRoutineSignature|
                    #[trigger] self.port_context_evidence(file, entry, &context)
                    && #[trigger] routine_signature_evidence(project, file as int, entry as int, max_width, Ok(Some(signature)))
                    && self.typed_after_signature(&context, &signature, other);
                self.port_contexts_agree(file, entry, &a_context, &b_context);
                checked_routine_signatures_agree(project, file as int, entry as int, max_width, a_signature, b_signature);
                let ports = a_signature.ports;
                let sources = a_signature.output_sources@;
                assert(self.typed_ports_before(&a_context, ports.inputs@, success.inputs@));
                assert(self.typed_ports_before(&a_context, ports.outputs@, success.outputs@));
                if error is TypeReference {
                    self.typed_ports_exclude_first_error(&a_context, &b_context, ports.inputs@,
                        success.inputs@, PortDirection::Input, error);
                    self.typed_ports_exclude_first_error(&a_context, &b_context, ports.outputs@,
                        success.outputs@, PortDirection::Output, error);
                } else {
                    let (inputs, outputs) = choose|inputs: Seq<TypedPort>, outputs: Seq<TypedPort>|
                        inputs.len() == ports.inputs@.len() && outputs.len() == ports.outputs@.len()
                        && #[trigger] self.typed_ports_before(&b_context, ports.inputs@, inputs)
                        && #[trigger] self.typed_ports_before(&b_context, ports.outputs@, outputs)
                        && first_shared_type_mismatch(sources, inputs, outputs, error);
                    self.typed_ports_agree(&a_context, &b_context, ports.inputs@, success.inputs@, inputs);
                    self.typed_ports_agree(&a_context, &b_context, ports.outputs@, success.outputs@, outputs);
                    shared_connections_exclude_type_error(sources, inputs, outputs, success.output_inputs@, error);
                }
            },
            _ => {},
        }
    }

    pub(super) proof fn typed_signature_sites(
        &self, file: usize, entry: usize, max_width: u64, typed: TypedRoutineSignature,
    )
        requires self.typed_signature_evidence(file, entry, max_width, Ok(Some(typed))),
        ensures ({
            let project = self.targets.project_model();
            let forms = project.circuits_model()[file as int].syntax.forms@;
            &&& typed.output_inputs@.len() == typed.outputs@.len()
            &&& forall|i: int| 0 <= i < typed.output_inputs@.len()
                ==> ((#[trigger] typed.output_inputs@[i]) matches Some(input) ==> input < typed.inputs@.len())
            &&& typed_name_sites(forms, typed.inputs@) && typed_name_sites(forms, typed.outputs@)
            &&& forall|i: int| 0 <= i < typed.outputs@.len() ==> {
                let port = #[trigger] typed.outputs@[i];
                *port.annotation.source == project.sources_model()[file as int]
                    && location_in_source(port.annotation)
            }
            &&& forall|i: int| 0 <= i < typed.inputs@.len() ==> {
                let port = #[trigger] typed.inputs@[i];
                *port.annotation.source == project.sources_model()[file as int]
                    && location_in_source(port.annotation)
            }
        }),
    {
        let project = &self.targets.project_model();
        let (context, signature) = choose|context: PortContext, signature: CheckedRoutineSignature|
            #[trigger] self.port_context_evidence(file, entry, &context)
            && #[trigger] routine_signature_evidence(project, file as int, entry as int, max_width, Ok(Some(signature)))
            && self.typed_after_signature(&context, &signature, Ok(Some(typed)));
        checked_signature_ports(project, file as int, entry as int, max_width, signature);
        checked_width_sites(project, file as int, entry as int, max_width, signature.ports);
        self.typed_names_follow_declared(&context, signature.ports.inputs@, typed.inputs@);
        self.typed_names_follow_declared(&context, signature.ports.outputs@, typed.outputs@);
        assert forall|i: int| 0 <= i < typed.outputs@.len() implies {
            let port = #[trigger] typed.outputs@[i];
            *port.annotation.source == project.sources_model()[file as int] && location_in_source(port.annotation)
        } by {
            assert(self.typed_port_evidence(&context, signature.ports.outputs@[i], typed.outputs@[i]));
        };
        assert forall|i: int| 0 <= i < typed.inputs@.len() implies {
            let port = #[trigger] typed.inputs@[i];
            *port.annotation.source == project.sources_model()[file as int] && location_in_source(port.annotation)
        } by {
            assert(self.typed_port_evidence(&context, signature.ports.inputs@[i], typed.inputs@[i]));
        };
    }

    pub(super) proof fn typed_signature_arity(
        &self, file: usize, entry: usize, max_width: u64, typed: TypedRoutineSignature, arity: RoutineArity,
    )
        requires
            self.typed_signature_evidence(file, entry, max_width, Ok(Some(typed))),
            ({
                let project = self.targets.project_model();
                &&& file < project.circuits_model().len() && file < project.sources_model().len()
                &&& routine_arity_matches(project.sources_model()[file as int].text,
                    &project.circuits_model()[file as int].syntax, entry as int, Some(arity))
            }),
        ensures typed.inputs@.len() == arity.inputs, typed.outputs@.len() == arity.outputs,
    {
        let project = &self.targets.project_model();
        let (context, signature) = choose|context: PortContext, signature: CheckedRoutineSignature|
            #[trigger] self.port_context_evidence(file, entry, &context)
                && #[trigger] routine_signature_evidence(project, file as int, entry as int, max_width, Ok(Some(signature)))
                && self.typed_after_signature(&context, &signature, Ok(Some(typed)));
        checked_signature_ports(project, file as int, entry as int, max_width, signature);
        checked_width_counts(project, file as int, entry as int, max_width, signature.ports, arity);
    }

    pub(super) proof fn typed_signature_skips_non_routines(&self, file: usize, entry: usize, max_width: u64)
        requires self.typed_signature_evidence(file, entry, max_width, Ok(None)),
        ensures ({
            let circuits = self.targets.project_model().circuits_model();
            file < circuits.len() && entry < circuits[file as int].syntax.entries@.len()
                ==> !(circuits[file as int].syntax.entries@[entry as int].head is Func)
                    && !(circuits[file as int].syntax.entries@[entry as int].head is Module)
        }),
    {
        crate::project::signatures::signature_check_skips_non_routines(
            &self.targets.project_model(), file as int, entry as int, max_width);
    }

    proof fn typed_names_follow_declared(&self, context: &PortContext, ports: Seq<CheckedPort>, typed: Seq<TypedPort>)
        requires
            checked_name_sites(context.forms@, ports),
            self.typed_ports_before(context, ports, typed),
        ensures typed_name_sites(context.forms@, typed),
    {
        assert forall|i: int| 0 <= i < typed.len() implies {
            let name = (#[trigger] typed[i]).declared.site.name;
            name < context.forms@.len() && context.forms@[name as int] is Atom
        } by {
            assert(typed[i].declared == ports[i]);
        };
    }

    spec fn typed_after_signature(
        &self, context: &PortContext, signature: &CheckedRoutineSignature,
        result: Result<Option<TypedRoutineSignature>, TypedSignatureError>,
    ) -> bool {
        match result {
            Err(error) if error is TypeReference =>
                self.first_port_type_error(context, signature.ports.inputs@, PortDirection::Input, error)
                || (exists|inputs: Seq<TypedPort>| inputs.len() == signature.ports.inputs@.len()
                    && #[trigger] self.typed_ports_before(context, signature.ports.inputs@, inputs)
                    && self.first_port_type_error(context, signature.ports.outputs@, PortDirection::Output, error)),
            _ => exists|inputs: Seq<TypedPort>, outputs: Seq<TypedPort>|
                inputs.len() == signature.ports.inputs@.len() && outputs.len() == signature.ports.outputs@.len()
                && #[trigger] self.typed_ports_before(context, signature.ports.inputs@, inputs)
                && #[trigger] self.typed_ports_before(context, signature.ports.outputs@, outputs)
                && match result {
                    Ok(Some(typed)) => typed.inputs@ == inputs && typed.outputs@ == outputs
                        && typed.output_inputs@.len() == outputs.len()
                        && shared_types_before(signature.output_sources@, inputs, outputs, typed.output_inputs@),
                    Err(error) => first_shared_type_mismatch(signature.output_sources@, inputs, outputs, error),
                    _ => false,
                },
        }
    }

    /// 指定した回路フォームの署名を検査し、ポートの型名を解決する。
    ///
    /// ファイルと名前空間ブロックは、この索引のプロジェクトにある署名から決める。
    /// ファイルや索引項目が存在しない場合や、対象が `func` と `module` 以外の場合は `Ok(None)`。
    /// 構造体は宣言の同一性で照合する。構造体のレイアウトと本体の結線は後続の検査で扱う。
    ///
    /// # Errors
    ///
    /// 署名、入力型名、出力型名、共有配線の順で最初の違反を返す。
    pub fn resolve_routine_signature(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<Option<TypedRoutineSignature<'p, 'a>>, TypedSignatureError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.typed_signature_evidence(file, entry, max_width, result),
    {
        let project = self.targets.project();
        let signature = match check_routine_signature(project, file, entry, max_width) {
            Ok(Some(signature)) => signature,
            Ok(None) => return Ok(None),
            Err(error) => return Err(TypedSignatureError::Signature(error)),
        };
        proof {
            checked_signature_ports(project, file as int, entry as int, max_width, signature);
            checked_width_sites(project, file as int, entry as int, max_width, signature.ports);
        }
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let owner = &parsed.syntax.entries[entry];
        proof {
            assert(parsed_circuit_matches(*source, *parsed));
            parsed_index_evidence(*source, *parsed);
            indexed_entry_evidence(source.text, parsed.syntax.forms@, parsed.syntax.entries@, entry as int);
            if let Some(parent) = owner.namespace {
                namespace_name_evidence(source.text, parsed.syntax.forms@, parsed.syntax.entries@,
                    parsed.names@, owner.form as int, parent);
                let i = choose|i: int| 0 <= i < parsed.names@.len() && (#[trigger] parsed.names@[i]).form == parent
                    && parsed.names@[i].head is Namespace && parsed.names@[i].block is None;
                assert(super::is_namespace_block(parsed.names@[i], parent));
            }
        }
        let Ok(namespace) = self.scope_namespace(file, owner.namespace) else {
            proof { assert(false); }
            unreachable!();
        };
        let context = PortContext { file, block: owner.namespace, namespace, source, forms: parsed.syntax.forms.as_slice() };
        assert(self.port_context_evidence(file, entry, &context));
        let inputs = self.resolve_port_types(&context, signature.ports.inputs.as_slice(), PortDirection::Input)?;
        let outputs = self.resolve_port_types(&context, signature.ports.outputs.as_slice(), PortDirection::Output)?;
        let ghost input_model = inputs@;
        let ghost output_model = outputs@;
        let result = match check_shared_types(signature.output_sources.as_slice(), inputs.as_slice(), outputs.as_slice()) {
            Ok(output_inputs) => Ok(Some(TypedRoutineSignature { inputs, outputs, output_inputs })),
            Err(error) => Err(error),
        };
        assert(self.typed_after_signature(&context, &signature, result)) by {
            assert(self.typed_ports_before(&context, signature.ports.inputs@, input_model));
            assert(self.typed_ports_before(&context, signature.ports.outputs@, output_model));
        };
        result
    }
}

pub(super) open spec fn typed_name_sites(forms: Seq<Form>, typed: Seq<TypedPort>) -> bool {
    forall|i: int| 0 <= i < typed.len() ==> {
        let name = (#[trigger] typed[i]).declared.site.name;
        name < forms.len() && forms[name as int] is Atom
    }
}

spec fn shared_types_before(
    sources: Seq<OutputSource>, inputs: Seq<TypedPort>, outputs: Seq<TypedPort>, connections: Seq<Option<usize>>,
) -> bool {
    &&& connections.len() <= sources.len() && sources.len() == outputs.len()
    &&& forall|i: int| 0 <= i < connections.len() ==> {
        let connection = #[trigger] connections[i];
        match sources[i] {
            OutputSource::Body => connection.is_none(),
            OutputSource::Input { port, .. } =>
                connection == Some(port) && port < inputs.len()
                    && port_types_equal(inputs[port as int].ty, outputs[i].ty),
        }
    }
}

spec fn first_shared_type_mismatch(
    sources: Seq<OutputSource>, inputs: Seq<TypedPort>, outputs: Seq<TypedPort>, error: TypedSignatureError,
) -> bool {
    error matches TypedSignatureError::SharedTypeMismatch { input, output }
        && !port_types_equal(input.ty, output.ty)
        && exists|i: int, earlier: Seq<Option<usize>>| 0 <= i < outputs.len() && i < sources.len()
            && (match #[trigger] sources[i] {
                OutputSource::Input { port, .. } => port < inputs.len()
                    && input == inputs[port as int] && output == outputs[i],
                _ => false,
            })
            && earlier.len() == i && #[trigger] shared_types_before(sources, inputs, outputs, earlier)
}

proof fn shared_connections_exclude_type_error(
    sources: Seq<OutputSource>, inputs: Seq<TypedPort>, outputs: Seq<TypedPort>, connections: Seq<Option<usize>>,
    error: TypedSignatureError,
)
    requires
        connections.len() == outputs.len(),
        shared_types_before(sources, inputs, outputs, connections),
    ensures !first_shared_type_mismatch(sources, inputs, outputs, error),
{
    if let TypedSignatureError::SharedTypeMismatch { input, output } = error {
        if first_shared_type_mismatch(sources, inputs, outputs, error) {
            let (i, _) = choose|i: int, earlier: Seq<Option<usize>>| 0 <= i < outputs.len() && i < sources.len()
                && (match #[trigger] sources[i] {
                    OutputSource::Input { port, .. } => port < inputs.len()
                        && input == inputs[port as int] && output == outputs[i],
                    _ => false,
                })
                && earlier.len() == i && #[trigger] shared_types_before(sources, inputs, outputs, earlier);
            let port = sources[i]->Input_port;
            assert(connections[i] == Some(port));
            assert(port_types_equal(inputs[port as int].ty, outputs[i].ty));
        }
    }
}

fn copy_typed_port<'p, 'a>(port: &TypedPort<'p, 'a>) -> (copy: TypedPort<'p, 'a>)
    ensures copy == *port,
{
    TypedPort {
        declared: port.declared,
        ty: port.ty,
        annotation: LocatedName {
            source: port.annotation.source,
            span: port.annotation.span.start..port.annotation.span.end,
        },
    }
}

fn check_shared_types<'p, 'a>(
    sources: &[OutputSource], inputs: &[TypedPort<'p, 'a>], outputs: &[TypedPort<'p, 'a>],
) -> (result: Result<Vec<Option<usize>>, TypedSignatureError<'p, 'a>>)
    requires
        sources@.len() == outputs@.len(),
        forall|i: int| 0 <= i < sources@.len() ==> match #[trigger] sources@[i] {
            OutputSource::Input { port, .. } => port < inputs@.len(),
            _ => true,
        },
    ensures match result {
        Ok(connections) => connections@.len() == outputs@.len()
            && shared_types_before(sources@, inputs@, outputs@, connections@),
        Err(error) => first_shared_type_mismatch(sources@, inputs@, outputs@, error),
    },
{
    let mut connections: Vec<Option<usize>> = Vec::new();
    let mut at = 0;
    while at < outputs.len()
        invariant
            sources@.len() == outputs@.len(),
            forall|i: int| 0 <= i < sources@.len() ==> match #[trigger] sources@[i] {
                OutputSource::Input { port, .. } => port < inputs@.len(),
                _ => true,
            },
            at == connections@.len() <= outputs@.len(),
            shared_types_before(sources@, inputs@, outputs@, connections@),
        decreases outputs@.len() - at,
    {
        let matched = match sources[at] {
            OutputSource::Body => None,
            OutputSource::Input { port, .. } => {
                let input = &inputs[port];
                let output = &outputs[at];
                if !input.ty.is_same_type(&output.ty) {
                    let error = TypedSignatureError::SharedTypeMismatch {
                        input: copy_typed_port(input), output: copy_typed_port(output),
                    };
                    assert(first_shared_type_mismatch(sources@, inputs@, outputs@, error));
                    return Err(error);
                }
                Some(port)
            },
        };
        connections.push(matched);
        at += 1;
    }
    Ok(connections)
}

} // verus!
