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
use crate::project::signatures::{checked_signature_ports, routine_signature_evidence};
#[cfg(verus_only)]
use crate::project::widths::{checked_name_sites, checked_width_sites, reference_kind};
use crate::project::{
    CheckedPort, DeclaredPortType, LocatedName, OutputSource, PortDirection, ProjectSource,
    RoutineSignatureError, check_routine_signature,
};
use crate::syntax::Form;
use crate::syntax::circuit::{NamedForm, PortTypeSite};
#[cfg(verus_only)]
use crate::syntax::circuit::{indexed_entry_evidence, namespace_name_evidence};
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

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
