//! 混在索引の署名からポート型を解決する。

mod wiring;
pub use wiring::MixedFuncWiringError;

use super::*;
use crate::project::{DeclaredPortType, FuncDriverError, FuncDriverResult, PortDirection, ResolvedPortType, RoutineSignatureError, TypedPort,
    TypedRoutineSignature, TypedSignatureError};
use crate::project::use_aliases::function_drivers::prepare_indexed_func_drivers;
#[cfg(verus_only)]
use crate::project::use_aliases::function_drivers::{indexed_func_driver_evidence, local_names_indexed, names_match_ports};
use crate::project::use_aliases::local_signal_index::LocalSignalIndex;
use crate::project::use_aliases::port_types::check_shared_types;
#[cfg(verus_only)]
use crate::project::use_aliases::port_types::{first_shared_type_mismatch, shared_input_bounds, shared_types_before};
use crate::syntax::circuit::{NamedBuildCircuit, PortTypeSite};
#[cfg(verus_only)]
use crate::syntax::circuit::indexed_entry_evidence;
use alloc::vec::Vec;
#[cfg(verus_only)]
use crate::project::widths::checked_name_sites;
#[cfg(verus_only)]
use crate::project::{circuits::name_in_source, parsed_circuit_matches};
use crate::project::CheckedPort;
#[cfg(verus_only)]
use crate::project::CheckedRoutineSignature;
#[cfg(verus_only)]
use crate::syntax::{Form, form_span, form_spans_valid};

verus! {

/// 混在ソース集合の署名で見つかった違反。
#[derive(Debug)]
pub enum MixedTypedSignatureError<'p, 'a> {
    /// ポート幅、ポート名、共有配線に関する署名の違反。
    Signature(RoutineSignatureError<'p, 'a>),
    /// ポートの型名が構造体宣言を指さない。
    TypeReference {
        /// 型名を指定したポートの方向。
        direction: PortDirection,
        /// ポートの型名の位置と文書版。
        reference: LocatedName<'p, 'a>,
        /// 解決結果と、見つかった宣言や名前空間の位置。
        reason: MixedFuncCalleeError<'p, 'a>,
    },
    /// 同じ配線を共有する入出力の解決後の型が一致しない。
    Shared(TypedSignatureError<'p, 'a>),
}

/// 混在プロジェクトの関数の署名または駆動元の違反。
#[derive(Debug)]
pub enum MixedFuncDriverError<'p, 'a> {
    /// ポートの型名や共有配線の型を含む署名の違反。
    Signature(MixedTypedSignatureError<'p, 'a>),
    /// 関数の駆動元の違反。
    Driver(FuncDriverError<'p, 'a>),
}

pub(super) open spec fn has_mixed_func(project: &ParsedProjectSources, file: usize, entry: usize) -> bool {
    &&& project.has_mixed_routine_signature(file, entry)
    &&& project.indexes_model()[file as int]->Circuit_0.syntax.entries@[entry as int].head is Func
}

// 名前の探索結果から、選んだ宣言が混在索引に現れるキーを取り出す。
#[verifier::spinoff_prover]
proof fn scoped_declaration_key<'q>(
    aliases: &MixedUseAliases, file: usize, scope: DefnScope, word: &'q str,
    expected: Head, declaration: ProjectDeclaration,
) -> (key: NameKey<'q>)
    requires
        scoped_circuit_name_matches(aliases, file, scope, word, expected, Ok(Some(declaration))),
        mixed_use_targets_match(&aliases.targets_model().project_model(), aliases.targets_model()),
    ensures
        declaration.kind == ProjectDeclarationKind::Circuit(expected),
        aliases.targets_model().exports_model().declarations_model().declaration_at(key, declaration),
{
    let targets = aliases.targets_model();
    let exports = targets.exports_model();
    let declarations = exports.declarations_model();
    let result = Ok(Some(declaration));
    match bare_atom_kind(word.spec_bytes()) {
        Some(AtomKind::Name) => {
            let binding = choose|binding: Option<MixedAbsoluteTarget>|
                {
                    &&& #[trigger] scoped_binding(aliases, file, scope, word, binding)
                    &&& binding matches Some(target)
                    &&& scoped_absolute_result(Ok(target), expected, result)
                };
            assert(binding == Some(MixedAbsoluteTarget::Declaration(declaration)));
            if aliases.first_alias_matches(file, scope.block, word, None) {
                assert(declarations.declaration_at(NameKey { parent: scope.namespace, name: word }, declaration));
            } else {
                let rows = targets.directives_model();
                let rank = choose|rank: usize| #[trigger] aliases.first_alias_matches(file, scope.block, word, Some(rank))
                    && rank < rows.len() && binding == Some(rows[rank as int].target);
                targets.directive_origin(rank as int);
                let row = rows[rank as int];
                absolute_name_declares(&exports, row.site.reference.word, row.site.namespace, declaration);
            }
        },
        Some(AtomKind::AbsolutePath) => {
            let absolute = choose|absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                #[trigger] mixed_absolute_resolution_evidence(&exports, word, scope.namespace, absolute)
                    && scoped_absolute_result(absolute, expected, result);
            assert(absolute == Ok(MixedAbsoluteTarget::Declaration(declaration)));
            absolute_name_declares(&exports, word, scope.namespace, declaration);
        },
        Some(AtomKind::RelativePath) => {
            let (head, middle, last, binding) = choose|head: &str, middle: Option<&str>, last: &str, binding: Option<MixedAbsoluteTarget>|
                #[trigger] relative_path_parts(word, head, middle, last)
                    && #[trigger] scoped_binding(aliases, file, scope, head, binding)
                    && match binding {
                        Some(MixedAbsoluteTarget::Namespace { key, .. }) =>
                            exists|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                                parent@ == parent_spelling(key, middle)
                                    && #[trigger] mixed_key_resolution(&exports, NameKey { parent: Some(parent), name: last }, scope.namespace, absolute)
                                    && scoped_absolute_result(absolute, expected, result),
                        _ => false,
                    };
            let key = binding->Some_0->Namespace_key;
            let (parent, absolute) = choose|parent: &str, absolute: Result<MixedAbsoluteTarget, AbsoluteResolutionError>|
                parent@ == parent_spelling(key, middle)
                    && #[trigger] mixed_key_resolution(&exports, NameKey { parent: Some(parent), name: last }, scope.namespace, absolute)
                    && scoped_absolute_result(absolute, expected, result);
            assert(absolute == Ok(MixedAbsoluteTarget::Declaration(declaration)));
            assert(declarations.declaration_at(NameKey { parent: Some(parent), name: last }, declaration));
        },
        _ => assert(false),
    }
    choose|key: NameKey| #[trigger] declarations.declaration_at(key, declaration)
}

struct MixedPortContext<'p, 'a> {
    file: usize,
    scope: DefnScope<'a>,
    source: &'p crate::project::ProjectSource<'a>,
    parsed: &'p NamedBuildCircuit<'a>,
}

spec fn port_annotation(port: CheckedPort) -> usize {
    match port.site.ty {
        PortTypeSite::ImplicitBit => port.site.name,
        PortTypeSite::Bits { width } => width,
        PortTypeSite::Named { form } => form,
    }
}

spec fn mixed_port_result(
    aliases: &MixedUseAliases, context: &MixedPortContext, port: CheckedPort, direction: PortDirection,
    result: Result<TypedPort, MixedTypedSignatureError>,
) -> bool {
    let forms = context.parsed.syntax.forms@;
    let annotation = form_span(forms[port_annotation(port) as int]);
    let project = aliases.targets_model().project_model();
    match result {
        Ok(typed) => {
            &&& typed.declared == port && *typed.annotation.source == *context.source && typed.annotation.span == annotation
            &&& match (port.ty, typed.ty) {
                (DeclaredPortType::Bits(width), ResolvedPortType::Bits(found)) => width == found,
                (DeclaredPortType::Named { .. }, ResolvedPortType::Struct { source, form }) => exists|word: &str, declaration: ProjectDeclaration| {
                    &&& word.spec_bytes() == context.source.text.spec_bytes()[annotation.start as int..annotation.end as int]
                    &&& #[trigger] scoped_circuit_name_matches(aliases, context.file, context.scope, word, Head::Struct, Ok(Some(declaration)))
                    &&& declaration.file < project.indexes_model().len()
                    &&& *source == *declaration.name.source
                    &&& project.indexes_model()[declaration.file as int] matches ProjectSourceIndex::Circuit(parsed)
                    &&& declaration.item < parsed.names@.len() && *form == parsed.names@[declaration.item as int]
                    &&& form.head is Struct
                },
                _ => false,
            }
        },
        Err(MixedTypedSignatureError::TypeReference { direction: actual, reference, reason }) => {
            &&& port.ty is Named && actual == direction && *reference.source == *context.source && reference.span == annotation
            &&& exists|word: &str, found: Result<Option<ProjectDeclaration>, MixedFuncCalleeError>| {
                &&& word.spec_bytes() == context.source.text.spec_bytes()[annotation.start as int..annotation.end as int]
                &&& #[trigger] scoped_circuit_name_matches(aliases, context.file, context.scope, word, Head::Struct, found)
                &&& (found == Err(reason) || found == Ok(None) && reason is Missing)
            }
        },
        Err(_) => false,
    }
}

spec fn typed_prefix(aliases: &MixedUseAliases, context: &MixedPortContext, ports: Seq<CheckedPort>,
    direction: PortDirection, typed: Seq<TypedPort>) -> bool
{
    &&& typed.len() <= ports.len()
    &&& forall|i: int| 0 <= i < typed.len() ==>
        mixed_port_result(aliases, context, ports[i], direction, Ok(#[trigger] typed[i]))
}

spec fn typed_ports_result(aliases: &MixedUseAliases, context: &MixedPortContext, ports: Seq<CheckedPort>,
    direction: PortDirection, result: Result<Vec<TypedPort>, MixedTypedSignatureError>) -> bool
{
    match result {
        Ok(typed) => typed@.len() == ports.len() && typed_prefix(aliases, context, ports, direction, typed@),
        Err(error) => exists|i: int, earlier: Seq<TypedPort>| 0 <= i < ports.len() && earlier.len() == i
            && #[trigger] typed_prefix(aliases, context, ports, direction, earlier)
            && #[trigger] mixed_port_result(aliases, context, ports[i], direction, Err(error)),
    }
}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    fn resolve_mixed_port(&self, context: &MixedPortContext<'p, 'a>, port: CheckedPort, direction: PortDirection)
        -> (result: Result<TypedPort<'p, 'a>, MixedTypedSignatureError<'p, 'a>>)
        requires
            checked_name_sites(context.parsed.syntax.forms@, seq![port]),
            parsed_circuit_matches(*context.source, *context.parsed),
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures mixed_port_result(self, context, port, direction, result),
    {
        let source = context.source;
        let forms = &context.parsed.syntax.forms;
        let at = match port.site.ty {
            PortTypeSite::ImplicitBit => port.site.name,
            PortTypeSite::Bits { width } => width,
            PortTypeSite::Named { form } => form,
        };
        proof {
            parsed_index_evidence(*source, *context.parsed);
            let ports = seq![port];
            assert(ports[0] == port);
            assert(at < forms@.len() && forms@[at as int] is Atom);
            if port.ty is Named {
                assert(port.site.ty is Named);
                assert(reference_atom(forms@[at as int]->Atom_kind));
            }
        }
        let (word, span) = read_indexed_atom(source.text, forms, at);
        let annotation = LocatedName { source, span };
        let ty = match port.ty {
            DeclaredPortType::Bits(width) => ResolvedPortType::Bits(width),
            DeclaredPortType::Named { .. } => {
                let selection = self.resolve_scoped_circuit_name(context.file, context.scope, word, Head::Struct);
                let declaration = match selection {
                    Ok(Some(declaration)) => declaration,
                    Ok(None) => return Err(MixedTypedSignatureError::TypeReference {
                        direction, reference: annotation, reason: MixedFuncCalleeError::Missing,
                    }),
                    Err(reason) => return Err(MixedTypedSignatureError::TypeReference { direction, reference: annotation, reason }),
                };
                let project = self.targets().project();
                proof {
                    let key = scoped_declaration_key(self, context.file, context.scope, word, Head::Struct, declaration);
                    let targets = self.targets_model();
                    let exports = targets.exports_model();
                    targets.mixed_use_exports_match(project);
                    mixed_exports_use_project_declarations(project, &exports);
                    mixed_declaration_origin(project, &exports.declarations_model(), key, declaration);
                    let file = declaration.file as int;
                    if project.indexes_model()[file] is Functional {
                        assert(false);
                    }
                }
                let ProjectSourceIndex::Circuit(parsed) = &project.indexes()[declaration.file] else { unreachable!() };
                let form = &parsed.names[declaration.item];
                ResolvedPortType::Struct { source: declaration.name.source, form }
            },
        };
        Ok(TypedPort { declared: port, ty, annotation })
    }

    fn resolve_mixed_ports(&self, context: &MixedPortContext<'p, 'a>, ports: &[CheckedPort], direction: PortDirection)
        -> (result: Result<Vec<TypedPort<'p, 'a>>, MixedTypedSignatureError<'p, 'a>>)
        requires
            checked_name_sites(context.parsed.syntax.forms@, ports@),
            parsed_circuit_matches(*context.source, *context.parsed),
            mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures typed_ports_result(self, context, ports@, direction, result),
    {
        let mut typed = Vec::new();
        let mut at = 0;
        while at < ports.len()
            invariant
                checked_name_sites(context.parsed.syntax.forms@, ports@),
                parsed_circuit_matches(*context.source, *context.parsed),
                mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
                at == typed@.len() <= ports@.len(),
                typed_prefix(self, context, ports@, direction, typed@),
            decreases ports@.len() - at,
        {
            assert(checked_name_sites(context.parsed.syntax.forms@, seq![ports@[at as int]]));
            let item = match self.resolve_mixed_port(context, ports[at], direction) {
                Ok(item) => item,
                Err(error) => return Err(error),
            };
            typed.push(item);
            at += 1;
        }
        Ok(typed)
    }

    /// 混在プロジェクトでポート型を解決し、共有配線の型を照合する。
    ///
    /// 関数またはモジュールの厳格索引を指定する。範囲外や別の構文項目に対しては `Ok(None)` を返す。
    ///
    /// # Errors
    ///
    /// 署名自体の違反を先に返す。その後、各入力、各出力、共有配線の順に型の違反を調べる。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::project::{FuncDriverResult, MixedFuncCalleeError, MixedTypedSignatureError,
    ///     ProjectSourceIndex, ResolvedPortType, SourceSnapshot, check_mixed_use_aliases,
    ///     index_mixed_use_targets, parse_project_sources};
    ///
    /// let helper = "(namespace meta (export ready) (defn ready (as-type (Fn () Bool) (fn () true))))";
    /// let circuit = "(namespace lib (export Word) (struct Word (width 8)))
    ///     (namespace app
    ///         (use ::lib::Word T) (use ::meta::ready Wrong)
    ///         (func wire (in (x T)) (out (x ::lib::Word)))
    ///         (func bad (in (x Wrong)) (out x)))";
    /// let project = parse_project_sources(&[
    ///     SourceSnapshot { path: "helpers.ncg2m", revision: 3, text: helper },
    ///     SourceSnapshot { path: "demo.ncg2", revision: 8, text: circuit },
    /// ]).unwrap();
    /// let targets = index_mixed_use_targets(&project).unwrap();
    /// let aliases = check_mixed_use_aliases(&targets).unwrap();
    /// let ProjectSourceIndex::Circuit(index) = &project.indexes()[1] else { panic!() };
    /// let entry = |name| {
    ///     let form = index.names.iter().find(|site| site.name.word == name).unwrap().form;
    ///     index.syntax.entries.iter().position(|item| item.form == form).unwrap()
    /// };
    /// let wire = aliases.resolve_mixed_routine_signature(1, entry("wire"), 64).unwrap().unwrap();
    /// assert!(matches!(wire.inputs[0].ty, ResolvedPortType::Struct { .. }));
    /// assert_eq!(wire.output_inputs, vec![Some(0)]);
    /// assert!(matches!(aliases.check_mixed_func_drivers(1, entry("wire"), 64),
    ///     Ok(FuncDriverResult::Checked(_))));
    /// let Err(MixedTypedSignatureError::TypeReference { reference,
    ///     reason: MixedFuncCalleeError::WrongDeclaration(found), .. }) =
    ///     aliases.resolve_mixed_routine_signature(1, entry("bad"), 64) else { panic!() };
    /// assert_eq!((&circuit[reference.span], reference.source.revision), ("Wrong", 8));
    /// assert_eq!((&helper[found.name.span], found.name.source.revision), ("ready", 3));
    /// ```
    pub fn resolve_mixed_routine_signature(&self, file: usize, entry: usize, max_width: u64)
        -> (result: Result<Option<TypedRoutineSignature<'p, 'a>>, MixedTypedSignatureError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures
            result != Ok(None) <==> self.targets_model().project_model().has_mixed_routine_signature(file, entry),
            self.mixed_typed_signature_matches(file, entry, max_width, result),
    {
        let project = self.targets().project();
        let raw = match project.check_mixed_routine_signature(file, entry, max_width) {
            Ok(Some(raw)) => raw,
            Ok(None) => return Ok(None),
            Err(error) => return Err(MixedTypedSignatureError::Signature(error)),
        };
        proof {
            project.mixed_routine_signature_ports(file, entry, max_width, raw);
            project.mixed_routine_indexed_sites(file, entry, max_width, raw);
        }
        let source = &project.sources()[file];
        let index = &project.indexes()[file];
        let ProjectSourceIndex::Circuit(parsed) = index else { unreachable!() };
        let owner = &parsed.syntax.entries[entry];
        proof {
            project_source_index_evidence(*source, *index);
            parsed_index_evidence(*source, *parsed);
            indexed_entry_evidence(source.text, parsed.syntax.forms@, parsed.syntax.entries@, entry as int);
            if let Some(block) = owner.namespace {
                namespace_name_evidence(source.text, parsed.syntax.forms@, parsed.syntax.entries@, parsed.names@, owner.form as int, block);
                let i = choose|i: int| 0 <= i < parsed.names@.len() && (#[trigger] parsed.names@[i]).form == block
                    && parsed.names@[i].head is Namespace && parsed.names@[i].block is None;
                assert(is_namespace_block(parsed.names@[i], block));
            }
        }
        let namespace = match owner.namespace {
            Some(block) => find_namespace(parsed, block),
            None => None,
        };
        let scope = DefnScope { block: owner.namespace, namespace };
        let context = MixedPortContext { file, scope, source, parsed };
        assert(func_scope_path(parsed, owner.namespace, namespace));
        let inputs = self.resolve_mixed_ports(&context, &raw.ports.inputs, PortDirection::Input)?;
        let outputs = self.resolve_mixed_ports(&context, &raw.ports.outputs, PortDirection::Output)?;
        match check_shared_types(&raw.output_sources, &inputs, &outputs) {
            Ok(output_inputs) => Ok(Some(TypedRoutineSignature { inputs, outputs, output_inputs })),
            Err(error) => Err(MixedTypedSignatureError::Shared(error)),
        }
    }

    /// 型検査の結果が同じ署名、別名スコープ、構造体宣言に対応することを表す。
    pub closed spec fn mixed_typed_signature_matches(
        &self, file: usize, entry: usize, max_width: u64,
        result: Result<Option<TypedRoutineSignature>, MixedTypedSignatureError>,
    ) -> bool {
        let project = self.targets_model().project_model();
        match result {
            Ok(None) => project.mixed_routine_signature_evidence(file, entry, max_width, Ok(None)),
            Err(MixedTypedSignatureError::Signature(error)) => project.mixed_routine_signature_evidence(file, entry, max_width, Err(error)),
            _ => exists|context: MixedPortContext, raw: CheckedRoutineSignature|
                #![trigger project.mixed_routine_signature_evidence(file, entry, max_width, Ok(Some(raw))),
                    func_scope_path(context.parsed, context.scope.block, context.scope.namespace)] {
                &&& project.mixed_routine_signature_evidence(file, entry, max_width, Ok(Some(raw)))
                &&& context.file == file && *context.source == project.sources_model()[file as int]
                &&& *context.parsed == project.indexes_model()[file as int]->Circuit_0
                &&& context.scope.block == context.parsed.syntax.entries@[entry as int].namespace
                &&& func_scope_path(context.parsed, context.scope.block, context.scope.namespace)
                &&& match result {
                    Ok(Some(typed)) => {
                        &&& typed_ports_result(self, &context, raw.ports.inputs@, PortDirection::Input, Ok(typed.inputs))
                        &&& typed_ports_result(self, &context, raw.ports.outputs@, PortDirection::Output, Ok(typed.outputs))
                        &&& typed.output_inputs@.len() == typed.outputs@.len()
                        &&& shared_types_before(raw.output_sources@, typed.inputs@, typed.outputs@, typed.output_inputs@)
                    },
                    Err(MixedTypedSignatureError::Shared(error)) => exists|inputs: Vec<TypedPort>, outputs: Vec<TypedPort>| {
                        &&& #[trigger] typed_ports_result(self, &context, raw.ports.inputs@, PortDirection::Input, Ok(inputs))
                        &&& #[trigger] typed_ports_result(self, &context, raw.ports.outputs@, PortDirection::Output, Ok(outputs))
                        &&& first_shared_type_mismatch(raw.output_sources@, inputs@, outputs@, error)
                    },
                    Err(error) => typed_ports_result(self, &context, raw.ports.inputs@, PortDirection::Input, Err(error))
                        || exists|inputs: Vec<TypedPort>| {
                            &&& #[trigger] typed_ports_result(self, &context, raw.ports.inputs@, PortDirection::Input, Ok(inputs))
                            &&& typed_ports_result(self, &context, raw.ports.outputs@, PortDirection::Output, Err(error))
                        },
                    _ => false,
                }
            },
        }
    }

    /// 型付きポートの名前と共有入力の添字が、元の厳格索引を使うことを示す。
    #[verifier::spinoff_prover]
    pub proof fn mixed_typed_signature_ports(
        &self, file: usize, entry: usize, max_width: u64, typed: TypedRoutineSignature<'p, 'a>,
    )
        requires self.mixed_typed_signature_matches(file, entry, max_width, Ok(Some(typed))),
        ensures ({
            let project = self.targets_model().project_model();
            let forms = project.indexes_model()[file as int]->Circuit_0.syntax.forms@;
            &&& project.has_mixed_routine_signature(file, entry)
            &&& typed.output_inputs@.len() == typed.outputs@.len()
            &&& forall|i: int| 0 <= i < typed.output_inputs@.len() ==>
                ((#[trigger] typed.output_inputs@[i]) matches Some(input) ==> input < typed.inputs@.len())
            &&& forall|i: int| 0 <= i < typed.inputs@.len() ==> {
                let port = #[trigger] typed.inputs@[i];
                &&& port.declared.site.name < forms.len() && forms[port.declared.site.name as int] is Atom
                &&& *port.annotation.source == project.sources_model()[file as int]
            }
            &&& forall|i: int| 0 <= i < typed.outputs@.len() ==> {
                let port = #[trigger] typed.outputs@[i];
                &&& port.declared.site.name < forms.len() && forms[port.declared.site.name as int] is Atom
                &&& *port.annotation.source == project.sources_model()[file as int]
            }
        }),
    {
        let project = self.targets_model().project_model();
        let (context, raw) = choose|context: MixedPortContext, raw: CheckedRoutineSignature|
            #![trigger project.mixed_routine_signature_evidence(file, entry, max_width, Ok(Some(raw))),
                func_scope_path(context.parsed, context.scope.block, context.scope.namespace)] {
            &&& project.mixed_routine_signature_evidence(file, entry, max_width, Ok(Some(raw)))
            &&& context.file == file && *context.source == project.sources_model()[file as int]
            &&& *context.parsed == project.indexes_model()[file as int]->Circuit_0
            &&& context.scope.block == context.parsed.syntax.entries@[entry as int].namespace
            &&& func_scope_path(context.parsed, context.scope.block, context.scope.namespace)
            &&& typed_ports_result(self, &context, raw.ports.inputs@, PortDirection::Input, Ok(typed.inputs))
            &&& typed_ports_result(self, &context, raw.ports.outputs@, PortDirection::Output, Ok(typed.outputs))
            &&& shared_types_before(raw.output_sources@, typed.inputs@, typed.outputs@, typed.output_inputs@)
        };
        project.mixed_routine_signature_ports(file, entry, max_width, raw);
        shared_input_bounds(raw.output_sources@, typed.inputs@, typed.outputs@, typed.output_inputs@);
    }

    /// 混在プロジェクトの関数で、ポート型を解決し、入力と出力の駆動元を検査する。
    ///
    /// 関数以外を指す添字には [`FuncDriverResult::NotFunc`] を返す。展開を要する本体には
    /// [`FuncDriverResult::NeedsExpansion`] とその位置を返す。
    ///
    /// # Errors
    ///
    /// 署名を先に検査し、その後、入力への駆動、多重駆動、出力の駆動元の不足を調べる。
    pub fn check_mixed_func_drivers(&self, file: usize, entry: usize, max_width: u64)
        -> (result: Result<FuncDriverResult<'p, 'a>, MixedFuncDriverError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures self.mixed_func_driver_matches(file, entry, max_width, result),
    {
        match self.prepare_mixed_func_drivers(file, entry, max_width) {
            Ok((drivers, _, _)) => Ok(drivers),
            Err(error) => Err(error),
        }
    }

    fn prepare_mixed_func_drivers(&self, file: usize, entry: usize, max_width: u64)
        -> (prepared: Result<(FuncDriverResult<'p, 'a>, Vec<NameSite<'a>>, Option<LocalSignalIndex>), MixedFuncDriverError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures match prepared {
            Ok((result, inputs, index)) => self.mixed_func_driver_matches(file, entry, max_width, Ok(result))
                && (result matches FuncDriverResult::Checked(drivers) ==> {
                    let project = self.targets_model().project_model();
                    let source = &project.sources_model()[file as int];
                    let parsed = &project.indexes_model()[file as int]->Circuit_0;
                    &&& has_mixed_func(&project, file, entry)
                    &&& inputs@.len() == drivers.signature.inputs@.len()
                    &&& names_match_ports(source.text, parsed.syntax.forms@, drivers.signature.inputs@, inputs@)
                    &&& forall|i: int| 0 <= i < drivers.definitions@.len() ==>
                        name_in_source(source.text, (#[trigger] drivers.definitions@[i]).name)
                    &&& (index matches Some(names) ==> local_names_indexed(
                        &names, inputs@, inputs@.len() as int, drivers.definitions@, drivers.definitions@.len() as int))
                }),
            Err(error) => self.mixed_func_driver_matches(file, entry, max_width, Err(error)),
        },
    {
        let project = self.targets().project();
        let sources = project.sources();
        let indexes = project.indexes();
        if file >= sources.len() { return Ok((FuncDriverResult::NotFunc, Vec::new(), None)); }
        let index = &indexes[file];
        let ProjectSourceIndex::Circuit(parsed) = index else { return Ok((FuncDriverResult::NotFunc, Vec::new(), None)); };
        if entry >= parsed.syntax.entries.len() || !matches!(parsed.syntax.entries[entry].head, Head::Func) {
            return Ok((FuncDriverResult::NotFunc, Vec::new(), None));
        }
        assert(has_mixed_func(project, file, entry));
        let signature = match self.resolve_mixed_routine_signature(file, entry, max_width) {
            Ok(Some(signature)) => signature,
            Ok(None) => { proof { assert(false); } unreachable!() },
            Err(error) => return Err(MixedFuncDriverError::Signature(error)),
        };
        let source = &sources[file];
        proof {
            project_source_index_evidence(*source, *index);
            self.mixed_typed_signature_ports(file, entry, max_width, signature);
        }
        match prepare_indexed_func_drivers(source, parsed, entry, signature, None) {
            Ok(prepared) => Ok(prepared),
            Err(error) => Err(MixedFuncDriverError::Driver(error)),
        }
    }

    /// 署名と駆動元の検査結果が同じ関数の厳格索引に対応することを表す。
    pub closed spec fn mixed_func_driver_matches(
        &self, file: usize, entry: usize, max_width: u64,
        result: Result<FuncDriverResult, MixedFuncDriverError>,
    ) -> bool {
        let project = self.targets_model().project_model();
        if !has_mixed_func(&project, file, entry) {
            result == Ok(FuncDriverResult::NotFunc)
        } else {
            let source = &project.sources_model()[file as int];
            let parsed = &project.indexes_model()[file as int]->Circuit_0;
            match result {
                Err(MixedFuncDriverError::Signature(error)) => self.mixed_typed_signature_matches(file, entry, max_width, Err(error)),
                Ok(drivers) => exists|typed: TypedRoutineSignature|
                    #[trigger] self.mixed_typed_signature_matches(file, entry, max_width, Ok(Some(typed)))
                    && indexed_func_driver_evidence(source, parsed, entry, typed, Ok(drivers)),
                Err(MixedFuncDriverError::Driver(error)) => exists|typed: TypedRoutineSignature|
                    #[trigger] self.mixed_typed_signature_matches(file, entry, max_width, Ok(Some(typed)))
                    && indexed_func_driver_evidence(source, parsed, entry, typed, Err(error)),
            }
        }
    }
}

}
