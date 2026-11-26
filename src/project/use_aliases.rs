//! 解決済みの `use` をスコープごとに照合し、別名の束縛と重複警告を求める。

mod alias_index;
mod batch;
mod bit_func;
pub use bit_func::{
    BitFuncError, BitFuncLowerError, CheckedBitFunc, ExpandFunctionsError, ExpandedFunctions, FunctionBuildDiagnostic,
    LoweredBitFunc, UnsupportedBitFunc,
};
#[cfg(verus_only)]
pub use bit_func::{
    bit_func_evaluation, bit_func_lowering_preserves_evaluation, bit_func_evaluations_agree,
    checked_bit_func_available, lowered_bit_func_result, port_values,
};
mod call_arity;
mod call_dependencies;
mod definitions;
mod dependency_order;
mod settling;
mod settling_hint;
pub use settling_hint::{ModuleExpansionHint, ModuleSettlingHint};
pub use settling::clocked_nor_settling_bound;
#[cfg(verus_only)]
pub use settling::{clocked_nor_bound_matches, clocked_nor_depths, clocked_nor_has_cycle, clocked_nor_states_settle, fixed_nor_states};
mod function_drivers;
mod function_atoms;
mod function_literals;
mod function_types;
mod function_wiring;
mod local_signal_index;
mod module_calls;
pub use port_types::{StorageSignature, StorageSignatureError};
pub use module_calls::{ModuleCallInputs, ModuleCallInputsError, ModuleCallPorts, ModuleCallPortsError,
    ModuleCallSignature, ModuleCallSignatureError, ModuleCallTarget};
mod module_drivers;
pub use module_drivers::{ModuleDriverError, ModuleDrivers};
mod module_types;
pub use module_types::{ModuleAliasCycleStep, ModuleAliasSource, ModuleAliasTypes, ModuleAliasTypesError,
    ModuleConcat, ModuleConcatOperand, ModuleConcats, ModuleConcatsError,
    CheckedModuleCall, ModuleCalls, ModuleCallsError, ModuleInferredCallError, PrimitiveModuleError,
    ModuleOutputTypes, ModuleOutputTypesError,
    ModuleRootTypes, ModuleRootTypesError, ModuleSelection, ModuleSelections, ModuleSelectionsError, ModuleTypeSources};
pub use module_types::{ClockedEndpointError, ClockedModuleVm, ClockedModuleVmError, ClockedModuleVmLimits};
pub use module_types::{VramOutputError, VramTarget};
pub use module_types::{ClockedDeviceVm, ClockedDeviceVmError, DevicePortBits, DevicePortIoError, DevicePortMap};
pub use module_types::{ClockedVramVm, VramDeclaration, VramSetupError, VramView};
#[cfg(verus_only)]
pub use module_types::ClockedModuleObservation;
pub use module_types::{ClockedArgumentWiringError, ClockedModuleOutputs, ClockedModuleOutputsError};
pub use module_types::{ClockedDriverBitsError, clocked_driver_bits};
#[cfg(verus_only)]
pub use module_types::{clocked_driver_bit, clocked_driver_bits_result, clocked_driver_port_model, clocked_driver_selection_matches};
pub use module_types::{ClockedDefinitionLayoutError, ClockedLinkPlan, ClockedModuleError, ClockedPlanError, ClockedStorageLayout, ClockedStorageLayoutError, ClockedStoragePlacement, ClockedWireDriver, plan_clocked_links};
#[cfg(verus_only)]
pub use module_types::{clocked_link_plan_result, clocked_regions_cover, clocked_wire_at, clocked_wire_cycle,
    clocked_wire_solutions_agree, clocked_wires_match};
mod module_wiring;
pub use module_wiring::{BoundModuleSignal, ModuleWiring, ModuleWiringError};
mod port_types;
mod reference_cursor;
mod call_site;
pub(crate) use call_site::TypedArithmeticSite;
#[cfg(verus_only)]
pub(crate) use call_site::arithmetic_sites_fit;
pub use call_site::{DefnCallEdge, DefnCallError, DefnCallSite, DefnPosition, PreparedDefnCall};
#[cfg(verus_only)]
pub(crate) use call_site::call_arity_matches;
#[cfg(verus_only)]
pub use call_site::{prepared_defn_call_matches, prepared_defn_call_origin, prepared_call_site, project_named_defn_body_matches, project_named_defn_body_origin};
mod defn_name;
mod macro_arguments;
pub use macro_arguments::{MacroArgument, MacroArgumentScope, MacroArguments};
mod macro_calls;
pub use macro_calls::{MacroCall, MacroCallError, MacroCalls};
#[cfg(verus_only)]
pub use macro_calls::{macro_call_matches, macro_call_spans_in_source};
mod defmacro_name;
pub use defmacro_name::{DefmacroNameError, ResolvedDefmacro};
#[cfg(verus_only)]
pub use defmacro_name::{
    defmacro_name_resolution, defmacro_ranges_readable, has_macro_caller, indexed_defmacro,
    indexed_defmacro_is_retained, macro_declaration_name_origin, macro_reference_declaration,
};
mod mixed_function;
pub use mixed_function::{MixedFuncArityError, MixedFuncCallError, MixedFuncCallee, MixedFuncCalleeError, MixedFuncCalleeResolution,
    MixedFuncInputTypes, MixedFuncOutputTypes, MixedFuncTypeError,
    MixedFuncDriverError, MixedFuncWiringError, MixedTypedSignatureError};
mod defn_call_graph;
pub use defn_name::{DefnNameError, ResolvedDefnName};
pub use defn_call_graph::{DefnCallGraphError, DefnCallPlan};
#[cfg(verus_only)]
pub use defn_call_graph::{defn_call_cycle, defn_call_plan_matches, defn_call_plan_contains, defn_call_plan_local_scalar_body, defn_call_plan_root_scalar_call, defn_call_plan_edge_order, defn_call_plan_site_at_rank};
#[cfg(verus_only)]
pub use defn_name::{defn_name_resolution, resolved_defn_name_origin, stage_name_has_no_binding};
mod mixed;
pub use mixed::{MixedUseAliasConflict, MixedUseAliases, check_mixed_use_aliases};
#[cfg(verus_only)]
pub use mixed::{mixed_alias_conflict_evidence, mixed_alias_conflicts_agree, mixed_alias_dispositions_agree, mixed_use_aliases_acceptable, mixed_use_aliases_match};
mod relative;
mod selection_arguments;
mod signature_cache;
mod signal_observations;
pub use signal_observations::{SignalOccurrence, SignalOccurrenceKind, SignalRole};
#[cfg(verus_only)]
pub use signal_observations::{signal_occurrence_valid, signal_occurrences_in_document};
mod single_bit_func;
mod structure_types;
pub use structure_types::{
    StructureExpressionTypeError,
    ResolvedStructure, ResolvedStructureEntry, ResolvedStructureField, ResolvedStructures,
    StructureFieldType, StructureIndexError, StructureLayout, StructureLayoutError, StructureLayoutField, StructureLayouts,
    StructurePlacementError, StructurePosition, StructureResolutionError, StructureTypeError, StructureTypeReference, StructureOperation, StructureOperationError, TypedStructureOperation,
};
pub use batch::{DefinitionBatchError, DefinitionPosition, DefinitionReferences, IndexedDefinitionBinding};
pub use call_dependencies::{FunctionCallSite, FunctionExpansionError, FunctionExpansionOrder};
pub use call_arity::{
    CallInputError, CallInputReason, CallPortType, CheckedCallInputs, FuncArityError, FuncCallArity, FuncCallInputsError, FuncCallSignature, FuncCallSignatureError,
    FuncCallOutputError, FuncCallOutputTypes,
    FuncCallTarget, TypedFuncCall,
};
pub use definitions::{
    DefinitionBinding, DefinitionReferenceError, DefinitionReferenceReason,
    DefinitionReferenceSite, ResolvedDefinitionReference,
};
pub use function_drivers::{
    DefinitionDriver, FuncDriverError, FuncDriverResult, FuncDrivers, OutputDriver,
};
pub use function_literals::{FuncLiteralError, FuncLiteralWidths};
pub use function_atoms::{FuncAtomTypeError, FuncAtomTypes, SignalType};
pub use selection_arguments::{CheckedBitSelection, SelectionArgument, SelectionArgumentError};
pub use function_types::{FuncSignalTypeError, FuncSignalTypes};
pub use single_bit_func::LoweredSingleBitFunc;
#[cfg(verus_only)]
pub use single_bit_func::{
    single_bit_evaluation_outputs_agree, single_bit_evaluation_result_agrees, single_bit_lowering_matches,
    single_bit_lowering_outputs_match,
    single_bit_lowering_preserves_evaluation, single_bit_lowering_preserves_outputs_evaluation,
    single_bit_source_evaluation, single_bit_source_evaluations_agree, single_bit_source_outputs_evaluation,
    single_bit_source_outputs_evaluations_agree,
};

pub use single_bit_func::{CheckedSingleBitFunc, SingleBitDefinition, SingleBitFuncError, SingleBitOperand, SingleBitRhs, UnsupportedSingleBitFunc};
pub use function_wiring::{
    BoundFuncSignal, FuncSignalReason, FuncWiring, FuncWiringError, FuncWiringResult,
};
#[cfg(verus_only)]
pub use function_wiring::indexed_signal_driver_matches;
#[cfg(verus_only)]
pub use port_types::port_types_equal;
pub use port_types::{ResolvedPortType, TypedPort, TypedRoutineSignature, TypedSignatureError};
pub use port_types::{NamedRoutinePort, RoutinePortLookup};
pub use port_types::{DeviceBindingsError, DevicePortRequest};
pub use port_types::{DevicePortBinding, DevicePortBindingError, DevicePortType};
#[cfg(verus_only)]
pub use port_types::{device_port_types_match, matching_circuit_direction};
pub use relative::{RelativeResolutionError, RelativeTarget};

#[cfg(verus_only)]
use super::name_keys::key_bytes;
#[cfg(verus_only)]
use super::resolution::{direct_targets_agree, selected_direct_target_matches, selected_direct_targets_agree};
#[cfg(verus_only)]
use super::use_targets::{resolved_use_evidence, resolved_uses_share_file};
use super::{AbsoluteTarget, NameKey, ResolvedUse, UseTargets};
use alias_index::AliasIndex;
#[cfg(verus_only)]
use super::{DeclarationTable, absolute_resolution_evidence, direct_target_matches, same_target};
#[cfg(verus_only)]
use crate::syntax::circuit::NamedForm;
use crate::syntax::circuit::{Head, NamedBuildCircuit};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 一つの `use` が作る束縛、またはその重複警告。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AliasDisposition {
    /// このスコープと別名で最初の指定。直下の同一対象とも束縛を共有できる。
    Binding,
    /// 同じスコープで同じ別名と対象を指定した。
    Duplicate {
        /// 最初の指定を解決済み一覧で指す添字。警告の関連位置に使う。
        first: usize,
    },
}

/// 別名に異なる対象を割り当てたときの診断。
#[derive(Debug)]
pub enum AliasConflict<Directive, Target> {
    /// 同じスコープの二つの `use` が、同じ別名で異なる対象を指す。
    BetweenUses {
        /// 後から別名を指定した箇所と、その参照先。
        later: Directive,
        /// 同じ別名を最初に指定した箇所と、その参照先。
        first: Directive,
    },
    /// 別名と同じ名前の直接宣言または子名前空間が、異なる対象を指す。
    Direct {
        /// 衝突を起こした別名の指定と、その参照先。
        directive: Directive,
        /// 元から存在した宣言または子名前空間と、その位置。
        existing: Target,
    },
}

/// 解決済み索引にある `use` を借用する衝突診断。
pub type UseAliasConflict<'t, 'p, 'a> = AliasConflict<&'t ResolvedUse<'p, 'a>, AbsoluteTarget<'p, 'a, 'a>>;

/// 一時的な解決済み索引から切り離した衝突診断。
pub type OwnedUseAliasConflict<'p, 'a> = AliasConflict<ResolvedUse<'p, 'a>, AbsoluteTarget<'p, 'a, 'a>>;

pub(super) open spec fn owned_conflict_matches(error: UseAliasConflict, owned: OwnedUseAliasConflict) -> bool {
    match (error, owned) {
        (AliasConflict::BetweenUses { later, first }, AliasConflict::BetweenUses { later: copy_later, first: copy_first }) =>
            *later == copy_later && *first == copy_first,
        (AliasConflict::Direct { directive, existing }, AliasConflict::Direct { directive: copy, existing: other }) =>
            *directive == copy && existing == other,
        _ => false,
    }
}

pub(super) fn own_conflict<'t, 'p, 'a>(error: UseAliasConflict<'t, 'p, 'a>) -> (owned: OwnedUseAliasConflict<'p, 'a>)
    ensures owned_conflict_matches(error, owned),
{
    match error {
        AliasConflict::BetweenUses { later, first } => AliasConflict::BetweenUses {
            later: later.copy_for_diagnostic(), first: first.copy_for_diagnostic(),
        },
        AliasConflict::Direct { directive, existing } => AliasConflict::Direct {
            directive: directive.copy_for_diagnostic(), existing,
        },
    }
}

/// 解決済みの各 `use` に対応する別名の束縛と警告。
pub struct UseAliases<'t, 'p, 'a> {
    targets: &'t UseTargets<'p, 'a>,
    dispositions: Vec<AliasDisposition>,
    index: Option<AliasIndex>,
}

/// 無修飾名が指す直接の束縛、または別名を作った指定。
#[derive(Debug)]
pub enum UnqualifiedTarget<'t, 'p, 'a, 'q> {
    /// 現在の名前空間に属する独立宣言または子名前空間。
    Direct(AbsoluteTarget<'p, 'a, 'q>),
    /// 現在のファイルとブロックで別名を最初に指定した `use`。
    Alias(&'t ResolvedUse<'p, 'a>),
}

/// 無修飾名の検索で指定した参照元が、構文済みプロジェクトに存在しない。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReferenceScopeError {
    /// 構文済みプロジェクトに指定したファイルの添字がない。
    UnknownFile,
    /// 指定したファイルのフォームは名前空間ブロックを指さない。
    UnknownBlock,
}

spec fn alias_key<'a>(item: ResolvedUse<'_, 'a>) -> NameKey<'a> {
    NameKey { parent: item.site.namespace, name: item.site.alias.word }
}

spec fn same_alias(left: ResolvedUse, right: ResolvedUse) -> bool {
    left.site.source.id.components_model() == right.site.source.id.components_model()
        && left.site.block == right.site.block
        && key_bytes(NameKey { parent: None, name: left.site.alias.word })
            == key_bytes(NameKey { parent: None, name: right.site.alias.word })
}

fn scope_and_alias_match(left: &ResolvedUse, right: &ResolvedUse) -> (same: bool)
    ensures same == same_alias(*left, *right),
{
    left.site.block == right.site.block
        && NameKey { parent: None, name: left.site.alias.word }
            .same_name(NameKey { parent: None, name: right.site.alias.word })
        && left.site.source.id.same_file(&right.site.source.id)
}

spec fn first_alias(items: Seq<ResolvedUse>, at: int, first: int) -> bool {
    &&& 0 <= first < at < items.len()
    &&& same_alias(items[first], items[at])
    &&& forall|i: int| 0 <= i < first ==> !same_alias(#[trigger] items[i], items[at])
}

fn find_first(items: &[ResolvedUse], at: usize) -> (first: Option<usize>)
    requires at < items@.len(),
    ensures match first {
        Some(first) => first_alias(items@, at as int, first as int),
        None => forall|i: int| 0 <= i < at ==> !same_alias(#[trigger] items@[i], items@[at as int]),
    },
{
    let mut i = 0;
    while i < at
        invariant
            i <= at < items@.len(),
            forall|j: int| 0 <= j < i ==> !same_alias(#[trigger] items@[j], items@[at as int]),
        decreases at - i,
    {
        if scope_and_alias_match(&items[i], &items[at]) {
            return Some(i);
        }
        i += 1;
    }
    None
}

spec fn alias_in_scope(item: ResolvedUse, file: usize, block: Option<usize>, name: &str) -> bool {
    &&& item._file == file
    &&& item.site.block == block
    &&& key_bytes(NameKey { parent: None, name: item.site.alias.word })
        == key_bytes(NameKey { parent: None, name })
}

spec fn alias_lookup_matches(
    items: Seq<ResolvedUse>, file: usize, block: Option<usize>, name: &str, found: Option<&ResolvedUse>,
) -> bool {
    match found {
        Some(item) => exists|i: int| 0 <= i < items.len()
            && #[trigger] alias_in_scope(items[i], file, block, name)
            && items[i] == *item
            && (forall|j: int| 0 <= j < i ==> !alias_in_scope(#[trigger] items[j], file, block, name)),
        None => forall|i: int| 0 <= i < items.len() ==> !alias_in_scope(#[trigger] items[i], file, block, name),
    }
}

#[cfg(verus_only)]
type AliasKey = ((usize, Option<usize>), Seq<u8>);

/// ファイル添字、ブロック添字、別名の UTF-8 バイト列を索引のキーにする。
spec fn scoped_alias_key(item: ResolvedUse) -> AliasKey {
    ((item._file, item.site.block), key_bytes(NameKey { parent: None, name: item.site.alias.word }).1)
}

/// 索引の各束縛が、処理済みの指定のうち同じキーを持つ最初の指定を指すことを表す。
spec fn alias_index_matches(bindings: Map<AliasKey, usize>, items: Seq<ResolvedUse>, stop: int) -> bool {
    &&& 0 <= stop <= items.len()
    &&& forall|i: int| 0 <= i < stop ==> bindings.contains_key(scoped_alias_key(#[trigger] items[i]))
    &&& forall|key: AliasKey| #[trigger] bindings.contains_key(key) ==> {
        let first = bindings[key] as int;
        &&& 0 <= first < stop
        &&& scoped_alias_key(items[first]) == key
        &&& forall|i: int| 0 <= i < first ==> scoped_alias_key(#[trigger] items[i]) != key
    }
}

/// 新しいキーだけを登録すると、次の指定まで索引が最初の位置を保つ。
proof fn advance_alias_index(bindings: Map<AliasKey, usize>, items: Seq<ResolvedUse>, at: usize)
    requires alias_index_matches(bindings, items, at as int), at < items.len(),
    ensures ({
        let key = scoped_alias_key(items[at as int]);
        let next = if bindings.contains_key(key) { bindings } else { bindings.insert(key, at) };
        alias_index_matches(next, items, at + 1)
    }),
{
    let key = scoped_alias_key(items[at as int]);
    let next = if bindings.contains_key(key) { bindings } else { bindings.insert(key, at) };
    assert forall|i: int| 0 <= i <= at implies next.contains_key(scoped_alias_key(#[trigger] items[i])) by {
        if i < at {
            assert(bindings.contains_key(scoped_alias_key(items[i])));
        }
    };
    if !bindings.contains_key(key) {
        assert forall|i: int| 0 <= i < at implies scoped_alias_key(#[trigger] items[i]) != key by {
            assert(bindings.contains_key(scoped_alias_key(items[i])));
        };
    }
}

/// 索引のキーの一致を、正規化ファイル ID を使う既存の別名照合に対応づける。
proof fn alias_keys_agree(targets: &UseTargets, left: int, right: int)
    requires
        targets.covers_project(),
        0 <= left < targets.directives_model().len(),
        0 <= right < targets.directives_model().len(),
    ensures ({
        let items = targets.directives_model();
        (scoped_alias_key(items[left]) == scoped_alias_key(items[right]))
            <==> same_alias(items[left], items[right])
    }),
{
    resolved_uses_share_file(targets, left, right);
}

/// 索引で見つけた先行指定が、線形照合で選ぶ最初の指定であることを示す。
proof fn indexed_first_alias(targets: &UseTargets, bindings: Map<AliasKey, usize>, at: int, previous: Option<usize>)
    requires
        targets.covers_project(),
        0 <= at < targets.directives_model().len(),
        alias_index_matches(bindings, targets.directives_model(), at),
        ({
            let key = scoped_alias_key(targets.directives_model()[at]);
            previous == if bindings.contains_key(key) {
                Some(bindings[key])
            } else { None }
        }),
    ensures ({
        let items = targets.directives_model();
        match previous {
            Some(first) => first_alias(items, at, first as int),
            None => forall|i: int| 0 <= i < at ==> !same_alias(#[trigger] items[i], items[at]),
        }
    }),
{
    let items = targets.directives_model();
    let stop = match previous {
        Some(first) => {
            alias_keys_agree(targets, first as int, at);
            first as int
        },
        None => at,
    };
    assert forall|i: int| 0 <= i < stop implies !same_alias(#[trigger] items[i], items[at]) by {
        alias_keys_agree(targets, i, at);
    };
}

fn lookup_alias<'t, 'p, 'a>(
    index: Option<&AliasIndex>, items: &'t [ResolvedUse<'p, 'a>], file: usize, block: Option<usize>, name: &str,
) -> (found: Option<&'t ResolvedUse<'p, 'a>>)
    requires index matches Some(index) ==> index.valid() && alias_index_matches(index.bindings(), items@, items@.len() as int),
    ensures alias_lookup_matches(items@, file, block, name, found),
{
    let Some(index) = index else {
        return first_binding(items, file, block, name);
    };
    let ghost key = ((file, block), key_bytes(NameKey { parent: None, name }).1);
    if let Some(first) = index.lookup((file, block), name) {
        assert(alias_in_scope(items@[first as int], file, block, name));
        Some(&items[first])
    } else {
        assert forall|i: int| 0 <= i < items@.len() implies !alias_in_scope(#[trigger] items@[i], file, block, name) by {
            assert(index.bindings().contains_key(scoped_alias_key(items@[i])));
            assert(scoped_alias_key(items@[i]) != key);
        };
        None
    }
}

fn first_binding<'t, 'p, 'a>(
    items: &'t [ResolvedUse<'p, 'a>], file: usize, block: Option<usize>, name: &str,
) -> (found: Option<&'t ResolvedUse<'p, 'a>>)
    ensures alias_lookup_matches(items@, file, block, name, found),
{
    let mut i = 0;
    while i < items.len()
        invariant
            i <= items@.len(),
            forall|j: int| 0 <= j < i ==> !alias_in_scope(#[trigger] items@[j], file, block, name),
        decreases items@.len() - i,
    {
        let item = &items[i];
        if item._file == file && item.site.block == block
            && (NameKey { parent: None, name: item.site.alias.word })
                .same_name(NameKey { parent: None, name })
        {
            assert(alias_in_scope(*item, file, block, name));
            return Some(item);
        }
        i += 1;
    }
    None
}

spec fn is_namespace_block(form: NamedForm, block: usize) -> bool {
    form.head is Namespace && form.form == block && form.block is None
}

fn find_namespace<'a>(parsed: &NamedBuildCircuit<'a>, block: usize) -> (path: Option<&'a str>)
    ensures match path {
        Some(path) => exists|i: int| 0 <= i < parsed.names@.len()
            && #[trigger] is_namespace_block(parsed.names@[i], block)
            && parsed.names@[i].name.word == path,
        None => forall|i: int| 0 <= i < parsed.names@.len() ==>
            !is_namespace_block(#[trigger] parsed.names@[i], block),
    },
{
    let mut i = 0;
    while i < parsed.names.len()
        invariant
            i <= parsed.names@.len(),
            forall|j: int| 0 <= j < i ==> !is_namespace_block(#[trigger] parsed.names@[j], block),
        decreases parsed.names@.len() - i,
    {
        let form = &parsed.names[i];
        if matches!(form.head, Head::Namespace) && form.form == block && form.block.is_none() {
            assert(is_namespace_block(*form, block));
            return Some(form.name.word);
        }
        i += 1;
    }
    None
}

spec fn allows_direct(table: &DeclarationTable, item: ResolvedUse) -> bool {
    forall|existing: AbsoluteTarget| #[trigger] direct_target_matches(table, alias_key(item), Some(existing))
        ==> same_target(existing, item.target)
}

spec fn disposition_matches(items: Seq<ResolvedUse>, at: int, disposition: AliasDisposition) -> bool {
    &&& 0 <= at < items.len()
    &&& match disposition {
        AliasDisposition::Binding =>
            forall|i: int| 0 <= i < at ==> !same_alias(#[trigger] items[i], items[at]),
        AliasDisposition::Duplicate { first } =>
            first_alias(items, at, first as int) && same_target(items[first as int].target, items[at].target),
    }
}

spec fn checked_prefix(
    table: &DeclarationTable, items: Seq<ResolvedUse>, dispositions: Seq<AliasDisposition>,
) -> bool {
    &&& dispositions.len() <= items.len()
    &&& forall|i: int| 0 <= i < dispositions.len() ==>
        disposition_matches(items, i, #[trigger] dispositions[i]) && allows_direct(table, items[i])
}

/// 同じスコープと別名の指定が同じ対象を指し、直接宣言と子名前空間にも衝突しないことを表す。
pub closed spec fn use_aliases_acceptable(targets: &UseTargets) -> bool {
    let items = targets.directives_model();
    let table = targets.exports_model().declarations_model();
    alias_prefix_acceptable(&table, items, items.len() as int)
}

spec fn alias_prefix_acceptable(table: &DeclarationTable, items: Seq<ResolvedUse>, stop: int) -> bool {
    &&& 0 <= stop <= items.len()
    &&& forall|i: int| 0 <= i < stop ==> allows_direct(table, #[trigger] items[i])
    &&& forall|i: int, j: int| 0 <= i < j < stop
        && #[trigger] same_alias(items[i], items[j])
        ==> same_target(items[i].target, items[j].target)
}

proof fn compatible_pair(items: Seq<ResolvedUse>, decisions: Seq<AliasDisposition>, i: int, j: int)
    requires
        0 <= i < j < decisions.len() <= items.len(),
        same_alias(items[i], items[j]),
        disposition_matches(items, i, decisions[i]),
        disposition_matches(items, j, decisions[j]),
    ensures same_target(items[i].target, items[j].target),
{
    assert(decisions[j] is Duplicate);
    let f = decisions[j]->Duplicate_first;
    assert(f <= i);
    if f < i {
        assert(same_alias(items[f as int], items[i]));
        assert(decisions[i] is Duplicate);
        let g = decisions[i]->Duplicate_first;
        assert(g <= f);
        assert(same_alias(items[g as int], items[j]));
        assert(f <= g);
    }
}

/// 束縛と警告を記録した範囲では、すべての指定が衝突の規則に従う。
proof fn checked_alias_prefix_is_acceptable(
    table: &DeclarationTable, items: Seq<ResolvedUse>, dispositions: Seq<AliasDisposition>,
)
    requires checked_prefix(table, items, dispositions),
    ensures alias_prefix_acceptable(table, items, dispositions.len() as int),
{
    assert forall|i: int| 0 <= i < dispositions.len()
        implies allows_direct(table, #[trigger] items[i]) by {
        assert(disposition_matches(items, i, dispositions[i]));
    };
    assert forall|i: int, j: int| 0 <= i < j < dispositions.len()
        && #[trigger] same_alias(items[i], items[j])
        implies same_target(items[i].target, items[j].target) by {
        compatible_pair(items, dispositions, i, j);
    };
}

/// 各指定に対して、衝突しない束縛または最初の指定を指す重複警告があることを表す。
pub closed spec fn use_aliases_match(targets: &UseTargets, aliases: UseAliases) -> bool {
    &&& *aliases.targets == *targets
    &&& aliases.dispositions@.len() == targets.directives_model().len()
    &&& checked_prefix(&targets.exports_model().declarations_model(), targets.directives_model(), aliases.dispositions@)
}

proof fn first_alias_position_agrees(items: Seq<ResolvedUse>, at: int, left: int, right: int)
    requires first_alias(items, at, left), first_alias(items, at, right),
    ensures left == right,
{
    if left < right {
        assert(!same_alias(items[left], items[at]));
    } else if right < left {
        assert(!same_alias(items[right], items[at]));
    }
}

/// 同じ解決済みの指定から得た束縛と警告は、指定の順序と最初の指定の位置が一致する。
pub proof fn use_alias_dispositions_agree(targets: &UseTargets, left: UseAliases, right: UseAliases)
    requires use_aliases_match(targets, left), use_aliases_match(targets, right),
    ensures left.dispositions_model() == right.dispositions_model(),
{
    let items = targets.directives_model();
    let a = left.dispositions_model();
    let b = right.dispositions_model();
    assert forall|i: int| 0 <= i < items.len() implies #[trigger] a[i] == #[trigger] b[i] by {
        assert(disposition_matches(items, i, a[i]) && disposition_matches(items, i, b[i]));
        match (a[i], b[i]) {
            (AliasDisposition::Duplicate { first: l }, AliasDisposition::Duplicate { first: r }) => {
                first_alias_position_agrees(items, i, l as int, r as int);
            },
            (AliasDisposition::Binding, AliasDisposition::Duplicate { first }) |
            (AliasDisposition::Duplicate { first }, AliasDisposition::Binding) => {
                assert(!same_alias(items[first as int], items[i]));
            },
            _ => {},
        }
    };
    assert(a =~= b);
}

/// 診断が最初に衝突した指定を指すことを表す。
///
/// 同じ指定で二種類の衝突が起きる場合は、直接宣言または子名前空間との衝突を選ぶ。
pub closed spec fn alias_conflict_evidence(targets: &UseTargets, error: UseAliasConflict) -> bool {
    let items = targets.directives_model();
    let table = targets.exports_model().declarations_model();
    exists|at: int| #[trigger] alias_conflict_at(&table, items, at, error)
}

spec fn alias_conflict_at(table: &DeclarationTable, items: Seq<ResolvedUse>, at: int, error: UseAliasConflict) -> bool {
    &&& 0 <= at < items.len()
    &&& alias_prefix_acceptable(table, items, at)
    &&& match error {
        UseAliasConflict::BetweenUses { later, first } =>
            items[at] == *later && allows_direct(table, *later) && !same_target(first.target, later.target)
                && (exists|before: int| #[trigger] first_alias(items, at, before) && items[before] == *first),
        UseAliasConflict::Direct { directive, existing } => items[at] == *directive
            && selected_direct_target_matches(table, alias_key(*directive), Some(existing))
            && !same_target(existing, directive.target),
    }
}

proof fn alias_conflict_blocks_prefix(
    table: &DeclarationTable, items: Seq<ResolvedUse>, at: int, end: int, error: UseAliasConflict,
)
    requires alias_conflict_at(table, items, at, error), at < end,
    ensures !alias_prefix_acceptable(table, items, end),
{
    if alias_prefix_acceptable(table, items, end) {
        match error {
            UseAliasConflict::BetweenUses { first, .. } => {
                let other = choose|before: int| #[trigger] first_alias(items, at, before) && items[before] == *first;
                assert(same_target(items[other].target, items[at].target));
            },
            UseAliasConflict::Direct { .. } => {
                assert(allows_direct(table, items[at]));
            },
        }
    }
}

proof fn first_alias_conflict_position(targets: &UseTargets, left: UseAliasConflict, right: UseAliasConflict)
    -> (position: int)
    requires alias_conflict_evidence(targets, left), alias_conflict_evidence(targets, right),
    ensures
        alias_conflict_at(&targets.exports_model().declarations_model(), targets.directives_model(), position, left),
        alias_conflict_at(&targets.exports_model().declarations_model(), targets.directives_model(), position, right),
{
    let items = targets.directives_model();
    let table = &targets.exports_model().declarations_model();
    let a = choose|at: int| #[trigger] alias_conflict_at(table, items, at, left);
    let b = choose|at: int| #[trigger] alias_conflict_at(table, items, at, right);
    if a < b {
        alias_conflict_blocks_prefix(table, items, a, b, left);
    } else if b < a {
        alias_conflict_blocks_prefix(table, items, b, a, right);
    }
    a
}

/// 同じ解決済みの指定から得た衝突診断は、主範囲と相手の範囲を含む値全体が一致する。
pub proof fn alias_conflicts_agree(targets: &UseTargets, left: UseAliasConflict, right: UseAliasConflict)
    requires targets.covers_project(), alias_conflict_evidence(targets, left), alias_conflict_evidence(targets, right),
    ensures left == right,
{
    let at = first_alias_conflict_position(targets, left, right);
    let items = targets.directives_model();
    let table = &targets.exports_model().declarations_model();
    match (left, right) {
        (UseAliasConflict::BetweenUses { first: a, .. }, UseAliasConflict::BetweenUses { first: b, .. }) => {
            let l = choose|before: int| #[trigger] first_alias(items, at, before) && items[before] == *a;
            let r = choose|before: int| #[trigger] first_alias(items, at, before) && items[before] == *b;
            first_alias_position_agrees(items, at, l, r);
        },
        (
            UseAliasConflict::Direct { existing: a, .. },
            UseAliasConflict::Direct { existing: b, .. },
        ) => {
            targets.declarations_cover_project();
            selected_direct_targets_agree(&targets.project_model(), table, alias_key(items[at]), Some(a), Some(b));
        },
        _ => {
            assert(allows_direct(table, items[at]));
        },
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 元の指定、参照先、診断の範囲を含む解決済み一覧を返す。
    pub fn directives(&self) -> (directives: &'t [ResolvedUse<'p, 'a>])
        ensures directives@ == self.directives_model(),
    {
        self.targets.directives()
    }

    /// 解決済み一覧の論理上の列を返す。
    pub closed spec fn directives_model(&self) -> Seq<ResolvedUse<'p, 'a>> {
        self.targets.directives_model()
    }

    /// 解決済み一覧と同じ順で、各指定の束縛または重複警告を返す。
    pub fn dispositions(&self) -> (dispositions: &[AliasDisposition])
        ensures dispositions@ == self.dispositions_model(),
    {
        self.dispositions.as_slice()
    }

    /// 束縛と重複警告の論理上の列を返す。
    pub closed spec fn dispositions_model(&self) -> Seq<AliasDisposition> {
        self.dispositions@
    }

    pub(super) fn into_dispositions(self) -> (dispositions: Vec<AliasDisposition>)
        ensures dispositions@ == self.dispositions_model(),
    {
        self.dispositions
    }

    /// 名前の検索に使う宣言表と別名が、構文済みプロジェクトに対応することを表す。
    pub closed spec fn can_resolve(&self) -> bool {
        &&& self.targets.covers_project()
        &&& self.targets.exports_model().declarations_model().well_formed()
        &&& use_aliases_match(self.targets, *self)
        &&& (self.index matches Some(index) ==> index.valid()
            && alias_index_matches(index.bindings(), self.directives_model(), self.directives_model().len() as int))
    }

    /// 無修飾名の検索結果と参照元スコープ、別名、共有宣言表との対応を表す。
    pub closed spec fn unqualified_resolution_matches(
        &self, file: usize, block: Option<usize>, name: &str,
        result: Result<Option<UnqualifiedTarget>, ReferenceScopeError>,
    ) -> bool {
        let circuits = self.targets.project_model().circuits_model();
        match result {
            Err(error) => self.scope_matches(file, block, Err(error)),
            Ok(found) => file < circuits.len() && {
                let names = circuits[file as int].names@;
                exists|namespace: Option<&str>| #[trigger] scope_namespace_matches(names, block, namespace)
                    && self.unqualified_binding_matches(file, block, name, namespace, found)
            },
        }
    }

    spec fn scope_matches(
        &self, file: usize, block: Option<usize>, result: Result<Option<&str>, ReferenceScopeError>,
    ) -> bool {
        let circuits = self.targets.project_model().circuits_model();
        match result {
            Err(ReferenceScopeError::UnknownFile) => file >= circuits.len(),
            Err(ReferenceScopeError::UnknownBlock) =>
                file < circuits.len() && (block matches Some(index) && {
                    let names = circuits[file as int].names@;
                    forall|i: int| 0 <= i < names.len() ==> !is_namespace_block(#[trigger] names[i], index)
                }),
            Ok(namespace) => file < circuits.len()
                && scope_namespace_matches(circuits[file as int].names@, block, namespace),
        }
    }

    spec fn unqualified_binding_matches(
        &self, file: usize, block: Option<usize>, name: &str, namespace: Option<&str>,
        found: Option<UnqualifiedTarget>,
    ) -> bool {
        let items = self.targets.directives_model();
        let table = self.targets.exports_model().declarations_model();
        match found {
            Some(UnqualifiedTarget::Alias(item)) => {
                &&& alias_lookup_matches(items, file, block, name, Some(item))
                &&& key_bytes(alias_key(*item)) == key_bytes(NameKey { parent: namespace, name })
                &&& allows_direct(&table, *item)
                &&& absolute_resolution_evidence(&self.targets.exports_model(),
                    item.site.reference.word, item.site.namespace, Ok(item.target))
            },
            Some(UnqualifiedTarget::Direct(target)) => alias_lookup_matches(items, file, block, name, None)
                && direct_target_matches(&table, NameKey { parent: namespace, name }, Some(target)),
            None => alias_lookup_matches(items, file, block, name, None)
                && direct_target_matches(&table, NameKey { parent: namespace, name }, None),
        }
    }

    /// 無修飾名が指す独立宣言または子名前空間を検索する。
    ///
    /// `file` は解析済みプロジェクトのソース一覧での添字で、`block` は同じファイルの構文木で
    /// 名前空間フォームを指す添字である。ファイル直下では `None` を渡す。
    /// `name` には字句解析で無修飾名と判定した綴りを渡す。
    /// 別名はブロック全体で有効であり、指定と参照の出現順に依存しない。
    /// 別名があれば最初の `use` を返す。どちらの束縛もなければ `Ok(None)` を返す。
    /// 組み込みの探索と使用位置で許される宣言種別の判定は、呼び出し側で行う。
    ///
    /// # Errors
    ///
    /// ファイルまたは名前空間ブロックが構文済みプロジェクトに存在しない場合はエラーを返す。
    pub fn resolve_unqualified<'q>(
        &'q self, file: usize, block: Option<usize>, name: &'q str,
    ) -> (result: Result<Option<UnqualifiedTarget<'t, 'p, 'a, 'q>>, ReferenceScopeError>)
        requires self.can_resolve(),
        ensures self.unqualified_resolution_matches(file, block, name, result),
    {
        let namespace = self.scope_namespace(file, block)?;
        Ok(self.lookup_in_scope(file, block, namespace, name))
    }

    fn scope_namespace(
        &self, file: usize, block: Option<usize>,
    ) -> (result: Result<Option<&'a str>, ReferenceScopeError>)
        ensures self.scope_matches(file, block, result),
    {
        let circuits = self.targets.project().circuits();
        if file >= circuits.len() {
            return Err(ReferenceScopeError::UnknownFile);
        }
        let parsed = &circuits[file];
        let namespace = if let Some(index) = block {
            let Some(path) = find_namespace(parsed, index) else {
                return Err(ReferenceScopeError::UnknownBlock);
            };
            Some(path)
        } else {
            None
        };
        assert(scope_namespace_matches(parsed.names@, block, namespace));
        Ok(namespace)
    }

    fn lookup_in_scope<'q>(
        &'q self, file: usize, block: Option<usize>, namespace: Option<&'q str>, name: &'q str,
    ) -> (found: Option<UnqualifiedTarget<'t, 'p, 'a, 'q>>)
        requires self.can_resolve(), self.scope_matches(file, block, Ok(namespace)),
        ensures self.unqualified_binding_matches(file, block, name, namespace, found),
    {
        if let Some(item) = lookup_alias(self.index.as_ref(), self.directives(), file, block, name) {
            proof {
                let items = self.directives_model();
                let i = choose|i: int| 0 <= i < items.len()
                    && #[trigger] alias_in_scope(items[i], file, block, name)
                    && items[i] == *item
                    && (forall|j: int| 0 <= j < i ==> !alias_in_scope(#[trigger] items[j], file, block, name));
                if let Some(index) = block {
                    let names = self.targets.project_model().circuits_model()[file as int].names@;
                    let path = namespace->Some_0;
                    let j = choose|j: int| 0 <= j < names.len()
                        && #[trigger] is_namespace_block(names[j], index) && names[j].name.word == path;
                    assert(names[j].form == index);
                }
                resolved_use_evidence(self.targets, i, namespace);
                assert(disposition_matches(items, i, self.dispositions@[i]));
            }
            return Some(UnqualifiedTarget::Alias(item));
        }
        let table = self.targets.exports().declarations();
        if let Some(target) = table.direct_target(NameKey { parent: namespace, name }) {
            Some(UnqualifiedTarget::Direct(target))
        } else {
            None
        }
    }
}

spec fn scope_namespace_matches(names: Seq<NamedForm>, block: Option<usize>, namespace: Option<&str>) -> bool {
    match (block, namespace) {
        (None, None) => true,
        (Some(block), Some(path)) => exists|i: int| 0 <= i < names.len()
            && #[trigger] is_namespace_block(names[i], block) && names[i].name.word == path,
        _ => false,
    }
}

/// 解決済みの `use` を照合し、別名の束縛と重複警告を返す。
///
/// [`index_use_targets`](super::index_use_targets) で得た指定を渡す。
/// 同じファイルとブロックで、同じ対象を同じ別名に割り当てた後続の指定には警告を出す。
/// 警告の関連位置は最初の指定を指す。名前空間内の直接宣言と子名前空間も照合する。
///
/// # Errors
///
/// 指定をソース順に照合し、最初に衝突を起こした指定と相手の位置を返す。
/// 一つの指定で両方の衝突が起きた場合は、直接宣言または子名前空間との衝突を返す。
pub fn check_use_aliases<'t, 'p, 'a>(targets: &'t UseTargets<'p, 'a>)
    -> (result: Result<UseAliases<'t, 'p, 'a>, UseAliasConflict<'t, 'p, 'a>>)
    requires targets.covers_project(), targets.exports_model().declarations_model().well_formed(),
    ensures
        result.is_ok() <==> use_aliases_acceptable(targets),
        match result {
            Ok(aliases) => use_aliases_match(targets, aliases) && aliases.can_resolve(),
            Err(error) => alias_conflict_evidence(targets, error),
        },
{
    let items = targets.directives();
    let table = targets.exports().declarations();
    let mut dispositions = Vec::new();
    let mut index = Some(AliasIndex::new());
    let mut at = 0;
    while at < items.len()
        invariant
            targets.covers_project(),
            items@ == targets.directives_model(),
            *table == targets.exports_model().declarations_model(),
            table.well_formed(),
            at == dispositions@.len(),
            checked_prefix(table, items@, dispositions@),
            index matches Some(index) ==> index.valid() && alias_index_matches(index.bindings(), items@, at as int),
        decreases items@.len() - at,
    {
        let directive = &items[at];
        let direct = table.direct_target(NameKey { parent: directive.site.namespace, name: directive.site.alias.word });
        let ghost direct_model = direct;
        if let Some(existing) = direct {
            if !existing.is_same_target(&directive.target) {
                let error = UseAliasConflict::Direct { directive, existing };
                proof { checked_alias_prefix_is_acceptable(table, items@, dispositions@); }
                assert(alias_conflict_at(table, items@, at as int, error));
                assert(alias_conflict_evidence(targets, error));
                assert(!allows_direct(table, *directive));
                assert(!use_aliases_acceptable(targets));
                return Err(error);
            }
        }
        assert(allows_direct(table, *directive)) by {
            assert forall|existing: AbsoluteTarget|
                #[trigger] direct_target_matches(table, alias_key(*directive), Some(existing))
                implies same_target(existing, directive.target) by {
                direct_targets_agree(table, alias_key(*directive), direct_model, Some(existing));
            };
        }
        let mut indexed = None;
        if let Some(ref mut bindings) = index {
            let ghost prior = bindings.bindings();
            indexed = bindings.insert_if_absent((directive._file, directive.site.block), directive.site.alias.word, at);
            proof {
                if let Some(previous) = indexed {
                    indexed_first_alias(targets, prior, at as int, previous);
                    advance_alias_index(prior, items@, at);
                }
            }
        }
        let first = if let Some(previous) = indexed {
            previous
        } else {
            // 部分索引から名前を引くと登録漏れが生じるため、以降は線形検索を使う。
            index = None;
            find_first(items, at)
        };
        let disposition = if let Some(first) = first {
            let previous = &items[first];
            if !previous.target.is_same_target(&directive.target) {
                let error = UseAliasConflict::BetweenUses { later: directive, first: previous };
                proof { checked_alias_prefix_is_acceptable(table, items@, dispositions@); }
                assert(alias_conflict_at(table, items@, at as int, error));
                assert(alias_conflict_evidence(targets, error));
                assert(same_alias(*previous, *directive));
                assert(!use_aliases_acceptable(targets));
                return Err(error);
            }
            AliasDisposition::Duplicate { first }
        } else {
            AliasDisposition::Binding
        };
        assert(disposition_matches(items@, at as int, disposition));
        dispositions.push(disposition);
        at += 1;
    }
    proof { checked_alias_prefix_is_acceptable(table, items@, dispositions@); }
    Ok(UseAliases { targets, dispositions, index })
}

} // verus!

impl core::fmt::Debug for UseAliases<'_, '_, '_> {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.debug_struct("UseAliases")
            .field("targets", &self.targets)
            .field("dispositions", &self.dispositions)
            .finish()
    }
}
