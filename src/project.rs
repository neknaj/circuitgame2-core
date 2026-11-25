//! プロジェクトに渡すソースの識別子と種別を扱う。

mod analysis;
mod basis;
mod bit_selection;
mod circuits;
mod concatenation;
mod declarations;
mod editor_recovery;
mod exports;
mod literal_width;
mod module_parts;
mod name_keys;
mod path;
mod resolution;
mod signatures;
mod source_indexes;
mod sources;
mod storage_declarations;
mod structure_declarations;
mod use_aliases;
mod use_targets;
mod widths;

pub use bit_selection::{BitSelectionError, check_bit_selection, select_bits};
#[cfg(verus_only)]
pub use bit_selection::{bit_selection_matches, selected_bit_in_range, selected_bits_match, selected_bits_values};
pub use concatenation::{ConcatResultWidthError, ConcatWidthError, check_concat_result_width, check_concat_width};
#[cfg(verus_only)]
pub use concatenation::{
    concat_prefix_width, concat_result_width_matches, concat_result_widths_agree, concat_width_matches,
    concat_width_results_agree,
};
pub use literal_width::{CircuitLiteralWidthError, check_circuit_literal_width};
#[cfg(verus_only)]
pub use literal_width::circuit_literal_width_matches;

#[cfg(verus_only)]
pub use signatures::routine_signature_evidence;
pub use signatures::{
    CheckedRoutineSignature, OutputSource, PortDirection, RoutineSignatureError, SharedPortType,
    check_routine_signature,
};
#[cfg(verus_only)]
pub use widths::routine_port_widths_evidence;
pub use widths::{
    CheckedPort, DeclaredPortType, PortWidthError, PortWidthErrorKind, RoutinePortWidths,
    check_routine_port_widths,
};

#[cfg(verus_only)]
pub use analysis::definition_analysis_evidence;
pub use analysis::{
    DefinitionAnalysis, DefinitionAnalysisError, UseAliasReport, analyze_definitions,
};
pub use basis::{CircuitBasisError, validate_circuit_basis};
#[cfg(verus_only)]
pub use basis::{basis_result_evidence, circuit_basis_valid};
pub use circuits::{
    CircuitProject, CircuitProjectError, CircuitProjectFailure, parse_circuit_project,
    parse_circuit_project_with_recovery,
};
pub(crate) use circuits::read_source_span;
#[cfg(verus_only)]
pub use circuits::{
    circuit_project_accepts, circuit_project_error, circuit_project_failure, parsed_circuit_matches,
};
pub use declarations::{
    DeclarationTable, LocatedName, MixedDeclarationTable, NameConflict, NameConflictKind, ProjectDeclaration,
    ProjectDeclarationKind, index_declarations, index_mixed_declarations,
};
#[cfg(verus_only)]
pub use declarations::{
    declaration_table_matches, location_in_source, mixed_declaration_origin, mixed_declaration_table_matches,
    mixed_name_conflict_evidence, mixed_name_conflicts_agree,
    mixed_project_names_conflict, name_conflict_evidence, project_declares,
    project_names_conflict,
};
pub use editor_recovery::{
    CircuitEditorFile, CircuitEditorProject, ObservedCircuitBinding, ObservedCircuitBindingKind,
    ModulePartCandidates, PartialCircuitDeclarations, RecoveredDeclarationQuery, inspect_circuit_file, inspect_circuit_project,
};
pub use exports::{ExportError, ExportTable, index_exports};
#[cfg(verus_only)]
pub use editor_recovery::circuit_editor_source;
#[cfg(verus_only)]
pub use exports::{export_error_evidence, export_table_matches, project_exports_valid};
pub use name_keys::NameKey;
pub use module_parts::{ModuleBody, ModuleBodyPosition, ModuleDefinition, ModulePartBinding, ModulePartError, ModulePartsError};
pub use use_aliases::{ModuleDriverError, ModuleDrivers};
pub use use_aliases::{BoundModuleSignal, ModuleWiring, ModuleWiringError};
pub use use_aliases::{ModuleAliasCycleStep, ModuleAliasSource, ModuleAliasTypes, ModuleAliasTypesError,
    ModuleConcat, ModuleConcatOperand, ModuleConcats, ModuleConcatsError,
    CheckedModuleCall, ModuleCalls, ModuleCallsError, ModuleInferredCallError, PrimitiveModuleError,
    ModuleOutputTypes, ModuleOutputTypesError,
    ModuleRootTypes, ModuleRootTypesError, ModuleSelection, ModuleSelections, ModuleSelectionsError, ModuleTypeSources};
pub use use_aliases::{ClockedEndpointError, ClockedModuleVm, ClockedModuleVmError, ClockedModuleVmLimits};
pub use use_aliases::{VramOutputError, VramTarget};
pub use use_aliases::{ClockedVramVm, VramDeclaration, VramSetupError, VramView};
#[cfg(verus_only)]
pub use use_aliases::ClockedModuleObservation;
pub use use_aliases::ModuleSettlingHint;
pub use use_aliases::{ClockedArgumentWiringError, ClockedModuleOutputs, ClockedModuleOutputsError};
pub use use_aliases::{ClockedDriverBitsError, clocked_driver_bits};
#[cfg(verus_only)]
pub use use_aliases::{clocked_driver_bit, clocked_driver_bits_result, clocked_driver_port_model, clocked_driver_selection_matches};
pub use use_aliases::{ClockedDefinitionLayoutError, ClockedLinkPlan, ClockedModuleError, ClockedPlanError, ClockedStorageLayout, ClockedStorageLayoutError, ClockedStoragePlacement, ClockedWireDriver, plan_clocked_links};
#[cfg(verus_only)]
pub use use_aliases::{clocked_link_plan_result, clocked_regions_cover, clocked_wire_at, clocked_wire_cycle,
    clocked_wire_solutions_agree, clocked_wires_match};
pub use use_aliases::{ModuleCallInputs, ModuleCallInputsError, ModuleCallPorts, ModuleCallPortsError,
    ModuleCallSignature, ModuleCallSignatureError, ModuleCallTarget, StorageSignature, StorageSignatureError};
pub use path::{PathError, SourceKind, VirtualPath, normalize_path};
#[cfg(verus_only)]
pub use path::{canonical_components, normalized_path, source_kind_of};
pub use resolution::{AbsoluteResolutionError, AbsoluteTarget};
#[cfg(verus_only)]
pub use resolution::{
    absolute_resolution_evidence, declaration_visible_from, direct_target_matches, same_target,
};
pub use source_indexes::{
    ParsedProjectSources, ProjectFileSyntaxError, ProjectSourceIndex, ProjectSourceParseError, parse_project_sources,
};
#[cfg(verus_only)]
pub use source_indexes::{
    project_file_diagnostic_origin, project_source_index_matches, project_source_parse_error,
    project_source_parse_errors_agree, project_source_set_accepts,
};
pub use sources::{ProjectSource, SourceSetError, SourceSnapshot, collect_sources};
pub use storage_declarations::{StorageDeclaration, check_storage_declaration};
#[cfg(verus_only)]
pub use storage_declarations::storage_declaration_result;
pub use structure_declarations::{
    DeclaredField, DeclaredFieldType, StructureDeclaration, StructureNumber, StructureNumberError, StructureNumberErrorKind,
    check_structure_declaration,
};
#[cfg(verus_only)]
pub use structure_declarations::structure_declaration_result;
#[cfg(verus_only)]
pub use sources::{first_source_set_error, project_sources_match, source_set_error, source_set_errors_agree, valid_source_snapshots};
#[cfg(verus_only)]
pub use use_aliases::port_types_equal;
pub use use_aliases::{
    AliasConflict, AliasDisposition, DefinitionBatchError, DefinitionBinding, DefinitionPosition, DefinitionReferences,
    DefinitionReferenceError, DefinitionReferenceReason, DefinitionReferenceSite,
    IndexedDefinitionBinding, OwnedUseAliasConflict, ReferenceScopeError, RelativeResolutionError,
    RelativeTarget, ResolvedDefinitionReference, UnqualifiedTarget, UseAliasConflict, UseAliases,
    FunctionCallSite, FunctionExpansionError, FunctionExpansionOrder,
    check_use_aliases,
};
pub use use_aliases::{
    CallInputError, CallInputReason, CallPortType, CheckedCallInputs, FuncArityError, FuncCallArity, FuncCallInputsError, FuncCallSignature, FuncCallSignatureError,
    FuncCallOutputError, FuncCallOutputTypes,
    FuncCallTarget, TypedFuncCall,
};
pub use use_aliases::{
    ResolvedStructure, ResolvedStructureEntry, ResolvedStructureField, ResolvedStructures,
    StructureExpressionTypeError,
    StructureFieldType, StructureIndexError, StructureLayout, StructureLayoutError, StructureLayoutField, StructureLayouts,
    StructurePlacementError, StructurePosition, StructureResolutionError, StructureTypeError, StructureTypeReference, StructureOperation, StructureOperationError, TypedStructureOperation,
};
pub use use_aliases::{FuncLiteralError, FuncLiteralWidths};
pub use use_aliases::{FuncAtomTypeError, FuncAtomTypes, SignalType};
pub use use_aliases::{CheckedBitSelection, SelectionArgument, SelectionArgumentError};
pub use use_aliases::{FuncSignalTypeError, FuncSignalTypes};
pub use use_aliases::LoweredSingleBitFunc;
pub use use_aliases::{
    BitFuncError, BitFuncLowerError, CheckedBitFunc, ExpandFunctionsError, ExpandedFunctions, FunctionBuildDiagnostic,
    LoweredBitFunc, UnsupportedBitFunc,
};
#[cfg(verus_only)]
pub use use_aliases::{
    bit_func_evaluation, bit_func_lowering_preserves_evaluation, bit_func_evaluations_agree,
    checked_bit_func_available, lowered_bit_func_result, port_values,
};
#[cfg(verus_only)]
pub use use_aliases::{
    single_bit_evaluation_outputs_agree, single_bit_evaluation_result_agrees, single_bit_lowering_matches,
    single_bit_lowering_outputs_match,
    single_bit_lowering_preserves_evaluation, single_bit_lowering_preserves_outputs_evaluation,
    single_bit_source_evaluation, single_bit_source_evaluations_agree, single_bit_source_outputs_evaluation,
    single_bit_source_outputs_evaluations_agree,
};

pub use use_aliases::clocked_nor_settling_bound;
#[cfg(verus_only)]
pub use use_aliases::{clocked_nor_bound_matches, clocked_nor_depths, clocked_nor_has_cycle, clocked_nor_states_settle, fixed_nor_states};
pub use use_aliases::{CheckedSingleBitFunc, SingleBitDefinition, SingleBitFuncError, SingleBitOperand, SingleBitRhs, UnsupportedSingleBitFunc};
pub use use_aliases::{
    DefinitionDriver, FuncDriverError, FuncDriverResult, FuncDrivers, OutputDriver,
};
pub use use_aliases::{
    BoundFuncSignal, FuncSignalReason, FuncWiring, FuncWiringError, FuncWiringResult,
};
pub use use_aliases::{ResolvedPortType, TypedPort, TypedRoutineSignature, TypedSignatureError};
#[cfg(verus_only)]
pub use use_aliases::{alias_conflict_evidence, alias_conflicts_agree, use_alias_dispositions_agree, use_aliases_acceptable, use_aliases_match};
pub use use_targets::{ResolvedUse, UseSite, UseTargetError, UseTargets, index_use_targets};
#[cfg(verus_only)]
pub use use_targets::{use_target_error_evidence, use_targets_match};
