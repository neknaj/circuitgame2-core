//! プロジェクトに渡すソースの識別子と種別を扱う。

mod analysis;
mod basis;
mod bit_selection;
mod circuits;
mod concatenation;
mod declarations;
mod exports;
mod literal_width;
mod name_keys;
mod path;
mod resolution;
mod signatures;
mod sources;
mod use_aliases;
mod use_targets;
mod widths;

pub use bit_selection::{BitSelectionError, check_bit_selection};
#[cfg(verus_only)]
pub use bit_selection::{bit_selection_matches, selected_bit_in_range};
pub use concatenation::{ConcatWidthError, check_concat_width};
#[cfg(verus_only)]
pub use concatenation::{concat_prefix_width, concat_width_matches};
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
#[cfg(verus_only)]
pub use circuits::{
    circuit_project_accepts, circuit_project_error, circuit_project_failure, parsed_circuit_matches,
};
pub use declarations::{
    DeclarationTable, LocatedName, NameConflict, NameConflictKind, index_declarations,
};
#[cfg(verus_only)]
pub use declarations::{
    declaration_table_matches, location_in_source, name_conflict_evidence, project_declares,
    project_names_conflict,
};
pub use exports::{ExportError, ExportTable, index_exports};
#[cfg(verus_only)]
pub use exports::{export_error_evidence, export_table_matches, project_exports_valid};
pub use name_keys::NameKey;
pub use path::{PathError, SourceKind, VirtualPath, normalize_path};
#[cfg(verus_only)]
pub use path::{canonical_components, normalized_path, source_kind_of};
pub use resolution::{AbsoluteResolutionError, AbsoluteTarget};
#[cfg(verus_only)]
pub use resolution::{
    absolute_resolution_evidence, declaration_visible_from, direct_target_matches, same_target,
};
pub use sources::{ProjectSource, SourceSetError, SourceSnapshot, collect_sources};
#[cfg(verus_only)]
pub use sources::{project_sources_match, source_set_error, valid_source_snapshots};
#[cfg(verus_only)]
pub use use_aliases::port_types_equal;
pub use use_aliases::{
    AliasConflict, AliasDisposition, DefinitionBatchError, DefinitionBinding, DefinitionPosition,
    DefinitionReferenceError, DefinitionReferenceReason, DefinitionReferenceSite,
    IndexedDefinitionBinding, OwnedUseAliasConflict, ReferenceScopeError, RelativeResolutionError,
    RelativeTarget, ResolvedDefinitionReference, UnqualifiedTarget, UseAliasConflict, UseAliases,
    check_use_aliases,
};
pub use use_aliases::{FuncArityError, FuncCallArity, FuncCallTarget};
pub use use_aliases::{FuncLiteralError, FuncLiteralWidths};
pub use use_aliases::{
    DefinitionDriver, FuncDriverError, FuncDriverResult, FuncDrivers, OutputDriver,
};
pub use use_aliases::{
    BoundFuncSignal, FuncSignalReason, FuncWiring, FuncWiringError, FuncWiringResult,
};
pub use use_aliases::{ResolvedPortType, TypedPort, TypedRoutineSignature, TypedSignatureError};
#[cfg(verus_only)]
pub use use_aliases::{alias_conflict_evidence, use_aliases_acceptable, use_aliases_match};
pub use use_targets::{ResolvedUse, UseSite, UseTargetError, UseTargets, index_use_targets};
#[cfg(verus_only)]
pub use use_targets::{use_target_error_evidence, use_targets_match};
