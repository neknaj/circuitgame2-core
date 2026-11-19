//! プロジェクトに渡すソースの識別子と種別を扱う。

mod circuits;
mod declarations;
mod exports;
mod name_keys;
mod path;
mod resolution;
mod sources;
mod use_aliases;
mod use_targets;

pub use circuits::{CircuitProject, CircuitProjectError, parse_circuit_project};
#[cfg(verus_only)]
pub use circuits::{circuit_project_accepts, circuit_project_error, parsed_circuit_matches};
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
pub use use_aliases::{
    AliasDisposition, ReferenceScopeError, RelativeResolutionError, RelativeTarget,
    UnqualifiedTarget, UseAliasConflict, UseAliases, check_use_aliases,
};
#[cfg(verus_only)]
pub use use_aliases::{alias_conflict_evidence, use_aliases_acceptable, use_aliases_match};
pub use use_targets::{ResolvedUse, UseSite, UseTargetError, UseTargets, index_use_targets};
#[cfg(verus_only)]
pub use use_targets::{use_target_error_evidence, use_targets_match};
