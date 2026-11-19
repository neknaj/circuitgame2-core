//! プロジェクトに渡すソースの識別子と種別を扱う。

mod circuits;
mod path;
mod sources;

pub use circuits::{CircuitProject, CircuitProjectError, parse_circuit_project};
#[cfg(verus_only)]
pub use circuits::{circuit_project_accepts, circuit_project_error, parsed_circuit_matches};
pub use path::{PathError, SourceKind, VirtualPath, normalize_path};
#[cfg(verus_only)]
pub use path::{canonical_components, normalized_path, source_kind_of};
pub use sources::{ProjectSource, SourceSetError, SourceSnapshot, collect_sources};
#[cfg(verus_only)]
pub use sources::{project_sources_match, source_set_error, valid_source_snapshots};
