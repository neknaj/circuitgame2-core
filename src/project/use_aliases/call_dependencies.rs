//! 通常呼び出しの解決先と、依存辺の根拠になる参照名の位置を求める。

mod graph;
mod roots;
mod vertices;
pub use graph::{FunctionCallSite, FunctionExpansionError, FunctionExpansionOrder};
#[cfg(verus_only)]
pub(super) use vertices::function_position;

use super::{ResolvedDefinitionReference, UseAliases};
#[cfg(verus_only)]
use super::DefinitionReferenceError;
use super::function_drivers::name_location;
use crate::project::LocatedName;
use vstd::prelude::*;

verus! {

/// 呼び出し先の宣言と、その呼び出し先名が現れたソース範囲。
pub(super) struct CallDependency<'p, 'a> {
    pub(super) target: (usize, usize),
    pub(super) reference: LocatedName<'p, 'a>,
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn resolved_call_dependency_matches(
        &self, resolved: ResolvedDefinitionReference, edge: Option<CallDependency>,
    ) -> bool {
        match edge {
            Some(edge) => self.func_position_matches(resolved.binding, Some(edge.target))
                && *edge.reference.source == *resolved.site.source
                && edge.reference.span == resolved.site.name.span
                && crate::project::location_in_source(edge.reference),
            None => self.func_position_matches(resolved.binding, None),
        }
    }

    pub(super) closed spec fn call_dependency_matches(
        &self, caller: (usize, usize, usize, usize),
        result: Result<Option<CallDependency>, DefinitionReferenceError>,
    ) -> bool {
        let (file, entry, definition, reference) = caller;
        match result {
            Ok(edge) => exists|resolved: ResolvedDefinitionReference|
                #[trigger] self.definition_resolution_evidence(file, entry, definition, reference, Ok(resolved))
                    && self.resolved_call_dependency_matches(resolved, edge),
            Err(error) => self.definition_resolution_evidence(file, entry, definition, reference, Err(error)),
        }
    }

    proof fn record_call_dependency(
        &self, caller: (usize, usize, usize, usize),
        resolved: ResolvedDefinitionReference, edge: Option<CallDependency>,
    )
        requires
            self.definition_resolution_evidence(caller.0, caller.1, caller.2, caller.3, Ok(resolved)),
            self.resolved_call_dependency_matches(resolved, edge),
        ensures self.call_dependency_matches(caller, Ok(edge)),
    {
        let (file, entry, definition, reference) = caller;
        assert(exists|candidate: ResolvedDefinitionReference|
            #[trigger] self.definition_resolution_evidence(file, entry, definition, reference, Ok(candidate))
                && self.resolved_call_dependency_matches(candidate, edge));
    }

    /// 既に解決した参照を再解決せず、依存先と参照元の位置を得る。
    pub(super) fn call_dependency_from_binding(
        &self, Ghost(caller): Ghost<(usize, usize, usize, usize)>,
        resolved: &ResolvedDefinitionReference<'p, 'a>,
    ) -> (edge: Option<CallDependency<'p, 'a>>)
        requires
            self.can_resolve(),
            self.func_call_at(caller.0, caller.1, caller.2, caller.3),
            self.definition_resolution_evidence(caller.0, caller.1, caller.2, caller.3, Ok(*resolved)),
        ensures
            self.call_dependency_matches(caller, Ok(edge)),
            edge.is_some() <==> resolved.binding is Declaration,
            edge matches Some(value) ==> crate::project::location_in_source(value.reference),
    {
        let position = self.resolved_func_position(Ghost(caller), resolved);
        let Some(target) = position else {
            assert(self.resolved_call_dependency_matches(*resolved, None));
            proof { self.record_call_dependency(caller, *resolved, None); }
            return None;
        };
        proof { self.resolved_reference_location(caller.0, caller.1, caller.2, caller.3, *resolved); }
        let reference = name_location(resolved.site.source, &resolved.site.name);
        let edge = CallDependency { target, reference };
        assert(self.resolved_call_dependency_matches(*resolved, Some(edge)));
        proof { self.record_call_dependency(caller, *resolved, Some(edge)); }
        Some(edge)
    }

    /// 同じ参照から得られる依存先と診断用の範囲は一意に決まる。
    pub(super) proof fn call_dependencies_agree(
        &self, caller: (usize, usize, usize, usize),
        left: Option<CallDependency>, right: Option<CallDependency>,
    )
        requires
            self.can_resolve(),
            self.call_dependency_matches(caller, Ok(left)),
            self.call_dependency_matches(caller, Ok(right)),
        ensures left == right,
    {
        let (file, entry, def, reference) = caller;
        let a = choose|resolved: ResolvedDefinitionReference|
            #[trigger] self.definition_resolution_evidence(file, entry, def, reference, Ok(resolved))
            && self.resolved_call_dependency_matches(resolved, left);
        let b = choose|resolved: ResolvedDefinitionReference|
            #[trigger] self.definition_resolution_evidence(file, entry, def, reference, Ok(resolved))
            && self.resolved_call_dependency_matches(resolved, right);
        match (left, right) {
            (Some(left), Some(right)) => {
                self.positioned_declarations_agree(file, entry, def, reference, a, b);
                self.declaration_positions_agree(left.target.0, left.target.1, right.target.0, right.target.1);
                self.resolved_reference_locations_agree(caller, a, b);
            },
            (None, Some(_)) => self.nor_binding_excludes_declaration(file, entry, def, reference, a, b),
            (Some(_), None) => self.nor_binding_excludes_declaration(file, entry, def, reference, b, a),
            (None, None) => {},
        }
    }


}

} // verus!
