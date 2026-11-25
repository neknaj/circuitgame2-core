//! モジュール内の呼び出しが使う関数を、宣言ごとに展開して共有する。

use super::{ClockedModuleError, LocatedName, ModuleBodyPosition, ModuleCallTarget, ModuleCalls, UseAliases};
use crate::project::use_aliases::bit_func::ClockedFunctionTemplate;
#[cfg(verus_only)]
use crate::project::use_aliases::call_dependencies::function_position;
use alloc::collections::BTreeMap;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::laws_cmp::obeys_cmp;

verus! {

pub(in crate::project::use_aliases::module_types) type FunctionTemplates<'p, 'a> = BTreeMap<(usize, usize), ClockedFunctionTemplate<'p, 'a>>;

/// キャッシュにあった展開結果が、その後も同じ宣言位置から得られることを表す。
pub(in crate::project::use_aliases::module_types) open spec fn function_cache_extends(
    before: Map<(usize, usize), ClockedFunctionTemplate>, after: Map<(usize, usize), ClockedFunctionTemplate>,
) -> bool {
    forall|key: (usize, usize)| #[trigger] before.contains_key(key) ==>
        after.contains_key(key) && after[key] == before[key]
}

/// モジュールの依存辺を持たない通常呼び出しが参照する宣言位置。
pub(in crate::project::use_aliases::module_types) open spec fn function_target(calls: &ModuleCalls, edges: Seq<Option<usize>>, i: int) -> Option<(usize, usize)> {
    match calls.calls@[i].inputs.ports.signature.target {
        ModuleCallTarget::Routine { position, .. } if edges[i].is_none() => Some((position.file, position.entry)),
        _ => None,
    }
}

pub(in crate::project::use_aliases::module_types) open spec fn function_templates_cover(calls: &ModuleCalls, edges: Seq<Option<usize>>,
    functions: Map<(usize, usize), ClockedFunctionTemplate>, end: int) -> bool {
    forall|i: int| 0 <= i < end && #[trigger] function_target(calls, edges, i) is Some ==>
        functions.contains_key(function_target(calls, edges, i)->Some_0)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(in crate::project::use_aliases::module_types) open spec fn function_targets_are_declared(&self, calls: &ModuleCalls, edges: Seq<Option<usize>>) -> bool {
        forall|i: int| 0 <= i < calls.calls@.len() ==>
            ((#[trigger] function_target(calls, edges, i)) matches Some(target)
                ==> function_position(self.targets.project_model().circuits_model(), target))
    }

    pub(in crate::project::use_aliases::module_types) open spec fn clocked_functions_match(
        &self, cache: Map<(usize, usize), ClockedFunctionTemplate>, width: u64, bits: usize, gates: usize,
    ) -> bool {
        forall|target: (usize, usize)| cache.contains_key(target) ==>
            self.clocked_function_template_matches(target, width, bits, gates, &#[trigger] cache[target])
    }

    /// 関数展開の診断を、モジュールの呼び出し箇所と解決済みの宣言に結び付ける。
    pub closed spec fn clocked_module_function_error(
        &self, width: u64, bits: usize, gates: usize, site: LocatedName, expansion: crate::project::ExpandFunctionsError,
    ) -> bool {
        exists|owner: ModuleBodyPosition, calls: ModuleCalls, i: int| {
            &&& #[trigger] self.module_calls_result(owner, width, Ok(Some(calls)))
            &&& 0 <= i < calls.calls@.len()
            &&& {
                let signature = (#[trigger] calls.calls@[i]).inputs.ports.signature;
                &&& site == (LocatedName { source: signature.source, span: signature.call.span })
                &&& signature.target matches ModuleCallTarget::Routine { position, .. }
                &&& self.expand_reachable_function_result((position.file, position.entry), width, bits, gates, Err(expansion))
            }
        }
    }

    /// それ以前の関数呼び出しの展開がそろった段階で見つかった失敗を表す。
    pub(in crate::project::use_aliases::module_types) closed spec fn function_expansion_stops_at(
        &self, calls: &ModuleCalls, edges: Seq<Option<usize>>, cache: Map<(usize, usize), ClockedFunctionTemplate>,
        width: u64, bits: usize, gates: usize, site: LocatedName, expansion: crate::project::ExpandFunctionsError,
    ) -> bool {
        exists|i: int| 0 <= i < calls.calls@.len() && {
            let signature = (#[trigger] calls.calls@[i]).inputs.ports.signature;
            &&& site == (LocatedName { source: signature.source, span: signature.call.span })
            &&& function_templates_cover(calls, edges, cache, i)
            &&& function_target(calls, edges, i) matches Some(target)
            &&& !cache.contains_key(target)
            &&& self.expand_reachable_function_result(target, width, bits, gates, Err(expansion))
        }
    }

    /// 呼び出し順に関数を展開し、すでに展開した宣言の配線を再利用する。
    ///
    /// # Errors
    ///
    /// 展開に失敗した最初の関数呼び出しの位置と、関数側の診断を返す。
    pub(in crate::project::use_aliases::module_types) fn prepare_clocked_functions(&self, _owner: ModuleBodyPosition, width: u64, bits: usize, gates: usize,
        calls: &ModuleCalls<'p, 'a>, edges: &[Option<usize>], cache: &mut FunctionTemplates<'p, 'a>,
    ) -> (result: Result<(), ClockedModuleError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_calls_result(_owner, width, Ok(Some(*calls))),
            edges@.len() == calls.calls@.len(), obeys_cmp::<(usize, usize)>(),
            self.clocked_functions_match(old(cache)@, width, bits, gates),
            self.function_targets_are_declared(calls, edges@),
        ensures
            self.clocked_functions_match(final(cache)@, width, bits, gates),
            function_cache_extends(old(cache)@, final(cache)@),
            result is Ok ==> function_templates_cover(calls, edges@, final(cache)@, calls.calls@.len() as int),
            !(result matches Err(ClockedModuleError::Parent(_) | ClockedModuleError::Recursion(_))),
            !(result matches Err(ClockedModuleError::PortLayout { .. })),
            result matches Err(ClockedModuleError::Function { call, expansion }) ==>
                self.clocked_module_function_error(width, bits, gates, call, expansion)
                    && self.function_expansion_stops_at(calls, edges@, final(cache)@, width, bits, gates, call, expansion),
    {
        let mut i = 0;
        while i < calls.calls.len()
            invariant
                self.can_resolve(), self.module_calls_result(_owner, width, Ok(Some(*calls))),
                i <= calls.calls@.len() == edges@.len(), obeys_cmp::<(usize, usize)>(),
                self.clocked_functions_match(cache@, width, bits, gates),
                function_cache_extends(old(cache)@, cache@),
                self.function_targets_are_declared(calls, edges@),
                function_templates_cover(calls, edges@, cache@, i as int),
            decreases calls.calls@.len() - i,
        {
            let call = &calls.calls[i];
            let signature = &call.inputs.ports.signature;
            let ghost before = cache@;
            if let ModuleCallTarget::Routine { position, .. } = &signature.target {
                if edges[i].is_none() {
                    let target = (position.file, position.entry);
                    assert(function_target(calls, edges@, i as int) == Some(target));
                    if cache.get(&target).is_none() {
                        let site = LocatedName { source: signature.source, span: signature.call.span.start..signature.call.span.end };
                        let template = match self.expand_clocked_function(target, width, bits, gates) {
                            Ok(template) => template,
                            Err(expansion) => {
                                assert(self.function_expansion_stops_at(calls, edges@, cache@, width, bits, gates, site, expansion));
                                assert(self.clocked_module_function_error(width, bits, gates, site, expansion));
                                return Err(ClockedModuleError::Function { call: site, expansion });
                            },
                        };
                        let _ = cache.insert(target, template);
                        assert(cache@ == before.insert(target, template));
                        assert(function_cache_extends(old(cache)@, cache@)) by {
                            assert forall|key: (usize, usize)| #[trigger] old(cache)@.contains_key(key) implies
                                cache@.contains_key(key) && cache@[key] == old(cache)@[key] by {
                                assert(before.contains_key(key));
                                assert(key != target);
                            };
                        };
                        assert(self.clocked_functions_match(cache@, width, bits, gates)) by {
                            assert forall|key: (usize, usize)| cache@.contains_key(key) implies
                                self.clocked_function_template_matches(key, width, bits, gates, &#[trigger] cache@[key]) by {
                                if key != target {
                                    assert(cache@[key] == before[key]);
                                }
                            };
                        };
                    }
                    assert(cache@.contains_key(target));
                }
            }
            assert forall|j: int| 0 <= j <= i && #[trigger] function_target(calls, edges@, j) is Some implies
                cache@.contains_key(function_target(calls, edges@, j)->Some_0) by {
                if j < i {
                    assert(before.contains_key(function_target(calls, edges@, j)->Some_0));
                }
            };
            i += 1;
        }
        Ok(())
    }
}

} // verus!
