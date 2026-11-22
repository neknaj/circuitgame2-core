//! 裸の信号名だけからなる右辺を、型を引き継ぐ元の駆動元に結び付ける。

use super::{ModuleRootTypes, ModuleRootTypesError, UseAliases};
use crate::project::{LocatedName, ModuleBodyPosition, ModuleWiring, OutputDriver};
use crate::project::use_aliases::function_atoms::copy_location;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
use crate::syntax::{AtomKind, Form, circuit::definition_target_atoms};
#[cfg(verus_only)]
use crate::syntax::circuit::{build_bare_signal_position, build_definition_scope_evidence,
    build_entry_ranges_evidence, definition_target_range};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 裸の信号参照が型を引き継ぐ元と、その参照位置。
#[derive(Debug)]
pub struct ModuleAliasSource<'p, 'a> {
    /// 入力宣言または全断片の左辺の駆動元。
    pub driver: OutputDriver,
    /// 右辺に信号名を書いたソース範囲。
    pub reference: LocatedName<'p, 'a>,
}

/// 通常呼び出しやビット選択から得た型と、裸の信号名を介した型の依存先。
#[derive(Debug)]
pub struct ModuleTypeSources<'p, 'a> {
    /// 配線検査と、通常呼び出しやビット選択から確定した型。
    pub roots: ModuleRootTypes<'p, 'a>,
    /// 左辺の駆動元と同じ順。右辺が単一の左辺を持つ裸名参照の場合に依存先を持つ。
    pub aliases: Vec<Option<ModuleAliasSource<'p, 'a>>>,
}

pub(super) fn find_member(members: &[ModuleBodyPosition], at: ModuleBodyPosition) -> (index: usize)
    requires members@.contains(at),
    ensures index < members@.len() && members@[index as int] == at,
{
    let mut i = 0;
    while i < members.len()
        invariant
            members@.contains(at), i <= members@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] members@[j] != at,
        decreases members@.len() - i,
    {
        let current = members[i];
        if current.file == at.file && current.entry == at.entry {
            return i;
        }
        i += 1;
    }
    proof {
        let index = choose|j: int| 0 <= j < members@.len() && members@[j] == at;
        assert(false);
    }
    unreachable!()
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn alias_source_at(&self, wiring: &ModuleWiring, index: int, found: Option<ModuleAliasSource>) -> bool {
        let project = self.targets.project_model();
        let driver = wiring.drivers.definitions@[index];
        let at = wiring.drivers.origins@[index];
        let parsed = &project.circuits_model()[at.file as int];
        let row = parsed.definitions@[driver.definition as int];
        let forms = parsed.syntax.forms@;
        let first = forms[row.expression.start as int];
        let (start, end) = definition_target_range(forms, row);
        if first is Atom && first->Atom_kind is Name && end - start == 1 {
            &&& found matches Some(alias)
            &&& exists|member: int| 0 <= member < wiring.drivers.body.members@.len()
                && (#[trigger] wiring.drivers.body.members@[member]) == at
                && {
                    let range = parsed.entry_ranges@[at.entry as int].signals;
                    let slot = row.signals.start - range.start;
                    let bound = wiring.signals@[member]@[slot];
                    &&& 0 <= slot < wiring.signals@[member]@.len()
                    &&& bound.form == row.expression.start
                    &&& alias.reference == bound.site && alias.driver == bound.driver
                }
            &&& match alias.driver {
                OutputDriver::Input(input) => input < wiring.drivers.signature.inputs@.len(),
                OutputDriver::Definition(definition) => definition < wiring.drivers.definitions@.len(),
            }
        } else { found.is_none() }
    }

    fn read_module_alias(&self, _owner: ModuleBodyPosition, _limit: u64, wiring: &ModuleWiring<'p, 'a>, index: usize)
        -> (alias: Option<ModuleAliasSource<'p, 'a>>)
        requires
            self.can_resolve(), index < wiring.drivers.definitions@.len(),
            self.module_wiring_result(_owner, _limit, Ok(Some(*wiring))),
        ensures self.alias_source_at(wiring, index as int, alias),
    {
        proof {
            self.module_wiring_keeps_drivers(_owner, _limit, *wiring);
            self.module_driver_sites(_owner, _limit, wiring.drivers, index as int);
        }
        let at = wiring.drivers.origins[index];
        let driver = &wiring.drivers.definitions[index];
        let project = self.targets.project();
        let parsed = &project.circuits()[at.file];
        let ghost source = &project.sources_model()[at.file as int];
        let ghost model = parsed.build_model();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, at.entry as int);
            build_definition_scope_evidence(source.text, &model, at.entry as int, driver.definition as int);
        }
        let row = &parsed.definitions[driver.definition];
        let forms = parsed.syntax.forms.as_slice();
        if !matches!(forms[row.expression.start], Form::Atom { kind: AtomKind::Name, .. }) {
            return None;
        }
        let left = definition_target_atoms(forms, row);
        if left.end - left.start != 1 {
            return None;
        }
        let member = find_member(wiring.drivers.body.members.as_slice(), at);
        proof {
            build_bare_signal_position(source.text, &model, at.entry as int, driver.definition as int);
            self.module_signal_index_item(_owner, _limit, *wiring, member as int, row.signals.start as int);
        }
        let frame = &parsed.entry_ranges[at.entry].signals;
        let group = &wiring.signals[member];
        let bound = &group[row.signals.start - frame.start];
        let alias = ModuleAliasSource { driver: bound.driver, reference: copy_location(&bound.site) };
        Some(alias)
    }

    #[verifier::opaque]
    spec fn alias_sources_prefix(&self, wiring: &ModuleWiring, aliases: Seq<Option<ModuleAliasSource>>) -> bool {
        &&& aliases.len() <= wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < aliases.len() ==> self.alias_source_at(wiring, i, #[trigger] aliases[i])
    }

    /// 確定済みの型と別名の依存先を、全断片の配線と対応付ける。
    pub closed spec fn module_type_sources_result(
        &self, owner: ModuleBodyPosition, limit: u64, result: Result<Option<ModuleTypeSources>, ModuleRootTypesError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_root_types_result(owner, limit, Ok(None)),
            Err(error) => self.module_root_types_result(owner, limit, Err(error)),
            Ok(Some(sources)) => self.module_root_types_result(owner, limit, Ok(Some(sources.roots)))
                && sources.aliases@.len() == sources.roots.wiring.drivers.definitions@.len()
                && self.alias_sources_prefix(&sources.roots.wiring, sources.aliases@),
        }
    }

    /// 型伝播で参照する添字が、対応する入力または左辺の範囲にあることを示す。
    pub(super) proof fn module_type_sources_bounds(&self, owner: ModuleBodyPosition, limit: u64, sources: ModuleTypeSources)
        requires self.module_type_sources_result(owner, limit, Ok(Some(sources))),
        ensures
            self.module_root_types_result(owner, limit, Ok(Some(sources.roots))),
            sources.aliases@.len() == sources.roots.types@.len(),
            forall|i: int| 0 <= i < sources.aliases@.len() ==>
                ((#[trigger] sources.aliases@[i]) matches Some(alias) ==> match alias.driver {
                    OutputDriver::Input(index) => index < sources.roots.wiring.drivers.signature.inputs@.len(),
                    OutputDriver::Definition(index) => index < sources.aliases@.len(),
                }),
    {
        self.module_root_types_evidence(owner, limit, sources.roots);
        reveal(UseAliases::alias_sources_prefix);
    }

    /// 右辺の型を決める通常呼び出しやビット選択と、裸の信号名の依存先を全断片から集める。
    ///
    /// 信号の型を伝播する前に、前方参照を含む依存先を確定する。
    /// 左辺に複数の名前がある裸名参照は、右辺の出力数を検査する段階で扱う。
    ///
    /// # Errors
    ///
    /// 配線、通常呼び出し、ビット選択の検査で見つかった最初の違反を返す。
    pub fn check_module_type_sources(&self, owner: ModuleBodyPosition, limit: u64)
        -> (result: Result<Option<ModuleTypeSources<'p, 'a>>, ModuleRootTypesError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_type_sources_result(owner, limit, result),
    {
        let Some(roots) = self.check_module_root_types(owner, limit)? else { return Ok(None); };
        proof { self.module_root_types_evidence(owner, limit, roots); }
        let wiring = &roots.wiring;
        let mut aliases = Vec::new();
        assert(self.alias_sources_prefix(wiring, aliases@)) by { reveal(UseAliases::alias_sources_prefix); };
        let mut i = 0;
        while i < wiring.drivers.definitions.len()
            invariant
                self.can_resolve(), self.module_root_types_result(owner, limit, Ok(Some(roots))),
                self.module_wiring_result(owner, limit, Ok(Some(*wiring))), *wiring == roots.wiring,
                i == aliases@.len() <= wiring.drivers.definitions@.len(),
                self.alias_sources_prefix(wiring, aliases@),
            decreases wiring.drivers.definitions@.len() - i,
        {
            let alias = self.read_module_alias(owner, limit, wiring, i);
            let ghost prior = aliases@;
            aliases.push(alias);
            assert(self.alias_sources_prefix(wiring, aliases@)) by {
                reveal(UseAliases::alias_sources_prefix);
                assert forall|j: int| 0 <= j < aliases@.len() implies
                    self.alias_source_at(wiring, j, #[trigger] aliases@[j]) by {
                    if j < i { assert(aliases@[j] == prior[j]); }
                };
            };
            i += 1;
        }
        Ok(Some(ModuleTypeSources { roots, aliases }))
    }
}

} // verus!
