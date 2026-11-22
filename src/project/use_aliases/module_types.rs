//! モジュールで右辺全体を占める呼び出しから、左辺の信号に型を割り当てる。

mod aliases;
pub use aliases::{ModuleAliasSource, ModuleTypeSources};
mod propagation;
pub use propagation::{ModuleAliasCycleStep, ModuleAliasTypes, ModuleAliasTypesError};

use super::{DefinitionDriver, DefinitionPosition, ModuleCallPortsError, ModuleWiring, ModuleWiringError, UseAliases};
use super::function_atoms::copy_location;
use crate::project::{LocatedName, ModuleBodyPosition, PortDirection, SignalType};
#[cfg(verus_only)]
use super::{ModuleCallPorts, function_drivers::indexed_driver_site};
#[cfg(verus_only)]
use crate::project::{CircuitProject, circuits::parsed_index_evidence};
use crate::syntax::circuit::definition_root_is_call;
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, build_entry_ranges_evidence, ordinary_call_at};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// モジュールの配線と、呼び出しの署名から決まる信号型。
#[derive(Debug)]
pub struct ModuleRootTypes<'p, 'a> {
    /// 全断片から得た信号の駆動元と束縛。
    pub wiring: ModuleWiring<'p, 'a>,
    /// `wiring.drivers.definitions` と同じ順の型。通常呼び出し以外の右辺は `None`。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

/// 呼び出しの出力型を決めるまでに見つかった診断。
#[derive(Debug)]
pub enum ModuleRootTypesError<'p, 'a> {
    /// 駆動元または信号の参照に関する診断。
    Wiring(ModuleWiringError<'p, 'a>),
    /// 右辺全体を占める通常呼び出しの診断。
    Call(ModuleCallPortsError<'p, 'a>),
}

spec fn direct_output_type(call: &ModuleCallPorts, output: usize, ty: SignalType) -> bool {
    exists|port: crate::project::CallPortType|
        #[trigger] call.signature.target.port_matches(PortDirection::Output, output, Some(port))
        && ty.ty == port.ty
        && ty.origin == match port.annotation {
            Some(annotation) => *annotation,
            None => LocatedName { source: call.signature.source, span: call.signature.call.span },
        }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn root_type(
        &self, at: ModuleBodyPosition, driver: DefinitionDriver, max_width: u64,
        result: Result<Option<SignalType>, ModuleCallPortsError>,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[at.file as int];
        let source = &project.sources_model()[at.file as int];
        let row = parsed.definitions@[driver.definition as int];
        let start = parsed.entry_ranges@[at.entry as int].definitions.start;
        let reference = DefinitionPosition { file: at.file, entry: at.entry,
            definition: (driver.definition - start) as usize, reference: 0 };
        if ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int) {
            match result {
                Ok(Some(ty)) => exists|call: ModuleCallPorts|
                    #[trigger] self.module_call_ports_result(reference, max_width, Ok(Some(call)))
                    && direct_output_type(&call, driver.result_index, ty),
                Err(error) => self.module_call_ports_result(reference, max_width, Err(error)),
                Ok(None) => false,
            }
        } else { result == Ok(None) }
    }

    fn check_root_type(&self, at: ModuleBodyPosition, driver: &DefinitionDriver<'a>, max_width: u64)
        -> (result: Result<Option<SignalType<'p, 'a>>, ModuleCallPortsError<'p, 'a>>)
        requires
            self.can_resolve(),
            ({
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[at.file as int];
                at.file < project.sources_model().len() && at.file < project.circuits_model().len()
                    && at.entry < parsed.syntax.entries@.len()
                    && (parsed.syntax.entries@[at.entry as int].head is Module || parsed.syntax.entries@[at.entry as int].head is ModulePart)
                    && indexed_driver_site(&project.sources_model()[at.file as int], parsed, at.entry as int, *driver)
            }),
        ensures self.root_type(at, *driver, max_width, result),
    {
        let project = self.targets.project();
        let source = &project.sources()[at.file];
        let parsed = &project.circuits()[at.file];
        let ghost model = parsed.build_model();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &model, at.entry as int);
            build_definition_scope_evidence(source.text, &model, at.entry as int, driver.definition as int);
        }
        let row = &parsed.definitions[driver.definition];
        if !definition_root_is_call(source.text, parsed.syntax.forms.as_slice(), row, parsed.references.as_slice()) {
            return Ok(None);
        }
        let local = driver.definition - parsed.entry_ranges[at.entry].definitions.start;
        let reference = DefinitionPosition { file: at.file, entry: at.entry, definition: local, reference: 0 };
        assert(self.module_call_at(reference));
        let Some(call) = self.check_module_call_ports(reference, max_width)? else {
            proof { self.module_call_ports_present(reference, max_width); }
            unreachable!()
        };
        proof {
            self.module_call_ports_evidence(reference, max_width, call);
            self.module_call_site_evidence(reference, max_width, call.signature);
            assert(call.signature.call.form == row.expression.start);
        }
        let Some(port) = call.signature.target.port(PortDirection::Output, driver.result_index) else {
            proof { assert(false); }
            unreachable!()
        };
        let origin = match port.annotation {
            Some(annotation) => copy_location(annotation),
            None => LocatedName { source, span: call.signature.call.span.start..call.signature.call.span.end },
        };
        let ty = SignalType { ty: port.ty, origin };
        assert(direct_output_type(&call, driver.result_index, ty));
        Ok(Some(ty))
    }

    #[verifier::opaque]
    spec fn root_types_prefix(&self, wiring: &ModuleWiring, max_width: u64, types: Seq<Option<SignalType>>) -> bool {
        &&& types.len() <= wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < types.len() ==> self.root_type(wiring.drivers.origins@[i],
            wiring.drivers.definitions@[i], max_width, Ok(#[trigger] types[i]))
    }

    /// 確定した型と診断が、元の断片にある右辺とポート順に対応することを表す。
    pub closed spec fn module_root_types_result(
        &self, owner: ModuleBodyPosition, max_width: u64, result: Result<Option<ModuleRootTypes>, ModuleRootTypesError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_wiring_result(owner, max_width, Ok(None)),
            Err(ModuleRootTypesError::Wiring(error)) => self.module_wiring_result(owner, max_width, Err(error)),
            Ok(Some(typed)) => self.module_wiring_result(owner, max_width, Ok(Some(typed.wiring)))
                && typed.types@.len() == typed.wiring.drivers.definitions@.len()
                && self.root_types_prefix(&typed.wiring, max_width, typed.types@),
            Err(ModuleRootTypesError::Call(error)) => exists|wiring: ModuleWiring, before: Seq<Option<SignalType>>|
                #[trigger] self.module_wiring_result(owner, max_width, Ok(Some(wiring)))
                && #[trigger] self.root_types_prefix(&wiring, max_width, before)
                && before.len() < wiring.drivers.definitions@.len()
                && self.root_type(wiring.drivers.origins@[before.len() as int], wiring.drivers.definitions@[before.len() as int],
                    max_width, Err(error)),
        }
    }

    /// 型伝播に使う左辺の型と、元の配線検査の対応を取り出す。
    pub(super) proof fn module_root_types_evidence(
        &self, owner: ModuleBodyPosition, max_width: u64, typed: ModuleRootTypes,
    )
        requires self.module_root_types_result(owner, max_width, Ok(Some(typed))),
        ensures
            self.module_wiring_result(owner, max_width, Ok(Some(typed.wiring))),
            typed.types@.len() == typed.wiring.drivers.definitions@.len(),
    {
    }

    /// 全断片の右辺全体を占める通常呼び出しから、左辺の型を求める。
    ///
    /// 型は参照先の署名で決まるため、呼び出しの引数が後続定義を参照しても取り出せる。
    /// 引数と、呼び出し以外の右辺の型は後段で検査する。
    ///
    /// # Errors
    ///
    /// 配線を検査した後、本体順・定義順に呼び出しを検査して最初の違反を返す。
    pub fn check_module_root_types(&self, owner: ModuleBodyPosition, max_width: u64)
        -> (result: Result<Option<ModuleRootTypes<'p, 'a>>, ModuleRootTypesError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_root_types_result(owner, max_width, result),
    {
        let wiring = match self.check_module_wiring(owner, max_width) {
            Ok(Some(wiring)) => wiring,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ModuleRootTypesError::Wiring(error)),
        };
        let mut types = Vec::new();
        assert(self.root_types_prefix(&wiring, max_width, types@)) by { reveal(UseAliases::root_types_prefix); };
        let mut index = 0;
        while index < wiring.drivers.definitions.len()
            invariant
                self.can_resolve(), self.module_wiring_result(owner, max_width, Ok(Some(wiring))),
                index == types@.len() <= wiring.drivers.definitions@.len(),
                self.root_types_prefix(&wiring, max_width, types@),
            decreases wiring.drivers.definitions@.len() - index,
        {
            proof {
                self.module_wiring_keeps_drivers(owner, max_width, wiring);
                self.module_driver_sites(owner, max_width, wiring.drivers, index as int);
            }
            let at = wiring.drivers.origins[index];
            let driver = &wiring.drivers.definitions[index];
            let ty = match self.check_root_type(at, driver, max_width) {
                Ok(ty) => ty,
                Err(error) => return Err(ModuleRootTypesError::Call(error)),
            };
            let ghost before = types@;
            types.push(ty);
            assert(self.root_types_prefix(&wiring, max_width, types@)) by {
                reveal(UseAliases::root_types_prefix);
                assert forall|i: int| 0 <= i < types@.len() implies self.root_type(wiring.drivers.origins@[i],
                    wiring.drivers.definitions@[i], max_width, Ok(#[trigger] types@[i])) by {
                    if i < index { assert(types@[i] == before[i]); }
                };
            };
            index += 1;
        }
        Ok(Some(ModuleRootTypes { wiring, types }))
    }
}

} // verus!
