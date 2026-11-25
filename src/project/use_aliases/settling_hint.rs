//! 定常化の上界を、その推論に使ったモジュールの宣言位置と結び付ける。

use super::{ClockedModuleVmError, ClockedModuleVmLimits, UseAliases};
#[cfg(verus_only)]
use super::ClockedModuleVm;
use crate::project::{LocatedName, ModuleBodyPosition};
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
use crate::syntax::circuit::{Head, named_build_entry};
use vstd::prelude::*;

verus! {

/// モジュール名の横で表示できる、固定入力での定常化の上界。
#[derive(Debug)]
pub struct ModuleSettlingHint<'p, 'a> {
    /// 上界を求めたモジュールの名前。ファイル識別子と文書バージョンを含む。
    pub location: LocatedName<'p, 'a>,
    /// 定常化までの tick 数の上界。
    pub ticks: usize,
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 宣言位置と展開済みの参照回路から、表示できる定常化の上界を定める。
    pub closed spec fn module_settling_hint_matches(
        &self, file: usize, name: usize, limits: ClockedModuleVmLimits, hint: ModuleSettlingHint,
    ) -> bool {
        let project = self.targets.project_model();
        let circuits = project.circuits_model();
        let sources = project.sources_model();
        &&& file < circuits.len() && file < sources.len()
        &&& name < circuits[file as int].names@.len()
        &&& {
            let circuit = circuits[file as int];
            let form = circuit.names@[name as int];
            &&& form.head is Module
            &&& hint.location.source == &sources[file as int]
            &&& hint.location.span == form.name.span
            &&& exists|pair: (ModuleBodyPosition, ClockedModuleVm)|
                pair.0.file == file && #[trigger] self.settling_hint_witness(pair.0, name, limits, Some(hint.ticks), pair.1)
        }
    }

    spec fn settling_hint_witness(
        &self, owner: ModuleBodyPosition, name: usize, limits: ClockedModuleVmLimits,
        bound: Option<usize>, compiled: ClockedModuleVm,
    ) -> bool {
        let project = self.targets.project_model();
        let circuits = project.circuits_model();
        &&& owner.file < circuits.len()
        &&& {
            let circuit = circuits[owner.file as int];
            &&& name < circuit.names@.len()
            &&& owner.entry < circuit.syntax.entries@.len()
            &&& circuit.syntax.entries@[owner.entry as int].form == circuit.names@[name as int].form
            &&& circuit.syntax.entries@[owner.entry as int].head is Module
            &&& compiled.vm.valid()
            &&& (self.clocked_module_vm_wiring(owner, limits, &compiled)
                || self.clocked_module_hierarchy_vm(owner, limits, &compiled))
            &&& compiled.vm.settling_bound_matches(bound)
        }
    }

    /// 指定した添字が、このプロジェクトのモジュール宣言を指すことを表す。
    pub closed spec fn settling_module_selected(&self, file: usize, name: usize) -> bool {
        let project = self.targets.project_model();
        let circuits = project.circuits_model();
        &&& file < project.sources_model().len() && file < circuits.len()
        &&& name < circuits[file as int].names@.len()
        &&& circuits[file as int].names@[name as int].head is Module
    }

    spec fn matches_settling_hint_owner(&self, owner: ModuleBodyPosition, name: usize) -> bool {
        let circuits = self.targets.project_model().circuits_model();
        &&& self.settling_module_selected(owner.file, name)
        &&& owner.entry < circuits[owner.file as int].syntax.entries@.len()
        &&& circuits[owner.file as int].syntax.entries@[owner.entry as int].head is Module
        &&& circuits[owner.file as int].syntax.entries@[owner.entry as int].form
            == circuits[owner.file as int].names@[name as int].form
    }

    /// 対象が存在しないか、そのモジュールの解析で上界を得られないことを表す。
    pub closed spec fn module_settling_hint_unavailable(
        &self, file: usize, name: usize, limits: ClockedModuleVmLimits,
    ) -> bool {
        !self.settling_module_selected(file, name)
        || exists|owner: ModuleBodyPosition| owner.file == file
            && #[trigger] self.matches_settling_hint_owner(owner, name)
            && (self.module_calls_result(owner, limits.width, Ok(None))
                || exists|compiled: ClockedModuleVm| #[trigger] self.settling_hint_witness(
                    owner, name, limits, None, compiled,
                ))
    }

    /// 推論結果の上界を保証する、同じモジュールの展開済み VM を特定する。
    pub proof fn module_settling_hint_vm(
        &self, file: usize, name: usize, limits: ClockedModuleVmLimits, hint: ModuleSettlingHint,
    ) -> (witness: (ModuleBodyPosition, ClockedModuleVm))
        requires self.module_settling_hint_matches(file, name, limits, hint),
        ensures
            witness.0.file == file,
            witness.1.vm.valid(),
            self.clocked_module_vm_wiring(witness.0, limits, &witness.1)
                || self.clocked_module_hierarchy_vm(witness.0, limits, &witness.1),
            witness.1.vm.settling_bound_matches(Some(hint.ticks)),
    {
        choose|pair: (ModuleBodyPosition, ClockedModuleVm)|
            pair.0.file == file && #[trigger] self.settling_hint_witness(pair.0, name, limits, Some(hint.ticks), pair.1)
    }


    /// 指定した名前索引のモジュールを展開し、定常化の推論結果を名前の位置とともに返す。
    ///
    /// 対象がモジュール宣言を指さない場合や、定常化の上界を推定できない場合は `Ok(None)`。
    /// プロジェクト全体の基底は、先に [`crate::project::validate_circuit_basis`] で検査する。
    /// 表示位置には `location.span.end` を使う。
    ///
    /// # Errors
    ///
    /// 型検査、結線検査、階層展開、または資源上限で失敗したときに、コンパイルの診断を返す。
    pub fn module_settling_hint(
        &self, file: usize, name: usize, limits: ClockedModuleVmLimits,
    ) -> (result: Result<Option<ModuleSettlingHint<'p, 'a>>, ClockedModuleVmError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            result matches Ok(Some(hint)) ==> self.module_settling_hint_matches(file, name, limits, hint),
            result matches Ok(None) ==> self.module_settling_hint_unavailable(file, name, limits),
            result.is_err() ==> self.settling_module_selected(file, name),
    {
        let project = self.targets.project();
        let (Some(source), Some(circuit)) = (project.sources().get(file), project.circuits().get(file)) else {
            return Ok(None);
        };
        let Some(form) = circuit.names.get(name) else {
            return Ok(None);
        };
        if !matches!(form.head, Head::Module) {
            return Ok(None);
        }
        proof {
            self.targets.parsed_project_model();
            source.text_model_is_text();
            parsed_index_evidence(*source, *circuit);
        }
        let entry = named_build_entry(source.text(), circuit, name);
        let owner = ModuleBodyPosition { file, entry };
        assert(self.matches_settling_hint_owner(owner, name));
        let Some(compiled) = self.lower_clocked_vm(owner, limits)? else {
            return Ok(None);
        };
        let Some(ticks) = compiled.vm.settling_bound() else {
            assert(self.settling_hint_witness(owner, name, limits, None, compiled));
            return Ok(None);
        };
        let hint = ModuleSettlingHint {
            location: LocatedName { source, span: form.name.span.start..form.name.span.end },
            ticks,
        };
        assert(self.settling_hint_witness(owner, name, limits, Some(ticks), compiled));
        proof {
            let model = self.targets.project_model();
            assert(hint.location.source == &model.sources_model()[file as int]);
            assert(hint.location.span == model.circuits_model()[file as int].names@[name as int].name.span);
            let pair = (owner, compiled);
            assert(pair.0.file == file);
            assert(self.settling_hint_witness(pair.0, name, limits, Some(hint.ticks), pair.1));
            assert(exists|pair: (ModuleBodyPosition, ClockedModuleVm)| pair.0.file == file
                && #[trigger] self.settling_hint_witness(pair.0, name, limits, Some(hint.ticks), pair.1));
            assert(self.module_settling_hint_matches(file, name, limits, hint));
        }
        Ok(Some(hint))
    }
}

} // verus!
