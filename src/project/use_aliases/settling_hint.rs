//! モジュールの展開結果を、元の宣言位置と結び付ける。

use super::{ClockedModuleVmError, ClockedModuleVmLimits, UseAliases};
#[cfg(verus_only)]
use super::{ClockedModuleVm, use_aliases_match};
use crate::project::{LocatedName, ModuleBodyPosition};
#[cfg(verus_only)]
use crate::project::{CircuitProject, UseTargets, circuits::parsed_index_evidence, use_targets_match};
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

/// モジュールを展開して得た NOR ゲート数と定常化の上界。
#[derive(Debug)]
pub struct ModuleExpansionHint<'p, 'a> {
    /// モジュール名の範囲。ファイル識別子と文書バージョンを含む。
    pub location: LocatedName<'p, 'a>,
    /// 階層展開後の2入力 NOR ゲート数。ラッチや RAM は含めない。
    pub nor_gates: usize,
    /// 固定入力での定常化の上界。上界を推定できない場合は `None`。
    pub settling_ticks: Option<usize>,
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 展開結果の出典と、ゲート数と上界を求めた同一の VM を表す。
    pub closed spec fn module_expansion_hint_matches(
        &self, file: usize, name: usize, limits: ClockedModuleVmLimits, hint: ModuleExpansionHint,
    ) -> bool {
        let project = self.targets.project_model();
        &&& self.settling_module_selected(file, name)
        &&& hint.location.source == &project.sources_model()[file as int]
        &&& hint.location.span == project.circuits_model()[file as int].names@[name as int].name.span
        &&& exists|pair: (ModuleBodyPosition, ClockedModuleVm)|
            pair.0.file == file
            && #[trigger] self.settling_hint_witness(pair.0, name, limits, hint.settling_ticks, pair.1)
            && hint.nor_gates == pair.1.vm.netlist_model().gates@.len()
    }

    /// 指定位置がモジュールを指さないか、その本体が展開対象にないことを表す。
    pub closed spec fn module_expansion_hint_unavailable(
        &self, file: usize, name: usize, limits: ClockedModuleVmLimits,
    ) -> bool {
        !self.settling_module_selected(file, name)
        || exists|owner: ModuleBodyPosition| owner.file == file
            && #[trigger] self.matches_settling_hint_owner(owner, name)
            && self.module_calls_result(owner, limits.width, Ok(None))
    }

    /// 元の宣言と、ゲート数と上界を求めた VM の対応を示す。
    pub proof fn module_expansion_hint_vm(
        &self, project: &CircuitProject, targets: &UseTargets,
        file: usize, name: usize, limits: ClockedModuleVmLimits, hint: ModuleExpansionHint,
    ) -> (witness: (ModuleBodyPosition, ClockedModuleVm))
        requires
            use_targets_match(project, *targets),
            use_aliases_match(targets, *self),
            self.module_expansion_hint_matches(file, name, limits, hint),
        ensures
            witness.0.file == file,
            file < project.circuits_model().len() && file < project.sources_model().len(),
            ({
                let circuit = project.circuits_model()[file as int];
                &&& name < circuit.names@.len()
                &&& witness.0.entry < circuit.syntax.entries@.len()
                &&& circuit.syntax.entries@[witness.0.entry as int].head is Module
                &&& circuit.syntax.entries@[witness.0.entry as int].form == circuit.names@[name as int].form
                &&& hint.location.source == &project.sources_model()[file as int]
                &&& hint.location.span == circuit.names@[name as int].name.span
            }),
            witness.1.vm.valid(),
            self.clocked_module_vm_wiring(witness.0, limits, &witness.1)
                || self.clocked_module_hierarchy_vm(witness.0, limits, &witness.1),
            hint.nor_gates == witness.1.vm.netlist_model().gates@.len(),
            witness.1.vm.settling_bound_matches(hint.settling_ticks),
    {
        targets.matched_project(project);
        assert(*self.targets == *targets);
        choose|pair: (ModuleBodyPosition, ClockedModuleVm)|
            pair.0.file == file
            && #[trigger] self.settling_hint_witness(pair.0, name, limits, hint.settling_ticks, pair.1)
            && hint.nor_gates == pair.1.vm.netlist_model().gates@.len()
    }

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
        match self.module_expansion_hint(file, name, limits)? {
            None => Ok(None),
            Some(expansion) => {
                let ghost pair = choose|pair: (ModuleBodyPosition, ClockedModuleVm)|
                    pair.0.file == file
                    && #[trigger] self.settling_hint_witness(pair.0, name, limits, expansion.settling_ticks, pair.1)
                    && expansion.nor_gates == pair.1.vm.netlist_model().gates@.len();
                if let Some(ticks) = expansion.settling_ticks {
                    let hint = ModuleSettlingHint { location: expansion.location, ticks };
                    proof {
                        assert(Some(hint.ticks) == expansion.settling_ticks);
                        assert(pair.0.file == file && self.settling_hint_witness(pair.0, name, limits, Some(hint.ticks), pair.1));
                        assert(exists|witness: (ModuleBodyPosition, ClockedModuleVm)| witness.0.file == file
                            && #[trigger] self.settling_hint_witness(witness.0, name, limits, Some(hint.ticks), witness.1));
                    }
                    Ok(Some(hint))
                } else {
                    proof {
                        assert(self.matches_settling_hint_owner(pair.0, name));
                        assert(self.settling_hint_witness(pair.0, name, limits, None, pair.1));
                        assert(exists|compiled: ClockedModuleVm| #[trigger] self.settling_hint_witness(
                            pair.0, name, limits, None, compiled,
                        ));
                    }
                    Ok(None)
                }
            }
        }
    }

    /// 指定した名前索引のモジュールを展開し、NOR ゲート数と定常化の上界を返す。
    ///
    /// ゲートのフィードバックや状態素子のため上界を推定できない場合も、展開に成功すればゲート数を返す。
    /// 対象がモジュール宣言を指さない場合は `Ok(None)` を返す。
    /// プロジェクト全体の基底は先に [`crate::project::validate_circuit_basis`] で検査する。
    /// 表示位置には元のソースの UTF-8 バイト範囲 `location.span.end` を使う。
    ///
    /// # Errors
    ///
    /// 型検査、結線検査、階層展開、または資源上限で失敗したときにコンパイルの診断を返す。
    pub fn module_expansion_hint(
        &self, file: usize, name: usize, limits: ClockedModuleVmLimits,
    ) -> (result: Result<Option<ModuleExpansionHint<'p, 'a>>, ClockedModuleVmError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            result matches Ok(Some(hint)) ==> self.module_expansion_hint_matches(file, name, limits, hint),
            result matches Ok(None) ==> self.module_expansion_hint_unavailable(file, name, limits),
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
        let hint = ModuleExpansionHint {
            location: LocatedName { source, span: form.name.span.start..form.name.span.end },
            nor_gates: compiled.vm.nor_gate_count(),
            settling_ticks: compiled.vm.settling_bound(),
        };
        proof {
            let model = self.targets.project_model();
            assert(hint.location.source == &model.sources_model()[file as int]);
            assert(hint.location.span == model.circuits_model()[file as int].names@[name as int].name.span);
            let pair = (owner, compiled);
            assert(self.settling_hint_witness(pair.0, name, limits, hint.settling_ticks, pair.1));
            assert(exists|pair: (ModuleBodyPosition, ClockedModuleVm)| pair.0.file == file
                && #[trigger] self.settling_hint_witness(pair.0, name, limits, hint.settling_ticks, pair.1)
                && hint.nor_gates == pair.1.vm.netlist_model().gates@.len());
        }
        Ok(Some(hint))
    }
}

} // verus!
