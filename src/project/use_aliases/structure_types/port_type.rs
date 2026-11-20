//! 配置表が使う位置から、ポート型が保持する構造体宣言を取得する。

use super::{StructurePosition, UseAliases};
use crate::project::ResolvedPortType;
use crate::syntax::circuit::Head;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::DefinitionBinding;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
#[cfg(verus_only)]
use crate::project::declarations::indexed_structure_is_declared;
#[cfg(verus_only)]
use crate::syntax::circuit::{named_form_matches, named_forms_match, named_head};

verus! {

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// プロジェクト内の宣言位置から構造体のポート型を得る。
    ///
    /// 位置はこの別名表を作ったプロジェクト内で指定する。
    /// 指定位置が範囲外か、構造体宣言を指していない場合は `None` を返す。
    ///
    /// # Examples
    ///
    /// 同じ幅でも、別々に宣言した構造体は異なる型になる。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     SourceSnapshot, StructurePosition, check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "types.ncg2", revision: 1, text: "(struct A (width 8)) (struct B (width 8))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let a = aliases.structure_port_type(StructurePosition { file: 0, entry: 0 }).unwrap();
    /// let b = aliases.structure_port_type(StructurePosition { file: 0, entry: 1 }).unwrap();
    /// assert!(!a.is_same_type(&b));
    /// assert!(aliases.structure_port_type(StructurePosition { file: 0, entry: 2 }).is_none());
    /// ```
    pub fn structure_port_type(&self, position: StructurePosition) -> (result: Option<ResolvedPortType<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.structure_port_type_matches(position, result),
    {
        let project = self.targets.project();
        let circuits = project.circuits();
        if position.file >= circuits.len() {
            return None;
        }
        let parsed = &circuits[position.file];
        if position.entry >= parsed.syntax.entries.len() {
            return None;
        }
        let entry = &parsed.syntax.entries[position.entry];
        if !matches!(entry.head, Head::Struct) {
            return None;
        }
        let source = &project.sources()[position.file];
        let names = parsed.names.as_slice();
        let ghost target = {
            parsed_index_evidence(*source, *parsed);
            reveal(named_forms_match);
            assert(named_head(entry.head));
            choose|i: int| 0 <= i < names@.len()
                && #[trigger] named_form_matches(source.text, parsed.syntax.forms@, *entry, names@[i])
        };
        proof {
            self.targets.declarations_cover_project();
            reveal(named_form_matches);
            assert(names@[target].form == entry.form);
        }
        let mut first = 0;
        let mut end = names.len();
        while first < end
            invariant
                first <= target < end <= names@.len(),
                names@ == parsed.names@,
                self.is_structure_position(position),
                position.file < self.targets.project_model().sources_model().len(),
                *source == self.targets.project_model().sources_model()[position.file as int],
                *parsed == self.targets.project_model().circuits_model()[position.file as int],
                *entry == parsed.syntax.entries@[position.entry as int],
                names@[target].form == entry.form && names@[target].head is Struct,
                crate::project::declarations::declaration_table_matches(
                    &self.targets.project_model(), self.targets.exports_model().declarations_model(),
                ),
                forall|i: int, j: int| 0 <= i < j < names@.len() ==>
                    (#[trigger] names@[i]).form < (#[trigger] names@[j]).form,
            decreases end - first,
        {
            let middle = first + (end - first) / 2;
            let name = &names[middle];
            if name.form < entry.form {
                assert(middle < target) by {
                    if target < middle { assert(names@[target].form < names@[middle as int].form); }
                };
                first = middle + 1;
            } else if name.form > entry.form {
                assert(target < middle) by {
                    if middle < target { assert(names@[middle as int].form < names@[target].form); }
                };
                end = middle;
            } else {
                let result = Some(ResolvedPortType::Struct { source, form: name });
                proof {
                    if middle < target { assert(names@[middle as int].form < names@[target].form); }
                    if target < middle { assert(names@[target].form < names@[middle as int].form); }
                    assert(middle == target);
                    reveal(UseAliases::structure_position_matches);
                    indexed_structure_is_declared(
                        &self.targets.project_model(), &self.targets.exports_model().declarations_model(),
                        position.file as int, middle as int, source, name,
                    );
                    assert(self.structure_position_matches(position, DefinitionBinding::Declaration { source, form: name }));
                    assert(exists|i: int| 0 <= i < parsed.names@.len()
                        && (#[trigger] parsed.names@[i]) == *name) by {
                        assert(parsed.names@[middle as int] == *name);
                    };
                    assert(self.structure_port_type_matches(position, result));
                }
                return result;
            }
        }
        None
    }
}

} // verus!
