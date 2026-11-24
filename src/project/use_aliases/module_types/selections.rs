//! 型が判明した信号のビット選択を検査し、元の信号への射影を得る。

use super::{ModuleAliasTypes, ModuleAliasTypesError, ModuleConcat, ModuleConcatsError, UseAliases, aliases::find_member};
#[cfg(verus_only)]
use super::{ModuleConcats, propagation::type_sites_valid};
use crate::project::{CheckedBitSelection, LocatedName, ModuleBodyPosition, OutputDriver, ResolvedPortType,
    SelectionArgumentError, SignalType, circuits::form_location};
use crate::project::use_aliases::{function_atoms::{copy_location, copy_signal_type}, selection_arguments::check_selection_chain};
#[cfg(verus_only)]
use crate::project::{ProjectSource, circuits::{is_form_location, parsed_index_evidence}};
#[cfg(verus_only)]
use crate::project::use_aliases::selection_arguments::selection_chain_arguments_match;
use crate::syntax::{AtomKind, Form, circuit::bit_selection_chain};
#[cfg(verus_only)]
use crate::syntax::circuit::{BitSelectionShape, bit_selection_path, bit_selection_shape_matches,
    bit_selection_shape_positions, bit_selection_step_root, build_definition_scope_evidence,
    build_entry_ranges_evidence, build_selection_chain_signal};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 検査済みのビット選択。複数段の選択は元の信号を参照する一つの射影にまとめる。
#[derive(Debug)]
pub struct ModuleSelection {
    /// ビットを選ぶ元の入力または左辺の駆動元。
    pub driver: OutputDriver,
    /// 元の信号に対する開始位置、選択数、刻み、末尾位置。
    pub projection: CheckedBitSelection,
}

/// 型伝播の結果と、現在検査できたビット選択。
#[derive(Debug)]
pub struct ModuleSelections<'p, 'a> {
    /// 全断片の配線と、連接の幅を伝える前に決まった型。
    pub typed: ModuleAliasTypes<'p, 'a>,
    /// 連接と別名を再評価して得た、左辺の駆動元順の型表。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
    /// 左辺の駆動元順に並んだ、幅が決まった連接。
    pub concats: Vec<Option<ModuleConcat<'p, 'a>>>,
    /// 左辺の駆動元順の射影。選択以外の式や、入力型を保留した選択は `None`。
    pub selections: Vec<Option<ModuleSelection>>,
}

/// 型伝播またはビット選択の検査で見つかった違反。
#[derive(Debug)]
pub enum ModuleSelectionsError<'p, 'a> {
    /// 配線、式の結果幅、または型伝播の診断。
    Types(ModuleAliasTypesError<'p, 'a>),
    /// 連接の型や幅に違反がある。
    Concat(ModuleConcatsError<'p, 'a>),
    /// ビット列以外の型の信号を選択対象にした。
    InputType {
        /// 選択対象として書いた信号名の範囲。
        input: LocatedName<'p, 'a>,
        /// 実際の型とその根拠となるソース範囲。
        actual: SignalType<'p, 'a>,
    },
    /// 選択数や刻み、または選んだ範囲に違反がある。
    Argument(SelectionArgumentError<'p, 'a>),
    /// 結果のビット幅が設定上限を超えた。
    Width {
        /// 選択式全体の範囲。
        expression: LocatedName<'p, 'a>,
        /// 選択結果のビット幅。
        width: u64,
        /// 検査で使ったビット幅上限。
        limit: u64,
    },
}

pub(super) open spec fn bound_type<'p, 'a>(typed: &ModuleAliasTypes<'p, 'a>, types: Seq<Option<SignalType<'p, 'a>>>, driver: OutputDriver) -> Option<SignalType<'p, 'a>> {
    match driver {
        OutputDriver::Input(index) => {
            let port = typed.sources.roots.wiring.drivers.signature.inputs@[index as int];
            Some(SignalType { ty: port.ty, origin: port.annotation })
        },
        OutputDriver::Definition(index) => types[index as int],
    }
}

/// 駆動元の型と根拠位置を取り出す。定義の型が未確定なら `None` を返す。
pub(super) fn read_bound_type<'p, 'a>(typed: &ModuleAliasTypes<'p, 'a>, types: &[Option<SignalType<'p, 'a>>], driver: OutputDriver)
    -> (result: Option<SignalType<'p, 'a>>)
    requires match driver {
        OutputDriver::Input(index) => index < typed.sources.roots.wiring.drivers.signature.inputs@.len(),
        OutputDriver::Definition(index) => index < types@.len(),
    },
    ensures result == bound_type(typed, types@, driver),
{
    match driver {
        OutputDriver::Input(index) => {
            let port = &typed.sources.roots.wiring.drivers.signature.inputs[index];
            Some(SignalType { ty: port.ty, origin: copy_location(&port.annotation) })
        },
        OutputDriver::Definition(index) => copy_signal_type(&types[index]),
    }
}

spec fn checked_range(
    source: &ProjectSource, forms: Seq<Form>, root: usize, leaf: usize, steps: Seq<BitSelectionShape>,
    driver: OutputDriver, base: Option<SignalType>, limit: u64, result: Result<Option<ModuleSelection>, ModuleSelectionsError>,
) -> bool {
    match base {
        None => result == Ok(None),
        Some(actual) => match actual.ty {
            ResolvedPortType::Struct { .. } => result matches Err(ModuleSelectionsError::InputType { input, actual: found })
                && found == actual && is_form_location(source, forms[leaf as int], input),
            ResolvedPortType::Bits(width) => match result {
                Ok(Some(checked)) => checked.driver == driver && checked.projection.count <= limit
                    && checked.projection.fits(width)
                    && selection_chain_arguments_match(source, forms, steps, width, actual.origin, Ok(checked.projection)),
                Err(ModuleSelectionsError::Argument(error)) =>
                    selection_chain_arguments_match(source, forms, steps, width, actual.origin, Err(error)),
                Err(ModuleSelectionsError::Width { expression, width: found, limit: cap }) =>
                    is_form_location(source, forms[root as int], expression) && cap == limit && found > limit
                    && exists|projection: CheckedBitSelection| #[trigger]
                        selection_chain_arguments_match(source, forms, steps, width, actual.origin, Ok(projection))
                        && projection.count == found,
                _ => false,
            },
        },
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn module_selection_at(
        &self, typed: &ModuleAliasTypes, types: Seq<Option<SignalType>>, index: int, limit: u64,
        result: Result<Option<ModuleSelection>, ModuleSelectionsError>,
    ) -> bool {
        let wiring = &typed.sources.roots.wiring;
        let project = self.targets.project_model();
        let at = wiring.drivers.origins@[index];
        let parsed = &project.circuits_model()[at.file as int];
        let source = &project.sources_model()[at.file as int];
        let row = parsed.definitions@[wiring.drivers.definitions@[index].definition as int];
        let forms = parsed.syntax.forms@;
        let root = row.expression.start;
        exists|steps: Seq<BitSelectionShape>, leaf: usize| #[trigger] bit_selection_path(source.text, forms, root, steps, leaf)
            && !(exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source.text, forms, leaf as int, shape))
            && if steps.len() == 0 || !(forms[leaf as int] is Atom && forms[leaf as int]->Atom_kind is Name) {
                result == Ok(None)
            } else {
                exists|member: int| 0 <= member < wiring.drivers.body.members@.len()
                    && (#[trigger] wiring.drivers.body.members@[member]) == at
                    && {
                        let frame = parsed.entry_ranges@[at.entry as int].signals;
                        let bound = wiring.signals@[member]@[row.signals.start - frame.start];
                        bound.form == leaf && checked_range(source, forms, root, leaf, steps, bound.driver,
                            bound_type(typed, types, bound.driver), limit, result)
                    }
            }
    }

    fn check_bound_selection(&self, _owner: ModuleBodyPosition, limit: u64, typed: &ModuleAliasTypes<'p, 'a>,
        types: &[Option<SignalType<'p, 'a>>], index: usize)
        -> (result: Result<Option<ModuleSelection>, ModuleSelectionsError<'p, 'a>>)
        requires
            self.can_resolve(), self.module_alias_types_result(_owner, limit, Ok(Some(*typed))),
            index < typed.sources.roots.wiring.drivers.definitions@.len(),
            types@.len() == typed.sources.roots.wiring.drivers.definitions@.len(), type_sites_valid(types@),
        ensures self.module_selection_at(typed, types@, index as int, limit, result),
    {
        let wiring = &typed.sources.roots.wiring;
        proof {
            self.module_alias_types_evidence(_owner, limit, *typed);
            self.module_wiring_keeps_drivers(_owner, limit, *wiring);
            self.module_driver_sites(_owner, limit, wiring.drivers, index as int);
            self.module_input_sites(_owner, limit, wiring.drivers);
        }
        let at = wiring.drivers.origins[index];
        let driver = &wiring.drivers.definitions[index];
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
        let forms = parsed.syntax.forms.as_slice();
        let root = row.expression.start;
        let (steps, leaf) = bit_selection_chain(source.text, forms, root);
        if steps.is_empty() { return Ok(None); }
        proof {
            let last = steps@.len() as int - 1;
            let position = bit_selection_step_root(root, steps@, last);
            assert(bit_selection_shape_matches(source.text, forms@, position, steps@[last]));
            bit_selection_shape_positions(source.text, forms@, position, steps@[last]);
        }
        if !matches!(forms[leaf], Form::Atom { kind: AtomKind::Name, .. }) { return Ok(None); }
        let member = find_member(wiring.drivers.body.members.as_slice(), at);
        proof {
            build_selection_chain_signal(source.text, &model, at.entry as int, driver.definition as int, steps@, leaf);
            self.module_signal_index_item(_owner, limit, *wiring, member as int, row.signals.start as int);
        }
        let frame = &parsed.entry_ranges[at.entry].signals;
        let bound = &wiring.signals[member][row.signals.start - frame.start];
        let Some(actual) = read_bound_type(typed, types, bound.driver) else { return Ok(None); };
        let ResolvedPortType::Bits(width) = actual.ty else {
            return Err(ModuleSelectionsError::InputType { input: form_location(source, forms, leaf), actual });
        };
        let projection = match check_selection_chain(source, forms, root, steps.as_slice(), leaf, width, &actual.origin) {
            Ok(projection) => projection,
            Err(error) => return Err(ModuleSelectionsError::Argument(error)),
        };
        if projection.count > limit {
            return Err(ModuleSelectionsError::Width { expression: form_location(source, forms, root), width: projection.count, limit });
        }
        Ok(Some(ModuleSelection { driver: bound.driver, projection }))
    }

    #[verifier::opaque]
    spec fn selection_prefix(&self, typed: &ModuleAliasTypes, types: Seq<Option<SignalType>>, limit: u64, selections: Seq<Option<ModuleSelection>>) -> bool {
        &&& selections.len() <= typed.sources.roots.wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < selections.len() ==> self.module_selection_at(typed, types, i, limit, Ok(#[trigger] selections[i]))
    }

    /// 全断片の選択の結果と、最初の違反を元のソースに対応付ける。
    pub closed spec fn module_selections_result(
        &self, owner: ModuleBodyPosition, limit: u64, result: Result<Option<ModuleSelections>, ModuleSelectionsError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_concats_result(owner, limit, Ok(None)),
            Err(ModuleSelectionsError::Types(error)) => self.module_concats_result(owner, limit, Err(ModuleConcatsError::Types(error))),
            Err(ModuleSelectionsError::Concat(error)) => !(error is Types) && self.module_concats_result(owner, limit, Err(error)),
            Ok(Some(checked)) => self.module_concats_result(owner, limit,
                Ok(Some(ModuleConcats { typed: checked.typed, types: checked.types, concats: checked.concats })))
                && checked.selections@.len() == checked.typed.sources.roots.wiring.drivers.definitions@.len()
                && self.selection_prefix(&checked.typed, checked.types@, limit, checked.selections@),
            Err(error) => exists|inferred: ModuleConcats, prefix: Seq<Option<ModuleSelection>>|
                #[trigger] self.module_concats_result(owner, limit, Ok(Some(inferred)))
                && #[trigger] self.selection_prefix(&inferred.typed, inferred.types@, limit, prefix)
                && prefix.len() < inferred.typed.sources.roots.wiring.drivers.definitions@.len()
                && self.module_selection_at(&inferred.typed, inferred.types@, prefix.len() as int, limit, Err(error)),
        }
    }

    /// 完了した式検査から、出力の照合に使う型表と元の駆動元の契約を取り出す。
    pub(super) proof fn module_selections_evidence(&self, owner: ModuleBodyPosition, limit: u64, checked: ModuleSelections)
        requires self.module_selections_result(owner, limit, Ok(Some(checked))),
        ensures
            self.module_alias_types_result(owner, limit, Ok(Some(checked.typed))),
            self.module_wiring_result(owner, limit, Ok(Some(checked.typed.sources.roots.wiring))),
            self.module_drivers_result(owner, limit, Ok(Some(checked.typed.sources.roots.wiring.drivers))),
            checked.types@.len() == checked.typed.sources.roots.wiring.drivers.definitions@.len(),
            type_sites_valid(checked.types@),
    {
        let inferred = ModuleConcats { typed: checked.typed, types: checked.types, concats: checked.concats };
        self.module_concats_evidence(owner, limit, inferred);
        self.module_alias_types_evidence(owner, limit, checked.typed);
        self.module_wiring_keeps_drivers(owner, limit, checked.typed.sources.roots.wiring);
    }

    /// 選択検査が保持する型表から、裸名の定義と駆動元の型の一致を取り出す。
    pub(super) proof fn module_selection_alias_binding(
        &self, owner: ModuleBodyPosition, limit: u64, checked: ModuleSelections, slot: usize,
    )
        requires self.module_selections_result(owner, limit, Ok(Some(checked))),
            slot < checked.typed.sources.aliases@.len(),
        ensures checked.typed.sources.aliases@[slot as int] matches Some(alias) ==>
            (checked.types@[slot as int].is_some() ==> checked.types@[slot as int]
                == bound_type(&checked.typed, checked.types@, alias.driver)),
    {
        self.module_concat_alias_binding(owner, limit,
            ModuleConcats { typed: checked.typed, types: checked.types, concats: checked.concats }, slot);
    }

    /// ビット選択後の型表にある構造体型が、このプロジェクトの宣言を参照することを示す。
    pub(super) proof fn module_selection_type_declarations(&self, owner: ModuleBodyPosition, limit: u64, checked: ModuleSelections)
        requires self.module_selections_result(owner, limit, Ok(Some(checked))),
        ensures self.module_types_declared(checked.types@),
    {
        self.module_concat_type_declarations(owner, limit, ModuleConcats {
            typed: checked.typed, types: checked.types, concats: checked.concats,
        });
    }

    /// 右辺全体がビット選択で、選択をたどると型が判明した信号に行き着く定義を検査する。
    ///
    /// 選択を内側から検査し、元の信号のビット位置へ合成する。ほかの式の選択は後段で扱う。
    ///
    /// # Errors
    ///
    /// 配線、右辺の結果幅、型伝播、連接の違反を先に返す。その後、定義順に選択対象の型、範囲、
    /// 結果幅の上限を検査する。
    pub fn check_module_selections(&self, owner: ModuleBodyPosition, limit: u64)
        -> (result: Result<Option<ModuleSelections<'p, 'a>>, ModuleSelectionsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.module_selections_result(owner, limit, result),
    {
        let inferred = match self.check_module_concats(owner, limit) {
            Ok(Some(inferred)) => inferred,
            Ok(None) => return Ok(None),
            Err(ModuleConcatsError::Types(error)) => return Err(ModuleSelectionsError::Types(error)),
            Err(error) => return Err(ModuleSelectionsError::Concat(error)),
        };
        proof { self.module_concats_evidence(owner, limit, inferred); }
        let typed = &inferred.typed;
        let types = inferred.types.as_slice();
        let count = typed.sources.roots.wiring.drivers.definitions.len();
        let mut selections = Vec::new();
        let mut i = 0;
        assert(self.selection_prefix(typed, types@, limit, selections@)) by { reveal(UseAliases::selection_prefix); };
        while i < count
            invariant
                self.can_resolve(), self.module_alias_types_result(owner, limit, Ok(Some(*typed))),
                self.module_concats_result(owner, limit, Ok(Some(inferred))), *typed == inferred.typed,
                types@ == inferred.types@, types@.len() == count, type_sites_valid(types@),
                i == selections@.len() <= count == typed.sources.roots.wiring.drivers.definitions@.len(),
                self.selection_prefix(typed, types@, limit, selections@),
            decreases count - i,
        {
            let selection = self.check_bound_selection(owner, limit, typed, types, i)?;
            let ghost before = selections@;
            selections.push(selection);
            assert(self.selection_prefix(typed, types@, limit, selections@)) by {
                reveal(UseAliases::selection_prefix);
                assert forall|j: int| 0 <= j < selections@.len() implies
                    self.module_selection_at(typed, types@, j, limit, Ok(#[trigger] selections@[j])) by {
                        if j < i { assert(selections@[j] == before[j]); }
                    };
            };
            i += 1;
        }
        Ok(Some(ModuleSelections { typed: inferred.typed, types: inferred.types, concats: inferred.concats, selections }))
    }
}

} // verus!
