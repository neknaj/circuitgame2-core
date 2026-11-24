//! 右辺全体を占める呼び出しやビット選択から、左辺の信号に型を割り当てる。

mod aliases;
mod argument_wiring;
pub use argument_wiring::ClockedArgumentWiringError;
pub use aliases::{ModuleAliasSource, ModuleTypeSources};
mod clocked_plan;
mod clocked_source;
mod source_arguments;
mod storage_placement;
pub use storage_placement::{ClockedStorageLayout, ClockedStorageLayoutError, ClockedStoragePlacement};
pub use clocked_source::ClockedModuleError;
pub use clocked_plan::{ClockedLinkPlan, ClockedPlanError, ClockedWireDriver, plan_clocked_links};
#[cfg(verus_only)]
pub use clocked_plan::{clocked_link_plan_result, clocked_regions_cover, clocked_wire_at, clocked_wire_cycle,
    clocked_wire_solutions_agree, clocked_wires_match};
mod calls;
pub use calls::{CheckedModuleCall, ModuleCalls, ModuleCallsError, ModuleInferredCallError};
mod driver_bits;
pub use driver_bits::{ClockedDriverBitsError, clocked_driver_bits};
#[cfg(verus_only)]
pub use driver_bits::{clocked_driver_bit, clocked_driver_bits_result, clocked_driver_port_model, clocked_driver_selection_matches};
mod definition_layout;
pub use definition_layout::ClockedDefinitionLayoutError;
mod concats;
pub use concats::{ModuleConcat, ModuleConcatOperand, ModuleConcats, ModuleConcatsError};
mod output_wiring;
pub use output_wiring::{ClockedModuleOutputs, ClockedModuleOutputsError};
mod outputs;
pub use outputs::{ModuleOutputTypes, ModuleOutputTypesError};
mod primitive_nor;
pub use primitive_nor::PrimitiveModuleError;
mod propagation;
pub use propagation::{ModuleAliasCycleStep, ModuleAliasTypes, ModuleAliasTypesError};
mod selections;
pub use selections::{ModuleSelection, ModuleSelections, ModuleSelectionsError};

use super::{DefinitionDriver, DefinitionPosition, ModuleCallPortsError, ModuleWiring, ModuleWiringError, UseAliases};
use super::function_atoms::copy_location;
use crate::project::{LocatedName, ModuleBodyPosition, PortDirection, ProjectSource, ResolvedPortType, SelectionArgumentError, SignalType, circuits::form_location};
use super::selection_arguments::read_selection_parameters;
#[cfg(verus_only)]
use super::selection_arguments::selection_parameters_match;
#[cfg(verus_only)]
use super::{ModuleCallPorts, function_drivers::indexed_driver_site};
#[cfg(verus_only)]
use crate::project::{CircuitProject, location_in_source, circuits::{is_form_location, parsed_index_evidence}};
use crate::syntax::{Form, circuit::{BuildDefinition, bit_selection_shape, definition_root_is_call, definition_target_atoms}};
#[cfg(verus_only)]
use crate::syntax::{form_spans_valid, circuit::{BitSelectionShape, bit_selection_shape_matches, build_definition_scope_evidence,
    build_entry_ranges_evidence, definition_target_range, definition_targets_match, ordinary_call_at}};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// モジュールの配線と、呼び出しの署名やビット選択の選択数から決まる信号型。
#[derive(Debug)]
pub struct ModuleRootTypes<'p, 'a> {
    /// 全断片から得た信号の駆動元と束縛。
    pub wiring: ModuleWiring<'p, 'a>,
    /// `wiring.drivers.definitions` と同じ順の型。この段階で型を決めない右辺は `None`。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

/// 呼び出しやビット選択の出力型を決めるまでに見つかった診断。
#[derive(Debug)]
pub enum ModuleRootTypesError<'p, 'a> {
    /// 駆動元または信号の参照に関する診断。
    Wiring(ModuleWiringError<'p, 'a>),
    /// 右辺全体を占める通常呼び出しの診断。
    Call(ModuleCallPortsError<'p, 'a>),
    /// ビット選択の数値引数に違反がある。
    SelectionArgument(SelectionArgumentError<'p, 'a>),
    /// 出力が一つのビット選択を複数の左辺に割り当てた。
    SelectionOutputs {
        /// ビット選択式全体のソース範囲。
        expression: LocatedName<'p, 'a>,
        /// 左辺全体のソース範囲。
        left: LocatedName<'p, 'a>,
        /// 左辺の名前の数。
        targets: usize,
    },
}

spec fn selection_root_type(
    source: &ProjectSource, forms: Seq<Form>, row: BuildDefinition, result: Result<Option<SignalType>, ModuleRootTypesError>,
) -> bool {
    let root = row.expression.start as int;
    match result {
        Ok(None) => forall|shape: BitSelectionShape| !#[trigger] bit_selection_shape_matches(source.text, forms, root, shape),
        _ => exists|shape: BitSelectionShape| #[trigger] bit_selection_shape_matches(source.text, forms, root, shape) && {
            let (start, end) = definition_target_range(forms, row);
            if end - start != 1 {
                result matches Err(ModuleRootTypesError::SelectionOutputs { expression, left, targets })
                    && targets == end - start && is_form_location(source, forms[root], expression)
                    && is_form_location(source, forms[row.form + 2], left)
            } else {
                match result {
                    Ok(Some(ty)) => ty.ty is Bits && 0 < ty.ty->Bits_0 && is_form_location(source, forms[root], ty.origin)
                        && exists|start: u64, stride: u64, last: usize| #[trigger]
                            selection_parameters_match(source, forms, &shape, Ok((start, ty.ty->Bits_0, stride, last))),
                    Err(ModuleRootTypesError::SelectionArgument(error)) => selection_parameters_match(source, forms, &shape, Err(error)),
                    _ => false,
                }
            }
        },
    }
}

fn check_selection_root<'p, 'a>(source: &'p ProjectSource<'a>, forms: &[Form], row: &BuildDefinition)
    -> (result: Result<Option<SignalType<'p, 'a>>, ModuleRootTypesError<'p, 'a>>)
    requires
        row.expression.start < forms@.len(), definition_targets_match(forms@, *row),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures selection_root_type(source, forms@, *row, result),
{
    let root = row.expression.start;
    let Some(shape) = bit_selection_shape(source.text, forms, root) else { return Ok(None); };
    assert(bit_selection_shape_matches(source.text, forms@, root as int, shape));
    let left = definition_target_atoms(forms, row);
    let targets = left.end - left.start;
    let expression = form_location(source, forms, root);
    if targets != 1 {
        let left = form_location(source, forms, row.form + 2);
        return Err(ModuleRootTypesError::SelectionOutputs { expression, left, targets });
    }
    let (_start, count, _stride, _last) = match read_selection_parameters(source, forms, root, &shape) {
        Ok(numbers) => numbers,
        Err(error) => return Err(ModuleRootTypesError::SelectionArgument(error)),
    };
    let ty = SignalType { ty: ResolvedPortType::Bits(count), origin: expression };
    proof {
        assert(ty.ty->Bits_0 == count && is_form_location(source, forms@[root as int], ty.origin));
        assert(exists|start: u64, stride: u64, last: usize| #[trigger]
            selection_parameters_match(source, forms@, &shape, Ok((start, ty.ty->Bits_0, stride, last)))) by {
            assert(selection_parameters_match(source, forms@, &shape, Ok((_start, ty.ty->Bits_0, _stride, _last))));
        };
        assert(selection_root_type(source, forms@, *row, Ok(Some(ty))));
    }
    Ok(Some(ty))
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
        result: Result<Option<SignalType>, ModuleRootTypesError>,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[at.file as int];
        let source = &project.sources_model()[at.file as int];
        let row = parsed.definitions@[driver.definition as int];
        let start = parsed.entry_ranges@[at.entry as int].definitions.start;
        let reference = DefinitionPosition { file: at.file, entry: at.entry,
            definition: (driver.definition - start) as usize, reference: 0 };
        &&& (result matches Ok(Some(ty)) ==> location_in_source(ty.origin))
        &&& if ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int) {
            match result {
                Ok(Some(ty)) => exists|call: ModuleCallPorts|
                    #[trigger] self.module_call_ports_result(reference, max_width, Ok(Some(call)))
                    && direct_output_type(&call, driver.result_index, ty),
                Err(ModuleRootTypesError::Call(error)) => self.module_call_ports_result(reference, max_width, Err(error)),
                _ => false,
            }
        } else { selection_root_type(source, parsed.syntax.forms@, row, result) }
    }

    fn check_root_type(&self, at: ModuleBodyPosition, driver: &DefinitionDriver<'a>, max_width: u64)
        -> (result: Result<Option<SignalType<'p, 'a>>, ModuleRootTypesError<'p, 'a>>)
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
            return check_selection_root(source, parsed.syntax.forms.as_slice(), row);
        }
        let local = driver.definition - parsed.entry_ranges[at.entry].definitions.start;
        let reference = DefinitionPosition { file: at.file, entry: at.entry, definition: local, reference: 0 };
        assert(self.module_call_at(reference));
        let call = match self.check_module_call_ports(reference, max_width) {
            Ok(Some(call)) => call,
            Ok(None) => {
                proof { self.module_call_ports_present(reference, max_width); }
                unreachable!()
            },
            Err(error) => return Err(ModuleRootTypesError::Call(error)),
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
        proof { self.module_call_port_location(reference, max_width, call.signature, PortDirection::Output, driver.result_index, port); }
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
            Err(error) => exists|wiring: ModuleWiring, before: Seq<Option<SignalType>>|
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
            forall|i: int| 0 <= i < typed.types@.len() ==>
                ((#[trigger] typed.types@[i]) matches Some(ty) ==> location_in_source(ty.origin)),
    {
        reveal(UseAliases::root_types_prefix);
    }

    /// 右辺の型として得た構造体が、呼び出し先の名前解決済みの宣言を指すことを示す。
    pub(super) proof fn module_root_type_declarations(
        &self, owner: ModuleBodyPosition, limit: u64, typed: ModuleRootTypes,
    )
        requires self.module_root_types_result(owner, limit, Ok(Some(typed))),
        ensures self.module_types_declared(typed.types@),
    {
        reveal(UseAliases::root_types_prefix);
        assert forall|i: int| 0 <= i < typed.types@.len() implies
            ((#[trigger] typed.types@[i]) matches Some(ty) ==> self.declared_port_type(ty.ty)) by {
            if let Some(ty) = typed.types@[i] {
                let wiring = typed.wiring;
                let at = wiring.drivers.origins@[i];
                let driver = wiring.drivers.definitions@[i];
                assert(self.root_type(at, driver, limit, Ok(Some(ty))));
                let project = self.targets.project_model();
                let parsed = &project.circuits_model()[at.file as int];
                let source = &project.sources_model()[at.file as int];
                let row = parsed.definitions@[driver.definition as int];
                if ordinary_call_at(source.text, parsed.syntax.forms@, row.expression.start as int, row.expression.end as int) {
                    let first = parsed.entry_ranges@[at.entry as int].definitions.start;
                    let reference = DefinitionPosition { file: at.file, entry: at.entry,
                        definition: (driver.definition - first) as usize, reference: 0 };
                    let call = choose|call: ModuleCallPorts|
                        #[trigger] self.module_call_ports_result(reference, limit, Ok(Some(call)))
                        && direct_output_type(&call, driver.result_index, ty);
                    let port = choose|port: crate::project::CallPortType|
                        #[trigger] call.signature.target.port_matches(PortDirection::Output, driver.result_index, Some(port))
                        && ty.ty == port.ty
                        && ty.origin == match port.annotation {
                            Some(annotation) => *annotation,
                            None => LocatedName { source: call.signature.source, span: call.signature.call.span },
                        };
                    self.module_call_ports_evidence(reference, limit, call);
                    self.module_call_port_type_declared(reference, limit, call.signature, PortDirection::Output, driver.result_index, port);
                } else {
                    assert(ty.ty is Bits);
                }
            }
        };
    }

    /// 型表にある各構造体型が、このプロジェクトの宣言を指す。
    pub(super) open spec fn module_types_declared(&self, types: Seq<Option<SignalType>>) -> bool {
        forall|i: int| 0 <= i < types.len() ==>
            ((#[trigger] types[i]) matches Some(ty) ==> self.declared_port_type(ty.ty))
    }

    /// 全断片の右辺全体を占める通常呼び出しやビット選択から、左辺の型を求める。
    ///
    /// 呼び出しの出力型は署名、ビット選択の出力幅は選択数で決まる。引数や選択対象が
    /// 後続定義を参照していても取り出せる。入力の型と選択範囲は後段で検査する。
    /// `max_width` はこの段階では署名に適用する。ビット選択の幅は選択範囲とともに検査する。
    ///
    /// # Errors
    ///
    /// 配線を検査した後、本体順・定義順に呼び出しとビット選択を検査して最初の違反を返す。
    /// ビット選択では左辺の名前数を先に検査する。
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
                Err(error) => return Err(error),
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
