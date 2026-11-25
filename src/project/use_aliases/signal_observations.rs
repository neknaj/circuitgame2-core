//! 型と束縛を検査した回路から、エディタで使う信号名の範囲を取り出す。

use alloc::{vec, vec::Vec};
use vstd::prelude::*;

use super::{
    DefinitionDriver, FuncSignalTypeError, FuncWiringResult, ModuleSelectionsError, OutputDriver,
    ResolvedPortType, SignalType, TypedRoutineSignature, UseAliases,
    function_atoms::{copy_location, copy_signal_type}, function_drivers::name_location,
};
use crate::project::{CircuitProject, LocatedName, ModuleBodyPosition, circuits::form_location};
#[cfg(verus_only)]
use crate::project::{ProjectSource, location_in_source, circuits::{is_form_location, name_in_source, parsed_index_evidence}};
#[cfg(verus_only)]
use crate::syntax::{Form, form_spans_valid};
#[cfg(verus_only)]
use super::{BoundFuncSignal, BoundModuleSignal, FuncSignalTypes, ModuleSelections, ModuleWiring, port_types::typed_name_sites};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 回路内での信号の役割。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SignalRole {
    /// 入力ポートまたは入力から値を得る参照。
    Input,
    /// 出力ポートまたは出力を駆動する定義とその参照。
    Output,
    /// 出力ポートを駆動しない局所定義とその参照。
    Local,
}

/// 元ソースにおける信号名の使い方。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SignalOccurrenceKind {
    /// `in` または `out` のポート名。
    PortDeclaration,
    /// `def` の左辺にある名前。
    Definition,
    /// `def` の右辺にある名前。
    Reference,
}

/// 元の名前、その駆動元、現在判明している型と幅。
#[derive(Debug)]
pub struct SignalOccurrence<'p, 'a> {
    /// 指定した文書の版と、信号名の UTF-8 半開バイト範囲。
    pub site: LocatedName<'p, 'a>,
    /// 値を供給する入力ポートまたは `def` の左辺。同じモジュールの別ファイルを指す場合がある。
    pub binding: LocatedName<'p, 'a>,
    /// 入力、出力、局所信号のいずれに当たるか。
    pub role: SignalRole,
    /// この位置が宣言、定義、参照のいずれか。
    pub occurrence: SignalOccurrenceKind,
    /// ポートでは宣言型、定義と参照では駆動元の型。型が判明していれば、その根拠の位置も保持する。
    pub ty: Option<SignalType<'p, 'a>>,
    /// ビット列型ならその幅。未確定の型や構造体型では `None`。
    pub width: Option<u64>,
}

/// 出現箇所と駆動元の範囲が文書に含まれ、幅が判明したビット列型と一致することを表す。
pub open spec fn signal_occurrence_valid(row: SignalOccurrence) -> bool {
    &&& location_in_source(row.site)
    &&& location_in_source(row.binding)
    &&& row.width == match row.ty {
        Some(SignalType { ty: ResolvedPortType::Bits(width), .. }) => Some(width),
        _ => None,
    }
}

spec fn signal_width(ty: Option<SignalType>) -> Option<u64> {
    match ty {
        Some(SignalType { ty: ResolvedPortType::Bits(width), .. }) => Some(width),
        _ => None,
    }
}

spec fn driver_in_bounds(driver: OutputDriver, inputs: nat, definitions: nat) -> bool {
    match driver {
        OutputDriver::Input(index) => index < inputs,
        OutputDriver::Definition(index) => index < definitions,
    }
}

struct SignalBindings<'p, 'a> {
    inputs: Vec<SignalOccurrence<'p, 'a>>,
    outputs: Vec<SignalOccurrence<'p, 'a>>,
    definitions: Vec<SignalOccurrence<'p, 'a>>,
}

impl<'p, 'a> SignalBindings<'p, 'a> {
    spec fn driver_model(&self, driver: OutputDriver) -> SignalOccurrence<'p, 'a> {
        match driver {
            OutputDriver::Input(index) => self.inputs@[index as int],
            OutputDriver::Definition(index) => self.definitions@[index as int],
        }
    }

    fn driver(&self, driver: OutputDriver) -> (row: &SignalOccurrence<'p, 'a>)
        requires driver_in_bounds(driver, self.inputs@.len(), self.definitions@.len()),
        ensures *row == self.driver_model(driver),
    {
        match driver {
            OutputDriver::Input(index) => &self.inputs[index],
            OutputDriver::Definition(index) => &self.definitions[index],
        }
    }
}

fn occurrence<'p, 'a>(
    site: LocatedName<'p, 'a>, binding: &LocatedName<'p, 'a>, role: SignalRole,
    kind: SignalOccurrenceKind, ty: Option<SignalType<'p, 'a>>,
) -> (row: SignalOccurrence<'p, 'a>)
    ensures row.site == site, row.binding == *binding, row.role == role,
        row.occurrence == kind, row.ty == ty, row.width == signal_width(ty),
{
    let width = match &ty {
        Some(SignalType { ty: ResolvedPortType::Bits(width), .. }) => Some(*width),
        _ => None,
    };
    SignalOccurrence { site, binding: copy_location(binding), role, occurrence: kind, ty, width }
}

spec fn definition_positions(origins: Option<&[ModuleBodyPosition]>) -> Option<Seq<ModuleBodyPosition>> {
    match origins {
        Some(positions) => Some(positions@),
        None => None,
    }
}

spec fn observe_definition_file(owner: usize, origins: Option<Seq<ModuleBodyPosition>>, index: int) -> usize {
    match origins {
        Some(positions) => positions[index].file,
        None => owner,
    }
}

spec fn definition_occurrence_matches(
    row: SignalOccurrence, source: &ProjectSource, definition: DefinitionDriver,
    ty: Option<SignalType>, drives_output: bool,
) -> bool {
    &&& *row.site.source == *source && row.site.span == definition.name.span
    &&& row.binding == row.site && row.ty == ty
    &&& row.role == if drives_output { SignalRole::Output } else { SignalRole::Local }
    &&& row.occurrence == SignalOccurrenceKind::Definition
    &&& signal_occurrence_valid(row)
}

spec fn port_occurrence_matches(
    row: SignalOccurrence, source: &ProjectSource, form: Form, port: super::TypedPort,
    binding: LocatedName, role: SignalRole,
) -> bool {
    &&& is_form_location(source, form, row.site)
    &&& row.binding == binding
    &&& row.ty == Some(SignalType { ty: port.ty, origin: port.annotation })
    &&& row.role == role && row.occurrence == SignalOccurrenceKind::PortDeclaration
    &&& signal_occurrence_valid(row)
}

spec fn bindings_match(
    project: &CircuitProject, owner: usize, signature: &TypedRoutineSignature,
    definitions: Seq<DefinitionDriver>, origins: Option<Seq<ModuleBodyPosition>>,
    output_drivers: Seq<OutputDriver>, types: Seq<Option<SignalType>>, result: &SignalBindings,
) -> bool {
    let source = &project.sources_model()[owner as int];
    let forms = project.circuits_model()[owner as int].syntax.forms@;
    &&& owner < project.sources_model().len()
    &&& owner < project.circuits_model().len()
    &&& result.inputs@.len() == signature.inputs@.len()
    &&& result.outputs@.len() == signature.outputs@.len()
    &&& result.definitions@.len() == definitions.len()
    &&& forall|i: int| 0 <= i < result.inputs@.len() ==> {
        let row = #[trigger] result.inputs@[i];
        let port = signature.inputs@[i];
        port_occurrence_matches(row, source, forms[port.declared.site.name as int], port, row.site, SignalRole::Input)
    }
    &&& forall|i: int| 0 <= i < result.outputs@.len() ==> {
        let row = #[trigger] result.outputs@[i];
        let port = signature.outputs@[i];
        port_occurrence_matches(row, source, forms[port.declared.site.name as int], port,
            result.driver_model(output_drivers[i]).binding, SignalRole::Output)
    }
    &&& forall|i: int| 0 <= i < result.definitions@.len() ==> {
        let row = #[trigger] result.definitions@[i];
        let file = observe_definition_file(owner, origins, i);
        definition_occurrence_matches(row, &project.sources_model()[file as int], definitions[i], types[i],
            output_drivers.contains(OutputDriver::Definition(i as usize)))
    }
}

spec fn usable_definition_site(
    project: &CircuitProject, owner: usize, definitions: Seq<DefinitionDriver>,
    origins: Option<Seq<ModuleBodyPosition>>, index: int,
) -> bool {
    let file = observe_definition_file(owner, origins, index);
    &&& file < project.sources_model().len()
    &&& name_in_source(project.sources_model()[file as int].text, definitions[index].name)
}

spec fn definition_sites_match(
    project: &CircuitProject, owner: usize, definitions: Seq<DefinitionDriver>,
    origins: Option<Seq<ModuleBodyPosition>>,
) -> bool {
    forall|i: int| 0 <= i < definitions.len() ==>
        #[trigger] usable_definition_site(project, owner, definitions, origins, i)
}

fn signal_bindings<'p, 'a>(
    project: &'p CircuitProject<'a>, owner: usize, signature: &TypedRoutineSignature<'p, 'a>,
    definitions: &[DefinitionDriver<'a>], origins: Option<&[ModuleBodyPosition]>,
    output_drivers: &[OutputDriver], types: &[Option<SignalType<'p, 'a>>],
) -> (result: SignalBindings<'p, 'a>)
    requires
        owner < project.sources_model().len(), owner < project.circuits_model().len(),
        output_drivers@.len() == signature.outputs@.len(),
        types@.len() == definitions@.len(),
        origins matches Some(positions) ==> positions@.len() == definitions@.len(),
        forall|i: int| 0 <= i < output_drivers@.len() ==>
            driver_in_bounds(#[trigger] output_drivers@[i], signature.inputs@.len(), definitions@.len()),
        ({
            let forms = project.circuits_model()[owner as int].syntax.forms@;
            let source = &project.sources_model()[owner as int];
            &&& typed_name_sites(forms, signature.inputs@) && typed_name_sites(forms, signature.outputs@)
            &&& form_spans_valid(source.text, forms, source.text.spec_bytes().len() as int)
        }),
        definition_sites_match(project, owner, definitions@, definition_positions(origins)),
    ensures
        bindings_match(project, owner, signature, definitions@, definition_positions(origins), output_drivers@, types@, &result),
{
    let source = &project.sources()[owner];
    let forms = project.circuits()[owner].syntax.forms.as_slice();
    let mut result = SignalBindings { inputs: Vec::new(), outputs: Vec::new(), definitions: Vec::new() };

    let mut index = 0;
    while index < signature.inputs.len()
        invariant
            index == result.inputs@.len() <= signature.inputs@.len(),
            owner < project.sources_model().len(), owner < project.circuits_model().len(),
            *source == project.sources_model()[owner as int],
            forms@ == project.circuits_model()[owner as int].syntax.forms@,
            typed_name_sites(forms@, signature.inputs@),
            form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
            forall|i: int| 0 <= i < result.inputs@.len() ==> {
                let row = #[trigger] result.inputs@[i];
                let port = signature.inputs@[i];
                port_occurrence_matches(row, source, forms@[port.declared.site.name as int], port, row.site, SignalRole::Input)
            },
        decreases signature.inputs@.len() - index,
    {
        let port = &signature.inputs[index];
        let site = form_location(source, forms, port.declared.site.name);
        let ty = SignalType { ty: port.ty, origin: copy_location(&port.annotation) };
        result.inputs.push(occurrence(
            copy_location(&site), &site, SignalRole::Input, SignalOccurrenceKind::PortDeclaration, Some(ty),
        ));
        index += 1;
    }

    let mut drives_output = vec![false; definitions.len()];
    let mut index = 0;
    assert forall|slot: usize| slot < drives_output@.len() implies
        (#[trigger] drives_output@[slot as int]) == output_drivers@.take(0).contains(OutputDriver::Definition(slot)) by {};
    while index < output_drivers.len()
        invariant
            drives_output@.len() == definitions@.len(),
            index <= output_drivers@.len(),
            forall|i: int| 0 <= i < output_drivers@.len() ==>
                driver_in_bounds(#[trigger] output_drivers@[i], signature.inputs@.len(), definitions@.len()),
            forall|slot: usize| slot < drives_output@.len() ==>
                (#[trigger] drives_output@[slot as int]) == output_drivers@.take(index as int).contains(OutputDriver::Definition(slot)),
        decreases output_drivers@.len() - index,
    {
        let ghost before = drives_output@;
        if let OutputDriver::Definition(slot) = output_drivers[index] {
            drives_output.set(slot, true);
        }
        proof {
            let prefix = output_drivers@.take(index as int);
            let driver = output_drivers@[index as int];
            assert(output_drivers@.take(index as int + 1) =~= prefix.push(driver));
            assert forall|slot: usize| slot < drives_output@.len() implies
                (#[trigger] drives_output@[slot as int]) == prefix.push(driver).contains(OutputDriver::Definition(slot)) by {
                if driver != OutputDriver::Definition(slot) {
                    assert(drives_output@[slot as int] == before[slot as int]);
                }
                vstd::seq_lib::lemma_seq_contains_after_push(prefix, driver, OutputDriver::Definition(slot));
            };
        }
        index += 1;
    }
    assert(output_drivers@.take(index as int) =~= output_drivers@);
    let mut index = 0;
    while index < definitions.len()
        invariant
            index == result.definitions@.len() <= definitions@.len() == types@.len() == drives_output@.len(),
            origins matches Some(positions) ==> positions@.len() == definitions@.len(),
            forall|slot: usize| slot < drives_output@.len() ==>
                (#[trigger] drives_output@[slot as int]) == output_drivers@.contains(OutputDriver::Definition(slot)),
            definition_sites_match(project, owner, definitions@, definition_positions(origins)),
            forall|i: int| 0 <= i < result.definitions@.len() ==> {
                let row = #[trigger] result.definitions@[i];
                let file = observe_definition_file(owner, definition_positions(origins), i);
                definition_occurrence_matches(row, &project.sources_model()[file as int], definitions@[i], types@[i],
                    output_drivers@.contains(OutputDriver::Definition(i as usize)))
            },
        decreases definitions@.len() - index,
    {
        let file = match origins { Some(positions) => positions[index].file, None => owner };
        let definition = &definitions[index];
        assert(usable_definition_site(project, owner, definitions@, definition_positions(origins), index as int));
        assert(file == observe_definition_file(owner, definition_positions(origins), index as int));
        assert(file < project.sources_model().len());
        assert(name_in_source(project.sources_model()[file as int].text, definition.name));
        let site = name_location(&project.sources()[file], &definition.name);
        let role = if drives_output[index] { SignalRole::Output } else { SignalRole::Local };
        result.definitions.push(occurrence(
            copy_location(&site), &site, role, SignalOccurrenceKind::Definition, copy_signal_type(&types[index]),
        ));
        index += 1;
    }

    let mut index = 0;
    while index < signature.outputs.len()
        invariant
            index == result.outputs@.len() <= signature.outputs@.len() == output_drivers@.len(),
            owner < project.sources_model().len(), owner < project.circuits_model().len(),
            *source == project.sources_model()[owner as int],
            forms@ == project.circuits_model()[owner as int].syntax.forms@,
            typed_name_sites(forms@, signature.outputs@),
            form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
            result.inputs@.len() == signature.inputs@.len(), result.definitions@.len() == definitions@.len(),
            forall|i: int| 0 <= i < output_drivers@.len() ==>
                driver_in_bounds(#[trigger] output_drivers@[i], signature.inputs@.len(), definitions@.len()),
            forall|i: int| 0 <= i < result.inputs@.len() ==> signal_occurrence_valid(#[trigger] result.inputs@[i]),
            forall|i: int| 0 <= i < result.definitions@.len() ==> signal_occurrence_valid(#[trigger] result.definitions@[i]),
            forall|i: int| 0 <= i < result.outputs@.len() ==> {
                let row = #[trigger] result.outputs@[i];
                let port = signature.outputs@[i];
                port_occurrence_matches(row, source, forms@[port.declared.site.name as int], port,
                    result.driver_model(output_drivers@[i]).binding, SignalRole::Output)
            },
        decreases signature.outputs@.len() - index,
    {
        let port = &signature.outputs[index];
        let site = form_location(source, forms, port.declared.site.name);
        let driver = result.driver(output_drivers[index]);
        let ty = SignalType { ty: port.ty, origin: copy_location(&port.annotation) };
        let row = occurrence(site, &driver.binding, SignalRole::Output, SignalOccurrenceKind::PortDeclaration, Some(ty));
        result.outputs.push(row);
        index += 1;
    }
    result
}

fn copy_occurrence<'p, 'a>(row: &SignalOccurrence<'p, 'a>) -> (copy: SignalOccurrence<'p, 'a>)
    requires signal_occurrence_valid(*row),
    ensures copy == *row,
{
    occurrence(copy_location(&row.site), &row.binding, row.role, row.occurrence, copy_signal_type(&row.ty))
}

fn reference_occurrence<'p, 'a>(
    site: &LocatedName<'p, 'a>, driver: &SignalOccurrence<'p, 'a>,
) -> (row: SignalOccurrence<'p, 'a>)
    requires location_in_source(*site), signal_occurrence_valid(*driver),
    ensures row == projected_reference(*site, *driver), row.site == *site, signal_occurrence_valid(row),
{
    occurrence(copy_location(site), &driver.binding, driver.role, SignalOccurrenceKind::Reference, copy_signal_type(&driver.ty))
}

spec fn projected_reference<'p, 'a>(
    site: LocatedName<'p, 'a>, driver: SignalOccurrence<'p, 'a>,
) -> SignalOccurrence<'p, 'a> {
    SignalOccurrence { site, binding: driver.binding, role: driver.role, occurrence: SignalOccurrenceKind::Reference,
        ty: driver.ty, width: signal_width(driver.ty) }
}

spec fn function_references<'p, 'a>(
    signals: Seq<BoundFuncSignal<'p, 'a>>, bindings: &SignalBindings<'p, 'a>,
) -> Seq<SignalOccurrence<'p, 'a>> {
    signals.map_values(|signal: BoundFuncSignal<'p, 'a>| projected_reference(signal.site, bindings.driver_model(signal.driver)))
}

spec fn member_references<'p, 'a>(
    signals: Seq<BoundModuleSignal<'p, 'a>>, bindings: &SignalBindings<'p, 'a>,
) -> Seq<SignalOccurrence<'p, 'a>> {
    signals.map_values(|signal: BoundModuleSignal<'p, 'a>| projected_reference(signal.site, bindings.driver_model(signal.driver)))
}

#[verifier::opaque]
spec fn module_definitions<'p, 'a>(
    bindings: &SignalBindings<'p, 'a>, origins: Seq<ModuleBodyPosition>, file: usize, stop: nat,
) -> Seq<SignalOccurrence<'p, 'a>>
    decreases stop,
{
    if stop == 0 { Seq::empty() } else {
        let prev = (stop - 1) as nat;
        let rows = module_definitions(bindings, origins, file, prev);
        if origins[prev as int].file == file { rows.push(bindings.definitions@[prev as int]) } else { rows }
    }
}

#[verifier::opaque]
spec fn module_references<'p, 'a>(
    bindings: &SignalBindings<'p, 'a>, wiring: &ModuleWiring<'p, 'a>, file: usize, stop: nat,
) -> Seq<SignalOccurrence<'p, 'a>>
    decreases stop,
{
    if stop == 0 { Seq::empty() } else {
        let prev = (stop - 1) as nat;
        let rows = module_references(bindings, wiring, file, prev);
        if wiring.drivers.body.members@[prev as int].file == file {
            rows + member_references(wiring.signals@[prev as int]@, bindings)
        } else { rows }
    }
}

fn append_declarations<'p, 'a>(
    result: &mut Vec<SignalOccurrence<'p, 'a>>, records: &[SignalOccurrence<'p, 'a>],
)
    requires forall|i: int| 0 <= i < records@.len() ==> signal_occurrence_valid(#[trigger] records@[i]),
    ensures final(result)@ == old(result)@ + records@,
{
    let mut i = 0;
    while i < records.len()
        invariant
            i <= records@.len(), result@ == old(result)@ + records@.take(i as int),
            forall|j: int| 0 <= j < records@.len() ==> signal_occurrence_valid(#[trigger] records@[j]),
        decreases records@.len() - i,
    {
        result.push(copy_occurrence(&records[i]));
        i += 1;
        assert(result@ =~= old(result)@ + records@.take(i as int));
    }
}

/// 各出現箇所が指定した文書版に属し、範囲が有効であることを表す。
pub open spec fn signal_occurrences_in_document(rows: Seq<SignalOccurrence>, source: ProjectSource) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> {
        let row = #[trigger] rows[i];
        *row.site.source == source && signal_occurrence_valid(row)
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 信号の出現箇所と束縛の出典を調べる対象プロジェクト。
    pub closed spec fn observation_project_model(&self) -> CircuitProject<'a> {
        self.targets.project_model()
    }

    /// 関数の観測列が検査済みの入力、出力、左辺、右辺の束縛と同じ順に対応することを表す。
    pub closed spec fn func_signal_observations_match(
        &self, file: usize, entry: usize, limit: u64, rows: Seq<SignalOccurrence>,
    ) -> bool {
        exists|typed: FuncSignalTypes, bindings: SignalBindings|
            #![trigger self.func_signal_types_evidence(file, entry, limit, Ok(typed)), bindings.inputs@]
            self.func_signal_types_evidence(file, entry, limit, Ok(typed))
                && (typed.literals.wiring matches FuncWiringResult::Checked(wiring) && {
                    let drivers = wiring.drivers;
                    let project = self.observation_project_model();
                    &&& bindings_match(&project, file, &drivers.signature, drivers.definitions@, None,
                        drivers.outputs@, typed.types@, &bindings)
                    &&& rows == bindings.inputs@ + bindings.outputs@ + bindings.definitions@ + function_references(wiring.signals@, &bindings)
                })
    }

    /// モジュールの観測列が指定文書に絞った検査済みの宣言、定義、参照と対応することを表す。
    pub closed spec fn module_signal_observations_match(
        &self, owner: ModuleBodyPosition, file: usize, limit: u64, rows: Seq<SignalOccurrence>,
    ) -> bool {
        exists|typed: ModuleSelections, bindings: SignalBindings|
            #![trigger self.module_selections_result(owner, limit, Ok(Some(typed))), bindings.inputs@]
            self.module_selections_result(owner, limit, Ok(Some(typed))) && {
                let project = self.observation_project_model();
                let wiring = typed.typed.sources.roots.wiring;
                let drivers = wiring.drivers;
                let ports = if file == owner.file { bindings.inputs@ + bindings.outputs@ } else { Seq::empty() };
                &&& bindings_match(&project, owner.file, &drivers.signature, drivers.definitions@,
                    Some(drivers.origins@), drivers.outputs@, typed.types@, &bindings)
                &&& rows == ports + module_definitions(&bindings, drivers.origins@, file, drivers.definitions@.len())
                    + module_references(&bindings, &wiring, file, wiring.signals@.len())
            }
    }

    /// 指定した `func` のポート、左辺、信号参照を順に返す。
    ///
    /// `file` と `entry` は厳格索引の添字。関数がない場合や展開を待つ場合は `None` を返す。
    ///
    /// # Errors
    ///
    /// 束縛や型を検査できない場合は、関数の型検査が返す診断を返す。
    pub fn observe_func_signals(
        &self, file: usize, entry: usize, limit: u64,
    ) -> (result: Result<Option<Vec<SignalOccurrence<'p, 'a>>>, FuncSignalTypeError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            result matches Err(error) ==> self.func_signal_types_evidence(file, entry, limit, Err(error)),
            result == Ok(None) ==> exists|typed: FuncSignalTypes|
                #[trigger] self.func_signal_types_evidence(file, entry, limit, Ok(typed))
                    && !(typed.literals.wiring is Checked),
            result matches Ok(Some(rows)) ==> {
                let project = self.observation_project_model();
                &&& file < project.sources_model().len()
                &&& signal_occurrences_in_document(rows@, project.sources_model()[file as int])
                &&& self.func_signal_observations_match(file, entry, limit, rows@)
            },
    {
        let (typed, _) = self.check_func_signal_projections(file, entry, limit, false, false)?;
        let FuncWiringResult::Checked(wiring) = &typed.literals.wiring else { return Ok(None); };
        let drivers = &wiring.drivers;
        let project = self.targets.project();
        proof {
            self.checked_types_keep_wiring(file, entry, limit, typed, *wiring);
            self.checked_wiring_is_func(file, entry, limit, *wiring);
            parsed_index_evidence(project.sources_model()[file as int], project.circuits_model()[file as int]);
            assert forall|i: int| 0 <= i < drivers.outputs@.len() implies
                driver_in_bounds(#[trigger] drivers.outputs@[i], drivers.signature.inputs@.len(), drivers.definitions@.len()) by {};
            assert forall|i: int| 0 <= i < drivers.definitions@.len() implies
                #[trigger] usable_definition_site(project, file, drivers.definitions@, None, i) by {
                assert(name_in_source(project.sources_model()[file as int].text, drivers.definitions@[i].name));
            };
        }
        let bindings = signal_bindings(
            project, file, &drivers.signature, &drivers.definitions, None, &drivers.outputs, &typed.types,
        );
        let mut rows = Vec::new();
        append_declarations(&mut rows, bindings.inputs.as_slice());
        append_declarations(&mut rows, bindings.outputs.as_slice());
        append_declarations(&mut rows, bindings.definitions.as_slice());
        let ghost selected = project.sources_model()[file as int];
        let ghost declarations = bindings.inputs@ + bindings.outputs@ + bindings.definitions@;
        let ghost refs = function_references(wiring.signals@, &bindings);
        assert(rows@ =~= declarations + refs.take(0));
        let mut i = 0;
        assert(signal_occurrences_in_document(rows@, selected));
        while i < wiring.signals.len()
            invariant
                self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))),
                i <= wiring.signals@.len(),
                refs == function_references(wiring.signals@, &bindings),
                rows@ == declarations + refs.take(i as int),
                signal_occurrences_in_document(rows@, selected),
                selected == project.sources_model()[file as int],
                *project == self.targets.project_model(),
                file < project.sources_model().len(),
                *drivers == wiring.drivers,
                bindings.inputs@.len() == drivers.signature.inputs@.len(),
                bindings.definitions@.len() == drivers.definitions@.len(),
                forall|row: int| 0 <= row < bindings.inputs@.len() ==> signal_occurrence_valid(#[trigger] bindings.inputs@[row]),
                forall|row: int| 0 <= row < bindings.definitions@.len() ==> signal_occurrence_valid(#[trigger] bindings.definitions@[row]),
            decreases wiring.signals@.len() - i,
        {
            let bound = &wiring.signals[i];
            proof {
                self.observed_func_reference(file, entry, limit, *wiring, i as int);
                assert(*bound == wiring.signals@[i as int]);
                assert(*project == self.targets.project_model());
                assert(*bound.site.source == selected);
                assert(driver_in_bounds(bound.driver, bindings.inputs@.len(), bindings.definitions@.len()));
            }
            let driver = bindings.driver(bound.driver);
            assert(signal_occurrence_valid(*driver)) by {
                match bound.driver {
                    OutputDriver::Input(slot) => { assert(*driver == bindings.inputs@[slot as int]); },
                    OutputDriver::Definition(slot) => { assert(*driver == bindings.definitions@[slot as int]); },
                }
            };
            let row = reference_occurrence(&bound.site, driver);
            assert(row.site == bound.site && *row.site.source == selected);
            rows.push(row);
            proof {
                assert(refs[i as int] == projected_reference(bound.site, bindings.driver_model(bound.driver)));
                assert(refs.take(i as int + 1) =~= refs.take(i as int).push(refs[i as int]));
                assert(rows@ =~= declarations + refs.take(i as int + 1));
            }
            i += 1;
        }
        assert(refs.take(i as int) =~= refs);
        assert(self.func_signal_observations_match(file, entry, limit, rows@));
        Ok(Some(rows))
    }

    /// モジュール本体と断片から、指定文書に現れるポート、左辺、信号参照を順に返す。
    ///
    /// `owner` はモジュール本体の位置、`file` は観測する文書の添字。
    /// 駆動元が別の文書にある場合も、その文書と範囲を返す。
    /// 対象文書の添字が範囲外の場合や、指定位置にモジュール本体がない場合は `None` を返す。
    ///
    /// # Errors
    ///
    /// モジュールの束縛や信号型を検査できない場合は、その診断を返す。
    pub fn observe_module_signals(
        &self, owner: ModuleBodyPosition, file: usize, limit: u64,
    ) -> (result: Result<Option<Vec<SignalOccurrence<'p, 'a>>>, ModuleSelectionsError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            result matches Err(error) ==> self.module_selections_result(owner, limit, Err(error)),
            result == Ok(None) ==> file >= self.observation_project_model().sources_model().len()
                || owner.file >= self.observation_project_model().sources_model().len()
                || owner.file >= self.observation_project_model().circuits_model().len()
                || self.module_selections_result(owner, limit, Ok(None)),
            result matches Ok(Some(rows)) ==> {
                let project = self.observation_project_model();
                &&& file < project.sources_model().len()
                &&& signal_occurrences_in_document(rows@, project.sources_model()[file as int])
                &&& self.module_signal_observations_match(owner, file, limit, rows@)
            },
    {
        let project = self.targets.project();
        if file >= project.sources().len() || owner.file >= project.sources().len() || owner.file >= project.circuits().len() {
            return Ok(None);
        }
        let ghost selected = project.sources_model()[file as int];
        let Some(checked) = self.check_module_selections(owner, limit)? else { return Ok(None); };
        let wiring = &checked.typed.sources.roots.wiring;
        let drivers = &wiring.drivers;
        let origins = drivers.origins.as_slice();
        let definitions = drivers.definitions.as_slice();
        proof {
            self.observed_module_selection_tables(owner, limit, checked);
            self.module_observation_wiring(owner, limit, *wiring);
            self.module_output_driver(owner, limit, *drivers, 0);
            self.typed_signature_sites(owner.file, owner.entry, limit, drivers.signature);
            parsed_index_evidence(project.sources_model()[owner.file as int], project.circuits_model()[owner.file as int]);
            assert forall|i: int| 0 <= i < drivers.outputs@.len() implies
                driver_in_bounds(#[trigger] drivers.outputs@[i], drivers.signature.inputs@.len(), drivers.definitions@.len()) by {
                self.module_output_driver(owner, limit, *drivers, i);
            };
            let positions = definition_positions(Some(origins));
            assert forall|i: int| 0 <= i < definitions@.len() implies
                #[trigger] usable_definition_site(project, owner.file, definitions@, positions, i) by {
                assert(definitions@ == drivers.definitions@);
                assert(origins@ == drivers.origins@);
                assert(0 <= i < origins@.len());
                let definition_file = observe_definition_file(owner.file, positions, i);
                assert(definition_file == drivers.origins@[i].file);
                self.module_driver_sites(owner, limit, *drivers, i);
            };
        }
        let bindings = signal_bindings(
            project, owner.file, &drivers.signature, definitions, Some(origins),
            &drivers.outputs, &checked.types,
        );
        let mut rows = Vec::new();
        if file == owner.file {
            append_declarations(&mut rows, bindings.inputs.as_slice());
            append_declarations(&mut rows, bindings.outputs.as_slice());
        }
        let ghost ports = if file == owner.file { bindings.inputs@ + bindings.outputs@ } else { Seq::empty() };
        assert(rows@ =~= ports + module_definitions(&bindings, drivers.origins@, file, 0)) by { reveal(module_definitions); };
        let mut i = 0;
        assert(signal_occurrences_in_document(rows@, selected));
        proof {
            let positions = definition_positions(Some(origins));
            assert forall|j: int| 0 <= j < bindings.definitions@.len() implies {
                let row = #[trigger] bindings.definitions@[j];
                let origin = drivers.origins@[j].file;
                &&& origin < project.sources_model().len()
                &&& signal_occurrence_valid(row) && *row.site.source == project.sources_model()[origin as int]
            } by {
                let origin = drivers.origins@[j].file;
                assert(positions == Some(drivers.origins@));
                assert(observe_definition_file(owner.file, positions, j) == origin);
                assert(usable_definition_site(project, owner.file, definitions@, positions, j));
                assert(definition_occurrence_matches(bindings.definitions@[j], &project.sources_model()[origin as int],
                    definitions@[j], checked.types@[j], drivers.outputs@.contains(OutputDriver::Definition(j as usize))));
            };
        }
        while i < drivers.origins.len()
            invariant
                i <= drivers.origins@.len() == bindings.definitions@.len(),
                rows@ == ports + module_definitions(&bindings, drivers.origins@, file, i as nat),
                signal_occurrences_in_document(rows@, selected),
                selected == project.sources_model()[file as int],
                file < project.sources_model().len(),
                forall|j: int| 0 <= j < bindings.definitions@.len() ==> {
                    let row = #[trigger] bindings.definitions@[j];
                    let origin = drivers.origins@[j].file;
                    &&& origin < project.sources_model().len()
                    &&& signal_occurrence_valid(row) && *row.site.source == project.sources_model()[origin as int]
                },
            decreases drivers.origins@.len() - i,
        {
            if drivers.origins[i].file == file {
                rows.push(copy_occurrence(&bindings.definitions[i]));
            }
            assert(rows@ =~= ports + module_definitions(&bindings, drivers.origins@, file, (i + 1) as nat)) by {
                reveal(module_definitions);
            };
            i += 1;
        }
        let ghost declared = rows@;
        assert(rows@ =~= declared + module_references(&bindings, wiring, file, 0)) by { reveal(module_references); };
        let mut member = 0;
        while member < drivers.body.members.len()
            invariant
                self.module_wiring_result(owner, limit, Ok(Some(*wiring))),
                member <= drivers.body.members@.len() == wiring.signals@.len(),
                rows@ == declared + module_references(&bindings, wiring, file, member as nat),
                signal_occurrences_in_document(rows@, selected),
                selected == project.sources_model()[file as int],
                *project == self.targets.project_model(),
                file < project.sources_model().len(),
                *drivers == wiring.drivers,
                bindings.inputs@.len() == drivers.signature.inputs@.len(),
                bindings.definitions@.len() == drivers.definitions@.len(),
                forall|j: int| 0 <= j < bindings.inputs@.len() ==> signal_occurrence_valid(#[trigger] bindings.inputs@[j]),
                forall|j: int| 0 <= j < bindings.definitions@.len() ==> signal_occurrence_valid(#[trigger] bindings.definitions@[j]),
            decreases drivers.body.members@.len() - member,
        {
            let ghost before = rows@;
            if drivers.body.members[member].file == file {
                let signals = &wiring.signals[member];
                let ghost refs = member_references(signals@, &bindings);
                assert(rows@ =~= before + refs.take(0));
                let mut i = 0;
                while i < signals.len()
                    invariant
                        self.module_wiring_result(owner, limit, Ok(Some(*wiring))),
                        member < drivers.body.members@.len() == wiring.signals@.len(),
                        drivers.body.members@[member as int].file == file,
                        *signals == wiring.signals@[member as int],
                        i <= signals@.len(),
                        refs == member_references(signals@, &bindings),
                        rows@ == before + refs.take(i as int),
                        signal_occurrences_in_document(rows@, selected),
                        selected == project.sources_model()[file as int],
                        *project == self.targets.project_model(),
                        file < project.sources_model().len(),
                        *drivers == wiring.drivers,
                        bindings.inputs@.len() == drivers.signature.inputs@.len(),
                        bindings.definitions@.len() == drivers.definitions@.len(),
                        forall|j: int| 0 <= j < bindings.inputs@.len() ==> signal_occurrence_valid(#[trigger] bindings.inputs@[j]),
                        forall|j: int| 0 <= j < bindings.definitions@.len() ==> signal_occurrence_valid(#[trigger] bindings.definitions@[j]),
                    decreases signals@.len() - i,
                {
                    let bound = &signals[i];
                    proof {
                        self.module_reference_at(owner, limit, *wiring, member as int, i as int);
                        assert(*bound == wiring.signals@[member as int]@[i as int]);
                        assert(*project == self.targets.project_model());
                        assert(*bound.site.source == selected);
                        assert(driver_in_bounds(bound.driver, bindings.inputs@.len(), bindings.definitions@.len()));
                    }
                    let driver = bindings.driver(bound.driver);
                    assert(signal_occurrence_valid(*driver)) by {
                        match bound.driver {
                            OutputDriver::Input(slot) => { assert(*driver == bindings.inputs@[slot as int]); },
                            OutputDriver::Definition(slot) => { assert(*driver == bindings.definitions@[slot as int]); },
                        }
                    };
                    let row = reference_occurrence(&bound.site, driver);
                    assert(row.site == bound.site && *row.site.source == selected);
                    rows.push(row);
                    proof {
                        assert(refs[i as int] == projected_reference(bound.site, bindings.driver_model(bound.driver)));
                        assert(refs.take(i as int + 1) =~= refs.take(i as int).push(refs[i as int]));
                        assert(rows@ =~= before + refs.take(i as int + 1));
                    }
                    i += 1;
                }
                assert(refs.take(i as int) =~= refs);
            }
            assert(rows@ =~= declared + module_references(&bindings, wiring, file, (member + 1) as nat)) by {
                reveal(module_references);
            };
            member += 1;
        }
        assert(self.module_signal_observations_match(owner, file, limit, rows@));
        Ok(Some(rows))
    }
}

} // verus!
