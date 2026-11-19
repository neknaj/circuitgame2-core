//! 組み合わせ回路の明示的な定義から、信号と出力の駆動元を求める。

use super::UseAliases;
#[cfg(verus_only)]
use super::port_types::typed_name_sites;
use crate::project::circuits::read_indexed_atom;
#[cfg(verus_only)]
use crate::project::circuits::{name_in_source, parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::project::declarations::located_name_evidence;
#[cfg(verus_only)]
use crate::project::location_in_source;
use crate::project::signatures::first_matching_name;
use crate::project::{
    LocatedName, ProjectSource, TypedPort, TypedRoutineSignature, TypedSignatureError,
};
use crate::syntax::{
    Form,
    circuit::{
        Head, NameSite, NamedBuildCircuit, definition_target_atoms, first_routine_expansion,
    },
};
#[cfg(verus_only)]
use crate::syntax::{
    circuit::{
        BuildDefinition, build_definition_scope_evidence, build_entry_ranges_evidence,
        build_index_matches, definition_target_range, routine_expansion_evidence,
    },
    form_span, form_spans_valid,
};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::encode_utf8_decode_utf8;

verus! {

/// `def` の左辺にある一つの信号の駆動元。
#[derive(Debug)]
pub struct DefinitionDriver<'a> {
    /// 元ソースにある左辺の信号名。
    pub name: NameSite<'a>,
    /// ファイルの平坦な定義配列の添字。
    pub definition: usize,
    /// 左辺の名前順で対応付ける、右辺の出力位置。
    pub result_index: usize,
}

/// 出力ポートまたは右辺で使う信号に値を供給する入力や定義。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OutputDriver {
    /// 同じ回路の入力配線。添字は署名の入力一覧を指す。
    Input(usize),
    /// 定義が返す出力。添字は [`FuncDrivers::definitions`] を指す。
    Definition(usize),
}

/// 組み合わせ回路の署名と、ソースで指定した駆動元。
#[derive(Debug)]
pub struct FuncDrivers<'p, 'a> {
    /// 型名を解決した入出力の署名。
    pub signature: TypedRoutineSignature<'p, 'a>,
    /// 左辺で定義した信号を、定義順かつ各左辺の名前順に並べた一覧。
    pub definitions: Vec<DefinitionDriver<'a>>,
    /// 出力の宣言順に並ぶ駆動元。
    pub outputs: Vec<OutputDriver>,
}

/// 組み合わせ回路の駆動元を検査した結果。
#[derive(Debug)]
pub enum FuncDriverResult<'p, 'a> {
    /// 指定位置に `func` がない。
    NotFunc,
    /// 本体に展開待ちのマクロ呼び出しがある。最初の呼び出しの範囲を持つ。
    NeedsExpansion(LocatedName<'p, 'a>),
    /// 入力と定義から各出力の駆動元が決まった。
    Checked(FuncDrivers<'p, 'a>),
}

/// 組み合わせ回路の署名または駆動元の違反。
#[derive(Debug)]
pub enum FuncDriverError<'p, 'a> {
    /// 署名の幅、名前または型の問題。
    Signature(TypedSignatureError<'p, 'a>),
    /// `def` が入力配線に値を割り当てようとした。
    DrivesInput {
        /// 再駆動しようとした左辺の名前。
        target: LocatedName<'p, 'a>,
        /// 入力を宣言した名前の範囲。
        input: LocatedName<'p, 'a>,
    },
    /// 同じ信号を複数の左辺で駆動しようとした。
    MultipleDrivers {
        /// 後から現れた左辺の名前。
        later: LocatedName<'p, 'a>,
        /// 最初に現れた左辺の名前。
        first: LocatedName<'p, 'a>,
    },
    /// 出力に対応する入力や定義がない。
    MissingOutput(LocatedName<'p, 'a>),
}

spec fn target_position(forms: Seq<Form>, definitions: Seq<BuildDefinition>, first: int, end: int, def: int, result: int) -> bool {
    &&& 0 <= first <= def < end <= definitions.len()
    &&& 0 <= result < definition_target_range(forms, definitions[def]).1 - definition_target_range(forms, definitions[def]).0
}

spec fn ordered(def: int, result: int, later_def: int, later_result: int) -> bool {
    def < later_def || (def == later_def && result < later_result)
}

spec fn driver_site(source: &str, forms: Seq<Form>, definitions: Seq<BuildDefinition>, first: int, end: int, driver: DefinitionDriver) -> bool {
    let def = driver.definition as int;
    let result = driver.result_index as int;
    let form = definition_target_range(forms, definitions[def]).0 + result;
    &&& target_position(forms, definitions, first, end, def, result)
    &&& 0 <= form < forms.len()
    &&& driver.name.span == form_span(forms[form])
    &&& name_in_source(source, driver.name)
}

pub(super) open spec fn indexed_driver_site(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, driver: DefinitionDriver,
) -> bool {
    let frame = parsed.entry_ranges@[entry].definitions;
    let forms = parsed.syntax.forms@;
    let (start, end) = definition_target_range(forms, parsed.definitions@[driver.definition as int]);
    &&& frame.start <= driver.definition < frame.end <= parsed.definitions@.len()
    &&& driver.result_index < end - start
    &&& 0 <= start + driver.result_index < forms.len()
    &&& driver.name.span == form_span(forms[start + driver.result_index])
    &&& name_in_source(source.text, driver.name)
}

spec fn drivers_before(
    source: &str, forms: Seq<Form>, definitions: Seq<BuildDefinition>, first: int, end: int,
    def: int, result: int, drivers: Seq<DefinitionDriver>,
) -> bool {
    &&& forall|i: int| 0 <= i < drivers.len() ==> {
        let driver = #[trigger] drivers[i];
        driver_site(source, forms, definitions, first, end, driver)
            && ordered(driver.definition as int, driver.result_index as int, def, result)
    }
    &&& forall|i: int, j: int| 0 <= i < j < drivers.len() ==> {
        let left = #[trigger] drivers[i];
        let right = #[trigger] drivers[j];
        ordered(left.definition as int, left.result_index as int, right.definition as int, right.result_index as int)
    }
    &&& forall|d: int, r: int| #[trigger] target_position(forms, definitions, first, end, d, r)
        && ordered(d, r, def, result) ==> exists|i: int| 0 <= i < drivers.len()
            && (#[trigger] drivers[i]).definition == d && drivers[i].result_index == r
}

proof fn record_driver(
    source: &str, forms: Seq<Form>, definitions: Seq<BuildDefinition>, first: int, end: int,
    drivers: Seq<DefinitionDriver>, driver: DefinitionDriver,
)
    requires
        driver_site(source, forms, definitions, first, end, driver),
        drivers_before(source, forms, definitions, first, end, driver.definition as int, driver.result_index as int, drivers),
    ensures drivers_before(source, forms, definitions, first, end,
        driver.definition as int, driver.result_index + 1, drivers.push(driver)),
{
    let updated = drivers.push(driver);
    let def = driver.definition as int;
    let result = driver.result_index as int;
    assert forall|d: int, r: int| #[trigger] target_position(forms, definitions, first, end, d, r)
        && ordered(d, r, def, result + 1) implies exists|i: int| 0 <= i < updated.len()
            && (#[trigger] updated[i]).definition == d && updated[i].result_index == r by {
        if ordered(d, r, def, result) {
            let i = choose|i: int| 0 <= i < drivers.len()
                && (#[trigger] drivers[i]).definition == d && drivers[i].result_index == r;
            assert(updated[i] == drivers[i]);
        } else {
            assert(d == def && r == result);
            assert(updated[drivers.len() as int] == driver);
        }
    };
}

fn collect_drivers<'a>(source: &'a str, parsed: &NamedBuildCircuit<'a>, entry: usize)
    -> (drivers: Vec<DefinitionDriver<'a>>)
    requires
        build_index_matches(source, parsed.build_model()),
        entry < parsed.syntax.entries@.len(),
        entry < parsed.entry_ranges@.len(),
        form_spans_valid(source, parsed.syntax.forms@, source.spec_bytes().len() as int),
    ensures ({
        let range = parsed.entry_ranges@[entry as int].definitions;
        drivers_before(source, parsed.syntax.forms@, parsed.definitions@, range.start as int,
            range.end as int, range.end as int, 0, drivers@)
    }),
{
    let range = &parsed.entry_ranges[entry].definitions;
    let forms = parsed.syntax.forms.as_slice();
    let first = range.start;
    let end = range.end;
    proof { build_entry_ranges_evidence(source, &parsed.build_model(), entry as int); }
    let mut def = first;
    let mut drivers: Vec<DefinitionDriver> = Vec::new();
    while def < end
        invariant
            build_index_matches(source, parsed.build_model()),
            entry < parsed.syntax.entries@.len(), entry < parsed.entry_ranges@.len(),
            *range == parsed.entry_ranges@[entry as int].definitions, first == range.start,
            first <= def <= end == range.end <= parsed.definitions@.len(),
            forms@ == parsed.syntax.forms@,
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            drivers_before(source, forms@, parsed.definitions@, first as int, end as int, def as int, 0, drivers@),
        decreases end - def,
    {
        proof { build_definition_scope_evidence(source, &parsed.build_model(), entry as int, def as int); }
        let targets = definition_target_atoms(forms, &parsed.definitions[def]);
        let mut at = targets.start;
        while at < targets.end
            invariant
                targets.start <= at <= targets.end <= forms@.len(),
                (targets.start as int, targets.end as int) == definition_target_range(forms@, parsed.definitions@[def as int]),
                forall|i: int| targets.start <= i < targets.end ==> (#[trigger] forms@[i]) is Atom,
                first <= def < end <= parsed.definitions@.len(),
                form_spans_valid(source, forms@, source.spec_bytes().len() as int),
                drivers_before(source, forms@, parsed.definitions@, first as int, end as int,
                    def as int, at - targets.start, drivers@),
            decreases targets.end - at,
        {
            let (word, span) = read_indexed_atom(source, forms, at);
            let driver = DefinitionDriver { definition: def, result_index: at - targets.start, name: NameSite { word, span } };
            proof { record_driver(source, forms@, parsed.definitions@, first as int, end as int, drivers@, driver); }
            drivers.push(driver);
            at += 1;
        }
        proof {
            assert forall|d: int, r: int| #[trigger] target_position(forms@, parsed.definitions@, first as int, end as int, d, r)
                && ordered(d, r, def + 1, 0) implies ordered(d, r, def as int, at - targets.start) by {};
        }
        def += 1;
    }
    drivers
}

pub(super) open spec fn names_match_ports(source: &str, forms: Seq<Form>, ports: Seq<TypedPort>, names: Seq<NameSite>) -> bool {
    &&& names.len() <= ports.len()
    &&& forall|i: int| 0 <= i < names.len() ==> {
        let name = #[trigger] names[i];
        name.span == form_span(forms[ports[i].declared.site.name as int]) && name_in_source(source, name)
    }
}

pub(super) fn typed_port_names<'a>(source: &'a str, forms: &[Form], ports: &[TypedPort]) -> (names: Vec<NameSite<'a>>)
    requires
        typed_name_sites(forms@, ports@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures names@.len() == ports@.len(), names_match_ports(source, forms@, ports@, names@),
{
    let mut names: Vec<NameSite> = Vec::new();
    let mut at = 0;
    while at < ports.len()
        invariant
            at == names@.len() <= ports@.len(),
            typed_name_sites(forms@, ports@),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            names_match_ports(source, forms@, ports@, names@),
        decreases ports@.len() - at,
    {
        let (word, span) = read_indexed_atom(source, forms, ports[at].declared.site.name);
        names.push(NameSite { word, span });
        at += 1;
    }
    names
}

pub(super) open spec fn same_word(left: NameSite, right: NameSite) -> bool {
    left.word.spec_bytes() == right.word.spec_bytes()
}

pub(super) fn find_driver(drivers: &[DefinitionDriver], stop: usize, word: &str) -> (found: Option<usize>)
    requires stop <= drivers@.len(),
    ensures
        found matches Some(i) ==> i < stop && drivers@[i as int].name.word.spec_bytes() == word.spec_bytes(),
        forall|i: int| 0 <= i < stop && (found is None || i < found->Some_0) ==>
            (#[trigger] drivers@[i]).name.word.spec_bytes() != word.spec_bytes(),
{
    let mut at = 0;
    while at < stop
        invariant
            at <= stop <= drivers@.len(),
            forall|i: int| 0 <= i < at ==> (#[trigger] drivers@[i]).name.word.spec_bytes() != word.spec_bytes(),
        decreases stop - at,
    {
        let candidate = drivers[at].name.word;
        proof { encode_utf8_decode_utf8(candidate@); encode_utf8_decode_utf8(word@); }
        if candidate == word { return Some(at); }
        at += 1;
    }
    None
}

pub(super) fn name_location<'p, 'a>(source: &'p ProjectSource<'a>, name: &NameSite) -> (location: LocatedName<'p, 'a>)
    requires name_in_source(source.text, *name),
    ensures location_in_source(location), *location.source == *source, location.span == name.span,
{
    let location = LocatedName { source, span: name.span.start..name.span.end };
    proof { located_name_evidence(location); }
    location
}

pub(super) open spec fn is_location(source: &ProjectSource, name: NameSite, location: LocatedName) -> bool {
    *location.source == *source && location.span == name.span && location_in_source(location)
}

pub(super) open spec fn disjoint_input(inputs: Seq<NameSite>, name: NameSite) -> bool {
    forall|i: int| 0 <= i < inputs.len() ==> !same_word(#[trigger] inputs[i], name)
}

spec fn single_drivers_before(inputs: Seq<NameSite>, drivers: Seq<DefinitionDriver>, stop: int) -> bool {
    &&& forall|i: int| 0 <= i < stop ==> disjoint_input(inputs, (#[trigger] drivers[i]).name)
    &&& forall|i: int, j: int| 0 <= i < j < stop
        ==> !same_word((#[trigger] drivers[i]).name, (#[trigger] drivers[j]).name)
}

spec fn drive_error(
    source: &ProjectSource, inputs: Seq<NameSite>, drivers: Seq<DefinitionDriver>, error: FuncDriverError,
) -> bool {
    exists|at: int| 0 <= at < drivers.len()
        && single_drivers_before(inputs, drivers, at)
        && {
            let current = (#[trigger] drivers[at]).name;
            match error {
                FuncDriverError::DrivesInput { target, input } =>
                    is_location(source, current, target)
                        && exists|i: int| 0 <= i < inputs.len() && same_word(#[trigger] inputs[i], current)
                            && is_location(source, inputs[i], input),
                FuncDriverError::MultipleDrivers { later, first } =>
                    is_location(source, current, later) && disjoint_input(inputs, current)
                        && exists|i: int| 0 <= i < at && same_word((#[trigger] drivers[i]).name, current)
                            && is_location(source, drivers[i].name, first),
                _ => false,
            }
        }
}

fn check_definitions<'p, 'a>(
    source: &'p ProjectSource<'a>, inputs: &[NameSite], drivers: &[DefinitionDriver],
) -> (result: Result<(), FuncDriverError<'p, 'a>>)
    requires
        forall|i: int| 0 <= i < inputs@.len() ==> name_in_source(source.text, #[trigger] inputs@[i]),
        forall|i: int| 0 <= i < drivers@.len() ==> name_in_source(source.text, (#[trigger] drivers@[i]).name),
    ensures match result {
        Ok(()) => single_drivers_before(inputs@, drivers@, drivers@.len() as int),
        Err(error) => drive_error(source, inputs@, drivers@, error),
    },
{
    let mut at = 0;
    while at < drivers.len()
        invariant
            at <= drivers@.len(),
            forall|i: int| 0 <= i < inputs@.len() ==> name_in_source(source.text, #[trigger] inputs@[i]),
            forall|i: int| 0 <= i < drivers@.len() ==> name_in_source(source.text, (#[trigger] drivers@[i]).name),
            single_drivers_before(inputs@, drivers@, at as int),
        decreases drivers@.len() - at,
    {
        let name = &drivers[at].name;
        if let Some(input) = first_matching_name(inputs, inputs.len(), name.word) {
            let error = FuncDriverError::DrivesInput {
                target: name_location(source, name),
                input: name_location(source, &inputs[input]),
            };
            assert(drive_error(source, inputs@, drivers@, error));
            return Err(error);
        }
        assert(disjoint_input(inputs@, *name));
        if let Some(first) = find_driver(drivers, at, name.word) {
            let error = FuncDriverError::MultipleDrivers {
                later: name_location(source, name),
                first: name_location(source, &drivers[first].name),
            };
            assert(drive_error(source, inputs@, drivers@, error));
            return Err(error);
        }
        at += 1;
    }
    Ok(())
}

spec fn output_drivers_before(
    shared: Seq<Option<usize>>, outputs: Seq<NameSite>, definitions: Seq<DefinitionDriver>, drivers: Seq<OutputDriver>,
) -> bool {
    &&& drivers.len() <= outputs.len() == shared.len()
    &&& forall|i: int| 0 <= i < drivers.len() ==> match #[trigger] drivers[i] {
        OutputDriver::Input(input) => shared[i] == Some(input),
        OutputDriver::Definition(at) => shared[i].is_none() && at < definitions.len()
            && same_word(outputs[i], definitions[at as int].name),
    }
}

spec fn missing_output_error(
    source: &ProjectSource, shared: Seq<Option<usize>>, outputs: Seq<NameSite>,
    definitions: Seq<DefinitionDriver>, error: FuncDriverError,
) -> bool {
    error matches FuncDriverError::MissingOutput(location)
        && exists|at: int, earlier: Seq<OutputDriver>|
            #![trigger output_drivers_before(shared, outputs, definitions, earlier), outputs[at]]
            0 <= at < outputs.len() == shared.len()
            && earlier.len() == at
            && output_drivers_before(shared, outputs, definitions, earlier)
            && is_location(source, outputs[at], location) && shared[at].is_none()
            && forall|i: int| 0 <= i < definitions.len()
                ==> !same_word(outputs[at], (#[trigger] definitions[i]).name)
}

fn check_outputs<'p, 'a>(
    source: &'p ProjectSource<'a>, shared: &[Option<usize>], outputs: &[NameSite], definitions: &[DefinitionDriver],
) -> (result: Result<Vec<OutputDriver>, FuncDriverError<'p, 'a>>)
    requires
        shared@.len() == outputs@.len(),
        forall|i: int| 0 <= i < outputs@.len() ==> name_in_source(source.text, #[trigger] outputs@[i]),
    ensures match result {
        Ok(drivers) => drivers@.len() == outputs@.len() && output_drivers_before(shared@, outputs@, definitions@, drivers@),
        Err(error) => missing_output_error(source, shared@, outputs@, definitions@, error),
    },
{
    let mut drivers: Vec<OutputDriver> = Vec::new();
    let mut at = 0;
    while at < outputs.len()
        invariant
            shared@.len() == outputs@.len(), at == drivers@.len() <= outputs@.len(),
            forall|i: int| 0 <= i < outputs@.len() ==> name_in_source(source.text, #[trigger] outputs@[i]),
            output_drivers_before(shared@, outputs@, definitions@, drivers@),
        decreases outputs@.len() - at,
    {
        let name = &outputs[at];
        let driver = if let Some(input) = shared[at] {
            OutputDriver::Input(input)
        } else if let Some(definition) = find_driver(definitions, definitions.len(), name.word) {
            OutputDriver::Definition(definition)
        } else {
            let error = FuncDriverError::MissingOutput(name_location(source, name));
            assert(missing_output_error(source, shared@, outputs@, definitions@, error));
            return Err(error);
        };
        drivers.push(driver);
        at += 1;
    }
    Ok(drivers)
}

spec fn func_at(circuits: Seq<NamedBuildCircuit>, file: usize, entry: usize) -> bool {
    &&& file < circuits.len() && entry < circuits[file as int].syntax.entries@.len()
    &&& circuits[file as int].syntax.entries@[entry as int].head is Func
}

pub(super) open spec fn expected_output_context(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, drivers: FuncDrivers,
) -> bool {
    &&& 0 <= entry < parsed.entry_ranges@.len()
    &&& drivers.outputs@.len() == drivers.signature.outputs@.len()
    &&& forall|i: int| 0 <= i < drivers.outputs@.len() && (#[trigger] drivers.outputs@[i]) is Definition
        ==> drivers.outputs@[i]->Definition_0 < drivers.definitions@.len()
    &&& forall|i: int| 0 <= i < drivers.definitions@.len() ==> {
        let def = (#[trigger] drivers.definitions@[i]).definition;
        let frame = parsed.entry_ranges@[entry].definitions;
        frame.start <= def < frame.end <= parsed.definitions@.len()
    }
    &&& forall|i: int| 0 <= i < drivers.signature.outputs@.len() ==> {
        let port = #[trigger] drivers.signature.outputs@[i];
        *port.annotation.source == *source && location_in_source(port.annotation)
    }
    &&& forall|i: int| 0 <= i < drivers.signature.inputs@.len() ==> {
        let port = #[trigger] drivers.signature.inputs@[i];
        *port.annotation.source == *source && location_in_source(port.annotation)
    }
    &&& forall|i: int, j: int| 0 <= i < j < drivers.definitions@.len()
        ==> (#[trigger] drivers.definitions@[i]).definition <= (#[trigger] drivers.definitions@[j]).definition
}

spec fn after_collecting_names(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize,
    signature: &TypedRoutineSignature, inputs: Seq<NameSite>, outputs: Seq<NameSite>,
    definitions: Seq<DefinitionDriver>, result: Result<FuncDriverResult, FuncDriverError>,
) -> bool {
    let forms = parsed.syntax.forms@;
    let frame = parsed.entry_ranges@[entry as int].definitions;
    &&& inputs.len() == signature.inputs@.len() && outputs.len() == signature.outputs@.len()
    &&& names_match_ports(source.text, forms, signature.inputs@, inputs)
    &&& names_match_ports(source.text, forms, signature.outputs@, outputs)
    &&& drivers_before(source.text, forms, parsed.definitions@, frame.start as int,
        frame.end as int, frame.end as int, 0, definitions)
    &&& match result {
        Ok(FuncDriverResult::Checked(checked)) => checked.signature == *signature
            && checked.definitions@ == definitions
            && single_drivers_before(inputs, definitions, definitions.len() as int)
            && checked.outputs@.len() == outputs.len()
            && output_drivers_before(signature.output_inputs@, outputs, definitions, checked.outputs@),
        Err(error) => drive_error(source, inputs, definitions, error)
            || (single_drivers_before(inputs, definitions, definitions.len() as int)
                && missing_output_error(source, signature.output_inputs@, outputs, definitions, error)),
        _ => false,
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 署名、明示的な出力の駆動元、または診断が実際の関数とそのソースに対応することを表す。
    pub closed spec fn func_driver_evidence(
        &self, file: usize, entry: usize, max_width: u64,
        result: Result<FuncDriverResult, FuncDriverError>,
    ) -> bool {
        let project = self.targets.project_model();
        let circuits = project.circuits_model();
        if !func_at(circuits, file, entry) {
            result is Ok && result->Ok_0 is NotFunc
        } else {
            let parsed = &circuits[file as int];
            let source = &project.sources_model()[file as int];
            match result {
                Err(FuncDriverError::Signature(error)) =>
                    self.typed_signature_evidence(file, entry, max_width, Err(error)),
                Ok(FuncDriverResult::NeedsExpansion(location)) =>
                    *location.source == *source && location_in_source(location)
                        && routine_expansion_evidence(source.text, &parsed.syntax, entry as int, Some(location.span))
                        && exists|signature: TypedRoutineSignature|
                            #[trigger] self.typed_signature_evidence(file, entry, max_width, Ok(Some(signature))),
                _ => routine_expansion_evidence(source.text, &parsed.syntax, entry as int, None)
                    && (exists|signature: TypedRoutineSignature, inputs: Seq<NameSite>, outputs: Seq<NameSite>,
                        definitions: Seq<DefinitionDriver>|
                        #[trigger] self.typed_signature_evidence(file, entry, max_width, Ok(Some(signature)))
                        && #[trigger] after_collecting_names(source, parsed, entry, &signature, inputs, outputs, definitions, result)),
            }
        }
    }

    proof fn reveal_checked_driver_result(
        &self, file: usize, entry: usize, max_width: u64, checked: FuncDrivers,
    )
        requires self.can_resolve(), self.func_driver_evidence(file, entry, max_width, Ok(FuncDriverResult::Checked(checked))),
        ensures ({
            let project = self.targets.project_model();
            let source = &project.sources_model()[file as int];
            let parsed = &project.circuits_model()[file as int];
            let frame = parsed.entry_ranges@[entry as int].definitions;
            &&& func_at(project.circuits_model(), file, entry)
            &&& self.typed_signature_evidence(file, entry, max_width, Ok(Some(checked.signature)))
            &&& entry < parsed.entry_ranges@.len()
            &&& checked.outputs@.len() == checked.signature.outputs@.len()
            &&& forall|i: int| 0 <= i < checked.outputs@.len() && (#[trigger] checked.outputs@[i]) is Definition
                ==> checked.outputs@[i]->Definition_0 < checked.definitions@.len()
            &&& forall|i: int| 0 <= i < checked.definitions@.len()
                ==> ({
                    let driver = #[trigger] checked.definitions@[i];
                    name_in_source(source.text, driver.name)
                        && frame.start <= driver.definition < frame.end <= parsed.definitions@.len()
                })
            &&& forall|i: int, j: int| 0 <= i < j < checked.definitions@.len()
                ==> (#[trigger] checked.definitions@[i]).definition <= (#[trigger] checked.definitions@[j]).definition
        }),
    {
        reveal(UseAliases::func_driver_evidence);
        self.targets.parsed_project_model();
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        assert(parsed_circuit_matches(*source, *parsed));
        parsed_index_evidence(*source, *parsed);
        let result = Ok(FuncDriverResult::Checked(checked));
        let (signature, inputs, outputs, definitions) = choose|sig: TypedRoutineSignature, ins: Seq<NameSite>,
            outs: Seq<NameSite>, defs: Seq<DefinitionDriver>|
            #[trigger] self.typed_signature_evidence(file, entry, max_width, Ok(Some(sig)))
                && #[trigger] after_collecting_names(source, parsed, entry, &sig, ins, outs, defs, result);
        assert(signature == checked.signature && definitions == checked.definitions@);
    }

    pub(super) proof fn checked_driver_sources(
        &self, file: usize, entry: usize, max_width: u64, checked: FuncDrivers,
    )
        requires self.can_resolve(), self.func_driver_evidence(file, entry, max_width, Ok(FuncDriverResult::Checked(checked))),
        ensures ({
            let project = self.targets.project_model();
            let source = &project.sources_model()[file as int];
            let circuits = project.circuits_model();
            &&& file < circuits.len() && entry < circuits[file as int].syntax.entries@.len()
            &&& circuits[file as int].syntax.entries@[entry as int].head is Func
            &&& typed_name_sites(circuits[file as int].syntax.forms@, checked.signature.inputs@)
            &&& expected_output_context(source, &circuits[file as int], entry as int, checked)
            &&& forall|i: int| 0 <= i < checked.definitions@.len()
                ==> indexed_driver_site(source, &circuits[file as int], entry as int, #[trigger] checked.definitions@[i])
        }),
    {
        self.reveal_checked_driver_result(file, entry, max_width, checked);
        self.typed_signature_sites(file, entry, max_width, checked.signature);
    }

    /// `func` の署名を解決し、本体の明示的な定義から出力の駆動元を求める。
    ///
    /// 指定位置に `func` がなければ [`FuncDriverResult::NotFunc`] を返す。
    /// 署名を検査した後、直接の本体項目に `expand` があれば [`FuncDriverResult::NeedsExpansion`] を返す。
    /// 定義の右辺は、式の型、参照順、出力数を調べる後続の検査に渡す。
    ///
    /// # Errors
    ///
    /// 署名の違反を先に返す。展開が不要なら、左辺を出現順に調べ、入力の再駆動または複数の駆動元を診断する。
    /// 左辺の検査後、入力も定義も対応しない出力があれば、宣言順で最初の出力を示す。
    pub fn check_func_drivers(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncDriverResult<'p, 'a>, FuncDriverError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_driver_evidence(file, entry, max_width, result),
    {
        let project = self.targets.project();
        let circuits = project.circuits();
        if file >= circuits.len() { return Ok(FuncDriverResult::NotFunc); }
        let parsed = &circuits[file];
        if entry >= parsed.syntax.entries.len() || !matches!(parsed.syntax.entries[entry].head, Head::Func) {
            return Ok(FuncDriverResult::NotFunc);
        }
        let signature = match self.resolve_routine_signature(file, entry, max_width) {
            Ok(Some(signature)) => signature,
            Ok(None) => {
                proof { self.typed_signature_skips_non_routines(file, entry, max_width); assert(false); }
                unreachable!()
            },
            Err(error) => return Err(FuncDriverError::Signature(error)),
        };
        let source = &project.sources()[file];
        let forms = parsed.syntax.forms.as_slice();
        proof {
            assert(parsed_circuit_matches(*source, *parsed));
            parsed_index_evidence(*source, *parsed);
            self.typed_signature_sites(file, entry, max_width, signature);
        }
        let expansion = first_routine_expansion(source.text, &parsed.syntax, entry);
        if let Some(span) = expansion {
            let location = LocatedName { source, span };
            proof { located_name_evidence(location); }
            return Ok(FuncDriverResult::NeedsExpansion(location));
        }
        let inputs = typed_port_names(source.text, forms, signature.inputs.as_slice());
        let outputs = typed_port_names(source.text, forms, signature.outputs.as_slice());
        let definitions = collect_drivers(source.text, parsed, entry);
        let ghost definitions_model = definitions@;
        let ghost signature_model = signature;
        let result = match check_definitions(source, inputs.as_slice(), definitions.as_slice()) {
            Err(error) => Err(error),
            Ok(()) => match check_outputs(source, signature.output_inputs.as_slice(), outputs.as_slice(), definitions.as_slice()) {
                Ok(outputs) => Ok(FuncDriverResult::Checked(FuncDrivers { signature, definitions, outputs })),
                Err(error) => Err(error),
            },
        };
        assert(after_collecting_names(source, parsed, entry, &signature_model, inputs@, outputs@, definitions_model, result));
        result
    }
}

} // verus!
