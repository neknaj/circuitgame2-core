//! 回路の署名で、ポート名と入出力が共有する配線を検査する。

use super::circuits::read_indexed_atom;
#[cfg(verus_only)]
use super::circuits::{name_in_source, parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use super::declarations::located_name_evidence;
#[cfg(verus_only)]
use super::location_in_source;
#[cfg(verus_only)]
use super::widths::{
    checked_name_sites, checked_width_sites, routine_port_widths_agree, routine_port_widths_evidence,
    routine_widths_success_excludes_other,
};
use super::{
    CheckedPort, CircuitProject, DeclaredPortType, LocatedName, PortWidthError, ProjectSource,
    RoutinePortWidths, check_routine_port_widths,
};
use crate::syntax::Form;
use crate::syntax::circuit::{NameSite, PortTypeSite};
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::encode_utf8_decode_utf8;

verus! {

/// ポートが属する署名の節。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PortDirection {
    /// 入力を並べる `in` 節。
    Input,
    /// 出力を並べる `out` 節。
    Output,
}

/// 同じ入力を公開する出力の型検査。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SharedPortType {
    /// 入出力は同じ幅のビット列を指定している。
    EqualBits,
    /// 少なくとも一方が名前付き型を指定しており、型名の解決が必要である。
    PendingNamedType,
}

/// 出力名に対応する配線の出所。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OutputSource {
    /// 同名の入力がない。本体の結線検査で駆動元を調べる。
    Body,
    /// 同名の入力配線を公開する。
    Input {
        /// 署名の入力ポート一覧の添字。
        port: usize,
        /// 入出力の型検査の結果。
        ty: SharedPortType,
    },
}

/// ポート名と共有配線を検査した回路の署名。
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedRoutineSignature {
    /// 入出力の宣言順の一覧。各ポートの構文位置と幅または型参照を持つ。
    pub ports: RoutinePortWidths,
    /// 出力ポートごとの配線の出所。出力ポート一覧と同じ順に並ぶ。
    pub output_sources: Vec<OutputSource>,
}

/// 回路の署名を検査して見つかった最初の違反。
#[derive(Debug)]
pub enum RoutineSignatureError<'p, 'a> {
    /// ポートの幅が使用できる範囲を外れている。
    Width(PortWidthError<'p, 'a>),
    /// 同じ方向のポートに同じ名前が二回以上現れる。
    Duplicate {
        /// 重複したポートが属する節。
        direction: PortDirection,
        /// 後から現れたポート名の範囲。
        later: LocatedName<'p, 'a>,
        /// 同名のポートが最初に現れた範囲。
        first: LocatedName<'p, 'a>,
    },
    /// 同じ配線を使う入出力のビット幅が一致しない。
    SharedWidthMismatch {
        /// 出力が要求する幅。
        expected: u64,
        /// 同名の入力配線の幅。
        actual: u64,
        /// 出力の幅指定。型を省略した場合は出力名の範囲。
        output: LocatedName<'p, 'a>,
        /// 入力の幅指定。型を省略した場合は入力名の範囲。
        input: LocatedName<'p, 'a>,
    },
}

spec fn port_word(source: &str, forms: Seq<Form>, port: CheckedPort) -> Seq<u8> {
    let span = form_span(forms[port.site.name as int]);
    source.spec_bytes()[span.start as int..span.end as int]
}

spec fn name_site(source: &str, forms: Seq<Form>, port: CheckedPort, name: NameSite) -> bool {
    name.span == form_span(forms[port.site.name as int]) && name.word.spec_bytes() == port_word(source, forms, port)
        && name_in_source(source, name)
}

spec fn names_for_ports(source: &str, forms: Seq<Form>, ports: Seq<CheckedPort>, names: Seq<NameSite>) -> bool {
    &&& names.len() <= ports.len()
    &&& forall|i: int| 0 <= i < names.len() ==> name_site(source, forms, ports[i], #[trigger] names[i])
}

fn read_port_names<'a>(source: &'a str, forms: &[Form], ports: &[CheckedPort]) -> (names: Vec<NameSite<'a>>)
    requires
        checked_name_sites(forms@, ports@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures names@.len() == ports@.len(), names_for_ports(source, forms@, ports@, names@),
{
    let mut names: Vec<NameSite> = Vec::new();
    let mut i = 0;
    while i < ports.len()
        invariant
            checked_name_sites(forms@, ports@),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            i == names@.len() <= ports@.len(),
            names_for_ports(source, forms@, ports@, names@),
        decreases ports@.len() - i,
    {
        let port = ports[i];
        let (word, span) = read_indexed_atom(source, forms, port.site.name);
        let name = NameSite { word, span };
        assert(name_site(source, forms@, port, name));
        names.push(name);
        i += 1;
    }
    names
}

pub(super) fn first_matching_name(names: &[NameSite], count: usize, name: &str) -> (result: Option<usize>)
    requires count <= names@.len(),
    ensures
        result matches Some(i) ==> i < count && names@[i as int].word.spec_bytes() == name.spec_bytes(),
        forall|i: int| 0 <= i < count && (result is None || i < result->Some_0)
            ==> (#[trigger] names@[i]).word.spec_bytes() != name.spec_bytes(),
{
    let mut i = 0;
    while i < count
        invariant
            i <= count <= names@.len(),
            forall|prior: int| 0 <= prior < i ==> (#[trigger] names@[prior]).word.spec_bytes() != name.spec_bytes(),
        decreases count - i,
    {
        let candidate = names[i].word;
        proof { encode_utf8_decode_utf8(candidate@); encode_utf8_decode_utf8(name@); }
        if candidate == name {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn site_location<'p, 'a>(source: &'p ProjectSource<'a>, name: &NameSite) -> (result: LocatedName<'p, 'a>)
    requires name_in_source(source.text, *name),
    ensures *result.source == *source, result.span == name.span, location_in_source(result),
{
    let location = LocatedName { source, span: name.span.start..name.span.end };
    proof { located_name_evidence(location); }
    location
}

spec fn unique_prefix(names: Seq<NameSite>, stop: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < stop ==>
        (#[trigger] names[i]).word.spec_bytes() != (#[trigger] names[j]).word.spec_bytes()
}

spec fn duplicate_for(
    source: &ProjectSource, names: Seq<NameSite>, direction: PortDirection, error: RoutineSignatureError,
) -> bool {
    error matches RoutineSignatureError::Duplicate { direction: reported, first, later }
        && reported == direction && *first.source == *source && *later.source == *source
        && location_in_source(first) && location_in_source(later)
        && exists|i: int, j: int| 0 <= i < j < names.len()
            && (#[trigger] names[i]).span == first.span && (#[trigger] names[j]).span == later.span
            && names[i].word.spec_bytes() == names[j].word.spec_bytes() && unique_prefix(names, j)
}

fn check_unique<'p, 'a>(
    source: &'p ProjectSource<'a>, names: &[NameSite], direction: PortDirection,
) -> (result: Result<(), RoutineSignatureError<'p, 'a>>)
    requires forall|i: int| 0 <= i < names@.len() ==> name_in_source(source.text, #[trigger] names@[i]),
    ensures match result {
        Ok(()) => unique_prefix(names@, names@.len() as int),
        Err(error) => duplicate_for(source, names@, direction, error),
    },
{
    let mut later = 0;
    while later < names.len()
        invariant
            later <= names@.len(), unique_prefix(names@, later as int),
            forall|i: int| 0 <= i < names@.len() ==> name_in_source(source.text, #[trigger] names@[i]),
        decreases names@.len() - later,
    {
        let name = &names[later];
        if let Some(first) = first_matching_name(names, later, name.word) {
            let first = site_location(source, &names[first]);
            let later = site_location(source, name);
            return Err(RoutineSignatureError::Duplicate { direction, later, first });
        }
        later += 1;
    }
    Ok(())
}

spec fn width_atom(port: CheckedPort) -> usize {
    match port.site.ty { PortTypeSite::Bits { width } => width, _ => port.site.name }
}

fn width_location<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], port: CheckedPort,
) -> (location: LocatedName<'p, 'a>)
    requires
        width_atom(port) < forms@.len(), forms@[width_atom(port) as int] is Atom,
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures *location.source == *source, location.span == form_span(forms@[width_atom(port) as int]),
        location_in_source(location),
{
    let atom = match port.site.ty { PortTypeSite::Bits { width } => width, _ => port.site.name };
    let (_, span) = read_indexed_atom(source.text, forms, atom);
    let location = LocatedName { source, span };
    proof { located_name_evidence(location); }
    location
}

spec fn same_names(left: NameSite, right: NameSite) -> bool {
    left.word.spec_bytes() == right.word.spec_bytes()
}

spec fn output_matches(
    inputs: Seq<CheckedPort>, names: Seq<NameSite>, output: CheckedPort, name: NameSite, connection: OutputSource,
) -> bool {
    match connection {
        OutputSource::Body => forall|i: int| 0 <= i < names.len() ==> !same_names(#[trigger] names[i], name),
        OutputSource::Input { port, ty } => {
            &&& port < names.len() && port < inputs.len()
            &&& same_names(names[port as int], name)
            &&& match (inputs[port as int].ty, output.ty) {
                (DeclaredPortType::Bits(actual), DeclaredPortType::Bits(expected)) =>
                    actual == expected && ty is EqualBits,
                _ => ty is PendingNamedType,
            }
        },
    }
}

spec fn connections_match(
    widths: &RoutinePortWidths, inputs: Seq<NameSite>, outputs: Seq<NameSite>, connections: Seq<OutputSource>,
) -> bool {
    &&& connections.len() <= outputs.len()
    &&& forall|i: int| 0 <= i < connections.len() ==> output_matches(
        widths.inputs@, inputs, widths.outputs@[i], outputs[i], #[trigger] connections[i])
}

spec fn shared_width_error(
    source: &ProjectSource, forms: Seq<Form>, widths: &RoutinePortWidths,
    inputs: Seq<NameSite>, outputs: Seq<NameSite>, error: RoutineSignatureError,
) -> bool {
    error matches RoutineSignatureError::SharedWidthMismatch { expected, actual, input, output }
        && expected != actual && *input.source == *source && *output.source == *source
        && location_in_source(input) && location_in_source(output)
        && exists|i: int, j: int| 0 <= i < inputs.len() && 0 <= j < outputs.len()
            && same_names(#[trigger] inputs[i], #[trigger] outputs[j])
            && widths.inputs@[i].ty == DeclaredPortType::Bits(actual)
            && widths.outputs@[j].ty == DeclaredPortType::Bits(expected)
            && input.span == form_span(forms[width_atom(widths.inputs@[i]) as int])
            && output.span == form_span(forms[width_atom(widths.outputs@[j]) as int])
            && exists|prefix: Seq<OutputSource>| prefix.len() == j
                && #[trigger] connections_match(widths, inputs, outputs, prefix)
}

fn connect_shared<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], widths: &RoutinePortWidths,
    inputs: &[NameSite], outputs: &[NameSite],
) -> (result: Result<Vec<OutputSource>, RoutineSignatureError<'p, 'a>>)
    requires
        inputs@.len() == widths.inputs@.len(), outputs@.len() == widths.outputs@.len(),
        checked_name_sites(forms@, widths.inputs@), checked_name_sites(forms@, widths.outputs@),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures match result {
        Ok(connections) => connections@.len() == outputs@.len()
            && connections_match(widths, inputs@, outputs@, connections@),
        Err(error) => shared_width_error(source, forms@, widths, inputs@, outputs@, error),
    },
{
    let mut connections: Vec<OutputSource> = Vec::new();
    let mut out = 0;
    while out < outputs.len()
        invariant
            inputs@.len() == widths.inputs@.len(), outputs@.len() == widths.outputs@.len(),
            checked_name_sites(forms@, widths.inputs@), checked_name_sites(forms@, widths.outputs@),
            form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
            out == connections@.len() <= outputs@.len(),
            connections_match(widths, inputs@, outputs@, connections@),
        decreases outputs@.len() - out,
    {
        let name = &outputs[out];
        let output = widths.outputs[out];
        let connection = if let Some(port) = first_matching_name(inputs, inputs.len(), name.word) {
            let input = widths.inputs[port];
            let ty = match (input.ty, output.ty) {
                (DeclaredPortType::Bits(actual), DeclaredPortType::Bits(expected)) => {
                    if actual != expected {
                        let result = RoutineSignatureError::SharedWidthMismatch {
                            expected, actual,
                            input: width_location(source, forms, input),
                            output: width_location(source, forms, output),
                        };
                        assert(shared_width_error(source, forms@, widths, inputs@, outputs@, result));
                        return Err(result);
                    }
                    SharedPortType::EqualBits
                },
                _ => SharedPortType::PendingNamedType,
            };
            OutputSource::Input { port, ty }
        } else {
            OutputSource::Body
        };
        assert(output_matches(widths.inputs@, inputs@, output, *name, connection));
        connections.push(connection);
        out += 1;
    }
    Ok(connections)
}

spec fn checked_signature_evidence(
    source: &ProjectSource, forms: Seq<Form>, widths: &RoutinePortWidths,
    inputs: Seq<NameSite>, outputs: Seq<NameSite>,
    result: Result<Option<CheckedRoutineSignature>, RoutineSignatureError>,
) -> bool {
    &&& inputs.len() == widths.inputs@.len() && outputs.len() == widths.outputs@.len()
    &&& names_for_ports(source.text, forms, widths.inputs@, inputs)
    &&& names_for_ports(source.text, forms, widths.outputs@, outputs)
    &&& match result {
        Ok(Some(signature)) => signature.ports == *widths
            && unique_prefix(inputs, inputs.len() as int) && unique_prefix(outputs, outputs.len() as int)
            && signature.output_sources@.len() == outputs.len()
            && connections_match(widths, inputs, outputs, signature.output_sources@),
        Err(error) => duplicate_for(source, inputs, PortDirection::Input, error)
            || (unique_prefix(inputs, inputs.len() as int) && duplicate_for(source, outputs, PortDirection::Output, error))
            || (unique_prefix(inputs, inputs.len() as int) && unique_prefix(outputs, outputs.len() as int)
                && shared_width_error(source, forms, widths, inputs, outputs, error)),
        _ => false,
    }
}

/// 署名で確認したポートと共有配線、または最初の違反の根拠を表す。
pub closed spec fn routine_signature_evidence(
    project: &CircuitProject, file: int, entry: int, max_width: u64,
    result: Result<Option<CheckedRoutineSignature>, RoutineSignatureError>,
) -> bool {
    match result {
        Ok(None) => routine_port_widths_evidence(project, file, entry, max_width, Ok(None)),
        Err(RoutineSignatureError::Width(error)) => routine_port_widths_evidence(project, file, entry, max_width, Err(error)),
        _ => {
            &&& 0 <= file < project.circuits_model().len()
            &&& exists|widths: RoutinePortWidths, inputs: Seq<NameSite>, outputs: Seq<NameSite>|
                #![trigger checked_signature_evidence(&project.sources_model()[file], project.circuits_model()[file].syntax.forms@,
                    &widths, inputs, outputs, result)]
                routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(widths)))
                && checked_signature_evidence(&project.sources_model()[file], project.circuits_model()[file].syntax.forms@,
                    &widths, inputs, outputs, result)
        },
    }
}

pub(super) proof fn checked_signature_ports(
    project: &CircuitProject, file: int, entry: int, max_width: u64, signature: CheckedRoutineSignature,
)
    requires routine_signature_evidence(project, file, entry, max_width, Ok(Some(signature))),
    ensures
        routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(signature.ports))),
        0 <= file < project.circuits_model().len(),
        0 <= entry < project.circuits_model()[file].syntax.entries@.len(),
        signature.output_sources@.len() == signature.ports.outputs@.len(),
        forall|i: int| 0 <= i < signature.output_sources@.len() ==> match #[trigger] signature.output_sources@[i] {
            OutputSource::Input { port, .. } => port < signature.ports.inputs@.len(),
            _ => true,
        },
{
    let source = &project.sources_model()[file];
    let forms = project.circuits_model()[file].syntax.forms@;
    let (widths, inputs, outputs) = choose|widths: RoutinePortWidths, inputs: Seq<NameSite>, outputs: Seq<NameSite>|
        routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(widths)))
        && #[trigger] checked_signature_evidence(source, forms, &widths, inputs, outputs, Ok(Some(signature)));
    super::widths::checked_width_entry_exists(project, file, entry, max_width, widths);
}

pub(super) proof fn checked_signature_input_names_unique(
    project: &CircuitProject, file: int, entry: int, limit: u64, signature: CheckedRoutineSignature,
    names: Seq<NameSite>,
)
    requires
        routine_signature_evidence(project, file, entry, limit, Ok(Some(signature))),
        names.len() == signature.ports.inputs@.len(),
        forall|i: int| 0 <= i < names.len() ==> {
            let name = #[trigger] names[i];
            let forms = project.circuits_model()[file].syntax.forms@;
            name.span == form_span(forms[signature.ports.inputs@[i].site.name as int])
                && name_in_source(project.sources_model()[file].text, name)
        },
    ensures forall|i: int, j: int| 0 <= i < j < names.len() ==>
        (#[trigger] names[i]).word.spec_bytes() != (#[trigger] names[j]).word.spec_bytes(),
{
    let source = &project.sources_model()[file];
    let forms = project.circuits_model()[file].syntax.forms@;
    let (widths, checked, outputs) = choose|widths: RoutinePortWidths, inputs: Seq<NameSite>, outputs: Seq<NameSite>|
        routine_port_widths_evidence(project, file, entry, limit, Ok(Some(widths)))
        && #[trigger] checked_signature_evidence(source, forms, &widths, inputs, outputs, Ok(Some(signature)));
    assert forall|i: int| 0 <= i < names.len() implies name_site(source.text, forms,
        signature.ports.inputs@[i], #[trigger] names[i]) by {};
    port_name_bytes_agree(source.text, forms, signature.ports.inputs@, checked, names);
    same_names_preserve_unique(checked, names);
}

proof fn port_name_bytes_agree(
    source: &str, forms: Seq<Form>, ports: Seq<CheckedPort>, left: Seq<NameSite>, right: Seq<NameSite>,
)
    requires
        left.len() == right.len(),
        names_for_ports(source, forms, ports, left),
        names_for_ports(source, forms, ports, right),
    ensures forall|i: int| 0 <= i < left.len() ==>
        (#[trigger] left[i]).word.spec_bytes() == (#[trigger] right[i]).word.spec_bytes(),
{
}

/// 同じ署名の二つの検査結果は、ポートの順序と幅、および共有する入力の対応まで一致する。
pub(super) proof fn checked_routine_signatures_agree(
    project: &CircuitProject, file: int, entry: int, max_width: u64,
    left: CheckedRoutineSignature, right: CheckedRoutineSignature,
)
    requires
        routine_signature_evidence(project, file, entry, max_width, Ok(Some(left))),
        routine_signature_evidence(project, file, entry, max_width, Ok(Some(right))),
    ensures
        left.ports.inputs@ == right.ports.inputs@,
        left.ports.outputs@ == right.ports.outputs@,
        left.output_sources@ == right.output_sources@,
{
    let source = &project.sources_model()[file];
    let forms = project.circuits_model()[file].syntax.forms@;
    let (left_widths, left_inputs, left_outputs) = choose|widths: RoutinePortWidths, inputs: Seq<NameSite>, outputs: Seq<NameSite>|
        routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(widths)))
        && #[trigger] checked_signature_evidence(source, forms, &widths, inputs, outputs, Ok(Some(left)));
    let (right_widths, right_inputs, right_outputs) = choose|widths: RoutinePortWidths, inputs: Seq<NameSite>, outputs: Seq<NameSite>|
        routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(widths)))
        && #[trigger] checked_signature_evidence(source, forms, &widths, inputs, outputs, Ok(Some(right)));
    routine_port_widths_agree(project, file, entry, max_width, left_widths, right_widths);
    port_name_bytes_agree(source.text, forms, left_widths.inputs@, left_inputs, right_inputs);
    port_name_bytes_agree(source.text, forms, left_widths.outputs@, left_outputs, right_outputs);
    let left_sources = left.output_sources@;
    let right_sources = right.output_sources@;
    assert forall|i: int| 0 <= i < left_sources.len() implies
        (#[trigger] left_sources[i]) == (#[trigger] right_sources[i]) by {
        assert(output_matches(left_widths.inputs@, left_inputs, left_widths.outputs@[i],
            left_outputs[i], left_sources[i]));
        assert(output_matches(right_widths.inputs@, right_inputs, right_widths.outputs@[i],
            right_outputs[i], right_sources[i]));
        match (left_sources[i], right_sources[i]) {
            (OutputSource::Input { port: a, .. }, OutputSource::Input { port: b, .. }) => {
                assert(same_names(left_inputs[b as int], left_outputs[i]));
                assert(a == b);
            },
            (OutputSource::Input { port, .. }, OutputSource::Body) => {
                assert(same_names(right_inputs[port as int], right_outputs[i]));
            },
            (OutputSource::Body, OutputSource::Input { port, .. }) => {
                assert(same_names(left_inputs[port as int], left_outputs[i]));
            },
            _ => {},
        }
    };
    assert(left_sources =~= right_sources);
}

proof fn unique_names_exclude_duplicate(
    source: &ProjectSource, names: Seq<NameSite>, direction: PortDirection, error: RoutineSignatureError,
)
    requires unique_prefix(names, names.len() as int),
    ensures !duplicate_for(source, names, direction, error),
{
    if let RoutineSignatureError::Duplicate { first, later, .. } = error {
        if duplicate_for(source, names, direction, error) {
            let (a, b) = choose|i: int, j: int| 0 <= i < j < names.len()
                && (#[trigger] names[i]).span == first.span && (#[trigger] names[j]).span == later.span
                && names[i].word.spec_bytes() == names[j].word.spec_bytes() && unique_prefix(names, j);
            assert(!same_names(names[a], names[b]));
        }
    }
}

proof fn same_names_preserve_unique(left: Seq<NameSite>, right: Seq<NameSite>)
    requires
        left.len() == right.len(),
        unique_prefix(left, left.len() as int),
        forall|i: int| 0 <= i < right.len() ==>
            (#[trigger] left[i]).word.spec_bytes() == (#[trigger] right[i]).word.spec_bytes(),
    ensures unique_prefix(right, right.len() as int),
{
    assert forall|i: int, j: int| 0 <= i < j < right.len() implies
        (#[trigger] right[i]).word.spec_bytes() != (#[trigger] right[j]).word.spec_bytes() by {
        assert(!same_names(left[i], left[j]));
        assert(same_names(left[i], right[i]) && same_names(left[j], right[j]));
    };
}

proof fn connections_exclude_width_error(
    source: &ProjectSource, forms: Seq<Form>, widths: &RoutinePortWidths, error_widths: &RoutinePortWidths,
    inputs: Seq<NameSite>, outputs: Seq<NameSite>, error_inputs: Seq<NameSite>,
    error_outputs: Seq<NameSite>, connections: Seq<OutputSource>, error: RoutineSignatureError,
)
    requires
        inputs.len() == widths.inputs@.len(),
        outputs.len() == widths.outputs@.len(),
        error_widths.inputs@ == widths.inputs@,
        error_widths.outputs@ == widths.outputs@,
        error_inputs.len() == inputs.len(),
        error_outputs.len() == outputs.len(),
        forall|i: int| 0 <= i < inputs.len() ==>
            (#[trigger] inputs[i]).word.spec_bytes() == (#[trigger] error_inputs[i]).word.spec_bytes(),
        forall|i: int| 0 <= i < outputs.len() ==>
            (#[trigger] outputs[i]).word.spec_bytes() == (#[trigger] error_outputs[i]).word.spec_bytes(),
        unique_prefix(inputs, inputs.len() as int),
        connections.len() == outputs.len(),
        connections_match(widths, inputs, outputs, connections),
    ensures !shared_width_error(source, forms, error_widths, error_inputs, error_outputs, error),
{
    if let RoutineSignatureError::SharedWidthMismatch { expected, actual, input, output } = error {
        if shared_width_error(source, forms, error_widths, error_inputs, error_outputs, error) {
            let (a, b) = choose|i: int, j: int| 0 <= i < error_inputs.len() && 0 <= j < error_outputs.len()
                && same_names(#[trigger] error_inputs[i], #[trigger] error_outputs[j])
                && widths.inputs@[i].ty == DeclaredPortType::Bits(actual)
                && widths.outputs@[j].ty == DeclaredPortType::Bits(expected)
                && input.span == form_span(forms[width_atom(widths.inputs@[i]) as int])
                && output.span == form_span(forms[width_atom(widths.outputs@[j]) as int])
                && exists|prefix: Seq<OutputSource>| prefix.len() == j
                    && #[trigger] connections_match(error_widths, error_inputs, error_outputs, prefix);
            assert(same_names(inputs[a], outputs[b]));
            assert(output_matches(widths.inputs@, inputs, widths.outputs@[b], outputs[b], connections[b]));
            match connections[b] {
                OutputSource::Input { port, .. } => {
                    assert(a == port);
                    assert(actual == expected);
                },
                OutputSource::Body => assert(!same_names(inputs[a], outputs[b])),
            }
        }
    }
}

/// 署名を受理したときは、幅、名前の重複、共有配線の診断が成立しない。
pub(super) proof fn checked_signature_success_excludes_other(
    project: &CircuitProject, file: int, entry: int, max_width: u64,
    success: CheckedRoutineSignature, other: Result<Option<CheckedRoutineSignature>, RoutineSignatureError>,
)
    requires
        routine_signature_evidence(project, file, entry, max_width, Ok(Some(success))),
        routine_signature_evidence(project, file, entry, max_width, other),
    ensures other is Ok && other->Ok_0 is Some,
{
    checked_signature_ports(project, file, entry, max_width, success);
    match other {
        Ok(None) => routine_widths_success_excludes_other(project, file, entry, max_width, success.ports, Ok(None)),
        Err(RoutineSignatureError::Width(error)) =>
            routine_widths_success_excludes_other(project, file, entry, max_width, success.ports, Err(error)),
        Err(error) => {
            let source = &project.sources_model()[file];
            let forms = project.circuits_model()[file].syntax.forms@;
            let (a_widths, a_inputs, a_outputs) = choose|widths: RoutinePortWidths, inputs: Seq<NameSite>, outputs: Seq<NameSite>|
                routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(widths)))
                && #[trigger] checked_signature_evidence(source, forms, &widths, inputs, outputs, Ok(Some(success)));
            let (b_widths, b_inputs, b_outputs) = choose|widths: RoutinePortWidths, inputs: Seq<NameSite>, outputs: Seq<NameSite>|
                routine_port_widths_evidence(project, file, entry, max_width, Ok(Some(widths)))
                && #[trigger] checked_signature_evidence(source, forms, &widths, inputs, outputs, other);
            routine_port_widths_agree(project, file, entry, max_width, a_widths, b_widths);
            port_name_bytes_agree(source.text, forms, a_widths.inputs@, a_inputs, b_inputs);
            port_name_bytes_agree(source.text, forms, a_widths.outputs@, a_outputs, b_outputs);
            same_names_preserve_unique(a_inputs, b_inputs);
            same_names_preserve_unique(a_outputs, b_outputs);
            unique_names_exclude_duplicate(source, b_inputs, PortDirection::Input, error);
            unique_names_exclude_duplicate(source, b_outputs, PortDirection::Output, error);
            connections_exclude_width_error(source, forms, &a_widths, &b_widths, a_inputs, a_outputs, b_inputs, b_outputs,
                success.output_sources@, error);
        },
        _ => {},
    }
}

pub(super) proof fn signature_check_skips_non_routines(project: &CircuitProject, file: int, entry: int, max_width: u64)
    requires routine_signature_evidence(project, file, entry, max_width, Ok(None)),
    ensures 0 <= file < project.circuits_model().len()
        && 0 <= entry < project.circuits_model()[file].syntax.entries@.len()
        ==> !(project.circuits_model()[file].syntax.entries@[entry].head is Func)
            && !(project.circuits_model()[file].syntax.entries@[entry].head is Module),
{
    super::widths::width_check_skips_non_routines(project, file, entry, max_width);
}

/// 回路のポート幅と名前を検査し、同名の入力を公開する出力を対応付ける。
///
/// `file` と `entry` は構文解析済みのファイルと回路フォームの添字。
/// 指定が範囲外、またはフォームが `func` と `module` 以外なら `Ok(None)` を返す。
/// 名前付き型は参照を保持し、配線を共有するポートの型照合は名前解決後に行う。
///
/// # Errors
///
/// ポート幅、入力名の重複、出力名の重複、共有配線の幅の順で最初の違反を返す。
/// ポート名が重複した場合は、最初に名前が再出現した位置と、その名前の初出を示す。
pub fn check_routine_signature<'p, 'a>(
    project: &'p CircuitProject<'a>, file: usize, entry: usize, max_width: u64,
) -> (result: Result<Option<CheckedRoutineSignature>, RoutineSignatureError<'p, 'a>>)
    requires project.has_parsed_sources(),
    ensures routine_signature_evidence(project, file as int, entry as int, max_width, result),
{
    let ports = match check_routine_port_widths(project, file, entry, max_width) {
        Ok(Some(ports)) => ports,
        Ok(None) => return Ok(None),
        Err(error) => return Err(RoutineSignatureError::Width(error)),
    };
    let circuits = project.circuits();
    proof { checked_width_sites(project, file as int, entry as int, max_width, ports); }
    let source = &project.sources()[file];
    let parsed = &circuits[file];
    proof {
        assert(parsed_circuit_matches(*source, *parsed));
        parsed_index_evidence(*source, *parsed);
    }
    let forms = parsed.syntax.forms.as_slice();
    let inputs = read_port_names(source.text, forms, ports.inputs.as_slice());
    let outputs = read_port_names(source.text, forms, ports.outputs.as_slice());
    let in_names = inputs.as_slice();
    let out_names = outputs.as_slice();
    let ghost model = ports;
    let result = match check_unique(source, in_names, PortDirection::Input) {
        Err(error) => Err(error),
        Ok(()) => match check_unique(source, out_names, PortDirection::Output) {
            Err(error) => Err(error),
            Ok(()) => match connect_shared(source, forms, &ports, in_names, out_names) {
                Ok(output_sources) => Ok(Some(CheckedRoutineSignature { ports, output_sources })),
                Err(error) => Err(error),
            },
        },
    };
    assert(checked_signature_evidence(source, forms@, &model, in_names@, out_names@, result));
    result
}

} // verus!
