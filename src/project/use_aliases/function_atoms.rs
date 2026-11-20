//! 定数と裸の信号名から、関数の左辺に対応する型を求める。

use super::function_literals::index_outputs;
use super::function_types::FuncSignalTypeError;
use super::selection_arguments::check_selection_arguments;
#[cfg(verus_only)]
use super::selection_arguments::selection_arguments_match;
#[cfg(verus_only)]
use super::function_literals::output_indices;
#[cfg(verus_only)]
use super::function_drivers::expected_output_context;
use super::{FuncLiteralError, FuncLiteralWidths, FuncWiring, FuncWiringResult, OutputDriver, ResolvedPortType, UseAliases};
use crate::project::{LocatedName, ProjectSource, TypedPort};
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::{
    circuits::{parsed_circuit_matches, parsed_index_evidence, is_form_location},
    location_in_source, port_types_equal,
};
use crate::syntax::{AtomKind, Form};
use crate::syntax::circuit::{BitSelectionShape, bit_selection_shape};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    NamedBuildCircuit, bit_selection_shape_matches, bit_selection_shape_positions, build_bare_signal_position,
    build_definition_scope_evidence, build_selection_input_position,
};
#[cfg(verus_only)]
use crate::syntax::form_spans_valid;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 確定した信号型と、その根拠となるソース位置。
#[derive(Debug)]
pub struct SignalType<'p, 'a> {
    /// 入力宣言または右辺から得た型。
    pub ty: ResolvedPortType<'p, 'a>,
    /// 型を与えたポートの注釈、定数、または組み込み呼び出しの範囲。信号名を介しても元の範囲を保つ。
    pub origin: LocatedName<'p, 'a>,
}

/// 配線、定数の幅、および定数や裸の信号参照から確定した型。
#[derive(Debug)]
pub struct FuncAtomTypes<'p, 'a> {
    /// 配線と定数の右辺の検査結果。
    pub literals: FuncLiteralWidths<'p, 'a>,
    /// 駆動元の左辺一覧と同じ順に並ぶ型。式の型が未確定なら `None`。
    /// 対象外や展開待ちでは空になる。
    pub types: Vec<Option<SignalType<'p, 'a>>>,
}

/// 定数の幅、または右辺と出力の型の不一致に関する診断。
#[derive(Debug)]
pub enum FuncAtomTypeError<'p, 'a> {
    /// 配線、個数または定数の右辺の違反。
    Literal(FuncLiteralError<'p, 'a>),
    /// 右辺の型と、駆動先の出力の宣言型が異なる。
    OutputType {
        /// 右辺の信号名またはビット選択式の範囲。
        reference: LocatedName<'p, 'a>,
        /// 出力が要求する型と、その注釈位置。
        expected: SignalType<'p, 'a>,
        /// 信号の型と、その型の根拠となる位置。
        actual: SignalType<'p, 'a>,
    },
}

pub(super) fn copy_location<'p, 'a>(location: &LocatedName<'p, 'a>) -> (copy: LocatedName<'p, 'a>)
    ensures copy == *location,
{
    LocatedName { source: location.source, span: location.span.start..location.span.end }
}

fn copy_signal_type<'p, 'a>(signal: &Option<SignalType<'p, 'a>>) -> (copy: Option<SignalType<'p, 'a>>)
    ensures copy == *signal,
{
    match signal {
        Some(known) => Some(SignalType { ty: known.ty, origin: copy_location(&known.origin) }),
        None => None,
    }
}

pub(super) open spec fn signal_type_at<'p, 'a>(
    wiring: &FuncWiring<'p, 'a>, types: Seq<Option<SignalType<'p, 'a>>>, origin: OutputDriver,
) -> Option<SignalType<'p, 'a>>
{
    match origin {
        OutputDriver::Input(input) => {
            let port = wiring.drivers.signature.inputs@[input as int];
            Some(SignalType { ty: port.ty, origin: port.annotation })
        },
        OutputDriver::Definition(definition) => types[definition as int],
    }
}

pub(super) fn inherit_type<'p, 'a>(
    wiring: &FuncWiring<'p, 'a>, types: &[Option<SignalType<'p, 'a>>], origin: OutputDriver,
) -> (ty: Option<SignalType<'p, 'a>>)
    requires match origin {
        OutputDriver::Input(i) => i < wiring.drivers.signature.inputs@.len(),
        OutputDriver::Definition(i) => i < types@.len(),
    },
    ensures ty == signal_type_at(wiring, types@, origin),
{
    match origin {
        OutputDriver::Input(i) => {
            let port = &wiring.drivers.signature.inputs[i];
            Some(SignalType { ty: port.ty, origin: copy_location(&port.annotation) })
        },
        OutputDriver::Definition(i) => copy_signal_type(&types[i]),
    }
}

pub(super) open spec fn named_selection_matches(source: &str, forms: Seq<Form>, index: int, shape: BitSelectionShape) -> bool {
    &&& bit_selection_shape_matches(source, forms, index, shape)
    &&& shape.input.end == shape.input.start + 1
    &&& forms[shape.input.start as int] is Atom
    &&& forms[shape.input.start as int]->Atom_kind is Name
}

pub(super) fn named_selection(source: &str, forms: &[Form], index: usize) -> (result: Option<BitSelectionShape>)
    ensures
        result matches Some(shape) ==> named_selection_matches(source, forms@, index as int, shape),
        forall|shape: BitSelectionShape| #[trigger] named_selection_matches(source, forms@, index as int, shape)
            <==> result == Some(shape),
{
    let Some(shape) = bit_selection_shape(source, forms, index) else { return None; };
    proof { bit_selection_shape_positions(source, forms@, index as int, shape); }
    if shape.input.end - shape.input.start == 1
        && matches!(forms[shape.input.start], Form::Atom { kind: AtomKind::Name, .. })
    {
        Some(shape)
    } else { None }
}

spec fn selection_type_matches(
    source: &ProjectSource, forms: Seq<Form>, root: usize, shape: BitSelectionShape,
    input: Option<SignalType>, expected: Option<TypedPort>, result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    match input {
        None => result == Ok(None),
        Some(input) => match input.ty {
            ResolvedPortType::Bits(width) => match result {
                Err(FuncSignalTypeError::SelectionArgument(error)) =>
                    selection_arguments_match(source, forms, &shape, width, &input.origin, Err(error)),
                _ => exists|selection: super::selection_arguments::CheckedBitSelection, expression: LocatedName|
                    #[trigger] selection_arguments_match(source, forms, &shape, width, &input.origin, Ok(selection))
                    && #[trigger] is_form_location(source, forms[root as int], expression)
                    && {
                        let actual = SignalType { ty: ResolvedPortType::Bits(selection.count), origin: expression };
                        if let Some(port) = expected {
                            if port_types_equal(actual.ty, port.ty) {
                                result == Ok(Some(actual))
                            } else {
                                result == Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                                    reference: expression,
                                    expected: SignalType { ty: port.ty, origin: port.annotation },
                                    actual,
                                }))
                            }
                        } else {
                            result == Ok(Some(actual))
                        }
                    },
            },
            _ => result matches Err(FuncSignalTypeError::SelectionInputType { reference, actual })
                && actual == input && is_form_location(source, forms[shape.input.start as int], reference),
        },
    }
}

fn check_selection_type<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], root: usize, shape: &BitSelectionShape,
    input: Option<SignalType<'p, 'a>>, expected: Option<&TypedPort<'p, 'a>>,
) -> (result: Result<Option<SignalType<'p, 'a>>, FuncSignalTypeError<'p, 'a>>)
    requires
        named_selection_matches(source.text, forms@, root as int, *shape),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
        input matches Some(ty) ==> location_in_source(ty.origin),
    ensures
        selection_type_matches(source, forms@, root, *shape, input,
            match expected { Some(port) => Some(*port), None => None }, result),
        result matches Ok(Some(ty)) ==> location_in_source(ty.origin),
        result matches Err(error) ==> (error is Signal || error is SelectionInputType || error is SelectionArgument),
        result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
{
    let Some(input) = input else { return Ok(None); };
    proof { bit_selection_shape_positions(source.text, forms@, root as int, *shape); }
    let ResolvedPortType::Bits(width) = input.ty else {
        let reference = form_location(source, forms, shape.input.start);
        return Err(FuncSignalTypeError::SelectionInputType { reference, actual: input });
    };
    let checked = match check_selection_arguments(source, forms, root, shape, width, &input.origin) {
        Ok(checked) => checked,
        Err(error) => return Err(FuncSignalTypeError::SelectionArgument(error)),
    };
    let expression = form_location(source, forms, root);
    let actual = SignalType { ty: ResolvedPortType::Bits(checked.count), origin: copy_location(&expression) };
    if let Some(port) = expected {
        if !actual.ty.is_same_type(&port.ty) {
            return Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                reference: expression,
                expected: SignalType { ty: port.ty, origin: copy_location(&port.annotation) },
                actual,
            }));
        }
    }
    Ok(Some(actual))
}

#[verifier::opaque]
spec fn atom_type_step(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, outputs: Seq<Option<usize>>, roots: Seq<Option<SignalType>>,
    prior: Seq<Option<SignalType>>, i: int,
    result: Result<Option<SignalType>, FuncSignalTypeError>,
) -> bool {
    let driver = wiring.drivers.definitions@[i];
    let row = parsed.definitions@[driver.definition as int];
    let root = parsed.syntax.forms@[row.expression.start as int];
    &&& 0 <= entry < parsed.entry_ranges@.len()
    &&& 0 <= i < wiring.drivers.definitions@.len()
    &&& i < widths.len() && i < outputs.len()
    &&& driver.definition < parsed.definitions@.len()
    &&& row.expression.start < parsed.syntax.forms@.len()
    &&& if let Some(width) = widths[i] {
        result matches Ok(Some(ty)) && ty.ty == ResolvedPortType::Bits(width)
            && is_form_location(source, root, ty.origin)
    } else if driver.result_index == 0 && root is Atom && root->Atom_kind is Name {
        let first = parsed.entry_ranges@[entry].signals.start;
        let bound = wiring.signals@[row.signals.start - first];
        let actual = signal_type_at(wiring, prior, bound.driver);
        &&& first <= row.signals.start < first + wiring.signals@.len()
        &&& bound.definition == driver.definition && is_form_location(source, root, bound.site)
        &&& match bound.driver {
            OutputDriver::Input(input) => input < wiring.drivers.signature.inputs@.len(),
            OutputDriver::Definition(i) => i < prior.len(),
        }
        &&& match (actual, outputs[i]) {
            (Some(actual), Some(output)) => {
                let port = wiring.drivers.signature.outputs@[output as int];
                &&& output < wiring.drivers.signature.outputs@.len()
                &&& if port_types_equal(actual.ty, port.ty) {
                    result == Ok(Some(actual))
                } else {
                    result == Err(FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                        reference: bound.site, expected: SignalType { ty: port.ty, origin: port.annotation }, actual,
                    }))
                }
            },
            _ => result == Ok(actual),
        }
    } else if roots.len() > 0 && driver.result_index == 0 && exists|shape: BitSelectionShape|
        #[trigger] named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape)
    {
        let shape = choose|shape: BitSelectionShape|
            #[trigger] named_selection_matches(source.text, parsed.syntax.forms@, row.expression.start as int, shape);
        let first = parsed.entry_ranges@[entry].signals.start;
        let bound = wiring.signals@[row.signals.start - first];
        let expected = if let Some(output) = outputs[i] {
            Some(wiring.drivers.signature.outputs@[output as int])
        } else { None };
        &&& first <= row.signals.start < first + wiring.signals@.len()
        &&& bound.definition == driver.definition
        &&& is_form_location(source, parsed.syntax.forms@[shape.input.start as int], bound.site)
        &&& match bound.driver {
            OutputDriver::Input(input) => input < wiring.drivers.signature.inputs@.len(),
            OutputDriver::Definition(prior_index) => prior_index < prior.len(),
        }
        &&& outputs[i] matches Some(output) ==> output < wiring.drivers.signature.outputs@.len()
        &&& selection_type_matches(source, parsed.syntax.forms@, row.expression.start, shape,
            signal_type_at(wiring, prior, bound.driver), expected, result)
    } else {
        result == Ok(if roots.len() == 0 { None } else { roots[i] })
    }
}

#[verifier::opaque]
spec fn typed_prefix(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, outputs: Seq<Option<usize>>, roots: Seq<Option<SignalType>>, types: Seq<Option<SignalType>>,
) -> bool {
    &&& types.len() <= wiring.drivers.definitions@.len()
    &&& forall|i: int| 0 <= i < types.len() ==>
        #[trigger] atom_type_step(source, parsed, entry, wiring, widths, outputs, roots, types.take(i), i, Ok(types[i]))
}

pub(super) closed spec fn atoms_match(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, roots: Seq<Option<SignalType>>, result: Result<Vec<Option<SignalType>>, FuncSignalTypeError>,
) -> bool {
    exists|outputs: Seq<Option<usize>>| #[trigger] output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, outputs)
        && match result {
            Ok(types) => types@.len() == wiring.drivers.definitions@.len()
                && typed_prefix(source, parsed, entry, wiring, widths, outputs, roots, types@),
            Err(error) => exists|prior: Seq<Option<SignalType>>| prior.len() < wiring.drivers.definitions@.len()
                && #[trigger] typed_prefix(source, parsed, entry, wiring, widths, outputs, roots, prior)
                && atom_type_step(source, parsed, entry, wiring, widths, outputs, roots, prior, prior.len() as int, Err(error)),
        }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(super) proof fn atom_types_keep_wiring(
        &self, file: usize, entry: usize, limit: u64, typed: FuncAtomTypes, wiring: FuncWiring,
    )
        requires
            self.func_atom_type_evidence(file, entry, limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(wiring),
        ensures
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
            typed.types@.len() == wiring.drivers.definitions@.len(),
    {
        self.literals_preserve_arity(file, entry, limit, typed.literals);
        self.arity_preserves_wiring(file, entry, limit, typed.literals.wiring);
    }
    pub(super) fn check_atoms(
        &self, file: usize, entry: usize, _limit: u64, literals: &FuncLiteralWidths<'p, 'a>, wiring: &FuncWiring<'p, 'a>,
        roots: &[Option<SignalType<'p, 'a>>],
    ) -> (result: Result<Vec<Option<SignalType<'p, 'a>>>, FuncSignalTypeError<'p, 'a>>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, _limit, Ok(FuncWiringResult::Checked(*wiring))),
            ({
                let project = self.targets.project_model();
                &&& file < project.circuits_model().len() && file < project.sources_model().len()
                &&& entry < project.circuits_model()[file as int].syntax.entries@.len()
                &&& expected_output_context(&project.sources_model()[file as int],
                    &project.circuits_model()[file as int], entry as int, wiring.drivers)
            }),
            literals.widths@.len() == wiring.drivers.definitions@.len(),
            roots@.len() == 0 || roots@.len() == wiring.drivers.definitions@.len(),
            forall|i: int| 0 <= i < roots@.len() && (#[trigger] roots@[i]).is_some()
                ==> location_in_source(roots@[i]->Some_0.origin),
        ensures
            ({
                let project = self.targets.project_model();
                atoms_match(&project.sources_model()[file as int], &project.circuits_model()[file as int],
                    entry as int, wiring, literals.widths@, roots@, result)
            }),
            result matches Ok(types) ==> types@.len() == wiring.drivers.definitions@.len(),
            result matches Err(error) ==> error is Signal
                || (roots@.len() > 0 && (error is SelectionInputType || error is SelectionArgument)),
            result matches Err(FuncSignalTypeError::Signal(error)) ==> error is OutputType,
    {
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let outputs = index_outputs(&wiring.drivers);
        let mut types: Vec<Option<SignalType>> = Vec::new();
        let mut i = 0;
        proof {
            reveal(typed_prefix);
            self.checked_wiring_is_func(file, entry, _limit, *wiring);
        }
        while i < wiring.drivers.definitions.len()
            invariant
                self.can_resolve(), self.func_wiring_evidence(file, entry, _limit, Ok(FuncWiringResult::Checked(*wiring))),
                *project == self.targets.project_model(),
                file < project.sources_model().len(), file < project.circuits_model().len(),
                *source == project.sources_model()[file as int], *parsed == project.circuits_model()[file as int],
                parsed_circuit_matches(*source, *parsed), entry < parsed.syntax.entries@.len(),
                expected_output_context(source, parsed, entry as int, wiring.drivers),
                output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, outputs@),
                literals.widths@.len() == wiring.drivers.definitions@.len(),
                roots@.len() == 0 || roots@.len() == wiring.drivers.definitions@.len(),
                forall|j: int| 0 <= j < roots@.len() && (#[trigger] roots@[j]).is_some()
                    ==> location_in_source(roots@[j]->Some_0.origin),
                super::function_drivers::checked_ports_and_output_bounds(parsed.syntax.forms@, wiring.drivers),
                forall|j: int| 0 <= j < types@.len() && (#[trigger] types@[j]).is_some()
                    ==> location_in_source(types@[j]->Some_0.origin),
                i == types@.len() <= wiring.drivers.definitions@.len(),
                typed_prefix(source, parsed, entry as int, wiring, literals.widths@, outputs@, roots@, types@),
            decreases wiring.drivers.definitions@.len() - i,
        {
            let driver = &wiring.drivers.definitions[i];
            let row = &parsed.definitions[driver.definition];
            let root = row.expression.start;
            let forms = parsed.syntax.forms.as_slice();
            proof {
                reveal(atom_type_step);
                reveal(output_indices);
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, driver.definition as int);
            }
            let next = if let Some(width) = literals.widths[i] {
                Some(SignalType { ty: ResolvedPortType::Bits(width), origin: form_location(source, forms, root) })
            } else if driver.result_index == 0 && matches!(forms[root], Form::Atom { kind: AtomKind::Name, .. }) {
                proof {
                    build_bare_signal_position(source.text, &parsed.build_model(), entry as int, driver.definition as int);
                    self.checked_signal_driver(file, entry, _limit, *wiring, driver.definition, row.signals.start);
                }
                let position = row.signals.start - parsed.entry_ranges[entry].signals.start;
                let bound = &wiring.signals[position];
                proof {
                    if let OutputDriver::Definition(prior) = bound.driver {
                        assert(prior < i) by {
                            if i < prior {
                                assert(wiring.drivers.definitions@[i as int].definition
                                    <= wiring.drivers.definitions@[prior as int].definition);
                            }
                        };
                    }
                }
                let actual = inherit_type(wiring, types.as_slice(), bound.driver);
                if let (Some(resolved), Some(output)) = (&actual, outputs[i]) {
                    let port = &wiring.drivers.signature.outputs[output];
                    if !resolved.ty.is_same_type(&port.ty) {
                        let error = FuncSignalTypeError::Signal(FuncAtomTypeError::OutputType {
                            reference: copy_location(&bound.site),
                            expected: SignalType { ty: port.ty, origin: copy_location(&port.annotation) },
                            actual: SignalType { ty: resolved.ty, origin: copy_location(&resolved.origin) },
                        });
                        assert(atom_type_step(source, parsed, entry as int, wiring, literals.widths@,
                            outputs@, roots@, types@, i as int, Err(error)));
                        return Err(error);
                    }
                }
                actual
            } else if roots.is_empty() {
                None
            } else if driver.result_index == 0 {
                if let Some(shape) = named_selection(source.text, forms, root) {
                    proof {
                        assert(named_selection_matches(source.text, forms@, root as int, shape));
                        build_selection_input_position(source.text, &parsed.build_model(), entry as int,
                            driver.definition as int, shape);
                        self.checked_signal_driver(file, entry, _limit, *wiring, driver.definition, row.signals.start);
                    }
                    let position = row.signals.start - parsed.entry_ranges[entry].signals.start;
                    let bound = &wiring.signals[position];
                    proof {
                        if let OutputDriver::Definition(prior) = bound.driver {
                            assert(prior < i) by {
                                if i < prior {
                                    assert(wiring.drivers.definitions@[i as int].definition
                                        <= wiring.drivers.definitions@[prior as int].definition);
                                }
                            };
                        }
                    }
                    let input = inherit_type(wiring, types.as_slice(), bound.driver);
                    let expected = match outputs[i] {
                        Some(output) => Some(&wiring.drivers.signature.outputs[output]),
                        None => None,
                    };
                    match check_selection_type(source, forms, root, &shape, input, expected) {
                        Ok(ty) => ty,
                        Err(error) => {
                            assert(atom_type_step(source, parsed, entry as int, wiring, literals.widths@,
                                outputs@, roots@, types@, i as int, Err(error)));
                            return Err(error);
                        },
                    }
                } else {
                    copy_signal_type(&roots[i])
                }
            } else {
                copy_signal_type(&roots[i])
            };
            assert(atom_type_step(source, parsed, entry as int, wiring, literals.widths@, outputs@, roots@, types@, i as int, Ok(next)));
            assert(next matches Some(ty) ==> location_in_source(ty.origin));
            let ghost before = types@;
            types.push(next);
            proof {
                reveal(typed_prefix);
                assert forall|j: int| 0 <= j < types@.len() && (#[trigger] types@[j]).is_some()
                    implies location_in_source(types@[j]->Some_0.origin) by {
                    if j < i { assert(types@[j] == before[j]); }
                };
                assert forall|j: int| 0 <= j < types@.len() implies
                    #[trigger] atom_type_step(source, parsed, entry as int, wiring, literals.widths@,
                        outputs@, roots@, types@.take(j), j, Ok(types@[j])) by {
                    if j < i {
                        assert(types@.take(j) =~= before.take(j));
                        assert(types@[j] == before[j]);
                    } else {
                        assert(j == i && types@[j] == next);
                        assert(types@.take(j) =~= before);
                    }
                };
            }
            i += 1;
        }
        Ok(types)
    }

    /// 検査結果が定数の型と信号の束縛に対応することを表す。
    pub closed spec fn func_atom_type_evidence(
        &self, file: usize, entry: usize, limit: u64, result: Result<FuncAtomTypes, FuncAtomTypeError>,
    ) -> bool {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        match result {
            Err(FuncAtomTypeError::Literal(error)) => self.func_literal_evidence(file, entry, limit, Err(error)),
            Ok(typed) => self.func_literal_evidence(file, entry, limit, Ok(typed.literals))
                && match typed.literals.wiring {
                    FuncWiringResult::Checked(wiring) => atoms_match(source, parsed, entry as int, &wiring,
                        typed.literals.widths@, Seq::empty(), Ok(typed.types)),
                    _ => typed.types@.len() == 0,
                },
            Err(error) => exists|literals: FuncLiteralWidths| literals.wiring is Checked
                && #[trigger] self.func_literal_evidence(file, entry, limit, Ok(literals))
                && atoms_match(source, parsed, entry as int, &literals.wiring->Checked_0, literals.widths@,
                    Seq::empty(), Err(FuncSignalTypeError::Signal(error))),
        }
    }

    /// `func` の定数と裸の信号参照の型を、定義順に求める。
    ///
    /// 信号の型は入力や先行定義から引き継ぐ。呼び出しや専用フォームから来る型は未確定のまま返す。
    ///
    /// # Errors
    ///
    /// 定数までの検査で見つかった診断を先に返す。その後、既知の型を持つ裸の信号参照を出力の
    /// 宣言型と照合し、定義順で最初の違反に参照・要求型・実測型の位置を添える。
    pub fn check_func_atom_types(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncAtomTypes<'p, 'a>, FuncAtomTypeError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_atom_type_evidence(file, entry, max_width, result),
    {
        let literals = match self.check_func_literal_widths(file, entry, max_width) {
            Ok(literals) => literals,
            Err(error) => return Err(FuncAtomTypeError::Literal(error)),
        };
        let FuncWiringResult::Checked(ref wiring) = literals.wiring else {
            return Ok(FuncAtomTypes { literals, types: Vec::new() });
        };
        proof {
            self.literals_preserve_arity(file, entry, max_width, literals);
            self.arity_preserves_wiring(file, entry, max_width, literals.wiring);
            self.checked_wiring_is_func(file, entry, max_width, *wiring);
        }
        let roots: &[Option<SignalType>] = &[];
        assert(roots@ =~= Seq::empty());
        match self.check_atoms(file, entry, max_width, &literals, wiring, roots) {
            Ok(types) => Ok(FuncAtomTypes { literals, types }),
            Err(FuncSignalTypeError::Signal(error)) => {
                assert(self.func_atom_type_evidence(file, entry, max_width, Err(error))) by {
                    assert(self.func_literal_evidence(file, entry, max_width, Ok(literals)));
                };
                Err(error)
            },
            Err(_) => {
                proof { assert(false); }
                unreachable!()
            },
        }
    }
}

} // verus!
