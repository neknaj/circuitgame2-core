//! 定数と裸の信号名から、関数の左辺に対応する型を求める。

use super::function_literals::index_outputs;
#[cfg(verus_only)]
use super::function_literals::output_indices;
#[cfg(verus_only)]
use super::function_drivers::expected_output_context;
use super::{FuncLiteralError, FuncLiteralWidths, FuncWiring, FuncWiringResult, OutputDriver, ResolvedPortType, UseAliases};
use crate::project::LocatedName;
use crate::project::circuits::form_location;
#[cfg(verus_only)]
use crate::project::{
    ProjectSource, circuits::{parsed_circuit_matches, parsed_index_evidence, is_form_location},
    port_types_equal,
};
use crate::syntax::{AtomKind, Form};
#[cfg(verus_only)]
use crate::syntax::circuit::{NamedBuildCircuit, build_bare_signal_position, build_definition_scope_evidence};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 確定した信号型と、その根拠となるソース位置。
#[derive(Debug)]
pub struct SignalType<'p, 'a> {
    /// 入力宣言または右辺から得た型。
    pub ty: ResolvedPortType<'p, 'a>,
    /// 型を与えた入力の注釈または定数の範囲。信号名を介した参照でも元の範囲を保つ。
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

/// 定数または裸の信号参照を検査した結果の診断。
#[derive(Debug)]
pub enum FuncAtomTypeError<'p, 'a> {
    /// 配線、個数または定数の右辺の違反。
    Literal(FuncLiteralError<'p, 'a>),
    /// 信号の型と、その信号が駆動する出力の宣言型が異なる。
    OutputType {
        /// 右辺の裸の信号名。
        reference: LocatedName<'p, 'a>,
        /// 出力が要求する型と、その注釈位置。
        expected: SignalType<'p, 'a>,
        /// 信号の型と、その型の根拠となる位置。
        actual: SignalType<'p, 'a>,
    },
}

fn copy_location<'p, 'a>(location: &LocatedName<'p, 'a>) -> (copy: LocatedName<'p, 'a>)
    ensures copy == *location,
{
    LocatedName { source: location.source, span: location.span.start..location.span.end }
}

spec fn signal_type_at<'p, 'a>(
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

fn inherit_type<'p, 'a>(
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
        OutputDriver::Definition(i) => match &types[i] {
            Some(known) => Some(SignalType { ty: known.ty, origin: copy_location(&known.origin) }),
            None => None,
        },
    }
}

#[verifier::opaque]
spec fn atom_type_step(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, outputs: Seq<Option<usize>>, prior: Seq<Option<SignalType>>, i: int,
    result: Result<Option<SignalType>, FuncAtomTypeError>,
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
                    result == Err(FuncAtomTypeError::OutputType {
                        reference: bound.site, expected: SignalType { ty: port.ty, origin: port.annotation }, actual,
                    })
                }
            },
            _ => result == Ok(actual),
        }
    } else {
        result == Ok(None)
    }
}

#[verifier::opaque]
spec fn typed_prefix(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, outputs: Seq<Option<usize>>, types: Seq<Option<SignalType>>,
) -> bool {
    &&& types.len() <= wiring.drivers.definitions@.len()
    &&& forall|i: int| 0 <= i < types.len() ==>
        #[trigger] atom_type_step(source, parsed, entry, wiring, widths, outputs, types.take(i), i, Ok(types[i]))
}

spec fn atoms_match(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: int, wiring: &FuncWiring,
    widths: Seq<Option<u64>>, result: Result<Vec<Option<SignalType>>, FuncAtomTypeError>,
) -> bool {
    exists|outputs: Seq<Option<usize>>| #[trigger] output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, outputs)
        && match result {
            Ok(types) => types@.len() == wiring.drivers.definitions@.len()
                && typed_prefix(source, parsed, entry, wiring, widths, outputs, types@),
            Err(error) => exists|prior: Seq<Option<SignalType>>| prior.len() < wiring.drivers.definitions@.len()
                && #[trigger] typed_prefix(source, parsed, entry, wiring, widths, outputs, prior)
                && atom_type_step(source, parsed, entry, wiring, widths, outputs, prior, prior.len() as int, Err(error)),
        }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    fn check_atoms(
        &self, file: usize, entry: usize, _limit: u64, literals: &FuncLiteralWidths<'p, 'a>, wiring: &FuncWiring<'p, 'a>,
    ) -> (result: Result<Vec<Option<SignalType<'p, 'a>>>, FuncAtomTypeError<'p, 'a>>)
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
        ensures
            ({
                let project = self.targets.project_model();
                atoms_match(&project.sources_model()[file as int], &project.circuits_model()[file as int],
                    entry as int, wiring, literals.widths@, result)
            }),
            result matches Err(error) ==> !(error is Literal),
    {
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let outputs = index_outputs(&wiring.drivers);
        let mut types: Vec<Option<SignalType>> = Vec::new();
        let mut i = 0;
        proof { reveal(typed_prefix); }
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
                i == types@.len() <= wiring.drivers.definitions@.len(),
                typed_prefix(source, parsed, entry as int, wiring, literals.widths@, outputs@, types@),
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
                        let error = FuncAtomTypeError::OutputType {
                            reference: copy_location(&bound.site),
                            expected: SignalType { ty: port.ty, origin: copy_location(&port.annotation) },
                            actual: SignalType { ty: resolved.ty, origin: copy_location(&resolved.origin) },
                        };
                        assert(atom_type_step(source, parsed, entry as int, wiring, literals.widths@,
                            outputs@, types@, i as int, Err(error)));
                        return Err(error);
                    }
                }
                actual
            } else { None };
            assert(atom_type_step(source, parsed, entry as int, wiring, literals.widths@, outputs@, types@, i as int, Ok(next)));
            let ghost before = types@;
            types.push(next);
            proof {
                reveal(typed_prefix);
                assert forall|j: int| 0 <= j < types@.len() implies
                    #[trigger] atom_type_step(source, parsed, entry as int, wiring, literals.widths@,
                        outputs@, types@.take(j), j, Ok(types@[j])) by {
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
                        typed.literals.widths@, Ok(typed.types)),
                    _ => typed.types@.len() == 0,
                },
            Err(error) => exists|literals: FuncLiteralWidths| literals.wiring is Checked
                && #[trigger] self.func_literal_evidence(file, entry, limit, Ok(literals))
                && atoms_match(source, parsed, entry as int, &literals.wiring->Checked_0, literals.widths@, Err(error)),
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
        match self.check_atoms(file, entry, max_width, &literals, wiring) {
            Ok(types) => Ok(FuncAtomTypes { literals, types }),
            Err(error) => {
                assert(self.func_atom_type_evidence(file, entry, max_width, Err(error))) by {
                    assert(self.func_literal_evidence(file, entry, max_width, Ok(literals)));
                };
                Err(error)
            },
        }
    }
}

} // verus!
