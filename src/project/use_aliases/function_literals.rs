//! 関数の定数の右辺に、対応する出力宣言の型と幅を適用する。

use super::{FuncArityError, FuncDrivers, FuncWiringResult, OutputDriver, ResolvedPortType, TypedPort, UseAliases};
#[cfg(verus_only)]
use super::function_drivers::{expected_output_context, same_definition_driver};
#[cfg(verus_only)]
use crate::project::literal_width::successful_literal_widths_agree;
use crate::project::circuits::read_indexed_atom;
#[cfg(verus_only)]
use crate::project::circuits::{parsed_circuit_matches, parsed_index_evidence};
use crate::project::{CircuitLiteralWidthError, LocatedName, ProjectSource, check_circuit_literal_width};
#[cfg(verus_only)]
use crate::project::{circuit_literal_width_matches, location_in_source};
#[cfg(verus_only)]
use crate::project::declarations::located_name_evidence;
use crate::syntax::{AtomKind, Form, circuit::NamedBuildCircuit};
#[cfg(verus_only)]
use crate::syntax::{circuit::build_definition_scope_evidence, form_span, form_spans_valid};
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 関数の配線と、定数の右辺に割り当てたビット幅。
#[derive(Debug)]
pub struct FuncLiteralWidths<'p, 'a> {
    /// 配線と個数検査の結果。指定位置が対象外の場合や展開待ちも含む。
    pub wiring: FuncWiringResult<'p, 'a>,
    /// `wiring` が検査済みの場合、駆動元の左辺一覧と同じ順に並ぶ幅。
    /// 定数の右辺から値を受け取る左辺にだけ幅があり、対象外・展開待ちでは空になる。
    pub widths: Vec<Option<u64>>,
}

/// 定数の右辺の検査で先に見つかった違反。
#[derive(Debug)]
pub enum FuncLiteralError<'p, 'a> {
    /// 配線、名前解決、または引数数・出力数の違反。
    Arity(FuncArityError<'p, 'a>),
    /// 定数に割り当てる幅に違反がある。
    Width {
        /// 右辺のリテラルの範囲。
        literal: LocatedName<'p, 'a>,
        /// 出力宣言が要求した幅の位置。局所定義では `None`。
        required_at: Option<LocatedName<'p, 'a>>,
        /// 期待幅への不適合または幅の上限超過などの理由。
        reason: CircuitLiteralWidthError,
    },
    /// 出力に構造体型が宣言されている。
    StructRequired {
        /// 右辺のリテラルの範囲。
        literal: LocatedName<'p, 'a>,
        /// 出力に書かれた構造体型名の位置。
        type_at: LocatedName<'p, 'a>,
        /// 出力宣言が要求する構造体型。
        ty: ResolvedPortType<'p, 'a>,
    },
}

#[verifier::opaque]
pub(super) open spec fn output_indices(drivers: &FuncDrivers, prefix: int, map: Seq<Option<usize>>) -> bool {
    &&& 0 <= prefix <= drivers.outputs@.len()
    &&& map.len() == drivers.definitions@.len()
    &&& forall|driver: int| 0 <= driver < map.len() ==> {
        let at = #[trigger] map[driver];
        &&& at matches Some(i) ==> i < prefix
            && drives_result(drivers.outputs@[i as int], driver)
        &&& forall|prior: int| 0 <= prior < prefix && (at is None || prior < at->Some_0)
            ==> !drives_result(#[trigger] drivers.outputs@[prior], driver)
    }
}

/// 出力の駆動元が同じなら、各定義に対応する最初の出力位置が一致する。
pub(super) proof fn output_indices_agree(
    left: &FuncDrivers, right: &FuncDrivers, a: Seq<Option<usize>>, b: Seq<Option<usize>>,
)
    requires
        left.outputs@ == right.outputs@,
        left.definitions@.len() == right.definitions@.len(),
        output_indices(left, left.outputs@.len() as int, a),
        output_indices(right, right.outputs@.len() as int, b),
    ensures a == b,
{
    reveal(output_indices);
    assert forall|i: int| 0 <= i < a.len() implies (#[trigger] a[i]) == (#[trigger] b[i]) by {
        match (a[i], b[i]) {
            (Some(x), Some(y)) => {
                if x < y { assert(!drives_result(right.outputs@[x as int], i)); }
                if y < x { assert(!drives_result(left.outputs@[y as int], i)); }
            },
            (Some(x), None) => assert(!drives_result(right.outputs@[x as int], i)),
            (None, Some(y)) => assert(!drives_result(left.outputs@[y as int], i)),
            _ => {},
        }
    };
    assert(a =~= b);
}

pub(super) open spec fn drives_result(output: OutputDriver, driver: int) -> bool {
    output matches OutputDriver::Definition(index) && index == driver
}

pub(super) fn index_outputs(drivers: &FuncDrivers) -> (map: Vec<Option<usize>>)
    requires
        forall|i: int| 0 <= i < drivers.outputs@.len() && (#[trigger] drivers.outputs@[i]) is Definition
            ==> drivers.outputs@[i]->Definition_0 < drivers.definitions@.len(),
    ensures output_indices(drivers, drivers.outputs@.len() as int, map@),
{
    let mut map: Vec<Option<usize>> = Vec::new();
    while map.len() < drivers.definitions.len()
        invariant
            map@.len() <= drivers.definitions@.len(),
            forall|i: int| 0 <= i < map@.len() ==> (#[trigger] map@[i]).is_none(),
        decreases drivers.definitions@.len() - map@.len(),
    {
        map.push(None);
    }
    let mut output = 0;
    proof { reveal(output_indices); }
    while output < drivers.outputs.len()
        invariant
            output <= drivers.outputs@.len(),
            output_indices(drivers, output as int, map@),
            forall|i: int| 0 <= i < drivers.outputs@.len() && (#[trigger] drivers.outputs@[i]) is Definition
                ==> drivers.outputs@[i]->Definition_0 < drivers.definitions@.len(),
        decreases drivers.outputs@.len() - output,
    {
        proof { reveal(output_indices); }
        let ghost before = map@;
        let source = drivers.outputs[output];
        if let OutputDriver::Definition(driver) = source {
            if map[driver].is_none() {
                map[driver] = Some(output);
                assert(map@ == before.update(driver as int, Some(output)));
            }
        }
        assert forall|driver: int| 0 <= driver < map@.len()
            implies {
                let at = #[trigger] map@[driver];
                &&& at matches Some(i) ==> i <= output && drives_result(drivers.outputs@[i as int], driver)
                &&& forall|prior: int| 0 <= prior <= output && (at is None || prior < at->Some_0)
                    ==> !drives_result(#[trigger] drivers.outputs@[prior], driver)
            } by {
            assert(before[driver].is_none() && drives_result(source, driver)
                ==> map@[driver] == Some(output));
        };
        output += 1;
    }
    map
}

spec fn is_literal(form: Form) -> bool {
    form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal || form->Atom_kind is Natural)
}

spec fn rhs_location(source: &ProjectSource, form: Form, site: LocatedName) -> bool {
    *site.source == *source && site.span == form_span(form) && location_in_source(site)
}

spec fn literal_result(
    source: &ProjectSource, form: Form, port: Option<TypedPort>, limit: u64,
    result: Result<Option<u64>, FuncLiteralError>,
) -> bool {
    if !is_literal(form) {
        result == Ok(None)
    } else if port is Some && port->Some_0.ty is Struct {
        let port = port->Some_0;
        result matches Err(FuncLiteralError::StructRequired { literal, type_at, ty })
            && rhs_location(source, form, literal) && type_at == port.annotation && ty == port.ty
    } else {
        let span = form_span(form);
        let bits = match port { Some(port) if port.ty is Bits => Some(port.ty->Bits_0), _ => None };
        let required = match port { Some(port) => Some(port.annotation), None => None };
        let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
        match result {
            Ok(Some(width)) => circuit_literal_width_matches(bytes, bits, limit, Ok(width)),
            Err(FuncLiteralError::Width { literal, required_at, reason }) =>
                rhs_location(source, form, literal) && required_at == required
                    && circuit_literal_width_matches(bytes, bits, limit, Err(reason)),
            _ => false,
        }
    }
}

fn literal_width<'p, 'a>(
    source: &'p ProjectSource<'a>, forms: &[Form], at: usize, port: Option<&TypedPort<'p, 'a>>, limit: u64,
) -> (result: Result<Option<u64>, FuncLiteralError<'p, 'a>>)
    requires
        at < forms@.len(),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures literal_result(source, forms@[at as int], match port { Some(port) => Some(*port), None => None }, limit, result),
{
    if !matches!(forms[at], Form::Atom {
        kind: AtomKind::Binary | AtomKind::Hexadecimal | AtomKind::Natural, ..
    }) {
        return Ok(None);
    }
    let (word, span) = read_indexed_atom(source.text, forms, at);
    let literal = LocatedName { source, span };
    proof { located_name_evidence(literal); }
    let (expected, required_at) = if let Some(port) = port {
        let required_at = LocatedName {
            source: port.annotation.source,
            span: port.annotation.span.start..port.annotation.span.end,
        };
        match port.ty {
            ResolvedPortType::Struct { .. } =>
                return Err(FuncLiteralError::StructRequired { literal, type_at: required_at, ty: port.ty }),
            ResolvedPortType::Bits(bits) => (Some(bits), Some(required_at)),
        }
    } else {
        (None, None)
    };
    match check_circuit_literal_width(word, expected, limit) {
        Ok(width) => Ok(Some(width)),
        Err(reason) => Err(FuncLiteralError::Width { literal, required_at, reason }),
    }
}

#[verifier::opaque]
spec fn driver_literal_result(
    source: &ProjectSource, parsed: &NamedBuildCircuit, drivers: &FuncDrivers, map: Seq<Option<usize>>,
    i: int, limit: u64, result: Result<Option<u64>, FuncLiteralError>,
) -> bool {
    let driver = drivers.definitions@[i];
    if driver.result_index != 0 {
        result == Ok(None)
    } else {
        let expression = parsed.definitions@[driver.definition as int].expression.start;
        let port = match map[i] { Some(port) => Some(drivers.signature.outputs@[port as int]), None => None };
        literal_result(source, parsed.syntax.forms@[expression as int], port, limit, result)
    }
}

#[verifier::opaque]
spec fn literal_prefix(
    source: &ProjectSource, parsed: &NamedBuildCircuit, drivers: &FuncDrivers,
    map: Seq<Option<usize>>, limit: u64, widths: Seq<Option<u64>>,
) -> bool {
    &&& widths.len() <= drivers.definitions@.len()
    &&& forall|i: int| 0 <= i < widths.len()
        ==> #[trigger] driver_literal_result(source, parsed, drivers, map, i, limit, Ok(widths[i]))
}

pub(super) closed spec fn literal_widths_match(
    source: &ProjectSource, parsed: &NamedBuildCircuit, drivers: &FuncDrivers,
    limit: u64, result: Result<Vec<Option<u64>>, FuncLiteralError>,
) -> bool {
    exists|map: Seq<Option<usize>>| #[trigger] output_indices(drivers, drivers.outputs@.len() as int, map)
        && match result {
            Ok(widths) => widths@.len() == drivers.definitions@.len()
                && literal_prefix(source, parsed, drivers, map, limit, widths@),
            Err(error) => exists|prefix: Seq<Option<u64>>|
                #[trigger] literal_prefix(source, parsed, drivers, map, limit, prefix)
                    && prefix.len() < drivers.definitions@.len()
                    && driver_literal_result(source, parsed, drivers, map, prefix.len() as int, limit, Err(error)),
        }
}

pub(super) fn check_literals<'p, 'a>(
    source: &'p ProjectSource<'a>, parsed: &NamedBuildCircuit, _entry: usize, drivers: &FuncDrivers<'p, 'a>, limit: u64,
) -> (result: Result<Vec<Option<u64>>, FuncLiteralError<'p, 'a>>)
    requires
        parsed_circuit_matches(*source, *parsed),
        _entry < parsed.syntax.entries@.len(),
        expected_output_context(source, parsed, _entry as int, *drivers),
    ensures literal_widths_match(source, parsed, drivers, limit, result),
        result matches Err(error) ==> !(error is Arity),
{
    let map = index_outputs(drivers);
    let mut widths = Vec::new();
    let mut i = 0;
    proof { reveal(literal_prefix); }
    while i < drivers.definitions.len()
        invariant
            expected_output_context(source, parsed, _entry as int, *drivers),
            parsed_circuit_matches(*source, *parsed), _entry < parsed.syntax.entries@.len(),
            output_indices(drivers, drivers.outputs@.len() as int, map@),
            i == widths@.len() <= drivers.definitions@.len(),
            literal_prefix(source, parsed, drivers, map@, limit, widths@),
        decreases drivers.definitions@.len() - i,
    {
        let driver = &drivers.definitions[i];
        // 個数検査を通った定数の右辺は一出力なので、結果位置 0 で調べる。
        let result = if driver.result_index == 0 {
            proof {
                reveal(output_indices);
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), _entry as int, driver.definition as int);
            }
            let at = parsed.definitions[driver.definition].expression.start;
            let port = match map[i] { Some(port) => Some(&drivers.signature.outputs[port]), None => None };
            literal_width(source, parsed.syntax.forms.as_slice(), at, port, limit)
        } else { Ok(None) };
        assert(driver_literal_result(source, parsed, drivers, map@, i as int, limit, result)) by {
            reveal(driver_literal_result);
        };
        let width = match result {
            Ok(width) => width,
            Err(error) => {
                proof { reveal(driver_literal_result); }
                return Err(error);
            },
        };
        let ghost prior = widths@;
        widths.push(width);
        proof {
            reveal(literal_prefix);
            assert forall|j: int| 0 <= j < widths@.len() implies
                #[trigger] driver_literal_result(source, parsed, drivers, map@, j, limit, Ok(widths@[j])) by {
                if j < i {
                    assert(widths@[j] == prior[j]);
                    assert(driver_literal_result(source, parsed, drivers, map@, j, limit, Ok(prior[j])));
                } else {
                    assert(j == i && widths@[j] == width);
                }
            };
        }
        i += 1;
    }
    Ok(widths)
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 同じ関数で成功した定数検査では、幅が付く定義とその幅が一致する。
    pub(super) proof fn checked_literal_widths_agree(
        &self, file: usize, entry: usize, limit: u64, left: FuncLiteralWidths, right: FuncLiteralWidths,
    )
        requires
            self.can_resolve(),
            left.wiring is Checked,
            right.wiring is Checked,
            self.func_literal_evidence(file, entry, limit, Ok(left)),
            self.func_literal_evidence(file, entry, limit, Ok(right)),
        ensures left.widths@ == right.widths@,
    {
        let l = left.wiring->Checked_0;
        let r = right.wiring->Checked_0;
        self.literals_preserve_arity(file, entry, limit, left);
        self.literals_preserve_arity(file, entry, limit, right);
        self.arity_preserves_wiring(file, entry, limit, left.wiring);
        self.arity_preserves_wiring(file, entry, limit, right.wiring);
        self.checked_func_wiring_agrees(file, entry, limit, l, r);
        let ld = &l.drivers;
        let rd = &r.drivers;
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let a = self.checked_literal_output_map(file, entry, limit, &left, &l);
        let b = self.checked_literal_output_map(file, entry, limit, &right, &r);
        output_indices_agree(ld, rd, a, b);
        reveal(literal_prefix);
        assert forall|i: int| 0 <= i < left.widths@.len() implies
            (#[trigger] left.widths@[i]) == (#[trigger] right.widths@[i]) by {
            assert(same_definition_driver(ld.definitions@[i], rd.definitions@[i]));
            assert(driver_literal_result(source, parsed, ld, a, i, limit, Ok(left.widths@[i])));
            assert(driver_literal_result(source, parsed, rd, b, i, limit, Ok(right.widths@[i])));
            reveal(driver_literal_result);
            if let (Some(x), Some(y)) = (left.widths@[i], right.widths@[i]) {
                let form = parsed.syntax.forms@[parsed.definitions@[ld.definitions@[i].definition as int].expression.start as int];
                let span = form_span(form);
                let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
                let port = match a[i] { Some(port) => Some(ld.signature.outputs@[port as int]), None => None };
                let expected = match port { Some(port) if port.ty is Bits => Some(port.ty->Bits_0), _ => None };
                successful_literal_widths_agree(bytes, expected, limit, x, y);
            }
        };
        assert(left.widths@ =~= right.widths@);
    }

    proof fn checked_literal_output_map(
        &self, file: usize, entry: usize, limit: u64, literals: &FuncLiteralWidths, wiring: &crate::project::FuncWiring,
    ) -> (map: Seq<Option<usize>>)
        requires
            literals.wiring == FuncWiringResult::Checked(*wiring),
            self.func_literal_evidence(file, entry, limit, Ok(*literals)),
        ensures
            output_indices(&wiring.drivers, wiring.drivers.outputs@.len() as int, map),
            ({
                let project = self.targets.project_model();
                literal_prefix(&project.sources_model()[file as int], &project.circuits_model()[file as int],
                    &wiring.drivers, map, limit, literals.widths@)
            }),
    {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let drivers = &wiring.drivers;
        choose|map: Seq<Option<usize>>| #[trigger] output_indices(drivers, drivers.outputs@.len() as int, map)
            && literal_prefix(source, parsed, drivers, map, limit, literals.widths@)
    }

    proof fn literal_width_at(
        &self, file: usize, entry: usize, limit: u64, literals: &FuncLiteralWidths,
        wiring: &crate::project::FuncWiring, i: int,
    )
        requires
            self.func_literal_evidence(file, entry, limit, Ok(*literals)),
            literals.wiring == FuncWiringResult::Checked(*wiring),
            0 <= i < wiring.drivers.definitions@.len(),
        ensures ({
            let project = self.targets.project_model();
            let parsed = project.circuits_model()[file as int];
            let driver = wiring.drivers.definitions@[i];
            let form = parsed.syntax.forms@[parsed.definitions@[driver.definition as int].expression.start as int];
            &&& (!is_literal(form) ==> literals.widths@[i].is_none())
            &&& (is_literal(form) && driver.result_index == 0
                ==> exists|port: Option<TypedPort>| #[trigger] literal_result(
                    &project.sources_model()[file as int], form, port, limit, Ok(literals.widths@[i]),
                ))
        }),
    {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let drivers = &wiring.drivers;
        let map = self.checked_literal_output_map(file, entry, limit, literals, wiring);
        reveal(literal_prefix);
        assert(driver_literal_result(source, parsed, drivers, map, i, limit, Ok(literals.widths@[i])));
        reveal(driver_literal_result);
    }

    pub(super) proof fn nonliteral_definition_has_no_literal_width(
        &self, file: usize, entry: usize, limit: u64, literals: &FuncLiteralWidths,
        wiring: &crate::project::FuncWiring, i: int,
    )
        requires
            self.func_literal_evidence(file, entry, limit, Ok(*literals)),
            literals.wiring == FuncWiringResult::Checked(*wiring),
            0 <= i < wiring.drivers.definitions@.len(),
            ({
                let parsed = self.targets.project_model().circuits_model()[file as int];
                let row = parsed.definitions@[wiring.drivers.definitions@[i].definition as int];
                let form = parsed.syntax.forms@[row.expression.start as int];
                form is List || (form is Atom && form->Atom_kind is Name)
            }),
        ensures literals.widths@[i].is_none(),
    {
        self.literal_width_at(file, entry, limit, literals, wiring, i);
    }

    pub(super) proof fn fixed_bit_definition_has_unit_width(
        &self, file: usize, entry: usize, limit: u64, literals: &FuncLiteralWidths,
        wiring: &crate::project::FuncWiring, i: int, bit: bool,
    )
        requires
            self.func_literal_evidence(file, entry, limit, Ok(*literals)),
            literals.wiring == FuncWiringResult::Checked(*wiring),
            0 <= i < wiring.drivers.definitions@.len(),
            wiring.drivers.definitions@[i].result_index == 0,
            ({
                let project = self.targets.project_model();
                let parsed = project.circuits_model()[file as int];
                let row = parsed.definitions@[wiring.drivers.definitions@[i].definition as int];
                let form = parsed.syntax.forms@[row.expression.start as int];
                let span = form_span(form);
                &&& form is Atom && form->Atom_kind is Natural
                &&& project.sources_model()[file as int].text.spec_bytes()[span.start as int..span.end as int]
                    == (if bit { "1" } else { "0" }).spec_bytes()
            }),
        ensures literals.widths@[i] == Some(1),
    {
        self.literal_width_at(file, entry, limit, literals, wiring, i);
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let row = parsed.definitions@[wiring.drivers.definitions@[i].definition as int];
        let form = parsed.syntax.forms@[row.expression.start as int];
        let port = choose|port: Option<TypedPort>|
            #[trigger] literal_result(source, form, port, limit, Ok(literals.widths@[i]));
        let span = form_span(form);
        let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
        let expected = match port { Some(port) if port.ty is Bits => Some(port.ty->Bits_0), _ => None };
        crate::project::literal_width::fixed_bit_literal_width(bytes, expected, limit, literals.widths@[i]->Some_0);
    }

    /// ビット列リテラルの右辺に、型検査で決めた幅を対応付ける。
    pub(super) proof fn bit_vector_definition_width(
        &self, file: usize, entry: usize, limit: u64, literals: &FuncLiteralWidths,
        wiring: &crate::project::FuncWiring, i: int,
    ) -> (bits: u64)
        requires
            self.func_literal_evidence(file, entry, limit, Ok(*literals)),
            literals.wiring == FuncWiringResult::Checked(*wiring),
            0 <= i < wiring.drivers.definitions@.len(),
            wiring.drivers.definitions@[i].result_index == 0,
            ({
                let parsed = self.targets.project_model().circuits_model()[file as int];
                let row = parsed.definitions@[wiring.drivers.definitions@[i].definition as int];
                let form = parsed.syntax.forms@[row.expression.start as int];
                form is Atom && (form->Atom_kind is Binary || form->Atom_kind is Hexadecimal)
            }),
        ensures
            literals.widths@[i] == Some(bits),
            ({
                let project = self.targets.project_model();
                let source = &project.sources_model()[file as int];
                let parsed = &project.circuits_model()[file as int];
                let row = parsed.definitions@[wiring.drivers.definitions@[i].definition as int];
                let span = form_span(parsed.syntax.forms@[row.expression.start as int]);
                let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
                exists|expected: Option<u64>| #[trigger] circuit_literal_width_matches(bytes, expected, limit, Ok(bits))
            }),
    {
        self.literal_width_at(file, entry, limit, literals, wiring, i);
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let row = parsed.definitions@[wiring.drivers.definitions@[i].definition as int];
        let form = parsed.syntax.forms@[row.expression.start as int];
        let port = choose|port: Option<TypedPort>|
            #[trigger] literal_result(source, form, port, limit, Ok(literals.widths@[i]));
        let span = form_span(form);
        let bytes = source.text.spec_bytes()[span.start as int..span.end as int];
        let expected = match port { Some(port) if port.ty is Bits => Some(port.ty->Bits_0), _ => None };
        let bits = literals.widths@[i]->Some_0;
        assert(circuit_literal_width_matches(bytes, expected, limit, Ok(bits)));
        bits
    }

    pub(super) proof fn literal_widths_fit_wiring(
        &self, file: usize, entry: usize, limit: u64, literals: &FuncLiteralWidths, wiring: &crate::project::FuncWiring,
    )
        requires self.func_literal_evidence(file, entry, limit, Ok(*literals)),
            literals.wiring == FuncWiringResult::Checked(*wiring),
        ensures literals.widths@.len() == wiring.drivers.definitions@.len(),
    {}

    pub(super) proof fn literals_preserve_arity(
        &self, file: usize, entry: usize, limit: u64, literals: FuncLiteralWidths,
    )
        requires self.func_literal_evidence(file, entry, limit, Ok(literals)),
        ensures self.func_arity_evidence(file, entry, limit, Ok(literals.wiring)),
            literals.wiring matches FuncWiringResult::Checked(wiring) ==>
                literals.widths@.len() == wiring.drivers.definitions@.len(),
    {
    }
    /// 定数だけを対象とした幅の検査が、出力の駆動元と元ソースに対応することを表す。
    pub closed spec fn func_literal_evidence(
        &self, file: usize, entry: usize, limit: u64, result: Result<FuncLiteralWidths, FuncLiteralError>,
    ) -> bool {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        match result {
            Err(FuncLiteralError::Arity(error)) => self.func_arity_evidence(file, entry, limit, Err(error)),
            Ok(widths) => self.func_arity_evidence(file, entry, limit, Ok(widths.wiring)) &&
                match widths.wiring {
                    FuncWiringResult::Checked(wiring) =>
                        literal_widths_match(source, parsed, &wiring.drivers, limit, Ok(widths.widths)),
                    _ => widths.widths@.len() == 0,
                },
            Err(error) => exists|wiring: FuncWiringResult| wiring is Checked
                && #[trigger] self.func_arity_evidence(file, entry, limit, Ok(wiring))
                && literal_widths_match(source, parsed, &wiring->Checked_0.drivers, limit, Err(error)),
        }
    }

    /// `func` の配線と個数を検査し、定数の右辺だけにビット幅を割り当てる。
    ///
    /// 出力を駆動する定数には出力の宣言型を使う。局所定義ではリテラル自身の幅を使う。
    /// 呼び出し、信号参照、専用フォームの型の検査は後続の段階で行う。
    ///
    /// # Errors
    ///
    /// 配線と個数の診断を優先し、その後は元ソース順に最初の定数の違反を返す。
    /// 出力の要求型と合わなければ、右辺の範囲と出力の型注釈を返す。
    pub fn check_func_literal_widths(
        &self, file: usize, entry: usize, max_width: u64,
    ) -> (result: Result<FuncLiteralWidths<'p, 'a>, FuncLiteralError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.func_literal_evidence(file, entry, max_width, result),
    {
        let wiring = match self.check_func_arity(file, entry, max_width) {
            Ok(wiring) => wiring,
            Err(error) => return Err(FuncLiteralError::Arity(error)),
        };
        let FuncWiringResult::Checked(ref checked) = wiring else {
            return Ok(FuncLiteralWidths { wiring, widths: Vec::new() });
        };
        proof {
            self.arity_preserves_wiring(file, entry, max_width, wiring);
            self.checked_wiring_is_func(file, entry, max_width, *checked);
        }
        let project = self.targets.project();
        let result = check_literals(&project.sources()[file], &project.circuits()[file], entry, &checked.drivers, max_width);
        match result {
            Ok(widths) => Ok(FuncLiteralWidths { wiring, widths }),
            Err(error) => {
                assert(self.func_literal_evidence(file, entry, max_width, Err(error))) by {
                    assert(self.func_arity_evidence(file, entry, max_width, Ok(wiring)));
                };
                Err(error)
            },
        }
    }
}

} // verus!
