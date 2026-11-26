//! 展開後の本体を、通常のビット列関数で使う駆動元と右辺へ変換する。

use super::{
    BitFuncRhs, CheckedBitDefinition, CheckedBitFunc, GeneratedWiringError, LocalSignalIndex, LocalSignalKey,
    OutputDriver, TypedRoutineSignature, bit_port_widths, generated_driver_width, index_generated_inputs,
    rows::{ScopedDefinition, ScopedOperand, ScopedRhs},
};
use crate::project::{LocatedName, SingleBitOperand, use_aliases::function_atoms::copy_location};
use crate::syntax::circuit::NameSite;
use alloc::{boxed::Box, vec::Vec};
use vstd::prelude::*;
#[cfg(verus_only)]
use super::{BindingKey, indexed_keys, ordinary_port_key,
    rows::{operand_location, scoped_definition_locations}};
#[cfg(verus_only)]
use crate::project::GeneratedSignalAlias;
#[cfg(verus_only)]
use super::super::{bit_definition_matches, bit_driver_width, checked_bit_func_available, nor_operand_matches};

verus! {

/// 展開後の関数を結線・幅検査できなかった理由。
#[derive(Debug)]
pub enum ExpandedFuncWiringError<'p, 'a> {
    /// 共有の署名・展開・出力検査で見つかった診断。
    Base(GeneratedWiringError<'p, 'a>),
    /// プロジェクトの基底ゲート宣言に違反がある。
    Basis(crate::project::CircuitBasisError<'p, 'a>),
    /// 通常の定義の右辺が、この入口の対応範囲外である。
    UnsupportedOrdinary(LocatedName<'p, 'a>),
    /// 呼び出しを解決する元のスコープを参照できない。
    NorScope(LocatedName<'p, 'a>),
    /// NOR 候補がユーザー定義の関数に解決された。
    NorResolvesToFunction {
        /// 元の呼び出し名。
        callee: LocatedName<'p, 'a>,
        /// 通常の名前解決で得た元の宣言。
        declaration: crate::project::ProjectDeclaration<'p, 'a>,
    },
    /// NOR 候補の名前解決に失敗した。
    NorName {
        /// 元の呼び出し名。
        callee: LocatedName<'p, 'a>,
        /// 通常の名前解決が報告した違反。
        error: crate::project::MixedFuncCalleeError<'p, 'a>,
    },
    /// 生成定義の検査で見つかった違反。
    Generated {
        /// この定義を生成した `expand` の文書版と UTF-8 半開バイト範囲。診断の主範囲に使う。
        call: LocatedName<'p, 'a>,
        /// 原因の診断。テンプレートまたは挿入元の構文を指す範囲を含む。
        cause: Box<ExpandedFuncWiringError<'p, 'a>>,
    },
    /// 同じ定義または後続の定義の信号を参照した。
    UnavailableDefinition {
        /// 右辺の参照箇所。
        reference: LocatedName<'p, 'a>,
        /// 先行していない左辺の元位置。
        target: LocatedName<'p, 'a>,
    },
    /// 生成定義の幅が出力ポートの宣言幅と一致しない。
    OutputWidthFromDefinition {
        /// 駆動元となる左辺の元位置。
        target: LocatedName<'p, 'a>,
        /// 宣言した出力幅を指す元位置。
        output: LocatedName<'p, 'a>,
        /// 出力ポートの宣言幅。
        expected: u64,
        /// 駆動元の幅。
        actual: u64,
    },
    /// 基底 NOR の入力が1ビットではない。
    NorInputWidth {
        /// 信号参照が元の構文に現れた位置。
        reference: LocatedName<'p, 'a>,
        /// 実際に束縛された信号の幅。
        width: u64,
    },
}

/// 生成行の診断が、原因の診断と生成元の呼び出しを保持することを表す。
pub open spec fn expanded_definition_diagnostic_wraps(
    call: Option<LocatedName>, cause: ExpandedFuncWiringError, error: ExpandedFuncWiringError,
) -> bool {
    match call {
        Some(site) => error matches ExpandedFuncWiringError::Generated { call, cause: inner }
            && call == site && *inner == cause,
        None => error == cause,
    }
}

pub(super) fn with_generated_call<'p, 'a>(
    call: Option<&LocatedName<'p, 'a>>, cause: ExpandedFuncWiringError<'p, 'a>,
) -> (error: ExpandedFuncWiringError<'p, 'a>)
    ensures expanded_definition_diagnostic_wraps(
        match call { Some(site) => Some(*site), None => None }, cause, error,
    ),
{
    match call {
        Some(call) => ExpandedFuncWiringError::Generated { call: copy_location(call), cause: Box::new(cause) },
        None => cause,
    }
}

/// 生成診断で保持する、幅・名前・結線の原因を指す元範囲を返す。
pub open spec fn expanded_definition_cause_location<'p, 'a>(cause: ExpandedFuncWiringError<'p, 'a>) -> Option<LocatedName<'p, 'a>> {
    match cause {
        ExpandedFuncWiringError::Base(GeneratedWiringError::MultipleDrivers(site))
        | ExpandedFuncWiringError::Base(GeneratedWiringError::Unavailable(site))
        | ExpandedFuncWiringError::NorScope(site)
        | ExpandedFuncWiringError::NorName { callee: site, .. }
        | ExpandedFuncWiringError::NorResolvesToFunction { callee: site, .. }
        | ExpandedFuncWiringError::NorInputWidth { reference: site, .. }
        | ExpandedFuncWiringError::OutputWidthFromDefinition { target: site, .. }
        | ExpandedFuncWiringError::UnavailableDefinition { reference: site, .. } => Some(site),
        _ => None,
    }
}

pub(super) open spec fn operand_diagnostic_at(operand: ScopedOperand, error: ExpandedFuncWiringError) -> bool {
    &&& error is UnavailableDefinition || error is NorInputWidth
        || (error matches ExpandedFuncWiringError::Base(cause) && cause is Unavailable)
    &&& expanded_definition_cause_location(error) == Some(operand_location(operand))
}

pub(super) open spec fn rhs_diagnostic_at(rhs: ScopedRhs, error: ExpandedFuncWiringError) -> bool {
    match rhs {
        ScopedRhs::Leaf(operand) => operand_diagnostic_at(operand, error),
        ScopedRhs::Nor { left, right, .. } => operand_diagnostic_at(left, error) || operand_diagnostic_at(right, error),
    }
}

pub(super) open spec fn row_diagnostic_at(definition: ScopedDefinition, error: ExpandedFuncWiringError) -> bool {
    match error {
        ExpandedFuncWiringError::Base(GeneratedWiringError::MultipleDrivers(site))
        | ExpandedFuncWiringError::OutputWidthFromDefinition { target: site, .. } =>
            site == definition.target.location_model(),
        _ => rhs_diagnostic_at(definition.rhs, error),
    }
}

// 名前解決を終えてから、生成済みの定義を検査して見つかる違反。
pub(super) open spec fn generated_error_after_collection(error: ExpandedFuncWiringError) -> bool {
    error matches ExpandedFuncWiringError::Generated { cause, .. }
        && match *cause {
            ExpandedFuncWiringError::Base(GeneratedWiringError::MultipleDrivers(_))
            | ExpandedFuncWiringError::Base(GeneratedWiringError::Unavailable(_))
            | ExpandedFuncWiringError::UnavailableDefinition { .. }
            | ExpandedFuncWiringError::NorInputWidth { .. }
            | ExpandedFuncWiringError::OutputWidthFromDefinition { .. } => true,
            _ => false,
        }
}

pub(super) open spec fn scoped_wiring_diagnostic_source(
    definitions: Seq<ScopedDefinition>, error: ExpandedFuncWiringError,
) -> bool {
    match error {
        ExpandedFuncWiringError::Generated { call, cause } =>
            exists|i: int| 0 <= i < definitions.len() && (#[trigger] definitions[i]).call == Some(call)
                && row_diagnostic_at(definitions[i], *cause),
        _ => true,
    }
}

proof fn scoped_diagnostic_from_row(
    definitions: Seq<ScopedDefinition>, at: int, cause: ExpandedFuncWiringError, error: ExpandedFuncWiringError,
)
    requires
        0 <= at < definitions.len(), !(cause is Generated), row_diagnostic_at(definitions[at], cause),
        expanded_definition_diagnostic_wraps(definitions[at].call, cause, error),
    ensures scoped_wiring_diagnostic_source(definitions, error),
{}

pub(super) proof fn scoped_diagnostic_cause_location(definitions: Seq<ScopedDefinition>, error: ExpandedFuncWiringError)
    requires
        scoped_wiring_diagnostic_source(definitions, error),
        forall|i: int| 0 <= i < definitions.len() ==> scoped_definition_locations(#[trigger] definitions[i]),
    ensures error matches ExpandedFuncWiringError::Generated { cause, .. } ==>
        expanded_definition_cause_location(*cause) matches Some(site)
            && crate::project::location_in_source(site),
{
    if let ExpandedFuncWiringError::Generated { call, cause } = error {
        let i = choose|i: int| 0 <= i < definitions.len() && (#[trigger] definitions[i]).call == Some(call)
            && row_diagnostic_at(definitions[i], *cause);
        let row = definitions[i];
        assert(scoped_definition_locations(row));
        assert(row_diagnostic_at(row, *cause));
    }
}

spec fn scoped_target_key(definition: ScopedDefinition) -> BindingKey {
    definition.target.key_model().model()
}

spec fn driver_names_key(
    inputs: Seq<NameSite>, definitions: Seq<ScopedDefinition>, key: BindingKey, driver: OutputDriver,
) -> bool {
    match driver {
        OutputDriver::Input(port) => port < inputs.len() && key == ordinary_port_key(inputs[port as int]),
        OutputDriver::Definition(row) => row < definitions.len() && key == scoped_target_key(definitions[row as int]),
    }
}

spec fn function_keys(
    inputs: Seq<NameSite>, definitions: Seq<ScopedDefinition>, at: int, names: Map<BindingKey, OutputDriver>,
) -> bool {
    &&& 0 <= at <= definitions.len()
    &&& forall|i: int| 0 <= i < inputs.len() ==> {
        let key = ordinary_port_key(#[trigger] inputs[i]);
        names.contains_key(key) && names[key] == OutputDriver::Input(i as usize)
    }
    &&& forall|i: int| 0 <= i < at ==> {
        let key = scoped_target_key(#[trigger] definitions[i]);
        names.contains_key(key) && names[key] == OutputDriver::Definition(i as usize)
    }
    &&& forall|key: BindingKey| #[trigger] names.contains_key(key) ==>
        driver_names_key(inputs, definitions.take(at), key, names[key])
}

proof fn add_scope_key(
    inputs: Seq<NameSite>, definitions: Seq<ScopedDefinition>, at: usize, before: Map<BindingKey, OutputDriver>,
)
    requires function_keys(inputs, definitions, at as int, before), at < definitions.len(),
        !before.contains_key(scoped_target_key(definitions[at as int])),
    ensures function_keys(inputs, definitions, at + 1,
        before.insert(scoped_target_key(definitions[at as int]), OutputDriver::Definition(at))),
{
    let added = scoped_target_key(definitions[at as int]);
    let next = before.insert(added, OutputDriver::Definition(at));
    assert forall|i: int| 0 <= i < at + 1 implies {
        let key = scoped_target_key(#[trigger] definitions[i]);
        next.contains_key(key) && next[key] == OutputDriver::Definition(i as usize)
    } by {
        if i < at { assert(before.contains_key(scoped_target_key(definitions[i]))); }
    };
    assert forall|key: BindingKey| #[trigger] next.contains_key(key) implies
        driver_names_key(inputs, definitions.take(at + 1), key, next[key]) by {
        if key != added {
            assert(driver_names_key(inputs, definitions.take(at as int), key, before[key]));
        }
    };
}

fn index_scoped_definitions<'p, 'a>(
    signature: &TypedRoutineSignature<'p, 'a>, input_names: &[NameSite], definitions: &[ScopedDefinition<'p, 'a>],
) -> (result: Result<LocalSignalIndex, ExpandedFuncWiringError<'p, 'a>>)
    requires signature.inputs@.len() == input_names@.len(),
    ensures
        result matches Ok(index) ==> index.valid()
            && function_keys(input_names@, definitions@, definitions@.len() as int, index.keyed_bindings()),
        result matches Err(error) ==> scoped_wiring_diagnostic_source(definitions@, error),
{
    let mut index = match index_generated_inputs(signature, input_names) {
        Ok(index) => index,
        Err(error) => return Err(ExpandedFuncWiringError::Base(error)),
    };
    proof {
        assert(indexed_keys(input_names@, Seq::<GeneratedSignalAlias>::empty(), input_names@.len() as int, 0, index.keyed_bindings()));
        assert(input_names@.take(input_names@.len() as int) =~= input_names@);
        assert forall|key: BindingKey| #[trigger] index.keyed_bindings().contains_key(key) implies
            driver_names_key(input_names@, definitions@.take(0), key, index.keyed_bindings()[key]) by {
            let driver = index.keyed_bindings()[key];
            assert(super::same_driver_key(input_names@, Seq::<GeneratedSignalAlias>::empty(), 0, key, driver));
        };
    }
    let mut i = 0;
    while i < definitions.len()
        invariant i <= definitions@.len(), index.valid(), function_keys(input_names@, definitions@, i as int, index.keyed_bindings()),
        decreases definitions@.len() - i,
    {
        let key = definitions[i].target.key();
        let ghost before = index.keyed_bindings();
        match index.insert_key_if_absent(key, OutputDriver::Definition(i)) {
            Some(None) => {},
            Some(Some(_)) => {
                let definition = &definitions[i];
                let cause = ExpandedFuncWiringError::Base(GeneratedWiringError::MultipleDrivers(copy_location(definition.target.location())));
                let ghost plain = cause;
                let error = with_generated_call(definition.call.as_ref(), cause);
                proof { scoped_diagnostic_from_row(definitions@, i as int, plain, error); }
                return Err(error);
            },
            None => return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::Capacity)),
        }
        proof { add_scope_key(input_names@, definitions@, i, before); }
        i += 1;
    }
    Ok(index)
}

spec fn operand_has_driver(
    inputs: Seq<NameSite>, definitions: Seq<ScopedDefinition>, operand: ScopedOperand, value: SingleBitOperand,
) -> bool {
    match (operand, value) {
        (ScopedOperand::Signal(name), SingleBitOperand::Driver(driver)) =>
            driver_names_key(inputs, definitions, name.key_model().model(), driver),
        (ScopedOperand::Bit { value, .. }, SingleBitOperand::Constant(bit)) => value == bit,
        _ => false,
    }
}

// 未定義、自己参照・前方参照、先行する駆動元を同じキーの完全一致で区別する。
#[verifier::opaque]
spec fn scoped_operand_result(
    keys: Map<BindingKey, OutputDriver>, definitions: Seq<ScopedDefinition>, at: usize,
    operand: ScopedOperand, result: Result<SingleBitOperand, ExpandedFuncWiringError>,
) -> bool {
    match operand {
        ScopedOperand::Bit { value, .. } => result == Ok(SingleBitOperand::Constant(value)),
        ScopedOperand::Signal(name) => {
            let key = name.key_model().model();
            if !keys.contains_key(key) {
                result matches Err(ExpandedFuncWiringError::Base(GeneratedWiringError::Unavailable(site)))
                    && site == name.location_model()
            } else {
                let driver = keys[key];
                if let OutputDriver::Definition(i) = driver {
                    if i >= at {
                        &&& i < definitions.len()
                        &&& result matches Err(ExpandedFuncWiringError::UnavailableDefinition { reference, target })
                        &&& reference == name.location_model() && target == definitions[i as int].target.location_model()
                    } else {
                        result == Ok(SingleBitOperand::Driver(driver))
                    }
                } else {
                    result == Ok(SingleBitOperand::Driver(driver))
                }
            }
        },
    }
}

fn resolve_operand<'p, 'a>(
    index: &LocalSignalIndex, names: &[NameSite], definitions: &[ScopedDefinition<'p, 'a>],
    at: usize, operand: &ScopedOperand<'p, 'a>,
) -> (result: Result<SingleBitOperand, ExpandedFuncWiringError<'p, 'a>>)
    requires index.valid(), at <= definitions@.len(),
        function_keys(names@, definitions@, definitions@.len() as int, index.keyed_bindings()),
    ensures
        scoped_operand_result(index.keyed_bindings(), definitions@, at, *operand, result),
        result matches Err(error) ==> !(error is NorInputWidth) && !(error is Generated)
            && operand_diagnostic_at(*operand, error),
        result matches Ok(value) ==> operand_has_driver(names@, definitions@.take(at as int), *operand, value),
{
    proof { reveal(scoped_operand_result); }
    match operand {
        ScopedOperand::Bit { value, .. } => Ok(SingleBitOperand::Constant(*value)),
        ScopedOperand::Signal(name) => {
            let key = name.key();
            let Some(driver) = index.lookup_key(key) else {
                return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::Unavailable(copy_location(name.location()))));
            };
            proof {
                assert(index.keyed_bindings().contains_key(key.model()));
                assert(definitions@.take(definitions@.len() as int) =~= definitions@);
                assert(driver_names_key(names@, definitions@, key.model(), driver));
            }
            if let OutputDriver::Definition(i) = driver {
                let _ = definitions.len();
                if i >= at {
                    return Err(ExpandedFuncWiringError::UnavailableDefinition {
                        reference: copy_location(name.location()),
                        target: copy_location(definitions[i].target.location()),
                    });
                }
            }
            Ok(SingleBitOperand::Driver(driver))
        },
    }
}

fn bound_width(inputs: &[u64], prior: &[CheckedBitDefinition], value: SingleBitOperand) -> (width: u64)
    requires value matches SingleBitOperand::Driver(driver) ==> bit_driver_width(inputs@, prior@, driver).is_some(),
    ensures
        width == if let SingleBitOperand::Driver(driver) = value { bit_driver_width(inputs@, prior@, driver).unwrap() } else { 1 },
        nor_operand_matches(inputs@, prior@, value) == (width == 1),
{
    match value {
        SingleBitOperand::Driver(driver) => generated_driver_width(inputs, prior, driver),
        SingleBitOperand::Constant(_) => 1,
    }
}

fn location_of_operand<'p, 'a>(value: &ScopedOperand<'p, 'a>) -> (site: LocatedName<'p, 'a>)
    ensures site == operand_location(*value),
{
    match value {
        ScopedOperand::Signal(name) => copy_location(name.location()),
        ScopedOperand::Bit { site, .. } => copy_location(site),
    }
}

fn resolve_nor_operand<'p, 'a>(
    index: &LocalSignalIndex, widths: &[u64], names: &[NameSite], definitions: &[ScopedDefinition<'p, 'a>],
    at: usize, prior: &[CheckedBitDefinition], operand: &ScopedOperand<'p, 'a>,
) -> (result: Result<SingleBitOperand, ExpandedFuncWiringError<'p, 'a>>)
    requires index.valid(), at == prior@.len() <= definitions@.len(), names@.len() == widths@.len(),
        function_keys(names@, definitions@, definitions@.len() as int, index.keyed_bindings()),
    ensures
        result matches Ok(bound) ==> nor_operand_matches(widths@, prior@, bound)
            && operand_has_driver(names@, definitions@.take(at as int), *operand, bound),
        result matches Err(error) ==> !(error is Generated) && operand_diagnostic_at(*operand, error),
        result matches Err(ExpandedFuncWiringError::NorInputWidth { reference, width }) ==> {
            &&& width != 1 && reference == operand_location(*operand)
            &&& exists|driver: OutputDriver| #[trigger] operand_has_driver(
                names@, definitions@.take(at as int), *operand, SingleBitOperand::Driver(driver))
                && bit_driver_width(widths@, prior@, driver) == Some(width)
        },
{
    let bound = resolve_operand(index, names, definitions, at, operand)?;
    let width = bound_width(widths, prior, bound);
    if width != 1 {
        proof {
            let driver = bound->Driver_0;
            assert(operand_has_driver(names@, definitions@.take(at as int), *operand, SingleBitOperand::Driver(driver)));
        }
        return Err(ExpandedFuncWiringError::NorInputWidth { reference: location_of_operand(operand), width });
    }
    Ok(bound)
}

spec fn scoped_rhs_bound(
    names: Seq<NameSite>, definitions: Seq<ScopedDefinition>, at: int, syntax: ScopedRhs, lowered: BitFuncRhs,
) -> bool {
    let visible = definitions.take(at);
    match (syntax, lowered) {
        (ScopedRhs::Leaf(operand), BitFuncRhs::Driver(driver)) =>
            operand_has_driver(names, visible, operand, SingleBitOperand::Driver(driver)),
        (ScopedRhs::Leaf(operand), BitFuncRhs::Constant(bit)) =>
            operand_has_driver(names, visible, operand, SingleBitOperand::Constant(bit)),
        (ScopedRhs::Nor { left, right, .. }, BitFuncRhs::Nor { left: lhs, right: rhs }) =>
            operand_has_driver(names, visible, left, lhs) && operand_has_driver(names, visible, right, rhs),
        _ => false,
    }
}

fn check_scoped_rhs<'p, 'a>(
    index: &LocalSignalIndex, widths: &[u64], names: &[NameSite], definitions: &[ScopedDefinition<'p, 'a>],
    at: usize, prior: &[CheckedBitDefinition<'p, 'a>],
) -> (result: Result<CheckedBitDefinition<'p, 'a>, ExpandedFuncWiringError<'p, 'a>>)
    requires index.valid(), at == prior@.len() < definitions@.len(), names@.len() == widths@.len(),
        function_keys(names@, definitions@, definitions@.len() as int, index.keyed_bindings()),
        scoped_definition_locations(definitions@[at as int]),
        forall|i: int| 0 <= i < widths@.len() ==> #[trigger] widths@[i] > 0,
        forall|i: int| 0 <= i < prior@.len() ==> (#[trigger] prior@[i]).width > 0,
    ensures
        result matches Ok(checked) ==> bit_definition_matches(widths@, prior@, checked)
            && checked.expression == definitions@[at as int].expression
            && scoped_rhs_bound(names@, definitions@, at as int, definitions@[at as int].rhs, checked.rhs),
        result matches Err(error) ==> !(error is Generated)
            && rhs_diagnostic_at(definitions@[at as int].rhs, error),
{
    let statement = &definitions[at];
    let (rhs, width) = match &statement.rhs {
        ScopedRhs::Leaf(operand) => {
            let bound = resolve_operand(index, names, definitions, at, operand)?;
            let width = bound_width(widths, prior, bound);
            let rhs = match bound {
                SingleBitOperand::Driver(driver) => BitFuncRhs::Driver(driver),
                SingleBitOperand::Constant(bit) => BitFuncRhs::Constant(bit),
            };
            (rhs, width)
        },
        ScopedRhs::Nor { left, right, .. } => {
            let lhs = resolve_nor_operand(index, widths, names, definitions, at, prior, left)?;
            let rhs = resolve_nor_operand(index, widths, names, definitions, at, prior, right)?;
            (BitFuncRhs::Nor { left: lhs, right: rhs }, 1)
        },
    };
    Ok(CheckedBitDefinition { expression: copy_location(&statement.expression), width, rhs, operands: Vec::new() })
}

spec fn scoped_definition_bound(
    inputs: Seq<u64>, names: Seq<NameSite>, definitions: Seq<ScopedDefinition>, prior: Seq<CheckedBitDefinition>,
    at: int, row: CheckedBitDefinition,
) -> bool {
    &&& row.expression == definitions[at].expression
    &&& scoped_rhs_bound(names, definitions, at, definitions[at].rhs, row.rhs)
    &&& bit_definition_matches(inputs, prior, row)
}

spec fn wired_definitions(
    inputs: Seq<u64>, names: Seq<NameSite>, definitions: Seq<ScopedDefinition>, rows: Seq<CheckedBitDefinition>,
) -> bool {
    &&& rows.len() <= definitions.len()
    &&& forall|at: int| 0 <= at < rows.len() ==>
        scoped_definition_bound(inputs, names, definitions, rows.take(at), at, #[trigger] rows[at])
    &&& forall|at: int| 0 <= at < rows.len() ==> (#[trigger] rows[at]).width > 0
}

proof fn append_wired_definition(
    inputs: Seq<u64>, names: Seq<NameSite>, definitions: Seq<ScopedDefinition>, prefix: Seq<CheckedBitDefinition>,
    row: CheckedBitDefinition,
)
    requires wired_definitions(inputs, names, definitions, prefix), prefix.len() < definitions.len(),
        scoped_definition_bound(inputs, names, definitions, prefix, prefix.len() as int, row),
    ensures wired_definitions(inputs, names, definitions, prefix.push(row)),
{
    let after = prefix.push(row);
    assert forall|i: int| 0 <= i < after.len() implies
        scoped_definition_bound(inputs, names, definitions, after.take(i), i, #[trigger] after[i]) by {
        if i < prefix.len() {
            assert(after[i] == prefix[i]);
            assert(after.take(i) =~= prefix.take(i));
        } else {
            assert(after.take(i) =~= prefix);
        }
    };
}

fn wire_scoped_definitions<'p, 'a>(
    index: &LocalSignalIndex, widths: &[u64], names: &[NameSite], definitions: &[ScopedDefinition<'p, 'a>],
) -> (result: Result<Vec<CheckedBitDefinition<'p, 'a>>, ExpandedFuncWiringError<'p, 'a>>)
    requires
        index.valid(), widths@.len() == names@.len(),
        function_keys(names@, definitions@, definitions@.len() as int, index.keyed_bindings()),
        forall|i: int| 0 <= i < widths@.len() ==> #[trigger] widths@[i] > 0,
        forall|i: int| 0 <= i < definitions@.len() ==> scoped_definition_locations(#[trigger] definitions@[i]),
    ensures
        result matches Ok(rows) ==> rows@.len() == definitions@.len()
            && wired_definitions(widths@, names@, definitions@, rows@),
        result matches Err(error) ==> scoped_wiring_diagnostic_source(definitions@, error),
{
    let mut rows: Vec<CheckedBitDefinition<'p, 'a>> = Vec::new();
    let mut at = 0;
    while at < definitions.len()
        invariant
            at == rows@.len() <= definitions@.len(), index.valid(), widths@.len() == names@.len(),
            function_keys(names@, definitions@, definitions@.len() as int, index.keyed_bindings()),
            forall|i: int| 0 <= i < widths@.len() ==> #[trigger] widths@[i] > 0,
            forall|i: int| 0 <= i < definitions@.len() ==> scoped_definition_locations(#[trigger] definitions@[i]),
            wired_definitions(widths@, names@, definitions@, rows@),
        decreases definitions@.len() - at,
    {
        let row = match check_scoped_rhs(index, widths, names, definitions, at, rows.as_slice()) {
            Ok(row) => row,
            Err(cause) => {
                let ghost plain = cause;
                let error = with_generated_call(definitions[at].call.as_ref(), cause);
                proof { scoped_diagnostic_from_row(definitions@, at as int, plain, error); }
                return Err(error);
            },
        };
        proof { append_wired_definition(widths@, names@, definitions@, rows@, row); }
        rows.push(row);
        at += 1;
    }
    Ok(rows)
}

spec fn scoped_output_matches(
    inputs: Seq<u64>, input_names: Seq<NameSite>, outputs: Seq<u64>, output_names: Seq<NameSite>,
    definitions: Seq<ScopedDefinition>, rows: Seq<CheckedBitDefinition>, port: int, driver: OutputDriver,
) -> bool {
    &&& driver_names_key(input_names, definitions, ordinary_port_key(output_names[port]), driver)
    &&& bit_driver_width(inputs, rows, driver) == Some(outputs[port])
}

fn scoped_outputs<'p, 'a>(
    index: &LocalSignalIndex, signature: &TypedRoutineSignature<'p, 'a>, inputs: &[u64], input_names: &[NameSite],
    widths: &[u64], names: &[NameSite], definitions: &[ScopedDefinition<'p, 'a>], rows: &[CheckedBitDefinition<'p, 'a>],
) -> (result: Result<Vec<OutputDriver>, ExpandedFuncWiringError<'p, 'a>>)
    requires
        index.valid(), inputs@.len() == input_names@.len(), widths@.len() == names@.len() == signature.outputs@.len(),
        rows@.len() == definitions@.len(),
        function_keys(input_names@, definitions@, definitions@.len() as int, index.keyed_bindings()),
    ensures
        result matches Ok(drivers) ==> drivers@.len() == widths@.len()
            && forall|i: int| 0 <= i < drivers@.len() ==> scoped_output_matches(
                inputs@, input_names@, widths@, names@, definitions@, rows@, i, #[trigger] drivers@[i]),
        result matches Err(error) ==> scoped_wiring_diagnostic_source(definitions@, error),
{
    let mut drivers: Vec<OutputDriver> = Vec::new();
    let mut i = 0;
    while i < names.len()
        invariant
            i == drivers@.len() <= widths@.len() == names@.len() == signature.outputs@.len(),
            index.valid(), inputs@.len() == input_names@.len(), rows@.len() == definitions@.len(),
            function_keys(input_names@, definitions@, definitions@.len() as int, index.keyed_bindings()),
            forall|j: int| 0 <= j < i ==> scoped_output_matches(
                inputs@, input_names@, widths@, names@, definitions@, rows@, j, #[trigger] drivers@[j]),
        decreases names@.len() - i,
    {
        let output = &signature.outputs[i];
        let key = LocalSignalKey::ordinary(names[i].word);
        let Some(driver) = index.lookup_key(key) else {
            return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::MissingOutput(copy_location(&output.annotation))));
        };
        let _ = inputs.len();
        let _ = rows.len();
        proof {
            assert(key.model() == ordinary_port_key(names@[i as int]));
            assert(index.keyed_bindings().contains_key(key.model()));
            assert(definitions@.take(definitions@.len() as int) =~= definitions@);
            assert(driver_names_key(input_names@, definitions@, key.model(), driver));
        }
        let actual = generated_driver_width(inputs, rows, driver);
        let expected = widths[i];
        if actual != expected {
            let site = copy_location(&output.annotation);
            if let OutputDriver::Definition(at) = driver {
                let definition = &definitions[at];
                if let Some(call) = &definition.call {
                    let cause = ExpandedFuncWiringError::OutputWidthFromDefinition {
                        target: copy_location(definition.target.location()), output: site, expected, actual,
                    };
                    let ghost plain = cause;
                    let error = with_generated_call(Some(call), cause);
                    proof { scoped_diagnostic_from_row(definitions@, at as int, plain, error); }
                    return Err(error);
                }
            }
            return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::OutputWidth { site, expected, actual }));
        }
        drivers.push(driver);
        i += 1;
    }
    Ok(drivers)
}

pub(super) closed spec fn expanded_bit_func_wiring(
    inputs: Seq<NameSite>, outputs: Seq<NameSite>, definitions: Seq<ScopedDefinition>, checked: &CheckedBitFunc,
) -> bool {
    &&& checked_bit_func_available(checked)
    &&& checked.input_widths@.len() == inputs.len() && checked.output_widths@.len() == outputs.len()
    &&& checked.definitions@.len() == definitions.len()
    &&& wired_definitions(checked.input_widths@, inputs, definitions, checked.definitions@)
    &&& forall|i: int| 0 <= i < checked.input_widths@.len() ==>
        checked.signature_model().inputs@[i].ty == super::ResolvedPortType::Bits(#[trigger] checked.input_widths@[i])
    &&& forall|i: int| 0 <= i < checked.output_widths@.len() ==>
        checked.signature_model().outputs@[i].ty == super::ResolvedPortType::Bits(#[trigger] checked.output_widths@[i])
    &&& forall|i: int| 0 <= i < checked.output_drivers@.len() ==> scoped_output_matches(checked.input_widths@,
        inputs, checked.output_widths@, outputs, definitions, checked.definitions@, i, #[trigger] checked.output_drivers@[i])
}

pub(super) fn check_scoped_wiring<'p, 'a>(
    signature: TypedRoutineSignature<'p, 'a>, input_names: &[NameSite], output_names: &[NameSite],
    body: &[ScopedDefinition<'p, 'a>],
) -> (result: Result<CheckedBitFunc<'p, 'a>, ExpandedFuncWiringError<'p, 'a>>)
    requires
        input_names@.len() == signature.inputs@.len(),
        0 < output_names@.len() == signature.outputs@.len(),
        forall|i: int| 0 <= i < body@.len() ==> scoped_definition_locations(#[trigger] body@[i]),
    ensures
        result matches Ok(checked) ==> checked_bit_func_available(&checked)
            && checked.signature_model() == signature && expanded_bit_func_wiring(input_names@, output_names@, body@, &checked),
        result matches Err(error) ==> scoped_wiring_diagnostic_source(body@, error),
{
    let input_widths = match bit_port_widths(signature.inputs.as_slice()) {
        Ok(widths) => widths,
        Err(error) => return Err(ExpandedFuncWiringError::Base(error)),
    };
    let output_widths = match bit_port_widths(signature.outputs.as_slice()) {
        Ok(widths) => widths,
        Err(error) => return Err(ExpandedFuncWiringError::Base(error)),
    };
    let index = index_scoped_definitions(&signature, input_names, body)?;
    let definitions = wire_scoped_definitions(&index, input_widths.as_slice(), input_names, body)?;
    let output_drivers = scoped_outputs(&index, &signature, input_widths.as_slice(), input_names,
        output_widths.as_slice(), output_names, body, definitions.as_slice())?;
    proof {
        reveal(checked_bit_func_available);
        assert forall|i: int| 0 <= i < definitions@.len() implies bit_definition_matches(
            input_widths@, definitions@.take(i), #[trigger] definitions@[i],
        ) by {
            assert(scoped_definition_bound(input_widths@, input_names@, body@, definitions@.take(i), i, definitions@[i]));
        };
        assert forall|i: int| 0 <= i < output_drivers@.len() implies
            bit_driver_width(input_widths@, definitions@, #[trigger] output_drivers@[i])
                == Some(output_widths@[i]) by {
            assert(scoped_output_matches(input_widths@, input_names@, output_widths@, output_names@,
                body@, definitions@, i, output_drivers@[i]));
        };
    }
    Ok(CheckedBitFunc { signature, input_widths, output_widths, definitions, output_drivers })
}

} // verus!
