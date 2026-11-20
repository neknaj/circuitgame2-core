//! 検査済みの構文、結線、型からビット列の組み合わせ回路を取り出す。

use alloc::vec::Vec;
use vstd::prelude::*;

use super::{BitFuncRhs, CheckedBitDefinition, CheckedBitFunc};
use super::super::{
    FuncCallSignatureError, FuncCallTarget, FuncSignalTypeError, FuncWiring, FuncWiringResult, OutputDriver,
    ResolvedPortType, SelectionArgumentError, SingleBitOperand, TypedPort, TypedRoutineSignature, UseAliases,
};
use super::super::function_atoms::{copy_location, named_selection};
use super::super::selection_arguments::check_selection_arguments;
use crate::project::{LocatedName, ProjectSource};
use crate::project::circuits::form_location;
use crate::syntax::{Form, circuit::{NamedBuildCircuit, definition_target_atoms}};

#[cfg(verus_only)]
use super::{bit_definition_matches, bit_driver_width, checked_bit_func_available, nor_operand_matches};
#[cfg(verus_only)]
use super::super::{
    FuncSignalTypes, TypedFuncCall, function_atoms::named_selection_matches, function_drivers::{checked_ports_and_output_bounds, expected_output_context},
    port_types::typed_name_sites, selection_arguments::selection_arguments_match, single_bit_func::{no_operand, operand_matches},
};
#[cfg(verus_only)]
use crate::project::location_in_source;
#[cfg(verus_only)]
use crate::project::circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use crate::syntax::{form_spans_valid, circuit::{
    BitSelectionShape, bit_selection_shape_positions, build_definition_scope_evidence,
    definition_target_range, indexed_entry_evidence,
}};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 現段階のビット列の回路へ取り出せない構文または型。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedBitFunc {
    /// 入力または出力に正の幅を持つビット列型を要求する。
    PortType,
    /// 出力ポートがない。
    OutputCount,
    /// 左辺に複数の結果が並んでいる。
    DefinitionOutputCount,
    /// 右辺が対応する構文に収まらない。
    Expression,
}

/// 幅付きの組み合わせ回路を取り出すときの診断。
#[derive(Debug)]
pub enum BitFuncError<'p, 'a> {
    /// 指定された項目が関数ではない。
    NotFunc,
    /// 展開が必要な箇所。
    NeedsExpansion(LocatedName<'p, 'a>),
    /// 既存の型・結線検査で見つかった違反。
    Check(FuncSignalTypeError<'p, 'a>),
    /// 定義内の呼び出し先の検査で見つかった違反。
    Call(usize, FuncCallSignatureError<'p, 'a>),
    /// ビット選択の引数の違反。
    Selection(SelectionArgumentError<'p, 'a>),
    /// 基底 NOR の入力幅の違反。
    NorInputWidth {
        /// 当該引数の位置。
        argument: LocatedName<'p, 'a>,
        /// 入力の幅。
        actual: u64,
    },
    /// 出力宣言と出力を駆動する値の幅が異なる。
    OutputWidth {
        /// 出力の宣言型を指定した位置。
        annotation: LocatedName<'p, 'a>,
        /// 宣言された幅。
        expected: u64,
        /// 駆動元の幅。
        actual: u64,
    },
    /// 正規化の対象に含まれない箇所。
    Unsupported(UnsupportedBitFunc, LocatedName<'p, 'a>),
}

struct FuncProjection<'w, 'p, 'a> {
    file: usize,
    entry: usize,
    limit: u64,
    source: &'p ProjectSource<'a>,
    parsed: &'p NamedBuildCircuit<'a>,
    wiring: &'w FuncWiring<'p, 'a>,
}

spec fn supported_ports(ports: Seq<TypedPort>) -> bool {
    forall|i: int| 0 <= i < ports.len() ==>
        ((#[trigger] ports[i]).ty matches ResolvedPortType::Bits(width) && width > 0)
}

spec fn unsupported_port(source: &ProjectSource, forms: Seq<Form>, ports: Seq<TypedPort>, site: LocatedName) -> bool {
    exists|i: int| 0 <= i < ports.len()
        && !((#[trigger] ports[i]).ty matches ResolvedPortType::Bits(width) && width > 0)
        && is_form_location(source, forms[ports[i].declared.site.name as int], site)
        && forall|j: int| 0 <= j < i ==>
            ((#[trigger] ports[j]).ty matches ResolvedPortType::Bits(width) && width > 0)
}

fn check_ports<'p, 'a>(source: &'p ProjectSource<'a>, forms: &[Form], ports: &[TypedPort<'p,'a>])
    -> (result: Result<(), LocatedName<'p, 'a>>)
    requires
        typed_name_sites(forms@, ports@),
        form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
    ensures
        result.is_ok() <==> supported_ports(ports@),
        result matches Err(location) ==> unsupported_port(source, forms@, ports@, location),
{
    let mut i = 0;
    while i < ports.len()
        invariant
            i <= ports@.len(),
            typed_name_sites(forms@, ports@),
            form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
            forall|j: int| 0 <= j < i ==>
                ((#[trigger] ports@[j]).ty matches ResolvedPortType::Bits(width) && width > 0),
        decreases ports@.len() - i,
    {
        let port = &ports[i];
        if !matches!(port.ty, ResolvedPortType::Bits(width) if width > 0) {
            return Err(form_location(source, forms, port.declared.site.name));
        }
        i += 1;
    }
    Ok(())
}

spec fn driver_width_origin<'p, 'a>(
    signature: &TypedRoutineSignature<'p, 'a>, prior: Seq<CheckedBitDefinition<'p, 'a>>, driver: OutputDriver,
) -> LocatedName<'p, 'a> {
    match driver {
        OutputDriver::Input(i) => signature.inputs@[i as int].annotation,
        OutputDriver::Definition(i) => prior[i as int].expression,
    }
}

fn driver_type<'w, 'p, 'a>(
    signature: &'w TypedRoutineSignature<'p, 'a>, prior: &'w [CheckedBitDefinition<'p, 'a>], driver: OutputDriver,
) -> (ty: (u64, &'w LocatedName<'p, 'a>))
    requires
        supported_ports(signature.inputs@),
        match driver {
            OutputDriver::Input(i) => i < signature.inputs@.len(),
            OutputDriver::Definition(i) => i < prior@.len(),
        },
    ensures
        bit_driver_width(signature, prior@, driver) == Some(ty.0),
        *ty.1 == driver_width_origin(signature, prior@, driver),
{
    match driver {
        OutputDriver::Input(i) => {
            let port = &signature.inputs[i];
            let ResolvedPortType::Bits(width) = port.ty else {
                proof { assert(false); }
                unreachable!()
            };
            (width, &port.annotation)
        },
        OutputDriver::Definition(i) => (prior[i].width, &prior[i].expression),
    }
}

fn operand_width(
    signature: &TypedRoutineSignature, prior: &[CheckedBitDefinition], operand: SingleBitOperand,
) -> (width: u64)
    requires
        supported_ports(signature.inputs@),
        super::super::single_bit_func::single_bit_operand_available(operand, signature.inputs@.len(), prior@.len()),
    ensures
        nor_operand_matches(signature, prior@, operand) <==> width == 1,
        operand is Constant ==> width == 1,
        operand matches SingleBitOperand::Driver(driver) ==> bit_driver_width(signature, prior@, driver) == Some(width),
{
    match operand {
        SingleBitOperand::Constant(_) => 1,
        SingleBitOperand::Driver(driver) => driver_type(signature, prior, driver).0,
    }
}

spec fn output_widths_before(
    signature: &TypedRoutineSignature, definitions: Seq<CheckedBitDefinition>, drivers: Seq<OutputDriver>, stop: int,
) -> bool {
    forall|j: int| 0 <= j < stop ==> bit_driver_width(signature, definitions, #[trigger] drivers[j])
        == Some(signature.outputs@[j].ty->Bits_0)
}

spec fn output_width_failure(
    signature: &TypedRoutineSignature, definitions: Seq<CheckedBitDefinition>, drivers: Seq<OutputDriver>, error: BitFuncError,
) -> bool {
    error matches BitFuncError::OutputWidth { annotation, expected, actual }
        && (exists|port: int| 0 <= port < drivers.len()
            && bit_driver_width(signature, definitions, #[trigger] drivers[port]) == Some(actual)
            && signature.outputs@[port].ty == ResolvedPortType::Bits(expected)
            && actual != expected && signature.outputs@[port].annotation == annotation
            && output_widths_before(signature, definitions, drivers, port))
}

fn check_output_widths<'p, 'a>(
    wiring: &FuncWiring<'p, 'a>, definitions: &[CheckedBitDefinition<'p, 'a>],
) -> (result: Result<(), BitFuncError<'p, 'a>>)
    requires
        supported_ports(wiring.drivers.signature.inputs@) && supported_ports(wiring.drivers.signature.outputs@),
        wiring.drivers.outputs@.len() == wiring.drivers.signature.outputs@.len(),
        forall|i: int| 0 <= i < wiring.drivers.outputs@.len() ==> match #[trigger] wiring.drivers.outputs@[i] {
            OutputDriver::Input(i) => i < wiring.drivers.signature.inputs@.len(),
            OutputDriver::Definition(i) => i < definitions@.len(),
        },
    ensures match result {
        Ok(()) => output_widths_before(&wiring.drivers.signature, definitions@, wiring.drivers.outputs@,
            wiring.drivers.outputs@.len() as int),
        Err(error) => output_width_failure(&wiring.drivers.signature, definitions@, wiring.drivers.outputs@, error),
    },
{
    let signature = &wiring.drivers.signature;
    let mut i = 0usize;
    while i < wiring.drivers.outputs.len()
        invariant
            *signature == wiring.drivers.signature,
            supported_ports(signature.inputs@) && supported_ports(signature.outputs@),
            i <= wiring.drivers.outputs@.len() == signature.outputs@.len(),
            forall|j: int| 0 <= j < wiring.drivers.outputs@.len() ==> match #[trigger] wiring.drivers.outputs@[j] {
                OutputDriver::Input(i) => i < signature.inputs@.len(),
                OutputDriver::Definition(i) => i < definitions@.len(),
            },
            output_widths_before(signature, definitions@, wiring.drivers.outputs@, i as int),
        decreases wiring.drivers.outputs@.len() - i,
    {
        let port = &signature.outputs[i];
        let ResolvedPortType::Bits(expected) = port.ty else {
            proof { assert(false); }
            unreachable!()
        };
        let (actual, _) = driver_type(signature, definitions, wiring.drivers.outputs[i]);
        if actual != expected {
            return Err(BitFuncError::OutputWidth { annotation: copy_location(&port.annotation), expected, actual });
        }
        i += 1;
    }
    Ok(())
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn projection_context(&self, scope: &FuncProjection) -> bool {
        let project = self.targets.project_model();
        &&& self.can_resolve()
        &&& self.func_wiring_evidence(scope.file, scope.entry, scope.limit, Ok(FuncWiringResult::Checked(*scope.wiring)))
        &&& scope.file < project.sources_model().len() && scope.file < project.circuits_model().len()
        &&& *scope.source == project.sources_model()[scope.file as int]
        &&& *scope.parsed == project.circuits_model()[scope.file as int]
        &&& parsed_circuit_matches(*scope.source, *scope.parsed)
        &&& scope.entry < scope.parsed.syntax.entries@.len()
        &&& expected_output_context(scope.source, scope.parsed, scope.entry as int, scope.wiring.drivers)
        &&& checked_ports_and_output_bounds(scope.parsed.syntax.forms@, scope.wiring.drivers)
    }

    spec fn bit_rhs_from_source(&self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, i: int,
        rhs: BitFuncRhs) -> bool {
        let parsed = scope.parsed;
        let forms = parsed.syntax.forms@;
        let definition = scope.wiring.drivers.definitions@[i].definition;
        let row = parsed.definitions@[definition as int];
        let root = row.expression.start as int;
        let entry = scope.entry;
        let local = (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let signature = &scope.wiring.drivers.signature;
        match rhs {
            BitFuncRhs::Driver(driver) =>
                operand_matches(scope.source, parsed, entry, definition, root, scope.wiring, i, SingleBitOperand::Driver(driver)),
            BitFuncRhs::Constant(bit) =>
                operand_matches(scope.source, parsed, entry, definition, root, scope.wiring, i, SingleBitOperand::Constant(bit)),
            BitFuncRhs::Nor { left, right } => {
                &&& forms[root] is List && row.expression.end == root + 4
                &&& operand_matches(scope.source, parsed, entry, definition, root + 2, scope.wiring, i, left)
                &&& operand_matches(scope.source, parsed, entry, definition, root + 3, scope.wiring, i, right)
                &&& exists|call: TypedFuncCall| #[trigger] self.func_call_signature_evidence(
                    scope.file, entry, local, 0, scope.limit, Ok(Some(call)),
                ) && call.call.call.form == root && call.call.call.arguments == 2 && call.call.target is Nor
            },
            BitFuncRhs::Selection { input, selection } => exists|shape: BitSelectionShape|
                #[trigger] named_selection_matches(scope.source.text, forms, root, shape)
                && (bit_driver_width(signature, prior, input) matches Some(width)
                && operand_matches(scope.source, parsed, entry, definition, shape.input.start as int, scope.wiring, i,
                    SingleBitOperand::Driver(input))
                && selection_arguments_match(scope.source, forms, &shape, width, &driver_width_origin(signature, prior, input),
                    Ok(selection))),
        }
    }

    spec fn bit_definition_from_source(
        &self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, i: int, checked: CheckedBitDefinition,
    ) -> bool {
        let parsed = scope.parsed;
        let row = parsed.definitions@[scope.wiring.drivers.definitions@[i].definition as int];
        let forms = parsed.syntax.forms@;
        let (first, end) = definition_target_range(forms, row);
        &&& end - first == 1
        &&& is_form_location(scope.source, forms[row.expression.start as int], checked.expression)
        &&& self.bit_rhs_from_source(scope, prior, i, checked.rhs)
        &&& bit_definition_matches(&scope.wiring.drivers.signature, prior, checked)
    }

    spec fn definition_prefix(&self, scope: &FuncProjection, definitions: Seq<CheckedBitDefinition>) -> bool {
        &&& definitions.len() <= scope.wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < definitions.len() ==>
            self.bit_definition_from_source(scope, definitions.take(i), i, #[trigger] definitions[i])
    }

    /// 入出力ポート、定義順、右辺の各参照が、検査した元の関数と対応することを表す。
    pub closed spec fn checked_bit_func_matches(&self, file: usize, entry: usize, limit: u64, checked: &CheckedBitFunc) -> bool {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        exists|typed: FuncSignalTypes| #[trigger] self.func_signal_types_evidence(file, entry, limit, Ok(typed))
            && (typed.literals.wiring matches FuncWiringResult::Checked(wiring)
            && {
                let scope = FuncProjection { file, entry, limit, source, parsed, wiring: &wiring };
                &&& self.projection_context(&scope)
                &&& checked.signature == wiring.drivers.signature
                &&& checked.definitions@.len() == wiring.drivers.definitions@.len()
                &&& self.definition_prefix(&scope, checked.definitions@)
                &&& checked.output_drivers@ == wiring.drivers.outputs@
            })
    }

    spec fn definition_error(
        &self, scope: &FuncProjection, prior: Seq<CheckedBitDefinition>, error: BitFuncError,
    ) -> bool {
        let parsed = scope.parsed;
        let entry = scope.entry;
        let wiring = scope.wiring;
        let signature = &wiring.drivers.signature;
        let source = scope.source;
        let forms = parsed.syntax.forms@;
        let i = prior.len() as int;
        let definition = wiring.drivers.definitions@[i].definition;
        let row = parsed.definitions@[definition as int];
        let root = row.expression.start as int;
        let (first, end) = definition_target_range(forms, row);
        let local = (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        let call_candidate = row.expression.end == root + 4 && forms[root] is List
            && (forall|shape: BitSelectionShape| !#[trigger] named_selection_matches(source.text, forms, root, shape));
        &&& i < wiring.drivers.definitions@.len()
        &&& (!(error matches BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, _))
            ==> end - first == 1 && no_operand(source, parsed, entry, definition, root, wiring, i))
        &&& match error {
            BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, site) =>
                end - first != 1 && is_form_location(source, forms[root], site),
            BitFuncError::Unsupported(UnsupportedBitFunc::Expression, site) => {
                if exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root, shape) {
                    exists|shape: BitSelectionShape| #[trigger] named_selection_matches(source.text, forms, root, shape)
                        && no_operand(source, parsed, entry, definition, shape.input.start as int, wiring, i)
                        && is_form_location(source, forms[root], site)
                } else {
                    self.unsupported_expression(scope.file, entry, scope.limit, wiring, i, site)
                }
            },
            BitFuncError::Call(position, error) => call_candidate && position == local
                && self.func_call_signature_evidence(scope.file, entry, position, 0, scope.limit, Err(error)),
            BitFuncError::Selection(error) => exists|shape: BitSelectionShape, driver: OutputDriver|
                #![trigger named_selection_matches(source.text, forms, root, shape),
                    bit_driver_width(signature, prior, driver)]
                named_selection_matches(source.text, forms, root, shape)
                && operand_matches(source, parsed, entry, definition, shape.input.start as int, wiring, i, SingleBitOperand::Driver(driver))
                && (bit_driver_width(signature, prior, driver) matches Some(width)
                    && selection_arguments_match(source, forms, &shape, width, &driver_width_origin(signature, prior, driver), Err(error))),
            BitFuncError::NorInputWidth { argument, actual } => call_candidate && actual != 1
                && (exists|left: SingleBitOperand, right: SingleBitOperand| #![trigger
                    operand_matches(source, parsed, entry, definition, root + 2, wiring, i, left),
                    operand_matches(source, parsed, entry, definition, root + 3, wiring, i, right)]
                    operand_matches(source, parsed, entry, definition, root + 2, wiring, i, left)
                    && operand_matches(source, parsed, entry, definition, root + 3, wiring, i, right)
                    && ((left matches SingleBitOperand::Driver(driver)
                            && bit_driver_width(signature, prior, driver) == Some(actual)
                            && is_form_location(source, forms[root + 2], argument))
                        || (nor_operand_matches(signature, prior, left)
                            && (right matches SingleBitOperand::Driver(driver)
                                && bit_driver_width(signature, prior, driver) == Some(actual)
                                && is_form_location(source, forms[root + 3], argument)))))
                && (exists|call: TypedFuncCall| #[trigger] self.func_call_signature_evidence(
                    scope.file, entry, local, 0, scope.limit, Ok(Some(call)),
                ) && call.call.call.form == root && call.call.call.arguments == 2 && call.call.target is Nor),
            _ => false,
        }
    }

    spec fn projection_failure(&self, scope: &FuncProjection, error: BitFuncError) -> bool {
        let signature = &scope.wiring.drivers.signature;
        let forms = scope.parsed.syntax.forms@;
        match error {
            BitFuncError::Unsupported(UnsupportedBitFunc::OutputCount, location) =>
                signature.outputs@.len() == 0
                && is_form_location(scope.source, forms[scope.parsed.syntax.entries@[scope.entry as int].form as int], location),
            BitFuncError::Unsupported(UnsupportedBitFunc::PortType, location) => signature.outputs@.len() > 0
                && (unsupported_port(scope.source, forms, signature.outputs@, location)
                    || (supported_ports(signature.outputs@) && unsupported_port(scope.source, forms, signature.inputs@, location))),
            _ => {
                &&& signature.outputs@.len() > 0
                &&& supported_ports(signature.outputs@) && supported_ports(signature.inputs@)
                &&& exists|prior: Seq<CheckedBitDefinition>| #[trigger] self.definition_prefix(scope, prior) && {
                    match error {
                        BitFuncError::OutputWidth { .. } =>
                            prior.len() == scope.wiring.drivers.definitions@.len()
                            && output_width_failure(signature, prior, scope.wiring.drivers.outputs@, error),
                        _ => self.definition_error(scope, prior, error),
                    }
                }
            },
        }
    }

    /// 診断が、型・結線検査または元ソースの対応範囲、右辺、出力型に根拠を持つことを表す。
    pub closed spec fn checked_bit_func_error(
        &self, file: usize, entry: usize, limit: u64, error: BitFuncError,
    ) -> bool {
        if let BitFuncError::Check(error) = error {
            self.func_signal_types_evidence(file, entry, limit, Err(error))
        } else {
            let project = self.targets.project_model();
            let source = &project.sources_model()[file as int];
            let parsed = &project.circuits_model()[file as int];
            exists|typed: FuncSignalTypes| #[trigger] self.func_signal_types_evidence(file, entry, limit, Ok(typed))
                && match (error, typed.literals.wiring) {
                    (BitFuncError::NotFunc, FuncWiringResult::NotFunc) => true,
                    (BitFuncError::NeedsExpansion(site), FuncWiringResult::NeedsExpansion(expansion)) => site == expansion,
                    (_, FuncWiringResult::Checked(wiring)) => {
                        let scope = FuncProjection { file, entry, limit, source, parsed, wiring: &wiring };
                        self.projection_context(&scope) && self.projection_failure(&scope, error)
                    },
                    _ => false,
                }
        }
    }

    proof fn projected_error(
        &self, scope: &FuncProjection, typed: FuncSignalTypes, error: BitFuncError,
    )
        requires
            self.func_signal_types_evidence(scope.file, scope.entry, scope.limit, Ok(typed)),
            typed.literals.wiring == FuncWiringResult::Checked(*scope.wiring),
            self.projection_context(scope),
            self.projection_failure(scope, error),
        ensures self.checked_bit_func_error(scope.file, scope.entry, scope.limit, error),
    {
    }

    fn project_definition(
        &self, scope: &FuncProjection<'_, 'p, 'a>, prior: &[CheckedBitDefinition<'p, 'a>], index: usize,
    ) -> (result: Result<CheckedBitDefinition<'p, 'a>, BitFuncError<'p, 'a>>)
        requires
            self.projection_context(scope),
            index == prior@.len() < scope.wiring.drivers.definitions@.len(),
            supported_ports(scope.wiring.drivers.signature.inputs@),
            forall|i: int| 0 <= i < prior@.len() ==>
                location_in_source((#[trigger] prior@[i]).expression) && prior@[i].width > 0,
        ensures
            result matches Ok(checked) ==> self.bit_definition_from_source(scope, prior@, index as int, checked),
            result matches Err(error) ==> self.definition_error(scope, prior@, error),
    {
        let file = scope.file;
        let entry = scope.entry;
        let limit = scope.limit;
        let source = scope.source;
        let parsed = scope.parsed;
        let wiring = scope.wiring;
        let signature = &wiring.drivers.signature;
        let definition = wiring.drivers.definitions[index].definition;
        let row = &parsed.definitions[definition];
        let root = row.expression.start;
        let end = row.expression.end;
        let forms = parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*source, *parsed);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, definition as int);
        }
        let expression = form_location(source, forms, root);
        let targets = definition_target_atoms(forms, row);
        if targets.end - targets.start != 1 {
            return Err(BitFuncError::Unsupported(UnsupportedBitFunc::DefinitionOutputCount, expression));
        }
        let (width, rhs) = if let Some(operand) = self.read_single_bit_operand(file, entry, limit, source, parsed, root, wiring, definition, index) {
            match operand {
                SingleBitOperand::Constant(bit) => (1, BitFuncRhs::Constant(bit)),
                SingleBitOperand::Driver(driver) => (driver_type(signature, prior, driver).0, BitFuncRhs::Driver(driver)),
            }
        } else if let Some(shape) = named_selection(source.text, forms, root) {
            proof { bit_selection_shape_positions(source.text, forms@, root as int, shape); }
            let Some(SingleBitOperand::Driver(input)) = self.read_single_bit_operand(
                file, entry, limit, source, parsed, shape.input.start, wiring, definition, index,
            ) else { return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, expression)); };
            let (width, origin) = driver_type(signature, prior, input);
            let selection = match check_selection_arguments(source, forms, root, &shape, width, origin) {
                Ok(checked) => checked,
                Err(error) => return Err(BitFuncError::Selection(error)),
            };
            (selection.count, BitFuncRhs::Selection { input, selection })
        } else if end - root == 4 && matches!(forms[root], Form::List { .. }) {
            let local = definition - parsed.entry_ranges[entry].definitions.start;
            let call = match self.resolve_func_call_signature(file, entry, local, 0, limit) {
                Ok(Some(call)) => call,
                Ok(None) => return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, expression)),
                Err(error) => return Err(BitFuncError::Call(local, error)),
            };
            if call.call.call.form != root || call.call.call.arguments != 2 || !matches!(call.call.target, FuncCallTarget::Nor) {
                return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, expression));
            }
            let Some(left) = self.read_single_bit_operand(file, entry, limit, source, parsed, root + 2, wiring, definition, index) else {
                return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, form_location(source, forms, root + 2)));
            };
            let Some(right) = self.read_single_bit_operand(file, entry, limit, source, parsed, root + 3, wiring, definition, index) else {
                return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, form_location(source, forms, root + 3)));
            };
            let left_width = operand_width(signature, prior, left);
            if left_width != 1 {
                return Err(BitFuncError::NorInputWidth { argument: form_location(source, forms, root + 2), actual: left_width });
            }
            let right_width = operand_width(signature, prior, right);
            if right_width != 1 {
                return Err(BitFuncError::NorInputWidth { argument: form_location(source, forms, root + 3), actual: right_width });
            }
            (1, BitFuncRhs::Nor { left, right })
        } else {
            return Err(BitFuncError::Unsupported(UnsupportedBitFunc::Expression, expression));
        };
        let checked = CheckedBitDefinition { expression, width, rhs };
        Ok(checked)
    }

    /// ビット列の組み合わせ関数を、宣言順のポートと定義順の右辺に取り出す。
    ///
    /// 信号の転送、定数 `0`・`1`、基底 NOR、裸の信号に対する `bit` と `slice` を扱う。
    ///
    /// # Errors
    ///
    /// 型・結線の違反を先に返す。対応範囲外の場合は、ポートや右辺の元ソース位置を返す。
    pub fn check_bit_func(
        &self, file: usize, entry: usize, limit: u64,
    ) -> (result: Result<CheckedBitFunc<'p, 'a>, BitFuncError<'p, 'a>>)
        requires self.can_resolve(),
        ensures match result {
            Ok(checked) => checked_bit_func_available(&checked) && self.checked_bit_func_matches(file, entry, limit, &checked),
            Err(error) => self.checked_bit_func_error(file, entry, limit, error),
        },
    {
        let typed = match self.check_func_signal_types(file, entry, limit) {
            Ok(typed) => typed,
            Err(error) => return Err(BitFuncError::Check(error)),
        };
        let ghost typed_model = typed;
        let wiring = match typed.literals.wiring {
            FuncWiringResult::Checked(wiring) => wiring,
            FuncWiringResult::NotFunc => return Err(BitFuncError::NotFunc),
            FuncWiringResult::NeedsExpansion(site) => return Err(BitFuncError::NeedsExpansion(site)),
        };
        proof {
            self.checked_types_keep_wiring(file, entry, limit, typed_model, wiring);
            self.checked_wiring_is_func(file, entry, limit, wiring);
            self.targets.parsed_project_model();
        }
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let forms = parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*source, *parsed);
            indexed_entry_evidence(source.text, forms@, parsed.syntax.entries@, entry as int);
        }
        let scope = FuncProjection { file, entry, limit, source, parsed, wiring: &wiring };
        let signature = &wiring.drivers.signature;
        if signature.outputs.is_empty() {
            let site = form_location(source, forms, parsed.syntax.entries[entry].form);
            let error = BitFuncError::Unsupported(UnsupportedBitFunc::OutputCount, site);
            proof { self.projected_error(&scope, typed_model, error); }
            return Err(error);
        }
        if let Err(location) = check_ports(source, forms, signature.outputs.as_slice()) {
            let error = BitFuncError::Unsupported(UnsupportedBitFunc::PortType, location);
            proof { self.projected_error(&scope, typed_model, error); }
            return Err(error);
        }
        if let Err(location) = check_ports(source, forms, signature.inputs.as_slice()) {
            let error = BitFuncError::Unsupported(UnsupportedBitFunc::PortType, location);
            proof { self.projected_error(&scope, typed_model, error); }
            return Err(error);
        }
        let mut definitions = Vec::new();
        let mut i = 0usize;
        while i < wiring.drivers.definitions.len()
            invariant
                self.projection_context(&scope),
                scope.wiring == &wiring && *signature == wiring.drivers.signature,
                scope.file == file && scope.entry == entry && scope.limit == limit,
                self.func_signal_types_evidence(file, entry, limit, Ok(typed_model)),
                typed_model.literals.wiring == FuncWiringResult::Checked(wiring),
                i == definitions@.len(),
                self.definition_prefix(&scope, definitions@),
                0 < signature.outputs@.len(),
                supported_ports(signature.outputs@), supported_ports(signature.inputs@),
                forall|j: int| 0 <= j < definitions@.len() ==>
                    location_in_source((#[trigger] definitions@[j]).expression)
                    && definitions@[j].width > 0,
            decreases wiring.drivers.definitions@.len() - i,
        {
            let checked = match self.project_definition(&scope, definitions.as_slice(), i) {
                Ok(checked) => checked,
                Err(error) => {
                    assert(self.projection_failure(&scope, error));
                    proof { self.projected_error(&scope, typed_model, error); }
                    return Err(error);
                },
            };
            let ghost previous = definitions@;
            definitions.push(checked);
            assert forall|j: int| 0 <= j < definitions@.len() implies
                self.bit_definition_from_source(&scope, definitions@.take(j), j, #[trigger] definitions@[j]) by {
                if j < i {
                    assert(definitions@[j] == previous[j]);
                    assert(definitions@.take(j) =~= previous.take(j));
                } else {
                    assert(definitions@.take(j) =~= previous);
                }
            };
            i += 1;
        }
        if let Err(error) = check_output_widths(&wiring, definitions.as_slice()) {
            assert(self.projection_failure(&scope, error));
            proof { self.projected_error(&scope, typed_model, error); }
            return Err(error);
        }
        proof { reveal(checked_bit_func_available); }
        let checked = CheckedBitFunc { signature: wiring.drivers.signature, definitions, output_drivers: wiring.drivers.outputs };
        assert(checked_bit_func_available(&checked));
        assert(self.checked_bit_func_matches(file, entry, limit, &checked));
        Ok(checked)
    }
}

} // verus!
