//! 1ビットの組み合わせ回路について、配線と右辺を降下に使える形へまとめる。

mod lowering;
pub use lowering::LoweredSingleBitFunc;
#[cfg(verus_only)]
pub use lowering::{
    single_bit_evaluation_result_agrees, single_bit_lowering_matches, single_bit_lowering_preserves_evaluation,
    single_bit_source_evaluation, single_bit_source_evaluations_agree,
};

use super::{FuncSignalTypeError, FuncWiring, FuncWiringResult, OutputDriver, ResolvedPortType, UseAliases};
use super::super::circuits::{form_location, read_indexed_atom};
use super::super::{DefinitionPosition, LocatedName, ProjectSource};
use super::{FuncCallSignatureError, FuncCallTarget};
use crate::syntax::circuit::{NamedBuildCircuit, definition_target_atoms};
use crate::syntax::{AtomKind, Form};
use alloc::vec::Vec;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::super::circuits::{is_form_location, parsed_circuit_matches, parsed_index_evidence};
#[cfg(verus_only)]
use super::{FuncSignalTypes, TypedFuncCall, TypedPort};
#[cfg(verus_only)]
use super::super::location_in_source;
#[cfg(verus_only)]
use crate::syntax::circuit::{build_definition_scope_evidence, definition_target_range, indexed_entry_evidence};
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid};
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::encode_utf8_decode_utf8};

verus! {

/// 右辺で使う1ビットの値。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SingleBitOperand {
    /// 入力または先行する定義から得る値。
    Driver(OutputDriver),
    /// 元ソースにある定数 `0` または `1`。
    Constant(bool),
}

/// 左辺の信号を駆動する右辺。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SingleBitRhs {
    /// 信号または定数をそのままつなぐ。
    Operand(SingleBitOperand),
    /// 1ビットの基底 NOR。
    Nor {
        /// 第1引数。
        left: SingleBitOperand,
        /// 第2引数。
        right: SingleBitOperand,
    },
}

/// 検査済みの一つの定義。
#[derive(Debug)]
pub struct SingleBitDefinition<'p, 'a> {
    /// 左辺の信号名の元ソース位置。
    pub name: LocatedName<'p, 'a>,
    /// 右辺全体の元ソース位置。
    pub expression: LocatedName<'p, 'a>,
    /// 束縛と値が決まった右辺。
    pub rhs: SingleBitRhs,
}

/// 入出力とすべての定義を1ビットとして検査した `func`。
#[derive(Debug)]
pub struct CheckedSingleBitFunc<'p, 'a> {
    declaration: LocatedName<'p, 'a>,
    inputs: Vec<LocatedName<'p, 'a>>,
    definitions: Vec<SingleBitDefinition<'p, 'a>>,
    output: LocatedName<'p, 'a>,
    output_driver: OutputDriver,
}

impl<'p, 'a> CheckedSingleBitFunc<'p, 'a> {
    #[verifier::type_invariant]
    spec fn available(&self) -> bool { single_bit_func_available(self) }

    /// 宣言全体の元ソース位置を返す。
    pub fn declaration(&self) -> (site: &LocatedName<'p, 'a>)
        ensures *site == self.declaration_model(),
    { &self.declaration }

    /// 入力名の位置を宣言順に返す。
    pub fn inputs(&self) -> (ports: &[LocatedName<'p, 'a>])
        ensures ports@ == self.inputs_model(),
    { self.inputs.as_slice() }

    /// 定義をソースに現れる順に返す。
    pub fn definitions(&self) -> (definitions: &[SingleBitDefinition<'p, 'a>])
        ensures definitions@ == self.definitions_model(),
    { self.definitions.as_slice() }

    /// 出力名の位置を返す。
    pub fn output(&self) -> (site: &LocatedName<'p, 'a>)
        ensures *site == self.output_model(),
    { &self.output }

    /// 唯一の出力を駆動する入力または定義を返す。
    pub fn output_driver(&self) -> (driver: OutputDriver)
        ensures driver == self.output_driver_model(),
    { self.output_driver }

    /// 宣言全体の元ソース位置を表す。
    pub closed spec fn declaration_model(&self) -> LocatedName<'p, 'a> { self.declaration }
    /// 宣言順の入力名の位置を表す。
    pub closed spec fn inputs_model(&self) -> Seq<LocatedName<'p, 'a>> { self.inputs@ }
    /// 定義順の右辺を表す。
    pub closed spec fn definitions_model(&self) -> Seq<SingleBitDefinition<'p, 'a>> { self.definitions@ }
    /// 出力名の位置を表す。
    pub closed spec fn output_model(&self) -> LocatedName<'p, 'a> { self.output }
    /// 出力を駆動する入力または定義を表す。
    pub closed spec fn output_driver_model(&self) -> OutputDriver { self.output_driver }
}

/// 現段階の降下で扱わない構文または型。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedSingleBitFunc {
    /// 入力または出力に1ビット以外の型がある。
    PortType,
    /// 出力の本数が1本ではない。
    OutputCount,
    /// 本体に複数結果の定義がある。
    DefinitionOutputCount,
    /// 右辺または引数が対応する形式に収まらない。
    Expression,
}

/// 選んだ `func` を降下用に検査できなかった理由。
#[derive(Debug)]
pub enum SingleBitFuncError<'p, 'a> {
    /// 指定位置に `func` がない。
    NotFunc,
    /// 先に展開が必要なマクロの位置。
    NeedsExpansion(LocatedName<'p, 'a>),
    /// 既存の型・結線検査で見つかった違反。
    Check(FuncSignalTypeError<'p, 'a>),
    /// 呼び出し先の解決で見つかった違反。
    Call(DefinitionPosition, FuncCallSignatureError<'p, 'a>),
    /// 仕様上の未対応箇所。
    Unsupported(UnsupportedSingleBitFunc, LocatedName<'p, 'a>),
}

/// 駆動元が入力または処理済みの定義を指すことを表す。
pub open spec fn single_bit_driver_available(driver: OutputDriver, inputs: nat, definitions: nat) -> bool {
    match driver {
        OutputDriver::Input(index) => index < inputs,
        OutputDriver::Definition(index) => index < definitions,
    }
}

/// オペランドが定数か、利用可能な駆動元を指すことを表す。
pub open spec fn single_bit_operand_available(operand: SingleBitOperand, inputs: nat, definitions: nat) -> bool {
    match operand {
        SingleBitOperand::Driver(driver) => single_bit_driver_available(driver, inputs, definitions),
        SingleBitOperand::Constant(_) => true,
    }
}

/// 右辺のオペランドが利用可能な値を参照することを表す。
pub open spec fn single_bit_rhs_available(rhs: SingleBitRhs, inputs: nat, definitions: nat) -> bool {
    match rhs {
        SingleBitRhs::Operand(value) => single_bit_operand_available(value, inputs, definitions),
        SingleBitRhs::Nor { left, right } =>
            single_bit_operand_available(left, inputs, definitions) && single_bit_operand_available(right, inputs, definitions),
    }
}

/// すべての右辺と出力が、利用可能な駆動元だけを参照することを表す。
pub open spec fn single_bit_func_available(checked: &CheckedSingleBitFunc) -> bool {
    &&& single_bit_driver_available(checked.output_driver_model(), checked.inputs_model().len(), checked.definitions_model().len())
    &&& forall|i: int| 0 <= i < checked.definitions_model().len()
        ==> single_bit_rhs_available((#[trigger] checked.definitions_model()[i]).rhs, checked.inputs_model().len(), i as nat)
}

fn driver_available(driver: OutputDriver, inputs: usize, definitions: usize) -> (available: bool)
    ensures available == single_bit_driver_available(driver, inputs as nat, definitions as nat),
{
    match driver {
        OutputDriver::Input(index) => index < inputs,
        OutputDriver::Definition(index) => index < definitions,
    }
}

spec fn prior_name_binding(
    parsed: &NamedBuildCircuit, entry: usize, definition: usize, root: int, wiring: &FuncWiring,
    prior: int, signal: int,
) -> bool {
    let row = parsed.definitions@[definition as int];
    let at = signal - parsed.entry_ranges@[entry as int].signals.start;
    &&& row.signals.start <= signal < row.signals.end <= parsed.signals@.len()
    &&& parsed.signals@[signal] == root
    &&& 0 <= at < wiring.signals@.len()
    &&& single_bit_driver_available(wiring.signals@[at].driver, wiring.drivers.signature.inputs@.len(), prior as nat)
}

spec fn one_bit_literal(source: &ProjectSource, form: Form, bit: bool) -> bool {
    let span = form_span(form);
    &&& form matches Form::Atom { kind: AtomKind::Natural, .. }
    &&& source.text.spec_bytes()[span.start as int..span.end as int]
        == (if bit { "1" } else { "0" }).spec_bytes()
}

spec fn operand_matches(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, definition: usize, root: int,
    wiring: &FuncWiring, prior: int, operand: SingleBitOperand,
) -> bool {
    let forms = parsed.syntax.forms@;
    &&& 0 <= root < forms.len()
    &&& match operand {
        SingleBitOperand::Constant(bit) => one_bit_literal(source, forms[root], bit),
        SingleBitOperand::Driver(driver) => forms[root] matches Form::Atom { kind: AtomKind::Name, .. }
            && exists|signal: int| prior_name_binding(parsed, entry, definition, root, wiring, prior, signal)
                && wiring.signals@[signal - parsed.entry_ranges@[entry as int].signals.start].driver == driver,
    }
}

spec fn no_operand(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, definition: usize, root: int,
    wiring: &FuncWiring, prior: int,
) -> bool {
    let forms = parsed.syntax.forms@;
    &&& 0 <= root < forms.len()
    &&& !one_bit_literal(source, forms[root], false)
    &&& !one_bit_literal(source, forms[root], true)
    &&& (forms[root] matches Form::Atom { kind: AtomKind::Name, .. } ==> forall|signal: int|
        !#[trigger] prior_name_binding(parsed, entry, definition, root, wiring, prior, signal))
}

proof fn operand_excludes_missing(
    source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, definition: usize, root: int,
    wiring: &FuncWiring, prior: int, operand: SingleBitOperand,
)
    requires
        operand_matches(source, parsed, entry, definition, root, wiring, prior, operand),
        no_operand(source, parsed, entry, definition, root, wiring, prior),
    ensures false,
{
    if let SingleBitOperand::Driver(driver) = operand {
        let signal = choose|signal: int| prior_name_binding(parsed, entry, definition, root, wiring, prior, signal)
            && wiring.signals@[signal - parsed.entry_ranges@[entry as int].signals.start].driver == driver;
        assert(!prior_name_binding(parsed, entry, definition, root, wiring, prior, signal));
    }
}

spec fn one_bit_input_types_before(ports: Seq<TypedPort>, stop: int) -> bool {
    &&& 0 <= stop <= ports.len()
    &&& forall|i: int| 0 <= i < stop ==> (#[trigger] ports[i]).ty == ResolvedPortType::Bits(1)
}

spec fn one_bit_input_matches(source: &ProjectSource, forms: Seq<Form>, port: TypedPort, site: LocatedName) -> bool {
    &&& port.ty == ResolvedPortType::Bits(1)
    &&& port.declared.site.name < forms.len()
    &&& is_form_location(source, forms[port.declared.site.name as int], site)
}

spec fn one_bit_inputs_match(source: &ProjectSource, forms: Seq<Form>, ports: Seq<TypedPort>, sites: Seq<LocatedName>) -> bool {
    &&& sites.len() <= ports.len()
    &&& forall|i: int| 0 <= i < sites.len()
        ==> one_bit_input_matches(source, forms, ports[i], #[trigger] sites[i])
}

proof fn input_locations_preserve_types(
    source: &ProjectSource, forms: Seq<Form>, ports: Seq<TypedPort>, sites: Seq<LocatedName>,
)
    requires one_bit_inputs_match(source, forms, ports, sites),
    ensures one_bit_input_types_before(ports, sites.len() as int),
{
    assert forall|i: int| 0 <= i < sites.len() implies (#[trigger] ports[i]).ty == ResolvedPortType::Bits(1) by {
        assert(one_bit_input_matches(source, forms, ports[i], sites[i]));
    };
}

proof fn one_bit_inputs_append(
    source: &ProjectSource, forms: Seq<Form>, ports: Seq<TypedPort>, before: Seq<LocatedName>, site: LocatedName,
)
    requires
        one_bit_inputs_match(source, forms, ports, before),
        before.len() < ports.len(),
        one_bit_input_matches(source, forms, ports[before.len() as int], site),
    ensures one_bit_inputs_match(source, forms, ports, before.push(site)),
{
    let next = before.push(site);
    assert forall|i: int| 0 <= i < next.len()
        implies one_bit_input_matches(source, forms, ports[i], #[trigger] next[i]) by {
        if i < before.len() { assert(next[i] == before[i]); }
    };
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn checked_rhs_matches(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, prior: int, rhs: SingleBitRhs,
    ) -> bool {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let forms = parsed.syntax.forms@;
        let definition = wiring.drivers.definitions@[prior].definition;
        let row = parsed.definitions@[definition as int];
        let start = row.expression.start as int;
        let end = row.expression.end as int;
        &&& 0 <= prior < wiring.drivers.definitions@.len()
        &&& definition_target_range(forms, row).1 - definition_target_range(forms, row).0 == 1
        &&& match rhs {
            SingleBitRhs::Operand(operand) =>
                operand_matches(source, parsed, entry, definition, start, wiring, prior, operand),
            SingleBitRhs::Nor { left, right } =>
                end == start + 4 && forms[start] is List
                && operand_matches(source, parsed, entry, definition, start + 2, wiring, prior, left)
                && operand_matches(source, parsed, entry, definition, start + 3, wiring, prior, right)
                && (exists|call: TypedFuncCall| #[trigger] self.func_call_signature_evidence(
                    file, entry, (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize,
                    0, limit, Ok(Some(call)),
                ) && call.call.call.form == start && call.call.call.arguments == 2 && call.call.target is Nor),
        }
    }

    spec fn checked_definitions_match(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, definitions: Seq<SingleBitDefinition>,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let forms = parsed.syntax.forms@;
        &&& definitions.len() <= wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < definitions.len() ==> {
            let checked = #[trigger] definitions[i];
            let driver = wiring.drivers.definitions@[i];
            let row = parsed.definitions@[driver.definition as int];
            &&& *checked.name.source == *source && checked.name.span == driver.name.span
            &&& is_form_location(source, forms[row.expression.start as int], checked.expression)
            &&& self.checked_rhs_matches(file, entry, limit, wiring, i, checked.rhs)
        }
    }

    /// 検査した入出力、定義、参照先を元の宣言に対応させる。
    pub closed spec fn single_bit_func_matches(
        &self, file: usize, entry: usize, limit: u64, checked: &CheckedSingleBitFunc,
    ) -> bool {
        let project = self.targets.project_model();
        let parsed = &project.circuits_model()[file as int];
        let source = &project.sources_model()[file as int];
        let forms = parsed.syntax.forms@;
        exists|wiring: FuncWiring| #[trigger] self.func_wiring_evidence(
            file, entry, limit, Ok(FuncWiringResult::Checked(wiring)),
        ) && {
            let signature = wiring.drivers.signature;
            &&& is_form_location(source, forms[parsed.syntax.entries@[entry as int].form as int], checked.declaration)
            &&& signature.inputs@.len() == checked.inputs@.len()
            &&& signature.outputs@.len() == 1
            &&& signature.outputs@[0].ty == ResolvedPortType::Bits(1)
            &&& is_form_location(source, forms[signature.outputs@[0].declared.site.name as int], checked.output)
            &&& checked.output_driver == wiring.drivers.outputs@[0]
            &&& one_bit_inputs_match(source, forms, signature.inputs@, checked.inputs@)
            &&& checked.definitions@.len() == wiring.drivers.definitions@.len()
            &&& self.checked_definitions_match(file, entry, limit, &wiring, checked.definitions@)
        }
    }

    spec fn unsupported_resolved_rhs(
        source: &ProjectSource, parsed: &NamedBuildCircuit, entry: usize, definition: usize, start: int,
        wiring: &FuncWiring, prior: int, call: TypedFuncCall, location: LocatedName,
    ) -> bool {
        let forms = parsed.syntax.forms@;
        if call.call.call.form == start && call.call.call.arguments == 2 && call.call.target is Nor {
            ||| is_form_location(source, forms[start + 2], location)
                && no_operand(source, parsed, entry, definition, start + 2, wiring, prior)
            ||| is_form_location(source, forms[start + 3], location)
                && no_operand(source, parsed, entry, definition, start + 3, wiring, prior)
                && (exists|operand: SingleBitOperand|
                    #[trigger] operand_matches(source, parsed, entry, definition, start + 2, wiring, prior, operand))
        } else {
            is_form_location(source, forms[start], location)
        }
    }

    spec fn unsupported_expression(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, prior: int, location: LocatedName,
    ) -> bool {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let forms = parsed.syntax.forms@;
        let definition = wiring.drivers.definitions@[prior].definition;
        let row = parsed.definitions@[definition as int];
        let start = row.expression.start as int;
        let end = row.expression.end as int;
        let local = (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        &&& no_operand(source, parsed, entry, definition, start, wiring, prior)
        &&& if end == start + 4 && forms[start] is List {
            ||| is_form_location(source, forms[start], location)
                && self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(None))
            ||| exists|call: TypedFuncCall|
                #[trigger] self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(Some(call)))
                && Self::unsupported_resolved_rhs(source, parsed, entry, definition, start, wiring, prior, call, location)
        } else {
            is_form_location(source, forms[start], location)
        }
    }

    /// 共通の構文と名前解決を使い、対応する右辺が未対応診断を持たないことを示す。
    proof fn unsupported_expression_excludes_rhs(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, prior: int,
        location: LocatedName, rhs: SingleBitRhs,
    )
        requires
            self.can_resolve(),
            self.unsupported_expression(file, entry, limit, wiring, prior, location),
            self.checked_rhs_matches(file, entry, limit, wiring, prior, rhs),
        ensures false,
    {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let forms = parsed.syntax.forms@;
        let definition = wiring.drivers.definitions@[prior].definition;
        let row = parsed.definitions@[definition as int];
        let start = row.expression.start as int;
        let local = (definition - parsed.entry_ranges@[entry as int].definitions.start) as usize;
        match rhs {
            SingleBitRhs::Operand(operand) => {
                operand_excludes_missing(source, parsed, entry, definition, start, wiring, prior, operand);
            },
            SingleBitRhs::Nor { left, right } => {
                let builtin = choose|call: TypedFuncCall| #[trigger] self.func_call_signature_evidence(
                    file, entry, local, 0, limit, Ok(Some(call)),
                ) && call.call.call.form == start && call.call.call.arguments == 2 && call.call.target is Nor;
                if self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(None)) {
                    self.resolved_nor_call_agrees(file, entry, local, 0, limit, builtin, None);
                } else {
                    let other = choose|call: TypedFuncCall|
                        #[trigger] self.func_call_signature_evidence(file, entry, local, 0, limit, Ok(Some(call)))
                        && Self::unsupported_resolved_rhs(source, parsed, entry, definition, start, wiring, prior, call, location);
                    self.resolved_nor_call_agrees(file, entry, local, 0, limit, builtin, Some(other));
                    if no_operand(source, parsed, entry, definition, start + 2, wiring, prior) {
                        operand_excludes_missing(source, parsed, entry, definition, start + 2, wiring, prior, left);
                    } else {
                        operand_excludes_missing(source, parsed, entry, definition, start + 3, wiring, prior, right);
                    }
                }
            },
        }
    }

    spec fn definition_supported(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, index: int,
    ) -> bool {
        exists|rhs: SingleBitRhs| #[trigger] self.checked_rhs_matches(file, entry, limit, wiring, index, rhs)
    }

    spec fn supported_definitions_before(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, stop: int,
    ) -> bool {
        &&& 0 <= stop <= wiring.drivers.definitions@.len()
        &&& forall|i: int| 0 <= i < stop
            ==> #[trigger] self.definition_supported(file, entry, limit, wiring, i)
    }

    /// 構築済みの定義列を、先行する定義が対応範囲に収まる証拠として使う。
    proof fn checked_definitions_are_supported(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring, definitions: Seq<SingleBitDefinition>,
    )
        requires self.checked_definitions_match(file, entry, limit, wiring, definitions),
        ensures self.supported_definitions_before(file, entry, limit, wiring, definitions.len() as int),
    {
        assert forall|i: int| 0 <= i < definitions.len()
            implies #[trigger] self.definition_supported(file, entry, limit, wiring, i) by {
            assert(self.checked_rhs_matches(file, entry, limit, wiring, i, definitions[i].rhs));
        };
    }

    spec fn subset_violation(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring,
        kind: UnsupportedSingleBitFunc, location: LocatedName, candidate: int,
    ) -> bool {
        let project = self.targets.project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.circuits_model()[file as int];
        let forms = parsed.syntax.forms@;
        let signature = &wiring.drivers.signature;
        &&& file < project.sources_model().len() && file < project.circuits_model().len()
        &&& entry < parsed.syntax.entries@.len() && entry < parsed.entry_ranges@.len()
        &&& location_in_source(location) && *location.source == *source
        &&& (kind != UnsupportedSingleBitFunc::OutputCount ==> signature.outputs@.len() == 1)
        &&& (kind == UnsupportedSingleBitFunc::PortType && candidate >= 0 ==>
            signature.outputs@[0].ty == ResolvedPortType::Bits(1)
                && one_bit_input_types_before(signature.inputs@, candidate))
        &&& ((kind == UnsupportedSingleBitFunc::DefinitionOutputCount || kind == UnsupportedSingleBitFunc::Expression) ==>
            signature.outputs@[0].ty == ResolvedPortType::Bits(1)
                && one_bit_input_types_before(signature.inputs@, signature.inputs@.len() as int)
                && self.supported_definitions_before(file, entry, limit, wiring, candidate))
        &&& match kind {
            UnsupportedSingleBitFunc::OutputCount => signature.outputs@.len() != 1
                && is_form_location(source, forms[parsed.syntax.entries@[entry as int].form as int], location),
            UnsupportedSingleBitFunc::PortType => {
                let port = if candidate == -1 { signature.outputs@[0] } else { signature.inputs@[candidate] };
                (candidate == -1 && signature.outputs@.len() == 1 || 0 <= candidate < signature.inputs@.len())
                    && port.ty != ResolvedPortType::Bits(1)
                    && is_form_location(source, forms[port.declared.site.name as int], location)
            },
            UnsupportedSingleBitFunc::DefinitionOutputCount => {
                let definition = wiring.drivers.definitions@[candidate].definition;
                let row = parsed.definitions@[definition as int];
                let (start, end) = definition_target_range(forms, row);
                &&& 0 <= candidate < wiring.drivers.definitions@.len() && definition < parsed.definitions@.len()
                &&& end - start != 1
                &&& is_form_location(source, forms[row.expression.start as int], location)
            },
            UnsupportedSingleBitFunc::Expression => {
                let definition = wiring.drivers.definitions@[candidate].definition;
                let row = parsed.definitions@[definition as int];
                let (start, end) = definition_target_range(forms, row);
                &&& 0 <= candidate < wiring.drivers.definitions@.len() && definition < parsed.definitions@.len()
                &&& end - start == 1
                &&& self.unsupported_expression(file, entry, limit, wiring, candidate, location)
            },
        }
    }

    /// 未対応の種別と位置を、検査順で最初に未対応となる候補に結び付ける。
    ///
    /// 出力本数、出力型、入力型の宣言順、本体の定義順で検査する。
    /// 各定義では左辺の結果数を調べてから右辺を検査する。
    pub closed spec fn single_bit_func_unsupported(
        &self, file: usize, entry: usize, limit: u64, kind: UnsupportedSingleBitFunc, location: LocatedName,
    ) -> bool {
        exists|wiring: FuncWiring, candidate: int| #![trigger
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring))),
            self.subset_violation(file, entry, limit, &wiring, kind, location, candidate)]
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(wiring)))
                && self.subset_violation(file, entry, limit, &wiring, kind, location, candidate)
                && ((kind == UnsupportedSingleBitFunc::DefinitionOutputCount || kind == UnsupportedSingleBitFunc::Expression)
                    ==> !self.definition_supported(file, entry, limit, &wiring, candidate))
    }

    proof fn unsupported_at(
        &self, file: usize, entry: usize, limit: u64, wiring: &FuncWiring,
        kind: UnsupportedSingleBitFunc, location: LocatedName, candidate: int,
    )
        requires
            self.can_resolve(),
            self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))),
            self.subset_violation(file, entry, limit, wiring, kind, location, candidate),
        ensures self.single_bit_func_unsupported(file, entry, limit, kind, location),
    {
        if (kind == UnsupportedSingleBitFunc::DefinitionOutputCount || kind == UnsupportedSingleBitFunc::Expression)
            && self.definition_supported(file, entry, limit, wiring, candidate) {
            let rhs = choose|rhs: SingleBitRhs| #[trigger] self.checked_rhs_matches(file, entry, limit, wiring, candidate, rhs);
            if kind == UnsupportedSingleBitFunc::Expression {
                self.unsupported_expression_excludes_rhs(file, entry, limit, wiring, candidate, location, rhs);
            }
            assert(false);
        }
    }

    /// 選択した宣言の型・結線を検査し、対応する1ビットの右辺を取り出す。
    ///
    /// 右辺は裸の信号、定数 `0`・`1`、またはそれらを直接引数に取る基底 NOR を扱う。
    /// 出力は1本とし、入力を直接公開する出力も受理する。
    ///
    /// # Errors
    ///
    /// 既存の型・結線検査の違反を先に返す。展開待ちや対応する形式に収まらない箇所にも元ソース位置を返す。
    pub fn check_single_bit_func(
        &self, file: usize, entry: usize, limit: u64,
    ) -> (result: Result<CheckedSingleBitFunc<'p, 'a>, SingleBitFuncError<'p, 'a>>)
        requires self.can_resolve(),
        ensures match result {
            Ok(checked) => single_bit_func_available(&checked) && self.single_bit_func_matches(file, entry, limit, &checked),
            Err(SingleBitFuncError::Check(error)) => self.func_signal_types_evidence(file, entry, limit, Err(error)),
            Err(SingleBitFuncError::Call(position, error)) =>
                position.file == file && position.entry == entry
                && self.func_call_signature_evidence(file, entry, position.definition, position.reference, limit, Err(error)),
            Err(SingleBitFuncError::Unsupported(kind, location)) =>
                self.single_bit_func_unsupported(file, entry, limit, kind, location),
            Err(SingleBitFuncError::NotFunc) => exists|typed: FuncSignalTypes|
                #[trigger] self.func_signal_types_evidence(file, entry, limit, Ok(typed))
                && typed.literals.wiring is NotFunc,
            Err(SingleBitFuncError::NeedsExpansion(location)) => exists|typed: FuncSignalTypes|
                #[trigger] self.func_signal_types_evidence(file, entry, limit, Ok(typed))
                && typed.literals.wiring == FuncWiringResult::NeedsExpansion(location),
        },
    {
        let typed = match self.check_func_signal_types(file, entry, limit) {
            Ok(typed) => typed,
            Err(error) => return Err(SingleBitFuncError::Check(error)),
        };
        let wiring = match &typed.literals.wiring {
            FuncWiringResult::Checked(wiring) => wiring,
            FuncWiringResult::NotFunc => return Err(SingleBitFuncError::NotFunc),
            FuncWiringResult::NeedsExpansion(location) =>
                return Err(SingleBitFuncError::NeedsExpansion(LocatedName {
                    source: location.source, span: location.span.start..location.span.end,
                })),
        };
        proof {
            self.checked_types_keep_wiring(file, entry, limit, typed, *wiring);
            self.checked_wiring_is_func(file, entry, limit, *wiring);
            self.targets.parsed_project_model();
        }
        let project = self.targets.project();
        let source = &project.sources()[file];
        let parsed = &project.circuits()[file];
        let forms = parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*source, *parsed);
            indexed_entry_evidence(source.text, forms@, parsed.syntax.entries@, entry as int);
            crate::syntax::circuit::build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let frame = &parsed.entry_ranges[entry];
        let declaration_index = parsed.syntax.entries[entry].form;
        let declaration = form_location(source, forms, declaration_index);
        let signature = &wiring.drivers.signature;
        if signature.outputs.len() != 1 {
            proof { self.unsupported_at(file, entry, limit, wiring, UnsupportedSingleBitFunc::OutputCount, declaration, -1); }
            return Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::OutputCount, declaration));
        }
        let output = &signature.outputs[0];
        let output_name = output.declared.site.name;
        let output_site = form_location(source, forms, output_name);
        if !matches!(output.ty, ResolvedPortType::Bits(1)) {
            proof { self.unsupported_at(file, entry, limit, wiring, UnsupportedSingleBitFunc::PortType, output_site, -1); }
            return Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::PortType, output_site));
        }
        let output_driver = wiring.drivers.outputs[0];

        let mut inputs = Vec::new();
        let mut i = 0;
        while i < signature.inputs.len()
            invariant
                *signature == wiring.drivers.signature,
                forms@ == parsed.syntax.forms@,
                form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
                declaration_index < forms@.len(),
                is_form_location(source, forms@[declaration_index as int], declaration),
                i == inputs@.len() <= signature.inputs@.len(),
                super::port_types::typed_name_sites(forms@, signature.inputs@),
                self.can_resolve(),
                self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))),
                file < project.circuits_model().len(), file < project.sources_model().len(),
                *project == self.targets.project_model(),
                *source == project.sources_model()[file as int], *parsed == project.circuits_model()[file as int],
                entry < parsed.entry_ranges@.len(), entry < parsed.syntax.entries@.len(),
                one_bit_inputs_match(source, forms@, signature.inputs@, inputs@),
                signature.outputs@.len() == 1,
                signature.outputs@[0].ty == ResolvedPortType::Bits(1),
            decreases signature.inputs@.len() - i,
        {
            let port = &signature.inputs[i];
            let name = port.declared.site.name;
            let location = form_location(source, forms, name);
            if !matches!(port.ty, ResolvedPortType::Bits(1)) {
                proof {
                    input_locations_preserve_types(source, forms@, signature.inputs@, inputs@);
                    self.unsupported_at(file, entry, limit, wiring, UnsupportedSingleBitFunc::PortType, location, i as int);
                }
                return Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::PortType, location));
            }
            let ghost previous = inputs@;
            inputs.push(location);
            proof { one_bit_inputs_append(source, forms@, signature.inputs@, previous, location); }
            i += 1;
        }

        proof { input_locations_preserve_types(source, forms@, signature.inputs@, inputs@); }
        let mut definitions = Vec::new();
        let mut i = 0;
        while i < wiring.drivers.definitions.len()
            invariant
                self.can_resolve(),
                self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))),
                file < project.circuits_model().len(), file < project.sources_model().len(),
                *project == self.targets.project_model(),
                *source == project.sources_model()[file as int], *parsed == project.circuits_model()[file as int],
                parsed_circuit_matches(*source, *parsed),
                forms@ == parsed.syntax.forms@, form_spans_valid(source.text, forms@, source.text.spec_bytes().len() as int),
                *frame == parsed.entry_ranges@[entry as int],
                entry < parsed.entry_ranges@.len(), entry < parsed.syntax.entries@.len(),
                i == definitions@.len() <= wiring.drivers.definitions@.len(),
                self.checked_definitions_match(file, entry, limit, wiring, definitions@),
                signature.outputs@.len() == 1,
                signature.outputs@[0].ty == ResolvedPortType::Bits(1),
                one_bit_input_types_before(signature.inputs@, signature.inputs@.len() as int),
                forall|j: int| 0 <= j < i ==>
                    single_bit_rhs_available((#[trigger] definitions@[j]).rhs, signature.inputs@.len(), j as nat),
                *signature == wiring.drivers.signature,
            decreases wiring.drivers.definitions@.len() - i,
        {
            proof { self.checked_wiring_is_func(file, entry, limit, *wiring); }
            let driver = &wiring.drivers.definitions[i];
            let definition = driver.definition;
            let row = &parsed.definitions[definition];
            let root = row.expression.start;
            let end = row.expression.end;
            proof {
                parsed_index_evidence(*source, *parsed);
                build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, definition as int);
            }
            let expression = form_location(source, forms, root);
            let targets = definition_target_atoms(forms, row);
            proof { self.checked_definitions_are_supported(file, entry, limit, wiring, definitions@); }
            if targets.end - targets.start != 1 {
                proof { self.unsupported_at(file, entry, limit, wiring, UnsupportedSingleBitFunc::DefinitionOutputCount, expression, i as int); }
                return Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::DefinitionOutputCount, expression));
            }
            let rhs = if let Some(operand) = self.read_single_bit_operand(file, entry, limit, source, parsed, root, wiring, definition, i) {
                SingleBitRhs::Operand(operand)
            } else if end - root == 4 && matches!(forms[root], Form::List { .. }) {
                let local = definition - frame.definitions.start;
                let result = self.resolve_func_call_signature(file, entry, local, 0, limit);
                let call = match result {
                    Ok(Some(call)) => call,
                    Ok(None) => {
                        proof { self.unsupported_at(file, entry, limit, wiring, UnsupportedSingleBitFunc::Expression, expression, i as int); }
                        return Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::Expression, expression));
                    },
                    Err(error) => return Err(SingleBitFuncError::Call(
                        DefinitionPosition { file, entry, definition: local, reference: 0 }, error)),
                };
                if call.call.call.form != root || call.call.call.arguments != 2 || !matches!(call.call.target, FuncCallTarget::Nor) {
                    proof { self.unsupported_at(file, entry, limit, wiring, UnsupportedSingleBitFunc::Expression, expression, i as int); }
                    return Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::Expression, expression));
                }
                let Some(left) = self.read_single_bit_operand(file, entry, limit, source, parsed, root + 2, wiring, definition, i) else {
                    let argument = form_location(source, forms, root + 2);
                    proof { self.unsupported_at(file, entry, limit, wiring, UnsupportedSingleBitFunc::Expression, argument, i as int); }
                    return Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::Expression, argument));
                };
                let Some(right) = self.read_single_bit_operand(file, entry, limit, source, parsed, root + 3, wiring, definition, i) else {
                    let argument = form_location(source, forms, root + 3);
                    proof { self.unsupported_at(file, entry, limit, wiring, UnsupportedSingleBitFunc::Expression, argument, i as int); }
                    return Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::Expression, argument));
                };
                SingleBitRhs::Nor { left, right }
            } else {
                proof { self.unsupported_at(file, entry, limit, wiring, UnsupportedSingleBitFunc::Expression, expression, i as int); }
                return Err(SingleBitFuncError::Unsupported(UnsupportedSingleBitFunc::Expression, expression));
            };
            assert(self.checked_rhs_matches(file, entry, limit, wiring, i as int, rhs));
            let name = LocatedName { source, span: driver.name.span.start..driver.name.span.end };
            let item = SingleBitDefinition { name, expression, rhs };
            let ghost previous = definitions@;
            definitions.push(item);
            assert forall|j: int| 0 <= j < definitions@.len() implies {
                let checked = #[trigger] definitions@[j];
                let driver = wiring.drivers.definitions@[j];
                let row = parsed.definitions@[driver.definition as int];
                &&& *checked.name.source == *source && checked.name.span == driver.name.span
                &&& is_form_location(source, forms@[row.expression.start as int], checked.expression)
                &&& self.checked_rhs_matches(file, entry, limit, wiring, j, checked.rhs)
                &&& single_bit_rhs_available(checked.rhs, signature.inputs@.len(), j as nat)
            } by {
                if j < i { assert(definitions@[j] == previous[j]); }
            };
            i += 1;
        }
        assert(self.checked_definitions_match(file, entry, limit, wiring, definitions@));
        assert(self.func_wiring_evidence(file, entry, limit, Ok(FuncWiringResult::Checked(*wiring))));
        let checked = CheckedSingleBitFunc { declaration, inputs, definitions, output: output_site, output_driver };
        assert(checked.inputs@.len() == wiring.drivers.signature.inputs@.len());
        assert(checked.definitions@.len() == wiring.drivers.definitions@.len());
        assert(is_form_location(source, parsed.syntax.forms@[parsed.syntax.entries@[entry as int].form as int], checked.declaration));
        assert(is_form_location(source, parsed.syntax.forms@[wiring.drivers.signature.outputs@[0].declared.site.name as int], checked.output));
        assert(wiring.drivers.signature.outputs@.len() == 1);
        assert(wiring.drivers.signature.outputs@[0].ty == ResolvedPortType::Bits(1));
        assert(checked.output_driver == wiring.drivers.outputs@[0]);
        assert(self.single_bit_func_matches(file, entry, limit, &checked));
        Ok(checked)
    }

    fn read_single_bit_operand(
        &self, _file: usize, entry: usize, _limit: u64, source: &'p ProjectSource<'a>,
        parsed: &NamedBuildCircuit<'a>, root: usize, wiring: &FuncWiring<'p, 'a>,
        definition: usize, prior: usize,
    ) -> (result: Option<SingleBitOperand>)
        requires
            self.can_resolve(),
            self.func_wiring_evidence(_file, entry, _limit, Ok(FuncWiringResult::Checked(*wiring))),
            _file < self.targets.project_model().sources_model().len(),
            _file < self.targets.project_model().circuits_model().len(),
            *source == self.targets.project_model().sources_model()[_file as int],
            *parsed == self.targets.project_model().circuits_model()[_file as int],
            parsed_circuit_matches(*source, *parsed),
            entry < parsed.syntax.entries@.len(), entry < parsed.entry_ranges@.len(),
            parsed.entry_ranges@[entry as int].definitions.start <= definition
                < parsed.entry_ranges@[entry as int].definitions.end <= parsed.definitions@.len(),
            root < parsed.syntax.forms@.len(),
        ensures match result {
            Some(operand) => operand_matches(source, parsed, entry, definition, root as int, wiring, prior as int, operand)
                && single_bit_operand_available(operand, wiring.drivers.signature.inputs@.len(), prior as nat),
            None => no_operand(source, parsed, entry, definition, root as int, wiring, prior as int),
        },
    {
        let forms = parsed.syntax.forms.as_slice();
        proof {
            parsed_index_evidence(*source, *parsed);
            indexed_entry_evidence(source.text, forms@, parsed.syntax.entries@, entry as int);
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, definition as int);
        }
        if matches!(forms[root], Form::Atom { kind: AtomKind::Natural, .. }) {
            let (word, _span) = read_indexed_atom(source.text, forms, root);
            proof {
                encode_utf8_decode_utf8(word@);
                encode_utf8_decode_utf8("0"@);
                encode_utf8_decode_utf8("1"@);
            }
            if word == "0" { Some(SingleBitOperand::Constant(false)) }
            else if word == "1" { Some(SingleBitOperand::Constant(true)) }
            else { None }
        } else if matches!(forms[root], Form::Atom { kind: AtomKind::Name, .. }) {
            let row = &parsed.definitions[definition];
            let frame = &parsed.entry_ranges[entry];
            let mut i = row.signals.start;
            while i < row.signals.end
                invariant
                    self.can_resolve(),
                    self.func_wiring_evidence(_file, entry, _limit, Ok(FuncWiringResult::Checked(*wiring))),
                    _file < self.targets.project_model().sources_model().len(),
                    _file < self.targets.project_model().circuits_model().len(),
                    *source == self.targets.project_model().sources_model()[_file as int],
                    *parsed == self.targets.project_model().circuits_model()[_file as int],
                    entry < parsed.syntax.entries@.len(), entry < parsed.entry_ranges@.len(),
                    *frame == parsed.entry_ranges@[entry as int],
                    frame.definitions.start <= definition < frame.definitions.end <= parsed.definitions@.len(),
                    *row == parsed.definitions@[definition as int],
                    row.signals.start <= i <= row.signals.end <= parsed.signals@.len(),
                    forall|signal: int| signal < i
                        ==> !#[trigger] prior_name_binding(parsed, entry, definition, root as int, wiring, prior as int, signal),

                    root < parsed.syntax.forms@.len(),
                    parsed.syntax.forms@[root as int] is Atom
                        && parsed.syntax.forms@[root as int]->Atom_kind is Name,
                decreases row.signals.end - i,
            {
                if parsed.signals[i] == root {
                    proof { self.checked_signal_driver(_file, entry, _limit, *wiring, definition, i); }
                    let pos = i - frame.signals.start;
                    let driver = wiring.signals[pos].driver;
                    if driver_available(driver, wiring.drivers.signature.inputs.len(), prior) {
                        assert(prior_name_binding(parsed, entry, definition, root as int, wiring, prior as int, i as int));
                        return Some(SingleBitOperand::Driver(driver));
                    }
                }
                assert(!prior_name_binding(parsed, entry, definition, root as int, wiring, prior as int, i as int));
                i += 1;
            }
            None
        } else {
            None
        }
    }
}

} // verus!
