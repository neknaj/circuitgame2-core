//! 生成された信号接続を、通常のビット列関数の駆動元と幅に変換する。

use super::{BitFuncRhs, CheckedBitDefinition, CheckedBitFunc, OutputDriver, TypedRoutineSignature};
use crate::project::{
    GeneratedSignalAlias, LocalSignalKey, LocatedName, MacroPreparationError, MixedTypedSignatureError,
    MixedUseAliases, ProjectSource, ProjectSourceIndex, ResolvedPortType,
};
use crate::ncg2m::call_evaluation::macro_expansion::MacroExpansionErrorKind;
use crate::ncg2m::call_evaluation::macro_syntax::ArgumentSyntaxToken;
use super::super::function_drivers::typed_port_names;
use core::num::NonZeroUsize;
use crate::syntax::circuit::{GeneratedDefinitionError, Head};
#[cfg(verus_only)]
use crate::syntax::{Form, form_span};
#[cfg(verus_only)]
use super::super::{TypedPort, function_drivers::names_match_ports};
#[cfg(verus_only)]
use crate::project::{
    circuits::parsed_index_evidence, source_indexes::project_source_index_evidence, mixed_use_targets_match,
};
use super::super::{function_atoms::copy_location, local_signal_index::LocalSignalIndex};
#[cfg(verus_only)]
use super::{bit_definition_matches, bit_driver_width, checked_bit_func_available};
#[cfg(verus_only)]
use crate::project::location_in_source;
use crate::syntax::circuit::NameSite;
use alloc::vec::Vec;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

mod collection;
mod simple_rhs;
mod scoped_nor;
mod rows;
mod wiring;
mod mixed_body;
#[cfg(verus_only)]
pub use mixed_body::{
    expanded_bit_func_matches,
    expanded_function_diagnostic_call, expanded_function_diagnostic_related, expanded_function_diagnostic_row,
    expanded_function_diagnostic_source, expanded_function_wiring_diagnostic,
    expanded_function_wiring_diagnostic_row,
};
#[cfg(verus_only)]
pub use wiring::{expanded_definition_cause_location, expanded_definition_diagnostic_wraps, expanded_function_is_wiring_diagnostic};
pub use wiring::ExpandedFuncWiringError;
use collection::collect_generated_aliases;
#[cfg(verus_only)]
use collection::collected_aliases_from_function;
#[cfg(verus_only)]
pub use collection::{
    collected_aliases_match, collected_alias_prefix, collected_alias_step, function_generated_aliases_match,
    generated_alias_element_matches, generated_alias_elements_match,
};

verus! {

/// 生成した信号接続を既存のビット列関数に渡せなかった理由。
#[derive(Debug)]
pub enum GeneratedWiringError<'p, 'a> {
    /// 関数の出力がないか、本体に展開呼び出し以外の定義がある。
    UnsupportedBody,
    /// 既存の混在プロジェクトの署名検査による診断。
    Signature(MixedTypedSignatureError<'p, 'a>),
    /// マクロ名、引数の個数、またはマクロ本体の型を検査できなかった。
    Preparation(MacroPreparationError<'p, 'a>),
    /// 一回の呼び出しに割り当てた実行枠を使い切った。
    Fuel(LocatedName<'p, 'a>),
    /// マクロ評価で違反が起きた。
    Expansion {
        /// 展開呼び出しの元範囲。
        call: LocatedName<'p, 'a>,
        /// 評価に失敗したマクロ本体のファイルと文書版。
        definition: &'p ProjectSource<'a>,
        /// マクロ本体を参照する UTF-8 半開バイト範囲。
        related: Range<usize>,
        /// 評価を止めた理由。
        kind: MacroExpansionErrorKind,
    },
    /// 生成定義が通常の回路文法または生成時の制限に違反した。
    InvalidDefinition {
        /// 展開呼び出しの元範囲。
        call: LocatedName<'p, 'a>,
        /// 展開結果のリスト内の順序。
        element: usize,
        /// 関連するテンプレートまたは実引数の元範囲。
        related: Option<LocatedName<'p, 'a>>,
        /// 投影した構文上の違反。
        kind: GeneratedDefinitionError,
    },
    /// 生成した括弧が対応しないか、元構文の添字が使えない。
    InvalidProjection {
        /// 展開呼び出しの元範囲。
        call: LocatedName<'p, 'a>,
        /// 展開結果のリスト内の順序。
        element: usize,
        /// 対応するリスト全体の元範囲。
        related: Option<LocatedName<'p, 'a>>,
        /// 診断に関係するトークン。
        token: ArgumentSyntaxToken,
    },
    /// 現在の入口の対応範囲外の生成結果。展開呼び出しを指す。
    UnsupportedDefinition {
        /// 展開呼び出しの元範囲。
        call: LocatedName<'p, 'a>,
        /// 展開結果のリスト内の順序。
        element: usize,
    },
    /// 入出力の型がビット列ではない。型の元位置を指す。
    PortType(LocatedName<'p, 'a>),
    /// 未束縛または後続の名前を参照した。元の右辺の位置を指す。
    Unavailable(LocatedName<'p, 'a>),
    /// 同じ束縛を複数の入力または左辺で駆動した。後の宣言位置を指す。
    MultipleDrivers(LocatedName<'p, 'a>),
    /// 出力に対応する、呼び出し側の駆動元がない。
    MissingOutput(LocatedName<'p, 'a>),
    /// 出力の宣言幅と結線で伝わる幅が一致しない。
    OutputWidth {
        /// 元の出力の位置。
        site: LocatedName<'p, 'a>,
        /// 宣言の幅。
        expected: u64,
        /// 駆動元の幅。
        actual: u64,
    },
    /// 信号名索引の添字を割り当てられない。
    Capacity,
}

type BindingKey = (Option<(usize, usize)>, Seq<u8>);

spec fn ordinary_port_key(name: NameSite) -> BindingKey { (None, name.word.spec_bytes()) }

spec fn target_key(alias: GeneratedSignalAlias) -> BindingKey { alias.target_model().key_model().model() }

spec fn reference_key(alias: GeneratedSignalAlias) -> BindingKey { alias.reference_model().key_model().model() }

spec fn same_driver_key(
    names: Seq<NameSite>, aliases: Seq<GeneratedSignalAlias>, stop: int, key: BindingKey, driver: OutputDriver,
) -> bool {
    match driver {
        OutputDriver::Input(i) => i < names.len() && key == ordinary_port_key(names[i as int]),
        OutputDriver::Definition(i) => i < stop <= aliases.len() && key == target_key(aliases[i as int]),
    }
}

spec fn indexed_keys(
    names: Seq<NameSite>, aliases: Seq<GeneratedSignalAlias>, input_count: int, stop: int,
    bindings: Map<BindingKey, OutputDriver>,
) -> bool {
    &&& 0 <= input_count <= names.len() && 0 <= stop <= aliases.len()
    &&& forall|i: int| 0 <= i < input_count ==> {
        let key = ordinary_port_key(#[trigger] names[i]);
        bindings.contains_key(key) && bindings[key] == OutputDriver::Input(i as usize)
    }
    &&& forall|i: int| 0 <= i < stop ==> {
        let key = target_key(#[trigger] aliases[i]);
        bindings.contains_key(key) && bindings[key] == OutputDriver::Definition(i as usize)
    }
    &&& forall|key: BindingKey| #[trigger] bindings.contains_key(key) ==>
        same_driver_key(names.take(input_count), aliases, stop, key, bindings[key])
}

spec fn generated_definition_wired(
    inputs: Seq<u64>, input_names: Seq<NameSite>, aliases: Seq<GeneratedSignalAlias>,
    prefix: Seq<CheckedBitDefinition>, at: int, checked: CheckedBitDefinition,
) -> bool {
    &&& checked.expression == aliases[at].reference_model().location_model()
    &&& checked.rhs matches BitFuncRhs::Driver(driver)
    &&& same_driver_key(input_names, aliases, at, reference_key(aliases[at]), driver)
    &&& bit_definition_matches(inputs, prefix, checked)
}

spec fn generated_aliases_wired(
    inputs: Seq<u64>, names: Seq<NameSite>, aliases: Seq<GeneratedSignalAlias>, rows: Seq<CheckedBitDefinition>,
) -> bool {
    &&& rows.len() <= aliases.len()
    &&& forall|i: int| 0 <= i < rows.len() ==>
        generated_definition_wired(inputs, names, aliases, rows.take(i), i, #[trigger] rows[i])
}

fn generated_driver_width(inputs: &[u64], definitions: &[CheckedBitDefinition], driver: OutputDriver) -> (width: u64)
    requires bit_driver_width(inputs@, definitions@, driver).is_some(),
    ensures bit_driver_width(inputs@, definitions@, driver) == Some(width),
{
    match driver {
        OutputDriver::Input(index) => inputs[index],
        OutputDriver::Definition(index) => definitions[index].width,
    }
}

fn bit_port_widths<'p, 'a>(ports: &[super::super::TypedPort<'p, 'a>]) -> (out: Result<Vec<u64>, GeneratedWiringError<'p, 'a>>)
    ensures match out {
        Ok(widths) => widths@.len() == ports@.len()
            && (forall|i: int| 0 <= i < widths@.len()
                ==> (#[trigger] widths@[i]) > 0 && ports@[i].ty == ResolvedPortType::Bits(widths@[i])),
        Err(error) => error matches GeneratedWiringError::PortType(site)
            && (exists|i: int| 0 <= i < ports@.len() && (#[trigger] ports@[i]).annotation == site
                && !(ports@[i].ty matches ResolvedPortType::Bits(width) && width > 0)),
    },
{
    let mut widths: Vec<u64> = Vec::new();
    let mut i = 0;
    while i < ports.len()
        invariant i == widths@.len() <= ports@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] widths@[j]) > 0
                && ports@[j].ty == ResolvedPortType::Bits(widths@[j]),
        decreases ports@.len() - i,
    {
        let port = &ports[i];
        match port.ty {
            ResolvedPortType::Bits(width) if width > 0 => widths.push(width),
            _ => return Err(GeneratedWiringError::PortType(copy_location(&port.annotation))),
        }
        i += 1;
    }
    Ok(widths)
}

fn index_generated_inputs<'p, 'a>(signature: &TypedRoutineSignature<'p, 'a>, names: &[NameSite])
    -> (result: Result<LocalSignalIndex, GeneratedWiringError<'p, 'a>>)
    requires names@.len() == signature.inputs@.len(),
    ensures result matches Ok(index) ==> index.valid()
        && indexed_keys(names@, Seq::<GeneratedSignalAlias>::empty(), names@.len() as int, 0, index.keyed_bindings()),
        result matches Err(error) ==> error is MultipleDrivers || error is Capacity,
{
    let mut index = LocalSignalIndex::new();
    let mut i = 0;
    while i < names.len()
        invariant i <= names@.len() == signature.inputs@.len(), index.valid(),
            indexed_keys(names@, Seq::<GeneratedSignalAlias>::empty(), i as int, 0, index.keyed_bindings()),
        decreases names@.len() - i,
    {
        let key = LocalSignalKey::ordinary(names[i].word);
        let ghost before = index.keyed_bindings();
        match index.insert_key_if_absent(key, OutputDriver::Input(i)) {
            Some(None) => {},
            Some(Some(_)) => return Err(GeneratedWiringError::MultipleDrivers(copy_location(&signature.inputs[i].annotation))),
            None => return Err(GeneratedWiringError::Capacity),
        };
        proof {
            let k = key.model();
            assert(ordinary_port_key(names@[i as int]) == k);
            assert(!before.contains_key(k));
            assert forall|j: int| 0 <= j < i + 1 implies {
                let word = ordinary_port_key(#[trigger] names@[j]);
                index.keyed_bindings().contains_key(word) && index.keyed_bindings()[word] == OutputDriver::Input(j as usize)
            } by {
                if j < i {
                    assert(before.contains_key(ordinary_port_key(names@[j])));
                }
            };
        }
        i += 1;
    }
    Ok(index)
}

proof fn extend_generated_index(
    names: Seq<NameSite>, aliases: Seq<GeneratedSignalAlias>, at: usize,
    before: Map<BindingKey, OutputDriver>,
)
    requires at < aliases.len(), indexed_keys(names, aliases, names.len() as int, at as int, before),
        !before.contains_key(target_key(aliases[at as int])),
    ensures indexed_keys(names, aliases, names.len() as int, at + 1,
        before.insert(target_key(aliases[at as int]), OutputDriver::Definition(at))),
{
    let added = target_key(aliases[at as int]);
    let index = before.insert(added, OutputDriver::Definition(at));
    assert forall|j: int| 0 <= j < at + 1 implies {
        let key = target_key(#[trigger] aliases[j]);
        index.contains_key(key) && index[key] == OutputDriver::Definition(j as usize)
    } by {
        if j < at { assert(before.contains_key(target_key(aliases[j]))); }
    };
    assert forall|key: BindingKey| #[trigger] index.contains_key(key) implies
        same_driver_key(names.take(names.len() as int), aliases, at + 1, key, index[key]) by {
        if key != added {
            assert(same_driver_key(names.take(names.len() as int), aliases, at as int, key, before[key]));
        }
    };
}

proof fn extend_generated_wiring(
    inputs: Seq<u64>, names: Seq<NameSite>, aliases: Seq<GeneratedSignalAlias>,
    rows: Seq<CheckedBitDefinition>, next: CheckedBitDefinition,
)
    requires generated_aliases_wired(inputs, names, aliases, rows), rows.len() < aliases.len(),
        generated_definition_wired(inputs, names, aliases, rows, rows.len() as int, next),
    ensures generated_aliases_wired(inputs, names, aliases, rows.push(next)),
{
    let updated = rows.push(next);
    assert forall|i: int| 0 <= i < updated.len() implies
        generated_definition_wired(inputs, names, aliases, updated.take(i), i, #[trigger] updated[i]) by {
        if i < rows.len() {
            assert(updated[i] == rows[i]);
            assert(updated.take(i) =~= rows.take(i));
        } else {
            assert(updated.take(i) =~= rows);
        }
    };
}

fn bind_generated_aliases<'p, 'a>(
    index: &mut LocalSignalIndex, inputs: &[u64], names: &[NameSite], aliases: &[GeneratedSignalAlias<'p, 'a>],
) -> (result: Result<Vec<CheckedBitDefinition<'p, 'a>>, GeneratedWiringError<'p, 'a>>)
    requires
        old(index).valid(), inputs@.len() == names@.len(),
        indexed_keys(names@, Seq::<GeneratedSignalAlias>::empty(), names@.len() as int, 0, old(index).keyed_bindings()),
        forall|i: int| 0 <= i < inputs@.len() ==> #[trigger] inputs@[i] > 0,
        forall|i: int| 0 <= i < aliases@.len() ==> location_in_source((#[trigger] aliases@[i]).reference_model().location_model()),
    ensures
        final(index).valid(),
        result matches Ok(rows) ==> rows@.len() == aliases@.len()
            && generated_aliases_wired(inputs@, names@, aliases@, rows@)
            && indexed_keys(names@, aliases@, names@.len() as int, aliases@.len() as int, final(index).keyed_bindings()),
{
    let mut rows: Vec<CheckedBitDefinition<'p, 'a>> = Vec::new();
    let mut i = 0;
    while i < aliases.len()
        invariant
            i == rows@.len() <= aliases@.len(), index.valid(), inputs@.len() == names@.len(),
            forall|j: int| 0 <= j < inputs@.len() ==> #[trigger] inputs@[j] > 0,
            forall|j: int| 0 <= j < aliases@.len() ==> location_in_source((#[trigger] aliases@[j]).reference_model().location_model()),
            generated_aliases_wired(inputs@, names@, aliases@, rows@),
            indexed_keys(names@, aliases@, names@.len() as int, i as int, index.keyed_bindings()),
        decreases aliases@.len() - i,
    {
        let alias = &aliases[i];
        let reference = alias.reference().key();
        let Some(driver) = index.lookup_key(reference) else {
            return Err(GeneratedWiringError::Unavailable(copy_location(alias.reference().location())));
        };
        let _ = rows.len();
        let _ = inputs.len();
        proof {
            assert(index.keyed_bindings().contains_key(reference.model()));
            assert(same_driver_key(names@, aliases@, i as int, reference.model(), driver));
            if let OutputDriver::Definition(slot) = driver {
                assert(generated_definition_wired(inputs@, names@, aliases@, rows@.take(slot as int), slot as int, rows@[slot as int]));
            }
        }
        let width = generated_driver_width(inputs, rows.as_slice(), driver);
        let ghost before = index.keyed_bindings();
        let key = alias.target().key();
        match index.insert_key_if_absent(key, OutputDriver::Definition(i)) {
            Some(None) => {},
            Some(Some(_)) => return Err(GeneratedWiringError::MultipleDrivers(copy_location(alias.target().location()))),
            None => return Err(GeneratedWiringError::Capacity),
        };
        proof {
            assert(key.model() == target_key(aliases@[i as int]));
            extend_generated_index(names@, aliases@, i, before);
        }
        let checked = CheckedBitDefinition {
            expression: copy_location(alias.reference().location()), width, rhs: BitFuncRhs::Driver(driver), operands: Vec::new(),
        };
        proof {
            assert(generated_definition_wired(inputs@, names@, aliases@, rows@, i as int, checked));
            extend_generated_wiring(inputs@, names@, aliases@, rows@, checked);
        }
        rows.push(checked);
        i += 1;
    }
    Ok(rows)
}

spec fn generated_output_wired(
    inputs: Seq<u64>, input_names: Seq<NameSite>, outputs: Seq<u64>, output_names: Seq<NameSite>,
    aliases: Seq<GeneratedSignalAlias>, rows: Seq<CheckedBitDefinition>, port: int, driver: OutputDriver,
) -> bool {
    &&& same_driver_key(input_names, aliases, rows.len() as int, ordinary_port_key(output_names[port]), driver)
    &&& bit_driver_width(inputs, rows, driver) == Some(outputs[port])
}

fn bind_generated_outputs<'p, 'a>(
    index: &LocalSignalIndex, signature: &TypedRoutineSignature<'p, 'a>, inputs: &[u64], input_names: &[NameSite],
    widths: &[u64], names: &[NameSite], aliases: &[GeneratedSignalAlias<'p, 'a>], rows: &[CheckedBitDefinition<'p, 'a>],
) -> (result: Result<Vec<OutputDriver>, GeneratedWiringError<'p, 'a>>)
    requires
        index.valid(), inputs@.len() == input_names@.len(), widths@.len() == names@.len() == signature.outputs@.len(),
        rows@.len() == aliases@.len(),
        indexed_keys(input_names@, aliases@, inputs@.len() as int, rows@.len() as int, index.keyed_bindings()),
    ensures result matches Ok(drivers) ==> drivers@.len() == widths@.len()
        && forall|i: int| 0 <= i < drivers@.len() ==> generated_output_wired(
            inputs@, input_names@, widths@, names@, aliases@, rows@, i, #[trigger] drivers@[i]),
{
    let mut drivers: Vec<OutputDriver> = Vec::new();
    let mut i = 0;
    while i < names.len()
        invariant
            i == drivers@.len() <= widths@.len() == names@.len() == signature.outputs@.len(),
            index.valid(), inputs@.len() == input_names@.len(), rows@.len() == aliases@.len(),
            indexed_keys(input_names@, aliases@, inputs@.len() as int, rows@.len() as int, index.keyed_bindings()),
            forall|j: int| 0 <= j < i ==> generated_output_wired(
                inputs@, input_names@, widths@, names@, aliases@, rows@, j, #[trigger] drivers@[j]),
        decreases names@.len() - i,
    {
        let output = &signature.outputs[i];
        let key = LocalSignalKey::ordinary(names[i].word);
        let Some(driver) = index.lookup_key(key) else {
            return Err(GeneratedWiringError::MissingOutput(copy_location(&output.annotation)));
        };
        let _ = inputs.len();
        let _ = rows.len();
        proof {
            assert(key.model() == ordinary_port_key(names@[i as int]));
            assert(index.keyed_bindings().contains_key(key.model()));
            assert(same_driver_key(input_names@, aliases@, rows@.len() as int, key.model(), driver));
        }
        let actual = generated_driver_width(inputs, rows, driver);
        let expected = widths[i];
        if actual != expected {
            return Err(GeneratedWiringError::OutputWidth { site: copy_location(&output.annotation), expected, actual });
        }
        drivers.push(driver);
        i += 1;
    }
    Ok(drivers)
}

/// 展開後の右辺・出力が、同じ束縛キーの駆動元を選び、そのビット幅を受け継ぐことを表す。
pub closed spec fn generated_alias_function_wiring(
    input_names: Seq<NameSite>, output_names: Seq<NameSite>, aliases: Seq<GeneratedSignalAlias>, checked: &CheckedBitFunc,
) -> bool {
    &&& checked_bit_func_available(checked)
    &&& checked.input_widths@.len() == input_names.len()
    &&& checked.output_widths@.len() == output_names.len()
    &&& forall|i: int| 0 <= i < checked.input_widths@.len() ==>
        checked.signature_model().inputs@[i].ty == ResolvedPortType::Bits(#[trigger] checked.input_widths@[i])
    &&& forall|i: int| 0 <= i < checked.output_widths@.len() ==>
        checked.signature_model().outputs@[i].ty == ResolvedPortType::Bits(#[trigger] checked.output_widths@[i])
    &&& checked.definitions@.len() == aliases.len()
    &&& generated_aliases_wired(checked.input_widths@, input_names, aliases, checked.definitions@)
    &&& forall|i: int| 0 <= i < checked.output_drivers@.len() ==> generated_output_wired(
        checked.input_widths@, input_names, checked.output_widths@, output_names,
        aliases, checked.definitions@, i, #[trigger] checked.output_drivers@[i])
}

fn check_expanded_alias_wiring<'p, 'a>(
    signature: TypedRoutineSignature<'p, 'a>, input_names: &[NameSite], output_names: &[NameSite],
    aliases: &[GeneratedSignalAlias<'p, 'a>],
) -> (result: Result<CheckedBitFunc<'p, 'a>, GeneratedWiringError<'p, 'a>>)
    requires
        input_names@.len() == signature.inputs@.len(),
        0 < output_names@.len() == signature.outputs@.len(),
        forall|i: int| 0 <= i < aliases@.len() ==> location_in_source((#[trigger] aliases@[i]).reference_model().location_model()),
    ensures result matches Ok(checked) ==>
        checked.signature_model() == signature
        && generated_alias_function_wiring(input_names@, output_names@, aliases@, &checked),
{
    let input_widths = bit_port_widths(signature.inputs.as_slice())?;
    let output_widths = bit_port_widths(signature.outputs.as_slice())?;
    let mut index = index_generated_inputs(&signature, input_names)?;
    let definitions = bind_generated_aliases(&mut index, input_widths.as_slice(), input_names, aliases)?;
    let output_drivers = bind_generated_outputs(&index, &signature, input_widths.as_slice(), input_names,
        output_widths.as_slice(), output_names, aliases, definitions.as_slice())?;
    proof {
        reveal(checked_bit_func_available);
        assert forall|i: int| 0 <= i < definitions@.len() implies bit_definition_matches(
            input_widths@, definitions@.take(i), #[trigger] definitions@[i],
        ) by {
            assert(generated_definition_wired(input_widths@, input_names@, aliases@, definitions@.take(i), i, definitions@[i]));
        };
        assert forall|i: int| 0 <= i < output_drivers@.len() implies
            bit_driver_width(input_widths@, definitions@, #[trigger] output_drivers@[i])
                == Some(output_widths@[i]) by {
            assert(generated_output_wired(input_widths@, input_names@, output_widths@, output_names@,
                aliases@, definitions@, i, output_drivers@[i]));
        };
    }
    let checked = CheckedBitFunc { signature, input_widths, output_widths, definitions, output_drivers };
    Ok(checked)
}

/// 生成した信号名と通常のビット列関数の両方を保持する検査結果。
#[derive(Debug)]
pub struct CheckedGeneratedAliasFunc<'p, 'a> {
    checked: CheckedBitFunc<'p, 'a>,
    aliases: Vec<GeneratedSignalAlias<'p, 'a>>,
    inputs: Vec<NameSite<'a>>,
    outputs: Vec<NameSite<'a>>,
}

impl<'p, 'a> CheckedGeneratedAliasFunc<'p, 'a> {
    #[verifier::type_invariant]
    spec fn wiring_invariant(&self) -> bool {
        generated_alias_function_wiring(self.input_names_model(), self.output_names_model(), self.aliases_model(), &self.bit_func_model())
    }

    /// 既存のビット列関数の配線変換に渡せる結果を借りる。
    pub fn bit_func(&self) -> (checked: &CheckedBitFunc<'p, 'a>)
        ensures *checked == self.bit_func_model(),
            generated_alias_function_wiring(self.input_names_model(), self.output_names_model(), self.aliases_model(), checked),
    {
        proof { use_type_invariant(self); }
        &self.checked
    }

    /// 束縛キーと元の構文範囲を保持する生成定義を本体順に返す。
    pub fn aliases(&self) -> (aliases: &[GeneratedSignalAlias<'p, 'a>])
        ensures aliases@ == self.aliases_model(),
    { self.aliases.as_slice() }

    /// ビット列関数の検査結果を表す。
    pub closed spec fn bit_func_model(&self) -> CheckedBitFunc<'p, 'a> { self.checked }

    /// 生成された信号接続を、結線を検査した順に表す。
    pub closed spec fn aliases_model(&self) -> Seq<GeneratedSignalAlias<'p, 'a>> { self.aliases@ }

    /// 各生成定義の右辺が参照する、入力または先行定義を表す。
    pub closed spec fn alias_driver_model(&self, index: int) -> OutputDriver {
        self.checked.definitions@[index].rhs->Driver_0
    }

    /// 生成定義の右辺から受け継いだビット幅を表す。
    pub closed spec fn alias_width_model(&self, index: int) -> u64 {
        self.checked.definitions@[index].width
    }

    /// 関数の入力ポートのビット幅を宣言順に表す。
    pub closed spec fn input_widths_model(&self) -> Seq<u64> { self.checked.input_widths@ }

    /// 生成定義の右辺が、同じ束縛キーによる駆動元とそのビット幅に結び付くことを示す。
    pub proof fn alias_driver_evidence(&self, index: int)
        requires
            generated_alias_function_wiring(self.input_names_model(), self.output_names_model(), self.aliases_model(), &self.bit_func_model()),
            0 <= index < self.aliases_model().len(),
        ensures
            match self.alias_driver_model(index) {
                OutputDriver::Input(port) => port < self.input_names_model().len()
                    && self.aliases_model()[index].reference_model().key_model().model()
                        == (None, self.input_names_model()[port as int].word.spec_bytes())
                    && self.alias_width_model(index) == self.input_widths_model()[port as int],
                OutputDriver::Definition(prior) => prior < index
                    && self.aliases_model()[index].reference_model().key_model().model()
                        == self.aliases_model()[prior as int].target_model().key_model().model()
                    && self.alias_width_model(index) == self.alias_width_model(prior as int),
            },
    {
        assert(generated_definition_wired(self.checked.input_widths@, self.input_names_model(),
            self.aliases_model(), self.checked.definitions@.take(index), index, self.checked.definitions@[index]));
    }

    /// 呼び出し側の入力名を宣言順に表す。
    pub closed spec fn input_names_model(&self) -> Seq<NameSite<'a>> { self.inputs@ }

    /// 呼び出し側の出力名を宣言順に表す。
    pub closed spec fn output_names_model(&self) -> Seq<NameSite<'a>> { self.outputs@ }
}


/// 入出力名が、元の関数のポート添字と同じ文書上の名前を指すことを表す。
pub open spec fn generated_port_names_match(source: &ProjectSource, forms: Seq<Form>, ports: Seq<TypedPort>, names: Seq<NameSite>) -> bool {
    &&& names.len() == ports.len()
    &&& forall|i: int| 0 <= i < names.len() ==> {
        let name = #[trigger] names[i];
        let at = ports[i].declared.site.name as int;
        &&& 0 <= at < forms.len() && forms[at] is Atom
        &&& name.span == form_span(forms[at])
        &&& name.word.spec_bytes() == source.text_model().spec_bytes()[name.span.start as int..name.span.end as int]
    }
}

proof fn generated_port_names_from_signature(source: &ProjectSource, forms: Seq<Form>, ports: Seq<TypedPort>, names: Seq<NameSite>)
    requires names.len() == ports.len(), names_match_ports(source.text_model(), forms, ports, names),
        forall|i: int| 0 <= i < ports.len() ==> {
            let port = #[trigger] ports[i];
            port.declared.site.name < forms.len() && forms[port.declared.site.name as int] is Atom
        },
    ensures generated_port_names_match(source, forms, ports, names),
{}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// 展開で生成した信号接続だけを本体に持つ関数を、通常のビット列関数として検査する。
    ///
    /// 指定位置に `func` がなければ `Ok(None)`。各マクロ呼び出しに一回ずつ `fuel` の実行枠を渡す。
    /// 一つの左辺を持つテンプレートの信号接続を扱う。挿入した名前が呼び出し側の名前に接続し、
    /// テンプレートが導入した名前は同じ展開内の参照だけから見える。
    ///
    /// # Errors
    ///
    /// 署名、マクロ準備・評価、対応範囲外の生成定義、結線、出力幅の順に検査する。
    /// 評価が割り当てた枠内に終わらなければ、生成途中の関数を公開せず `Fuel` を返す。
    pub fn check_generated_alias_func(
        &self, file: usize, entry: usize, width_limit: u64, fuel: NonZeroUsize,
    ) -> (result: Result<Option<CheckedGeneratedAliasFunc<'p, 'a>>, GeneratedWiringError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures result matches Ok(Some(checked)) ==> {
            let project = self.targets_model().project_model();
            let signature = checked.bit_func_model().signature_model();
            let forms = project.indexes_model()[file as int]->Circuit_0.syntax.forms@;
            let source = &project.sources_model()[file as int];
            &&& generated_port_names_match(source, forms, signature.inputs@, checked.input_names_model())
            &&& generated_port_names_match(source, forms, signature.outputs@, checked.output_names_model())
            &&& generated_alias_function_wiring(
                checked.input_names_model(), checked.output_names_model(), checked.aliases_model(), &checked.bit_func_model())
            &&& self.mixed_typed_signature_matches(file, entry, width_limit, Ok(Some(checked.bit_func_model().signature_model())))
            &&& function_generated_aliases_match(self, file, entry, fuel@ as nat, checked.aliases_model())
        },
    {
        let project = self.targets().project();
        let Some(index) = project.indexes().get(file) else { return Ok(None); };
        let ProjectSourceIndex::Circuit(parsed) = index else { return Ok(None); };
        let Some(routine) = parsed.syntax.entries.get(entry) else { return Ok(None); };
        if !matches!(routine.head, Head::Func) { return Ok(None); }
        let source = &project.sources()[file];
        let signature = match self.resolve_mixed_routine_signature(file, entry, width_limit) {
            Ok(Some(signature)) => signature,
            Ok(None) => return Ok(None),
            Err(error) => return Err(GeneratedWiringError::Signature(error)),
        };
        proof {
            self.mixed_typed_signature_ports(file, entry, width_limit, signature);
            project_source_index_evidence(*source, *index);
            parsed_index_evidence(*source, *parsed);
            source.text_model_is_text();
        }
        let frame = &parsed.entry_ranges[entry];
        if frame.definitions.start != frame.definitions.end || signature.outputs.is_empty() {
            return Err(GeneratedWiringError::UnsupportedBody);
        }
        let text = source.text();
        let inputs = typed_port_names(text, parsed.syntax.forms.as_slice(), signature.inputs.as_slice());
        let outputs = typed_port_names(text, parsed.syntax.forms.as_slice(), signature.outputs.as_slice());
        proof {
            generated_port_names_from_signature(source, parsed.syntax.forms@, signature.inputs@, inputs@);
            generated_port_names_from_signature(source, parsed.syntax.forms@, signature.outputs@, outputs@);
        }
        let Some(calls) = self.macro_calls(file, entry) else { return Ok(None); };
        let ghost start = calls;
        let aliases = collect_generated_aliases(calls, fuel)?;
        proof { collected_aliases_from_function(self, file, entry, fuel@ as nat, start, aliases@); }
        let checked = check_expanded_alias_wiring(signature, inputs.as_slice(), outputs.as_slice(), aliases.as_slice())?;
        Ok(Some(CheckedGeneratedAliasFunc { checked, aliases, inputs, outputs }))
    }
}

} // verus!
