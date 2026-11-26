//! 生成定義の信号名を、元文書の範囲と束縛範囲に結び付ける。

use super::LocalSignalKey;
use crate::ncg2m::call_evaluation::macro_syntax::{
    ArgumentSyntaxToken, CheckedTemplateDefinition, MacroSyntaxEvent, MacroSyntaxOrigin,
};
#[cfg(verus_only)]
use crate::ncg2m::call_evaluation::macro_syntax::{projected_form_has_origin, syntax_event_in_source};
use crate::project::{LocatedName, circuits::{form_location, read_indexed_atom}};
#[cfg(verus_only)]
use crate::project::{declarations::located_name_evidence, location_in_source};
#[cfg(verus_only)]
use crate::syntax::{circuit::generated_definition_sites, form_span};
use crate::syntax::circuit::GeneratedDefinition;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::encode_utf8};

verus! {

/// 生成定義から取る信号名の位置。
#[derive(Clone, Copy, Debug)]
pub enum GeneratedSignalPosition {
    /// 左辺の定義名を、先頭を0とする添字で選ぶ。
    Target(usize),
    /// 右辺の信号参照を、構文順の添字で選ぶ。
    Reference(usize),
}

/// 元の文書位置と、回路本体で束縛を探すためのキー。
#[derive(Debug)]
pub struct GeneratedSignalName<'p, 'a> {
    pub(super) key: LocalSignalKey<'a>,
    pub(super) site: LocatedName<'p, 'a>,
}

impl<'p, 'a> GeneratedSignalName<'p, 'a> {
    /// 通常の回路本体の名前と、展開が導入した名前を識別するキーを返す。
    pub fn key(&self) -> (key: LocalSignalKey<'a>)
        ensures key == self.key_model(),
    { self.key }

    /// 元の文書版と、元の名前を指す UTF-8 半開バイト範囲を借りる。
    pub fn location(&self) -> (site: &LocatedName<'p, 'a>)
        ensures *site == self.location_model(),
    { &self.site }

    /// 束縛の識別子と名前のバイト列を比較できるキーを表す。
    pub closed spec fn key_model(&self) -> LocalSignalKey<'a> { self.key }

    /// プロジェクトの元文書上で名前が現れた位置を表す。
    pub closed spec fn location_model(&self) -> LocatedName<'p, 'a> { self.site }
}

/// 一つの信号を参照し、一つの名前に接続する生成定義。
#[derive(Debug)]
pub struct GeneratedSignalAlias<'p, 'a> {
    pub(super) target: GeneratedSignalName<'p, 'a>,
    pub(super) reference: GeneratedSignalName<'p, 'a>,
}

impl<'p, 'a> GeneratedSignalAlias<'p, 'a> {
    /// 元文書の位置と束縛キーを持つ左辺を読む。
    pub fn target(&self) -> (target: &GeneratedSignalName<'p, 'a>)
        ensures *target == self.target_model(),
    { &self.target }

    /// 元文書の位置と束縛キーを持つ右辺を読む。
    pub fn reference(&self) -> (reference: &GeneratedSignalName<'p, 'a>)
        ensures *reference == self.reference_model(),
    { &self.reference }

    /// 単一の左辺を表す。
    pub closed spec fn target_model(&self) -> GeneratedSignalName<'p, 'a> { self.target }

    /// 右辺全体となる信号参照を表す。
    pub closed spec fn reference_model(&self) -> GeneratedSignalName<'p, 'a> { self.reference }
}

/// 一つの左辺と、信号名一つだけでできた右辺を持つ定義である。
pub open spec fn generated_signal_alias_shape(row: GeneratedDefinition) -> bool {
    &&& row.targets.start + 1 == row.targets.end && row.expression.start + 1 == row.expression.end
    &&& row.signals@.len() == 1 && row.signals@[0] == row.expression.start
}

fn is_generated_signal_alias(row: &GeneratedDefinition) -> (supported: bool)
    ensures supported == generated_signal_alias_shape(*row),
{
    row.targets.start.checked_add(1) == Some(row.targets.end)
        && row.expression.start.checked_add(1) == Some(row.expression.end)
        && row.signals.len() == 1 && row.signals[0] == row.expression.start
}

/// 選んだ信号名が投影済みの構文木のどのアトムに当たるかを表す。
pub open spec fn generated_signal_form(row: GeneratedDefinition, position: GeneratedSignalPosition) -> Option<usize> {
    match position {
        GeneratedSignalPosition::Target(i) => if i < row.targets.end - row.targets.start {
            Some((row.targets.start + i) as usize)
        } else { None },
        GeneratedSignalPosition::Reference(i) => if i < row.signals@.len() {
            Some(row.signals@[i as int])
        } else { None },
    }
}

/// 元の定義または実引数の構文から、信号の綴り・束縛範囲・診断位置を決める。
pub open spec fn generated_signal_origin_matches(event: MacroSyntaxEvent, name: &GeneratedSignalName) -> bool {
    let site = name.location_model();
    let key = name.key_model().model();
    &&& syntax_event_in_source(event) && event.token is Atom
    &&& site.source == event.origin.source_model() && location_in_source(site)
    &&& site.span == form_span(event.origin.forms_model()[event.token->Atom_0 as int])
    &&& key.1 == site.source.text_model().spec_bytes()[site.span.start as int..site.span.end as int]
    &&& match event.origin {
        MacroSyntaxOrigin::Template(call) => key.0 == Some((call.scope_model().file, call.site_model().span.start)),
        MacroSyntaxOrigin::Argument(_) => key.0.is_none(),
    }
}

/// 選んだ位置の名前が元の構文と同じで、導入した名前だけが展開位置を持つことを表す。
pub open spec fn generated_template_signal_matches(
    checked: &CheckedTemplateDefinition, position: GeneratedSignalPosition, result: Option<GeneratedSignalName>,
) -> bool {
    match generated_signal_form(checked.row_model(), position) {
        Some(form) => {
            &&& result matches Some(name)
            &&& form < checked.forms_model().len()
            &&& generated_signal_origin_matches(checked.origins_model()[form as int], &name)
        },
        None => result.is_none(),
    }
}

pub(super) fn generated_event_location<'p, 'a>(event: MacroSyntaxEvent<'_, 'p, 'a>) -> (site: LocatedName<'p, 'a>)
    requires syntax_event_in_source(event),
    ensures location_in_source(site), *site.source == *event.origin.source_model(),
        site.span == form_span(event.origin.forms_model()[match event.token {
            ArgumentSyntaxToken::Atom(at) | ArgumentSyntaxToken::Open(at) | ArgumentSyntaxToken::Close(at) => at as int,
        }]),
{
    let source = event.origin.source();
    let forms = event.origin.forms();
    let at = match event.token {
        ArgumentSyntaxToken::Atom(at) | ArgumentSyntaxToken::Open(at) | ArgumentSyntaxToken::Close(at) => at,
    };
    proof { source.text_model_is_text(); }
    form_location(source, forms, at)
}

fn read_generated_signal_origin<'b, 'p, 'a>(event: MacroSyntaxEvent<'b, 'p, 'a>)
    -> (name: GeneratedSignalName<'p, 'a>)
    requires syntax_event_in_source(event), event.token is Atom,
    ensures generated_signal_origin_matches(event, &name),
{
    let ArgumentSyntaxToken::Atom(at) = event.token else { unreachable!() };
    let source = event.origin.source();
    let (word, span) = read_indexed_atom(source.text(), event.origin.forms(), at);
    let key = match event.origin {
        MacroSyntaxOrigin::Template(call) => call.introduced_signal_key(word),
        MacroSyntaxOrigin::Argument(_) => LocalSignalKey::ordinary(word),
    };
    let site = LocatedName { source, span };
    proof {
        source.text_model_is_text();
        located_name_evidence(site);
    }
    GeneratedSignalName { key, site }
}

impl<'b, 'p, 'a> CheckedTemplateDefinition<'b, 'p, 'a> {
    /// 指定した左辺の名前または右辺の信号参照から、元文書上の名前と束縛キーを返す。
    ///
    /// 添字が範囲外なら `None` を返す。テンプレートのリテラルには展開位置を付ける。
    /// 挿入した構文の名前は、呼び出し元に直接書いた名前と同じキーになる。
    pub fn signal_name(&self, position: GeneratedSignalPosition) -> (result: Option<GeneratedSignalName<'p, 'a>>)
        ensures generated_template_signal_matches(self, position, result),
    {
        let row = self.row();
        let _text = self.text();
        let _forms = self.forms();
        let at = match position {
            GeneratedSignalPosition::Target(i) => {
                if i >= row.targets.end - row.targets.start { return None; }
                row.targets.start + i
            },
            GeneratedSignalPosition::Reference(i) => *row.signals.get(i)?,
        };
        let event = self.origin(at).unwrap();
        proof {
            assert(generated_definition_sites(_text, _forms@, *row));
            assert(_forms@[at as int] is Atom);
            assert(projected_form_has_origin(encode_utf8(self.text_model()), self.forms_model()[at as int], event));
        }
        Some(read_generated_signal_origin(event))
    }

    /// 単一の左辺と信号名一つの右辺を持つ生成定義を、結線検査に渡す。
    ///
    /// 関数呼び出し、リテラル、複数出力などはこの入口では `None` を返す。
    pub fn signal_alias(&self) -> (outcome: Option<GeneratedSignalAlias<'p, 'a>>)
        ensures
            outcome.is_some() == generated_signal_alias_shape(self.row_model()),
            outcome matches Some(alias) ==> {
                &&& generated_template_signal_matches(self, GeneratedSignalPosition::Target(0), Some(alias.target_model()))
                &&& generated_template_signal_matches(self, GeneratedSignalPosition::Reference(0), Some(alias.reference_model()))
            },
    {
        let row = self.row();
        if !is_generated_signal_alias(row) { return None; }
        let target = self.signal_name(GeneratedSignalPosition::Target(0)).unwrap();
        let reference = self.signal_name(GeneratedSignalPosition::Reference(0)).unwrap();
        Some(GeneratedSignalAlias { target, reference })
    }

}

} // verus!
