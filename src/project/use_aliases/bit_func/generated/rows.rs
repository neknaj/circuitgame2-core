//! 通常の定義と生成した定義を、同じ信号参照・定数・基底 NOR の表現へ移す。

use super::{
    scoped_nor::{CalleeScope, NorScopeError, check_scoped_nor},
    simple_rhs::{SimpleOperandSyntax, SimpleRhsSyntax, read_simple_rhs},
};
use crate::ncg2m::call_evaluation::macro_syntax::CheckedTemplateDefinition;
use crate::project::{
    GeneratedSignalName, GeneratedSignalPosition, LocatedName, MixedUseAliases, ProjectSource,
    circuits::{form_location, read_indexed_atom}, use_aliases::generated_signals::{generated_event_location, ordinary_signal_name},
};
use crate::syntax::{Form, circuit::{BuildDefinition, definition_target_atoms}};
use vstd::prelude::*;
#[cfg(verus_only)]
use super::{
    scoped_nor::{event_callee_scope, nor_scope_error_location, scoped_nor_matches},
    simple_rhs::{simple_operand_uses_atom, simple_rhs, simple_rhs_sites},
};
#[cfg(verus_only)]
use crate::project::{generated_signal_origin_matches, generated_template_signal_matches, location_in_source};
#[cfg(verus_only)]
use crate::syntax::{
    circuit::{definition_target_range, definition_targets_match, generated_definition_sites}, form_span, form_spans_valid,
};
#[cfg(verus_only)]
use crate::ncg2m::call_evaluation::macro_syntax::{projected_form_has_origin, syntax_event_in_source};
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::encode_utf8};

verus! {

#[derive(Debug)]
pub(super) enum ScopedOperand<'p, 'a> {
    Signal(GeneratedSignalName<'p, 'a>),
    Bit { value: bool, site: LocatedName<'p, 'a> },
}

#[derive(Debug)]
pub(super) enum ScopedRhs<'p, 'a> {
    Leaf(ScopedOperand<'p, 'a>),
    Nor { callee: LocatedName<'p, 'a>, left: ScopedOperand<'p, 'a>, right: ScopedOperand<'p, 'a> },
}

#[derive(Debug)]
pub(super) struct ScopedDefinition<'p, 'a> {
    pub(super) call: Option<LocatedName<'p, 'a>>,
    pub(super) target: GeneratedSignalName<'p, 'a>,
    pub(super) expression: LocatedName<'p, 'a>,
    pub(super) rhs: ScopedRhs<'p, 'a>,
}

pub(super) open spec fn operand_location<'p, 'a>(operand: ScopedOperand<'p, 'a>) -> LocatedName<'p, 'a> {
    match operand {
        ScopedOperand::Signal(name) => name.location_model(),
        ScopedOperand::Bit { site, .. } => site,
    }
}

pub(super) open spec fn scoped_definition_locations(definition: ScopedDefinition) -> bool {
    &&& (definition.call matches Some(call) ==> location_in_source(call))
    &&& location_in_source(definition.target.location_model())
    &&& location_in_source(definition.expression)
    &&& match definition.rhs {
        ScopedRhs::Leaf(operand) => location_in_source(operand_location(operand)),
        ScopedRhs::Nor { callee, left, right } => location_in_source(callee)
            && location_in_source(operand_location(left)) && location_in_source(operand_location(right)),
    }
}

spec fn ordinary_site(source: &ProjectSource, forms: Seq<Form>, at: usize, site: LocatedName) -> bool {
    &&& location_in_source(site) && *site.source == *source
    &&& at < forms.len() && site.span == form_span(forms[at as int])
}

spec fn template_site(checked: &CheckedTemplateDefinition, at: usize, site: LocatedName) -> bool {
    let event = checked.origins_model()[at as int];
    let original = match event.token {
        crate::ncg2m::call_evaluation::macro_syntax::ArgumentSyntaxToken::Atom(at)
        | crate::ncg2m::call_evaluation::macro_syntax::ArgumentSyntaxToken::Open(at)
        | crate::ncg2m::call_evaluation::macro_syntax::ArgumentSyntaxToken::Close(at) => at,
    };
    ordinary_site(event.origin.source_model(), event.origin.forms_model(), original, site)
        && syntax_event_in_source(event)
}

spec fn ordinary_operand_matches(
    source: &ProjectSource, forms: Seq<Form>, syntax: SimpleOperandSyntax, operand: ScopedOperand,
) -> bool {
    match (syntax, operand) {
        (SimpleOperandSyntax::Signal(at), ScopedOperand::Signal(name)) => {
            let site = name.location_model();
            &&& ordinary_site(source, forms, at, site)
            &&& name.key_model().model() == (None, source.text_model().spec_bytes()[site.span.start as int..site.span.end as int])
        },
        (SimpleOperandSyntax::Bit { at, value }, ScopedOperand::Bit { site, value: got }) =>
            value == got && ordinary_site(source, forms, at, site),
        _ => false,
    }
}

spec fn template_operand_matches(
    checked: &CheckedTemplateDefinition, syntax: SimpleOperandSyntax, operand: ScopedOperand,
) -> bool {
    match (syntax, operand) {
        (SimpleOperandSyntax::Signal(at), ScopedOperand::Signal(name)) =>
            generated_signal_origin_matches(checked.origins_model()[at as int], &name),
        (SimpleOperandSyntax::Bit { at, value }, ScopedOperand::Bit { site, value: got }) =>
            value == got && template_site(checked, at, site),
        _ => false,
    }
}

fn read_template_site<'p, 'a>(checked: &CheckedTemplateDefinition<'_, 'p, 'a>, at: usize)
    -> (site: LocatedName<'p, 'a>)
    requires at < checked.forms_model().len(),
    ensures template_site(checked, at, site),
{
    let event = checked.origin(at).unwrap();
    assert(projected_form_has_origin(encode_utf8(checked.text_model()), checked.forms_model()[at as int], event));
    generated_event_location(event)
}

fn read_ordinary_operand<'p, 'a>(source: &'p ProjectSource<'a>, forms: &[Form], syntax: SimpleOperandSyntax)
    -> (operand: ScopedOperand<'p, 'a>)
    requires simple_operand_uses_atom(forms@, syntax),
        form_spans_valid(source.text_model(), forms@, source.text_model().spec_bytes().len() as int),
    ensures ordinary_operand_matches(source, forms@, syntax, operand), location_in_source(operand_location(operand)),
{
    match syntax {
        SimpleOperandSyntax::Signal(at) => ScopedOperand::Signal(ordinary_signal_name(source, forms, at)),
        SimpleOperandSyntax::Bit { at, value } => {
            proof { source.text_model_is_text(); }
            ScopedOperand::Bit { value, site: form_location(source, forms, at) }
        },
    }
}

fn read_template_operand<'p, 'a>(checked: &CheckedTemplateDefinition<'_, 'p, 'a>, syntax: SimpleOperandSyntax)
    -> (operand: ScopedOperand<'p, 'a>)
    requires simple_operand_uses_atom(checked.forms_model(), syntax),
    ensures template_operand_matches(checked, syntax, operand), location_in_source(operand_location(operand)),
{
    match syntax {
        SimpleOperandSyntax::Signal(at) => ScopedOperand::Signal(checked.scoped_signal_at(at)),
        SimpleOperandSyntax::Bit { at, value } => ScopedOperand::Bit { value, site: read_template_site(checked, at) },
    }
}

spec fn ordinary_rhs_matches(
    aliases: &MixedUseAliases, at: CalleeScope, source: &ProjectSource, forms: Seq<Form>, syntax: SimpleRhsSyntax, rhs: ScopedRhs,
) -> bool {
    match (syntax, rhs) {
        (SimpleRhsSyntax::Leaf(syntax), ScopedRhs::Leaf(operand)) =>
            ordinary_operand_matches(source, forms, syntax, operand),
        (SimpleRhsSyntax::Nor { callee, left, right }, ScopedRhs::Nor { callee: site, left: lhs, right: rhs }) =>
            ordinary_site(source, forms, callee, site)
                && scoped_nor_matches(aliases, at, site, Ok(()))
                && ordinary_operand_matches(source, forms, left, lhs) && ordinary_operand_matches(source, forms, right, rhs),
        _ => false,
    }
}

spec fn template_rhs_matches(
    aliases: &MixedUseAliases, checked: &CheckedTemplateDefinition, syntax: SimpleRhsSyntax, rhs: ScopedRhs,
) -> bool {
    match (syntax, rhs) {
        (SimpleRhsSyntax::Leaf(syntax), ScopedRhs::Leaf(operand)) => template_operand_matches(checked, syntax, operand),
        (SimpleRhsSyntax::Nor { callee, left, right }, ScopedRhs::Nor { callee: site, left: lhs, right: rhs }) =>
            template_site(checked, callee, site)
                && scoped_nor_matches(aliases, event_callee_scope(checked.origins_model()[callee as int].origin), site, Ok(()))
                && template_operand_matches(checked, left, lhs) && template_operand_matches(checked, right, rhs),
        _ => false,
    }
}

pub(super) closed spec fn ordinary_simple_definition(
    aliases: &MixedUseAliases, at: CalleeScope, source: &ProjectSource, forms: Seq<Form>,
    row: BuildDefinition, definition: ScopedDefinition,
) -> bool {
    let (target, end) = definition_target_range(forms, row);
    let site = definition.target.location_model();
    &&& definition.call.is_none()
    &&& target + 1 == end
    &&& ordinary_site(source, forms, target as usize, site)
    &&& definition.target.key_model().model() == (None, source.text_model().spec_bytes()[site.span.start as int..site.span.end as int])
    &&& ordinary_site(source, forms, row.expression.start, definition.expression)
    &&& simple_rhs(source.text_model(), forms, row.expression) matches Some(syntax)
    &&& ordinary_rhs_matches(aliases, at, source, forms, syntax, definition.rhs)
}

pub(super) closed spec fn template_simple_definition(
    aliases: &MixedUseAliases, checked: &CheckedTemplateDefinition, definition: ScopedDefinition,
) -> bool {
    let row = checked.row_model();
    &&& row.targets.start + 1 == row.targets.end
    &&& generated_template_signal_matches(checked, GeneratedSignalPosition::Target(0), Some(definition.target))
    &&& template_site(checked, row.expression.start, definition.expression)
    &&& simple_rhs_with_template_text(checked, row.expression, aliases, definition.rhs)
}

spec fn simple_rhs_with_template_text(
    checked: &CheckedTemplateDefinition, range: core::ops::Range<usize>, aliases: &MixedUseAliases, rhs: ScopedRhs,
) -> bool {
    exists|text: &str| text@ == checked.text_model()
        && match #[trigger] simple_rhs(text, checked.forms_model(), range) {
            Some(syntax) => template_rhs_matches(aliases, checked, syntax, rhs),
            None => false,
        }
}

pub(super) fn read_ordinary_definition<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, at: CalleeScope, source: &'p ProjectSource<'a>, forms: &[Form], row: &BuildDefinition,
) -> (result: Result<Option<ScopedDefinition<'p, 'a>>, NorScopeError<'p, 'a>>)
    requires definition_targets_match(forms@, *row),
        form_spans_valid(source.text_model(), forms@, source.text_model().spec_bytes().len() as int),
    ensures result matches Ok(Some(definition)) ==> scoped_definition_locations(definition)
        && definition.call.is_none() && ordinary_simple_definition(aliases, at, source, forms@, *row, definition),
{
    let targets = definition_target_atoms(forms, row);
    if targets.end - targets.start != 1 { return Ok(None); }
    let text = source.text();
    let range = row.expression.start..row.expression.end;
    let Some(syntax) = read_simple_rhs(text, forms, range) else { return Ok(None); };
    proof {
        source.text_model_is_text();
        simple_rhs_sites(text, forms@, row.expression, syntax);
    }
    let target = ordinary_signal_name(source, forms, targets.start);
    let expression = form_location(source, forms, row.expression.start);
    let rhs = match syntax {
        SimpleRhsSyntax::Leaf(operand) => ScopedRhs::Leaf(read_ordinary_operand(source, forms, operand)),
        SimpleRhsSyntax::Nor { callee, left, right } => {
            let site = form_location(source, forms, callee);
            let (word, _) = read_indexed_atom(text, forms, callee);
            check_scoped_nor(aliases, at, word, crate::project::use_aliases::function_atoms::copy_location(&site))?;
            ScopedRhs::Nor { callee: site, left: read_ordinary_operand(source, forms, left), right: read_ordinary_operand(source, forms, right) }
        },
    };
    Ok(Some(ScopedDefinition { call: None, target, expression, rhs }))
}

pub(super) fn read_template_definition<'p, 'a>(
    aliases: &MixedUseAliases<'_, 'p, 'a>, checked: &CheckedTemplateDefinition<'_, 'p, 'a>, call: &LocatedName<'p, 'a>,
) -> (result: Result<Option<ScopedDefinition<'p, 'a>>, NorScopeError<'p, 'a>>)
    requires location_in_source(*call),
    ensures
        result matches Ok(Some(definition)) ==> scoped_definition_locations(definition)
            && definition.call == Some(*call) && template_simple_definition(aliases, checked, definition),
        result matches Err(error) ==> location_in_source(nor_scope_error_location(error)),
{
    let row = checked.row();
    let forms = checked.forms();
    let text = checked.text();
    let lo = row.targets.start;
    if row.targets.end - lo != 1 { return Ok(None); }
    let range = row.expression.start..row.expression.end;
    let Some(syntax) = read_simple_rhs(text, forms, range) else { return Ok(None); };
    proof { simple_rhs_sites(text, forms@, row.expression, syntax); }
    let target = checked.signal_name(GeneratedSignalPosition::Target(0)).unwrap();
    let expression = read_template_site(checked, row.expression.start);
    let rhs = match syntax {
        SimpleRhsSyntax::Leaf(operand) => ScopedRhs::Leaf(read_template_operand(checked, operand)),
        SimpleRhsSyntax::Nor { callee, left, right } => {
            let event = checked.origin(callee).unwrap();
            let scope = CalleeScope::from_event(event.origin);
            let site = read_template_site(checked, callee);
            let (word, _) = read_indexed_atom(text, forms, callee);
            check_scoped_nor(aliases, scope, word, crate::project::use_aliases::function_atoms::copy_location(&site))?;
            ScopedRhs::Nor { callee: site, left: read_template_operand(checked, left), right: read_template_operand(checked, right) }
        },
    };
    assert(simple_rhs_with_template_text(checked, row.expression, aliases, rhs));
    Ok(Some(ScopedDefinition { call: Some(crate::project::use_aliases::function_atoms::copy_location(call)), target, expression, rhs }))
}

} // verus!
