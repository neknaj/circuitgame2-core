//! 普通の定義と展開で得た定義を、元の関数本体順で結線検査に渡す。

use super::{
    GeneratedWiringError,
    rows::{ScopedDefinition, read_ordinary_definition, read_template_definition},
    scoped_nor::{CalleeScope, NorScopeError},
    wiring::{ExpandedFuncWiringError, check_scoped_wiring, with_generated_call},
};
use super::super::CheckedBitFunc;
use crate::ncg2m::call_evaluation::{
    macro_expansion::{MacroExpandedBody, MacroExpansionSlice},
    macro_syntax::TemplateDefinitionError,
};
use crate::project::{
    LocatedName, MacroCalls, MixedUseAliases, ProjectSource, ProjectSourceIndex,
    circuits::form_location, use_aliases::{function_drivers::typed_port_names, generated_signals::generated_event_location},
    validate_mixed_circuit_basis,
};
use crate::syntax::circuit::{Head, NamedBuildCircuit};
use alloc::vec::Vec;
use core::num::NonZeroUsize;
use vstd::prelude::*;
#[cfg(verus_only)]
use super::{
    generated_port_names_from_signature, generated_port_names_match, scoped_nor::nor_scope_error_location,
    wiring::{
        expanded_bit_func_wiring, expanded_definition_cause_location, expanded_function_is_wiring_diagnostic,
        row_diagnostic_at, scoped_diagnostic_cause_location, scoped_wiring_diagnostic_source,
    },
    rows::{ordinary_simple_definition, scoped_definition_locations, template_simple_definition},
};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    NameSite, RoutineExpansionSite, expansion_body_region_matches, routine_expansion_site_at, routine_expansion_sites_match,
};
#[cfg(verus_only)]
use crate::ncg2m::call_evaluation::macro_binding::BoundMacroCall;
#[cfg(verus_only)]
use crate::ncg2m::call_evaluation::macro_expansion::{MacroExpansion, MacroExpansionError, macro_expansion_slice_matches};
#[cfg(verus_only)]
use crate::ncg2m::expression_types::checked_macro_body_layout;
#[cfg(verus_only)]
use super::super::checked_bit_func_available;
#[cfg(verus_only)]
use crate::ncg2m::call_evaluation::macro_syntax::{CheckedTemplateDefinition, template_definition_check_matches};
#[cfg(verus_only)]
use crate::project::{MacroPreparationError, circuits::parsed_index_evidence, declarations::located_name_evidence, location_in_source,
    macro_call_spans_in_source, source_indexes::project_source_index_evidence, mixed_use_targets_match};
#[cfg(verus_only)]
use crate::syntax::{
    circuit::{build_definition_scope_evidence, build_index_matches}, form_span, form_spans_valid,
};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

struct OrdinaryBody<'s, 't, 'p, 'a> {
    aliases: &'s MixedUseAliases<'t, 'p, 'a>,
    file: usize,
    entry: usize,
    source: &'p ProjectSource<'a>,
    parsed: &'p NamedBuildCircuit<'a>,
}

impl OrdinaryBody<'_, '_, '_, '_> {
    spec fn valid(&self) -> bool {
        &&& self.entry < self.parsed.syntax.entries@.len()
        &&& self.entry < self.parsed.entry_ranges@.len()
        &&& self.range().start <= self.range().end <= self.parsed.definitions@.len()
        &&& build_index_matches(self.source.text_model(), self.parsed.build_model())
        &&& form_spans_valid(self.source.text_model(), self.parsed.syntax.forms@,
            self.source.text_model().spec_bytes().len() as int)
    }

    spec fn range(&self) -> core::ops::Range<usize> { self.parsed.entry_ranges@[self.entry as int].definitions }
}


#[verifier::opaque]
spec fn call_in_body(body: &OrdinaryBody, call: LocatedName) -> bool {
    &&& *call.source == *body.source && location_in_source(call)
    &&& exists|first: usize, last: usize, site: RoutineExpansionSite| {
        &&& expansion_body_region_matches(body.source.text_model(), &body.parsed.syntax, body.entry as int, Some((first, last)))
        &&& #[trigger] routine_expansion_site_at(
            body.source.text_model(), body.parsed.syntax.forms@, first as int, last as int, site,
        )
        &&& call.span == site.span
    }
}

spec fn definition_in_body(body: &OrdinaryBody, definition: ScopedDefinition) -> bool {
    &&& scoped_definition_locations(definition)
    &&& (definition.call matches Some(call) ==> call_in_body(body, call))
}

spec fn locations_valid(body: &OrdinaryBody, rows: Seq<ScopedDefinition>) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> definition_in_body(body, #[trigger] rows[i])
}

proof fn push_keeps_locations(body: &OrdinaryBody, rows: Seq<ScopedDefinition>, row: ScopedDefinition)
    requires locations_valid(body, rows), definition_in_body(body, row),
    ensures locations_valid(body, rows.push(row)),
{
    let next = rows.push(row);
    assert forall|i: int| 0 <= i < next.len() implies definition_in_body(body, #[trigger] next[i]) by {
        if i < rows.len() { assert(next[i] == rows[i]); }
    };
}

/// 展開に由来する診断から呼び出しの範囲と文書版を取り出す。
pub open spec fn expanded_function_diagnostic_call<'p, 'a>(
    error: ExpandedFuncWiringError<'p, 'a>,
) -> Option<LocatedName<'p, 'a>> {
    match error {
        ExpandedFuncWiringError::Generated { call, .. }
        | ExpandedFuncWiringError::Base(GeneratedWiringError::Fuel(call))
        | ExpandedFuncWiringError::Base(GeneratedWiringError::Expansion { call, .. })
        | ExpandedFuncWiringError::Base(GeneratedWiringError::InvalidDefinition { call, .. })
        | ExpandedFuncWiringError::Base(GeneratedWiringError::InvalidProjection { call, .. })
        | ExpandedFuncWiringError::Base(GeneratedWiringError::UnsupportedDefinition { call, .. }) => Some(call),
        ExpandedFuncWiringError::Base(GeneratedWiringError::Preparation(error)) =>
            Some(LocatedName { source: error.source, span: error.site.span }),
        _ => None,
    }
}

/// 展開後の結線、構文投影、評価で特定できた原因の元範囲を取り出す。
pub open spec fn expanded_function_diagnostic_related<'p, 'a>(
    error: ExpandedFuncWiringError<'p, 'a>,
) -> Option<LocatedName<'p, 'a>> {
    match error {
        ExpandedFuncWiringError::Generated { cause, .. } => expanded_definition_cause_location(*cause),
        ExpandedFuncWiringError::Base(GeneratedWiringError::InvalidDefinition { related, .. })
        | ExpandedFuncWiringError::Base(GeneratedWiringError::InvalidProjection { related, .. }) => related,
        ExpandedFuncWiringError::Base(GeneratedWiringError::Expansion { definition, related, .. }) =>
            Some(LocatedName { source: definition, span: related }),
        _ => None,
    }
}

spec fn diagnostic_in_body(body: &OrdinaryBody, error: ExpandedFuncWiringError) -> bool {
    &&& (expanded_function_diagnostic_call(error) matches Some(call) ==> call_in_body(body, call))
    &&& (error is Generated ==> expanded_function_diagnostic_related(error).is_some())
    &&& (expanded_function_diagnostic_related(error) matches Some(site) ==> location_in_source(site))
}

spec fn macro_call_location<'p, 'a>(bound: &BoundMacroCall<'p, 'a>) -> LocatedName<'p, 'a> {
    LocatedName { source: bound.scope_model().source, span: bound.site_model().span }
}

fn map_nor_scope_error<'p, 'a>(error: NorScopeError<'p, 'a>) -> (out: ExpandedFuncWiringError<'p, 'a>)
    ensures
        !(out is Generated), expanded_definition_cause_location(out) == Some(nor_scope_error_location(error)),
        out is NorScope || out is NorName || out is NorResolvesToFunction,
{
    match error {
        NorScopeError::MissingScope(callee) => ExpandedFuncWiringError::NorScope(callee),
        NorScopeError::Function { callee, declaration } => ExpandedFuncWiringError::NorResolvesToFunction { callee, declaration },
        NorScopeError::Name { callee, error } => ExpandedFuncWiringError::NorName { callee, error },
    }
}

#[verifier::opaque]
spec fn ordinary_row_matches(
    body: &OrdinaryBody, position: int, boundary: Option<usize>, definition: ScopedDefinition,
) -> bool {
    let row = body.parsed.definitions@[position];
    &&& body.range().start <= position < body.range().end
    &&& (boundary matches Some(form) ==> row.form < form)
    &&& ordinary_simple_definition(body.aliases, CalleeScope::Circuit { file: body.file, entry: body.entry },
        body.source, body.parsed.syntax.forms@, row, definition)
}

spec fn ordinary_prefix(
    body: &OrdinaryBody, start: int, consumed: int, boundary: Option<usize>, rows: Seq<ScopedDefinition>,
) -> bool {
    &&& body.range().start <= start <= consumed <= body.range().end
    &&& rows.len() == consumed - start
    &&& forall|i: int| 0 <= i < rows.len() ==> #[trigger] ordinary_row_matches(body, start + i, boundary, rows[i])
}

spec fn ordinary_before_matches(
    body: &OrdinaryBody, start: usize, consumed: usize, boundary: Option<usize>, rows: Seq<ScopedDefinition>,
) -> bool {
    &&& ordinary_prefix(body, start as int, consumed as int, boundary, rows)
    &&& if let Some(form) = boundary {
        consumed < body.range().end ==> body.parsed.definitions@[consumed as int].form >= form
    } else {
        consumed == body.range().end
    }
}

proof fn record_ordinary_row(
    body: &OrdinaryBody, start: int, consumed: int, boundary: Option<usize>,
    rows: Seq<ScopedDefinition>, definition: ScopedDefinition,
)
    requires
        ordinary_prefix(body, start, consumed, boundary, rows), consumed < body.range().end,
        ordinary_row_matches(body, consumed, boundary, definition),
    ensures ordinary_prefix(body, start, consumed + 1, boundary, rows.push(definition)),
{
    let after = rows.push(definition);
    assert forall|i: int| 0 <= i < after.len() implies #[trigger] ordinary_row_matches(body, start + i, boundary, after[i]) by {
        if i < rows.len() {
            assert(after[i] == rows[i]);
            assert(ordinary_row_matches(body, start + i, boundary, rows[i]));
        } else {
            assert(i == rows.len());
            assert(start + i == consumed);
            assert(after[i] == definition);
        }
    };
    assert(ordinary_prefix(body, start, consumed + 1, boundary, after));
}

proof fn prefix_after_row<'p, 'a>(before: Seq<ScopedDefinition<'p, 'a>>, item: ScopedDefinition<'p, 'a>, at: int)
    requires 0 <= at <= before.len(),
    ensures before.push(item).take(at) == before.take(at),
        before.push(item).skip(at) == before.skip(at).push(item),
{
    assert(before.push(item).take(at) =~= before.take(at));
    assert(before.push(item).skip(at) =~= before.skip(at).push(item));
}

fn take_ordinary_before<'p, 'a>(
    body: &OrdinaryBody<'_, '_, 'p, 'a>, position: &mut usize, stop_form: Option<usize>, rows: &mut Vec<ScopedDefinition<'p, 'a>>,
) -> (result: Result<(), ExpandedFuncWiringError<'p, 'a>>)
    requires body.valid(), body.range().start <= *old(position) <= body.range().end, locations_valid(body, old(rows)@),
    ensures body.range().start <= *final(position) <= body.range().end, locations_valid(body, final(rows)@),
        result.is_ok() ==> {
            &&& old(rows)@.len() <= final(rows)@.len()
            &&& final(rows)@.take(old(rows)@.len() as int) == old(rows)@
            &&& ordinary_before_matches(body, *old(position), *final(position), stop_form,
                final(rows)@.skip(old(rows)@.len() as int))
        },
        result matches Err(error) ==> expanded_function_diagnostic_call(error).is_none()
            && expanded_function_diagnostic_related(error).is_none() && !expanded_function_is_wiring_diagnostic(error),
{
    let start = *position;
    let offset = rows.len();
    let ghost earlier = rows@;
    let stop = body.parsed.entry_ranges[body.entry].definitions.end;
    let forms = body.parsed.syntax.forms.as_slice();
    while *position < stop
        invariant body.valid(), stop == body.range().end, body.range().start <= *position <= stop,
            forms@ == body.parsed.syntax.forms@, locations_valid(body, rows@),
            start == *old(position), offset == earlier.len(), earlier == old(rows)@,
            offset <= rows@.len(), rows@.take(offset as int) == earlier,
            ordinary_prefix(body, start as int, *position as int, stop_form, rows@.skip(offset as int)),
        decreases stop - *position,
    {
        let row = &body.parsed.definitions[*position];
        if let Some(boundary) = stop_form {
            if row.form >= boundary { return Ok(()); }
        }
        proof { build_definition_scope_evidence(body.source.text_model(), &body.parsed.build_model(), body.entry as int, *position as int); }
        let origin = CalleeScope::Circuit { file: body.file, entry: body.entry };
        let definition = match read_ordinary_definition(body.aliases, origin, body.source, forms, row) {
            Ok(Some(definition)) => definition,
            Ok(None) => {
                proof { body.source.text_model_is_text(); }
                return Err(ExpandedFuncWiringError::UnsupportedOrdinary(form_location(body.source, forms, row.expression.start)));
            },
            Err(error) => return Err(map_nor_scope_error(error)),
        };
        proof {
            push_keeps_locations(body, rows@, definition);
            assert(ordinary_row_matches(body, *position as int, stop_form, definition)) by {
                reveal(ordinary_row_matches);
            };
            record_ordinary_row(body, start as int, *position as int, stop_form, rows@.skip(offset as int), definition);
            prefix_after_row(rows@, definition, offset as int);
        }
        rows.push(definition);
        *position += 1;
    }
    Ok(())
}

#[verifier::opaque]
spec fn template_element_matches(
    aliases: &MixedUseAliases, expanded: &MacroExpandedBody, element: usize, definition: ScopedDefinition,
) -> bool {
    element < expanded.elements_model().len()
        && definition.call == Some(macro_call_location(expanded.call_model()))
        && exists|checked: CheckedTemplateDefinition|
            #[trigger] template_definition_check_matches(expanded, element, Some(Ok(checked)))
            && template_simple_definition(aliases, &checked, definition)
}

proof fn record_template_element(
    aliases: &MixedUseAliases, expanded: &MacroExpandedBody, element: usize, checked: CheckedTemplateDefinition,
    definition: ScopedDefinition,
)
    requires element < expanded.elements_model().len(),
        template_definition_check_matches(expanded, element, Some(Ok(checked))),
        template_simple_definition(aliases, &checked, definition),
        definition.call == Some(macro_call_location(expanded.call_model())),
    ensures template_element_matches(aliases, expanded, element, definition),
{
    reveal(template_element_matches);
}

spec fn generated_rows_match(aliases: &MixedUseAliases, expanded: &MacroExpandedBody, rows: Seq<ScopedDefinition>) -> bool {
    &&& rows.len() == expanded.elements_model().len()
    &&& forall|i: int| 0 <= i < rows.len() ==> template_element_matches(aliases, expanded, i as usize, #[trigger] rows[i])
}

fn take_expansion<'p, 'a>(
    body: &OrdinaryBody<'_, '_, 'p, 'a>, expanded: &MacroExpandedBody<'_, 'p, 'a>, rows: &mut Vec<ScopedDefinition<'p, 'a>>,
) -> (result: Result<(), ExpandedFuncWiringError<'p, 'a>>)
    requires locations_valid(body, old(rows)@), call_in_body(body, macro_call_location(expanded.call_model())),
        location_in_source(macro_call_location(expanded.call_model())),
    ensures locations_valid(body, final(rows)@),
        result.is_ok() ==> {
            &&& old(rows)@.len() <= final(rows)@.len()
            &&& final(rows)@.take(old(rows)@.len() as int) == old(rows)@
            &&& generated_rows_match(body.aliases, expanded, final(rows)@.skip(old(rows)@.len() as int))
        },
        result matches Err(ExpandedFuncWiringError::Generated { call, cause }) ==> {
            &&& call == macro_call_location(expanded.call_model()) && call_in_body(body, call)
            &&& expanded_definition_cause_location(*cause) matches Some(site) && location_in_source(site)
        },
        result matches Err(error) ==> diagnostic_in_body(body, error) && !expanded_function_is_wiring_diagnostic(error),
{
    let aliases = body.aliases;
    let offset = rows.len();
    let ghost earlier = rows@;
    let bound = expanded.call();
    let site = bound.site();
    let source = bound.scope().source;
    let primary = LocatedName { source, span: site.span.start..site.span.end };
    assert(primary == macro_call_location(expanded.call_model()));
    let count = expanded.elements().len();
    let mut element = 0;
    while element < count
        invariant element <= count == expanded.elements_model().len(), locations_valid(body, rows@),
            primary == macro_call_location(expanded.call_model()), location_in_source(primary), call_in_body(body, primary),
            offset == earlier.len(), earlier == old(rows)@,
            offset + element == rows@.len(), rows@.take(offset as int) == earlier,
            forall|i: int| 0 <= i < element ==> template_element_matches(aliases, expanded, i as usize, #[trigger] rows@[offset + i]),
        decreases count - element,
    {
        let call = crate::project::use_aliases::function_atoms::copy_location(&primary);
        let checked = match expanded.check_template_definition(element) {
            Some(Ok(checked)) => checked,
            None => return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::UnsupportedDefinition { call, element })),
            Some(Err(diagnostic)) => {
                let error = match diagnostic.error {
                    TemplateDefinitionError::Definition { kind, related } => {
                        let related = match related {
                            Some(event) => Some(generated_event_location(event)),
                            None => None,
                        };
                        GeneratedWiringError::InvalidDefinition { call, element, related, kind }
                    },
                    TemplateDefinitionError::UnexpectedClose(event) | TemplateDefinitionError::Unclosed(event) =>
                        GeneratedWiringError::InvalidProjection {
                            call, element, related: Some(generated_event_location(event)), token: event.token,
                        },
                    TemplateDefinitionError::Source(error) =>
                        GeneratedWiringError::InvalidProjection { call, element, related: None, token: error.token },
                };
                return Err(ExpandedFuncWiringError::Base(error));
            },
        };
        let definition = match read_template_definition(aliases, &checked, &call) {
            Ok(Some(definition)) => definition,
            Ok(None) => return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::UnsupportedDefinition { call, element })),
            Err(error) => return Err(with_generated_call(Some(&call), map_nor_scope_error(error))),
        };
        proof {
            push_keeps_locations(body, rows@, definition);
            record_template_element(aliases, expanded, element, checked, definition);
            prefix_after_row(rows@, definition, offset as int);
        }
        let ghost prior = rows@;
        rows.push(definition);
        proof {
            assert forall|i: int| 0 <= i < element + 1 implies
                template_element_matches(aliases, expanded, i as usize, #[trigger] rows@[offset + i]) by {
                if i < element { assert(rows@[offset + i] == prior[offset + i]); }
            };
        }
        element += 1;
    }
    proof {
        let added = rows@.skip(offset as int);
        assert forall|i: int| 0 <= i < added.len() implies template_element_matches(
            aliases, expanded, i as usize, #[trigger] added[i]) by { assert(added[i] == rows@[offset + i]); };
    }
    Ok(())
}

type BodyCursorState<'s, 't, 'p, 'a> = (MacroCalls<'s, 't, 'p, 'a>, usize, Seq<ScopedDefinition<'p, 'a>>);

#[verifier::opaque]
spec fn mixed_body_step(
    body: &OrdinaryBody, fuel: nat, before: BodyCursorState, after: BodyCursorState,
) -> bool {
    exists|between: Seq<ScopedDefinition>, start: MacroExpansion, expanded: MacroExpandedBody| {
        &&& before.2.len() <= between.len() <= after.2.len()
        &&& between.take(before.2.len() as int) == before.2
        &&& after.2.take(between.len() as int) == between
        &&& before.0.binding_advances(&after.0, Some(Ok(*expanded.call_model())))
        &&& start.initial_for(expanded.call_model())
        &&& #[trigger] macro_expansion_slice_matches(start, fuel, Ok(MacroExpansionSlice::Complete(expanded)))
        &&& ordinary_before_matches(body, before.1, after.1, Some(expanded.call_model().site_model().form),
            between.skip(before.2.len() as int))
        &&& #[trigger] generated_rows_match(body.aliases, &expanded, after.2.skip(between.len() as int))
    }
}

proof fn record_mixed_body_step(
    body: &OrdinaryBody, fuel: nat, before: BodyCursorState, after: BodyCursorState,
    between: Seq<ScopedDefinition>, start: MacroExpansion, expanded: MacroExpandedBody,
)
    requires before.2.len() <= between.len() <= after.2.len(),
        between.take(before.2.len() as int) == before.2, after.2.take(between.len() as int) == between,
        before.0.binding_advances(&after.0, Some(Ok(*expanded.call_model()))),
        start.initial_for(expanded.call_model()),
        macro_expansion_slice_matches(start, fuel, Ok(MacroExpansionSlice::Complete(expanded))),
        ordinary_before_matches(body, before.1, after.1, Some(expanded.call_model().site_model().form),
            between.skip(before.2.len() as int)),
        generated_rows_match(body.aliases, &expanded, after.2.skip(between.len() as int)),
    ensures mixed_body_step(body, fuel, before, after),
{
    reveal(mixed_body_step);
}

spec fn mixed_body_prefix(body: &OrdinaryBody, initial: MacroCalls, fuel: nat, history: Seq<BodyCursorState>) -> bool {
    &&& 0 < history.len()
    &&& history[0].0 == initial && history[0].1 == body.range().start && history[0].2.len() == 0
    &&& forall|i: int| 0 <= i && i+1 < history.len() ==> #[trigger] mixed_body_step(body, fuel, history[i], history[i+1])
}

proof fn extend_mixed_body(
    body: &OrdinaryBody, initial: MacroCalls, fuel: nat, history: Seq<BodyCursorState>, next: BodyCursorState,
)
    requires mixed_body_prefix(body, initial, fuel, history), mixed_body_step(body, fuel, history.last(), next),
    ensures mixed_body_prefix(body, initial, fuel, history.push(next)),
{
    let later = history.push(next);
    assert forall|i: int| 0 <= i && i+1 < later.len()
        implies #[trigger] mixed_body_step(body, fuel, later[i], later[i+1]) by {
        if i + 1 < history.len() {
            assert(mixed_body_step(body, fuel, history[i], history[i+1]));
        }
    };
}

#[verifier::opaque]
spec fn complete_mixed_body(body: &OrdinaryBody, initial: MacroCalls, fuel: nat, rows: Seq<ScopedDefinition>) -> bool {
    exists|history: Seq<BodyCursorState>, end: MacroCalls| {
        let last = history.last();
        &&& #[trigger] mixed_body_prefix(body, initial, fuel, history)
        &&& #[trigger] history.last().0.binding_advances(&end, None)
        &&& last.2.len() <= rows.len() && rows.take(last.2.len() as int) == last.2
        &&& ordinary_before_matches(body, last.1, body.range().end, None, rows.skip(last.2.len() as int))
    }
}

proof fn finish_mixed_body(
    body: &OrdinaryBody, initial: MacroCalls, fuel: nat, history: Seq<BodyCursorState>, end: MacroCalls, rows: Seq<ScopedDefinition>,
)
    requires mixed_body_prefix(body, initial, fuel, history), history.last().0.binding_advances(&end, None),
        history.last().2.len() <= rows.len(), rows.take(history.last().2.len() as int) == history.last().2,
        ordinary_before_matches(body, history.last().1, body.range().end, None, rows.skip(history.last().2.len() as int)),
    ensures complete_mixed_body(body, initial, fuel, rows),
{
    reveal(complete_mixed_body);
}

spec fn cursor_stays_in_body(body: &OrdinaryBody, initial: MacroCalls, cursor: MacroCalls) -> bool {
    &&& cursor.valid()
    &&& cursor.origin_model() == (body.file, body.entry) && cursor.aliases_model() == body.aliases
    &&& *cursor.source_model() == *body.source && *cursor.sites_model().syntax_model() == body.parsed.syntax
    &&& cursor.sites_model().body_model() == initial.sites_model().body_model()
}

proof fn indexed_call_in_body(
    body: &OrdinaryBody, initial: MacroCalls, later: MacroCalls, site: RoutineExpansionSite,
    origin: LocatedName,
)
    requires
        mixed_calls_start(body, initial), cursor_stays_in_body(body, initial, later),
        origin.source == later.source_model(), origin.span == site.span,
        macro_call_spans_in_source(later.source_model().text_model(), site),
        routine_expansion_site_at(later.source_model().text_model(), later.sites_model().syntax_model().forms@,
            later.sites_model().body_model().start as int, later.sites_model().body_model().end as int, site),
    ensures call_in_body(body, origin), location_in_source(origin),
{
    let region = later.sites_model().body_model();
    origin.source.text_model_is_text();
    located_name_evidence(origin);
    reveal(call_in_body);
    assert(expansion_body_region_matches(body.source.text_model(), &body.parsed.syntax, body.entry as int,
        Some((region.start, region.end))));
}

proof fn resolved_call_in_body(
    body: &OrdinaryBody, initial: MacroCalls, before: MacroCalls, later: MacroCalls, bound: BoundMacroCall,
)
    requires mixed_calls_start(body, initial), cursor_stays_in_body(body, initial, before),
        before.binding_advances(&later, Some(Ok(bound))),
    ensures cursor_stays_in_body(body, initial, later), call_in_body(body, macro_call_location(&bound)),
        location_in_source(macro_call_location(&bound)),
{
    indexed_call_in_body(body, initial, later, bound.site_model(), macro_call_location(&bound));
}

proof fn failed_call_in_body(
    body: &OrdinaryBody, initial: MacroCalls, before: MacroCalls, later: MacroCalls, error: MacroPreparationError,
)
    requires mixed_calls_start(body, initial), cursor_stays_in_body(body, initial, before),
        before.binding_advances(&later, Some(Err(error))),
    ensures call_in_body(body, LocatedName { source: error.source, span: error.site.span }),
{
    indexed_call_in_body(body, initial, later, error.site, LocatedName { source: error.source, span: error.site.span });
}

proof fn expansion_error_location(start: MacroExpansion, error: MacroExpansionError)
    requires start.call_model().valid(), start.failure_matches(error),
    ensures location_in_source(LocatedName { source: error.definition, span: error.related }),
{
    let checked = start.call_model().body_model();
    let body = checked.body_model();
    let at = match error.kind {
        crate::ncg2m::call_evaluation::macro_expansion::MacroExpansionErrorKind::Expression { .. } => {
            choose|at: usize| at < body.forms@.len() && #[trigger] form_span(body.forms@[at as int]) == error.related
        },
        _ => checked.elements_model()[error.element as int].at_model(),
    };
    assert(checked_macro_body_layout(&checked));
    assert(at < body.forms@.len() && error.related == form_span(body.forms@[at as int]));
    body.source.text_model_is_text();
    reveal(form_spans_valid);
    located_name_evidence(LocatedName { source: error.definition, span: error.related });
}

proof fn scoped_wiring_error_in_body(body: &OrdinaryBody, rows: Seq<ScopedDefinition>, error: ExpandedFuncWiringError)
    requires locations_valid(body, rows), scoped_wiring_diagnostic_source(rows, error),
    ensures diagnostic_in_body(body, error),
{
    if let ExpandedFuncWiringError::Generated { call, .. } = error {
        let i = choose|i: int| 0 <= i < rows.len() && (#[trigger] rows[i]).call == Some(call);
        assert(definition_in_body(body, rows[i]));
        assert forall|j: int| 0 <= j < rows.len() implies scoped_definition_locations(#[trigger] rows[j]) by {
            assert(definition_in_body(body, rows[j]));
        };
        scoped_diagnostic_cause_location(rows, error);
    }
}

fn collect_body<'p, 'a>(
    body: &OrdinaryBody<'_, '_, 'p, 'a>, initial: MacroCalls<'_, '_, 'p, 'a>, fuel: NonZeroUsize,
) -> (result: Result<Vec<ScopedDefinition<'p, 'a>>, ExpandedFuncWiringError<'p, 'a>>)
    requires body.valid(), mixed_calls_start(body, initial),
    ensures
        result matches Ok(rows) ==> locations_valid(body, rows@) && complete_mixed_body(body, initial, fuel@ as nat, rows@),
        result matches Err(error) ==> diagnostic_in_body(body, error) && !expanded_function_is_wiring_diagnostic(error),
{
    let mut rows: Vec<ScopedDefinition<'p, 'a>> = Vec::new();
    let mut calls = initial;
    let mut position = body.parsed.entry_ranges[body.entry].definitions.start;
    let ghost mut history = seq![(initial, position, rows@)];
    loop
        invariant body.valid(), body.range().start <= position <= body.range().end, locations_valid(body, rows@),
            mixed_calls_start(body, initial), cursor_stays_in_body(body, initial, calls),
            history.last() == (calls, position, rows@), mixed_body_prefix(body, initial, fuel@ as nat, history),
        decreases calls.sites_model().body_model().end - calls.sites_model().position_model(),
    {
        let ghost before = (calls, position, rows@);
        let Some(next) = calls.next_bound_macro() else {
            take_ordinary_before(body, &mut position, None, &mut rows)?;
            proof { finish_mixed_body(body, initial, fuel@ as nat, history, calls, rows@); }
            return Ok(rows);
        };
        let form = match &next {
            Ok(bound) => bound.site().form,
            Err(error) => error.site.form,
        };
        take_ordinary_before(body, &mut position, Some(form), &mut rows)?;
        let ghost between = rows@;
        let bound = match next {
            Ok(bound) => bound,
            Err(error) => {
                proof { failed_call_in_body(body, initial, before.0, calls, error); }
                return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::Preparation(error)));
            },
        };
        proof { resolved_call_in_body(body, initial, before.0, calls, bound); }
        let site = bound.site();
        let call = LocatedName { source: bound.scope().source, span: site.span.start..site.span.end };
        assert(call == macro_call_location(&bound));
        let start = bound.start_expansion();
        let ghost initial_expansion = start;
        let expanded = match start.run_slice(fuel) {
            Ok(MacroExpansionSlice::Complete(expanded)) => expanded,
            Ok(MacroExpansionSlice::Suspended(_)) => return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::Fuel(call))),
            Err(error) => {
                proof { expansion_error_location(initial_expansion, error); }
                return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::Expansion {
                    call, definition: error.definition, related: error.related, kind: error.kind,
                }));
            },
        };
        take_expansion(body, &expanded, &mut rows)?;
        proof {
            let next = (calls, position, rows@);
            record_mixed_body_step(body, fuel@ as nat, before, next, between, initial_expansion, expanded);
            extend_mixed_body(body, initial, fuel@ as nat, history, next);
            history = history.push(next);
        }
    }
}

spec fn source_body_matches(body: &OrdinaryBody, aliases: &MixedUseAliases, file: usize, entry: usize) -> bool {
    let project = aliases.targets_model().project_model();
    &&& body.valid() && body.aliases == aliases && body.file == file && body.entry == entry
    &&& file < project.sources_model().len() && file < project.indexes_model().len()
    &&& project.indexes_model()[file as int] is Circuit
    &&& *body.source == project.sources_model()[file as int]
    &&& *body.parsed == project.indexes_model()[file as int]->Circuit_0
    &&& body.parsed.syntax.entries@[entry as int].head is Func
}

spec fn mixed_calls_start(body: &OrdinaryBody, initial: MacroCalls) -> bool {
    &&& initial.valid() && initial.origin_model() == (body.file, body.entry)
    &&& initial.aliases_model() == body.aliases
    &&& *initial.source_model() == *body.source && *initial.sites_model().syntax_model() == body.parsed.syntax
    &&& routine_expansion_sites_match(initial.source_model().text_model(), initial.sites_model().syntax_model(),
        body.entry as int, Some(initial.sites_model()))
}

/// 指定した元関数を展開・結線した結果であり、通常の定義と全展開結果を本体順に含む。
pub closed spec fn expanded_bit_func_matches(
    aliases: &MixedUseAliases, file: usize, entry: usize, fuel: nat, checked: &CheckedBitFunc,
) -> bool {
    exists|body: OrdinaryBody, initial: MacroCalls, rows: Seq<ScopedDefinition>, inputs: Seq<NameSite>, outputs: Seq<NameSite>| {
        let signature = checked.signature_model();
        let forms = body.parsed.syntax.forms@;
        &&& source_body_matches(&body, aliases, file, entry)
        &&& mixed_calls_start(&body, initial)
        &&& #[trigger] complete_mixed_body(&body, initial, fuel, rows)
        &&& generated_port_names_match(body.source, forms, signature.inputs@, inputs)
        &&& generated_port_names_match(body.source, forms, signature.outputs@, outputs)
        &&& #[trigger] expanded_bit_func_wiring(inputs, outputs, rows, checked)
    }
}

proof fn record_expanded_bit_func(
    aliases: &MixedUseAliases, file: usize, entry: usize, fuel: nat, checked: &CheckedBitFunc,
    body: OrdinaryBody, initial: MacroCalls, rows: Seq<ScopedDefinition>, inputs: Seq<NameSite>, outputs: Seq<NameSite>,
)
    requires source_body_matches(&body, aliases, file, entry), mixed_calls_start(&body, initial),
        complete_mixed_body(&body, initial, fuel, rows),
        generated_port_names_match(body.source, body.parsed.syntax.forms@, checked.signature_model().inputs@, inputs),
        generated_port_names_match(body.source, body.parsed.syntax.forms@, checked.signature_model().outputs@, outputs),
        expanded_bit_func_wiring(inputs, outputs, rows, checked),
    ensures expanded_bit_func_matches(aliases, file, entry, fuel, checked),
{
}

/// 展開の診断が検査対象の関数本体にある呼び出しを指す。
///
/// 原因の元範囲は元文書の UTF-8 文字境界にある。
pub open spec fn expanded_function_diagnostic_source(
    aliases: &MixedUseAliases, file: usize, entry: usize, error: ExpandedFuncWiringError,
) -> bool {
    &&& (error is Generated ==> expanded_function_diagnostic_related(error).is_some())
    &&& (expanded_function_diagnostic_related(error) matches Some(site) ==> location_in_source(site))
    &&& (expanded_function_diagnostic_call(error) matches Some(call) ==> {
        let project = aliases.targets_model().project_model();
        let source = &project.sources_model()[file as int];
        let parsed = &project.indexes_model()[file as int]->Circuit_0;
        &&& file < project.sources_model().len() && file < project.indexes_model().len()
        &&& project.indexes_model()[file as int] is Circuit
        &&& entry < parsed.syntax.entries@.len() && parsed.syntax.entries@[entry as int].head is Func
        &&& *source == *call.source && location_in_source(call)
        &&& exists|first: usize, last: usize, site: RoutineExpansionSite| {
            &&& expansion_body_region_matches(source.text_model(), &parsed.syntax, entry as int, Some((first, last)))
            &&& #[trigger] routine_expansion_site_at(source.text_model(), parsed.syntax.forms@, first as int, last as int, site)
            &&& call.span == site.span
        }
    })
}

proof fn expanded_diagnostic_from_body(
    body: &OrdinaryBody, aliases: &MixedUseAliases, file: usize, entry: usize, error: ExpandedFuncWiringError,
)
    requires source_body_matches(body, aliases, file, entry), diagnostic_in_body(body, error),
    ensures expanded_function_diagnostic_source(aliases, file, entry, error),
{
    reveal(call_in_body);
}

/// 生成後の結線・幅の診断が、同じ関数を展開した本体の行と、その行の原因位置に対応する。
pub closed spec fn expanded_function_wiring_diagnostic(
    aliases: &MixedUseAliases, file: usize, entry: usize, fuel: nat, error: ExpandedFuncWiringError,
) -> bool {
    expanded_function_is_wiring_diagnostic(error) ==> {
        exists|body: OrdinaryBody, initial: MacroCalls, rows: Seq<ScopedDefinition>| {
            &&& source_body_matches(&body, aliases, file, entry)
            &&& mixed_calls_start(&body, initial)
            &&& #[trigger] complete_mixed_body(&body, initial, fuel, rows)
            &&& locations_valid(&body, rows)
            &&& scoped_wiring_diagnostic_source(rows, error)
        }
    }
}

/// 検査対象の関数を展開して得た、診断対象の定義を表す。
///
/// `row` は展開後の本体順の添字。左辺と右辺の先頭は元の文書と版を指す。
pub closed spec fn expanded_function_diagnostic_row(
    aliases: &MixedUseAliases, file: usize, entry: usize, fuel: nat, error: ExpandedFuncWiringError,
    row: int, target: LocatedName, expression: LocatedName,
) -> bool {
    &&& error matches ExpandedFuncWiringError::Generated { call, cause }
    &&& exists|body: OrdinaryBody, initial: MacroCalls, rows: Seq<ScopedDefinition>| {
        &&& source_body_matches(&body, aliases, file, entry)
        &&& mixed_calls_start(&body, initial)
        &&& #[trigger] complete_mixed_body(&body, initial, fuel, rows)
        &&& 0 <= row < rows.len()
        &&& rows[row].call == Some(call) && row_diagnostic_at(rows[row], *cause)
        &&& rows[row].target.location_model() == target && rows[row].expression == expression
    }
}

/// 結線や幅の違反から、その原因となった生成定義の本体内の順序と元範囲を得る。
pub proof fn expanded_function_wiring_diagnostic_row(
    aliases: &MixedUseAliases, file: usize, entry: usize, fuel: nat, error: ExpandedFuncWiringError,
)
    requires expanded_function_is_wiring_diagnostic(error), expanded_function_wiring_diagnostic(aliases, file, entry, fuel, error),
    ensures exists|row: int, target: LocatedName, expression: LocatedName| {
        &&& 0 <= row && #[trigger] expanded_function_diagnostic_row(aliases, file, entry, fuel, error, row, target, expression)
        &&& location_in_source(target) && location_in_source(expression)
        &&& match error {
            ExpandedFuncWiringError::Generated { cause, .. } => {
                (*cause is OutputWidthFromDefinition
                    || (*cause matches ExpandedFuncWiringError::Base(reason) && reason is MultipleDrivers))
                    ==> expanded_definition_cause_location(*cause) == Some(target)
            },
            _ => false,
        }
    },
{
    if let ExpandedFuncWiringError::Generated { call, cause } = error {
        let (body, initial, rows) = choose|body: OrdinaryBody, initial: MacroCalls, rows: Seq<ScopedDefinition>| {
            &&& source_body_matches(&body, aliases, file, entry)
            &&& mixed_calls_start(&body, initial)
            &&& #[trigger] complete_mixed_body(&body, initial, fuel, rows)
            &&& locations_valid(&body, rows)
            &&& scoped_wiring_diagnostic_source(rows, error)
        };
        let row = choose|i: int| 0 <= i < rows.len() && (#[trigger] rows[i]).call == Some(call)
            && row_diagnostic_at(rows[i], *cause);
        assert(definition_in_body(&body, rows[row]));
        let target = rows[row].target.location_model();
        let expression = rows[row].expression;
        assert(expanded_function_diagnostic_row(aliases, file, entry, fuel, error, row, target, expression));
    }
}

proof fn expanded_wiring_diagnostic_from_body(
    aliases: &MixedUseAliases, file: usize, entry: usize, fuel: nat, error: ExpandedFuncWiringError,
    body: &OrdinaryBody, initial: MacroCalls, rows: Seq<ScopedDefinition>,
)
    requires
        source_body_matches(body, aliases, file, entry), mixed_calls_start(body, initial),
        complete_mixed_body(body, initial, fuel, rows), locations_valid(body, rows), scoped_wiring_diagnostic_source(rows, error),
    ensures expanded_function_wiring_diagnostic(aliases, file, entry, fuel, error),
{}

impl<'t, 'p, 'a> MixedUseAliases<'t, 'p, 'a> {
    /// 通常の定義と生成定義が混在する関数を検査し、結線とビット幅を確定する。
    ///
    /// 指定位置に関数がなければ `Ok(None)` を返す。左辺が一つの定義では、右辺に信号名、
    /// 1ビット定数、基底 NOR を指定できる。NOR の直接の引数には信号名または1ビット定数を指定する。
    /// `fuel` は展開呼び出し一件ごとの実行ステップ数の上限。
    ///
    /// # Errors
    ///
    /// 基底と署名を検査してから本体を順に展開する。駆動元を登録した後、定義と出力の幅を
    /// 順に検査する。対応範囲外の式、先行しない駆動元、NOR の幅違反には元文書の範囲を返す。
    /// マクロの準備、評価、生成定義の検査に関する診断では `expand` の位置と文書版を返す。
    /// 評価や生成定義の検査で原因の範囲を特定できる場合は、原因の元文書と範囲も返す。
    pub fn check_expanded_bit_func(
        &self, file: usize, entry: usize, width_limit: u64, fuel: NonZeroUsize,
    ) -> (result: Result<Option<CheckedBitFunc<'p, 'a>>, ExpandedFuncWiringError<'p, 'a>>)
        requires mixed_use_targets_match(&self.targets_model().project_model(), self.targets_model()),
        ensures
            result matches Ok(Some(checked)) ==> checked_bit_func_available(&checked)
                && expanded_bit_func_matches(self, file, entry, fuel@ as nat, &checked)
                && self.mixed_typed_signature_matches(file, entry, width_limit, Ok(Some(checked.signature_model()))),
            result matches Err(error) ==> expanded_function_diagnostic_source(self, file, entry, error)
                && expanded_function_wiring_diagnostic(self, file, entry, fuel@ as nat, error),
    {
        let project = self.targets().project();
        let Some(index) = project.indexes().get(file) else { return Ok(None); };
        let ProjectSourceIndex::Circuit(parsed) = index else { return Ok(None); };
        let Some(item) = parsed.syntax.entries.get(entry) else { return Ok(None); };
        if !matches!(item.head, Head::Func) { return Ok(None); }
        let source = &project.sources()[file];
        if let Err(error) = validate_mixed_circuit_basis(project) {
            return Err(ExpandedFuncWiringError::Basis(error));
        }
        let signature = match self.resolve_mixed_routine_signature(file, entry, width_limit) {
            Ok(Some(signature)) => signature,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::Signature(error))),
        };
        if signature.outputs.is_empty() {
            return Err(ExpandedFuncWiringError::Base(GeneratedWiringError::UnsupportedBody));
        }
        proof {
            self.mixed_typed_signature_ports(file, entry, width_limit, signature);
            project_source_index_evidence(*source, *index);
            parsed_index_evidence(*source, *parsed);
            source.text_model_is_text();
            crate::syntax::circuit::build_entry_ranges_evidence(source.text_model(), &parsed.build_model(), entry as int);
        }
        let text = source.text();
        let inputs = typed_port_names(text, parsed.syntax.forms.as_slice(), signature.inputs.as_slice());
        let outputs = typed_port_names(text, parsed.syntax.forms.as_slice(), signature.outputs.as_slice());
        let Some(calls) = self.macro_calls(file, entry) else { return Ok(None); };
        let body = OrdinaryBody { aliases: self, file, entry, source, parsed };
        let ghost initial = calls;
        proof {
            generated_port_names_from_signature(source, parsed.syntax.forms@, signature.inputs@, inputs@);
            generated_port_names_from_signature(source, parsed.syntax.forms@, signature.outputs@, outputs@);
            assert(source_body_matches(&body, self, file, entry));
            assert(mixed_calls_start(&body, initial));
        }
        let definitions = match collect_body(&body, calls, fuel) {
            Ok(definitions) => definitions,
            Err(error) => {
                proof { expanded_diagnostic_from_body(&body, self, file, entry, error); }
                return Err(error);
            },
        };
        let checked = match check_scoped_wiring(signature, inputs.as_slice(), outputs.as_slice(), definitions.as_slice()) {
            Ok(checked) => checked,
            Err(error) => {
                proof {
                    scoped_wiring_error_in_body(&body, definitions@, error);
                    expanded_diagnostic_from_body(&body, self, file, entry, error);
                    expanded_wiring_diagnostic_from_body(self, file, entry, fuel@ as nat, error, &body, initial, definitions@);
                }
                return Err(error);
            },
        };
        proof {
            record_expanded_bit_func(self, file, entry, fuel@ as nat, &checked, body, initial, definitions@, inputs@, outputs@);
        }
        Ok(Some(checked))
    }
}

} // verus!
