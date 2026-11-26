//! 参照の用途と名前検索の観測値から、診断の種別と関連範囲を定める。

use super::*;
use crate::project::{LookupTarget, OwnedAbsoluteLookup, OwnedUnqualifiedLookup};
#[cfg(verus_only)]
use crate::project::lookup_observation::{lookup_location_model, owned_absolute_model, owned_unqualified_model};

verus! {

/// 定義の参照を解決した際に行った名前検索。
#[derive(Debug, Eq, PartialEq)]
pub enum DefinitionLookupObservation {
    /// 現在のブロックにある別名または直下の束縛を検索した。
    Unqualified(OwnedUnqualifiedLookup),
    /// 完全修飾名の候補と参照元からの可視性を調べた。
    Absolute(OwnedAbsoluteLookup),
}

/// ソースの版に依存しない診断の種別。
#[derive(Debug, Eq, PartialEq)]
pub enum ReferenceDiagnosticKind {
    /// 対象が存在しない。
    Missing,
    /// 相対パスの先頭が見つからない。
    MissingPrefix,
    /// 相対パスの先頭が宣言を指している。
    DeclarationPrefix,
    /// 宣言が参照元に公開されていない。
    Private,
    /// 宣言が必要な位置で名前空間を参照している。
    Namespace,
    /// この位置では参照できない宣言種別。
    WrongDeclaration,
}

type RelatedLocation = (Seq<Seq<u8>>, core::ops::Range<usize>);
type Problem = (ReferenceDiagnosticKind, Option<Head>, Option<RelatedLocation>);

pub open spec fn named_location(source: &ProjectSource, span: core::ops::Range<usize>) -> RelatedLocation {
    (source.virtual_path_model().components_model(), span)
}

spec fn observed_target_problem(
    role: ReferenceUse, target: LookupTarget, visible: bool,
) -> Option<Problem> {
    match target {
        LookupTarget::Declaration { head, location } => {
            let position = Some(lookup_location_model(location));
            if !visible { Some((ReferenceDiagnosticKind::Private, None, position)) }
            else if accepts_declaration(role, head) { None }
            else { Some((ReferenceDiagnosticKind::WrongDeclaration, Some(head), position)) }
        },
        LookupTarget::Namespace { introduced_at, .. } =>
            Some((ReferenceDiagnosticKind::Namespace, None, Some(lookup_location_model(introduced_at)))),
    }
}

spec fn observed_problem(input: ReferenceRequest, observation: DefinitionLookupObservation) -> Option<Problem> {
    match observation {
        DefinitionLookupObservation::Unqualified(lookup) => match lookup {
            OwnedUnqualifiedLookup::Missing =>
                if input.role is Callee && input.word@ == "nor"@ { None }
                else { Some((ReferenceDiagnosticKind::Missing, None, None)) },
            OwnedUnqualifiedLookup::Alias { target, .. } | OwnedUnqualifiedLookup::Direct(target) =>
                observed_target_problem(input.role, target, true),
        },
        DefinitionLookupObservation::Absolute(lookup) => match lookup.target {
            None => Some((ReferenceDiagnosticKind::Missing, None, None)),
            Some(target) => observed_target_problem(input.role, target, lookup.visible_declaration),
        },
    }
}

pub open spec fn problem_kind(reason: DefinitionReferenceReason) -> Problem {
    match reason {
        DefinitionReferenceReason::Missing => (ReferenceDiagnosticKind::Missing, None, None),
        DefinitionReferenceReason::MissingPrefix => (ReferenceDiagnosticKind::MissingPrefix, None, None),
        DefinitionReferenceReason::DeclarationPrefix { source, form } =>
            (ReferenceDiagnosticKind::DeclarationPrefix, None, Some(named_location(source, form.name.span))),
        DefinitionReferenceReason::Private(location) =>
            (ReferenceDiagnosticKind::Private, None, Some(named_location(location.source, location.span))),
        DefinitionReferenceReason::Namespace(location) =>
            (ReferenceDiagnosticKind::Namespace, None, Some(named_location(location.source, location.span))),
        DefinitionReferenceReason::WrongDeclaration { source, form } =>
            (ReferenceDiagnosticKind::WrongDeclaration, Some(form.head), Some(named_location(source, form.name.span))),
    }
}

spec fn binding_problem(binding: Result<DefinitionBinding, DefinitionReferenceReason>) -> Option<Problem> {
    match binding {
        Ok(_) => None,
        Err(reason) => Some(problem_kind(reason)),
    }
}

pub(super) closed spec fn observed_binding_matches(
    request: ReferenceRequest, observation: DefinitionLookupObservation,
    binding: Result<DefinitionBinding, DefinitionReferenceReason>,
) -> bool {
    observed_problem(request, observation) == binding_problem(binding)
}

pub(super) proof fn unqualified_problem_matches(
    request: ReferenceRequest, found: Option<UnqualifiedTarget>, lookup: OwnedUnqualifiedLookup,
)
    requires owned_unqualified_model(lookup, found),
    ensures observed_binding_matches(request, DefinitionLookupObservation::Unqualified(lookup),
        unqualified_binding(request, found)),
{
    match found {
        Some(UnqualifiedTarget::Alias(item)) => {
            item.target_model_agrees();
            match item.target {
                AbsoluteTarget::Namespace { .. } | AbsoluteTarget::Declaration { .. } => {},
            }
        },
        Some(UnqualifiedTarget::Direct(target)) => match target {
            AbsoluteTarget::Namespace { .. } | AbsoluteTarget::Declaration { .. } => {},
        },
        None => {},
    }
}

pub(super) proof fn absolute_problem_matches(
    request: ReferenceRequest, lookup: AbsoluteLookup, owned: OwnedAbsoluteLookup,
    binding: Result<DefinitionBinding, DefinitionReferenceReason>,
)
    requires owned_absolute_model(owned, lookup), absolute_outcome(request, lookup.resolution_model(), binding),
    ensures observed_binding_matches(request, DefinitionLookupObservation::Absolute(owned), binding),
{
    match lookup.target_model() {
        Some(AbsoluteTarget::Namespace { .. }) | Some(AbsoluteTarget::Declaration { .. }) => {},
        None => {},
    }
}

/// 参照の診断を、主範囲、元の綴り、種別、必要な関連範囲で表す。
///
/// ソースの版と LSP の位置は、公開前に現在のスナップショットから求める。
pub open spec fn definition_diagnostic_model(
    result: Result<ResolvedDefinitionReference, DefinitionReferenceError>,
) -> Option<(RelatedLocation, Seq<char>, Problem)> {
    match result {
        Err(DefinitionReferenceError::Rejected { site, reason }) =>
            Some((named_location(site.source, site.name.span), site.name.word@, problem_kind(reason))),
        _ => None,
    }
}

/// 参照の主範囲と、観測から得た診断が解決結果に対応することを表す。
pub closed spec fn definition_lookup_matches(
    result: Result<ResolvedDefinitionReference, DefinitionReferenceError>, observation: DefinitionLookupObservation,
) -> bool {
    match result {
        Ok(resolved) => observed_binding_matches(resolved.site.request_model(), observation, Ok(resolved.binding)),
        Err(DefinitionReferenceError::Rejected { site, reason }) =>
            observed_binding_matches(site.request_model(), observation, Err(reason)),
        _ => false,
    }
}

pub(super) proof fn observation_from_binding(
    site: DefinitionReferenceSite, binding: Result<DefinitionBinding, DefinitionReferenceReason>,
    observation: Option<DefinitionLookupObservation>,
    result: Result<ResolvedDefinitionReference, DefinitionReferenceError>,
)
    requires
        observation matches Some(observation) ==> observed_binding_matches(site.request_model(), observation, binding),
        result == match binding {
            Ok(binding) => Ok(ResolvedDefinitionReference { site, binding }),
            Err(reason) => Err(DefinitionReferenceError::Rejected { site, reason }),
        },
    ensures observation matches Some(observation) ==> definition_lookup_matches(result, observation),
{
}

/// 診断を再利用するときに照合する、参照元の位置、綴り、用途を表す。
pub open spec fn definition_lookup_input(
    result: Result<ResolvedDefinitionReference, DefinitionReferenceError>,
) -> Option<(RelatedLocation, Seq<char>, ExpressionReferenceKind, Head)> {
    let site = match result {
        Ok(resolved) => Some(resolved.site),
        Err(DefinitionReferenceError::Rejected { site, .. }) => Some(site),
        _ => None,
    };
    match site {
        Some(site) => Some((named_location(site.source, site.name.span), site.name.word@, site.role, site.owner)),
        None => None,
    }
}

/// 参照の位置・綴り・用途と名前検索の観測が同じなら、型付き診断と関連範囲も一致する。
pub proof fn definition_lookup_diagnostics_agree(
    left: Result<ResolvedDefinitionReference, DefinitionReferenceError>,
    right: Result<ResolvedDefinitionReference, DefinitionReferenceError>,
    observation: DefinitionLookupObservation,
)
    requires definition_lookup_matches(left, observation), definition_lookup_matches(right, observation),
        definition_lookup_input(left) == definition_lookup_input(right),
    ensures definition_diagnostic_model(left) == definition_diagnostic_model(right),
{
}

} // verus!
