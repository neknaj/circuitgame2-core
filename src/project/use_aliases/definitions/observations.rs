//! 参照の用途と名前検索の観測値から、診断の種別と関連範囲を定める。

use super::*;
use alloc::{borrow::ToOwned, string::String};
use crate::project::lookup_observation::{capture_location, head_matches, lookup_location_matches};
use crate::project::{LookupLocation, LookupTarget, OwnedAbsoluteLookup, OwnedUnqualifiedLookup};
#[cfg(verus_only)]
use crate::project::lookup_observation::{lookup_location_model, owned_absolute_model, owned_unqualified_model};
use crate::project::DefinitionPosition;
#[cfg(verus_only)]
use crate::project::{declaration_visible_from, selected_direct_target_matches};
#[cfg(verus_only)]
use crate::project::resolution::key_resolutions_agree;

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
        DefinitionLookupObservation::Absolute(lookup) => absolute_lookup_problem(input.role, lookup),
    }
}

spec fn absolute_lookup_problem(role: ReferenceUse, lookup: OwnedAbsoluteLookup) -> Option<Problem> {
    match lookup.target {
        None => Some((ReferenceDiagnosticKind::Missing, None, None)),
        Some(target) => observed_target_problem(role, target, lookup.visible_declaration),
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

/// 版をまたいで保持する型付きの参照診断。
#[derive(Debug)]
pub struct StoredReferenceProblem {
    /// 診断の種別。
    pub kind: ReferenceDiagnosticKind,
    /// この参照位置で使えないと判定した宣言種別。
    pub declaration_kind: Option<Head>,
    /// 対象の宣言または名前空間の範囲。
    pub related: Option<LookupLocation>,
}

impl StoredReferenceProblem {
    /// 診断の種別と関連範囲の比較に用いる値を表す。
    pub open spec fn model(&self) -> Problem {
        (self.kind, self.declaration_kind, match self.related {
            None => None,
            Some(location) => Some(lookup_location_model(location)),
        })
    }
}

fn store_problem(problem: &DefinitionReferenceReason) -> (stored: StoredReferenceProblem)
    ensures stored.model() == problem_kind(*problem),
{
    let (kind, declaration_kind, related) = match problem {
        DefinitionReferenceReason::Missing => (ReferenceDiagnosticKind::Missing, None, None),
        DefinitionReferenceReason::MissingPrefix => (ReferenceDiagnosticKind::MissingPrefix, None, None),
        DefinitionReferenceReason::DeclarationPrefix { source, form } =>
            (ReferenceDiagnosticKind::DeclarationPrefix, None, Some(capture_location(source, &form.name.span))),
        DefinitionReferenceReason::Private(location) =>
            (ReferenceDiagnosticKind::Private, None, Some(capture_location(location.source, &location.span))),
        DefinitionReferenceReason::Namespace(location) =>
            (ReferenceDiagnosticKind::Namespace, None, Some(capture_location(location.source, &location.span))),
        DefinitionReferenceReason::WrongDeclaration { source, form } =>
            (ReferenceDiagnosticKind::WrongDeclaration, Some(form.head), Some(capture_location(source, &form.name.span))),
    };
    StoredReferenceProblem { kind, declaration_kind, related }
}

/// 完全修飾の参照で記録した入力と候補、および診断。
///
/// 正常な参照は診断が `None` の項目として記録する。
#[derive(Debug)]
pub struct CachedAbsoluteReferenceDiagnostic {
    primary: LookupLocation,
    word: String,
    role: ExpressionReferenceKind,
    owner: Head,
    lookup: OwnedAbsoluteLookup,
    problem: Option<StoredReferenceProblem>,
}

impl CachedAbsoluteReferenceDiagnostic {
    /// 参照元が占める UTF-8 半開バイト範囲と、その仮想ファイル識別子を借りる。
    pub fn primary(&self) -> &LookupLocation { &self.primary }

    /// 参照元で使われた完全修飾名の綴りを借りる。
    pub fn word(&self) -> &str { self.word.as_str() }

    /// 診断を借りる。名前が解決したときは `None`。
    pub fn problem(&self) -> Option<&StoredReferenceProblem> { self.problem.as_ref() }

    /// 保存された診断の比較に用いる値を表す。
    pub closed spec fn diagnostic_model(&self) -> Option<(RelatedLocation, Seq<char>, Problem)> {
        match self.problem {
            None => None,
            Some(problem) => Some((lookup_location_model(self.primary), self.word@, problem.model())),
        }
    }

    /// 名前検索の観測値だけから、保存した診断が決まることを表す。
    pub closed spec fn valid(&self) -> bool {
        let role = match self.role {
            ExpressionReferenceKind::CastType => ReferenceUse::StructType,
            ExpressionReferenceKind::Callee => ReferenceUse::Callee(self.owner),
        };
        absolute_lookup_problem(role, self.lookup) == match self.problem {
            Some(problem) => Some(problem.model()),
            None => None,
        }
    }

    /// 現在の参照元と観測値が、保存した入力に一致することを表す。
    pub closed spec fn matches_current(&self, site: DefinitionReferenceSite, lookup: AbsoluteLookup) -> bool {
        &&& lookup_location_model(self.primary) == named_location(site.source, site.name.span)
        &&& self.word@ == site.name.word@
        &&& self.role == site.role
        &&& self.owner == site.owner
        &&& owned_absolute_model(self.lookup, lookup)
    }

    /// 新版で観測した候補が一致すれば、用途判定から得られる診断は保存済みの値に等しい。
    ///
    /// この補題は新版で観測付きの参照解決を実行することを前提にしない。
    pub proof fn diagnostic_agrees(
        &self, site: DefinitionReferenceSite, lookup: AbsoluteLookup,
        binding: Result<DefinitionBinding, DefinitionReferenceReason>,
    )
        requires self.valid(), self.matches_current(site, lookup),
            absolute_observation_answers(site, lookup, binding),
        ensures self.diagnostic_model() == match binding {
            Ok(_) => None,
            Err(reason) => Some((named_location(site.source, site.name.span), site.name.word@, problem_kind(reason))),
        },
    {
        absolute_problem_matches(site.request_model(), lookup, self.lookup, binding);
    }
}

/// 新版の候補から、参照位置で利用できる宣言または診断が定まることを表す。
pub closed spec fn absolute_observation_answers(
    site: DefinitionReferenceSite, lookup: AbsoluteLookup,
    binding: Result<DefinitionBinding, DefinitionReferenceReason>,
) -> bool {
    absolute_outcome(site.request_model(), lookup.resolution_model(), binding)
}
fn reference_roles_match(left: ExpressionReferenceKind, right: ExpressionReferenceKind) -> (same: bool)
    ensures same == (left == right),
{
    matches!((left, right),
        (ExpressionReferenceKind::Callee, ExpressionReferenceKind::Callee) |
        (ExpressionReferenceKind::CastType, ExpressionReferenceKind::CastType))
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 完全修飾の参照を解決し、次の版で照合できる診断を保存する。
    ///
    /// 位置が範囲外、または完全修飾名以外であれば保存する項目はない。
    pub fn cache_absolute_reference_diagnostic(&self, at: DefinitionPosition)
        -> (out: Option<CachedAbsoluteReferenceDiagnostic>)
        requires self.can_resolve(),
        ensures out matches Some(cached) ==> {
            &&& cached.valid()
            &&& exists|result: Result<ResolvedDefinitionReference, DefinitionReferenceError>|
                #[trigger] self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, result)
                && cached.diagnostic_model() == definition_diagnostic_model(result)
        },
    {
        let (result, observation) = self.observe_definition_reference(at.file, at.entry, at.definition, at.reference);
        let Some(DefinitionLookupObservation::Absolute(lookup)) = observation else { return None; };
        let ghost resolved = result;
        let ghost observed_lookup = lookup;
        let (site, problem) = match result {
            Ok(resolved) => (resolved.site, None),
            Err(DefinitionReferenceError::Rejected { site, reason }) =>
                (site, Some(store_problem(&reason))),
            Err(DefinitionReferenceError::UnknownPosition) => {
                proof { assert(false); }
                return None;
            },
        };
        let cached = CachedAbsoluteReferenceDiagnostic {
            primary: capture_location(site.source, &site.name.span),
            word: site.name.word.to_owned(),
            role: site.role,
            owner: site.owner,
            lookup,
            problem,
        };
        assert(definition_lookup_matches(resolved, DefinitionLookupObservation::Absolute(observed_lookup)));
        assert(cached.diagnostic_model() == definition_diagnostic_model(resolved));
        Some(cached)
    }

    /// 現在の索引と候補が、保存済みの参照先の観測に対応することを表す。
    pub closed spec fn current_absolute_lookup_matches(
        &self, at: DefinitionPosition, cached: &CachedAbsoluteReferenceDiagnostic,
    ) -> bool {
        exists|site: DefinitionReferenceSite, lookup: AbsoluteLookup, from: Option<&str>, key: NameKey|
            #![trigger cached.matches_current(site, lookup), absolute_path_parts(site.name.word, key.parent, key.name),
                self.scope_matches(at.file, site.block, Ok(from))] {
            &&& self.positioned_reference(at.file, at.entry, at.definition, at.reference, site, AtomKind::AbsolutePath)
            &&& self.scope_matches(at.file, site.block, Ok(from))
            &&& absolute_path_parts(site.name.word, key.parent, key.name)
            &&& selected_direct_target_matches(&self.targets.exports_model().declarations_model(), key, lookup.target_model())
            &&& lookup.visible_model() == (lookup.target_model() matches Some(AbsoluteTarget::Declaration { .. })
                && declaration_visible_from(&self.targets.exports_model(), key, from))
            &&& has_resolution(&self.targets.exports_model(), key, from, lookup.resolution_model())
            &&& bare_atom_kind(site.name.word.spec_bytes()) == Some(AtomKind::AbsolutePath)
            &&& cached.matches_current(site, lookup)
        }
    }

    /// 照合できた項目は、現在の参照を通常どおり解決したときと同じ診断を持つ。
    pub proof fn reused_absolute_diagnostic_agrees(
        &self, at: DefinitionPosition, cached: &CachedAbsoluteReferenceDiagnostic,
        result: Result<ResolvedDefinitionReference, DefinitionReferenceError>,
    )
        requires self.can_resolve(), cached.valid(), self.current_absolute_lookup_matches(at, cached),
            self.definition_resolution_evidence(at.file, at.entry, at.definition, at.reference, result),
        ensures cached.diagnostic_model() == definition_diagnostic_model(result),
    {
        let exports = &self.targets.exports_model();
        let (site, lookup, from, key) =
            choose|site: DefinitionReferenceSite, lookup: AbsoluteLookup, from: Option<&str>, key: NameKey|
                #![trigger cached.matches_current(site, lookup), absolute_path_parts(site.name.word, key.parent, key.name),
                    self.scope_matches(at.file, site.block, Ok(from))] {
                &&& self.positioned_reference(at.file, at.entry, at.definition, at.reference, site, AtomKind::AbsolutePath)
                &&& self.scope_matches(at.file, site.block, Ok(from))
                &&& absolute_path_parts(site.name.word, key.parent, key.name)
                &&& has_resolution(exports, key, from, lookup.resolution_model())
                &&& bare_atom_kind(site.name.word.spec_bytes()) == Some(AtomKind::AbsolutePath)
                &&& cached.matches_current(site, lookup)
            };
        let (other, binding) = match result {
            Ok(resolved) => (resolved.site, Ok(resolved.binding)),
            Err(DefinitionReferenceError::Rejected { site, reason }) => (site, Err(reason)),
            Err(DefinitionReferenceError::UnknownPosition) => { assert(false); arbitrary() },
        };
        assert(site.name.word.spec_bytes() == other.name.word.spec_bytes());
        encode_utf8_decode_utf8(site.name.word@);
        encode_utf8_decode_utf8(other.name.word@);
        assert(site.name.word@ == other.name.word@);
        let other_scope = choose|scope: Option<&str>| #[trigger] self.scope_matches(at.file, other.block, Ok(scope))
            && self.binding_evidence(at.file, other.request_model(), scope, AtomKind::AbsolutePath, binding);
        self.relative_scope_agrees(at.file, site.block, from, other_scope);
        let answer = choose|found: Result<AbsoluteTarget, AbsoluteResolutionError>|
            #[trigger] absolute_resolution_evidence(exports, other.name.word, other_scope, found)
            && absolute_outcome(other.request_model(), found, binding);
        let other_key = choose|candidate: NameKey|
            #[trigger] absolute_path_parts(other.name.word, candidate.parent, candidate.name)
            && has_resolution(exports, candidate, other_scope, answer);
        absolute_path_parts_agree(site.name.word, key.parent, key.name, other.name.word, other_key.parent, other_key.name);
        self.targets.declarations_cover_project();
        key_resolutions_agree(&self.targets.project_model(), exports, key, other_key, from, lookup.resolution_model(), answer);
        cached.diagnostic_agrees(site, lookup, binding);
    }

    /// 現在の参照元と宣言表を照合し、再利用できる項目を借りる。
    ///
    /// 候補と可視性だけを読み、参照の用途を判定しない。照合できない場合は `None`。
    /// 一致した項目の `problem()` が `None` であれば、診断はない。
    pub fn reuse_absolute_reference_diagnostic<'c>(
        &self, at: DefinitionPosition, cached: &'c CachedAbsoluteReferenceDiagnostic,
    ) -> (out: Option<&'c CachedAbsoluteReferenceDiagnostic>)
        requires self.can_resolve(),
        ensures
            out matches Some(reused) ==> reused == cached && self.current_absolute_lookup_matches(at, cached),
    {
        let (site, kind, from) = self.read_definition_site(at.file, at.entry, at.definition, at.reference)?;
        if !matches!(kind, AtomKind::AbsolutePath)
            || site.name.word != cached.word.as_str()
            || !reference_roles_match(site.role, cached.role)
            || !head_matches(site.owner, cached.owner)
        {
            return None;
        }
        if !lookup_location_matches(&cached.primary, site.source, &site.name.span) {
            return None;
        }
        let Some((parent, name)) = split_absolute_path(site.name.word) else {
            proof { assert(false); }
            return None;
        };
        let key = NameKey { parent, name };
        let lookup = self.targets.exports().observe_absolute_key(key, from);
        if !lookup.matches_owned_observation(&cached.lookup) {
            return None;
        }
        assert(site.name.word@ == cached.word@);
        assert(site.role == cached.role && site.owner == cached.owner);
        assert(absolute_path_parts(site.name.word, key.parent, key.name));
        assert(cached.matches_current(site, lookup));
        assert(self.current_absolute_lookup_matches(at, cached));
        Some(cached)
    }
}

} // verus!
