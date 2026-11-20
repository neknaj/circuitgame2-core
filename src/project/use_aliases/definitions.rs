//! 定義の右辺にある名前を、参照元のスコープと用途に従って解決する。

use super::{RelativeResolutionError, RelativeTarget, UnqualifiedTarget, UseAliases};
#[cfg(verus_only)]
use crate::project::absolute_resolution_evidence;
#[cfg(verus_only)]
use crate::project::declarations::{declaration_key_evidence, declaration_sites_agree, form_key, same_declaration_key};
#[cfg(verus_only)]
use crate::project::resolution::absolute_declaration_evidence;
#[cfg(verus_only)]
use crate::project::name_keys::key_view;
#[cfg(verus_only)]
use crate::project::resolution::{declaration_exists, direct_targets_agree, has_resolution};
#[cfg(verus_only)]
use crate::project::{NameKey, same_target};
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
use crate::project::circuits::read_indexed_atom;
use crate::project::{AbsoluteResolutionError, AbsoluteTarget, LocatedName, ProjectSource};
#[cfg(verus_only)]
use crate::syntax::{absolute_path_parts, absolute_path_parts_agree, bare_atom_kind};
use crate::syntax::circuit::{ExpressionReferenceKind, Head, NameSite, NamedForm};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    NamedBuildCircuit, build_definition_scope_evidence, build_entry_ranges_evidence,
    expression_reference_in_source, namespace_name_evidence,
};
use crate::syntax::{AtomKind, Form};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::encode_utf8_decode_utf8};

verus! {

pub(super) open spec fn definition_count(parsed: &NamedBuildCircuit, entry: int) -> int {
    if 0 <= entry < parsed.entry_ranges@.len() {
        let defs = parsed.entry_ranges@[entry].definitions;
        defs.end - defs.start
    } else { 0 }
}

pub(super) open spec fn reference_count(parsed: &NamedBuildCircuit, entry: int, definition: int) -> int {
    if 0 <= entry < parsed.entry_ranges@.len() && 0 <= definition < definition_count(parsed, entry) {
        let position = parsed.entry_ranges@[entry].definitions.start + definition;
        if 0 <= position < parsed.definitions@.len() {
            let refs = parsed.definitions@[position].references;
            refs.end - refs.start
        } else { 0 }
    } else { 0 }
}

/// 定義の右辺で名前を参照した位置と、その用途。
#[derive(Debug)]
pub struct DefinitionReferenceSite<'p, 'a> {
    /// 参照元のファイルと文書版。
    pub source: &'p ProjectSource<'a>,
    /// 元の綴りと UTF-8 半開バイト範囲。
    pub name: NameSite<'a>,
    /// 呼び出し名または型名としての用途。
    pub role: ExpressionReferenceKind,
    /// 参照を含む宣言またはモジュール断片の種別。
    pub owner: Head,
    /// 参照元を囲む名前空間ブロックの添字。ファイル直下では `None`。
    pub block: Option<usize>,
}

/// 定義の右辺に現れた名前が指す対象。
#[derive(Debug)]
pub enum DefinitionBinding<'p, 'a> {
    /// 共有宣言表にある回路または構造体。
    Declaration {
        /// 定義元のファイルと文書版。
        source: &'p ProjectSource<'a>,
        /// 定義の名前、種別、ソース範囲。
        form: &'p NamedForm<'a>,
    },
    /// 無修飾の呼び出しで、宣言や別名の束縛がないときに選ぶ基底ゲート。
    Nor,
}

/// 定義の参照元と、用途に従って解決した対象。
#[derive(Debug)]
pub struct ResolvedDefinitionReference<'p, 'a> {
    /// 名前を使った位置。
    pub site: DefinitionReferenceSite<'p, 'a>,
    /// 元の宣言または基底ゲート。
    pub binding: DefinitionBinding<'p, 'a>,
}

/// 回路名または構造体型の参照を解決できなかった理由。
#[derive(Debug)]
pub enum DefinitionReferenceReason<'p, 'a> {
    /// 指定した名前の対象が見つからない。
    Missing,
    /// 相対パスの先頭を参照元のスコープで解決できない。
    MissingPrefix,
    /// 相対パスの先頭は名前空間を指す必要がある。
    DeclarationPrefix {
        /// 先頭の名前が指した宣言のファイル。
        source: &'p ProjectSource<'a>,
        /// 先頭の名前が指した宣言。
        form: &'p NamedForm<'a>,
    },
    /// 非公開の宣言を別の名前空間から参照した。
    Private(LocatedName<'p, 'a>),
    /// 呼び出し名または型名が名前空間を指した。
    Namespace(LocatedName<'p, 'a>),
    /// 参照用途または参照元の宣言で使えない種別を指した。
    WrongDeclaration {
        /// 解決した宣言のファイル。
        source: &'p ProjectSource<'a>,
        /// 解決した宣言の種別と名前の位置。
        form: &'p NamedForm<'a>,
    },
}

/// 定義の参照を解決する際に返す診断。
#[derive(Debug)]
pub enum DefinitionReferenceError<'p, 'a> {
    /// ファイル、索引項目、定義、参照のいずれかの添字が範囲外である。
    UnknownPosition,
    /// 参照先が見つからないか、参照位置で使えない。
    Rejected {
        /// 診断の主範囲を含む参照元。
        site: DefinitionReferenceSite<'p, 'a>,
        /// 違反の理由と、関連する宣言や名前空間の位置。
        reason: DefinitionReferenceReason<'p, 'a>,
    },
}

#[derive(Clone, Copy)]
pub(super) enum ReferenceUse {
    StructType,
    Callee(Head),
}

pub(super) struct ReferenceRequest<'a> {
    pub(super) block: Option<usize>,
    pub(super) word: &'a str,
    pub(super) role: ReferenceUse,
}

impl<'p, 'a> DefinitionReferenceSite<'p, 'a> {
    spec fn request_model(&self) -> ReferenceRequest<'a> {
        ReferenceRequest {
            block: self.block,
            word: self.name.word,
            role: match self.role {
                ExpressionReferenceKind::CastType => ReferenceUse::StructType,
                ExpressionReferenceKind::Callee => ReferenceUse::Callee(self.owner),
            },
        }
    }

    fn request(&self) -> (request: ReferenceRequest<'a>)
        ensures request == self.request_model(),
    {
        let role = match self.role {
            ExpressionReferenceKind::CastType => ReferenceUse::StructType,
            ExpressionReferenceKind::Callee => ReferenceUse::Callee(self.owner),
        };
        ReferenceRequest { block: self.block, word: self.name.word, role }
    }
}

pub(super) open spec fn accepts_declaration(role: ReferenceUse, target: Head) -> bool {
    match role {
        ReferenceUse::StructType => target is Struct,
        ReferenceUse::Callee(owner) => target is Func
            || (!(owner is Func) && (target is Module || target is Latch || target is Memory)),
    }
}

fn declaration_allowed(role: ReferenceUse, target: Head) -> (allowed: bool)
    ensures allowed == accepts_declaration(role, target),
{
    match role {
        ReferenceUse::StructType => matches!(target, Head::Struct),
        ReferenceUse::Callee(owner) => matches!(target, Head::Func)
            || (!matches!(owner, Head::Func) && matches!(target, Head::Module | Head::Latch | Head::Memory)),
    }
}

spec fn declaration_binding<'p, 'a>(
    site: ReferenceRequest, source: &'p ProjectSource<'a>, form: &'p NamedForm<'a>,
) -> Result<DefinitionBinding<'p, 'a>, DefinitionReferenceReason<'p, 'a>> {
    if accepts_declaration(site.role, form.head) {
        Ok(DefinitionBinding::Declaration { source, form })
    } else {
        Err(DefinitionReferenceReason::WrongDeclaration { source, form })
    }
}

fn check_declaration<'p, 'a>(
    site: &ReferenceRequest, source: &'p ProjectSource<'a>, form: &'p NamedForm<'a>,
) -> (result: Result<DefinitionBinding<'p, 'a>, DefinitionReferenceReason<'p, 'a>>)
    ensures result == declaration_binding(*site, source, form),
{
    if declaration_allowed(site.role, form.head) {
        Ok(DefinitionBinding::Declaration { source, form })
    } else {
        Err(DefinitionReferenceReason::WrongDeclaration { source, form })
    }
}

spec fn absolute_binding<'p, 'a>(
    site: ReferenceRequest, target: AbsoluteTarget<'p, 'a, '_>,
) -> Result<DefinitionBinding<'p, 'a>, DefinitionReferenceReason<'p, 'a>> {
    match target {
        AbsoluteTarget::Declaration { source, form } => declaration_binding(site, source, form),
        AbsoluteTarget::Namespace { introduced_at, .. } => Err(DefinitionReferenceReason::Namespace(introduced_at)),
    }
}

fn check_absolute<'p, 'a>(
    site: &ReferenceRequest, target: &AbsoluteTarget<'p, 'a, '_>,
) -> (result: Result<DefinitionBinding<'p, 'a>, DefinitionReferenceReason<'p, 'a>>)
    ensures result == absolute_binding(*site, *target),
{
    match target {
        AbsoluteTarget::Declaration { source, form } => check_declaration(site, source, form),
        AbsoluteTarget::Namespace { introduced_at, .. } =>
            Err(DefinitionReferenceReason::Namespace(LocatedName {
                source: introduced_at.source, span: introduced_at.span.start..introduced_at.span.end,
            })),
    }
}

spec fn unqualified_binding<'p, 'a>(
    site: ReferenceRequest, found: Option<UnqualifiedTarget<'_, 'p, 'a, '_>>,
) -> Result<DefinitionBinding<'p, 'a>, DefinitionReferenceReason<'p, 'a>> {
    match found {
        Some(UnqualifiedTarget::Alias(directive)) => absolute_binding(site, directive.target),
        Some(UnqualifiedTarget::Direct(target)) => absolute_binding(site, target),
        None => if site.role is Callee && site.word@ == "nor"@ {
            Ok(DefinitionBinding::Nor)
        } else {
            Err(DefinitionReferenceReason::Missing)
        },
    }
}

spec fn relative_binding(
    site: ReferenceRequest, found: Result<RelativeTarget, RelativeResolutionError>,
    binding: Result<DefinitionBinding, DefinitionReferenceReason>,
) -> bool {
    match found {
        Ok(RelativeTarget::Declaration { source, form }) =>
            binding == declaration_binding(site, source, form),
        Ok(RelativeTarget::Namespace { introduced_at, .. }) =>
            binding == Err(DefinitionReferenceReason::Namespace(introduced_at)),
        Err(RelativeResolutionError::Private(location)) =>
            binding == Err(DefinitionReferenceReason::Private(location)),
        Err(RelativeResolutionError::MissingHead) =>
            binding == Err(DefinitionReferenceReason::MissingPrefix),
        Err(RelativeResolutionError::DeclarationHead { source, form }) =>
            binding == Err(DefinitionReferenceReason::DeclarationPrefix { source, form }),
        Err(RelativeResolutionError::Missing) => binding == Err(DefinitionReferenceReason::Missing),
        Err(_) => false,
    }
}

spec fn absolute_outcome(
    site: ReferenceRequest, found: Result<AbsoluteTarget, AbsoluteResolutionError>,
    binding: Result<DefinitionBinding, DefinitionReferenceReason>,
) -> bool {
    match found {
        Ok(target) => binding == absolute_binding(site, target),
        Err(AbsoluteResolutionError::Missing) => binding == Err(DefinitionReferenceReason::Missing),
        Err(AbsoluteResolutionError::Private(location)) => binding == Err(DefinitionReferenceReason::Private(location)),
        Err(AbsoluteResolutionError::InvalidPath) => false,
    }
}

pub(super) open spec fn unqualified_target<'p, 'a, 'q>(target: UnqualifiedTarget<'_, 'p, 'a, 'q>) -> AbsoluteTarget<'p, 'a, 'q> {
    match target {
        UnqualifiedTarget::Alias(directive) => directive.target,
        UnqualifiedTarget::Direct(target) => target,
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 同じスコープで同じ名前を引くと、同じ宣言または名前空間を参照する。
    pub(super) proof fn unqualified_targets_agree(
        &self, file: usize, block: Option<usize>, from: Option<&str>, left_name: &str, right_name: &str,
        left: UnqualifiedTarget, right: UnqualifiedTarget,
    )
        requires
            left_name@ == right_name@,
            self.unqualified_binding_matches(file, block, left_name, from, Some(left)),
            self.unqualified_binding_matches(file, block, right_name, from, Some(right)),
        ensures same_target(unqualified_target(left), unqualified_target(right)),
    {
        let items = self.directives_model();
        match (left, right) {
            (UnqualifiedTarget::Alias(a), UnqualifiedTarget::Alias(b)) => {
                let i = choose|i: int| 0 <= i < items.len()
                    && #[trigger] super::alias_in_scope(items[i], file, block, left_name)
                    && items[i] == *a
                    && (forall|j: int| 0 <= j < i ==> !super::alias_in_scope(#[trigger] items[j], file, block, left_name));
                let j = choose|j: int| 0 <= j < items.len()
                    && #[trigger] super::alias_in_scope(items[j], file, block, right_name)
                    && items[j] == *b
                    && (forall|i: int| 0 <= i < j ==> !super::alias_in_scope(#[trigger] items[i], file, block, right_name));
                if i < j {
                    assert(!super::alias_in_scope(items[i], file, block, right_name));
                } else if j < i {
                    assert(!super::alias_in_scope(items[j], file, block, left_name));
                }
            },
            (UnqualifiedTarget::Direct(a), UnqualifiedTarget::Direct(b)) => {
                let table = &self.targets.exports_model().declarations_model();
                let key = NameKey { parent: from, name: left_name };
                let other = NameKey { parent: from, name: right_name };
                match b {
                    AbsoluteTarget::Declaration { source, form } => {
                        same_declaration_key(table, other, key, source, form);
                        direct_targets_agree(table, key, Some(a), Some(b));
                    },
                    AbsoluteTarget::Namespace { key: b, .. } => {
                        match a {
                            AbsoluteTarget::Namespace { key: a, .. } => { assert(key_view(a) == key_view(b)); },
                            AbsoluteTarget::Declaration { source, form } => {
                                same_declaration_key(table, key, other, source, form);
                                assert(declaration_exists(table, other));
                            },
                        }
                    },
                }
            },
            (UnqualifiedTarget::Alias(a), UnqualifiedTarget::Direct(_)) => {
                let i = choose|i: int| 0 <= i < items.len()
                    && #[trigger] super::alias_in_scope(items[i], file, block, left_name) && items[i] == *a;
                assert(!super::alias_in_scope(items[i], file, block, right_name));
            },
            (UnqualifiedTarget::Direct(_), UnqualifiedTarget::Alias(b)) => {
                let i = choose|i: int| 0 <= i < items.len()
                    && #[trigger] super::alias_in_scope(items[i], file, block, right_name) && items[i] == *b;
                assert(!super::alias_in_scope(items[i], file, block, left_name));
            },
        }
    }

    /// 同じスコープと名前で、束縛がある場合とない場合は両立しない。
    pub(super) proof fn unqualified_target_excludes_missing(
        &self, file: usize, block: Option<usize>, from: Option<&str>, bound: &str, missing: &str,
        found: UnqualifiedTarget,
    )
        requires
            bound@ == missing@,
            self.unqualified_binding_matches(file, block, bound, from, Some(found)),
            self.unqualified_binding_matches(file, block, missing, from, None),
        ensures false,
    {
        let table = &self.targets.exports_model().declarations_model();
        let left = NameKey { parent: from, name: bound };
        let right = NameKey { parent: from, name: missing };
        match found {
            UnqualifiedTarget::Alias(item) => {
                let items = self.directives_model();
                let i = choose|i: int| 0 <= i < items.len()
                    && #[trigger] super::alias_in_scope(items[i], file, block, bound) && items[i] == *item;
                assert(!super::alias_in_scope(items[i], file, block, missing));
            },
            UnqualifiedTarget::Direct(AbsoluteTarget::Declaration { source, form }) => {
                same_declaration_key(table, left, right, source, form);
                assert(declaration_exists(table, right));
            },
            UnqualifiedTarget::Direct(AbsoluteTarget::Namespace { introduced_at, .. }) => {
                table.same_namespace_key(left, right, introduced_at);
            },
        }
    }

    /// 同じ参照元と完全修飾キーで独立宣言を参照できるなら、その宣言以外の解決結果は成立しない。
    pub(super) proof fn declaration_resolution_excludes_other_outcomes(
        &self, left: NameKey, right: NameKey, from: Option<&str>, source: &ProjectSource, form: &NamedForm,
        outcome: Result<AbsoluteTarget, AbsoluteResolutionError>,
    )
        requires
            self.can_resolve(),
            key_view(left) == key_view(right),
            has_resolution(&self.targets.exports_model(), left, from, Ok(AbsoluteTarget::Declaration { source, form })),
            has_resolution(&self.targets.exports_model(), right, from, outcome),
        ensures outcome == Ok(AbsoluteTarget::Declaration { source, form }),
    {
        let exports = &self.targets.exports_model();
        let table = &exports.declarations_model();
        exports.same_publication_key(left, right);
        same_declaration_key(table, left, right, source, form);
        assert(declaration_exists(table, right));
        if let Ok(AbsoluteTarget::Declaration { source: other_source, form: other_form }) = outcome {
            self.targets.declarations_cover_project();
            declaration_sites_agree(&self.targets.project_model(), table, right, source, form, other_source, other_form);
        }
    }

    pub(super) proof fn struct_binding_is_struct(
        &self, file: usize, request: ReferenceRequest, from: Option<&str>, kind: AtomKind,
        binding: DefinitionBinding,
    )
        requires
            request.role is StructType,
            self.binding_evidence(file, request, from, kind, Ok(binding)),
        ensures binding matches DefinitionBinding::Declaration { form, .. } && form.head is Struct,
    {
    }

    pub(super) closed spec fn binding_evidence(
        &self, file: usize, site: ReferenceRequest, from: Option<&str>, kind: AtomKind,
        binding: Result<DefinitionBinding, DefinitionReferenceReason>,
    ) -> bool {
        match kind {
            AtomKind::Name => exists|found: Option<UnqualifiedTarget>|
                #[trigger] self.unqualified_binding_matches(file, site.block, site.word, from, found)
                && binding == unqualified_binding(site, found),
            AtomKind::RelativePath => exists|found: Result<RelativeTarget, RelativeResolutionError>|
                #[trigger] self.relative_resolution_matches(file, site.block, site.word, found)
                && relative_binding(site, found, binding),
            AtomKind::AbsolutePath => exists|found: Result<AbsoluteTarget, AbsoluteResolutionError>|
                #[trigger] absolute_resolution_evidence(&self.targets.exports_model(), site.word, from, found)
                && absolute_outcome(site, found, binding),
            _ => false,
        }
    }

    pub(super) fn resolve_scoped_binding(
        &self, file: usize, site: &ReferenceRequest, from: Option<&str>, kind: AtomKind,
    ) -> (binding: Result<DefinitionBinding<'p, 'a>, DefinitionReferenceReason<'p, 'a>>)
        requires
            self.can_resolve(),
            self.scope_matches(file, site.block, Ok(from)),
            bare_atom_kind(site.word.spec_bytes()) == Some(kind),
            kind is Name || kind is RelativePath || kind is AbsolutePath,
        ensures self.binding_evidence(file, *site, from, kind, binding),
    {
        let word = site.word;
        match kind {
            AtomKind::Name => {
                let found = self.lookup_in_scope(file, site.block, from, word);
                match found {
                    Some(UnqualifiedTarget::Alias(directive)) => check_absolute(site, &directive.target),
                    Some(UnqualifiedTarget::Direct(target)) => check_absolute(site, &target),
                    None if matches!(site.role, ReferenceUse::Callee(_)) && word == "nor" => Ok(DefinitionBinding::Nor),
                    None => Err(DefinitionReferenceReason::Missing),
                }
            },
            AtomKind::RelativePath => {
                let found = self.resolve_relative(file, site.block, word);
                proof { self.relative_requires_valid_input(file, site.block, word, from, found); }
                match found {
                    Ok(RelativeTarget::Declaration { source, form }) => check_declaration(site, source, form),
                    Ok(RelativeTarget::Namespace { introduced_at, .. }) => Err(DefinitionReferenceReason::Namespace(introduced_at)),
                    Err(RelativeResolutionError::Private(location)) => Err(DefinitionReferenceReason::Private(location)),
                    Err(RelativeResolutionError::MissingHead) => Err(DefinitionReferenceReason::MissingPrefix),
                    Err(RelativeResolutionError::DeclarationHead { source, form }) =>
                        Err(DefinitionReferenceReason::DeclarationPrefix { source, form }),
                    Err(RelativeResolutionError::Missing) => Err(DefinitionReferenceReason::Missing),
                    Err(RelativeResolutionError::Scope(_) | RelativeResolutionError::InvalidPath) => {
                        proof { assert(false); }
                        unreachable!();
                    }
                }
            },
            AtomKind::AbsolutePath => {
                let found = self.targets.exports().resolve_absolute(word, from);
                match found {
                    Ok(target) => check_absolute(site, &target),
                    Err(AbsoluteResolutionError::Missing) => Err(DefinitionReferenceReason::Missing),
                    Err(AbsoluteResolutionError::Private(location)) => Err(DefinitionReferenceReason::Private(location)),
                    Err(AbsoluteResolutionError::InvalidPath) => {
                        proof { assert(false); }
                        unreachable!();
                    }
                }
            },
            _ => {
                proof { assert(false); }
                unreachable!();
            },
        }
    }

    pub(super) open spec fn position_exists(&self, file: usize, entry: usize, definition: usize, reference: usize) -> bool {
        let circuits = self.targets.project_model().circuits_model();
        &&& file < circuits.len()
        &&& {
            let parsed = &circuits[file as int];
            &&& entry < parsed.entry_ranges@.len()
            &&& definition < definition_count(parsed, entry as int)
            &&& reference < reference_count(parsed, entry as int, definition as int)
        }
    }

    spec fn valid_definition_scope(&self, file: usize, block: Option<usize>) -> bool {
        let circuits = self.targets.project_model().circuits_model();
        &&& file < circuits.len()
        &&& (block matches Some(parent) ==> {
            let names = circuits[file as int].names@;
            exists|i: int| 0 <= i < names.len() && #[trigger] super::is_namespace_block(names[i], parent)
        })
    }

    spec fn positioned_binding(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        site: DefinitionReferenceSite, binding: Result<DefinitionBinding, DefinitionReferenceReason>,
    ) -> bool {
        let project = self.targets.project_model();
        &&& self.position_exists(file, entry, definition, reference)
        &&& file < project.sources_model().len()
        &&& *site.source == project.sources_model()[file as int]
        &&& {
            let parsed = project.circuits_model()[file as int];
            let item = parsed.syntax.entries@[entry as int];
            let definition_index = parsed.entry_ranges@[entry as int].definitions.start + definition;
            let ref_index = parsed.definitions@[definition_index].references.start + reference;
            let reference = parsed.references@[ref_index];
            &&& expression_reference_in_source(site.source.text, parsed.syntax.forms@, reference)
            &&& site.owner == item.head && site.block == item.namespace && site.role == reference.kind
            &&& site.name.span == reference.span
            &&& site.name.word.spec_bytes() == site.source.text.spec_bytes()[reference.span.start as int..reference.span.end as int]
            &&& exists|from: Option<&str>| #[trigger] self.scope_matches(file, site.block, Ok(from))
                && self.binding_evidence(file, site.request_model(), from, parsed.syntax.forms@[reference.form as int]->Atom_kind, binding)
        }
    }

    /// 解決結果と診断が、指定された参照箇所と名前解決規則に対応することを表す。
    pub closed spec fn definition_resolution_evidence(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        result: Result<ResolvedDefinitionReference, DefinitionReferenceError>,
    ) -> bool {
        match result {
            Ok(resolved) => self.positioned_binding(file, entry, definition, reference, resolved.site, Ok(resolved.binding)),
            Err(DefinitionReferenceError::Rejected { site, reason }) =>
                self.positioned_binding(file, entry, definition, reference, site, Err(reason)),
            Err(DefinitionReferenceError::UnknownPosition) => !self.position_exists(file, entry, definition, reference),
        }
    }

    /// 同じ参照位置に対する解決で、基底 NOR と独立宣言が同時に選ばれることはない。
    pub(super) proof fn nor_binding_excludes_declaration(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        builtin: ResolvedDefinitionReference, declaration: ResolvedDefinitionReference,
    )
        requires
            self.can_resolve(),
            self.definition_resolution_evidence(file, entry, definition, reference, Ok(builtin)),
            self.definition_resolution_evidence(file, entry, definition, reference, Ok(declaration)),
            builtin.binding is Nor, declaration.binding is Declaration,
        ensures false,
    {
        let project = self.targets.project_model();
        let parsed = project.circuits_model()[file as int];
        let row = parsed.definitions@[parsed.entry_ranges@[entry as int].definitions.start + definition];
        let indexed = parsed.references@[row.references.start + reference];
        let kind = parsed.syntax.forms@[indexed.form as int]->Atom_kind;
        let lhs = builtin.site.request_model();
        let rhs = declaration.site.request_model();
        let left_scope = choose|from: Option<&str>| #[trigger] self.scope_matches(file, builtin.site.block, Ok(from))
            && self.binding_evidence(file, lhs, from, kind, Ok(builtin.binding));
        let right_scope = choose|from: Option<&str>| #[trigger] self.scope_matches(file, declaration.site.block, Ok(from))
            && self.binding_evidence(file, rhs, from, kind, Ok(declaration.binding));
        assert(kind is Name);
        self.relative_scope_agrees(file, lhs.block, left_scope, right_scope);
        encode_utf8_decode_utf8(lhs.word@);
        encode_utf8_decode_utf8(rhs.word@);
        assert(lhs.word@ == rhs.word@);
        let bound = choose|found: Option<UnqualifiedTarget>|
            #[trigger] self.unqualified_binding_matches(file, rhs.block, rhs.word, right_scope, found)
                && Ok(declaration.binding) == unqualified_binding(rhs, found);
        assert(self.unqualified_binding_matches(file, lhs.block, lhs.word, left_scope, None));
        self.unqualified_target_excludes_missing(file, lhs.block, left_scope, rhs.word, lhs.word, bound->Some_0);
    }

    pub(super) proof fn valid_position_is_not_unknown(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
    )
        requires
            self.position_exists(file, entry, definition, reference),
            self.definition_resolution_evidence(file, entry, definition, reference, Err(DefinitionReferenceError::UnknownPosition)),
        ensures false,
    {
    }

    pub(super) proof fn binding_declaration_origin(
        &self, file: usize, request: ReferenceRequest, from: Option<&str>, kind: AtomKind,
        source: &ProjectSource, form: &NamedForm,
    )
        requires self.binding_evidence(file, request, from, kind, Ok(DefinitionBinding::Declaration { source, form })),
        ensures
            accepts_declaration(request.role, form.head),
            self.targets.exports_model().declarations_model().declaration_at(form_key(*form), source, form),
    {
        let table = &self.targets.exports_model();
        let binding = Ok(DefinitionBinding::Declaration { source, form });
        match kind {
            AtomKind::Name => {
                let found = choose|found: Option<UnqualifiedTarget>|
                    #[trigger] self.unqualified_binding_matches(file, request.block, request.word, from, found)
                    && binding == unqualified_binding(request, found);
                match found {
                    Some(UnqualifiedTarget::Alias(item)) =>
                        absolute_declaration_evidence(table, item.site.reference.word, item.site.namespace, source, form),
                    Some(UnqualifiedTarget::Direct(_)) =>
                        declaration_key_evidence(&table.declarations_model(),
                            NameKey { parent: from, name: request.word }, source, form),
                    None => { assert(false); },
                }
            },
            AtomKind::RelativePath => {
                let found = choose|found: Result<RelativeTarget, RelativeResolutionError>|
                    #[trigger] self.relative_resolution_matches(file, request.block, request.word, found)
                    && relative_binding(request, found, binding);
                self.relative_declaration_evidence(file, request.block, request.word, source, form);
            },
            AtomKind::AbsolutePath => {
                let found = choose|found: Result<AbsoluteTarget, AbsoluteResolutionError>|
                    #[trigger] absolute_resolution_evidence(table, request.word, from, found)
                    && absolute_outcome(request, found, binding);
                absolute_declaration_evidence(table, request.word, from, source, form);
            },
            _ => { assert(false); },
        }
    }

    /// 同じ構造体型の参照について、宣言元のソースと構文項目は一意に定まる。
    pub(super) proof fn struct_bindings_agree(
        &self, file: usize, left_request: ReferenceRequest, right_request: ReferenceRequest,
        left_from: Option<&str>, right_from: Option<&str>, kind: AtomKind,
        left_source: &ProjectSource, left_form: &NamedForm, right_source: &ProjectSource, right_form: &NamedForm,
    )
        requires
            self.can_resolve(),
            left_request.role is StructType, right_request.role is StructType,
            left_request.block == right_request.block, left_request.word@ == right_request.word@,
            left_from == right_from,
            self.binding_evidence(file, left_request, left_from, kind,
                Ok(DefinitionBinding::Declaration { source: left_source, form: left_form })),
            self.binding_evidence(file, right_request, right_from, kind,
                Ok(DefinitionBinding::Declaration { source: right_source, form: right_form })),
        ensures left_source == right_source, left_form == right_form,
    {
        let left = Ok(DefinitionBinding::Declaration { source: left_source, form: left_form });
        let right = Ok(DefinitionBinding::Declaration { source: right_source, form: right_form });
        let table = &self.targets.exports_model().declarations_model();
        let left_key = form_key(*left_form);
        let right_key = form_key(*right_form);
        match kind {
            AtomKind::Name => {
                let a = choose|found: Option<UnqualifiedTarget>|
                    #[trigger] self.unqualified_binding_matches(file, left_request.block, left_request.word, left_from, found)
                        && left == unqualified_binding(left_request, found);
                let b = choose|found: Option<UnqualifiedTarget>|
                    #[trigger] self.unqualified_binding_matches(file, right_request.block, right_request.word, right_from, found)
                        && right == unqualified_binding(right_request, found);
                self.unqualified_targets_agree(file, left_request.block, left_from,
                    left_request.word, right_request.word, a->Some_0, b->Some_0);
            },
            AtomKind::RelativePath => self.relative_declaration_resolution_agrees(
                file, left_request.block, left_request.word, right_request.word, left_source, left_form,
                Ok(RelativeTarget::Declaration { source: right_source, form: right_form })),
            AtomKind::AbsolutePath => {
                let exports = &self.targets.exports_model();
                let a = Ok(AbsoluteTarget::Declaration { source: left_source, form: left_form });
                let b = Ok(AbsoluteTarget::Declaration { source: right_source, form: right_form });
                let ak = choose|key: NameKey| #[trigger] absolute_path_parts(left_request.word, key.parent, key.name)
                    && has_resolution(exports, key, left_from, a);
                let bk = choose|key: NameKey| #[trigger] absolute_path_parts(right_request.word, key.parent, key.name)
                    && has_resolution(exports, key, right_from, b);
                absolute_path_parts_agree(left_request.word, ak.parent, ak.name, right_request.word, bk.parent, bk.name);
                declaration_key_evidence(table, ak, left_source, left_form);
                declaration_key_evidence(table, bk, right_source, right_form);
            },
            _ => { assert(false); },
        }
        assert(key_view(left_key) == key_view(right_key));
        self.binding_declaration_origin(file, left_request, left_from, kind, left_source, left_form);
        self.binding_declaration_origin(file, right_request, right_from, kind, right_source, right_form);
        same_declaration_key(table, right_key, left_key, right_source, right_form);
        self.targets.declarations_cover_project();
        declaration_sites_agree(&self.targets.project_model(), table, left_key, left_source, left_form, right_source, right_form);
    }

    /// 同じスコープと構造体型名で、宣言への解決成功と失敗は両立しない。
    pub(super) proof fn struct_binding_excludes_error(
        &self, file: usize, success: ReferenceRequest, failure: ReferenceRequest,
        success_from: Option<&str>, failure_from: Option<&str>, kind: AtomKind,
        source: &ProjectSource, form: &NamedForm, reason: DefinitionReferenceReason,
    )
        requires
            self.can_resolve(),
            success.role is StructType, failure.role is StructType,
            success.block == failure.block, success.word@ == failure.word@,
            success_from == failure_from,
            self.binding_evidence(file, success, success_from, kind, Ok(DefinitionBinding::Declaration { source, form })),
            self.binding_evidence(file, failure, failure_from, kind, Err(reason)),
        ensures false,
    {
        let binding = DefinitionBinding::Declaration { source, form };
        self.struct_binding_is_struct(file, success, success_from, kind, binding);
        let exports = &self.targets.exports_model();
        let table = &exports.declarations_model();
        match kind {
            AtomKind::Name => {
                let good = choose|found: Option<UnqualifiedTarget>|
                    #[trigger] self.unqualified_binding_matches(file, success.block, success.word, success_from, found)
                        && Ok(binding) == unqualified_binding(success, found);
                let bad = choose|found: Option<UnqualifiedTarget>|
                    #[trigger] self.unqualified_binding_matches(file, failure.block, failure.word, failure_from, found)
                        && Err(reason) == unqualified_binding(failure, found);
                let a = good->Some_0;
                if let Some(b) = bad {
                    self.unqualified_targets_agree(file, success.block, success_from, success.word, failure.word, a, b);
                    let target = unqualified_target(b);
                    let other_source = target->Declaration_source;
                    let other_form = target->Declaration_form;
                    let left_key = form_key(*form);
                    let right_key = form_key(*other_form);
                    self.binding_declaration_origin(file, success, success_from, kind, source, form);
                    match b {
                        UnqualifiedTarget::Alias(item) => absolute_declaration_evidence(exports,
                            item.site.reference.word, item.site.namespace, other_source, other_form),
                        UnqualifiedTarget::Direct(_) => declaration_key_evidence(table,
                            NameKey { parent: failure_from, name: failure.word }, other_source, other_form),
                    }
                    same_declaration_key(table, right_key, left_key, other_source, other_form);
                    self.targets.declarations_cover_project();
                    declaration_sites_agree(&self.targets.project_model(), table,
                        left_key, source, form, other_source, other_form);
                } else {
                    self.unqualified_target_excludes_missing(file, success.block, success_from, success.word, failure.word, a);
                }
            },
            AtomKind::RelativePath => {
                let bad = choose|found: Result<RelativeTarget, RelativeResolutionError>|
                    #[trigger] self.relative_resolution_matches(file, failure.block, failure.word, found)
                        && relative_binding(failure, found, Err(reason));
                self.relative_declaration_resolution_agrees(file, success.block, success.word, failure.word, source, form, bad);
            },
            AtomKind::AbsolutePath => {
                let bad = choose|found: Result<AbsoluteTarget, AbsoluteResolutionError>|
                    #[trigger] absolute_resolution_evidence(exports, failure.word, failure_from, found)
                        && absolute_outcome(failure, found, Err(reason));
                let a = choose|key: NameKey| #[trigger] absolute_path_parts(success.word, key.parent, key.name)
                    && has_resolution(exports, key, success_from, Ok(AbsoluteTarget::Declaration { source, form }));
                let b = choose|key: NameKey| #[trigger] absolute_path_parts(failure.word, key.parent, key.name)
                    && has_resolution(exports, key, failure_from, bad);
                absolute_path_parts_agree(success.word, a.parent, a.name, failure.word, b.parent, b.name);
                self.declaration_resolution_excludes_other_outcomes(a, b, success_from, source, form, bad);
            },
            _ => {},
        }
    }

    pub(super) proof fn resolved_func_declaration(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
        result: ResolvedDefinitionReference, source: &ProjectSource, form: &NamedForm,
    )
        requires
            self.definition_resolution_evidence(file, entry, definition, reference, Ok(result)),
            ({
                let parsed = self.targets.project_model().circuits_model()[file as int];
                let def = parsed.entry_ranges@[entry as int].definitions.start + definition;
                parsed.syntax.entries@[entry as int].head is Func
                    && parsed.references@[parsed.definitions@[def].references.start + reference].kind is Callee
            }),
            result.binding == (DefinitionBinding::Declaration { source, form }),
        ensures
            form.head is Func,
            self.targets.exports_model().declarations_model().declaration_at(form_key(*form), source, form),
    {
        let project = self.targets.project_model();
        let parsed = project.circuits_model()[file as int];
        let def = parsed.entry_ranges@[entry as int].definitions.start + definition;
        let indexed = parsed.references@[parsed.definitions@[def].references.start + reference];
        let kind = parsed.syntax.forms@[indexed.form as int]->Atom_kind;
        let from = choose|from: Option<&str>| #[trigger] self.scope_matches(file, result.site.block, Ok(from))
            && self.binding_evidence(file, result.site.request_model(), from, kind, Ok(result.binding));
        self.binding_declaration_origin(file, result.site.request_model(), from, kind, source, form);
    }

    /// 定義の右辺にある回路名または型名を、その定義のスコープで解決する。
    ///
    /// `file` はソース一覧、`entry` は各ファイルの厳格索引の添字。
    /// `definition` は索引項目内、`reference` は定義内の相対添字。
    /// `nor` は無修飾の呼び出しで同名の束縛がない場合に選ぶ。基底の指定回数はプロジェクト全体の検査で扱う。
    ///
    /// # Errors
    ///
    /// 添字が範囲外の場合は位置のエラーを返す。名前の解決や用途の検査で失敗した場合は、参照名の範囲と理由を返す。
    pub fn resolve_definition_reference(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
    ) -> (result: Result<ResolvedDefinitionReference<'p, 'a>, DefinitionReferenceError<'p, 'a>>)
        requires self.can_resolve(),
        ensures self.definition_resolution_evidence(file, entry, definition, reference, result),
    {
        let project = self.targets.project();
        let circuits = project.circuits();
        if file >= circuits.len() {
            return Err(DefinitionReferenceError::UnknownPosition);
        }
        let parsed = &circuits[file];
        if entry >= parsed.entry_ranges.len() {
            return Err(DefinitionReferenceError::UnknownPosition);
        }
        let source = &project.sources()[file];
        proof {
            parsed_index_evidence(*source, *parsed);
            build_entry_ranges_evidence(source.text, &parsed.build_model(), entry as int);
        }
        let defs = &parsed.entry_ranges[entry].definitions;
        if definition >= defs.end - defs.start {
            return Err(DefinitionReferenceError::UnknownPosition);
        }
        let _definition_count = parsed.definitions.len();
        assert(defs.start + definition < _definition_count);
        let definition_index = defs.start + definition;
        let refs = &parsed.definitions[definition_index].references;
        proof {
            build_definition_scope_evidence(source.text, &parsed.build_model(), entry as int, definition_index as int);
        }
        if reference >= refs.end - refs.start {
            return Err(DefinitionReferenceError::UnknownPosition);
        }
        let _reference_count = parsed.references.len();
        assert(refs.start + reference < _reference_count);
        let owner = &parsed.syntax.entries[entry];
        let indexed = &parsed.references[refs.start + reference];
        let forms = &parsed.syntax.forms;
        proof {
            if let Some(parent) = owner.namespace {
                namespace_name_evidence(source.text, forms@, parsed.syntax.entries@, parsed.names@, owner.form as int, parent);
                let i = choose|i: int| 0 <= i < parsed.names@.len() && (#[trigger] parsed.names@[i]).form == parent
                    && parsed.names@[i].head is Namespace && parsed.names@[i].block is None;
                assert(super::is_namespace_block(parsed.names@[i], parent));
            }
            assert(self.valid_definition_scope(file, owner.namespace));
            assert(expression_reference_in_source(source.text, forms@, *indexed));
        }
        let Form::Atom { kind: atom_kind, .. } = &forms[indexed.form] else {
            proof { assert(false); }
            unreachable!();
        };
        let (word, span) = read_indexed_atom(source.text, forms, indexed.form);
        let site = DefinitionReferenceSite {
            source, name: NameSite { word, span }, role: indexed.kind, owner: owner.head, block: owner.namespace,
        };
        let Ok(from) = self.scope_namespace(file, site.block) else {
            proof { assert(false); }
            unreachable!();
        };
        match self.resolve_scoped_binding(file, &site.request(), from, *atom_kind) {
            Ok(binding) => Ok(ResolvedDefinitionReference { site, binding }),
            Err(reason) => Err(DefinitionReferenceError::Rejected { site, reason }),
        }
    }
}

} // verus!
