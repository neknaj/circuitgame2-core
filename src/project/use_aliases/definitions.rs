//! 定義の右辺にある名前を、参照元のスコープと用途に従って解決する。

use super::{RelativeResolutionError, RelativeTarget, UnqualifiedTarget, UseAliases};
#[cfg(verus_only)]
use crate::project::absolute_resolution_evidence;
#[cfg(verus_only)]
use crate::project::circuits::parsed_index_evidence;
use crate::project::circuits::read_indexed_atom;
use crate::project::{AbsoluteResolutionError, AbsoluteTarget, LocatedName, ProjectSource};
#[cfg(verus_only)]
use crate::syntax::bare_atom_kind;
use crate::syntax::circuit::{ExpressionReferenceKind, Head, NameSite, NamedForm};
#[cfg(verus_only)]
use crate::syntax::circuit::{
    NamedBuildCircuit, build_definition_scope_evidence, build_entry_ranges_evidence,
    expression_reference_in_source, namespace_name_evidence,
};
use crate::syntax::{AtomKind, Form};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

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

spec fn accepts_declaration(role: ReferenceUse, target: Head) -> bool {
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

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
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

    pub(super) proof fn valid_position_is_not_unknown(
        &self, file: usize, entry: usize, definition: usize, reference: usize,
    )
        requires
            self.position_exists(file, entry, definition, reference),
            self.definition_resolution_evidence(file, entry, definition, reference, Err(DefinitionReferenceError::UnknownPosition)),
        ensures false,
    {
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
