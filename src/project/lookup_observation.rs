//! 名前検索で読んだ候補を、解析スナップショットから独立した値に写す。

use alloc::vec::Vec;
use core::ops::Range;
use super::{AbsoluteLookup, AbsoluteTarget, ProjectSource, ReferenceScopeError, UnqualifiedTarget, UseAliases};
use crate::syntax::circuit::Head;
use vstd::{prelude::*, slice::slice_to_vec};
#[cfg(verus_only)]
use super::path::component_bytes;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 診断と定義位置の照合に使う仮想ファイル識別子と UTF-8 バイト範囲。
///
/// 保存した範囲を表示するときは、現在の解析スナップショットで照合する。
#[derive(Debug, Eq, PartialEq)]
pub struct LookupLocation {
    /// 正規化したファイル識別子をルートから並べた UTF-8 成分列。
    pub file: Vec<Vec<u8>>,
    /// 参照先の名前が占める半開バイト範囲。
    pub span: Range<usize>,
}

/// 名前検索が選んだ宣言または名前空間の観測値。
#[derive(Debug, Eq, PartialEq)]
pub enum LookupTarget {
    /// 独立宣言。宣言の種別は呼び出しや型参照で使えるかの判定に使う。
    Declaration {
        /// 宣言の種別。
        head: Head,
        /// 宣言の名前がある位置。
        location: LookupLocation,
    },
    /// 明示された、または完全修飾名の途中にある名前空間。
    Namespace {
        /// 親の完全修飾名の UTF-8 本文。ルート直下なら `None`。
        parent: Option<Vec<u8>>,
        /// 末尾の名前の UTF-8 本文。
        name: Vec<u8>,
        /// この名前空間の導入位置。
        introduced_at: LookupLocation,
    },
}

/// 完全修飾名の候補と参照元からの可視性。相対名の末尾の検索にも使う。
#[derive(Debug, Eq, PartialEq)]
pub struct OwnedAbsoluteLookup {
    /// 候補の不在は `None`。
    pub target: Option<LookupTarget>,
    /// 独立宣言が参照元から見える。名前空間と候補の不在では偽。
    pub visible_declaration: bool,
}

/// 無修飾名または相対名の先頭の検索で選んだ束縛。
#[derive(Debug, Eq, PartialEq)]
pub enum OwnedUnqualifiedLookup {
    /// このスコープに別名も直接の候補もない。
    Missing,
    /// 別名がなく、現在の名前空間に直接の候補がある。
    Direct(LookupTarget),
    /// 現在のブロックで最初に指定した別名が選ばれた。
    Alias {
        /// 選ばれた別名の指定位置。
        directive: LookupLocation,
        /// 別名が参照する宣言または名前空間。
        target: LookupTarget,
    },
}

/// 保存した位置を仮想ファイル識別子の成分列と範囲で表す。
pub open spec fn lookup_location_model(location: LookupLocation) -> (Seq<Seq<u8>>, Range<usize>) {
    (location.file@.map_values(|part: Vec<u8>| part@), location.span)
}

pub(super) fn capture_location(source: &ProjectSource, span: &Range<usize>) -> (out: LookupLocation)
    ensures lookup_location_model(out) == (source.virtual_path_model().components_model(), *span),
{
    let parts = source.virtual_path().components();
    let mut file: Vec<Vec<u8>> = Vec::with_capacity(parts.len());
    let mut index = 0;
    while index < parts.len()
        invariant
            component_bytes(parts@) == source.virtual_path_model().components_model(),
            index == file@.len(),
            index <= parts@.len(),
            forall|i: int| 0 <= i < index ==> (#[trigger] file@[i])@ == parts@[i].spec_bytes(),
        decreases parts@.len() - index,
    {
        let bytes = slice_to_vec(parts[index].as_bytes());
        file.push(bytes);
        index += 1;
    }
    assert(file@.map_values(|part: Vec<u8>| part@) =~= component_bytes(parts@));
    LookupLocation { file, span: span.start..span.end }
}

// 所有済みの名前成分を、現在の本文を借りたまま照合する。
fn bytes_match(saved: &[u8], current: &str) -> (same: bool)
    ensures same == (saved@ == current.spec_bytes()),
{
    let bytes = current.as_bytes();
    let same = saved == bytes;
    if same { assert(saved@ =~= bytes@); }
    same
}

pub(super) fn lookup_location_matches(saved: &LookupLocation, source: &ProjectSource, span: &Range<usize>) -> (same: bool)
    ensures same == (lookup_location_model(*saved) == (source.virtual_path_model().components_model(), *span)),
{
    if saved.span.start != span.start || saved.span.end != span.end {
        return false;
    }
    let parts = source.virtual_path().components();
    if saved.file.len() != parts.len() {
        assert(lookup_location_model(*saved).0.len() == saved.file@.len());
        assert(component_bytes(parts@).len() == parts@.len());
        return false;
    }
    let mut index = 0;
    while index < parts.len()
        invariant
            saved.span == *span,
            saved.file@.len() == parts@.len(),
            component_bytes(parts@) == source.virtual_path_model().components_model(),
            index <= parts@.len(),
            forall|i: int| 0 <= i < index ==> (#[trigger] saved.file@[i])@ == parts@[i].spec_bytes(),
        decreases parts@.len() - index,
    {
        if !bytes_match(saved.file[index].as_slice(), parts[index]) {
            assert(saved.file@.map_values(|part: Vec<u8>| part@)[index as int] != component_bytes(parts@)[index as int]);
            return false;
        }
        index += 1;
    }
    assert(saved.file@.map_values(|part: Vec<u8>| part@) =~= component_bytes(parts@));
    true
}

// フォーム種別の実行時比較を、その直和型の等値につなぐ。
pub(super) fn head_matches(left: Head, right: Head) -> (same: bool)
    ensures same == (left == right),
{
    matches!((left, right),
        (Head::Using, Head::Using) | (Head::Namespace, Head::Namespace) |
        (Head::Use, Head::Use) | (Head::Export, Head::Export) |
        (Head::Func, Head::Func) | (Head::Module, Head::Module) |
        (Head::ModulePart, Head::ModulePart) | (Head::Struct, Head::Struct) |
        (Head::Latch, Head::Latch) | (Head::Memory, Head::Memory) | (Head::Test, Head::Test))
}

fn lookup_target_matches(saved: &LookupTarget, target: &AbsoluteTarget) -> (same: bool)
    ensures same == lookup_target_model(*saved, *target),
{
    match (saved, target) {
        (LookupTarget::Declaration { head, location }, AbsoluteTarget::Declaration { source, form }) =>
            head_matches(*head, form.head) && lookup_location_matches(location, source, &form.name.span),
        (
            LookupTarget::Namespace { parent, name, introduced_at },
            AbsoluteTarget::Namespace { key, introduced_at: current },
        ) => {
            let same_parent = match (parent, key.parent) {
                (Some(saved), Some(word)) => bytes_match(saved.as_slice(), word),
                (None, None) => true,
                _ => false,
            };
            same_parent && bytes_match(name.as_slice(), key.name)
                && lookup_location_matches(introduced_at, current.source, &current.span)
        },
        _ => false,
    }
}

/// 保存した候補が構文索引の候補と同じ種別、名前、位置を持つことを表す。
pub open spec fn lookup_target_model(out: LookupTarget, target: AbsoluteTarget) -> bool {
    match (out, target) {
        (LookupTarget::Declaration { head, location }, AbsoluteTarget::Declaration { source, form }) =>
            head == form.head && lookup_location_model(location) == (source.virtual_path_model().components_model(), form.name.span),
        (LookupTarget::Namespace { parent, name, introduced_at }, AbsoluteTarget::Namespace { key, introduced_at: original }) =>
            (match parent { Some(bytes) => Some(bytes@), None => None })
                == (match key.parent { Some(word) => Some(word.spec_bytes()), None => None })
                && name@ == key.name.spec_bytes()
                && lookup_location_model(introduced_at) == (original.source.virtual_path_model().components_model(), original.span),
        _ => false,
    }
}

fn capture_target(target: &AbsoluteTarget) -> (out: LookupTarget)
    ensures lookup_target_model(out, *target),
{
    match target {
        AbsoluteTarget::Declaration { source, form } => LookupTarget::Declaration {
            head: form.head, location: capture_location(source, &form.name.span),
        },
        AbsoluteTarget::Namespace { key, introduced_at } => {
            let parent = match key.parent {
                Some(word) => Some(slice_to_vec(word.as_bytes())),
                None => None,
            };
            LookupTarget::Namespace {
                parent, name: slice_to_vec(key.name.as_bytes()),
                introduced_at: capture_location(introduced_at.source, &introduced_at.span),
            }
        },
    }
}

/// 完全修飾名の検索で保存した候補と可視性を、同じ検索の観測値に結び付ける。
pub open spec fn owned_absolute_model(out: OwnedAbsoluteLookup, lookup: AbsoluteLookup) -> bool {
    &&& out.visible_declaration == lookup.visible_model()
    &&& match (out.target, lookup.target_model()) {
        (Some(out), Some(target)) => lookup_target_model(out, target),
        (None, None) => true,
        _ => false,
    }
}

impl AbsoluteLookup<'_, '_, '_> {
    /// 現在の候補と可視性を、保存済みの観測と割り当てなしで比較する。
    pub fn matches_owned_observation(&self, saved: &OwnedAbsoluteLookup) -> (same: bool)
        ensures same == owned_absolute_model(*saved, *self),
    {
        if self.is_visible_declaration() != saved.visible_declaration {
            return false;
        }
        match (&saved.target, self.target()) {
            (Some(saved), Some(current)) => lookup_target_matches(saved, current),
            (None, None) => true,
            _ => false,
        }
    }

    /// 完全修飾名の検索で観測した候補と可視性を、他の版と照合できる値に写す。
    pub fn owned_observation(&self) -> (out: OwnedAbsoluteLookup)
        ensures owned_absolute_model(out, *self),
    {
        let target = match self.target() {
            Some(target) => Some(capture_target(target)),
            None => None,
        };
        OwnedAbsoluteLookup { target, visible_declaration: self.is_visible_declaration() }
    }
}

/// 保存した無修飾名の観測値を、候補の不在、直接の候補、別名指定に結び付ける。
pub open spec fn owned_unqualified_model(out: OwnedUnqualifiedLookup, resolved: Option<UnqualifiedTarget>) -> bool {
    match (out, resolved) {
        (OwnedUnqualifiedLookup::Missing, None) => true,
        (OwnedUnqualifiedLookup::Direct(out), Some(UnqualifiedTarget::Direct(target))) => lookup_target_model(out, target),
        (OwnedUnqualifiedLookup::Alias { directive, target }, Some(UnqualifiedTarget::Alias(item))) =>
            lookup_location_model(directive)
                == (item.site_model().source.virtual_path_model().components_model(), item.site_model().alias.span)
                && lookup_target_model(target, item.target_model()),
        _ => false,
    }
}

pub(super) fn capture_unqualified(resolved: &Option<UnqualifiedTarget>) -> (out: OwnedUnqualifiedLookup)
    ensures owned_unqualified_model(out, *resolved),
{
    match resolved {
        None => OwnedUnqualifiedLookup::Missing,
        Some(UnqualifiedTarget::Direct(target)) => OwnedUnqualifiedLookup::Direct(capture_target(target)),
        Some(UnqualifiedTarget::Alias(item)) => {
            let site = item.site();
            OwnedUnqualifiedLookup::Alias {
                directive: capture_location(site.source, &site.alias.span),
                target: capture_target(item.target()),
            }
        },
    }
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    /// 無修飾名の検索で確定する束縛を、他の版と照合できる値に写す。
    ///
    /// 相対名では先頭の成分を `name` に渡す。別名の選択、直接の候補、不在を区別する。
    ///
    /// # Errors
    ///
    /// ファイルまたは名前空間ブロックが解析スナップショットに存在しないときは診断を返す。
    pub fn observe_unqualified(&self, file: usize, block: Option<usize>, name: &str)
        -> (out: Result<OwnedUnqualifiedLookup, ReferenceScopeError>)
        requires self.can_resolve(),
        ensures match out {
            Ok(out) => exists|target: Option<UnqualifiedTarget>|
                #[trigger] self.unqualified_resolution_matches(file, block, name, Ok(target))
                && owned_unqualified_model(out, target),
            Err(error) => self.unqualified_resolution_matches(file, block, name, Err(error)),
        },
    {
        let resolved = self.resolve_unqualified(file, block, name)?;
        let out = capture_unqualified(&resolved);
        assert(owned_unqualified_model(out, resolved));
        Ok(out)
    }
}

} // verus!
