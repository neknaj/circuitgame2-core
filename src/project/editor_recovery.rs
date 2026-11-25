//! 回復後も確認できる宣言と名前空間を、元のソースに結び付ける。

use super::declarations::defines_binding;
#[cfg(verus_only)]
use super::declarations::named_binding;
use super::{LocatedName, NameKey, ProjectSource, SourceKind};
#[cfg(verus_only)]
use super::source_kind_of;
use crate::syntax::circuit::{Head, RecoveredNamePosition, RecoveredNames, recover_circuit_names};
#[cfg(verus_only)]
use crate::syntax::circuit::RecoveredName;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::is_char_boundary;

verus! {

/// 元の回路フォームで確認できた宣言または名前空間。
#[derive(Debug)]
pub struct ObservedCircuitBinding<'p, 'a> {
    /// 宣言名または名前空間パスが現れたファイルとバイト範囲。
    pub location: LocatedName<'p, 'a>,
    /// 宣言の照合キー、または名前空間のパス。
    pub kind: ObservedCircuitBindingKind<'a>,
}

/// 回復解析で確認できた名前の種類。
#[derive(Debug)]
pub enum ObservedCircuitBindingKind<'a> {
    /// 独立した回路宣言。
    Declaration {
        /// 元のフォームの種別。
        head: Head,
        /// 所属する名前空間と宣言名。
        key: NameKey<'a>,
    },
    /// 元のフォームに書かれた名前空間。パスはルートからの全成分を含む。
    Namespace(&'a str),
}

/// 回路ソースと、そのファイルから回復した名前。
pub struct CircuitEditorFile<'p, 'a> {
    source: &'p ProjectSource<'a>,
    names: RecoveredNames<'a>,
}

spec fn observed_binding<'p, 'a>(
    source: &'p ProjectSource<'a>, name: RecoveredName<'a>,
) -> Option<ObservedCircuitBinding<'p, 'a>> {
    if !named_binding(name.head) {
        None
    } else {
        Some(ObservedCircuitBinding {
            location: LocatedName { source, span: name.name.span },
            kind: if name.head is Namespace {
                ObservedCircuitBindingKind::Namespace(name.name.word)
            } else {
                let parent = match name.namespace {
                    Some(site) => Some(site.word),
                    None => None,
                };
                ObservedCircuitBindingKind::Declaration {
                    head: name.head,
                    key: NameKey { parent, name: name.name.word },
                }
            },
        })
    }
}

impl<'p, 'a> CircuitEditorFile<'p, 'a> {
    /// 解析に用いたファイルを表す。
    pub closed spec fn source_model(&self) -> &'p ProjectSource<'a> {
        self.source
    }

    /// ファイルの本文と名前の回復結果が対応することを表す。
    pub closed spec fn valid(&self) -> bool {
        circuit_editor_source(self.source) && self.names.valid()
            && self.names.source_model() == self.source.text_model()
    }

    #[verifier::type_invariant]
    spec fn source_matches_names(&self) -> bool {
        self.valid()
    }

    /// 解析に用いたファイル識別子、文書バージョン、本文を返す。
    pub fn source(&self) -> (source: &'p ProjectSource<'a>)
        ensures source == self.source_model(),
    {
        self.source
    }

    /// 元の本文から得た構文の回復結果を表す。
    pub closed spec fn recovered_names_model(&self) -> &RecoveredNames<'a> {
        &self.names
    }

    /// 元のフォームの名前を選び、診断と修復記録を参照するための回復結果を返す。
    pub fn recovered_names(&self) -> (names: &RecoveredNames<'a>)
        ensures
            names == self.recovered_names_model(),
            names.valid(), names.source_model() == self.source_model().text_model(),
    {
        proof { use_type_invariant(self); }
        &self.names
    }

    /// 選んだフォームの名前と、回復後に確認できる宣言または名前空間との対応を表す。
    pub closed spec fn binding_matches(
        &self, position: RecoveredNamePosition, binding: Option<ObservedCircuitBinding<'p, 'a>>,
    ) -> bool {
        exists|name: Option<RecoveredName<'a>>| #[trigger] self.names.name_matches(position, name)
            && binding == match name {
                Some(name) => observed_binding(self.source, name),
                None => None,
            }
    }

    /// 回復後に確認できた宣言の元フォームを、名前の回復結果から特定する。
    pub proof fn observed_binding_origin(
        &self, position: RecoveredNamePosition, binding: ObservedCircuitBinding<'p, 'a>,
    )
        requires self.binding_matches(position, Some(binding)),
        ensures exists|name: RecoveredName<'a>|
            #[trigger] self.recovered_names_model().name_matches(position, Some(name))
            && binding.location.source == self.source_model()
            && binding.location.span == name.name.span
            && match binding.kind {
                ObservedCircuitBindingKind::Declaration { head, key } => head == name.head
                    && key.name == name.name.word
                    && key.parent == match name.namespace {
                        Some(parent) => Some(parent.word),
                        None => None,
                    },
                ObservedCircuitBindingKind::Namespace(path) => name.head is Namespace && path == name.name.word,
            },
    {
        let candidate = choose|name: Option<RecoveredName<'a>>| #[trigger] self.names.name_matches(position, name)
            && Some(binding) == match name {
                Some(name) => observed_binding(self.source, name),
                None => None,
            };
        assert(candidate.is_some());
        let name = candidate->Some_0;
        assert(candidate == Some(name));
        assert(self.recovered_names_model().name_matches(position, Some(name)));
        assert(Some(binding) == observed_binding(self.source, name));
    }

    /// 選んだ元フォームの宣言または名前空間を返す。
    ///
    /// 対象外の位置やフォームでは `None` を返す。`module-part` の対象名は独立宣言に含めない。
    /// この結果から確認できるのはフォームの出現であり、名前の一意性や可視性の判定には全体の名前解決が必要。
    pub fn observed_binding_at(
        &self, position: RecoveredNamePosition,
    ) -> (binding: Option<ObservedCircuitBinding<'p, 'a>>)
        ensures
            self.binding_matches(position, binding),
            binding matches Some(binding) ==> {
                let bytes = self.source_model().text_model().spec_bytes();
                let span = binding.location.span;
                let word = match binding.kind {
                    ObservedCircuitBindingKind::Declaration { key, .. } => key.name,
                    ObservedCircuitBindingKind::Namespace(path) => path,
                };
                &&& binding.location.source == self.source_model()
                &&& span.start < span.end <= bytes.len()
                &&& is_char_boundary(bytes, span.start as int) && is_char_boundary(bytes, span.end as int)
                &&& word.spec_bytes() == bytes[span.start as int..span.end as int]
            },
    {
        proof { use_type_invariant(self); }
        let result = self.names.name_at(position);
        let Some(name) = result else {
            return None;
        };
        if !defines_binding(name.head) {
            return None;
        }
        proof { self.names.name_uses_source_ranges(position, name); }
        let kind = if matches!(name.head, Head::Namespace) {
            ObservedCircuitBindingKind::Namespace(name.name.word)
        } else {
            let parent = match name.namespace {
                Some(site) => Some(site.word),
                None => None,
            };
            ObservedCircuitBindingKind::Declaration {
                head: name.head,
                key: NameKey { parent, name: name.name.word },
            }
        };
        Some(ObservedCircuitBinding {
            location: LocatedName { source: self.source, span: name.name.span },
            kind,
        })
    }
}

/// 元のソーススナップショットに回路フォームの回復結果を結び付ける。
///
/// 回路言語のファイルを解析する。NCG2M のファイルでは `None` を返す。
pub fn inspect_circuit_file<'p, 'a>(
    source: &'p ProjectSource<'a>,
) -> (file: Option<CircuitEditorFile<'p, 'a>>)
    ensures
        file.is_some() <==> circuit_editor_source(source),
        file matches Some(file) ==> file.valid() && file.source_model() == source,
{
    if !matches!(source.kind, SourceKind::Circuit)
        || !matches!(source.id.source_kind(), Some(SourceKind::Circuit))
    {
        return None;
    }
    let names = recover_circuit_names(source.text());
    Some(CircuitEditorFile { source, names })
}

/// 回路フォームの回復解析を適用する言語を表す。
pub closed spec fn circuit_editor_source(source: &ProjectSource) -> bool {
    source.kind is Circuit && source_kind_of(source.id.components_model()) is Some &&
        source_kind_of(source.id.components_model())->Some_0 is Circuit
}

} // verus!
