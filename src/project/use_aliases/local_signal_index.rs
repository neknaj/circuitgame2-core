//! 回路本体の信号と駆動元を対応付ける索引。

use super::OutputDriver;
use crate::ncg2m::call_evaluation::macro_binding::BoundMacroCall;
use crate::project::declarations::path_index::PathIndex;
use alloc::collections::BTreeMap;
#[cfg(verus_only)]
use vstd::laws_cmp::obeys_cmp;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::{string::StringSliceAdditionalSpecFns, utf8::encode_utf8_decode_utf8};

verus! {

type ExpansionPosition = (usize, usize);
type SignalScope = Option<ExpansionPosition>;
type Terminal = (SignalScope, usize);
type SignalKey = (SignalScope, Seq<u8>);

/// 一つの回路本体の信号索引に渡す名前と、その束縛の範囲。
#[derive(Clone, Copy, Debug)]
pub struct LocalSignalKey<'a> {
    scope: SignalScope,
    word: &'a str,
}

impl<'a> LocalSignalKey<'a> {
    /// 導入元の展開位置と、元の綴りの UTF-8 バイト列を表す。
    pub closed spec fn model(&self) -> (Option<(usize, usize)>, Seq<u8>) {
        (self.scope, self.word.spec_bytes())
    }

    /// 回路本体に直接書いた名前と、挿入した引数由来の名前に使うキーを作る。
    pub fn ordinary(word: &'a str) -> (key: Self)
        ensures key.model() == (None, word.spec_bytes()),
    {
        Self { scope: None, word }
    }

    /// 診断に表示する元の綴りを返す。
    pub fn word(&self) -> (word: &'a str)
        ensures word.spec_bytes() == self.model().1,
    {
        self.word
    }

    /// 二つの名前が、同じ回路本体で同じ束縛を指すかを判定する。
    pub fn same(&self, other: &LocalSignalKey) -> (equal: bool)
        ensures equal == (self.model() == other.model()),
    {
        proof {
            encode_utf8_decode_utf8(self.word@);
            encode_utf8_decode_utf8(other.word@);
        }
        self.scope == other.scope && self.word == other.word
    }
}

impl BoundMacroCall<'_, '_> {
    /// テンプレートが導入する局所信号のキーを、同じ呼び出しの要素間で共有する。
    ///
    /// ファイル番号は同じ解析済みプロジェクトの中で解釈する。呼び出しのバイト位置を使うため、
    /// 同じ文書版では、実行枠の分け方や展開結果を取り出す順序に依存しない。
    pub fn introduced_signal_key<'w>(&self, word: &'w str) -> (key: LocalSignalKey<'w>)
        ensures key.model() == (Some((self.scope_model().file, self.site_model().span.start)), word.spec_bytes()),
    {
        let file = self.scope().file;
        let at = self.site().span.start;
        LocalSignalKey { scope: Some((file, at)), word }
    }
}

/// 二つの導入名が一致するのは、同じファイルの同じ展開位置で綴りが一致するときに限る。
pub proof fn introduced_signal_keys_agree(
    first: &BoundMacroCall, first_word: &str, first_key: LocalSignalKey,
    second: &BoundMacroCall, second_word: &str, second_key: LocalSignalKey,
)
    requires
        first_key.model() == (Some((first.scope_model().file, first.site_model().span.start)), first_word.spec_bytes()),
        second_key.model() == (Some((second.scope_model().file, second.site_model().span.start)), second_word.spec_bytes()),
    ensures first_key.model() == second_key.model() <==> (
        first.scope_model().file == second.scope_model().file
            && first.site_model().span.start == second.site_model().span.start
            && first_word.spec_bytes() == second_word.spec_bytes()),
{}

pub(in crate::project) struct LocalSignalIndex {
    paths: PathIndex,
    drivers: BTreeMap<Terminal, OutputDriver>,
    keyed_bindings: Ghost<Map<SignalKey, OutputDriver>>,
    ordinary: Ghost<Map<Seq<u8>, OutputDriver>>,
}

// 同じ綴りは索引内の節点を共有し、駆動元はその節点と導入元の組に一つ登録する。
spec fn drivers_match(
    paths: Seq<Seq<u8>>, drivers: Map<Terminal, OutputDriver>, bindings: Map<SignalKey, OutputDriver>,
) -> bool {
    &&& forall|terminal: Terminal| #[trigger] drivers.contains_key(terminal) ==> {
        let (scope, node) = terminal;
        &&& node < paths.len()
        &&& bindings.contains_key((scope, paths[node as int]))
        &&& bindings[(scope, paths[node as int])] == drivers[terminal]
    }
    &&& forall|key: SignalKey| #[trigger] bindings.contains_key(key) ==>
        exists|node: usize| #[trigger] drivers.contains_key((key.0, node)) && node < paths.len()
            && paths[node as int] == key.1
}

proof fn extend_paths(
    before: Seq<Seq<u8>>, after: Seq<Seq<u8>>, drivers: Map<Terminal, OutputDriver>,
    bindings: Map<SignalKey, OutputDriver>,
)
    requires before.is_prefix_of(after), drivers_match(before, drivers, bindings),
    ensures drivers_match(after, drivers, bindings),
{
    assert forall|key: SignalKey| #[trigger] bindings.contains_key(key) implies
        exists|node: usize| #[trigger] drivers.contains_key((key.0, node)) && node < after.len()
            && after[node as int] == key.1 by {
        let node = choose|node: usize| #[trigger] drivers.contains_key((key.0, node)) && node < before.len()
            && before[node as int] == key.1;
        assert(after[node as int] == before[node as int]);
    };
}

// 通常の名前を使う従来の検査には、導入位置を持たない束縛だけが見える。
spec fn ordinary_matches(ordinary: Map<Seq<u8>, OutputDriver>, bindings: Map<SignalKey, OutputDriver>) -> bool {
    &&& forall|word: Seq<u8>| #[trigger] ordinary.contains_key(word) <==> bindings.contains_key((None, word))
    &&& forall|word: Seq<u8>| #[trigger] ordinary.contains_key(word) ==> ordinary[word] == bindings[(None, word)]
}

impl LocalSignalIndex {
    pub(in crate::project) closed spec fn bindings(&self) -> Map<Seq<u8>, OutputDriver> {
        self.ordinary@
    }

    pub(in crate::project) closed spec fn keyed_bindings(&self) -> Map<SignalKey, OutputDriver> {
        self.keyed_bindings@
    }

    pub(in crate::project) closed spec fn valid(&self) -> bool {
        &&& self.paths.valid()
        &&& drivers_match(self.paths.paths(), self.drivers@, self.keyed_bindings())
        &&& ordinary_matches(self.bindings(), self.keyed_bindings())
    }

    pub(in crate::project) fn new() -> (index: Self)
        ensures index.valid(), index.bindings() == Map::<Seq<u8>, OutputDriver>::empty(),
            index.keyed_bindings() == Map::<SignalKey, OutputDriver>::empty(),
    {
        let paths = PathIndex::new();
        let drivers = BTreeMap::new();
        Self { paths, drivers, keyed_bindings: Ghost(Map::empty()), ordinary: Ghost(Map::empty()) }
    }

    // 同じ綴りの節点が一つに定まることを使い、スコープ付きの駆動元を取り出す。
    proof fn terminal_binding(&self, key: SignalKey, node: usize)
        requires self.valid(), node < self.paths.paths().len(), self.paths.paths()[node as int] == key.1,
        ensures self.drivers@.contains_key((key.0, node)) == self.keyed_bindings().contains_key(key),
            self.drivers@.contains_key((key.0, node)) ==>
                self.drivers@[(key.0, node)] == self.keyed_bindings()[key],
    {
        if self.keyed_bindings().contains_key(key) {
            let other = choose|other: usize| #[trigger] self.drivers@.contains_key((key.0, other))
                && other < self.paths.paths().len() && self.paths.paths()[other as int] == key.1;
            self.paths.same_path(other as int, node as int);
        }
    }

    /// 名前と完全に一致する通常の束縛を返す。
    pub(super) fn lookup(&self, word: &str) -> (result: Option<OutputDriver>)
        requires self.valid(),
        ensures result == if self.bindings().contains_key(word.spec_bytes()) {
            Some(self.bindings()[word.spec_bytes()])
        } else { None },
    {
        let key = LocalSignalKey::ordinary(word);
        assert(self.bindings().contains_key(word.spec_bytes()) == self.keyed_bindings().contains_key(key.model()));
        self.lookup_key(key)
    }

    /// 名前と導入元の展開位置が一致する束縛を返す。
    pub(in crate::project) fn lookup_key(&self, key: LocalSignalKey) -> (result: Option<OutputDriver>)
        requires self.valid(),
        ensures result == if self.keyed_bindings().contains_key(key.model()) {
            Some(self.keyed_bindings()[key.model()])
        } else { None },
    {
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<Terminal>());
            self.paths.empty_root();
        }
        let Some(node) = self.paths.follow(0, key.word.as_bytes()) else {
            proof {
                let model = key.model();
                if self.keyed_bindings().contains_key(model) {
                    let node = choose|node: usize| #[trigger] self.drivers@.contains_key((model.0, node))
                        && node < self.paths.paths().len() && self.paths.paths()[node as int] == model.1;
                    assert(model.1.is_prefix_of(self.paths.paths()[node as int]));
                    assert(false);
                }
            }
            return None;
        };
        proof { self.terminal_binding(key.model(), node); }
        match self.drivers.get(&(key.scope, node)) {
            Some(driver) => Some(*driver),
            None => None,
        }
    }

    /// 通常の束縛を登録する。登録済みの名前には、先に登録した駆動元を返す。
    pub(super) fn insert_if_absent(&mut self, word: &str, value: OutputDriver)
        -> (result: Option<Option<OutputDriver>>)
        requires old(self).valid(),
        ensures final(self).valid(), match result {
            None => final(self).bindings() == old(self).bindings(),
            Some(previous) => {
                &&& previous == if old(self).bindings().contains_key(word.spec_bytes()) {
                    Some(old(self).bindings()[word.spec_bytes()])
                } else { None }
                &&& final(self).bindings() == if previous.is_none() {
                    old(self).bindings().insert(word.spec_bytes(), value)
                } else { old(self).bindings() }
            },
        },
    {
        let key = LocalSignalKey::ordinary(word);
        assert(self.bindings().contains_key(word.spec_bytes()) == self.keyed_bindings().contains_key(key.model()));
        self.insert_key_if_absent(key, value)
    }

    /// 名前と導入元を登録する。完全に一致するキーには先に登録した駆動元を返す。
    ///
    /// `Some(None)` は登録成功、`Some(Some(driver))` は登録済み、`None` は節点の添字の枯渇を表す。
    pub(in crate::project) fn insert_key_if_absent(&mut self, key: LocalSignalKey, value: OutputDriver)
        -> (result: Option<Option<OutputDriver>>)
        requires old(self).valid(),
        ensures final(self).valid(),
            final(self).bindings() == if key.model().0.is_none() && result == Some(None) {
                old(self).bindings().insert(key.model().1, value)
            } else { old(self).bindings() },
            match result {
            None => final(self).keyed_bindings() == old(self).keyed_bindings(),
            Some(previous) => {
                let model = key.model();
                &&& previous == if old(self).keyed_bindings().contains_key(model) {
                    Some(old(self).keyed_bindings()[model])
                } else { None }
                &&& final(self).keyed_bindings() == if previous.is_none() {
                    old(self).keyed_bindings().insert(model, value)
                } else { old(self).keyed_bindings() }
            },
        },
    {
        proof {
            broadcast use vstd::laws_cmp::group_laws_cmp;
            assert(obeys_cmp::<Terminal>());
            self.paths.empty_root();
        }
        let ghost paths_before = self.paths.paths();
        let node = self.paths.extend_bytes(0, key.word.as_bytes());
        proof { extend_paths(paths_before, self.paths.paths(), self.drivers@, self.keyed_bindings@); }
        let node = node?;
        proof { self.terminal_binding(key.model(), node); }
        let terminal = (key.scope, node);
        if let Some(previous) = self.drivers.get(&terminal) {
            return Some(Some(*previous));
        }
        let ghost prior_drivers = self.drivers@;
        let ghost prior_bindings = self.keyed_bindings@;
        let ghost model = key.model();
        let _ = self.drivers.insert(terminal, value);
        self.keyed_bindings = Ghost(prior_bindings.insert(model, value));
        let ghost prior_ordinary = self.ordinary@;
        self.ordinary = Ghost(if model.0.is_none() { prior_ordinary.insert(model.1, value) } else { prior_ordinary });
        assert(ordinary_matches(self.ordinary@, self.keyed_bindings@)) by {
            assert forall|word: Seq<u8>| #[trigger] self.ordinary@.contains_key(word)
                == self.keyed_bindings@.contains_key((None, word)) by {
                if (None, word) != model {
                    assert(prior_ordinary.contains_key(word) == prior_bindings.contains_key((None, word)));
                }
            };
            assert forall|word: Seq<u8>| #[trigger] self.ordinary@.contains_key(word)
                implies self.ordinary@[word] == self.keyed_bindings@[(None, word)] by {
                if (None, word) != model {
                    assert(prior_ordinary.contains_key(word));
                }
            };
        };
        assert forall|other: Terminal| #[trigger] self.drivers@.contains_key(other) implies {
            let (scope, node) = other;
            &&& node < self.paths.paths().len()
            &&& self.keyed_bindings@.contains_key((scope, self.paths.paths()[node as int]))
            &&& self.keyed_bindings@[(scope, self.paths.paths()[node as int])] == self.drivers@[other]
        } by {
            if other != terminal {
                assert(prior_drivers.contains_key(other));
                if other.0 == model.0 {
                    self.paths.same_path(other.1 as int, node as int);
                }
            }
        };
        assert forall|stored: SignalKey| #[trigger] self.keyed_bindings@.contains_key(stored) implies
            exists|other: usize| #[trigger] self.drivers@.contains_key((stored.0, other))
                && other < self.paths.paths().len() && self.paths.paths()[other as int] == stored.1 by {
            if stored == model {
                assert(self.drivers@.contains_key(terminal));
            } else {
                assert(prior_bindings.contains_key(stored));
                let other = choose|other: usize| #[trigger] prior_drivers.contains_key((stored.0, other))
                    && other < self.paths.paths().len() && self.paths.paths()[other as int] == stored.1;
                assert(self.drivers@.contains_key((stored.0, other)));
            }
        };
        Some(None)
    }
}

} // verus!


#[cfg(test)]
mod tests {
    use super::{LocalSignalIndex, LocalSignalKey, OutputDriver};
    use crate::project::{SourceSnapshot, check_mixed_use_aliases, index_mixed_use_targets, parse_project_sources};
    use crate::syntax::Form;

    #[test]
    fn macro_and_caller_keys_use_the_same_driver_index_without_capture() {
        let project = parse_project_sources(&[
            SourceSnapshot {
                path: "lib.ncg2m",
                revision: 2,
                text: "(defmacro expose (output) (list (syntax (def (unsyntax output) (nor tmp tmp)))))",
            },
            SourceSnapshot {
                path: "sub/../top.ncg2",
                revision: 3,
                text: "(using nor) (func top (in tmp) (out y) (expand expose tmp) (expand expose y))",
            },
        ]).unwrap();
        let targets = index_mixed_use_targets(&project).unwrap();
        let aliases = check_mixed_use_aliases(&targets).unwrap();
        let mut calls = aliases.macro_calls(1, 1).unwrap();
        let first = calls.next_bound_macro().unwrap().unwrap();
        let second = calls.next_bound_macro().unwrap().unwrap();
        let first_target = first.introduced_signal_key("tmp");
        let second_target = second.introduced_signal_key("tmp");

        let mut index = LocalSignalIndex::new();
        assert_eq!(index.insert_if_absent("tmp", OutputDriver::Input(0)), Some(None));
        assert_eq!(index.insert_key_if_absent(first_target, OutputDriver::Definition(0)), Some(None));
        assert_eq!(index.insert_key_if_absent(second_target, OutputDriver::Definition(1)), Some(None));
        assert_eq!(index.lookup_key(first.introduced_signal_key("tmp")), Some(OutputDriver::Definition(0)));
        assert_eq!(index.lookup_key(second.introduced_signal_key("tmp")), Some(OutputDriver::Definition(1)));
        let inserted = &first.arguments()[0];
        let Form::Atom { span, .. } = &inserted.forms()[inserted.nodes().start] else { unreachable!() };
        let inserted_word = &inserted.scope().source.text()[span.clone()];
        assert_eq!(index.lookup_key(LocalSignalKey::ordinary(inserted_word)), Some(OutputDriver::Input(0)));
        assert_eq!(index.lookup("tmp"), Some(OutputDriver::Input(0)));
        assert_eq!(index.insert_key_if_absent(first_target, OutputDriver::Definition(2)),
            Some(Some(OutputDriver::Definition(0))));
    }
}
