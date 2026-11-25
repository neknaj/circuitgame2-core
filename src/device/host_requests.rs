//! デバイスが返した要求に番号を付け、確定した順序でホストに渡す。

use alloc::vec::Vec;
use vstd::prelude::*;

use crate::time::ScheduledEvent;
use super::{HostRequestId, IssuedRequestIds, PendingDeviceEvents, QueuedResponse, RequestBatchTickError, RequestKey};

verus! {

/// デバイスがホストに渡す値。各 payload の型はデバイスの種別で定まる。
pub enum HostRequest<N, R> {
    /// 応答を待たない通知。
    Notify(N),
    /// ローカルタグを付け、ホストからの応答を1件待つ要求。
    Request {
        /// デバイスが応答を区別するタグ。
        tag: u64,
        /// ホストが行う操作のデータ。
        payload: R,
    },
}

/// 実行設定のインスタンスと、そのインスタンスが生成した要求または通知。
pub struct DeviceHostRequest<N, R> {
    /// 実行設定で0から割り当てたインスタンス番号。
    pub instance: usize,
    /// ホストに渡す値。
    pub request: HostRequest<N, R>,
}

/// 確定した tick でホストに渡す要求または通知。
pub enum CommittedHostRequest<'a, N, R> {
    /// インスタンスと通知のデータ。
    Notify {
        /// 通知を生成したインスタンス。
        instance: usize,
        /// ホストに渡すデータ。
        notification: &'a N,
    },
    /// ホストが応答するときに使う番号を付けた要求。
    Request {
        /// 要求のインスタンス、世代、世代内の通し番号。
        id: HostRequestId,
        /// デバイスが応答を区別するタグ。
        tag: u64,
        /// ホストが行う操作のデータ。
        payload: &'a R,
    },
}

/// ホスト要求を含む tick を確定できない理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HostRequestCommitError {
    /// 直前の項目より小さいインスタンス番号が最初に現れた位置。
    InstanceOrder(usize),
    /// 確定前に索引または要求キーの領域を確保できなかった。
    Allocation,
    /// 採番、要求の登録、応答の配送、回路入力のいずれかの検査に失敗した。
    /// 登録エラーの添字は、通知を除いた要求列を指す。
    Tick(RequestBatchTickError),
}

/// 1 tick で確定したホスト要求。payload は呼び出し側が渡したスライスから借りる。
pub struct CommittedHostRequests<'a, N, R> {
    source: &'a [DeviceHostRequest<N, R>],
    ranks: Vec<u64>,
    ids: IssuedRequestIds,
    keys: Ghost<Seq<RequestKey>>,
}

impl<N, R> DeviceHostRequest<N, R> {
    /// 応答を待つ項目に対応する登録キー。
    pub open spec fn key_model(&self) -> Option<RequestKey> {
        match self.request {
            HostRequest::Notify(_) => None,
            HostRequest::Request { tag, .. } => Some(RequestKey { instance: self.instance, tag }),
        }
    }
}

/// 通知を除き、元の順序で台帳に登録する要求キーを並べる。
pub open spec fn host_request_keys<N, R>(input: Seq<DeviceHostRequest<N, R>>) -> Seq<RequestKey>
    decreases input.len(),
{
    if input.len() == 0 {
        Seq::empty()
    } else {
        let keys = host_request_keys(input.drop_last());
        match input.last().key_model() {
            Some(key) => keys.push(key),
            None => keys,
        }
    }
}

/// 各項目の位置に対し、先行する要求の件数と要求キーが対応することを表す。
pub open spec fn request_ranks_match<N, R>(
    input: Seq<DeviceHostRequest<N, R>>, ranks: Seq<u64>, keys: Seq<RequestKey>,
) -> bool {
    &&& ranks.len() == input.len()
    &&& if input.len() == 0 { keys.len() == 0 } else { ranks[0] == 0 }
    &&& forall|i: int| 0 <= i < input.len() ==> {
        let rank = #[trigger] ranks[i] as int;
        let next = if i + 1 == input.len() { keys.len() as int } else { ranks[i + 1] as int };
        &&& rank <= next <= keys.len()
        &&& match input[i].key_model() {
            Some(key) => next == rank + 1 && keys[rank] == key,
            None => next == rank,
        }
    }
}

/// 実行設定で先に現れるインスタンスの項目を先に渡す。
pub open spec fn host_request_order<N, R>(input: Seq<DeviceHostRequest<N, R>>) -> bool {
    forall|i: int| 0 < i < input.len() ==> (#[trigger] input[i - 1]).instance <= input[i].instance
}

impl<'a, N, R> CommittedHostRequests<'a, N, R> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        &&& request_ranks_match(self.source@, self.ranks@, self.keys@)
        &&& self.ids.count_model() == self.keys@.len()
        &&& host_request_order(self.source@)
    }

    /// 要求と通知が生成された順序。
    pub closed spec fn source_model(&self) -> Seq<DeviceHostRequest<N, R>> { self.source@ }

    /// 確定した通し番号の範囲。
    pub closed spec fn ids_model(&self) -> IssuedRequestIds { self.ids }

    /// 台帳に追加した要求キーの列。通知は含めない。
    pub closed spec fn keys_model(&self) -> Seq<RequestKey> { self.keys@ }

    /// 各項目の位置に対応する通し番号の差分。通知も並びに含む。
    pub closed spec fn ranks_model(&self) -> Seq<u64> { self.ranks@ }

    /// 通知と要求を合わせた件数を返す。
    pub fn len(&self) -> (count: usize)
        ensures count == self.source_model().len(),
    {
        self.source.len()
    }

    /// 指定位置の通知または要求を返す。範囲外なら `None` を返す。
    pub fn get(&self, index: usize) -> (entry: Option<CommittedHostRequest<'a, N, R>>)
        ensures
            entry.is_some() <==> index < self.source_model().len(),
            entry matches Some(value) ==> {
                let source = self.source_model()[index as int];
                match (source.request, value) {
                    (HostRequest::Notify(sent), CommittedHostRequest::Notify { instance, notification }) =>
                        instance == source.instance && *notification == sent,
                    (HostRequest::Request { tag, payload: sent },
                        CommittedHostRequest::Request { id, tag: delivered_tag, payload }) =>
                        id.instance == source.instance && id.generation == self.ids_model().generation_model()
                        && id.serial as int == self.ids_model().first_model() + self.ranks_model()[index as int] as int
                        && delivered_tag == tag && *payload == sent,
                    _ => false,
                }
            },
    {
        proof { use_type_invariant(self); }
        if index >= self.source.len() { return None; }
        let item = &self.source[index];
        match &item.request {
            HostRequest::Notify(payload) =>
                Some(CommittedHostRequest::Notify { instance: item.instance, notification: payload }),
            HostRequest::Request { tag, payload } => {
                let rank = self.ranks[index];
                assert(self.keys@[rank as int] == RequestKey { instance: item.instance, tag: *tag });
                let id = self.ids.id_at(rank, item.instance);
                match id {
                    Some(id) => Some(CommittedHostRequest::Request { id, tag: *tag, payload }),
                    None => { proof { assert(false); } None },
                }
            },
        }
    }
}

fn index_requests<N, R>(source: &[DeviceHostRequest<N, R>])
    -> (result: Result<(Vec<u64>, Vec<RequestKey>), HostRequestCommitError>)
    ensures
        result matches Ok((ranks, keys)) ==> request_ranks_match(source@, ranks@, keys@)
            && keys@ == host_request_keys(source@) && host_request_order(source@),
        result matches Err(HostRequestCommitError::InstanceOrder(i)) ==> {
            &&& 0 < i < source@.len()
            &&& source@[i as int - 1].instance > source@[i as int].instance
            &&& host_request_order(source@.take(i as int))
        },
        result.is_err() ==> result matches Err(HostRequestCommitError::InstanceOrder(_))
            || result matches Err(HostRequestCommitError::Allocation),
{
    let mut ranks = Vec::new();
    let mut keys = Vec::new();
    if ranks.try_reserve_exact(source.len()).is_err() { return Err(HostRequestCommitError::Allocation); }
    let mut i = 0;
    while i < source.len()
        invariant
            i <= source@.len(),
            keys@.len() <= i,
            keys@ == host_request_keys(source@.take(i as int)),
            request_ranks_match(source@.take(i as int), ranks@, keys@),
            host_request_order(source@.take(i as int)),
        decreases source@.len() - i,
    {
        let item = &source[i];
        if i != 0 && source[i - 1].instance > item.instance {
            return Err(HostRequestCommitError::InstanceOrder(i));
        }
        let ghost before_ranks = ranks@;
        let ghost before_keys = keys@;
        ranks.push(keys.len() as u64);
        if let HostRequest::Request { tag, .. } = &item.request {
            if keys.try_reserve(1).is_err() { return Err(HostRequestCommitError::Allocation); }
            keys.push(RequestKey { instance: item.instance, tag: *tag });
        }
        proof {
            let prefix = source@.take(i as int);
            let extended = source@.take(i as int + 1);
            assert(extended =~= prefix.push(*item));
            assert(extended.drop_last() =~= prefix);
            assert(host_request_keys(extended) == keys@);
            assert forall|j: int| 0 < j < extended.len() implies
                (#[trigger] extended[j - 1]).instance <= extended[j].instance by {
                if j < i { assert(prefix[j - 1].instance <= prefix[j].instance); }
            }
            assert forall|j: int| 0 <= j < extended.len() implies {
                let rank = #[trigger] ranks@[j] as int;
                let next = if j + 1 == extended.len() { keys@.len() as int } else { ranks@[j + 1] as int };
                &&& rank <= next <= keys@.len()
                &&& match extended[j].key_model() {
                    Some(key) => next == rank + 1 && keys@[rank] == key,
                    None => next == rank,
                }
            } by {
                if j < i {
                    assert(before_ranks[j] == ranks@[j]);
                    if j + 1 == i { assert(ranks@[j + 1] as int == before_keys.len()); }
                }
            }
        }
        i += 1;
    }
    assert(source@.take(i as int) =~= source@);
    Ok((ranks, keys))
}

impl<'tick, E: QueuedResponse> PendingDeviceEvents<'tick, E> {
    /// 要求と通知の順序を保ち、回路更新が成功したときにだけホストへ渡す。
    ///
    /// 同じインスタンスの項目はデバイスが返したリスト順に並べる。通知には番号を振らない。
    ///
    /// # Errors
    ///
    /// インスタンス番号が降順になる箇所、索引の領域確保失敗、または tick の確定エラーを返す。
    /// エラー時は、回路、論理時刻、イベント列、台帳の内容、採番状態を保持する。
    pub fn commit_host_requests<'a, N, R>(
        self, input: &[bool], source: &'a [DeviceHostRequest<N, R>],
    ) -> (result: Result<(Vec<ScheduledEvent<E>>, CommittedHostRequests<'a, N, R>),
        HostRequestCommitError>)
        ensures
            result.is_err() ==> {
                &&& self.after_model().0 == self.before_model().0
                &&& self.after_model().1.generation_model() == self.before_model().1.generation_model()
                &&& self.after_model().1.requests() == self.before_model().1.requests()
                &&& self.after_model().2 == self.before_model().2
                &&& self.after_ids() == self.before_ids()
            },
            result matches Err(HostRequestCommitError::InstanceOrder(i)) ==> {
                &&& 0 < i < source@.len()
                &&& source@[i as int - 1].instance > source@[i as int].instance
                &&& host_request_order(source@.take(i as int))
            },
            result matches Err(HostRequestCommitError::Tick(error)) ==>
                host_request_order(source@) && self.request_batch_error(input@, host_request_keys(source@), error),
            result matches Ok((consumed, committed)) ==> {
                &&& committed.source_model() == source@
                &&& host_request_order(source@)
                &&& committed.keys_model() == host_request_keys(source@)
                &&& request_ranks_match(source@, committed.ranks_model(), committed.keys_model())
                &&& self.request_batch_committed(
                    input@, committed.keys_model(), consumed@, committed.ids_model(),
                )
            },
    {
        let (ranks, keys) = match index_requests(source) {
            Ok(index) => index,
            Err(error) => {
                self.cancel();
                return Err(error);
            },
        };
        let ghost registered_keys = keys@;
        match self.commit_with_requests(input, keys.as_slice()) {
            Ok((consumed, ids)) => Ok((consumed, CommittedHostRequests {
                source, ranks, ids, keys: Ghost(registered_keys),
            })),
            Err(error) => Err(HostRequestCommitError::Tick(error)),
        }
    }
}

} // verus!
