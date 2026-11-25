//! UI の実行枠をまたいで、デバイスが読む確定状態とイベントを固定する。

use alloc::vec::Vec;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::first_unknown_host_instance;
#[cfg(verus_only)]
use crate::device::ledger::batch_request_error;
#[cfg(verus_only)]
use crate::device::{
    BatchRegistrationError, DeviceEventSession, HostRequestCommitError, RequestBatchTickError,
    ResponseTickError, first_batch_request_error, queued_response_keys, valid_request_batch,
};
use super::{DeviceStateSession, DeviceStateTickError, DeviceStateTickResult, Event};
use crate::device::DeviceHostRequest;
use crate::time::{ClockError, TickPosition};
#[cfg(verus_only)]
use crate::device::{host_request_keys, host_request_order, request_ranks_match};
#[cfg(verus_only)]
use crate::time::{events_at_tick, next_event_matches};

verus! {

/// 次の tick のデバイス評価が終わるまで、元のセッションを所有する。
///
/// 停止中も直前の回路出力、デバイス状態、対象 tick のイベントを参照できる。
/// 評価器の継続は、この値とともに呼び出し側が保持する。状態とイベントは共有参照から
/// 変更できない値で渡す。評価を取り消して元の実行に戻るには [Self::cancel] を使う。
/// 実行枠の途中で届いた外部入力はホスト側で保留し、次に準備できる tick に予約する。
pub struct OwnedDeviceStateTick<I, R, S> {
    session: DeviceStateSession<I, R, S>,
    target: TickPosition,
}

impl<I, R, S> DeviceStateSession<I, R, S> {
    /// セッションとイベント列を複製せずに、次の tick の準備へ移る。
    ///
    /// # Errors
    ///
    /// tick 番号が上限なら、元のセッションとともにエラーを返す。
    pub fn prepare_owned_tick(self)
        -> (result: Result<OwnedDeviceStateTick<I, R, S>, (Self, ClockError)>)
        requires self.execution_model().valid(),
        ensures
            result.is_ok() <==> self.execution_model().model().0.position_model().tick < u64::MAX,
            result matches Ok(tick) ==> tick.before_model() == self
                && tick.target_model().generation == self.execution_model().model().0.position_model().generation
                && tick.target_model().tick as int == self.execution_model().model().0.position_model().tick as int + 1,
            result matches Err((session, error)) ==> session == self && error == ClockError::TickOutOfRange,
    {
        let current = self.position();
        let Some(tick) = current.tick.checked_add(1) else {
            return Err((self, ClockError::TickOutOfRange));
        };
        let target = TickPosition { generation: current.generation, tick };
        Ok(OwnedDeviceStateTick { session: self, target })
    }
}

impl<I, R, S> OwnedDeviceStateTick<I, R, S> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        let execution = self.before_model().execution_model();
        let current = execution.model().0.position_model();
        &&& execution.valid()
        &&& self.target_model().generation == current.generation
        &&& self.target_model().tick as int == current.tick as int + 1
    }

    /// 評価を始める前に確定していたセッション。
    pub closed spec fn before_model(&self) -> DeviceStateSession<I, R, S> { self.session }

    /// 今回の確定予定の世代と tick。
    pub closed spec fn target_model(&self) -> TickPosition { self.target }

    /// デバイスに渡す論理位置を返す。
    pub fn target(&self) -> (target: TickPosition)
        ensures target == self.target_model(),
    {
        self.target
    }

    /// 今回の tick で全デバイスが読む状態を、設定順で借りる。
    pub fn states(&self) -> (states: &[S])
        ensures states@ == self.before_model().states_model(),
    {
        self.session.states()
    }

    /// すべてのデバイスが読む、直前に確定した回路の出力を借りる。
    pub fn previous_output(&self) -> (bits: &[bool])
        ensures bits@ == self.before_model().execution_model().model().0.output_model(),
    {
        self.session.output()
    }

    /// 指定添字以降にある、今回の tick の最初のイベントを借りる。
    ///
    /// 評価を再開しても同じ順序と添字を使う。イベントの消費は確定時に行う。
    pub fn next_event(&self, from: usize) -> (result: Option<(usize, &Event<I, R>)>)
        ensures next_event_matches(self.before_model().execution_model().model().2,
            self.target_model(), from, result),
    {
        self.session.execution.next_event_at(self.target, from)
    }

    /// 候補から返し得る確定エラーを、開始時のイベントと回路の状態から決める。
    ///
    /// 領域の確保失敗はホスト上の資源に依存する。ほかの診断は候補と開始時の状態から検査する。
    pub open spec fn commit_error<N, Q>(
        &self, next_count: nat, input: Seq<bool>, hosts: Seq<DeviceHostRequest<N, Q>>,
        error: DeviceStateTickError,
    ) -> bool {
        let before = self.before_model().execution_model();
        let count = self.before_model().states_model().len();
        match error {
            DeviceStateTickError::StateCount(error) => error.expected == count
                && error.actual == next_count && error.actual != error.expected,
            DeviceStateTickError::HostInstance { request, instance } => next_count == count
                && first_unknown_host_instance(hosts, count, request)
                && instance == hosts[request as int].instance,
            DeviceStateTickError::Commit(error) => {
                &&& next_count == count
                &&& forall|i: int| 0 <= i < hosts.len() ==> (#[trigger] hosts[i]).instance < count
                &&& DeviceEventSession::<I, R>::host_request_commit_error_at(
                    before.model(), before.ids_model(), self.target_model(), input, hosts, error)
            },
        }
    }

    /// 状態数、入力幅、要求の順序と採番、応答の照合が、開始時の状態に適合することを表す。
    pub open spec fn candidate_fits<N, Q>(
        &self, next_count: nat, input: Seq<bool>, hosts: Seq<DeviceHostRequest<N, Q>>,
    ) -> bool {
        let before = self.before_model().execution_model();
        let (circuit, ledger, events) = before.model();
        let ids = before.ids_model();
        let keys = host_request_keys(hosts);
        let target = self.target_model();
        &&& next_count == self.before_model().states_model().len()
        &&& input.len() == circuit.vm_model().external_count()
        &&& host_request_order(hosts)
        &&& forall|i: int| 0 <= i < hosts.len() ==> (#[trigger] hosts[i]).instance < next_count
        &&& ids.fits(keys.len() as u64)
        &&& valid_request_batch(&ledger, keys, ids.generation_model(), ids.next_model(), target.tick)
        &&& ledger.valid_delivery(queued_response_keys(events, target), target)
    }

    /// 適合する候補を確定できない理由は、ホスト上での領域確保の失敗に限る。
    pub proof fn valid_candidate_error_is_allocation<N, Q>(
        &self, next_count: nat, input: Seq<bool>, hosts: Seq<DeviceHostRequest<N, Q>>,
        error: DeviceStateTickError,
    )
        requires self.candidate_fits(next_count, input, hosts),
            self.commit_error(next_count, input, hosts, error),
        ensures
            error == DeviceStateTickError::Commit(HostRequestCommitError::Allocation)
            || error == DeviceStateTickError::Commit(HostRequestCommitError::Tick(
                RequestBatchTickError::Registration(BatchRegistrationError::Allocation))),
    {
        let execution = self.before_model().execution_model();
        let (_, ledger, events) = execution.model();
        let ids = execution.ids_model();
        let keys = host_request_keys(hosts);
        let target = self.target_model();
        match error {
            DeviceStateTickError::StateCount(_) => { assert(false); },
            DeviceStateTickError::HostInstance { request, .. } => {
                assert(request < hosts.len());
                assert(hosts[request as int].instance < next_count);
                assert(false);
            },
            DeviceStateTickError::Commit(HostRequestCommitError::InstanceOrder(i)) => {
                assert(0 < i < hosts.len());
                assert(hosts[i as int - 1].instance <= hosts[i as int].instance);
                assert(false);
            },
            DeviceStateTickError::Commit(HostRequestCommitError::Tick(
                RequestBatchTickError::Registration(reason))) => {
                if reason != BatchRegistrationError::Allocation {
                    let generation = ids.generation_model();
                    let first = ids.next_model();
                    assert(first_batch_request_error(&ledger, keys, generation, first, target.tick, reason));
                    let i = choose|i: usize| i < keys.len()
                        && #[trigger] batch_request_error(&ledger, keys, generation, first, target.tick, i) == Some(reason);
                    assert(batch_request_error(&ledger, keys, generation, first, target.tick, i).is_none());
                    assert(false);
                }
            },
            DeviceStateTickError::Commit(HostRequestCommitError::Tick(
                RequestBatchTickError::Tick(ResponseTickError::Delivery(reason)))) => {
                self.before_model().execution_model().model().1
                    .valid_delivery_excludes_error(queued_response_keys(events, target), target, reason);
                assert(false);
            },
            DeviceStateTickError::Commit(HostRequestCommitError::Tick(
                RequestBatchTickError::Number(_) | RequestBatchTickError::Tick(ResponseTickError::Input(_)))) => {
                assert(false);
            },
            DeviceStateTickError::Commit(HostRequestCommitError::Allocation) => {},
        }
    }

    /// 評価結果を既存の確定処理に渡し、セッションと確定結果を返す。
    ///
    /// `next` は設定順の次状態、`input` は回路への入力フレーム、`hosts` は設定順の通知と要求。
    /// 成功した tick のイベントと要求だけをホストに返す。
    ///
    /// # Errors
    ///
    /// 次状態の数、ホストに渡す要求、回路入力を検査する。失敗時は tick を始める前の
    /// 回路、デバイス状態、採番状態、応答と外部イベントを保持する。
    pub fn commit<'p, N, Q>(self, next: Vec<S>, input: &[bool], hosts: &'p [DeviceHostRequest<N, Q>])
        -> (result: (DeviceStateSession<I, R, S>, Result<DeviceStateTickResult<'p, I, R, N, Q>, DeviceStateTickError>))
        ensures {
            let (session, outcome) = result;
            let before = self.before_model().execution_model();
            let after = session.execution_model();
            let (old_circuit, old_ledger, old_events) = before.model();
            let (circuit, ledger, events) = after.model();
            &&& after.valid()
            &&& match outcome {
                Err(error) => self.commit_error(next@.len(), input@, hosts@, error)
                    && session.states_model() == self.before_model().states_model()
                    && circuit == old_circuit && after.ids_model() == before.ids_model()
                    && ledger.generation_model() == old_ledger.generation_model()
                    && ledger.requests() == old_ledger.requests() && events == old_events,
                Ok(done) => {
                    &&& session.states_model() == next@
                    &&& session.states_model().len() == self.before_model().states_model().len()
                    &&& circuit.position_model() == self.target_model()
                    &&& circuit.vm_model().tick_matches(&old_circuit.vm_model(), input@, circuit.output_model())
                    &&& events == events_at_tick(old_events, self.target_model(), false)
                    &&& done.consumed@ == events_at_tick(old_events, self.target_model(), true)
                    &&& forall|i: int| 0 <= i < hosts@.len() ==>
                        (#[trigger] hosts@[i]).instance < self.before_model().states_model().len()
                    &&& done.outgoing.source_model() == hosts@
                    &&& host_request_order(hosts@)
                    &&& done.outgoing.keys_model() == host_request_keys(hosts@)
                    &&& request_ranks_match(hosts@, done.outgoing.ranks_model(), done.outgoing.keys_model())
                    &&& done.outgoing.ids_model().count_model() as nat == done.outgoing.keys_model().len()
                    &&& after.ids_model().generation_model() == before.ids_model().generation_model()
                    &&& done.outgoing.ids_model().first_model() == before.ids_model().next_model()
                    &&& done.outgoing.ids_model().generation_model() == self.target_model().generation
                    &&& after.ids_model().next_model() == before.ids_model().next_model() + done.outgoing.keys_model().len()
                },
            }
        },
    {
        proof { use_type_invariant(&self); }
        let ghost start = self;
        let ghost target = self.target_model();
        let ghost count = next@.len();
        let mut session = self.session;
        let Ok(tick) = session.prepare_tick() else { unreachable!() };
        assert(tick.tick_model().target_model() == target);
        let ghost pending = tick;
        let result = tick.commit(next, input, hosts);
        proof {
            let snapshot = start.before_model().execution_model();
            assert(pending.tick_model().before_model() == snapshot.model());
            assert(pending.tick_model().before_ids() == snapshot.ids_model());
            if let Err(error) = result {
                assert(start.commit_error(count, input@, hosts@, error));
            }
        }
        (session, result)
    }

    /// 未確定の評価を打ち切り、イベントを消費せずに元のセッションを返す。
    ///
    /// reset する場合は、このセッションで次の世代の準備を始める。
    pub fn cancel(self) -> (session: DeviceStateSession<I, R, S>)
        ensures session == self.before_model(), session.execution_model().valid(),
    {
        proof { use_type_invariant(&self); }
        self.session
    }
}

} // verus!
