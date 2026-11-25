//! デバイスごとの状態を回路と同じ tick または reset で確定する。

use alloc::vec::Vec;
use vstd::prelude::*;

use crate::netlist::ClockedVm;
use crate::time::{ClockError, ScheduledEvent, TickPosition};
#[cfg(verus_only)]
use crate::time::next_event_matches;
use super::{
    CommittedHostRequests, DeviceEvent, DeviceEventSession, DeviceHostRequest, HostRequestCommitError,
    HostRequestId, PendingDeviceEvents, PendingDeviceEventsReset, ScheduleInputError, ScheduleResponseError,
};
#[cfg(verus_only)]
use super::{host_request_keys, host_request_order, request_ranks_match};

mod owned_tick;
pub use owned_tick::OwnedDeviceStateTick;

verus! {

type Event<I, R> = ScheduledEvent<DeviceEvent<I, R>>;

/// 回路の実行と、設定に並ぶ各デバイスの確定状態。
///
/// 状態は共有参照から変更できない値で渡す。デバイスの純粋な遷移はその値を読み、次の値を返す。
pub struct DeviceStateSession<I, R, S> {
    execution: DeviceEventSession<I, R>,
    states: Vec<S>,
}

/// 全デバイスの評価で同じ確定済み状態を使うための tick。
pub struct PendingDeviceStateTick<'a, I, R, S> {
    tick: PendingDeviceEvents<'a, DeviceEvent<I, R>>,
    states: &'a mut Vec<S>,
}

/// 旧世代の状態を借りたまま、各デバイスの初期化を待つ reset。
pub struct PendingDeviceStateReset<'a, I, R, S> {
    reset: PendingDeviceEventsReset<'a, DeviceEvent<I, R>>,
    states: &'a mut Vec<S>,
}

/// 次の状態の列が実行設定のインスタンス数と異なる。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DeviceStateCountError {
    /// 実行を始めたときのインスタンス数。
    pub expected: usize,
    /// 次の状態が渡された件数。
    pub actual: usize,
}

/// 初期化済みのデバイスへ外部入力を予約できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StatefulInputError {
    /// 設定に存在しないインスタンス。
    UnknownInstance(usize),
    /// 配送予定の世代か tick が現在の実行と合わない。
    Schedule(ScheduleInputError),
}

/// デバイスの状態と回路を一括確定できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeviceStateTickError {
    /// 次状態がインスタンスごとに一つずつ渡されていない。
    StateCount(DeviceStateCountError),
    /// 確定する要求が設定に存在しないインスタンスを指す。
    HostInstance {
        /// 要求と通知を合わせた入力列での最初の位置。
        request: usize,
        /// 対象のインスタンス番号。
        instance: usize,
    },
    /// ホスト要求の検査、応答の配送、または回路更新に失敗した。
    Commit(HostRequestCommitError),
}

/// 回路とデバイスを確定した tick からホストへ返す結果。
pub struct DeviceStateTickResult<'p, I, R, N, Q> {
    /// 対象 tick から、到着順に消費したイベント。
    pub consumed: Vec<Event<I, R>>,
    /// 通知と、応答を待つ要求に採番した結果。
    pub outgoing: CommittedHostRequests<'p, N, Q>,
}

/// 設定にないインスタンスを指す、入力順で最初の要求または通知を表す。
pub open spec fn first_unknown_host_instance<N, Q>(
    hosts: Seq<DeviceHostRequest<N, Q>>, count: nat, request: usize,
) -> bool {
    &&& request < hosts.len()
    &&& hosts[request as int].instance >= count
    &&& forall|j: int| 0 <= j < request ==> (#[trigger] hosts[j]).instance < count
}

fn unknown_host_instance<N, Q>(hosts: &[DeviceHostRequest<N, Q>], count: usize) -> (result: Option<usize>)
    ensures
        result matches Some(index) ==> first_unknown_host_instance(hosts@, count as nat, index),
        result.is_none() ==> forall|i: int| 0 <= i < hosts@.len() ==> (#[trigger] hosts@[i]).instance < count,
{
    let mut i = 0;
    while i < hosts.len()
        invariant
            i <= hosts@.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] hosts@[j]).instance < count,
        decreases hosts@.len() - i,
    {
        if hosts[i].instance >= count {
            return Some(i);
        }
        i += 1;
    }
    None
}

impl<I, R, S> DeviceStateSession<I, R, S> {
    /// 現在の回路、要求管理、イベント列を所有する実行。
    pub closed spec fn execution_model(&self) -> DeviceEventSession<I, R> { self.execution }

    /// 実行設定の順に並ぶデバイスの状態。
    pub closed spec fn states_model(&self) -> Seq<S> { self.states@ }

    /// 初期化に成功した全デバイスの状態を設定順に受け取り、世代0を開始する。
    pub fn new(vm: ClockedVm, initial: Vec<S>) -> (session: Self)
        requires vm.valid(),
        ensures
            session.execution_model().valid(),
            session.execution_model().model().0.position_model() == (TickPosition { generation: 0, tick: 0 }),
            session.execution_model().model().0.vm_model().same_layout(&vm),
            session.execution_model().model().2.len() == 0,
            session.states_model() == initial@,
    {
        Self::from_initial_execution(DeviceEventSession::new(vm), initial)
    }

    pub(crate) fn from_initial_execution(execution: DeviceEventSession<I, R>, initial: Vec<S>) -> (session: Self)
        requires
            execution.valid(),
            execution.model().0.position_model() == (TickPosition { generation: 0, tick: 0 }),
            execution.model().1.requests().len() == 0,
            execution.model().2.len() == 0,
            execution.ids_model().next_model() == 0,
        ensures session.execution_model() == execution, session.states_model() == initial@,
    {
        Self { execution, states: initial }
    }

    /// 現在確定しているデバイスの状態を設定順で借りる。
    pub fn states(&self) -> (result: &[S])
        ensures result@ == self.states_model(),
    {
        self.states.as_slice()
    }

    /// 最後に確定した世代と tick を返す。
    pub fn position(&self) -> (position: TickPosition)
        ensures position == self.execution_model().model().0.position_model(),
    {
        self.execution.position()
    }

    /// 最後に確定した回路の公開出力を、ポートのビット順に借りる。
    ///
    /// 初期化やリセットの直後は、その世代の tick 0 の出力を返す。
    pub fn output(&self) -> (bits: &[bool])
        ensures bits@ == self.execution_model().model().0.output_model(),
    {
        self.execution.output()
    }

    /// 設定にあるインスタンスにだけ外部入力を予約する。
    ///
    /// # Errors
    ///
    /// インスタンス番号を先に調べ、次に適用する世代と tick を検査する。
    /// 失敗時は確定状態とイベント列を保持する。
    pub fn schedule_input(&mut self, instance: usize, delivery: TickPosition, payload: I)
        -> (result: Result<(), StatefulInputError>)
        requires old(self).execution_model().valid(),
        ensures
            final(self).execution_model().valid(),
            final(self).states_model() == old(self).states_model(),
            final(self).execution_model().ids_model() == old(self).execution_model().ids_model(),
            final(self).execution_model().model().0 == old(self).execution_model().model().0,
            final(self).execution_model().model().1 == old(self).execution_model().model().1,
            result matches Err(StatefulInputError::UnknownInstance(number)) ==>
                number == instance && instance >= old(self).states_model().len(),
            result matches Err(StatefulInputError::Schedule(reason)) ==> {
                let current = old(self).execution_model().model().0.position_model();
                &&& instance < old(self).states_model().len()
                &&& match reason {
                    ScheduleInputError::DifferentGeneration => delivery.generation != current.generation,
                    ScheduleInputError::AlreadyCommitted =>
                        delivery.generation == current.generation && delivery.tick <= current.tick,
                }
            },
            result.is_ok() <==> {
                let current = old(self).execution_model().model().0.position_model();
                instance < old(self).states_model().len() && delivery.generation == current.generation
                    && delivery.tick > current.tick
            },
            result.is_err() ==> final(self).execution_model().model() == old(self).execution_model().model(),
            result.is_ok() ==> final(self).execution_model().model().2 ==
                old(self).execution_model().model().2.push(ScheduledEvent {
                    position: delivery, payload: DeviceEvent::Input { instance, payload },
                }),
    {
        if instance >= self.states.len() {
            return Err(StatefulInputError::UnknownInstance(instance));
        }
        match self.execution.schedule_input(instance, delivery, payload) {
            Ok(()) => Ok(()),
            Err(error) => Err(StatefulInputError::Schedule(error)),
        }
    }

    /// 発行済みの要求と照合した応答を、未開始の tick に予約する。
    ///
    /// # Errors
    ///
    /// 世代、配送予定の tick、元の要求を順に照合する。失敗時は確定状態とイベント列を保持する。
    pub fn schedule_response(&mut self, id: HostRequestId, delivery: TickPosition, payload: R)
        -> (result: Result<(), ScheduleResponseError>)
        requires old(self).execution_model().valid(),
        ensures
            final(self).execution_model().valid(),
            final(self).states_model() == old(self).states_model(),
            final(self).execution_model().ids_model() == old(self).execution_model().ids_model(),
            final(self).execution_model().model().0 == old(self).execution_model().model().0,
            result == Err(ScheduleResponseError::DifferentGeneration) <==>
                delivery.generation != old(self).execution_model().model().0.position_model().generation,
            result == Err(ScheduleResponseError::AlreadyCommitted) <==> {
                let current = old(self).execution_model().model().0.position_model();
                delivery.generation == current.generation && delivery.tick <= current.tick
            },
            result matches Err(ScheduleResponseError::Response(reason)) ==> {
                let (circuit, ledger, _) = old(self).execution_model().model();
                &&& delivery.generation == circuit.position_model().generation
                &&& delivery.tick > circuit.position_model().tick
                &&& ledger.rejects_response(id, delivery, reason)
            },
            result.is_err() ==> final(self).execution_model().model() == old(self).execution_model().model(),
            result.is_ok() <==> {
                let (circuit, ledger, _) = old(self).execution_model().model();
                &&& delivery.generation == circuit.position_model().generation
                &&& delivery.tick > circuit.position_model().tick
                &&& ledger.accepts_response(id, delivery)
            },
            result.is_ok() ==> {
                let events = final(self).execution_model().model().2;
                &&& events.len() == old(self).execution_model().model().2.len() + 1
                &&& events.drop_last() == old(self).execution_model().model().2
                &&& events.last().position == delivery
                &&& events.last().payload matches DeviceEvent::Response(response)
                    && response.model().0 == id && response.model().2 == payload
            },
    {
        self.execution.schedule_response(id, delivery, payload)
    }

    /// 次の tick で使う回路出力、デバイス状態、イベント列を固定する。
    ///
    /// # Errors
    ///
    /// tick 番号が上限なら、現在の実行を保持する。
    pub fn prepare_tick(&mut self) -> (result: Result<PendingDeviceStateTick<'_, I, R, S>, ClockError>)
        requires old(self).execution_model().valid(),
        ensures
            result.is_ok() <==> old(self).execution_model().model().0.position_model().tick < u64::MAX,
            result matches Ok(pending) ==> {
                let time = pending.tick_model().target_model();
                let current = old(self).execution_model().model().0.position_model();
                &&& pending.before_states() == old(self).states_model()
                &&& pending.after_states() == final(self).states_model()
                &&& time.tick as int == current.tick as int + 1
                &&& time.generation == current.generation
                &&& pending.tick_model().before_model() == old(self).execution_model().model()
                &&& pending.tick_model().after_model() == final(self).execution_model().model()
                &&& pending.tick_model().before_ids() == old(self).execution_model().ids_model()
                &&& pending.tick_model().after_ids() == final(self).execution_model().ids_model()
            },
            result matches Err(error) ==> error == ClockError::TickOutOfRange
                && final(self).execution_model().model() == old(self).execution_model().model()
                && final(self).execution_model().ids_model() == old(self).execution_model().ids_model()
                && final(self).states_model() == old(self).states_model(),
    {
        let tick = self.execution.prepare_tick()?;
        Ok(PendingDeviceStateTick { tick, states: &mut self.states })
    }

    /// 現在の状態を保持したまま、次の世代の初期化を準備する。
    ///
    /// # Errors
    ///
    /// 世代が上限なら、現在の実行を保持する。
    pub fn prepare_reset(&mut self) -> (result: Result<PendingDeviceStateReset<'_, I, R, S>, ClockError>)
        requires old(self).execution_model().valid(),
        ensures
            result.is_ok() <==> old(self).execution_model().model().0.position_model().generation < u64::MAX,
            result matches Ok(pending) ==> {
                &&& pending.before_states() == old(self).states_model()
                &&& pending.after_states() == final(self).states_model()
                &&& pending.reset_model().target_model().tick == 0
                &&& pending.reset_model().target_model().generation as int ==
                    old(self).execution_model().model().0.position_model().generation as int + 1
                &&& pending.reset_model().before_model() ==
                    (old(self).execution_model().model(), old(self).execution_model().ids_model())
                &&& pending.reset_model().after_model() ==
                    (final(self).execution_model().model(), final(self).execution_model().ids_model())
            },
            result matches Err(error) ==> error == ClockError::GenerationOutOfRange
                && final(self).execution_model().model() == old(self).execution_model().model()
                && final(self).execution_model().ids_model() == old(self).execution_model().ids_model()
                && final(self).states_model() == old(self).states_model(),
    {
        let reset = self.execution.prepare_reset()?;
        Ok(PendingDeviceStateReset { reset, states: &mut self.states })
    }
}

impl<'a, I, R, S> PendingDeviceStateTick<'a, I, R, S> {
    /// 開始時に固定したデバイスの状態。
    pub closed spec fn before_states(&self) -> Seq<S> { self.states@ }

    /// 確定または取り消し後のデバイスの状態。
    #[verifier::prophetic]
    pub closed spec fn after_states(&self) -> Seq<S> { final(self.states)@ }

    /// 対応する回路と要求管理の tick。
    pub closed spec fn tick_model(&self) -> PendingDeviceEvents<'a, DeviceEvent<I, R>> { self.tick }

    /// この tick で全デバイスが読む確定状態を返す。
    pub fn states(&self) -> (states: &[S])
        ensures states@ == self.before_states(),
    {
        self.states.as_slice()
    }

    /// 全デバイスが観測する、直前に確定した回路出力。
    pub fn previous_output(&self) -> (bits: &[bool])
        ensures bits@ == self.tick_model().before_model().0.output_model(),
    {
        self.tick.previous_output()
    }

    /// 今回の確定予定の世代と tick。
    pub fn target(&self) -> (time: TickPosition)
        ensures time == self.tick_model().target_model(),
    {
        self.tick.target()
    }

    /// 指定添字以降の最初のイベントを、開始時に固定した列から借りる。
    pub fn next_event(&self, from: usize) -> (event: Option<(usize, &Event<I, R>)>)
        ensures next_event_matches(self.tick_model().before_model().2, self.tick_model().target_model(), from, event),
    {
        self.tick.next_event(from)
    }

    /// 全デバイスの評価結果を受け取り、回路とデバイスを一括で更新する。
    ///
    /// 各インスタンスの次状態を設定順に渡す。入力フレームは検査済みのポートを使って組み立てる。
    /// 成功した場合だけ、消費したイベントとホストへ渡す要求を返す。
    ///
    /// # Errors
    ///
    /// 状態数、要求先のインスタンス、ホスト要求と回路の確定の順で検査する。
    /// 失敗時は最後に確定した実行状態を保持する。
    pub fn commit<'p, N, Q>(
        self, next: Vec<S>, input: &[bool], hosts: &'p [DeviceHostRequest<N, Q>],
    ) -> (result: Result<DeviceStateTickResult<'p, I, R, N, Q>, DeviceStateTickError>)
        ensures
            result.is_err() ==> {
                let tick = self.tick_model();
                &&& self.after_states() == self.before_states()
                &&& tick.after_model().0 == tick.before_model().0
                &&& tick.after_model().1.generation_model() == tick.before_model().1.generation_model()
                &&& tick.after_model().1.requests() == tick.before_model().1.requests()
                &&& tick.after_model().2 == tick.before_model().2
                &&& tick.after_ids() == tick.before_ids()
            },
            result matches Err(DeviceStateTickError::StateCount(error)) ==> {
                &&& error.expected == self.before_states().len()
                &&& error.actual == next@.len() && error.actual != error.expected
            },
            result matches Err(DeviceStateTickError::HostInstance { request, instance }) ==> {
                &&& next@.len() == self.before_states().len()
                &&& first_unknown_host_instance(hosts@, next@.len(), request)
                &&& instance == hosts@[request as int].instance
            },
            result matches Err(DeviceStateTickError::Commit(error)) ==> {
                &&& next@.len() == self.before_states().len()
                &&& forall|i: int| 0 <= i < hosts@.len() ==>
                    (#[trigger] hosts@[i]).instance < self.before_states().len()
                &&& self.tick_model().host_request_commit_error(input@, hosts@, error)
            },
            result matches Ok(done) ==> {
                &&& self.after_states() == next@
                &&& self.after_states().len() == self.before_states().len()
                &&& forall|i: int| 0 <= i < hosts@.len() ==>
                    (#[trigger] hosts@[i]).instance < self.before_states().len()
                &&& done.outgoing.source_model() == hosts@
                &&& host_request_order(hosts@)
                &&& done.outgoing.keys_model() == host_request_keys(hosts@)
                &&& request_ranks_match(hosts@, done.outgoing.ranks_model(), done.outgoing.keys_model())
                &&& self.tick_model().request_batch_committed(
                    input@, done.outgoing.keys_model(), done.consumed@, done.outgoing.ids_model(),
                )
            },
    {
        let tick = self.tick;
        let states = self.states;
        let count = states.len();
        if next.len() != count {
            tick.cancel();
            return Err(DeviceStateTickError::StateCount(DeviceStateCountError {
                expected: count, actual: next.len(),
            }));
        }
        if let Some(request) = unknown_host_instance(hosts, count) {
            tick.cancel();
            return Err(DeviceStateTickError::HostInstance { request, instance: hosts[request].instance });
        }
        match tick.commit_host_requests(input, hosts) {
            Ok((consumed, outgoing)) => {
                *states = next;
                Ok(DeviceStateTickResult { consumed, outgoing })
            },
            Err(error) => Err(DeviceStateTickError::Commit(error)),
        }
    }

    /// 途中まで評価した tick を破棄し、最後に確定した状態を保持する。
    pub fn cancel(self)
        ensures
            self.after_states() == self.before_states(),
            self.tick_model().after_model() == self.tick_model().before_model(),
            self.tick_model().after_ids() == self.tick_model().before_ids(),
    {
        self.tick.cancel();
    }
}

impl<'a, I, R, S> PendingDeviceStateReset<'a, I, R, S> {
    /// reset 開始前のデバイス状態。
    pub closed spec fn before_states(&self) -> Seq<S> { self.states@ }

    /// 確定または取り消し後のデバイス状態。
    #[verifier::prophetic]
    pub closed spec fn after_states(&self) -> Seq<S> { final(self.states)@ }

    /// 対応する回路と要求管理の reset。
    pub closed spec fn reset_model(&self) -> PendingDeviceEventsReset<'a, DeviceEvent<I, R>> { self.reset }

    /// デバイスの reset が読む直前の確定状態を返す。
    pub fn states(&self) -> (states: &[S])
        ensures states@ == self.before_states(),
    {
        self.states.as_slice()
    }

    /// 全デバイスの初期化先となる次世代の tick 0。
    pub fn target(&self) -> (time: TickPosition)
        ensures time == self.reset_model().target_model(), time.tick == 0,
    {
        self.reset.target()
    }

    /// 各デバイスの初期化が成功したら、新世代の回路と状態を一括確定する。
    ///
    /// # Errors
    ///
    /// 次状態の件数が初期化済みデバイスの数と違う場合は、現在の実行を保持する。
    pub fn commit(self, next: Vec<S>) -> (result: Result<Vec<Event<I, R>>, DeviceStateCountError>)
        ensures
            result.is_ok() <==> self.before_states().len() == next@.len(),
            result matches Ok(events) ==> {
                let reset = self.reset_model();
                &&& self.after_states() == next@
                &&& reset.after_model().0.0.position_model() == reset.target_model()
                &&& reset.after_model().0.0.valid()
                &&& reset.after_model().0.0.vm_model().same_layout(&reset.before_model().0.0.vm_model())
                &&& reset.after_model().0.0.vm_model().reset_matches(reset.after_model().0.0.output_model())
                &&& reset.after_model().0.1.generation_model() == reset.target_model().generation
                &&& reset.after_model().1.generation_model() == reset.target_model().generation
                &&& reset.after_model().0.1.requests().len() == 0
                &&& reset.after_model().1.next_model() == 0
                &&& events@ == crate::time::events_by_reset_generation(
                    reset.before_model().0.2, reset.target_model().generation, true,
                )
                &&& reset.after_model().0.2 == crate::time::events_by_reset_generation(
                    reset.before_model().0.2, reset.target_model().generation, false,
                )
            },
            result matches Err(error) ==> {
                &&& error.expected == self.before_states().len() && error.actual == next@.len()
                &&& self.after_states() == self.before_states()
                &&& self.reset_model().after_model() == self.reset_model().before_model()
            },
    {
        let reset = self.reset;
        let states = self.states;
        let count = states.len();
        if next.len() != count {
            reset.cancel();
            return Err(DeviceStateCountError { expected: count, actual: next.len() });
        }
        let removed = reset.commit();
        *states = next;
        Ok(removed)
    }

    /// 初期化に失敗した場合に準備を取り消し、現在の実行を保持する。
    pub fn cancel(self)
        ensures
            self.after_states() == self.before_states(),
            self.reset_model().after_model() == self.reset_model().before_model(),
    {
        self.reset.cancel();
    }
}

} // verus!
