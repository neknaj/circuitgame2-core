//! 1件の応答を、発行済みの要求と配送予定の tick に対応付ける。

#[cfg(not(verus_only))]
use verus_builtin_macros::verus;
#[cfg(verus_only)]
use vstd::prelude::*;

use super::{HostRequestId, TickPosition};

verus! {

/// 受け取った応答を保留できなかった理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HostResponseError {
    /// 要求または応答が、配送先と異なる reset 世代を指している。
    DifferentGeneration,
    /// 応答のインスタンスまたは通し番号が要求と一致しない。
    UnknownRequest,
    /// 同じ要求の応答をすでに受理した。
    DuplicateResponse,
    /// 配送予定が要求を発行した tick 以前にある。
    TooEarly,
}

/// 発行済み要求に対する応答の状態。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResponseStatus {
    /// ホストからの応答をまだ受理していない。
    Awaiting,
    /// 受理済みの応答を指定した tick まで保持している。
    Held(TickPosition),
    /// 応答を回路とデバイスの更新と一緒に消費した。
    Consumed(TickPosition),
}

/// 1件の要求に対応する応答の受理と消費を管理する。
///
/// payload の型はデバイスの記述に従って別途検査し、応答が受理されたときに保留する。
#[derive(Clone, Copy)]
pub struct ResponseSlot {
    id: HostRequestId,
    issued_tick: u64,
    status: ResponseStatus,
}

impl ResponseSlot {
    /// 発行済みの要求 ID。
    pub closed spec fn id_model(&self) -> HostRequestId { self.id }

    /// 要求を確定した同世代内の tick 番号。
    pub closed spec fn issued_model(&self) -> u64 { self.issued_tick }

    /// 応答の受理・配送状態。
    pub closed spec fn status_model(&self) -> ResponseStatus { self.status }

    /// 応答を待つ要求の ID を返す。
    pub fn id(&self) -> (id: HostRequestId)
        ensures id == self.id_model(),
    {
        self.id
    }

    /// 応答の受理・配送状態を返す。
    pub fn status(&self) -> (status: ResponseStatus)
        ensures status == self.status_model(),
    {
        self.status
    }

    /// 指定の tick の開始時点で、この要求のタグを使用中かを返す。
    pub fn tag_busy_at(&self, tick: u64) -> (busy: bool)
        ensures busy == busy_at(self.status_model(), tick),
    {
        match self.status {
            ResponseStatus::Consumed(delivered) => tick <= delivered.tick,
            ResponseStatus::Awaiting | ResponseStatus::Held(_) => true,
        }
    }

    /// 指定の要求を、応答待ちの状態で登録する。
    pub fn new(id: HostRequestId, issued_tick: u64) -> (slot: Self)
        ensures
            slot.id_model() == id,
            slot.issued_model() == issued_tick,
            slot.status_model() == ResponseStatus::Awaiting,
    {
        Self { id, issued_tick, status: ResponseStatus::Awaiting }
    }

    /// 応答 ID と配送時刻を照合し、最初の違反を選ぶ。
    pub open spec fn response_error(&self, response: HostRequestId, position: TickPosition) -> Option<HostResponseError> {
        if response.generation != position.generation || self.id_model().generation != position.generation {
            Some(HostResponseError::DifferentGeneration)
        } else if response != self.id_model() {
            Some(HostResponseError::UnknownRequest)
        } else if self.status_model() != ResponseStatus::Awaiting {
            Some(HostResponseError::DuplicateResponse)
        } else if position.tick <= self.issued_model() {
            Some(HostResponseError::TooEarly)
        } else {
            None
        }
    }

    /// 応答 ID を照合し、適用先の tick まで配送を保留する。
    ///
    /// 呼び出し側は、現在の世代で入力列をまだ確定していない後続 tick を渡す。
    /// 先に payload の型を検査し、受理後に同じ時刻でイベントを記録する。
    ///
    /// # Errors
    ///
    /// 異なる世代、要求 ID の不一致、受理済みの応答、発行以前の tick の順に検査する。
    /// 失敗した場合は、保留中の応答も配送時刻も変更しない。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_device_timing::{HostRequestId, HostResponseError, ResponseSlot, TickPosition};
    ///
    /// let id = HostRequestId { instance: 2, generation: 4, serial: 7 };
    /// let mut slot = ResponseSlot::new(id, 10);
    /// let issued = TickPosition { generation: 4, tick: 10 };
    /// let delivery = TickPosition { generation: 4, tick: 11 };
    /// let next_generation = TickPosition { generation: 5, tick: 11 };
    ///
    /// assert_eq!(slot.receive(id, next_generation), Err(HostResponseError::DifferentGeneration));
    /// assert_eq!(slot.receive(id, issued), Err(HostResponseError::TooEarly));
    /// assert_eq!(slot.receive(id, delivery), Ok(delivery));
    /// assert_eq!(slot.receive(id, delivery), Err(HostResponseError::DuplicateResponse));
    /// assert!(!slot.consume_at(issued));
    /// assert!(slot.consume_at(delivery));
    /// assert!(!slot.consume_at(delivery));
    /// assert_eq!(slot.receive(id, delivery), Err(HostResponseError::DuplicateResponse));
    /// ```
    pub fn receive(&mut self, response: HostRequestId, position: TickPosition)
        -> (result: Result<TickPosition, HostResponseError>)
        ensures
            match result {
                Ok(received) => {
                    &&& old(self).response_error(response, position).is_none()
                    &&& received == position
                    &&& final(self).status_model() == ResponseStatus::Held(position)
                    &&& final(self).id_model() == old(self).id_model()
                    &&& final(self).issued_model() == old(self).issued_model()
                },
                Err(error) => old(self).response_error(response, position) == Some(error)
                    && *final(self) == *old(self),
            },
    {
        if response.generation != position.generation || self.id.generation != position.generation {
            return Err(HostResponseError::DifferentGeneration);
        }
        if response.instance != self.id.instance || response.serial != self.id.serial {
            return Err(HostResponseError::UnknownRequest);
        }
        assert(response == self.id);
        let ResponseStatus::Awaiting = self.status else {
            return Err(HostResponseError::DuplicateResponse);
        };
        if position.tick <= self.issued_tick {
            return Err(HostResponseError::TooEarly);
        }
        self.status = ResponseStatus::Held(position);
        Ok(position)
    }

    /// 指定の tick を確定した場合に、保留中の応答を消費する。
    ///
    /// 配送予定と一致する場合だけ `true` を返す。取り消し時はこの関数を呼ばない。
    pub fn consume_at(&mut self, position: TickPosition) -> (consumed: bool)
        ensures
            consumed <==> old(self).status_model() == ResponseStatus::Held(position),
            consumed ==> final(self).status_model() == ResponseStatus::Consumed(position)
                && final(self).id_model() == old(self).id_model()
                && final(self).issued_model() == old(self).issued_model(),
            !consumed ==> *final(self) == *old(self),
    {
        let ResponseStatus::Held(expected) = self.status else { return false; };
        if expected.generation != position.generation || expected.tick != position.tick {
            return false;
        }
        assert(expected == position);
        self.status = ResponseStatus::Consumed(position);
        true
    }
}

/// 応答を消費した tick までタグを占有する。
pub open spec fn busy_at(status: ResponseStatus, tick: u64) -> bool {
    match status {
        ResponseStatus::Consumed(delivered) => tick <= delivered.tick,
        _ => true,
    }
}

} // verus!
