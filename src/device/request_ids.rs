//! 1回の実行の各 reset 世代で、ホスト要求の通し番号を確定する。

use vstd::prelude::*;

verus! {

/// 応答を発行元の要求へ結び付ける、実行内の識別子。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HostRequestId {
    /// 実行設定におけるデバイスの識別子。
    pub instance: usize,
    /// 要求を発行した reset 世代。
    pub generation: u64,
    /// 同じ世代で要求を確定した順の番号。0から始まる。
    pub serial: u64,
}

/// 要求 ID 用の通し番号を割り当てられない理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RequestIdError {
    /// 残りの通し番号では一括確定するすべての要求を識別できない。
    SerialOutOfRange,
}

/// 1回の実行の一つの reset 世代に属する、要求番号の割り当て状態。
///
/// ホストは同じ世代内のすべてのデバイスでこの状態を共有する。
pub struct RequestIds {
    generation: u64,
    // 最後の u64 番号を発行した後も、その次の位置を表せるようにする。
    next: u128,
}

/// 要求番号を確定するまで、同じ世代の割り当て状態を排他的に借りる。
pub struct PendingRequestIds<'a> {
    sequence: &'a mut RequestIds,
    count: u64,
}

/// 1回の確定で取り出した、通し番号順の要求番号の範囲。
pub struct IssuedRequestIds {
    generation: u64,
    first: u128,
    count: u64,
}

impl RequestIds {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        self.next as int <= u64::MAX as int + 1
    }

    /// 割り当て状態が属する reset 世代。
    pub closed spec fn generation_model(&self) -> u64 { self.generation }

    /// 次に発行する通し番号。全件発行後の値は `u64::MAX + 1`。
    pub closed spec fn next_model(&self) -> int { self.next as int }

    /// 指定の reset 世代を、未発行の状態から開始する。
    ///
    /// 新しい世代を確定したときに作る。同じ世代内では既存の割り当て状態を使い続ける。
    pub fn new(generation: u64) -> (sequence: Self)
        ensures sequence.generation_model() == generation, sequence.next_model() == 0,
    {
        Self { generation, next: 0 }
    }

    /// この世代で対象件数を続けて発行できることを表す。
    pub open spec fn fits(&self, count: u64) -> bool {
        self.next_model() + count as int <= u64::MAX as int + 1
    }

    /// 要求の件数を受け取り、番号の範囲を準備する。
    ///
    /// 通知は件数に含めない。デバイスの実行設定順と各要求リストの順に番号を使う。
    ///
    /// # Errors
    ///
    /// 番号が足りなければ一件も発行せず、割り当て状態を保持してエラーを返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::device::{HostRequestId, RequestIdError, RequestIds};
    ///
    /// let mut sequence = RequestIds::new(4);
    /// sequence.prepare(2).unwrap().cancel();
    /// let bulk = sequence.prepare(u64::MAX).unwrap().commit();
    /// assert_eq!(bulk.id_at(0, 1), Some(HostRequestId {
    ///     instance: 1, generation: 4, serial: 0,
    /// }));
    /// assert!(matches!(sequence.prepare(2), Err(RequestIdError::SerialOutOfRange)));
    /// let last = sequence.prepare(1).unwrap().commit();
    /// assert_eq!(last.id_at(0, 3).unwrap().serial, u64::MAX);
    /// assert!(last.id_at(1, 3).is_none());
    /// assert!(matches!(sequence.prepare(1), Err(RequestIdError::SerialOutOfRange)));
    /// assert!(sequence.prepare(0).unwrap().commit().id_at(0, 1).is_none());
    /// ```
    pub fn prepare(&mut self, count: u64) -> (result: Result<PendingRequestIds<'_>, RequestIdError>)
        ensures
            result.is_ok() <==> old(self).fits(count),
            match result {
                Ok(pending) => {
                    &&& pending.before_model() == *old(self)
                    &&& pending.after_model() == *final(self)
                    &&& pending.count_model() == count
                },
                Err(error) => error == RequestIdError::SerialOutOfRange && *final(self) == *old(self),
            },
    {
        proof { use_type_invariant(&*self); }
        if self.next + count as u128 > u64::MAX as u128 + 1 {
            return Err(RequestIdError::SerialOutOfRange);
        }
        Ok(PendingRequestIds { sequence: self, count })
    }
}

impl<'a> PendingRequestIds<'a> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool { self.sequence.fits(self.count) }

    /// 準備時の割り当て状態。
    pub closed spec fn before_model(&self) -> RequestIds { *self.sequence }

    /// 確定または取り消しの後の割り当て状態。
    #[verifier::prophetic]
    pub closed spec fn after_model(&self) -> RequestIds { *final(self.sequence) }

    /// 準備した要求の件数。
    pub closed spec fn count_model(&self) -> u64 { self.count }

    /// tick の成功後に要求番号を確定し、発行に使う番号の範囲を返す。
    pub fn commit(self) -> (issued: IssuedRequestIds)
        ensures
            issued.generation_model() == self.before_model().generation_model(),
            issued.first_model() == self.before_model().next_model(),
            issued.count_model() == self.count_model(),
            self.after_model().next_model() == issued.first_model() + issued.count_model() as int,
            self.after_model().generation_model() == issued.generation_model(),
    {
        proof { use_type_invariant(&self); }
        let Self { sequence, count } = self;
        let issued = IssuedRequestIds {
            generation: sequence.generation,
            first: sequence.next,
            count,
        };
        sequence.next += count as u128;
        issued
    }

    /// 確定前の失敗や中断により取り消し、通し番号を進めずに返す。
    pub fn cancel(self)
        ensures self.after_model() == self.before_model(),
    {
    }
}

impl IssuedRequestIds {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        self.first as int + self.count as int <= u64::MAX as int + 1
    }

    /// 発行した番号の世代。
    pub closed spec fn generation_model(&self) -> u64 { self.generation }

    /// 最初に発行した通し番号。空の範囲では発行前の次番号。
    pub closed spec fn first_model(&self) -> int { self.first as int }

    /// 発行した番号の件数。
    pub closed spec fn count_model(&self) -> u64 { self.count }

    /// 設定と要求リストの順に並べた要求へ、確定済みの番号を付ける。
    ///
    /// `index` はこの確定で取り出した範囲内の0始まりの添字。
    /// 範囲外なら `None` を返す。インスタンスの識別子は呼び出し側が指定する。
    pub fn id_at(&self, index: u64, instance: usize) -> (result: Option<HostRequestId>)
        ensures
            result.is_some() <==> index < self.count_model(),
            result matches Some(id) ==> {
                &&& id.instance == instance
                &&& id.generation == self.generation_model()
                &&& id.serial as int == self.first_model() + index as int
            },
    {
        proof { use_type_invariant(self); }
        if index >= self.count { return None; }
        Some(HostRequestId {
            instance,
            generation: self.generation,
            serial: (self.first + index as u128) as u64,
        })
    }
}

proof fn representative_serial_boundaries() {
    let last = RequestIds { generation: 0, next: u64::MAX as u128 };
    assert(last.fits(1)) by (compute);
    assert(!last.fits(2)) by (compute);

    let exhausted = RequestIds { generation: 0, next: (u64::MAX as int + 1) as u128 };
    assert(exhausted.fits(0)) by (compute);
    assert(!exhausted.fits(1)) by (compute);
}

} // verus!
