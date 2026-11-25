//! 外付けデバイスとホストの間で要求と応答の対応を管理する。

mod ledger;
mod request_ids;
mod response;

pub use ledger::{RegisterRequestError, RequestLedger};
#[cfg(verus_only)]
pub use ledger::{busy_at, response_update};
pub use request_ids::{HostRequestId, IssuedRequestIds, PendingRequestIds, RequestIdError, RequestIds};

pub use response::{HostResponseError, ResponseSlot, ResponseStatus};
