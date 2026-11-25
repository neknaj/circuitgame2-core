//! 外付けデバイスとホストの間で要求と応答の対応を管理する。

mod ledger;
mod request_ids;
mod response;
mod scheduling;

pub use ledger::{DeliveryError, PendingDelivery, RegisterRequestError, RequestLedger, ResponseKey};
#[cfg(verus_only)]
pub use ledger::{busy_at, delivery_matches, response_update};
pub use request_ids::{HostRequestId, IssuedRequestIds, PendingRequestIds, RequestIdError, RequestIds};

pub use response::{HostResponseError, ResponseSlot, ResponseStatus};
pub use scheduling::{ScheduleResponseError, ScheduledResponse};
