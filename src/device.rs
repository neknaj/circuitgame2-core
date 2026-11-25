//! 外付けデバイスとホストの間で要求と応答の対応を管理する。

mod events;
mod host_requests;
mod ledger;
mod scheduling;
mod session;
mod state_session;

pub use events::{DeviceEvent, ScheduleInputError};
#[cfg(verus_only)]
pub use events::{device_response_keys, device_response_keys_step};
pub use host_requests::{CommittedHostRequest, CommittedHostRequests, DeviceHostRequest, HostRequest, HostRequestCommitError};
#[cfg(verus_only)]
pub use host_requests::{host_request_keys, host_request_order, request_ranks_match};
pub use ledger::{BatchRegistrationError, RequestKey, DeliveryError, PendingDelivery, RegisterRequestError, RequestLedger, ResponseKey};
#[cfg(verus_only)]
pub use ledger::{first_batch_request_error, delivery_matches, issued_rows_match, response_update, valid_request_batch};
pub use circuitgame2_device_timing::{HostRequestId, IssuedRequestIds, PendingRequestIds, RequestIdError, RequestIds};

#[cfg(verus_only)]
pub use circuitgame2_device_timing::busy_at;
pub use circuitgame2_device_timing::{HostResponseError, ResponseSlot, ResponseStatus};
pub use scheduling::{QueuedResponse, ResponseTickError, ScheduleResponseError, ScheduledResponse};

#[cfg(verus_only)]
pub use scheduling::{queued_response_keys, response_keys};

pub use session::{DeviceEventSession, DeviceResponseSession, DeviceSession, PendingDeviceEvents, PendingDeviceEventsReset, PendingDeviceReset, PendingDeviceTick, RequestBatchTickError, RequestIssueError};

pub use state_session::{DeviceStateSession, DeviceStateCountError, DeviceStateTickError, DeviceStateTickResult, PendingDeviceStateTick, PendingDeviceStateReset, StatefulInputError};
