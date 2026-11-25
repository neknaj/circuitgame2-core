//! 外付けデバイスとホストの間で要求と応答の対応を管理する。

mod request_ids;

pub use request_ids::{HostRequestId, IssuedRequestIds, PendingRequestIds, RequestIdError, RequestIds};
