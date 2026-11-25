#![no_std]

//! tick、reset 世代、ホスト要求の通し番号を管理する。

mod clock;
mod period;
mod request_ids;

pub use clock::{ClockError, PendingClockChange, SimulationClock, TickPosition};
#[cfg(verus_only)]
pub use clock::clock_change_matches;
pub use period::exact_microseconds;
pub use request_ids::{HostRequestId, IssuedRequestIds, PendingRequestIds, RequestIdError, RequestIds};
