#![no_std]

//! tick、reset 世代、ホスト要求の通し番号を管理する。
//!
//! 固定容量の台帳では、要求と応答の照合から配送までを動的割り当てなしで扱う。

mod clock;
mod fixed_requests;
mod i2c_ports;
mod i2c_transfer;
mod period;
mod request_ids;
mod response;

pub use clock::{ClockError, PendingClockChange, SimulationClock, TickPosition};
#[cfg(verus_only)]
pub use clock::clock_change_matches;
pub use i2c_ports::{i2c_port_bit, i2c_port_octet};
pub use i2c_transfer::{I2cTransfer, I2cTransferError, I2cTransferKind};
#[cfg(verus_only)]
pub use i2c_ports::{i2c_octet_bit, i2c_octet_matches, i2c_port_bytes_match};
#[cfg(verus_only)]
pub use i2c_transfer::{i2c_transfer_error, i2c_transfer_kind};
pub use period::exact_microseconds;
pub use request_ids::{HostRequestId, IssuedRequestIds, PendingRequestIds, RequestIdError, RequestIds, RequestKey};

pub use fixed_requests::{
    CommittedFixedTick, FixedIssueError, FixedPrepareError, FixedReceiveError, FixedRequestLedger,
    FixedRequestRow, FixedTickError, PreparedFixedTick,
};
#[cfg(verus_only)]
pub use fixed_requests::delivery_due_at;
pub use response::{HostResponseError, ResponseSlot, ResponseStatus};
#[cfg(verus_only)]
pub use response::busy_at;
