#![no_std]

//! RP2040 と RP2350 の実行ファームウェアで使う通信処理。

#[cfg(feature = "i2c")]
mod i2c_transport;
