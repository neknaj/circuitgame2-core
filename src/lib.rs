//! NCG2 の CLI と Web で共用する API を公開する。
//!
//! 回路ソースの構文解析には [`syntax`] を使う。

#![no_std]

extern crate alloc;

pub mod editor;
pub mod netlist;
pub mod project;
pub use circuitgame2_syntax as syntax;
