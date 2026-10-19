//! Verified decoding of network frames.
//!
//! Every decoder here is extracted to Lean and proved correct by
//! `cargo untrusted verify -p net` (`make verify-net`).

#![no_std]

pub mod crc32;
pub mod ethernet;
