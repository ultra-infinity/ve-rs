//! Verified decoding of network frames.
//!
//! Every decoder here is extracted to Lean and proved correct by
//! `cargo untrusted verify -p net` (`make verify-net`).

#![no_std]

pub mod arp;
pub mod crc32;
pub mod ethernet;
pub mod icmp;
pub mod inet;
pub mod ipv4;
pub mod ipv6;
pub mod udp;
