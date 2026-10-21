//! A runtime for userspace WireGuard interfaces around the verified sans-IO
//! [`wireguard::device::Device`], without the Rust standard library: the
//! configuration file, the operating system (packet and raw sockets, a TUN
//! device, the clocks, the kernel's randomness, signals) and the event loop.
//!
//! It contains no protocol logic. The interface's addresses, MTU and routes
//! are set outside, with `ip`.

#![cfg_attr(not(test), no_std)]

pub mod config;
pub mod runner;
pub mod sys;

pub use runner::{run, Hook, Inner, Plain};
