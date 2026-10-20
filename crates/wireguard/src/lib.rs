//! A verified, sans-IO WireGuard core.
//!
//! Every item of this crate is extracted to Lean and proved correct by
//! `cargo untrusted verify -p wireguard --extract-all --link net=Net`
//! (`make verify-wireguard`). It reuses the verified decoders of `net` for the
//! IP packets it carries.

#![no_std]

pub mod cookie;
pub mod crypto;
pub mod inner;
pub mod message;
pub mod noise;
pub mod replay;
