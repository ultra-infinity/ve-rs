//! A verified, sans-IO packet filter that blocks advertising (and any other
//! listed) domains.
//!
//! Ad content travels encrypted, so the filter acts where a domain name is
//! visible in the clear, as DNS-based blockers and SNI firewalls do:
//! - a DNS query for a listed domain (or a subdomain of one) is answered at
//!   once with NXDOMAIN, so the name does not resolve;
//! - a TLS ClientHello naming a listed domain in its server name indication
//!   is dropped, so the connection is never made.
//!
//! Every item of this crate is extracted to Lean and proved correct
//! (`make verify-diomede`), building on the verified decoders and encoders of
//! `net`.

#![no_std]

pub mod blocklist;
pub mod dns;
pub mod filter;
pub mod name;
pub mod tls;
