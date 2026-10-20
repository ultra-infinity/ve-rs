//! Transport data (whitepaper section 5.4.6): IP packets, encrypted under the
//! keys of a completed handshake.
//!
//! A packet is padded with zeros to a multiple of 16 bytes and sealed with
//! ChaCha20-Poly1305, the message counter as the nonce. On receipt, the
//! checks are made in the order of the Linux implementation: the packet must
//! be authentic (the counter is part of the nonce, so a forged counter cannot
//! move the replay window), its counter new, and then either empty (a
//! keepalive) or a well-formed IP packet, checked with the verified decoders
//! of `net`, whose source address routes back to the peer it came from.
//!
//! `proofs/Wireguard/TransportTop.lean` proves that [`encrypt`] writes a
//! transport message that decodes to the header and the sealed padded packet,
//! and that [`receive`] accepts, records and delivers exactly as above.

use crate::allowed_ips::AllowedIps;
use crate::crypto::{Crypto, AEAD_TAG_LEN, KEY_LEN};
use crate::message::{TransportHeader, TRANSPORT_HEADER_LEN};
use crate::replay::Replay;
use net::ipv4::Ipv4Packet;
use net::ipv6::Ipv6Packet;
use untrusted::{LittleEndian, Untrusted};

/// The plaintext of a packet of `len` bytes, padded to a multiple of 16.
pub fn padded_len(len: usize) -> usize {
    // Not `is_multiple_of`, which the Lean model of `core` may not cover.
    #[allow(clippy::manual_is_multiple_of)]
    if len % 16 == 0 {
        len
    } else {
        len / 16 * 16 + 16
    }
}

/// Encrypts `packet` into a transport message to `receiver`, with `counter`,
/// in `out`; `work` holds the padded plaintext. Returns the message's length,
/// or None if `work` or `out` is too short.
pub fn encrypt<C: Crypto>(
    c: &C,
    key: &[u8; KEY_LEN],
    receiver: u32,
    counter: u64,
    packet: &[u8],
    work: &mut [u8],
    out: &mut [u8],
) -> Option<usize> {
    let p = padded_len(packet.len());
    if work.len() < p || out.len() < TRANSPORT_HEADER_LEN + p + AEAD_TAG_LEN {
        return None;
    }
    let mut i = 0;
    while i < p {
        work[i] = if i < packet.len() { packet[i] } else { 0 };
        i += 1;
    }
    let header = TransportHeader {
        receiver: LittleEndian(receiver),
        counter: LittleEndian(counter),
    }
    .encode();
    let mut j = 0;
    while j < TRANSPORT_HEADER_LEN {
        out[j] = header[j];
        j += 1;
    }
    let n = TRANSPORT_HEADER_LEN + p + AEAD_TAG_LEN;
    c.aead_seal(
        key,
        counter,
        &[],
        &work[..p],
        &mut out[TRANSPORT_HEADER_LEN..n],
    );
    Some(n)
}

/// An IP packet's addresses and length, as `u128`s for both families (an
/// IPv4 address in the low 32 bits).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Inner {
    pub v6: bool,
    pub src: u128,
    pub dst: u128,
    /// The packet's own length; any bytes after it are padding.
    pub len: usize,
}

/// The addresses and length of `packet`, if it starts with a well-formed IPv4
/// or IPv6 packet (anything after it is padding).
pub fn inner(packet: &[u8]) -> Option<Inner> {
    if packet.is_empty() {
        return None;
    }
    let version = packet[0] / 16;
    if version == 4 {
        match Untrusted::new(packet).validate::<Ipv4Packet>() {
            Ok(p) => Some(Inner {
                v6: false,
                src: p.header.src.0 as u128,
                dst: p.header.dst.0 as u128,
                len: p.header.total_len.0 as usize,
            }),
            Err(_) => None,
        }
    } else if version == 6 {
        match Untrusted::new(packet).validate::<Ipv6Packet>() {
            Ok(p) => Some(Inner {
                v6: true,
                src: p.header.src.0,
                dst: p.header.dst.0,
                // The 40-byte fixed header, then the payload.
                len: 40 + p.header.payload_len.0 as usize,
            }),
            Err(_) => None,
        }
    } else {
        None
    }
}

/// What became of a received transport message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Received {
    /// Not authentic, replayed, not an IP packet, or from an address the
    /// peer is not allowed.
    Drop,
    /// Authentic and new, but empty.
    Keepalive,
    /// An IP packet of this length, at the start of `out`.
    Packet(usize),
}

/// Receives the encrypted packet `body` (ciphertext and tag) of a transport
/// message with `counter`, from `peer`, under `key`: decrypts it into `out`,
/// and records the counter in `window` if it is authentic.
#[allow(clippy::too_many_arguments)]
pub fn receive<C: Crypto>(
    c: &C,
    key: &[u8; KEY_LEN],
    window: &mut Replay,
    table: &AllowedIps,
    peer: u16,
    counter: u64,
    body: &[u8],
    out: &mut [u8],
) -> Received {
    if body.len() < AEAD_TAG_LEN {
        return Received::Drop;
    }
    let n = body.len() - AEAD_TAG_LEN;
    if out.len() < n {
        return Received::Drop;
    }
    if !c.aead_open(key, counter, &[], body, &mut out[..n]) {
        return Received::Drop;
    }
    if !window.check_and_update(counter) {
        return Received::Drop;
    }
    if n == 0 {
        return Received::Keepalive;
    }
    match inner(&out[..n]) {
        Some(p) => match table.lookup(p.v6, p.src) {
            Some(q) if q == peer => Received::Packet(p.len),
            _ => Received::Drop,
        },
        None => Received::Drop,
    }
}
