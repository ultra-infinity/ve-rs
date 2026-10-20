//! The `Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s` handshake of WireGuard
//! (whitepaper sections 5.4.2 to 5.4.5), as pure functions.
//!
//! Randomness and time are inputs: each side's ephemeral private key, its
//! sender index and the initiator's TAI64N timestamp are passed in, so every
//! function here is deterministic. The responder's processing of an initiation
//! is split in two: [`consume_initiation_static`] decrypts the initiator's
//! static public key, the caller looks that peer up (and later checks the
//! timestamp is newer than the last one, with [`timestamp_after`]), then
//! [`consume_initiation_timestamp`] decrypts the timestamp.
//!
//! The MAC fields of the messages are left zero: they are computed over the
//! encoded message by `cookie`.
//!
//! In the comments, `C` is the chaining key, `H` the hash, `S` static keys,
//! `E` ephemeral keys, `Q` the pre-shared key, and `κ`/`τ` temporary keys, as in
//! the whitepaper.

use crate::crypto::{kdf1, kdf2, kdf3, Crypto, KEY_LEN};
use crate::message::{Initiation, Response};
use untrusted::LittleEndian;

/// The Noise protocol name.
pub const CONSTRUCTION: [u8; 37] = *b"Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s";
/// WireGuard's Noise prologue.
pub const IDENTIFIER: [u8; 34] = *b"WireGuard v1 zx2c4 Jason@zx2c4.com";
/// Length of a TAI64N timestamp.
pub const TIMESTAMP_LEN: usize = 12;

/// The running state of the handshake: the chaining key `C` and the hash `H`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Chain {
    pub key: [u8; KEY_LEN],
    pub hash: [u8; KEY_LEN],
}

/// What the initiator keeps between its initiation and the response.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InitiatorState {
    pub chain: Chain,
    pub ephemeral_private: [u8; KEY_LEN],
}

/// What the responder learns from the first half of an initiation, before it
/// looks the initiator up.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InitiationStatic {
    pub chain: Chain,
    pub initiator_static: [u8; KEY_LEN],
}

/// `Hash(h ‖ data)`.
fn mix_hash<C: Crypto>(c: &C, h: &[u8; KEY_LEN], data: &[u8]) -> [u8; KEY_LEN] {
    let mut out = [0u8; KEY_LEN];
    c.hash(h, data, &mut out);
    out
}

/// The state both sides start from, given the responder's static public key:
/// `C = Hash(CONSTRUCTION)`, `H = Hash(Hash(C ‖ IDENTIFIER) ‖ S_r^pub)`.
pub fn initial_chain<C: Crypto>(c: &C, responder_static: &[u8; KEY_LEN]) -> Chain {
    let mut key = [0u8; KEY_LEN];
    c.hash(&CONSTRUCTION, &[], &mut key);
    let hash = mix_hash(c, &key, &IDENTIFIER);
    let hash = mix_hash(c, &hash, responder_static);
    Chain { key, hash }
}

/// The initiator's first message, and the state it keeps for the response.
/// None if a Diffie-Hellman result is zero.
#[allow(clippy::too_many_arguments)]
pub fn create_initiation<C: Crypto>(
    c: &C,
    local_private: &[u8; KEY_LEN],
    local_public: &[u8; KEY_LEN],
    remote_public: &[u8; KEY_LEN],
    ephemeral_private: &[u8; KEY_LEN],
    sender: u32,
    timestamp: &[u8; TIMESTAMP_LEN],
) -> Option<(Initiation, InitiatorState)> {
    let chain = initial_chain(c, remote_public);
    // E_i^pub; C = KDF1(C, E_i^pub); H = Hash(H ‖ E_i^pub).
    let mut ephemeral = [0u8; KEY_LEN];
    c.x25519_public(ephemeral_private, &mut ephemeral);
    let key = kdf1(c, &chain.key, &ephemeral);
    let hash = mix_hash(c, &chain.hash, &ephemeral);
    // (C, κ) = KDF2(C, DH(E_i^priv, S_r^pub)); static = AEAD(κ, 0, S_i^pub, H).
    let mut dh = [0u8; KEY_LEN];
    if !c.x25519(ephemeral_private, remote_public, &mut dh) {
        return None;
    }
    let (key, k) = kdf2(c, &key, &dh);
    let mut encrypted_static = [0u8; KEY_LEN + 16];
    c.aead_seal(&k, 0, &hash, local_public, &mut encrypted_static);
    let hash = mix_hash(c, &hash, &encrypted_static);
    // (C, κ) = KDF2(C, DH(S_i^priv, S_r^pub)); timestamp = AEAD(κ, 0, T, H).
    if !c.x25519(local_private, remote_public, &mut dh) {
        return None;
    }
    let (key, k) = kdf2(c, &key, &dh);
    let mut encrypted_timestamp = [0u8; TIMESTAMP_LEN + 16];
    c.aead_seal(&k, 0, &hash, timestamp, &mut encrypted_timestamp);
    let hash = mix_hash(c, &hash, &encrypted_timestamp);
    Some((
        Initiation {
            sender: LittleEndian(sender),
            ephemeral,
            encrypted_static,
            encrypted_timestamp,
            mac1: [0; 16],
            mac2: [0; 16],
        },
        InitiatorState {
            chain: Chain { key, hash },
            ephemeral_private: *ephemeral_private,
        },
    ))
}

/// The responder's processing of an initiation, up to the initiator's static
/// public key. None if a Diffie-Hellman result is zero or the key does not
/// decrypt.
pub fn consume_initiation_static<C: Crypto>(
    c: &C,
    local_private: &[u8; KEY_LEN],
    local_public: &[u8; KEY_LEN],
    msg: &Initiation,
) -> Option<InitiationStatic> {
    let chain = initial_chain(c, local_public);
    let key = kdf1(c, &chain.key, &msg.ephemeral);
    let hash = mix_hash(c, &chain.hash, &msg.ephemeral);
    let mut dh = [0u8; KEY_LEN];
    if !c.x25519(local_private, &msg.ephemeral, &mut dh) {
        return None;
    }
    let (key, k) = kdf2(c, &key, &dh);
    let mut initiator_static = [0u8; KEY_LEN];
    if !c.aead_open(&k, 0, &hash, &msg.encrypted_static, &mut initiator_static) {
        return None;
    }
    let hash = mix_hash(c, &hash, &msg.encrypted_static);
    Some(InitiationStatic {
        chain: Chain { key, hash },
        initiator_static,
    })
}

/// The rest of the responder's processing of an initiation, once the
/// initiator is known: the state and the timestamp. None if the
/// Diffie-Hellman result is zero or the timestamp does not decrypt.
pub fn consume_initiation_timestamp<C: Crypto>(
    c: &C,
    local_private: &[u8; KEY_LEN],
    st: &InitiationStatic,
    msg: &Initiation,
) -> Option<(Chain, [u8; TIMESTAMP_LEN])> {
    let mut dh = [0u8; KEY_LEN];
    if !c.x25519(local_private, &st.initiator_static, &mut dh) {
        return None;
    }
    let (key, k) = kdf2(c, &st.chain.key, &dh);
    let mut timestamp = [0u8; TIMESTAMP_LEN];
    if !c.aead_open(
        &k,
        0,
        &st.chain.hash,
        &msg.encrypted_timestamp,
        &mut timestamp,
    ) {
        return None;
    }
    let hash = mix_hash(c, &st.chain.hash, &msg.encrypted_timestamp);
    Some((Chain { key, hash }, timestamp))
}

/// Whether the TAI64N timestamp `a` is later than `b`: both are big-endian,
/// so this compares them as byte strings.
pub fn timestamp_after(a: &[u8; TIMESTAMP_LEN], b: &[u8; TIMESTAMP_LEN]) -> bool {
    let mut i = 0;
    while i < TIMESTAMP_LEN {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
        i += 1;
    }
    false
}

/// The responder's message, and its final state. None if a Diffie-Hellman
/// result is zero.
#[allow(clippy::too_many_arguments)]
pub fn create_response<C: Crypto>(
    c: &C,
    chain: &Chain,
    initiator_ephemeral: &[u8; KEY_LEN],
    initiator_static: &[u8; KEY_LEN],
    psk: &[u8; KEY_LEN],
    ephemeral_private: &[u8; KEY_LEN],
    sender: u32,
    receiver: u32,
) -> Option<(Response, Chain)> {
    // E_r^pub; C = KDF1(C, E_r^pub); H = Hash(H ‖ E_r^pub).
    let mut ephemeral = [0u8; KEY_LEN];
    c.x25519_public(ephemeral_private, &mut ephemeral);
    let key = kdf1(c, &chain.key, &ephemeral);
    let hash = mix_hash(c, &chain.hash, &ephemeral);
    // C = KDF1(C, DH(E_r^priv, E_i^pub)); C = KDF1(C, DH(E_r^priv, S_i^pub)).
    let mut dh = [0u8; KEY_LEN];
    if !c.x25519(ephemeral_private, initiator_ephemeral, &mut dh) {
        return None;
    }
    let key = kdf1(c, &key, &dh);
    if !c.x25519(ephemeral_private, initiator_static, &mut dh) {
        return None;
    }
    let key = kdf1(c, &key, &dh);
    // (C, τ, κ) = KDF3(C, Q); H = Hash(H ‖ τ); empty = AEAD(κ, 0, ε, H).
    let (key, t, k) = kdf3(c, &key, psk);
    let hash = mix_hash(c, &hash, &t);
    let mut encrypted_nothing = [0u8; 16];
    c.aead_seal(&k, 0, &hash, &[], &mut encrypted_nothing);
    let hash = mix_hash(c, &hash, &encrypted_nothing);
    Some((
        Response {
            sender: LittleEndian(sender),
            receiver: LittleEndian(receiver),
            ephemeral,
            encrypted_nothing,
            mac1: [0; 16],
            mac2: [0; 16],
        },
        Chain { key, hash },
    ))
}

/// The initiator's processing of the response: its final state. None if a
/// Diffie-Hellman result is zero or the empty payload does not decrypt.
pub fn consume_response<C: Crypto>(
    c: &C,
    st: &InitiatorState,
    local_private: &[u8; KEY_LEN],
    psk: &[u8; KEY_LEN],
    msg: &Response,
) -> Option<Chain> {
    let key = kdf1(c, &st.chain.key, &msg.ephemeral);
    let hash = mix_hash(c, &st.chain.hash, &msg.ephemeral);
    let mut dh = [0u8; KEY_LEN];
    if !c.x25519(&st.ephemeral_private, &msg.ephemeral, &mut dh) {
        return None;
    }
    let key = kdf1(c, &key, &dh);
    if !c.x25519(local_private, &msg.ephemeral, &mut dh) {
        return None;
    }
    let key = kdf1(c, &key, &dh);
    let (key, t, k) = kdf3(c, &key, psk);
    let hash = mix_hash(c, &hash, &t);
    let mut nothing = [0u8; 0];
    if !c.aead_open(&k, 0, &hash, &msg.encrypted_nothing, &mut nothing) {
        return None;
    }
    let hash = mix_hash(c, &hash, &msg.encrypted_nothing);
    Some(Chain { key, hash })
}

/// The transport keys of a completed handshake: `KDF2(C, ε)`, the first for
/// initiator to responder, the second for responder to initiator.
pub fn transport_keys<C: Crypto>(c: &C, chain: &Chain) -> ([u8; KEY_LEN], [u8; KEY_LEN]) {
    kdf2(c, &chain.key, &[])
}
