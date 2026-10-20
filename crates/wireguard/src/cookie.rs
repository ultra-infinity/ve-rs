//! MACs and cookies (whitepaper sections 5.4.4 and 5.4.7).
//!
//! Every handshake message ends with two MACs:
//! - `mac1 = MAC(HASH(LABEL_MAC1 ‖ S^pub), msg_α)`, under the recipient's
//!   static public key, over the bytes before `mac1`. A message without a
//!   valid `mac1` is dropped before any expensive computation.
//! - `mac2 = MAC(τ, msg_β)` over the bytes before `mac2`, where `τ` is a
//!   cookie the sender got from the recipient; zeros if it has none. Under
//!   load, a responder only processes messages with a valid `mac2`, and
//!   answers the others with a cookie reply.
//!
//! The cookie of a sender is `MAC(R, A)`, where `R` is a secret the
//! responder changes every two minutes and `A` the sender's address. It is
//! sent encrypted with XChaCha20-Poly1305 under `HASH(LABEL_COOKIE ‖ S^pub)`,
//! with the sender's `mac1` as associated data.

use crate::crypto::{Crypto, KEY_LEN, MAC_LEN, XNONCE_LEN};
use crate::message::{put_bytes, CookieReply};
use untrusted::{LittleEndian, Untrusted};

/// The label of `mac1` keys.
pub const LABEL_MAC1: [u8; 8] = *b"mac1----";
/// The label of cookie keys.
pub const LABEL_COOKIE: [u8; 8] = *b"cookie--";
/// Length of a cookie.
pub const COOKIE_LEN: usize = 16;
/// Length of the two MACs at the end of a handshake message (`2 * MAC_LEN`,
/// written out so that it is a plain constant in the Lean model).
pub const MACS_LEN: usize = 32;

/// The `mac1` key of messages to the holder of `static_public`.
pub fn mac1_key<C: Crypto>(c: &C, static_public: &[u8; KEY_LEN]) -> [u8; KEY_LEN] {
    let mut out = [0u8; KEY_LEN];
    c.hash(&LABEL_MAC1, static_public, &mut out);
    out
}

/// The key of cookie replies from the holder of `static_public`.
pub fn cookie_key<C: Crypto>(c: &C, static_public: &[u8; KEY_LEN]) -> [u8; KEY_LEN] {
    let mut out = [0u8; KEY_LEN];
    c.hash(&LABEL_COOKIE, static_public, &mut out);
    out
}

/// The 16 bytes of `msg` at `pos`, which must exist.
fn mac_at(msg: &[u8], pos: usize) -> [u8; MAC_LEN] {
    // Always exactly 16 bytes, so this cannot fail. A `match` rather than
    // `unwrap_or`, which the Lean model of `core` may not cover.
    #[allow(clippy::manual_unwrap_or)]
    match Untrusted::new(&msg[pos..pos + MAC_LEN]).read_all::<[u8; MAC_LEN]>() {
        Ok(m) => m,
        Err(_) => [0; MAC_LEN],
    }
}

/// Writes `mac1` and `mac2` into the last 32 bytes of the encoded handshake
/// message `msg` (an initiation or a response, so at least 32 bytes): `mac2`
/// under `cookie` if there is one, else zeros. Returns `mac1`, which the
/// sender keeps to open a cookie reply. (The cookie is named `tau`, `τ` in the
/// paper: `cookie` would shadow this module in the generated Lean.)
pub fn add_macs<C: Crypto>(
    c: &C,
    msg: &mut [u8],
    mac1_key: &[u8; KEY_LEN],
    tau: Option<&[u8; COOKIE_LEN]>,
) -> [u8; MAC_LEN] {
    let n = msg.len();
    let mut mac1 = [0u8; MAC_LEN];
    c.mac(mac1_key, &msg[..n - MACS_LEN], &mut mac1);
    put_bytes(msg, n - MACS_LEN, &mac1);
    let mut mac2 = [0u8; MAC_LEN];
    if let Some(tau) = tau {
        c.mac(tau, &msg[..n - MAC_LEN], &mut mac2);
    }
    put_bytes(msg, n - MAC_LEN, &mac2);
    mac1
}

/// Whether the encoded handshake message `msg` has a valid `mac1` under
/// `mac1_key`.
pub fn check_mac1<C: Crypto>(c: &C, msg: &[u8], mac1_key: &[u8; KEY_LEN]) -> bool {
    let n = msg.len();
    if n < MACS_LEN {
        return false;
    }
    let mut expected = [0u8; MAC_LEN];
    c.mac(mac1_key, &msg[..n - MACS_LEN], &mut expected);
    c.ct_eq(&expected, &mac_at(msg, n - MACS_LEN))
}

/// Whether the encoded handshake message `msg` has a valid `mac2` under
/// `cookie`.
pub fn check_mac2<C: Crypto>(c: &C, msg: &[u8], tau: &[u8; COOKIE_LEN]) -> bool {
    let n = msg.len();
    if n < MACS_LEN {
        return false;
    }
    let mut expected = [0u8; MAC_LEN];
    c.mac(tau, &msg[..n - MAC_LEN], &mut expected);
    c.ct_eq(&expected, &mac_at(msg, n - MAC_LEN))
}

/// The cookie of a sender at `address` (its IP address and port, as bytes),
/// under the responder's current `secret`.
pub fn make_cookie<C: Crypto>(c: &C, secret: &[u8; KEY_LEN], address: &[u8]) -> [u8; COOKIE_LEN] {
    let mut out = [0u8; COOKIE_LEN];
    c.mac(secret, address, &mut out);
    out
}

/// A cookie reply carrying `cookie`, to a handshake message from `receiver`
/// whose `mac1` was `mac1`; `cookie_key` is the replier's own.
pub fn create_cookie_reply<C: Crypto>(
    c: &C,
    cookie_key: &[u8; KEY_LEN],
    receiver: u32,
    nonce: &[u8; XNONCE_LEN],
    tau: &[u8; COOKIE_LEN],
    mac1: &[u8; MAC_LEN],
) -> CookieReply {
    let mut encrypted_cookie = [0u8; COOKIE_LEN + 16];
    c.xaead_seal(cookie_key, nonce, mac1, tau, &mut encrypted_cookie);
    CookieReply {
        receiver: LittleEndian(receiver),
        nonce: *nonce,
        encrypted_cookie,
    }
}

/// The cookie in a reply to our message whose `mac1` was `mac1`, from the
/// peer whose cookie key is `cookie_key`. None if it does not decrypt.
pub fn consume_cookie_reply<C: Crypto>(
    c: &C,
    cookie_key: &[u8; KEY_LEN],
    msg: &CookieReply,
    mac1: &[u8; MAC_LEN],
) -> Option<[u8; COOKIE_LEN]> {
    let mut tau = [0u8; COOKIE_LEN];
    if !c.xaead_open(
        cookie_key,
        &msg.nonce,
        mac1,
        &msg.encrypted_cookie,
        &mut tau,
    ) {
        return None;
    }
    Some(tau)
}
