//! The cryptographic primitives WireGuard uses, behind one trait, and the
//! key derivation built on them (whitepaper section 5.4).
//!
//! [`Crypto`] is the only way this crate reaches cryptography. Its
//! implementation (`wireguard-libcrux`) is not part of this crate and is not
//! extracted. The proofs assume it computes the functions its documentation
//! states; nothing else is assumed. HMAC and the KDFs are written here, on top
//! of [`Crypto::hash`], and are proved.

/// Length of keys, hashes and Diffie-Hellman results.
pub const KEY_LEN: usize = 32;
/// Length of a MAC.
pub const MAC_LEN: usize = 16;
/// Length of an XChaCha20-Poly1305 nonce.
pub const XNONCE_LEN: usize = 24;
/// Length of an AEAD tag.
pub const AEAD_TAG_LEN: usize = 16;
/// The BLAKE2s block length, used by HMAC.
pub const BLOCK_LEN: usize = 64;

/// The primitives of `Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s`, plus the
/// XChaCha20-Poly1305 used by cookies.
///
/// Every method is deterministic and never panics when called as documented.
pub trait Crypto {
    /// X25519: `out = private · public`. Returns false iff `out` is all zeros
    /// (`public` has a small order), which callers must treat as failure.
    fn x25519(
        &self,
        private: &[u8; KEY_LEN],
        public: &[u8; KEY_LEN],
        out: &mut [u8; KEY_LEN],
    ) -> bool;
    /// The X25519 public key of `private`.
    fn x25519_public(&self, private: &[u8; KEY_LEN], out: &mut [u8; KEY_LEN]);
    /// BLAKE2s-256 of `a ‖ b`.
    fn hash(&self, a: &[u8], b: &[u8], out: &mut [u8; KEY_LEN]);
    /// Keyed BLAKE2s with a 16-byte output: `MAC(key, input)`. The key is 1 to
    /// 32 bytes: a 32-byte key for `mac1` and cookies, a 16-byte cookie for
    /// `mac2`.
    fn mac(&self, key: &[u8], input: &[u8], out: &mut [u8; MAC_LEN]);
    /// ChaCha20-Poly1305 encryption of `plaintext` with associated data `ad`,
    /// under the nonce made of 4 zero bytes then `counter`, little-endian.
    /// `out` must be exactly `plaintext.len() + 16` bytes: the ciphertext,
    /// then the tag.
    fn aead_seal(
        &self,
        key: &[u8; KEY_LEN],
        counter: u64,
        ad: &[u8],
        plaintext: &[u8],
        out: &mut [u8],
    );
    /// The inverse of [`Crypto::aead_seal`]: `out` must be exactly
    /// `ciphertext.len() - 16` bytes. Returns true, with the plaintext in
    /// `out`, iff `ciphertext` is authentic.
    fn aead_open(
        &self,
        key: &[u8; KEY_LEN],
        counter: u64,
        ad: &[u8],
        ciphertext: &[u8],
        out: &mut [u8],
    ) -> bool;
    /// XChaCha20-Poly1305 encryption, as [`Crypto::aead_seal`] with a 24-byte
    /// nonce.
    fn xaead_seal(
        &self,
        key: &[u8; KEY_LEN],
        nonce: &[u8; XNONCE_LEN],
        ad: &[u8],
        plaintext: &[u8],
        out: &mut [u8],
    );
    /// The inverse of [`Crypto::xaead_seal`].
    fn xaead_open(
        &self,
        key: &[u8; KEY_LEN],
        nonce: &[u8; XNONCE_LEN],
        ad: &[u8],
        ciphertext: &[u8],
        out: &mut [u8],
    ) -> bool;
    /// Whether `a == b`, in time independent of their contents.
    fn ct_eq(&self, a: &[u8; MAC_LEN], b: &[u8; MAC_LEN]) -> bool;
}

/// `HMAC(key, msg)` over BLAKE2s (RFC 2104 with a 64-byte block).
pub fn hmac<C: Crypto>(c: &C, key: &[u8; KEY_LEN], msg: &[u8]) -> [u8; KEY_LEN] {
    // The key, zero-padded to a block, XORed with the inner pad.
    let mut pad = [0u8; BLOCK_LEN];
    let mut i = 0;
    while i < BLOCK_LEN {
        pad[i] = if i < KEY_LEN { key[i] ^ 0x36 } else { 0x36 };
        i += 1;
    }
    let mut inner = [0u8; KEY_LEN];
    c.hash(&pad, msg, &mut inner);
    // The same, XORed with the outer pad instead.
    let mut i = 0;
    while i < BLOCK_LEN {
        pad[i] ^= 0x36 ^ 0x5c;
        i += 1;
    }
    let mut out = [0u8; KEY_LEN];
    c.hash(&pad, &inner, &mut out);
    out
}

/// `t ‖ b`.
fn append_byte(t: &[u8; KEY_LEN], b: u8) -> [u8; KEY_LEN + 1] {
    let mut out = [b; KEY_LEN + 1];
    let mut i = 0;
    while i < KEY_LEN {
        out[i] = t[i];
        i += 1;
    }
    out
}

/// `KDF1(key, input)`: the first output of HKDF over HMAC-BLAKE2s.
pub fn kdf1<C: Crypto>(c: &C, key: &[u8; KEY_LEN], input: &[u8]) -> [u8; KEY_LEN] {
    let t0 = hmac(c, key, input);
    hmac(c, &t0, &[1])
}

/// `KDF2(key, input)`: the first two outputs.
pub fn kdf2<C: Crypto>(c: &C, key: &[u8; KEY_LEN], input: &[u8]) -> ([u8; KEY_LEN], [u8; KEY_LEN]) {
    let t0 = hmac(c, key, input);
    let t1 = hmac(c, &t0, &[1]);
    let t2 = hmac(c, &t0, &append_byte(&t1, 2));
    (t1, t2)
}

/// `KDF3(key, input)`: the first three outputs.
pub fn kdf3<C: Crypto>(
    c: &C,
    key: &[u8; KEY_LEN],
    input: &[u8],
) -> ([u8; KEY_LEN], [u8; KEY_LEN], [u8; KEY_LEN]) {
    let t0 = hmac(c, key, input);
    let t1 = hmac(c, &t0, &[1]);
    let t2 = hmac(c, &t0, &append_byte(&t1, 2));
    let t3 = hmac(c, &t0, &append_byte(&t2, 3));
    (t1, t2, t3)
}
