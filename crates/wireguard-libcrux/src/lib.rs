//! The [`Crypto`] primitives of `wireguard`, from
//! [libcrux](https://github.com/cryspen/libcrux): formally verified,
//! constant-time code generated from HACL*.
//!
//! This crate is not extracted to Lean. The `wireguard` proofs assume its
//! methods compute the functions [`Crypto`] documents (`CryptoLaws` in
//! `proofs/Wireguard/Crypto.lean`); this crate is where that assumption has to
//! hold. It only adapts libcrux's API: the nonce layout, buffer handling and
//! error mapping, all tested below against the RFC test vectors.

#![no_std]

use libcrux_blake2::Blake2sBuilder;
use libcrux_chacha20poly1305::{self as chacha, xchacha20_poly1305 as xchacha};
use wireguard::crypto::{Crypto, KEY_LEN, MAC_LEN, XNONCE_LEN};

/// The libcrux implementation of [`Crypto`].
#[derive(Debug, Clone, Copy, Default)]
pub struct Libcrux;

/// The ChaCha20-Poly1305 nonce of WireGuard: 4 zero bytes, then the counter,
/// little-endian.
fn nonce(counter: u64) -> [u8; chacha::NONCE_LEN] {
    let mut n = [0u8; chacha::NONCE_LEN];
    n[4..].copy_from_slice(&counter.to_le_bytes());
    n
}

impl Crypto for Libcrux {
    fn x25519(
        &self,
        private: &[u8; KEY_LEN],
        public: &[u8; KEY_LEN],
        out: &mut [u8; KEY_LEN],
    ) -> bool {
        // libcrux fails exactly when the result is all zeros; make sure `out`
        // then holds those zeros, as `Crypto::x25519` documents.
        let ok = libcrux_curve25519::ecdh(out, public, private).is_ok();
        if !ok {
            *out = [0; KEY_LEN];
        }
        ok
    }

    fn x25519_public(&self, private: &[u8; KEY_LEN], out: &mut [u8; KEY_LEN]) {
        libcrux_curve25519::secret_to_public(out, private)
    }

    fn hash(&self, a: &[u8], b: &[u8], out: &mut [u8; KEY_LEN]) {
        let mut h = Blake2sBuilder::new_unkeyed().build_const_digest_len::<KEY_LEN>();
        // Updates only fail past 2^64 bytes of input.
        h.update(a).expect("BLAKE2s input too long");
        h.update(b).expect("BLAKE2s input too long");
        h.finalize(out);
    }

    fn mac(&self, key: &[u8], input: &[u8], out: &mut [u8; MAC_LEN]) {
        // Keys of 1 to 32 bytes are valid, as `Crypto::mac` requires.
        let mut h = Blake2sBuilder::new_keyed_dynamic(key)
            .expect("MAC key must be 1 to 32 bytes")
            .build_const_digest_len::<MAC_LEN>();
        h.update(input).expect("BLAKE2s input too long");
        h.finalize(out);
    }

    fn aead_seal(
        &self,
        key: &[u8; KEY_LEN],
        counter: u64,
        ad: &[u8],
        plaintext: &[u8],
        out: &mut [u8],
    ) {
        chacha::encrypt(key, plaintext, out, ad, &nonce(counter))
            .expect("aead_seal: `out` must be 16 bytes longer than the plaintext");
    }

    fn aead_open(
        &self,
        key: &[u8; KEY_LEN],
        counter: u64,
        ad: &[u8],
        ciphertext: &[u8],
        out: &mut [u8],
    ) -> bool {
        chacha::decrypt(key, out, ciphertext, ad, &nonce(counter)).is_ok()
    }

    fn xaead_seal(
        &self,
        key: &[u8; KEY_LEN],
        nonce: &[u8; XNONCE_LEN],
        ad: &[u8],
        plaintext: &[u8],
        out: &mut [u8],
    ) {
        xchacha::encrypt(key, plaintext, out, ad, nonce)
            .expect("xaead_seal: `out` must be 16 bytes longer than the plaintext");
    }

    fn xaead_open(
        &self,
        key: &[u8; KEY_LEN],
        nonce: &[u8; XNONCE_LEN],
        ad: &[u8],
        ciphertext: &[u8],
        out: &mut [u8],
    ) -> bool {
        xchacha::decrypt(key, out, ciphertext, ad, nonce).is_ok()
    }

    fn ct_eq(&self, a: &[u8; MAC_LEN], b: &[u8; MAC_LEN]) -> bool {
        // Accumulate the differences without branching on them.
        let mut diff = 0u8;
        let mut i = 0;
        while i < MAC_LEN {
            diff |= a[i] ^ b[i];
            i += 1;
        }
        core::hint::black_box(diff) == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex<const N: usize>(s: &str) -> [u8; N] {
        let mut out = [0u8; N];
        for (i, o) in out.iter_mut().enumerate() {
            *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }

    #[test]
    fn x25519_rfc7748() {
        let c = Libcrux;
        // Section 5.2, first vector.
        let k = hex::<32>("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
        let u = hex::<32>("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
        let mut out = [0u8; 32];
        assert!(c.x25519(&k, &u, &mut out));
        assert_eq!(
            out,
            hex::<32>("c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")
        );
        // Section 6.1: both sides agree.
        let a = hex::<32>("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a");
        let b = hex::<32>("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb");
        let (mut pa, mut pb) = ([0u8; 32], [0u8; 32]);
        c.x25519_public(&a, &mut pa);
        c.x25519_public(&b, &mut pb);
        assert_eq!(
            pa,
            hex::<32>("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
        );
        assert_eq!(
            pb,
            hex::<32>("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")
        );
        let (mut sa, mut sb) = ([0u8; 32], [0u8; 32]);
        assert!(c.x25519(&a, &pb, &mut sa));
        assert!(c.x25519(&b, &pa, &mut sb));
        let shared = hex::<32>("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742");
        assert_eq!((sa, sb), (shared, shared));
    }

    #[test]
    fn x25519_rejects_small_order_points() {
        let c = Libcrux;
        let mut out = [1u8; 32];
        // The point 0 has order 1: the result is all zeros.
        assert!(!c.x25519(&[7; 32], &[0; 32], &mut out));
        assert_eq!(out, [0; 32]);
    }

    #[test]
    fn blake2s_rfc7693() {
        let c = Libcrux;
        let mut out = [0u8; 32];
        // Appendix B, split across the two inputs.
        c.hash(b"ab", b"c", &mut out);
        assert_eq!(
            out,
            hex::<32>("508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982")
        );
        let mut whole = [0u8; 32];
        c.hash(b"", b"abc", &mut whole);
        assert_eq!(whole, out);
    }

    #[test]
    fn mac_is_keyed() {
        let c = Libcrux;
        let (mut m1, mut m2, mut m3) = ([0u8; 16], [0u8; 16], [0u8; 16]);
        c.mac(&[1; 32], b"message", &mut m1);
        c.mac(&[2; 32], b"message", &mut m2);
        c.mac(&[1; 32], b"message", &mut m3);
        assert_ne!(m1, m2);
        assert_eq!(m1, m3);
        assert!(c.ct_eq(&m1, &m3));
        assert!(!c.ct_eq(&m1, &m2));
    }

    #[test]
    fn aead_uses_wireguard_nonces() {
        let c = Libcrux;
        let key = [0x42; 32];
        let pt = b"a packet";
        let mut ct = [0u8; 8 + 16];
        c.aead_seal(&key, 0x0102_0304_0506_0708, b"ad", pt, &mut ct);
        // The same as libcrux with the nonce 00000000 0807060504030201.
        let mut direct = [0u8; 8 + 16];
        let n = hex::<12>("000000000807060504030201");
        chacha::encrypt(&key, pt, &mut direct, b"ad", &n).unwrap();
        assert_eq!(ct, direct);
        // Round trip, and every tampering is detected.
        let mut back = [0u8; 8];
        assert!(c.aead_open(&key, 0x0102_0304_0506_0708, b"ad", &ct, &mut back));
        assert_eq!(&back, pt);
        assert!(!c.aead_open(&key, 1, b"ad", &ct, &mut back));
        assert!(!c.aead_open(&key, 0x0102_0304_0506_0708, b"AD", &ct, &mut back));
        for i in 0..ct.len() {
            let mut bad = ct;
            bad[i] ^= 1;
            assert!(!c.aead_open(&key, 0x0102_0304_0506_0708, b"ad", &bad, &mut back));
        }
    }

    #[test]
    fn xaead_round_trip() {
        let c = Libcrux;
        let (key, nonce) = ([3; 32], [9; 24]);
        let mut ct = [0u8; 32 + 16];
        c.xaead_seal(&key, &nonce, b"mac1", &[5; 32], &mut ct);
        let mut back = [0u8; 32];
        assert!(c.xaead_open(&key, &nonce, b"mac1", &ct, &mut back));
        assert_eq!(back, [5; 32]);
        let mut other = nonce;
        other[23] ^= 1;
        assert!(!c.xaead_open(&key, &other, b"mac1", &ct, &mut back));
    }
}
