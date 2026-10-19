//! The Internet checksum (RFC 1071), used by IPv4, ICMP, UDP and ICMPv6.
//!
//! The data is read as big-endian 16-bit words, an odd final byte padded with
//! a zero byte, and the words are added with end-around carry (one's-complement
//! addition). A header or datagram is intact when the sum over all of it,
//! checksum field included, is `0xFFFF`.
//!
//! Written with plain arithmetic rather than shifts and casts, so the proof
//! (`proofs/Net/Checksum.lean`) is a direct match with the textbook
//! definition, which is also checked there against a known IPv4 header.

/// The sum of a byte string whose checksum is correct.
pub const VALID: u16 = 0xFFFF;

/// Adds the 16-bit words of `data` to `acc`, with end-around carry.
pub fn sum(acc: u16, data: &[u8]) -> u16 {
    let mut acc = acc;
    let mut i = 0;
    while i < data.len() {
        // `hi * 256 + lo` is at most `0xFFFF`, so it never overflows.
        let word = if data.len() - i >= 2 {
            let w = data[i] as u16 * 256 + data[i + 1] as u16;
            i += 2;
            w
        } else {
            let w = data[i] as u16 * 256;
            i += 1;
            w
        };
        acc = add(acc, word);
    }
    acc
}

/// One's-complement addition: `a + b`, with a carry out of bit 15 added back in.
fn add(a: u16, b: u16) -> u16 {
    // `a + b > 0xFFFF`, written so that nothing overflows.
    if a > 0xFFFF - b {
        a - (0xFFFF - b)
    } else {
        a + b
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The worked IPv4 header example (checksum `0xB861`).
    const HEADER: [u8; 20] = [
        0x45, 0x00, 0x00, 0x73, 0x00, 0x00, 0x40, 0x00, 0x40, 0x11, 0xb8, 0x61, 0xc0, 0xa8, 0x00,
        0x01, 0xc0, 0xa8, 0x00, 0xc7,
    ];

    /// A straightforward reference: sum into a `u32`, then fold the carries.
    fn reference(data: &[u8]) -> u16 {
        let mut s: u32 = 0;
        for c in data.chunks(2) {
            s += (c[0] as u32) << 8 | c.get(1).copied().unwrap_or(0) as u32;
        }
        while s > 0xFFFF {
            s = (s & 0xFFFF) + (s >> 16);
        }
        s as u16
    }

    #[test]
    fn known_header() {
        assert_eq!(sum(0, &HEADER), VALID);
        let mut h = HEADER;
        h[10] = 0;
        h[11] = 0;
        assert_eq!(!sum(0, &h), 0xb861);
    }

    #[test]
    fn matches_reference() {
        let data: [u8; 61] = core::array::from_fn(|i| (i as u8).wrapping_mul(97).wrapping_add(13));
        for n in 0..=data.len() {
            assert_eq!(sum(0, &data[..n]), reference(&data[..n]), "n = {n}");
        }
        assert_eq!(sum(0, &[]), 0);
        assert_eq!(sum(0, &[0xff, 0xff, 0x00, 0x01]), 1);
        assert_eq!(sum(0xFFFF, &[0xff, 0xff]), 0xFFFF);
    }

    #[test]
    fn splits_at_even_offsets() {
        let data: [u8; 33] = core::array::from_fn(|i| (i as u8).wrapping_mul(31));
        for k in (0..=data.len()).step_by(2) {
            assert_eq!(sum(sum(0, &data[..k]), &data[k..]), sum(0, &data));
        }
    }
}
