//! CRC-32 as used by the Ethernet frame check sequence (IEEE 802.3).
//!
//! Reflected polynomial `0xEDB88320`, initial value and final XOR
//! `0xFFFFFFFF`. Computed bit by bit, without a lookup table, so the proof
//! is a direct match with the textbook definition; it is proved equal to it in
//! `proofs/Net/Manual.lean`, where that definition is also checked against the
//! standard check value.

/// The reflected IEEE 802.3 polynomial.
pub const POLY: u32 = 0xEDB8_8320;

/// The CRC-32 of `data`.
pub fn crc32(data: &[u8]) -> u32 {
    let mut crc: u32 = 0xFFFF_FFFF;
    let mut i = 0;
    while i < data.len() {
        crc = update(crc, data[i]);
        i += 1;
    }
    !crc
}

/// Feeds one byte into the CRC register, least significant bit first.
fn update(crc: u32, byte: u8) -> u32 {
    let mut c = crc ^ (byte as u32);
    let mut k = 0;
    while k < 8 {
        c = if c & 1 == 1 { (c >> 1) ^ POLY } else { c >> 1 };
        k += 1;
    }
    c
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_value() {
        // The standard CRC-32/ISO-HDLC check value.
        assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
        assert_eq!(crc32(b""), 0);
    }
}
