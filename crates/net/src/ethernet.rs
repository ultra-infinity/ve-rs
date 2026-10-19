//! Ethernet II frames (IEEE 802.3), optionally 802.1Q-tagged, with or without
//! the frame check sequence.
//!
//! ```text
//! untagged: | dst (6) | src (6) | EtherType (2)                         | payload (46..=1500) |
//! tagged:   | dst (6) | src (6) | 0x8100 (2) | TCI (2) | EtherType (2) | payload (42..=1500) |
//! ```
//!
//! [`Frame`] accepts exactly the byte strings of this shape. All fields are
//! big-endian. The EtherType must be at least `0x0600`: smaller values are 802.3
//! length fields. A tag's VLAN ID must not be the reserved `0xFFF`, and stacked
//! tags (an inner EtherType of `0x8100`) are rejected. [`FrameWithFcs`]
//! additionally requires the frame to end with its CRC-32, least significant
//! byte first.
//!
//! The payload is handed back still [`Untrusted`], to be validated by the next
//! layer.

use crate::crc32::crc32;
use untrusted::{BigEndian, Decode, LittleEndian, Reader, Untrusted, Validate, ValidationError};

/// Length of an untagged header: two MAC addresses and the EtherType.
pub const HEADER_LEN: usize = 14;
/// Length of an 802.1Q tag: the TPID and the TCI.
pub const VLAN_TAG_LEN: usize = 4;
/// Smallest payload of an untagged frame: frames are at least 64 bytes,
/// including the 4-byte FCS.
pub const MIN_PAYLOAD: usize = 46;
/// Smallest payload of a tagged frame: the tag counts towards the 64 bytes.
pub const MIN_PAYLOAD_TAGGED: usize = 42;
/// Largest payload: the standard MTU.
pub const MAX_PAYLOAD: usize = 1500;
/// Smallest EtherType; smaller values denote an 802.3 length.
pub const MIN_ETHER_TYPE: u16 = 0x0600;
/// The tag protocol identifier of an 802.1Q tag.
pub const TPID_8021Q: u16 = 0x8100;
/// The VLAN ID reserved by 802.1Q, which must not appear in a frame.
pub const VID_RESERVED: u16 = 0x0FFF;
/// Length of the frame check sequence.
pub const FCS_LEN: usize = 4;

/// A 48-bit MAC address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacAddr(pub [u8; 6]);

impl Decode for MacAddr {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        let b0 = r.read_byte()?;
        let b1 = r.read_byte()?;
        let b2 = r.read_byte()?;
        let b3 = r.read_byte()?;
        let b4 = r.read_byte()?;
        let b5 = r.read_byte()?;
        Ok(MacAddr([b0, b1, b2, b3, b4, b5]))
    }
}

/// An Ethernet II EtherType: always at least [`MIN_ETHER_TYPE`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EtherType(pub u16);

impl Decode for EtherType {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        let t = r.read::<BigEndian<u16>>()?.0;
        if t >= MIN_ETHER_TYPE {
            Ok(EtherType(t))
        } else {
            Err(ValidationError::OutOfRange)
        }
    }
}

/// The tag control information of an 802.1Q tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VlanTag {
    /// Priority code point (3 bits).
    pub pcp: u8,
    /// Drop eligible indicator.
    pub dei: bool,
    /// VLAN identifier (12 bits), never [`VID_RESERVED`].
    pub vid: u16,
}

impl Decode for VlanTag {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        let tci = r.read::<BigEndian<u16>>()?.0;
        let vid = tci & 0x0FFF;
        if vid == VID_RESERVED {
            return Err(ValidationError::OutOfRange);
        }
        Ok(VlanTag {
            pcp: (tci >> 13) as u8,
            dei: (tci >> 12) & 1 == 1,
            vid,
        })
    }
}

/// What follows the MAC addresses: an optional 802.1Q tag, then the EtherType.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tagging {
    pub vlan: Option<VlanTag>,
    pub ether_type: EtherType,
}

impl Decode for Tagging {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        let t = r.read::<BigEndian<u16>>()?.0;
        if t == TPID_8021Q {
            let vlan = r.decode::<VlanTag>()?;
            let ether_type = r.decode::<EtherType>()?;
            // Stacked tags (QinQ) are not supported.
            if ether_type.0 == TPID_8021Q {
                return Err(ValidationError::OutOfRange);
            }
            Ok(Tagging {
                vlan: Some(vlan),
                ether_type,
            })
        } else if t >= MIN_ETHER_TYPE {
            Ok(Tagging {
                vlan: None,
                ether_type: EtherType(t),
            })
        } else {
            Err(ValidationError::OutOfRange)
        }
    }
}

/// The Ethernet header: 14 bytes, or 18 with an 802.1Q tag.
#[derive(Decode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct EthernetHeader {
    pub dst: MacAddr,
    pub src: MacAddr,
    pub tagging: Tagging,
}

/// An Ethernet II frame without FCS: a header and a payload of
/// [`MIN_PAYLOAD`] (or [`MIN_PAYLOAD_TAGGED`]) to [`MAX_PAYLOAD`] bytes,
/// borrowed from the input.
pub struct Frame<'a> {
    pub header: EthernetHeader,
    pub payload: Untrusted<&'a [u8]>,
}

impl<'a> Validate<&'a [u8]> for Frame<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        if input.len() < HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        // The header decoder below makes the same decision from the same
        // bytes; it is only needed here to know where the header ends.
        let tagged = input[12] == 0x81 && input[13] == 0x00;
        let (header_len, min_payload) = if tagged {
            (HEADER_LEN + VLAN_TAG_LEN, MIN_PAYLOAD_TAGGED)
        } else {
            (HEADER_LEN, MIN_PAYLOAD)
        };
        if input.len() < header_len {
            return Err(ValidationError::EndOfInput);
        }
        let payload_len = input.len() - header_len;
        // Plain comparisons rather than `RangeInclusive::contains`, which the
        // Lean model of `core` may not cover.
        #[allow(clippy::manual_range_contains)]
        if payload_len < min_payload || payload_len > MAX_PAYLOAD {
            return Err(ValidationError::OutOfRange);
        }
        let header = Untrusted::new(&input[..header_len]).read_all::<EthernetHeader>()?;
        Ok(Frame {
            header,
            payload: Untrusted::new(&input[header_len..]),
        })
    }
}

/// An Ethernet II frame whose trailing frame check sequence was verified.
pub struct FrameWithFcs<'a> {
    pub frame: Frame<'a>,
}

impl<'a> Validate<&'a [u8]> for FrameWithFcs<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        if input.len() < FCS_LEN {
            return Err(ValidationError::EndOfInput);
        }
        let body_len = input.len() - FCS_LEN;
        let body = &input[..body_len];
        let fcs = Untrusted::new(&input[body_len..])
            .validate::<LittleEndian<u32>>()?
            .0;
        if crc32(body) != fcs {
            return Err(ValidationError::ChecksumMismatch);
        }
        let frame = Untrusted::new(body).validate::<Frame>()?;
        Ok(FrameWithFcs { frame })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DST: [u8; 6] = [0xff; 6];
    const SRC: [u8; 6] = [0x02, 0x00, 0x00, 0x00, 0x00, 0x01];

    /// A frame with the given EtherType, optional TCI and payload length.
    fn frame(ether_type: u16, tci: Option<u16>, payload_len: usize) -> ([u8; 1600], usize) {
        let mut buf = [0u8; 1600];
        buf[..6].copy_from_slice(&DST);
        buf[6..12].copy_from_slice(&SRC);
        let mut n = 12;
        if let Some(tci) = tci {
            buf[n..n + 2].copy_from_slice(&TPID_8021Q.to_be_bytes());
            buf[n + 2..n + 4].copy_from_slice(&tci.to_be_bytes());
            n += 4;
        }
        buf[n..n + 2].copy_from_slice(&ether_type.to_be_bytes());
        n += 2;
        for (i, b) in buf[n..n + payload_len].iter_mut().enumerate() {
            *b = i as u8;
        }
        (buf, n + payload_len)
    }

    /// Appends the FCS.
    fn with_fcs(mut buf: [u8; 1600], n: usize) -> ([u8; 1600], usize) {
        let fcs = crc32(&buf[..n]);
        buf[n..n + 4].copy_from_slice(&fcs.to_le_bytes());
        (buf, n + 4)
    }

    fn validate(bytes: &[u8]) -> Result<Frame<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Frame>()
    }

    /// Consumes everything, recording how many bytes there were.
    #[derive(Debug, PartialEq)]
    struct Count(usize);

    impl Decode for Count {
        fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
            let n = r.remaining();
            r.skip(n)?;
            Ok(Count(n))
        }
    }

    #[test]
    fn accepts_untagged_frames() {
        for len in [MIN_PAYLOAD, 100, MAX_PAYLOAD] {
            let (buf, n) = frame(0x0800, None, len);
            let f = validate(&buf[..n]).unwrap();
            assert_eq!(f.header.dst, MacAddr(DST));
            assert_eq!(f.header.src, MacAddr(SRC));
            assert_eq!(f.header.tagging.vlan, None);
            assert_eq!(f.header.tagging.ether_type, EtherType(0x0800));
            // The payload is still untrusted: decode it to inspect it.
            assert_eq!(f.payload.read_all::<Count>(), Ok(Count(len)));
        }
    }

    #[test]
    fn accepts_tagged_frames() {
        // PCP 5, DEI 1, VID 0x123.
        let tci = (5 << 13) | (1 << 12) | 0x123;
        for len in [MIN_PAYLOAD_TAGGED, 100, MAX_PAYLOAD] {
            let (buf, n) = frame(0x86dd, Some(tci), len);
            let f = validate(&buf[..n]).unwrap();
            assert_eq!(
                f.header.tagging.vlan,
                Some(VlanTag {
                    pcp: 5,
                    dei: true,
                    vid: 0x123
                })
            );
            assert_eq!(f.header.tagging.ether_type, EtherType(0x86dd));
            assert_eq!(f.payload.read_all::<Count>(), Ok(Count(len)));
        }
    }

    #[test]
    fn rejects_bad_lengths() {
        assert_eq!(validate(&[0; 13]).err(), Some(ValidationError::EndOfInput));
        for len in [0, MIN_PAYLOAD - 1, MAX_PAYLOAD + 1] {
            let (buf, n) = frame(0x0800, None, len);
            assert_eq!(validate(&buf[..n]).err(), Some(ValidationError::OutOfRange));
        }
        for len in [MIN_PAYLOAD_TAGGED - 1, MAX_PAYLOAD + 1] {
            let (buf, n) = frame(0x0800, Some(1), len);
            assert_eq!(validate(&buf[..n]).err(), Some(ValidationError::OutOfRange));
        }
    }

    #[test]
    fn rejects_bad_types_and_tags() {
        // 802.3 length field.
        let (buf, n) = frame(MIN_ETHER_TYPE - 1, None, 100);
        assert_eq!(validate(&buf[..n]).err(), Some(ValidationError::OutOfRange));
        // Reserved VLAN ID.
        let (buf, n) = frame(0x0800, Some(VID_RESERVED), 100);
        assert_eq!(validate(&buf[..n]).err(), Some(ValidationError::OutOfRange));
        // Stacked tags.
        let (buf, n) = frame(TPID_8021Q, Some(1), 100);
        assert_eq!(validate(&buf[..n]).err(), Some(ValidationError::OutOfRange));
        // An 802.3 length after a tag.
        let (buf, n) = frame(MIN_ETHER_TYPE - 1, Some(1), 100);
        assert_eq!(validate(&buf[..n]).err(), Some(ValidationError::OutOfRange));
    }

    #[test]
    fn checks_the_fcs() {
        let (buf, n) = frame(0x0800, Some(7), 100);
        let (mut buf, n) = with_fcs(buf, n);
        let f = Untrusted::new(&buf[..n])
            .validate::<FrameWithFcs>()
            .unwrap();
        assert_eq!(f.frame.header.tagging.ether_type, EtherType(0x0800));
        assert_eq!(f.frame.payload.read_all::<Count>(), Ok(Count(100)));

        buf[20] ^= 1;
        assert_eq!(
            Untrusted::new(&buf[..n]).validate::<FrameWithFcs>().err(),
            Some(ValidationError::ChecksumMismatch)
        );
        assert_eq!(
            Untrusted::new(&buf[..3]).validate::<FrameWithFcs>().err(),
            Some(ValidationError::EndOfInput)
        );
    }
}
