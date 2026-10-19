//! Ethernet II frames (IEEE 802.3, without the frame check sequence).
//!
//! ```text
//! | dst MAC (6) | src MAC (6) | EtherType (2, big-endian) | payload (46..=1500) |
//! ```
//!
//! [`Frame`] accepts exactly the byte strings of this shape whose EtherType
//! is at least `0x0600`: smaller values are 802.3 length fields, not Ethernet
//! II types. The payload is handed back still [`Untrusted`], to be validated by
//! the next layer.

use untrusted::{BigEndian, Decode, Reader, Untrusted, Validate, ValidationError};

/// Length of the Ethernet header: two MAC addresses and the EtherType.
pub const HEADER_LEN: usize = 14;
/// Smallest payload: frames are padded to 64 bytes, including the 4-byte FCS.
pub const MIN_PAYLOAD: usize = 46;
/// Largest payload: the standard MTU.
pub const MAX_PAYLOAD: usize = 1500;
/// Smallest EtherType; smaller values denote an 802.3 length.
pub const MIN_ETHER_TYPE: u16 = 0x0600;

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

/// The 14-byte Ethernet header.
#[derive(Decode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct EthernetHeader {
    pub dst: MacAddr,
    pub src: MacAddr,
    pub ether_type: EtherType,
}

/// An Ethernet II frame: a header and a payload of
/// [`MIN_PAYLOAD`]`..=`[`MAX_PAYLOAD`] bytes, borrowed from the input.
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
        let payload_len = input.len() - HEADER_LEN;
        // Plain comparisons rather than `RangeInclusive::contains`, which the
        // Lean model of `core` may not cover.
        #[allow(clippy::manual_range_contains)]
        if payload_len < MIN_PAYLOAD || payload_len > MAX_PAYLOAD {
            return Err(ValidationError::OutOfRange);
        }
        let header = Untrusted::new(&input[..HEADER_LEN]).read_all::<EthernetHeader>()?;
        Ok(Frame {
            header,
            payload: Untrusted::new(&input[HEADER_LEN..]),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DST: [u8; 6] = [0xff; 6];
    const SRC: [u8; 6] = [0x02, 0x00, 0x00, 0x00, 0x00, 0x01];

    /// A frame with the given EtherType and payload length.
    fn frame(ether_type: u16, payload_len: usize) -> ([u8; 1600], usize) {
        let mut buf = [0u8; 1600];
        buf[..6].copy_from_slice(&DST);
        buf[6..12].copy_from_slice(&SRC);
        buf[12..14].copy_from_slice(&ether_type.to_be_bytes());
        for (i, b) in buf[14..14 + payload_len].iter_mut().enumerate() {
            *b = i as u8;
        }
        (buf, 14 + payload_len)
    }

    fn validate(bytes: &[u8]) -> Result<Frame<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Frame>()
    }

    #[test]
    fn accepts_well_formed_frames() {
        for len in [MIN_PAYLOAD, 100, MAX_PAYLOAD] {
            let (buf, n) = frame(0x0800, len);
            let f = validate(&buf[..n]).unwrap();
            assert_eq!(f.header.dst, MacAddr(DST));
            assert_eq!(f.header.src, MacAddr(SRC));
            assert_eq!(f.header.ether_type, EtherType(0x0800));
            // The payload is still untrusted: decode it to inspect it.
            assert_eq!(f.payload.read_all::<Count>(), Ok(Count(len)));
        }
    }

    #[test]
    fn rejects_bad_lengths() {
        assert_eq!(validate(&[0; 13]).err(), Some(ValidationError::EndOfInput));
        for len in [0, MIN_PAYLOAD - 1, MAX_PAYLOAD + 1] {
            let (buf, n) = frame(0x0800, len);
            assert_eq!(validate(&buf[..n]).err(), Some(ValidationError::OutOfRange));
        }
    }

    #[test]
    fn rejects_802_3_length_fields() {
        let (buf, n) = frame(MIN_ETHER_TYPE - 1, 100);
        assert_eq!(validate(&buf[..n]).err(), Some(ValidationError::OutOfRange));
        let (buf, n) = frame(MIN_ETHER_TYPE, 100);
        assert!(validate(&buf[..n]).is_ok());
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
}
