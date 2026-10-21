//! IPv6 packets (RFC 8200).
//!
//! ```text
//! | version/class/flow (4) | payload length (2) | next header (1) | hop limit (1) |
//! | src (16) | dst (16) | payload | padding |
//! ```
//!
//! [`Ipv6Packet`] accepts exactly the byte strings of this shape: version 6
//! and at least `40 + payload length` bytes. There is no header checksum.
//! Extension headers are not interpreted: the next header is handed back as
//! is, with the payload. Bytes after the payload are link-layer padding; they
//! are handed back too, so they are never dropped silently.

use untrusted::{
    BigEndian, Decode, Encode, EncodeError, Reader, Untrusted, Validate, ValidationError, Writer,
};

/// The EtherType of IPv6.
pub const ETHER_TYPE_IPV6: u16 = 0x86DD;
/// Length of the fixed header.
pub const HEADER_LEN: usize = 40;
/// The next header of UDP.
pub const NEXT_UDP: u8 = 17;
/// The next header of ICMPv6.
pub const NEXT_ICMPV6: u8 = 58;

/// An IPv6 address, as a big-endian `u128`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ipv6Addr(pub u128);

impl Decode for Ipv6Addr {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        Ok(Ipv6Addr(r.read::<BigEndian<u128>>()?.0))
    }
}

impl Encode for Ipv6Addr {
    fn encode(&self, w: &mut Writer<'_>) -> Result<(), EncodeError> {
        BigEndian(self.0).encode(w)
    }
}

/// The first header word: version 6, the traffic class and the flow label.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VersionClassFlow {
    pub traffic_class: u8,
    /// The flow label (20 bits).
    pub flow_label: u32,
}

impl Decode for VersionClassFlow {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        let w = r.read::<BigEndian<u32>>()?.0;
        if w / 0x1000_0000 != 6 {
            return Err(ValidationError::OutOfRange);
        }
        Ok(VersionClassFlow {
            traffic_class: (w / 0x10_0000 % 256) as u8,
            flow_label: w % 0x10_0000,
        })
    }
}

/// Version 6, the traffic class and the flow label's 20 bits.
impl Encode for VersionClassFlow {
    fn encode(&self, w: &mut Writer<'_>) -> Result<(), EncodeError> {
        let word = 0x6000_0000 + self.traffic_class as u32 * 0x10_0000 + self.flow_label % 0x10_0000;
        BigEndian(word).encode(w)
    }
}

/// The 40-byte fixed IPv6 header.
#[derive(Decode, Encode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ipv6Header {
    pub version_class_flow: VersionClassFlow,
    pub payload_len: BigEndian<u16>,
    pub next_header: BigEndian<u8>,
    pub hop_limit: BigEndian<u8>,
    pub src: Ipv6Addr,
    pub dst: Ipv6Addr,
}

/// An IPv6 packet, borrowed from the input.
pub struct Ipv6Packet<'a> {
    pub header: Ipv6Header,
    /// The payload length bytes after the header.
    pub payload: Untrusted<&'a [u8]>,
    /// The bytes after the payload.
    pub padding: Untrusted<&'a [u8]>,
}

/// Where the payload of an IPv6 packet ends: 40 plus the payload length,
/// read directly from its first 40 bytes (which must exist). The header
/// decoder reads the same field from the same bytes.
pub(crate) fn payload_end(input: &[u8]) -> usize {
    HEADER_LEN + input[4] as usize * 256 + input[5] as usize
}

impl<'a> Validate<&'a [u8]> for Ipv6Packet<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        if input.len() < HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        let end = payload_end(input);
        if end > input.len() {
            return Err(ValidationError::EndOfInput);
        }
        let header = Untrusted::new(&input[..HEADER_LEN]).read_all::<Ipv6Header>()?;
        Ok(Ipv6Packet {
            header,
            payload: Untrusted::new(&input[HEADER_LEN..end]),
            padding: Untrusted::new(&input[end..]),
        })
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::ipv4::tests::Count;

    /// `fe80::1`.
    pub(crate) const SRC: u128 = 0xfe80_0000_0000_0000_0000_0000_0000_0001;
    /// `fe80::2`.
    pub(crate) const DST: u128 = 0xfe80_0000_0000_0000_0000_0000_0000_0002;

    /// Writes an IPv6 header for `payload_len` bytes of payload (numbered
    /// 0, 1, …) into `buf`, then `pad` bytes of padding. Returns the length
    /// written.
    pub(crate) fn packet(buf: &mut [u8], next: u8, payload_len: usize, pad: usize) -> usize {
        let n = HEADER_LEN + payload_len;
        buf[..n + pad].fill(0);
        // Version 6, traffic class 0xb8, flow label 0x12345.
        buf[..4].copy_from_slice(&0x6b81_2345u32.to_be_bytes());
        buf[4..6].copy_from_slice(&(payload_len as u16).to_be_bytes());
        buf[6] = next;
        buf[7] = 64;
        buf[8..24].copy_from_slice(&SRC.to_be_bytes());
        buf[24..40].copy_from_slice(&DST.to_be_bytes());
        for (i, b) in buf[HEADER_LEN..n].iter_mut().enumerate() {
            *b = i as u8;
        }
        n + pad
    }

    fn validate(bytes: &[u8]) -> Result<Ipv6Packet<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Ipv6Packet>()
    }

    #[test]
    fn accepts_packets() {
        let mut buf = [0u8; 128];
        for (len, pad) in [(0, 0), (20, 0), (6, 10)] {
            let n = packet(&mut buf, NEXT_UDP, len, pad);
            let p = validate(&buf[..n]).unwrap();
            assert_eq!(
                p.header.version_class_flow,
                VersionClassFlow {
                    traffic_class: 0xb8,
                    flow_label: 0x12345
                }
            );
            assert_eq!(p.header.payload_len.0 as usize, len);
            assert_eq!(p.header.next_header.0, NEXT_UDP);
            assert_eq!(p.header.hop_limit.0, 64);
            assert_eq!(p.header.src, Ipv6Addr(SRC));
            assert_eq!(p.header.dst, Ipv6Addr(DST));
            assert_eq!(p.payload.read_all::<Count>(), Ok(Count(len)));
            assert_eq!(p.padding.read_all::<Count>(), Ok(Count(pad)));
        }
    }

    #[test]
    fn rejects_malformed_packets() {
        let mut buf = [0u8; 128];
        let n = packet(&mut buf, NEXT_UDP, 20, 0);
        assert_eq!(validate(&buf[..39]).err(), Some(ValidationError::EndOfInput));
        assert_eq!(validate(&buf[..n - 1]).err(), Some(ValidationError::EndOfInput));
        let mut b = buf;
        b[0] = 0x4b;
        assert_eq!(validate(&b[..n]).err(), Some(ValidationError::OutOfRange));
    }
}
