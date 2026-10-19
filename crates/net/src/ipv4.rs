//! IPv4 packets (RFC 791).
//!
//! ```text
//! | ver/IHL (1) | ToS (1) | total length (2) | ident (2) | flags/offset (2) |
//! | TTL (1) | protocol (1) | checksum (2) | src (4) | dst (4) | options | payload | padding |
//! ```
//!
//! [`Ipv4Packet`] accepts exactly the byte strings of this shape: version 4, a
//! header length `hl = 4 * IHL` and a total length `tl` with
//! `20 <= hl <= tl <= input length`, a valid header checksum, and the reserved
//! flag bit clear. Options are not interpreted. Bytes after `tl` are link-layer
//! padding (a minimum-size Ethernet frame pads short packets); they are handed
//! back too, so they are never dropped silently. Fragments are accepted; see
//! [`Fragment`].

use crate::inet;
use untrusted::{BigEndian, Decode, Reader, Untrusted, Validate, ValidationError};

/// The EtherType of IPv4.
pub const ETHER_TYPE_IPV4: u16 = 0x0800;
/// Length of a header without options.
pub const MIN_HEADER_LEN: usize = 20;
/// The protocol number of ICMP.
pub const PROTO_ICMP: u8 = 1;
/// The protocol number of UDP.
pub const PROTO_UDP: u8 = 17;

/// An IPv4 address, as a big-endian `u32` (`192.168.0.1` is `0xC0A8_0001`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ipv4Addr(pub u32);

impl Decode for Ipv4Addr {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        Ok(Ipv4Addr(r.read::<BigEndian<u32>>()?.0))
    }
}

/// The first header byte: version 4 and the header length in 32-bit words.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VersionIhl {
    /// The header length in 32-bit words, at least 5.
    pub ihl: u8,
}

impl Decode for VersionIhl {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        let b = r.read::<BigEndian<u8>>()?.0;
        if b / 16 != 4 {
            return Err(ValidationError::OutOfRange);
        }
        let ihl = b % 16;
        if ihl < 5 {
            return Err(ValidationError::OutOfRange);
        }
        Ok(VersionIhl { ihl })
    }
}

/// The flags and fragment offset. The reserved flag bit must be clear.
///
/// A packet is a fragment of a larger one unless `more_fragments` is false and
/// `offset` is 0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fragment {
    pub dont_fragment: bool,
    pub more_fragments: bool,
    /// The fragment offset, in units of 8 bytes (13 bits).
    pub offset: u16,
}

impl Fragment {
    /// Whether this packet is only part of a larger one.
    pub fn is_fragment(&self) -> bool {
        self.more_fragments || self.offset != 0
    }
}

impl Decode for Fragment {
    fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
        let f = r.read::<BigEndian<u16>>()?.0;
        if f >= 0x8000 {
            return Err(ValidationError::OutOfRange);
        }
        Ok(Fragment {
            dont_fragment: f / 0x4000 == 1,
            more_fragments: f / 0x2000 % 2 == 1,
            offset: f % 0x2000,
        })
    }
}

/// The 20-byte fixed IPv4 header.
#[derive(Decode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ipv4Header {
    pub version_ihl: VersionIhl,
    pub tos: BigEndian<u8>,
    pub total_len: BigEndian<u16>,
    pub ident: BigEndian<u16>,
    pub fragment: Fragment,
    pub ttl: BigEndian<u8>,
    pub protocol: BigEndian<u8>,
    pub checksum: BigEndian<u16>,
    pub src: Ipv4Addr,
    pub dst: Ipv4Addr,
}

/// An IPv4 packet with a valid header checksum, borrowed from the input.
pub struct Ipv4Packet<'a> {
    pub header: Ipv4Header,
    /// The header options (`hl - 20` bytes), not interpreted.
    pub options: Untrusted<&'a [u8]>,
    /// The `tl - hl` bytes after the header.
    pub payload: Untrusted<&'a [u8]>,
    /// The bytes after the total length.
    pub padding: Untrusted<&'a [u8]>,
}

/// The header length `4 * IHL` and the total length of an IPv4 packet, read
/// directly from its first 20 bytes (which must exist). The header decoder
/// reads the same fields from the same bytes.
pub(crate) fn lengths(input: &[u8]) -> (usize, usize) {
    let header_len = input[0] as usize % 16 * 4;
    let total_len = input[2] as usize * 256 + input[3] as usize;
    (header_len, total_len)
}

impl<'a> Validate<&'a [u8]> for Ipv4Packet<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        if input.len() < MIN_HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        let (header_len, total_len) = lengths(input);
        if header_len < MIN_HEADER_LEN {
            return Err(ValidationError::OutOfRange);
        }
        if total_len < header_len {
            return Err(ValidationError::OutOfRange);
        }
        if total_len > input.len() {
            return Err(ValidationError::EndOfInput);
        }
        if inet::sum(0, &input[..header_len]) != inet::VALID {
            return Err(ValidationError::ChecksumMismatch);
        }
        let header = Untrusted::new(&input[..MIN_HEADER_LEN]).read_all::<Ipv4Header>()?;
        Ok(Ipv4Packet {
            header,
            options: Untrusted::new(&input[MIN_HEADER_LEN..header_len]),
            payload: Untrusted::new(&input[header_len..total_len]),
            padding: Untrusted::new(&input[total_len..]),
        })
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// Consumes everything, recording how many bytes there were.
    #[derive(Debug, PartialEq)]
    pub(crate) struct Count(pub usize);

    impl Decode for Count {
        fn decode(r: &mut Reader<'_>) -> Result<Self, ValidationError> {
            let n = r.remaining();
            r.skip(n)?;
            Ok(Count(n))
        }
    }

    /// Writes a valid IPv4 header (with `options_len` zero bytes of options)
    /// for `payload_len` payload bytes into `buf`, then `pad` bytes of
    /// padding. Returns the length written.
    pub(crate) fn packet(
        buf: &mut [u8],
        protocol: u8,
        options_len: usize,
        payload_len: usize,
        pad: usize,
    ) -> usize {
        let hl = MIN_HEADER_LEN + options_len;
        let tl = hl + payload_len;
        buf[..tl + pad].fill(0);
        buf[0] = 0x40 | (hl / 4) as u8;
        buf[2..4].copy_from_slice(&(tl as u16).to_be_bytes());
        buf[4..6].copy_from_slice(&0x1c46u16.to_be_bytes());
        buf[6] = 0x40; // Don't fragment.
        buf[8] = 64;
        buf[9] = protocol;
        buf[12..16].copy_from_slice(&[192, 168, 0, 1]);
        buf[16..20].copy_from_slice(&[192, 168, 0, 199]);
        for (i, b) in buf[hl..tl].iter_mut().enumerate() {
            *b = i as u8;
        }
        let c = !inet::sum(0, &buf[..hl]);
        buf[10..12].copy_from_slice(&c.to_be_bytes());
        tl + pad
    }

    fn validate(bytes: &[u8]) -> Result<Ipv4Packet<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Ipv4Packet>()
    }

    #[test]
    fn accepts_packets() {
        let mut buf = [0u8; 128];
        for (opts, len, pad) in [(0, 0, 0), (0, 26, 0), (8, 10, 6), (40, 3, 0)] {
            let n = packet(&mut buf, PROTO_UDP, opts, len, pad);
            let p = validate(&buf[..n]).unwrap();
            assert_eq!(p.header.version_ihl.ihl as usize, 5 + opts / 4);
            assert_eq!(p.header.total_len.0 as usize, 20 + opts + len);
            assert_eq!(p.header.protocol.0, PROTO_UDP);
            assert_eq!(p.header.src, Ipv4Addr(0xC0A8_0001));
            assert_eq!(p.header.dst, Ipv4Addr(0xC0A8_00C7));
            assert!(p.header.fragment.dont_fragment);
            assert!(!p.header.fragment.is_fragment());
            assert_eq!(p.options.read_all::<Count>(), Ok(Count(opts)));
            assert_eq!(p.payload.read_all::<Count>(), Ok(Count(len)));
            assert_eq!(p.padding.read_all::<Count>(), Ok(Count(pad)));
        }
    }

    #[test]
    fn decodes_fragments() {
        let mut buf = [0u8; 64];
        let n = packet(&mut buf, PROTO_UDP, 0, 8, 0);
        // More fragments, offset 0x123.
        buf[6] = 0x21;
        buf[7] = 0x23;
        buf[10] = 0;
        buf[11] = 0;
        let c = !inet::sum(0, &buf[..20]);
        buf[10..12].copy_from_slice(&c.to_be_bytes());
        let f = validate(&buf[..n]).unwrap().header.fragment;
        assert_eq!(
            f,
            Fragment {
                dont_fragment: false,
                more_fragments: true,
                offset: 0x123
            }
        );
        assert!(f.is_fragment());
    }

    #[test]
    fn rejects_malformed_packets() {
        let mut buf = [0u8; 64];
        let n = packet(&mut buf, PROTO_UDP, 0, 8, 0);
        assert_eq!(validate(&buf[..19]).err(), Some(ValidationError::EndOfInput));
        // Truncated: shorter than the total length.
        assert_eq!(validate(&buf[..n - 1]).err(), Some(ValidationError::EndOfInput));

        // Each change below breaks the checksum too, so it is fixed up: the
        // check that fails must be the one on the field.
        let check = |f: &dyn Fn(&mut [u8]), e| {
            let mut b = buf;
            f(&mut b);
            b[10] = 0;
            b[11] = 0;
            let c = !inet::sum(0, &b[..20]);
            b[10..12].copy_from_slice(&c.to_be_bytes());
            assert_eq!(validate(&b[..n]).err(), Some(e));
        };
        // IHL below 5.
        check(&|b| b[0] = 0x44, ValidationError::OutOfRange);
        // Header longer than the total length.
        check(&|b| b[0] = 0x48, ValidationError::OutOfRange);
        // Total length shorter than the header.
        check(&|b| b[3] = 19, ValidationError::OutOfRange);
        // Version 6.
        check(&|b| b[0] = 0x65, ValidationError::OutOfRange);
        // Reserved flag.
        check(&|b| b[6] |= 0x80, ValidationError::OutOfRange);

        let mut b = buf;
        b[8] ^= 1;
        assert_eq!(validate(&b[..n]).err(), Some(ValidationError::ChecksumMismatch));
    }
}
