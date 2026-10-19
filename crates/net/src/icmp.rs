//! ICMP messages over IPv4 (RFC 792) and IPv6 (RFC 4443).
//!
//! ```text
//! | type (1) | code (1) | checksum (2) | rest of header (4) | body |
//! ```
//!
//! Message types are not interpreted: the type and code are handed back as
//! decoded, and the rest of the header (for an echo request or reply, the
//! identifier and sequence number) as a big-endian `u32`.

use crate::inet;
use crate::ipv4::{self, Ipv4Packet, PROTO_ICMP};
use crate::ipv6::{self, Ipv6Packet, NEXT_ICMPV6};
use untrusted::{BigEndian, Decode, Untrusted, Validate, ValidationError};

/// Length of the ICMP header.
pub const HEADER_LEN: usize = 8;

/// The ICMP header.
#[derive(Decode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct IcmpHeader {
    /// The message type, e.g. 8 for an echo request, 0 for an echo reply.
    pub kind: BigEndian<u8>,
    pub code: BigEndian<u8>,
    pub checksum: BigEndian<u16>,
    /// The rest of the header, whose meaning depends on the type.
    pub rest: BigEndian<u32>,
}

/// An ICMP message carried by an IPv4 packet.
///
/// Accepts exactly the IPv4 packets ([`Ipv4Packet`]) with protocol 1 that are
/// not fragments, whose payload is at least 8 bytes long and has a valid
/// Internet checksum.
pub struct Icmpv4<'a> {
    pub ip: Ipv4Packet<'a>,
    pub header: IcmpHeader,
    pub body: Untrusted<&'a [u8]>,
}

impl<'a> Validate<&'a [u8]> for Icmpv4<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        let ip = Untrusted::new(input).validate::<Ipv4Packet>()?;
        if ip.header.protocol.0 != PROTO_ICMP {
            return Err(ValidationError::OutOfRange);
        }
        if ip.header.fragment.more_fragments {
            return Err(ValidationError::OutOfRange);
        }
        if ip.header.fragment.offset != 0 {
            return Err(ValidationError::OutOfRange);
        }
        // `ip.payload`, located again: `Ipv4Packet` accepted the input, so it
        // has a full header and these lengths are within it.
        let (header_len, total_len) = ipv4::lengths(input);
        let message = &input[header_len..total_len];
        if message.len() < HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        if inet::sum(0, message) != inet::VALID {
            return Err(ValidationError::ChecksumMismatch);
        }
        let header = Untrusted::new(&message[..HEADER_LEN]).read_all::<IcmpHeader>()?;
        Ok(Icmpv4 {
            ip,
            header,
            body: Untrusted::new(&message[HEADER_LEN..]),
        })
    }
}

/// An ICMPv6 message carried by an IPv6 packet.
///
/// Accepts exactly the IPv6 packets ([`Ipv6Packet`]) whose next header is 58
/// (so with no extension headers), whose payload is at least 8 bytes long and
/// has a valid Internet checksum over the pseudo-header (source and
/// destination address, the payload length as 32 bits, three zero bytes, the
/// next header 58) followed by the message.
pub struct Icmpv6<'a> {
    pub ip: Ipv6Packet<'a>,
    pub header: IcmpHeader,
    pub body: Untrusted<&'a [u8]>,
}

impl<'a> Validate<&'a [u8]> for Icmpv6<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        let ip = Untrusted::new(input).validate::<Ipv6Packet>()?;
        if ip.header.next_header.0 != NEXT_ICMPV6 {
            return Err(ValidationError::OutOfRange);
        }
        // `ip.payload`, located again: `Ipv6Packet` accepted the input, so it
        // has a full header and the payload is within it.
        let end = ipv6::payload_end(input);
        let message = &input[ipv6::HEADER_LEN..end];
        if message.len() < HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        // The pseudo-header: the addresses, the message length as 32 bits
        // (bytes 4 and 5 of `input` hold its low half), three zero bytes and
        // the next header.
        let acc = inet::sum(0, &input[8..40]);
        let acc = inet::sum(acc, &[0, 0]);
        let acc = inet::sum(acc, &input[4..6]);
        let acc = inet::sum(acc, &[0, 0, 0, NEXT_ICMPV6]);
        if inet::sum(acc, message) != inet::VALID {
            return Err(ValidationError::ChecksumMismatch);
        }
        let header = Untrusted::new(&message[..HEADER_LEN]).read_all::<IcmpHeader>()?;
        Ok(Icmpv6 {
            ip,
            header,
            body: Untrusted::new(&message[HEADER_LEN..]),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ipv4::tests::{packet, Count};
    use crate::ipv4::PROTO_UDP;
    use crate::ipv6::NEXT_UDP;

    /// An IPv4 packet carrying an echo request with `data_len` bytes of data.
    fn echo(buf: &mut [u8], data_len: usize) -> usize {
        let n = packet(buf, PROTO_ICMP, 0, HEADER_LEN + data_len, 0);
        buf[20] = 8;
        buf[21] = 0;
        buf[22..24].fill(0);
        buf[24..28].copy_from_slice(&[0x12, 0x34, 0x00, 0x01]);
        let c = !inet::sum(0, &buf[20..20 + HEADER_LEN + data_len]);
        buf[22..24].copy_from_slice(&c.to_be_bytes());
        n
    }

    fn validate(bytes: &[u8]) -> Result<Icmpv4<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Icmpv4>()
    }

    #[test]
    fn accepts_echo_requests() {
        let mut buf = [0u8; 128];
        for len in [0, 7, 56] {
            let n = echo(&mut buf, len);
            let m = validate(&buf[..n]).unwrap();
            assert_eq!(m.header.kind, BigEndian(8));
            assert_eq!(m.header.code, BigEndian(0));
            assert_eq!(m.header.rest, BigEndian(0x1234_0001));
            assert_eq!(m.body.read_all::<Count>(), Ok(Count(len)));
        }
    }

    /// An IPv6 packet carrying an ICMPv6 echo request with `data_len` bytes of
    /// data.
    fn echo6(buf: &mut [u8], data_len: usize) -> usize {
        let len = HEADER_LEN + data_len;
        let n = ipv6::tests::packet(buf, NEXT_ICMPV6, len, 0);
        buf[40] = 128;
        buf[41] = 0;
        buf[42..44].fill(0);
        buf[44..48].copy_from_slice(&[0x12, 0x34, 0x00, 0x01]);
        let acc = inet::sum(0, &buf[8..40]);
        let acc = inet::sum(acc, &(len as u32).to_be_bytes());
        let acc = inet::sum(acc, &[0, 0, 0, NEXT_ICMPV6]);
        let c = !inet::sum(acc, &buf[40..40 + len]);
        buf[42..44].copy_from_slice(&c.to_be_bytes());
        n
    }

    fn validate6(bytes: &[u8]) -> Result<Icmpv6<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Icmpv6>()
    }

    #[test]
    fn accepts_ipv6_echo_requests() {
        let mut buf = [0u8; 128];
        for len in [0, 7, 56] {
            let n = echo6(&mut buf, len);
            let m = validate6(&buf[..n]).unwrap();
            assert_eq!(m.header.kind, BigEndian(128));
            assert_eq!(m.header.rest, BigEndian(0x1234_0001));
            assert_eq!(m.body.read_all::<Count>(), Ok(Count(len)));
        }
    }

    #[test]
    fn rejects_malformed_ipv6_messages() {
        let mut buf = [0u8; 128];
        let n = echo6(&mut buf, 10);
        // Corrupted data, or destination address.
        for i in [n - 1, 39] {
            let mut b = buf;
            b[i] ^= 1;
            assert_eq!(validate6(&b[..n]).err(), Some(ValidationError::ChecksumMismatch));
        }
        let mut b = buf;
        b[6] = NEXT_UDP;
        assert_eq!(validate6(&b[..n]).err(), Some(ValidationError::OutOfRange));
        let n2 = ipv6::tests::packet(&mut buf, NEXT_ICMPV6, 7, 0);
        assert_eq!(validate6(&buf[..n2]).err(), Some(ValidationError::EndOfInput));
    }

    #[test]
    fn rejects_malformed_messages() {
        let mut buf = [0u8; 128];
        let n = echo(&mut buf, 10);
        let mut b = buf;
        b[n - 1] ^= 1;
        assert_eq!(validate(&b[..n]).err(), Some(ValidationError::ChecksumMismatch));
        let n2 = packet(&mut buf, PROTO_ICMP, 0, 7, 0);
        assert_eq!(validate(&buf[..n2]).err(), Some(ValidationError::EndOfInput));
        let n3 = packet(&mut buf, PROTO_UDP, 0, 16, 0);
        assert_eq!(validate(&buf[..n3]).err(), Some(ValidationError::OutOfRange));
    }
}
