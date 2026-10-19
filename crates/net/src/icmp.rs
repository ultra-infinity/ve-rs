//! ICMP messages (RFC 792).
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ipv4::tests::{packet, Count};
    use crate::ipv4::PROTO_UDP;

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
