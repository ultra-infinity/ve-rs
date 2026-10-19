//! UDP datagrams (RFC 768).
//!
//! ```text
//! | src port (2) | dst port (2) | length (2) | checksum (2) | payload |
//! ```
//!
//! The checksum covers a pseudo-header made of fields of the IP header, so a
//! datagram is validated together with the packet that carries it:
//! [`Ipv4Udp`] takes a whole IPv4 packet.

use crate::inet;
use crate::ipv4::{self, Ipv4Packet, PROTO_UDP};
use untrusted::{BigEndian, Decode, Untrusted, Validate, ValidationError};

/// Length of the UDP header.
pub const HEADER_LEN: usize = 8;

/// The UDP header.
#[derive(Decode, Debug, Clone, Copy, PartialEq, Eq)]
pub struct UdpHeader {
    pub src_port: BigEndian<u16>,
    pub dst_port: BigEndian<u16>,
    /// The length of the datagram, header included.
    pub length: BigEndian<u16>,
    /// The checksum; 0 means none was computed (allowed over IPv4 only).
    pub checksum: BigEndian<u16>,
}

/// A UDP datagram carried by an IPv4 packet.
///
/// Accepts exactly the IPv4 packets ([`Ipv4Packet`]) with protocol 17 that are
/// not fragments, whose payload is a UDP header followed by data, where:
/// - the UDP length equals the IPv4 payload length;
/// - the checksum is 0, or the Internet checksum over the pseudo-header
///   (source and destination address, a zero byte, the protocol, the UDP
///   length) followed by the datagram is valid.
pub struct Ipv4Udp<'a> {
    pub ip: Ipv4Packet<'a>,
    pub header: UdpHeader,
    pub payload: Untrusted<&'a [u8]>,
}

impl<'a> Validate<&'a [u8]> for Ipv4Udp<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        let ip = Untrusted::new(input).validate::<Ipv4Packet>()?;
        if ip.header.protocol.0 != PROTO_UDP {
            return Err(ValidationError::OutOfRange);
        }
        if ip.header.fragment.more_fragments {
            return Err(ValidationError::OutOfRange);
        }
        if ip.header.fragment.offset != 0 {
            return Err(ValidationError::OutOfRange);
        }
        // `ip.payload`, located again: `Ipv4Packet` accepted the input, so it
        // has a full header and these lengths are within it. (Not named `udp`:
        // that would shadow the `udp` namespace in the generated Lean.)
        let (header_len, total_len) = ipv4::lengths(input);
        let datagram = &input[header_len..total_len];
        if datagram.len() < HEADER_LEN {
            return Err(ValidationError::EndOfInput);
        }
        let header = Untrusted::new(&datagram[..HEADER_LEN]).read_all::<UdpHeader>()?;
        if header.length.0 as usize != datagram.len() {
            return Err(ValidationError::LengthMismatch {
                expected: datagram.len(),
                actual: header.length.0 as usize,
            });
        }
        if header.checksum.0 != 0 {
            // The pseudo-header: the addresses, a zero byte and the protocol,
            // then the UDP length, which bytes 4 and 5 of `datagram` hold (as
            // just checked).
            let acc = inet::sum(0, &input[12..20]);
            let acc = inet::sum(acc, &[0, PROTO_UDP]);
            let acc = inet::sum(acc, &datagram[4..6]);
            if inet::sum(acc, datagram) != inet::VALID {
                return Err(ValidationError::ChecksumMismatch);
            }
        }
        Ok(Ipv4Udp {
            ip,
            header,
            payload: Untrusted::new(&datagram[HEADER_LEN..]),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ipv4::tests::{packet, Count};
    use crate::ipv4::PROTO_ICMP;

    /// An IPv4 packet carrying a UDP datagram with `data_len` bytes of data,
    /// with a correct checksum if `checksum`, else none. Returns its length.
    pub(crate) fn datagram(buf: &mut [u8], data_len: usize, checksum: bool, pad: usize) -> usize {
        let n = packet(buf, PROTO_UDP, 0, HEADER_LEN + data_len, pad);
        let udp_len = (HEADER_LEN + data_len) as u16;
        buf[20..22].copy_from_slice(&5353u16.to_be_bytes());
        buf[22..24].copy_from_slice(&53u16.to_be_bytes());
        buf[24..26].copy_from_slice(&udp_len.to_be_bytes());
        buf[26..28].fill(0);
        if checksum {
            let acc = inet::sum(0, &buf[12..20]);
            let acc = inet::sum(acc, &[0, PROTO_UDP]);
            let acc = inet::sum(acc, &udp_len.to_be_bytes());
            let mut c = !inet::sum(acc, &buf[20..20 + udp_len as usize]);
            // A computed 0 is sent as 0xFFFF; 0 means "no checksum".
            if c == 0 {
                c = 0xFFFF;
            }
            buf[26..28].copy_from_slice(&c.to_be_bytes());
        }
        n
    }

    fn validate(bytes: &[u8]) -> Result<Ipv4Udp<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Ipv4Udp>()
    }

    #[test]
    fn accepts_datagrams() {
        let mut buf = [0u8; 128];
        for (len, checksum, pad) in [(0, true, 0), (17, true, 0), (17, false, 0), (4, true, 14)] {
            let n = datagram(&mut buf, len, checksum, pad);
            let u = validate(&buf[..n]).unwrap();
            assert_eq!(u.header.src_port, BigEndian(5353));
            assert_eq!(u.header.dst_port, BigEndian(53));
            assert_eq!(u.header.length.0 as usize, HEADER_LEN + len);
            assert_eq!(u.header.checksum.0 == 0, !checksum);
            assert_eq!(u.payload.read_all::<Count>(), Ok(Count(len)));
            assert_eq!(u.ip.padding.read_all::<Count>(), Ok(Count(pad)));
        }
    }

    #[test]
    fn rejects_malformed_datagrams() {
        let mut buf = [0u8; 128];
        let n = datagram(&mut buf, 10, true, 0);

        // Corrupted data.
        let mut b = buf;
        b[n - 1] ^= 1;
        assert_eq!(validate(&b[..n]).err(), Some(ValidationError::ChecksumMismatch));
        // Corrupted address: part of the pseudo-header, not of the IP checksum
        // once that is fixed up.
        let mut b = buf;
        b[19] ^= 1;
        b[10..12].fill(0);
        let c = !inet::sum(0, &b[..20]);
        b[10..12].copy_from_slice(&c.to_be_bytes());
        assert_eq!(validate(&b[..n]).err(), Some(ValidationError::ChecksumMismatch));
        // Length field disagreeing with the IP payload (checksum disabled).
        let n2 = datagram(&mut buf, 10, false, 0);
        let mut b = buf;
        b[25] = 17;
        assert_eq!(
            validate(&b[..n2]).err(),
            Some(ValidationError::LengthMismatch {
                expected: 18,
                actual: 17
            })
        );
        // Shorter than a UDP header.
        let n3 = packet(&mut buf, PROTO_UDP, 0, 7, 0);
        assert_eq!(validate(&buf[..n3]).err(), Some(ValidationError::EndOfInput));
        // Another protocol.
        let n4 = packet(&mut buf, PROTO_ICMP, 0, 16, 0);
        assert_eq!(validate(&buf[..n4]).err(), Some(ValidationError::OutOfRange));
    }

    #[test]
    fn rejects_fragments() {
        let mut buf = [0u8; 128];
        let n = datagram(&mut buf, 10, false, 0);
        for (b6, b7) in [(0x20, 0), (0, 1)] {
            let mut b = buf;
            b[6] = b6;
            b[7] = b7;
            b[10..12].fill(0);
            let c = !inet::sum(0, &b[..20]);
            b[10..12].copy_from_slice(&c.to_be_bytes());
            assert_eq!(validate(&b[..n]).err(), Some(ValidationError::OutOfRange));
        }
    }
}
