//! UDP datagrams (RFC 768).
//!
//! ```text
//! | src port (2) | dst port (2) | length (2) | checksum (2) | payload |
//! ```
//!
//! The checksum covers a pseudo-header made of fields of the IP header, so a
//! datagram is validated together with the packet that carries it:
//! [`Ipv4Udp`] takes a whole IPv4 packet, [`Ipv6Udp`] a whole IPv6 packet.

use crate::inet;
use crate::ipv4::{self, Ipv4Packet, PROTO_UDP};
use crate::ipv6::{self, Ipv6Packet, NEXT_UDP};
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

/// A UDP datagram carried by an IPv6 packet.
///
/// Accepts exactly the IPv6 packets ([`Ipv6Packet`]) whose next header is 17
/// (so with no extension headers), whose payload is a UDP header followed by
/// data, where:
/// - the UDP length equals the IPv6 payload length;
/// - the checksum, which IPv6 makes mandatory, is not 0, and the Internet
///   checksum over the pseudo-header (source and destination address, the UDP
///   length as 32 bits, three zero bytes, the next header 17) followed by the
///   datagram is valid.
pub struct Ipv6Udp<'a> {
    pub ip: Ipv6Packet<'a>,
    pub header: UdpHeader,
    pub payload: Untrusted<&'a [u8]>,
}

impl<'a> Validate<&'a [u8]> for Ipv6Udp<'a> {
    type Err = ValidationError;

    fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
        let ip = Untrusted::new(input).validate::<Ipv6Packet>()?;
        if ip.header.next_header.0 != NEXT_UDP {
            return Err(ValidationError::OutOfRange);
        }
        // `ip.payload`, located again: `Ipv6Packet` accepted the input, so it
        // has a full header and the payload is within it.
        let end = ipv6::payload_end(input);
        let datagram = &input[ipv6::HEADER_LEN..end];
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
        if header.checksum.0 == 0 {
            return Err(ValidationError::ChecksumMismatch);
        }
        // The pseudo-header: the addresses, the UDP length as 32 bits (bytes 4
        // and 5 of `datagram` hold its low half, as just checked), three zero
        // bytes and the next header.
        let acc = inet::sum(0, &input[8..40]);
        let acc = inet::sum(acc, &[0, 0]);
        let acc = inet::sum(acc, &datagram[4..6]);
        let acc = inet::sum(acc, &[0, 0, 0, NEXT_UDP]);
        if inet::sum(acc, datagram) != inet::VALID {
            return Err(ValidationError::ChecksumMismatch);
        }
        Ok(Ipv6Udp {
            ip,
            header,
            payload: Untrusted::new(&datagram[HEADER_LEN..]),
        })
    }
}

/// The time to live (IPv4) or hop limit (IPv6) of the packets the encoders
/// write.
pub const TTL: u8 = 64;
/// The largest IP packet.
pub const MAX_PACKET_LEN: usize = 65535;

/// The bytes of `v`, big-endian.
pub(crate) fn be32(v: u32) -> [u8; 4] {
    [
        (v / 16_777_216) as u8,
        (v / 65536 % 256) as u8,
        (v / 256 % 256) as u8,
        (v % 256) as u8,
    ]
}

/// The bytes of `v`, big-endian.
fn be128(v: u128) -> [u8; 16] {
    let a = be32((v / 79_228_162_514_264_337_593_543_950_336) as u32);
    let b = be32((v / 18_446_744_073_709_551_616 % 4_294_967_296) as u32);
    let c = be32((v / 4_294_967_296 % 4_294_967_296) as u32);
    let d = be32((v % 4_294_967_296) as u32);
    [
        a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3], c[0], c[1], c[2], c[3], d[0], d[1], d[2],
        d[3],
    ]
}

/// The IPv4 header of a packet of `total` bytes from `src` to `dst` carrying
/// protocol `proto`, with `checksum`: no options, not fragmented,
/// don't-fragment set.
pub(crate) fn ipv4_header(src: u32, dst: u32, total: u16, proto: u8, checksum: u16) -> [u8; 20] {
    let s = be32(src);
    let d = be32(dst);
    [
        0x45,
        0,
        (total / 256) as u8,
        (total % 256) as u8,
        0,
        0,
        0x40,
        0,
        TTL,
        proto,
        (checksum / 256) as u8,
        (checksum % 256) as u8,
        s[0],
        s[1],
        s[2],
        s[3],
        d[0],
        d[1],
        d[2],
        d[3],
    ]
}

/// The IPv6 header of a packet from `src` to `dst` carrying `len` bytes
/// under next header `next`: traffic class and flow label 0, no extension
/// headers.
pub(crate) fn ipv6_header(src: u128, dst: u128, len: u16, next: u8) -> [u8; 40] {
    let s = be128(src);
    let d = be128(dst);
    [
        0x60,
        0,
        0,
        0,
        (len / 256) as u8,
        (len % 256) as u8,
        next,
        TTL,
        s[0],
        s[1],
        s[2],
        s[3],
        s[4],
        s[5],
        s[6],
        s[7],
        s[8],
        s[9],
        s[10],
        s[11],
        s[12],
        s[13],
        s[14],
        s[15],
        d[0],
        d[1],
        d[2],
        d[3],
        d[4],
        d[5],
        d[6],
        d[7],
        d[8],
        d[9],
        d[10],
        d[11],
        d[12],
        d[13],
        d[14],
        d[15],
    ]
}

/// A UDP header.
fn udp_header(src_port: u16, dst_port: u16, len: u16, checksum: u16) -> [u8; 8] {
    [
        (src_port / 256) as u8,
        (src_port % 256) as u8,
        (dst_port / 256) as u8,
        (dst_port % 256) as u8,
        (len / 256) as u8,
        (len % 256) as u8,
        (checksum / 256) as u8,
        (checksum % 256) as u8,
    ]
}

/// Copies `src` to `out[pos..pos + src.len()]`, which must exist.
pub(crate) fn put_bytes(out: &mut [u8], pos: usize, src: &[u8]) {
    let mut i = 0;
    while i < src.len() {
        out[pos + i] = src[i];
        i += 1;
    }
}

/// The checksum to write for a sum `s` taken with the checksum field zero:
/// what makes the sum `0xFFFF`. For UDP, a computed 0 is sent as `0xFFFF`
/// (its one's-complement equal), since 0 means "no checksum".
fn udp_checksum(s: u16) -> u16 {
    if s == 0xFFFF {
        0xFFFF
    } else {
        0xFFFF - s
    }
}

/// Writes to the start of `out` an IPv4 packet (no options, not fragmented,
/// don't-fragment set) carrying a UDP datagram from `src:src_port` to
/// `dst:dst_port` with `data`, both checksums computed. Returns its length,
/// or `None` if `out` is too short or the packet would be too long.
///
/// `proofs/Net/UdpEncode.lean` proves that [`Ipv4Udp`] accepts the result
/// and decodes it back to these addresses, ports and data.
pub fn encode_ipv4(
    src: ipv4::Ipv4Addr,
    dst: ipv4::Ipv4Addr,
    src_port: u16,
    dst_port: u16,
    data: &[u8],
    out: &mut [u8],
) -> Option<usize> {
    if data.len() > MAX_PACKET_LEN - 28 {
        return None;
    }
    let n = 28 + data.len();
    if out.len() < n {
        return None;
    }
    let total = n as u16;
    let len = (n - 20) as u16;
    // Each checksum is computed with its field 0, as `Ipv4Udp` checks it.
    let zero = ipv4_header(src.0, dst.0, total, PROTO_UDP, 0);
    let header = ipv4_header(src.0, dst.0, total, PROTO_UDP, 0xFFFF - inet::sum(0, &zero));
    let udp0 = udp_header(src_port, dst_port, len, 0);
    let acc = inet::sum(0, &header[12..20]);
    let acc = inet::sum(acc, &[0, PROTO_UDP]);
    let acc = inet::sum(acc, &udp0[4..6]);
    let acc = inet::sum(acc, &udp0);
    let s = inet::sum(acc, data);
    // Not named `udp`: that would shadow the `udp` namespace in Lean.
    let datagram_header = udp_header(src_port, dst_port, len, udp_checksum(s));
    put_bytes(out, 0, &header);
    put_bytes(out, 20, &datagram_header);
    put_bytes(out, 28, data);
    Some(n)
}

/// Writes to the start of `out` an IPv6 packet (no extension headers)
/// carrying a UDP datagram from `src:src_port` to `dst:dst_port` with `data`,
/// its checksum computed. Returns its length, or `None` if `out` is too short
/// or the datagram would be too long.
///
/// `proofs/Net/UdpEncode.lean` proves that [`Ipv6Udp`] accepts the result
/// and decodes it back to these addresses, ports and data.
pub fn encode_ipv6(
    src: ipv6::Ipv6Addr,
    dst: ipv6::Ipv6Addr,
    src_port: u16,
    dst_port: u16,
    data: &[u8],
    out: &mut [u8],
) -> Option<usize> {
    if data.len() > MAX_PACKET_LEN - 8 {
        return None;
    }
    let n = 48 + data.len();
    if out.len() < n {
        return None;
    }
    let len = (n - 40) as u16;
    let header = ipv6_header(src.0, dst.0, len, NEXT_UDP);
    // The checksum is computed with its field 0, as `Ipv6Udp` checks it.
    let udp0 = udp_header(src_port, dst_port, len, 0);
    let acc = inet::sum(0, &header[8..40]);
    let acc = inet::sum(acc, &[0, 0]);
    let acc = inet::sum(acc, &udp0[4..6]);
    let acc = inet::sum(acc, &[0, 0, 0, NEXT_UDP]);
    let acc = inet::sum(acc, &udp0);
    let s = inet::sum(acc, data);
    // Not named `udp`: that would shadow the `udp` namespace in Lean.
    let datagram_header = udp_header(src_port, dst_port, len, udp_checksum(s));
    put_bytes(out, 0, &header);
    put_bytes(out, 40, &datagram_header);
    put_bytes(out, 48, data);
    Some(n)
}

#[cfg(test)]
pub(crate) mod tests {
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
        assert_eq!(
            validate(&b[..n]).err(),
            Some(ValidationError::ChecksumMismatch)
        );
        // Corrupted address: part of the pseudo-header, not of the IP checksum
        // once that is fixed up.
        let mut b = buf;
        b[19] ^= 1;
        b[10..12].fill(0);
        let c = !inet::sum(0, &b[..20]);
        b[10..12].copy_from_slice(&c.to_be_bytes());
        assert_eq!(
            validate(&b[..n]).err(),
            Some(ValidationError::ChecksumMismatch)
        );
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
        assert_eq!(
            validate(&buf[..n3]).err(),
            Some(ValidationError::EndOfInput)
        );
        // Another protocol.
        let n4 = packet(&mut buf, PROTO_ICMP, 0, 16, 0);
        assert_eq!(
            validate(&buf[..n4]).err(),
            Some(ValidationError::OutOfRange)
        );
    }

    /// An IPv6 packet carrying a UDP datagram with `data_len` bytes of data
    /// and a correct checksum. Returns its length.
    fn datagram6(buf: &mut [u8], data_len: usize) -> usize {
        let udp_len = HEADER_LEN + data_len;
        let n = ipv6::tests::packet(buf, NEXT_UDP, udp_len, 0);
        buf[40..42].copy_from_slice(&5353u16.to_be_bytes());
        buf[42..44].copy_from_slice(&53u16.to_be_bytes());
        buf[44..46].copy_from_slice(&(udp_len as u16).to_be_bytes());
        buf[46..48].fill(0);
        let acc = inet::sum(0, &buf[8..40]);
        let acc = inet::sum(acc, &(udp_len as u32).to_be_bytes());
        let acc = inet::sum(acc, &[0, 0, 0, NEXT_UDP]);
        let mut c = !inet::sum(acc, &buf[40..40 + udp_len]);
        if c == 0 {
            c = 0xFFFF;
        }
        buf[46..48].copy_from_slice(&c.to_be_bytes());
        n
    }

    fn validate6(bytes: &[u8]) -> Result<Ipv6Udp<'_>, ValidationError> {
        Untrusted::new(bytes).validate::<Ipv6Udp>()
    }

    #[test]
    fn accepts_ipv6_datagrams() {
        let mut buf = [0u8; 128];
        for len in [0, 1, 17] {
            let n = datagram6(&mut buf, len);
            let u = validate6(&buf[..n]).unwrap();
            assert_eq!(u.header.src_port, BigEndian(5353));
            assert_eq!(u.header.dst_port, BigEndian(53));
            assert_eq!(u.header.length.0 as usize, HEADER_LEN + len);
            assert_eq!(u.payload.read_all::<Count>(), Ok(Count(len)));
        }
    }

    #[test]
    fn rejects_malformed_ipv6_datagrams() {
        let mut buf = [0u8; 128];
        let n = datagram6(&mut buf, 10);
        // Corrupted data, or source address.
        for i in [n - 1, 8] {
            let mut b = buf;
            b[i] ^= 1;
            assert_eq!(
                validate6(&b[..n]).err(),
                Some(ValidationError::ChecksumMismatch)
            );
        }
        // No checksum: not allowed over IPv6.
        let mut b = buf;
        b[46..48].fill(0);
        assert_eq!(
            validate6(&b[..n]).err(),
            Some(ValidationError::ChecksumMismatch)
        );
        // Length field disagreeing with the IPv6 payload.
        let mut b = buf;
        b[45] = 17;
        assert_eq!(
            validate6(&b[..n]).err(),
            Some(ValidationError::LengthMismatch {
                expected: 18,
                actual: 17
            })
        );
        // An extension header (hop-by-hop options) before the datagram.
        let mut b = buf;
        b[6] = 0;
        assert_eq!(validate6(&b[..n]).err(), Some(ValidationError::OutOfRange));
        // Shorter than a UDP header.
        let n2 = ipv6::tests::packet(&mut buf, NEXT_UDP, 7, 0);
        assert_eq!(
            validate6(&buf[..n2]).err(),
            Some(ValidationError::EndOfInput)
        );
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

#[cfg(test)]
pub(crate) mod encode_tests {
    extern crate std;
    use super::*;

    /// The bytes themselves, accepted as they are.
    struct Raw<'a>(&'a [u8]);

    impl<'a> Validate<&'a [u8]> for Raw<'a> {
        type Err = ValidationError;
        fn validate(input: &'a [u8]) -> Result<Self, ValidationError> {
            Ok(Raw(input))
        }
    }

    #[test]
    fn encoded_datagrams_decode_back() {
        let mut out = [0u8; 2048];
        for len in [0usize, 1, 2, 17, 1400] {
            let data: [u8; 1400] = core::array::from_fn(|i| (i * 7 + len) as u8);
            let data = &data[..len];
            let n = encode_ipv4(
                ipv4::Ipv4Addr(0xC0A8_0001),
                ipv4::Ipv4Addr(0x0A00_0002),
                51820,
                4242,
                data,
                &mut out,
            )
            .unwrap();
            assert_eq!(n, 28 + len);
            let u = Untrusted::new(&out[..n])
                .validate::<Ipv4Udp>()
                .ok()
                .unwrap();
            assert_eq!(u.ip.header.src, ipv4::Ipv4Addr(0xC0A8_0001));
            assert_eq!(u.ip.header.dst, ipv4::Ipv4Addr(0x0A00_0002));
            assert_eq!((u.header.src_port.0, u.header.dst_port.0), (51820, 4242));
            assert_ne!(u.header.checksum.0, 0);
            assert_eq!(u.payload.validate::<Raw>().unwrap().0, data);

            let n = encode_ipv6(
                ipv6::Ipv6Addr(0xfd00 << 112 | 1),
                ipv6::Ipv6Addr(0xfd00 << 112 | 2),
                51820,
                4242,
                data,
                &mut out,
            )
            .unwrap();
            assert_eq!(n, 48 + len);
            let u = Untrusted::new(&out[..n])
                .validate::<Ipv6Udp>()
                .ok()
                .unwrap();
            assert_eq!(u.ip.header.src, ipv6::Ipv6Addr(0xfd00 << 112 | 1));
            assert_eq!(u.ip.header.dst, ipv6::Ipv6Addr(0xfd00 << 112 | 2));
            assert_eq!((u.header.src_port.0, u.header.dst_port.0), (51820, 4242));
            assert_eq!(u.payload.validate::<Raw>().unwrap().0, data);
        }
        assert_eq!(
            encode_ipv4(
                ipv4::Ipv4Addr(1),
                ipv4::Ipv4Addr(2),
                1,
                2,
                &[0; 10],
                &mut out[..37]
            ),
            None
        );
    }

    /// `bytes` as lowercase hex.
    pub(crate) fn hex(bytes: &[u8]) -> std::string::String {
        bytes.iter().map(|b| std::format!("{b:02x}")).collect()
    }

    /// The exact bytes the encoders write: the wire format must not change
    /// when the encoders are rebuilt.
    #[test]
    fn golden_datagrams() {
        let mut out = [0u8; 64];
        let (a, b) = (ipv4::Ipv4Addr(0xC0A8_0001), ipv4::Ipv4Addr(0x0A00_0002));
        let n = encode_ipv4(a, b, 51820, 53, b"golden", &mut out).unwrap();
        assert_eq!(hex(&out[..n]), "450000220000400040117020c0a800010a000002ca6c0035000e3143676f6c64656e");
        let n = encode_ipv4(a, b, 1, 2, b"", &mut out).unwrap();
        assert_eq!(hex(&out[..n]), "4500001c0000400040117026c0a800010a0000020001000200083530");
        let (a, b) = (ipv6::Ipv6Addr(0xfd00 << 112 | 1), ipv6::Ipv6Addr(0x2001_0db8 << 96 | 0xabcd));
        let n = encode_ipv6(a, b, 51820, 53, b"golden!", &mut out).unwrap();
        assert_eq!(hex(&out[..n]), "60000000000f1140fd00000000000000000000000000000120010db800000000000000000000abcdca6c0035000f0464676f6c64656e21");
    }
}
